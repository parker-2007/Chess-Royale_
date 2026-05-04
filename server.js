const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(express.static(path.join(__dirname, 'public')));

// ── Constants ──────────────────────────────────────────────────────────────
const MAX_ELIXIR = 21;
const REGEN_RATE = 1.0;
const TICK_MS = 100;
const COOLDOWN_MS = 3000;
const PROMOTE_TYPES = ['queen','rook','bishop','knight'];

const PIECE_DATA = {
  king:   { deploy: 0,  moveCost: (d) => d * 10 },
  queen:  { deploy: 10, moveCost: (d) => d * 3  },
  rook:   { deploy: 7,  moveCost: (d) => d * 2  },
  bishop: { deploy: 5,  moveCost: (d) => d * 2  },
  knight: { deploy: 5,  moveCost: ()  => 5      },
  pawn:   { deploy: 2,  moveCost: (d) => d * 1  },
};

const PIECE_TYPES = ['pawn','pawn','pawn','knight','knight','bishop','bishop','rook','rook','queen'];
const PIECE_VALUE = { king:1000, queen:9, rook:5, bishop:3, knight:3, pawn:1 };

// AI difficulty settings
const AI_SETTINGS = {
  easy:   { minDelay:3500, maxDelay:5000, randomness:20, aggressiveness:1  },
  medium: { minDelay:1500, maxDelay:2500, randomness:2,  aggressiveness:3  },
  hard:   { minDelay:600,  maxDelay:1200, randomness:0,  aggressiveness:8  },
};

// ── Helpers ────────────────────────────────────────────────────────────────
function shuffle(arr) {
  const a = [...arr];
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function buildQueue() {
  return [...shuffle(PIECE_TYPES), ...shuffle(PIECE_TYPES), ...shuffle(PIECE_TYPES)];
}

function buildPromotionQueue() {
  // Pre-roll promotion sequence for whole game
  const q = [];
  for (let i = 0; i < 20; i++) q.push(PROMOTE_TYPES[Math.floor(Math.random() * PROMOTE_TYPES.length)]);
  return q;
}

function initBoard() {
  const b = Array.from({ length: 8 }, () => Array(8).fill(null));
  b[0][4] = { type: 'king', player: 2 };
  b[0][3] = { type: 'pawn', player: 2 };
  b[0][5] = { type: 'pawn', player: 2 };
  b[1][3] = { type: 'pawn', player: 2 };
  b[1][5] = { type: 'pawn', player: 2 };
  b[1][4] = { type: 'pawn', player: 2 };
  b[7][4] = { type: 'king', player: 1 };
  b[7][3] = { type: 'pawn', player: 1 };
  b[7][5] = { type: 'pawn', player: 1 };
  b[6][3] = { type: 'pawn', player: 1 };
  b[6][5] = { type: 'pawn', player: 1 };
  b[6][4] = { type: 'pawn', player: 1 };
  return b;
}

function moveCost(type, fromRow, fromCol, toRow, toCol) {
  const dist = Math.max(Math.abs(toRow - fromRow), Math.abs(toCol - fromCol));
  return PIECE_DATA[type].moveCost(dist);
}

function getValidMoves(board, row, col) {
  const piece = board[row][col];
  if (!piece) return [];
  const moves = [];
  const p = piece.player;
  const dir = p === 1 ? -1 : 1;
  function add(r, c) {
    if (r < 0 || r >= 8 || c < 0 || c >= 8) return false;
    const t = board[r][c];
    if (t && t.player === p) return false;
    moves.push({ row: r, col: c });
    return !t;
  }
  function slide(dr, dc) { for (let i = 1; i < 8; i++) if (!add(row + dr * i, col + dc * i)) break; }
  switch (piece.type) {
    case 'king': for (let dr=-1;dr<=1;dr++) for (let dc=-1;dc<=1;dc++) if (dr||dc) add(row+dr,col+dc); break;
    case 'queen': slide(1,0);slide(-1,0);slide(0,1);slide(0,-1);slide(1,1);slide(1,-1);slide(-1,1);slide(-1,-1); break;
    case 'rook':  slide(1,0);slide(-1,0);slide(0,1);slide(0,-1); break;
    case 'bishop':slide(1,1);slide(1,-1);slide(-1,1);slide(-1,-1); break;
    case 'knight': [[2,1],[2,-1],[-2,1],[-2,-1],[1,2],[1,-2],[-1,2],[-1,-2]].forEach(([dr,dc])=>add(row+dr,col+dc)); break;
    case 'pawn': {
      const fr = row + dir;
      if (fr >= 0 && fr < 8 && !board[fr][col]) {
        moves.push({ row: fr, col });
        const startRow = p === 1 ? 6 : 1;
        if (row === startRow && !board[row + dir * 2]?.[col]) moves.push({ row: row + dir * 2, col });
      }
      [-1, 1].forEach(dc => {
        if (col+dc >= 0 && col+dc < 8 && board[fr]?.[col+dc]?.player && board[fr][col+dc].player !== p)
          moves.push({ row: fr, col: col+dc });
      });
      break;
    }
  }
  return moves;
}

// ── Pawn Promotion ─────────────────────────────────────────────────────────
function checkPromotion(room, row, col) {
  const piece = room.board[row][col];
  if (!piece || piece.type !== 'pawn') return false;
  const backRank = piece.player === 1 ? 0 : 7;
  if (row !== backRank) return false;
  const promoteTo = room.promotionQueue[room.promotionIdx++ % room.promotionQueue.length];
  room.board[row][col] = { type: promoteTo, player: piece.player };
  io.to(room.code).emit('promotion', { row, col, type: promoteTo, player: piece.player });
  return true;
}

// ── Room Management ────────────────────────────────────────────────────────
const rooms = {};

function createRoom(roomCode) {
  rooms[roomCode] = {
    code: roomCode,
    players: [],
    board: initBoard(),
    elixir: [0, 0],
    hands: [[], []],
    queueIdx: [0, 0],
    queue: buildQueue(),
    promotionQueue: buildPromotionQueue(),
    promotionIdx: 0,
    cooldowns: {},
    gameOver: false,
    ticker: null,
    isAI: false,
    aiDifficulty: 'medium',
    aiTicker: null,
  };
  return rooms[roomCode];
}

function resetRoom(room) {
  room.board = initBoard();
  room.elixir = [0, 0];
  room.hands = [[], []];
  room.queueIdx = [0, 0];
  room.queue = buildQueue();
  room.promotionQueue = buildPromotionQueue();
  room.promotionIdx = 0;
  room.cooldowns = {};
  room.gameOver = false;
  room.winner = null;
  room.rematchVotes = new Set();
  room.ticker = null;
  dealHand(room, 0); dealHand(room, 1);
}

function dealHand(room, playerIdx) {
  while (room.hands[playerIdx].length < 3) {
    room.hands[playerIdx].push(room.queue[room.queueIdx[playerIdx]++]);
  }
}

function getPublicState(room) {
  const now = Date.now();
  const cooldownsRemaining = {};
  for (const [key, expiry] of Object.entries(room.cooldowns)) {
    const remaining = expiry - now;
    if (remaining > 0) cooldownsRemaining[key] = remaining;
  }
  return {
    board: room.board,
    elixir: room.elixir,
    hands: room.hands,
    queueNexts: [room.queue[room.queueIdx[0]], room.queue[room.queueIdx[1]]],
    cooldowns: cooldownsRemaining,
    gameOver: room.gameOver,
    winner: room.winner || null,
  };
}

function startCountdown(roomCode, onComplete) {
  let count = 3;
  io.to(roomCode).emit('countdown', count);
  const iv = setInterval(() => {
    count--;
    if (count > 0) {
      io.to(roomCode).emit('countdown', count);
    } else {
      clearInterval(iv);
      io.to(roomCode).emit('countdown', 0);
      setTimeout(onComplete, 100);
    }
  }, 1000);
}

function startTicker(roomCode) {
  const room = rooms[roomCode];
  if (room.ticker) return;
  let last = Date.now();
  room.ticker = setInterval(() => {
    if (room.gameOver) { clearInterval(room.ticker); return; }
    const now = Date.now();
    const dt = (now - last) / 1000;
    last = now;
    room.elixir[0] = Math.min(MAX_ELIXIR, room.elixir[0] + REGEN_RATE * dt);
    room.elixir[1] = Math.min(MAX_ELIXIR, room.elixir[1] + REGEN_RATE * dt);
    io.to(roomCode).emit('state', getPublicState(room));
  }, TICK_MS);
}

// ── AI ─────────────────────────────────────────────────────────────────────
function aiTick(roomCode) {
  const room = rooms[roomCode];
  if (!room || room.gameOver || !room.isAI) return;
  const AI = 1;
  const elixir = room.elixir[AI];
  const now = Date.now();
  const settings = AI_SETTINGS[room.aiDifficulty] || AI_SETTINGS.medium;

  let bestMove = null, bestScore = -Infinity;

  for (let r = 0; r < 8; r++) {
    for (let c = 0; c < 8; c++) {
      const piece = room.board[r][c];
      if (!piece || piece.player !== 2) continue;
      const cdKey = `${r},${c}`;
      if (room.cooldowns[cdKey] && room.cooldowns[cdKey] > now) continue;
      const moves = getValidMoves(room.board, r, c);
      for (const { row, col } of moves) {
        const cost = moveCost(piece.type, r, c, row, col);
        if (elixir < cost) continue;
        let score = 0;
        const target = room.board[row][col];
        if (target) score += PIECE_VALUE[target.type] * 100;
        if (target?.type === 'king') score += 100000;

        let p1KingRow = 7, p1KingCol = 4;
        for (let rr = 0; rr < 8; rr++) for (let cc = 0; cc < 8; cc++)
          if (room.board[rr][cc]?.type === 'king' && room.board[rr][cc]?.player === 1) { p1KingRow = rr; p1KingCol = cc; }

        const distBefore = Math.abs(r-p1KingRow) + Math.abs(c-p1KingCol);
        const distAfter  = Math.abs(row-p1KingRow) + Math.abs(col-p1KingCol);
        score += (distBefore - distAfter) * settings.aggressiveness;

        // Hard: also protect own pieces
        if (room.aiDifficulty === 'hard') {
          let threatened = false;
          for (let rr = 0; rr < 8; rr++) for (let cc = 0; cc < 8; cc++) {
            const op = room.board[rr][cc];
            if (op?.player === 1) {
              const om = getValidMoves(room.board, rr, cc);
              if (om.find(m => m.row === r && m.col === c)) threatened = true;
            }
          }
          if (threatened) score += PIECE_VALUE[piece.type] * 5;
        }

        score -= cost * 0.5;
        score += (Math.random() - 0.5) * settings.randomness;
        if (score > bestScore) { bestScore = score; bestMove = { fromRow:r, fromCol:c, toRow:row, toCol:col, cost }; }
      }
    }
  }

  // Deploy
  const hand = room.hands[AI];
  for (let i = 0; i < hand.length; i++) {
    const type = hand[i];
    const cost = PIECE_DATA[type].deploy;
    if (elixir < cost + (room.aiDifficulty === 'easy' ? 5 : 3)) continue;
    const emptyCols = [];
    for (let c = 0; c < 8; c++) if (!room.board[0][c]) emptyCols.push(c);
    if (emptyCols.length === 0) continue;
    let p1KingCol = 4;
    for (let rr = 0; rr < 8; rr++) for (let cc = 0; cc < 8; cc++)
      if (room.board[rr][cc]?.type === 'king' && room.board[rr][cc]?.player === 1) p1KingCol = cc;
    emptyCols.sort((a,b) => Math.abs(a-p1KingCol) - Math.abs(b-p1KingCol));
    const deployScore = PIECE_VALUE[type] * 10 - cost * 0.5 + (Math.random()-0.5)*settings.randomness;
    if (deployScore > bestScore) {
      bestScore = deployScore;
      bestMove = { deploy: true, cardIdx: i, row: 0, col: emptyCols[0], cost };
    }
  }

  if (!bestMove) return;

  if (bestMove.deploy) {
    const type = hand[bestMove.cardIdx];
    room.elixir[AI] -= bestMove.cost;
    room.board[bestMove.row][bestMove.col] = { type, player: 2 };
    hand.splice(bestMove.cardIdx, 1);
    dealHand(room, AI);
  } else {
    room.elixir[AI] -= bestMove.cost;
    const piece = room.board[bestMove.fromRow][bestMove.fromCol];
    if (room.board[bestMove.toRow][bestMove.toCol]?.type === 'king') {
      room.board[bestMove.toRow][bestMove.toCol] = piece;
      room.board[bestMove.fromRow][bestMove.fromCol] = null;
      room.gameOver = true;
      room.winner = 2;
    } else {
      room.board[bestMove.toRow][bestMove.toCol] = piece;
      room.board[bestMove.fromRow][bestMove.fromCol] = null;
      room.cooldowns[`${bestMove.toRow},${bestMove.toCol}`] = now + COOLDOWN_MS;
      checkPromotion(room, bestMove.toRow, bestMove.toCol);
    }
  }
  io.to(roomCode).emit('state', getPublicState(room));
}

function startAITicker(roomCode) {
  const room = rooms[roomCode];
  if (room.aiTicker) return;
  const settings = AI_SETTINGS[room.aiDifficulty] || AI_SETTINGS.medium;
  function scheduleNext() {
    const delay = settings.minDelay + Math.random() * (settings.maxDelay - settings.minDelay);
    room.aiTicker = setTimeout(() => {
      if (!rooms[roomCode] || rooms[roomCode].gameOver) return;
      aiTick(roomCode);
      scheduleNext();
    }, delay);
  }
  scheduleNext();
}

// ── Socket Handlers ────────────────────────────────────────────────────────
io.on('connection', (socket) => {
  console.log('Connected:', socket.id);

  socket.on('createRoom', (roomCode) => {
    if (rooms[roomCode]) { socket.emit('error', 'Room already exists'); return; }
    const room = createRoom(roomCode);
    room.players.push(socket.id);
    socket.join(roomCode);
    socket.roomCode = roomCode;
    socket.playerIdx = 0;
    dealHand(room, 0); dealHand(room, 1);
    socket.emit('joined', { playerIdx: 0, roomCode });
    console.log(`Room ${roomCode} created`);
  });

  socket.on('joinRoom', (roomCode) => {
    const room = rooms[roomCode];
    if (!room) { socket.emit('error', 'Room not found'); return; }
    if (room.players.length >= 2) { socket.emit('error', 'Room is full'); return; }
    room.players.push(socket.id);
    socket.join(roomCode);
    socket.roomCode = roomCode;
    socket.playerIdx = 1;
    socket.emit('joined', { playerIdx: 1, roomCode });
    startCountdown(roomCode, () => {
      io.to(roomCode).emit('gameStart');
      startTicker(roomCode);
    });
    console.log(`Room ${roomCode} P2 joined`);
  });

  socket.on('playAI', ({ difficulty }) => {
    const roomCode = 'AI_' + socket.id;
    const room = createRoom(roomCode);
    room.isAI = true;
    room.aiDifficulty = difficulty || 'medium';
    room.players.push(socket.id);
    socket.join(roomCode);
    socket.roomCode = roomCode;
    socket.playerIdx = 0;
    dealHand(room, 0); dealHand(room, 1);
    socket.emit('joined', { playerIdx: 0, roomCode });
    startCountdown(roomCode, () => {
      io.to(roomCode).emit('gameStart');
      startTicker(roomCode);
      startAITicker(roomCode);
    });
    console.log(`AI (${room.aiDifficulty}) game started`);
  });

  socket.on('move', ({ fromRow, fromCol, toRow, toCol }) => {
    const room = rooms[socket.roomCode];
    if (!room || room.gameOver) return;
    const p = socket.playerIdx;
    const piece = room.board[fromRow][fromCol];
    if (!piece || piece.player !== p + 1) return;
    const cdKey = `${fromRow},${fromCol}`;
    if (room.cooldowns[cdKey] && room.cooldowns[cdKey] > Date.now()) return;
    const valid = getValidMoves(room.board, fromRow, fromCol).find(m => m.row === toRow && m.col === toCol);
    if (!valid) return;
    const cost = moveCost(piece.type, fromRow, fromCol, toRow, toCol);
    if (room.elixir[p] < cost) return;
    room.elixir[p] -= cost;
    if (room.board[toRow][toCol]?.type === 'king') {
      room.board[toRow][toCol] = piece;
      room.board[fromRow][fromCol] = null;
      room.gameOver = true;
      room.winner = p + 1;
      io.to(socket.roomCode).emit('state', getPublicState(room));
      return;
    }
    room.board[toRow][toCol] = piece;
    room.board[fromRow][fromCol] = null;
    room.cooldowns[`${toRow},${toCol}`] = Date.now() + COOLDOWN_MS;
    checkPromotion(room, toRow, toCol);
    io.to(socket.roomCode).emit('state', getPublicState(room));
  });

  socket.on('deploy', ({ cardIdx, row, col }) => {
    const room = rooms[socket.roomCode];
    if (!room || room.gameOver) return;
    const p = socket.playerIdx;
    const deployRow = p === 0 ? 7 : 0;
    if (row !== deployRow) return;
    if (room.board[row][col]) return;
    const hand = room.hands[p];
    if (cardIdx < 0 || cardIdx >= hand.length) return;
    const type = hand[cardIdx];
    const cost = PIECE_DATA[type].deploy;
    if (room.elixir[p] < cost) return;
    room.elixir[p] -= cost;
    room.board[row][col] = { type, player: p + 1 };
    hand.splice(cardIdx, 1);
    dealHand(room, p);
    io.to(socket.roomCode).emit('state', getPublicState(room));
  });

  socket.on('rematch', () => {
    const room = rooms[socket.roomCode];
    if (!room || !room.gameOver) return;

    if (room.isAI) {
      clearInterval(room.ticker);
      clearTimeout(room.aiTicker);
      room.aiTicker = null;
      resetRoom(room);
      startCountdown(socket.roomCode, () => {
        socket.emit('rematchStart');
        startTicker(socket.roomCode);
        startAITicker(socket.roomCode);
      });
      return;
    }

    if (!room.rematchVotes) room.rematchVotes = new Set();
    if (room.rematchVotes.has(socket.playerIdx)) return;
    room.rematchVotes.add(socket.playerIdx);
    socket.emit('rematchVote', { mine: true });
    socket.to(socket.roomCode).emit('rematchVote', { mine: false });
    if (room.rematchVotes.size >= 2) {
      clearInterval(room.ticker);
      resetRoom(room);
      startCountdown(socket.roomCode, () => {
        io.to(socket.roomCode).emit('rematchStart');
        startTicker(socket.roomCode);
      });
    }
  });

  socket.on('disconnect', () => {
    const room = rooms[socket.roomCode];
    if (room) {
      clearInterval(room.ticker);
      clearTimeout(room.aiTicker);
      if (!room.isAI) io.to(socket.roomCode).emit('playerLeft');
      delete rooms[socket.roomCode];
    }
    console.log('Disconnected:', socket.id);
  });
});

const PORT = 3000;
server.listen(PORT, '0.0.0.0', () => {
  console.log(`\n✅ Chess Royale server running on port ${PORT}\n`);
});
