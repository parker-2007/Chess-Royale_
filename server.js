const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(express.static(path.join(__dirname, 'public')));

// ── Game Constants ─────────────────────────────────────────────────────────
const MAX_ELIXIR = 21;
const REGEN_RATE = 1.0;
const TICK_MS = 100;
const COOLDOWN_MS = 3000;

const PIECE_DATA = {
  king:   { deploy: 0,  moveCost: (d) => d * 10 },
  queen:  { deploy: 10, moveCost: (d) => d * 3  },
  rook:   { deploy: 7,  moveCost: (d) => d * 2  },
  bishop: { deploy: 5,  moveCost: (d) => d * 2  },
  knight: { deploy: 5,  moveCost: ()  => 5      },
  pawn:   { deploy: 2,  moveCost: (d) => d * 1  },
};

const PIECE_TYPES = ['pawn','pawn','pawn','knight','knight','bishop','bishop','rook','rook','queen'];

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

function initBoard() {
  const b = Array.from({ length: 8 }, () => Array(8).fill(null));
  // Player 2 (red) top — king at [0][4]
  b[0][4] = { type: 'king', player: 2 };
  b[0][3] = { type: 'pawn', player: 2 };
  b[0][5] = { type: 'pawn', player: 2 };
  b[1][3] = { type: 'pawn', player: 2 };
  b[1][5] = { type: 'pawn', player: 2 };
  b[1][4] = { type: 'pawn', player: 2 };
  // Player 1 (blue) bottom — king at [7][4]
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
    case 'king':
      for (let dr = -1; dr <= 1; dr++) for (let dc = -1; dc <= 1; dc++) if (dr || dc) add(row + dr, col + dc);
      break;
    case 'queen': slide(1,0);slide(-1,0);slide(0,1);slide(0,-1);slide(1,1);slide(1,-1);slide(-1,1);slide(-1,-1); break;
    case 'rook':  slide(1,0);slide(-1,0);slide(0,1);slide(0,-1); break;
    case 'bishop':slide(1,1);slide(1,-1);slide(-1,1);slide(-1,-1); break;
    case 'knight':
      [[2,1],[2,-1],[-2,1],[-2,-1],[1,2],[1,-2],[-1,2],[-1,-2]].forEach(([dr,dc]) => add(row+dr, col+dc));
      break;
    case 'pawn': {
      const fr = row + dir;
      if (fr >= 0 && fr < 8 && !board[fr][col]) {
        moves.push({ row: fr, col });
        const startRow = p === 1 ? 6 : 1;
        if (row === startRow && !board[row + dir * 2]?.[col]) moves.push({ row: row + dir * 2, col });
      }
      [-1, 1].forEach(dc => {
        if (col + dc >= 0 && col + dc < 8 && board[fr]?.[col + dc]?.player && board[fr][col + dc].player !== p)
          moves.push({ row: fr, col: col + dc });
      });
      break;
    }
  }
  return moves;
}

// ── Room Management ────────────────────────────────────────────────────────
const rooms = {};

function createRoom(roomCode) {
  const queue = buildQueue();
  rooms[roomCode] = {
    players: [],
    board: initBoard(),
    elixir: [0, 0],
    hands: [[], []],
    queueIdx: [0, 0],
    queue,
    cooldowns: {},  // key: "row,col" => timestamp when cooldown expires
    gameOver: false,
    ticker: null,
  };
  return rooms[roomCode];
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
    console.log(`Room ${roomCode} created by P1`);
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
    io.to(roomCode).emit('gameStart');
    startTicker(roomCode);
    console.log(`Room ${roomCode} P2 joined — game starting`);
  });

  socket.on('move', ({ fromRow, fromCol, toRow, toCol }) => {
    const room = rooms[socket.roomCode];
    if (!room || room.gameOver) return;
    const p = socket.playerIdx;
    const piece = room.board[fromRow][fromCol];
    if (!piece || piece.player !== p + 1) return;

    // Check cooldown
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
    // Set cooldown on destination square
    room.cooldowns[`${toRow},${toCol}`] = Date.now() + COOLDOWN_MS;
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
    if (!room.rematchVotes) room.rematchVotes = new Set();
    if (room.rematchVotes.has(socket.playerIdx)) return;
    room.rematchVotes.add(socket.playerIdx);
    // Tell each player individually their own state
    socket.emit('rematchVote', { mine: true, votes: room.rematchVotes.size });
    socket.to(socket.roomCode).emit('rematchVote', { mine: false, votes: room.rematchVotes.size });
    if (room.rematchVotes.size >= 2) {
      clearInterval(room.ticker);
      const queue = buildQueue();
      room.board = initBoard();
      room.elixir = [0, 0];
      room.hands = [[], []];
      room.queueIdx = [0, 0];
      room.queue = queue;
      room.cooldowns = {};
      room.gameOver = false;
      room.winner = null;
      room.rematchVotes = new Set();
      room.ticker = null;
      dealHand(room, 0); dealHand(room, 1);
      io.to(socket.roomCode).emit('rematchStart');
      startTicker(socket.roomCode);
    }
  });

  socket.on('disconnect', () => {
    const room = rooms[socket.roomCode];
    if (room) {
      clearInterval(room.ticker);
      io.to(socket.roomCode).emit('playerLeft');
      delete rooms[socket.roomCode];
    }
    console.log('Disconnected:', socket.id);
  });
});

// ── Start ──────────────────────────────────────────────────────────────────
const PORT = 3000;
server.listen(PORT, '0.0.0.0', () => {
  const { networkInterfaces } = require('os');
  const nets = networkInterfaces();
  let localIP = 'localhost';
  for (const name of Object.keys(nets)) {
    for (const net of nets[name]) {
      if (net.family === 'IPv4' && !net.internal) { localIP = net.address; break; }
    }
  }
  console.log(`\n✅ CheshRoyale server running`);
  console.log(`   Local:   http://localhost:${PORT}`);
  console.log(`   Brother: http://${localIP}:${PORT}`);
  console.log(`\n   Share the Brother link with your brother!\n`);
});
