const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(express.static(path.join(__dirname, 'public')));

// ── Constants ──────────────────────────────────────────────────────────────
const MAX_ELIXIR = 15;
const REGEN_RATE = 1.0;
const TICK_MS = 100;
const COOLDOWN_MS = 3000;
const GAME_DURATION = 180; // 3 minutes in seconds
const PROMOTE_TYPES = ['queen','rook','bishop','knight'];
const PIECE_DATA = {
  king:   { deploy: 0,  moveCost: (d,timeLeft) => d * (timeLeft<=60 ? 3 : 10) },
  queen:  { deploy: 15, moveCost: (d) => d * 1  },
  rook:   { deploy: 10, moveCost: (d) => d * 2  },
  bishop: { deploy: 6,  moveCost: (d) => d * 2  },
  knight: { deploy: 6,  moveCost: ()  => 6      },
  pawn:   { deploy: 2,  moveCost: (d) => d * 1  },
};
const PIECE_TYPES = ['pawn','knight','bishop','rook','queen'];
const PIECE_VALUE = { king:1000, queen:9, rook:5, bishop:3, knight:3, pawn:1 };

// ── Spells ─────────────────────────────────────────────────────────────────
const SPELL_DATA = {
  freeze: { name:'Freeze', icon:'❄️', cost:3, area:3 },
  mud:    { name:'Mud',    icon:'🟤', cost:3, area:2 },
  haste:  { name:'Haste',  icon:'⚡', cost:7, area:1 },
};
const SPELL_TYPES = ['freeze','mud','haste'];
const ALL_CARDS = [...PIECE_TYPES,...SPELL_TYPES]; // 8 total, pick 6
const DEFAULT_DECK = ['pawn','knight','bishop','rook','queen','freeze'];

function isSpell(type){ return !!SPELL_DATA[type]; }

// Build an infinite cycle from a 6-card deck (CR style: shuffle deck, repeat)
function buildCycleFromDeck(deck) {
  // Repeat shuffled deck 5 times so we have plenty of cards
  const cycle=[];
  for(let i=0;i<5;i++) cycle.push(...shuffle([...deck]));
  return cycle;
}
const AI_SETTINGS = {
  easy:   { minDelay:3500, maxDelay:5000, randomness:20, aggressiveness:1 },
  medium: { minDelay:1500, maxDelay:2500, randomness:2,  aggressiveness:3 },
  hard:   { minDelay:600,  maxDelay:1200, randomness:0,  aggressiveness:8 },
};

// ── ELO & Leaderboard ──────────────────────────────────────────────────────
const playerRatings = {}; // socketId => { name, elo }
const leaderboard   = []; // [{ name, elo }] top 10, persists in memory

function getOrCreateRating(socketId, name) {
  if (!playerRatings[socketId]) playerRatings[socketId] = { name: name || 'Player', elo: 1000 };
  return playerRatings[socketId];
}

function calcElo(winnerElo, loserElo) {
  const K = 32;
  const expected = 1 / (1 + Math.pow(10, (loserElo - winnerElo) / 400));
  const winnerNew = Math.round(winnerElo + K * (1 - expected));
  const loserNew  = Math.round(loserElo  + K * (0 - (1 - expected)));
  return { winnerNew, loserNew };
}

function updateLeaderboard(name, elo) {
  const idx = leaderboard.findIndex(e => e.name === name);
  if (idx >= 0) leaderboard[idx].elo = Math.max(leaderboard[idx].elo, elo);
  else leaderboard.push({ name, elo });
  leaderboard.sort((a,b) => b.elo - a.elo);
  if (leaderboard.length > 10) leaderboard.length = 10;
}

function getLeaderboard() { return leaderboard.slice(0, 10); }

// ── Matchmaking queue ──────────────────────────────────────────────────────
let matchmakingQueue = null; // { socketId, socket, name, elo }

// ── Helpers ────────────────────────────────────────────────────────────────
function shuffle(arr) {
  const a = [...arr];
  for (let i = a.length-1; i > 0; i--) { const j=Math.floor(Math.random()*(i+1)); [a[i],a[j]]=[a[j],a[i]]; }
  return a;
}
function buildQueue() { return [...shuffle(PIECE_TYPES),...shuffle(PIECE_TYPES),...shuffle(PIECE_TYPES)]; }
function buildPromotionQueue() { const q=[]; for(let i=0;i<20;i++) q.push(PROMOTE_TYPES[Math.floor(Math.random()*PROMOTE_TYPES.length)]); return q; }

function initBoard() {
  const b = Array.from({length:8}, ()=>Array(8).fill(null));
  b[0][4]={type:'king',player:2}; b[0][3]={type:'pawn',player:2}; b[0][5]={type:'pawn',player:2};
  b[7][4]={type:'king',player:1}; b[7][3]={type:'pawn',player:1}; b[7][5]={type:'pawn',player:1};
  return b;
}
function moveCost(type,fr,fc,tr,tc,timeLeft=999) { return PIECE_DATA[type].moveCost(Math.max(Math.abs(tr-fr),Math.abs(tc-fc)),timeLeft); }

function getValidMoves(board,row,col) {
  const piece=board[row][col]; if(!piece) return [];
  const moves=[],p=piece.player,dir=p===1?-1:1;
  function add(r,c){if(r<0||r>=8||c<0||c>=8)return false;const t=board[r][c];if(t&&t.player===p)return false;moves.push({row:r,col:c});return!t;}
  function slide(dr,dc){for(let i=1;i<8;i++)if(!add(row+dr*i,col+dc*i))break;}
  switch(piece.type){
    case 'king': for(let dr=-1;dr<=1;dr++)for(let dc=-1;dc<=1;dc++)if(dr||dc)add(row+dr,col+dc); break;
    case 'queen': slide(1,0);slide(-1,0);slide(0,1);slide(0,-1);slide(1,1);slide(1,-1);slide(-1,1);slide(-1,-1); break;
    case 'rook':  slide(1,0);slide(-1,0);slide(0,1);slide(0,-1); break;
    case 'bishop':slide(1,1);slide(1,-1);slide(-1,1);slide(-1,-1); break;
    case 'knight':[[2,1],[2,-1],[-2,1],[-2,-1],[1,2],[1,-2],[-1,2],[-1,-2]].forEach(([dr,dc])=>add(row+dr,col+dc)); break;
    case 'pawn':{
      const fr=row+dir;
      if(fr>=0&&fr<8&&!board[fr][col]){
        moves.push({row:fr,col});
        // Starting row: p1 starts at row 6-7, p2 starts at row 0-1
        const startRow=p===1?6:1;
        if(row===startRow&&fr>=0&&fr<8&&!board[fr+dir]?.[col])
          moves.push({row:fr+dir,col});
      }
      [-1,1].forEach(dc=>{
        if(col+dc>=0&&col+dc<8&&fr>=0&&fr<8&&board[fr]?.[col+dc]?.player&&board[fr][col+dc].player!==p)
          moves.push({row:fr,col:col+dc});
      });
      break;
    }
  }
  return moves;
}

function checkPromotion(room,row,col) {
  const piece=room.board[row][col]; if(!piece||piece.type!=='pawn') return false;
  const backRank=piece.player===1?0:7; if(row!==backRank) return false;
  const promoteTo=room.promotionQueue[room.promotionIdx++%room.promotionQueue.length];
  room.board[row][col]={type:promoteTo,player:piece.player};
  io.to(room.code).emit('promotion',{row,col,type:promoteTo,player:piece.player});
  return true;
}

// ── Room Management ────────────────────────────────────────────────────────
const rooms = {};

function createRoom(roomCode) {
  rooms[roomCode] = {
    code:roomCode, players:[], socketIds:[], board:initBoard(),
    elixir:[0,0], hands:[[],[]], queueIdx:[0,0],
    decks:[DEFAULT_DECK,DEFAULT_DECK],
    cycles:[buildCycleFromDeck(DEFAULT_DECK),buildCycleFromDeck(DEFAULT_DECK)],
    promotionQueue:buildPromotionQueue(), promotionIdx:0,
    cooldowns:{}, gameOver:false, ticker:null,
    isAI:false, aiDifficulty:'medium', aiTicker:null,
    isMatchmaking:false,
    timeLeft:GAME_DURATION, startedAt:null,
    deployRows:[[7],[0]],
    kills:[0,0],
    effects:[],
  };
  return rooms[roomCode];
}

function resetRoom(room) {
  room.board=initBoard(); room.elixir=[0,0]; room.hands=[[],[]]; room.queueIdx=[0,0];
  room.cycles=[buildCycleFromDeck(room.decks[0]),buildCycleFromDeck(room.decks[1])];
  room.promotionQueue=buildPromotionQueue(); room.promotionIdx=0;
  room.cooldowns={}; room.gameOver=false; room.winner=null; room.rematchVotes=new Set();
  room.ticker=null; room.timeLeft=GAME_DURATION; room.startedAt=null;
  room.deployRows=[[7],[0]]; room.kills=[0,0]; room.effects=[];
  dealHand(room,0); dealHand(room,1);
}

function dealHand(room,idx) {
  while(room.hands[idx].length<3){
    if(room.queueIdx[idx]>=room.cycles[idx].length)
      room.cycles[idx].push(...shuffle([...room.decks[idx]]));
    room.hands[idx].push(room.cycles[idx][room.queueIdx[idx]++]);
  }
}

function getPublicState(room) {
  const now=Date.now(), cd={};
  for(const [k,expiry] of Object.entries(room.cooldowns)){const r=expiry-now;if(r>0)cd[k]=r;}
  // Clean expired effects and send active ones
  room.effects=room.effects.filter(e=>e.expiry>now||e.type==='freeze');
  const activeEffects=room.effects.filter(e=>e.expiry>now).map(e=>({
    type:e.type, squares:e.squares, remaining:Math.max(0,e.expiry-now)
  }));
  return { board:room.board, elixir:room.elixir, hands:room.hands,
           queueNexts:[room.cycles[0][room.queueIdx[0]],room.cycles[1][room.queueIdx[1]]],
           cooldowns:cd, gameOver:room.gameOver, winner:room.winner||null,
           timeLeft:Math.max(0,room.timeLeft), deployRows:room.deployRows,
           kills:room.kills, effects:activeEffects,
           doubleGold:room.timeLeft<=60, kingCheap:room.timeLeft<=60 };
}

// ── Spell helpers ──────────────────────────────────────────────────────────
function getAoeSquares(centerRow, centerCol, area) {
  const squares=[], half=Math.floor(area/2);
  for(let r=centerRow-half;r<=centerRow+half;r++)
    for(let c=centerCol-half;c<=centerCol+half;c++)
      if(r>=0&&r<8&&c>=0&&c<8) squares.push({r,c});
  return squares;
}

function isSquareAffected(room, row, col, effectType) {
  const now=Date.now();
  return room.effects.some(e=>e.type===effectType&&e.expiry>now&&e.squares.some(s=>s.r===row&&s.c===col));
}

function getMoveCostWithEffects(room, type, fr, fc, tr, tc) {
  let cost=moveCost(type,fr,fc,tr,tc,room.timeLeft);
  // Mud doubles move cost for pieces in mud zone
  if(isSquareAffected(room,fr,fc,'mud')) cost*=2;
  return cost;
}

function castSpell(room, spellType, centerRow, centerCol, casterPlayer) {
  const now=Date.now();
  const squares=getAoeSquares(centerRow,centerCol,SPELL_DATA[spellType].area);

  if(spellType==='freeze'){
    // Add 5s cooldown to all pieces in zone
    squares.forEach(({r,c})=>{
      const piece=room.board[r][c];
      if(piece){
        const key=`${r},${c}`;
        const existing=room.cooldowns[key]||now;
        room.cooldowns[key]=Math.max(existing,now)+5000;
      }
    });
    // Add visual effect (instant, no duration needed but show briefly)
    room.effects.push({type:'freeze',squares,expiry:now+1500,caster:casterPlayer});
  } else if(spellType==='mud'){
    room.effects.push({type:'mud',squares,expiry:now+10000,caster:casterPlayer});
  } else if(spellType==='haste'){
    // Remove cooldown from the piece on the target square
    squares.forEach(({r,c})=>{
      const piece=room.board[r][c];
      if(piece&&piece.player===casterPlayer){
        delete room.cooldowns[`${r},${c}`];
        // Add haste effect — 0s cooldown for 10s
        room.effects.push({type:'haste',squares:[{r,c}],expiry:now+10000,caster:casterPlayer});
      }
    });
  }
}

function startCountdown(roomCode,onComplete) {
  let count=3; io.to(roomCode).emit('countdown',count);
  const iv=setInterval(()=>{ count--; if(count>0){io.to(roomCode).emit('countdown',count);}else{clearInterval(iv);io.to(roomCode).emit('countdown',0);setTimeout(onComplete,100);} },1000);
}

function countPieces(board, player) {
  let count=0;
  for(let r=0;r<8;r++) for(let c=0;c<8;c++) if(board[r][c]?.player===player) count++;
  return count;
}

function startTicker(roomCode) {
  const room=rooms[roomCode]; if(room.ticker) return;
  let last=Date.now();
  room.startedAt=Date.now();
  let lastMinute=3; // track which minute we're in to trigger deploy zone changes

  room.ticker=setInterval(()=>{
    if(room.gameOver){clearInterval(room.ticker);return;}
    const now=Date.now(), dt=(now-last)/1000; last=now;

    // Update timer
    room.timeLeft=Math.max(0, GAME_DURATION - (now-room.startedAt)/1000);

    // Gold regen — 2x in last 60 seconds
    const rate = room.timeLeft<=60 ? REGEN_RATE*2 : REGEN_RATE;
    room.elixir[0]=Math.min(MAX_ELIXIR, room.elixir[0]+rate*dt);
    room.elixir[1]=Math.min(MAX_ELIXIR, room.elixir[1]+rate*dt);

    // Deploy zone — add a new row each minute (cumulative)
    const minutesLeft = Math.ceil(room.timeLeft/60);
    if(minutesLeft < lastMinute) {
      lastMinute = minutesLeft;
      // P1 adds next row up (toward 0), P2 adds next row down (toward 7)
      const p1Next = Math.min(...room.deployRows[0]) - 1; // one row higher
      const p2Next = Math.max(...room.deployRows[1]) + 1; // one row lower
      if(p1Next >= 4) room.deployRows[0].push(p1Next);
      if(p2Next <= 3) room.deployRows[1].push(p2Next);
      io.to(roomCode).emit('deployZoneChanged', { deployRows: room.deployRows });
    }

    // Game over on timeout — most kills wins
    if(room.timeLeft<=0){
      room.gameOver=true;
      if(room.kills[0]>room.kills[1]) room.winner=1;
      else if(room.kills[1]>room.kills[0]) room.winner=2;
      else room.winner=0; // draw
      const state=getPublicState(room);
      io.to(roomCode).emit('state',{...state, timeout:true, p1kills:room.kills[0], p2kills:room.kills[1]});
      clearInterval(room.ticker);
      return;
    }

    io.to(roomCode).emit('state',getPublicState(room));
  },TICK_MS);
}

// ── AI ─────────────────────────────────────────────────────────────────────
function aiTick(roomCode) {
  const room=rooms[roomCode]; if(!room||room.gameOver||!room.isAI) return;
  const AI=1,elixir=room.elixir[AI],now=Date.now(),settings=AI_SETTINGS[room.aiDifficulty]||AI_SETTINGS.medium;
  let bestMove=null,bestScore=-Infinity;
  for(let r=0;r<8;r++) for(let c=0;c<8;c++){
    const piece=room.board[r][c]; if(!piece||piece.player!==2) continue;
    if(room.cooldowns[`${r},${c}`]&&room.cooldowns[`${r},${c}`]>now) continue;
    const moves=getValidMoves(room.board,r,c);
    for(const{row,col}of moves){
      const cost=moveCost(piece.type,r,c,row,col,room.timeLeft); if(elixir<cost) continue;
      let score=0; const target=room.board[row][col];
      if(target) score+=PIECE_VALUE[target.type]*100;
      if(target?.type==='king') score+=100000;
      let p1KingRow=7,p1KingCol=4;
      for(let rr=0;rr<8;rr++)for(let cc=0;cc<8;cc++)if(room.board[rr][cc]?.type==='king'&&room.board[rr][cc]?.player===1){p1KingRow=rr;p1KingCol=cc;}
      score+=(Math.abs(r-p1KingRow)+Math.abs(c-p1KingCol)-Math.abs(row-p1KingRow)-Math.abs(col-p1KingCol))*settings.aggressiveness;
      if(room.aiDifficulty==='hard'){let threatened=false;for(let rr=0;rr<8;rr++)for(let cc=0;cc<8;cc++){const op=room.board[rr][cc];if(op?.player===1){const om=getValidMoves(room.board,rr,cc);if(om.find(m=>m.row===r&&m.col===c))threatened=true;}}if(threatened)score+=PIECE_VALUE[piece.type]*5;}
      score-=cost*0.5; score+=(Math.random()-.5)*settings.randomness;
      if(score>bestScore){bestScore=score;bestMove={fromRow:r,fromCol:c,toRow:row,toCol:col,cost};}
    }
  }
  const hand=room.hands[AI];
  for(let i=0;i<hand.length;i++){
    const type=hand[i];
    if(SPELL_DATA[type]) continue; // AI doesn't cast spells yet
    const cost=PIECE_DATA[type]?.deploy;
    if(elixir<cost+(room.aiDifficulty==='easy'?5:3)) continue;
    const emptyCols=[];for(let c=0;c<8;c++)if(!room.board[0][c])emptyCols.push(c);
    if(!emptyCols.length) continue;
    let p1KingCol=4;for(let rr=0;rr<8;rr++)for(let cc=0;cc<8;cc++)if(room.board[rr][cc]?.type==='king'&&room.board[rr][cc]?.player===1)p1KingCol=cc;
    emptyCols.sort((a,b)=>Math.abs(a-p1KingCol)-Math.abs(b-p1KingCol));
    const ds=PIECE_VALUE[type]*10-cost*0.5+(Math.random()-.5)*settings.randomness;
    if(ds>bestScore){bestScore=ds;bestMove={deploy:true,cardIdx:i,row:0,col:emptyCols[0],cost};}
  }
  if(!bestMove) return;
  if(bestMove.deploy){const type=hand[bestMove.cardIdx];room.elixir[AI]-=bestMove.cost;room.board[bestMove.row][bestMove.col]={type,player:2};hand.splice(bestMove.cardIdx,1);dealHand(room,AI);}
  else{room.elixir[AI]-=bestMove.cost;const piece=room.board[bestMove.fromRow][bestMove.fromCol];if(room.board[bestMove.toRow][bestMove.toCol]?.type==='king'){room.board[bestMove.toRow][bestMove.toCol]=piece;room.board[bestMove.fromRow][bestMove.fromCol]=null;room.gameOver=true;room.winner=2;}else{room.board[bestMove.toRow][bestMove.toCol]=piece;room.board[bestMove.fromRow][bestMove.fromCol]=null;room.cooldowns[`${bestMove.toRow},${bestMove.toCol}`]=now+COOLDOWN_MS;checkPromotion(room,bestMove.toRow,bestMove.toCol);}}
  io.to(roomCode).emit('state',getPublicState(room));
}

function startAITicker(roomCode) {
  const room=rooms[roomCode]; if(room.aiTicker) return;
  const settings=AI_SETTINGS[room.aiDifficulty]||AI_SETTINGS.medium;
  function next(){const delay=settings.minDelay+Math.random()*(settings.maxDelay-settings.minDelay);room.aiTicker=setTimeout(()=>{if(!rooms[roomCode]||rooms[roomCode].gameOver)return;aiTick(roomCode);next();},delay);}
  next();
}

// ── ELO resolution ─────────────────────────────────────────────────────────
function resolveElo(room, winnerIdx) {
  if (room.isAI || room.isMatchmaking === false) return null;
  const [id0, id1] = room.socketIds;
  if (!id0 || !id1) return null;
  const r0 = playerRatings[id0], r1 = playerRatings[id1];
  if (!r0 || !r1) return null;
  const winnerElo = winnerIdx === 0 ? r0.elo : r1.elo;
  const loserElo  = winnerIdx === 0 ? r1.elo : r0.elo;
  const { winnerNew, loserNew } = calcElo(winnerElo, loserElo);
  if (winnerIdx === 0) { r0.elo = winnerNew; r1.elo = loserNew; }
  else                 { r1.elo = winnerNew; r0.elo = loserNew; }
  updateLeaderboard(r0.name, r0.elo);
  updateLeaderboard(r1.name, r1.elo);
  return { p0elo: r0.elo, p1elo: r1.elo, p0change: winnerIdx===0?winnerNew-winnerElo:loserNew-loserElo, p1change: winnerIdx===0?loserNew-loserElo:winnerNew-winnerElo };
}

// ── Socket Handlers ────────────────────────────────────────────────────────
io.on('connection', (socket) => {

  socket.on('submitDeck', (deck) => {
    // Validate deck — 6 unique cards from ALL_CARDS
    if(!Array.isArray(deck)||deck.length!==6) return;
    if(new Set(deck).size!==6) return;
    if(!deck.every(c=>ALL_CARDS.includes(c))) return;
    socket.deck = deck; // store on socket for use when game starts
    // If already in a room, update deck
    const room=rooms[socket.roomCode];
    if(room&&socket.playerIdx>=0){
      room.decks[socket.playerIdx]=deck;
      room.cycles[socket.playerIdx]=buildCycleFromDeck(deck);
    }
  });

  socket.on('register', ({ name, elo }) => {
    playerRatings[socket.id] = { name: name||'Player', elo: elo||1000 };
    socket.emit('leaderboard', getLeaderboard());
  });

  socket.on('getLeaderboard', () => socket.emit('leaderboard', getLeaderboard()));

  socket.on('quickMatch', ({ name, elo }) => {
    getOrCreateRating(socket.id, name);
    playerRatings[socket.id].elo = elo || playerRatings[socket.id].elo;

    if (matchmakingQueue && matchmakingQueue.socketId !== socket.id) {
      // Pair with waiting player
      const opponent = matchmakingQueue;
      matchmakingQueue = null;
      const roomCode = 'MM_' + Date.now();
      const room = createRoom(roomCode);
      room.isMatchmaking = true;
      room.socketIds = [opponent.socketId, socket.id];
      if(opponent.deck){ room.decks[0]=opponent.deck; room.cycles[0]=buildCycleFromDeck(opponent.deck); }
      if(socket.deck){ room.decks[1]=socket.deck; room.cycles[1]=buildCycleFromDeck(socket.deck); }

      room.players.push(opponent.socketId); room.players.push(socket.id);
      opponent.socket.join(roomCode); socket.join(roomCode);
      opponent.socket.roomCode = roomCode; opponent.socket.playerIdx = 0;
      socket.roomCode = roomCode; socket.playerIdx = 1;
      dealHand(room,0); dealHand(room,1);

      const p0elo = playerRatings[opponent.socketId]?.elo || 1000;
      const p1elo = playerRatings[socket.id]?.elo || 1000;

      opponent.socket.emit('joined', { playerIdx:0, roomCode, opponentElo:p1elo, opponentName:name });
      socket.emit('joined', { playerIdx:1, roomCode, opponentElo:p0elo, opponentName:opponent.name });

      startCountdown(roomCode, () => {
        io.to(roomCode).emit('gameStart');
        startTicker(roomCode);
      });
    } else {
      // Join queue
      matchmakingQueue = { socketId:socket.id, socket, name, elo: elo||1000, deck:socket.deck };
      socket.emit('matchmaking', { status:'searching' });
    }
  });

  socket.on('cancelMatchmaking', () => {
    if (matchmakingQueue?.socketId === socket.id) matchmakingQueue = null;
  });

  socket.on('createRoom', (roomCode) => {
    if (rooms[roomCode]) { socket.emit('error','Room already exists'); return; }
    const room = createRoom(roomCode);
    if(socket.deck){ room.decks[0]=socket.deck; room.cycles[0]=buildCycleFromDeck(socket.deck); }
    room.players.push(socket.id); room.socketIds[0] = socket.id;
    socket.join(roomCode); socket.roomCode=roomCode; socket.playerIdx=0;
    dealHand(room,0); dealHand(room,1);
    socket.emit('joined',{playerIdx:0,roomCode});
  });

  socket.on('joinRoom', (roomCode) => {
    const room = rooms[roomCode];
    if (!room) { socket.emit('error','Room not found'); return; }
    if (room.players.length >= 2) { socket.emit('error','Room is full'); return; }
    if(socket.deck){ room.decks[1]=socket.deck; room.cycles[1]=buildCycleFromDeck(socket.deck); }
    room.players.push(socket.id); room.socketIds[1] = socket.id;
    socket.join(roomCode); socket.roomCode=roomCode; socket.playerIdx=1;
    // Reset hands to use new deck
    room.hands=[[],[]]; room.queueIdx=[0,0];
    dealHand(room,0); dealHand(room,1);
    socket.emit('joined',{playerIdx:1,roomCode});
    startCountdown(roomCode,()=>{ io.to(roomCode).emit('gameStart'); startTicker(roomCode); });
  });

  socket.on('playAI', ({difficulty}) => {
    const roomCode='AI_'+socket.id;
    const room=createRoom(roomCode);
    room.isAI=true; room.aiDifficulty=difficulty||'medium';
    if(socket.deck){ room.decks[0]=socket.deck; room.cycles[0]=buildCycleFromDeck(socket.deck); }
    room.players.push(socket.id); room.socketIds[0]=socket.id;
    socket.join(roomCode); socket.roomCode=roomCode; socket.playerIdx=0;
    dealHand(room,0); dealHand(room,1);
    socket.emit('joined',{playerIdx:0,roomCode});
    startCountdown(roomCode,()=>{ io.to(roomCode).emit('gameStart'); startTicker(roomCode); startAITicker(roomCode); });
  });

  socket.on('forfeit', () => {
    const room=rooms[socket.roomCode]; if(!room||room.gameOver) return;
    const p=socket.playerIdx; room.gameOver=true; room.winner=p===0?2:1;
    const eloResult=resolveElo(room, room.winner-1);
    const state=getPublicState(room);
    if(eloResult){
      const myChange=p===0?eloResult.p0change:eloResult.p1change;
      const oppChange=p===0?eloResult.p1change:eloResult.p0change;
      socket.emit('state',{...state,forfeit:true,eloChange:myChange});
      socket.to(socket.roomCode).emit('state',{...state,opponentForfeited:true,eloChange:oppChange});
    } else {
      socket.emit('state',{...state,forfeit:true});
      socket.to(socket.roomCode).emit('state',{...state,opponentForfeited:true});
    }
  });

  socket.on('move', ({fromRow,fromCol,toRow,toCol}) => {
    const room=rooms[socket.roomCode]; if(!room||room.gameOver) return;
    const p=socket.playerIdx; const piece=room.board[fromRow][fromCol];
    if(!piece||piece.player!==p+1) return;
    if(room.cooldowns[`${fromRow},${fromCol}`]&&room.cooldowns[`${fromRow},${fromCol}`]>Date.now()) return;
    const valid=getValidMoves(room.board,fromRow,fromCol).find(m=>m.row===toRow&&m.col===toCol); if(!valid) return;
    const cost=getMoveCostWithEffects(room,piece.type,fromRow,fromCol,toRow,toCol); if(room.elixir[p]<cost) return;
    room.elixir[p]-=cost;
    const captured=room.board[toRow][toCol];
    if(captured) room.kills[p]++; // track kills
    const cols='abcdefgh';
    const moveEntry={player:p+1,piece:piece.type,from:`${cols[fromCol]}${8-fromRow}`,to:`${cols[toCol]}${8-toRow}`,capture:captured?captured.type:null};
    if(room.board[toRow][toCol]?.type==='king'){
      room.board[toRow][toCol]=piece; room.board[fromRow][fromCol]=null;
      room.gameOver=true; room.winner=p+1;
      const eloResult=resolveElo(room,p);
      io.to(socket.roomCode).emit('move_history',moveEntry);
      const state=getPublicState(room);
      if(eloResult){
        const myChange=p===0?eloResult.p0change:eloResult.p1change;
        const oppChange=p===0?eloResult.p1change:eloResult.p0change;
        socket.emit('state',{...state,eloChange:myChange});
        socket.to(socket.roomCode).emit('state',{...state,eloChange:oppChange});
      } else {
        io.to(socket.roomCode).emit('state',state);
      }
      return;
    }
    room.board[toRow][toCol]=piece; room.board[fromRow][fromCol]=null;
    // Apply cooldown — haste gives 0s cooldown
    if(isSquareAffected(room,toRow,toCol,'haste')){
      // Remove haste from old square, keep 0 cooldown
      room.effects=room.effects.filter(e=>!(e.type==='haste'&&e.squares.some(s=>s.r===fromRow&&s.c===fromCol)));
    } else {
      room.cooldowns[`${toRow},${toCol}`]=Date.now()+COOLDOWN_MS;
    }
    checkPromotion(room,toRow,toCol);
    io.to(socket.roomCode).emit('move_history',moveEntry);
    io.to(socket.roomCode).emit('state',getPublicState(room));
  });

  socket.on('deploy', ({cardIdx,row,col}) => {
    const room=rooms[socket.roomCode]; if(!room||room.gameOver) return;
    const p=socket.playerIdx;
    const validRows=room.deployRows ? room.deployRows[p] : [p===0?7:0];
    if(!validRows.includes(row)||room.board[row][col]) return;
    const hand=room.hands[p]; if(cardIdx<0||cardIdx>=hand.length) return;
    const type=hand[cardIdx];
    if(SPELL_DATA[type]) return; // spells use castSpell handler
    const cost=PIECE_DATA[type]?.deploy; if(cost===undefined||room.elixir[p]<cost) return;
    room.elixir[p]-=cost; room.board[row][col]={type,player:p+1};
    hand.splice(cardIdx,1); dealHand(room,p);
    io.to(socket.roomCode).emit('state',getPublicState(room));
  });

  socket.on('castSpell', ({cardIdx, centerRow, centerCol}) => {
    const room=rooms[socket.roomCode]; if(!room||room.gameOver) return;
    const p=socket.playerIdx;
    const hand=room.hands[p]; if(cardIdx<0||cardIdx>=hand.length) return;
    const spellType=hand[cardIdx];
    if(!SPELL_DATA[spellType]) return; // not a spell
    const cost=SPELL_DATA[spellType].cost; if(room.elixir[p]<cost) return;
    room.elixir[p]-=cost;
    castSpell(room,spellType,centerRow,centerCol,p+1);
    hand.splice(cardIdx,1); dealHand(room,p);
    io.to(socket.roomCode).emit('spellCast',{type:spellType,centerRow,centerCol,caster:p+1});
    io.to(socket.roomCode).emit('state',getPublicState(room));
  });

  socket.on('rematch', () => {
    const room=rooms[socket.roomCode]; if(!room||!room.gameOver) return;
    if(room.isAI){
      clearInterval(room.ticker); clearTimeout(room.aiTicker); room.aiTicker=null; resetRoom(room);
      startCountdown(socket.roomCode,()=>{ socket.emit('rematchStart'); startTicker(socket.roomCode); startAITicker(socket.roomCode); });
      return;
    }
    if(!room.rematchVotes) room.rematchVotes=new Set();
    if(room.rematchVotes.has(socket.playerIdx)) return;
    room.rematchVotes.add(socket.playerIdx);
    socket.emit('rematchVote',{mine:true});
    socket.to(socket.roomCode).emit('rematchVote',{mine:false});
    if(room.rematchVotes.size>=2){
      clearInterval(room.ticker); resetRoom(room);
      startCountdown(socket.roomCode,()=>{ io.to(socket.roomCode).emit('rematchStart'); startTicker(socket.roomCode); });
    }
  });

  socket.on('disconnect', () => {
    if(matchmakingQueue?.socketId===socket.id) matchmakingQueue=null;
    const room=rooms[socket.roomCode];
    if(room && !room.isAI && !room.gameOver) {
      const disconnectedIdx = socket.playerIdx;
      const roomCode = socket.roomCode;
      // Tell remaining player
      socket.to(roomCode).emit('opponentDisconnecting', { seconds: 10 });
      room.disconnectTimer = setTimeout(() => {
        const r=rooms[roomCode]; if(!r) return;
        r.gameOver=true;
        r.winner=disconnectedIdx===0?2:1;
        const eloResult=resolveElo(r,r.winner-1);
        const state=getPublicState(r);
        // Emit to everyone still in the room
        io.to(roomCode).emit('state',{...state,opponentDisconnected:true,eloChange:eloResult?.(disconnectedIdx===0?eloResult.p1change:eloResult.p0change)||0});
        clearInterval(r.ticker);
        delete rooms[roomCode];
      }, 10000);
    } else if(room) {
      clearInterval(room.ticker);
      clearTimeout(room.aiTicker);
      clearTimeout(room.disconnectTimer);
      if(!room.isAI) io.to(socket.roomCode).emit('playerLeft');
      delete rooms[socket.roomCode];
    }
    delete playerRatings[socket.id];
  });

  socket.on('reconnectRoom', (roomCode) => {
    const room = rooms[roomCode];
    if(!room || room.gameOver) { socket.emit('error', 'Room no longer available'); return; }
    // Cancel disconnect timer
    clearTimeout(room.disconnectTimer);
    room.disconnectTimer = null;
    socket.join(roomCode);
    socket.roomCode = roomCode;
    socket.playerIdx = room.players.indexOf(socket.id) >= 0 ? room.players.indexOf(socket.id) : socket.playerIdx;
    socket.to(roomCode).emit('opponentReconnected');
    socket.emit('state', getPublicState(room));
  });
});

const PORT=3000;
server.listen(PORT,'0.0.0.0',()=>console.log(`\n✅ Chess Royale server running on port ${PORT}\n`));
