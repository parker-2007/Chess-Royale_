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
const COOLDOWN_MS = 3000; // fallback only
const GAME_DURATION = 180;
const PROMOTE_TYPES = ['queen','rook','bishop','knight'];
const PIECE_COOLDOWN = { king:2000, queen:5000, rook:4000, bishop:3000, knight:3000, pawn:2000 };
const PIECE_DATA = {
  king:   { deploy: 0,  moveCost: (d,timeLeft) => d * (timeLeft<=60 ? 3 : 6) },
  queen:  { deploy: 15, moveCost: (d) => d * 1  },
  rook:   { deploy: 8,  moveCost: (d) => d * 2  },
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
  haste:  { name:'Haste',  icon:'⚡', cost:9, area:1 },
};
const SPELL_TYPES = ['freeze','mud','haste'];
const ALL_CARDS = [...PIECE_TYPES,...SPELL_TYPES]; // 8 total, pick 6
const DEFAULT_DECK = ['pawn','knight','bishop','rook','queen','freeze'];

function ensureDeck(s) {
  if(!s.deck || s.deck.length !== 6) s.deck = DEFAULT_DECK.slice();
  return s.deck;
}

function isSpell(type){ return !!SPELL_DATA[type]; }

// CR-style cycle: shuffled deck order, played card goes to back of queue
function buildCycleFromDeck(deck) {
  return shuffle([...deck]); // just the shuffled 6-card order
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
  // 6 second cooldown on promoted piece
  room.cooldowns[`${row},${col}`]=Date.now()+6000;
  io.to(room.code).emit('promotion',{row,col,type:promoteTo,player:piece.player});
  return true;
}

// ── Room Management ────────────────────────────────────────────────────────
const rooms = {};

function createRoom(roomCode) {
  rooms[roomCode] = {
    code:roomCode, players:[], socketIds:[], board:initBoard(),
    elixir:[0,0], hands:[[],[]], 
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
  room.board=initBoard(); room.elixir=[0,0]; room.hands=[[],[]];
  room.cycles=[buildCycleFromDeck(room.decks[0]),buildCycleFromDeck(room.decks[1])];
  room.promotionQueue=buildPromotionQueue(); room.promotionIdx=0;
  room.cooldowns={}; room.gameOver=false; room.winner=null; room.rematchVotes=new Set();
  room.ticker=null; room.timeLeft=GAME_DURATION; room.startedAt=null;
  room.deployRows=[[7],[0]]; room.kills=[0,0]; room.effects=[];
  dealHand(room,0); dealHand(room,1);
}

function dealHand(room,idx) {
  // Draw from front of cycle queue until hand has 3 cards
  while(room.hands[idx].length<3 && room.cycles[idx].length>0){
    room.hands[idx].push(room.cycles[idx].shift());
  }
}

function returnCardToCycle(room,idx,cardType) {
  // Played card goes to back of cycle (CR style)
  room.cycles[idx].push(cardType);
}

function getPublicState(room) {
  const now=Date.now(), cd={};
  for(const [k,expiry] of Object.entries(room.cooldowns)){const r=expiry-now;if(r>0)cd[k]=r;}
  // Clean expired effects and send active ones
  room.effects=room.effects.filter(e=>e.expiry>now||e.type==='freeze');
  const activeEffects=room.effects.filter(e=>e.expiry>now||(e.type==='haste'&&e.movesLeft>0)).map(e=>({
    type:e.type, squares:e.squares, remaining:Math.max(0,e.expiry-now),
    movesLeft:e.movesLeft||null
  }));
  return { board:room.board, elixir:room.elixir, hands:room.hands,
           queueNexts:[room.cycles[0][0], room.cycles[1][0]],
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

function getMoveCostWithEffects(room, type, fr, fc, tr, tc, movingPlayer) {
  let cost=moveCost(type,fr,fc,tr,tc,room.timeLeft);
  const now=Date.now();
  // Mud: doubles cost for enemy pieces standing in mud zone
  const inMud=room.effects.some(e=>
    e.type==='mud' && e.expiry>now &&
    e.caster!==movingPlayer &&
    e.squares.some(s=>s.r===fr&&s.c===fc)
  );
  if(inMud) cost*=2;
  return cost;
}

function isPieceHasted(room, row, col, player) {
  return room.effects.some(e=>
    e.type==='haste' &&
    e.movesLeft>0 &&
    e.player===player &&
    e.squares.some(s=>s.r===row&&s.c===col)
  );
}

function castSpell(room, spellType, centerRow, centerCol, casterPlayer) {
  const now=Date.now();
  const squares=getAoeSquares(centerRow,centerCol,SPELL_DATA[spellType].area);
  const enemy=casterPlayer===1?2:1;

  if(spellType==='freeze'){
    squares.forEach(({r,c})=>{
      const piece=room.board[r][c];
      if(piece&&piece.player===enemy&&piece.type!=='king'){
        const key=`${r},${c}`;
        const existing=room.cooldowns[key]||now;
        room.cooldowns[key]=Math.max(existing,now)+5000;
      }
    });
    room.effects.push({type:'freeze',squares,expiry:now+5000,caster:casterPlayer});

  } else if(spellType==='mud'){
    // Mud stored as effect — getMoveCostWithEffects already checks caster, add king exclusion there
    room.effects.push({type:'mud',squares,expiry:now+10000,caster:casterPlayer});

  } else if(spellType==='haste'){
    squares.forEach(({r,c})=>{
      const piece=room.board[r][c];
      if(piece&&piece.player===casterPlayer){
        delete room.cooldowns[`${r},${c}`];
        room.effects.push({
          type:'haste',
          squares:[{r,c}],
          expiry:now+60000, // long fallback — removed by move count
          movesLeft:3,
          caster:casterPlayer,
          player:casterPlayer,
        });
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
// Random AI deck
function buildAIDeck() {
  return shuffle([...ALL_CARDS]).slice(0,6);
}

function aiTick(roomCode) {
  const room=rooms[roomCode]; if(!room||room.gameOver||!room.isAI) return;
  const AI=1, elixir=room.elixir[AI], now=Date.now();
  const settings=AI_SETTINGS[room.aiDifficulty]||AI_SETTINGS.medium;
  const hand=room.hands[AI];

  // 1. DEFENSE: check if AI king is in check, move it first
  let aiKingRow=-1,aiKingCol=-1;
  for(let r=0;r<8;r++)for(let c=0;c<8;c++)if(room.board[r][c]?.type==='king'&&room.board[r][c]?.player===2){aiKingRow=r;aiKingCol=c;}
  const inCheck=aiKingRow>=0&&(()=>{
    for(let r=0;r<8;r++)for(let c=0;c<8;c++){
      const p=room.board[r][c]; if(!p||p.player!==1) continue;
      if(getValidMoves(room.board,r,c).find(m=>m.row===aiKingRow&&m.col===aiKingCol)) return true;
    }
    return false;
  })();

  let bestMove=null, bestScore=-Infinity;

  // Escape check first
  if(inCheck&&(!room.cooldowns[`${aiKingRow},${aiKingCol}`]||room.cooldowns[`${aiKingRow},${aiKingCol}`]<=now)){
    for(const{row,col}of getValidMoves(room.board,aiKingRow,aiKingCol)){
      const kc=getMoveCostWithEffects(room,'king',aiKingRow,aiKingCol,row,col,2);
      if(elixir<kc) continue;
      let attacked=false;
      for(let r=0;r<8;r++)for(let c=0;c<8;c++){const p=room.board[r][c];if(p?.player===1&&getValidMoves(room.board,r,c).find(m=>m.row===row&&m.col===col)){attacked=true;break;}}
      const score=attacked?-500:500+(Math.random()-.5)*20;
      if(score>bestScore){bestScore=score;bestMove={fromRow:aiKingRow,fromCol:aiKingCol,toRow:row,toCol:col,cost:kc};}
    }
  }

  // 2. SPELLS
  let p1KingRow=7,p1KingCol=4;
  for(let r=0;r<8;r++)for(let c=0;c<8;c++)if(room.board[r][c]?.type==='king'&&room.board[r][c]?.player===1){p1KingRow=r;p1KingCol=c;}

  if(elixir>=4){
    for(let i=0;i<hand.length;i++){
      const type=hand[i]; if(!SPELL_DATA[type]) continue;
      const cost=SPELL_DATA[type].cost; if(elixir<cost) continue;
      if(type==='freeze'){
        let bestC=null,bestN=0;
        for(let r=0;r<8;r++)for(let c=0;c<8;c++){const n=getAoeSquares(r,c,3).filter(({r:sr,c:sc})=>room.board[sr][sc]?.player===1).length;if(n>bestN){bestN=n;bestC={r,c};}}
        if(bestN>=2){const s=bestN*80+(Math.random()-.5)*settings.randomness;if(s>bestScore){bestScore=s;bestMove={spell:true,cardIdx:i,type,centerRow:bestC.r,centerCol:bestC.c,cost};}}
      } else if(type==='mud'){
        let bestC=null,bestN=0;
        for(let r=0;r<8;r++)for(let c=0;c<8;c++){const n=getAoeSquares(r,c,2).filter(({r:sr,c:sc})=>room.board[sr][sc]?.player===1).length;if(n>bestN){bestN=n;bestC={r,c};}}
        if(bestN>=1){const s=bestN*60+(Math.random()-.5)*settings.randomness;if(s>bestScore){bestScore=s;bestMove={spell:true,cardIdx:i,type,centerRow:bestC.r,centerCol:bestC.c,cost};}}
      } else if(type==='haste'){
        let bestP=null,bestD=999;
        for(let r=0;r<8;r++)for(let c=0;c<8;c++){const p=room.board[r][c];if(p?.player===2&&p.type!=='king'&&!(room.cooldowns[`${r},${c}`]&&room.cooldowns[`${r},${c}`]>now)){const d=Math.abs(r-p1KingRow)+Math.abs(c-p1KingCol);if(d<bestD){bestD=d;bestP={r,c};}}}
        if(bestP){const s=100-bestD*5+(Math.random()-.5)*settings.randomness;if(s>bestScore){bestScore=s;bestMove={spell:true,cardIdx:i,type,centerRow:bestP.r,centerCol:bestP.c,cost};}}
      }
    }
  }

  // 3. MOVES
  for(let r=0;r<8;r++)for(let c=0;c<8;c++){
    const piece=room.board[r][c]; if(!piece||piece.player!==2) continue;
    if(room.cooldowns[`${r},${c}`]&&room.cooldowns[`${r},${c}`]>now) continue;
    for(const{row,col}of getValidMoves(room.board,r,c)){
      const cost=getMoveCostWithEffects(room,piece.type,r,c,row,col,2); if(elixir<cost) continue;
      let score=0; const target=room.board[row][col];
      if(target) score+=PIECE_VALUE[target.type]*100;
      if(target?.type==='king') score+=100000;
      score+=(Math.abs(r-p1KingRow)+Math.abs(c-p1KingCol)-Math.abs(row-p1KingRow)-Math.abs(col-p1KingCol))*settings.aggressiveness;
      if(room.aiDifficulty==='hard'){let th=false;for(let rr=0;rr<8;rr++)for(let cc=0;cc<8;cc++){const op=room.board[rr][cc];if(op?.player===1&&getValidMoves(room.board,rr,cc).find(m=>m.row===row&&m.col===col)){th=true;break;}}if(th)score-=PIECE_VALUE[piece.type]*40;}
      score-=cost*0.5; score+=(Math.random()-.5)*settings.randomness;
      if(score>bestScore){bestScore=score;bestMove={fromRow:r,fromCol:c,toRow:row,toCol:col,cost};}
    }
  }

  // 4. DEPLOY
  for(let i=0;i<hand.length;i++){
    const type=hand[i]; if(SPELL_DATA[type]) continue;
    const cost=PIECE_DATA[type]?.deploy;
    if(elixir<cost+(room.aiDifficulty==='easy'?5:3)) continue;
    const deployRow=room.deployRows[AI][0];
    const emptyCols=[];for(let c=0;c<8;c++)if(!room.board[deployRow][c])emptyCols.push(c);
    if(!emptyCols.length) continue;
    emptyCols.sort((a,b)=>Math.abs(a-p1KingCol)-Math.abs(b-p1KingCol));
    const ds=PIECE_VALUE[type]*10-cost*0.5+(Math.random()-.5)*settings.randomness;
    if(ds>bestScore){bestScore=ds;bestMove={deploy:true,cardIdx:i,row:deployRow,col:emptyCols[0],cost};}
  }

  if(!bestMove) return;
  if(bestMove.spell){
    room.elixir[AI]-=bestMove.cost;
    castSpell(room,bestMove.type,bestMove.centerRow,bestMove.centerCol,2);
    hand.splice(bestMove.cardIdx,1); returnCardToCycle(room,AI,bestMove.type); dealHand(room,AI);
    io.to(roomCode).emit('spellCast',{type:bestMove.type,centerRow:bestMove.centerRow,centerCol:bestMove.centerCol,caster:2});
  } else if(bestMove.deploy){
    const type=hand[bestMove.cardIdx];
    room.elixir[AI]-=bestMove.cost;
    room.board[bestMove.row][bestMove.col]={type,player:2};
    room.cooldowns[`${bestMove.row},${bestMove.col}`]=now+1500;
    hand.splice(bestMove.cardIdx,1); returnCardToCycle(room,AI,type); dealHand(room,AI);
  } else {
    room.elixir[AI]-=bestMove.cost;
    const piece=room.board[bestMove.fromRow][bestMove.fromCol];
    if(room.board[bestMove.toRow][bestMove.toCol]?.type==='king'){
      room.board[bestMove.toRow][bestMove.toCol]=piece;
      room.board[bestMove.fromRow][bestMove.fromCol]=null;
      room.gameOver=true; room.winner=2;
    } else {
      if(room.board[bestMove.toRow][bestMove.toCol]) room.kills[AI]++;
      room.board[bestMove.toRow][bestMove.toCol]=piece;
      room.board[bestMove.fromRow][bestMove.fromCol]=null;
      const wasHasted=isPieceHasted(room,bestMove.fromRow,bestMove.fromCol,2);
      if(wasHasted){
        room.effects=room.effects.map(e=>{
          if(e.type==='haste'&&e.player===2&&e.squares.some(s=>s.r===bestMove.fromRow&&s.c===bestMove.fromCol))
            return {...e,squares:[{r:bestMove.toRow,c:bestMove.toCol}],movesLeft:(e.movesLeft||1)-1};
          return e;
        }).filter(e=>e.type!=='haste'||e.movesLeft>0);
      } else {
        room.cooldowns[`${bestMove.toRow},${bestMove.toCol}`]=now+(PIECE_COOLDOWN[piece.type]||COOLDOWN_MS);
      }
      delete room.cooldowns[`${bestMove.fromRow},${bestMove.fromCol}`];
      checkPromotion(room,bestMove.toRow,bestMove.toCol);
    }
  }
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
  console.log('connect', socket.id);
  socket.on('error', (err) => console.error('socket error', socket.id, err));

  socket.on('submitDeck', (deck) => {
    if(!Array.isArray(deck)||deck.length!==6) return;
    if(!deck.every(c=>ALL_CARDS.includes(c))) return;
    socket.deck = deck;
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
      else { room.decks[0]=DEFAULT_DECK.slice(); room.cycles[0]=buildCycleFromDeck(DEFAULT_DECK); }
      if(socket.deck){ room.decks[1]=socket.deck; room.cycles[1]=buildCycleFromDeck(socket.deck); }
      else { room.decks[1]=DEFAULT_DECK.slice(); room.cycles[1]=buildCycleFromDeck(DEFAULT_DECK); }

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
    room.decks[0]=socket.deck||DEFAULT_DECK.slice(); room.cycles[0]=buildCycleFromDeck(room.decks[0]);
    room.players.push(socket.id); room.socketIds[0] = socket.id;
    socket.join(roomCode); socket.roomCode=roomCode; socket.playerIdx=0;
    dealHand(room,0); dealHand(room,1);
    socket.emit('joined',{playerIdx:0,roomCode});
  });

  socket.on('joinRoom', (roomCode) => {
    const room = rooms[roomCode];
    if (!room) { socket.emit('error','Room not found'); return; }
    if (room.players.length >= 2) { socket.emit('error','Room is full'); return; }
    room.decks[1]=socket.deck||DEFAULT_DECK.slice(); room.cycles[1]=buildCycleFromDeck(room.decks[1]);
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
    const aiDeck=buildAIDeck();
    room.decks[1]=aiDeck; room.cycles[1]=buildCycleFromDeck(aiDeck);
    room.decks[0]=socket.deck||DEFAULT_DECK.slice(); room.cycles[0]=buildCycleFromDeck(room.decks[0]);
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
    const cost=getMoveCostWithEffects(room,piece.type,fromRow,fromCol,toRow,toCol,p+1); if(room.elixir[p]<cost) return;
    room.elixir[p]-=cost;
    const captured=room.board[toRow][toCol];
    if(captured){
      room.kills[p]++;
      // Remove any spell effects on the captured square
      room.effects=room.effects.filter(e=>!e.squares.some(s=>s.r===toRow&&s.c===toCol)||e.squares.length>1);
      // For multi-square effects, remove just that square
      room.effects=room.effects.map(e=>({...e,squares:e.squares.filter(s=>!(s.r===toRow&&s.c===toCol))})).filter(e=>e.squares.length>0);
    }
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
    const wasHasted=isPieceHasted(room,fromRow,fromCol,p+1);
    if(wasHasted){
      room.effects=room.effects.map(e=>{
        if(e.type==='haste'&&e.player===p+1&&e.squares.some(s=>s.r===fromRow&&s.c===fromCol)){
          const newMovesLeft=(e.movesLeft||1)-1;
          // Move effect to new square, decrement counter
          return {...e, squares:[{r:toRow,c:toCol}], movesLeft:newMovesLeft};
        }
        return e;
      }).filter(e=>e.type!=='haste'||e.movesLeft>0);
    } else {
      room.cooldowns[`${toRow},${toCol}`]=Date.now()+(PIECE_COOLDOWN[piece.type]||COOLDOWN_MS);
    }
    delete room.cooldowns[`${fromRow},${fromCol}`];
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
    room.cooldowns[`${row},${col}`]=Date.now()+1500; // 1.5s deploy cooldown
    hand.splice(cardIdx,1); returnCardToCycle(room,p,type); dealHand(room,p);
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
    hand.splice(cardIdx,1); returnCardToCycle(room,p,spellType); dealHand(room,p);
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

const PORT = process.env.PORT || 3000;
server.listen(PORT, '0.0.0.0', () => console.log(`\n✅ Chess Royale running on port ${PORT}\n`));
