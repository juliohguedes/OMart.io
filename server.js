require('dotenv').config();

const express = require("express");
const http = require("http");
const { Server } = require("socket.io");
const fs = require("fs");
const path = require("path");
const PORT = process.env.PORT || 3000;
const HOST = "0.0.0.0"; // Railway/containers: expor em todas as interfaces
const SOCKET_PING_INTERVAL_MS = 25000;
const SOCKET_PING_TIMEOUT_MS = 6 * 60 * 1000; // mobile em segundo plano nao cai rapido

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
  pingInterval: SOCKET_PING_INTERVAL_MS,
  pingTimeout: SOCKET_PING_TIMEOUT_MS,
});

app.use(express.static(path.join(__dirname, "public")));

const rooms = {};
const DEFAULT_ROOM_LIMIT = 12;
const ROOM_LIMIT_BY_ROOM_TIER = {
  3: 10,
  6: 12,
  9: 15,
};
const DEBUG_GUARDS = true;
const ENFORCE_GUARDS = true; // se false, não bloquear nada (só observabilidade)

const roomState = {}; // { [roomId]: "lobby" | "playing" }
const roomDrawerIndex = {}; // { [roomId]: number }
const roomDrawerClientId = {}; // { [roomId]: string|null } -> fonte de verdade do desenhista
const roomDrawerOrder = {}; // { [roomId]: string[] } -> fila fixa por ordem de entrada
const roomTimers = {}; // { [roomId]: { phaseTimeout?: any, tickInterval?: any } }

const ROUND_MS = 120000; // 120s
const BREAK_MS = 15000; // 15s
const VICTORY_MS = 30000; // 30s
const RECONNECT_GRACE_MS = 30000; // 30s
const DISCONNECT_ANNOUNCE_DELAY_MS = 5000; // evita "saiu" em refresh/reconexao rapida
const RECONNECT_CLEANUP_MS = 2000; // 2s
const AFK_IDLE_MS = 5 * 60 * 1000; // 5 min without interaction
const AFK_CONFIRM_MS = 30 * 1000; // 30s to confirm "still here"
const DRAW_ACTION_BATCH_MAX = 80; // server-side hard cap per packet
const LOBBY_WATCHERS_ROOM = "__lobby_watchers__";
const CHAT_CONSECUTIVE_LIMIT = 12; // consecutive messages by same player
const CHAT_CONSECUTIVE_UNLOCK_MS = 60 * 1000; // 1 min auto-unlock

const roomRoundEndsAt = {}; // { [roomId]: number }
const roomWord = {}; // { [roomId]: string }

// fase da sala: "round" | "break" | "victory"
const roomPhase = {}; // { [roomId]: "round" | "break" | "victory" }

// desenhista precisa clicar "Desenhar"
const roomDrawEnabled = {}; // { [roomId]: boolean }

const ROOM_STATE = {
  LOBBY: "LOBBY",
  IN_ROUND: "IN_ROUND",
  ROUND_END: "ROUND_END",
  GAME_END: "GAME_END",
};

// snapshot do canvas (late join)
const roomCanvasSnapshot = {}; // { [roomId]: string|null }
const roomGuessHistory = {}; // { [roomId]: Array<payload> }
const roomTalkHistory = {}; // { [roomId]: Array<payload> }
const ROOM_CHAT_HISTORY_LIMIT = 200;

// reconexão (nick -> dados por 60s)
const roomGhosts = {}; // { [roomId]: { [normNick]: { score:number, wins:number, expiresAt:number } } }

// anti-spam por socket
const spamState = {}; // { [socketId]: { lastGuess?:string, guessRepeat?:number, lastTalkAt?:number, talkBurst?:number } }

// anti-flood por sequência em chats (talk/guess)
const roomChatConsecutive = {};
// { [roomId]: { talk:{ lastKey:string|null, streak:number, blocked:{ [playerKey]: number } }, guess:{...} } }

// anti-vazamento "picado" por sala/socket
const roomTalkLeakBuffer = {};
// { [roomId]: { [socketId]: Array<{ ts:number, txt:string }> } }
const TALK_LEAK_WINDOW_MS = 6000;
const TALK_LEAK_MAX_MSG = 10;
const TALK_LEAK_SHORT_MAX = 3;

// -------------------- HINT SYSTEM (50% - tamanho conta) --------------------
const roomHint = {};
// { [roomId]: { stage:number, mask:string|null, revealedIdx:Set<number>, maxHints:number, totalLetters:number } }

// -------------------- REPORT DRAWING --------------------
// votos de denúncia por rodada
const roomReports = {};
// { [roomId]: { voters:Set<socketId> } }

const roomReportIpLocks = {};
// { [roomId]: Set<ipKey> } (apenas da rodada atual)

// quantas vezes o desenho de um player foi cancelado por denúncia
const roomDrawerReportCancels = {};
// { [roomId]: { [drawerId]: number } }

// quando bater 2 cancelamentos, ele perde a PRÓXIMA vez de desenhar
const roomSkipNextDraw = {};
// { [roomId]: { [drawerId]: boolean } }

// snapshot de score no início do round (pra desfazer pontos se denunciar)
const roomScoreSnapshot = {};
// { [roomId]: { [socketId]: number } }

// timer de 15s pro desenhista decidir
const roomDrawerDecisionTimer = {};
// { [roomId]: any }

function guardWarn(tag, data = {}) {
  if (!DEBUG_GUARDS) return;
  console.warn(`[GUARD] ${tag}`, data);
}

function ensureRoomGuardState(roomId) {
  if (!rooms[roomId]) return ROOM_STATE.LOBBY;
  const cur = String(rooms[roomId].state || "");
  if (!Object.values(ROOM_STATE).includes(cur)) {
    rooms[roomId].state = ROOM_STATE.LOBBY;
  }
  return rooms[roomId].state;
}

function setRoomGuardState(roomId, nextState) {
  if (!rooms[roomId]) return;
  rooms[roomId].state = nextState;
}

function guardCanStartRound(roomId, eventName, socket, nick) {
  const state = ensureRoomGuardState(roomId);
  const count = getConnectedRoomPlayers(roomId).length;
  const ok = count >= 2 && state !== ROOM_STATE.IN_ROUND;
  if (!ok) {
    guardWarn("invalid startRound", {
      roomId,
      eventName,
      state,
      playerId: socket?.id || null,
      nick: nick || null,
      players: count,
    });
  }
  return ok || !ENFORCE_GUARDS;
}

function guardCanGuess(roomId, eventName, socket, nick) {
  const state = ensureRoomGuardState(roomId);
  const ok = state === ROOM_STATE.IN_ROUND;
  if (!ok) {
    guardWarn("invalid guess state", {
      roomId,
      eventName,
      state,
      playerId: socket?.id || null,
      nick: nick || null,
    });
  }
  return ok || !ENFORCE_GUARDS;
}

function guardCanDrawEvent(roomId, eventName, socket, nick) {
  const state = ensureRoomGuardState(roomId);
  const drawer = currentDrawer(roomId);
  const drawerSocketId = getPlayerSocketId(drawer);
  const ok = state === ROOM_STATE.IN_ROUND && !!drawer && drawerSocketId === socket?.id;
  if (!ok) {
    guardWarn("invalid draw/canvas event", {
      roomId,
      eventName,
      state,
      playerId: socket?.id || null,
      nick: nick || null,
      drawerId: drawerSocketId,
    });
  }
  return ok || !ENFORCE_GUARDS;
}

function resetReports(roomId) {
  roomReports[roomId] = { voters: new Set() };
}

function clearReports(roomId) {
  delete roomReports[roomId];
}

function clearReportIpLocks(roomId) {
  delete roomReportIpLocks[roomId];
}

function normalizeIp(rawIp) {
  let ip = String(rawIp || "").trim();
  if (!ip) return "";
  if (ip.includes(",")) ip = ip.split(",")[0].trim();
  if (ip.startsWith("::ffff:")) ip = ip.slice(7);
  return ip;
}

function getReportIpKey(socket) {
  const forwarded = socket?.handshake?.headers?.["x-forwarded-for"];
  const forwardedIp = Array.isArray(forwarded) ? forwarded[0] : forwarded;
  const directIp = socket?.handshake?.address || socket?.conn?.remoteAddress || "";

  const ip = normalizeIp(forwardedIp || directIp);
  if (ip) return `ip:${ip}`;

  const cid = normalizeClientId(socket?.data?.clientId || "");
  if (cid) return `cid:${cid}`;

  const sid = String(socket?.id || "").trim();
  if (sid) return `sid:${sid}`;
  return "";
}

function hasReportedByIpInRound(roomId, ipKey) {
  if (!ipKey) return false;
  const set = roomReportIpLocks[roomId];
  return !!(set && set.has(ipKey));
}

function markReportedByIpInRound(roomId, ipKey) {
  if (!ipKey) return;
  if (!roomReportIpLocks[roomId]) roomReportIpLocks[roomId] = new Set();
  roomReportIpLocks[roomId].add(ipKey);
}

function getReportNeeded(roomId) {
  const players = rooms[roomId] || [];
  const n = players.length;
  if (n <= 0) return 1;

  // regra: se total é ímpar, desenhista não conta (ex: 5 -> base 4)
  const base = n % 2 === 1 ? n - 1 : n;

  // 50% (arredondando pra cima)
  return Math.max(1, Math.ceil(base / 2));
}

function markDrawerCancel(roomId, drawerId) {
  if (!drawerId) return;

  if (!roomDrawerReportCancels[roomId]) roomDrawerReportCancels[roomId] = {};
  if (!roomSkipNextDraw[roomId]) roomSkipNextDraw[roomId] = {};

  const cur = Number(roomDrawerReportCancels[roomId][drawerId] || 0) + 1;
  roomDrawerReportCancels[roomId][drawerId] = cur;

  // a cada 2 cancelamentos, perde a próxima vez
  if (cur >= 2 && cur % 2 === 0) {
    roomSkipNextDraw[roomId][drawerId] = true;
  }
}

function shouldSkipDrawer(roomId, drawerId) {
  return !!(roomSkipNextDraw[roomId] && roomSkipNextDraw[roomId][drawerId]);
}

function clearSkipDrawer(roomId, drawerId) {
  if (roomSkipNextDraw[roomId]) delete roomSkipNextDraw[roomId][drawerId];
}

function takeScoreSnapshot(roomId) {
  const ps = rooms[roomId] || [];
  roomScoreSnapshot[roomId] = {};
  for (const p of ps) {
    const key = String(p.clientId || p.id || "").trim();
    if (!key) continue;
    roomScoreSnapshot[roomId][key] = Number(p.score || 0);
  }
}

function restoreScoreSnapshot(roomId) {
  const snap = roomScoreSnapshot[roomId];
  if (!snap) return;

  const ps = rooms[roomId] || [];
  for (const p of ps) {
    const key = String(p.clientId || p.id || "").trim();
    if (!key) continue;
    if (snap[key] != null) p.score = Number(snap[key]);
  }
  emitScores(roomId);
}

function clearDrawerDecisionTimer(roomId) {
  if (roomDrawerDecisionTimer[roomId]) clearTimeout(roomDrawerDecisionTimer[roomId]);
  delete roomDrawerDecisionTimer[roomId];
}

function startDrawerDecisionTimer(roomId) {
  clearDrawerDecisionTimer(roomId);

  if (!rooms[roomId] || roomState[roomId] !== "playing") return;
  if (roomPhase[roomId] !== "round") return;
  if (roomDrawEnabled[roomId] === true) return;

  const d = currentDrawer(roomId);
  if (!d) return;
  const drawerClientId = d.clientId || null;
  const localRoundId = ensureRoomRoundId(roomId);

  const timerRef = setTimeout(() => {
    const roomRoundId = ensureRoomRoundId(roomId);
    if (roomRoundId !== localRoundId) {
      guardWarn("stale timer", { roomId, localRoundId, roomRoundId, timer: "drawerDecision" });
      clearTimeout(timerRef);
      if (roomDrawerDecisionTimer[roomId] === timerRef) delete roomDrawerDecisionTimer[roomId];
      return;
    }

    // revalida estado ao expirar
    if (!rooms[roomId] || roomState[roomId] !== "playing") return;
    if (roomPhase[roomId] !== "round") return;
    if (roomDrawEnabled[roomId] === true) return;

    const cur = currentDrawer(roomId);
    if (!cur || (cur.clientId || null) !== drawerClientId) return;
    const curSocketId = getPlayerSocketId(cur);

    // ✅ todos veem (azul)
    emitSystemGuess(roomId, `⚠️ ${cur.nick} perdeu a vez!`);
    // ✅ só ele vê extra (azul)
    if (curSocketId) io.to(curSocketId).emit("guessMessage", {
      roomId,
      nick: "Sistema",
      text: "Você perdeu a vez!",
      kind: "systemBlue",
      ts: Date.now(),
    });

    // limpa e vai pro intervalo
    startBreak(roomId, "AUTO_SKIP", {
      actorNick: cur.nick,
      actorIsAdmin: isAdminPlayer(cur),
    });
  }, 15000);
  roomDrawerDecisionTimer[roomId] = timerRef;
}

function isLetter(ch) {
  return /\p{L}/u.test(ch);
}

function calcMaxHints(totalLetters) {
  if (!totalLetters || totalLetters <= 0) return 0;
  return Math.floor(totalLetters * 0.5);
}

function countLetters(word) {
  const chars = Array.from(String(word || ""));
  let total = 0;
  for (const ch of chars) if (isLetter(ch)) total++;
  return total;
}

function findFirstLetterIndex(word) {
  const chars = Array.from(String(word || ""));
  for (let i = 0; i < chars.length; i++) {
    if (isLetter(chars[i])) return i;
  }
  return -1;
}

function computeBlanksMask(word) {
  const chars = Array.from(String(word || ""));
  const maskChars = chars.map((ch) => (isLetter(ch) ? "_" : ch));
  return maskChars.join(" ");
}

function computeMask(word, revealedIdx) {
  const chars = Array.from(String(word || ""));
  const maskChars = chars.map((ch, i) => {
    if (!isLetter(ch)) return ch;
    return revealedIdx.has(i) ? ch : "_";
  });
  return maskChars.join(" ");
}

function usedHintsCount(h) {
  if (!h) return 0;
  if (h.stage === 0) return 0;
  if (h.stage === 1) return 1;
  return 1 + h.revealedIdx.size;
}

function emitHint(roomId) {
  const h = roomHint[roomId];
  if (!h) return;

  io.to(roomId).emit("hintUpdate", {
    roomId,
    mask: h.stage === 0 ? null : h.mask,
    revealed: usedHintsCount(h),
    maxReveal: h.maxHints,
  });
}

function resetHintForRoom(roomId) {
  const word = roomWord[roomId] || "";
  if (!word) {
    delete roomHint[roomId];
    io.to(roomId).emit("hintUpdate", { roomId, mask: null, revealed: 0, maxReveal: 0 });
    return;
  }

  const totalLetters = countLetters(word);
  const maxHints = calcMaxHints(totalLetters);

  roomHint[roomId] = {
    stage: 0,
    mask: null,
    revealedIdx: new Set(),
    maxHints,
    totalLetters,
  };

  emitHint(roomId);
}

function revealHintStep(roomId) {
  const word = roomWord[roomId] || "";
  if (!word) return { ok: false, reason: "NO_WORD" };

  const h = roomHint[roomId];
  if (!h) return { ok: false, reason: "NO_HINT" };

  if (h.maxHints <= 0) return { ok: false, reason: "LIMIT" };

  const used = usedHintsCount(h);
  if (used >= h.maxHints) return { ok: false, reason: "LIMIT" };

  if (h.stage === 0) {
    h.stage = 1;
    h.mask = computeBlanksMask(word);
    emitHint(roomId);
    return { ok: true };
  }

  const chars = Array.from(word);

  // 2a dica: sempre revela a primeira letra da palavra (primeira letra valida).
  if (h.stage === 1) {
    const firstLetterIdx = findFirstLetterIndex(word);
    if (firstLetterIdx < 0) return { ok: false, reason: "NO_CANDIDATE" };

    h.revealedIdx.add(firstLetterIdx);
    h.stage = 2;
    h.mask = computeMask(word, h.revealedIdx);
    emitHint(roomId);
    return { ok: true };
  }

  const candidates = [];
  for (let i = 0; i < chars.length; i++) {
    if (!isLetter(chars[i])) continue;
    if (!h.revealedIdx.has(i)) candidates.push(i);
  }

  if (!candidates.length) return { ok: false, reason: "NO_CANDIDATE" };

  const pick = candidates[Math.floor(Math.random() * candidates.length)];
  h.revealedIdx.add(pick);
  h.stage = 2;
  h.mask = computeMask(word, h.revealedIdx);

  emitHint(roomId);
  return { ok: true };
}

// -------------------- SCORE SYSTEM --------------------
const WIN_SCORE_BY_ROOM_TIER = {
  3: 120,
  6: 150,
  9: 175,
};
const DEFAULT_WIN_SCORE = 150;

function getRoomTierFromRoomId(roomId) {
  const parts = String(roomId || "").trim().split(/\s+/);
  const tier = Number(parts[1] || "");
  return Number.isFinite(tier) ? tier : null;
}

function getWinScoreForRoom(roomId) {
  const tier = getRoomTierFromRoomId(roomId);
  return WIN_SCORE_BY_ROOM_TIER[tier] || DEFAULT_WIN_SCORE;
}

function getRoomPlayerLimitForRoom(roomId) {
  const tier = getRoomTierFromRoomId(roomId);
  return ROOM_LIMIT_BY_ROOM_TIER[tier] || DEFAULT_ROOM_LIMIT;
}

// quem já acertou na rodada (ordem importa)
const roomRoundGuessed = {}; // { [roomId]: Set<socketId> }
const roomRoundHasCorrect = {}; // { [roomId]: boolean }

function ensureRoomRoundId(roomId) {
  if (!rooms[roomId]) return 0;
  if (!Number.isInteger(rooms[roomId].roundId)) rooms[roomId].roundId = 0;
  return rooms[roomId].roundId;
}

function startNewRoundState(roomId) {
  if (!rooms[roomId]) return 0;
  const nextRound = ensureRoomRoundId(roomId) + 1;
  rooms[roomId].roundId = nextRound;
  clearGuessedStateForRound(roomId);
  roomRoundHasCorrect[roomId] = false;
  return nextRound;
}

function markRoundFirstCorrect(roomId, nick = null) {
  if (roomRoundHasCorrect[roomId]) return false;
  roomRoundHasCorrect[roomId] = true;
  io.to(roomId).emit("roundFirstCorrect", { roomId, nick: nick || null });
  return true;
}

function emitRoundFirstCorrectStateToSocket(socket, roomId) {
  if (!socket || !roomId) return;
  if (roomPhase[roomId] !== "round") return;
  if (!roomRoundHasCorrect[roomId]) return;
  socket.emit("roundFirstCorrect", { roomId, nick: null, already: true });
}

function playerGuessedThisRound(roomId, socketId) {
  const roundId = ensureRoomRoundId(roomId);
  const p = findPlayerBySocket(roomId, socketId);
  if (!p) return false;
  return Number(p.guessedRoundId) === roundId;
}

function markPlayerGuessedThisRound(roomId, socketId) {
  const roundId = ensureRoomRoundId(roomId);
  const p = findPlayerBySocket(roomId, socketId);
  if (p) p.guessedRoundId = roundId;
  if (!roomRoundGuessed[roomId]) roomRoundGuessed[roomId] = new Set();
  const key = String(p?.clientId || socketId || "").trim();
  if (key) roomRoundGuessed[roomId].add(key);
}

function clearGuessedStateForRound(roomId) {
  const ps = rooms[roomId] || [];
  for (const p of ps) p.guessedRoundId = null;
  roomRoundGuessed[roomId] = new Set();
}

function ensureScore(roomId, socketId) {
  const p = findPlayerBySocket(roomId, socketId);
  if (p) {
    if (typeof p.score !== "number") p.score = 0;
    if (typeof p.wins !== "number") p.wins = 0;
  }
  return p || null;
}

function getNickBySocketInRoom(roomId, socketId) {
  const p = findPlayerBySocket(roomId, socketId);
  return p?.nick || "???";
}

function buildRankPayload(roomId) {
  const ps = getConnectedRoomPlayers(roomId);
  const roundId = ensureRoomRoundId(roomId);
  const isRoundPhase = roomPhase[roomId] === "round";
  const drawer = currentDrawer(roomId);
  const drawerCid = drawer?.clientId || roomDrawerClientId[roomId] || null;

  const payload = ps.map((p) => ({
    id: p.id,
    nick: p.nick,
    score: Number(p.score || 0),
    wins: Number(p.wins || 0),
    guessed: isRoundPhase && Number(p.guessedRoundId) === roundId,
    isDrawer: isRoundPhase && !!drawerCid && String(p.clientId || "") === String(drawerCid),
    isAdmin: isAdminPlayer(p),
  }));

  payload.sort((a, b) => b.score - a.score || b.wins - a.wins || a.nick.localeCompare(b.nick));
  return payload;
}

function emitScores(roomId) {
  io.to(roomId).emit("scoreUpdate", { roomId, players: buildRankPayload(roomId) });
}

function basePointsForGuesser(order1based) {
  if (order1based <= 9) return 11 - order1based;
  return 1;
}

function basePointsForDrawer(order1based) {
  return order1based === 1 ? 11 : 2;
}

function hintMultiplierNow(roomId) {
  const usedHintsNow = usedHintsCount(roomHint[roomId]);
  const mult = 1 - 0.1 * usedHintsNow;
  return Math.max(0, mult);
}

function pickWinnerNick(roomId) {
  const ps = rooms[roomId] || [];
  const winScore = getWinScoreForRoom(roomId);
  const winners = ps
    .map((p) => ({ id: p.id, nick: p.nick, score: Number(p.score || 0) }))
    .filter((p) => p.score >= winScore);

  if (!winners.length) return null;

  winners.sort((a, b) => b.score - a.score || a.nick.localeCompare(b.nick));
  return winners[0].nick;
}

function pickWinnerId(roomId) {
  const ps = rooms[roomId] || [];
  const winScore = getWinScoreForRoom(roomId);
  const winners = ps
    .map((p) => ({ id: p.id, nick: p.nick, score: Number(p.score || 0) }))
    .filter((p) => p.score >= winScore);

  if (!winners.length) return null;

  winners.sort((a, b) => b.score - a.score || a.nick.localeCompare(b.nick));
  return winners[0].id;
}

function awardPointsForCorrectGuess(roomId, guesserSocketId) {
  const players = rooms[roomId] || [];
  if (!players.length) return { guesserAdd: 0, drawerAdd: 0, order: 0 };

  ensureScore(roomId, guesserSocketId);

  const drawer = currentDrawer(roomId);
  const drawerCid = drawer?.clientId || null;

  if (playerGuessedThisRound(roomId, guesserSocketId)) return { guesserAdd: 0, drawerAdd: 0, order: 0 };

  const roundId = ensureRoomRoundId(roomId);
  const order =
    players.filter((p) => String(p.clientId || "") !== String(drawerCid || "") && Number(p.guessedRoundId) === roundId).length + 1;
  const mult = hintMultiplierNow(roomId);

  const guesserAdd = Math.floor(basePointsForGuesser(order) * mult);
  const drawerAdd = Math.floor(basePointsForDrawer(order) * mult);

  const guesserP = ensureScore(roomId, guesserSocketId);
  if (guesserP) guesserP.score = Number(guesserP.score || 0) + guesserAdd;

  if (drawer) {
    if (typeof drawer.score !== "number") drawer.score = 0;
    drawer.score = Number(drawer.score || 0) + drawerAdd;
  }

  markPlayerGuessedThisRound(roomId, guesserSocketId);

  emitScores(roomId);

  return { guesserAdd, drawerAdd, order };
}

function allNonDrawerGuessed(roomId) {
  const players = rooms[roomId] || [];
  if (players.length < 2) return false;

  const drawer = currentDrawer(roomId);
  const drawerCid = drawer?.clientId || null;

  const totalGuessers = players.filter((p) => String(p.clientId || "") !== String(drawerCid || "")).length;
  if (totalGuessers <= 0) return false;

  const roundId = ensureRoomRoundId(roomId);
  const guessedCount =
    players.filter((p) => String(p.clientId || "") !== String(drawerCid || "") && Number(p.guessedRoundId) === roundId).length;

  return guessedCount >= totalGuessers;
}

// -------------------- CHAT / GUESS HELPERS --------------------
function normNick(nick) {
  return String(nick || "").trim().toLowerCase();
}

const ADMIN_NICK = String(process.env.ADMIN_NICK || "Miau-Sensei").trim();
const ADMIN_KEY = String(process.env.ADMIN_KEY || "19082005").trim();
const ADMIN_NICK_NORM = normNick(ADMIN_NICK);

function isReservedAdminNick(nick) {
  if (!ADMIN_NICK_NORM) return false;
  return normNick(nick) === ADMIN_NICK_NORM;
}

function hasValidAdminKey(adminKey) {
  if (!ADMIN_NICK_NORM) return true;
  if (!ADMIN_KEY) return false;
  return String(adminKey || "").trim() === ADMIN_KEY;
}

function isAdminPlayer(player) {
  if (!player) return false;
  if (player.isAdmin === true) return true;
  return isReservedAdminNick(player.nick);
}

function emitNickBlocked(socket, roomId, nick, reason = "ADMIN_KEY_REQUIRED") {
  socket.emit("nickBlocked", {
    roomId: String(roomId || "").trim(),
    nick: String(nick || "").trim(),
    reason,
  });
}

function normalizeClientId(clientId) {
  return String(clientId || "").trim();
}

// acerto EXATO: mantém acento/hífen/espaço (mas ignora case e trim)
function normalizeExact(s) {
  return String(s || "")
    .normalize("NFC")
    .replace(/[\u200B-\u200D\uFEFF]/g, "")
    .replace(/\u00A0/g, " ")
    .trim()
    .replace(/\s+/g, " ")
    .toLocaleLowerCase("pt-BR");
}

// para "perto": remove acento e símbolos
function normalizeNear(s) {
  return String(s || "")
    .trim()
    .toLowerCase()
    .normalize("NFD")
    .replace(/[\u0300-\u036f]/g, "")
    .replace(/[^a-z0-9]+/gi, "");
}

function normalizeLeak(s) {
  return String(s || "")
    .toLowerCase()
    .normalize("NFD")
    .replace(/[\u0300-\u036f]/g, "")
    .replace(/[^\p{L}\p{N}]/gu, "");
}

function clearTalkLeakBuffer(roomId) {
  delete roomTalkLeakBuffer[roomId];
}

function clearTalkLeakBufferForSocket(roomId, socketId) {
  if (!roomTalkLeakBuffer[roomId]) return;
  delete roomTalkLeakBuffer[roomId][socketId];
  if (Object.keys(roomTalkLeakBuffer[roomId]).length === 0) {
    delete roomTalkLeakBuffer[roomId];
  }
}

function appendTalkLeakChunk(roomId, socketId, normalizedText, now) {
  if (!normalizedText) return [];
  if (!roomTalkLeakBuffer[roomId]) roomTalkLeakBuffer[roomId] = {};
  if (!roomTalkLeakBuffer[roomId][socketId]) roomTalkLeakBuffer[roomId][socketId] = [];

  const arr = roomTalkLeakBuffer[roomId][socketId];
  arr.push({ ts: now, txt: normalizedText });

  const cutoff = now - TALK_LEAK_WINDOW_MS;
  roomTalkLeakBuffer[roomId][socketId] = arr
    .filter((x) => x && typeof x.txt === "string" && x.txt && x.ts >= cutoff)
    .slice(-TALK_LEAK_MAX_MSG);

  return roomTalkLeakBuffer[roomId][socketId];
}

function hasRelevantLeakInConcat(answerNorm, concatNorm) {
  if (!answerNorm || !concatNorm) return false;
  if (concatNorm.includes(answerNorm)) return true;

  const minFragLen = Math.max(4, Math.ceil(answerNorm.length * 0.7));
  if (answerNorm.length < minFragLen + 1) return false;

  for (let i = 0; i <= answerNorm.length - minFragLen; i++) {
    const frag = answerNorm.slice(i, i + minFragLen);
    if (frag && concatNorm.includes(frag)) return true;
  }

  return false;
}

function isChunkedAnswerLeak(roomId, socketId, text, now = Date.now()) {
  const answerNorm = normalizeLeak(roomWord[roomId] || "");
  if (!answerNorm) return false;

  const msgNorm = normalizeLeak(text);
  if (!msgNorm) return false;

  const entries = appendTalkLeakChunk(roomId, socketId, msgNorm, now);
  if (!entries.length) return false;

  const shortConcat = entries
    .filter((x) => x.txt.length <= TALK_LEAK_SHORT_MAX)
    .map((x) => x.txt)
    .join("");

  if (!shortConcat) return false;
  return hasRelevantLeakInConcat(answerNorm, shortConcat);
}

function isCorrectGuess(roomId, text) {
  const w = roomWord[roomId] || "";
  if (!w) return false;
  const a = normalizeExact(text);
  const b = normalizeExact(w);
  return a.length > 0 && a === b;
}

// Damerau-Levenshtein (limitado) — melhor “perto”
function damerauLevenshteinWithin(a, b, maxDist) {
  if (a === b) return true;
  const la = a.length,
    lb = b.length;
  if (Math.abs(la - lb) > maxDist) return false;
  if (la === 0) return lb <= maxDist;
  if (lb === 0) return la <= maxDist;

  const dp = Array.from({ length: la + 1 }, () => new Array(lb + 1).fill(0));
  for (let i = 0; i <= la; i++) dp[i][0] = i;
  for (let j = 0; j <= lb; j++) dp[0][j] = j;

  let bestInRow;
  for (let i = 1; i <= la; i++) {
    bestInRow = dp[i][0];
    for (let j = 1; j <= lb; j++) {
      const cost = a[i - 1] === b[j - 1] ? 0 : 1;
      let v = Math.min(dp[i - 1][j] + 1, dp[i][j - 1] + 1, dp[i - 1][j - 1] + cost);

      // transposição
      if (i > 1 && j > 1 && a[i - 1] === b[j - 2] && a[i - 2] === b[j - 1]) {
        v = Math.min(v, dp[i - 2][j - 2] + 1);
      }

      dp[i][j] = v;
      if (v < bestInRow) bestInRow = v;
    }
    if (bestInRow > maxDist) return false;
  }
  return dp[la][lb] <= maxDist;
}

function isNearGuess(roomId, text) {
  const w = roomWord[roomId] || "";
  if (!w) return false;

  const guess = normalizeNear(text);
  const answer = normalizeNear(w);

  if (!guess || !answer) return false;
  if (guess === answer) {
    const exactGuess = normalizeExact(text);
    const exactAnswer = normalizeExact(w);
    return exactGuess !== exactAnswer;
  }

  // se for parte grande do termo (ex: “cachorro” dentro de “cachorro-quente”)
  if (guess.length >= 3 && answer.includes(guess)) return true;

  // threshold dinâmico
  const len = answer.length;
  let maxDist = 2;
  if (len <= 4) maxDist = 1;
  else if (len <= 8) maxDist = 2;
  else if (len <= 12) maxDist = 3;
  else maxDist = 4;

  return damerauLevenshteinWithin(guess, answer, maxDist);
}

function containsAnswerSubstring(roomId, text) {
  const w = roomWord[roomId] || "";
  if (!w) return false;

  const msg = normalizeLeak(text);
  const ans = normalizeLeak(w);

  if (!msg || !ans) return false;
  return msg.includes(ans);
}

function emitGuess(roomId, payload) {
  if (!roomGuessHistory[roomId]) roomGuessHistory[roomId] = [];
  roomGuessHistory[roomId].push(payload);
  if (roomGuessHistory[roomId].length > ROOM_CHAT_HISTORY_LIMIT) {
    roomGuessHistory[roomId].splice(0, roomGuessHistory[roomId].length - ROOM_CHAT_HISTORY_LIMIT);
  }
  io.to(roomId).emit("guessMessage", payload);
}

function emitTalk(roomId, payload) {
  if (!roomTalkHistory[roomId]) roomTalkHistory[roomId] = [];
  roomTalkHistory[roomId].push(payload);
  if (roomTalkHistory[roomId].length > ROOM_CHAT_HISTORY_LIMIT) {
    roomTalkHistory[roomId].splice(0, roomTalkHistory[roomId].length - ROOM_CHAT_HISTORY_LIMIT);
  }
  io.to(roomId).emit("talkMessage", payload);
}

// mensagens de sistema (azul) — talk e guess
function emitSystemTalkToOthers(socket, roomId, text) {
  if (!rooms[roomId] || (rooms[roomId] || []).length === 0) return;

  const payload = {
    roomId,
    nick: "Sistema",
    text,
    kind: "systemBlue",
    ts: Date.now(),
  };
  if (!roomTalkHistory[roomId]) roomTalkHistory[roomId] = [];
  roomTalkHistory[roomId].push(payload);
  if (roomTalkHistory[roomId].length > ROOM_CHAT_HISTORY_LIMIT) {
    roomTalkHistory[roomId].splice(0, roomTalkHistory[roomId].length - ROOM_CHAT_HISTORY_LIMIT);
  }
  socket.to(roomId).emit("talkMessage", payload);
}

function hasConnectedPlayersInRoom(roomId) {
  return getConnectedRoomPlayers(roomId).length > 0;
}

function isSocketAliveInRoom(socketId, roomId) {
  const sid = String(socketId || "").trim();
  if (!sid) return false;
  const s = io.sockets.sockets.get(sid);
  return !!(s && s.connected && s.rooms && s.rooms.has(roomId));
}

function isPlayerConnectedInRoom(roomId, player) {
  if (!roomId || !player) return false;
  const sid = getPlayerSocketId(player);
  if (!sid) return false;
  return isSocketAliveInRoom(sid, roomId);
}

function getConnectedRoomPlayers(roomId) {
  const players = rooms[roomId] || [];
  if (!players.length) return [];
  return players.filter((p) => isPlayerConnectedInRoom(roomId, p));
}

function emitRoomUpdate(roomId, targetSocket = null) {
  const players = getConnectedRoomPlayers(roomId);
  if (targetSocket) targetSocket.emit("roomUpdate", players);
  else io.to(roomId).emit("roomUpdate", players);
}

function emitSystemGuess(roomId, text) {
  emitGuess(roomId, {
    roomId,
    nick: "Sistema",
    text,
    kind: "systemBlue",
    ts: Date.now(),
  });
}

function emitRedGuess(roomId, text) {
  emitGuess(roomId, {
    roomId,
    nick: "Sistema",
    text,
    kind: "blocked", // no seu game.html: "blocked" é vermelho e bold
    ts: Date.now(),
  });
}

function replayRoomHistoryToSocket(socket, roomId) {
  const guessArr = roomGuessHistory[roomId] || [];
  const talkArr = roomTalkHistory[roomId] || [];
  for (const msg of guessArr) {
    socket.emit("guessMessage", { ...msg, replay: true });
  }
  for (const msg of talkArr) {
    socket.emit("talkMessage", { ...msg, replay: true });
  }
}

// -------------------- WORDS LOADING --------------------
function loadWordsJson(fileRelPath) {
  const fullPath = path.join(__dirname, fileRelPath);

  try {
    if (!fs.existsSync(fullPath)) {
      console.log(`❌ Arquivo não existe: ${fullPath}`);
      return [];
    }

    const raw = fs.readFileSync(fullPath, "utf8");
    const arr = JSON.parse(raw);

    if (!Array.isArray(arr)) {
      console.log(`❌ JSON não é array: ${fullPath}`);
      return [];
    }

    return arr.map((w) => String(w).trim()).filter(Boolean);
  } catch (e) {
    console.log(`⚠️ Erro lendo/parseando JSON: ${fullPath}`);
    console.log("   Motivo:", e.message);
    return [];
  }
}

const WORDS_BY_CATEGORY = {
  alimentos: [],
  animais: [],
  objetos: [],
  geral: [],
  pokemon: [],
};

function reloadDictionaries() {
  WORDS_BY_CATEGORY.alimentos = loadWordsJson("words/alimentos.json");
  WORDS_BY_CATEGORY.animais = loadWordsJson("words/animais.json");
  WORDS_BY_CATEGORY.objetos = loadWordsJson("words/objetos.json");
  WORDS_BY_CATEGORY.geral = loadWordsJson("words/geral.json");
  WORDS_BY_CATEGORY.pokemon = loadWordsJson("words/pokemon.json");

  console.log("📚 Alimentos carregados:", WORDS_BY_CATEGORY.alimentos.length);
  console.log("📚 Animais carregados:", WORDS_BY_CATEGORY.animais.length);
  console.log("📚 Objetos carregados:", WORDS_BY_CATEGORY.objetos.length);
  console.log("📚 Geral carregado:", WORDS_BY_CATEGORY.geral.length);
  console.log("📚 Pokemon carregados:", WORDS_BY_CATEGORY.pokemon.length);
}

reloadDictionaries();

try {
  const watchPath = path.join(__dirname, "words", "animais.json");
  if (fs.existsSync(watchPath)) {
    fs.watch(watchPath, { persistent: false }, () => {
      console.log("🔁 Detectei mudança em animais.json -> recarregando...");
      reloadDictionaries();
    });
  }
} catch (_) {}

function getCategoryFromRoomId(roomId) {
  const first = String(roomId || "").trim().split(/\s+/)[0] || "geral";
  return first.toLowerCase();
}

function keepRoomWordPoolData(oldRoom, newRoom) {
  if (!oldRoom || !newRoom || oldRoom === newRoom) return;
  if (Number.isInteger(oldRoom.roundId)) newRoom.roundId = oldRoom.roundId;
  if (typeof oldRoom.state === "string") newRoom.state = oldRoom.state;
  if (typeof oldRoom.wordPoolId === "string") newRoom.wordPoolId = oldRoom.wordPoolId;
  if (Array.isArray(oldRoom.wordsList)) newRoom.wordsList = oldRoom.wordsList;
  if (oldRoom.wordWeightsByPool && typeof oldRoom.wordWeightsByPool === "object") {
    newRoom.wordWeightsByPool = oldRoom.wordWeightsByPool;
  }
  if (oldRoom.wordsUsedThisMatchByPool && typeof oldRoom.wordsUsedThisMatchByPool === "object") {
    newRoom.wordsUsedThisMatchByPool = oldRoom.wordsUsedThisMatchByPool;
  }
}

function setRoomPlayers(roomId, players) {
  const oldRoom = rooms[roomId];
  rooms[roomId] = players;
  keepRoomWordPoolData(oldRoom, rooms[roomId]);
  ensureRoomGuardState(roomId);
  scheduleLobbyRoomCountsEmit();
  return rooms[roomId];
}

let lobbyCountsEmitTimer = null;
let lastLobbyCountsSignature = "";

function buildLobbyRoomCounts() {
  const counts = {};
  for (const rid in rooms) {
    const n = getConnectedRoomPlayers(rid).length;
    if (n > 0) counts[rid] = n;
  }
  return counts;
}

function lobbyCountsSignature(countsObj) {
  const keys = Object.keys(countsObj || {}).sort();
  if (!keys.length) return "";
  return keys.map((k) => `${k}:${Number(countsObj[k] || 0)}`).join("|");
}

function emitLobbyRoomCounts(targetSocket = null, force = false) {
  const counts = buildLobbyRoomCounts();
  const sig = lobbyCountsSignature(counts);

  if (!force && !targetSocket && sig === lastLobbyCountsSignature) return;
  if (!targetSocket) lastLobbyCountsSignature = sig;

  const payload = { counts, ts: Date.now() };
  if (targetSocket) targetSocket.emit("lobbyRoomCounts", payload);
  else io.to(LOBBY_WATCHERS_ROOM).emit("lobbyRoomCounts", payload);
}

function scheduleLobbyRoomCountsEmit() {
  if (lobbyCountsEmitTimer) return;
  lobbyCountsEmitTimer = setTimeout(() => {
    lobbyCountsEmitTimer = null;
    emitLobbyRoomCounts();
  }, 120);
}

function ensureRoomWordPoolState(roomId) {
  const room = rooms[roomId];
  if (!room) return null;

  const poolId = getCategoryFromRoomId(roomId);
  const list = (WORDS_BY_CATEGORY[poolId] || []).map((w) => String(w).trim()).filter(Boolean);

  room.wordPoolId = poolId;
  room.wordsList = list;

  if (!room.wordWeightsByPool || typeof room.wordWeightsByPool !== "object") {
    room.wordWeightsByPool = {};
  }
  if (!room.wordsUsedThisMatchByPool || typeof room.wordsUsedThisMatchByPool !== "object") {
    room.wordsUsedThisMatchByPool = {};
  }
  if (!room.wordWeightsByPool[poolId] || typeof room.wordWeightsByPool[poolId] !== "object") {
    room.wordWeightsByPool[poolId] = {};
  }
  if (!(room.wordsUsedThisMatchByPool[poolId] instanceof Set)) {
    room.wordsUsedThisMatchByPool[poolId] = new Set();
  }

  return room;
}

function pickWeightedWord(room) {
  if (!room) return null;

  const poolId = String(room.wordPoolId || "").trim().toLowerCase();
  const list = Array.isArray(room.wordsList) ? room.wordsList : [];
  if (!poolId || !list.length) return null;

  if (!room.wordWeightsByPool || typeof room.wordWeightsByPool !== "object") {
    room.wordWeightsByPool = {};
  }
  if (!room.wordsUsedThisMatchByPool || typeof room.wordsUsedThisMatchByPool !== "object") {
    room.wordsUsedThisMatchByPool = {};
  }
  if (!room.wordWeightsByPool[poolId] || typeof room.wordWeightsByPool[poolId] !== "object") {
    room.wordWeightsByPool[poolId] = {};
  }
  if (!(room.wordsUsedThisMatchByPool[poolId] instanceof Set)) {
    room.wordsUsedThisMatchByPool[poolId] = new Set();
  }

  const weights = room.wordWeightsByPool[poolId];
  const usedSet = room.wordsUsedThisMatchByPool[poolId];
  const STEP = 0.5;
  const MAX = 25;

  for (const word of list) {
    const current = Number(weights[word]);
    if (!Number.isFinite(current)) weights[word] = 1;
  }

  let total = 0;
  for (const word of list) {
    total += Math.max(0, Number(weights[word] || 0));
  }

  let picked = null;
  if (total <= 0) {
    const idx = Math.floor(Math.random() * list.length);
    picked = String(list[idx] || "").trim() || null;
  } else {
    let r = Math.random() * total;
    for (const word of list) {
      r -= Math.max(0, Number(weights[word] || 0));
      if (r <= 0) {
        picked = word;
        break;
      }
    }
    if (!picked) picked = list[list.length - 1] || null;
  }

  if (!picked) return null;

  weights[picked] = 0;
  usedSet.add(picked);

  for (const word of list) {
    if (word === picked) continue;
    const current = Number(weights[word]);
    const safe = Number.isFinite(current) ? current : 1;
    weights[word] = Math.min(MAX, safe + STEP);
  }

  return String(picked).trim();
}

function resetCurrentPoolWeightsAfterMatch(room) {
  if (!room) return;

  const poolId = String(room.wordPoolId || "").trim().toLowerCase();
  const list = Array.isArray(room.wordsList) ? room.wordsList : [];
  if (!poolId || !list.length) return;

  if (!room.wordWeightsByPool || typeof room.wordWeightsByPool !== "object") {
    room.wordWeightsByPool = {};
  }
  if (!room.wordsUsedThisMatchByPool || typeof room.wordsUsedThisMatchByPool !== "object") {
    room.wordsUsedThisMatchByPool = {};
  }
  if (!room.wordWeightsByPool[poolId] || typeof room.wordWeightsByPool[poolId] !== "object") {
    room.wordWeightsByPool[poolId] = {};
  }
  if (!(room.wordsUsedThisMatchByPool[poolId] instanceof Set)) {
    room.wordsUsedThisMatchByPool[poolId] = new Set();
  }

  const weights = room.wordWeightsByPool[poolId];
  const usedSet = room.wordsUsedThisMatchByPool[poolId];

  for (const word of list) {
    weights[word] = usedSet.has(word) ? 0 : 1;
  }

  usedSet.clear();
}

// -------------------- ROOM HELPERS --------------------
function getPlayerSocketId(player) {
  if (!player) return null;
  if (Number.isInteger(player.disconnectedAt)) return null;
  return String(player.socketId || player.id || "").trim() || null;
}

function isPlayerDisconnected(player) {
  return Number.isInteger(player?.disconnectedAt);
}

function isPlayerOnline(player) {
  return !!getPlayerSocketId(player) && !isPlayerDisconnected(player);
}

function disconnectedBeyondGrace(player, now = Date.now()) {
  if (!Number.isInteger(player?.disconnectedAt)) return false;
  return now - Number(player.disconnectedAt) > RECONNECT_GRACE_MS;
}

function disconnectedBeyondAnnounceDelay(player, now = Date.now()) {
  if (!Number.isInteger(player?.disconnectedAt)) return false;
  return now - Number(player.disconnectedAt) > DISCONNECT_ANNOUNCE_DELAY_MS;
}

function findPlayerBySocket(roomId, socketId) {
  const sid = String(socketId || "").trim();
  if (!sid) return null;
  const ps = rooms[roomId] || [];
  return ps.find((p) => getPlayerSocketId(p) === sid || p.id === sid) || null;
}

function findPlayerByClientId(roomId, clientId) {
  const cid = String(clientId || "").trim();
  if (!cid) return null;
  const ps = rooms[roomId] || [];
  return ps.find((p) => String(p.clientId || "").trim() === cid) || null;
}

function touchPlayerConnection(player, socketId) {
  if (!player) return;
  const sid = String(socketId || "").trim();
  if (sid) {
    player.socketId = sid;
    // compat: parte da base ainda usa "id" como socket atual
    player.id = sid;
  }
  player.lastSeenAt = Date.now();
  player.disconnectedAt = null;
  player.disconnectAnnouncedAt = null;
}

function markPlayerDisconnected(player) {
  if (!player) return;
  player.lastSeenAt = Date.now();
  player.disconnectedAt = Date.now();
  player.disconnectAnnouncedAt = null;
  player.socketId = null;
}

function ensurePlayerActivityState(player, now = Date.now()) {
  if (!player) return;
  if (!Number.isInteger(player.lastActionAt)) {
    player.lastActionAt = Number.isInteger(player.lastSeenAt) ? player.lastSeenAt : now;
  }
  if (!Number.isInteger(player.afkWarnAt)) player.afkWarnAt = null;
  if (!Number.isInteger(player.afkKickAt)) player.afkKickAt = null;
}

function registerPlayerInteraction(roomId, socketId, opts = {}) {
  const now = Date.now();
  const confirm = opts.confirm === true;
  const player = findPlayerBySocket(roomId, socketId);
  if (!player) return null;

  ensurePlayerActivityState(player, now);
  const hadPendingWarning = Number.isInteger(player.afkKickAt);

  // when warning is active, only explicit confirmation can clear it
  if (hadPendingWarning && !confirm) return player;

  player.lastActionAt = now;
  player.afkWarnAt = null;
  player.afkKickAt = null;

  const sid = getPlayerSocketId(player);
  if (hadPendingWarning && sid) {
    io.to(sid).emit("afkWarning", { roomId, active: false });
  }

  return player;
}

function shouldFreezeDrawerDuringRound(roomId) {
  return roomState[roomId] === "playing" &&
    (roomPhase[roomId] === "round" || roomPhase[roomId] === "break" || roomPhase[roomId] === "victory");
}

function ensureDrawerOrder(roomId) {
  const players = rooms[roomId] || [];
  const queue = Array.isArray(roomDrawerOrder[roomId]) ? roomDrawerOrder[roomId] : [];
  const present = new Set();
  const orderedPlayerIds = [];

  for (const p of players) {
    const cid = String(p?.clientId || "").trim();
    if (!cid || present.has(cid)) continue;
    present.add(cid);
    orderedPlayerIds.push(cid);
  }

  const nextQueue = [];
  for (const cid of queue) {
    const key = String(cid || "").trim();
    if (!key || !present.has(key)) continue;
    if (!nextQueue.includes(key)) nextQueue.push(key);
  }

  for (const cid of orderedPlayerIds) {
    if (!nextQueue.includes(cid)) nextQueue.push(cid);
  }

  roomDrawerOrder[roomId] = nextQueue;
  return nextQueue;
}

function appendDrawerOrderClient(roomId, clientId) {
  const cid = String(clientId || "").trim();
  if (!cid) return;
  const queue = ensureDrawerOrder(roomId);
  if (!queue.includes(cid)) queue.push(cid);
}

function removeDrawerOrderClient(roomId, clientId) {
  const cid = String(clientId || "").trim();
  if (!cid || !Array.isArray(roomDrawerOrder[roomId])) return;
  roomDrawerOrder[roomId] = roomDrawerOrder[roomId].filter((id) => String(id || "").trim() !== cid);
}

function syncDrawerIndexFromClient(roomId) {
  const players = rooms[roomId] || [];
  const drawerCid = String(roomDrawerClientId[roomId] || "").trim();
  const idx = players.findIndex((p) => String(p?.clientId || "").trim() === drawerCid);
  roomDrawerIndex[roomId] = idx >= 0 ? idx : 0;
}

function setDrawerFromQueueHead(roomId) {
  const queue = ensureDrawerOrder(roomId);
  roomDrawerClientId[roomId] = queue[0] || null;
  syncDrawerIndexFromClient(roomId);
  return roomDrawerClientId[roomId] || null;
}

function moveDrawerClientToQueueEnd(roomId, clientId) {
  const queue = ensureDrawerOrder(roomId);
  if (!queue.length) return queue;

  const cid = String(clientId || "").trim();
  if (!cid) return queue;

  const idx = queue.findIndex((id) => String(id || "").trim() === cid);
  if (idx < 0) return queue;

  const [moved] = queue.splice(idx, 1);
  if (moved) queue.push(moved);
  return queue;
}

function ensureDrawer(roomId) {
  const players = rooms[roomId];
  if (!players || players.length === 0) return;

  const queue = ensureDrawerOrder(roomId);
  if (!queue.length) {
    roomDrawerClientId[roomId] = null;
    roomDrawerIndex[roomId] = 0;
    return;
  }

  const drawerCid = String(roomDrawerClientId[roomId] || "").trim();
  if (drawerCid && queue.includes(drawerCid)) {
    syncDrawerIndexFromClient(roomId);
    return;
  }

  // Em round ativo, nunca reatribui desenhista no meio da rodada.
  if (shouldFreezeDrawerDuringRound(roomId) && drawerCid) return;

  setDrawerFromQueueHead(roomId);
}

function currentDrawer(roomId) {
  const players = rooms[roomId];
  if (!players || players.length === 0) return null;
  ensureDrawer(roomId);

  const drawerCid = String(roomDrawerClientId[roomId] || "").trim();
  if (!drawerCid) return null;

  const byClient = players.find((p) => String(p.clientId || "") === drawerCid) || null;
  if (byClient) {
    syncDrawerIndexFromClient(roomId);
    return byClient;
  }

  // Em round ativo, mantém desenhista "congelado" (mesmo offline),
  // e retorna null para impedir troca em tempo real.
  if (shouldFreezeDrawerDuringRound(roomId)) return null;

  setDrawerFromQueueHead(roomId);

  const nextCid = String(roomDrawerClientId[roomId] || "").trim();
  if (!nextCid) return null;
  return players.find((p) => String(p.clientId || "") === nextCid) || null;
}

function emitDrawer(roomId) {
  const d = currentDrawer(roomId);
  const drawerSocketId = getPlayerSocketId(d);
  io.to(roomId).emit("drawerUpdate", {
    roomId,
    drawer: d ? { id: drawerSocketId, nick: d.nick, isAdmin: isAdminPlayer(d) } : null,
    drawerIndex: roomDrawerIndex[roomId] ?? 0,
  });
  emitScores(roomId);
}

function announceDrawerTurn(roomId) {
  const d = currentDrawer(roomId);
  if (!d) return;
  const drawerSocketId = getPlayerSocketId(d);

  // todos veem no chat de respostas
  emitSystemGuess(roomId, `🔎 Vez de ~${d.nick}`);
  // desenhista vê extra (mais direto)
  if (drawerSocketId) io.to(drawerSocketId).emit("guessMessage", {
    roomId,
    nick: "Sistema",
    text: "✏️ É sua vez de desenhar!",
    kind: "systemBlue",
    ts: Date.now(),
  });
}

function getPhaseTotalMs(phase) {
  if (phase === "round") return ROUND_MS;
  if (phase === "break") return BREAK_MS;
  if (phase === "victory") return VICTORY_MS;
  return null;
}

function emitPhase(roomId, extra = {}) {
  const phase = roomPhase[roomId] || null;
  const endsAt = roomRoundEndsAt[roomId] || null;
  const totalMs = phase ? getPhaseTotalMs(phase) : null;

  io.to(roomId).emit("phaseUpdate", {
    roomId,
    phase,
    endsAt,
    totalMs,
    ...extra,
  });
}

function emitRoundTimer(roomId) {
  const endsAt = roomRoundEndsAt[roomId] || null;
  const phase = roomPhase[roomId] || null;
  if (!endsAt || !phase) return;

  const remainingMs = Math.max(0, endsAt - Date.now());
  io.to(roomId).emit("roundTimer", {
    roomId,
    endsAt,
    remainingMs,
    phase,
    totalMs: getPhaseTotalMs(phase),
  });
}

function emitWordToDrawer(roomId) {
  const drawer = currentDrawer(roomId);
  if (!drawer) return;
  const drawerSocketId = getPlayerSocketId(drawer);
  if (!drawerSocketId) return;

  const word = roomWord[roomId] || "";
  io.to(drawerSocketId).emit("secretWord", { roomId, word });
}

function newRoundWord(roomId) {
  roomRoundGuessed[roomId] = new Set();
  clearTalkLeakBuffer(roomId);

  const room = ensureRoomWordPoolState(roomId);
  const word = pickWeightedWord(room);

  if (!word) {
    roomWord[roomId] = "";
    const pool = room?.wordPoolId || getCategoryFromRoomId(roomId);
    console.log(`❌ Sem palavras para categoria "${pool}" na sala (${roomId})`);

    const drawer = currentDrawer(roomId);
    const drawerSocketId = getPlayerSocketId(drawer);
    if (drawerSocketId) {
      io.to(drawerSocketId).emit("secretWord", { roomId, word: "(SEM PALAVRAS NO DICIONÁRIO)" });
    }

    resetHintForRoom(roomId);
    return;
  }

  roomWord[roomId] = word;
  console.log(`🟡 Palavra (${roomId}): ${roomWord[roomId]}`);
  emitWordToDrawer(roomId);

  resetHintForRoom(roomId);
}

function stopRoomTimers(roomId) {
  clearDrawerDecisionTimer(roomId);

  const t = roomTimers[roomId];
  if (t?.phaseTimeout) clearTimeout(t.phaseTimeout);
  if (t?.tickInterval) clearInterval(t.tickInterval);
  delete roomTimers[roomId];
}

function schedulePhase(roomId, ms, fn) {
  if (!roomTimers[roomId]) roomTimers[roomId] = {};
  if (roomTimers[roomId].phaseTimeout) clearTimeout(roomTimers[roomId].phaseTimeout);
  const localRoundId = ensureRoomRoundId(roomId);
  const timeoutRef = setTimeout(() => {
    const roomRoundId = ensureRoomRoundId(roomId);
    if (roomRoundId !== localRoundId) {
      guardWarn("stale timer", { roomId, localRoundId, roomRoundId, timer: "phaseTimeout" });
      clearTimeout(timeoutRef);
      if (roomTimers[roomId]?.phaseTimeout === timeoutRef) delete roomTimers[roomId].phaseTimeout;
      return;
    }
    if (roomTimers[roomId]?.phaseTimeout === timeoutRef) delete roomTimers[roomId].phaseTimeout;
    fn();
  }, ms);
  roomTimers[roomId].phaseTimeout = timeoutRef;
}

function cleanExpiredGhosts(roomId) {
  const now = Date.now();
  if (!roomGhosts[roomId]) return;
  for (const nn in roomGhosts[roomId]) {
    if (roomGhosts[roomId][nn]?.expiresAt <= now) delete roomGhosts[roomId][nn];
  }
}

function emitDrawerQueue(roomId) {
  const players = rooms[roomId] || [];
  if (!players.length) return;

  const queue = ensureDrawerOrder(roomId);
  if (!queue.length) return;

  const byClientId = new Map();
  for (const p of players) {
    const cid = String(p?.clientId || "").trim();
    if (!cid || byClientId.has(cid)) continue;
    byClientId.set(cid, p);
  }

  const currentCid = String(roomDrawerClientId[roomId] || "").trim();
  const currentIdx = queue.findIndex((cid) => String(cid || "").trim() === currentCid);

  const getAt = (offset) => {
    const base = currentIdx >= 0 ? currentIdx : -1;
    const idx = ((base + offset) % queue.length + queue.length) % queue.length;
    const cid = String(queue[idx] || "").trim();
    const player = byClientId.get(cid) || null;
    return {
      nick: player?.nick || null,
      isAdmin: isAdminPlayer(player),
    };
  };
  const next = getAt(1);
  const in1 = getAt(2);
  const in2 = getAt(3);

  io.to(roomId).emit("drawerQueue", {
    roomId,
    next: next.nick,
    in1: in1.nick,
    in2: in2.nick,
    nextIsAdmin: next.isAdmin,
    in1IsAdmin: in1.isAdmin,
    in2IsAdmin: in2.isAdmin,
  });
}

function startVictory(roomId, winnerNick, winnerId) {
  if (!rooms[roomId] || roomState[roomId] !== "playing") return;

  clearDrawerDecisionTimer(roomId);
  const room = ensureRoomWordPoolState(roomId);
  resetCurrentPoolWeightsAfterMatch(room);
  setRoomGuardState(roomId, ROOM_STATE.GAME_END);

  const ps = rooms[roomId] || [];
  const w = ps.find((p) => p.id === winnerId);
  if (w) w.wins = Number(w.wins || 0) + 1;
  const winnerIsAdmin = isAdminPlayer(w) || isReservedAdminNick(winnerNick);

  for (const p of ps) p.score = 0;

  emitScores(roomId);

  roomPhase[roomId] = "victory";
  roomDrawEnabled[roomId] = false;
  roomRoundHasCorrect[roomId] = false;
  roomRoundEndsAt[roomId] = Date.now() + VICTORY_MS;

  roomRoundGuessed[roomId] = new Set();

  roomCanvasSnapshot[roomId] = null;
  io.to(roomId).emit("clearCanvas", { roomId });

  io.to(roomId).emit("drawControl", { roomId, enabled: false, reason: "VICTORY" });

  emitPhase(roomId, { winner: winnerNick, winnerIsAdmin });
  emitRoundTimer(roomId);

  // reset reports em fases que não são round
  clearReports(roomId);
  clearReportIpLocks(roomId);

  schedulePhase(roomId, VICTORY_MS, () => startBreak(roomId, "VICTORY"));
}

function startBreak(roomId, reason = "TIMEOUT", meta = {}) {
  if (!rooms[roomId] || roomState[roomId] !== "playing") return;

  clearDrawerDecisionTimer(roomId);
  setRoomGuardState(roomId, ROOM_STATE.ROUND_END);

  if (reason === "TIMEOUT") {
    emitGuess(roomId, {
      roomId,
      nick: "Sistema",
      text: `⚠️ A resposta era: ${roomWord[roomId] || ""}`,
      kind: "warn",
      ts: Date.now(),
    });

    emitGuess(roomId, {
      roomId,
      nick: "Sistema",
      text: "⚠️ Intervalo...",
      kind: "warn",
      ts: Date.now(),
    });
  }
  if (reason === "REPORT_CANCEL") {
    emitGuess(roomId, {
      roomId,
      nick: "Sistema",
      text: "⚠️ Intervalo...",
      kind: "warn",
      ts: Date.now(),
    });
  }

  roomPhase[roomId] = "break";
  roomDrawEnabled[roomId] = false;
  roomRoundHasCorrect[roomId] = false;
  roomRoundEndsAt[roomId] = Date.now() + BREAK_MS;

  // Atualiza ranking no break para limpar selo/cor de acerto e status de desenhista.
  emitScores(roomId);

  roomCanvasSnapshot[roomId] = null;
  io.to(roomId).emit("clearCanvas", { roomId });

  io.to(roomId).emit("drawControl", { roomId, enabled: false, reason: "BREAK" });

  const actorNick = String(meta.actorNick || "").trim() || null;
  const actorIsAdmin = meta.actorIsAdmin === true;
  emitPhase(roomId, { reason, actorNick, actorIsAdmin });
  emitRoundTimer(roomId);

  emitDrawerQueue(roomId);

  // reset reports no break
  clearReports(roomId);
  clearReportIpLocks(roomId);

  schedulePhase(roomId, BREAK_MS, () => rotateRound(roomId));
}

function advanceToNextEligibleDrawer(roomId) {
  const players = rooms[roomId] || [];
  if (players.length < 2) return;

  const queue = ensureDrawerOrder(roomId);
  if (!queue.length) {
    roomDrawerClientId[roomId] = null;
    roomDrawerIndex[roomId] = 0;
    return;
  }

  // evita loop infinito
  let safety = queue.length + 2;

  while (safety-- > 0) {
    setDrawerFromQueueHead(roomId);

    const drawerKey = String(roomDrawerClientId[roomId] || "").trim();
    if (!drawerKey) return;

    const d = players.find((p) => String(p?.clientId || "").trim() === drawerKey) || null;

    // se ele tá marcado pra pular, pula e limpa a marca
    if (drawerKey && shouldSkipDrawer(roomId, drawerKey)) {
      clearSkipDrawer(roomId, drawerKey);
      emitSystemGuess(roomId, `⚠️ ${d?.nick || "Jogador"} teve a vez pulada.`);
      moveDrawerClientToQueueEnd(roomId, drawerKey);
      continue;
    }

    syncDrawerIndexFromClient(roomId);
    return;
  }
}

function rotateRound(roomId) {
  if (!rooms[roomId] || roomState[roomId] !== "playing") return;

  const players = rooms[roomId];
  if (!players || players.length < 2) return;
  if (!guardCanStartRound(roomId, "rotateRound", null, null)) return;

  startNewRoundState(roomId);
  setRoomGuardState(roomId, ROOM_STATE.IN_ROUND);
  roomPhase[roomId] = "round";

  const queue = ensureDrawerOrder(roomId);
  if (!queue.length) {
    roomDrawerClientId[roomId] = null;
    roomDrawerIndex[roomId] = 0;
    return;
  }

  const currentCid = String(roomDrawerClientId[roomId] || "").trim();
  if (currentCid && queue.includes(currentCid)) {
    moveDrawerClientToQueueEnd(roomId, currentCid);
  }
  setDrawerFromQueueHead(roomId);

  // aplica regra de pular a vez (por denúncias)
  advanceToNextEligibleDrawer(roomId);

  roomRoundEndsAt[roomId] = Date.now() + ROUND_MS;

  roomDrawEnabled[roomId] = false;
  io.to(roomId).emit("drawControl", { roomId, enabled: false, reason: "ROUND_START" });

  roomCanvasSnapshot[roomId] = null;
  io.to(roomId).emit("clearCanvas", { roomId });

  // reset reports no começo do round
  resetReports(roomId);
  clearReportIpLocks(roomId);

  emitDrawer(roomId);
  announceDrawerTurn(roomId);

  emitPhase(roomId, { reason: "ROUND_START" });
  emitRoundTimer(roomId);

  newRoundWord(roomId);

  // snapshot de score do round (pra desfazer em denúncia)
  takeScoreSnapshot(roomId);

  // ✅ timer de 15s pra decidir
  startDrawerDecisionTimer(roomId);

  const d = currentDrawer(roomId);
  console.log(`🎨 Troca desenhista (${roomId}) -> ${d ? d.nick : "ninguém"}`);

  schedulePhase(roomId, ROUND_MS, () => startBreak(roomId, "TIMEOUT"));
}

function startRoomTimers(roomId) {
  if (!roomTimers[roomId]) roomTimers[roomId] = {};
  if (roomTimers[roomId].tickInterval) return;

  const localRoundId = ensureRoomRoundId(roomId);
  const intervalRef = setInterval(() => {
    const roomRoundId = ensureRoomRoundId(roomId);
    if (roomRoundId !== localRoundId) {
      guardWarn("stale timer", { roomId, localRoundId, roomRoundId, timer: "tickInterval" });
      clearInterval(intervalRef);
      if (roomTimers[roomId]?.tickInterval === intervalRef) delete roomTimers[roomId].tickInterval;
      if (rooms[roomId] && roomState[roomId] === "playing") startRoomTimers(roomId);
      return;
    }
    if (!rooms[roomId] || roomState[roomId] !== "playing") return;
    cleanExpiredGhosts(roomId);
    emitRoundTimer(roomId);
  }, 250);
  roomTimers[roomId].tickInterval = intervalRef;

  emitRoundTimer(roomId);
  console.log(
    `▶️ Timers iniciados na sala ${roomId} (ROUND_MS=${ROUND_MS}ms, BREAK_MS=${BREAK_MS}ms, VICTORY_MS=${VICTORY_MS}ms)`
  );
}

function ensureRoomTimers(roomId) {
  if (roomState[roomId] === "playing") startRoomTimers(roomId);
}

function updateRoomState(roomId) {
  if (!rooms[roomId]) return;
  ensureRoomGuardState(roomId);

  const count = getConnectedRoomPlayers(roomId).length;
  const newState = count >= 2 ? "playing" : "lobby";

  if (roomState[roomId] !== newState) {
    roomState[roomId] = newState;
    io.to(roomId).emit("roomState", { roomId, state: newState });
    console.log(`🟣 Estado da sala ${roomId}: ${newState} (${count} players)`);

    if (newState === "playing") {
      if (!guardCanStartRound(roomId, "updateRoomState:startRound", null, null)) return;
      ensureDrawer(roomId);
      startNewRoundState(roomId);
      setRoomGuardState(roomId, ROOM_STATE.IN_ROUND);

      roomPhase[roomId] = "round";
      roomDrawEnabled[roomId] = false;

      roomRoundEndsAt[roomId] = Date.now() + ROUND_MS;

      // reset reports
      resetReports(roomId);
      clearReportIpLocks(roomId);

      emitDrawer(roomId);
      announceDrawerTurn(roomId);

      emitPhase(roomId, { reason: "START" });
      startRoomTimers(roomId);
      emitRoundTimer(roomId);

      newRoundWord(roomId);

      // snapshot score do round
      takeScoreSnapshot(roomId);

      io.to(roomId).emit("drawControl", { roomId, enabled: false, reason: "ROUND_START" });

      roomCanvasSnapshot[roomId] = null;
      io.to(roomId).emit("clearCanvas", { roomId });

      // timer 15s
      startDrawerDecisionTimer(roomId);

      schedulePhase(roomId, ROUND_MS, () => startBreak(roomId, "TIMEOUT"));
    } else {
      setRoomGuardState(roomId, ROOM_STATE.LOBBY);
      stopRoomTimers(roomId);

      delete roomPhase[roomId];
      delete roomDrawEnabled[roomId];

      delete roomRoundEndsAt[roomId];
      io.to(roomId).emit("roundTimer", { roomId, endsAt: null, remainingMs: null, phase: null, totalMs: null });
      emitPhase(roomId, { phase: null });

      delete roomWord[roomId];
      delete roomHint[roomId];
      delete roomRoundGuessed[roomId];
      delete roomRoundHasCorrect[roomId];
      clearTalkLeakBuffer(roomId);

      clearReports(roomId);
      clearReportIpLocks(roomId);
      delete roomScoreSnapshot[roomId];

      io.to(roomId).emit("hintUpdate", { roomId, mask: null, revealed: 0, maxReveal: 0 });

      roomCanvasSnapshot[roomId] = null;
      io.to(roomId).emit("clearCanvas", { roomId });

      emitDrawer(roomId);
      emitScores(roomId);
    }
  }
}

function saveGhost(roomId, nick, score, wins, guessedRoundId = null, drawerRoundId = null) {
  const nn = normNick(nick);
  if (!roomGhosts[roomId]) roomGhosts[roomId] = {};
  roomGhosts[roomId][nn] = {
    score: Number(score || 0),
    wins: Number(wins || 0),
    guessedRoundId: Number.isInteger(guessedRoundId) ? guessedRoundId : null,
    drawerRoundId: Number.isInteger(drawerRoundId) ? drawerRoundId : null,
    expiresAt: Date.now() + 60000,
  };
}

function removeFromRoom(roomId, socketId, reason = "LEAVE", opts = {}) {
  if (!roomId || !rooms[roomId]) return;

  ensureDrawer(roomId);

  const byClientId = String(opts.clientId || "").trim();
  const sid = String(socketId || "").trim();

  const beforePlayers = rooms[roomId].slice();
  const before = beforePlayers.length;

  const leaving = byClientId
    ? beforePlayers.find((p) => String(p.clientId || "") === byClientId)
    : beforePlayers.find((p) => getPlayerSocketId(p) === sid || p.id === sid);

  if (!leaving) return;

  const leavingIdx = beforePlayers.findIndex((p) => p === leaving);
  if (leavingIdx < 0) return;

  const leavingSocketId = getPlayerSocketId(leaving) || sid || null;
  const leavingClientId = String(leaving.clientId || "").trim() || null;
  const wasRoundPhase = roomState[roomId] === "playing" && roomPhase[roomId] === "round";
  const wasCurrentDrawer =
    !!leavingClientId && String(roomDrawerClientId[roomId] || "").trim() === leavingClientId;

  // se ele tinha votado denúncia, remove o voto
  if (roomReports[roomId]?.voters) {
    if (leavingSocketId) roomReports[roomId].voters.delete(leavingSocketId);
    if (sid) roomReports[roomId].voters.delete(sid);
  }

  if (leavingSocketId) clearTalkLeakBufferForSocket(roomId, leavingSocketId);
  if (sid && sid !== leavingSocketId) clearTalkLeakBufferForSocket(roomId, sid);

  setRoomPlayers(
    roomId,
    beforePlayers.filter((_, idx) => idx !== leavingIdx)
  );
  if (leavingClientId) removeDrawerOrderClient(roomId, leavingClientId);
  else ensureDrawerOrder(roomId);

  if (rooms[roomId].length === before) return;

  if (rooms[roomId].length === 0) {
    delete rooms[roomId];
    delete roomState[roomId];
    delete roomDrawerIndex[roomId];
    delete roomDrawerClientId[roomId];
    delete roomDrawerOrder[roomId];
    delete roomRoundEndsAt[roomId];
    delete roomWord[roomId];
    delete roomHint[roomId];
    delete roomRoundGuessed[roomId];
    delete roomRoundHasCorrect[roomId];
    clearTalkLeakBuffer(roomId);
    delete roomGuessHistory[roomId];
    delete roomTalkHistory[roomId];
    delete roomPhase[roomId];
    delete roomDrawEnabled[roomId];
    delete roomGhosts[roomId];
    delete roomScoreSnapshot[roomId];
    clearReports(roomId);
    clearReportIpLocks(roomId);
    clearRoomConsecutiveState(roomId);
    roomCanvasSnapshot[roomId] = null;
    stopRoomTimers(roomId);
    return;
  }

  // Se o desenhista sair no meio do desenho, mantém o round atual com o
  // canvas já existente até timeout/todos acertarem, sem trocar desenhista.
  if (wasRoundPhase && wasCurrentDrawer) {
    const drawingAlreadyStarted = roomDrawEnabled[roomId] === true;

    if (drawingAlreadyStarted && leavingClientId) {
      roomDrawerClientId[roomId] = leavingClientId;

      emitRoomUpdate(roomId);
      emitScores(roomId);

      updateRoomState(roomId);
      ensureRoomTimers(roomId);
      emitDrawer(roomId);

      if (roomState[roomId] === "playing") {
        emitGuess(roomId, {
          roomId,
          nick: "Sistema",
          text: `⚠️ ${String(leaving.nick || "desenhista")} saiu, mas a rodada continua.`,
          kind: "warn",
          ts: Date.now(),
        });

        if (!roomHint[roomId]) resetHintForRoom(roomId);
        else emitHint(roomId);
        emitRoundTimer(roomId);
      }
      return;
    }

    emitRoomUpdate(roomId);
    emitScores(roomId);

    updateRoomState(roomId);
    ensureRoomTimers(roomId);

    if (roomState[roomId] === "playing" && roomPhase[roomId] === "round") {
      emitGuess(roomId, {
        roomId,
        nick: "Sistema",
        text: `⚠️ ${String(leaving.nick || "desenhista")} saiu antes de começar a desenhar.`,
        kind: "warn",
        ts: Date.now(),
      });
      startBreak(roomId, "AUTO_SKIP", {
        actorNick: leaving.nick,
        actorIsAdmin: isAdminPlayer(leaving),
      });
      return;
    }

    emitDrawer(roomId);

    if (roomState[roomId] === "playing") {
      if (!roomWord[roomId]) newRoundWord(roomId);
      else {
        emitWordToDrawer(roomId);
        if (!roomHint[roomId]) resetHintForRoom(roomId);
        else emitHint(roomId);
      }
      emitRoundTimer(roomId);
      if (roomPhase[roomId] === "break") emitDrawerQueue(roomId);
    }
    return;
  }

  ensureDrawer(roomId);
  if (leavingClientId && String(roomDrawerClientId[roomId] || "").trim() === leavingClientId) {
    if (shouldFreezeDrawerDuringRound(roomId)) {
      roomDrawerClientId[roomId] = leavingClientId;
      syncDrawerIndexFromClient(roomId);
    } else {
      setDrawerFromQueueHead(roomId);
    }
  } else {
    ensureDrawer(roomId);
  }

  emitRoomUpdate(roomId);
  emitScores(roomId);

  updateRoomState(roomId);
  ensureRoomTimers(roomId);
  emitDrawer(roomId);

  if (roomState[roomId] === "playing") {
    if (!roomWord[roomId]) newRoundWord(roomId);
    else {
      emitWordToDrawer(roomId);
      if (!roomHint[roomId]) resetHintForRoom(roomId);
      else emitHint(roomId);
    }
    emitRoundTimer(roomId);
    if (roomPhase[roomId] === "break") emitDrawerQueue(roomId);
  }
}

// -------------------- PRUNE ROOM (FIX NICK PRESO) --------------------
function pruneRoom(roomId) {
  if (!rooms[roomId]) return;

  const now = Date.now();
  const players = rooms[roomId] || [];
  let changed = false;

  for (const p of players) {
    const sid = getPlayerSocketId(p);
    const s = sid ? io.sockets.sockets.get(sid) : null;
    const alive = !!(s && s.rooms && s.rooms.has(roomId));

    if (alive) {
      p.lastSeenAt = now;
      if (isPlayerDisconnected(p)) {
        p.disconnectedAt = null;
        p.disconnectAnnouncedAt = null;
        changed = true;
      }
      if (!p.socketId && sid) {
        p.socketId = sid;
        changed = true;
      }
      continue;
    }

    if (!Number.isInteger(p.disconnectedAt)) {
      p.disconnectedAt = now;
      changed = true;
    }
  }

  if (changed) {
    setRoomPlayers(roomId, players);
  }
}

function cleanupExpiredDisconnectedInRoom(roomId) {
  if (!rooms[roomId]) return;

  const now = Date.now();
  const players = rooms[roomId] || [];

  for (const p of players) {
    const alreadyAnnounced =
      Number.isInteger(p.disconnectAnnouncedAt) &&
      Number.isInteger(p.disconnectedAt) &&
      Number(p.disconnectAnnouncedAt) === Number(p.disconnectedAt);
    if (alreadyAnnounced) continue;
    if (!disconnectedBeyondAnnounceDelay(p, now)) continue;

    emitTalk(roomId, {
      roomId,
      nick: "Sistema",
      text: "~" + String(p.nick || "???") + " saiu do jogo.",
      kind: "systemBlue",
      ts: Date.now(),
    });
    p.disconnectAnnouncedAt = p.disconnectedAt;
  }

  const expired = players.filter((p) => disconnectedBeyondGrace(p, now));
  if (!expired.length) return;

  for (const p of expired) {
    removeFromRoom(roomId, p.id || null, "DISCONNECT_EXPIRE", { clientId: p.clientId || null });
  }
}

function processAfkInRoom(roomId, now = Date.now()) {
  if (!rooms[roomId]) return;

  const players = rooms[roomId] || [];
  if (!players.length) return;

  const toKick = [];

  for (const p of players) {
    const sid = getPlayerSocketId(p);
    if (!sid) continue;

    ensurePlayerActivityState(p, now);

    if (Number.isInteger(p.afkKickAt)) {
      if (now >= p.afkKickAt) {
        toKick.push({
          roomId,
          socketId: sid,
          clientId: String(p.clientId || "").trim() || null,
          nick: String(p.nick || "jogador"),
        });
      }
      continue;
    }

    if (now - Number(p.lastActionAt || now) < AFK_IDLE_MS) continue;

    p.afkWarnAt = now;
    p.afkKickAt = now + AFK_CONFIRM_MS;
    io.to(sid).emit("afkWarning", {
      roomId,
      active: true,
      deadlineAt: p.afkKickAt,
      timeoutMs: AFK_CONFIRM_MS,
    });
  }

  for (const item of toKick) {
    if (!rooms[roomId]) break;

    const player =
      (item.clientId && findPlayerByClientId(roomId, item.clientId)) ||
      findPlayerBySocket(roomId, item.socketId);
    if (!player) continue;

    const nick = String(player.nick || item.nick || "jogador");
    const sid = getPlayerSocketId(player) || item.socketId || null;
    const clientId = String(player.clientId || item.clientId || "").trim() || null;
    const targetSocket = sid ? io.sockets.sockets.get(sid) : null;

    if (targetSocket) {
      targetSocket.emit("afkWarning", { roomId, active: false });
      targetSocket.leave(roomId);
    }

    removeFromRoom(roomId, sid, "AFK_TIMEOUT", { clientId });

    if (rooms[roomId] && rooms[roomId].length > 0) {
      emitTalk(roomId, {
        roomId,
        nick: "Sistema",
        text: `~${nick} foi removido por inatividade.`,
        kind: "systemBlue",
        ts: Date.now(),
      });
    }

    if (targetSocket) {
      if (targetSocket.data.roomId === roomId) {
        targetSocket.data.roomId = null;
        targetSocket.data.nick = null;
        targetSocket.data.clientId = null;
        targetSocket.data.token = null;
      }
      targetSocket.emit("left", { roomId, reason: "AFK_TIMEOUT" });
    }
  }
}

function cleanupExpiredDisconnectedPlayers() {
  const now = Date.now();
  for (const roomId in rooms) {
    pruneRoom(roomId);
    cleanupExpiredDisconnectedInRoom(roomId);
    processAfkInRoom(roomId, now);
  }
}

setInterval(() => {
  cleanupExpiredDisconnectedPlayers();
}, RECONNECT_CLEANUP_MS);

function clearRoomCompletely(roomId) {
  delete rooms[roomId];
  delete roomState[roomId];
  delete roomDrawerIndex[roomId];
  delete roomDrawerClientId[roomId];
  delete roomDrawerOrder[roomId];
  delete roomRoundEndsAt[roomId];
  delete roomWord[roomId];
  delete roomHint[roomId];
  delete roomRoundGuessed[roomId];
  delete roomRoundHasCorrect[roomId];
  clearTalkLeakBuffer(roomId);
  delete roomGuessHistory[roomId];
  delete roomTalkHistory[roomId];
  delete roomPhase[roomId];
  delete roomDrawEnabled[roomId];
  delete roomGhosts[roomId];
  delete roomScoreSnapshot[roomId];
  clearReports(roomId);
  clearReportIpLocks(roomId);
  clearRoomConsecutiveState(roomId);
  roomCanvasSnapshot[roomId] = null;
  stopRoomTimers(roomId);
  scheduleLobbyRoomCountsEmit();
}

function maybeClearEmptyRoom(roomId) {
  if (!rooms[roomId]) return;
  if (rooms[roomId].length === 0) {
    clearRoomCompletely(roomId);
  }
}

// -------------------- DRAW HELPERS (server validation) --------------------
function isDrawerSocket(roomId, socketId) {
  const d = currentDrawer(roomId);
  return !!d && getPlayerSocketId(d) === socketId;
}

function canDrawNow(roomId, socketId) {
  return (
    roomState[roomId] === "playing" &&
    roomPhase[roomId] === "round" &&
    roomDrawEnabled[roomId] === true &&
    isDrawerSocket(roomId, socketId)
  );
}

function isValidDrawAction(action) {
  if (!action || typeof action !== "object") return false;

  const type = String(action.type || "");
  const allowed = new Set(["stroke", "shape", "fill", "spray", "clear"]);
  if (!allowed.has(type)) return false;

  if (type === "stroke") {
    if (!action.from || !action.to) return false;
    return true;
  }
  if (type === "shape") {
    if (!action.shape) return false;
    return true;
  }
  if (type === "fill") {
    if (typeof action.x !== "number" || typeof action.y !== "number") return false;
    if (typeof action.color !== "string") return false;
    return true;
  }
  if (type === "spray") {
    if (!Array.isArray(action.points)) return false;
    return true;
  }
  if (type === "clear") return true;

  return false;
}

function sanitizeHistory(history) {
  if (!Array.isArray(history)) return null;
  if (history.length > 5000) return null;
  for (const a of history) {
    if (!isValidDrawAction(a)) return null;
  }
  return history;
}

// -------------------- SPAM HELPERS --------------------
function ensureSpam(socketId) {
  if (!spamState[socketId]) spamState[socketId] = {};
  return spamState[socketId];
}

function blockOnlyToSocket(socket, kind, text, channel, roomId) {
  const payload = { roomId, nick: "Sistema", text, kind, ts: Date.now() };
  if (channel === "guess") socket.emit("guessMessage", payload);
  else socket.emit("talkMessage", payload);
}

function ensureRoomConsecutiveState(roomId) {
  if (!roomChatConsecutive[roomId]) {
    roomChatConsecutive[roomId] = {
      talk: { lastKey: null, streak: 0, blocked: {} },
      guess: { lastKey: null, streak: 0, blocked: {} },
    };
  }
  return roomChatConsecutive[roomId];
}

function clearRoomConsecutiveState(roomId) {
  delete roomChatConsecutive[roomId];
}

function getConsecutivePlayerKey(roomId, socket) {
  const p = findPlayerBySocket(roomId, socket?.id);
  const cid = normalizeClientId(p?.clientId || socket?.data?.clientId || "");
  if (cid) return `cid:${cid}`;
  const sid = String(socket?.id || "").trim();
  return sid ? `sid:${sid}` : "";
}

function checkConsecutiveBlocked(roomId, channel, socket, now = Date.now()) {
  const state = ensureRoomConsecutiveState(roomId);
  const ch = state[channel];
  if (!ch) return { blocked: false, waitMs: 0 };

  const key = getConsecutivePlayerKey(roomId, socket);
  if (!key) return { blocked: false, waitMs: 0 };

  const until = Number(ch.blocked[key] || 0);
  if (!until) return { blocked: false, waitMs: 0 };

  if (now >= until) {
    delete ch.blocked[key];
    if (ch.lastKey === key) {
      ch.lastKey = null;
      ch.streak = 0;
    }
    return { blocked: false, waitMs: 0 };
  }

  return { blocked: true, waitMs: until - now };
}

function resetSpamOnSpeakerChange(roomId, currentSocketId) {
  const curSid = String(currentSocketId || "").trim();
  const players = rooms[roomId] || [];
  for (const p of players) {
    const sid = getPlayerSocketId(p);
    if (!sid || sid === curSid) continue;
    const st = ensureSpam(sid);
    st.talkBurst = 0;
    st.lastTalkAt = 0;
    st.lastGuess = "";
    st.guessRepeat = 0;
  }
}

function maybeUnlockBySpeakerSwitch(roomId, channel, socket) {
  const state = ensureRoomConsecutiveState(roomId);
  const ch = state[channel];
  if (!ch) return;

  const key = getConsecutivePlayerKey(roomId, socket);
  if (!key) return;
  if (!ch.lastKey || ch.lastKey === key) return;

  // outro jogador assumiu o chat/canal: libera bloqueios ativos desse canal
  ch.blocked = {};
  ch.lastKey = key;
  ch.streak = 0;
  resetSpamOnSpeakerChange(roomId, socket?.id);
}

function registerConsecutiveMessage(roomId, channel, socket, now = Date.now()) {
  const state = ensureRoomConsecutiveState(roomId);
  const ch = state[channel];
  if (!ch) return;

  const key = getConsecutivePlayerKey(roomId, socket);
  if (!key) return;

  if (ch.lastKey && ch.lastKey !== key) {
    // alguém cortou a sequência -> desbloqueia todos desse canal
    ch.blocked = {};
    resetSpamOnSpeakerChange(roomId, socket?.id);
    ch.lastKey = key;
    ch.streak = 1;
    return;
  }

  if (ch.lastKey === key) ch.streak = Number(ch.streak || 0) + 1;
  else {
    ch.lastKey = key;
    ch.streak = 1;
  }

  // após enviar 12 seguidas, próximo envio do mesmo player é bloqueado
  if (ch.streak >= CHAT_CONSECUTIVE_LIMIT) {
    ch.blocked[key] = now + CHAT_CONSECUTIVE_UNLOCK_MS;
  }
}

function buildRoomInfo(roomId) {
  const players = getConnectedRoomPlayers(roomId).map((p) => ({
    nick: p.nick,
    score: Number(p.score || 0),
    isAdmin: isAdminPlayer(p),
  }));

  players.sort((a, b) => b.score - a.score || a.nick.localeCompare(b.nick));
  return { roomId, players };
}

function emitJoinRoomError(socket, roomId, reason, extra = {}) {
  socket.emit("joinRoomError", { roomId, reason, ...extra });
}

// -------------------- SOCKETS --------------------
io.on("connection", (socket) => {
  console.log("Usuário conectado:", socket.id);

  socket.data.roomId = null;
  socket.data.nick = null;
  socket.data.clientId = null;
  socket.data.token = null;
  socket.data.joinedOnce = {}; // { [roomId]: true }

  socket.on("subscribeLobby", () => {
    socket.join(LOBBY_WATCHERS_ROOM);
    emitLobbyRoomCounts(socket, true);
  });

  socket.on("unsubscribeLobby", () => {
    socket.leave(LOBBY_WATCHERS_ROOM);
  });

  socket.on("getRoomInfo", ({ roomId } = {}, cb) => {
    const rid = String(roomId || "").trim();

    if (!rid) {
      const payload = { roomId: "", players: [] };
      socket.emit("roomInfo", payload);
      return cb?.({ ok: false, reason: "ROOM_REQUIRED", ...payload });
    }

    pruneRoom(rid);
    cleanupExpiredDisconnectedInRoom(rid);
    if (!rooms[rid]) rooms[rid] = [];
    ensureRoomGuardState(rid);

    const payload = buildRoomInfo(rid);
    socket.emit("roomInfo", payload);
    return cb?.({ ok: true, ...payload });
  });

  socket.on("checkNick", ({ roomId, nick, clientId, adminKey } = {}, cb) => {
    const rid = String(roomId || "").trim();
    const nn = normNick(nick);
    const cid = normalizeClientId(clientId);

    if (!rid) return cb?.({ ok: false, reason: "ROOM_REQUIRED" });
    if (!nn) return cb?.({ ok: false, reason: "NICK_REQUIRED" });

    if (!rooms[rid]) rooms[rid] = [];
    ensureRoomGuardState(rid);

    pruneRoom(rid);
    cleanupExpiredDisconnectedInRoom(rid);
    if (!rooms[rid]) rooms[rid] = [];
    ensureRoomGuardState(rid);

    cleanExpiredGhosts(rid);

    if (isReservedAdminNick(nn) && !hasValidAdminKey(adminKey)) {
      emitNickBlocked(socket, rid, nick, "ADMIN_KEY_REQUIRED");
      return cb?.({ ok: false, reason: "NICK_BLOCKED" });
    }

    const connectedPlayers = getConnectedRoomPlayers(rid);

    const nickJaExiste = connectedPlayers.some((p) => {
      if (normNick(p.nick) !== nn) return false;
      if (cid && String(p.clientId || "") === cid) return false;
      return true;
    });
    if (nickJaExiste) return cb?.({ ok: false, reason: "NICK_TAKEN" });

    const otherPlayers = connectedPlayers.filter((p) => !(cid && String(p.clientId || "") === cid));
    const roomLimit = getRoomPlayerLimitForRoom(rid);
    if (otherPlayers.length >= roomLimit) return cb?.({ ok: false, reason: "ROOM_FULL" });

    return cb?.({ ok: true });
  });

  socket.on("joinRoom", ({ roomId, nick, clientId, token, adminKey } = {}) => {
    const rid = String(roomId || "").trim();
    const nickRaw = String(nick || "").trim();
    const nn = normNick(nickRaw);
    const cid = normalizeClientId(clientId);

    if (!rid) {
      emitJoinRoomError(socket, "", "room_required");
      return socket.emit("roomInvalid");
    }
    if (!nn) {
      emitJoinRoomError(socket, rid, "nick_required");
      return socket.emit("nickInvalid");
    }
    if (!cid) {
      emitJoinRoomError(socket, rid, "client_required");
      return socket.emit("roomInvalid");
    }

    if (!rooms[rid]) rooms[rid] = [];
    ensureRoomGuardState(rid);

    pruneRoom(rid);
    cleanupExpiredDisconnectedInRoom(rid);
    if (!rooms[rid]) rooms[rid] = [];
    ensureRoomGuardState(rid);

    cleanExpiredGhosts(rid);

    if (isReservedAdminNick(nn) && !hasValidAdminKey(adminKey)) {
      emitJoinRoomError(socket, rid, "nick_blocked", { nick: nickRaw });
      emitNickBlocked(socket, rid, nickRaw, "ADMIN_KEY_REQUIRED");
      return;
    }

    // guard: se ja esta na sala, nao re-anuncia "entrou"
    const alreadyInRoom =
      socket.data.roomId === rid &&
      socket.rooms &&
      socket.rooms.has(rid) &&
      rooms[rid].some((p) => getPlayerSocketId(p) === socket.id || p.id === socket.id);

    if (alreadyInRoom) {
      registerPlayerInteraction(rid, socket.id, { confirm: true });

      emitRoomUpdate(rid, socket);
      emitScores(rid);

      socket.emit("roomState", { roomId: rid, state: roomState[rid] || "lobby" });

      ensureDrawer(rid);
      emitDrawer(rid);

      if (roomState[rid] === "playing") emitRoundTimer(rid);

      socket.emit("drawControl", {
        roomId: rid,
        enabled: !!roomDrawEnabled[rid],
        reason: roomDrawEnabled[rid] ? "ENABLED" : "DISABLED",
      });
      emitPhase(rid);
      emitRoundFirstCorrectStateToSocket(socket, rid);

      if (roomCanvasSnapshot[rid]) {
        socket.emit("canvasSnapshot", { roomId: rid, dataUrl: roomCanvasSnapshot[rid] });
      }

      if (roomState[rid] === "playing") {
        const drawer = currentDrawer(rid);
        if (drawer && getPlayerSocketId(drawer) === socket.id) {
          socket.emit("secretWord", { roomId: rid, word: roomWord[rid] || "" });
        }

        if (!roomHint[rid]) resetHintForRoom(rid);
        else emitHint(rid);

        if (roomPhase[rid] === "break") emitDrawerQueue(rid);

        if (playerGuessedThisRound(rid, socket.id)) {
          socket.emit("guessLocked", {
            roomId: rid,
            locked: true,
            reason: "ALREADY_GUESSED",
            message: "Voce ja acertou!",
            ts: Date.now(),
          });
        }
      } else {
        socket.emit("hintUpdate", { roomId: rid, mask: null, revealed: 0, maxReveal: 0 });
      }

      const me = findPlayerBySocket(rid, socket.id);
      socket.emit("joined", {
        roomId: rid,
        players: getConnectedRoomPlayers(rid),
        youIsAdmin: isAdminPlayer(me),
      });
      return;
    }

    setRoomPlayers(
      rid,
      rooms[rid].filter((p) => getPlayerSocketId(p) !== socket.id && p.id !== socket.id)
    );

    if (socket.data.roomId && socket.data.roomId !== rid) {
      const oldRoom = socket.data.roomId;
      socket.leave(oldRoom);
      removeFromRoom(oldRoom, socket.id, "SWITCH");
      maybeClearEmptyRoom(oldRoom);
    }

    let joinedPlayer = findPlayerByClientId(rid, cid);
    let restoredFromReconnect = false;

    if (joinedPlayer && isPlayerDisconnected(joinedPlayer) && disconnectedBeyondGrace(joinedPlayer)) {
      removeFromRoom(rid, null, "DISCONNECT_EXPIRE", { clientId: cid });
      joinedPlayer = null;
    }

    if (joinedPlayer) {
      const prevSocketId = getPlayerSocketId(joinedPlayer);
      if (prevSocketId && prevSocketId !== socket.id) {
        const oldSock = io.sockets.sockets.get(prevSocketId);
        if (oldSock) oldSock.disconnect(true);
      }

      touchPlayerConnection(joinedPlayer, socket.id);
      joinedPlayer.clientId = cid;
      if (nickRaw) joinedPlayer.nick = nickRaw;
      joinedPlayer.isAdmin = isReservedAdminNick(joinedPlayer.nick);
      if (typeof joinedPlayer.score !== "number") joinedPlayer.score = 0;
      if (typeof joinedPlayer.wins !== "number") joinedPlayer.wins = 0;
      if (!Number.isInteger(joinedPlayer.guessedRoundId)) joinedPlayer.guessedRoundId = null;

      restoredFromReconnect = true;

      if (roomState[rid] === "playing" && roomPhase[rid] === "round" && ensureRoomGuardState(rid) === ROOM_STATE.IN_ROUND) {
        if (String(roomDrawerClientId[rid] || "") === String(joinedPlayer.clientId || "")) {
          const restoredIdx = rooms[rid].findIndex((p) => p === joinedPlayer);
          if (restoredIdx >= 0) roomDrawerIndex[rid] = restoredIdx;
        }
      }

      ensureDrawerOrder(rid);
    } else {
      const connectedPlayers = getConnectedRoomPlayers(rid);

      const nickJaExiste = connectedPlayers.some((p) => {
        if (normNick(p.nick) !== nn) return false;
        if (String(p.clientId || "") === cid) return false;
        return true;
      });
      if (nickJaExiste) {
        emitJoinRoomError(socket, rid, "duplicate", { nick: nickRaw });
        return socket.emit("nickInUse", { roomId: rid, nick: nickRaw });
      }

      const roomLimit = getRoomPlayerLimitForRoom(rid);
      if (connectedPlayers.length >= roomLimit) {
        emitJoinRoomError(socket, rid, "room_full");
        return socket.emit("roomFull");
      }

      joinedPlayer = {
        id: socket.id,
        socketId: socket.id,
        clientId: cid,
        nick: nickRaw,
        isAdmin: isReservedAdminNick(nickRaw),
        score: 0,
        wins: 0,
        guessedRoundId: null,
        lastSeenAt: Date.now(),
        lastActionAt: Date.now(),
        afkWarnAt: null,
        afkKickAt: null,
        disconnectedAt: null,
        disconnectAnnouncedAt: null,
      };
      rooms[rid].push(joinedPlayer);
      appendDrawerOrderClient(rid, joinedPlayer.clientId);

      if (!roomDrawerClientId[rid]) {
        roomDrawerClientId[rid] = joinedPlayer.clientId;
      }
    }

    socket.join(rid);
    socket.data.roomId = rid;
    socket.data.nick = joinedPlayer.nick;
    socket.data.clientId = cid;
    socket.data.token = token || null;
    registerPlayerInteraction(rid, socket.id, { confirm: true });

    console.log(
      joinedPlayer.nick + " entrou em " + rid +
      " (clientId=" + cid + ", reconnect=" + restoredFromReconnect +
      ", score=" + Number(joinedPlayer.score || 0) + ", wins=" + Number(joinedPlayer.wins || 0) + ")"
    );

    if (!restoredFromReconnect) {
      emitSystemTalkToOthers(socket, rid, "~" + joinedPlayer.nick + " entrou no jogo.");
    }

    emitRoomUpdate(rid);
    emitScores(rid);
    scheduleLobbyRoomCountsEmit();

    updateRoomState(rid);
    socket.emit("roomState", { roomId: rid, state: roomState[rid] || "lobby" });

    ensureDrawer(rid);
    emitDrawer(rid);

    ensureRoomTimers(rid);
    if (roomState[rid] === "playing") emitRoundTimer(rid);

    socket.emit("drawControl", {
      roomId: rid,
      enabled: !!roomDrawEnabled[rid],
      reason: roomDrawEnabled[rid] ? "ENABLED" : "DISABLED",
    });
    emitPhase(rid);
    emitRoundFirstCorrectStateToSocket(socket, rid);

    if (roomCanvasSnapshot[rid]) {
      socket.emit("canvasSnapshot", { roomId: rid, dataUrl: roomCanvasSnapshot[rid] });
    }

    if (roomState[rid] === "playing") {
      if (!roomWord[rid]) newRoundWord(rid);

      const drawer = currentDrawer(rid);
      if (drawer && getPlayerSocketId(drawer) === socket.id) {
        socket.emit("secretWord", { roomId: rid, word: roomWord[rid] || "" });
      }

      if (!roomHint[rid]) resetHintForRoom(rid);
      else emitHint(rid);

      if (roomPhase[rid] === "break") emitDrawerQueue(rid);

      if (playerGuessedThisRound(rid, socket.id)) {
        socket.emit("guessLocked", {
          roomId: rid,
          locked: true,
          reason: "ALREADY_GUESSED",
          message: "Voce ja acertou!",
          ts: Date.now(),
        });
      }
    } else {
      socket.emit("hintUpdate", { roomId: rid, mask: null, revealed: 0, maxReveal: 0 });
    }

    replayRoomHistoryToSocket(socket, rid);
    socket.emit("joined", {
      roomId: rid,
      players: getConnectedRoomPlayers(rid),
      youIsAdmin: isAdminPlayer(joinedPlayer),
    });
  });

  socket.on("afkStillHere", (payload = {}, cb) => {
    const rid = String(payload.roomId || socket.data.roomId || "").trim();
    if (!rid || !rooms[rid]) return cb?.({ ok: false, reason: "NO_ROOM" });

    const player = findPlayerBySocket(rid, socket.id);
    if (!player) return cb?.({ ok: false, reason: "NOT_IN_ROOM" });

    registerPlayerInteraction(rid, socket.id, { confirm: true });
    return cb?.({ ok: true });
  });

  // TALK — bloqueia substring da resposta + anti-spam (10 seguidas)
  socket.on("talkMessage", (payload = {}, cb) => {
    const rid = String(payload.roomId || socket.data.roomId || "").trim();
    if (!rid) return cb?.({ ok: false, reason: "NO_ROOM" });
    if (!rooms[rid]) return cb?.({ ok: false, reason: "NO_ROOM" });

    const text = String(payload.text || "").trim();
    if (!text) return cb?.({ ok: false, reason: "EMPTY" });
    if (text.length > 160) return cb?.({ ok: false, reason: "TOO_LONG" });
    registerPlayerInteraction(rid, socket.id);

    const nick = socket.data.nick || getNickBySocketInRoom(rid, socket.id);
    const sender = findPlayerBySocket(rid, socket.id);
    const isAdmin = sender ? isAdminPlayer(sender) : isReservedAdminNick(nick);

    maybeUnlockBySpeakerSwitch(rid, "talk", socket);
    maybeUnlockBySpeakerSwitch(rid, "guess", socket);

    const st = ensureSpam(socket.id);
    const now = Date.now();
    if (!st.lastTalkAt || now - st.lastTalkAt > 12000) st.talkBurst = 0;
    st.lastTalkAt = now;
    st.talkBurst = Number(st.talkBurst || 0) + 1;

    if (st.talkBurst > 10) {
      blockOnlyToSocket(socket, "blocked", "bloqueado!(spam) Aguarde alguns segundos ou outra pessoa falar.", "talk", rid);
      return cb?.({ ok: true, blocked: true, spam: true });
    }

    const seqBlock = checkConsecutiveBlocked(rid, "talk", socket, now);
    if (seqBlock.blocked) {
      blockOnlyToSocket(
        socket,
        "blocked",
        "bloqueado!(flood) Aguarde 1 minuto ou outra pessoa falar.",
        "talk",
        rid
      );
      return cb?.({ ok: true, blocked: true, flood: true, waitMs: seqBlock.waitMs });
    }

    if (roomState[rid] === "playing") {
      const blockedByDirectLeak = containsAnswerSubstring(rid, text);
      const blockedByChunkLeak = !blockedByDirectLeak && isChunkedAnswerLeak(rid, socket.id, text, now);

      if (blockedByDirectLeak || blockedByChunkLeak) {
        clearTalkLeakBufferForSocket(rid, socket.id);
        socket.emit("talkMessage", {
          roomId: rid,
          nick: "Sistema",
          text: "(mensagem bloqueada)",
          kind: "blocked",
          ts: Date.now(),
        });
        return cb?.({
          ok: true,
          blocked: true,
          reason: blockedByDirectLeak ? "DIRECT_LEAK" : "CHUNK_LEAK",
        });
      }
    }

    emitTalk(rid, { roomId: rid, nick, text, kind: "chat", isAdmin, ts: Date.now() });
    registerConsecutiveMessage(rid, "talk", socket, now);
    return cb?.({ ok: true });
  });

  // ✅ DENUNCIAR DESENHO
  socket.on("reportDrawing", (payload = {}, cb) => {
    const rid = String(payload.roomId || socket.data.roomId || "").trim();
    if (!rid || !rooms[rid]) return cb?.({ ok: false, reason: "NO_ROOM" });

    if (roomState[rid] !== "playing") return cb?.({ ok: false, reason: "NOT_PLAYING" });
    if (roomPhase[rid] !== "round") return cb?.({ ok: false, reason: "NOT_ROUND" });

    const drawer = currentDrawer(rid);
    if (!drawer) return cb?.({ ok: false, reason: "NO_DRAWER" });

    // desenhista não pode denunciar
    if (getPlayerSocketId(drawer) === socket.id) return cb?.({ ok: false, reason: "IS_DRAWER" });

    // se ainda não existe, cria
    if (!roomReports[rid]) resetReports(rid);

    const reportIpKey = getReportIpKey(socket);
    if (hasReportedByIpInRound(rid, reportIpKey)) {
      const needed = getReportNeeded(rid);
      const count = roomReports[rid].voters.size;
      return cb?.({ ok: true, already: true, byIp: true, count, needed });
    }

    // já votou?
    if (roomReports[rid].voters.has(socket.id)) {
      const needed = getReportNeeded(rid);
      const count = roomReports[rid].voters.size;
      return cb?.({ ok: true, already: true, count, needed });
    }

    roomReports[rid].voters.add(socket.id);
    markReportedByIpInRound(rid, reportIpKey);

    const reporterNick = String(socket.data.nick || getNickBySocketInRoom(rid, socket.id) || "Alguém").trim() || "Alguém";
    emitRedGuess(rid, `${reporterNick} denunciou!!`);

    const needed = getReportNeeded(rid);
    const count = roomReports[rid].voters.size;

    // bateu 50% -> cancela
    if (count >= needed) {
      // marca cancelamento pro desenhista
      markDrawerCancel(rid, drawer.clientId || drawer.id);

      // limpa status de acerto da rodada
      clearGuessedStateForRound(rid);

      // desfaz pontos da rodada
      restoreScoreSnapshot(rid);
      emitScores(rid);


      // avisa (vermelho) e vai pro intervalo
      emitRedGuess(rid, "❌ Desenho cancelado!");

      startBreak(rid, "REPORT_CANCEL");
      return cb?.({ ok: true, canceled: true, count, needed });
    }

    return cb?.({ ok: true, count, needed });
  });

  socket.on("reportPlayer", (payload = {}, cb) => {
    const rid = String(payload.roomId || socket.data.roomId || "").trim();
    if (!rid || !rooms[rid]) return cb?.({ ok: false, reason: "NO_ROOM" });

    const reporter = findPlayerBySocket(rid, socket.id);
    if (!reporter) return cb?.({ ok: false, reason: "NOT_IN_ROOM" });

    const targetSocketId = String(payload.targetSocketId || "").trim();
    if (!targetSocketId) return cb?.({ ok: false, reason: "TARGET_REQUIRED" });

    if (targetSocketId === socket.id) return cb?.({ ok: false, reason: "CANNOT_REPORT_SELF" });

    const target = findPlayerBySocket(rid, targetSocketId);
    if (!target) return cb?.({ ok: false, reason: "TARGET_NOT_FOUND" });

    emitTalk(rid, {
      roomId: rid,
      nick: "Sistema",
      text: `🚩 Denúncia registrada contra ~${String(target.nick || "jogador")}.`,
      kind: "systemBlue",
      ts: Date.now(),
    });

    return cb?.({ ok: true, message: "Denuncia de jogador registrada." });
  });

  // GUESS — pontua + “perto” + travas + anti-spam + lock after guessed
  socket.on("guessMessage", (payload = {}, cb) => {
    const rid = String(payload.roomId || socket.data.roomId || "").trim();
    if (!rid) return cb?.({ ok: false, reason: "NO_ROOM" });
    if (!rooms[rid]) return cb?.({ ok: false, reason: "NO_ROOM" });

    const rawText = String(payload.text || "");
    const text = rawText.trim();
    if (!text) return cb?.({ ok: false, reason: "EMPTY" });
    if (text.length > 80) return cb?.({ ok: false, reason: "TOO_LONG" });
    registerPlayerInteraction(rid, socket.id);

    const nick = socket.data.nick || getNickBySocketInRoom(rid, socket.id);
    const sender = findPlayerBySocket(rid, socket.id);
    const isAdmin = sender ? isAdminPlayer(sender) : isReservedAdminNick(nick);

    maybeUnlockBySpeakerSwitch(rid, "talk", socket);
    maybeUnlockBySpeakerSwitch(rid, "guess", socket);
    if (!guardCanGuess(rid, "guessMessage", socket, nick)) {
      return cb?.({ ok: false, reason: "INVALID_STATE" });
    }

    const playing = roomState[rid] === "playing";
    const drawer = playing ? currentDrawer(rid) : null;
    const isDrawer = !!drawer && getPlayerSocketId(drawer) === socket.id;

    if (!playing) {
      emitGuess(rid, { roomId: rid, nick, text, kind: "chat", isAdmin, ts: Date.now() });
      return cb?.({ ok: true });
    }

    const phase = roomPhase[rid];
    if (phase === "break") {
      guardWarn("invalid guess state", { roomId: rid, eventName: "guessMessage", state: ensureRoomGuardState(rid), playerId: socket.id, nick });
      if (!ENFORCE_GUARDS) {
        // observabilidade apenas
      } else {
      socket.emit("guessLocked", { roomId: rid, locked: true, reason: "BREAK", message: "Intervalo!!", ts: Date.now() });
      return cb?.({ ok: false, locked: true, reason: "BREAK" });
      }
    }
    if (phase === "victory") {
      guardWarn("invalid guess state", { roomId: rid, eventName: "guessMessage", state: ensureRoomGuardState(rid), playerId: socket.id, nick });
      if (!ENFORCE_GUARDS) {
        // observabilidade apenas
      } else {
      socket.emit("guessLocked", { roomId: rid, locked: true, reason: "VICTORY", message: "Vitória!!", ts: Date.now() });
      return cb?.({ ok: false, locked: true, reason: "VICTORY" });
      }
    }

    // desenhista nunca chuta
    if (isDrawer) {
      guardWarn("drawer guess blocked", { roomId: rid, eventName: "guessMessage", state: ensureRoomGuardState(rid), playerId: socket.id, nick });
      if (!ENFORCE_GUARDS) {
        // observabilidade apenas
      } else {
      socket.emit("guessLocked", { roomId: rid, locked: true, reason: "DRAWER_TURN", message: "É sua vez de desenhar!!", ts: Date.now() });
      return cb?.({ ok: false, locked: true, reason: "DRAWER_TURN" });
      }
    }

    // já acertou => trava
    if (playerGuessedThisRound(rid, socket.id)) {
      guardWarn("duplicate score attempt", { roomId: rid, eventName: "guessMessage", state: ensureRoomGuardState(rid), playerId: socket.id, nick, roundId: ensureRoomRoundId(rid) });
      if (!ENFORCE_GUARDS) {
        // observabilidade apenas
      } else {
      socket.emit("guessLocked", { roomId: rid, locked: true, reason: "ALREADY_GUESSED", message: "Você já acertou!", ts: Date.now() });
      return cb?.({ ok: false, locked: true, reason: "ALREADY_GUESSED" });
      }
    }

    // aguarda desenhista clicar "Desenhar"
    if (roomDrawEnabled[rid] !== true) {
      guardWarn("guess before draw enabled", { roomId: rid, eventName: "guessMessage", state: ensureRoomGuardState(rid), playerId: socket.id, nick });
      if (!ENFORCE_GUARDS) {
        // observabilidade apenas
      } else {
      socket.emit("guessLocked", { roomId: rid, locked: true, reason: "WAIT_DRAW", message: "Aguardando o desenhista...", ts: Date.now() });
      return cb?.({ ok: false, locked: true, reason: "WAIT_DRAW" });
      }
    }

    // anti-spam guess repetido (mesma palavra 5x -> 6ª bloqueia)
    const st = ensureSpam(socket.id);
    const sKey = normalizeNear(text);
    if (st.lastGuess === sKey) st.guessRepeat = Number(st.guessRepeat || 0) + 1;
    else {
      st.lastGuess = sKey;
      st.guessRepeat = 1;
    }
    if (st.guessRepeat > 5) {
      blockOnlyToSocket(socket, "blocked", "bloqueado!(spam) Aguarde alguns segundos ou outra pessoa falar.", "guess", rid);
      return cb?.({ ok: true, blocked: true, spam: true });
    }

    const now = Date.now();
    const seqBlock = checkConsecutiveBlocked(rid, "guess", socket, now);
    if (seqBlock.blocked) {
      blockOnlyToSocket(
        socket,
        "blocked",
        "bloqueado!(flood) Aguarde 1 minuto ou outra pessoa falar.",
        "guess",
        rid
      );
      return cb?.({ ok: true, blocked: true, flood: true, waitMs: seqBlock.waitMs });
    }

    registerConsecutiveMessage(rid, "guess", socket, now);

    if (isCorrectGuess(rid, text)) {
      const { guesserAdd, drawerAdd } = awardPointsForCorrectGuess(rid, socket.id);
      markRoundFirstCorrect(rid, nick);

      socket.to(rid).emit("guessMessage", {
        roomId: rid,
        nick: "Sistema",
        text: `✅ ${nick} acertou!!`,
        kind: "correct",
        ts: Date.now(),
      });

      socket.emit("guessMessage", {
        roomId: rid,
        nick: "Sistema",
        text: `✅ Você acertou: ${roomWord[rid] || ""}`,
        kind: "you",
        ts: Date.now(),
      });

      socket.emit("pointsGained", { roomId: rid, add: guesserAdd, role: "guesser" });
      const drawerSocketId = getPlayerSocketId(drawer);
      if (drawerSocketId) io.to(drawerSocketId).emit("pointsGained", { roomId: rid, add: drawerAdd, role: "drawer" });

      socket.emit("guessLocked", { roomId: rid, locked: true, reason: "ALREADY_GUESSED", message: "Você já acertou!", ts: Date.now() });

      const winnerNick = pickWinnerNick(rid);
      if (winnerNick) {
        const winnerId = pickWinnerId(rid);
        startVictory(rid, winnerNick, winnerId);
        return cb?.({ ok: true, guessed: true, victory: true });
      }

      if (allNonDrawerGuessed(rid)) {
        emitGuess(rid, { roomId: rid, nick: "Sistema", text: "⚠️ Todos acertaram...", kind: "warn", ts: Date.now() });
        emitGuess(rid, { roomId: rid, nick: "Sistema", text: `⚠️ A resposta era: ${roomWord[rid] || ""}`, kind: "warn", ts: Date.now() });
        emitGuess(rid, { roomId: rid, nick: "Sistema", text: "⚠️ Intervalo...", kind: "warn", ts: Date.now() });
        startBreak(rid, "ALL_GUESSED");
      }

      return cb?.({ ok: true, guessed: true });
    }

    if (isNearGuess(rid, text)) {
      socket.emit("guessMessage", {
        roomId: rid,
        nick: "Sistema",
        text: `⚡ ${text} está perto!`,
        kind: "near",
        ts: Date.now(),
      });
      return cb?.({ ok: true, near: true });
    }

    emitGuess(rid, { roomId: rid, nick, text, kind: "chat", isAdmin, ts: Date.now() });
    return cb?.({ ok: true });
  });

  socket.on("revealHint", (payload = {}, cb) => {
    const rid = String(payload.roomId || socket.data.roomId || "").trim();
    if (!rid) return cb?.({ ok: false, reason: "NO_ROOM" });

    if (roomState[rid] !== "playing") return cb?.({ ok: false, reason: "NOT_PLAYING" });
    if (roomPhase[rid] !== "round") return cb?.({ ok: false, reason: "NOT_ROUND" });

    const drawer = currentDrawer(rid);
    if (!drawer || getPlayerSocketId(drawer) !== socket.id) return cb?.({ ok: false, reason: "NOT_DRAWER" });

    if (!roomHint[rid]) resetHintForRoom(rid);

    const res = revealHintStep(rid);

    // todo mundo vê as dicas no chat de respostas (azul), conforme o desenhista libera
    if (res?.ok) {
      const h = roomHint[rid];
      const used = usedHintsCount(h);
      const mask = h?.mask || "";
      emitSystemGuess(rid, `⚠️ Dica (${used}): ${mask}`);
    }

    return cb?.(res);
  });

  socket.on("startDrawing", (payload = {}, cb) => {
    const rid = String(payload.roomId || socket.data.roomId || "").trim();
    const nick = socket.data.nick || getNickBySocketInRoom(rid, socket.id);
    if (!rid || !rooms[rid]) return cb?.({ ok: false, reason: "NO_ROOM" });
    registerPlayerInteraction(rid, socket.id);
    if (!guardCanDrawEvent(rid, "startDrawing", socket, nick)) {
      return cb?.({ ok: false, reason: "INVALID_STATE" });
    }
    if (roomState[rid] !== "playing") {
      guardWarn("invalid draw/canvas event", { roomId: rid, eventName: "startDrawing", state: ensureRoomGuardState(rid), playerId: socket.id, nick });
      if (ENFORCE_GUARDS) return cb?.({ ok: false, reason: "NOT_PLAYING" });
    }
    if (roomPhase[rid] !== "round") {
      guardWarn("invalid draw/canvas event", { roomId: rid, eventName: "startDrawing", state: ensureRoomGuardState(rid), playerId: socket.id, nick });
      if (ENFORCE_GUARDS) return cb?.({ ok: false, reason: "NOT_ROUND" });
    }

    const drawer = currentDrawer(rid);
    if (!drawer || getPlayerSocketId(drawer) !== socket.id) {
      guardWarn("invalid draw/canvas event", { roomId: rid, eventName: "startDrawing", state: ensureRoomGuardState(rid), playerId: socket.id, nick, drawerId: getPlayerSocketId(drawer) });
      if (ENFORCE_GUARDS) return cb?.({ ok: false, reason: "NOT_DRAWER" });
    }

    clearDrawerDecisionTimer(rid);

    roomDrawEnabled[rid] = true;
    io.to(rid).emit("drawControl", { roomId: rid, enabled: true, reason: "DRAW_ENABLED" });
    return cb?.({ ok: true });
  });

  socket.on("skipRound", (payload = {}, cb) => {
    const rid = String(payload.roomId || socket.data.roomId || "").trim();
    const nick = socket.data.nick || getNickBySocketInRoom(rid, socket.id);
    if (!rid || !rooms[rid]) return cb?.({ ok: false, reason: "NO_ROOM" });
    if (!guardCanDrawEvent(rid, "skipRound", socket, nick)) {
      return cb?.({ ok: false, reason: "INVALID_STATE" });
    }
    if (roomState[rid] !== "playing") {
      guardWarn("invalid draw/canvas event", { roomId: rid, eventName: "skipRound", state: ensureRoomGuardState(rid), playerId: socket.id, nick });
      if (ENFORCE_GUARDS) return cb?.({ ok: false, reason: "NOT_PLAYING" });
    }
    if (roomPhase[rid] !== "round") {
      guardWarn("invalid draw/canvas event", { roomId: rid, eventName: "skipRound", state: ensureRoomGuardState(rid), playerId: socket.id, nick });
      if (ENFORCE_GUARDS) return cb?.({ ok: false, reason: "NOT_ROUND" });
    }

    const drawer = currentDrawer(rid);
    if (!drawer || getPlayerSocketId(drawer) !== socket.id) {
      guardWarn("invalid draw/canvas event", { roomId: rid, eventName: "skipRound", state: ensureRoomGuardState(rid), playerId: socket.id, nick, drawerId: getPlayerSocketId(drawer) });
      if (ENFORCE_GUARDS) return cb?.({ ok: false, reason: "NOT_DRAWER" });
    }

    clearDrawerDecisionTimer(rid);

    emitGuess(rid, { roomId: rid, nick: "Sistema", text: `⏭️ ${drawer.nick} pulou a rodada.`, kind: "warn", ts: Date.now() });
    emitGuess(rid, { roomId: rid, nick: "Sistema", text: "⚠️ Intervalo...", kind: "warn", ts: Date.now() });

    startBreak(rid, "SKIP", {
      actorNick: drawer.nick,
      actorIsAdmin: isAdminPlayer(drawer),
    });
    return cb?.({ ok: true });
  });

  socket.on("drawAction", (payload = {}) => {
    const rid = String(payload.roomId || socket.data.roomId || "").trim();
    if (!rid || !rooms[rid]) return;
    const nick = socket.data.nick || getNickBySocketInRoom(rid, socket.id);
    if (!guardCanDrawEvent(rid, "drawAction", socket, nick)) return;
    if (!canDrawNow(rid, socket.id)) {
      guardWarn("draw blocked by round gates", { roomId: rid, eventName: "drawAction", state: ensureRoomGuardState(rid), playerId: socket.id, nick });
      if (ENFORCE_GUARDS) return;
    }

    const rawBatch = Array.isArray(payload.actions) ? payload.actions : null;
    const source = rawBatch && rawBatch.length ? rawBatch : [payload.action];
    const actions = [];

    for (const item of source) {
      if (actions.length >= DRAW_ACTION_BATCH_MAX) break;
      if (!isValidDrawAction(item)) continue;
      actions.push(item);
    }
    if (!actions.length) return;

    if (actions.length === 1) {
      io.to(rid).emit("drawAction", { roomId: rid, action: actions[0], from: socket.id });
      return;
    }

    io.to(rid).emit("drawActionBatch", { roomId: rid, actions, from: socket.id });
  });

  socket.on("replaceHistory", (payload = {}) => {
    const rid = String(payload.roomId || socket.data.roomId || "").trim();
    if (!rid || !rooms[rid]) return;
    const nick = socket.data.nick || getNickBySocketInRoom(rid, socket.id);
    if (!guardCanDrawEvent(rid, "replaceHistory", socket, nick)) return;
    if (!canDrawNow(rid, socket.id)) {
      guardWarn("draw blocked by round gates", { roomId: rid, eventName: "replaceHistory", state: ensureRoomGuardState(rid), playerId: socket.id, nick });
      if (ENFORCE_GUARDS) return;
    }

    const history = sanitizeHistory(payload.history);
    if (!history) return;

    io.to(rid).emit("replaceHistory", { roomId: rid, history, from: socket.id });
  });

  socket.on("canvasSnapshot", (payload = {}) => {
    const rid = String(payload.roomId || socket.data.roomId || "").trim();
    if (!rid || !rooms[rid]) return;
    const nick = socket.data.nick || getNickBySocketInRoom(rid, socket.id);
    if (!guardCanDrawEvent(rid, "canvasSnapshot", socket, nick)) return;
    if (roomState[rid] !== "playing" || !isDrawerSocket(rid, socket.id)) {
      guardWarn("draw blocked by round gates", { roomId: rid, eventName: "canvasSnapshot", state: ensureRoomGuardState(rid), playerId: socket.id, nick });
      if (ENFORCE_GUARDS) return;
    }

    const dataUrl = String(payload.dataUrl || "");
    if (!dataUrl.startsWith("data:image/")) return;

    roomCanvasSnapshot[rid] = dataUrl;
  });

  socket.on("leaveRoom", (payload = {}) => {
    const rid = String(payload.roomId || socket.data.roomId || "").trim();
    if (!rid) {
      socket.emit("left", { roomId: null });
      return;
    }

    const leavingNick = socket.data.nick || getNickBySocketInRoom(rid, socket.id);

    socket.leave(rid);
    removeFromRoom(rid, socket.id, "LEAVE");

    // ✅ só os OUTROS veem que eu saí
    if (rooms[rid] && rooms[rid].length > 0) {
      emitSystemTalkToOthers(socket, rid, `(!) ~${leavingNick} saiu do jogo.`);
    }

    if (socket.data.roomId === rid) {
      socket.data.roomId = null;
      socket.data.nick = null;
      socket.data.clientId = null;
      socket.data.token = null;
    }

    if (rooms[rid]) {
      updateRoomState(rid);
      ensureRoomTimers(rid);
      if (roomPhase[rid] === "break") emitDrawerQueue(rid);
    }

    console.log(`Usuário ${socket.id} saiu de ${rid}`);
    socket.emit("left", { roomId: rid });
  });

  socket.on("disconnect", () => {
    for (const roomId in rooms) {
      const leaving = findPlayerBySocket(roomId, socket.id);
      if (!leaving) continue;

      markPlayerDisconnected(leaving);

      // remove voto de denuncia
      if (roomReports[roomId]?.voters) roomReports[roomId].voters.delete(socket.id);
      clearTalkLeakBufferForSocket(roomId, socket.id);

      // regra: sala sem jogadores conectados reseta tudo imediatamente
      if (!hasConnectedPlayersInRoom(roomId)) {
        clearRoomCompletely(roomId);
        continue;
      }

      // Nao anuncia saida no disconnect imediato: refresh/reconexao rapida
      // nao deve poluir o chat. O aviso e emitido apenas no cleanup apos grace.
      leaving.disconnectAnnouncedAt = null;

      emitRoomUpdate(roomId);
      emitScores(roomId);
      emitDrawer(roomId);

      if (roomState[roomId] === "playing") {
        emitRoundTimer(roomId);
        if (roomPhase[roomId] === "break") emitDrawerQueue(roomId);
      }
    }

    delete spamState[socket.id];

    socket.data.roomId = null;
    socket.data.nick = null;
    socket.data.clientId = null;
    socket.data.token = null;

    console.log("Usuario desconectado:", socket.id);
  });
});

server.listen(PORT, HOST, () => {
  console.log(`Servidor rodando em ${HOST}:${PORT}`);
});


