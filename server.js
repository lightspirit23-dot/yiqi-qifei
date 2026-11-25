'use strict';
// 「一起起飞」多人实时小游戏服务器。零依赖：HTTP + SSE（服务器推送）+ JSON POST。
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const G = (() => { const module = { exports: {} };

// 核心数值：95% 理论 RTP 的开奖与倍率曲线（纯函数，便于测试）
const crypto = require('crypto');

const K = 0.09;            // 倍率增长率：mult(t) = e^(K·t)，约 7.7 秒到 2×，约 51 秒到 100×
const MAX_CENTS = 10000;   // 100.00× 封顶
const MIN_CASH_CENTS = 101; // 最低可收手倍率 1.01×
const TWO48 = 2n ** 48n;

/**
 * 抽一局的最后可收手倍率（单位：百分之一倍，即 250 = 2.50×）。
 * U 在 (0,1] 上均匀：U = n / 2^48，n ∈ [1, 2^48]
 * 倍率 = floor(0.95 / U × 100) / 100，最低 1.00×。
 * 0.95/U×100 = 95·2^48 / n，用 BigInt 整数除法做到精确向下取整，没有浮点误差。
 * 原始值 ≥ 100× 时封顶为 100×（capped=true，所有仍在场玩家在 100× 自动结算）。
 */
function drawCrash(n48) {
  let n = n48;
  if (n === undefined) n = BigInt(crypto.randomBytes(6).readUIntBE(0, 6)) + 1n; // [1, 2^48]
  let cents = Number((95n * TWO48) / n);
  if (cents < 100) cents = 100;
  const capped = cents >= MAX_CENTS;
  if (capped) cents = MAX_CENTS;
  return { cents, capped };
}

// 飞行 t 秒时的倍率（百分之一倍）
function multCentsAt(tSec) {
  return Math.floor(100 * Math.exp(K * tSec));
}

// 从起飞到飞机飞走的时长（秒）：倍率将超过最后倍率的那一刻
function flightEndSec({ cents, capped }) {
  if (cents <= 100) return 0;                       // 1.00× 直接结束
  if (capped) return Math.log(MAX_CENTS / 100) / K; // 到 100.00× 的时刻
  return Math.log((cents + 1) / 100) / K;           // 倍率即将越过 cents 的时刻
}

// 自动收手目标（百分之一倍）被触发的时刻（秒）
function autoTimeSec(autoCents) {
  return Math.log(autoCents / 100) / K;
}

module.exports = { K, MAX_CENTS, MIN_CASH_CENTS, drawCrash, multCentsAt, flightEndSec, autoTimeSec };

return module.exports; })();

const PORT = +process.env.PORT || 3000;
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const BET_MS = +process.env.BET_MS || 5000;      // 起飞前倒计时
const CRASH_MS = +process.env.CRASH_MS || 4500;  // 飞走后停留，再开下一局
const START_BALANCE = 10000;
const CHIPS = [100, 200, 500];
const ROOM_CAP = 60;
// 仅用于自动化测试：指定接下来每局的最后倍率（逗号分隔，如 "2.5,1.0,100"），循环使用
const TEST_CRASHES = process.env.TEST_CRASHES
  ? process.env.TEST_CRASHES.split(',').map((s) => Math.round(parseFloat(s) * 100)) : null;
let testIdx = 0;

/* ------------------------------ 玩家与持久化 ------------------------------ */
const players = new Map(); // token -> player
const playersById = new Map();
const PLAYERS_FILE = path.join(DATA_DIR, 'players.json');

function loadPlayers() {
  try {
    const arr = JSON.parse(fs.readFileSync(PLAYERS_FILE, 'utf8'));
    const cutoff = Date.now() - 30 * 86400e3;
    for (const p of arr) {
      if ((p.lastSeen || 0) < cutoff) continue;
      players.set(p.token, p);
      playersById.set(p.id, p);
    }
  } catch (_) { /* 首次启动 */ }
}
let saveTimer = null;
function saveSoon() { if (!saveTimer) saveTimer = setTimeout(() => { saveTimer = null; saveNow(); }, 2000); }
function saveNow() {
  try {
    // 持久化时把进行中、尚未结算的押分退回到余额：服务器重启不会让人白白损失积分
    const pending = new Map();
    for (const room of rooms.values()) {
      for (const [pid, b] of room.bets) if (b.state === 'placed') pending.set(pid, (pending.get(pid) || 0) + b.amount);
    }
    const out = [...players.values()].map((p) => ({ ...p, balance: p.balance + (pending.get(p.id) || 0) }));
    fs.mkdirSync(DATA_DIR, { recursive: true });
    const tmp = PLAYERS_FILE + '.tmp';
    fs.writeFileSync(tmp, JSON.stringify(out));
    fs.renameSync(tmp, PLAYERS_FILE);
  } catch (e) { console.error('save failed', e.message); }
}

function cleanName(s) {
  const t = String(s ?? '').replace(/[\u0000-\u001f\u007f<>]/g, '').replace(/\s+/g, ' ').trim();
  return [...t].slice(0, 12).join('');
}
function newId() { return crypto.randomBytes(5).toString('hex'); }

/* ---------------------------------- 房间 ---------------------------------- */
const rooms = new Map();

class Room {
  constructor(code) {
    this.code = code;
    this.phase = 'idle';   // idle | betting | flying | crashed
    this.round = 0;
    this.clients = new Set(); // { res, pid }
    this.presence = new Map(); // pid -> 连接数
    this.bets = new Map();     // pid -> bet
    this.history = [];
    this.startAt = 0; this.nextAt = 0;
    this.crash = null;         // { cents, capped } —— 开奖结果，本局结束前只保存在服务器
    this.endSec = 0;
    this.touched = Date.now();
  }

  newRound() {
    this.round += 1;
    this.phase = 'betting';
    this.bets = new Map();
    // 本局独立抽一次随机数
    if (TEST_CRASHES) {
      const c = TEST_CRASHES[testIdx++ % TEST_CRASHES.length];
      this.crash = { cents: Math.max(100, Math.min(G.MAX_CENTS, c)), capped: c >= G.MAX_CENTS };
    } else {
      this.crash = G.drawCrash();
    }
    this.endSec = G.flightEndSec(this.crash);
    this.startAt = Date.now() + BET_MS;
    this.nextAt = 0;
    this.broadcast();
  }

  // 把房间状态推进到 now（所有判定都以服务器时间为准）
  advance(now) {
    if (this.phase === 'betting' && now >= this.startAt) {
      this.phase = 'flying';
      this.broadcast();
    }
    if (this.phase === 'flying') {
      const t = (now - this.startAt) / 1000;
      this.settleAutos(Math.min(t, this.endSec));
      if (t >= this.endSec) this.finish(now);
    } else if (this.phase === 'crashed' && now >= this.nextAt) {
      if (this.clients.size > 0) this.newRound(); else { this.phase = 'idle'; this.broadcast(); }
    }
  }

  // 触发已到达的自动收手：恰好等于最后倍率也算成功
  settleAutos(tSec) {
    let changed = false;
    for (const [pid, b] of this.bets) {
      if (b.state !== 'placed' || b.auto == null) continue;
      if (b.auto <= this.crash.cents && G.autoTimeSec(b.auto) <= tSec + 1e-9) {
        this.cash(pid, b, b.auto); changed = true;
      }
    }
    if (changed) this.broadcast();
  }

  // 结算一次收手；只有 state==='placed' 才会生效，所以重复调用不会重复发分
  cash(pid, b, multCents) {
    if (b.state !== 'placed') return false;
    const payout = (b.amount / 100) * multCents; // 押分是 100 的整数倍，所以结果恒为整数
    b.state = 'cashed'; b.multCents = multCents; b.payout = payout;
    const p = playersById.get(pid);
    if (p) p.balance += payout;
    saveSoon();
    return true;
  }

  finish(now) {
    for (const [pid, b] of this.bets) {
      if (b.state !== 'placed') continue;
      if (this.crash.capped) this.cash(pid, b, G.MAX_CENTS); // 100× 自动结算所有仍在场玩家
      else b.state = 'lost';
    }
    this.history.push({ r: this.round, c: this.crash.cents / 100, maxed: this.crash.capped });
    if (this.history.length > 30) this.history.shift();
    this.phase = 'crashed';
    this.nextAt = now + CRASH_MS;
    this.broadcast();
    saveSoon();
  }

  /* --- 推送 --- */
  shared() {
    const list = new Map();
    for (const [pid, n] of this.presence) if (n > 0) list.set(pid, true);
    for (const pid of this.bets.keys()) if (!list.has(pid)) list.set(pid, false);
    const ps = [];
    for (const [pid, online] of list) {
      const p = playersById.get(pid); if (!p) continue;
      const b = this.bets.get(pid);
      ps.push({
        id: pid, name: p.name, online,
        bet: b ? { amount: b.amount, state: b.state, mult: b.multCents ? b.multCents / 100 : null, payout: b.payout || 0 } : null,
      });
    }
    const crashed = this.phase === 'crashed';
    return {
      type: 'state', room: this.code, phase: this.phase, round: this.round, k: G.K,
      now: Date.now(), startAt: this.startAt, nextAt: this.nextAt,
      crash: crashed ? this.crash.cents / 100 : null,      // 开奖结果只在本局结束后才下发
      maxed: crashed ? this.crash.capped : false,
      history: this.history, players: ps, online: [...this.presence.values()].filter((n) => n > 0).length,
    };
  }
  meFor(pid) {
    const p = playersById.get(pid); const b = this.bets.get(pid);
    return {
      id: pid, name: p.name, balance: p.balance, auto: p.auto ? p.auto / 100 : null,
      canRefill: p.balance < CHIPS[0],
      bet: b ? { amount: b.amount, state: b.state, mult: b.multCents ? b.multCents / 100 : null, payout: b.payout || 0, auto: b.auto ? b.auto / 100 : null } : null,
    };
  }
  sendTo(c, shared) {
    try { c.res.write('data: ' + JSON.stringify({ ...shared, me: this.meFor(c.pid) }) + '\n\n'); } catch (_) { /* 连接已断 */ }
  }
  broadcast() {
    if (!this.clients.size) return;
    const s = this.shared();
    for (const c of this.clients) this.sendTo(c, s);
  }
}

function getRoom(code) {
  let r = rooms.get(code);
  if (!r) { if (rooms.size >= 500) return null; r = new Room(code); rooms.set(code, r); }
  r.touched = Date.now();
  return r;
}

setInterval(() => {
  const now = Date.now();
  for (const [code, r] of rooms) {
    if (r.phase !== 'idle') r.advance(now);
    if (r.clients.size === 0 && r.phase === 'idle' && now - r.touched > 30 * 60e3) rooms.delete(code);
  }
}, 40);
setInterval(() => { for (const r of rooms.values()) for (const c of r.clients) { try { c.res.write(': hb\n\n'); } catch (_) {} } }, 15000);

/* ------------------------------ 动作（均幂等） ------------------------------ */
function parseAuto(v) {
  if (v === null || v === undefined || v === '' || v === 0) return null;
  const x = Number(v);
  if (!Number.isFinite(x) || x < 1.01 || x > 100) return undefined;
  return Math.round(x * 100);
}

function doBet(room, p, amount) {
  const now = Date.now();
  room.advance(now);
  if (room.phase !== 'betting' || now >= room.startAt) return { ok: false, reason: 'closed' };
  amount = Number(amount);
  const old = room.bets.get(p.id);
  const refund = old && old.state === 'placed' ? old.amount : 0;
  if (amount === 0) {
    if (old) { p.balance += refund; room.bets.delete(p.id); }
  } else {
    if (!CHIPS.includes(amount)) return { ok: false, reason: 'badamount' };
    if (p.balance + refund < amount) return { ok: false, reason: 'insufficient' };
    p.balance += refund - amount;
    room.bets.set(p.id, { amount, auto: p.auto || null, state: 'placed', multCents: 0, payout: 0 });
  }
  saveSoon(); room.broadcast();
  return { ok: true };
}

function doCashout(room, p) {
  const now = Date.now();
  room.advance(now);   // 先把房间推进到「服务器收到请求」的这一刻
  const b = room.bets.get(p.id);
  if (!b) return { ok: false, reason: 'nobet' };
  if (b.state === 'cashed') return { ok: true, already: true, mult: b.multCents / 100, payout: b.payout }; // 重复点击/重放
  if (b.state === 'lost') return { ok: false, reason: 'crashed' };
  if (room.phase !== 'flying') return { ok: false, reason: 'notflying' };
  const t = (now - room.startAt) / 1000;
  const m = Math.min(G.multCentsAt(t), room.crash.cents);
  if (m < G.MIN_CASH_CENTS) return { ok: false, reason: 'tooearly' };
  room.cash(p.id, b, m);
  room.broadcast();
  return { ok: true, mult: m / 100, payout: b.payout };
}

function doAuto(room, p, v) {
  const auto = parseAuto(v);
  if (auto === undefined) return { ok: false, reason: 'badauto' };
  if (room) {
    room.advance(Date.now());
    const b = room.bets.get(p.id);
    if (b && b.state === 'placed' && room.phase !== 'betting') return { ok: false, reason: 'locked' };
    if (b && b.state === 'placed') b.auto = auto;
  }
  p.auto = auto;
  saveSoon();
  if (room) room.broadcast();
  return { ok: true };
}

/* ----------------------------------- HTTP ----------------------------------- */
const ASSETS = {"index.html": "<!doctype html>\n<html lang=\"zh-CN\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no,viewport-fit=cover\">\n<meta name=\"theme-color\" content=\"#0a1330\">\n<title>一起起飞</title>\n<link rel=\"icon\" href=\"/favicon.svg\">\n<link rel=\"stylesheet\" href=\"/style.css\">\n</head>\n<body>\n\n<main id=\"landing\" class=\"view hidden\">\n  <div class=\"landing-card\">\n    <svg class=\"logo\" viewBox=\"0 0 64 64\" aria-hidden=\"true\"><use href=\"/favicon.svg#p\"/></svg>\n    <h1>一起起飞</h1>\n    <p class=\"tag\">开个房间，把链接发到群里<br>和朋友看同一架飞机，赌谁收手最稳</p>\n    <button id=\"btnCreate\" class=\"cta\">创建房间</button>\n    <div class=\"join-row\">\n      <input id=\"inpCode\" placeholder=\"或输入房间码\" maxlength=\"8\" autocapitalize=\"characters\" autocomplete=\"off\">\n      <button id=\"btnJoinCode\" class=\"ghost\">进入</button>\n    </div>\n    <p class=\"fine\">只用游戏积分，没有任何真实货币。理论返还率 95%。</p>\n  </div>\n</main>\n\n<main id=\"game\" class=\"view hidden\">\n  <header>\n    <div class=\"room\">\n      <span class=\"room-label\">房间</span><b id=\"roomCode\"></b>\n      <span id=\"online\" class=\"online\"></span>\n    </div>\n    <button id=\"btnInvite\" class=\"invite\">邀请朋友</button>\n    <div class=\"bal\"><span class=\"bal-label\">积分</span><b id=\"balance\">—</b></div>\n  </header>\n\n  <section id=\"stage\">\n    <canvas id=\"cv\"></canvas>\n    <div id=\"hud\">\n      <div id=\"mult\">—</div>\n      <div id=\"sub\"></div>\n    </div>\n    <div id=\"conn\" class=\"conn hidden\">重连中…</div>\n  </section>\n\n  <div id=\"history\" aria-label=\"最近几局的最后倍率\"></div>\n\n  <section id=\"panel\">\n    <div class=\"row-label\">押分 <small id=\"betHint\"></small></div>\n    <div id=\"chips\" class=\"chips\">\n      <button class=\"chip\" data-amt=\"100\">100</button>\n      <button class=\"chip\" data-amt=\"200\">200</button>\n      <button class=\"chip\" data-amt=\"500\">500</button>\n    </div>\n    <div class=\"row-label\">自动收手 <small id=\"autoHint\"></small></div>\n    <div id=\"autos\" class=\"autos\">\n      <button class=\"pill\" data-auto=\"\">关</button>\n      <button class=\"pill\" data-auto=\"1.5\">1.5×</button>\n      <button class=\"pill\" data-auto=\"2\">2×</button>\n      <button class=\"pill\" data-auto=\"3\">3×</button>\n      <button class=\"pill\" data-auto=\"5\">5×</button>\n      <button class=\"pill\" data-auto=\"10\">10×</button>\n      <button class=\"pill\" data-auto=\"custom\">自定义</button>\n    </div>\n    <div id=\"customRow\" class=\"custom hidden\">\n      <input id=\"inpAuto\" inputmode=\"decimal\" placeholder=\"1.01 ~ 100\" autocomplete=\"off\">\n      <span>×</span>\n      <button id=\"btnAutoOk\" class=\"ghost\">确定</button>\n    </div>\n    <button id=\"action\" class=\"action\" disabled>连接中…</button>\n    <button id=\"btnRefill\" class=\"refill hidden\">积分用完了 · 免费补满 10,000</button>\n  </section>\n\n  <section id=\"players\">\n    <div class=\"players-head\"><span>牌桌</span><span id=\"pcount\"></span></div>\n    <ul id=\"plist\"></ul>\n  </section>\n  <footer class=\"fine\">只用游戏积分 · 理论返还率 95% · 请理性娱乐</footer>\n</main>\n\n<div id=\"nameModal\" class=\"modal hidden\">\n  <form id=\"nameForm\" class=\"modal-card\">\n    <h2>你叫什么？</h2>\n    <p>朋友们会在牌桌上看到这个昵称</p>\n    <input id=\"inpName\" maxlength=\"12\" placeholder=\"昵称（最多 12 个字）\" autocomplete=\"off\" required>\n    <button class=\"cta\" type=\"submit\">进入房间</button>\n  </form>\n</div>\n<div id=\"toast\" class=\"toast\"></div>\n<script src=\"/app.js\"></script>\n</body>\n</html>\n", "app.js": "'use strict';\n(() => {\n  const $ = (s) => document.querySelector(s);\n  const store = {\n    get(k) { try { return localStorage.getItem(k); } catch (_) { return null; } },\n    set(k, v) { try { localStorage.setItem(k, v); } catch (_) {} },\n  };\n  const ROOM = (location.pathname.match(/^\\/r\\/([A-Za-z0-9]{4,8})\\/?$/) || [])[1]?.toUpperCase() || null;\n  const fmt = (n) => Math.round(n).toLocaleString('en-US');\n  const fx = (m) => m.toFixed(2) + '×';\n\n  /* ------------------------------ 网络 ------------------------------ */\n  let ident = null;\n  try { ident = JSON.parse(store.get('qf_ident') || 'null'); } catch (_) {}\n  async function api(path, body) {\n    try {\n      const r = await fetch(path, { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify(body) });\n      const j = await r.json().catch(() => ({}));\n      j.status = r.status; return j;\n    } catch (_) { return { ok: false, reason: 'net' }; }\n  }\n  let toastTimer;\n  function toast(msg, ms = 2200) {\n    const t = $('#toast'); t.textContent = msg; t.classList.add('show');\n    clearTimeout(toastTimer); toastTimer = setTimeout(() => t.classList.remove('show'), ms);\n  }\n\n  // 校准与服务器的时钟差（取往返最短的一次），动画里的倍率才和服务器同步\n  let clockOffset = 0;\n  async function syncClock() {\n    let best = null;\n    for (let i = 0; i < 5; i++) {\n      const c0 = Date.now(), p0 = performance.now();\n      try {\n        const j = await (await fetch('/api/time', { cache: 'no-store' })).json();\n        const rtt = performance.now() - p0;\n        if (!best || rtt < best.rtt) best = { rtt, off: j.t - (c0 + rtt / 2) };\n      } catch (_) {}\n    }\n    if (best) clockOffset = best.off;\n  }\n  const now = () => Date.now() + clockOffset;\n\n  /* ------------------------------ 状态 ------------------------------ */\n  let S = null;            // 最近一次服务器状态\n  let es = null;\n  let customOpen = false;\n  let cashing = false;\n  let flight = { round: 0, trail: [] };\n  let crashAnim = null;    // { t0 }\n  let lastSettledRound = 0;\n\n  function liveCents() {\n    if (!S || S.phase !== 'flying') return 100;\n    const t = Math.max(0, (now() - S.startAt) / 1000);\n    return Math.min(10000, Math.max(100, Math.floor(100 * Math.exp(S.k * t))));\n  }\n\n  function connect() {\n    if (es) es.close();\n    es = new EventSource(`/api/stream?room=${ROOM}&token=${encodeURIComponent(ident.token)}`);\n    es.onopen = () => $('#conn').classList.add('hidden');\n    es.onmessage = (ev) => { try { onState(JSON.parse(ev.data)); } catch (_) {} };\n    es.onerror = () => {\n      $('#conn').classList.remove('hidden');\n      if (es.readyState === 2) setTimeout(() => join(ident.name, true), 1500); // 服务器重启等导致被拒：重新登记后重连\n    };\n  }\n\n  function onState(s) {\n    const prev = S;\n    S = s;\n    if (!prev || prev.round !== s.round) { flight = { round: s.round, trail: [] }; crashAnim = null; }\n    if (s.phase === 'crashed' && (!prev || prev.phase !== 'crashed')) {\n      crashAnim = { t0: performance.now() };\n      if (s.round !== lastSettledRound) {\n        lastSettledRound = s.round;\n        const b = s.me.bet;\n        if (b && b.state === 'cashed') toast(`本局收手 ${fx(b.mult)} · 拿回 ${fmt(b.payout)} 分`);\n        else if (b && b.state === 'lost') toast(`飞走了 ${fx(s.crash)} · 输掉 ${fmt(b.amount)} 分`);\n      }\n    }\n    renderStatic();\n  }\n\n  /* ------------------------------ 加入房间 ------------------------------ */\n  async function join(name, silent) {\n    const j = await api('/api/join', { token: ident && ident.token, name });\n    if (!j.ok) { if (!silent) toast('进入失败，请重试'); return false; }\n    ident = { token: j.token, id: j.id, name: j.name };\n    store.set('qf_ident', JSON.stringify(ident));\n    connect();\n    return true;\n  }\n\n  async function enterGame() {\n    $('#game').classList.remove('hidden');\n    $('#roomCode').textContent = ROOM;\n    syncClock(); setInterval(syncClock, 30000);\n    requestAnimationFrame(frame);\n    const saved = ident && ident.name;\n    if (saved) { await join(saved); return; }\n    $('#nameModal').classList.remove('hidden');\n    $('#inpName').focus();\n  }\n  $('#nameForm').addEventListener('submit', async (e) => {\n    e.preventDefault();\n    const name = $('#inpName').value.trim();\n    if (!name) return;\n    if (await join(name)) $('#nameModal').classList.add('hidden');\n  });\n\n  /* ------------------------------ 操作 ------------------------------ */\n  const REASONS = {\n    closed: '这局已经起飞，下一局再押', insufficient: '积分不够啦', net: '网络不稳，再试一次',\n    crashed: '慢了一步，飞机已经飞走', tooearly: '倍率还没到 1.01×', locked: '已起飞，不能再改自动收手', badauto: '自动收手请填 1.01 ~ 100',\n  };\n  $('#chips').addEventListener('click', async (e) => {\n    const b = e.target.closest('.chip'); if (!b || !S) return;\n    const amt = +b.dataset.amt, cur = S.me.bet && S.me.bet.amount;\n    const j = await api('/api/bet', { token: ident.token, room: ROOM, amount: cur === amt ? 0 : amt });\n    if (!j.ok) toast(REASONS[j.reason] || '下注失败');\n  });\n  $('#autos').addEventListener('click', async (e) => {\n    const b = e.target.closest('.pill'); if (!b || !S) return;\n    const v = b.dataset.auto;\n    if (v === 'custom') { customOpen = !customOpen; renderStatic(); if (customOpen) $('#inpAuto').focus(); return; }\n    customOpen = false;\n    const j = await api('/api/auto', { token: ident.token, room: ROOM, auto: v === '' ? null : +v });\n    if (!j.ok) toast(REASONS[j.reason] || '设置失败');\n  });\n  async function submitCustom() {\n    const v = parseFloat($('#inpAuto').value);\n    const j = await api('/api/auto', { token: ident.token, room: ROOM, auto: v });\n    if (!j.ok) return toast(REASONS[j.reason] || '设置失败');\n    customOpen = false; $('#inpAuto').blur(); renderStatic();\n  }\n  $('#btnAutoOk').addEventListener('click', submitCustom);\n  $('#inpAuto').addEventListener('keydown', (e) => { if (e.key === 'Enter') submitCustom(); });\n\n  async function doCashout() {\n    if (cashing || !S) return;\n    const b = S.me.bet;\n    if (!b || b.state !== 'placed' || S.phase !== 'flying') return;\n    cashing = true;\n    const j = await api('/api/cashout', { token: ident.token, room: ROOM });\n    cashing = false;\n    if (j.ok) { if (navigator.vibrate) navigator.vibrate(25); toast(`已收手 ${fx(j.mult)} · 拿回 ${fmt(j.payout)} 分`); }\n    else toast(REASONS[j.reason] || '收手失败');\n  }\n  // 收手按钮用 pointerdown，少一次抬手延迟；重复点击由服务器保证只结算一次\n  $('#action').addEventListener('pointerdown', (e) => {\n    const b = S && S.me.bet;\n    if (S && S.phase === 'flying' && b && b.state === 'placed') { e.preventDefault(); doCashout(); }\n  });\n  $('#action').addEventListener('click', async () => {\n    const b = S && S.me.bet;\n    if (S && S.phase === 'betting' && b) {\n      const j = await api('/api/bet', { token: ident.token, room: ROOM, amount: 0 });\n      if (!j.ok) toast(REASONS[j.reason] || '取消失败');\n    }\n  });\n  $('#btnRefill').addEventListener('click', async () => {\n    const j = await api('/api/refill', { token: ident.token });\n    toast(j.ok ? '已补满 10,000 积分' : '积分还够，暂时不用补');\n  });\n  $('#btnInvite').addEventListener('click', async () => {\n    const url = location.origin + '/r/' + ROOM;\n    const text = `来「一起起飞」和我玩一局！房间 ${ROOM}`;\n    try { if (navigator.share) { await navigator.share({ title: '一起起飞', text, url }); return; } } catch (_) { return; }\n    try { await navigator.clipboard.writeText(`${text} ${url}`); toast('链接已复制，发到群里吧'); }\n    catch (_) { prompt('复制这个链接发给朋友', url); }\n  });\n\n  /* ------------------------------ 渲染（非动画部分） ------------------------------ */\n  const COLORS = ['#ffd166', '#7bdff2', '#b2f7ef', '#f7a8b8', '#c3a6ff', '#9be564', '#ffb36b'];\n  const colorOf = (id) => { let h = 0; for (const c of id) h = (h * 31 + c.charCodeAt(0)) >>> 0; return COLORS[h % COLORS.length]; };\n\n  function renderStatic() {\n    if (!S) return;\n    const me = S.me;\n    $('#balance').textContent = fmt(me.balance);\n    $('#online').textContent = `${S.online} 人在线`;\n    $('#pcount').textContent = `${S.players.filter((p) => p.bet).length} 人下注 · ${S.online} 人在线`;\n    $('#btnRefill').classList.toggle('hidden', !me.canRefill);\n\n    const b = me.bet, betting = S.phase === 'betting';\n    for (const el of document.querySelectorAll('.chip')) {\n      const amt = +el.dataset.amt;\n      el.classList.toggle('on', !!b && b.amount === amt);\n      el.disabled = !betting || (!(b && b.amount === amt) && me.balance + (b ? b.amount : 0) < amt);\n    }\n    $('#betHint').textContent = b ? `已押 ${fmt(b.amount)}（再点一次取消）` : (betting ? '起飞前点一下下注' : '下一局再押');\n\n    const locked = !!b && b.state === 'placed' && S.phase !== 'betting';\n    const presets = ['', '1.5', '2', '3', '5', '10'];\n    const cur = me.auto;\n    let curIsPreset = cur === null || presets.includes(String(cur));\n    for (const el of document.querySelectorAll('.pill')) {\n      const v = el.dataset.auto;\n      el.disabled = locked;\n      el.classList.toggle('on', v === 'custom' ? (!curIsPreset || customOpen) : (cur === null ? v === '' : Number(v) === cur && v !== ''));\n      if (v === 'custom') el.textContent = !curIsPreset ? `${cur}×` : '自定义';\n    }\n    $('#autoHint').textContent = cur ? `到 ${cur}× 自动收手` : '手动收手';\n    $('#customRow').classList.toggle('hidden', !customOpen);\n\n    // 历史\n    $('#history').replaceChildren(...S.history.slice().reverse().map((h) => {\n      const d = document.createElement('span');\n      d.className = 'h' + (h.c >= 10 ? ' hi' : h.c >= 2 ? ' mid' : '');\n      d.textContent = fx(h.c); return d;\n    }));\n\n    // 牌桌\n    const rank = (p) => (p.id === me.id ? 0 : p.bet ? 1 : 2);\n    const ps = S.players.slice().sort((a, c) => rank(a) - rank(c) || (c.bet ? c.bet.amount : 0) - (a.bet ? a.bet.amount : 0));\n    $('#plist').replaceChildren(...ps.map((p) => {\n      const li = document.createElement('li'); if (!p.online) li.className = 'off';\n      const av = document.createElement('div'); av.className = 'av'; av.style.background = colorOf(p.id); av.textContent = [...p.name][0] || '?';\n      const nm = document.createElement('div'); nm.className = 'pn'; nm.textContent = p.name;\n      if (p.id === me.id) { const i = document.createElement('i'); i.textContent = '我'; nm.append(i); }\n      const bt = document.createElement('div'); bt.className = 'pb'; bt.textContent = p.bet ? `押 ${fmt(p.bet.amount)}` : '';\n      const st = document.createElement('div'); st.className = 'ps';\n      const k = p.bet;\n      if (!k) { st.classList.add('dim'); st.textContent = S.phase === 'betting' ? '观望中' : '围观'; }\n      else if (k.state === 'cashed') { st.classList.add('win'); st.textContent = `${fx(k.mult)} +${fmt(k.payout - k.amount)}`; }\n      else if (k.state === 'lost') { st.classList.add('lose'); st.textContent = `−${fmt(k.amount)}`; }\n      else { st.classList.add(S.phase === 'betting' ? 'dim' : 'fly'); st.textContent = S.phase === 'betting' ? '已下注' : '飞行中…'; }\n      li.append(av, nm, bt, st); return li;\n    }));\n  }\n\n  /* ------------------------------ 每帧：倍率、按钮、画面 ------------------------------ */\n  const multEl = $('#mult'), subEl = $('#sub'), actEl = $('#action');\n  let lastAct = '';\n  function setAction(cls, html) {\n    const key = cls + '|' + html;\n    if (key === lastAct) return; lastAct = key;\n    actEl.className = 'action ' + cls; actEl.innerHTML = html;\n    actEl.disabled = cls === '' || cls === 'done' || cls === 'lose';\n  }\n  const esc = (s) => String(s).replace(/[&<>]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));\n\n  function updateHud() {\n    if (!S) { multEl.textContent = '…'; subEl.textContent = '连接中'; setAction('', '连接中…'); return; }\n    const me = S.me, b = me.bet;\n    multEl.classList.remove('crashed', 'count');\n    if (S.phase === 'betting') {\n      const left = Math.max(0, Math.ceil((S.startAt - now()) / 1000));\n      multEl.textContent = left; multEl.classList.add('count');\n      subEl.textContent = b ? '已下注，准备起飞' : '秒后起飞 · 点筹码下注';\n      if (b) setAction('cancel', `已押 ${fmt(b.amount)} 分<small>点这里取消</small>`);\n      else setAction('', me.balance < 100 ? '积分不够了，先补满' : '点上方筹码下注，或本局围观');\n    } else if (S.phase === 'flying') {\n      const c = liveCents();\n      multEl.textContent = fx(c / 100); subEl.textContent = '飞行中';\n      if (b && b.state === 'placed') {\n        setAction('cash', `收手<small>现在收手可拿回 ${fmt(b.amount * c / 100)} 分</small>`);\n      } else if (b && b.state === 'cashed') {\n        setAction('done', `已收手 ${fx(b.mult)}<small>拿回 ${fmt(b.payout)} 分，看看朋友能飞多高</small>`);\n      } else setAction('', '围观中 · 下一局再押');\n    } else if (S.phase === 'crashed') {\n      multEl.textContent = fx(S.crash); multEl.classList.add('crashed');\n      subEl.textContent = S.maxed ? '满倍 100× · 在场玩家自动结算' : '飞机飞走了';\n      if (b && b.state === 'cashed') setAction('done', `赢了 +${fmt(b.payout - b.amount)}<small>${fx(b.mult)} 收手，拿回 ${fmt(b.payout)} 分</small>`);\n      else if (b && b.state === 'lost') setAction('lose', `输了 −${fmt(b.amount)}<small>${esc(fx(S.crash))} 飞走时还没收手</small>`);\n      else setAction('', `本局围观 · 飞到了 ${fx(S.crash)}`);\n    } else { multEl.textContent = '—'; subEl.textContent = '等待开局…'; setAction('', '等待开局…'); }\n  }\n\n  /* ------------------------------ 画面 ------------------------------ */\n  const cv = $('#cv'), ctx = cv.getContext('2d');\n  let W = 0, H = 0, dpr = 1;\n  function resize() {\n    dpr = Math.min(2, window.devicePixelRatio || 1);\n    const r = cv.getBoundingClientRect(); W = r.width; H = r.height;\n    cv.width = Math.round(W * dpr); cv.height = Math.round(H * dpr);\n  }\n  new ResizeObserver(resize).observe(cv);\n  const stars = Array.from({ length: 46 }, () => ({ x: Math.random(), y: Math.random(), r: 0.6 + Math.random() * 1.6, v: 0.3 + Math.random() }));\n  const clouds = Array.from({ length: 5 }, () => ({ x: Math.random(), y: Math.random(), s: 0.6 + Math.random() * 0.9, v: 0.5 + Math.random() }));\n  let scroll = 0, lastTs = 0;\n\n  function planePos(u) {            // u = ln(倍率)，飞机沿曲线向右上，越往后越靠近右上角\n    const f = 1 - Math.exp(-u / 1.5);\n    return { x: W * (0.14 + 0.62 * f), y: H * (0.78 - 0.5 * f) };\n  }\n  function drawPlane(x, y, ang, s, alpha, flame) {\n    ctx.save(); ctx.translate(x, y); ctx.rotate(ang); ctx.scale(s, s); ctx.globalAlpha = alpha;\n    if (flame) { ctx.fillStyle = 'rgba(255,170,60,.9)'; ctx.beginPath(); ctx.moveTo(-1.0, -0.04); ctx.lineTo(-1.55 - Math.random() * 0.25, 0.02); ctx.lineTo(-1.0, 0.1); ctx.fill(); }\n    ctx.fillStyle = '#ff7a1a'; ctx.beginPath(); ctx.moveTo(-0.8, -0.05); ctx.lineTo(-1.15, -0.55); ctx.lineTo(-0.6, -0.55); ctx.lineTo(-0.35, -0.08); ctx.fill(); // 尾翼\n    ctx.fillStyle = '#c9d4f2'; ctx.beginPath(); ctx.moveTo(-0.15, 0.02); ctx.lineTo(-0.7, 0.62); ctx.lineTo(-0.35, 0.62); ctx.lineTo(0.35, 0.05); ctx.fill(); // 远侧机翼\n    ctx.fillStyle = '#f4f7ff'; ctx.beginPath(); ctx.moveTo(-1.0, -0.03);\n    ctx.quadraticCurveTo(-0.95, -0.27, -0.3, -0.28); ctx.lineTo(0.5, -0.24); ctx.quadraticCurveTo(1.25, -0.1, 1.3, 0.05);\n    ctx.quadraticCurveTo(1.0, 0.27, 0.3, 0.27); ctx.lineTo(-0.7, 0.2); ctx.closePath(); ctx.fill(); // 机身\n    ctx.fillStyle = '#5aa2ff'; ctx.beginPath(); ctx.moveTo(0.55, -0.2); ctx.quadraticCurveTo(1.0, -0.16, 1.1, -0.03); ctx.lineTo(0.55, -0.03); ctx.fill(); // 驾驶舱\n    ctx.fillStyle = '#9fb3e8'; for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.arc(-0.2 + i * 0.2, -0.06, 0.04, 0, 7); ctx.fill(); }\n    ctx.fillStyle = '#dfe7ff'; ctx.beginPath(); ctx.moveTo(-0.05, 0.05); ctx.lineTo(-0.62, 0.72); ctx.lineTo(-0.28, 0.72); ctx.lineTo(0.5, 0.08); ctx.fill(); // 近侧机翼\n    ctx.restore();\n  }\n\n  function draw(ts) {\n    const dt = Math.min(0.05, (ts - lastTs) / 1000 || 0.016); lastTs = ts;\n    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);\n    const g = ctx.createLinearGradient(0, 0, 0, H);\n    g.addColorStop(0, '#0a1740'); g.addColorStop(0.6, '#1a3a8c'); g.addColorStop(1, '#3b72d9');\n    ctx.fillStyle = g; ctx.fillRect(0, 0, W, H);\n\n    const phase = S ? S.phase : 'idle';\n    const cents = phase === 'flying' ? liveCents() : (phase === 'crashed' ? Math.round(S.crash * 100) : 100);\n    const u = Math.log(cents / 100);\n    const speed = phase === 'flying' ? 14 + Math.min(u, 4.6) * 26 : phase === 'crashed' ? 8 : 6;\n    scroll += speed * dt;\n\n    ctx.fillStyle = '#fff';\n    for (const s of stars) {\n      const y = ((s.y * H + scroll * s.v * 0.5) % H);\n      ctx.globalAlpha = 0.35 + 0.4 * s.v; ctx.beginPath(); ctx.arc(s.x * W, y, s.r, 0, 7); ctx.fill();\n    }\n    ctx.globalAlpha = 0.16; ctx.fillStyle = '#fff';\n    for (const c of clouds) {\n      const y = ((c.y * H + scroll * c.v * 1.4) % (H + 60)) - 30, x = c.x * W - ((scroll * c.v * 0.6) % 40);\n      for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.ellipse(x + i * 22 * c.s, y + (i % 2) * 6, 34 * c.s, 13 * c.s, 0, 0, 7); ctx.fill(); }\n    }\n    ctx.globalAlpha = 1;\n\n    const size = Math.min(W, H) * 0.13;\n    if (phase === 'betting' || phase === 'idle' || !S) {\n      // 停机坪\n      ctx.fillStyle = '#0d1b45'; ctx.fillRect(0, H * 0.86, W, H * 0.14);\n      ctx.fillStyle = 'rgba(255,255,255,.35)'; for (let x = 10; x < W; x += 44) ctx.fillRect(x, H * 0.92, 24, 3);\n      const p = planePos(0); const sh = Math.sin(ts / 60) * 0.6;\n      drawPlane(p.x, H * 0.86 - size * 0.3 + sh, -0.06, size, 1, false);\n    } else if (phase === 'flying') {\n      const p = planePos(u);\n      const bob = Math.sin(ts / 420) * 3 * Math.min(1, u);\n      const q = planePos(u + 0.02); const ang = Math.atan2(q.y - p.y, q.x - p.x);\n      flight.trail.push([p.x, p.y + bob]); if (flight.trail.length > 90) flight.trail.shift();\n      drawTrail(); drawPlane(p.x, p.y + bob, ang * 0.9, size, 1, true);\n    } else if (phase === 'crashed') {\n      const p = planePos(u); const k = crashAnim ? Math.min(1.4, (performance.now() - crashAnim.t0) / 700) : 1.4;\n      const fx_ = p.x + k * k * W * 0.7, fy_ = p.y - k * k * H * 0.5;\n      drawTrail(); if (k < 1.4) drawPlane(fx_, fy_, -0.6, size, Math.max(0, 1 - k / 1.4), true);\n    }\n  }\n  function drawTrail() {\n    const t = flight.trail; if (t.length < 2) return;\n    ctx.lineCap = 'round';\n    for (let i = 1; i < t.length; i++) {\n      ctx.strokeStyle = `rgba(255,190,110,${(i / t.length) * 0.55})`; ctx.lineWidth = 1 + (i / t.length) * 4;\n      ctx.beginPath(); ctx.moveTo(t[i - 1][0], t[i - 1][1]); ctx.lineTo(t[i][0], t[i][1]); ctx.stroke();\n    }\n  }\n\n  function frame(ts) { updateHud(); draw(ts); requestAnimationFrame(frame); }\n\n  /* ------------------------------ 首页 ------------------------------ */\n  function landing() {\n    $('#landing').classList.remove('hidden');\n    $('#btnCreate').addEventListener('click', async () => {\n      try { const j = await (await fetch('/api/new-room', { cache: 'no-store' })).json(); location.href = '/r/' + j.room; }\n      catch (_) { toast('网络不稳，再试一次'); }\n    });\n    const go = () => { const c = $('#inpCode').value.trim().toUpperCase(); if (/^[A-Z0-9]{4,8}$/.test(c)) location.href = '/r/' + c; else toast('房间码是 4~8 位字母数字'); };\n    $('#btnJoinCode').addEventListener('click', go);\n    $('#inpCode').addEventListener('keydown', (e) => { if (e.key === 'Enter') go(); });\n  }\n\n  document.addEventListener('visibilitychange', () => { if (!document.hidden && es && es.readyState === 2) join(ident.name, true); });\n  if (ROOM) enterGame(); else landing();\n})();\n", "style.css": ":root {\n  --bg: #0a1330; --bg2: #101d4a; --card: rgba(255,255,255,.07); --line: rgba(255,255,255,.12);\n  --text: #eef2ff; --dim: #9aa8d6; --green: #22c55e; --green-d: #16a34a; --orange: #ff8a1f;\n  --red: #ff4d5e; --gold: #ffc43d; --blue: #5aa2ff;\n  --safe-b: env(safe-area-inset-bottom, 0px);\n}\n* { box-sizing: border-box; -webkit-tap-highlight-color: transparent; }\nhtml, body { margin: 0; height: 100%; background: var(--bg); color: var(--text);\n  font: 15px/1.35 -apple-system, BlinkMacSystemFont, \"PingFang SC\", \"Noto Sans SC\", \"Microsoft YaHei\", sans-serif; }\nbody { overscroll-behavior: none; }\nbutton { font: inherit; color: inherit; border: 0; cursor: pointer; touch-action: manipulation; }\ninput { font: inherit; color: inherit; }\n.hidden { display: none !important; }\n.fine { color: var(--dim); font-size: 12px; text-align: center; margin: 10px 0 0; }\n\n.view { max-width: 480px; margin: 0 auto; min-height: 100dvh; }\n\n/* 首页 */\n#landing { display: flex; align-items: center; justify-content: center; padding: 24px;\n  background: radial-gradient(120% 80% at 50% 0%, #1b2f78 0%, var(--bg) 60%); }\n.landing-card { text-align: center; width: 100%; }\n.logo { width: 84px; height: 84px; border-radius: 20px; background: #0e1b45; box-shadow: 0 10px 30px rgba(0,0,0,.4); }\nh1 { margin: 14px 0 6px; font-size: 34px; letter-spacing: 2px; }\n.tag { color: var(--dim); margin: 0 0 26px; }\n.cta { width: 100%; padding: 16px; border-radius: 16px; font-size: 18px; font-weight: 700; color: #1b1000;\n  background: linear-gradient(180deg, #ffb347, var(--orange)); box-shadow: 0 6px 18px rgba(255,138,31,.35); }\n.cta:active { transform: translateY(1px); }\n.ghost { padding: 12px 16px; border-radius: 12px; background: var(--card); border: 1px solid var(--line); }\n.join-row { display: flex; gap: 8px; margin-top: 14px; }\n.join-row input, #inpName, #inpAuto { flex: 1; min-width: 0; padding: 12px 14px; border-radius: 12px; background: rgba(0,0,0,.25);\n  border: 1px solid var(--line); outline: none; }\n.join-row input { text-transform: uppercase; }\n\n/* 游戏页：竖屏单列 */\n#game { display: flex; flex-direction: column; padding: 0 12px calc(8px + var(--safe-b));\n  background: linear-gradient(180deg, var(--bg2) 0%, var(--bg) 40%); }\nheader { display: flex; align-items: center; gap: 8px; padding: 10px 0 8px; }\n.room { flex: 1; min-width: 0; display: flex; align-items: baseline; gap: 6px; white-space: nowrap; }\n.room-label, .bal-label { color: var(--dim); font-size: 12px; }\n.room b { font-size: 17px; letter-spacing: 2px; }\n.online { color: var(--dim); font-size: 12px; overflow: hidden; text-overflow: ellipsis; }\n.invite { padding: 7px 12px; border-radius: 999px; background: var(--card); border: 1px solid var(--line); font-size: 13px; }\n.bal { display: flex; flex-direction: column; align-items: flex-end; line-height: 1.1; min-width: 70px; }\n.bal b { font-size: 18px; color: var(--gold); font-variant-numeric: tabular-nums; }\n\n#stage { position: relative; height: clamp(210px, 34dvh, 330px); border-radius: 20px; overflow: hidden;\n  border: 1px solid var(--line); background: #0b1a47; }\n#cv { position: absolute; inset: 0; width: 100%; height: 100%; display: block; }\n#hud { position: absolute; inset: 0; display: flex; flex-direction: column; align-items: center; justify-content: center;\n  pointer-events: none; text-align: center; text-shadow: 0 2px 14px rgba(0,0,0,.55); }\n#mult { font-size: clamp(54px, 18vw, 82px); font-weight: 800; font-variant-numeric: tabular-nums; letter-spacing: -1px; line-height: 1; }\n#sub { margin-top: 6px; color: #d7e0ff; font-size: 14px; min-height: 20px; }\n#mult.crashed { color: var(--red); }\n#mult.count { font-size: clamp(64px, 22vw, 96px); }\n.conn { position: absolute; top: 8px; left: 50%; transform: translateX(-50%); background: rgba(255,77,94,.9); padding: 3px 10px;\n  border-radius: 999px; font-size: 12px; }\n\n#history { display: flex; gap: 6px; overflow-x: auto; padding: 8px 0 2px; scrollbar-width: none; min-height: 36px; }\n#history::-webkit-scrollbar { display: none; }\n.h { flex: none; padding: 3px 9px; border-radius: 999px; font-size: 12px; font-weight: 700; font-variant-numeric: tabular-nums;\n  background: rgba(255,255,255,.09); color: #c3cdf0; }\n.h.mid { background: rgba(90,162,255,.2); color: var(--blue); }\n.h.hi { background: rgba(255,196,61,.2); color: var(--gold); }\n\n#panel { padding-top: 4px; }\n.row-label { color: var(--dim); font-size: 12px; margin: 8px 0 5px; }\n.row-label small { color: var(--text); margin-left: 6px; }\n.chips { display: grid; grid-template-columns: repeat(3, 1fr); gap: 8px; }\n.chip { padding: 12px 0; border-radius: 14px; font-size: 18px; font-weight: 700; background: var(--card); border: 1.5px solid var(--line);\n  font-variant-numeric: tabular-nums; }\n.chip.on { background: linear-gradient(180deg, #ffb347, var(--orange)); color: #1b1000; border-color: transparent; }\n.chip:disabled { opacity: .35; }\n.autos { display: flex; gap: 6px; flex-wrap: wrap; }\n.pill { padding: 7px 12px; border-radius: 999px; background: var(--card); border: 1px solid var(--line); font-size: 14px; }\n.pill.on { background: rgba(34,197,94,.22); border-color: var(--green); color: #b8f5cd; }\n.pill:disabled { opacity: .4; }\n.custom { display: flex; align-items: center; gap: 8px; margin-top: 8px; }\n.action { width: 100%; margin-top: 12px; padding: 14px 10px; min-height: 76px; border-radius: 20px; font-size: 22px; font-weight: 800;\n  line-height: 1.25; background: var(--card); border: 1.5px solid var(--line); color: var(--dim); }\n.action small { display: block; font-size: 15px; font-weight: 600; opacity: .95; }\n.action.cash { color: #04210f; border-color: transparent; background: linear-gradient(180deg, #4ade80, var(--green-d));\n  box-shadow: 0 0 0 0 rgba(74,222,128,.7); animation: pulse 1s infinite; font-size: 30px; min-height: 92px; }\n.action.cash:active { transform: scale(.985); }\n.action.done { color: #b8f5cd; background: rgba(34,197,94,.14); border-color: rgba(34,197,94,.5); }\n.action.lose { color: #ffb3bb; background: rgba(255,77,94,.12); border-color: rgba(255,77,94,.45); }\n.action.cancel { color: var(--text); background: rgba(255,138,31,.16); border-color: rgba(255,138,31,.55); }\n@keyframes pulse { 70% { box-shadow: 0 0 0 14px rgba(74,222,128,0); } 100% { box-shadow: 0 0 0 0 rgba(74,222,128,0); } }\n.refill { width: 100%; margin-top: 8px; padding: 12px; border-radius: 14px; font-weight: 700; color: #1b1000; background: var(--gold); }\n\n#players { margin-top: 12px; background: var(--card); border: 1px solid var(--line); border-radius: 16px; padding: 8px 10px; flex: 1; min-height: 120px; }\n.players-head { display: flex; justify-content: space-between; color: var(--dim); font-size: 12px; padding: 2px 2px 6px; }\n#plist { list-style: none; margin: 0; padding: 0; }\n#plist li { display: flex; align-items: center; gap: 10px; padding: 7px 2px; border-top: 1px solid rgba(255,255,255,.06); }\n#plist li:first-child { border-top: 0; }\n.av { width: 30px; height: 30px; border-radius: 50%; flex: none; display: grid; place-items: center; font-weight: 700; font-size: 14px; color: #0a1330; }\n.pn { flex: 1; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }\n.pn i { font-style: normal; color: var(--orange); font-size: 12px; margin-left: 4px; }\n.pb { color: var(--dim); font-variant-numeric: tabular-nums; font-size: 13px; }\n.ps { min-width: 88px; text-align: right; font-weight: 700; font-variant-numeric: tabular-nums; font-size: 14px; }\n.ps.win { color: var(--green); } .ps.lose { color: var(--red); } .ps.fly { color: var(--blue); } .ps.dim { color: var(--dim); font-weight: 500; }\n.off { opacity: .5; }\n\n/* 昵称弹窗 / 提示 */\n.modal { position: fixed; inset: 0; z-index: 10; display: grid; place-items: center; padding: 24px; background: rgba(5,9,25,.78); backdrop-filter: blur(4px); }\n.modal-card { width: 100%; max-width: 360px; background: #14235a; border: 1px solid var(--line); border-radius: 22px; padding: 22px; }\n.modal-card h2 { margin: 0 0 4px; } .modal-card p { margin: 0 0 14px; color: var(--dim); }\n.modal-card input { width: 100%; margin-bottom: 14px; }\n.toast { position: fixed; left: 50%; top: calc(70px + env(safe-area-inset-top, 0px)); transform: translate(-50%, -12px); opacity: 0; pointer-events: none;\n  background: rgba(20,30,70,.96); border: 1px solid var(--line); padding: 10px 16px; border-radius: 14px; max-width: 86vw; text-align: center;\n  transition: .25s; z-index: 20; }\n.toast.show { opacity: 1; transform: translate(-50%, 0); }\ninput { font-size: 16px; }\n", "favicon.svg": "<svg xmlns=\"http://www.w3.org/2000/svg\" xmlns:xlink=\"http://www.w3.org/1999/xlink\" viewBox=\"0 0 64 64\">\n  <defs>\n    <g id=\"p\">\n      <path d=\"M6 40 L58 14 L38 50 L30 38 Z\" fill=\"#f4f7ff\"/>\n      <path d=\"M30 38 L58 14 L26 44 Z\" fill=\"#c9d4f2\"/>\n      <path d=\"M30 38 L33 54 L38 50 Z\" fill=\"#ff7a1a\"/>\n    </g>\n  </defs>\n  <rect width=\"64\" height=\"64\" rx=\"14\" fill=\"#0e1b45\"/>\n  <use href=\"#p\"/>\n</svg>\n"};
const STATIC = {
  '/app.js': ['app.js', 'text/javascript; charset=utf-8'],
  '/style.css': ['style.css', 'text/css; charset=utf-8'],
  '/favicon.svg': ['favicon.svg', 'image/svg+xml'],
};
const HEADERS = {
  'X-Content-Type-Options': 'nosniff',
  'Referrer-Policy': 'no-referrer',
  'Content-Security-Policy': "default-src 'self'; img-src 'self' data:; style-src 'self' 'unsafe-inline'; connect-src 'self'; frame-ancestors 'none'",
};

function json(res, code, obj) {
  res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store', ...HEADERS });
  res.end(JSON.stringify(obj));
}
function readJson(req) {
  return new Promise((resolve, reject) => {
    let n = 0; const chunks = [];
    req.on('data', (c) => { n += c.length; if (n > 4096) { reject(new Error('big')); req.destroy(); } else chunks.push(c); });
    req.on('end', () => { try { resolve(JSON.parse(Buffer.concat(chunks).toString() || '{}')); } catch (e) { reject(e); } });
    req.on('error', reject);
  });
}
function normRoom(s) { const c = String(s || '').toUpperCase(); return /^[A-Z0-9]{4,8}$/.test(c) ? c : null; }

const server = http.createServer(async (req, res) => {
  try {
    const url = new URL(req.url, 'http://x');
    const p = url.pathname;
    if (req.method === 'GET') {
      if (p === '/' || /^\/r\/[A-Za-z0-9]{4,8}\/?$/.test(p)) {
        res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache', ...HEADERS });
        return res.end(ASSETS['index.html']);
      }
      if (STATIC[p]) {
        res.writeHead(200, { 'Content-Type': STATIC[p][1], 'Cache-Control': 'no-cache', ...HEADERS });
        return res.end(ASSETS[STATIC[p][0]]);
      }
      if (p === '/health') return json(res, 200, { ok: true, rooms: rooms.size });
      if (p === '/api/time') return json(res, 200, { t: Date.now() });
      if (p === '/api/new-room') {
        let code; do { code = Array.from(crypto.randomBytes(5), (b) => 'ABCDEFGHJKMNPQRSTUVWXYZ23456789'[b % 31]).join(''); } while (rooms.has(code));
        return json(res, 200, { room: code });
      }
      if (p === '/api/stream') {
        const code = normRoom(url.searchParams.get('room'));
        const pl = players.get(url.searchParams.get('token') || '');
        if (!code || !pl) return json(res, 401, { ok: false, reason: 'auth' });
        const room = getRoom(code);
        if (!room || (room.clients.size >= ROOM_CAP && !room.presence.get(pl.id))) return json(res, 503, { ok: false, reason: 'full' });
        res.writeHead(200, {
          'Content-Type': 'text/event-stream; charset=utf-8', 'Cache-Control': 'no-cache, no-transform',
          Connection: 'keep-alive', 'X-Accel-Buffering': 'no', ...HEADERS,
        });
        res.write('retry: 1500\n\n');
        const client = { res, pid: pl.id };
        room.clients.add(client);
        room.presence.set(pl.id, (room.presence.get(pl.id) || 0) + 1);
        pl.lastSeen = Date.now();
        if (room.phase === 'idle') room.newRound(); else room.advance(Date.now());
        room.broadcast();
        req.on('close', () => {
          room.clients.delete(client);
          const n = (room.presence.get(pl.id) || 1) - 1;
          if (n <= 0) room.presence.delete(pl.id); else room.presence.set(pl.id, n);
          room.touched = Date.now();
          room.broadcast();
        });
        return;
      }
      res.writeHead(404, HEADERS); return res.end('not found');
    }

    if (req.method === 'POST') {
      const body = await readJson(req);
      if (p === '/api/join') {
        const name = cleanName(body.name);
        if (!name) return json(res, 400, { ok: false, reason: 'name' });
        let pl = players.get(String(body.token || ''));
        if (!pl) {
          pl = { token: crypto.randomBytes(16).toString('hex'), id: newId(), name, balance: START_BALANCE, auto: null, lastSeen: Date.now() };
          players.set(pl.token, pl); playersById.set(pl.id, pl);
        } else pl.name = name;
        pl.lastSeen = Date.now(); saveSoon();
        return json(res, 200, { ok: true, token: pl.token, id: pl.id, name: pl.name, balance: pl.balance });
      }
      const pl = players.get(String(body.token || ''));
      if (!pl) return json(res, 401, { ok: false, reason: 'auth' });
      if (p === '/api/refill') {
        // 积分用完（低于最小押分）才可以免费补充；条件检查和加分在同一步里，重复点击不会多发
        if (pl.balance >= CHIPS[0]) return json(res, 200, { ok: false, reason: 'notneeded', balance: pl.balance });
        pl.balance = START_BALANCE; saveSoon();
        for (const r of rooms.values()) if (r.presence.get(pl.id)) r.broadcast();
        return json(res, 200, { ok: true, balance: pl.balance });
      }
      const code = normRoom(body.room);
      const room = code ? rooms.get(code) : null;
      if (p === '/api/auto') return json(res, 200, doAuto(room, pl, body.auto));
      if (!room) return json(res, 404, { ok: false, reason: 'noroom' });
      if (p === '/api/bet') return json(res, 200, doBet(room, pl, body.amount));
      if (p === '/api/cashout') return json(res, 200, doCashout(room, pl));
    }
    json(res, 404, { ok: false, reason: 'notfound' });
  } catch (e) {
    if (!res.headersSent) json(res, 400, { ok: false, reason: 'bad' });
  }
});

loadPlayers();
if (require.main === module) {
  server.listen(PORT, () => console.log(`一起起飞 listening on :${PORT}`));
  const bye = () => { saveNow(); process.exit(0); };
  process.on('SIGTERM', bye); process.on('SIGINT', bye);
}
module.exports = { server };
