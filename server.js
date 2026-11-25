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
const ASSETS = {"index.html": "<!doctype html>\n<html lang=\"zh-CN\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no,viewport-fit=cover\">\n<meta name=\"theme-color\" content=\"#24094f\">\n<title>一起起飞</title>\n<link rel=\"icon\" href=\"/favicon.svg\">\n<link rel=\"stylesheet\" href=\"/style.css\">\n</head>\n<body>\n<svg width=\"0\" height=\"0\" style=\"position:absolute\" aria-hidden=\"true\">\n  <defs>\n    <linearGradient id=\"gGold\" x1=\"0\" y1=\"0\" x2=\"0\" y2=\"1\">\n      <stop offset=\"0\" stop-color=\"#fff4c4\"/><stop offset=\".45\" stop-color=\"#ffd36a\"/>\n      <stop offset=\".7\" stop-color=\"#e8962a\"/><stop offset=\"1\" stop-color=\"#ffd98a\"/>\n    </linearGradient>\n    <linearGradient id=\"gCoin\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"1\">\n      <stop offset=\"0\" stop-color=\"#fff1b0\"/><stop offset=\".5\" stop-color=\"#f5b83a\"/><stop offset=\"1\" stop-color=\"#b86a12\"/>\n    </linearGradient>\n    <symbol id=\"laurel\" viewBox=\"0 0 40 90\">\n      <path d=\"M30 88 C 10 70, 6 40, 18 4\" fill=\"none\" stroke=\"url(#gGold)\" stroke-width=\"2.2\" stroke-linecap=\"round\"/>\n      <g fill=\"url(#gGold)\">\n        <ellipse cx=\"25\" cy=\"76\" rx=\"4\" ry=\"9\" transform=\"rotate(-50 25 76)\"/>\n        <ellipse cx=\"15\" cy=\"70\" rx=\"4\" ry=\"9\" transform=\"rotate(40 15 70)\"/>\n        <ellipse cx=\"18\" cy=\"58\" rx=\"4\" ry=\"9\" transform=\"rotate(-45 18 58)\"/>\n        <ellipse cx=\"8\" cy=\"52\" rx=\"4\" ry=\"9\" transform=\"rotate(35 8 52)\"/>\n        <ellipse cx=\"14\" cy=\"40\" rx=\"4\" ry=\"9\" transform=\"rotate(-35 14 40)\"/>\n        <ellipse cx=\"6\" cy=\"33\" rx=\"3.6\" ry=\"8.5\" transform=\"rotate(30 6 33)\"/>\n        <ellipse cx=\"15\" cy=\"22\" rx=\"3.6\" ry=\"8.5\" transform=\"rotate(-25 15 22)\"/>\n        <ellipse cx=\"10\" cy=\"14\" rx=\"3.2\" ry=\"7.5\" transform=\"rotate(20 10 14)\"/>\n        <ellipse cx=\"19\" cy=\"6\" rx=\"3\" ry=\"7\" transform=\"rotate(-10 19 6)\"/>\n      </g>\n    </symbol>\n    <symbol id=\"wings\" viewBox=\"0 0 160 40\">\n      <g fill=\"url(#gGold)\">\n        <path d=\"M70 22 C 50 6, 26 4, 4 10 C 22 12, 34 16, 42 22 C 30 20, 20 22, 12 26 C 30 26, 46 28, 64 30 Z\"/>\n        <path d=\"M90 22 C 110 6, 134 4, 156 10 C 138 12, 126 16, 118 22 C 130 20, 140 22, 148 26 C 130 26, 114 28, 96 30 Z\"/>\n        <circle cx=\"80\" cy=\"20\" r=\"13\" fill=\"none\" stroke=\"url(#gGold)\" stroke-width=\"3\"/>\n      </g>\n      <path d=\"M80 9 L 88 20 L 80 31 L 72 20 Z\" fill=\"#3ee6c8\" stroke=\"#bafff0\" stroke-width=\"1\"/>\n    </symbol>\n    <symbol id=\"coin\" viewBox=\"0 0 60 24\">\n      <ellipse cx=\"30\" cy=\"15\" rx=\"27\" ry=\"9\" fill=\"#a85a0e\"/>\n      <rect x=\"3\" y=\"9\" width=\"54\" height=\"6\" fill=\"#d98a1c\"/>\n      <ellipse cx=\"30\" cy=\"9\" rx=\"27\" ry=\"9\" fill=\"url(#gCoin)\" stroke=\"#ffe7a0\" stroke-width=\"1\"/>\n      <ellipse cx=\"30\" cy=\"9\" rx=\"18\" ry=\"5.6\" fill=\"none\" stroke=\"#b8700f\" stroke-width=\"1.4\" opacity=\".7\"/>\n      <path d=\"M30 4.6 l1.6 3.1 3.4.4-2.5 2.3.7 3.3-3.2-1.7-3.2 1.7.7-3.3-2.5-2.3 3.4-.4z\" fill=\"#b8700f\" opacity=\".85\"/>\n    </symbol>\n    <symbol id=\"horn\" viewBox=\"0 0 32 28\">\n      <path d=\"M4 10 h6 l12 -7 v22 l-12 -7 h-6 z\" fill=\"url(#gGold)\"/>\n      <path d=\"M8 18 l2 7 h4 l-2 -7\" fill=\"#e8962a\"/>\n      <path d=\"M25 8 l4 -3 M26 14 h5 M25 20 l4 3\" stroke=\"#ffb74a\" stroke-width=\"2\" stroke-linecap=\"round\"/>\n    </symbol>\n  </defs>\n</svg>\n\n<main id=\"landing\" class=\"view hidden\">\n  <div class=\"landing-card\">\n    <svg class=\"wings big\"><use href=\"#wings\"/></svg>\n    <h1 class=\"gold title\">一起起飞</h1>\n    <p class=\"tag\">开个房间，把链接发到群里<br>和朋友看同一架飞机，比谁收手最稳</p>\n    <canvas id=\"lcv\" class=\"landing-plane\"></canvas>\n    <button id=\"btnCreate\" class=\"cta\">创建房间</button>\n    <div class=\"join-row\">\n      <input id=\"inpCode\" placeholder=\"输入房间码加入\" maxlength=\"8\" autocapitalize=\"characters\" autocomplete=\"off\">\n      <button id=\"btnJoinCode\" class=\"ghost\">进入</button>\n    </div>\n    <p class=\"fine\">只用游戏积分，不涉及任何真实货币 · 理论返还率 95%</p>\n  </div>\n</main>\n\n<main id=\"game\" class=\"view hidden\">\n  <header class=\"top\">\n    <div class=\"me\">\n      <div id=\"meAv\" class=\"av ring\">?</div>\n      <div class=\"me-txt\"><b id=\"meName\">—</b><span>积分 <i id=\"balance\">—</i></span></div>\n    </div>\n    <div class=\"brand\"><svg class=\"wings\"><use href=\"#wings\"/></svg><h1 class=\"gold\">一起起飞</h1></div>\n    <button id=\"btnInvite\" class=\"invite\"><em id=\"roomCode\"></em><svg viewBox=\"0 0 24 24\" width=\"18\" height=\"18\"><path d=\"M12 3v12M7 8l5-5 5 5M5 13v6h14v-6\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"2\" stroke-linecap=\"round\" stroke-linejoin=\"round\"/></svg>邀请</button>\n  </header>\n\n  <div class=\"crowd\"><div id=\"faces\" class=\"faces\"></div><span id=\"online\"></span><span class=\"recent-l\">最近</span><div id=\"history\"></div></div>\n  <div class=\"divider\"><i></i></div>\n\n  <section id=\"stage\">\n    <canvas id=\"cv\"></canvas>\n    <div id=\"ladder\"><div class=\"rail\"></div><div id=\"ticks\"></div><div id=\"ladderMark\"></div></div>\n    <div id=\"conn\" class=\"conn hidden\">重连中…</div>\n    <section class=\"status\">\n      <svg class=\"laurel l\"><use href=\"#laurel\"/></svg>\n      <div class=\"status-mid\">\n      <div id=\"sub\">连接中</div>\n      <div id=\"mult\" class=\"gold\">…</div>\n      </div>\n      <svg class=\"laurel r\"><use href=\"#laurel\"/></svg>\n    </section>\n\n  </section>\n\n  <div class=\"ticker\"><svg class=\"horn\"><use href=\"#horn\"/></svg><div id=\"tickAv\" class=\"av sm hidden\"></div><div id=\"tickTxt\">等待乘客登机…</div></div>\n\n  <section id=\"panel\" class=\"card\">\n    <div class=\"card-h\"><i></i><span id=\"panelTitle\">选择押分</span><i></i></div>\n    <div id=\"pickWrap\">\n      <div id=\"chips\" class=\"stakes\">\n        <button class=\"stake\" data-amt=\"100\"><svg class=\"coins n1\"><use href=\"#coin\"/></svg><b>100 分</b></button>\n        <button class=\"stake\" data-amt=\"200\"><svg class=\"coins n2\"><use href=\"#coin\"/></svg><svg class=\"coins n2 b\"><use href=\"#coin\"/></svg><b>200 分</b></button>\n        <button class=\"stake\" data-amt=\"500\"><svg class=\"coins n3\"><use href=\"#coin\"/></svg><svg class=\"coins n3 b\"><use href=\"#coin\"/></svg><svg class=\"coins n3 c\"><use href=\"#coin\"/></svg><b>500 分</b></button>\n      </div>\n    </div>\n    <div id=\"flyWrap\" class=\"hidden\">\n      <div class=\"fly-row\">\n        <div><span>本局押分</span><b id=\"flyBet\">—</b></div>\n        <div class=\"sep\"></div>\n        <div><span>自动收手</span><b id=\"flyAuto\">—</b></div>\n      </div>\n      <div class=\"fly-label\" id=\"flyLabel\">现在收手可拿回</div>\n      <div class=\"fly-big gold\" id=\"flyBig\">—</div>\n    </div>\n    <div class=\"meta\">\n      <div><span>本局押分</span><b id=\"metaBet\">—</b></div>\n      <div class=\"sep\"></div>\n      <button id=\"btnAuto\"><span>自动收手</span><b id=\"autoVal\">关</b><em>›</em></button>\n    </div>\n    <button id=\"action\" class=\"action\" disabled>连接中…</button>\n    <button id=\"btnRefill\" class=\"refill hidden\">积分用完了 · 免费补满 10,000</button>\n  </section>\n\n  <section id=\"players\" class=\"card\">\n    <div class=\"card-h\"><i></i><span>本局乘客</span><i></i></div>\n    <div class=\"players-sub\" id=\"pcount\"></div>\n    <ul id=\"plist\"></ul>\n  </section>\n\n  <section class=\"rules\">\n    <div class=\"rules-ic\">✦</div>\n    <p><b>游戏规则：</b>起飞前押分，倍率不断上涨，随时收手按当时倍率拿回积分；飞机飞走时还没收手就输掉本局押分。最高 100×，理论返还率 95%，只用游戏积分。</p>\n  </section>\n</main>\n\n<div id=\"nameModal\" class=\"modal hidden\">\n  <form id=\"nameForm\" class=\"modal-card\">\n    <svg class=\"wings\"><use href=\"#wings\"/></svg>\n    <h2 class=\"gold\">登机前留个名</h2>\n    <p>朋友们会在乘客名单上看到这个昵称</p>\n    <input id=\"inpName\" maxlength=\"12\" placeholder=\"昵称（最多 12 个字）\" autocomplete=\"off\" required>\n    <button class=\"cta\" type=\"submit\">进入房间</button>\n  </form>\n</div>\n\n<div id=\"autoSheet\" class=\"modal sheet hidden\">\n  <div class=\"sheet-card\">\n    <div class=\"card-h\"><i></i><span>自动收手</span><i></i></div>\n    <p class=\"sheet-tip\">倍率到达设定值时自动帮你收手（起飞后本局不能再改）</p>\n    <div id=\"autos\" class=\"autos\">\n      <button class=\"pill\" data-auto=\"\">关闭</button>\n      <button class=\"pill\" data-auto=\"1.5\">1.5×</button>\n      <button class=\"pill\" data-auto=\"2\">2×</button>\n      <button class=\"pill\" data-auto=\"3\">3×</button>\n      <button class=\"pill\" data-auto=\"5\">5×</button>\n      <button class=\"pill\" data-auto=\"10\">10×</button>\n    </div>\n    <div class=\"custom\">\n      <input id=\"inpAuto\" inputmode=\"decimal\" placeholder=\"自定义 1.01 ~ 100\" autocomplete=\"off\">\n      <span>×</span>\n      <button id=\"btnAutoOk\" class=\"ghost\">确定</button>\n    </div>\n    <button id=\"btnSheetClose\" class=\"ghost wide\">完成</button>\n  </div>\n</div>\n<div id=\"toast\" class=\"toast\"></div>\n<script src=\"/app.js\"></script>\n</body>\n</html>\n", "app.js": "'use strict';\n(() => {\n  const $ = (s) => document.querySelector(s);\n  const store = {\n    get(k) { try { return localStorage.getItem(k); } catch (_) { return null; } },\n    set(k, v) { try { localStorage.setItem(k, v); } catch (_) {} },\n  };\n  const ROOM = (location.pathname.match(/^\\/r\\/([A-Za-z0-9]{4,8})\\/?$/) || [])[1]?.toUpperCase() || null;\n  const fmt = (n) => Math.round(n).toLocaleString('en-US');\n  const fx = (m) => m.toFixed(2) + '×';\n  const esc = (s) => String(s).replace(/[&<>\"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '\"': '&quot;' }[c]));\n\n  /* ------------------------------ 网络 ------------------------------ */\n  let ident = null;\n  try { ident = JSON.parse(store.get('qf_ident') || 'null'); } catch (_) {}\n  async function api(path, body) {\n    try {\n      const r = await fetch(path, { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify(body) });\n      const j = await r.json().catch(() => ({}));\n      j.status = r.status; return j;\n    } catch (_) { return { ok: false, reason: 'net' }; }\n  }\n  let toastTimer;\n  function toast(msg, ms = 2200) {\n    const t = $('#toast'); t.textContent = msg; t.classList.add('show');\n    clearTimeout(toastTimer); toastTimer = setTimeout(() => t.classList.remove('show'), ms);\n  }\n  let clockOffset = 0;\n  async function syncClock() {\n    let best = null;\n    for (let i = 0; i < 5; i++) {\n      const c0 = Date.now(), p0 = performance.now();\n      try {\n        const j = await (await fetch('/api/time', { cache: 'no-store' })).json();\n        const rtt = performance.now() - p0;\n        if (!best || rtt < best.rtt) best = { rtt, off: j.t - (c0 + rtt / 2) };\n      } catch (_) {}\n    }\n    if (best) clockOffset = best.off;\n  }\n  const now = () => Date.now() + clockOffset;\n\n  /* ------------------------------ 状态 ------------------------------ */\n  let S = null, es = null, cashing = false, betting = false;\n  let stake = +(store.get('qf_stake') || 200); if (![100, 200, 500].includes(stake)) stake = 200;\n  let flight = { round: 0, trail: [] };\n  let crashAnim = null, lastSettledRound = 0;\n\n  function liveCents() {\n    if (!S || S.phase !== 'flying') return 100;\n    const t = Math.max(0, (now() - S.startAt) / 1000);\n    return Math.min(10000, Math.max(100, Math.floor(100 * Math.exp(S.k * t))));\n  }\n\n  function connect() {\n    if (es) es.close();\n    es = new EventSource(`/api/stream?room=${ROOM}&token=${encodeURIComponent(ident.token)}`);\n    es.onopen = () => $('#conn').classList.add('hidden');\n    es.onmessage = (ev) => { try { onState(JSON.parse(ev.data)); } catch (_) {} };\n    es.onerror = () => {\n      $('#conn').classList.remove('hidden');\n      if (es.readyState === 2) setTimeout(() => join(ident.name, true), 1500);\n    };\n  }\n\n  /* ------------------------------ 实时播报 ------------------------------ */\n  const COLORS = ['#ffd166', '#7bdff2', '#b2f7ef', '#f7a8b8', '#d3b8ff', '#a8f07a', '#ffb36b', '#ff9ad5'];\n  const colorOf = (id) => { let h = 0; for (const c of id) h = (h * 31 + c.charCodeAt(0)) >>> 0; return COLORS[h % COLORS.length]; };\n  const initial = (n) => [...(n || '?')][0];\n  function avatar(p, cls = 'av') {\n    const d = document.createElement('div'); d.className = cls; d.style.background = colorOf(p.id); d.textContent = initial(p.name); return d;\n  }\n  const ticks = [];\n  let tickShownAt = 0;\n  function pushTick(p, html) { ticks.push({ p, html }); if (ticks.length > 8) ticks.shift(); }\n  function pumpTicker() {\n    if (!ticks.length || performance.now() - tickShownAt < 1100) return;\n    const { p, html } = ticks.shift(); tickShownAt = performance.now();\n    const av = $('#tickAv');\n    if (p) { av.classList.remove('hidden'); av.style.background = colorOf(p.id); av.textContent = initial(p.name); } else av.classList.add('hidden');\n    const t = $('#tickTxt'); t.innerHTML = html; t.style.animation = 'none'; void t.offsetWidth; t.style.animation = '';\n  }\n  function diffEvents(prev, s) {\n    const old = new Map(prev && prev.round === s.round ? prev.players.map((p) => [p.id, p]) : []);\n    for (const p of s.players) {\n      const o = old.get(p.id), b = p.bet, ob = o && o.bet;\n      const nm = `<b>${esc(p.name)}</b>`;\n      if (b && (!ob || ob.amount !== b.amount) && b.state === 'placed') pushTick(p, `${nm} 登机 · 押 ${fmt(b.amount)} 分`);\n      if (b && b.state === 'cashed' && (!ob || ob.state !== 'cashed')) pushTick(p, `${nm} 在 <b>${fx(b.mult)}</b> 收手！+${fmt(b.payout - b.amount)}`);\n      if (!o && prev && prev.round === s.round && !b) pushTick(p, `${nm} 进入了房间`);\n    }\n    if (s.phase === 'crashed' && (!prev || prev.phase !== 'crashed')) pushTick(null, s.maxed ? `满倍 <b>100×</b>！在场乘客全部自动结算` : `飞机在 <b>${fx(s.crash)}</b> 飞走了`);\n    if (s.phase === 'flying' && prev && prev.phase === 'betting') pushTick(null, `起飞！<b>${s.players.filter((p) => p.bet).length}</b> 位乘客在机上`);\n  }\n\n  function onState(s) {\n    const prev = S;\n    S = s;\n    if (!prev || prev.round !== s.round) { flight = { round: s.round, trail: [] }; crashAnim = null; }\n    diffEvents(prev, s);\n    if (s.phase === 'crashed' && (!prev || prev.phase !== 'crashed')) {\n      crashAnim = { t0: performance.now() };\n      lastSettledRound = s.round;\n    }\n    renderStatic();\n  }\n\n  /* ------------------------------ 加入房间 ------------------------------ */\n  async function join(name, silent) {\n    const j = await api('/api/join', { token: ident && ident.token, name });\n    if (!j.ok) { if (!silent) toast('进入失败，请重试'); return false; }\n    ident = { token: j.token, id: j.id, name: j.name };\n    store.set('qf_ident', JSON.stringify(ident));\n    connect();\n    return true;\n  }\n  async function enterGame() {\n    $('#game').classList.remove('hidden');\n    $('#roomCode').textContent = ROOM;\n    syncClock(); setInterval(syncClock, 30000);\n    requestAnimationFrame(frame);\n    if (ident && ident.name) { await join(ident.name); return; }\n    $('#nameModal').classList.remove('hidden');\n    $('#inpName').focus();\n  }\n  $('#nameForm').addEventListener('submit', async (e) => {\n    e.preventDefault();\n    const name = $('#inpName').value.trim();\n    if (!name) return;\n    if (await join(name)) $('#nameModal').classList.add('hidden');\n  });\n\n  /* ------------------------------ 操作 ------------------------------ */\n  const REASONS = {\n    closed: '这局已经起飞，下一局再登机', insufficient: '积分不够啦', net: '网络不稳，再试一次',\n    crashed: '慢了一步，飞机已经飞走', tooearly: '倍率还没到 1.01×', locked: '已起飞，本局不能再改自动收手', badauto: '自动收手请填 1.01 ~ 100',\n  };\n  async function placeBet(amount) {\n    if (betting) return; betting = true;\n    const j = await api('/api/bet', { token: ident.token, room: ROOM, amount });\n    betting = false;\n    if (!j.ok) toast(REASONS[j.reason] || '登机失败');\n  }\n  $('#chips').addEventListener('click', (e) => {\n    const b = e.target.closest('.stake'); if (!b || !S) return;\n    stake = +b.dataset.amt; store.set('qf_stake', stake);\n    const my = S.me.bet;\n    if (S.phase === 'betting' && my && my.amount !== stake) placeBet(stake); // 已登机时换档，直接改押\n    renderStatic(); lastAct = '';\n  });\n\n  async function doCashout() {\n    if (cashing || !S) return;\n    const b = S.me.bet;\n    if (!b || b.state !== 'placed' || S.phase !== 'flying') return;\n    cashing = true;\n    const j = await api('/api/cashout', { token: ident.token, room: ROOM });\n    cashing = false;\n    if (j.ok) { if (navigator.vibrate) navigator.vibrate(25); }\n    else toast(REASONS[j.reason] || '收手失败');\n  }\n  $('#action').addEventListener('pointerdown', (e) => {\n    const b = S && S.me.bet;\n    if (S && S.phase === 'flying' && b && b.state === 'placed') { e.preventDefault(); doCashout(); }\n  });\n  $('#action').addEventListener('click', () => {\n    if (!S || S.phase !== 'betting') return;\n    if (S.me.bet) placeBet(0); else placeBet(stake);\n  });\n  $('#btnRefill').addEventListener('click', async () => {\n    const j = await api('/api/refill', { token: ident.token });\n    toast(j.ok ? '已补满 10,000 积分' : '积分还够，暂时不用补');\n  });\n  $('#btnInvite').addEventListener('click', async () => {\n    const url = location.origin + '/r/' + ROOM;\n    const text = `来「一起起飞」和我玩一局！房间 ${ROOM}`;\n    try { if (navigator.share) { await navigator.share({ title: '一起起飞', text, url }); return; } } catch (_) { return; }\n    try { await navigator.clipboard.writeText(`${text} ${url}`); toast('链接已复制，发到群里吧'); }\n    catch (_) { prompt('复制这个链接发给朋友', url); }\n  });\n\n  // 自动收手面板\n  $('#btnAuto').addEventListener('click', () => { $('#autoSheet').classList.remove('hidden'); renderStatic(); });\n  $('#btnSheetClose').addEventListener('click', () => $('#autoSheet').classList.add('hidden'));\n  $('#autoSheet').addEventListener('click', (e) => { if (e.target.id === 'autoSheet') $('#autoSheet').classList.add('hidden'); });\n  $('#autos').addEventListener('click', async (e) => {\n    const b = e.target.closest('.pill'); if (!b || !S) return;\n    const v = b.dataset.auto;\n    const j = await api('/api/auto', { token: ident.token, room: ROOM, auto: v === '' ? null : +v });\n    if (!j.ok) toast(REASONS[j.reason] || '设置失败'); else setTimeout(() => $('#autoSheet').classList.add('hidden'), 150);\n  });\n  async function submitCustom() {\n    const v = parseFloat($('#inpAuto').value);\n    const j = await api('/api/auto', { token: ident.token, room: ROOM, auto: v });\n    if (!j.ok) return toast(REASONS[j.reason] || '设置失败');\n    $('#inpAuto').value = ''; $('#inpAuto').blur(); $('#autoSheet').classList.add('hidden');\n  }\n  $('#btnAutoOk').addEventListener('click', submitCustom);\n  $('#inpAuto').addEventListener('keydown', (e) => { if (e.key === 'Enter') submitCustom(); });\n\n  /* ------------------------------ 渲染（状态变化时） ------------------------------ */\n  function renderStatic() {\n    if (!S) return;\n    const me = S.me, b = me.bet, isBet = S.phase === 'betting';\n    const meP = { id: me.id, name: me.name };\n    const av = $('#meAv'); av.style.background = colorOf(me.id); av.textContent = initial(me.name);\n    $('#meName').textContent = me.name;\n    $('#balance').textContent = fmt(me.balance);\n    $('#autoVal').textContent = me.auto ? fx(me.auto) : '关';\n    $('#online').textContent = `${S.online} 人在线`;\n    $('#faces').replaceChildren(...S.players.filter((p) => p.online).slice(0, 4).map((p) => avatar(p)));\n    $('#btnRefill').classList.toggle('hidden', !me.canRefill);\n\n    // 押分卡片 / 飞行中信息\n    const inFlight = S.phase !== 'betting' && b;\n    $('#pickWrap').classList.toggle('hidden', !!inFlight);\n    $('#flyWrap').classList.toggle('hidden', !inFlight);\n    $('#panelTitle').textContent = inFlight ? '本轮飞行' : (isBet ? '选择押分' : '下一局押分');\n    for (const el of document.querySelectorAll('.stake')) {\n      const amt = +el.dataset.amt;\n      const sel = b ? b.amount === amt : stake === amt;\n      el.classList.toggle('on', sel);\n      el.disabled = me.balance + (b && b.state === 'placed' ? b.amount : 0) < amt;\n    }\n    $('.meta').classList.toggle('hidden', !!inFlight);\n    $('#metaBet').textContent = fmt(b ? b.amount : stake) + ' 分';\n    if (inFlight) {\n      $('#flyBet').textContent = fmt(b.amount) + ' 分';\n      $('#flyAuto').textContent = b.auto ? fx(b.auto) : '手动';\n    }\n\n    // 自动收手面板\n    const locked = !!b && b.state === 'placed' && !isBet;\n    const presets = ['', '1.5', '2', '3', '5', '10'];\n    for (const el of document.querySelectorAll('.pill')) {\n      const v = el.dataset.auto; el.disabled = locked;\n      el.classList.toggle('on', me.auto === null ? v === '' : v !== '' && Number(v) === me.auto);\n    }\n    if (me.auto !== null && !presets.includes(String(me.auto))) $('#inpAuto').placeholder = `当前 ${fx(me.auto)} · 自定义 1.01 ~ 100`;\n\n    // 最近航程（最新在前）\n    $('#history').replaceChildren(...S.history.slice().reverse().map((h) => {\n      const d = document.createElement('span');\n      d.className = 'h' + (h.c >= 10 ? ' hi' : h.c >= 2 ? ' mid' : ' lo');\n      d.textContent = fx(h.c); return d;\n    }));\n\n    // 乘客名单\n    const rank = (p) => (p.id === me.id ? 0 : p.bet ? 1 : 2);\n    const ps = S.players.slice().sort((a, c) => rank(a) - rank(c) || (c.bet ? c.bet.amount : 0) - (a.bet ? a.bet.amount : 0));\n    const nBet = S.players.filter((p) => p.bet).length;\n    $('#pcount').textContent = `${nBet} 人登机 · ${S.online} 人在线`;\n    $('#plist').replaceChildren(...ps.map((p) => {\n      const li = document.createElement('li'); if (!p.online) li.className = 'off';\n      const nm = document.createElement('div'); nm.className = 'pn'; nm.textContent = p.name;\n      if (p.id === me.id) { const i = document.createElement('i'); i.textContent = '我'; nm.append(i); }\n      const bt = document.createElement('div'); bt.className = 'pb'; bt.textContent = p.bet ? `押 ${fmt(p.bet.amount)}` : '';\n      const st = document.createElement('div'); st.className = 'ps';\n      const k = p.bet;\n      if (!k) { st.classList.add('dim'); st.textContent = isBet ? '观望中' : '围观'; }\n      else if (k.state === 'cashed') { st.classList.add('win'); st.textContent = `${fx(k.mult)} +${fmt(k.payout - k.amount)}`; }\n      else if (k.state === 'lost') { st.classList.add('lose'); st.textContent = `−${fmt(k.amount)}`; }\n      else { st.classList.add(isBet ? 'dim' : 'fly'); st.textContent = isBet ? '已登机' : '飞行中…'; }\n      li.append(avatar(p), nm, bt, st); return li;\n    }));\n    void meP;\n  }\n\n  /* ------------------------------ 每帧：数字、按钮、刻度尺 ------------------------------ */\n  const multEl = $('#mult'), subEl = $('#sub'), actEl = $('#action');\n  let lastAct = '';\n  function setAction(cls, html) {\n    const key = cls + '|' + html;\n    if (key === lastAct) return; lastAct = key;\n    actEl.className = 'action ' + cls; actEl.innerHTML = html;\n    actEl.disabled = !(cls === 'go' || cls === 'cash' || cls === 'cancel');\n  }\n  let ladderHi = 0;\n  function niceHi(m) { for (const v of [3, 5, 10, 20, 50, 100]) if (m * 1.25 <= v) return v; return 100; }\n  function updateLadder(m, show) {\n    const hi = Math.max(3, S && S.phase === 'flying' ? niceHi(m) : (S && S.phase === 'crashed' ? niceHi(m) : 3));\n    if (hi !== ladderHi) {\n      ladderHi = hi;\n      const els = [];\n      for (let i = 0; i < 5; i++) {\n        const v = 1 + (hi - 1) * i / 4;\n        const d = document.createElement('div'); d.className = 'tick';\n        d.style.top = (100 - i * 25) + '%';\n        d.textContent = (v < 10 ? v.toFixed(1) : Math.round(v)) + '×';\n        els.push(d);\n      }\n      $('#ticks').replaceChildren(...els);\n    }\n    const mk = $('#ladderMark');\n    mk.style.opacity = show ? 1 : 0;\n    if (show) { mk.style.top = (100 - Math.min(1, (m - 1) / (hi - 1)) * 100) + '%'; mk.textContent = fx(m); }\n  }\n\n  function updateHud() {\n    pumpTicker();\n    if (!S) { multEl.textContent = '…'; subEl.textContent = '连接中'; setAction('', '连接中…'); return; }\n    const me = S.me, b = me.bet;\n    multEl.classList.remove('crashed');\n    if (S.phase === 'betting') {\n      const left = Math.max(0, (S.startAt - now()) / 1000);\n      multEl.textContent = '00:0' + Math.ceil(left);\n      subEl.textContent = '登机中';\n      updateLadder(1, false);\n      if (b) setAction('cancel', `已登机 · ${fmt(b.amount)} 分<small>点这里取消</small>`);\n      else if (me.balance < stake) setAction('', me.balance < 100 ? '积分不够了，先免费补满' : '积分不够这一档，换个小点的');\n      else setAction('go', `登机 · ${fmt(stake)} 分`);\n    } else if (S.phase === 'flying') {\n      const c = liveCents();\n      multEl.textContent = fx(c / 100); subEl.textContent = '飞行中 · 当前倍率';\n      updateLadder(c / 100, true);\n      if (b && b.state === 'placed') {\n        const pay = b.amount * c / 100;\n        $('#flyLabel').textContent = '现在收手可拿回';\n        $('#flyBig').innerHTML = `${fmt(pay)}<small>分</small>`;\n        setAction('cash', `收手 · 拿回 ${fmt(pay)} 分`);\n      } else if (b && b.state === 'cashed') {\n        $('#flyLabel').textContent = `已在 ${fx(b.mult)} 收手，拿回`;\n        $('#flyBig').innerHTML = `${fmt(b.payout)}<small>分</small>`;\n        setAction('done', `已收手 ${fx(b.mult)} · +${fmt(b.payout - b.amount)}<small>看看朋友能飞多高</small>`);\n      } else setAction('', '本局围观中 · 下一局再登机');\n    } else if (S.phase === 'crashed') {\n      multEl.textContent = fx(S.crash); multEl.classList.add('crashed');\n      subEl.textContent = S.maxed ? '满倍 100× · 全员自动结算' : '飞机飞走了';\n      updateLadder(S.crash, true);\n      const left = Math.max(0, Math.ceil((S.nextAt - now()) / 1000));\n      if (b && b.state === 'cashed') {\n        $('#flyLabel').textContent = `${fx(b.mult)} 收手，拿回`; $('#flyBig').innerHTML = `${fmt(b.payout)}<small>分</small>`;\n        setAction('done', `赢了 +${fmt(b.payout - b.amount)}<small>${left} 秒后开下一局</small>`);\n      } else if (b && b.state === 'lost') {\n        $('#flyLabel').textContent = '飞机飞走时还没收手'; $('#flyBig').innerHTML = `<span class=\"neg\">−${fmt(b.amount)}<small>分</small></span>`;\n        setAction('lose', `输了 −${fmt(b.amount)}<small>${left} 秒后开下一局</small>`);\n      } else setAction('', `${left} 秒后开下一局`);\n    } else { multEl.textContent = '—'; subEl.textContent = '等待开局'; setAction('', '等待开局…'); }\n  }\n\n  /* ------------------------------ 画面 ------------------------------ */\n  function makeScene(cv) {\n    const ctx = cv.getContext('2d');\n    const sc = { W: 0, H: 0, dpr: 1 };\n    function resize() {\n      sc.dpr = Math.min(2, window.devicePixelRatio || 1);\n      const r = cv.getBoundingClientRect(); sc.W = r.width; sc.H = r.height;\n      cv.width = Math.round(sc.W * sc.dpr); cv.height = Math.round(sc.H * sc.dpr);\n    }\n    new ResizeObserver(resize).observe(cv);\n    sc.ctx = ctx; return sc;\n  }\n\n  // 水晶纸飞机（机头朝右上，局部坐标约 [-1.1,1.3]）\n  function drawCrystal(ctx, x, y, ang, s, alpha, t) {\n    ctx.save(); ctx.translate(x, y); ctx.rotate(ang); ctx.scale(s, s); ctx.globalAlpha = alpha;\n    const N = [1.35, -0.06], FT = [-0.78, -0.62], S = [-0.92, 0.08], NT = [-1.02, 0.6], F = [-0.97, 0.36];\n    const path = (pts) => { ctx.beginPath(); ctx.moveTo(...pts[0]); for (const q of pts.slice(1)) ctx.lineTo(...q); ctx.closePath(); };\n    const sh = Math.sin(t / 650) * 0.12;\n    // 外发光\n    ctx.shadowColor = 'rgba(225,120,255,.95)'; ctx.shadowBlur = 36;\n    path([N, FT, S, NT]); ctx.fillStyle = 'rgba(120,60,220,.9)'; ctx.fill();\n    ctx.shadowBlur = 0;\n    // 远侧机翼（上表面，冷色）\n    let g = ctx.createLinearGradient(-0.7, -0.9, 1.0, 0.1);\n    g.addColorStop(0, '#6d7bff'); g.addColorStop(0.35 + sh, '#b9e6ff'); g.addColorStop(0.7, '#f0d4ff'); g.addColorStop(1, '#ffffff');\n    path([N, FT, S]); ctx.fillStyle = g; ctx.fill();\n    // 远侧机翼内折面\n    g = ctx.createLinearGradient(-0.8, -0.3, 1.0, 0); g.addColorStop(0, 'rgba(90,40,200,.75)'); g.addColorStop(1, 'rgba(180,140,255,.2)');\n    path([N, [-0.82, -0.26], S]); ctx.fillStyle = g; ctx.fill();\n    // 近侧机翼（暖色虹彩）\n    g = ctx.createLinearGradient(-1.0, 0.8, 1.2, -0.1);\n    g.addColorStop(0, '#5a22c8'); g.addColorStop(0.3 - sh, '#c04dff'); g.addColorStop(0.55, '#ff8fd6'); g.addColorStop(0.78, '#9ff0ff'); g.addColorStop(1, '#ffffff');\n    path([N, S, NT]); ctx.fillStyle = g; ctx.fill();\n    // 机腹折痕\n    g = ctx.createLinearGradient(-1, 0.3, 1.2, 0); g.addColorStop(0, '#2e0c7a'); g.addColorStop(1, 'rgba(120,70,230,.4)');\n    path([N, S, F]); ctx.fillStyle = g; ctx.fill();\n    // 高光\n    ctx.globalAlpha = alpha * 0.7; ctx.fillStyle = '#fff';\n    path([N, [-0.2, -0.36], [0.15, -0.22]]); ctx.fill();\n    ctx.globalAlpha = alpha * 0.45; path([N, [-0.4, 0.32], [0.0, 0.22]]); ctx.fill();\n    ctx.globalAlpha = alpha;\n    // 金边\n    ctx.lineJoin = 'round'; ctx.strokeStyle = '#ffd36a'; ctx.lineWidth = 0.04;\n    path([N, FT, S, NT]); ctx.stroke();\n    ctx.beginPath(); ctx.moveTo(...N); ctx.lineTo(...S); ctx.stroke();\n    ctx.lineWidth = 0.022; ctx.beginPath(); ctx.moveTo(...N); ctx.lineTo(...F); ctx.stroke();\n    // 金色翼徽\n    ctx.save(); ctx.translate(-0.2, 0.14); ctx.rotate(-0.06); ctx.scale(0.8, 0.8); ctx.fillStyle = '#ffd36a';\n    ctx.shadowColor = 'rgba(255,200,90,.9)'; ctx.shadowBlur = 8;\n    for (const d of [-1, 1]) { ctx.beginPath(); ctx.moveTo(0, 0); ctx.quadraticCurveTo(0.16 * d, -0.16, 0.36 * d, -0.1); ctx.quadraticCurveTo(0.22 * d, -0.02, 0.06 * d, 0.06); ctx.fill(); }\n    ctx.fillStyle = '#3ee6c8'; path([[0, -0.09], [0.065, 0], [0, 0.09], [-0.065, 0]]); ctx.fill();\n    ctx.restore();\n    // 机头闪光\n    const tw = 0.5 + 0.5 * Math.sin(t / 220);\n    ctx.globalAlpha = alpha * tw; ctx.fillStyle = '#fff';\n    ctx.beginPath(); ctx.moveTo(N[0] + 0.22, N[1]); ctx.lineTo(N[0], N[1] + 0.04); ctx.lineTo(N[0] - 0.22, N[1]); ctx.lineTo(N[0], N[1] - 0.04); ctx.fill();\n    ctx.beginPath(); ctx.moveTo(N[0], N[1] - 0.2); ctx.lineTo(N[0] + 0.035, N[1]); ctx.lineTo(N[0], N[1] + 0.2); ctx.lineTo(N[0] - 0.035, N[1]); ctx.fill();\n    ctx.restore();\n  }\n\n  const stars = Array.from({ length: 60 }, () => ({ x: Math.random(), y: Math.random() * 0.7, r: 0.5 + Math.random() * 1.4, p: Math.random() * 6 }));\n  const clouds = Array.from({ length: 6 }, () => ({ x: Math.random(), y: Math.random(), s: 0.7 + Math.random() * 1.1, v: 0.5 + Math.random() }));\n  const sparks = [];\n\n  function drawGround(ctx, W, H, off, ts) {\n    const hz = H * 0.36 + off; // 地平线\n    if (hz > H + 20) return;\n    // 远山\n    ctx.fillStyle = '#2a0f63';\n    ctx.beginPath(); ctx.moveTo(0, hz);\n    for (let i = 0; i <= 10; i++) ctx.lineTo(W * i / 10, hz - (12 + 14 * Math.abs(Math.sin(i * 1.7))));\n    ctx.lineTo(W, hz); ctx.fill();\n    // 城市灯\n    ctx.fillStyle = '#3b177f'; for (let i = 0; i < 14; i++) { const w = 10 + (i * 7) % 16, h = 8 + (i * 13) % 22; ctx.fillRect(W * 0.12 + i * W * 0.045, hz - h, w, h); }\n    ctx.fillStyle = 'rgba(255,200,120,.75)'; for (let i = 0; i < 40; i++) ctx.fillRect(W * 0.13 + ((i * 37) % 260) * W / 420, hz - 3 - ((i * 11) % 18), 1.6, 1.6);\n    // 塔台 + 探照灯\n    const tx = W * 0.66;\n    ctx.save(); ctx.globalCompositeOperation = 'lighter';\n    for (const [a0, w] of [[-1.35 + Math.sin(ts / 2400) * 0.12, 0.09], [-1.85 + Math.sin(ts / 3100) * 0.1, 0.07]]) {\n      const g = ctx.createLinearGradient(tx, hz - 50, tx + Math.cos(a0) * H, hz - 50 + Math.sin(a0) * H);\n      g.addColorStop(0, 'rgba(210,170,255,.5)'); g.addColorStop(1, 'rgba(210,170,255,0)');\n      ctx.fillStyle = g; ctx.beginPath(); ctx.moveTo(tx, hz - 50);\n      ctx.lineTo(tx + Math.cos(a0 - w) * H, hz - 50 + Math.sin(a0 - w) * H); ctx.lineTo(tx + Math.cos(a0 + w) * H, hz - 50 + Math.sin(a0 + w) * H); ctx.fill();\n    }\n    ctx.restore();\n    ctx.fillStyle = '#4a1f96'; ctx.fillRect(tx - 4, hz - 46, 8, 46); ctx.fillStyle = '#ffd98a'; ctx.fillRect(tx - 9, hz - 54, 18, 9);\n    // 机库\n    const hx = W * 0.86, hw = W * 0.28, hh = 46;\n    ctx.fillStyle = '#3a1783'; ctx.beginPath(); ctx.ellipse(hx, hz, hw / 2, hh, 0, Math.PI, 0); ctx.fill();\n    const hg = ctx.createRadialGradient(hx, hz, 4, hx, hz, hh); hg.addColorStop(0, '#ffd2f4'); hg.addColorStop(1, 'rgba(255,120,200,.15)');\n    ctx.fillStyle = hg; ctx.beginPath(); ctx.ellipse(hx, hz, hw / 3, hh * 0.68, 0, Math.PI, 0); ctx.fill();\n    // 地面\n    const gg = ctx.createLinearGradient(0, hz, 0, H + off); gg.addColorStop(0, '#2b0e66'); gg.addColorStop(1, '#170538');\n    ctx.fillStyle = gg; ctx.fillRect(0, hz, W, H * 2);\n    // 跑道（透视梯形）\n    const cx = W * 0.5, topW = W * 0.06, botW = W * 1.1, bot = H + off + H * 0.25;\n    const rg = ctx.createLinearGradient(0, hz, 0, bot); rg.addColorStop(0, '#3a1a7a'); rg.addColorStop(1, '#25104f');\n    ctx.fillStyle = rg; ctx.beginPath(); ctx.moveTo(cx - topW, hz); ctx.lineTo(cx + topW, hz); ctx.lineTo(cx + botW / 2, bot); ctx.lineTo(cx - botW / 2, bot); ctx.fill();\n    // 边灯与中线\n    const lerp = (a, b, k) => a + (b - a) * k;\n    for (let i = 0; i < 16; i++) {\n      const k = Math.pow(i / 15, 1.8), y = lerp(hz, bot, k), hw2 = lerp(topW, botW / 2, k), r = 0.8 + k * 3.2;\n      const blink = 0.6 + 0.4 * Math.sin(ts / 300 - i * 0.6);\n      ctx.fillStyle = `rgba(255,214,140,${0.55 + 0.45 * blink})`; ctx.shadowColor = '#ffcf7a'; ctx.shadowBlur = 8 * k + 2;\n      ctx.beginPath(); ctx.arc(cx - hw2, y, r, 0, 7); ctx.arc(cx + hw2, y, r, 0, 7); ctx.fill();\n    }\n    ctx.shadowBlur = 0; ctx.fillStyle = 'rgba(255,240,210,.55)';\n    for (let i = 0; i < 10; i++) {\n      const k0 = Math.pow(i / 10, 1.8), k1 = Math.pow((i + 0.45) / 10, 1.8);\n      const y0 = lerp(hz, bot, k0), y1 = lerp(hz, bot, k1), w0 = lerp(1, 7, k0), w1 = lerp(1, 7, k1);\n      ctx.beginPath(); ctx.moveTo(cx - w0 / 2, y0); ctx.lineTo(cx + w0 / 2, y0); ctx.lineTo(cx + w1 / 2, y1); ctx.lineTo(cx - w1 / 2, y1); ctx.fill();\n    }\n    // 起点斑马线\n    const zy = lerp(hz, bot, 0.42), zw = lerp(topW, botW / 2, 0.62);\n    ctx.fillStyle = 'rgba(255,236,190,.5)';\n    for (let i = -4; i <= 4; i++) { if (!i) continue; ctx.fillRect(cx + i * zw / 5.2 - zw / 22, zy, zw / 11, 10 + 6 * 0.62); }\n  }\n\n  function drawSky(sc, ts, phase, u, dt, scrollState) {\n    const { ctx, W, H } = sc;\n    const g = ctx.createLinearGradient(0, 0, 0, H);\n    const lift = Math.min(1, u / 3);\n    g.addColorStop(0, lift > 0.5 ? '#12053a' : '#1d0a4c'); g.addColorStop(0.55, '#4a1b9e'); g.addColorStop(1, '#6a2fc0');\n    ctx.fillStyle = g; ctx.fillRect(0, 0, W, H);\n    for (const s of stars) {\n      ctx.globalAlpha = 0.35 + 0.35 * Math.sin(ts / 600 + s.p); ctx.fillStyle = '#fff';\n      ctx.beginPath(); ctx.arc(s.x * W, ((s.y * H + scrollState.s * 0.3) % H), s.r, 0, 7); ctx.fill();\n    }\n    ctx.globalAlpha = 1;\n  }\n\n  function drawClouds(sc, scrollState, front) {\n    const { ctx, W, H } = sc;\n    ctx.fillStyle = front ? 'rgba(200,150,255,.14)' : 'rgba(160,110,240,.18)';\n    for (const [i, c] of clouds.entries()) {\n      if ((i % 2 === 0) !== front) continue;\n      const y = ((c.y * H + scrollState.s * c.v * (front ? 1.6 : 0.9)) % (H + 80)) - 40, x = c.x * W;\n      for (let k = 0; k < 4; k++) { ctx.beginPath(); ctx.ellipse(x + k * 26 * c.s - 30, y + (k % 2) * 7, 38 * c.s, 14 * c.s, 0, 0, 7); ctx.fill(); }\n    }\n  }\n\n  // 游戏画布\n  const sc = makeScene($('#cv'));\n  const scroll = { s: 0 };\n  let lastTs = 0;\n  function planePos(u) {\n    const f = 1 - Math.exp(-u / 0.55);\n    return { x: sc.W * (0.53 + 0.08 * f), y: sc.H * (0.54 - 0.28 * f), s: Math.min(sc.W * 0.19, sc.H * 0.21) * (1 - 0.2 * f) };\n  }\n  function draw(ts) {\n    const { ctx, W, H, dpr } = sc;\n    if (!W) return;\n    const dt = Math.min(0.05, (ts - lastTs) / 1000 || 0.016); lastTs = ts;\n    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);\n    const phase = S ? S.phase : 'idle';\n    const cents = phase === 'flying' ? liveCents() : (phase === 'crashed' ? Math.round(S.crash * 100) : 100);\n    const u = Math.log(cents / 100);\n    scroll.s += (phase === 'flying' ? 30 + Math.min(u, 4.6) * 40 : phase === 'crashed' ? 20 : 4) * dt;\n    drawSky(sc, ts, phase, u, dt, scroll);\n    drawClouds(sc, scroll, false);\n    const groundOff = phase === 'flying' || phase === 'crashed' ? Math.min(1, u / 0.5) ** 1.3 * H * 0.75 : 0;\n    drawGround(ctx, W, H, groundOff, ts);\n    let p = planePos(phase === 'betting' || phase === 'idle' ? 0 : u);\n    if (phase === 'betting' || phase === 'idle' || !S) {\n      const bob = Math.sin(ts / 500) * 2;\n      const rg = ctx.createRadialGradient(p.x, p.y + p.s * 0.75, 2, p.x, p.y + p.s * 0.75, p.s * 1.3);\n      rg.addColorStop(0, 'rgba(230,150,255,.55)'); rg.addColorStop(1, 'rgba(230,150,255,0)');\n      ctx.fillStyle = rg; ctx.beginPath(); ctx.ellipse(p.x, p.y + p.s * 0.75, p.s * 1.3, p.s * 0.28, 0, 0, 7); ctx.fill();\n      drawCrystal(ctx, p.x, p.y + bob, -0.08, p.s, 1, ts);\n    } else if (phase === 'flying') {\n      const bob = Math.sin(ts / 420) * 3 * Math.min(1, u * 2);\n      const ang = -0.12 - 0.25 * Math.min(1, u * 1.5);\n      // 尾迹火花\n      for (let i = 0; i < 2; i++) sparks.push({ x: p.x - p.s * 0.95, y: p.y + bob + p.s * 0.1, vx: -30 - Math.random() * 40, vy: 30 + Math.random() * 50, life: 1, c: Math.random() < 0.6 ? '#ffd36a' : '#ff9ae6' });\n      drawSparks(dt);\n      drawCrystal(ctx, p.x, p.y + bob, ang, p.s, 1, ts);\n    } else if (phase === 'crashed') {\n      const k = crashAnim ? Math.min(1.5, (performance.now() - crashAnim.t0) / 650) : 1.5;\n      drawSparks(dt);\n      if (k < 1.5) drawCrystal(ctx, p.x + k * k * W * 0.6, p.y - k * k * H * 0.55, -0.55, p.s * (1 - k * 0.35), Math.max(0, 1 - k / 1.5), ts);\n    }\n    if (phase === 'flying' || phase === 'crashed') drawClouds(sc, scroll, true);\n  }\n  function drawSparks(dt) {\n    const { ctx } = sc;\n    ctx.save(); ctx.globalCompositeOperation = 'lighter';\n    for (let i = sparks.length - 1; i >= 0; i--) {\n      const s = sparks[i]; s.x += s.vx * dt; s.y += s.vy * dt; s.life -= dt * 1.4;\n      if (s.life <= 0) { sparks.splice(i, 1); continue; }\n      ctx.globalAlpha = s.life; ctx.fillStyle = s.c; ctx.beginPath(); ctx.arc(s.x, s.y, 1 + 2.2 * s.life, 0, 7); ctx.fill();\n    }\n    ctx.restore();\n  }\n\n  function frame(ts) { updateHud(); draw(ts); requestAnimationFrame(frame); }\n\n  /* ------------------------------ 首页 ------------------------------ */\n  function landing() {\n    $('#landing').classList.remove('hidden');\n    const ls = makeScene($('#lcv'));\n    const loop = (ts) => {\n      if (ls.W) {\n        const { ctx, W, H, dpr } = ls; ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.clearRect(0, 0, W, H);\n        const g = ctx.createRadialGradient(W / 2, H * 0.55, 4, W / 2, H * 0.55, W * 0.45); g.addColorStop(0, 'rgba(210,140,255,.45)'); g.addColorStop(1, 'rgba(210,140,255,0)');\n        ctx.fillStyle = g; ctx.fillRect(0, 0, W, H);\n        drawCrystal(ctx, W / 2, H * 0.52 + Math.sin(ts / 600) * 6, -0.2, Math.min(W, H) * 0.32, 1, ts);\n      }\n      requestAnimationFrame(loop);\n    };\n    requestAnimationFrame(loop);\n    $('#btnCreate').addEventListener('click', async () => {\n      try { const j = await (await fetch('/api/new-room', { cache: 'no-store' })).json(); location.href = '/r/' + j.room; }\n      catch (_) { toast('网络不稳，再试一次'); }\n    });\n    const go = () => { const c = $('#inpCode').value.trim().toUpperCase(); if (/^[A-Z0-9]{4,8}$/.test(c)) location.href = '/r/' + c; else toast('房间码是 4~8 位字母数字'); };\n    $('#btnJoinCode').addEventListener('click', go);\n    $('#inpCode').addEventListener('keydown', (e) => { if (e.key === 'Enter') go(); });\n  }\n\n  document.addEventListener('visibilitychange', () => { if (!document.hidden && es && es.readyState === 2) join(ident.name, true); });\n  if (ROOM) enterGame(); else landing();\n})();\n", "style.css": ":root {\n  --bg0: #12052e; --bg1: #24094f; --bg2: #3a1585;\n  --glass: rgba(76, 36, 150, .38); --glass2: rgba(40, 14, 92, .55);\n  --gold: #ffd36a; --gold-d: #e8962a; --line: rgba(255, 205, 120, .38); --line2: rgba(255, 205, 120, .18);\n  --text: #f6efff; --dim: #b9a6e6; --green: #4be35a; --red: #ff5a7a; --cyan: #3ee6c8;\n  --safe-b: env(safe-area-inset-bottom, 0px);\n}\n* { box-sizing: border-box; -webkit-tap-highlight-color: transparent; }\nhtml, body { margin: 0; min-height: 100%; color: var(--text);\n  background: radial-gradient(130% 50% at 50% 0%, #4a1aa0 0%, var(--bg1) 45%, var(--bg0) 100%) var(--bg0);\n  font: 15px/1.35 -apple-system, BlinkMacSystemFont, \"PingFang SC\", \"Noto Sans SC\", \"Microsoft YaHei\", sans-serif; }\nbody { overscroll-behavior: none; }\nbutton { font: inherit; color: inherit; border: 0; background: none; cursor: pointer; touch-action: manipulation; padding: 0; }\ninput { font: inherit; font-size: 16px; color: inherit; }\n.hidden { display: none !important; }\n.view { max-width: 480px; margin: 0 auto; min-height: 100dvh; }\n\n.gold { background: linear-gradient(180deg, #fffbe6 0%, #ffe38f 38%, #f7b63e 62%, #ffe09a 100%);\n  -webkit-background-clip: text; background-clip: text; color: transparent;\n  filter: drop-shadow(0 2px 0 #7a3300) drop-shadow(0 0 10px rgba(255, 180, 60, .35)); }\n.wings { width: 120px; height: 30px; display: block; margin: 0 auto -4px; }\n.wings.big { width: 170px; height: 42px; }\n\n/* ---------- 首页 ---------- */\n#landing { display: flex; align-items: center; justify-content: center; padding: 28px 22px; }\n.landing-card { width: 100%; text-align: center; }\nh1.title { font-size: 46px; margin: 4px 0 6px; letter-spacing: 6px; font-weight: 900; }\n.tag { color: var(--dim); margin: 0 0 4px; }\n.landing-plane { width: 100%; height: 190px; display: block; }\n.cta { width: 100%; padding: 16px; border-radius: 999px; font-size: 20px; font-weight: 800; color: #0d3a06;\n  background: linear-gradient(180deg, #b6ff7a 0%, #4be35a 45%, #23b02f 100%);\n  box-shadow: inset 0 2px 0 rgba(255,255,255,.6), inset 0 -3px 0 rgba(0,70,0,.35), 0 0 0 2px #ffcf66, 0 6px 0 #a8650e, 0 10px 24px rgba(75,227,90,.35);\n  text-shadow: 0 1px 0 rgba(255,255,255,.5); }\n.cta:active { transform: translateY(2px); }\n.ghost { padding: 12px 16px; border-radius: 14px; background: var(--glass); border: 1px solid var(--line); }\n.ghost.wide { width: 100%; margin-top: 12px; }\n.join-row { display: flex; gap: 8px; margin-top: 18px; }\n.join-row input, #inpName, #inpAuto { flex: 1; min-width: 0; padding: 12px 14px; border-radius: 14px; outline: none;\n  background: rgba(10, 2, 30, .45); border: 1px solid var(--line); }\n.join-row input { text-transform: uppercase; }\n.fine { color: var(--dim); font-size: 12px; text-align: center; margin: 14px 0 0; opacity: .85; }\n\n/* ---------- 游戏页 ---------- */\n#game { padding: 0 12px calc(16px + var(--safe-b)); }\n.top { display: grid; grid-template-columns: 1fr auto 1fr; align-items: center; padding: 10px 0 2px; }\n.me { display: flex; align-items: center; gap: 8px; min-width: 0; }\n.me-txt { display: flex; flex-direction: column; min-width: 0; line-height: 1.2; }\n.me-txt b { font-size: 13px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 84px; }\n.me-txt span { font-size: 12px; color: var(--dim); } .me-txt i { font-style: normal; font-weight: 800; color: var(--gold); font-variant-numeric: tabular-nums; }\n.brand h1 { margin: 0; font-size: 26px; font-weight: 900; letter-spacing: 3px; white-space: nowrap; }\n.brand .wings { width: 104px; height: 26px; }\n.invite em { font-style: normal; display: none; }\n.invite { justify-self: end; display: flex; align-items: center; gap: 4px; padding: 7px 12px; border-radius: 999px; font-size: 14px;\n  background: var(--glass); border: 1px solid var(--line); }\n\n.av { width: 34px; height: 34px; border-radius: 50%; flex: none; display: grid; place-items: center; font-weight: 800; font-size: 15px;\n  color: #2a0c55; border: 2px solid #ffe08a; box-shadow: 0 0 0 2px rgba(255,170,60,.35); }\n.av.ring { width: 42px; height: 42px; font-size: 18px; box-shadow: 0 0 0 3px #b53cff, 0 0 14px #d36bff; }\n.av.sm { width: 26px; height: 26px; font-size: 12px; }\n\n.crowd { display: flex; align-items: center; gap: 8px; margin-top: 6px; }\n.crowd .recent-l { margin-left: 6px; padding-left: 10px; border-left: 1px solid var(--line2); }\n.faces { display: flex; } .faces .av { width: 30px; height: 30px; font-size: 13px; margin-left: -8px; } .faces .av:first-child { margin-left: 0; }\n#online { color: var(--dim); font-size: 13px; flex: none; }\n.recent { display: flex; align-items: center; gap: 12px; margin-top: 8px; }\n.recent-l { color: var(--dim); font-size: 13px; flex: none; }\n#history { display: flex; gap: 10px; overflow-x: auto; scrollbar-width: none; flex: 1; }\n#history::-webkit-scrollbar { display: none; }\n.h { flex: none; font-size: 15px; font-weight: 700; font-variant-numeric: tabular-nums; color: #e9e0ff; }\n.h.mid { color: #8fd2ff; } .h.hi { color: var(--gold); } .h.lo { color: #c8b8ee; }\n.divider { height: 1px; margin: 8px 0 8px; background: linear-gradient(90deg, transparent, var(--gold), transparent); position: relative; }\n.divider i { position: absolute; left: 50%; top: -5px; width: 10px; height: 10px; transform: translateX(-50%) rotate(45deg);\n  background: var(--cyan); border: 1px solid #fff3c0; }\n\n#stage { position: relative; height: clamp(270px, 41dvh, 400px); border-radius: 22px; overflow: hidden; margin: 0 -4px; }\n#cv { position: absolute; inset: 0; width: 100%; height: 100%; display: block; }\n#ladder { position: absolute; left: 8px; top: 14px; bottom: 104px; width: 70px; pointer-events: none; }\n#ladder .rail { position: absolute; left: 9px; top: 0; bottom: 0; width: 3px; border-radius: 2px;\n  background: linear-gradient(180deg, #ffe7a0, #e8962a); box-shadow: 0 0 6px rgba(255,190,80,.6); }\n.tick { position: absolute; left: 0; transform: translateY(-50%); display: flex; align-items: center; gap: 8px;\n  font-weight: 700; font-size: 15px; text-shadow: 0 1px 3px rgba(0,0,0,.6); transition: top .4s; }\n.tick::before { content: \"\"; width: 14px; height: 14px; margin-left: 3.5px; border-radius: 50%; flex: none;\n  background: radial-gradient(circle at 35% 30%, #fff6c8, #f2a93a 60%, #a0560e); }\n#ladderMark { position: absolute; left: -4px; min-width: 68px; text-align: center; z-index: 2; transform: translateY(-50%); padding: 2px 8px; border-radius: 999px; font-size: 13px; font-weight: 800;\n  color: #3a1400; background: linear-gradient(180deg, #fff1b8, #ffc24a); box-shadow: 0 0 10px rgba(255,190,80,.8); font-variant-numeric: tabular-nums;\n  white-space: nowrap; opacity: 0; transition: opacity .3s; }\n.conn { position: absolute; top: 10px; left: 50%; transform: translateX(-50%); background: rgba(255,90,122,.92); padding: 3px 12px;\n  border-radius: 999px; font-size: 12px; }\n\n.status { position: absolute; left: 0; right: 0; bottom: 4px; display: flex; align-items: center; justify-content: center; gap: 2px; z-index: 1; pointer-events: none;\n  background: radial-gradient(60% 70% at 50% 60%, rgba(20,4,50,.55), rgba(20,4,50,0)); }\n.laurel { width: 30px; height: 68px; flex: none; } .laurel.r { transform: scaleX(-1); }\n.status-mid { min-width: 210px; text-align: center; }\n#sub { font-size: 16px; text-shadow: 0 1px 4px rgba(0,0,0,.7); font-weight: 700; color: #fff; letter-spacing: 2px; min-height: 24px; }\n#mult { font-size: 50px; font-weight: 900; font-style: italic; line-height: 1.05; font-variant-numeric: tabular-nums; letter-spacing: 1px; padding: 0 6px; }\n#mult.crashed { background: linear-gradient(180deg, #ffe0e6, #ff6f8f 55%, #d1244d); -webkit-background-clip: text; background-clip: text;\n  filter: drop-shadow(0 2px 0 #5a0018) drop-shadow(0 0 12px rgba(255,80,120,.45)); }\n\n.ticker { display: flex; align-items: center; gap: 10px; margin: 8px 0 10px; padding: 5px 14px; min-height: 40px;\n  border-top: 1px solid var(--line); border-bottom: 1px solid var(--line);\n  background: linear-gradient(90deg, transparent, rgba(80,30,160,.45), transparent); }\n.horn { width: 30px; height: 26px; flex: none; }\n#tickTxt { flex: 1; min-width: 0; font-size: 15px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; animation: tin .35s; }\n#tickTxt b { color: var(--gold); }\n@keyframes tin { from { opacity: 0; transform: translateY(6px); } }\n\n.card { background: linear-gradient(180deg, var(--glass), var(--glass2)); border: 1px solid var(--line); border-radius: 22px;\n  padding: 10px 12px 14px; box-shadow: inset 0 1px 0 rgba(255,255,255,.08), 0 10px 30px rgba(10,0,40,.4); }\n.card-h { display: flex; align-items: center; gap: 10px; justify-content: center; font-size: 17px; font-weight: 800; letter-spacing: 2px; margin-bottom: 8px; }\n.card-h i { flex: 1; max-width: 70px; height: 1px; background: linear-gradient(90deg, transparent, var(--gold)); }\n.card-h i:last-child { transform: scaleX(-1); }\n\n.stakes { display: grid; grid-template-columns: repeat(3, 1fr); gap: 10px; }\n.stake { position: relative; display: flex; flex-direction: column; align-items: center; justify-content: flex-end; height: 92px;\n  border-radius: 18px; background: rgba(20, 6, 52, .45); border: 1px solid var(--line2); padding-bottom: 8px; }\n.stake b { font-size: 16px; }\n.coins { position: absolute; width: 60px; height: 24px; left: 50%; transform: translateX(-50%); filter: drop-shadow(0 3px 3px rgba(0,0,0,.45)); }\n.coins.n1 { top: 26px; }\n.coins.n2 { top: 30px; } .coins.n2.b { top: 21px; }\n.coins.n3 { top: 34px; } .coins.n3.b { top: 25px; } .coins.n3.c { top: 16px; }\n.stake.on { border-color: #ffd36a; background: radial-gradient(90% 80% at 50% 30%, rgba(255,190,80,.28), rgba(40,10,90,.6));\n  box-shadow: 0 0 0 1px #ffd36a, 0 0 18px rgba(255,190,80,.45); }\n.stake.on::after { content: \"\"; position: absolute; bottom: -7px; left: 22%; right: 22%; height: 4px; border-radius: 3px;\n  background: #8cff4a; box-shadow: 0 0 8px #8cff4a; }\n.stake:disabled { opacity: .38; }\n\n.fly-row, .meta { display: flex; align-items: center; justify-content: space-around; padding: 6px 6px; border-radius: 16px;\n  background: rgba(20, 6, 52, .45); border: 1px solid var(--line2); }\n.fly-row > div, .meta > div, #btnAuto { display: flex; flex-direction: column; align-items: center; gap: 2px; }\n.fly-row span, .meta span { color: var(--dim); font-size: 13px; }\n.fly-row b, .meta b { font-size: 18px; font-variant-numeric: tabular-nums; }\n.meta b#balance { color: var(--gold); }\n.sep { width: 1px; align-self: stretch; background: var(--line2); }\n#btnAuto em { position: absolute; margin: 18px 0 0 92px; font-style: normal; color: var(--gold); font-size: 20px; }\n#btnAuto { position: relative; padding: 0 14px; }\n.fly-label { text-align: center; color: var(--dim); margin-top: 6px; font-size: 13px; }\n.fly-big { text-align: center; font-size: 44px; font-weight: 900; font-style: italic; line-height: 1.1; font-variant-numeric: tabular-nums; }\n.fly-big small { font-size: 20px; font-style: normal; margin-left: 4px; }\n.meta { margin-top: 10px; }\n\n.action { width: 100%; margin-top: 12px; min-height: 62px; padding: 10px; border-radius: 999px; font-size: 24px; font-weight: 900; line-height: 1.15;\n  color: #c9b8ee; background: rgba(30, 10, 70, .6); border: 1.5px solid var(--line); letter-spacing: 1px; }\n.action small { display: block; font-size: 13px; font-weight: 600; opacity: .9; letter-spacing: 0; }\n.action.go, .action.cash { color: #0b3a05; border: 0; text-shadow: 0 1px 0 rgba(255,255,255,.45);\n  background: linear-gradient(180deg, #c4ff8c 0%, #4be35a 45%, #1fa82c 100%);\n  box-shadow: inset 0 2px 0 rgba(255,255,255,.65), inset 0 -4px 0 rgba(0,70,0,.3), 0 0 0 2px #ffcf66, 0 6px 0 #a8650e, 0 12px 26px rgba(75,227,90,.35); }\n.action.go:active, .action.cash:active { transform: translateY(3px); box-shadow: inset 0 2px 0 rgba(255,255,255,.65), 0 0 0 2px #ffcf66, 0 3px 0 #a8650e; }\n.action.cash { min-height: 72px; font-size: 28px; animation: pulse 1s infinite; }\n@keyframes pulse { 50% { box-shadow: inset 0 2px 0 rgba(255,255,255,.65), inset 0 -4px 0 rgba(0,70,0,.3), 0 0 0 2px #ffcf66, 0 6px 0 #a8650e, 0 0 34px rgba(120,255,110,.75); } }\n.action.cancel { color: #ffe7a6; background: linear-gradient(180deg, rgba(255,190,80,.18), rgba(120,50,10,.2)); border-color: #ffcf66; }\n.action.done { color: #b9ffbf; border-color: rgba(75,227,90,.6); background: rgba(30,120,40,.22); }\n.action.lose { color: #ffc2cf; border-color: rgba(255,90,122,.6); background: rgba(150,20,60,.22); }\n.refill { width: 100%; margin-top: 12px; padding: 13px; border-radius: 999px; font-weight: 800; color: #3a1400;\n  background: linear-gradient(180deg, #fff1b8, #ffc24a); box-shadow: 0 4px 0 #a8650e; }\n\n#players { margin-top: 14px; }\n.players-sub { text-align: center; color: var(--dim); font-size: 12px; margin: -6px 0 6px; }\n#plist { list-style: none; margin: 0; padding: 0; }\n#plist li { display: flex; align-items: center; gap: 10px; padding: 8px 4px; border-top: 1px solid rgba(255,205,120,.1); }\n#plist li:first-child { border-top: 0; }\n.pn { flex: 1; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }\n.pn i { font-style: normal; font-size: 11px; color: #3a1400; background: var(--gold); border-radius: 6px; padding: 0 5px; margin-left: 6px; }\n.pb { color: var(--dim); font-size: 13px; font-variant-numeric: tabular-nums; }\n.ps { min-width: 92px; text-align: right; font-weight: 800; font-size: 14px; font-variant-numeric: tabular-nums; }\n.ps.win { color: #7dff86; } .ps.lose { color: var(--red); } .ps.fly { color: #8fd2ff; } .ps.dim { color: var(--dim); font-weight: 500; }\n.off { opacity: .5; }\n\n.rules { display: flex; gap: 12px; align-items: flex-start; margin-top: 14px; padding: 12px 16px; border-radius: 22px;\n  border: 1px solid var(--line); background: linear-gradient(90deg, rgba(90,40,170,.5), rgba(40,14,92,.5)); }\n.rules-ic { font-size: 26px; color: var(--gold); line-height: 1; margin-top: 2px; text-shadow: 0 0 10px rgba(255,190,80,.6); }\n.rules p { margin: 0; font-size: 13px; color: #ddd0ff; } .rules b { color: var(--gold); }\n\n/* ---------- 弹窗 ---------- */\n.modal { position: fixed; inset: 0; z-index: 10; display: grid; place-items: center; padding: 24px; background: rgba(8, 2, 24, .72); backdrop-filter: blur(5px); }\n.modal-card { width: 100%; max-width: 360px; text-align: center; border-radius: 26px; padding: 22px;\n  background: linear-gradient(180deg, #3d1690, #1d0846); border: 1px solid var(--line); }\n.modal-card h2 { margin: 6px 0 4px; font-size: 26px; } .modal-card p { margin: 0 0 16px; color: var(--dim); }\n.modal-card input { width: 100%; margin-bottom: 16px; }\n.sheet { place-items: end center; padding: 0; }\n.sheet-card { width: 100%; max-width: 480px; padding: 18px 16px calc(18px + var(--safe-b)); border-radius: 26px 26px 0 0;\n  background: linear-gradient(180deg, #3d1690, #1d0846); border-top: 1px solid var(--line); animation: up .25s; }\n@keyframes up { from { transform: translateY(40px); opacity: 0; } }\n.sheet-tip { color: var(--dim); font-size: 13px; text-align: center; margin: -4px 0 12px; }\n.autos { display: grid; grid-template-columns: repeat(3, 1fr); gap: 8px; }\n.pill { padding: 11px 0; border-radius: 14px; font-weight: 700; background: rgba(20,6,52,.5); border: 1px solid var(--line2); }\n.pill.on { border-color: #ffd36a; color: #ffe08a; background: rgba(255,190,80,.16); box-shadow: 0 0 12px rgba(255,190,80,.35); }\n.pill:disabled { opacity: .4; }\n.custom { display: flex; align-items: center; gap: 8px; margin-top: 10px; }\n\n.toast { position: fixed; left: 50%; top: calc(64px + env(safe-area-inset-top, 0px)); transform: translate(-50%, -12px); opacity: 0; pointer-events: none;\n  background: linear-gradient(180deg, #4a1c9e, #2a0c62); border: 1px solid var(--gold); padding: 10px 18px; border-radius: 16px; max-width: 86vw;\n  text-align: center; font-weight: 700; transition: .25s; z-index: 20; box-shadow: 0 8px 24px rgba(0,0,0,.4); }\n.toast.show { opacity: 1; transform: translate(-50%, 0); }\n\n.fly-big .neg { background: linear-gradient(180deg, #ffe0e6, #ff6f8f 55%, #d1244d); -webkit-background-clip: text; background-clip: text; color: transparent; }\n", "favicon.svg": "<svg xmlns=\"http://www.w3.org/2000/svg\" xmlns:xlink=\"http://www.w3.org/1999/xlink\" viewBox=\"0 0 64 64\">\n  <defs>\n    <g id=\"p\">\n      <path d=\"M6 40 L58 14 L38 50 L30 38 Z\" fill=\"#f4f7ff\"/>\n      <path d=\"M30 38 L58 14 L26 44 Z\" fill=\"#c9d4f2\"/>\n      <path d=\"M30 38 L33 54 L38 50 Z\" fill=\"#ff7a1a\"/>\n    </g>\n  </defs>\n  <rect width=\"64\" height=\"64\" rx=\"14\" fill=\"#0e1b45\"/>\n  <use href=\"#p\"/>\n</svg>\n"};
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
