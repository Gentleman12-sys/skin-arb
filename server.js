#!/usr/bin/env node
/* ============================================================================
 * СПРЕД — арбитраж скинов CS2 · Steam ↔ LIS-Skins
 * ----------------------------------------------------------------------------
 * Бэкенд на чистом Node.js (только встроенные модули, без npm install).
 *
 * Зачем нужен бэкенд: эндпоинты Steam (priceoverview) и LIS-Skins не отдают
 * данные напрямую в браузер — мешает CORS, а у Steam ещё и жёсткий лимит
 * запросов. Этот сервер выступает прокси + кэшем + считалкой спреда, а
 * фронтенд (spread-arbitrage.html) ходит к нему за реальными ценами.
 *
 * Оптимизация: LIS-прайс выгружается ОДИН раз при старте, агрегируется до
 * Map<market_hash_name, usd> (~19K записей) и кэшируется в памяти + на диск.
 * Обновление в фоне каждые PRICES_TTL секунд — поиск не блокируется.
 *
 * Запуск:
 *   node server.js                 — поднять веб-сервер (по умолчанию :8787)
 *   node server.js serve --port N — то же, на порту N
 *   node server.js search 8000 [--currency RUB] [--corridor 5] [--net]
 *                                  [--mode auto|live|demo]   — поиск в консоли
 *   node server.js fx             — показать курсы валют
 *   node server.js steam "<name>" — цена одного скина в Steam
 *   node server.js diag           — формат прайс-листа LIS
 *
 * Все цены внутри считаются в USD (LIS отдаёт USD), пользователю
 * показываются в выбранной валюте по курсу USD→валюта.
 * ========================================================================== */

'use strict';

const http  = require('http');
const https = require('https');
const zlib  = require('zlib');
const fs    = require('fs');
const path  = require('path');
const crypto= require('crypto');
const { URL } = require('url');

const VERSION = '2.0.0';
const ROOT    = __dirname;

/* ============================================================================
 * КОНФИГ (всё переопределяется переменными окружения)
 * ========================================================================== */
const CFG = {
  port: int(process.env.PORT, 8787),
  cacheDir: process.env.CACHE_DIR || path.join(ROOT, '.cache'),

  // Источник курсов валют (USD-база, без ключа). Фолбэк — константы из демо.
  fxUrl: process.env.FX_PROVIDER_URL || 'https://open.er-api.com/v6/latest/USD',
  fxTtl: int(process.env.FX_TTL, 6 * 3600) * 1000,

  // LIS-Skins. Приоритет: локальный файл → API по токену → bulk-JSON по ссылке.
  lisPricesFile: process.env.LIS_PRICES_FILE || '',
  lisApiBase:    process.env.LIS_API_BASE || 'https://api.lis-skins.com/v1',
  lisApiToken:   process.env.LIS_API_TOKEN || '',
  lisBulkUrl:    process.env.LIS_BULK_URL || 'https://lis-skins.com/market_export_json/api_csgo_full.json',

  pricesTtl: int(process.env.PRICES_TTL, 30 * 60) * 1000,  // 30 мин

  // Steam priceoverview: appid 730 (CS2), currency=1 (USD).
  steamTtl:         int(process.env.STEAM_TTL, 6 * 3600) * 1000,
  steamDelayMs:     int(process.env.STEAM_DELAY_MS, 3500),     // ~17 запросов/мин
  steamMaxLookups:  int(process.env.STEAM_MAX_LOOKUPS, 40),   // потолок «свежих» запросов
  steamRetries:     int(process.env.STEAM_RETRIES, 3),

  // Комиссия Steam при продаже (для режима «чистыми»).
  steamFee: float(process.env.STEAM_FEE, 0.15),

  // demo | live | auto
  defaultMode: (process.env.MODE || 'auto').toLowerCase(),

  httpTimeout: int(process.env.HTTP_TIMEOUT, 15000),  // увеличено для bulk (640МБ)
  userAgent: process.env.USER_AGENT ||
    'Mozilla/5.0 (compatible; SpreadArbBot/2.0; +https://localhost)',
  quiet: process.env.QUIET === '1',
};

// Шаблоны ссылок
const LINKS = {
  steam: (mhn) => `https://steamcommunity.com/market/listings/730/${encodeURIComponent(mhn)}`,
  lis:   (base) => `https://lis-skins.com/market/csgo/?query=${encodeURIComponent(base)}`,
};

const WEARS = ['Factory New', 'Minimal Wear', 'Field-Tested', 'Well-Worn', 'Battle-Scarred'];

/* ============================================================================
 * МЕЛКИЕ УТИЛИТЫ
 * ========================================================================== */
function int(v, d)  { const n = parseInt(v, 10);  return Number.isFinite(n) ? n : d; }
function float(v, d){ const n = parseFloat(v);     return Number.isFinite(n) ? n : d; }
function sleep(ms)  { return new Promise((r) => setTimeout(r, ms)); }

// Структурированное логирование с таймстемпом
const logLevel = process.env.LOG_LEVEL === 'debug' ? 1 : 0;
function log(level, ...a) {
  if (level === 'debug' && !logLevel) return;
  if (CFG.quiet && level !== 'error' && level !== 'warn') return;
  const ts = new Date().toISOString();
  const prefix = level === 'error' ? 'ERR' : level === 'warn' ? 'WRN' : level === 'debug' ? 'DBG' : 'INF';
  console.error(`${ts} [${prefix}]`, ...a);
}
function info(...a)  { log('info', ...a); }
function warn(...a)  { log('warn', ...a); }
function error(...a) { log('error', ...a); }
function debug(...a) { log('debug', ...a); }

// Нормализация имени скина: убрать NBSP и лишние пробелы, сохранить ★ и ™.
function normName(s) {
  return String(s == null ? '' : s)
    .replace(/\u00A0/g, ' ')
    .replace(/\s+/g, ' ')
    .trim();
}

// Разбор денежной строки в число
function parseMoney(v) {
  if (typeof v === 'number') return Number.isFinite(v) ? v : null;
  if (v == null) return null;
  let s = String(v).replace(/[^\d.,-]/g, '');
  if (s.indexOf(',') > -1 && s.indexOf('.') > -1) {
    s = s.replace(/,/g, '');
  } else if (s.indexOf(',') > -1) {
    s = /,\d{1,2}$/.test(s) ? s.replace(',', '.') : s.replace(/,/g, '');
  }
  const n = parseFloat(s);
  return Number.isFinite(n) ? n : null;
}

// Выделить износ из market_hash_name
function splitWear(mhn) {
  const m = String(mhn).match(/^(.*\S)\s+\(([^()]+)\)\s*$/);
  if (m && WEARS.includes(m[2])) return { base: m[1], wear: m[2] };
  return { base: String(mhn), wear: '' };
}

/* ============================================================================
 * HTTP-КЛИЕНТ (https/http + gzip + таймаут + ретраи с бэк-оффом)
 * ========================================================================== */
function httpGet(urlStr, opts = {}) {
  const { headers = {}, timeout = CFG.httpTimeout, retries = 2 } = opts;
  return new Promise((resolve, reject) => {
    let attempt = 0;
    const go = () => {
      let u;
      try { u = new URL(urlStr); } catch (e) { return reject(e); }
      const mod = u.protocol === 'http:' ? http : https;
      const req = mod.request(u, {
        method: 'GET',
        headers: {
          'User-Agent': CFG.userAgent,
          'Accept': 'application/json,text/plain,*/*',
          'Accept-Encoding': 'gzip, deflate',
          ...headers,
        },
      }, (res) => {
        const code = res.statusCode || 0;
        if (code >= 300 && code < 400 && res.headers.location) {
          res.resume();
          urlStr = new URL(res.headers.location, u).toString();
          if (attempt++ < 5) return go();
          return reject(new Error('too many redirects'));
        }
        const chunks = [];
        res.on('data', (c) => chunks.push(c));
        res.on('end', () => {
          let buf = Buffer.concat(chunks);
          const enc = (res.headers['content-encoding'] || '').toLowerCase();
          try {
            if (enc === 'gzip') buf = zlib.gunzipSync(buf);
            else if (enc === 'deflate') buf = zlib.inflateSync(buf);
            else if (enc === 'br') buf = zlib.brotliDecompressSync(buf);
          } catch (_) { /* отдадим как есть */ }
          const body = buf.toString('utf8');
          if (code === 429) {
            const err = new Error('HTTP 429 (rate limited)');
            err.statusCode = 429; err.body = body;
            return reject(err);
          }
          if (code < 200 || code >= 300) {
            const err = new Error('HTTP ' + code);
            err.statusCode = code; err.body = body;
            return reject(err);
          }
          resolve({ status: code, headers: res.headers, body });
        });
      });
      req.setTimeout(timeout, () => req.destroy(new Error('timeout')));
      req.on('error', (e) => {
        if (attempt++ < retries) return setTimeout(go, 400 * attempt);
        reject(e);
      });
      req.end();
    };
    go();
  });
}

async function httpGetJson(urlStr, opts) {
  const r = await httpGet(urlStr, opts);
  try { return JSON.parse(r.body); }
  catch (e) { const err = new Error('bad JSON from ' + urlStr); err.body = r.body; throw err; }
}

/* ============================================================================
 * ДИСКОВЫЙ КЭШ (+ память)
 * ========================================================================== */
const memCache = new Map();
function cacheKey(k)     { return crypto.createHash('sha1').update(k).digest('hex').slice(0, 24); }
function cacheFile(k)   { return path.join(CFG.cacheDir, cacheKey(k) + '.json'); }

function cacheGet(k, ttl) {
  const m = memCache.get(k);
  if (m && Date.now() - m.ts < ttl) return m.val;
  try {
    const raw = fs.readFileSync(cacheFile(k), 'utf8');
    const obj = JSON.parse(raw);
    if (Date.now() - obj.ts < ttl) {
      memCache.set(k, obj);
      return obj.val;
    }
  } catch (_) { /* нет кэша */ }
  return undefined;
}
function cacheSet(k, val) {
  const obj = { ts: Date.now(), val };
  memCache.set(k, obj);
  try {
    fs.mkdirSync(CFG.cacheDir, { recursive: true });
    fs.writeFileSync(cacheFile(k), JSON.stringify(obj));
  } catch (e) { warn('cache write failed:', e.message); }
}

/* ============================================================================
 * ДЕМО-ДАННЫЕ (data/demo_prices.json) + аварийный встроенный мини-набор
 * ========================================================================== */
const BUILTIN_DEMO = {
  fx_fallback: { USD: 1, RUB: 92.0, EUR: 0.92, KZT: 475, UAH: 41 },
  skins: [
    { name: 'AK-47 | Asiimov',   wear: 'Field-Tested', lis: 85.5,  steam: 66.2 },
    { name: 'AK-47 | Redline',   wear: 'Field-Tested', lis: 86.0,  steam: 71.4 },
    { name: 'AWP | Asiimov',     wear: 'Well-Worn',     lis: 90.5,  steam: 79.2 },
    { name: '★ Karambit | Doppler', wear: 'Factory New', lis: 290.1, steam: null, why: 'символ ★' },
  ],
};
let DEMO = BUILTIN_DEMO;
try {
  DEMO = JSON.parse(fs.readFileSync(path.join(ROOT, 'data', 'demo_prices.json'), 'utf8'));
} catch (_) { info('demo_prices.json не найден — использую встроенный мини-набор'); }

const FALLBACK_FX = Object.assign({ USD: 1, RUB: 92, EUR: 0.92, KZT: 475, UAH: 41 }, DEMO.fx_fallback || {});

/* ============================================================================
 * КУРСЫ ВАЛЮТ
 * ========================================================================== */
async function getFx() {
  const cached = cacheGet('fx:USD', CFG.fxTtl);
  if (cached) return cached;
  try {
    const data = await httpGetJson(CFG.fxUrl, { retries: 1 });
    const rates = data && (data.rates || data.conversion_rates);
    if (rates && rates.RUB) {
      const out = { rates, source: hostOf(CFG.fxUrl), ts: Date.now() };
      cacheSet('fx:USD', out);
      return out;
    }
  } catch (e) { warn('fx provider failed:', e.message); }
  return { rates: FALLBACK_FX, source: 'fallback', ts: Date.now() };
}
function resolveRate(fx, currency) {
  const c = String(currency || 'USD').toUpperCase();
  if (fx.rates && Number.isFinite(fx.rates[c])) return fx.rates[c];
  return FALLBACK_FX[c] || 1;
}
function hostOf(u) { try { return new URL(u).host; } catch (_) { return u; } }

/* ============================================================================
 * STEAM — priceoverview, USD, кэш + сериализованная очередь с паузами
 * ========================================================================== */
let steamChain = Promise.resolve();
let lastSteamAt = 0;
function enqueueSteam(fn) {
  const run = steamChain.then(async () => {
    const wait = CFG.steamDelayMs - (Date.now() - lastSteamAt);
    if (wait > 0) await sleep(wait);
    try { return await fn(); }
    finally { lastSteamAt = Date.now(); }
  });
  steamChain = run.then(() => {}, () => {});
  return run;
}

async function getSteamPrice(mhn) {
  const key = 'steam:' + mhn;
  const cached = cacheGet(key, CFG.steamTtl);
  if (cached !== undefined) return Object.assign({ source: 'cache' }, cached);

  let delay = CFG.steamDelayMs;
  for (let attempt = 0; attempt <= CFG.steamRetries; attempt++) {
    try {
      const out = await enqueueSteam(async () => {
        const url = 'https://steamcommunity.com/market/priceoverview/?appid=730&currency=1'
          + '&market_hash_name=' + encodeURIComponent(mhn);
        const data = await httpGetJson(url, { retries: 0, timeout: CFG.httpTimeout });
        if (!data || data.success !== true) return { price: null };
        const raw = data.lowest_price || data.median_price || null;
        return { price: parseMoney(raw) };
      });
      const result = { price: out.price, source: 'steam' };
      cacheSet(key, { price: out.price });
      return result;
    } catch (e) {
      if (e.statusCode === 429 && attempt < CFG.steamRetries) {
        delay = Math.min(delay * 2, 30000);
        warn(`steam 429 «${mhn}» — пауза ${delay}мс`);
        await sleep(delay);
        continue;
      }
      return { price: null, source: 'error', error: e.message };
    }
  }
  return { price: null, source: 'error', error: 'retries exhausted' };
}

/* ============================================================================
 * ПАРСЕР ПРАЙС-ЛИСТОВ (универсальный) → Map<market_hash_name, usd>
 * Понимает: массив объектов, словарь {name: price}, обёртки items/data/prices,
 * а также Lis-Skins bulk-формат (items[] с id/name/price — агрегирует дубликаты).
 * ========================================================================== */
const NAME_FIELDS  = ['market_hash_name', 'market_name', 'hash_name', 'name', 'fullName', 'title'];
const PRICE_FIELDS = ['price', 'payout', 'suggested_price', 'lowest_price', 'value', 'usd', 'priceUsd', 'min_price'];

function pickField(obj, fields) {
  for (const f of fields) if (obj[f] != null && obj[f] !== '') return obj[f];
  return undefined;
}

function parsePriceList(raw) {
  const map = new Map();
  let data = raw;
  if (data && !Array.isArray(data) && typeof data === 'object') {
    if (Array.isArray(data.items))   data = data.items;
    else if (Array.isArray(data.data))    data = data.data;
    else if (Array.isArray(data.prices))  data = data.prices;
    else if (Array.isArray(data.result))  data = data.result;
  }
  if (Array.isArray(data)) {
    for (const it of data) {
      if (!it || typeof it !== 'object') continue;
      const name = normName(pickField(it, NAME_FIELDS));
      const price = parseMoney(pickField(it, PRICE_FIELDS));
      if (name && price != null && price > 0) keepMax(map, name, price);
    }
  } else if (data && typeof data === 'object') {
    for (const [k, v] of Object.entries(data)) {
      const name = normName(k);
      let price = null;
      if (typeof v === 'number' || typeof v === 'string') price = parseMoney(v);
      else if (v && typeof v === 'object') price = parseMoney(pickField(v, PRICE_FIELDS));
      if (name && price != null && price > 0) keepMax(map, name, price);
    }
  }
  return map;
}
function keepMax(map, name, price) {
  const prev = map.get(name);
  if (prev == null || price > prev) map.set(name, price);
}

async function loadPriceFileOrUrl(file, url, headers) {
  if (file) {
    info(`LIS: загрузка из файла ${path.basename(file)} …`);
    const raw = JSON.parse(fs.readFileSync(file, 'utf8'));
    const map = parsePriceList(raw);
    info(`LIS: ${map.size.toLocaleString()} уникальных скинов из файла`);
    return { map, source: 'file:' + path.basename(file) };
  }
  if (url) {
    info(`LIS: загрузка из ${hostOf(url)} …`);
    const t0 = Date.now();
    const raw = await httpGetJson(url, { headers, retries: 2, timeout: 120000 }); // 2 мин для bulk
    const map = parsePriceList(raw);
    const elapsed = ((Date.now() - t0) / 1000).toFixed(1);
    info(`LIS: ${map.size.toLocaleString()} уникальных скинов за ${elapsed}с`);
    return { map, source: hostOf(url) };
  }
  return { map: new Map(), source: 'none' };
}

/* ============================================================================
 * АДАПТЕР LIS-SKINS → Map<mhn, usd>  (единственная площадка)
 *
 * Оптимизация: прайс загружается один раз при старте и периодически
 * обновляется в фоне. Кэш — память + диск.
 * ========================================================================== */
let lisState = { map: new Map(), source: 'none', loading: false, lastRefresh: 0, error: null };

async function refreshLisPrices() {
  if (lisState.loading) return lisState;
  lisState.loading = true;
  try {
    // Приоритет: локальный файл → API по токену → bulk-URL
    let res;
    if (CFG.lisPricesFile) {
      res = await loadPriceFileOrUrl(CFG.lisPricesFile, '');
    } else if (CFG.lisApiToken) {
      const url = CFG.lisApiBase.replace(/\/$/, '') + '/market/prices';
      res = await loadPriceFileOrUrl('', url, { Authorization: 'Bearer ' + CFG.lisApiToken });
    } else {
      res = await loadPriceFileOrUrl('', CFG.lisBulkUrl);
    }
    if (res.map.size) {
      // Кэшируем как массив пар для JSON-сериализации
      cacheSet('prices:lis', { entries: [...res.map], source: res.source });
      lisState.map    = res.map;
      lisState.source = res.source;
      lisState.error  = null;
    }
    lisState.lastRefresh = Date.now();
    return lisState;
  } catch (e) {
    error('LIS prices failed:', e.message);
    lisState.error = e.message;
    return lisState;
  } finally {
    lisState.loading = false;
  }
}

// Попробовать восстановить из кэша при старте (мгновенно)
function initLisFromCache() {
  const cached = cacheGet('prices:lis', CFG.pricesTtl * 2); // двойной TTL для старта
  if (cached) {
    lisState.map    = new Map(cached.entries);
    lisState.source = cached.source;
    info(`LIS: восстановлено из кэша — ${lisState.map.size.toLocaleString()} скинов (${cached.source})`);
    return true;
  }
  return false;
}

// Фоновое обновление прайсов
let bgRefreshTimer = null;
function startBgRefresh() {
  if (bgRefreshTimer) clearInterval(bgRefreshTimer);
  bgRefreshTimer = setInterval(async () => {
    debug('LIS: фоновое обновление прайсов …');
    await refreshLisPrices();
  }, CFG.pricesTtl);
  // Не даем таймеру удерживать процесс
  if (bgRefreshTimer.unref) bgRefreshTimer.unref();
}

/* ============================================================================
 * СБОРКА ТАБЛИЦЫ РЫНКА
 * ========================================================================== */
function demoTable() {
  return (DEMO.skins || []).map((s) => {
    const name = normName(s.name);
    const wear = s.wear || splitWear(name).wear;
    const base = splitWear(name).base;
    return {
      name: base, wear,
      mhn: wear && !/\(/.test(name) ? `${base} (${wear})` : name,
      lis: parseMoney(s.lis),
      steam: s.steam == null ? null : parseMoney(s.steam),
      why: s.why,
    };
  });
}

async function liveTable() {
  const map = lisState.map;
  const rows = [];
  for (const [mhn, price] of map) {
    const { base, wear } = splitWear(mhn);
    rows.push({
      name: base, wear, mhn,
      lis: price,
      steam: undefined, // подтянем точечно из Steam
    });
  }
  return { rows, source: lisState.source, error: lisState.error };
}

/* ============================================================================
 * ДВИЖОК АРБИТРАЖА
 * ========================================================================== */
async function runSearch(params) {
  const amount      = float(params.amount, 0);
  const currency    = String(params.currency || 'RUB').toUpperCase();
  const corridorPct = Math.max(0.5, float(params.corridor, 5));
  const net         = params.net === true || params.net === '1' || params.net === 'true';
  let mode          = ['auto', 'live', 'demo'].includes(params.mode) ? params.mode : CFG.defaultMode;

  const fx   = await getFx();
  const rate = resolveRate(fx, currency);
  const targetUsd = amount > 0 ? amount / rate : 0;
  const corr = corridorPct / 100;
  const lo   = targetUsd * (1 - corr);
  const hi   = targetUsd * (1 + corr);

  const warnings = [];
  let table, source, usedMode = mode;

  if (mode === 'demo') {
    table = demoTable();
    source = 'demo';
  } else {
    const live = await liveTable();
    const usable = live.rows.some((r) => r.lis != null && r.lis > 0);
    if (!usable && mode === 'auto') {
      warnings.push('Прайс-лист LIS недоступен/пуст — показываю демо-данные. См. README, как подключить источник.');
      table = demoTable();
      source = 'demo';
      usedMode = 'demo';
    } else {
      table = live.rows;
      source = live.source;
      usedMode = 'live';
      if (live.error) warnings.push('LIS: ' + live.error);
    }
  }

  // Кандидаты в ценовом коридоре
  const candidates = [];
  for (const r of table) {
    if (r.lis == null || r.lis <= 0) continue;
    if (targetUsd > 0 && (r.lis < lo || r.lis > hi)) continue;
    candidates.push({ ...r, payout: r.lis });
  }
  candidates.sort((a, b) => b.payout - a.payout);

  // Цены Steam по кандидатам
  const matched = [], unmatched = [];
  let freshLookups = 0;
  for (const c of candidates) {
    let steam = c.steam, steamSource = 'demo';
    if (usedMode === 'live') {
      const cachedHit = cacheGet('steam:' + c.mhn, CFG.steamTtl);
      if (cachedHit !== undefined) {
        steam = cachedHit.price;
        steamSource = 'cache';
      } else if (freshLookups < CFG.steamMaxLookups) {
        const sp = await getSteamPrice(c.mhn);
        steam = sp.price;
        steamSource = sp.source;
        freshLookups++;
      } else {
        unmatched.push({
          name: c.name, wear: c.wear, mhn: c.mhn,
          payout: c.payout,
          why: 'лимит Steam — повтори поиск, дозапросим',
        });
        continue;
      }
    }
    if (steam == null) {
      unmatched.push({
        name: c.name, wear: c.wear, mhn: c.mhn,
        payout: c.payout,
        why: c.why || 'нет цены в Steam (имя ≠ market_hash_name)',
      });
      continue;
    }
    let spread = c.payout - steam;
    if (net) spread -= steam * CFG.steamFee;
    const pct = steam > 0 ? (spread / steam) * 100 : 0;
    matched.push({
      name: c.name, wear: c.wear, mhn: c.mhn,
      lis: numOrNull(c.lis),
      payout: round2(c.payout), steam: round2(steam),
      spread: round2(spread), pct: Math.round(pct * 10) / 10, steamSource,
      links: { steam: LINKS.steam(c.mhn), lis: LINKS.lis(c.name) },
    });
  }
  matched.sort((a, b) => b.spread - a.spread);
  const best = matched.length
    ? matched.reduce((m, r) => (r.spread > m.spread ? r : m), matched[0])
    : null;

  return {
    ok: true, version: VERSION,
    mode: usedMode, net, currency,
    fx: { rate: round4(rate), source: fx.source, currency },
    query: { amount, targetUsd: round2(targetUsd), corridorPct,
             corridor: { lo: round2(lo), hi: round2(hi) } },
    meta: {
      candidates: candidates.length, matched: matched.length,
      unmatched: unmatched.length, steamLookups: freshLookups,
      lisSource: source, lisTotal: lisState.map.size,
      lisLastRefresh: lisState.lastRefresh,
    },
    best, rows: matched, unmatched, warnings,
  };
}

function numOrNull(v) { return Number.isFinite(v) ? round2(v) : null; }
function round2(n) { return Math.round(n * 100) / 100; }
function round4(n) { return Math.round(n * 10000) / 10000; }

/* ============================================================================
 * HTTP-СЕРВЕР
 * ========================================================================== */
const STATIC = {
  '/':                        { file: 'spread-arbitrage.html', type: 'text/html; charset=utf-8' },
  '/spread-arbitrage.html':   { file: 'spread-arbitrage.html', type: 'text/html; charset=utf-8' },
  '/data/demo_prices.json':   { file: 'data/demo_prices.json',  type: 'application/json; charset=utf-8' },
};

function sendJson(res, code, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(code, {
    'Content-Type': 'application/json; charset=utf-8',
    'Access-Control-Allow-Origin': '*',
    'Cache-Control': 'no-store',
  });
  res.end(body);
}

async function handleApi(pathname, q, res) {
  if (pathname === '/api/health') {
    return sendJson(res, 200, {
      ok: true, version: VERSION, mode: CFG.defaultMode,
      lis: {
        configured: !!(CFG.lisPricesFile || CFG.lisApiToken || CFG.lisBulkUrl),
        source: CFG.lisPricesFile ? 'file' : CFG.lisApiToken ? 'api' : 'bulk',
        total: lisState.map.size,
        cached: !!cacheGet('prices:lis', CFG.pricesTtl * 2),
        loading: lisState.loading,
        lastRefresh: lisState.lastRefresh || null,
        error: lisState.error,
      },
      steam: { delayMs: CFG.steamDelayMs, maxLookups: CFG.steamMaxLookups },
      demoSkins: (DEMO.skins || []).length,
      uptime: process.uptime(),
    });
  }
  if (pathname === '/api/fx') {
    const fx = await getFx();
    return sendJson(res, 200, { ok: true, base: 'USD', source: fx.source, rates: fx.rates });
  }
  if (pathname === '/api/steam') {
    const name = normName(q.get('name'));
    if (!name) return sendJson(res, 400, { ok: false, error: 'name required' });
    const sp = await getSteamPrice(name);
    return sendJson(res, 200, { ok: true, name, price: sp.price, source: sp.source, error: sp.error });
  }
  if (pathname === '/api/prices') {
    const sample = [...lisState.map].slice(0, int(q.get('limit'), 50));
    return sendJson(res, 200, {
      ok: true, exchange: 'lis', source: lisState.source,
      count: lisState.map.size,
      sample: sample.map(([name, price]) => ({ name, price })),
      error: lisState.error,
    });
  }
  if (pathname === '/api/search') {
    // Если LIS ещё не загружен — подождать
    if (lisState.map.size === 0 && !lisState.loading) {
      await refreshLisPrices();
    }
    const result = await runSearch({
      amount:   q.get('amount'),
      currency:  q.get('currency'),
      corridor:  q.get('corridor'),
      net:       q.get('net'),
      mode:      q.get('mode'),
    });
    return sendJson(res, 200, result);
  }
  return sendJson(res, 404, { ok: false, error: 'unknown endpoint' });
}

function serveStatic(pathname, res) {
  const entry = STATIC[pathname];
  if (!entry) {
    res.writeHead(404, { 'Content-Type': 'text/plain' });
    return res.end('404');
  }
  fs.readFile(path.join(ROOT, entry.file), (err, buf) => {
    if (err) {
      res.writeHead(404, { 'Content-Type': 'text/plain' });
      return res.end('not found');
    }
    res.writeHead(200, { 'Content-Type': entry.type, 'Access-Control-Allow-Origin': '*' });
    res.end(buf);
  });
}

let server = null;
function startServer(port) {
  server = http.createServer(async (req, res) => {
    let u;
    try { u = new URL(req.url, 'http://localhost'); } catch (_) {
      res.writeHead(400);
      return res.end('bad request');
    }
    if (req.method === 'OPTIONS') {
      res.writeHead(204, {
        'Access-Control-Allow-Origin': '*',
        'Access-Control-Allow-Methods': 'GET,OPTIONS',
        'Access-Control-Allow-Headers': 'Content-Type',
      });
      return res.end();
    }
    const pathname = u.pathname;
    if (pathname === '/favicon.ico') { res.writeHead(204); return res.end(); }
    if (pathname.startsWith('/api/')) {
      try {
        await handleApi(pathname, u.searchParams, res);
      } catch (e) {
        error('API error:', e.stack || e.message);
        sendJson(res, 500, { ok: false, error: e.message });
      }
      return;
    }
    serveStatic(pathname, res);
  });
  server.listen(port, () => {
    console.log('');
    console.log(`  СПРЕД v${VERSION} — сервер запущен`);
    console.log(`  → http://localhost:${port}`);
    console.log(`  Режим: ${CFG.defaultMode}`);
    const lisSrc = CFG.lisPricesFile ? 'файл' : CFG.lisApiToken ? 'API-токен' : 'bulk-URL';
    console.log(`  LIS: ${lisSrc} · Steam: priceoverview · FX: ${hostOf(CFG.fxUrl)}`);
    console.log('');
  });
  return server;
}

/* ============================================================================
 * CLI
 * ========================================================================== */
function parseArgs(argv) {
  const out = { _: [] };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a.startsWith('--')) {
      const key = a.slice(2);
      const next = argv[i + 1];
      if (next === undefined || next.startsWith('--')) out[key] = true;
      else { out[key] = next; i++; }
    } else out._.push(a);
  }
  return out;
}

function fmt(n, dp) {
  return Number(n).toLocaleString('ru-RU', { minimumFractionDigits: dp, maximumFractionDigits: dp });
}

async function cliSearch(args) {
  const amount = float(args._[0], 0);
  if (!amount) { console.error('Укажи сумму: node server.js search 8000'); process.exit(1); }
  const currency = (args.currency || 'RUB').toUpperCase();
  const result = await runSearch({
    amount, currency, corridor: args.corridor || 5,
    net: !!args.net, mode: args.mode || CFG.defaultMode,
  });
  const dp = ['RUB', 'KZT', 'UAH'].includes(currency) ? 0 : 2;
  const toCur = (usd) => fmt(usd * result.fx.rate, dp);

  console.log('');
  console.log(`  Режим: ${result.mode} · площадка: LIS · валюта: ${currency}` +
    (result.net ? ' · чистыми (−Steam 15%)' : ''));
  console.log(`  Курс USD→${currency}: ${result.fx.rate} (${result.fx.source})`);
  console.log(`  LIS: ${result.meta.lisTotal.toLocaleString()} скинов (${result.meta.lisSource})`);
  console.log(`  Цель: ${fmt(amount, dp)} ${currency} (~$${result.query.targetUsd}) · ` +
    `коридор ${toCur(result.query.corridor.lo)}–${toCur(result.query.corridor.hi)} ${currency} · ` +
    `кандидатов: ${result.meta.candidates}`);
  for (const w of result.warnings) console.log('  ⚠ ' + w);
  console.log('');

  if (!result.rows.length) {
    console.log('  Нет кандидатов в этом коридоре — расширь диапазон (--corridor 10).');
  } else {
    const pad  = (s, n) => String(s).slice(0, n).padEnd(n);
    const padL = (s, n) => String(s).padStart(n);
    console.log('  ' + pad('#', 3) + pad('Скин', 40) + padL('LIS платит', 14) +
      padL('Steam', 11) + padL('спред', 11) + padL('%', 8));
    console.log('  ' + '-'.repeat(87));
    result.rows.forEach((r, i) => {
      const star = result.best && r.mhn === result.best.mhn ? '★' : String(i + 1);
      console.log('  ' + pad(star, 3) + pad(`${r.name} (${r.wear})`, 40) +
        padL(toCur(r.payout), 14) + padL(toCur(r.steam), 11) +
        padL('+' + toCur(r.spread), 11) + padL('+' + r.pct.toFixed(1) + '%', 8));
    });
  }

  if (result.best) {
    console.log('');
    console.log(`  ★ Лучшая сделка: ${result.best.name} (${result.best.wear}) · LIS`);
    console.log(`    Steam ${toCur(result.best.steam)} → LIS платит ${toCur(result.best.payout)} ${currency}` +
      ` · спред +${toCur(result.best.spread)} ${currency} (+${result.best.pct.toFixed(1)}%)`);
    console.log(`    ${result.best.links.steam}`);
    console.log(`    ${result.best.links.lis}`);
  }
  if (result.unmatched.length) {
    console.log('');
    console.log(`  Не вошли в рейтинг (${result.unmatched.length}): нет цены Steam —`);
    result.unmatched.slice(0, 12).forEach((u) =>
      console.log(`    · ${u.name}${u.wear ? ' (' + u.wear + ')' : ''} — ${u.why}`));
  }
  console.log('');
  console.log('  Спред ≠ чистый профит: вычти комиссию Steam ~15%, курс и удержания LIS.');
  console.log('');
}

async function cliFx() {
  const fx = await getFx();
  console.log('Источник:', fx.source);
  for (const c of ['USD', 'RUB', 'EUR', 'KZT', 'UAH']) {
    if (fx.rates[c] != null) console.log(`  USD→${c}: ${fx.rates[c]}`);
  }
}

async function cliSteam(args) {
  const name = normName(args._.join(' '));
  if (!name) { console.error('Укажи имя: node server.js steam "AK-47 | Asiimov (Field-Tested)"'); process.exit(1); }
  const sp = await getSteamPrice(name);
  console.log(`${name}: ${sp.price == null ? 'нет цены' : '$' + sp.price} (${sp.source})${sp.error ? ' — ' + sp.error : ''}`);
}

async function cliDiag() {
  console.log(`Источник: LIS`);
  console.log(`  source=${lisState.source} · позиций=${lisState.map.size}${lisState.error ? ' · ошибка: ' + lisState.error : ''}`);
  [...lisState.map].slice(0, 10).forEach(([name, price]) => console.log(`    ${name} → $${price}`));
  if (!lisState.map.size) console.log('    (пусто — настрой LIS_PRICES_FILE / LIS_API_TOKEN, см. README)');
}

/* ============================================================================
 * LIFECYCLE — graceful shutdown + process handlers
 * ========================================================================== */
function setupProcessHandlers() {
  const shutdown = (sig) => {
    info(`получен ${sig} — завершение …`);
    if (server) {
      server.close(() => {
        info('сервер остановлен');
        process.exit(0);
      });
      // Ждём最多 5 сек, потом убиваем
      setTimeout(() => {
        warn('graceful shutdown timeout — принудительное завершение');
        process.exit(1);
      }, 5000).unref();
    } else {
      process.exit(0);
    }
  };
  process.on('SIGTERM', () => shutdown('SIGTERM'));
  process.on('SIGINT',  () => shutdown('SIGINT'));

  process.on('unhandledRejection', (reason, promise) => {
    error('Unhandled Rejection:', reason);
  });
  process.on('uncaughtException', (err) => {
    error('Uncaught Exception:', err.message, err.stack);
    // В продакшене можно решить — убивать или продолжать
    // Для арбитражного скрипта лучше упасть и перезапуститься
    process.exit(1);
  });
}

/* ============================================================================
 * ENTRY
 * ========================================================================== */
async function main() {
  const argv = process.argv.slice(2);
  const cmd  = argv[0];
  const args = parseArgs(argv.slice(1));

  setupProcessHandlers();

  if (cmd === 'search') return cliSearch(args);
  if (cmd === 'fx')     return cliFx();
  if (cmd === 'steam')  return cliSteam(args);
  if (cmd === 'diag')   return cliDiag();
  if (cmd === 'help' || cmd === '--help' || cmd === '-h') {
    console.log(fs.readFileSync(__filename, 'utf8').split('\n').slice(2, 22).join('\n').replace(/^ \* ?/gm, ''));
    return;
  }

  // serve (по умолчанию)
  const port = int((cmd === 'serve' ? args.port : process.env.PORT) || CFG.port, CFG.port);

  // 1) Восстановить LIS из кэша (мгновенно, если есть)
  initLisFromCache();

  // 2) Поднять сервер (не ждём загрузки прайсов)
  startServer(port);

  // 3) Загрузить/обновить LIS прайсы в фоне
  if (lisState.map.size === 0) {
    info('LIS: первая загрузка прайсов (может занять время для bulk) …');
  } else {
    info('LIS: обновление прайсов в фоне …');
  }
  refreshLisPrices().then(() => {
    info(`LIS: готов — ${lisState.map.size.toLocaleString()} скинов (${lisState.source})`);
  });

  // 4) Фоновое обновление каждые 30 мин
  startBgRefresh();
}

main().catch((e) => {
  error('fatal:', e.stack || e.message);
  process.exit(1);
});