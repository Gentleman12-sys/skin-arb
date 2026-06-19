#!/usr/bin/env node
/* ============================================================================
 * СПРЕД — арбитраж скинов CS2 · Steam ↔ LIS-Skins / CS.money
 * ----------------------------------------------------------------------------
 * Бэкенд на чистом Node.js (только встроенные модули, без npm install).
 *
 * Зачем нужен бэкенд: эндпоинты Steam (priceoverview) и LIS/CS.money не отдают
 * данные напрямую в браузер — мешает CORS, а у Steam ещё и жёсткий лимит
 * запросов. Этот сервер выступает прокси + кэшем + считалкой спреда, а
 * фронтенд (spread-arbitrage.html) ходит к нему за реальными ценами. Если
 * сервер не запущен, фронт работает автономно на демо-данных.
 *
 * Запуск:
 *   node server.js                 — поднять веб-сервер (по умолчанию :8787)
 *   node server.js serve --port N  — то же, на порту N
 *   node server.js search 8000 [--currency RUB] [--corridor 5]
 *                                  [--exchange best|lis|csmoney] [--net]
 *                                  [--mode auto|live|demo]   — поиск в консоли
 *   node server.js fx              — показать курсы валют
 *   node server.js steam "<name>"  — цена одного скина в Steam
 *   node server.js diag [--exchange lis] — формат прайс-листа источника
 *
 * Все цены внутри считаются в USD (источники отдают USD), пользователю
 * показываются в выбранной валюте по курсу USD→валюта.
 * ========================================================================== */

'use strict';

const http = require('http');
const https = require('https');
const zlib = require('zlib');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { URL } = require('url');

const VERSION = '1.0.0';
const ROOT = __dirname;

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
  // Если LIS_PRICES_FILE не задан, но рядом лежит data/lis_prices.json —
  // используем его автоматически (самый надёжный путь, не зависит от антибота).
  lisPricesFile: process.env.LIS_PRICES_FILE ||
    firstExisting([path.join(ROOT, 'data', 'lis_prices.json')]),
  lisApiBase: process.env.LIS_API_BASE || 'https://api.lis-skins.com/v1',
  lisApiToken: process.env.LIS_API_TOKEN || '',
  lisBulkUrl: process.env.LIS_BULK_URL || 'https://lis-skins.com/market_export_json/api_csgo_full.json',

  // CS.money. Локальный файл (или data/csmoney_prices.json) или JSON-эндпоинт.
  csmoneyPricesFile: process.env.CSMONEY_PRICES_FILE ||
    firstExisting([path.join(ROOT, 'data', 'csmoney_prices.json')]),
  csmoneyUrl: process.env.CSMONEY_URL || '',

  pricesTtl: int(process.env.PRICES_TTL, 30 * 60) * 1000,
  // Прайс-лист может быть большим — даём ему отдельный, увеличенный таймаут.
  pricesTimeout: int(process.env.PRICES_TIMEOUT, 30000),

  // Steam priceoverview: appid 730 (CS2), currency=1 (USD).
  steamTtl: int(process.env.STEAM_TTL, 6 * 3600) * 1000,
  steamDelayMs: int(process.env.STEAM_DELAY_MS, 3500),   // ~17 запросов/мин
  steamMaxLookups: int(process.env.STEAM_MAX_LOOKUPS, 40), // потолок «свежих» запросов на один поиск
  steamRetries: int(process.env.STEAM_RETRIES, 3),

  // Комиссия Steam при продаже (для режима «чистыми»).
  steamFee: float(process.env.STEAM_FEE, 0.15),

  // demo | live | auto — режим по умолчанию для API/CLI.
  defaultMode: (process.env.MODE || 'auto').toLowerCase(),

  httpTimeout: int(process.env.HTTP_TIMEOUT, 12000),
  // Реалистичный браузерный User-Agent: LIS/Steam за Cloudflare часто отвечают
  // 403 на «ботовые» UA. Переопределяется переменной USER_AGENT.
  userAgent: process.env.USER_AGENT ||
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 ' +
    '(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
  acceptLanguage: process.env.ACCEPT_LANGUAGE || 'en-US,en;q=0.9,ru;q=0.8',
  quiet: process.env.QUIET === '1',
};

// Шаблоны ссылок на скин на каждой площадке.
const LINKS = {
  steam: (mhn) => `https://steamcommunity.com/market/listings/730/${encodeURIComponent(mhn)}`,
  lis: (base) => `https://lis-skins.com/market/csgo/?query=${encodeURIComponent(base)}`,
  csmoney: (base) => `https://cs.money/market/buy/?search=${encodeURIComponent(base)}`,
};

const WEARS = ['Factory New', 'Minimal Wear', 'Field-Tested', 'Well-Worn', 'Battle-Scarred'];

/* ============================================================================
 * МЕЛКИЕ УТИЛИТЫ
 * ========================================================================== */
function int(v, d) { const n = parseInt(v, 10); return Number.isFinite(n) ? n : d; }
function float(v, d) { const n = parseFloat(v); return Number.isFinite(n) ? n : d; }
// Первый существующий файл из списка (для авто-подхвата data/lis_prices.json).
function firstExisting(paths) {
  for (const p of paths) { try { if (p && fs.statSync(p).isFile()) return p; } catch (_) { /* нет */ } }
  return '';
}
function sleep(ms) { return new Promise((r) => setTimeout(r, ms)); }
function log(...a) { if (!CFG.quiet) console.error(...a); }

// Нормализация имени скина: убрать NBSP и лишние пробелы, сохранить ★ и ™.
function normName(s) {
  return String(s == null ? '' : s)
    .replace(/ /g, ' ')
    .replace(/\s+/g, ' ')
    .trim();
}

// Разбор денежной строки в число: "$1,234.56", "1 234,56", "82.5", 82.5 → number|null
function parseMoney(v) {
  if (typeof v === 'number') return Number.isFinite(v) ? v : null;
  if (v == null) return null;
  let s = String(v).replace(/[^\d.,-]/g, '');
  if (s.indexOf(',') > -1 && s.indexOf('.') > -1) {
    s = s.replace(/,/g, '');                       // запятая = разделитель тысяч
  } else if (s.indexOf(',') > -1) {
    s = /,\d{1,2}$/.test(s) ? s.replace(',', '.') : s.replace(/,/g, '');
  }
  const n = parseFloat(s);
  return Number.isFinite(n) ? n : null;
}

// Выделить износ из market_hash_name: "AK-47 | Asiimov (Field-Tested)" → {base, wear}
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
          'Accept-Language': CFG.acceptLanguage,
          'Accept-Encoding': 'gzip, deflate',
          ...headers,
        },
      }, (res) => {
        const code = res.statusCode || 0;
        // редиректы
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
 * ДИСКОВЫЙ КЭШ (+ память). Файлы JSON под CACHE_DIR.
 * ========================================================================== */
const memCache = new Map();
function cacheKey(k) { return crypto.createHash('sha1').update(k).digest('hex').slice(0, 24); }
function cacheFile(k) { return path.join(CFG.cacheDir, cacheKey(k) + '.json'); }

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
  } catch (e) { log('cache write failed:', e.message); }
}

/* ============================================================================
 * ДЕМО-ДАННЫЕ (data/demo_prices.json) + аварийный встроенный мини-набор
 * ========================================================================== */
const BUILTIN_DEMO = {
  fx_fallback: { USD: 1, RUB: 92.0, EUR: 0.92, KZT: 475, UAH: 41 },
  skins: [
    { name: 'AK-47 | Asiimov', wear: 'Field-Tested', lis: 85.5, csmoney: 83.9, steam: 66.2 },
    { name: 'AK-47 | Redline', wear: 'Field-Tested', lis: 86.0, csmoney: 87.2, steam: 71.4 },
    { name: 'AWP | Asiimov', wear: 'Well-Worn', lis: 90.5, csmoney: 89.1, steam: 79.2 },
    { name: '★ Karambit | Doppler', wear: 'Factory New', lis: 290.1, csmoney: 305.0, steam: null, why: 'символ ★' },
  ],
};
let DEMO = BUILTIN_DEMO;
try {
  DEMO = JSON.parse(fs.readFileSync(path.join(ROOT, 'data', 'demo_prices.json'), 'utf8'));
} catch (_) { log('demo_prices.json не найден — использую встроенный мини-набор'); }

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
  } catch (e) { log('fx provider failed:', e.message); }
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

// Возвращает { price:number|null, source, error? }. null = цены в Steam нет.
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
        const raw = data.lowest_price || data.median_price || null; // минимальная, иначе медианная
        return { price: parseMoney(raw) };
      });
      const result = { price: out.price, source: 'steam' };
      cacheSet(key, { price: out.price });
      return result;
    } catch (e) {
      if (e.statusCode === 429 && attempt < CFG.steamRetries) {
        delay = Math.min(delay * 2, 30000);
        log(`steam 429 «${mhn}» — пауза ${delay}мс`);
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
 * Понимает: массив объектов, объект-словарь {name: price|{...}}, обёртки
 * {items:[...]}/{data:[...]}, цены строкой или числом.
 * ========================================================================== */
const NAME_FIELDS = ['market_hash_name', 'market_name', 'hash_name', 'name', 'fullName', 'title'];
const PRICE_FIELDS = ['price', 'payout', 'suggested_price', 'lowest_price', 'value', 'usd', 'priceUsd', 'min_price'];

function pickField(obj, fields) {
  for (const f of fields) if (obj[f] != null && obj[f] !== '') return obj[f];
  return undefined;
}

function parsePriceList(raw) {
  const map = new Map();
  let data = raw;
  if (data && !Array.isArray(data) && typeof data === 'object') {
    if (Array.isArray(data.items)) data = data.items;
    else if (Array.isArray(data.data)) data = data.data;
    else if (Array.isArray(data.prices)) data = data.prices;
    else if (Array.isArray(data.result)) data = data.result;
  }
  if (Array.isArray(data)) {
    for (const it of data) {
      if (!it || typeof it !== 'object') continue;
      const name = normName(pickField(it, NAME_FIELDS));
      const price = parseMoney(pickField(it, PRICE_FIELDS));
      if (name && price != null && price > 0) keepCheapest(map, name, price);
    }
  } else if (data && typeof data === 'object') {
    for (const [k, v] of Object.entries(data)) {
      const name = normName(k);
      let price = null;
      if (typeof v === 'number' || typeof v === 'string') price = parseMoney(v);
      else if (v && typeof v === 'object') price = parseMoney(pickField(v, PRICE_FIELDS));
      if (name && price != null && price > 0) keepCheapest(map, name, price);
    }
  }
  return map;
}
// Bulk-экспорт LIS — это МИЛЛИОНЫ отдельных листингов продавцов: на один
// market_hash_name приходятся десятки цен (разный float, наклейки, наценки).
// Рыночная цена скина = САМЫЙ ДЕШЁВЫЙ листинг (lowest ask): именно за столько его
// реально можно купить, и именно он соответствует цене чистого предмета в Steam.
// Брать максимум нельзя — это поймает экземпляр с дорогими наклейками или просто
// чью-то заведомо завышенную цену (баг с «Zeus за 1247₽» при реальных ~46₽).
function keepCheapest(map, name, price) {
  const prev = map.get(name);
  if (prev == null || price < prev) map.set(name, price);
}

async function loadPriceFileOrUrl(file, url, headers) {
  if (file) {
    const raw = JSON.parse(fs.readFileSync(file, 'utf8'));
    return { map: parsePriceList(raw), source: 'file:' + path.basename(file) };
  }
  if (url) {
    const raw = await httpGetJson(url, { headers, retries: 2, timeout: CFG.pricesTimeout });
    return { map: parsePriceList(raw), source: hostOf(url) };
  }
  return { map: new Map(), source: 'none' };
}

// Помечает результат загрузки прайса понятной ошибкой, если данных не пришло.
// 'none'/'skipped' — это «не настроено», а не ошибка, их не трогаем.
function flagEmpty(res, label) {
  if (res.map.size || res.source === 'none' || res.source === 'skipped') return res;
  res.error = res.error || `${label}: источник ${res.source} вернул 0 позиций — проверь формат/доступ`;
  return res;
}

/* ============================================================================
 * АДАПТЕРЫ ПЛОЩАДОК (выплата за скин, USD) → Map<mhn, usd>
 * ========================================================================== */
// Подсказка по типичным ошибкам прямого доступа к LIS (антибот/токен).
function lisErrorHint(e) {
  if (e.statusCode === 403) {
    return 'HTTP 403 — LIS отклонил запрос (антибот/Cloudflare). Самый надёжный путь: ' +
      'скачай прайс из залогиненного аккаунта в data/lis_prices.json (см. README).';
  }
  if (e.statusCode === 401) return 'HTTP 401 — неверный/просроченный LIS_API_TOKEN.';
  if (e.statusCode === 429) return 'HTTP 429 — LIS лимитирует запросы, попробуй позже.';
  return e.message;
}

// Ключ кэша зависит от конкретного источника — иначе после смены источника
// (файл → bulk и т.п.) сервер до 30 минут отдавал бы чужие данные из кэша.
function lisSourceTag() {
  if (CFG.lisPricesFile) return 'file:' + CFG.lisPricesFile;
  if (CFG.lisApiToken) return 'api:' + CFG.lisApiBase;
  return 'bulk:' + CFG.lisBulkUrl;
}
function csmoneySourceTag() {
  if (CFG.csmoneyPricesFile) return 'file:' + CFG.csmoneyPricesFile;
  if (CFG.csmoneyUrl) return 'url:' + CFG.csmoneyUrl;
  return 'none';
}

async function getLisPrices() {
  const ckey = 'prices:lis:' + lisSourceTag();
  const cached = cacheGet(ckey, CFG.pricesTtl);
  if (cached) return { map: new Map(cached.entries), source: cached.source };
  try {
    let res;
    if (CFG.lisPricesFile) {
      res = await loadPriceFileOrUrl(CFG.lisPricesFile, '');
    } else if (CFG.lisApiToken) {
      const url = CFG.lisApiBase.replace(/\/$/, '') + '/market/prices';
      res = await loadPriceFileOrUrl('', url, {
        Authorization: 'Bearer ' + CFG.lisApiToken, Referer: 'https://lis-skins.com/',
      });
    } else {
      res = await loadPriceFileOrUrl('', CFG.lisBulkUrl, { Referer: 'https://lis-skins.com/' });
    }
    flagEmpty(res, 'LIS');
    if (res.map.size) cacheSet(ckey, { entries: [...res.map], source: res.source });
    return res;
  } catch (e) {
    const hint = lisErrorHint(e);
    log('LIS prices failed:', hint);
    return { map: new Map(), source: 'error', error: hint };
  }
}

async function getCsMoneyPrices() {
  const ckey = 'prices:csmoney:' + csmoneySourceTag();
  const cached = cacheGet(ckey, CFG.pricesTtl);
  if (cached) return { map: new Map(cached.entries), source: cached.source };
  try {
    const res = await loadPriceFileOrUrl(CFG.csmoneyPricesFile, CFG.csmoneyUrl);
    flagEmpty(res, 'CS.money');
    if (res.map.size) cacheSet(ckey, { entries: [...res.map], source: res.source });
    return res;
  } catch (e) {
    log('CS.money prices failed:', e.message);
    return { map: new Map(), source: 'error', error: e.message };
  }
}

/* ============================================================================
 * СБОРКА ТАБЛИЦЫ РЫНКА (для выбранных площадок и режима)
 * Возвращает { rows:[{name,wear,mhn,lis?,csmoney?,steam?}], sources, mode }
 * ========================================================================== */
function demoTable() {
  return (DEMO.skins || []).map((s) => {
    const name = normName(s.name);
    const wear = s.wear || splitWear(name).wear;
    const base = splitWear(name).base;
    return {
      name: base, wear,
      mhn: wear && !/\(/.test(name) ? `${base} (${wear})` : name,
      lis: parseMoney(s.lis), csmoney: parseMoney(s.csmoney),
      steam: s.steam == null ? null : parseMoney(s.steam),
      why: s.why,
    };
  });
}

async function liveTable(exchange) {
  const wantLis = exchange !== 'csmoney';
  const wantCsm = exchange !== 'lis';
  const [lis, csm] = await Promise.all([
    wantLis ? getLisPrices() : Promise.resolve({ map: new Map(), source: 'skipped' }),
    wantCsm ? getCsMoneyPrices() : Promise.resolve({ map: new Map(), source: 'skipped' }),
  ]);
  const names = new Set([...lis.map.keys(), ...csm.map.keys()]);
  const rows = [];
  for (const mhn of names) {
    const { base, wear } = splitWear(mhn);
    rows.push({
      name: base, wear, mhn,
      lis: lis.map.get(mhn), csmoney: csm.map.get(mhn),
      steam: undefined, // подтянем из Steam точечно
    });
  }
  return { rows, sources: { lis: lis.source, csmoney: csm.source }, lisErr: lis.error, csmErr: csm.error };
}

/* ============================================================================
 * ДВИЖОК АРБИТРАЖА
 * ========================================================================== */
function chosenPayout(row, exchange) {
  const lis = Number.isFinite(row.lis) ? row.lis : null;
  const csm = Number.isFinite(row.csmoney) ? row.csmoney : null;
  if (exchange === 'lis') return lis == null ? null : { payout: lis, ex: 'lis' };
  if (exchange === 'csmoney') return csm == null ? null : { payout: csm, ex: 'csmoney' };
  // best: максимальная выплата
  if (lis == null && csm == null) return null;
  if (csm == null || (lis != null && lis >= csm)) return { payout: lis, ex: 'lis' };
  return { payout: csm, ex: 'csmoney' };
}

async function runSearch(params) {
  const amount = float(params.amount, 0);
  const currency = String(params.currency || 'RUB').toUpperCase();
  const corridorPct = Math.max(0.5, float(params.corridor, 5));
  const exchange = ['lis', 'csmoney', 'best'].includes(params.exchange) ? params.exchange : 'best';
  const net = params.net === true || params.net === '1' || params.net === 'true';
  let mode = ['auto', 'live', 'demo'].includes(params.mode) ? params.mode : CFG.defaultMode;

  const fx = await getFx();
  const rate = resolveRate(fx, currency);
  const targetUsd = amount > 0 ? amount / rate : 0;
  const corr = corridorPct / 100;
  const lo = targetUsd * (1 - corr);
  const hi = targetUsd * (1 + corr);

  const warnings = [];
  let table, sources, usedMode = mode;

  if (mode === 'demo') {
    table = demoTable(); sources = { lis: 'demo', csmoney: 'demo' };
  } else {
    const live = await liveTable(exchange);
    const usable = live.rows.some((r) => chosenPayout(r, exchange));
    if (!usable && mode === 'auto') {
      const why = live.lisErr ? 'LIS: ' + live.lisErr
        : live.csmErr ? 'CS.money: ' + live.csmErr
        : 'источники вернули пустой прайс-лист';
      warnings.push('Реальные цены недоступны — показываю демо-данные. Причина → ' + why);
      table = demoTable(); sources = { lis: 'demo', csmoney: 'demo' }; usedMode = 'demo';
    } else {
      table = live.rows; sources = live.sources; usedMode = 'live';
      if (live.lisErr) warnings.push('LIS: ' + live.lisErr);
      if (live.csmErr) warnings.push('CS.money: ' + live.csmErr);
    }
  }

  // Кандидаты в ценовом коридоре по выбранной выплате
  const candidates = [];
  for (const r of table) {
    const cp = chosenPayout(r, exchange);
    if (!cp) continue;
    if (targetUsd > 0 && (cp.payout < lo || cp.payout > hi)) continue;
    candidates.push(Object.assign({}, r, { payout: cp.payout, exchange: cp.ex }));
  }
  candidates.sort((a, b) => b.payout - a.payout);

  // Цены Steam по кандидатам (демо — из набора, live — точечные запросы с лимитом)
  const matched = [], unmatched = [];
  let freshLookups = 0, steamErrors = 0;
  for (const c of candidates) {
    let steam = c.steam, steamSource = 'demo', steamError = null;
    if (usedMode === 'live') {
      const cachedHit = cacheGet('steam:' + c.mhn, CFG.steamTtl);
      if (cachedHit !== undefined) { steam = cachedHit.price; steamSource = 'cache'; }
      else if (freshLookups < CFG.steamMaxLookups) {
        const sp = await getSteamPrice(c.mhn);
        steam = sp.price; steamSource = sp.source; steamError = sp.error; freshLookups++;
        if (sp.source === 'error') steamErrors++;
      } else {
        unmatched.push({ name: c.name, wear: c.wear, mhn: c.mhn, exchange: c.exchange,
          payout: c.payout, why: 'лимит Steam — повтори поиск, дозапросим' });
        continue;
      }
    }
    if (steam == null) {
      // Различаем «Steam не вернул цену» (несовпадение имени) и «запрос упал»
      // (403/429/таймаут) — иначе пользователь чинит не ту проблему.
      const why = steamSource === 'error'
        ? 'ошибка Steam: ' + (steamError || 'запрос не прошёл')
        : (c.why || 'нет цены в Steam (имя ≠ market_hash_name: ★, StatTrak™)');
      unmatched.push({ name: c.name, wear: c.wear, mhn: c.mhn, exchange: c.exchange,
        payout: c.payout, why });
      continue;
    }
    let spread = c.payout - steam;
    if (net) spread -= steam * CFG.steamFee;
    const pct = steam > 0 ? (spread / steam) * 100 : 0;
    matched.push({
      name: c.name, wear: c.wear, mhn: c.mhn,
      exchange: c.exchange, lis: numOrNull(c.lis), csmoney: numOrNull(c.csmoney),
      payout: round2(c.payout), steam: round2(steam), spread: round2(spread),
      pct: Math.round(pct * 10) / 10, steamSource,
      links: { steam: LINKS.steam(c.mhn), exchange: LINKS[c.exchange](c.name) },
    });
  }
  matched.sort((a, b) => b.spread - a.spread);
  const best = matched.length ? matched.reduce((m, r) => (r.spread > m.spread ? r : m), matched[0]) : null;

  // Если Steam сыпал ошибками (особенно когда ни одного скина не сматчилось) —
  // выносим это в общий warning, чтобы причина пустого результата была очевидна.
  if (steamErrors > 0) {
    warnings.push(`Steam не ответил по ${steamErrors} скин(ам) (403/429/таймаут) — ` +
      'часть цен не получена, повтори поиск позже (кэш дозаполнится).');
  }

  return {
    ok: true, version: VERSION,
    mode: usedMode, exchange, net, currency,
    fx: { rate: round4(rate), source: fx.source, currency },
    query: { amount, targetUsd: round2(targetUsd), corridorPct,
      corridor: { lo: round2(lo), hi: round2(hi) } },
    meta: { candidates: candidates.length, matched: matched.length,
      unmatched: unmatched.length, steamLookups: freshLookups, sources },
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
  '/': { file: 'spread-arbitrage.html', type: 'text/html; charset=utf-8' },
  '/spread-arbitrage.html': { file: 'spread-arbitrage.html', type: 'text/html; charset=utf-8' },
  '/data/demo_prices.json': { file: 'data/demo_prices.json', type: 'application/json; charset=utf-8' },
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
      exchanges: {
        lis: { configured: !!(CFG.lisPricesFile || CFG.lisApiToken || CFG.lisBulkUrl),
          source: CFG.lisPricesFile ? 'file' : CFG.lisApiToken ? 'api' : 'bulk',
          file: CFG.lisPricesFile || null },
        csmoney: { configured: !!(CFG.csmoneyPricesFile || CFG.csmoneyUrl),
          source: CFG.csmoneyPricesFile ? 'file' : CFG.csmoneyUrl ? 'url' : 'demo-only',
          file: CFG.csmoneyPricesFile || null },
      },
      steam: { delayMs: CFG.steamDelayMs, maxLookups: CFG.steamMaxLookups },
      demoSkins: (DEMO.skins || []).length,
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
    const ex = q.get('exchange') === 'csmoney' ? 'csmoney' : 'lis';
    const r = ex === 'csmoney' ? await getCsMoneyPrices() : await getLisPrices();
    const entries = [...r.map].slice(0, int(q.get('limit'), 50));
    return sendJson(res, 200, { ok: true, exchange: ex, source: r.source,
      count: r.map.size, sample: entries.map(([name, price]) => ({ name, price })), error: r.error });
  }
  if (pathname === '/api/search') {
    const result = await runSearch({
      amount: q.get('amount'), currency: q.get('currency'), corridor: q.get('corridor'),
      exchange: q.get('exchange'), net: q.get('net'), mode: q.get('mode'),
    });
    return sendJson(res, 200, result);
  }
  return sendJson(res, 404, { ok: false, error: 'unknown endpoint' });
}

function serveStatic(pathname, res) {
  const entry = STATIC[pathname];
  if (!entry) { res.writeHead(404, { 'Content-Type': 'text/plain' }); return res.end('404'); }
  fs.readFile(path.join(ROOT, entry.file), (err, buf) => {
    if (err) { res.writeHead(404, { 'Content-Type': 'text/plain' }); return res.end('not found'); }
    res.writeHead(200, { 'Content-Type': entry.type, 'Access-Control-Allow-Origin': '*' });
    res.end(buf);
  });
}

function startServer(port) {
  const server = http.createServer(async (req, res) => {
    let u;
    try { u = new URL(req.url, 'http://localhost'); } catch (_) {
      res.writeHead(400); return res.end('bad request');
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
      try { await handleApi(pathname, u.searchParams, res); }
      catch (e) { log('API error:', e.stack || e.message); sendJson(res, 500, { ok: false, error: e.message }); }
      return;
    }
    serveStatic(pathname, res);
  });
  server.listen(port, () => {
    const rel = (p) => path.relative(ROOT, p) || p;
    const lisSrc = CFG.lisPricesFile ? 'файл ' + rel(CFG.lisPricesFile)
      : CFG.lisApiToken ? 'API-токен' : 'bulk-URL (публичный)';
    const csmSrc = CFG.csmoneyPricesFile ? 'файл ' + rel(CFG.csmoneyPricesFile)
      : CFG.csmoneyUrl ? 'URL' : 'не настроен → демо';
    console.log(`\n  СПРЕД v${VERSION} — сервер запущен`);
    console.log(`  → http://localhost:${port}`);
    console.log(`  Режим по умолчанию: ${CFG.defaultMode}`);
    console.log(`  LIS: ${lisSrc} · CS.money: ${csmSrc}`);
    if (!CFG.lisPricesFile && !CFG.lisApiToken) {
      console.log('  ⓘ LIS на публичном bulk-URL — возможен HTTP 403 (антибот Cloudflare).');
      console.log('    Надёжнее: положи прайс в data/lis_prices.json (см. README) или задай LIS_API_TOKEN.');
    }
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
    exchange: args.exchange || 'best', net: !!args.net, mode: args.mode || CFG.defaultMode,
  });
  const dp = ['RUB', 'KZT', 'UAH'].includes(currency) ? 0 : 2;
  const toCur = (usd) => fmt(usd * result.fx.rate, dp);

  console.log('');
  console.log(`  Режим: ${result.mode} · площадка: ${result.exchange} · валюта: ${currency}` +
    (result.net ? ' · чистыми (−Steam 15%)' : ''));
  console.log(`  Курс USD→${currency}: ${result.fx.rate} (${result.fx.source})`);
  console.log(`  Цель: ${fmt(amount, dp)} ${currency} (~$${result.query.targetUsd}) · ` +
    `коридор ${toCur(result.query.corridor.lo)}–${toCur(result.query.corridor.hi)} ${currency} · ` +
    `кандидатов: ${result.meta.candidates}`);
  for (const w of result.warnings) console.log('  ⚠ ' + w);
  console.log('');

  if (!result.rows.length) {
    console.log('  Нет кандидатов в этом коридоре — расширь диапазон (--corridor 10).');
  } else {
    const pad = (s, n) => String(s).slice(0, n).padEnd(n);
    const padL = (s, n) => String(s).padStart(n);
    console.log('  ' + pad('#', 3) + pad('Скин', 40) + pad('Площ.', 9) +
      padL('платит', 11) + padL('Steam', 11) + padL('спред', 11) + padL('%', 8));
    console.log('  ' + '-'.repeat(93));
    result.rows.forEach((r, i) => {
      const star = result.best && r.mhn === result.best.mhn ? '★' : (i + 1);
      console.log('  ' + pad(star, 3) + pad(`${r.name} (${r.wear})`, 40) + pad(r.exchange, 9) +
        padL(toCur(r.payout), 11) + padL(toCur(r.steam), 11) +
        padL('+' + toCur(r.spread), 11) + padL('+' + r.pct.toFixed(1) + '%', 8));
    });
  }

  if (result.best) {
    console.log('');
    console.log(`  ★ Лучшая сделка: ${result.best.name} (${result.best.wear}) · ${result.best.exchange}`);
    console.log(`    Steam ${toCur(result.best.steam)} → платит ${toCur(result.best.payout)} ${currency}` +
      ` · спред +${toCur(result.best.spread)} ${currency} (+${result.best.pct.toFixed(1)}%)`);
    console.log(`    ${result.best.links.steam}`);
  }
  if (result.unmatched.length) {
    console.log('');
    console.log(`  Не вошли в рейтинг (${result.unmatched.length}): нет цены Steam —`);
    result.unmatched.slice(0, 12).forEach((u) =>
      console.log(`    · ${u.name}${u.wear ? ' (' + u.wear + ')' : ''} — ${u.why}`));
  }
  console.log('');
  console.log('  Спред ≠ чистый профит: вычти комиссию Steam ~15%, курс и удержания LIS/CS.money.');
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

async function cliDiag(args) {
  const ex = args.exchange === 'csmoney' ? 'csmoney' : 'lis';
  console.log(`Источник: ${ex}`);
  const r = ex === 'csmoney' ? await getCsMoneyPrices() : await getLisPrices();
  console.log(`  source=${r.source} · позиций=${r.map.size}${r.error ? ' · ошибка: ' + r.error : ''}`);
  [...r.map].slice(0, 10).forEach(([name, price]) => console.log(`    ${name} → $${price}`));
  if (!r.map.size) console.log('    (пусто — настрой LIS_PRICES_FILE / CSMONEY_URL, см. README)');
}

/* ============================================================================
 * ENTRY
 * ========================================================================== */
async function main() {
  const argv = process.argv.slice(2);
  const cmd = argv[0];
  const args = parseArgs(argv.slice(1));

  if (cmd === 'search') return cliSearch(args);
  if (cmd === 'fx') return cliFx();
  if (cmd === 'steam') return cliSteam(args);
  if (cmd === 'diag') return cliDiag(args);
  if (cmd === 'help' || cmd === '--help' || cmd === '-h') {
    console.log(fs.readFileSync(__filename, 'utf8').split('\n').slice(2, 24).join('\n').replace(/^ \* ?/gm, ''));
    return;
  }
  // serve (по умолчанию)
  const port = int((cmd === 'serve' ? args.port : process.env.PORT) || CFG.port, CFG.port);
  startServer(port);
}

main().catch((e) => { console.error(e); process.exit(1); });
