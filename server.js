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
 * Быстрый поиск: при наличии LIS_API_TOKEN прайс НЕ выгружается целиком.
 * Вместо медленной выгрузки bulk (~640 МБ) используется точечный запрос
 * market/search с фильтром по цене (price_from/price_to) — отдаёт только
 * скины из нужного ценового коридора. Без токена остаётся старый путь
 * (локальный файл / bulk-стриминг) как запасной.
 *
 * Валюты без внешнего FX: Steam отдаёт цену сразу в валюте пользователя
 * (priceoverview&currency=<код>), т.к. цены в регионах Steam независимы.
 * LIS работает в USD — его цена переводится в валюту по курсу, который
 * берётся из самого Steam (эталонный скин в USD и в валюте), с кэшем.
 *
 * Запуск:
 *   node server.js                 — поднять веб-сервер (по умолчанию :8787)
 *   node server.js serve --port N — то же, на порту N
 *   node server.js search 8000 [--currency RUB] [--corridor 5] [--net]
 *                                  [--mode auto|live|demo]   — поиск в консоли
 *   node server.js fx             — показать курсы (Steam-derived)
 *   node server.js steam "<name>" [--currency RUB] — цена скина в Steam
 *   node server.js diag           — состояние источника LIS
 *
 * Спред считается в валюте пользователя: Steam — нативно, LIS — USD×курс.
 * ========================================================================== */

'use strict';

const http  = require('http');
const https = require('https');
const zlib  = require('zlib');
const fs    = require('fs');
const path  = require('path');
const crypto= require('crypto');
const { URL } = require('url');

const VERSION = '2.2.0';
const ROOT    = __dirname;

/* ============================================================================
 * КОНФИГ (всё переопределяется переменными окружения)
 * ========================================================================== */
const CFG = {
  port: int(process.env.PORT, 8787),
  cacheDir: process.env.CACHE_DIR || path.join(ROOT, '.cache'),

  // Курс USD→валюта берётся из самого Steam (эталонный скин), без внешнего FX.
  // FX_REF_ITEM — ликвидный скин, по которому считается курс. FX_TTL — кэш курса.
  fxRefItem: process.env.FX_REF_ITEM || 'AK-47 | Redline (Field-Tested)',
  fxTtl: int(process.env.FX_TTL, 6 * 3600) * 1000,

  // LIS-Skins. Приоритет live-источника: API-токен (market/search, быстро) →
  // локальный файл → bulk-JSON по ссылке (медленно, запасной путь).
  lisPricesFile: process.env.LIS_PRICES_FILE || '',
  lisApiBase:    process.env.LIS_API_BASE || 'https://api.lis-skins.com/v1',
  lisApiToken:   process.env.LIS_API_TOKEN || '',
  lisBulkUrl:    process.env.LIS_BULK_URL || 'https://lis-skins.com/market_export_json/api_csgo_full.json',
  lisGame:       process.env.LIS_GAME || 'csgo',
  // Сколько страниц market/search листать и сколько уникальных скинов набирать.
  lisSearchPages: int(process.env.LIS_SEARCH_PAGES, 6),
  lisSearchMax:   int(process.env.LIS_SEARCH_MAX, 120),

  pricesTtl: int(process.env.PRICES_TTL, 30 * 60) * 1000,  // 30 мин

  // Steam priceoverview: appid 730 (CS2). currency задаётся по валюте поиска.
  steamTtl:         int(process.env.STEAM_TTL, 6 * 3600) * 1000,
  steamDelayMs:     int(process.env.STEAM_DELAY_MS, 3500),     // ~17 запросов/мин
  steamMaxLookups:  int(process.env.STEAM_MAX_LOOKUPS, 40),   // потолок «свежих» запросов
  steamRetries:     int(process.env.STEAM_RETRIES, 3),
  // Если lowest_price < median × этого порога — считаем lowest выбросом и
  // берём медиану (защита от фейкового спреда из-за протухшего дешёвого лота).
  steamOutlierRatio: float(process.env.STEAM_OUTLIER_RATIO, 0.5),

  // Комиссия Steam при продаже (для режима «чистыми»).
  steamFee: float(process.env.STEAM_FEE, 0.15),

  // demo | live | auto
  defaultMode: (process.env.MODE || 'auto').toLowerCase(),

  httpTimeout: int(process.env.HTTP_TIMEOUT, 15000),
  userAgent: process.env.USER_AGENT ||
    'Mozilla/5.0 (compatible; SpreadArbBot/2.1; +https://localhost)',
  quiet: process.env.QUIET === '1',
};

// Шаблоны ссылок
const LINKS = {
  steam: (mhn) => `https://steamcommunity.com/market/listings/730/${encodeURIComponent(mhn)}`,
  lis:   (base) => `https://lis-skins.com/market/csgo/?query=${encodeURIComponent(base)}`,
};

const WEARS = ['Factory New', 'Minimal Wear', 'Field-Tested', 'Well-Worn', 'Battle-Scarred'];

// Числовые коды валют Steam (priceoverview&currency=<код>). Цены в регионах
// Steam независимы, поэтому запрашиваем нативно, а не пересчитываем через FX.
const STEAM_CURRENCY = { USD: 1, EUR: 3, RUB: 5, UAH: 18, KZT: 37 };
function steamCurrencyCode(currency) {
  return STEAM_CURRENCY[String(currency || 'USD').toUpperCase()] || 1;
}

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
        // Для очень больших ответов — ограничиваем размер буфера
        let totalSize = 0;
        const MAX_RESPONSE_SIZE = 100 * 1024 * 1024; // 100 MB для обычных запросов
        res.on('data', (c) => {
          totalSize += c.length;
          if (totalSize > MAX_RESPONSE_SIZE) {
            res.destroy(new Error(`Response too large: ${totalSize} bytes (max ${MAX_RESPONSE_SIZE})`));
            return;
          }
          chunks.push(c);
        });
        res.on('end', () => {
          let buf = Buffer.concat(chunks);
          const enc = (res.headers['content-encoding'] || '').toLowerCase();
          try {
            if (enc === 'gzip') buf = zlib.gunzipSync(buf);
            else if (enc === 'deflate') buf = zlib.inflateSync(buf);
            else if (enc === 'br') buf = zlib.brotliDecompressSync(buf);
          } catch (_) { /* отдадим как есть */ }
          try {
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
          } catch (e) {
            reject(new Error('Cannot convert response to string: ' + e.message));
          }
        });
        res.on('error', (e) => reject(e));
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
 * СТРИМИНГ JSON-ПАРСЕР ДЛЯ BULK-ДАННЫХ LIS
 *
 * Вместо загрузки всего 640+ МБ в одну строку (превышает лимит V8 ~536 МБ),
 * читаем ответ чанками и извлекаем объекты JSON-массива по одному.
 * ========================================================================== */

/**
 * Скачать большой JSON-массив по URL и обработать каждый элемент через callback.
 * Не создаёт единую строку из всего ответа — парсит incremental.
 * @param {string} urlStr
 * @param {object} opts - { timeout, headers, retries }
 * @param {function} onItem - вызывается для каждого объекта: onItem(obj) => void
 * @returns {Promise<{totalItems: number, bytesReceived: number, elapsed: number}>}
 */
function streamJsonArray(urlStr, opts, onItem) {
  const { headers = {}, timeout = 120000, retries = 1 } = opts;
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
        if (code < 200 || code >= 300) {
          let body = '';
          res.on('data', (c) => { body += c.toString('utf8'); });
          res.on('end', () => {
            const err = new Error('HTTP ' + code);
            err.statusCode = code; err.body = body;
            reject(err);
          });
          return;
        }

        // Определяем кодировку и при необходимости распаковываем
        const enc = (res.headers['content-encoding'] || '').toLowerCase();
        let stream = res;
        if (enc === 'gzip') stream = res.pipe(zlib.createGunzip());
        else if (enc === 'deflate') stream = res.pipe(zlib.createInflate());
        else if (enc === 'br') stream = res.pipe(zlib.createBrotliDecompress());

        const t0 = Date.now();
        let totalItems = 0;
        let bytesReceived = 0;

        // Состояние парсера: находим полные JSON-объекты внутри массива
        // Мы ожидаем формат: [{"key":"val",...},{"key":"val",...},...]
        const parser = new StreamingJsonArrayParser((item) => {
          totalItems++;
          onItem(item);
        });

        stream.on('data', (chunk) => {
          bytesReceived += chunk.length;
          // Конвертируем чанк в строку (чанки маленькие, ~64KB — проблем нет)
          const text = chunk.toString('utf8');
          parser.feed(text);
        });

        stream.on('end', () => {
          parser.flush(); // обработать остатки
          const elapsed = ((Date.now() - t0) / 1000).toFixed(1);
          resolve({ totalItems, bytesReceived, elapsed: parseFloat(elapsed) });
        });

        stream.on('error', (e) => {
          reject(new Error('Stream error: ' + e.message));
        });

        req.setTimeout(timeout, () => {
          stream.destroy();
          req.destroy(new Error('timeout'));
        });
      });
      req.on('error', (e) => {
        if (attempt++ < retries) return setTimeout(go, 1000 * attempt);
        reject(e);
      });
      req.end();
    };
    go();
  });
}

/**
 * Простой стриминг-парсер JSON-массива.
 * Поддерживает извлечение объектов из массива: [{...}, {...}, ...]
 * Также поддерживает обёртки: {"items":[...], ...} и {"data":[...], ...}
 */
class StreamingJsonArrayParser {
  constructor(onItem) {
    this.onItem = onItem;
    this.buffer = '';
    this.depth = 0;
    this.inArray = false;
    this.inObject = false;
    this.objectStart = -1;
    this.foundArray = false;
    this.wrapperParsed = false;
    this.wrapperDepth = -1;
    this.arrayDepth = -1;
  }

  feed(text) {
    this.buffer += text;
    this._parse();
  }

  flush() {
    if (this.buffer.trim()) {
      this._parse();
    }
  }

  _parse() {
    while (this.buffer.length > 0) {
      // Пропускаем пробелы перед началом
      const trimmed = this.buffer.trimStart();
      if (!trimmed) break;
      this.buffer = trimmed;

      // Ищем начало массива (если ещё не нашли)
      if (!this.foundArray) {
        const idx = this.buffer.indexOf('[');
        if (idx === -1) {
          // Проверяем, есть ли обёртка-объект
          if (this.buffer[0] === '{') {
            // Парсим начало обёртки — ищем имя ключа и [
            const colonIdx = this.buffer.indexOf(':');
            if (colonIdx === -1) break;
            const key = this.buffer.slice(1, colonIdx).trim().replace(/"/g, '');
            // Ищем [ после :
            const arrIdx = this.buffer.indexOf('[', colonIdx);
            if (arrIdx === -1) break;
            this.buffer = this.buffer.slice(arrIdx + 1);
            this.foundArray = true;
            this.inArray = true;
            continue;
          }
          break; // Ждём больше данных
        }
        this.buffer = this.buffer.slice(idx + 1);
        this.foundArray = true;
        this.inArray = true;
        continue;
      }

      if (!this.inArray) break;

      // Пропускаем пробелы и запятые между элементами
      if (this.buffer[0] === ' ' || this.buffer[0] === '\n' || this.buffer[0] === '\r' ||
          this.buffer[0] === '\t' || this.buffer[0] === ',') {
        this.buffer = this.buffer.slice(1);
        continue;
      }

      // Конец массива
      if (this.buffer[0] === ']') {
        this.inArray = false;
        this.buffer = '';
        break;
      }

      // Начало объекта — извлекаем его целиком
      if (this.buffer[0] === '{') {
        const obj = this._extractObject();
        if (obj === null) break; // Нужно больше данных
        try {
          const parsed = JSON.parse(obj);
          this.onItem(parsed);
        } catch (e) {
          // Пропускаем невалидные объекты
        }
        continue;
      }

      // Пропускаем другие токены (числа, строки вне объектов)
      if (this.buffer[0] === '"' || this.buffer[0] === '-' || (this.buffer[0] >= '0' && this.buffer[0] <= '9') || this.buffer[0] === 'n' || this.buffer[0] === 't' || this.buffer[0] === 'f') {
        const end = this._skipValue();
        if (end === -1) break;
        this.buffer = this.buffer.slice(end);
        continue;
      }

      // Неизвестный символ — пропускаем
      this.buffer = this.buffer.slice(1);
    }
  }

  /**
   * Извлечь один JSON-объект из буфера, отслеживая вложенность скобок и строк.
   * @returns {string|null} JSON-строка объекта или null если данных недостаточно
   */
  _extractObject() {
    let depth = 0;
    let i = 0;
    let inString = false;
    let escape = false;

    for (; i < this.buffer.length; i++) {
      const ch = this.buffer[i];

      if (escape) {
        escape = false;
        continue;
      }

      if (ch === '\\' && inString) {
        escape = true;
        continue;
      }

      if (ch === '"' && !escape) {
        inString = !inString;
        continue;
      }

      if (inString) continue;

      if (ch === '{') depth++;
      if (ch === '}') {
        depth--;
        if (depth === 0) {
          const obj = this.buffer.slice(0, i + 1);
          this.buffer = this.buffer.slice(i + 1);
          return obj;
        }
      }
    }

    // Недостаточно данных
    return null;
  }

  /**
   * Пропустить одно JSON-значение (строка, число, null, true, false).
   * @returns {number} количество символов пропущенных, или -1 если данных мало
   */
  _skipValue() {
    const ch = this.buffer[0];
    if (ch === '"') {
      let i = 1;
      while (i < this.buffer.length) {
        if (this.buffer[i] === '\\') { i += 2; continue; }
        if (this.buffer[i] === '"') return i + 1;
        i++;
      }
      return -1;
    }
    if (ch === 'n') return this.buffer.startsWith('null') ? 4 : -1;
    if (ch === 't') return this.buffer.startsWith('true') ? 4 : -1;
    if (ch === 'f') return this.buffer.startsWith('false') ? 5 : -1;
    // Число
    let i = 0;
    if (this.buffer[i] === '-') i++;
    while (i < this.buffer.length && ((this.buffer[i] >= '0' && this.buffer[i] <= '9') || this.buffer[i] === '.' || this.buffer[i] === 'e' || this.buffer[i] === 'E' || this.buffer[i] === '+' || this.buffer[i] === '-')) i++;
    return i > 0 ? i : -1;
  }
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
 * КУРС USD→ВАЛЮТА БЕЗ ВНЕШНЕГО FX
 *
 * LIS работает в USD, Steam — нативно в валюте региона. Чтобы перевести цену
 * LIS в валюту показа, берём курс из самого Steam: эталонный ликвидный скин
 * (FX_REF_ITEM) запрашивается в USD и в нужной валюте, отношение цен = курс.
 * Кэш на FX_TTL. Если Steam недоступен — фолбэк на встроенные константы.
 * Для USD курс = 1 (никаких запросов).
 * ========================================================================== */
async function getCurrencyRate(currency) {
  const cur = String(currency || 'USD').toUpperCase();
  if (cur === 'USD') return { rate: 1, source: 'usd' };
  const code = STEAM_CURRENCY[cur];
  if (!code) return { rate: FALLBACK_FX[cur] || 1, source: 'fallback' };

  const key = 'rate:' + cur;
  const cached = cacheGet(key, CFG.fxTtl);
  if (cached) return cached;

  try {
    const usd = await getSteamPrice(CFG.fxRefItem, 1);
    const loc = await getSteamPrice(CFG.fxRefItem, code);
    if (usd.price > 0 && loc.price > 0) {
      const out = { rate: loc.price / usd.price, source: 'steam' };
      cacheSet(key, out);
      return out;
    }
  } catch (e) { warn('steam rate failed:', e.message); }

  return { rate: FALLBACK_FX[cur] || 1, source: 'fallback' };
}

// Курс только из кэша/констант — без обращений к Steam (для /api/fx и подсказок).
function cachedRate(currency) {
  const cur = String(currency || 'USD').toUpperCase();
  if (cur === 'USD') return { rate: 1, source: 'usd' };
  const cached = cacheGet('rate:' + cur, CFG.fxTtl);
  if (cached) return cached;
  return { rate: FALLBACK_FX[cur] || 1, source: 'fallback' };
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

// Ключ кэша Steam учитывает валюту: цены в регионах независимы.
function steamKey(mhn, code) { return 'steam:' + code + ':' + mhn; }

// Выбор цены Steam. lowest_price (самый дешёвый лот) иногда аномально низкий —
// одиночный протухший/неадекватный лот или скин другого качества под тем же
// market_hash_name. Если lowest сильно ниже медианы продаж — берём медиану как
// реалистичную цену, чтобы не показывать фейковый спред в тысячи процентов.
function pickSteamPrice(low, med) {
  if (low == null) return med != null ? med : null;
  if (med == null) return low;
  return low < med * CFG.steamOutlierRatio ? med : low;
}

async function getSteamPrice(mhn, code = 1) {
  const key = steamKey(mhn, code);
  const cached = cacheGet(key, CFG.steamTtl);
  if (cached !== undefined) return Object.assign({ source: 'cache' }, cached);

  let delay = CFG.steamDelayMs;
  for (let attempt = 0; attempt <= CFG.steamRetries; attempt++) {
    try {
      const out = await enqueueSteam(async () => {
        const url = 'https://steamcommunity.com/market/priceoverview/?appid=730&currency=' + code
          + '&market_hash_name=' + encodeURIComponent(mhn);
        const data = await httpGetJson(url, { retries: 0, timeout: CFG.httpTimeout });
        if (!data || data.success !== true) return { price: null };
        const low = parseMoney(data.lowest_price);
        const med = parseMoney(data.median_price);
        return { price: pickSteamPrice(low, med), low, med };
      });
      const result = { price: out.price, low: out.low, med: out.med, source: 'steam' };
      cacheSet(key, { price: out.price, low: out.low, med: out.med });
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
function keepMin(map, name, price) {
  const prev = map.get(name);
  if (prev == null || price < prev) map.set(name, price);
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
    // Для обычных JSON-ответов (не bulk) используем стандартный httpGet
    const raw = await httpGetJson(url, { headers, retries: 2, timeout: 30000 });
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
 *
 * Для bulk-URL (~640 МБ) используется стриминг-парсер — JSON парсится
 * по одному объекту без создания полной строки ответа в памяти.
 * ========================================================================== */
let lisState = { map: new Map(), source: 'none', loading: false, lastRefresh: 0, error: null };

/**
 * Загрузить bulk-прайс через стриминг. Извлекает объекты из массива по одному,
 * избегая ограничения V8 на длину строки (~536 МБ).
 */
async function loadBulkStreaming(url, headers) {
  const map = new Map();
  info(`LIS: стриминг-загрузка bulk с ${hostOf(url)} …`);

  const result = await streamJsonArray(url, { headers, timeout: 180000 }, (item) => {
    if (!item || typeof item !== 'object') return;
    const name = normName(pickField(item, NAME_FIELDS));
    const price = parseMoney(pickField(item, PRICE_FIELDS));
    if (name && price != null && price > 0) keepMin(map, name, price);
  });

  const mb = (result.bytesReceived / (1024 * 1024)).toFixed(1);
  info(`LIS: bulk загружен — ${result.bytesReceived.toLocaleString()} байт (${mb} МБ), ` +
    `${result.totalItems.toLocaleString()} записей обработано за ${result.elapsed}с, ` +
    `${map.size.toLocaleString()} уникальных скинов`);
  return { map, source: hostOf(url) };
}

async function refreshLisPrices() {
  if (lisState.loading) return lisState;
  lisState.loading = true;
  try {
    // Приоритет: локальный файл → API по токену → bulk-URL (стриминг)
    let res;
    if (CFG.lisPricesFile) {
      res = await loadPriceFileOrUrl(CFG.lisPricesFile, '');
    } else if (CFG.lisApiToken) {
      const url = CFG.lisApiBase.replace(/\/$/, '') + '/market/prices';
      res = await loadPriceFileOrUrl('', url, { Authorization: 'Bearer ' + CFG.lisApiToken });
    } else {
      // Bulk URL — используем стриминг-парсер (без ограничения на размер строки)
      res = await loadBulkStreaming(CFG.lisBulkUrl);
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
 * LIS market/search — быстрый точечный поиск по ценовому коридору (нужен токен)
 *
 * Главная оптимизация скорости: вместо выгрузки всего прайса (~640 МБ) берём
 * только скины из диапазона [priceFrom, priceTo] (USD). Листаем по cursor'у
 * (meta.next_cursor) и агрегируем до Map<market_hash_name, usd> — минимальная
 * цена за скин. Адаптация метода market/search публичного API LIS-Skins.
 * ========================================================================== */
async function lisSearch(priceFrom, priceTo) {
  if (!CFG.lisApiToken) throw new Error('LIS_API_TOKEN не задан');
  const base = CFG.lisApiBase.replace(/\/$/, '');
  const headers = { Authorization: 'Bearer ' + CFG.lisApiToken, Accept: 'application/json' };
  const map = new Map();
  let cursor = null, pages = 0, listings = 0;
  const t0 = Date.now();

  while (pages < CFG.lisSearchPages && map.size < CFG.lisSearchMax) {
    const p = new URLSearchParams();
    p.set('game', CFG.lisGame);
    if (priceFrom != null && priceFrom > 0) p.set('price_from', String(round2(priceFrom)));
    if (priceTo   != null && priceTo   > 0) p.set('price_to',   String(round2(priceTo)));
    p.set('sort_by', 'lowest_price');
    if (cursor) p.set('cursor', cursor);

    const data = await httpGetJson(base + '/market/search?' + p.toString(),
      { headers, retries: 1, timeout: CFG.httpTimeout });

    const list = Array.isArray(data && data.data)  ? data.data
               : Array.isArray(data && data.items) ? data.items
               : Array.isArray(data)               ? data : [];
    if (!list.length) break;
    for (const it of list) {
      if (!it || typeof it !== 'object') continue;
      listings++;
      const name  = normName(pickField(it, NAME_FIELDS));
      const price = parseMoney(pickField(it, PRICE_FIELDS));
      if (name && price != null && price > 0) keepMin(map, name, price);
    }
    cursor = (data && data.meta && data.meta.next_cursor) || null;
    pages++;
    if (!cursor) break;
  }
  const elapsed = ((Date.now() - t0) / 1000).toFixed(1);
  info(`LIS: market/search — ${map.size} скинов из ${listings} листингов за ${elapsed}с (${pages} стр.)`);
  return { map, source: 'api:market/search' };
}

// Отфильтровать предзагруженный прайс (файл/bulk) по ценовому коридору USD.
function filterMapByCorridor(map, loUsd, hiUsd) {
  const out = new Map();
  for (const [name, price] of map) {
    if (price == null || price <= 0) continue;
    if (loUsd > 0 && (price < loUsd || price > hiUsd)) continue;
    out.set(name, price);
  }
  return out;
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

// Map<mhn, usd> → список кандидатов с разбором износа.
function mapToCandidates(map) {
  const out = [];
  for (const [mhn, usd] of map) {
    const { base, wear } = splitWear(mhn);
    out.push({ name: base, wear, mhn, lisUsd: usd });
  }
  return out;
}

// Демо-кандидаты в коридоре USD (у демо уже есть и LIS, и Steam — без запросов).
function demoCandidates(loUsd, hiUsd, targetUsd) {
  return demoTable()
    .filter((r) => r.lis != null && r.lis > 0 &&
      (targetUsd <= 0 || (r.lis >= loUsd && r.lis <= hiUsd)))
    .map((r) => ({
      name: r.name, wear: r.wear, mhn: r.mhn,
      lisUsd: r.lis, steamUsd: r.steam == null ? null : r.steam, why: r.why,
    }));
}

/* ============================================================================
 * ДВИЖОК АРБИТРАЖА
 *
 * Спред считается в валюте пользователя. LIS отдаёт USD → переводим по курсу
 * (Steam-derived). Steam запрашиваем нативно в той же валюте (currency=<код>).
 * ========================================================================== */
async function runSearch(params) {
  const amount      = float(params.amount, 0);
  const currency    = String(params.currency || 'RUB').toUpperCase();
  const corridorPct = Math.max(0.5, float(params.corridor, 5));
  const net         = params.net === true || params.net === '1' || params.net === 'true';
  let mode          = ['auto', 'live', 'demo'].includes(params.mode) ? params.mode : CFG.defaultMode;

  const code = steamCurrencyCode(currency);

  // Курс USD→валюта из Steam (для перевода цены LIS в валюту показа).
  const fx   = await getCurrencyRate(currency);
  const rate = fx.rate;

  const targetUsd = amount > 0 ? amount / rate : 0;
  const corr  = corridorPct / 100;
  const loUsd = targetUsd * (1 - corr);
  const hiUsd = targetUsd * (1 + corr);

  const warnings = [];
  let candidates = [];          // { name, wear, mhn, lisUsd, steamUsd?, why? }
  let source, usedMode = mode;

  if (mode === 'demo') {
    candidates = demoCandidates(loUsd, hiUsd, targetUsd);
    source = 'demo';
  } else if (CFG.lisApiToken) {
    // Быстрый путь: точечный market/search по ценовому коридору.
    try {
      if (targetUsd <= 0) {
        warnings.push('Укажи сумму — market/search ищет по ценовому коридору.');
      } else {
        const res = await lisSearch(loUsd, hiUsd);
        candidates = mapToCandidates(res.map);
      }
      source = 'api:market/search';
      usedMode = 'live';
    } catch (e) {
      warn('LIS search failed:', e.message);
      if (mode === 'auto') {
        warnings.push('LIS недоступен (' + e.message + ') — демо-данные.');
        candidates = demoCandidates(loUsd, hiUsd, targetUsd);
        source = 'demo'; usedMode = 'demo';
      } else {
        warnings.push('LIS: ' + e.message);
        source = 'error'; usedMode = 'live';
      }
    }
  } else {
    // Запасной путь без токена: предзагруженный прайс (файл/bulk) + фильтр.
    const usable = lisState.map.size > 0;
    if (!usable && mode === 'auto') {
      warnings.push('Прайс-лист LIS недоступен/пуст — показываю демо-данные. См. README, как подключить источник.');
      candidates = demoCandidates(loUsd, hiUsd, targetUsd);
      source = 'demo'; usedMode = 'demo';
    } else {
      candidates = mapToCandidates(filterMapByCorridor(lisState.map, loUsd, hiUsd));
      source = lisState.source; usedMode = 'live';
      if (lisState.error) warnings.push('LIS: ' + lisState.error);
    }
  }

  // Сортируем по выплате LIS (USD) убыв.
  candidates.sort((a, b) => b.lisUsd - a.lisUsd);

  const matched = [], unmatched = [];
  let freshLookups = 0;
  for (const c of candidates) {
    const payoutCur = c.lisUsd * rate;       // LIS USD → валюта показа

    // Steam — нативно в валюте пользователя (или из демо, переведённого по курсу).
    let steamCur, steamSource;
    if (usedMode === 'demo') {
      steamCur = c.steamUsd == null ? null : c.steamUsd * rate;
      steamSource = 'demo';
    } else {
      const cachedHit = cacheGet(steamKey(c.mhn, code), CFG.steamTtl);
      if (cachedHit !== undefined) {
        steamCur = cachedHit.price;
        steamSource = 'cache';
      } else if (freshLookups < CFG.steamMaxLookups) {
        const sp = await getSteamPrice(c.mhn, code);
        steamCur = sp.price;
        steamSource = sp.source;
        freshLookups++;
      } else {
        unmatched.push({
          name: c.name, wear: c.wear, mhn: c.mhn, payout: round2(payoutCur),
          why: 'лимит Steam — повтори поиск, дозапросим',
        });
        continue;
      }
    }
    if (steamCur == null) {
      unmatched.push({
        name: c.name, wear: c.wear, mhn: c.mhn, payout: round2(payoutCur),
        why: c.why || 'нет цены в Steam (имя ≠ market_hash_name)',
      });
      continue;
    }
    let spread = payoutCur - steamCur;
    if (net) spread -= steamCur * CFG.steamFee;
    const pct = steamCur > 0 ? (spread / steamCur) * 100 : 0;
    matched.push({
      name: c.name, wear: c.wear, mhn: c.mhn,
      lis: round2(payoutCur),
      payout: round2(payoutCur), steam: round2(steamCur),
      spread: round2(spread), pct: Math.round(pct * 10) / 10, steamSource,
      links: { steam: LINKS.steam(c.mhn), lis: LINKS.lis(c.name) },
    });
  }
  matched.sort((a, b) => b.spread - a.spread);
  const best = matched.length
    ? matched.reduce((m, r) => (r.spread > m.spread ? r : m), matched[0])
    : null;

  // Коридор в валюте показа = сумма ± коридор (без обратного перевода).
  const loCur = amount > 0 ? round2(amount * (1 - corr)) : 0;
  const hiCur = amount > 0 ? round2(amount * (1 + corr)) : 0;

  return {
    ok: true, version: VERSION,
    mode: usedMode, net, currency,
    fx: { rate: round4(rate), source: fx.source, currency },
    query: { amount, targetUsd: round2(targetUsd), corridorPct,
             corridor: { lo: loCur, hi: hiCur } },
    meta: {
      candidates: candidates.length, matched: matched.length,
      unmatched: unmatched.length, steamLookups: freshLookups,
      lisSource: source,
      lisTotal: CFG.lisApiToken ? candidates.length : lisState.map.size,
      lisLastRefresh: CFG.lisApiToken ? Date.now() : lisState.lastRefresh,
    },
    best, rows: matched, unmatched, warnings,
  };
}

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
        configured: !!(CFG.lisApiToken || CFG.lisPricesFile || CFG.lisBulkUrl),
        source: CFG.lisApiToken ? 'api/search' : CFG.lisPricesFile ? 'file' : 'bulk',
        total: lisState.map.size,
        cached: !!cacheGet('prices:lis', CFG.pricesTtl * 2),
        loading: lisState.loading,
        lastRefresh: lisState.lastRefresh || null,
        error: lisState.error,
      },
      steam: { delayMs: CFG.steamDelayMs, maxLookups: CFG.steamMaxLookups },
      fx: { source: 'steam', refItem: CFG.fxRefItem, currencies: Object.keys(STEAM_CURRENCY) },
      demoSkins: (DEMO.skins || []).length,
      uptime: process.uptime(),
    });
  }
  if (pathname === '/api/fx') {
    // Курсы из кэша/констант (Steam-derived). Без запросов к Steam здесь.
    const rates = {};
    for (const c of Object.keys(STEAM_CURRENCY)) rates[c] = round4(cachedRate(c).rate);
    return sendJson(res, 200, { ok: true, base: 'USD', source: 'steam', refItem: CFG.fxRefItem, rates });
  }
  if (pathname === '/api/steam') {
    const name = normName(q.get('name'));
    if (!name) return sendJson(res, 400, { ok: false, error: 'name required' });
    const currency = String(q.get('currency') || 'USD').toUpperCase();
    const sp = await getSteamPrice(name, steamCurrencyCode(currency));
    return sendJson(res, 200, { ok: true, name, currency, price: sp.price, lowest: sp.low, median: sp.med, source: sp.source, error: sp.error });
  }
  if (pathname === '/api/prices') {
    const sample = [...lisState.map].slice(0, int(q.get('limit'), 50));
    return sendJson(res, 200, {
      ok: true, exchange: 'lis',
      source: CFG.lisApiToken ? 'api/search (on-demand)' : lisState.source,
      count: lisState.map.size,
      sample: sample.map(([name, price]) => ({ name, price })),
      note: CFG.lisApiToken ? 'market/search — точечный поиск, прайс не выгружается целиком' : undefined,
      error: lisState.error,
    });
  }
  if (pathname === '/api/search') {
    // Без токена ждём предзагрузку прайса (файл/bulk). С токеном — точечный поиск.
    if (!CFG.lisApiToken && lisState.map.size === 0 && !lisState.loading) {
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
    const lisSrc = CFG.lisApiToken ? 'API market/search (точечно)'
                 : CFG.lisPricesFile ? 'файл' : 'bulk-URL (стриминг)';
    console.log(`  LIS: ${lisSrc} · Steam: priceoverview (нативная валюта) · курс: Steam`);
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
  // Значения уже в валюте показа (Steam — нативно, LIS — USD×курс).
  const toCur = (v) => fmt(v, dp);

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
  console.log('Курс USD→валюта (из Steam, эталон: ' + CFG.fxRefItem + ')');
  for (const c of ['RUB', 'EUR', 'KZT', 'UAH']) {
    const r = await getCurrencyRate(c);
    console.log(`  USD→${c}: ${round4(r.rate)} (${r.source})`);
  }
}

async function cliSteam(args) {
  const name = normName(args._.join(' '));
  if (!name) { console.error('Укажи имя: node server.js steam "AK-47 | Asiimov (Field-Tested)"'); process.exit(1); }
  const currency = (args.currency || 'USD').toUpperCase();
  const sp = await getSteamPrice(name, steamCurrencyCode(currency));
  const extra = (sp.low != null || sp.med != null)
    ? ` [lowest=${sp.low ?? '—'} · median=${sp.med ?? '—'}]` : '';
  console.log(`${name}: ${sp.price == null ? 'нет цены' : sp.price + ' ' + currency} (${sp.source})${extra}${sp.error ? ' — ' + sp.error : ''}`);
}

async function cliDiag() {
  if (CFG.lisApiToken) {
    console.log('Источник: LIS market/search (точечный поиск по токену)');
    console.log('  Прайс не выгружается целиком — каждый поиск запрашивает только');
    console.log('  скины из ценового коридора. Проверка: node server.js search 8000');
    return;
  }
  console.log(`Источник: LIS (файл/bulk)`);
  console.log(`  source=${lisState.source} · позиций=${lisState.map.size}${lisState.error ? ' · ошибка: ' + lisState.error : ''}`);
  [...lisState.map].slice(0, 10).forEach(([name, price]) => console.log(`    ${name} → $${price}`));
  if (!lisState.map.size) console.log('    (пусто — настрой LIS_API_TOKEN / LIS_PRICES_FILE, см. README)');
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
      // Ждём максимум 5 сек, потом убиваем
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

  if (CFG.lisApiToken) {
    // Быстрый путь: ничего не выгружаем заранее — каждый поиск точечно
    // обращается к market/search по ценовому коридору.
    startServer(port);
    info('LIS: режим market/search — прайс не выгружается, поиск точечный по токену');
  } else {
    // Запасной путь без токена: предзагрузка прайса (файл/bulk) + фон.
    initLisFromCache();
    startServer(port);
    if (lisState.map.size === 0) info('LIS: первая загрузка прайсов (bulk через стриминг) …');
    else info('LIS: обновление прайсов в фоне …');
    refreshLisPrices().then(() => {
      info(`LIS: готов — ${lisState.map.size.toLocaleString()} скинов (${lisState.source})`);
    });
    startBgRefresh();
  }
}

main().catch((e) => {
  error('fatal:', e.stack || e.message);
  process.exit(1);
});