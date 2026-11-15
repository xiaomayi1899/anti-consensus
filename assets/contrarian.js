/*!
 * 反共识选号 · 双色球 / 大乐透
 * 思路：先用走势图统计冷热、遗漏、和值、形态，再模拟彩民的生日号、吉利号、
 * 热号、均衡偏好等心理偏差，最后刻意反着选一注。
 *
 * 重要：彩票每期开奖是独立随机事件，任何组合中奖概率相同。
 * 本页不提高中奖概率，只尝试降低“与很多人选到同一注”的概率，
 * 从而在中奖时减少奖金分摊。仅供娱乐，理性购彩。
 */
(function () {
  "use strict";

  var E = window.LotteryEngine;
  if (!E) throw new Error("LotteryEngine 未加载");

  var GAMES = E.GAMES;
  var ORDER = ["ssq", "dlt"];
  var DATA_URL = "data/lottery.json";
  // Netlify 等静态托管时，后台尝试从旧站读取最新数据；失败则继续用打包数据
  var LIVE_DATA_URL = "https://xiaomayi1899.github.io/lucky-numbers/data/lottery.json";
  var REFRESH_MS = 60 * 1000;
  var LS_DATA = "anti.lottery.cache.v1";
  var LS_GAME = "anti.contrarian.game.v1";
  var LS_WINDOW = "anti.contrarian.window.v1";

  var LUCKY = { 6: 1, 8: 1, 9: 1, 16: 1, 18: 1, 28: 1 };

  var state = {
    data: null,
    active: "ssq",
    window: 30,
    reco: null,
    lastFetch: 0,
    nextFetch: 0,
    online: null,
    fetching: false,
  };

  var dom = {};

  /* ---------------- 基础工具 ---------------- */

  function $(sel, root) { return (root || document).querySelector(sel); }
  function $$(sel, root) { return Array.prototype.slice.call((root || document).querySelectorAll(sel)); }
  function save(key, value) { try { localStorage.setItem(key, value); } catch (e) { /* ignore */ } }
  function read(key) { try { return localStorage.getItem(key); } catch (e) { return null; } }
  function two(n) { return E.pad(n); }
  function range(min, max) { return E.range(min, max); }
  function sum(arr) { var s = 0; for (var i = 0; i < arr.length; i++) s += arr[i]; return s; }
  function mean(arr) { return arr.length ? sum(arr) / arr.length : 0; }
  function std(arr) {
    if (arr.length < 2) return 0;
    var m = mean(arr), s = 0;
    for (var i = 0; i < arr.length; i++) s += (arr[i] - m) * (arr[i] - m);
    return Math.sqrt(s / arr.length);
  }
  function clamp(x, lo, hi) { return Math.max(lo, Math.min(hi, x)); }
  function zeroMap(pool) {
    var out = {};
    for (var i = 0; i < pool.length; i++) out[pool[i]] = 0;
    return out;
  }
  function normalizeMap(map, pool) {
    var min = Infinity, max = -Infinity;
    for (var i = 0; i < pool.length; i++) {
      var v = map[pool[i]] || 0;
      if (v < min) min = v;
      if (v > max) max = v;
    }
    var span = max - min;
    var out = {};
    for (var j = 0; j < pool.length; j++) {
      var val = map[pool[j]] || 0;
      out[pool[j]] = span > 1e-12 ? (val - min) / span : 0.5;
    }
    return out;
  }
  function escapeHtml(s) {
    return String(s).replace(/[&<>"']/g, function (c) {
      return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c];
    });
  }
  function formatTime(iso) {
    if (!iso) return "--:--";
    var d = new Date(iso);
    if (isNaN(d.getTime())) return "--:--";
    try {
      return d.toLocaleTimeString("zh-CN", {
        hour12: false, hour: "2-digit", minute: "2-digit", timeZone: "Asia/Shanghai",
      });
    } catch (e) {
      return two(d.getHours()) + ":" + two(d.getMinutes());
    }
  }
  function formatMoney(n) {
    if (!n || isNaN(n)) return "";
    if (n >= 1e8) return (n / 1e8).toFixed(2) + " 亿元";
    if (n >= 1e4) return (n / 1e4).toFixed(0) + " 万元";
    return Math.round(n) + " 元";
  }
  function isTaboo(n) { return n % 10 === 4; }
  function isLucky(n) { return !!LUCKY[n]; }
  function isBig(n, game) { return n > (game.id === "ssq" ? 16 : 17); }
  function bigCut(game) { return game.id === "ssq" ? 16 : 17; }
  function zoneCuts(game) { return game.id === "ssq" ? [11, 22, 33] : [12, 24, 35]; }
  function zoneIndex(n, cuts) {
    var z = 0;
    while (z < cuts.length && n > cuts[z]) z += 1;
    return Math.min(z, cuts.length - 1);
  }
  function zoneCounts(nums, cuts) {
    var z = [];
    for (var i = 0; i < cuts.length; i++) z.push(0);
    for (var j = 0; j < nums.length; j++) z[zoneIndex(nums[j], cuts)] += 1;
    return z;
  }
  function consecutivePairs(nums) {
    var n = 0;
    for (var i = 1; i < nums.length; i++) if (nums[i] - nums[i - 1] === 1) n += 1;
    return n;
  }
  function maxRun(nums) {
    var best = 1, run = 1;
    for (var i = 1; i < nums.length; i++) {
      if (nums[i] - nums[i - 1] === 1) run += 1; else run = 1;
      if (run > best) best = run;
    }
    return nums.length ? best : 0;
  }
  function sameTailPairs(nums) {
    var n = 0;
    for (var i = 0; i < nums.length; i++) {
      for (var j = i + 1; j < nums.length; j++) if (nums[i] % 10 === nums[j] % 10) n += 1;
    }
    return n;
  }
  function isArithmetic(nums) {
    if (nums.length < 3) return false;
    var d = nums[1] - nums[0];
    for (var i = 2; i < nums.length; i++) if (nums[i] - nums[i - 1] !== d) return false;
    return true;
  }
  function intersection(a, b) {
    var out = [];
    for (var i = 0; i < a.length; i++) if (b.indexOf(a[i]) >= 0) out.push(a[i]);
    return out;
  }
  function shortIssue(issue) { return String(issue || "").slice(-3); }

  /* ---------------- 数据 ---------------- */

  function drawsFor(gameId) {
    var g = state.data && state.data.games && state.data.games[gameId];
    return g && Array.isArray(g.draws) ? g.draws : [];
  }

  function loadCache() {
    var raw = read(LS_DATA);
    if (!raw) return;
    try {
      var parsed = JSON.parse(raw);
      if (parsed && parsed.games) state.data = parsed;
    } catch (e) { /* ignore */ }
  }

  function validateData(json) {
    if (!json || !json.games) throw new Error("bad data");
    var n = 0;
    for (var id in json.games) if (json.games[id] && json.games[id].draws) n += json.games[id].draws.length;
    if (!n) throw new Error("empty data");
  }

  function setOnline(ok) {
    if (!dom.netDot) return;
    dom.netDot.classList.toggle("online", ok === true);
    dom.netDot.classList.toggle("offline", ok === false);
    dom.netDot.title = ok ? "数据已连接" : "离线缓存";
  }

  function fetchData(manual) {
    if (state.fetching) return;
    state.fetching = true;
    dom.refreshBtn.classList.add("spinning");
    fetch(DATA_URL + "?t=" + Date.now(), { cache: "no-store" })
      .then(function (res) {
        if (!res.ok) throw new Error("HTTP " + res.status);
        var fromCache = res.headers.get("X-Lottery-Cache") === "1";
        return res.json().then(function (json) { return { json: json, fromCache: fromCache }; });
      })
      .then(function (result) {
        validateData(result.json);
        var before = state.data && state.data.updated;
        state.data = result.json;
        state.data.cachedAt = Date.now();
        state.online = !result.fromCache;
        state.lastFetch = Date.now();
        state.nextFetch = Date.now() + REFRESH_MS;
        save(LS_DATA, JSON.stringify(state.data));
        setOnline(state.online);
        if (before !== state.data.updated) state.reco = null;
        render();
        if (manual) toast(result.fromCache ? "网络不可用，已读取离线缓存" : "已更新到最新开奖数据");
        fetchLiveData();
      })
      .catch(function (err) {
        state.online = false;
        state.nextFetch = Date.now() + REFRESH_MS;
        if (!state.data) loadCache();
        setOnline(false);
        render();
        if (manual) toast("网络暂时不可用，已显示本地缓存");
        console.warn("fetch failed", err);
      })
      .then(function () {
        state.fetching = false;
        window.setTimeout(function () { dom.refreshBtn.classList.remove("spinning"); }, 500);
      });
  }


  function fetchLiveData() {
    var controller = typeof AbortController !== "undefined" ? new AbortController() : null;
    var timer = window.setTimeout(function () { if (controller) controller.abort(); }, 6000);
    var opts = { cache: "no-store" };
    if (controller) opts.signal = controller.signal;
    fetch(LIVE_DATA_URL + "?t=" + Date.now(), opts)
      .then(function (res) { return res.ok ? res.json() : null; })
      .then(function (json) {
        clearTimeout(timer);
        if (!json || !json.games) return;
        validateData(json);
        var current = state.data && state.data.updated ? Date.parse(state.data.updated) : 0;
        var live = json.updated ? Date.parse(json.updated) : 0;
        if (!isFinite(current)) current = 0;
        if (!isFinite(live)) live = 0;
        if (live <= current) return;
        state.data = json;
        state.data.cachedAt = Date.now();
        state.online = true;
        save(LS_DATA, JSON.stringify(state.data));
        state.reco = null;
        setOnline(true);
        render();
      })
      .catch(function () { clearTimeout(timer); });
  }

  /* ---------------- 走势与统计 ---------------- */

  function countNumbers(draws, game, target, pool) {
    var counts = zeroMap(pool);
    for (var i = 0; i < draws.length; i++) {
      var arr = target === "special" ? E.specialNumbers(game, draws[i]) : E.mainNumbers(game, draws[i]);
      for (var j = 0; j < arr.length; j++) if (counts[arr[j]] != null) counts[arr[j]] += 1;
    }
    return counts;
  }

  function omissionFor(draws, pool, game, target) {
    var values = [];
    for (var i = 0; i < draws.length; i++) {
      values.push(target === "special" ? E.specialNumbers(game, draws[i]) : E.mainNumbers(game, draws[i]));
    }
    var omit = zeroMap(pool);
    var maxOmit = zeroMap(pool);
    var gapSum = zeroMap(pool);
    var gapCount = zeroMap(pool);
    for (var p = 0; p < pool.length; p++) {
      var n = pool[p];
      var gap = 0, seen = false, lastSeen = -1;
      for (var d = 0; d < values.length; d++) {
        var hit = values[d].indexOf(n) >= 0;
        if (hit) {
          if (seen) {
            gapSum[n] += gap;
            gapCount[n] += 1;
            if (gap > maxOmit[n]) maxOmit[n] = gap;
          }
          seen = true;
          gap = 0;
          if (lastSeen < 0) lastSeen = d;
        } else {
          gap += 1;
        }
      }
      omit[n] = lastSeen < 0 ? values.length : lastSeen;
      if (omit[n] > maxOmit[n]) maxOmit[n] = omit[n];
    }
    var avgOmit = zeroMap(pool);
    for (var q = 0; q < pool.length; q++) {
      var v = pool[q];
      avgOmit[v] = gapCount[v] ? gapSum[v] / gapCount[v] : values.length;
      if (avgOmit[v] < 1) avgOmit[v] = 1;
    }
    return { omit: omit, avgOmit: avgOmit, maxOmit: maxOmit };
  }

  function isNeighborOf(n, arr) {
    for (var i = 0; i < arr.length; i++) if (Math.abs(arr[i] - n) === 1) return true;
    return false;
  }

  function isDiagonalOf(n, prev, prev2) {
    for (var i = 0; i < prev.length; i++) {
      var p = prev[i];
      if (Math.abs(p - n) === 1) {
        var dir = n - p;
        if (prev2.indexOf(p - dir) >= 0) return true;
      }
    }
    return false;
  }

  /* 走势图信号：热、冷、重号、邻号、斜连、区间、尾数、空档 */
  function buildSignals(game, draws, pool, target, heat10Norm, heat30Norm, omitNorm, last, prev, prev2) {
    var cuts = zoneCuts(game);
    var zoneSum = {}, zoneCnt = {}, tailSum = {}, tailCnt = {};
    for (var i = 0; i < pool.length; i++) {
      var n = pool[i];
      var z = zoneIndex(n, cuts);
      var t = n % 10;
      zoneSum[z] = (zoneSum[z] || 0) + (heat10Norm[n] || 0);
      zoneCnt[z] = (zoneCnt[z] || 0) + 1;
      tailSum[t] = (tailSum[t] || 0) + (heat10Norm[n] || 0);
      tailCnt[t] = (tailCnt[t] || 0) + 1;
    }
    var last5 = draws.slice(0, 5);
    var signals = {};
    for (var j = 0; j < pool.length; j++) {
      var v = pool[j];
      var zone = zoneIndex(v, cuts);
      var tail = v % 10;
      var repeat = last.indexOf(v) >= 0 ? 1 : 0;
      var neighbor = isNeighborOf(v, last) ? 1 : 0;
      var diagonal = isDiagonalOf(v, prev, prev2) ? 1 : 0;
      var gap5 = 1;
      for (var d = 0; d < last5.length; d++) {
        var vals = target === "special" ? E.specialNumbers(game, last5[d]) : E.mainNumbers(game, last5[d]);
        if (vals.indexOf(v) >= 0) { gap5 = 0; break; }
      }
      var zoneHeat = zoneCnt[zone] ? zoneSum[zone] / zoneCnt[zone] : 0;
      var tailHeat = tailCnt[tail] ? tailSum[tail] / tailCnt[tail] : 0;
      var trend = 0.39 * (heat10Norm[v] || 0) +
        0.18 * (heat30Norm[v] || 0) +
        0.22 * (omitNorm[v] || 0) +
        0.04 * repeat +
        0.04 * neighbor +
        0.03 * diagonal +
        0.06 * zoneHeat +
        0.04 * tailHeat;
      signals[v] = {
        hot10: heat10Norm[v] || 0,
        hot30: heat30Norm[v] || 0,
        omitNorm: omitNorm[v] || 0,
        repeat: repeat,
        neighbor: neighbor,
        diagonal: diagonal,
        gap5: gap5,
        zoneHeat: zoneHeat,
        tailHeat: tailHeat,
        trendScore: clamp(trend, 0, 1),
      };
    }
    return signals;
  }

  /* 模拟 2000 个“看走势图选号”的彩民：追热、补冷、重号、邻号、斜连、区间、尾数、均衡 */
  function buildInfo(pool, signals, omitData) {
    var info = {};
    var sorted = pool.slice().sort(function (x, y) {
      return signals[x].trendScore - signals[y].trendScore || x - y;
    });
    var rank = {};
    for (var r = 0; r < sorted.length; r++) rank[sorted[r]] = r + 1;

    for (var i = 0; i < pool.length; i++) {
      var n = pool[i];
      var s = signals[n];
      var parts = {
        hot10: 0.39 * s.hot10,
        hot30: 0.18 * s.hot30,
        omit: 0.22 * s.omitNorm,
        repeat: 0.04 * s.repeat,
        neighbor: 0.04 * s.neighbor,
        diagonal: 0.03 * s.diagonal,
        zone: 0.06 * s.zoneHeat,
        tail: 0.04 * s.tailHeat,
      };
      var consensus = clamp((parts.hot10 + parts.hot30 + parts.omit + parts.repeat +
        parts.neighbor + parts.diagonal + parts.zone + parts.tail) * 100, 0, 100);

      var tags = [];
      if (s.hot10 >= 0.7) tags.push("热号");
      if (omitData.omit[n] >= Math.max(5, omitData.avgOmit[n] * 1.5)) tags.push("高遗漏");
      if (s.repeat) tags.push("重号");
      if (s.neighbor) tags.push("邻号");
      if (s.diagonal) tags.push("斜连");
      if (s.zoneHeat >= 0.75) tags.push("热区");
      if (s.tailHeat >= 0.75) tags.push("热尾");
      if (s.gap5) tags.push("空档");
      if (n > 31) tags.push("非生日");
      if (!tags.length) tags.push("中性");

      info[n] = {
        n: n,
        consensus: consensus,
        parts: parts,
        rank: rank[n],
        heat10: s.hot10,
        heat30: s.hot30,
        omit: omitData.omit[n],
        avgOmit: omitData.avgOmit[n],
        tags: tags,
      };
    }
    return info;
  }

  /* 形态的历史分布：众数、常见区间（累积 85%）、出现率、均值/标准差 */
  function histStat(values) {
    var total = values.length;
    var counts = {};
    for (var i = 0; i < total; i++) {
      var v = values[i];
      counts[v] = (counts[v] || 0) + 1;
    }
    var keys = [];
    for (var key in counts) if (counts.hasOwnProperty(key)) keys.push(+key);
    keys.sort(function (x, y) { return x - y; });
    var prob = {}, mode = keys.length ? keys[0] : 0, maxP = 0;
    for (var j = 0; j < keys.length; j++) {
      prob[keys[j]] = total ? counts[keys[j]] / total : 0;
      if (prob[keys[j]] > maxP) { maxP = prob[keys[j]]; mode = keys[j]; }
    }
    /* 以众数为中心向两侧扩展，累积到 85% 得到“历史常见区间” */
    var acc = maxP, lo = mode, hi = mode;
    while (acc < 0.85) {
      var down = prob[lo - 1] || 0, up = prob[hi + 1] || 0;
      if (!down && !up) break;
      if (up >= down) { hi += 1; acc += up; } else { lo -= 1; acc += down; }
    }
    var atLeastOne = 0;
    for (var t = 1; t <= 12; t++) atLeastOne += prob[t] || 0;
    return {
      sample: total,
      mean: total ? mean(values) : 0,
      std: total ? std(values) : 0,
      mode: mode,
      maxP: maxP,
      lo: lo,
      hi: hi,
      prob: prob,
      rate: atLeastOne,
      values: keys,
    };
  }

  /* 该数量在历史分布里的相对概率（0-1，用于组合校准） */
  function patternFit(stat, value) {
    var pv = stat.prob[value];
    if (pv === undefined) {
      var edge = value > stat.hi ? stat.hi : stat.lo;
      return Math.max(0, 0.35 / (1 + Math.abs(value - edge) * 2));
    }
    return Math.sqrt(pv / (stat.maxP || 1));
  }

  /* 是否落在历史常见区间内 */
  function patternCommon(stat, value) {
    return value >= stat.lo && value <= stat.hi;
  }

  /* 常见区间外一格仍可接受（用于候选放宽） */
  function patternNear(stat, value) {
    return value >= stat.lo - 1 && value <= stat.hi + 1;
  }

  function patternText(stat) {
    return "最常见 " + stat.mode + "（" + Math.round((stat.maxP || 0) * 100) + "%）";
  }

  /* 近 100 期真实形态统计：重号、邻号、斜连、连号、同尾、空档、空区、和值、奇偶、大小、跨度 */
  function buildPatternStats(draws, game, cuts) {
    var n = Math.min(100, draws.length);
    var repeats = [], neighbors = [], diagonals = [], consecs = [], tails = [];
    var gaps = [], empties = [], sums = [], odds = [], bigs = [], spans = [];
    for (var i = 0; i < n - 1; i++) {
      var cur = E.mainNumbers(game, draws[i]);
      var prev = E.mainNumbers(game, draws[i + 1]);
      var prev2 = draws[i + 2] ? E.mainNumbers(game, draws[i + 2]) : [];
      repeats.push(intersection(cur, prev).length);
      neighbors.push(cur.filter(function (x) { return isNeighborOf(x, prev); }).length);
      diagonals.push(cur.filter(function (x) { return isDiagonalOf(x, prev, prev2); }).length);
      consecs.push(consecutivePairs(cur));
      tails.push(sameTailPairs(cur));
      if (i + 5 < draws.length) {
        var prev5 = [];
        for (var j = i + 1; j <= i + 5; j++) prev5 = prev5.concat(E.mainNumbers(game, draws[j]));
        gaps.push(cur.filter(function (x) { return prev5.indexOf(x) < 0; }).length);
      }
      empties.push(zoneCounts(cur, cuts).filter(function (z) { return z === 0; }).length);
      sums.push(sum(cur));
      odds.push(cur.filter(function (x) { return x % 2; }).length);
      bigs.push(cur.filter(function (x) { return x > bigCut(game); }).length);
      spans.push(Math.max.apply(null, cur) - Math.min.apply(null, cur));
    }
    function m(arr) { return arr.length ? mean(arr) : 0; }
    function rate(arr, t) {
      return arr.length ? arr.filter(function (x) { return x >= t; }).length / arr.length : 0;
    }
    var stats = {
      repeat: histStat(repeats),
      neighbor: histStat(neighbors),
      diagonal: histStat(diagonals),
      consec: histStat(consecs),
      tail: histStat(tails),
      gap: histStat(gaps),
      emptyZone: histStat(empties),
      odd: histStat(odds),
      big: histStat(bigs),
      span: histStat(spans),
    };
    return {
      stats: stats,
      sample: Math.max(0, n - 1),
      repeatMean: m(repeats),
      neighborMean: m(neighbors),
      diagonalMean: m(diagonals),
      diagonalRate: rate(diagonals, 1),
      consecMean: m(consecs),
      consecRate: rate(consecs, 1),
      tailMean: m(tails),
      gapMean: m(gaps),
      emptyZoneMean: m(empties),
      sumMean: m(sums),
      sumStd: std(sums),
      oddMean: m(odds),
      bigMean: m(bigs),
      spanMean: m(spans),
    };
  }

  function analyze(gameId, windowSize) {
    var game = GAMES[gameId];
    var draws = drawsFor(gameId);
    if (!draws.length) return null;
    var last = draws[0];
    var mainPool = range(game.mainMin, game.mainMax);
    var specialPool = game.specialCount ? range(game.specialMin, game.specialMax) : [];
    var lastMain = E.mainNumbers(game, last);
    var lastSpecial = E.specialNumbers(game, last);
    var prevMain = draws[1] ? E.mainNumbers(game, draws[1]) : [];
    var prev2Main = draws[2] ? E.mainNumbers(game, draws[2]) : [];
    var prevSpecial = draws[1] ? E.specialNumbers(game, draws[1]) : [];
    var prev2Special = draws[2] ? E.specialNumbers(game, draws[2]) : [];

    var heat10 = countNumbers(draws.slice(0, 10), game, "main", mainPool);
    var heat30 = countNumbers(draws.slice(0, 30), game, "main", mainPool);
    var omitData = omissionFor(draws.slice(0, Math.max(windowSize, 60)), mainPool, game, "main");
    var heat10Norm = normalizeMap(heat10, mainPool);
    var heat30Norm = normalizeMap(heat30, mainPool);
    var omitNorm = normalizeMap(omitData.omit, mainPool);
    var signals = buildSignals(game, draws, mainPool, "main", heat10Norm, heat30Norm, omitNorm, lastMain, prevMain, prev2Main);
    var mainInfo = buildInfo(mainPool, signals, omitData);

    var specialInfo = null;
    var specialSignals = null;
    if (specialPool.length) {
      var sHeat10 = countNumbers(draws.slice(0, 10), game, "special", specialPool);
      var sHeat30 = countNumbers(draws.slice(0, 30), game, "special", specialPool);
      var sOmitData = omissionFor(draws.slice(0, Math.max(windowSize, 60)), specialPool, game, "special");
      var sHeat10Norm = normalizeMap(sHeat10, specialPool);
      var sHeat30Norm = normalizeMap(sHeat30, specialPool);
      var sOmitNorm = normalizeMap(sOmitData.omit, specialPool);
      specialSignals = buildSignals(game, draws, specialPool, "special", sHeat10Norm, sHeat30Norm, sOmitNorm, lastSpecial, prevSpecial, prev2Special);
      specialInfo = buildInfo(specialPool, specialSignals, sOmitData);
    }

    var sums = [];
    for (var i = 0; i < Math.min(30, draws.length); i++) sums.push(sum(E.mainNumbers(game, draws[i])));
    var meanSum = mean(sums);
    var stdSum = std(sums);

    var cuts = zoneCuts(game);
    var cutBig = bigCut(game);
    var patterns = buildPatternStats(draws, game, cuts);
    var formRows = [];
    for (var r = 0; r < Math.min(8, draws.length); r++) {
      var d = draws[r];
      var main = E.mainNumbers(game, d);
      var prev = draws[r + 1] ? E.mainNumbers(game, draws[r + 1]) : [];
      var zones = zoneCounts(main, cuts);
      formRows.push({
        issue: shortIssue(d.issue),
        sum: sum(main),
        odd: main.filter(function (n) { return n % 2; }).length,
        even: main.length - main.filter(function (n) { return n % 2; }).length,
        big: main.filter(function (n) { return n > cutBig; }).length,
        small: main.length - main.filter(function (n) { return n > cutBig; }).length,
        zones: zones.join(":"),
        consecutive: consecutivePairs(main),
        repeat: intersection(main, prev).length,
      });
    }

    return {
      game: game, gameId: gameId, window: windowSize, draws: draws,
      last: last, lastMain: lastMain, lastSpecial: lastSpecial,
      prevMain: prevMain, prev2Main: prev2Main,
      mainPool: mainPool, specialPool: specialPool,
      heat10: heat10, heat30: heat30, omit: omitData.omit,
      avgOmit: omitData.avgOmit, maxOmit: omitData.maxOmit,
      heat10Norm: heat10Norm, heat30Norm: heat30Norm, omitNorm: omitNorm,
      signals: signals, specialSignals: specialSignals,
      mainInfo: mainInfo, specialInfo: specialInfo,
      sums: sums, meanSum: meanSum, stdSum: stdSum, formRows: formRows,
      patterns: patterns, zoneCuts: cuts, bigCut: cutBig,
    };
  }

  /* ---------------- 反共识评分 ---------------- */

  function combinationRaw(nums, a) {
    var k = nums.length;
    var info = a.mainInfo;
    var signals = a.signals;
    var st = a.patterns.stats;
    var avgConsensus = 0, odd = 0, big = 0;
    var hot = 0, cold = 0, neighbors = 0, diagonals = 0, gaps = 0;
    for (var i = 0; i < nums.length; i++) {
      var n = nums[i];
      var f = info[n];
      var s = signals[n];
      avgConsensus += f.consensus;
      if (n % 2) odd += 1;
      if (n > a.bigCut) big += 1;
      if (f.heat10 >= 0.7) hot += 1;
      if (f.omit >= Math.max(5, f.avgOmit * 1.5)) cold += 1;
      if (s.neighbor) neighbors += 1;
      if (s.diagonal) diagonals += 1;
      if (s.gap5) gaps += 1;
    }
    avgConsensus /= k;

    var zones = zoneCounts(nums, a.zoneCuts);
    var idealZone = k / zones.length;
    var zoneDev = 0;
    for (var z = 0; z < zones.length; z++) zoneDev += Math.abs(zones[z] - idealZone);
    var sumZ = Math.abs(sum(nums) - a.meanSum) / (a.stdSum || 1);
    var repeat = intersection(nums, a.lastMain).length;
    var consec = consecutivePairs(nums);
    var tails = sameTailPairs(nums);
    var span = nums[nums.length - 1] - nums[0];
    var emptyZones = 0;
    for (var e = 0; e < zones.length; e++) if (zones[e] === 0) emptyZones += 1;

    var penalty = 0;
    var allOdd = odd === k, allEven = odd === 0;
    var allBig = big === k, allSmall = big === 0;
    var allOneZone = zones.some(function (x) { return x === k; });
    if (allOdd || allEven) penalty += 8;
    if (allBig || allSmall) penalty += 8;
    if (allOneZone) penalty += 8;
    if (tails >= k - 1 && k > 2) penalty += 8;
    if (isArithmetic(nums)) penalty += 8;
    if (maxRun(nums) >= 4) penalty += 6;

    /* 形态项统一写成“偏离历史分布的罚分”：越贴近近 100 期真实分布罚分越低。
       斜连 0 个（68%）与 1 个（29%）都只是不同程度的贴近，不会被系统排除。 */
    function miss(stat, value, weight) { return weight * (1 - patternFit(stat, value)); }

    return 0.42 * avgConsensus +
      miss(st.repeat, repeat, 14) +
      miss(st.neighbor, neighbors, 12) +
      miss(st.diagonal, diagonals, 8) +
      miss(st.consec, consec, 6) +
      miss(st.tail, tails, 4) +
      miss(st.gap, gaps, 5) +
      miss(st.emptyZone, emptyZones, 3) +
      miss(st.odd, odd, 2) +
      miss(st.big, big, 2) +
      12 * (1 - Math.exp(-sumZ * sumZ / 2)) +
      10 * zoneDev / k +
      4 * (1 - Math.exp(-0.5 * Math.pow((span - st.span.mean) / (st.span.std || 1), 2))) +
      (hot > 2 ? (hot - 2) * 4 : 0) +
      (cold === 0 ? 2 : 0) +
      (cold > 2 ? (cold - 2) * 8 : 0) +
      penalty;
  }

  /* 反共识候选池：共识分最低的一批 + 重号/邻号/斜连各留配额，
     避免常见形态的号码被整体挤出候选池（这正是 v4 里“重号 0 邻号 0 斜连 0”的成因）。 */
  function candidatePool(a) {
    var sorted = a.mainPool.slice().sort(function (x, y) {
      return a.mainInfo[x].consensus - a.mainInfo[y].consensus || x - y;
    });
    var base = sorted.slice(0, Math.min(16, sorted.length));
    var extra = [];
    function addBy(test, count) {
      var added = 0;
      for (var i = 0; i < sorted.length && added < count; i++) {
        var n = sorted[i];
        if (base.indexOf(n) >= 0 || extra.indexOf(n) >= 0) continue;
        if (!test(n)) continue;
        extra.push(n);
        added += 1;
      }
    }
    addBy(function (n) { return a.signals[n].repeat; }, 3);
    addBy(function (n) { return a.signals[n].neighbor; }, 3);
    addBy(function (n) { return a.signals[n].diagonal; }, 2);
    var pool = base.concat(extra);
    for (var j = 0; j < sorted.length && pool.length < 24; j++) {
      if (pool.indexOf(sorted[j]) < 0) pool.push(sorted[j]);
    }
    return pool;
  }

  function buildCandidates(a) {
    var k = a.game.mainCount;
    var top = candidatePool(a);
    var lastKey = a.lastMain.slice().sort(function (x, y) { return x - y; }).join(",");
    var out = [], chosen = [];
    var st = a.patterns.stats;

    /* 形态数量是否落在历史常见区间：默认按累积 85% 区间判断，
       放宽容错时允许区间外一格。斜连 0 个或 1 个都能通过——不预设“必须有几个”。 */
    function patternOk(nums, relax) {
      var repeat = intersection(nums, a.lastMain).length;
      var neighbors = nums.filter(function (n) { return a.signals[n].neighbor; }).length;
      var diagonals = nums.filter(function (n) { return a.signals[n].diagonal; }).length;
      var consec = consecutivePairs(nums);
      var tails = sameTailPairs(nums);
      var gaps = nums.filter(function (n) { return a.signals[n].gap5; }).length;
      var zones = zoneCounts(nums, a.zoneCuts);
      var emptyZones = zones.filter(function (z) { return z === 0; }).length;
      var odd = nums.filter(function (n) { return n % 2; }).length;
      var big = nums.filter(function (n) { return n > a.bigCut; }).length;
      var span = nums[nums.length - 1] - nums[0];
      var checks = [
        [st.repeat, repeat], [st.neighbor, neighbors], [st.diagonal, diagonals],
        [st.consec, consec], [st.tail, tails], [st.gap, gaps],
        [st.emptyZone, emptyZones], [st.odd, odd], [st.big, big],
      ];
      for (var c = 0; c < checks.length; c++) {
        var stat = checks[c][0], val = checks[c][1];
        if (relax ? !patternNear(stat, val) : !patternCommon(stat, val)) return false;
      }
      return Math.abs(span - st.span.mean) <= (relax ? 8 : 5);
    }

    function rec(start, relax) {
      if (chosen.length === k) {
        var nums = chosen.slice().sort(function (x, y) { return x - y; });
        var key = nums.join(",");
        if (key === lastKey) return;
        if (!patternOk(nums, relax)) return;
        out.push({ nums: nums, key: key, raw: combinationRaw(nums, a) });
        return;
      }
      for (var i = start; i < top.length; i++) {
        if (top.length - i < k - chosen.length) break;
        chosen.push(top[i]);
        rec(i + 1, relax);
        chosen.pop();
      }
    }
    rec(0, false);
    if (!out.length) rec(0, true);
    out.sort(function (x, y) {
      return x.raw - y.raw || x.key.localeCompare(y.key);
    });
    if (!out.length) {
      var fallback = top.slice(0, k).sort(function (x, y) { return x - y; });
      out.push({ nums: fallback, key: fallback.join(","), raw: combinationRaw(fallback, a), fallback: true });
    }
    return out;
  }

  function specialPick(a, count) {
    if (!a.specialInfo) return [];
    var sorted = a.specialPool.slice().sort(function (x, y) {
      return a.specialInfo[x].consensus - a.specialInfo[y].consensus || x - y;
    });
    return sorted.slice(0, count).sort(function (x, y) { return x - y; });
  }

  function buildRecommendation(a) {
    var candidates = buildCandidates(a);
    var final = candidates[0];
    if (!final) return null;
    var sp = specialPick(a, a.game.specialCount);
    var avg = 0;
    for (var i = 0; i < final.nums.length; i++) avg += a.mainInfo[final.nums[i]].consensus;
    avg = avg / final.nums.length;
    var set = {
      label: "固定一注",
      primary: final.nums,
      special: sp,
      anti: clamp(Math.round(100 - avg), 0, 100),
      avg: Math.round(avg * 10) / 10,
      raw: final.raw,
      fit: Math.round(clamp(100 - final.raw, 0, 100) * 10) / 10,
    };
    return {
      sets: [set],
      candidateCount: candidates.length,
      analysis: a,
      gameId: a.gameId,
      window: a.window,
      latest: a.last ? a.last.issue : "",
      generatedAt: Date.now(),
    };
  }

  function ensureReco() {
    var gameId = state.active;
    var draws = drawsFor(gameId);
    var latest = draws[0] ? draws[0].issue : "";
    var cur = state.reco;
    var stale = !cur || cur.gameId !== gameId || cur.window !== state.window || cur.latest !== latest;
    if (stale) {
      var analysis = analyze(gameId, state.window);
      if (!analysis) return null;
      state.reco = buildRecommendation(analysis);
    }
    return state.reco;
  }

  /* ---------------- 规则 ---------------- */

  function buildRules(reco) {
    var a = reco.analysis;
    var set = reco.sets[0];
    var nums = set.primary;
    var k = nums.length;
    var info = a.mainInfo;
    var signals = a.signals;
    var p = a.patterns;
    var hot = 0, cold = 0, repeat = 0, neighbors = 0, diagonals = 0, gaps = 0, hotTails = 0;
    for (var i = 0; i < nums.length; i++) {
      var n = nums[i];
      var f = info[n];
      var s = signals[n];
      if (f.heat10 >= 0.7) hot += 1;
      if (f.omit >= Math.max(5, f.avgOmit * 1.5)) cold += 1;
      if (s.repeat) repeat += 1;
      if (s.neighbor) neighbors += 1;
      if (s.diagonal) diagonals += 1;
      if (s.gap5) gaps += 1;
      if (s.tailHeat >= 0.75) hotTails += 1;
    }
    var odd = nums.filter(function (n) { return n % 2; }).length;
    var big = nums.filter(function (n) { return n > a.bigCut; }).length;
    var zones = zoneCounts(nums, a.zoneCuts);
    var emptyZones = zones.filter(function (z) { return z === 0; }).length;
    var total = sum(nums);
    var sumZ = Math.abs(total - a.meanSum) / (a.stdSum || 1);
    var span = nums[nums.length - 1] - nums[0];
    var consec = consecutivePairs(nums);
    var tails = sameTailPairs(nums);
    var st = p.stats;
    function pct(x) { return Math.round((x || 0) * 100) + "%"; }
    function distText(stat, unit) {
      return "近100期最常见 " + stat.mode + " " + unit + "（" + pct(stat.maxP) +
        "），常见区间 " + stat.lo + "-" + stat.hi + " " + unit + "。";
    }

    return [
      { name: "热号追踪", bias: "彩民会追近 10 期热号，但不代表热号一定继续出。", current: "本注含近10期热号 <b>" + hot + "</b> 个。", action: "控制：热号不超过 1 个，降低撞热号。", ok: hot <= 1 },
      { name: "冷号回补", bias: "长期未出会被认为“该补了”，但极端冷号并不更稳。", current: "本注含高遗漏 <b>" + cold + "</b> 个。", action: "校准：保留 1-2 个中高遗漏，不追极端。", ok: cold >= 1 && cold <= 2 },
      { name: "上期重号", bias: "重号是高频形态：" + distText(st.repeat, "个"), current: "本注 <b>" + repeat + "</b> 个。", action: "校准：落在历史常见区间即可，不刻意凑也不刻意躲。", ok: patternCommon(st.repeat, repeat) },
      { name: "邻号延伸", bias: "上期号码的 ±1 邻号几乎每期都有：" + pct(st.neighbor.rate) + " 的期次至少 1 个。" + distText(st.neighbor, "个"), current: "本注 <b>" + neighbors + "</b> 个。", action: "校准：按历史分布保留邻号，不把它当“要回避的形态”。", ok: patternCommon(st.neighbor, neighbors) },
      { name: "斜连走势", bias: "斜连经常出现：" + pct(st.diagonal.rate) + " 的期次至少 1 个；0 个同样常见（" + pct(st.diagonal.prob[0] || 0) + "）。" + distText(st.diagonal, "个"), current: "本注 <b>" + diagonals + "</b> 个。", action: "校准：0 个或 1 个都算正常，由其他维度决定，不预设必须含斜连。", ok: patternCommon(st.diagonal, diagonals) },
      { name: "连号形态", bias: "连号是常见形态：" + pct(st.consec.rate) + " 的期次至少 1 组。" + distText(st.consec, "组"), current: "本注 <b>" + consec + "</b> 组。", action: "校准：落在历史常见区间即可，不认为连号不会出。", ok: patternCommon(st.consec, consec) },
      { name: "同尾走势", bias: "同尾号也会出现：" + pct(st.tail.rate) + " 的期次至少 1 组。" + distText(st.tail, "组"), current: "本注 <b>" + tails + "</b> 组。", action: "校准：按历史分布取数量，不刻意回避同尾。", ok: patternCommon(st.tail, tails) },
      { name: "区间轮动", bias: "空区并不罕见：" + pct(st.emptyZone.prob[1] || 0) + " 的期次有 1 个空区。" + distText(st.emptyZone, "个"), current: "三区 <b>" + zones.join(":") + "</b>，空区 <b>" + emptyZones + "</b> 个。", action: "校准：空区数量贴近历史分布。", ok: patternCommon(st.emptyZone, emptyZones) },
      { name: "和值回归", bias: "和值围绕历史均值波动；近100期均值 " + p.sumMean.toFixed(0) + "±" + p.sumStd.toFixed(0) + "。", current: "和值 <b>" + total + "</b>；偏离 <b>" + sumZ.toFixed(1) + "σ</b>。", action: "校准：控制在与历史分布相近的范围。", ok: sumZ <= 1.5 },
      { name: "奇偶均衡", bias: "奇偶比例有历史分布：" + distText(st.odd, "个奇数"), current: "奇偶 <b>" + odd + ":" + (k - odd) + "</b>，奇数 <b>" + odd + "</b> 个。", action: "校准：允许偏态，但落在历史常见区间。", ok: patternCommon(st.odd, odd) },
      { name: "大小均衡", bias: "大小号比例也有历史分布：" + distText(st.big, "个大号"), current: "大小 <b>" + big + ":" + (k - big) + "</b>，大号 <b>" + big + "</b> 个。", action: "校准：允许偏态，但落在历史常见区间。", ok: patternCommon(st.big, big) },
      { name: "空档回补", bias: "近5期没开过的“空档号”也会开出：" + distText(st.gap, "个"), current: "本注含近5期空档 <b>" + gaps + "</b> 个。", action: "校准：按历史空档数量调整。", ok: patternCommon(st.gap, gaps) },
      { name: "跨度选择", bias: "跨度有历史分布；近100期均值 " + st.span.mean.toFixed(1) + "，波动 ±" + st.span.std.toFixed(1) + "。", current: "跨度 <b>" + span + "</b>。", action: "校准：允许大/小跨度，但靠近历史均值。", ok: Math.abs(span - st.span.mean) <= (st.span.std || 1) * 1.5 },
      { name: "热尾轮动", bias: "近期热尾会被追，但热尾不等于必出。", current: "本注含热尾 <b>" + hotTails + "</b> 个。", action: "控制：热尾不超过 1 个，降低撞热尾。", ok: hotTails <= 1 },
    ];
  }

  function patternHTML(a) {
    var p = a.patterns;
    var st = p.stats;
    function chip(label, value, sub) {
      return '<div class="pattern-chip"><span class="pattern-label">' + escapeHtml(label) +
        '</span><span class="pattern-value">' + escapeHtml(value) + "</span>" +
        (sub ? '<span class="pattern-sub">' + escapeHtml(sub) + "</span>" : "") + "</div>";
    }
    function pct(x) { return Math.round((x || 0) * 100) + "%"; }
    function range(stat) { return "常见 " + stat.lo + "-" + stat.hi + "｜率 " + pct(stat.rate); }
    return '<section class="card pattern-card">' +
      '<div class="card-head"><div class="card-title"><span class="icon">▤</span>历史形态校准</div>' +
      '<span class="badge">近 ' + p.sample + " 期</span></div>" +
      '<p class="hint-text">斜连、邻号、重号、连号本身就经常出现，所以不反选、也不硬凑：先统计它们近 100 期的真实分布，再让组合的数量落在历史常见区间，由其他维度决定具体号码。</p>' +
      '<div class="pattern-grid">' +
      chip("重号", "均值 " + st.repeat.mean.toFixed(1) + " 个", "最常见 " + st.repeat.mode + "｜" + range(st.repeat)) +
      chip("邻号", "均值 " + st.neighbor.mean.toFixed(1) + " 个", "最常见 " + st.neighbor.mode + "｜" + range(st.neighbor)) +
      chip("斜连", "均值 " + st.diagonal.mean.toFixed(1) + " 个", "0 个 " + pct(st.diagonal.prob[0] || 0) + "｜1 个 " + pct(st.diagonal.prob[1] || 0)) +
      chip("连号", "均值 " + st.consec.mean.toFixed(1) + " 组", "最常见 " + st.consec.mode + "｜" + range(st.consec)) +
      chip("同尾", "均值 " + st.tail.mean.toFixed(1) + " 组", "最常见 " + st.tail.mode + "｜" + range(st.tail)) +
      chip("空档", "均值 " + st.gap.mean.toFixed(1) + " 个", "最常见 " + st.gap.mode + "｜" + range(st.gap)) +
      chip("空区", "均值 " + st.emptyZone.mean.toFixed(1) + " 个", "最常见 " + st.emptyZone.mode + "｜" + range(st.emptyZone)) +
      chip("和值", "均值 " + p.sumMean.toFixed(0) + " ± " + p.sumStd.toFixed(0), "近100期") +
      chip("奇数", "均值 " + st.odd.mean.toFixed(1) + " 个", "最常见 " + st.odd.mode + "｜" + range(st.odd)) +
      chip("大号", "均值 " + st.big.mean.toFixed(1) + " 个", "最常见 " + st.big.mode + "｜" + range(st.big)) +
      chip("跨度", "均值 " + st.span.mean.toFixed(1), "波动 ±" + st.span.std.toFixed(1)) +
      "</div></section>";
  }

  /* ---------------- 渲染 ---------------- */

  function renderTabs() {
    if (!dom.tabs) return;
    dom.tabs.innerHTML = ORDER.map(function (id) {
      var g = GAMES[id];
      return '<button class="tab" type="button" role="tab" data-game="' + id + '" aria-selected="' +
        (id === state.active ? "true" : "false") + '" style="--dot:' + g.color + '">' +
        '<span class="dot"></span>' + escapeHtml(g.name) + "</button>";
    }).join("");
  }

  function latestBallsHTML(a) {
    var game = a.game;
    if (game.kind === "digits") {
      return a.lastMain.map(function (d, i) {
        return '<span class="ball teal" style="animation-delay:' + (i * 24) + 'ms">' + d + "</span>";
      }).join("");
    }
    var mainClass = game.id === "dlt" ? "orange" : "red";
    var out = a.lastMain.map(function (n, i) {
      return '<span class="ball ' + mainClass + '" style="animation-delay:' + (i * 22) + 'ms">' + two(n) + "</span>";
    }).join("");
    if (a.lastSpecial.length) {
      out += '<span class="plus">＋</span>' + a.lastSpecial.map(function (n) {
        return '<span class="ball blue">' + two(n) + "</span>";
      }).join("");
    }
    return out;
  }

  function tagOf(info) {
    if (!info || !info.tags || !info.tags.length) return "";
    var tags = info.tags;
    var priority = ["热号", "高遗漏", "重号", "邻号", "斜连", "热区", "热尾", "空档", "非生日", "中性"];
    for (var p = 0; p < priority.length; p++) {
      if (tags.indexOf(priority[p]) >= 0) return priority[p];
    }
    return tags[0];
  }

  function ballWithTag(n, klass, info, display) {
    return '<span class="ball-wrap"><span class="ball ' + klass + '">' +
      escapeHtml(display) + '</span><span class="tag-badge">' + escapeHtml(tagOf(info)) + "</span></span>";
  }

  function copyButtonHTML(text, cls) {
    return '<button class="' + (cls || "copy-btn") + '" type="button" data-copy="' + escapeHtml(text) + '" aria-label="复制这注号码">' +
      '<svg viewBox="0 0 24 24" width="16" height="16" aria-hidden="true"><rect x="8" y="8" width="11" height="11" rx="2" fill="none" stroke="currentColor" stroke-width="1.7"/><path d="M6 15V6a2 2 0 0 1 2-2h9" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round"/></svg>' +
      "</button>";
  }

  function setText(gameId, set) {
    var game = GAMES[gameId];
    var text = game.name + " " + set.label + "：" + set.primary.map(two).join(" ");
    if (set.special && set.special.length) text += " ＋ " + set.special.map(two).join(" ");
    return text;
  }

  function introHTML() {
    return '<section class="card intro-card">' +
      '<div class="intro-eyebrow">V4 · SHAPE CALIBRATION</div>' +
      "<h2>先看历史形态，再固定一注</h2>" +
      "<p>不再把斜连、邻号、重号当成“不可能”。先统计近 100 期这些形态的真实出现率，再给每个号码逐项打分，组合按历史分布校准，最后确定性枚举、固定一注。仍不使用随机数；刷新页面不会换号，只有新开奖数据或切换统计窗口才重算。</p>" +
      '<div class="intro-tags"><span>历史校准</span><span>逐号计算</span><span>固定一注</span><span>低共识</span></div>' +
      "</section>";
  }

  function latestHTML(a) {
    var game = a.game;
    var pool = a.last.pool || 0;
    var updated = formatTime(state.data && (state.data.updated || state.data.cachedAt));
    return '<section class="card draw-card">' +
      '<div class="draw-top"><div class="draw-title">' +
      '<div class="draw-issue"><span class="live-dot"></span>第 ' + escapeHtml(a.last.issue) + " 期" +
      '<span class="badge gray">' + escapeHtml(game.tag) + "</span></div>" +
      '<span class="draw-date">' + escapeHtml(a.last.date || "") + " 开奖</span></div>" +
      '<div class="countdown-box"><span class="countdown-label">距下期开奖</span>' +
      '<span class="countdown" data-countdown>--:--:--</span></div></div>' +
      '<div class="draw-numbers" role="img" aria-label="' + escapeHtml(game.name + "最新开奖号码") + '">' +
      latestBallsHTML(a) + "</div>" +
      '<div class="pool-line">' +
      (pool ? "<span>奖池 <b>" + escapeHtml(formatMoney(pool)) + "</b></span>" : "") +
      "<span>更新 <b>" + escapeHtml(updated) + "</b></span>" +
      '<span data-refresh-countdown>60 秒后检查</span></div></section>';
  }

  function finalHTML(reco) {
    var game = GAMES[reco.gameId];
    var a = reco.analysis;
    var set = reco.sets[0];
    var mainInfo = a.mainInfo;
    var specialInfo = a.specialInfo || {};
    var mainClass = game.id === "dlt" ? "orange" : "red";
    var spClass = "blue";

    var mainBalls = set.primary.map(function (n) {
      return ballWithTag(n, mainClass, mainInfo[n], two(n));
    }).join("");
    var specialBalls = set.special.map(function (n) {
      return ballWithTag(n, spClass, specialInfo[n], two(n));
    }).join("");

    var hot = 0, cold = 0, repeat = 0, neighbors = 0, diagonals = 0, gaps = 0;
    for (var fi = 0; fi < set.primary.length; fi++) {
      var fn = set.primary[fi];
      var ff = mainInfo[fn];
      var fs = a.signals[fn];
      if (ff.heat10 >= 0.7) hot += 1;
      if (ff.omit >= Math.max(5, ff.avgOmit * 1.5)) cold += 1;
      if (fs.repeat) repeat += 1;
      if (fs.neighbor) neighbors += 1;
      if (fs.diagonal) diagonals += 1;
      if (fs.gap5) gaps += 1;
    }

    return '<section class="card final-card">' +
      '<div class="card-head"><div class="card-title"><span class="icon">✦</span>固定一注</div>' +
      '<span class="badge">当前数据固定</span></div>' +
      '<div class="anti-hero">' +
      '<div class="anti-score-wrap"><span class="anti-score">' + set.anti + '<small>/100</small></span>' +
      '<span class="anti-score-label">反共识度</span></div>' +
      '<div class="anti-metrics">' +
      '<div><div class="metric-head"><span>平均共识分</span><b>' + set.avg + "/100</b></div>" +
      '<div class="metric-bar risk"><i style="width:' + Math.round(set.avg) + '%"></i></div></div>' +
      '<div><div class="metric-head"><span>历史贴合度</span><b>' + set.fit.toFixed(1) + "</b></div>" +
      '<div class="metric-bar"><i style="width:' + Math.min(100, Math.max(0, set.fit)) + '%"></i></div></div>' +
      "</div></div>" +
      '<div class="final-balls"><div class="balls">' + mainBalls + "</div>" +
      (specialBalls ? '<div class="final-special"><span class="label">' + escapeHtml(game.specialLabel) + "</span>" + specialBalls + "</div>" : "") +
      "</div>" +
      '<div class="anti-facts">' +
      "<span>热号 <b>" + hot + "</b></span><span>高遗漏 <b>" + cold + "</b></span>" +
      "<span>重号 <b>" + repeat + "</b></span><span>邻号 <b>" + neighbors + "</b></span>" +
      "<span>斜连 <b>" + diagonals + "</b></span><span>空档 <b>" + gaps + "</b></span>" +
      "</div>" +
      '<div class="rec-foot"><button class="btn btn-primary" type="button" data-action="calc">查看每个号码的计算</button>' +
      '<div class="auto-line"><span class="dot"></span><span>当前数据下固定<br>开奖后自动重算</span></div></div>' +
      '<p class="anti-note">本注由每个号码的走势共识分单独计算，再对所有候选组合做确定性排序选出；不随点击变化。只有新开奖数据或切换统计窗口才会重算。</p>' +
      "</section>";
  }

  function calcTableHTML(title, pool, info, signals, selected) {
    var rows = pool.slice().sort(function (x, y) {
      return info[x].consensus - info[y].consensus || x - y;
    }).map(function (n) {
      var f = info[n];
      var p = f.parts;
      var isSel = selected.indexOf(n) >= 0;
      return '<tr class="' + (isSel ? "calc-selected" : "") + '">' +
        "<td>" + f.rank + "</td>" +
        '<td class="calc-num">' + two(n) + "</td>" +
        "<td>" + p.hot10.toFixed(2) + "</td>" +
        "<td>" + p.hot30.toFixed(2) + "</td>" +
        "<td>" + p.omit.toFixed(2) + "</td>" +
        "<td>" + p.repeat.toFixed(2) + "</td>" +
        "<td>" + p.neighbor.toFixed(2) + "</td>" +
        "<td>" + p.diagonal.toFixed(2) + "</td>" +
        "<td>" + p.zone.toFixed(2) + "</td>" +
        "<td>" + p.tail.toFixed(2) + "</td>" +
        '<td class="calc-total">' + Math.round(f.consensus) + "</td>" +
        "<td>" + (isSel ? "入选" : "") + "</td></tr>";
    }).join("");
    return '<div class="calc-sub">' + escapeHtml(title) + "</div>" +
      '<div class="calc-scroll"><table class="calc-table"><thead><tr>' +
      "<th>排名</th><th>号码</th><th>热10</th><th>热30</th><th>遗漏</th><th>重号</th><th>邻号</th><th>斜连</th><th>区间</th><th>尾数</th><th>共识</th><th>结果</th>" +
      "</tr></thead><tbody>" + rows + "</tbody></table></div>";
  }

  function calcHTML(reco) {
    var a = reco.analysis;
    var set = reco.sets[0];
    var html = '<section class="card calc-card">' +
      '<div class="card-head"><div class="card-title"><span class="icon">∑</span>逐号计算明细</div>' +
      '<span class="badge">确定性 · 无随机</span></div>' +
      '<p class="hint-text">每个号码先单独计算共识分；分数越低越反共识。候选池 = 共识分最低的 16 个号码 + 重号/邻号/斜连配额 8 个（不让常见形态整体挤出），枚举所有组合后按“共识分 + 历史形态分布校准”排序取第一注，不使用随机数。</p>' +
      '<div class="formula-line">共识分 = 100 × (0.39×热10 + 0.18×热30 + 0.22×遗漏 + 0.04×重号 + 0.04×邻号 + 0.03×斜连 + 0.06×区间 + 0.04×尾数)</div>' +
      calcTableHTML(a.game.mainLabel, a.mainPool, a.mainInfo, a.signals, set.primary);
    if (a.specialInfo) {
      html += calcTableHTML(a.game.specialLabel, a.specialPool, a.specialInfo, a.specialSignals, set.special);
    }
    html += "</section>";
    return html;
  }

  function sumChartHTML(a) {
    var sums = a.sums.slice(0, 30).reverse();
    if (sums.length < 2) return "";
    var W = 340, H = 132, pl = 27, pr = 10, pt = 12, pb = 20;
    var min = Math.min.apply(null, sums), max = Math.max.apply(null, sums);
    var avg = mean(sums);
    var span = max - min || 1;
    function x(i) { return pl + i * (W - pl - pr) / (sums.length - 1); }
    function y(v) { return H - pb - (v - min) / span * (H - pt - pb); }
    var pts = [];
    for (var i = 0; i < sums.length; i++) pts.push([x(i), y(sums[i])]);
    var path = "M" + pts.map(function (p) { return p[0].toFixed(1) + " " + p[1].toFixed(1); }).join(" L");
    var area = path + " L" + pts[pts.length - 1][0].toFixed(1) + " " + (H - pb) +
      " L" + pts[0][0].toFixed(1) + " " + (H - pb) + " Z";
    var dots = pts.map(function (p, idx) {
      return '<circle cx="' + p[0].toFixed(1) + '" cy="' + p[1].toFixed(1) + '" r="2.1" fill="#ff9b92"/>';
    }).join("");
    var first = a.draws[Math.min(sums.length - 1, a.draws.length - 1)] || a.last;
    var last = a.last;
    return '<div class="sum-chart"><svg viewBox="0 0 340 132" role="img" aria-label="近30期和值走势">' +
      '<defs><linearGradient id="sumfill-' + escapeHtml(a.gameId) + '" x1="0" y1="0" x2="0" y2="1">' +
      '<stop offset="0%" stop-color="#ff7a6d" stop-opacity="0.28"/><stop offset="100%" stop-color="#ff7a6d" stop-opacity="0"/>' +
      "</linearGradient></defs>" +
      '<line x1="' + pl + '" y1="' + (H - pb) + '" x2="' + (W - pr) + '" y2="' + (H - pb) + '" stroke="rgba(255,255,255,.08)" stroke-width="1"/>' +
      '<line x1="' + pl + '" y1="' + y(avg).toFixed(1) + '" x2="' + (W - pr) + '" y2="' + y(avg).toFixed(1) + '" stroke="#ffb454" stroke-width="1" stroke-dasharray="4 3" opacity=".7"/>' +
      '<path d="' + area + '" fill="url(#sumfill-' + escapeHtml(a.gameId) + ')"/>' +
      '<path d="' + path + '" fill="none" stroke="#ff7a6d" stroke-width="2" stroke-linejoin="round"/>' + dots +
      '<text x="' + pl + '" y="' + (y(max) - 4).toFixed(1) + '" fill="#98a3ba" font-size="7">' + max + "</text>" +
      '<text x="' + pl + '" y="' + (y(min) + 10).toFixed(1) + '" fill="#98a3ba" font-size="7">' + min + "</text>" +
      '<text x="' + (W - pr) + '" y="' + (H - 5) + '" fill="#6d7891" font-size="7" text-anchor="end">' + escapeHtml(shortIssue(last.issue)) + "</text>" +
      '<text x="' + pl + '" y="' + (H - 5) + '" fill="#6d7891" font-size="7">' + escapeHtml(shortIssue(first.issue)) + "</text>" +
      "</svg></div>";
  }

  function trendMatrixHTML(a) {
    var max = a.game.mainMax;
    var rows = a.draws.slice(0, 15);
    var head = '<div class="trend-row head"><span class="trend-issue">期</span>';
    for (var n = 1; n <= max; n++) head += '<span class="trend-cell">' + (n % 5 === 0 ? n : "") + "</span>";
    head += '<span class="trend-special">' + (a.game.id === "ssq" ? "蓝" : "后") + "</span></div>";
    var body = rows.map(function (d) {
      var main = E.mainNumbers(a.game, d);
      var special = E.specialNumbers(a.game, d);
      var row = '<div class="trend-row"><span class="trend-issue">' + escapeHtml(shortIssue(d.issue)) + "</span>";
      for (var i = 1; i <= max; i++) {
        row += '<span class="trend-cell' + (main.indexOf(i) >= 0 ? " hit" : "") +
          '" title="' + escapeHtml(d.issue + " · " + i) + '"></span>';
      }
      row += '<span class="trend-special">' + special.map(function (s) { return "<i>" + two(s) + "</i>"; }).join("") + "</span></div>";
      return row;
    }).join("");
    return '<div class="trend-scroll"><div class="trend-table" style="--cols:' + max + '">' + head + body + "</div></div>" +
      '<div class="trend-legend"><span><i></i>主区开出</span><span><i class="blue"></i>' +
      escapeHtml(a.game.specialLabel) + "开出</span><span>横向滑动查看全部号码</span></div>";
  }

  function formTableHTML(a) {
    var rows = a.formRows.map(function (r) {
      return "<tr><td class=\"issue\">" + escapeHtml(r.issue) + "</td><td>" + r.sum + "</td><td>" +
        r.odd + ":" + r.even + "</td><td>" + r.big + ":" + r.small + "</td><td>" + r.zones +
        "</td><td>" + r.consecutive + "</td><td>" + r.repeat + "</td></tr>";
    }).join("");
    return '<div class="form-scroll"><table class="form-table"><thead><tr><th>期号</th><th>和值</th><th>奇偶</th>' +
      "<th>大小</th><th>三区</th><th>连号</th><th>重号</th></tr></thead><tbody>" + rows + "</tbody></table></div>";
  }

  function trendHTML(a) {
    return '<section class="card trend-card">' +
      '<div class="card-head"><div class="card-title"><span class="icon">◈</span>走势图</div>' +
      '<div class="segmented">' +
      '<button class="seg-btn' + (state.window === 30 ? " active" : "") + '" type="button" data-window="30">近30期</button>' +
      '<button class="seg-btn' + (state.window === 100 ? " active" : "") + '" type="button" data-window="100">近100期</button>' +
      "</div></div>" +
      '<div class="chart-box"><div class="chart-title"><b>和值走势</b><span>近 ' + Math.min(30, a.sums.length) + " 期</span></div>" +
      sumChartHTML(a) + "</div>" +
      '<div class="chart-box"><div class="chart-title"><b>号码分布走势</b><span>最近 15 期 · 滑动查看</span></div>' +
      trendMatrixHTML(a) + "</div>" +
      '<div class="chart-box"><div class="chart-title"><b>近期形态</b><span>和值 / 奇偶 / 大小 / 三区</span></div>' +
      formTableHTML(a) + "</div></section>";
  }

  function rulesHTML(reco) {
    var rules = buildRules(reco);
    var list = rules.map(function (r, i) {
      return '<li class="rule-item"><span class="rule-index">' + (i + 1) + "</span>" +
        '<div class="rule-body"><div class="rule-head"><b>' + escapeHtml(r.name) + "</b>" +
        '<span class="' + (r.ok ? "rule-ok" : "rule-warn") + '">' + (r.ok ? "✓ 校准" : "· 偏离历史") + "</span></div>" +
        '<p class="rule-bias">' + escapeHtml(r.bias) + "</p>" +
        '<p class="rule-current">' + r.current + "</p>" +
        '<p class="rule-action">' + escapeHtml(r.action) + "</p></div></li>";
    }).join("");
    return '<section class="card rules-card">' +
      '<div class="card-head"><div class="card-title"><span class="icon">◎</span>形态校准</div>' +
      '<span class="badge gray">v4 · 形态校准</span></div>' +
      '<div class="step-strip">' +
      "<div class=\"step\"><b>1. 读走势</b>热号、冷号、遗漏、区间、和值</div>" +
      "<div class=\"step\"><b>2. 统计形态</b>近100期真实出现率</div>" +
      "<div class=\"step\"><b>3. 固定选号</b>逐号计算 + 枚举组合</div></div>" +
      '<ul class="rules-list">' + list + "</ul></section>";
  }

  function consensusHTML(reco) {
    var a = reco.analysis;
    var set = reco.sets[0];
    var main = a.mainPool.slice().sort(function (x, y) {
      return a.mainInfo[x].consensus - a.mainInfo[y].consensus;
    });
    var mainChips = main.map(function (n) {
      var info = a.mainInfo[n];
      var selected = set.primary.indexOf(n) >= 0;
      return '<div class="consensus-chip' + (selected ? " selected" : "") + '">' +
        '<span class="consensus-num">' + two(n) + "</span>" +
        '<span class="consensus-bar"><i style="width:' + Math.round(info.consensus) + '%"></i></span>' +
        '<span class="consensus-score">' + Math.round(info.consensus) + "</span>" +
        '<span class="consensus-tags">' + escapeHtml(info.tags.slice(0, 2).join(" · ")) + "</span></div>";
    }).join("");

    var specialChips = "";
    if (a.specialInfo) {
      var sp = a.specialPool.slice().sort(function (x, y) {
        return a.specialInfo[x].consensus - a.specialInfo[y].consensus;
      });
      specialChips = sp.map(function (n) {
        var info = a.specialInfo[n];
        var selected = set.special.indexOf(n) >= 0;
        return '<div class="consensus-chip' + (selected ? " selected" : "") + '">' +
          '<span class="consensus-num">' + two(n) + "</span>" +
          '<span class="consensus-bar"><i style="width:' + Math.round(info.consensus) + '%"></i></span>' +
          '<span class="consensus-score">' + Math.round(info.consensus) + "</span>" +
          '<span class="consensus-tags">' + escapeHtml(info.tags.slice(0, 2).join(" · ")) + "</span></div>";
      }).join("");
    }

    return '<section class="card consensus-card">' +
      '<div class="card-head"><div class="card-title"><span class="icon">◉</span>走势共识榜</div>' +
      '<span class="badge">低共识 → 高共识</span></div>' +
      '<p class="hint-text">数值越低，表示越偏离模拟走势图彩民的偏好；这是走势策略共识，不是中奖概率。选中号码以红色边框标出。</p>' +
      '<div class="consensus-grid">' + mainChips + "</div>" +
      (specialChips ? '<div class="consensus-sub">' + escapeHtml(a.game.specialLabel) + "</div><div class=\"consensus-grid\">" + specialChips + "</div>" : "") +
      "</section>";
  }

  function aboutHTML() {
    return '<section class="card about-card">' +
      '<div class="card-head"><div class="card-title"><span class="icon">ⓘ</span>先把话说清楚</div><span class="badge gray">v4 · 形态校准</span></div>' +
      '<ul class="about-list">' +
      '<li><span class="bullet">1</span><div><b>每注概率相同</b>：双色球/大乐透的每一组号码中奖概率完全一样；反共识不能提高中奖概率，也不能保证“实际会中奖”。</div></li>' +
      '<li><span class="bullet">2</span><div><b>目标只是少分摊</b>：如果中奖，避开大众常用号码，可能减少与其他人同时中奖、分摊奖金的概率。它影响的是“撞号”，不是“中奖”。</div></li>' +
      '<li><span class="bullet">3</span><div><b>返奖率</b>：官方返奖率约 <b>51%</b>（奖金约 50% + 调节基金），不是 40%；浮动奖奖金会按中奖注数分摊，所以“销量高、奖金低”要区分返奖率与分摊。</div></li>' +
      '<li><span class="bullet">4</span><div><b>数据与走势</b>：使用福彩/体彩公开开奖数据，最近 30/100 期统计；走势图只描述过去，不预示未来。</div></li>' +
      '<li><span class="bullet">5</span><div><b>固定一注</b>：每个号码由走势因子逐项加权计算，组合用确定性枚举排序；刷新页面、重复点击不会换号，只有新开奖数据或切换统计窗口才重算。</div></li>' +
      "</ul>" +
      '<div class="optimization">' +
      '<div class="opt-title">v4 优化日志</div>' +
      '<div class="opt-row"><b>v1 问题</b>生日号 / 吉利号 / 尾4 权重过高，反选看起来刻意。</div>' +
      '<div class="opt-row"><b>v2 问题</b>改为走势图策略，但仍使用随机模拟和重新抽号，点击就换号。</div>' +
      '<div class="opt-row"><b>v3 问题</b>虽然固定一注，但仍把斜连/邻号/重号等常见形态当作“要回避”，逻辑不够贴近真实走势。</div>' +
      '<div class="opt-row"><b>v4 改动</b>统计近100期重号/邻号/斜连/连号/同尾/空档/空区/和值/奇偶/大小/跨度真实分布，组合评分按历史分布校准；斜连/邻号不再被当作“不可能”。</div>' +
      '<div class="opt-row"><b>v4 修正</b>形态不再“越接近 1 越好”：重号/邻号/斜连的逐号权重降到 0.04/0.04/0.03，不再把这类号码整体挤出候选池；候选池额外保留形态配额，形态数量只看是否落在历史常见区间（斜连 0 个或 1 个都正常）。</div>' +
      '<div class="opt-row"><b>下一步</b>根据反馈调整各走势因子的权重，持续迭代。</div>' +
      '</div>' +
      '<div class="rate-note">反共识、冷热、遗漏、连号、同尾都不是“必开信号”。走势图可以用来看，但不能用来承诺结果。</div>' +
      '<div class="about-links"><a href="https://www.cwl.gov.cn/" target="_blank" rel="noopener">中国福利彩票</a>' +
      '<a href="https://www.sporttery.cn/" target="_blank" rel="noopener">中国体育彩票</a>' +
      '<a href="https://xiaomayi1899.github.io/lucky-numbers/">开奖与推荐</a></div>' +
      '<div class="disclaimer">理性购彩，量力而行。未满 18 周岁禁止购买彩票。本页仅提供公开开奖信息与娱乐性号码组合，不提供购彩、代购或兑奖服务。</div>' +
      "</section>";
  }

  function render() {
    if (!dom.main) return;
    renderTabs();
    var game = GAMES[state.active];
    if (!drawsFor(state.active).length) {
      dom.main.innerHTML = '<section class="card empty-card"><h2>正在获取开奖数据</h2>' +
        "<p>第一次打开需要联网载入，请稍候或点右上角刷新。</p>" +
        '<button class="btn btn-ghost" type="button" data-retry style="margin-top:14px">重新加载</button></section>' + introHTML();
      return;
    }
    var reco = ensureReco();
    if (!reco) return;
    var a = reco.analysis;
    var notice = state.online === false
      ? '<div class="notice"><span class="n-dot"></span><span>网络暂时不可用，正在显示本地缓存。网络恢复后会自动同步。</span></div>'
      : "";
    dom.main.innerHTML = notice + introHTML() + latestHTML(a) + finalHTML(reco) + calcHTML(reco) +
      trendHTML(a) + patternHTML(a) + rulesHTML(reco) + consensusHTML(reco) + aboutHTML();
    tick();
  }

  /* ---------------- 计时与事件 ---------------- */

  function tick() {
    var gameId = state.active;
    var countdownEls = $$("[data-countdown]");
    if (countdownEls.length) {
      var remain = E.nextDraw(gameId) - Date.now();
      var text = E.formatDuration(remain);
      countdownEls.forEach(function (el) {
        el.textContent = text;
        el.classList.toggle("near", remain > 0 && remain < 10 * 60 * 1000);
      });
    }
    var fetchEls = $$("[data-refresh-countdown]");
    if (fetchEls.length) {
      var secs = Math.max(0, Math.ceil((state.nextFetch - Date.now()) / 1000));
      fetchEls.forEach(function (el) { el.textContent = secs + " 秒后检查"; });
    }
  }

  var toastTimer = 0;
  function toast(msg) {
    if (!dom.toast) return;
    dom.toast.textContent = msg;
    dom.toast.classList.add("show");
    clearTimeout(toastTimer);
    toastTimer = window.setTimeout(function () { dom.toast.classList.remove("show"); }, 2200);
  }

  function copyText(text) {
    function fallback() {
      var ta = document.createElement("textarea");
      ta.value = text;
      ta.setAttribute("readonly", "");
      ta.style.position = "fixed";
      ta.style.top = "-1000px";
      document.body.appendChild(ta);
      ta.select();
      var ok = false;
      try { ok = document.execCommand("copy"); } catch (e) { ok = false; }
      document.body.removeChild(ta);
      toast(ok ? "已复制：" + text : "复制失败，请长按号码手动复制");
    }
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(function () { toast("已复制：" + text); }).catch(fallback);
    } else {
      fallback();
    }
  }

  function bind() {
    dom.refreshBtn.addEventListener("click", function () { fetchData(true); });

    dom.tabs.addEventListener("click", function (e) {
      var btn = e.target.closest("[data-game]");
      if (!btn) return;
      var id = btn.getAttribute("data-game");
      if (!GAMES[id] || id === state.active) return;
      state.active = id;
      save(LS_GAME, id);
      state.reco = null;
      render();
      window.scrollTo({ top: 0, behavior: "smooth" });
      try { btn.scrollIntoView({ behavior: "smooth", inline: "center", block: "nearest" }); } catch (err) { /* ignore */ }
    });

    dom.main.addEventListener("click", function (e) {
      var copyBtn = e.target.closest("[data-copy]");
      if (copyBtn) { copyText(copyBtn.getAttribute("data-copy")); return; }
      var winBtn = e.target.closest("[data-window]");
      if (winBtn) {
        var w = Number(winBtn.getAttribute("data-window"));
        if (w !== state.window) {
          state.window = w;
          save(LS_WINDOW, String(w));
          state.reco = null;
          render();
          toast("统计窗口已切换为近 " + w + " 期");
        }
        return;
      }
      var action = e.target.closest("[data-action]");
      if (action && action.getAttribute("data-action") === "calc") {
        var calc = document.querySelector(".calc-card");
        if (calc) calc.scrollIntoView({ behavior: "smooth", block: "start" });
        return;
      }
      if (e.target.closest("[data-retry]")) fetchData(true);
    });

    document.addEventListener("visibilitychange", function () {
      if (document.visibilityState === "visible") {
        if (Date.now() >= state.nextFetch - 5000) fetchData(false);
        tick();
      }
    });
    window.addEventListener("online", function () { fetchData(false); });
    window.addEventListener("offline", function () { setOnline(false); });
  }

  function registerSW() {
    if (!("serviceWorker" in navigator)) { dom.swState.textContent = "浏览器不支持离线缓存"; return; }
    var secure = location.protocol === "https:" || location.hostname === "localhost" || location.hostname === "127.0.0.1";
    if (!secure) { dom.swState.textContent = "需 https 才能离线"; return; }
    navigator.serviceWorker.register("sw.js").then(function (reg) {
      dom.swState.textContent = "离线缓存已就绪";
      window.setInterval(function () { reg.update(); }, 30 * 60 * 1000);
    }).catch(function (err) {
      dom.swState.textContent = "离线缓存未启用";
      console.warn("SW register failed", err);
    });
  }

  function init() {
    dom.main = $("#main");
    dom.tabs = $("#tabs");
    dom.refreshBtn = $("#refreshBtn");
    dom.netDot = $("#netDot");
    dom.toast = $("#toast");
    dom.swState = $("#swState");

    var g = read(LS_GAME);
    if (g && GAMES[g] && ORDER.indexOf(g) >= 0) state.active = g;
    var w = Number(read(LS_WINDOW));
    if (w === 30 || w === 100) state.window = w;
    state.nextFetch = Date.now() + REFRESH_MS;

    loadCache();
    renderTabs();
    render();
    bind();
    registerSW();
    setOnline(null);
    fetchData(false);
    window.setInterval(function () {
      if (document.visibilityState === "visible" && Date.now() >= state.nextFetch) fetchData(false);
    }, 5000);
    window.setInterval(tick, 1000);
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", init);
  else init();
})();
