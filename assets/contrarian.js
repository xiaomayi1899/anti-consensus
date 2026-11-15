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
      var trend = 0.30 * (heat10Norm[v] || 0) +
        0.15 * (heat30Norm[v] || 0) +
        0.18 * (omitNorm[v] || 0) +
        0.10 * repeat +
        0.10 * neighbor +
        0.10 * diagonal +
        0.04 * zoneHeat +
        0.03 * tailHeat;
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
        hot10: 0.30 * s.hot10,
        hot30: 0.15 * s.hot30,
        omit: 0.18 * s.omitNorm,
        repeat: 0.10 * s.repeat,
        neighbor: 0.10 * s.neighbor,
        diagonal: 0.10 * s.diagonal,
        zone: 0.04 * s.zoneHeat,
        tail: 0.03 * s.tailHeat,
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
      zoneCuts: cuts, bigCut: cutBig,
    };
  }

  /* ---------------- 反共识评分 ---------------- */

  function combinationRaw(nums, a) {
    var k = nums.length;
    var info = a.mainInfo;
    var signals = a.signals;
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
    var idealOdd = k / 2, idealBig = k / 2, idealZone = k / zones.length;
    var zoneDev = 0;
    for (var z = 0; z < zones.length; z++) zoneDev += Math.abs(zones[z] - idealZone);
    var sumZ = Math.abs(sum(nums) - a.meanSum) / (a.stdSum || 1);
    var repeat = intersection(nums, a.lastMain).length;
    var consec = consecutivePairs(nums);
    var tails = sameTailPairs(nums);
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

    return 0.42 * avgConsensus +
      12 * Math.exp(-sumZ * sumZ / 2) +
      10 * clamp(1 - Math.abs(odd - idealOdd) / k, 0, 1) +
      8 * clamp(1 - Math.abs(big - idealBig) / k, 0, 1) +
      10 * clamp(1 - zoneDev / k, 0, 1) +
      12 * Math.exp(-Math.pow(repeat - 1, 2)) +
      8 * Math.exp(-Math.pow(neighbors - 1, 2)) +
      8 * Math.exp(-Math.pow(diagonals - 1, 2)) +
      5 * Math.exp(-Math.pow(hot - 2, 2)) +
      5 * Math.exp(-Math.pow(cold - 1, 2)) +
      4 * Math.exp(-Math.pow(gaps - 1, 2)) +
      4 * Math.exp(-Math.pow(consec - 1, 2)) +
      3 * Math.exp(-Math.pow(tails - 1, 2)) -
      10 * emptyZones +
      (cold > 2 ? (cold - 2) * 8 : 0) +
      (neighbors > 2 ? (neighbors - 2) * 6 : 0) +
      (gaps > 2 ? (gaps - 2) * 4 : 0) +
      penalty;
  }

  function buildCandidates(a) {
    var pool = a.mainPool;
    var k = a.game.mainCount;
    var sorted = pool.slice().sort(function (x, y) {
      return a.mainInfo[x].consensus - a.mainInfo[y].consensus || x - y;
    });
    var top = sorted.slice(0, Math.min(16, sorted.length));
    var lastKey = a.lastMain.slice().sort(function (x, y) { return x - y; }).join(",");
    var out = [], chosen = [];

    function rec(start) {
      if (chosen.length === k) {
        var nums = chosen.slice().sort(function (x, y) { return x - y; });
        var key = nums.join(",");
        if (key === lastKey) return;
        out.push({ nums: nums, key: key, raw: combinationRaw(nums, a) });
        return;
      }
      for (var i = start; i < top.length; i++) {
        if (top.length - i < k - chosen.length) break;
        chosen.push(top[i]);
        rec(i + 1);
        chosen.pop();
      }
    }
    rec(0);
    out.sort(function (x, y) {
      return x.raw - y.raw || x.key.localeCompare(y.key);
    });
    if (!out.length) {
      var fallback = top.slice(0, k).sort(function (x, y) { return x - y; });
      out.push({ nums: fallback, key: fallback.join(","), raw: combinationRaw(fallback, a) });
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
    var zoneMax = Math.max.apply(null, zones);
    var emptyZones = zones.filter(function (z) { return z === 0; }).length;
    var total = sum(nums);
    var sumZ = Math.abs(total - a.meanSum) / (a.stdSum || 1);
    var span = nums[nums.length - 1] - nums[0];
    var consec = consecutivePairs(nums);
    var tails = sameTailPairs(nums);
    var fullSpan = a.game.mainMax - a.game.mainMin;

    return [
      { name: "热号追踪", bias: "看走势图的彩民会追近 10 期热号，越热越敢追。", current: "本注含近10期热号 <b>" + hot + "</b> 个。", action: "反选：热号不超过 1 个。", ok: hot <= 1 },
      { name: "冷号回补", bias: "长期未出的号码被当作“该回补了”，冷号也有追随者。", current: "本注含高遗漏 <b>" + cold + "</b> 个。", action: "反选：保留 1-2 个，不追极端。", ok: cold >= 1 && cold <= 2 },
      { name: "上期重号", bias: "走势图派常从上期号码里留 1 个重号。", current: "本注含上期重号 <b>" + repeat + "</b> 个。", action: "反选：0-1 个重号。", ok: repeat <= 1 },
      { name: "邻号延伸", bias: "上期号码的 ±1 邻号是常见走势选号。", current: "本注含邻号 <b>" + neighbors + "</b> 个。", action: "反选：邻号不超过 1 个。", ok: neighbors <= 1 },
      { name: "斜连走势", bias: "走势图上 05→06→07 的斜连会被追。", current: "本注含斜连号 <b>" + diagonals + "</b> 个。", action: "反选：斜连 0-1 个。", ok: diagonals <= 1 },
      { name: "连号形态", bias: "彩民常按“连号该出了/不该出了”选 1 组连号。", current: "本注有 <b>" + consec + "</b> 组连号。", action: "反选：保留 1 组。", ok: consec === 1 },
      { name: "同尾走势", bias: "同尾号（05/15/25）是走势图常见观察点。", current: "本注有 <b>" + tails + "</b> 组同尾。", action: "反选：允许 0-1 组。", ok: tails <= 1 },
      { name: "区间轮动", bias: "彩民会根据近期哪个区热，集中选该区。", current: "三区 <b>" + zones.join(":") + "</b>，空区 <b>" + emptyZones + "</b> 个。", action: "反选：允许空区/偏态。", ok: emptyZones >= 1 || zoneMax >= Math.ceil(k / zones.length) + 1 },
      { name: "和值回归", bias: "彩民倾向选接近近 30 期均值和的组合。", current: "和值 <b>" + total + "</b>，偏离 <b>" + sumZ.toFixed(1) + "σ</b>。", action: "反选：允许偏离均值。", ok: sumZ >= 0.8 },
      { name: "奇偶均衡", bias: "3:3、2:4 等均衡奇偶是大众偏好。", current: "奇偶 <b>" + odd + ":" + (k - odd) + "</b>。", action: "反选：允许偏态。", ok: Math.abs(odd - k / 2) >= 1 },
      { name: "大小均衡", bias: "大小号均衡分布是常见组合习惯。", current: "大小 <b>" + big + ":" + (k - big) + "</b>。", action: "反选：允许偏态。", ok: Math.abs(big - k / 2) >= 1 },
      { name: "空档回补", bias: "走势图上的空档区会被认为“该补了”。", current: "本注含近5期空档 <b>" + gaps + "</b> 个。", action: "反选：保留 1-2 个。", ok: gaps >= 1 && gaps <= 2 },
      { name: "跨度选择", bias: "彩民常避开极大/极小跨度，偏好中等跨度。", current: "跨度 <b>" + span + "</b>。", action: "反选：允许大/小跨度。", ok: span > fullSpan * 0.55 || span < fullSpan * 0.35 },
      { name: "热尾轮动", bias: "近期热尾会被追，冷尾被忽略。", current: "本注含热尾 <b>" + hotTails + "</b> 个。", action: "反选：热尾不超过 1 个。", ok: hotTails <= 1 },
    ];
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
      '<div class="intro-eyebrow">V3 · FIXED CALC</div>' +
      "<h2>每个号码单独计算，固定一注</h2>" +
      "<p>先按走势图给每个号码逐项打分：热号、近30热度、遗漏、重号、邻号、斜连、区间、尾数；再把共识分最低的 16 个号码枚举所有组合，按组合得分排序，固定选出第一注。不使用随机数，点击页面不会换号；只有新开奖数据或切换统计窗口才会重算。</p>" +
      '<div class="intro-tags"><span>逐号计算</span><span>确定性</span><span>固定一注</span><span>低共识</span></div>' +
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
      '<div><div class="metric-head"><span>组合计算得分</span><b>' + set.raw.toFixed(1) + "</b></div>" +
      '<div class="metric-bar"><i style="width:' + Math.min(100, Math.max(0, set.raw)) + '%"></i></div></div>' +
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
      '<p class="hint-text">每个号码先单独计算共识分；分数越低越反共识。最终一注从共识分最低的 16 个号码中枚举所有组合，按组合得分从低到高排序取第一注，不使用随机数。</p>' +
      '<div class="formula-line">共识分 = 100 × (0.30×热10 + 0.15×热30 + 0.18×遗漏 + 0.10×重号 + 0.10×邻号 + 0.10×斜连 + 0.04×区间 + 0.03×尾数)</div>' +
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
        '<span class="' + (r.ok ? "rule-ok" : "rule-warn") + '">' + (r.ok ? "✓ 已反选" : "· 仍偏大众") + "</span></div>" +
        '<p class="rule-bias">' + escapeHtml(r.bias) + "</p>" +
        '<p class="rule-current">' + r.current + "</p>" +
        '<p class="rule-action">' + escapeHtml(r.action) + "</p></div></li>";
    }).join("");
    return '<section class="card rules-card">' +
      '<div class="card-head"><div class="card-title"><span class="icon">◎</span>走势图策略</div>' +
      '<span class="badge gray">v3 · 固定计算</span></div>' +
      '<div class="step-strip">' +
      "<div class=\"step\"><b>1. 读走势</b>热号、冷号、遗漏、区间、和值</div>" +
      "<div class=\"step\"><b>2. 逐号计算</b>每个号码单独打分</div>" +
      "<div class=\"step\"><b>3. 固定选号</b>枚举组合，取最低分</div></div>" +
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
      '<div class="card-head"><div class="card-title"><span class="icon">ⓘ</span>先把话说清楚</div><span class="badge gray">v3 · 固定计算</span></div>' +
      '<ul class="about-list">' +
      '<li><span class="bullet">1</span><div><b>每注概率相同</b>：双色球/大乐透的每一组号码中奖概率完全一样；反共识不能提高中奖概率，也不能保证“实际会中奖”。</div></li>' +
      '<li><span class="bullet">2</span><div><b>目标只是少分摊</b>：如果中奖，避开大众常用号码，可能减少与其他人同时中奖、分摊奖金的概率。它影响的是“撞号”，不是“中奖”。</div></li>' +
      '<li><span class="bullet">3</span><div><b>返奖率</b>：官方返奖率约 <b>51%</b>（奖金约 50% + 调节基金），不是 40%；浮动奖奖金会按中奖注数分摊，所以“销量高、奖金低”要区分返奖率与分摊。</div></li>' +
      '<li><span class="bullet">4</span><div><b>数据与走势</b>：使用福彩/体彩公开开奖数据，最近 30/100 期统计；走势图只描述过去，不预示未来。</div></li>' +
      '<li><span class="bullet">5</span><div><b>固定一注</b>：每个号码由走势因子逐项加权计算，组合用确定性枚举排序；刷新页面、重复点击不会换号，只有新开奖数据或切换统计窗口才重算。</div></li>' +
      "</ul>" +
      '<div class="optimization">' +
      '<div class="opt-title">v3 优化日志</div>' +
      '<div class="opt-row"><b>v1 问题</b>生日号 / 吉利号 / 尾4 权重过高，反选看起来刻意。</div>' +
      '<div class="opt-row"><b>v2 问题</b>改为走势图策略，但仍使用随机模拟和重新抽号，点击就换号。</div>' +
      '<div class="opt-row"><b>v3 改动</b>去掉随机模拟与重新抽号；每个号码单独加权计算共识分，组合用确定性枚举排序，固定一注。</div>' +
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
      trendHTML(a) + rulesHTML(reco) + consensusHTML(reco) + aboutHTML();
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
