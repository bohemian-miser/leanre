/* leanre interactive zoomable nested-rectangle proof treemap explorer & draft PR composer.
 *
 * Reads static `leanre.treemap/1` exports (`manifest.json`, `dom.lxrt`, `folder.lxrt`,
 * lazy `tiles_<view>/{id}.lxrt`, and optional `overlay.json`) and exposes:
 *   - window.LeanreTreemap.renderExplorer(host, opts)
 *   - window.LeanreTreemap.runSelfTest(assert, opts)
 *   - window.LeanreTreemap.squarify(items, rect)
 *   - window.LeanreTreemap.buildDraftJsonl(input)
 *   - window.LeanreTreemap.validateDraft(input)
 *   - window.LeanreTreemap.SCHEMA
 *
 * Safety: DOM is constructed solely with document.createElement / textContent /
 * setAttribute. No innerHTML, no eval, no external network requests.
 *
 * License: AGPL-3.0-or-later
 */
(function (root) {
  "use strict";

  const VERSION = "1.0.0";
  const SCHEMA = "leanre.treemap/1";
  const TREE_SCHEMA = "leanre.treemap.tree/1";
  const OVERLAY_SCHEMA = "leanre.treemap.overlay/1";
  const ANNOT_SCHEMA = "leanre.annot/1";

  const DEFAULT_TOOL_REPO = "https://github.com/bohemian-miser/leanre";
  const TILE_LRU_CAP = 64;
  const MAX_GH_NEW_URL_LEN = 7000;
  const MAX_VISIBLE_DEPTH = 4;
  const SIGHASH_RX = /^[a-z][a-z0-9._-]{0,31}:[0-9a-f]{16,128}$/;
  const PINNED_GH_LINE_RX = /^https:\/\/github\.com\/[A-Za-z0-9-]+\/[A-Za-z0-9._-]+\/blob\/[0-9a-f]{7,40}\/[^#\s]+#L\d+(?:-L\d+)?$/i;
  const FLOATING_GH_RX = /^https?:\/\/github\.com\/[^/]+\/[^/]+\/blob\/(?:main|master|HEAD)\//i;
  const OVERCLAIM_RX = /\b(RH is proved|proves RH|proved the Riemann Hypothesis|proves the Riemann Hypothesis|Riemann Hypothesis is proved|proves Navier[- ]Stokes|Navier[- ]Stokes is proved|Navier[- ]Stokes is solved)\b/i;
  const XSS_MARKUP_RX = /<\s*script\b|<\s*iframe\b|<\s*object\b|<\s*embed\b|javascript\s*:|\bon(?:error|load|click|mouseover|focus)\s*=/i;
  const LEAN_PASTE_RX = /:=[ \t]*by\b|^\s*import\s+[A-Z][\w.]*/m;
  const LEAN_MULTI_LINE_RX = /^\s*(?:theorem|lemma|def|instance|structure|inductive|by|have|let|rw|simp|exact|apply|intro|cases|induction)\b/;
  const CTRL_RX = /[\x00-\x08\x0b-\x1f\x7f\u2028\u2029]/;

  // Publication-grade muted palette matching site.css / MAP_PALETTE
  const PILLAR_PALETTE_DARK = [
    "#5b99b8", "#4d9e77", "#b88642", "#9678c4", "#3d998d",
    "#688bc4", "#ad8d49", "#6c7687", "#b85c60", "#6da668"
  ];
  const PILLAR_PALETTE_LIGHT = [
    "#2f7699", "#247d54", "#9c6216", "#6f49ad", "#187368",
    "#3c64a8", "#85621e", "#5b6472", "#a8383e", "#3d7a39"
  ];

  const hasDoc = typeof document !== "undefined";
  const utf8Dec = typeof TextDecoder !== "undefined" ? new TextDecoder("utf-8") : null;

  // ---------------------------------------------------------------------------
  // Formatting & small helpers
  // ---------------------------------------------------------------------------
  function fmtInt(n) {
    if (n == null || !isFinite(n)) return "–";
    return Math.round(Number(n)).toLocaleString("en-US");
  }

  function fmtCompact(n) {
    const v = Number(n);
    if (!isFinite(v)) return "–";
    if (Math.abs(v) >= 1e6) return (v / 1e6).toFixed(2).replace(/\.00$/, "") + "M";
    if (Math.abs(v) >= 1e3) return (v / 1e3).toFixed(1).replace(/\.0$/, "") + "K";
    return String(Math.round(v));
  }

  function fmtPct(frac) {
    if (frac == null || !isFinite(frac)) return "0.0%";
    return (Number(frac) * 100).toFixed(1) + "%";
  }

  function clamp(v, lo, hi) {
    return v < lo ? lo : v > hi ? hi : v;
  }

  function shortName(name) {
    const s = String(name || "");
    const parts = s.split(".");
    if (parts.length < 2) return s;
    let last = parts[parts.length - 1];
    if (/^_/.test(last) && parts.length >= 3) {
      last = parts[parts.length - 2] + "." + last;
    }
    return last || s;
  }

  function safeHref(u) {
    const s = String(u == null ? "" : u).trim();
    if (!s) return null;
    if (s.startsWith("#") || s.startsWith("./") || s.startsWith("/")) return s;
    try {
      const parsed = new URL(s);
      if (parsed.protocol === "https:" || parsed.protocol === "http:") return parsed.href;
    } catch (_) {
      return null;
    }
    return null;
  }

  function h(tag, attrs, children) {
    const node = document.createElement(tag);
    if (attrs) {
      for (const k of Object.keys(attrs)) {
        const v = attrs[k];
        if (v == null || v === false) continue;
        if (k === "className" || k === "class") node.className = String(v);
        else if (k === "textContent") node.textContent = String(v);
        else if (k === "value") node.value = String(v);
        else if (k === "checked") node.checked = Boolean(v);
        else if (k === "disabled") node.disabled = Boolean(v);
        else if (k.startsWith("on") && typeof v === "function") node.addEventListener(k.slice(2).toLowerCase(), v);
        else if (v === true) node.setAttribute(k, "");
        else node.setAttribute(k, String(v));
      }
    }
    if (children != null) {
      const list = Array.isArray(children) ? children : [children];
      for (const ch of list) {
        if (ch == null || ch === false) continue;
        if (typeof ch === "string" || typeof ch === "number") {
          node.appendChild(document.createTextNode(String(ch)));
        } else {
          node.appendChild(ch);
        }
      }
    }
    return node;
  }

  function clearEl(node) {
    while (node && node.firstChild) node.removeChild(node.firstChild);
  }

  function identWbr(name) {
    const s = String(name || "");
    const parts = s.split(/([._])/);
    const frag = document.createDocumentFragment();
    for (const p of parts) {
      if (!p) continue;
      frag.appendChild(document.createTextNode(p));
      if (p === "." || p === "_") frag.appendChild(document.createElement("wbr"));
    }
    return frag;
  }

  function isLightTheme() {
    if (!hasDoc) return false;
    return document.documentElement.getAttribute("data-theme") === "light";
  }

  function cssVar(name, fallback) {
    if (!hasDoc) return fallback;
    try {
      const v = getComputedStyle(document.documentElement).getPropertyValue(name).trim();
      return v || fallback;
    } catch (_) {
      return fallback;
    }
  }

  // ---------------------------------------------------------------------------
  // Color utilities (WCAG luminance + smooth ramps)
  // ---------------------------------------------------------------------------
  function hexToRgb(hex) {
    const s = String(hex || "").trim();
    if (s.startsWith("rgb")) {
      const m = s.match(/(\d+)\s*,\s*(\d+)\s*,\s*(\d+)/);
      return m ? [Number(m[1]), Number(m[2]), Number(m[3])] : [90, 100, 118];
    }
    const clean = s.replace(/^#/, "");
    if (clean.length === 3) {
      return [
        parseInt(clean[0] + clean[0], 16),
        parseInt(clean[1] + clean[1], 16),
        parseInt(clean[2] + clean[2], 16)
      ];
    }
    if (clean.length >= 6) {
      return [
        parseInt(clean.slice(0, 2), 16),
        parseInt(clean.slice(2, 4), 16),
        parseInt(clean.slice(4, 6), 16)
      ];
    }
    return [90, 100, 118];
  }

  function mixRgb(a, b, t) {
    const u = clamp(t, 0, 1);
    return [
      Math.round(a[0] + (b[0] - a[0]) * u),
      Math.round(a[1] + (b[1] - a[1]) * u),
      Math.round(a[2] + (b[2] - a[2]) * u)
    ];
  }

  function rgbStr(c) {
    return "rgb(" + c[0] + "," + c[1] + "," + c[2] + ")";
  }

  function rampColor(stops, t) {
    const u = clamp(t, 0, 1) * (stops.length - 1);
    const k = Math.min(stops.length - 2, Math.floor(u));
    return mixRgb(stops[k], stops[k + 1], u - k);
  }

  function relLuminance(rgb) {
    const lin = (c) => {
      const s = c / 255;
      return s <= 0.03928 ? s / 12.92 : Math.pow((s + 0.055) / 1.055, 2.4);
    };
    return 0.2126 * lin(rgb[0]) + 0.7152 * lin(rgb[1]) + 0.0722 * lin(rgb[2]);
  }

  function contrastTextColor(bgRgb) {
    // Optimal WCAG crossover (~0.179) between #05070a and #ffffff guarantees >= 4.5:1 for any fill.
    return relLuminance(bgRgb) > 0.179 ? "#05070a" : "#ffffff";
  }

  // ---------------------------------------------------------------------------
  // LRU cache + Gzip sniffer + Static fetch
  // ---------------------------------------------------------------------------
  class LRU {
    constructor(cap) {
      this.cap = Math.max(1, cap | 0);
      this.m = new Map();
    }
    has(k) { return this.m.has(k); }
    get(k) {
      if (!this.m.has(k)) return undefined;
      const v = this.m.get(k);
      this.m.delete(k);
      this.m.set(k, v);
      return v;
    }
    set(k, v) {
      if (this.m.has(k)) this.m.delete(k);
      this.m.set(k, v);
      while (this.m.size > this.cap) this.m.delete(this.m.keys().next().value);
    }
    clear() { this.m.clear(); }
  }

  function isGzip(u8) {
    return Boolean(u8 && u8.length >= 2 && u8[0] === 0x1f && u8[1] === 0x8b);
  }

  async function gunzipIfNeeded(u8) {
    const bytes = u8 instanceof Uint8Array ? u8 : new Uint8Array(u8);
    if (!isGzip(bytes)) return bytes;
    if (typeof DecompressionStream !== "function") {
      throw new Error("This browser cannot unpack compressed treemap data (DecompressionStream is unavailable).");
    }
    const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream("gzip"));
    return new Uint8Array(await new Response(stream).arrayBuffer());
  }

  function decodeUtf8(u8) {
    if (utf8Dec) return utf8Dec.decode(u8);
    return Buffer.from(u8).toString("utf8");
  }

  async function fetchJsonOrLxrt(url, signal, fetchImpl) {
    const f = fetchImpl || (typeof fetch === "function" ? fetch : null);
    if (!f) throw new Error("fetch is not available");
    const resp = await f(url, signal ? { signal, credentials: "same-origin" } : { credentials: "same-origin" });
    if (!resp.ok) {
      const err = new Error("HTTP " + resp.status + " for " + url);
      err.status = resp.status;
      throw err;
    }
    const buf = await resp.arrayBuffer();
    const u8 = await gunzipIfNeeded(new Uint8Array(buf));
    return JSON.parse(decodeUtf8(u8));
  }

  // ---------------------------------------------------------------------------
  // Tree parsing (column-name resolution) & lazy tile splicing
  // ---------------------------------------------------------------------------
  const STD_NUM_COLS = new Set([
    "sz", "vn", "loc", "mods", "line", "depth", "mathlib_pct",
    "hb_cnt", "hb_max", "comment_pct", "sorry_p", "sorry_c",
    "orphan_pct", "wrapper_pct", "compress"
  ]);

  function resolveTableValue(val, tbl) {
    if (val == null) return "";
    if (typeof val === "string") return val;
    if (Array.isArray(tbl) && Number.isInteger(val) && val >= 0 && val < tbl.length) {
      return String(tbl[val] || "");
    }
    return String(val);
  }

  function buildColumnIndex(cols) {
    const idx = {};
    if (Array.isArray(cols)) {
      for (let i = 0; i < cols.length; i++) idx[cols[i]] = i;
    }
    return idx;
  }

  function rowToNode(row, colIdx, tables, baseDepth) {
    const get = (k) => (colIdx[k] != null ? row[colIdx[k]] : undefined);
    const num = (k, dflt) => {
      const v = get(k);
      if (v == null || v === "") return dflt;
      const n = Number(v);
      return Number.isFinite(n) ? n : dflt;
    };
    const rawId = get("id");
    const name = String(get("name") || get("short") || rawId || "");
    const shortVal = String(get("short") || "").trim() || shortName(name);
    const kindRaw = get("kind");
    const pillarRaw = get("pillar");
    const modRaw = get("mod");
    const pRaw = get("p");
    const pIdx = pRaw == null || pRaw === "" ? -1 : Number(pRaw);
    return {
      id: rawId != null ? rawId : name,
      p: Number.isFinite(pIdx) ? pIdx : -1,
      name,
      short: shortVal,
      kind: resolveTableValue(kindRaw, tables.kinds),
      pillarIdx: Number.isInteger(pillarRaw) ? pillarRaw : 0,
      pillar: resolveTableValue(pillarRaw, tables.pillars),
      sz: num("sz", 0),
      vn: num("vn", 0),
      loc: num("loc", 0),
      mods: num("mods", 0),
      mod: resolveTableValue(modRaw, tables.mods),
      line: num("line", 0),
      depth: num("depth", baseDepth || 0),
      hash: String(get("hash") || ""),
      tile: String(get("tile") || ""),
      mathlib_pct: num("mathlib_pct", 0),
      hb_cnt: num("hb_cnt", 0),
      hb_max: num("hb_max", 0),
      comment_pct: num("comment_pct", 0),
      sorry_p: num("sorry_p", 0),
      sorry_c: num("sorry_c", 0),
      orphan_pct: num("orphan_pct", 0),
      wrapper_pct: num("wrapper_pct", 0),
      compress: num("compress", 0),
      children: [],
      parent: null,
      tileLoaded: false,
      tileLoading: false,
      tileError: null
    };
  }

  function registerNode(tree, node) {
    if (!tree || !node) return;
    if (node.id != null && node.id !== "") tree.nodesById.set(String(node.id), node);
    if (node.name) {
      if (!tree.nodesByName.has(node.name)) tree.nodesByName.set(node.name, node);
    }
    tree.allNodes.push(node);
  }

  function parseTreePayload(payload, fallbackTables) {
    if (!payload || !Array.isArray(payload.cols) || !Array.isArray(payload.rows)) {
      throw new Error("Invalid treemap tree payload (missing cols or rows)");
    }
    const tables = Object.assign(
      { kinds: [], pillars: [], mods: [] },
      fallbackTables || {},
      payload.tables || {}
    );
    const colIdx = buildColumnIndex(payload.cols);
    const rows = payload.rows;
    const nodes = new Array(rows.length);
    for (let i = 0; i < rows.length; i++) {
      nodes[i] = rowToNode(rows[i], colIdx, tables, 0);
    }
    const roots = [];
    for (let i = 0; i < nodes.length; i++) {
      const n = nodes[i];
      if (n.p >= 0 && n.p < nodes.length && n.p !== i) {
        n.parent = nodes[n.p];
        nodes[n.p].children.push(n);
      } else {
        roots.push(n);
      }
    }
    let rootNode = roots[0] || null;
    if (roots.length > 1) {
      rootNode = {
        id: "__root__",
        p: -1,
        name: payload.root_name || "Root",
        short: payload.root_name || "Root",
        kind: "root",
        pillarIdx: 0,
        pillar: "Root",
        sz: roots.reduce((s, r) => s + r.sz, 0),
        vn: roots.reduce((s, r) => s + r.vn, 0),
        loc: roots.reduce((s, r) => s + r.loc, 0),
        mods: roots.reduce((s, r) => s + r.mods, 0),
        mod: "",
        line: 0,
        depth: 0,
        hash: "",
        tile: "",
        mathlib_pct: 0,
        hb_cnt: roots.reduce((s, r) => s + r.hb_cnt, 0),
        hb_max: Math.max(0, ...roots.map((r) => r.hb_max)),
        comment_pct: 0,
        sorry_p: roots.reduce((s, r) => s + r.sorry_p, 0),
        sorry_c: roots.reduce((s, r) => s + r.sorry_c, 0),
        orphan_pct: 0,
        wrapper_pct: 0,
        compress: 0,
        children: roots,
        parent: null,
        tileLoaded: true,
        tileLoading: false,
        tileError: null
      };
      for (const r of roots) r.parent = rootNode;
    }
    const tree = {
      schema: payload.schema || TREE_SCHEMA,
      view: payload.view || "dom",
      rootName: payload.root_name || (rootNode ? rootNode.name : "Main"),
      tables,
      cols: payload.cols,
      root: rootNode,
      allNodes: [],
      nodesById: new Map(),
      nodesByName: new Map(),
      hasComments: false
    };
    const seen = new Set();
    const walk = (n) => {
      if (!n || seen.has(n)) return;
      seen.add(n);
      if (n.comment_pct > 0) tree.hasComments = true;
      registerNode(tree, n);
      for (const ch of n.children) walk(ch);
    };
    walk(rootNode);
    return tree;
  }

  function spliceTileRows(targetNode, tilePayload, rootTree) {
    if (!targetNode || !tilePayload) return { added: 0 };
    const tileTree = parseTreePayload(tilePayload, rootTree ? rootTree.tables : null);
    if (!tileTree.root) {
      targetNode.tileLoaded = true;
      return { added: 0 };
    }
    const existingKeys = new Set(targetNode.children.map((c) => String(c.id) + "\0" + c.name));
    let candidates = [];
    const tileRoot = tileTree.root;
    const matchesTarget =
      tileRoot.id === "__root__" ||
      String(tileRoot.id) === String(targetNode.id) ||
      (tileRoot.name && tileRoot.name === targetNode.name);

    if (matchesTarget && tileRoot.children.length > 0) {
      candidates = tileRoot.children;
    } else if (tileRoot !== null && !matchesTarget) {
      candidates = [tileRoot];
    }

    let added = 0;
    const addSubtree = (node, parent, depthOffset) => {
      node.parent = parent;
      node.depth = Math.max(parent.depth + 1, (parent.depth || 0) + depthOffset);
      if (node.comment_pct > 0 && rootTree) rootTree.hasComments = true;
      registerNode(rootTree, node);
      added++;
      for (const ch of node.children) addSubtree(ch, node, 1);
    };

    for (const ch of candidates) {
      const k = String(ch.id) + "\0" + ch.name;
      if (existingKeys.has(k)) continue;
      existingKeys.add(k);
      targetNode.children.push(ch);
      addSubtree(ch, targetNode, 1);
    }
    targetNode.tileLoaded = true;
    targetNode.tileLoading = false;
    targetNode.tileError = null;
    return { added };
  }

  // ---------------------------------------------------------------------------
  // Overlay normalization & live descendant coverage roll-up
  // ---------------------------------------------------------------------------
  function inferLayerKind(layerObj, sampleEntries) {
    const raw = String((layerObj && layerObj.kind) || "").toLowerCase().trim();
    if (raw === "ai-draft" || raw === "ai" || raw === "bot-check") return "ai-draft";
    if (raw === "dossier" || raw === "review-note" || raw === "notes") return "dossier";
    if (raw === "human-review" || raw === "human") return "human-review";
    const id = String((layerObj && (layerObj.id || layerObj.layer)) || "").toLowerCase();
    if (id.startsWith("ai/") || id.startsWith("ai-") || id.includes("draft")) return "ai-draft";
    if (id.startsWith("dossier") || id.includes("dossier")) return "dossier";
    if (sampleEntries && sampleEntries.some((e) => e.draft === true || String(e.author || "").startsWith("ai:"))) {
      return "ai-draft";
    }
    return "human-review";
  }

  function normalizeOverlay(raw) {
    const out = {
      schema: (raw && raw.schema) || OVERLAY_SCHEMA,
      layers: [],
      layerMap: new Map(),
      entriesByName: new Map(),
      entriesByHash: new Map(),
      authors: []
    };
    if (!raw || typeof raw !== "object") return out;

    const addEntry = (keyHint, rec) => {
      if (!rec || typeof rec !== "object") return;
      const entry = {
        layer: String(rec.layer || "default"),
        kind: String(rec.kind || ""),
        status: String(rec.status || "").toLowerCase(),
        verdict: String(rec.verdict || "").toLowerCase(),
        author: String(rec.author || ""),
        note: String(rec.note || ""),
        breaks: String(rec.breaks || ""),
        draft: Boolean(rec.draft),
        source: String(rec.source || ""),
        url: String(rec.url || ""),
        dossier_route: String(rec.dossier_route || ""),
        updated: String(rec.updated || ""),
        sighash: String(rec.sighash || rec.hash || ""),
        name: String(rec.name || keyHint || ""),
        target: String(rec.target || ""),
        contested: Boolean(rec.contested),
        issues: rec.issues || null
      };
      if (entry.name) {
        if (!out.entriesByName.has(entry.name)) out.entriesByName.set(entry.name, []);
        out.entriesByName.get(entry.name).push(entry);
      }
      if (entry.sighash) {
        if (!out.entriesByHash.has(entry.sighash)) out.entriesByHash.set(entry.sighash, []);
        out.entriesByHash.get(entry.sighash).push(entry);
      }
      if (keyHint && keyHint !== entry.name && keyHint !== entry.sighash) {
        const targetMap = SIGHASH_RX.test(keyHint) ? out.entriesByHash : out.entriesByName;
        if (!targetMap.has(keyHint)) targetMap.set(keyHint, []);
        targetMap.get(keyHint).push(entry);
      }
    };

    const rawEntries = raw.entries;
    if (Array.isArray(rawEntries)) {
      for (const rec of rawEntries) addEntry("", rec);
    } else if (rawEntries && typeof rawEntries === "object") {
      for (const key of Object.keys(rawEntries)) {
        const val = rawEntries[key];
        if (Array.isArray(val)) {
          for (const rec of val) addEntry(key, rec);
        } else if (val && typeof val === "object") {
          addEntry(key, val);
        }
      }
    }

    const layerStats = new Map();
    const authorSet = new Set();
    const collectMeta = (map) => {
      for (const list of map.values()) {
        for (const e of list) {
          if (e.author) authorSet.add(e.author);
          if (!layerStats.has(e.layer)) layerStats.set(e.layer, []);
          layerStats.get(e.layer).push(e);
        }
      }
    };
    collectMeta(out.entriesByName);

    const seenLayers = new Set();
    for (const l of (Array.isArray(raw.layers) ? raw.layers : [])) {
      if (!l || typeof l !== "object") continue;
      const id = String(l.id || l.layer || "");
      if (!id || seenLayers.has(id)) continue;
      seenLayers.add(id);
      const kind = inferLayerKind(l, layerStats.get(id));
      const defaultOn = typeof l.default_on === "boolean" ? l.default_on : (kind !== "ai-draft");
      const norm = {
        id,
        title: String(l.title || id).replace(/\s*\(HANDOFF\.md[^)]*\)/gi, "").trim(),
        kind,
        default_on: defaultOn,
        author: String(l.author || ""),
        count: Number(l.count != null ? l.count : (layerStats.get(id) || []).length) || 0,
        description: String(l.description || "")
      };
      out.layers.push(norm);
      out.layerMap.set(id, norm);
    }

    for (const [id, list] of layerStats.entries()) {
      if (seenLayers.has(id)) continue;
      seenLayers.add(id);
      const kind = inferLayerKind({ id }, list);
      const norm = {
        id,
        title: id,
        kind,
        default_on: kind !== "ai-draft",
        author: "",
        count: list.length,
        description: ""
      };
      out.layers.push(norm);
      out.layerMap.set(id, norm);
    }

    out.authors = Array.from(authorSet).sort();
    return out;
  }

  function isPositiveEntry(e) {
    return e.status === "verified" || e.status === "exact" || e.verdict === "verified" || e.verdict === "real";
  }

  function isNegativeEntry(e) {
    return e.status === "flagged" || e.verdict === "suspect" || e.verdict === "flagged" || e.verdict === "invalid";
  }

  function getNodeEntries(node, overlay, activeLayerIds, contributorFilter) {
    if (!node || !overlay) return { entries: [], contested: false };
    const matched = [];
    const seen = new Set();
    const pushList = (list) => {
      if (!list) return;
      for (const e of list) {
        if (activeLayerIds && !activeLayerIds.has(e.layer)) continue;
        if (contributorFilter && e.author !== contributorFilter) continue;
        const k = e.layer + "\0" + e.author + "\0" + e.status + "\0" + e.note.slice(0, 64);
        if (seen.has(k)) continue;
        seen.add(k);
        matched.push(e);
      }
    };
    if (node.name) pushList(overlay.entriesByName.get(node.name));
    if (node.hash) pushList(overlay.entriesByHash.get(node.hash));

    let hasPos = false;
    let hasNeg = false;
    let explicitContested = false;
    for (const e of matched) {
      if (e.contested) explicitContested = true;
      if (isPositiveEntry(e)) hasPos = true;
      if (isNegativeEntry(e)) hasNeg = true;
    }
    return { entries: matched, contested: explicitContested || (hasPos && hasNeg) };
  }

  function classifyDirectTier(node, matchedInfo, overlay) {
    const entries = matchedInfo.entries;
    if (matchedInfo.contested) return "flagged";
    let hasHuman = false;
    let hasDossier = false;
    let hasAi = false;
    let hasFlagged = false;

    for (const e of entries) {
      const layerMeta = overlay && overlay.layerMap ? overlay.layerMap.get(e.layer) : null;
      const lKind = (layerMeta && layerMeta.kind) || inferLayerKind({ id: e.layer, kind: e.kind }, [e]);
      if (isNegativeEntry(e)) {
        hasFlagged = true;
      } else if (lKind === "ai-draft" || e.draft || String(e.author || "").startsWith("ai:")) {
        hasAi = true;
      } else if (lKind === "dossier" || e.dossier_route) {
        hasDossier = true;
      } else if (e.status === "verified" || lKind === "human-review") {
        if (e.status === "summary" || e.status === "read") hasDossier = true;
        else hasHuman = true;
      } else {
        hasDossier = true;
      }
    }

    if (hasFlagged || (node && node.sorry_p > 0 && !hasHuman)) return "flagged";
    if (hasHuman) return "human";
    if (hasDossier) return "dossier";
    if (hasAi) return "ai";
    return "unreviewed";
  }

  function computeCoverageStats(rootNode, overlay, activeLayerIds, contributorFilter) {
    if (!rootNode) return { human: 0, dossier: 0, ai: 0, flagged: 0, unreviewed: 0, total: 1 };

    const visit = (node) => {
      const info = getNodeEntries(node, overlay, activeLayerIds, contributorFilter);
      const tier = classifyDirectTier(node, info, overlay);
      const rawW = Math.max(1, Number(node.sz) || Number(node.loc) || 1);

      let human = 0;
      let dossier = 0;
      let ai = 0;
      let flagged = 0;
      let childTotal = 0;

      for (const ch of node.children) {
        const c = visit(ch);
        human += c.human;
        dossier += c.dossier;
        ai += c.ai;
        flagged += c.flagged;
        childTotal += c.total;
      }

      let ownW = 0;
      let unexpandedRest = 0;
      if (node.children.length > 0) {
        ownW = rawW > childTotal ? (rawW - childTotal) : 0;
      } else if (node.tile && !node.tileLoaded && rawW > 1) {
        ownW = 1;
        unexpandedRest = rawW - 1;
      } else {
        ownW = rawW;
      }

      if (tier === "human") human += ownW;
      else if (tier === "dossier") dossier += ownW;
      else if (tier === "ai") ai += ownW;
      else if (tier === "flagged") flagged += ownW;

      const total = Math.max(1, childTotal + ownW + unexpandedRest);
      const unreviewed = Math.max(0, total - human - dossier - ai - flagged);

      node._cov = {
        human,
        dossier,
        ai,
        flagged,
        unreviewed,
        total,
        humanPct: human / total,
        dossierPct: dossier / total,
        aiPct: ai / total,
        flaggedPct: flagged / total,
        reviewedPct: (human + dossier) / total,
        directTier: tier,
        directEntries: info.entries,
        contested: info.contested
      };
      return node._cov;
    };

    return visit(rootNode);
  }

  // ---------------------------------------------------------------------------
  // Bruls-Huizing-van Wijk Squarified Treemap Layout
  // ---------------------------------------------------------------------------
  function squarify(items, rect) {
    if (!Array.isArray(items) || !items.length) return [];
    const rx = Number(rect.x) || 0;
    const ry = Number(rect.y) || 0;
    const rw = Number(rect.w) || 0;
    const rh = Number(rect.h) || 0;
    if (rw <= 0 || rh <= 0) return [];

    const valid = [];
    let totalW = 0;
    for (let i = 0; i < items.length; i++) {
      const it = items[i];
      const w = Number(it && it.weight);
      if (Number.isFinite(w) && w > 0) {
        valid.push({ item: it, weight: w, idx: i });
        totalW += w;
      }
    }
    if (!valid.length || totalW <= 0) return [];

    valid.sort((a, b) => (b.weight - a.weight) || (a.idx - b.idx));
    const totalArea = rw * rh;
    const scale = totalArea / totalW;
    const areas = valid.map((v) => v.weight * scale);

    const out = [];
    let x = rx;
    let y = ry;
    let w = rw;
    let h = rh;

    function worstRatio(rowAreas, sideLen) {
      if (!rowAreas.length || sideLen <= 0) return Infinity;
      let sum = 0;
      let maxA = 0;
      let minA = Infinity;
      for (let i = 0; i < rowAreas.length; i++) {
        const a = rowAreas[i];
        sum += a;
        if (a > maxA) maxA = a;
        if (a < minA) minA = a;
      }
      if (sum <= 0 || minA <= 0) return Infinity;
      const s2 = sum * sum;
      const w2 = sideLen * sideLen;
      return Math.max((w2 * maxA) / s2, s2 / (w2 * minA));
    }

    function layoutRow(rowItems, rowAreas) {
      let sum = 0;
      for (let i = 0; i < rowAreas.length; i++) sum += rowAreas[i];
      const horizontalStrip = w >= h; // cut along shorter side (height h when w >= h)
      if (horizontalStrip) {
        const stripW = h > 0 ? Math.min(w, sum / h) : 0;
        let cy = y;
        for (let i = 0; i < rowItems.length; i++) {
          const isLast = i === rowItems.length - 1;
          const bh = isLast ? Math.max(0, y + h - cy) : (stripW > 0 ? rowAreas[i] / stripW : 0);
          out.push({
            item: rowItems[i].item,
            x,
            y: cy,
            w: stripW,
            h: bh
          });
          cy += bh;
        }
        x += stripW;
        w = Math.max(0, w - stripW);
      } else {
        const stripH = w > 0 ? Math.min(h, sum / w) : 0;
        let cx = x;
        for (let i = 0; i < rowItems.length; i++) {
          const isLast = i === rowItems.length - 1;
          const bw = isLast ? Math.max(0, x + w - cx) : (stripH > 0 ? rowAreas[i] / stripH : 0);
          out.push({
            item: rowItems[i].item,
            x: cx,
            y,
            w: bw,
            h: stripH
          });
          cx += bw;
        }
        y += stripH;
        h = Math.max(0, h - stripH);
      }
    }

    let rowItems = [];
    let rowAreas = [];
    let side = Math.min(w, h);

    for (let i = 0; i < valid.length; i++) {
      const candArea = areas[i];
      if (!rowItems.length) {
        side = Math.min(w, h);
        rowItems.push(valid[i]);
        rowAreas.push(candArea);
        continue;
      }
      const curWorst = worstRatio(rowAreas, side);
      const nextAreas = rowAreas.concat(candArea);
      const nextWorst = worstRatio(nextAreas, side);
      if (nextWorst <= curWorst) {
        rowItems.push(valid[i]);
        rowAreas.push(candArea);
      } else {
        layoutRow(rowItems, rowAreas);
        side = Math.min(w, h);
        rowItems = [valid[i]];
        rowAreas = [candArea];
      }
    }
    if (rowItems.length) layoutRow(rowItems, rowAreas);
    return out;
  }

  // ---------------------------------------------------------------------------
  // Draft Annotation PR Validator & JSONL Builder (leanre.annot/1)
  // ---------------------------------------------------------------------------
  function sanitizeSlugPart(raw, fallback) {
    const s = String(raw || "")
      .trim()
      .toLowerCase()
      .replace(/\.\.+/g, "_")
      .replace(/[^a-z0-9._-]+/g, "-")
      .replace(/^[-._]+|[-._]+$/g, "");
    return s || fallback;
  }

  function buildDraftPath(input) {
    const slug = sanitizeSlugPart(input && input.slug, "project");
    const authorRaw = String((input && input.author) || "reviewer").replace(/^@/, "").replace(/^ai:/i, "ai-");
    const author = sanitizeSlugPart(authorRaw, "reviewer");
    const shortTarget = sanitizeSlugPart(shortName((input && input.name) || "target"), "item");
    return "annotations/contrib/" + slug + "/" + author + "__" + shortTarget + ".jsonl";
  }

  function utcNowIso() {
    return new Date().toISOString().replace(/\.\d{3}Z$/, "Z");
  }

  function canonicalJson(obj) {
    if (Array.isArray(obj)) return "[" + obj.map(canonicalJson).join(",") + "]";
    if (obj && typeof obj === "object") {
      const keys = Object.keys(obj).sort();
      return "{" + keys.map((k) => JSON.stringify(k) + ":" + canonicalJson(obj[k])).join(",") + "}";
    }
    return JSON.stringify(obj);
  }

  function validateDraft(input) {
    const d = input || {};
    const errors = [];
    const warnings = [];
    const name = String(d.name || "").trim();
    const slug = String(d.slug || "").trim();
    const kind = String(d.kind || "human-review").trim();
    const status = String(d.status || "summary").trim();
    const author = String(d.author || "").trim();
    const note = String(d.note || "").trim();
    const source = String(d.source || "").trim();
    const breaks = String(d.breaks || "").trim();
    const sighash = String(d.sighash || "").trim();
    const target = String(d.target || "decl").trim();

    if (!name) errors.push("Missing declaration or node target name.");
    if (!slug) errors.push("Missing project slug.");
    if (!author) errors.push("Author handle is required (e.g. @alice or ai:model-name).");
    if (!note) errors.push("Summary / mathematical note is required.");
    if (!source) errors.push("Evidence / GitHub source URL is required.");

    if (author.length > 120) errors.push("Author exceeds 120 characters.");
    if (note.length > 2000) errors.push("Note exceeds 2,000 characters (keep annotations concise).");
    if (breaks.length > 2000) errors.push("Caveats field exceeds 2,000 characters.");

    for (const [lbl, val] of [["Author", author], ["Note", note], ["Source", source], ["Caveats", breaks]]) {
      if (CTRL_RX.test(val)) errors.push(lbl + " contains disallowed control characters.");
      if (XSS_MARKUP_RX.test(val)) errors.push(lbl + " contains disallowed HTML or script markup.");
    }

    if (OVERCLAIM_RX.test(note)) {
      errors.push("Note contains disallowed overclaim phrasing (describe local lemma behavior instead).");
    }

    if (LEAN_PASTE_RX.test(note)) {
      errors.push("Do not paste verbatim Lean proof bodies (:= by or import lines) into annotations.");
    } else {
      const leanLines = note.split(/\r?\n/).filter((ln) => LEAN_MULTI_LINE_RX.test(ln));
      if (leanLines.length >= 3) {
        errors.push("Multi-line Lean code block detected in note; cite a pinned GitHub #L line link instead.");
      }
    }

    const isAiKind = kind === "ai-draft" || kind === "bot-check";
    if (isAiKind) {
      if (author && !author.startsWith("ai:")) {
        errors.push("AI draft and bot check records must use an author handle starting with \"ai:\".");
      }
      if (!breaks) {
        errors.push("AI draft and bot check records require a \"Caveats / what breaks\" note.");
      }
    } else if (author.startsWith("ai:")) {
      errors.push("Author handles starting with \"ai:\" must use Kind = \"ai-draft\" or \"bot-check\".");
    }

    if (source) {
      if (FLOATING_GH_RX.test(source)) {
        errors.push("GitHub link uses a floating branch (/blob/main/); pin it to a full commit SHA.");
      } else if (!PINNED_GH_LINE_RX.test(source)) {
        warnings.push("Evidence link is missing a pinned commit GitHub #L anchor (https://github.com/.../blob/<sha>/...#L<line>).");
      }
    }

    if (sighash && target === "decl" && !SIGHASH_RX.test(sighash)) {
      warnings.push("Signature hash does not match expected scheme:hex format and will be omitted.");
    }

    return {
      valid: errors.length === 0,
      errors,
      warnings,
      path: buildDraftPath({ slug, author, name }),
      status
    };
  }

  function buildDraftJsonl(input) {
    const d = input || {};
    const slug = sanitizeSlugPart(d.slug, "project");
    const kind = String(d.kind || "human-review").trim();
    const isAi = kind === "ai-draft" || kind === "bot-check";
    const status = String(d.status || "summary").trim() || "summary";
    const target = ["decl", "module", "folder", "namespace"].includes(d.target) ? d.target : "decl";
    const name = String(d.name || "").trim();
    const rawAuthor = String(d.author || (isAi ? "ai:reviewer" : "@reviewer")).trim();
    const author = isAi && !rawAuthor.startsWith("ai:") ? ("ai:" + rawAuthor.replace(/^@/, "")) : rawAuthor;
    const authorSlug = sanitizeSlugPart(author.replace(/^@/, "").replace(/^ai:/, ""), "reviewer");
    const layerId = (isAi ? "ai/" : "human/") + "contrib-" + slug + "-" + authorSlug.slice(0, 24);
    const nowIso = String(d.timestamp || utcNowIso());
    const sighash = String(d.sighash || "").trim();
    const note = String(d.note || "").trim();
    const source = String(d.source || "").trim();
    const breaksText = String(d.breaks || "").trim() ||
      (isAi ? "Draft automated note; proof body not independently verified by a human mathematician." : "");

    const header = { type: "pack", schema: ANNOT_SCHEMA };
    const layer = {
      type: "layer",
      layer: layerId,
      kind: isAi ? "ai-draft" : "human",
      default_on: !isAi,
      title: (isAi ? "AI draft notes by " : "Community review by ") + author + " (" + slug + ")"
    };
    const annot = {
      type: "annot",
      target,
      name,
      layer: layerId,
      tag: isAi ? "M" : (breaksText ? "M" : "L"),
      source,
      author,
      note,
      created: nowIso,
      updated: nowIso,
      extra: {
        project: slug,
        status,
        review_kind: kind
      }
    };
    if (d.dom_subtree != null && Number(d.dom_subtree) > 0) {
      annot.extra.dom_subtree = Math.round(Number(d.dom_subtree));
    }
    if (isAi) annot.draft = true;
    if (breaksText) annot.breaks = breaksText;
    if (target === "decl" && SIGHASH_RX.test(sighash)) annot.sighash = sighash;

    return [canonicalJson(header), canonicalJson(layer), canonicalJson(annot)].join("\n") + "\n";
  }

  function buildGithubNewPrUrl(path, content, toolRepoUrl) {
    const repo = String(toolRepoUrl || DEFAULT_TOOL_REPO).replace(/\/+$/, "");
    const url = repo + "/new/main?filename=" + encodeURIComponent(path) + "&value=" + encodeURIComponent(content);
    return { url, tooLong: url.length >= MAX_GH_NEW_URL_LEN, length: url.length };
  }

  // ---------------------------------------------------------------------------
  // Client
  // ---------------------------------------------------------------------------
  class TreemapClient {
    constructor(baseUrl, opts) {
      const b = String(baseUrl || "data/treemap/");
      this.baseUrl = b.endsWith("/") ? b : b + "/";
      this.opts = opts || {};
      this.manifest = this.opts.manifest || null;
      this.overlay = this.opts.overlay ? normalizeOverlay(this.opts.overlay) : null;
      this.views = new Map();
      this.tiles = new LRU(TILE_LRU_CAP);
      this.initPromise = null;
    }

    async init() {
      if (this.manifest && this.overlay) return this.manifest;
      if (this.initPromise) return this.initPromise;
      this.initPromise = (async () => {
        if (!this.manifest) {
          this.manifest = await fetchJsonOrLxrt(this.baseUrl + "manifest.json", null, this.opts.fetchImpl);
        }
        if (!this.manifest || this.manifest.schema !== SCHEMA) {
          throw new Error("Unexpected treemap manifest schema: " + (this.manifest && this.manifest.schema));
        }
        if (!this.overlay) {
          const ovFile = this.manifest.overlay || "overlay.json";
          try {
            const rawOv = await fetchJsonOrLxrt(this.baseUrl + ovFile, null, this.opts.fetchImpl);
            this.overlay = normalizeOverlay(rawOv);
          } catch (_) {
            this.overlay = normalizeOverlay(null);
          }
        }
        return this.manifest;
      })();
      return this.initPromise;
    }

    async loadView(viewId) {
      await this.init();
      const spec = (this.manifest.views || []).find((v) => v.id === viewId) || (this.manifest.views || [])[0];
      if (!spec) throw new Error("No treemap views available");
      if (this.views.has(spec.id)) return this.views.get(spec.id);
      let payload = this.opts.trees && this.opts.trees[spec.id];
      if (!payload) {
        payload = await fetchJsonOrLxrt(this.baseUrl + spec.file, null, this.opts.fetchImpl);
      }
      const tree = parseTreePayload(payload, null);
      this.views.set(spec.id, { spec, tree });
      return { spec, tree };
    }

    async loadTile(viewSpec, tileKey, tree) {
      const cacheKey = viewSpec.id + ":" + tileKey;
      if (this.tiles.has(cacheKey)) return this.tiles.get(cacheKey);
      const tpl = viewSpec.tile_path || ("tiles_" + viewSpec.id + "/{id}.lxrt");
      const rel = tpl.replace(/\{id\}|\{tile\}/g, encodeURIComponent(String(tileKey)));
      let payload = this.opts.tiles && this.opts.tiles[cacheKey];
      if (!payload && this.opts.tiles && this.opts.tiles[tileKey]) payload = this.opts.tiles[tileKey];
      if (!payload) {
        payload = await fetchJsonOrLxrt(this.baseUrl + rel, null, this.opts.fetchImpl);
      }
      this.tiles.set(cacheKey, payload);
      return payload;
    }
  }

  // ---------------------------------------------------------------------------
  // Color modes & legends
  // ---------------------------------------------------------------------------
  const COLOR_MODE_DEFS = [
    { id: "coverage", label: "Review coverage" },
    { id: "pillar", label: "Topic / Pillar" },
    { id: "novelty", label: "Novelty (unmatched %)" },
    { id: "bloat", label: "Proof AST density" },
    { id: "heartbeats", label: "Heartbeat pressure" },
    { id: "comments", label: "Comments %" },
    { id: "sorry", label: "Sorry / gaps" },
    { id: "compress", label: "Name compressibility" }
  ];

  function createAiHatchPattern(ctx, light) {
    if (typeof document === "undefined" || !ctx || typeof ctx.createPattern !== "function") return null;
    const c = document.createElement("canvas");
    c.width = 10;
    c.height = 10;
    const g = c.getContext("2d");
    if (!g) return null;
    g.strokeStyle = light ? "rgba(154, 91, 11, 0.34)" : "rgba(255, 214, 140, 0.28)";
    g.lineWidth = 2;
    g.beginPath();
    g.moveTo(-2, 10);
    g.lineTo(10, -2);
    g.moveTo(0, 12);
    g.lineTo(12, 0);
    g.stroke();
    return ctx.createPattern(c, "repeat");
  }

  function computeColorMetricRanges(tree) {
    let maxAst = 1;
    let maxHb = 1;
    let maxComment = 0;
    for (const n of tree.allNodes) {
      const ast = Math.log1p(Math.max(0, n.vn) / Math.max(1, n.sz));
      if (ast > maxAst) maxAst = ast;
      const hb = Math.log1p(Math.max(0, n.hb_max || n.hb_cnt));
      if (hb > maxHb) maxHb = hb;
      if (n.comment_pct > maxComment) maxComment = n.comment_pct;
    }
    return { maxAst, maxHb, maxComment };
  }

  function nodeColor(node, modeId, ranges, light) {
    const baseSlate = light ? [213, 217, 224] : [49, 57, 71];
    const humanRgb = light ? [34, 139, 92] : [52, 148, 104];
    const dossierRgb = light ? [20, 128, 119] : [42, 138, 126];
    const aiRgb = light ? [184, 122, 34] : [170, 120, 48];
    const flagRgb = light ? [194, 62, 69] : [188, 76, 82];

    if (modeId === "coverage") {
      const cov = node._cov || { humanPct: 0, dossierPct: 0, aiPct: 0, flaggedPct: 0, directTier: "unreviewed" };
      let rgb = baseSlate;
      let hatch = false;
      if (cov.directTier === "flagged" || cov.flaggedPct > 0.12) {
        rgb = mixRgb(baseSlate, flagRgb, Math.max(0.55, cov.flaggedPct));
      } else if (cov.directTier === "human" || cov.humanPct > 0) {
        const strength = cov.directTier === "human" ? 0.9 : Math.max(0.32, Math.min(0.92, 0.28 + cov.humanPct * 0.65));
        rgb = mixRgb(baseSlate, humanRgb, strength);
      } else if (cov.directTier === "dossier" || cov.dossierPct > 0) {
        const strength = cov.directTier === "dossier" ? 0.88 : Math.max(0.32, Math.min(0.9, 0.28 + cov.dossierPct * 0.65));
        rgb = mixRgb(baseSlate, dossierRgb, strength);
      } else if (cov.directTier === "ai" || cov.aiPct > 0) {
        const strength = cov.directTier === "ai" ? 0.78 : Math.max(0.28, Math.min(0.82, 0.24 + cov.aiPct * 0.6));
        rgb = mixRgb(baseSlate, aiRgb, strength);
        hatch = true;
      } else if (cov.flaggedPct > 0) {
        rgb = mixRgb(baseSlate, flagRgb, 0.45);
      }
      return { rgb, fill: rgbStr(rgb), hatch };
    }

    if (modeId === "pillar") {
      const pal = light ? PILLAR_PALETTE_LIGHT : PILLAR_PALETTE_DARK;
      const idx = Math.abs(Number(node.pillarIdx) || 0) % pal.length;
      const rgb = hexToRgb(pal[idx]);
      return { rgb, fill: rgbStr(rgb), hatch: false };
    }

    if (modeId === "novelty") {
      const nov = clamp(1 - (Number(node.mathlib_pct) || 0), 0, 1);
      const stops = light
        ? [[48, 128, 120], [168, 174, 184], [194, 130, 32]]
        : [[42, 118, 112], [68, 78, 94], [198, 142, 54]];
      const rgb = rampColor(stops, nov);
      return { rgb, fill: rgbStr(rgb), hatch: false };
    }

    if (modeId === "bloat") {
      const v = Math.log1p(Math.max(0, node.vn) / Math.max(1, node.sz));
      const t = clamp(v / Math.max(1e-6, ranges.maxAst), 0, 1);
      const stops = light
        ? [[198, 204, 214], [58, 126, 168], [186, 114, 34]]
        : [[49, 57, 71], [62, 130, 168], [194, 132, 52]];
      const rgb = rampColor(stops, t);
      return { rgb, fill: rgbStr(rgb), hatch: false };
    }

    if (modeId === "heartbeats") {
      const v = Math.log1p(Math.max(0, node.hb_max || node.hb_cnt));
      const t = clamp(v / Math.max(1e-6, ranges.maxHb), 0, 1);
      const stops = light
        ? [[206, 211, 220], [196, 138, 44], [186, 56, 62]]
        : [[49, 57, 71], [184, 128, 48], [192, 74, 80]];
      const rgb = rampColor(stops, t);
      return { rgb, fill: rgbStr(rgb), hatch: false };
    }

    if (modeId === "comments") {
      const t = clamp((Number(node.comment_pct) || 0) / Math.max(1, ranges.maxComment || 50), 0, 1);
      const stops = light
        ? [[206, 211, 220], [42, 142, 132]]
        : [[49, 57, 71], [46, 146, 134]];
      const rgb = rampColor(stops, t);
      return { rgb, fill: rgbStr(rgb), hatch: false };
    }

    if (modeId === "sorry") {
      let rgb = baseSlate;
      if (node.sorry_p > 0) rgb = flagRgb;
      else if (node.sorry_c > 0) rgb = aiRgb;
      return { rgb, fill: rgbStr(rgb), hatch: false };
    }

    // compress
    const t = clamp(Number(node.compress) || 0, 0, 1);
    const stops = light
      ? [[198, 204, 214], [96, 118, 178], [146, 86, 174]]
      : [[49, 57, 71], [86, 112, 174], [142, 92, 178]];
    const rgb = rampColor(stops, t);
    return { rgb, fill: rgbStr(rgb), hatch: false };
  }

  // ---------------------------------------------------------------------------
  // Explorer Renderer
  // ---------------------------------------------------------------------------
  async function renderExplorer(host, opts) {
    if (!hasDoc) throw new Error("renderExplorer requires a browser DOM");
    const o = Object.assign({}, opts || {});
    const client = o.client || new TreemapClient(o.baseUrl || "data/treemap/", o);

    clearEl(host);
    const rootEl = h("section", { class: "tm-root", "aria-label": "Proof treemap explorer" });
    host.appendChild(rootEl);

    const loadingBox = h("div", { class: "tm-empty-box" }, "Loading proof treemap…");
    rootEl.appendChild(loadingBox);

    try {
      await client.init();
    } catch (err) {
      clearEl(rootEl);
      rootEl.appendChild(h("div", { class: "tm-empty-box" }, "Unable to load treemap index: " + String(err && err.message || err)));
      return null;
    }

    const manifest = client.manifest;
    const views = Array.isArray(manifest.views) ? manifest.views : [];
    const defaultViewId = o.initialView && views.some((v) => v.id === o.initialView)
      ? o.initialView
      : (views[0] ? views[0].id : "dom");

    const state = {
      viewId: defaultViewId,
      viewSpec: null,
      tree: null,
      ranges: { maxAst: 1, maxHb: 1, maxComment: 0 },
      sizeCol: "sz",
      colorMode: (manifest.color_modes && manifest.color_modes[0]) || "coverage",
      activeLayers: new Set(),
      contributorFilter: "",
      focusNode: null,
      selectedNode: null,
      hoveredNode: null,
      flashNodeId: null,
      flashUntil: 0,
      cam: { x: 0, y: 0, zoom: 1 },
      anim: null,
      renderedBoxes: [],
      fullScreen: false,
      composerOpen: false,
      draftKind: "human-review",
      draftStatus: "summary",
      draftAuthor: "",
      draftNote: "",
      draftSource: "",
      draftBreaks: "",
      draftToast: ""
    };

    for (const l of client.overlay.layers) {
      if (l.default_on) state.activeLayers.add(l.id);
    }

    clearEl(rootEl);

    // Page header
    const head = h("header", { class: "tm-head" }, [
      h("div", { class: "tm-title-row" }, [
        h("h1", { class: "tm-title" }, "Proof Treemap"),
        h("span", { class: "trust-badge tool" }, "Nested area map · " + (manifest.mode === "kernel" ? "Kernel + Source" : "Source tree"))
      ]),
      h("p", { class: "tm-sub" }, "Zoom through nested proof containers down to individual theorems, compare active review layers, and export a draft annotation PR.")
    ]);
    rootEl.appendChild(head);

    const shell = h("div", { class: "tm-shell" });
    rootEl.appendChild(shell);

    // Toolbar controls
    const viewSeg = h("div", { class: "seg", role: "group", "aria-label": "Hierarchy view" });
    const sizeSelect = h("select", { class: "tm-select", "aria-label": "Size by" });
    const colorSelect = h("select", { class: "tm-select", "aria-label": "Color by" });
    const contribSelect = h("select", { class: "tm-select", "aria-label": "Contributor filter" });
    const searchInput = h("input", {
      type: "search",
      class: "tm-input tm-search-input",
      placeholder: "Jump to theorem or folder…",
      "aria-label": "Jump to theorem or folder"
    });
    const acList = h("ul", { class: "tm-ac hidden", role: "listbox" });
    const searchWrap = h("div", { class: "tm-search-wrap" }, [searchInput, acList]);

    const zoomOutBtn = h("button", { type: "button", class: "btn sm", title: "Zoom out", "aria-label": "Zoom out" }, "−");
    const zoomReadout = h("span", { class: "tm-zoom-val" }, "1.0×");
    const zoomInBtn = h("button", { type: "button", class: "btn sm", title: "Zoom in", "aria-label": "Zoom in" }, "+");
    const upBtn = h("button", { type: "button", class: "btn sm", title: "Up one level" }, "Up one level");
    const resetBtn = h("button", { type: "button", class: "btn sm", title: "Reset view" }, "Reset");
    const fsBtn = h("button", { type: "button", class: "btn sm fs-btn", title: "Toggle full screen" }, "⛶ Full screen");

    const toolbar = h("div", { class: "tm-toolbar" }, [
      views.length > 1 ? viewSeg : null,
      h("label", { class: "tm-ctl" }, [h("span", { class: "tm-ctl-lbl" }, "Size by"), sizeSelect]),
      h("label", { class: "tm-ctl" }, [h("span", { class: "tm-ctl-lbl" }, "Color by"), colorSelect]),
      searchWrap,
      h("div", { class: "tm-zoom-group" }, [zoomOutBtn, zoomReadout, zoomInBtn, upBtn, resetBtn, fsBtn])
    ]);
    shell.appendChild(toolbar);

    // Trust layer bar
    const layerChipsWrap = h("div", { class: "tm-layer-chips" });
    const layersBar = h("div", { class: "tm-layers-bar" }, [
      h("span", { class: "tm-layers-title" }, "Overlay layers:"),
      layerChipsWrap,
      h("label", { class: "tm-ctl" }, [h("span", { class: "tm-ctl-lbl" }, "Contributor"), contribSelect])
    ]);
    shell.appendChild(layersBar);

    // Breadcrumb & coverage summary bar
    const crumbsEl = h("nav", { class: "tm-crumbs", "aria-label": "Treemap zoom path" });
    const covBarEl = h("div", { class: "tm-cov-bar", "aria-live": "polite" });
    const metaStrip = h("div", { class: "tm-meta-strip" }, [crumbsEl, covBarEl]);
    shell.appendChild(metaStrip);

    // Legend strip
    const legendStrip = h("div", { class: "tm-legend-strip" });
    shell.appendChild(legendStrip);

    // Main split body: Canvas + Inspector
    const canvas = h("canvas", { class: "tm-canvas", role: "img", "aria-label": "Interactive nested proof treemap" });
    const tipEl = h("div", { class: "tm-tip hidden", role: "tooltip" });
    const zoomHintEl = h("div", { class: "tm-zoom-hint" }, "Hold Ctrl + scroll to zoom");
    const tilePill = h("div", { class: "tm-tile-pill hidden" }, [
      h("span", { class: "tm-spin", "aria-hidden": "true" }),
      h("span", null, "Loading subtree tile…")
    ]);
    const canvasWrap = h("div", { class: "tm-canvas-wrap" }, [canvas, tipEl, zoomHintEl, tilePill]);
    const inspectorEl = h("aside", { class: "tm-inspector", "aria-label": "Selected rectangle inspector" });
    const bodyEl = h("div", { class: "tm-body" }, [canvasWrap, inspectorEl]);
    shell.appendChild(bodyEl);

    let zoomHintTimer = null;
    function flashZoomHint() {
      zoomHintEl.classList.add("show");
      if (zoomHintTimer) clearTimeout(zoomHintTimer);
      zoomHintTimer = setTimeout(() => zoomHintEl.classList.remove("show"), 1300);
    }

    function nodeWeight(node) {
      if (!node) return 0;
      const col = state.sizeCol || "sz";
      const val = Number(node[col]);
      if (Number.isFinite(val) && val > 0) return val;
      if (col === "sz") return Math.max(0, Number(node.loc) || 0);
      return 0;
    }

    function resolveGithubUrl(node) {
      if (!node) return null;
      const target = node.mod || (state.viewId === "folder" && node.name && node.name.endsWith(".lean") ? node.name : "");
      if (!target) return null;
      if (typeof o.buildGithubUrl === "function") {
        const u = o.buildGithubUrl(target, node.line > 0 ? node.line : undefined);
        if (u) return u;
      }
      if (!o.repoUrl) return null;
      const base = String(o.repoUrl).replace(/\/+$/, "");
      const commit = String(o.pinnedCommit || "main");
      const prefix = String(o.srcPrefix || "").replace(/^\/+/, "");
      let path = target.replace(/^\/+/, "");
      if (!path.endsWith(".lean") && !path.includes("/")) path = path.replace(/\./g, "/") + ".lean";
      if (prefix && !path.startsWith(prefix)) path = prefix + path;
      const frag = node.line > 0 ? "#L" + Math.floor(node.line) : "";
      return safeHref(base + "/blob/" + encodeURIComponent(commit) + "/" + path + frag);
    }

    function refreshCoverage() {
      if (!state.tree || !state.tree.root) return;
      const stats = computeCoverageStats(state.tree.root, client.overlay, state.activeLayers, state.contributorFilter);
      clearEl(covBarEl);
      covBarEl.appendChild(h("span", null, [
        "Coverage with active layers: ",
        h("strong", null, fmtPct(stats.humanPct) + " human-verified"),
        " · ",
        fmtPct(stats.dossierPct) + " dossier/notes",
        " · ",
        fmtPct(stats.aiPct) + " AI draft",
        " · ",
        fmtPct(stats.flaggedPct) + " flagged"
      ]));
    }

    function renderLayerChips() {
      clearEl(layerChipsWrap);
      const layers = client.overlay.layers;
      if (!layers.length) {
        layerChipsWrap.appendChild(h("span", { class: "tm-muted" }, "No overlay layers loaded (showing unreviewed baseline)."));
      } else {
        for (const l of layers) {
          const on = state.activeLayers.has(l.id);
          const isAi = l.kind === "ai-draft";
          const dotCls = isAi ? "ai" : (l.kind === "dossier" ? "dossier" : "human");
          const chip = h("button", {
            type: "button",
            class: "tm-layer-chip" + (on ? "" : " off") + (isAi ? " ai" : ""),
            "aria-pressed": on ? "true" : "false",
            title: l.description || l.title,
            onclick: () => {
              if (state.activeLayers.has(l.id)) state.activeLayers.delete(l.id);
              else state.activeLayers.add(l.id);
              renderLayerChips();
              refreshCoverage();
              scheduleDraw();
              renderInspector();
            }
          }, [
            h("span", { class: "tm-layer-dot " + dotCls }),
            h("span", null, l.title),
            isAi ? h("span", { class: "tm-badge-ai" }, "AI draft") : null,
            h("span", { class: "tm-muted" }, "(" + fmtInt(l.count) + ")")
          ]);
          layerChipsWrap.appendChild(chip);
        }
      }

      clearEl(contribSelect);
      contribSelect.appendChild(h("option", { value: "" }, "All contributors"));
      for (const a of client.overlay.authors) {
        contribSelect.appendChild(h("option", { value: a }, a));
      }
      contribSelect.value = state.contributorFilter;
    }

    function renderLegend() {
      clearEl(legendStrip);
      const mode = state.colorMode;
      if (mode === "coverage") {
        const items = [
          ["Unreviewed", "var(--tm-unrev)", false],
          ["Human-verified", "var(--tm-human)", false],
          ["Dossier / note", "var(--tm-dossier)", false],
          ["AI draft (unverified)", "", true],
          ["Flagged / sorry / contested", "var(--tm-flagged)", false]
        ];
        for (const [lbl, bg, hatch] of items) {
          const sw = h("span", { class: "tm-leg-swatch" + (hatch ? " hatch" : "") });
          if (bg) sw.style.background = bg;
          legendStrip.appendChild(h("span", { class: "tm-leg-item" }, [sw, lbl]));
        }
      } else if (mode === "pillar") {
        const tbl = (state.tree && state.tree.tables && state.tree.tables.pillars) || [];
        const pal = isLightTheme() ? PILLAR_PALETTE_LIGHT : PILLAR_PALETTE_DARK;
        const shown = tbl.slice(0, 8);
        shown.forEach((lbl, i) => {
          const sw = h("span", { class: "tm-leg-swatch" });
          sw.style.background = pal[i % pal.length];
          legendStrip.appendChild(h("span", { class: "tm-leg-item" }, [sw, String(lbl || ("Part " + i))]));
        });
      } else if (mode === "sorry") {
        const items = [
          ["Clean (0 sorry)", "var(--tm-unrev)"],
          ["Challenge / comparator sorry", "var(--tm-ai)"],
          ["Proof sorry", "var(--tm-flagged)"]
        ];
        for (const [lbl, bg] of items) {
          const sw = h("span", { class: "tm-leg-swatch" });
          sw.style.background = bg;
          legendStrip.appendChild(h("span", { class: "tm-leg-item" }, [sw, lbl]));
        }
      } else {
        const grad = h("span", { class: "tm-grad-bar" });
        const labels = {
          novelty: ["Library-backed", "Project-native (unmatched)", "linear-gradient(90deg, #2f7d76, #6e788a, #c68e36)"],
          bloat: ["Compact", "Dense AST", "linear-gradient(90deg, #313947, #3e82a8, #c28434)"],
          heartbeats: ["Low", "High maxHeartbeats", "linear-gradient(90deg, #313947, #b88030, #c04a50)"],
          comments: ["0% comments", "Commented", "linear-gradient(90deg, #313947, #2e9286)"],
          compress: ["Unique names", "Repetitive names", "linear-gradient(90deg, #313947, #5670ae, #8e5cb2)"]
        };
        const [lo, hi, css] = labels[mode] || ["Low", "High", "linear-gradient(90deg, #313947, #7cc4e4)"];
        grad.style.background = css;
        legendStrip.appendChild(h("span", { class: "tm-leg-item" }, [lo, grad, hi]));
      }
      if (state.tree && !state.tree.hasComments) {
        legendStrip.appendChild(h("span", { class: "tm-caption-note" }, "Comments % unavailable (0% comments in this export)."));
      }
    }

    function renderCrumbs() {
      clearEl(crumbsEl);
      const chain = [];
      let cur = state.focusNode;
      while (cur) {
        chain.push(cur);
        cur = cur.parent;
      }
      chain.reverse();
      chain.forEach((n, idx) => {
        if (idx > 0) crumbsEl.appendChild(h("span", { class: "tm-crumb-sep", "aria-hidden": "true" }, "›"));
        const isLast = idx === chain.length - 1;
        const wStr = fmtCompact(nodeWeight(n));
        const label = (n.short || n.name) + " (" + wStr + ")";
        if (isLast) {
          crumbsEl.appendChild(h("span", { class: "tm-crumb cur", title: n.name }, label));
        } else {
          crumbsEl.appendChild(h("button", {
            type: "button",
            class: "tm-crumb",
            title: n.name,
            onclick: () => focusOnNode(n)
          }, label));
        }
      });
    }

    function syncSelectors() {
      // Size modes: hide options whose root sum <= 0
      clearEl(sizeSelect);
      const sizeDefs = Array.isArray(manifest.size_modes) && manifest.size_modes.length
        ? manifest.size_modes
        : [
          { id: "decls", label: "Declarations", col: "sz" },
          { id: "ast", label: "Proof AST size", col: "vn" },
          { id: "loc", label: "Lines of code", col: "loc" },
          { id: "mods", label: "Files", col: "mods" }
        ];
      const availableSizes = sizeDefs.filter((m) => {
        if (!state.tree || !state.tree.root) return true;
        return Number(state.tree.root[m.col]) > 0;
      });
      const useSizes = availableSizes.length ? availableSizes : [sizeDefs[0]];
      if (!useSizes.some((m) => m.col === state.sizeCol)) {
        state.sizeCol = useSizes[0].col;
      }
      for (const m of useSizes) {
        sizeSelect.appendChild(h("option", { value: m.col }, m.label));
      }
      sizeSelect.value = state.sizeCol;

      // Color modes: disable/hide comments if 0% across tree
      clearEl(colorSelect);
      const allowed = new Set(Array.isArray(manifest.color_modes) && manifest.color_modes.length
        ? manifest.color_modes
        : COLOR_MODE_DEFS.map((c) => c.id));
      for (const def of COLOR_MODE_DEFS) {
        if (!allowed.has(def.id)) continue;
        if (def.id === "comments" && state.tree && !state.tree.hasComments) continue;
        colorSelect.appendChild(h("option", { value: def.id }, def.label));
      }
      if (!Array.from(colorSelect.options).some((op) => op.value === state.colorMode)) {
        state.colorMode = colorSelect.options[0] ? colorSelect.options[0].value : "coverage";
      }
      colorSelect.value = state.colorMode;
    }

    // -------------------------------------------------------------------------
    // Lazy tile hydration
    // -------------------------------------------------------------------------
    async function ensureTileLoaded(node) {
      if (!node || !node.tile || node.tileLoaded || node.tileLoading) return;
      node.tileLoading = true;
      tilePill.classList.remove("hidden");
      try {
        const payload = await client.loadTile(state.viewSpec, node.tile, state.tree);
        spliceTileRows(node, payload, state.tree);
        state.ranges = computeColorMetricRanges(state.tree);
        refreshCoverage();
        renderInspector();
        scheduleDraw();
      } catch (err) {
        node.tileLoading = false;
        node.tileError = String(err && err.message || err);
      } finally {
        tilePill.classList.add("hidden");
      }
    }

    function focusOnNode(node) {
      if (!node) return;
      state.focusNode = node;
      state.selectedNode = node;
      state.cam = { x: 0, y: 0, zoom: 1 };
      zoomReadout.textContent = "1.0×";
      canvasWrap.classList.remove("zoomed");
      renderCrumbs();
      renderInspector();
      scheduleDraw();
      if (node.tile && !node.tileLoaded) {
        ensureTileLoaded(node);
      }
    }

    // -------------------------------------------------------------------------
    // Canvas drawing (nested squarified cushion treemap)
    // -------------------------------------------------------------------------
    let drawPending = false;
    function scheduleDraw() {
      if (drawPending) return;
      drawPending = true;
      const raf = typeof requestAnimationFrame === "function" ? requestAnimationFrame : (fn) => setTimeout(fn, 16);
      raf(() => {
        drawPending = false;
        drawCanvas();
      });
    }

    function truncateToWidth(ctx, text, maxW) {
      if (!text || maxW <= 4) return "";
      if (ctx.measureText(text).width <= maxW) return text;
      const ell = "…";
      const ellW = ctx.measureText(ell).width;
      if (ellW >= maxW) return "";
      let lo = 0;
      let hi = text.length;
      while (lo < hi) {
        const mid = (lo + hi + 1) >> 1;
        if (ctx.measureText(text.slice(0, mid)).width + ellW <= maxW) lo = mid;
        else hi = mid - 1;
      }
      return lo > 0 ? text.slice(0, lo) + ell : "";
    }

    function drawCanvas() {
      if (!state.tree || !state.focusNode) return;
      const rect = canvasWrap.getBoundingClientRect();
      const cw = Math.max(240, Math.floor(rect.width || canvasWrap.clientWidth || 720));
      const ch = Math.max(220, Math.floor(rect.height || canvasWrap.clientHeight || 480));
      const dpr = (typeof window !== "undefined" && window.devicePixelRatio) ? window.devicePixelRatio : 1;

      if (canvas.width !== Math.round(cw * dpr) || canvas.height !== Math.round(ch * dpr)) {
        canvas.width = Math.round(cw * dpr);
        canvas.height = Math.round(ch * dpr);
      }

      const ctx = canvas.getContext("2d");
      if (!ctx) return;
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

      const light = isLightTheme();
      const bgCol = cssVar("--bg-code", light ? "#f6f6f3" : "#0c0f13");
      const borderBase = light ? "rgba(23, 25, 28, 0.24)" : "rgba(255, 255, 255, 0.14)";
      const accentCol = cssVar("--accent", light ? "#1f6f96" : "#7cc4e4");
      const hatchPat = createAiHatchPattern(ctx, light);

      ctx.fillStyle = bgCol;
      ctx.fillRect(0, 0, cw, ch);

      const z = state.cam.zoom;
      const worldW = cw * z;
      const worldH = ch * z;
      state.cam.x = clamp(state.cam.x, Math.min(0, cw - worldW), 0);
      state.cam.y = clamp(state.cam.y, Math.min(0, ch - worldH), 0);

      const boxes = [];
      const fontFamily = cssVar("--sans", "sans-serif");
      const monoFamily = cssVar("--mono", "monospace");
      const nowMs = Date.now();
      const flashing = state.flashNodeId != null && nowMs < state.flashUntil;

      function paintNode(node, boxRect, depth, isHeaderOnly) {
        const { x, y, w, h: bh } = boxRect;
        if (w < 1.2 || bh < 1.2) return;
        if (x + w < 0 || y + bh < 0 || x > cw || y > ch) return;

        const hasKids = node.children && node.children.length > 0;
        const canRecurse = hasKids && depth < MAX_VISIBLE_DEPTH && w >= 28 && bh >= 26 && !isHeaderOnly;

        const colInfo = nodeColor(node, state.colorMode, state.ranges, light);
        ctx.fillStyle = colInfo.fill;
        ctx.fillRect(x, y, w, bh);

        if (colInfo.hatch && hatchPat) {
          ctx.fillStyle = hatchPat;
          ctx.fillRect(x, y, w, bh);
        }

        // Subtle cushion border shading
        if (w >= 6 && bh >= 6) {
          const grad = ctx.createLinearGradient(x, y, x, y + bh);
          grad.addColorStop(0, light ? "rgba(255,255,255,0.16)" : "rgba(255,255,255,0.08)");
          grad.addColorStop(1, light ? "rgba(0,0,0,0.08)" : "rgba(0,0,0,0.18)");
          ctx.fillStyle = grad;
          ctx.fillRect(x, y, w, bh);
        }

        ctx.strokeStyle = borderBase;
        ctx.lineWidth = 1;
        ctx.strokeRect(x + 0.5, y + 0.5, Math.max(0, w - 1), Math.max(0, bh - 1));

        const ink = contrastTextColor(colInfo.rgb);

        if (canRecurse) {
          const hdrH = w >= 48 && bh >= 34 ? clamp(Math.floor(bh * 0.13), 15, 20) : 0;
          const pad = w >= 40 && bh >= 40 ? 3 : 1.5;

          if (hdrH > 0) {
            const hdrAlpha = light ? 0.10 : 0.26;
            const hdrRgb = mixRgb(colInfo.rgb, [0, 0, 0], hdrAlpha);
            ctx.fillStyle = light ? "rgba(0,0,0,0.10)" : "rgba(0,0,0,0.26)";
            ctx.fillRect(x + 1, y + 1, w - 2, hdrH);
            ctx.font = "600 11px " + monoFamily;
            ctx.textBaseline = "middle";
            ctx.fillStyle = contrastTextColor(hdrRgb);
            const titleText = truncateToWidth(ctx, (node.short || node.name) + (node.tile && !node.tileLoaded ? " ⊕" : ""), w - 10);
            if (titleText) ctx.fillText(titleText, x + 5, y + 1 + hdrH / 2);
          }

          boxes.push({
            node,
            x,
            y,
            w,
            h: hdrH > 0 ? hdrH : bh,
            fullBox: boxRect,
            isContainer: true
          });

          const inner = {
            x: x + pad,
            y: y + hdrH + pad,
            w: w - pad * 2,
            h: bh - hdrH - pad * 2
          };
          if (inner.w >= 4 && inner.h >= 4) {
            const childItems = [];
            for (const chNode of node.children) {
              const cwVal = nodeWeight(chNode);
              if (cwVal > 0) childItems.push({ node: chNode, weight: cwVal });
            }
            const laid = squarify(childItems, inner);
            for (const cell of laid) {
              paintNode(cell.item.node, cell, depth + 1, false);
            }
          }
        } else {
          boxes.push({
            node,
            x,
            y,
            w,
            h: bh,
            fullBox: boxRect,
            isContainer: false
          });

          if (w >= 34 && bh >= 16) {
            ctx.save();
            ctx.beginPath();
            ctx.rect(x + 2, y + 2, w - 4, bh - 4);
            ctx.clip();

            const fontSize = w >= 120 && bh >= 48 ? 12 : 10.5;
            ctx.font = "600 " + fontSize + "px " + monoFamily;
            ctx.textBaseline = "top";
            ctx.fillStyle = ink;
            const lbl = truncateToWidth(ctx, node.short || node.name, w - 8);
            if (lbl) ctx.fillText(lbl, x + 4, y + 4);

            if (bh >= 34 && w >= 64) {
              ctx.font = "400 10px " + fontFamily;
              ctx.globalAlpha = 0.85;
              const sub = truncateToWidth(ctx, fmtCompact(nodeWeight(node)) + (node.tile && !node.tileLoaded ? " · zoom" : ""), w - 8);
              if (sub) ctx.fillText(sub, x + 4, y + 6 + fontSize + 2);
              ctx.globalAlpha = 1;
            }
            ctx.restore();
          }
        }
      }

      const rootBox = { x: state.cam.x, y: state.cam.y, w: worldW, h: worldH };
      const focusChildren = state.focusNode.children || [];
      if (focusChildren.length > 0) {
        const items = [];
        for (const chNode of focusChildren) {
          const wVal = nodeWeight(chNode);
          if (wVal > 0) items.push({ node: chNode, weight: wVal });
        }
        const laid = squarify(items, rootBox);
        for (const cell of laid) {
          paintNode(cell.item.node, cell, 0, false);
        }
      } else {
        paintNode(state.focusNode, rootBox, 0, false);
      }

      // Draw selection / hover / search flash rings on top
      const drawRing = (node, color, lw) => {
        if (!node) return;
        const match = boxes.find((b) => b.node === node);
        if (!match) return;
        const b = match.fullBox || match;
        ctx.save();
        ctx.strokeStyle = color;
        ctx.lineWidth = lw;
        ctx.strokeRect(b.x + lw / 2, b.y + lw / 2, Math.max(0, b.w - lw), Math.max(0, b.h - lw));
        ctx.restore();
      };

      if (state.hoveredNode && state.hoveredNode !== state.selectedNode) {
        drawRing(state.hoveredNode, light ? "rgba(23,25,28,0.6)" : "rgba(236,239,243,0.65)", 1.5);
      }
      if (state.selectedNode) {
        drawRing(state.selectedNode, accentCol, 2.5);
      }
      if (flashing) {
        const flashTarget = boxes.find((b) => String(b.node.id) === String(state.flashNodeId));
        if (flashTarget) {
          drawRing(flashTarget.node, cssVar("--amber", "#e0a95a"), 3);
        }
      }

      state.renderedBoxes = boxes;
    }

    function hitTest(px, py) {
      for (let i = state.renderedBoxes.length - 1; i >= 0; i--) {
        const b = state.renderedBoxes[i];
        if (px >= b.x && px <= b.x + b.w && py >= b.y && py <= b.y + b.h) {
          return b;
        }
      }
      return null;
    }

    // -------------------------------------------------------------------------
    // Inspector & Draft PR Composer
    // -------------------------------------------------------------------------
    function renderInspector() {
      clearEl(inspectorEl);
      const node = state.selectedNode || state.focusNode;
      if (!node) {
        inspectorEl.appendChild(h("p", { class: "tm-muted" }, "Select a rectangle to inspect details."));
        return;
      }

      const cov = node._cov || { humanPct: 0, dossierPct: 0, aiPct: 0, flaggedPct: 0, directEntries: [], contested: false };
      const ghUrl = resolveGithubUrl(node);

      // Path breadcrumbs inside inspector
      const ancestors = [];
      let p = node;
      while (p) { ancestors.push(p.short || p.name); p = p.parent; }
      ancestors.reverse();

      inspectorEl.appendChild(h("div", { class: "tm-ins-hd" }, [
        h("span", { class: "tm-ins-kicker" }, "Inspector"),
        h("span", { class: "tm-muted" }, node.kind || "node")
      ]));
      inspectorEl.appendChild(h("div", { class: "tm-ins-path" }, ancestors.join(" › ")));
      inspectorEl.appendChild(h("h2", { class: "tm-ins-title", title: node.name }, [identWbr(node.name)]));

      const badges = h("div", { class: "tm-ins-badges" });
      if (node.pillar) badges.appendChild(h("span", { class: "pill" }, node.pillar));
      if (node.hash) badges.appendChild(h("span", { class: "pill mono", title: "Signature hash" }, node.hash));
      if (node.tile && !node.tileLoaded) badges.appendChild(h("span", { class: "pill" }, "Deep tile available"));
      inspectorEl.appendChild(badges);

      // Action buttons
      const acts = h("div", { class: "tm-ins-actions" });
      if ((node.children && node.children.length > 0) || node.tile) {
        acts.appendChild(h("button", {
          type: "button",
          class: "btn sm primary",
          onclick: () => focusOnNode(node)
        }, "Zoom into box"));
      }
      const isDeclLike = !node.kind || !["folder", "root"].includes(node.kind);
      if (isDeclLike && node.name) {
        acts.appendChild(h("a", {
          class: "btn sm",
          href: "#item/" + encodeURIComponent(node.name) + "?tab=source",
          onclick: (e) => {
            if (typeof o.onNavigateItem === "function") {
              e.preventDefault();
              o.onNavigateItem(node.name, "source");
            }
          }
        }, "Lean Source ›"));
        acts.appendChild(h("a", {
          class: "btn sm",
          href: "#xrefs/" + encodeURIComponent(node.name),
          onclick: (e) => {
            if (typeof o.onNavigateXref === "function") {
              e.preventDefault();
              o.onNavigateXref(node.name);
            }
          }
        }, "Cross-refs ›"));
      }
      if (ghUrl) {
        acts.appendChild(h("a", {
          class: "btn sm",
          href: ghUrl,
          target: "_blank",
          rel: "noopener noreferrer"
        }, "Proof file ↗"));
        if (typeof o.onPeekSource === "function" && node.mod) {
          acts.appendChild(h("button", {
            type: "button",
            class: "btn sm",
            onclick: () => o.onPeekSource(node.mod, node.line > 0 ? node.line : undefined, node.name)
          }, "Peek"));
        }
      }
      inspectorEl.appendChild(acts);

      // Stats grid
      const statsGrid = h("div", { class: "tm-stats-grid" });
      const addStat = (k, v) => {
        statsGrid.appendChild(h("div", { class: "tm-stat" }, [
          h("div", { class: "tm-stat-v" }, v),
          h("div", { class: "tm-stat-k" }, k)
        ]));
      };
      const isSourceMode = manifest.mode === "source";
      addStat("Declarations", fmtInt(node.sz));
      addStat("Proof AST size", isSourceMode && !node.vn ? "—" : fmtInt(node.vn));
      addStat("Lines of code", fmtInt(node.loc));
      addStat("Files", fmtInt(node.mods));
      addStat("Library match", isSourceMode && !node.mathlib_pct ? "—" : fmtPct(node.mathlib_pct));
      addStat("Heartbeats", node.hb_cnt > 0 ? (fmtInt(node.hb_cnt) + " (max " + fmtCompact(node.hb_max) + ")") : "0");
      addStat("Comments %", state.tree && state.tree.hasComments ? fmtPct(node.comment_pct / (node.comment_pct > 1 ? 100 : 1)) : "0%");
      addStat("Sorry (proof / chal)", fmtInt(node.sorry_p) + " / " + fmtInt(node.sorry_c));
      addStat("Wrapper %", isSourceMode && !node.wrapper_pct ? "—" : fmtPct(node.wrapper_pct));
      addStat("Human verified", fmtPct(cov.humanPct));
      inspectorEl.appendChild(statsGrid);

      // Top children mini-list
      if (node.children && node.children.length > 0) {
        const sortedKids = node.children.slice().sort((a, b) => nodeWeight(b) - nodeWeight(a)).slice(0, 10);
        const ul = h("ul", { class: "tm-children-list" });
        for (const ch of sortedKids) {
          ul.appendChild(h("li", null, [
            h("button", {
              type: "button",
              class: "tm-child-btn",
              title: ch.name,
              onclick: () => focusOnNode(ch)
            }, [
              h("span", { class: "tm-child-name" }, ch.short || ch.name),
              h("span", { class: "tm-child-w" }, fmtCompact(nodeWeight(ch)))
            ])
          ]));
        }
        inspectorEl.appendChild(h("section", null, [
          h("h3", { class: "tm-sec-title" }, "Top nested blocks (" + fmtInt(node.children.length) + ")"),
          ul
        ]));
      }

      // Attached annotations & dossiers
      const annSec = h("section", { class: "tm-annots" });
      annSec.appendChild(h("h3", { class: "tm-sec-title" }, "Annotations & Dossiers (" + cov.directEntries.length + ")"));

      if (cov.contested) {
        annSec.appendChild(h("div", { class: "tm-contested-banner", role: "alert" },
          "Contested: active layers disagree on this target (verified vs flagged)."
        ));
      }

      if (!cov.directEntries.length) {
        annSec.appendChild(h("p", { class: "tm-muted", style: "margin:0;font-size:12px;" },
          "No active overlay entries directly on this node."
        ));
      } else {
        for (const e of cov.directEntries) {
          const layerMeta = client.overlay.layerMap.get(e.layer);
          const lKind = (layerMeta && layerMeta.kind) || inferLayerKind({ id: e.layer, kind: e.kind }, [e]);
          const isAi = lKind === "ai-draft" || e.draft || String(e.author || "").startsWith("ai:");
          const trustBadge = isAi
            ? h("span", { class: "tm-badge-ai" }, "AI draft")
            : (lKind === "dossier" || e.dossier_route
              ? h("span", { class: "tm-badge-note" }, "Review note")
              : h("span", { class: "tm-badge-human" }, "Human review"));

          const card = h("article", { class: "tm-annot-card" + (isAi ? " ai" : "") });
          const top = h("div", { class: "tm-annot-top" }, [
            trustBadge,
            e.status ? h("span", { class: isNegativeEntry(e) ? "tm-badge-flagged" : "pill" }, e.status) : null,
            e.author ? h("span", { class: "tm-annot-author" }, e.author) : null
          ]);
          card.appendChild(top);
          if (e.note) card.appendChild(h("p", { class: "tm-annot-note" }, e.note));
          if (e.breaks) card.appendChild(h("p", { class: "tm-annot-breaks" }, "Caveat: " + e.breaks));

          const links = h("div", { class: "tm-annot-links" });
          const uHref = safeHref(e.url || (e.source && e.source.startsWith("http") ? e.source : ""));
          if (uHref) {
            links.appendChild(h("a", { href: uHref, target: "_blank", rel: "noopener noreferrer" }, "Source ↗"));
          } else if (e.source) {
            links.appendChild(h("span", { class: "tm-muted" }, e.source));
          }
          if (e.dossier_route) {
            const dHref = safeHref(e.dossier_route.startsWith("#") ? e.dossier_route : ("#" + e.dossier_route));
            if (dHref) {
              links.appendChild(h("a", { href: dHref }, "Open dossier ›"));
            }
          }
          if (links.childNodes.length) card.appendChild(links);
          annSec.appendChild(card);
        }
      }
      inspectorEl.appendChild(annSec);

      // Inline "Annotate / Draft PR" composer
      const toggleBtn = h("button", {
        type: "button",
        class: "btn sm",
        onclick: () => {
          state.composerOpen = !state.composerOpen;
          if (state.composerOpen && !state.draftSource && ghUrl) state.draftSource = ghUrl;
          renderInspector();
        }
      }, state.composerOpen ? "Hide Draft PR composer" : "+ Annotate chunk / Draft PR");
      inspectorEl.appendChild(toggleBtn);

      if (state.composerOpen) {
        inspectorEl.appendChild(renderComposer(node, ghUrl));
      }
    }

    function renderComposer(node, ghUrl) {
      if (!state.draftSource && ghUrl) state.draftSource = ghUrl;
      const box = h("section", { class: "tm-composer", "aria-label": "Draft annotation PR composer" });

      const targetType = node.kind === "folder" || node.kind === "root" ? "folder" : (node.kind === "module" ? "module" : "decl");

      box.appendChild(h("div", { class: "tm-field" }, [
        h("span", null, "Target (" + targetType + ") & project"),
        h("div", { class: "tm-ro" }, (manifest.slug || "project") + " · " + node.name + (node.hash ? (" · " + node.hash) : ""))
      ]));

      const kindSel = h("select", { class: "tm-select" }, [
        h("option", { value: "human-review" }, "human-review"),
        h("option", { value: "ai-draft" }, "ai-draft"),
        h("option", { value: "bot-check" }, "bot-check")
      ]);
      kindSel.value = state.draftKind;

      const statusSel = h("select", { class: "tm-select" }, [
        h("option", { value: "summary" }, "summary"),
        h("option", { value: "read" }, "read"),
        h("option", { value: "verified" }, "verified"),
        h("option", { value: "flagged" }, "flagged")
      ]);
      statusSel.value = state.draftStatus;

      const authorIn = h("input", {
        type: "text",
        class: "tm-input",
        placeholder: state.draftKind === "human-review" ? "@alice" : "ai:model-name",
        value: state.draftAuthor
      });
      const sourceIn = h("input", {
        type: "text",
        class: "tm-input",
        placeholder: "https://github.com/owner/repo/blob/<sha>/...#L10",
        value: state.draftSource
      });
      const noteIn = h("textarea", {
        class: "tm-textarea",
        placeholder: "Concise mathematical summary of what this declaration proves and depends on…",
        textContent: state.draftNote
      });
      noteIn.value = state.draftNote;

      const breaksIn = h("textarea", {
        class: "tm-textarea",
        style: "min-height:48px;",
        placeholder: "Optional caveats / where an analogy or draft might break (required for ai-draft)…"
      });
      breaksIn.value = state.draftBreaks;

      const valHost = h("div", { class: "tm-val-issues" });
      const pathPreview = h("div", { class: "tm-ro" });
      const toastEl = h("div", { class: "tm-toast" }, state.draftToast || "");

      const copyBtn = h("button", { type: "button", class: "btn sm" }, "Copy JSONL");
      const dlBtn = h("button", { type: "button", class: "btn sm" }, "Download .jsonl");
      const prLink = h("a", { class: "btn sm primary", target: "_blank", rel: "noopener noreferrer" }, "Open draft PR on GitHub ↗");

      const refreshComposer = () => {
        state.draftKind = kindSel.value;
        state.draftStatus = statusSel.value;
        state.draftAuthor = authorIn.value;
        state.draftSource = sourceIn.value;
        state.draftNote = noteIn.value;
        state.draftBreaks = breaksIn.value;

        const draftPayload = {
          slug: manifest.slug || "project",
          target: targetType,
          name: node.name,
          sighash: node.hash || "",
          dom_subtree: node.sz,
          kind: state.draftKind,
          status: state.draftStatus,
          author: state.draftAuthor,
          note: state.draftNote,
          source: state.draftSource,
          breaks: state.draftBreaks
        };
        const res = validateDraft(draftPayload);
        pathPreview.textContent = "Target file: " + res.path;
        clearEl(valHost);
        for (const err of res.errors) valHost.appendChild(h("div", { class: "tm-val-err" }, err));
        for (const w of res.warnings) valHost.appendChild(h("div", { class: "tm-val-warn" }, w));
        if (res.valid && !res.warnings.length) {
          valHost.appendChild(h("div", { class: "tm-val-ok" }, "Valid leanre.annot/1 record ready for PR."));
        }

        const jsonl = buildDraftJsonl(draftPayload);
        const ghInfo = buildGithubNewPrUrl(res.path, jsonl, o.toolRepoUrl);
        if (!res.valid) {
          prLink.classList.add("hidden");
        } else if (ghInfo.tooLong) {
          prLink.classList.add("hidden");
          valHost.appendChild(h("div", { class: "tm-val-warn" }, "Payload exceeds 7,000-character URL limit; copy or download .jsonl and upload on GitHub."));
        } else {
          prLink.classList.remove("hidden");
          prLink.setAttribute("href", ghInfo.url);
        }
        return { res, jsonl };
      };

      kindSel.addEventListener("change", () => {
        authorIn.placeholder = kindSel.value === "human-review" ? "@alice" : "ai:model-name";
        refreshComposer();
      });
      statusSel.addEventListener("change", refreshComposer);
      authorIn.addEventListener("input", refreshComposer);
      sourceIn.addEventListener("input", refreshComposer);
      noteIn.addEventListener("input", refreshComposer);
      breaksIn.addEventListener("input", refreshComposer);

      copyBtn.addEventListener("click", async () => {
        const { res, jsonl } = refreshComposer();
        if (!res.valid) { toastEl.textContent = "Fix validation errors before copying."; return; }
        try {
          if (navigator.clipboard && navigator.clipboard.writeText) {
            await navigator.clipboard.writeText(jsonl);
            toastEl.textContent = "Copied JSONL to clipboard.";
          } else {
            toastEl.textContent = "Clipboard unavailable; use Download .jsonl.";
          }
        } catch (_) {
          toastEl.textContent = "Clipboard copy blocked; use Download .jsonl.";
        }
      });

      dlBtn.addEventListener("click", () => {
        const { res, jsonl } = refreshComposer();
        if (!res.valid) { toastEl.textContent = "Fix validation errors before downloading."; return; }
        const blob = new Blob([jsonl], { type: "application/x-ndjson;charset=utf-8" });
        const url = URL.createObjectURL(blob);
        const a = document.createElement("a");
        a.href = url;
        a.download = res.path.split("/").pop() || "annotation.jsonl";
        document.body.appendChild(a);
        a.click();
        a.remove();
        setTimeout(() => URL.revokeObjectURL(url), 1000);
        toastEl.textContent = "Downloaded " + a.download;
      });

      box.appendChild(h("div", { class: "tm-field-row" }, [
        h("label", { class: "tm-field" }, [h("span", null, "Kind"), kindSel]),
        h("label", { class: "tm-field" }, [h("span", null, "Status"), statusSel])
      ]));
      box.appendChild(h("label", { class: "tm-field" }, [h("span", null, "Author / handle"), authorIn]));
      box.appendChild(h("label", { class: "tm-field" }, [h("span", null, "Summary / mathematical note"), noteIn]));
      box.appendChild(h("label", { class: "tm-field" }, [h("span", null, "Evidence link"), sourceIn]));
      box.appendChild(h("label", { class: "tm-field" }, [h("span", null, "Caveats / what breaks"), breaksIn]));
      box.appendChild(pathPreview);
      box.appendChild(valHost);
      box.appendChild(h("div", { class: "tm-composer-acts" }, [copyBtn, dlBtn, prLink]));
      box.appendChild(toastEl);

      refreshComposer();
      return box;
    }

    // -------------------------------------------------------------------------
    // Search jump
    // -------------------------------------------------------------------------
    function jumpToNode(node) {
      if (!node) return;
      const targetFocus = (node.children && node.children.length > 0) ? node : (node.parent || state.tree.root);
      state.focusNode = targetFocus;
      state.selectedNode = node;
      state.cam = { x: 0, y: 0, zoom: 1 };
      zoomReadout.textContent = "1.0×";
      state.flashNodeId = node.id;
      state.flashUntil = Date.now() + 1400;
      setTimeout(scheduleDraw, 1450);
      renderCrumbs();
      renderInspector();
      scheduleDraw();
    }

    function updateSearchList() {
      const q = String(searchInput.value || "").trim().toLowerCase();
      clearEl(acList);
      if (!q || !state.tree) {
        acList.classList.add("hidden");
        return;
      }
      const hits = [];
      for (const n of state.tree.allNodes) {
        const hay = (n.name + " " + n.short).toLowerCase();
        if (hay.includes(q)) {
          hits.push(n);
          if (hits.length >= 25) break;
        }
      }
      hits.sort((a, b) => {
        const aPre = a.short.toLowerCase().startsWith(q) || a.name.toLowerCase().startsWith(q) ? 0 : 1;
        const bPre = b.short.toLowerCase().startsWith(q) || b.name.toLowerCase().startsWith(q) ? 0 : 1;
        return (aPre - bPre) || (nodeWeight(b) - nodeWeight(a));
      });
      if (!hits.length) {
        acList.appendChild(h("li", { class: "tm-ac-item" }, h("span", { class: "tm-muted" }, "No loaded matches for \"" + searchInput.value + "\"")));
        acList.classList.remove("hidden");
        return;
      }
      for (const n of hits.slice(0, 14)) {
        acList.appendChild(h("li", {
          class: "tm-ac-item",
          role: "option",
          onclick: () => {
            acList.classList.add("hidden");
            searchInput.value = n.short || n.name;
            jumpToNode(n);
          }
        }, [
          h("span", { class: "tm-ac-name", title: n.name }, n.name),
          h("span", { class: "tm-ac-meta" }, fmtCompact(nodeWeight(n)))
        ]));
      }
      acList.classList.remove("hidden");
    }

    searchInput.addEventListener("input", updateSearchList);
    searchInput.addEventListener("keydown", (e) => {
      if (e.key === "Enter") {
        const firstOpt = acList.querySelector(".tm-ac-item[role='option']");
        if (firstOpt) firstOpt.click();
      } else if (e.key === "Escape") {
        acList.classList.add("hidden");
      }
    });
    document.addEventListener("click", (e) => {
      if (!searchWrap.contains(e.target)) acList.classList.add("hidden");
    });

    // -------------------------------------------------------------------------
    // Zoom, Pan, Pointer/Pinch & Wheel interactions
    // -------------------------------------------------------------------------
    function applyZoomAt(factor, cx, cy) {
      const rect = canvasWrap.getBoundingClientRect();
      const cw = rect.width || 720;
      const ch = rect.height || 480;
      const px = cx != null ? cx : cw / 2;
      const py = cy != null ? cy : ch / 2;
      const oldZ = state.cam.zoom;
      const newZ = clamp(oldZ * factor, 1, 24);
      const scale = newZ / oldZ;
      state.cam.x = px - (px - state.cam.x) * scale;
      state.cam.y = py - (py - state.cam.y) * scale;
      state.cam.zoom = newZ;
      zoomReadout.textContent = newZ.toFixed(1) + "×";
      canvasWrap.classList.toggle("zoomed", newZ > 1.05);
      scheduleDraw();
    }

    zoomInBtn.addEventListener("click", () => applyZoomAt(1.4));
    zoomOutBtn.addEventListener("click", () => applyZoomAt(1 / 1.4));
    upBtn.addEventListener("click", () => {
      if (state.focusNode && state.focusNode.parent) focusOnNode(state.focusNode.parent);
    });
    resetBtn.addEventListener("click", () => {
      if (state.tree && state.tree.root) focusOnNode(state.tree.root);
    });

    function setFullScreen(on) {
      state.fullScreen = Boolean(on);
      shell.classList.toggle("fs-on", state.fullScreen);
      if (hasDoc) document.body.classList.toggle("fs-lock", state.fullScreen);
      fsBtn.textContent = state.fullScreen ? "✕ Exit full screen" : "⛶ Full screen";
      scheduleDraw();
    }

    fsBtn.addEventListener("click", () => setFullScreen(!state.fullScreen));
    if (hasDoc) {
      document.addEventListener("keydown", (e) => {
        if (e.key === "Escape" && state.fullScreen) setFullScreen(false);
      });
    }

    canvasWrap.addEventListener("wheel", (e) => {
      const canScrollZoom = e.ctrlKey || e.metaKey || state.fullScreen || state.cam.zoom > 1.05;
      if (!canScrollZoom) {
        flashZoomHint();
        return;
      }
      e.preventDefault();
      const rect = canvasWrap.getBoundingClientRect();
      const factor = e.deltaY < 0 ? 1.15 : (1 / 1.15);
      applyZoomAt(factor, e.clientX - rect.left, e.clientY - rect.top);
    }, { passive: false });

    const activePointers = new Map();
    let dragMoved = false;
    let dragStart = null;
    let lastPinchDist = null;
    let lastTapTime = 0;
    let lastTapNode = null;

    canvasWrap.addEventListener("pointerdown", (e) => {
      if (e.button !== 0 && e.pointerType === "mouse") return;
      activePointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
      dragMoved = false;
      dragStart = { x: e.clientX, y: e.clientY, camX: state.cam.x, camY: state.cam.y };
      if (activePointers.size === 2) {
        const pts = Array.from(activePointers.values());
        lastPinchDist = Math.hypot(pts[1].x - pts[0].x, pts[1].y - pts[0].y);
      }
      try { canvasWrap.setPointerCapture(e.pointerId); } catch (_) {}
    });

    canvasWrap.addEventListener("pointermove", (e) => {
      const rect = canvasWrap.getBoundingClientRect();
      const lx = e.clientX - rect.left;
      const ly = e.clientY - rect.top;

      if (activePointers.has(e.pointerId)) {
        activePointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
        if (activePointers.size === 2) {
          const pts = Array.from(activePointers.values());
          const dist = Math.hypot(pts[1].x - pts[0].x, pts[1].y - pts[0].y);
          if (lastPinchDist && dist > 0) {
            const mx = ((pts[0].x + pts[1].x) / 2) - rect.left;
            const my = ((pts[0].y + pts[1].y) / 2) - rect.top;
            applyZoomAt(dist / lastPinchDist, mx, my);
            dragMoved = true;
          }
          lastPinchDist = dist;
          return;
        }
        if (dragStart) {
          const dx = e.clientX - dragStart.x;
          const dy = e.clientY - dragStart.y;
          if (Math.hypot(dx, dy) > 4) {
            dragMoved = true;
            if (state.cam.zoom > 1.01) {
              canvasWrap.classList.add("panning");
              state.cam.x = dragStart.camX + dx;
              state.cam.y = dragStart.camY + dy;
              scheduleDraw();
            }
          }
        }
        return;
      }

      const hit = hitTest(lx, ly);
      const nextHover = hit ? hit.node : null;
      if (nextHover !== state.hoveredNode) {
        state.hoveredNode = nextHover;
        scheduleDraw();
      }
      if (hit) {
        const n = hit.node;
        const cov = n._cov || { humanPct: 0, aiPct: 0 };
        clearEl(tipEl);
        tipEl.appendChild(h("div", { class: "tm-tip-title" }, n.name));
        tipEl.appendChild(h("div", null, [
          (n.kind || "node") + " · " + fmtCompact(nodeWeight(n)),
          n.pillar ? (" · " + n.pillar) : ""
        ]));
        if (state.colorMode === "coverage") {
          tipEl.appendChild(h("div", null, "Human: " + fmtPct(cov.humanPct) + " · AI draft: " + fmtPct(cov.aiPct)));
        }
        tipEl.style.left = clamp(lx + 14, 6, Math.max(6, rect.width - 290)) + "px";
        tipEl.style.top = clamp(ly + 14, 6, Math.max(6, rect.height - 90)) + "px";
        tipEl.classList.remove("hidden");
      } else {
        tipEl.classList.add("hidden");
      }
    });

    const endPointer = (e) => {
      const wasDown = activePointers.has(e.pointerId);
      activePointers.delete(e.pointerId);
      if (activePointers.size < 2) lastPinchDist = null;
      canvasWrap.classList.remove("panning");
      if (!wasDown || dragMoved) return;

      const rect = canvasWrap.getBoundingClientRect();
      const hit = hitTest(e.clientX - rect.left, e.clientY - rect.top);
      if (!hit) return;
      const nowTap = Date.now();
      const isDoubleTap = hit.node === lastTapNode && (nowTap - lastTapTime) < 340;
      lastTapTime = nowTap;
      lastTapNode = hit.node;

      state.selectedNode = hit.node;
      renderInspector();
      scheduleDraw();

      if (isDoubleTap && ((hit.node.children && hit.node.children.length > 0) || hit.node.tile)) {
        focusOnNode(hit.node);
      } else if (hit.node.tile && !hit.node.tileLoaded && hit.node === state.focusNode) {
        ensureTileLoaded(hit.node);
      }
    };

    canvasWrap.addEventListener("pointerup", endPointer);
    canvasWrap.addEventListener("pointercancel", (e) => {
      activePointers.delete(e.pointerId);
      lastPinchDist = null;
      canvasWrap.classList.remove("panning");
    });
    canvasWrap.addEventListener("pointerleave", () => {
      tipEl.classList.add("hidden");
      if (state.hoveredNode) {
        state.hoveredNode = null;
        scheduleDraw();
      }
    });

    // ResizeObserver for Retina responsiveness
    let ro = null;
    if (typeof ResizeObserver === "function") {
      ro = new ResizeObserver(() => scheduleDraw());
      ro.observe(canvasWrap);
    }

    // Control event bindings
    sizeSelect.addEventListener("change", () => {
      state.sizeCol = sizeSelect.value;
      renderCrumbs();
      renderInspector();
      scheduleDraw();
    });

    colorSelect.addEventListener("change", () => {
      state.colorMode = colorSelect.value;
      renderLegend();
      scheduleDraw();
    });

    contribSelect.addEventListener("change", () => {
      state.contributorFilter = contribSelect.value;
      refreshCoverage();
      renderInspector();
      scheduleDraw();
    });

    async function switchView(viewId) {
      state.viewId = viewId;
      for (const btn of viewSeg.querySelectorAll("button")) {
        const active = btn.getAttribute("data-view") === viewId;
        btn.classList.toggle("active", active);
        btn.setAttribute("aria-pressed", active ? "true" : "false");
      }
      const { spec, tree } = await client.loadView(viewId);
      state.viewSpec = spec;
      state.tree = tree;
      state.ranges = computeColorMetricRanges(tree);
      state.focusNode = tree.root;
      state.selectedNode = tree.root;
      state.cam = { x: 0, y: 0, zoom: 1 };
      zoomReadout.textContent = "1.0×";
      syncSelectors();
      renderLayerChips();
      refreshCoverage();
      renderLegend();
      renderCrumbs();
      renderInspector();
      scheduleDraw();
    }

    for (const v of views) {
      viewSeg.appendChild(h("button", {
        type: "button",
        "data-view": v.id,
        class: v.id === state.viewId ? "active" : "",
        "aria-pressed": v.id === state.viewId ? "true" : "false",
        onclick: () => switchView(v.id)
      }, v.label));
    }

    await switchView(state.viewId);

    return {
      root: rootEl,
      client,
      state,
      switchView,
      focusOnNode,
      jumpToNode,
      destroy: () => { if (ro) ro.disconnect(); }
    };
  }

  // ---------------------------------------------------------------------------
  // Self-test (for #selftest=1 and Node CI verification)
  // ---------------------------------------------------------------------------
  async function runSelfTest(assert, opts) {
    const o = opts || {};
    const results = { pass: true, checks: 0 };
    const ok = (cond, msg) => {
      results.checks++;
      if (!cond) results.pass = false;
      assert(!!cond, "treemap: " + msg);
    };

    // 1. Gzip sniffer
    ok(isGzip(new Uint8Array([0x1f, 0x8b, 0x08])) === true, "detects gzip magic 1f 8b");
    ok(isGzip(new Uint8Array([0x7b, 0x22])) === false, "passes non-gzip JSON through");
    const plain = new Uint8Array([123, 125]);
    ok((await gunzipIfNeeded(plain)) === plain, "plain bytes pass through gunzipIfNeeded");

    // 2. Squarify invariants
    const laid = squarify(
      [{ id: "a", weight: 60 }, { id: "b", weight: 25 }, { id: "c", weight: 10 }, { id: "d", weight: 5 }],
      { x: 0, y: 0, w: 400, h: 200 }
    );
    ok(laid.length === 4, "squarify emits one box per positive-weight item");
    const areaSum = laid.reduce((s, r) => s + r.w * r.h, 0);
    ok(Math.abs(areaSum - 80000) < 1e-3, "squarify conserves total rectangle area");
    ok(laid.every((r) => r.x >= -1e-6 && r.y >= -1e-6 && r.x + r.w <= 400 + 1e-6 && r.y + r.h <= 200 + 1e-6),
      "squarify stays inside container bounds");

    // 3. Column-name resolution & lazy tile splicing
    const colsRev = ["name", "sz", "p", "id", "kind", "pillar", "vn", "loc", "mods", "mod", "line", "depth", "hash", "tile", "mathlib_pct", "hb_cnt", "hb_max", "comment_pct", "sorry_p", "sorry_c", "orphan_pct", "wrapper_pct", "compress", "short"];
    const tree = parseTreePayload({
      schema: TREE_SCHEMA,
      view: "dom",
      root_name: "Main",
      tables: { kinds: ["thm"], pillars: ["Spine", "Pillar A"], mods: ["Main"] },
      cols: colsRev,
      rows: [
        ["Main", 100, -1, 1, 0, 0, 500, 120, 1, 0, 1, 0, "", "", 0.1, 0, 0, 0, 0, 0, 0, 0, 0.2, "Main"],
        ["PillarA.sub", 60, 0, 2, 0, 1, 300, 70, 1, 0, 10, 1, "k1n:0123456789abcdef", "2", 0.2, 0, 0, 0, 0, 0, 0, 0, 0.2, "sub"],
        ["Other.leaf", 40, 0, 3, 0, 0, 200, 50, 1, 0, 50, 1, "", "", 0.5, 0, 0, 0, 0, 0, 0, 0, 0.3, "leaf"]
      ]
    });
    ok(tree.root && tree.root.children.length === 2, "column-index-agnostic parser builds tree");
    const subNode = tree.nodesByName.get("PillarA.sub");
    const spliceRes = spliceTileRows(subNode, {
      schema: TREE_SCHEMA,
      view: "dom",
      tables: { kinds: ["thm"], pillars: ["Pillar A"], mods: ["SubMod"] },
      cols: ["id", "p", "name", "sz", "vn", "loc"],
      rows: [
        [2, -1, "PillarA.sub", 60, 300, 70],
        [20, 0, "PillarA.leaf1", 35, 180, 40],
        [21, 0, "PillarA.leaf2", 25, 120, 30]
      ]
    }, tree);
    ok(spliceRes.added === 2 && subNode.children.length === 2 && subNode.tileLoaded, "lazy tile splices children cleanly");

    // 4. Overlay & coverage roll-up toggling
    const ov = normalizeOverlay({
      schema: OVERLAY_SCHEMA,
      layers: [
        { id: "human/facts", title: "Human", kind: "human-review", default_on: true },
        { id: "ai/drafts", title: "AI", kind: "ai-draft", default_on: false }
      ],
      entries: {
        "PillarA.leaf1": [{ layer: "human/facts", status: "verified", author: "@alice", note: "Checked." }],
        "Other.leaf": [{ layer: "ai/drafts", status: "summary", draft: true, author: "ai:gpt", note: "Draft note." }]
      }
    });
    const covOff = computeCoverageStats(tree.root, ov, new Set(["human/facts"]), "");
    ok(Math.abs(covOff.humanPct - 0.35) < 1e-6 && covOff.aiPct === 0, "coverage roll-up with AI layer OFF");
    const covOn = computeCoverageStats(tree.root, ov, new Set(["human/facts", "ai/drafts"]), "");
    ok(Math.abs(covOn.humanPct - 0.35) < 1e-6 && Math.abs(covOn.aiPct - 0.40) < 1e-6, "toggling AI draft layer updates roll-up");

    // 5. Draft PR validator & JSONL builder
    const badOverclaim = validateDraft({
      slug: "riemann-hypothesis",
      name: "Claim.zeta",
      author: "@alice",
      note: "This proves RH completely.",
      source: "https://github.com/o/r/blob/40e56bab026552e089d7afcfeff08d2defb9c005/Main.lean#L10"
    });
    ok(!badOverclaim.valid, "validator rejects RH overclaim phrasing");

    const badXss = validateDraft({
      slug: "riemann-hypothesis",
      name: "Claim.zeta",
      author: "@alice",
      note: "Summary <script>alert(1)</script>",
      source: "https://github.com/o/r/blob/40e56bab026552e089d7afcfeff08d2defb9c005/Main.lean#L10"
    });
    ok(!badXss.valid, "validator rejects XSS markup");

    const badMainUrl = validateDraft({
      slug: "riemann-hypothesis",
      name: "Claim.zeta",
      author: "@alice",
      note: "Clean local summary.",
      source: "https://github.com/o/r/blob/main/Main.lean#L10"
    });
    ok(!badMainUrl.valid, "validator rejects floating /blob/main/ URL");

    const goodDraft = {
      slug: "riemann-hypothesis",
      name: "Claim.zeta",
      sighash: "k1n:0123456789abcdef0123456789abcdef",
      kind: "human-review",
      status: "verified",
      author: "@alice",
      note: "Verified local reduction to primitive character strip.",
      source: "https://github.com/o/r/blob/40e56bab026552e089d7afcfeff08d2defb9c005/Main.lean#L75"
    };
    const goodRes = validateDraft(goodDraft);
    const jsonl = buildDraftJsonl(goodDraft);
    const lines = jsonl.trim().split("\n").map((l) => JSON.parse(l));
    ok(goodRes.valid && lines.length === 3 && lines[0].schema === ANNOT_SCHEMA && lines[2].sighash === goodDraft.sighash,
      "buildDraftJsonl emits valid 3-line leanre.annot/1 pack");

    if (o.host && hasDoc) {
      await renderExplorer(o.host, o);
      ok((o.host.textContent || "").length > 0, "renderExplorer renders into host");
    }

    return results;
  }

  const api = {
    version: VERSION,
    SCHEMA,
    TREE_SCHEMA,
    OVERLAY_SCHEMA,
    ANNOT_SCHEMA,
    TreemapClient,
    renderExplorer,
    runSelfTest,
    squarify,
    buildDraftJsonl,
    validateDraft,
    buildDraftPath,
    buildGithubNewPrUrl,
    isGzip,
    gunzipIfNeeded,
    parseTreePayload,
    spliceTileRows,
    normalizeOverlay,
    computeCoverageStats
  };

  root.LeanreTreemap = api;
  if (typeof module !== "undefined" && module.exports) module.exports = api;
})(typeof window !== "undefined" ? window : globalThis);
