/* leanre interactive zoomable nested-rectangle proof treemap explorer & draft PR composer.
 *
 * Reads static `leanre.treemap/1` exports (`manifest.json`, `dom.lxrt`, `folder.lxrt`,
 * lazy `tiles_<view>/{id}.lxrt`, and optional `overlay.json`) and exposes:
 *   - window.LeanreTreemap.renderExplorer(host, opts)
 *   - window.LeanreTreemap.runSelfTest(assert, opts)
 *   - window.LeanreTreemap.squarify(items, rect)
 *   - window.LeanreTreemap.layoutTreemap(focus, rect, opts)   (pixel-gated, unary-collapsed)
 *   - window.LeanreTreemap.rasterizeBoxes(ctx, boxes, opts)   (offscreen cushion raster)
 *   - window.LeanreTreemap.nodeSelectPayload(node)            (opts.onSelectNode payload)
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

  const VERSION = "2.7.2";
  const SCHEMA = "leanre.treemap/1";
  const TREE_SCHEMA = "leanre.treemap.tree/1";
  const OVERLAY_SCHEMA = "leanre.treemap.overlay/1";
  const ANNOT_SCHEMA = "leanre.annot/1";

  const DEFAULT_TOOL_REPO = "https://github.com/bohemian-miser/leanre";
  const TILE_LRU_CAP = 64;
  const MAX_GH_NEW_URL_LEN = 7000;
  // Deep pixel-gated layout: recurse into any box still >= MIN_RECURSE_PX on screen.
  const MAX_VISIBLE_DEPTH = 32;
  const MIN_RECURSE_PX = 2.5;
  const MAX_LAYOUT_BOXES = 60000;
  const UNARY_COLLAPSE_FRAC = 0.9;
  const HEADER_MIN_W = 90;
  const HEADER_MIN_H = 46;
  const HEADER_MAX_VDEPTH = 4;
  const MAX_ZOOM = 256;
  // Automatic deep-zoom tile hydration (Google Maps style).
  const AUTO_TILE_MIN_W = 90;
  const AUTO_TILE_MIN_H = 60;
  const AUTO_TILE_CONCURRENCY = 3;
  const AUTO_TILE_DEBOUNCE_MS = 140;
  const SIGHASH_RX = /^[a-z][a-z0-9._-]{0,31}:[0-9a-f]{16,128}$/;
  const PINNED_GH_LINE_RX = /^https:\/\/github\.com\/[A-Za-z0-9-]+\/[A-Za-z0-9._-]+\/blob\/[0-9a-f]{7,40}\/[^#\s]+#L\d+(?:-L\d+)?$/i;
  const FLOATING_GH_RX = /^https?:\/\/github\.com\/[^/]+\/[^/]+\/blob\/(?:main|master|HEAD)\//i;
  const OVERCLAIM_RX = /\b(RH is proved|proves RH|proved the Riemann Hypothesis|proves the Riemann Hypothesis|Riemann Hypothesis is proved|proves Navier[- ]Stokes|Navier[- ]Stokes is proved|Navier[- ]Stokes is solved)\b/i;
  const XSS_MARKUP_RX = /<\s*script\b|<\s*iframe\b|<\s*object\b|<\s*embed\b|javascript\s*:|\bon(?:error|load|click|mouseover|focus)\s*=/i;
  const LEAN_PASTE_RX = /:=[ \t]*by\b|^\s*import\s+[A-Z][\w.]*/m;
  const LEAN_MULTI_LINE_RX = /^\s*(?:theorem|lemma|def|instance|structure|inductive|by|have|let|rw|simp|exact|apply|intro|cases|induction)\b/;
  const HANDOFF_REF_RX = /\s*\([^)]*HANDOFF\.md[^)]*\)/gi;
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

    const rootPillars = (rootTree && rootTree.tables && Array.isArray(rootTree.tables.pillars))
      ? rootTree.tables.pillars
      : null;
    const remapPillarIdx = (node, parent) => {
      if (node.pillar && rootPillars) {
        let idx = rootPillars.indexOf(node.pillar);
        if (idx < 0) {
          idx = rootPillars.length;
          rootPillars.push(node.pillar);
        }
        node.pillarIdx = idx;
      } else if (parent && Number.isInteger(parent.pillarIdx)) {
        node.pillarIdx = parent.pillarIdx;
        if (!node.pillar && parent.pillar) node.pillar = parent.pillar;
      }
      node._ck = 0;
      node._col = null;
    };

    let added = 0;
    const addSubtree = (node, parent, depthOffset) => {
      node.parent = parent;
      node.depth = Math.max(parent.depth + 1, (parent.depth || 0) + depthOffset);
      remapPillarIdx(node, parent);
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
        title: String(l.title || id).replace(HANDOFF_REF_RX, "").trim() || id,
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

    // Worst aspect ratio of a row with running (sum, min, max): O(1) per candidate,
    // so containers with thousands of children stay linear.
    function worstOf(sum, minA, maxA, sideLen) {
      if (sum <= 0 || minA <= 0 || sideLen <= 0) return Infinity;
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
          out.push({ item: rowItems[i].item, x, y: cy, w: stripW, h: bh });
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
          out.push({ item: rowItems[i].item, x: cx, y, w: bw, h: stripH });
          cx += bw;
        }
        y += stripH;
        h = Math.max(0, h - stripH);
      }
    }

    let rowItems = [];
    let rowAreas = [];
    let rSum = 0, rMin = Infinity, rMax = 0;
    let side = Math.min(w, h);

    for (let i = 0; i < valid.length; i++) {
      const candArea = areas[i];
      if (!rowItems.length) {
        side = Math.min(w, h);
        rowItems.push(valid[i]);
        rowAreas.push(candArea);
        rSum = candArea; rMin = candArea; rMax = candArea;
        continue;
      }
      const curWorst = worstOf(rSum, rMin, rMax, side);
      const nSum = rSum + candArea;
      const nMin = candArea < rMin ? candArea : rMin;
      const nMax = candArea > rMax ? candArea : rMax;
      const nextWorst = worstOf(nSum, nMin, nMax, side);
      if (nextWorst <= curWorst) {
        rowItems.push(valid[i]);
        rowAreas.push(candArea);
        rSum = nSum; rMin = nMin; rMax = nMax;
      } else {
        layoutRow(rowItems, rowAreas);
        side = Math.min(w, h);
        rowItems = [valid[i]];
        rowAreas = [candArea];
        rSum = candArea; rMin = candArea; rMax = candArea;
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

  const SIZE_UNIT_SHORT = { sz: "decls", vn: "AST nodes", loc: "lines", mods: "files" };

  function createAiHatchPattern(ctx, light, dpr) {
    if (!hasDoc || !ctx || typeof ctx.createPattern !== "function") return null;
    const s = Math.max(6, Math.round(7 * (dpr || 1)));
    const c = document.createElement("canvas");
    c.width = s;
    c.height = s;
    const g = c.getContext("2d");
    if (!g) return null;
    g.strokeStyle = light ? "rgba(122, 66, 4, 0.55)" : "rgba(255, 220, 150, 0.50)";
    g.lineWidth = Math.max(1, Math.round(1.25 * (dpr || 1)));
    g.beginPath();
    g.moveTo(-1, s + 1);
    g.lineTo(s + 1, -1);
    g.moveTo(-1, 1);
    g.lineTo(1, -1);
    g.moveTo(s - 1, s + 1);
    g.lineTo(s + 1, s - 1);
    g.stroke();
    return ctx.createPattern(c, "repeat");
  }

  /** Micro-brick texture for aggregated buckets (many tiny declarations rolled into one box). */
  function createAggregatePattern(ctx, light, dpr) {
    if (!hasDoc || !ctx || typeof ctx.createPattern !== "function") return null;
    const s = Math.max(4, Math.round(5 * (dpr || 1)));
    const c = document.createElement("canvas");
    c.width = s;
    c.height = s;
    const g = c.getContext("2d");
    if (!g) return null;
    g.fillStyle = light ? "rgba(20, 28, 40, 0.10)" : "rgba(0, 0, 0, 0.26)";
    g.fillRect(0, s - 1, s, 1);
    g.fillRect(s - 1, 0, 1, s);
    g.fillStyle = light ? "rgba(255, 255, 255, 0.35)" : "rgba(255, 255, 255, 0.05)";
    g.fillRect(0, 0, s - 1, 1);
    return ctx.createPattern(c, "repeat");
  }

  /** Pre-rendered van Wijk / SequoiaView parabolic cushion sprite (alpha-only light map). */
  function createCushionSprite(light) {
    if (!hasDoc) return null;
    const S = 32; // small sprite: drawImage cost is dominated by per-call overhead, not size
    const c = document.createElement("canvas");
    c.width = S;
    c.height = S;
    const g = c.getContext("2d");
    if (!g || typeof g.createImageData !== "function") return null;
    const img = g.createImageData(S, S);
    const d = img.data;
    // Light from the top-left, slightly in front.
    let lx = -0.42, ly = -0.62, lz = 1.0;
    const ll = Math.hypot(lx, ly, lz);
    lx /= ll; ly /= ll; lz /= ll;
    const hgt = 0.34;
    const flat = lz;
    const gainW = light ? 0.55 : 0.42;
    const gainB = light ? 0.42 : 0.62;
    for (let j = 0; j < S; j++) {
      const v = (j + 0.5) / S;
      for (let i = 0; i < S; i++) {
        const u = (i + 0.5) / S;
        const nx = -4 * hgt * (1 - 2 * u);
        const ny = -4 * hgt * (1 - 2 * v);
        const nl = Math.hypot(nx, ny, 1);
        const dot = Math.max(0, (nx * lx + ny * ly + lz) / nl);
        const delta = dot - flat;
        const k = (j * S + i) * 4;
        if (delta >= 0) {
          d[k] = 255; d[k + 1] = 255; d[k + 2] = 255;
          d[k + 3] = Math.round(255 * Math.min(0.42, delta * gainW * 2.2));
        } else {
          d[k] = 0; d[k + 1] = 0; d[k + 2] = 0;
          d[k + 3] = Math.round(255 * Math.min(0.62, -delta * gainB * 2.2));
        }
      }
    }
    g.putImageData(img, 0, 0);
    return c;
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

  function nodeJitter(node) {
    if (node._jit != null) return node._jit;
    const s = String(node.id != null ? node.id : node.name);
    let hsh = 2166136261;
    for (let i = 0; i < s.length; i++) {
      hsh ^= s.charCodeAt(i);
      hsh = Math.imul(hsh, 16777619);
    }
    node._jit = ((hsh >>> 0) / 4294967295) * 2 - 1;
    return node._jit;
  }

  function shadeRgb(rgb, delta) {
    return [
      clamp(Math.round(rgb[0] + delta), 0, 255),
      clamp(Math.round(rgb[1] + delta), 0, 255),
      clamp(Math.round(rgb[2] + delta), 0, 255)
    ];
  }

  /** Unreviewed baseline: slate tinted by pillar hue with depth + per-node luminance texture. */
  function texturedSlate(node, light) {
    const baseSlate = light ? [206, 211, 219] : [46, 54, 68];
    const pal = light ? PILLAR_PALETTE_LIGHT : PILLAR_PALETTE_DARK;
    const tint = hexToRgb(pal[Math.abs(Number(node.pillarIdx) || 0) % pal.length]);
    const tinted = mixRgb(baseSlate, tint, light ? 0.17 : 0.22);
    const depth = Number(node.depth) || 0;
    const dl = ((depth % 4) - 1.5) * (light ? 2.6 : 3.4) + nodeJitter(node) * (light ? 5 : 6.5);
    return shadeRgb(tinted, dl);
  }

  function nodeColor(node, modeId, ranges, light) {
    const humanRgb = light ? [30, 132, 86] : [56, 160, 110];
    const dossierRgb = light ? [16, 120, 112] : [40, 142, 132];
    const aiRgb = light ? [190, 128, 40] : [176, 124, 50];
    const flagRgb = light ? [200, 60, 66] : [214, 86, 88];
    const baseSlate = light ? [210, 214, 222] : [46, 54, 68];

    if (modeId === "coverage") {
      const cov = node._cov || { humanPct: 0, dossierPct: 0, aiPct: 0, flaggedPct: 0, directTier: "unreviewed" };
      const tex = texturedSlate(node, light);
      let rgb = tex;
      let hatch = false;
      if (cov.directTier === "flagged" || cov.flaggedPct > 0.12) {
        rgb = mixRgb(tex, flagRgb, Math.max(0.78, cov.flaggedPct));
      } else if (cov.directTier === "human" || cov.humanPct > 0) {
        const strength = cov.directTier === "human" ? 0.94 : Math.min(0.9, 0.2 + cov.humanPct * 0.8);
        rgb = mixRgb(tex, humanRgb, strength);
      } else if (cov.directTier === "dossier" || cov.dossierPct > 0) {
        const strength = cov.directTier === "dossier" ? 0.9 : Math.min(0.88, 0.18 + cov.dossierPct * 0.8);
        rgb = mixRgb(tex, dossierRgb, strength);
      } else if (cov.directTier === "ai" || cov.aiPct > 0) {
        const strength = cov.directTier === "ai" ? 0.82 : Math.min(0.8, 0.18 + cov.aiPct * 0.7);
        rgb = mixRgb(tex, aiRgb, strength);
        hatch = true;
      } else if (cov.flaggedPct > 0) {
        rgb = mixRgb(tex, flagRgb, 0.55);
      }
      return { rgb, fill: rgbStr(rgb), hatch };
    }

    if (modeId === "pillar") {
      const pal = light ? PILLAR_PALETTE_LIGHT : PILLAR_PALETTE_DARK;
      const idx = Math.abs(Number(node.pillarIdx) || 0) % pal.length;
      const rgb = shadeRgb(hexToRgb(pal[idx]), nodeJitter(node) * 7 + (((Number(node.depth) || 0) % 3) - 1) * 3);
      return { rgb, fill: rgbStr(rgb), hatch: false };
    }

    const jit = nodeJitter(node) * 3.5;
    if (modeId === "novelty") {
      const nov = clamp(1 - (Number(node.mathlib_pct) || 0), 0, 1);
      const stops = light
        ? [[48, 128, 120], [168, 174, 184], [194, 130, 32]]
        : [[42, 118, 112], [68, 78, 94], [198, 142, 54]];
      const rgb = shadeRgb(rampColor(stops, nov), jit);
      return { rgb, fill: rgbStr(rgb), hatch: false };
    }

    if (modeId === "bloat") {
      const v = Math.log1p(Math.max(0, node.vn) / Math.max(1, node.sz));
      const t = clamp(v / Math.max(1e-6, ranges.maxAst), 0, 1);
      const stops = light
        ? [[198, 204, 214], [58, 126, 168], [186, 114, 34]]
        : [[49, 57, 71], [62, 130, 168], [194, 132, 52]];
      const rgb = shadeRgb(rampColor(stops, t), jit);
      return { rgb, fill: rgbStr(rgb), hatch: false };
    }

    if (modeId === "heartbeats") {
      const v = Math.log1p(Math.max(0, node.hb_max || node.hb_cnt));
      const t = clamp(v / Math.max(1e-6, ranges.maxHb), 0, 1);
      const stops = light
        ? [[206, 211, 220], [196, 138, 44], [186, 56, 62]]
        : [[49, 57, 71], [184, 128, 48], [192, 74, 80]];
      const rgb = shadeRgb(rampColor(stops, t), jit);
      return { rgb, fill: rgbStr(rgb), hatch: false };
    }

    if (modeId === "comments") {
      const t = clamp((Number(node.comment_pct) || 0) / Math.max(1, ranges.maxComment || 50), 0, 1);
      const stops = light
        ? [[206, 211, 220], [42, 142, 132]]
        : [[49, 57, 71], [46, 146, 134]];
      const rgb = shadeRgb(rampColor(stops, t), jit);
      return { rgb, fill: rgbStr(rgb), hatch: false };
    }

    if (modeId === "sorry") {
      let rgb = shadeRgb(baseSlate, jit);
      if (node.sorry_p > 0) rgb = flagRgb;
      else if (node.sorry_c > 0) rgb = aiRgb;
      return { rgb, fill: rgbStr(rgb), hatch: false };
    }

    // compress
    const t = clamp(Number(node.compress) || 0, 0, 1);
    const stops = light
      ? [[198, 204, 214], [96, 118, 178], [146, 86, 174]]
      : [[49, 57, 71], [86, 112, 174], [142, 92, 178]];
    const rgb = shadeRgb(rampColor(stops, t), jit);
    return { rgb, fill: rgbStr(rgb), hatch: false };
  }

  // ---------------------------------------------------------------------------
  // Node classification & selection payload (public, consumed by site.js)
  // ---------------------------------------------------------------------------
  const GROUP_KINDS = new Set(["root", "group", "ns_group", "folder", "ns", "namespace"]);

  function isGroupNode(n) {
    if (!n) return false;
    const k = String(n.kind || "").toLowerCase();
    return GROUP_KINDS.has(k) || n.id === "__root__" || /\/\[other\]$/.test(String(n.name || ""));
  }

  function isModuleNode(n) {
    if (!n || isGroupNode(n)) return false;
    const k = String(n.kind || "").toLowerCase();
    return k === "module" || k === "file" || /\.lean$/i.test(String(n.name || ""));
  }

  /** Exporter bucket that rolls up many sub-threshold declarations with no deeper rows. */
  function isAggregateBucket(n) {
    return Boolean(n) && isGroupNode(n) && !n.tile && (!n.children || !n.children.length) && Number(n.sz) > 1;
  }

  function nodeSelectPayload(node) {
    if (!node) return null;
    const cov = node._cov || null;
    const group = isGroupNode(node);
    const module = isModuleNode(node);
    const entries = cov && Array.isArray(cov.directEntries) ? cov.directEntries : [];
    return {
      id: node.id,
      name: String(node.name || ""),
      short: String(node.short || ""),
      kind: String(node.kind || ""),
      mod: String(node.mod || ""),
      line: Number(node.line) || 0,
      sz: Number(node.sz) || 0,
      vn: Number(node.vn) || 0,
      loc: Number(node.loc) || 0,
      mods: Number(node.mods) || 0,
      pillar: String(node.pillar || ""),
      hash: String(node.hash || ""),
      isDecl: !group && !module,
      isModule: module,
      isGroup: group,
      annotations: entries.map((e) => ({
        layer: e.layer,
        kind: e.kind,
        status: e.status,
        verdict: e.verdict,
        author: e.author,
        note: e.note,
        breaks: e.breaks,
        draft: Boolean(e.draft),
        url: e.url,
        source: e.source,
        dossier_route: e.dossier_route
      })),
      coverage: {
        tier: cov ? cov.directTier : "unreviewed",
        humanPct: cov ? cov.humanPct : 0,
        dossierPct: cov ? cov.dossierPct : 0,
        aiPct: cov ? cov.aiPct : 0,
        flaggedPct: cov ? cov.flaggedPct : 0,
        reviewedPct: cov ? cov.reviewedPct : 0,
        contested: Boolean(cov && cov.contested)
      }
    };
  }

  // ---------------------------------------------------------------------------
  // Pixel-gated nested layout (breadth-first, viewport-culled, unary-collapsed)
  // ---------------------------------------------------------------------------
  /**
   * Lays out `focus`'s descendants inside `rect` (screen space) using
   * zoom-invariant world coordinates `[0, refW] x [0, refH]`.
   *
   * Squarification, container headers (`hdrWorld`), and hairline padding
   * (`padWorld`) depend ONLY on a node's immutable 1x world dimensions, never
   * on the transient camera zoom. As a result, zooming from 1x to 256x produces
   * zero box drift (`maxDrift === 0 px`) and zero horizontal/vertical row flips,
   * so the stretched bitmap preview aligns pixel-for-pixel with the crisp
   * re-rasterized frame. Optional `opts.worldCache` (`Map`) caches each
   * expanded container's `squarify` subdivision across pan/zoom redraws.
   */
  function layoutTreemap(focus, rect, opts) {
    const o = opts || {};
    const weightOf = typeof o.weightOf === "function" ? o.weightOf : (n) => Math.max(0, Number(n.sz) || 0);
    const vw = o.viewW != null ? o.viewW : Math.max(1, rect.x + rect.w);
    const vh = o.viewH != null ? o.viewH : Math.max(1, rect.y + rect.h);
    const refW = Math.max(1, o.refW != null ? o.refW : vw);
    const refH = Math.max(1, o.refH != null ? o.refH : vh);
    const originX = rect.x;
    const originY = rect.y;
    const zoomX = rect.w / refW;
    const zoomY = rect.h / refH;
    const cache = o.worldCache instanceof Map ? o.worldCache : null;
    const maxBoxes = o.maxBoxes || MAX_LAYOUT_BOXES;
    const maxDepth = o.maxDepth || MAX_VISIBLE_DEPTH;
    const minPx = o.minPx || MIN_RECURSE_PX;
    const boxes = [];
    const stats = { maxDepth: 0, collapsed: 0, headers: 0, culled: 0, truncated: false, leaves: 0 };
    const queue = [];
    if (!focus) return { boxes, stats };

    const childItems = (n) => {
      const out = [];
      const kids = n.children || [];
      for (let i = 0; i < kids.length; i++) {
        const w = weightOf(kids[i]);
        if (w > 0) out.push({ node: kids[i], weight: w });
      }
      return out;
    };

    const getTopEntries = () => {
      const curLen = (focus.children && focus.children.length) || 0;
      const rootKey = "__root__";
      const cached = cache && cache.get(rootKey);
      if (cached && cached.focus === focus && cached.kidsLen === curLen) {
        return cached.entries;
      }
      let entries;
      const topKids = curLen ? childItems(focus) : [];
      if (topKids.length) {
        const laid = squarify(topKids, { x: 0, y: 0, w: refW, h: refH });
        entries = laid.map((cell) => ({
          node: cell.item.node,
          wx: cell.x, wy: cell.y, ww: cell.w, wh: cell.h,
          d: 0, vd: 0, chain: null,
          hdrW: 0, padW: 0, collapsed: false, kids: null, kidsLen: -1
        }));
      } else {
        entries = [{
          node: focus,
          wx: 0, wy: 0, ww: refW, wh: refH,
          d: 0, vd: 0, chain: null,
          hdrW: 0, padW: 0, collapsed: false, kids: null, kidsLen: -1
        }];
      }
      if (cache) cache.set(rootKey, { focus, kidsLen: curLen, entries });
      return entries;
    };

    const topEntries = getTopEntries();
    for (let i = 0; i < topEntries.length; i++) queue.push(topEntries[i]);

    let qi = 0;
    while (qi < queue.length) {
      const e = queue[qi++];
      const sw = e.ww * zoomX;
      const sh = e.wh * zoomY;
      if (sw < 0.6 || sh < 0.6) continue; // sub-pixel: parent fill already covers it
      const sx = originX + e.wx * zoomX;
      const sy = originY + e.wy * zoomY;
      if (sx + sw < 0 || sy + sh < 0 || sx > vw || sy > vh) { stats.culled++; continue; }
      const node = e.node;
      const box = {
        node,
        x: sx, y: sy, w: sw, h: sh,
        wx: e.wx, wy: e.wy, ww: e.ww, wh: e.wh,
        d: e.d, vd: e.vd,
        hdr: 0, hdrWorld: 0, pad: 0,
        chain: e.chain, cont: false, collapsed: false
      };
      boxes.push(box);
      if (e.d > stats.maxDepth) stats.maxDepth = e.d;

      const kids = node.children;
      const kidsLen = kids ? kids.length : 0;
      if (!kidsLen || e.d + 1 >= maxDepth || sw < minPx || sh < minPx) { stats.leaves++; continue; }
      if (boxes.length + (queue.length - qi) >= maxBoxes) { stats.truncated = true; stats.leaves++; continue; }

      if (!e.kids || e.kidsLen !== kidsLen) {
        const items = childItems(node);
        if (!items.length) {
          e.kids = [];
          e.kidsLen = kidsLen;
          e.hdrW = 0;
          e.padW = 0;
          e.collapsed = false;
          stats.leaves++;
          continue;
        }
        let sumKids = 0;
        let top = items[0];
        for (const it of items) {
          sumKids += it.weight;
          if (it.weight > top.weight) top = it;
        }
        const selfW = Math.max(weightOf(node), sumKids);
        const dom = top.weight >= UNARY_COLLAPSE_FRAC * selfW && top.node.children && top.node.children.length ? top.node : null;
        let hdrW = 0;
        let padW = 0;
        let collapsed = false;
        if (dom) {
          collapsed = true;
          padW = e.ww >= 8 && e.wh >= 8 ? 0.5 : 0;
        } else {
          const wantsHdr = e.ww >= HEADER_MIN_W && e.wh >= HEADER_MIN_H &&
            (e.vd <= HEADER_MAX_VDEPTH || (e.ww >= 220 && e.wh >= 120));
          if (wantsHdr) hdrW = clamp(Math.floor(e.wh * 0.06), 13, 15);
          padW = hdrW ? (e.vd <= 1 && e.ww >= 160 && e.wh >= 120 ? 1.5 : 0.75) : (e.ww >= 12 && e.wh >= 12 ? 0.25 : 0);
        }
        const iw = e.ww - padW * 2;
        const ih = e.wh - hdrW - padW * 2;
        if (iw <= 0 || ih <= 0) {
          e.kids = [];
          e.kidsLen = kidsLen;
          e.hdrW = hdrW;
          e.padW = padW;
          e.collapsed = collapsed;
          continue;
        }
        const laid = squarify(items, { x: e.wx + padW, y: e.wy + hdrW + padW, w: iw, h: ih });
        const nextVd = dom ? e.vd : e.vd + 1;
        const chainNext = dom ? (e.chain ? e.chain.concat([node]) : [node]) : null;
        const childEntries = new Array(laid.length);
        for (let i = 0; i < laid.length; i++) {
          const cell = laid[i];
          const cn = cell.item.node;
          childEntries[i] = {
            node: cn,
            wx: cell.x, wy: cell.y, ww: cell.w, wh: cell.h,
            d: e.d + 1,
            vd: nextVd,
            chain: cn === dom ? chainNext : null,
            hdrW: 0, padW: 0, collapsed: false, kids: null, kidsLen: -1
          };
        }
        e.kids = childEntries;
        e.kidsLen = kidsLen;
        e.hdrW = hdrW;
        e.padW = padW;
        e.collapsed = collapsed;
      }

      if (!e.kids.length) { stats.leaves++; continue; }
      box.cont = true;
      box.collapsed = e.collapsed;
      box.hdrWorld = e.hdrW;
      box.hdr = e.hdrW * zoomY;
      box.pad = e.padW * zoomX;
      if (e.collapsed) stats.collapsed++;
      if (e.hdrW > 0) stats.headers++;
      for (let i = 0; i < e.kids.length; i++) queue.push(e.kids[i]);
    }
    return { boxes, stats };
  }

  /** Fast O(depth) point query through a cached world-space layout tree. */
  function hitTestWorldTree(worldCache, focus, wx, wy, zoom) {
    if (!worldCache || !focus) return null;
    const top = worldCache.get("__root__");
    if (!top || top.focus !== focus || !top.entries) return null;
    const minVis = 0.6 / Math.max(1e-6, zoom);
    let list = top.entries;
    let found = null;
    while (list && list.length) {
      let next = null;
      for (let i = 0; i < list.length; i++) {
        const e = list[i];
        if (wx >= e.wx && wx <= e.wx + e.ww && wy >= e.wy && wy <= e.wy + e.wh && e.ww >= minVis && e.wh >= minVis) {
          next = e;
          break;
        }
      }
      if (!next) break;
      found = next;
      // Stop on the parent container if pointing inside its header bar.
      if (next.hdrW > 0 && wy <= next.wy + next.hdrW + next.padW) break;
      if (!next.kids || !next.kids.length || next.ww * zoom < MIN_RECURSE_PX || next.wh * zoom < MIN_RECURSE_PX) break;
      list = next.kids;
    }
    return found;
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

  /** Monospace fit: one measureText per font instead of a binary search per label. */
  function fitMono(text, maxW, cw) {
    if (!text || maxW <= 4 || cw <= 0) return "";
    if (text.length * cw <= maxW) return text;
    const n = Math.floor(maxW / cw) - 1;
    return n > 0 ? text.slice(0, n) + "…" : "";
  }

  function chainHeaderLabel(ctx, box, weightOf, maxW) {
    const n = box.node;
    const tail = (n.short || n.name) + " (" + fmtCompact(weightOf(n)) + ")" + (n.tile && !n.tileLoaded ? " +" : "");
    const chain = box.chain || [];
    const cw = box._cw || 0;
    const width = (t) => (cw > 0 ? t.length * cw : ctx.measureText(t).width);
    for (let k = 0; k <= chain.length; k++) {
      const parts = chain.slice(k).map((c) => c.short || c.name);
      const txt = (k > 0 ? "… › " : "") + parts.concat([tail]).join(" › ");
      if (width(txt) <= maxW) return txt;
    }
    return cw > 0 ? fitMono(tail, maxW, cw) : truncateToWidth(ctx, tail, maxW);
  }

  /**
   * Rasterizes laid-out boxes into a 2D context in DEVICE pixels (snapped for
   * razor-sharp edges): fills, AI hatch, cushion light map, header strips,
   * batched hairline strokes, deep-tile markers and fitted labels.
   */
  function rasterizeBoxes(ctx, boxes, p) {
    const dpr = p.dpr || 1;
    const light = Boolean(p.light);
    const colorOf = p.colorOf;
    const weightOf = p.weightOf || ((n) => Number(n.sz) || 0);
    const mono = p.mono || "monospace";
    const sans = p.sans || "sans-serif";
    const n = boxes.length;
    const px = new Float64Array(n * 4);
    let cushions = 0;

    const VW = p.viewW || Infinity;
    const VH = p.viewH || Infinity;
    const hasBounds = Number.isFinite(VW) && Number.isFinite(VH);
    const cwSpr = p.cushion ? (p.cushion.width || 32) : 0;
    const chSpr = p.cushion ? (p.cushion.height || 32) : 0;

    // Pass 1: fills, hatch, cushion light map (clamped to viewport to prevent GPU glitches on deep zooms).
    for (let i = 0; i < n; i++) {
      const b = boxes[i];
      const X = Math.round(b.x * dpr);
      const Y = Math.round(b.y * dpr);
      let W = Math.round((b.x + b.w) * dpr) - X;
      let H = Math.round((b.y + b.h) * dpr) - Y;
      if (W < 1) W = 1;
      if (H < 1) H = 1;
      px[i * 4] = X; px[i * 4 + 1] = Y; px[i * 4 + 2] = W; px[i * 4 + 3] = H;
      const cx0 = hasBounds ? Math.max(X, 0) : X;
      const cy0 = hasBounds ? Math.max(Y, 0) : Y;
      const cx1 = hasBounds ? Math.min(X + W, VW) : (X + W);
      const cy1 = hasBounds ? Math.min(Y + H, VH) : (Y + H);
      const cw = cx1 - cx0;
      const ch = cy1 - cy0;
      const col = colorOf(b.node, b);
      b.rgb = col.rgb;
      if (cw <= 0 || ch <= 0) continue;
      ctx.fillStyle = col.fill;
      ctx.fillRect(cx0, cy0, cw, ch);
      // Containers are almost fully overdrawn by their children: shade leaves only
      // (keeps the cushion pass ~O(canvas area) instead of O(area x depth)).
      if (b.cont) continue;
      if (col.hatch && p.hatch) {
        ctx.fillStyle = p.hatch;
        ctx.fillRect(cx0, cy0, cw, ch);
      }
      if (p.agg && W >= 10 && H >= 10 && isAggregateBucket(b.node)) {
        ctx.fillStyle = p.agg;
        ctx.fillRect(cx0, cy0, cw, ch);
      }
      if (p.cushion && W >= 3 && H >= 3) {
        if (!hasBounds || (cx0 === X && cy0 === Y && cw === W && ch === H)) {
          ctx.drawImage(p.cushion, X, Y, W, H);
        } else {
          // Crop proportional source sub-rect so giant zoomed off-screen leaves keep exact cushion shading.
          const sx = ((cx0 - X) / W) * cwSpr;
          const sy = ((cy0 - Y) / H) * chSpr;
          const sw = Math.max(1e-3, (cw / W) * cwSpr);
          const sh = Math.max(1e-3, (ch / H) * chSpr);
          ctx.drawImage(p.cushion, sx, sy, sw, sh, cx0, cy0, cw, ch);
        }
        cushions++;
      }
    }

    const addBoxEdges = (X, Y, W, H) => {
      if (!hasBounds || (X >= -2 && Y >= -2 && X + W <= VW + 2 && Y + H <= VH + 2)) {
        ctx.rect(X + 0.5, Y + 0.5, W - 1, H - 1);
        return;
      }
      const xL = X + 0.5, xR = X + W - 0.5;
      const yT = Y + 0.5, yB = Y + H - 0.5;
      const cxL = Math.max(-1, xL), cxR = Math.min(VW + 1, xR);
      const cyT = Math.max(-1, yT), cyB = Math.min(VH + 1, yB);
      if (cxL < cxR) {
        if (yT >= -1 && yT <= VH + 1) { ctx.moveTo(cxL, yT); ctx.lineTo(cxR, yT); }
        if (yB >= -1 && yB <= VH + 1) { ctx.moveTo(cxL, yB); ctx.lineTo(cxR, yB); }
      }
      if (cyT < cyB) {
        if (xL >= -1 && xL <= VW + 1) { ctx.moveTo(xL, cyT); ctx.lineTo(xL, cyB); }
        if (xR >= -1 && xR <= VW + 1) { ctx.moveTo(xR, cyT); ctx.lineTo(xR, cyB); }
      }
    };

    // Pass 2: batched hairline strokes (one path per tier, viewport-clamped).
    ctx.lineWidth = 1;
    ctx.beginPath();
    let strokes = 0;
    for (let i = 0; i < n; i++) {
      const W = px[i * 4 + 2], H = px[i * 4 + 3];
      if (W < 4 || H < 4) continue;
      addBoxEdges(px[i * 4], px[i * 4 + 1], W, H);
      strokes++;
    }
    ctx.strokeStyle = light ? "rgba(18, 22, 30, 0.26)" : "rgba(0, 0, 0, 0.55)";
    ctx.stroke();

    ctx.beginPath();
    for (let i = 0; i < n; i++) {
      const b = boxes[i];
      if (!b.cont || b.vd > 2 || px[i * 4 + 2] < 12 || px[i * 4 + 3] < 12) continue;
      addBoxEdges(px[i * 4], px[i * 4 + 1], px[i * 4 + 2], px[i * 4 + 3]);
    }
    ctx.strokeStyle = light ? "rgba(18, 22, 30, 0.45)" : "rgba(0, 0, 0, 0.8)";
    ctx.stroke();

    // Pass 3: deep-tile markers (small corner notch on boxes with more depth available).
    ctx.beginPath();
    for (let i = 0; i < n; i++) {
      const b = boxes[i];
      if (!b.node.tile || b.node.tileLoaded) continue;
      const W = px[i * 4 + 2], H = px[i * 4 + 3];
      if (W < 14 * dpr || H < 10 * dpr) continue;
      const s = Math.min(7 * dpr, W / 4, H / 4);
      const X2 = px[i * 4] + W - 1, Y = px[i * 4 + 1] + 1;
      if (hasBounds && (X2 < 0 || X2 - s > VW || Y > VH || Y + s < 0)) continue;
      ctx.moveTo(X2 - s, Y);
      ctx.lineTo(X2, Y);
      ctx.lineTo(X2, Y + s);
      ctx.closePath();
    }
    ctx.fillStyle = light ? "rgba(20, 30, 45, 0.30)" : "rgba(235, 242, 250, 0.32)";
    ctx.fill();

    // Pass 4: container header strips + breadcrumb labels (world-locked & viewport-clamped).
    const hdrRects = [];
    ctx.textBaseline = "middle";
    const hdrFont = "600 " + (11 * dpr).toFixed(1) + "px " + mono;
    ctx.font = hdrFont;
    const hdrCw = ctx.measureText("0000000000").width / 10;
    let headers = 0;
    for (let i = 0; i < n; i++) {
      const b = boxes[i];
      if (!b.hdr) continue;
      const X = px[i * 4], Y = px[i * 4 + 1], W = px[i * 4 + 2];
      const HH = Math.max(1, Math.round(b.hdr * dpr));
      const hx0 = hasBounds ? Math.max(X + 1, 0) : (X + 1);
      const hy0 = hasBounds ? Math.max(Y + 1, 0) : (Y + 1);
      const hx1 = hasBounds ? Math.min(X + W - 1, VW) : (X + W - 1);
      const hy1 = hasBounds ? Math.min(Y + 1 + HH, VH) : (Y + 1 + HH);
      if (hx1 <= hx0 || hy1 <= hy0) continue;
      hdrRects.push({ x: hx0, y: hy0, w: hx1 - hx0, h: hy1 - hy0 });
      const hdrAlpha = light ? 0.12 : 0.34;
      const hdrRgb = mixRgb(b.rgb || [60, 70, 84], [0, 0, 0], hdrAlpha);
      ctx.fillStyle = light ? "rgba(0,0,0,0.12)" : "rgba(0,0,0,0.34)";
      ctx.fillRect(hx0, hy0, hx1 - hx0, hy1 - hy0);
      if (HH > 22 * dpr && Y + HH <= VH && Y + HH >= 0) {
        ctx.fillStyle = light ? "rgba(18,22,30,0.28)" : "rgba(0,0,0,0.65)";
        ctx.fillRect(hx0, Y + HH, hx1 - hx0, Math.max(1, Math.round(dpr)));
      }
      ctx.fillStyle = contrastTextColor(hdrRgb);
      const lx0 = hasBounds ? Math.max(X, 0) : X;
      const lx1 = hasBounds ? Math.min(X + W, VW) : (X + W);
      b._cw = hdrCw;
      const lbl = chainHeaderLabel(ctx, b, weightOf, lx1 - lx0 - 10 * dpr);
      if (lbl) {
        // At 1x center text inside the strip; when zoomed deep pin near the bottom edge right above children.
        const textY = HH <= 24 * dpr
          ? (Y + 1 + HH / 2)
          : clamp(Y + HH - 9 * dpr, hy0 + 7 * dpr, hy1 - 7 * dpr);
        ctx.fillText(lbl, lx0 + 5 * dpr, textY);
      }
      headers++;
    }

    // Plan floating non-displacing pills for deep containers revealed by zoom (zero child drift).
    const zScale = p.zoom || 1;
    const zoomTags = [];
    if (zScale > 1.35 && hasBounds) {
      const tagH = Math.round(15 * dpr);
      const tagFont = "600 " + (9.5 * dpr).toFixed(1) + "px " + mono;
      ctx.font = tagFont;
      const tagCw = ctx.measureText("0000000000").width / 10;
      const hitsRect = (list, x, y, w, h) => {
        for (let j = 0; j < list.length; j++) {
          const r = list[j];
          if (x < r.x + r.w + 2 * dpr && x + w + 2 * dpr > r.x && y < r.y + r.h + 2 * dpr && y + h + 2 * dpr > r.y) return true;
        }
        return false;
      };
      for (let i = 0; i < n && zoomTags.length < 14; i++) {
        const b = boxes[i];
        if (!b.cont || b.collapsed || b.hdrWorld > 0) continue;
        // Anchor only when the container's real top-left corner is on screen and clearly spacious.
        const bx = px[i * 4], by = px[i * 4 + 1], bw = px[i * 4 + 2], bh = px[i * 4 + 3];
        if (by < -2 || by > VH - 40 * dpr || bx > VW - 60 * dpr) continue;
        const X = Math.max(bx, 0), Y = Math.max(by, 0);
        const W = Math.min(bx + bw, VW) - X;
        const Hv = Math.min(by + bh, VH) - Y;
        if (W < 180 * dpr || Hv < 96 * dpr) continue;
        const tx = X + 2 * dpr, ty = Y + 2 * dpr;
        const label = fitMono((b.node.short || b.node.name) + " (" + fmtCompact(weightOf(b.node)) + ")", Math.min(W - 14 * dpr, 230 * dpr), tagCw);
        if (!label) continue;
        const tw = Math.min(W - 4 * dpr, Math.ceil(label.length * tagCw + 10 * dpr));
        if (hitsRect(hdrRects, tx, ty, tw, tagH) || hitsRect(zoomTags, tx, ty, tw, tagH)) continue;
        zoomTags.push({ x: tx, y: ty, w: tw, h: tagH, label, font: tagFont });
      }
    }

    // Pass 5: leaf labels (fitted, avoiding overlap with floating zoom-tag pills).
    ctx.textBaseline = "top";
    let labels = 0;
    const leafFontBig = "600 " + (12 * dpr).toFixed(1) + "px " + mono;
    const leafFont = "600 " + (10.5 * dpr).toFixed(1) + "px " + mono;
    const subFont = "400 " + (10 * dpr).toFixed(1) + "px " + sans;
    ctx.font = leafFontBig;
    const cwBig = ctx.measureText("0000000000").width / 10;
    ctx.font = leafFont;
    const cwSmall = ctx.measureText("0000000000").width / 10;
    let curFont = leafFont;
    for (let i = 0; i < n && labels < 2500; i++) {
      const b = boxes[i];
      if (b.cont) continue;
      // Sticky: place the label inside the visible part of partially off-screen boxes.
      const X = Math.max(px[i * 4], 0), Y = Math.max(px[i * 4 + 1], 0);
      const W = Math.min(px[i * 4] + px[i * 4 + 2], VW) - X;
      const Hv = Math.min(px[i * 4 + 1] + px[i * 4 + 3], VH) - Y;
      if (W < 34 * dpr || Hv < 16 * dpr) continue;
      // Nudge label down below any floating parent zoom-tag pill covering its top edge.
      let ly = Y + 4 * dpr;
      let remH = Hv;
      for (let j = 0; j < zoomTags.length; j++) {
        const t = zoomTags[j];
        if (X < t.x + t.w + 2 * dpr && X + W > t.x && ly < t.y + t.h + 2 * dpr && Y + Hv > t.y) {
          ly = Math.max(ly, t.y + t.h + 3 * dpr);
          remH = (Y + Hv) - ly;
        }
      }
      if (remH < 13 * dpr) continue;
      const vwCss = W / dpr, vhCss = remH / dpr;
      const big = vwCss >= 120 && vhCss >= 48;
      const want = big ? leafFontBig : leafFont;
      if (curFont !== want) { ctx.font = want; curFont = want; }
      ctx.fillStyle = contrastTextColor(b.rgb || [60, 70, 84]);
      const lbl = fitMono(b.node.short || b.node.name, W - 8 * dpr, big ? cwBig : cwSmall);
      if (!lbl) continue;
      ctx.fillText(lbl, X + 4 * dpr, ly);
      labels++;
      if (vhCss >= 34 && vwCss >= 64) {
        ctx.font = subFont;
        curFont = subFont;
        ctx.globalAlpha = 0.9;
        const extra = b.node.tile && !b.node.tileLoaded ? " · more inside" : (isAggregateBucket(b.node) ? " · small decls rolled up" : "");
        const sub = truncateToWidth(ctx, fmtCompact(weightOf(b.node)) + extra, W - 8 * dpr);
        if (sub) ctx.fillText(sub, X + 4 * dpr, ly + ((big ? 12 : 10.5) + 4) * dpr);
        ctx.globalAlpha = 1;
      }
    }

    // Pass 6: draw crisp glass zoom-tag pills on top (zero text collisions).
    if (zoomTags.length) {
      ctx.textBaseline = "middle";
      ctx.font = zoomTags[0].font;
      for (let j = 0; j < zoomTags.length; j++) {
        const t = zoomTags[j];
        ctx.fillStyle = light ? "rgba(248, 249, 251, 0.94)" : "rgba(10, 14, 20, 0.88)";
        ctx.fillRect(t.x, t.y, t.w, t.h);
        ctx.strokeStyle = light ? "rgba(18, 22, 30, 0.28)" : "rgba(235, 241, 248, 0.26)";
        ctx.lineWidth = Math.max(1, dpr * 0.75);
        ctx.strokeRect(t.x + 0.5, t.y + 0.5, t.w - 1, t.h - 1);
        ctx.fillStyle = light ? "rgba(18, 22, 30, 0.96)" : "rgba(235, 241, 248, 0.96)";
        ctx.fillText(t.label, t.x + 5 * dpr, t.y + t.h / 2);
      }
    }
    return { boxes: n, cushions, strokes, headers, labels, px };
  }

  // ---------------------------------------------------------------------------
  // Explorer Renderer
  // ---------------------------------------------------------------------------
  async function renderExplorer(host, opts) {
    if (!hasDoc) throw new Error("renderExplorer requires a browser DOM");
    const o = Object.assign({}, opts || {});
    const client = o.client || new TreemapClient(o.baseUrl || "data/treemap/", o);
    const layoutMode = o.layout === "sidebar" ? "sidebar" : "stacked";

    clearEl(host);
    const rootEl = h("section", { class: "tm-root tm-layout-" + layoutMode, "aria-label": "Proof treemap explorer" });
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
    const isSourceMode = manifest.mode === "source";
    const views = Array.isArray(manifest.views) ? manifest.views : [];
    const defaultViewId = o.initialView && views.some((v) => v.id === o.initialView)
      ? o.initialView
      : (views[0] ? views[0].id : "dom");

    const state = {
      viewId: defaultViewId,
      viewSpec: null,
      tree: null,
      ranges: { maxAst: 1, maxHb: 1, maxComment: 0 },
      sizeCol: o.sizeCol || "sz",
      colorMode: o.colorMode || (manifest.color_modes && manifest.color_modes[0]) || "coverage",
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
      boxByNode: new Map(),
      layoutStats: null,
      perf: { layoutMs: 0, rasterMs: 0, overlayMs: 0, boxes: 0, rasters: 0 },
      colorVersion: 1,
      fullScreen: false,
      layersOpen: false,
      childrenOpen: false,
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

    if (o.showTitle !== false) {
      rootEl.appendChild(h("header", { class: "tm-head" }, [
        h("h1", { class: "tm-title" }, o.title || "Proof Treemap"),
        h("span", { class: "trust-badge tool" }, "Nested area map · " + (manifest.mode === "kernel" ? "Kernel + Source" : "Source tree")),
        h("p", { class: "tm-sub" }, "Every box is a real declaration or folder, nested by ownership. Scroll, double-click, or pinch to zoom; drag to pan.")
      ]));
    }

    const shell = h("div", { class: "tm-shell" });
    rootEl.appendChild(shell);

    // --- Slim one-row toolbar -------------------------------------------------
    const viewSeg = h("div", { class: "seg tm-view-seg", role: "group", "aria-label": "Hierarchy view" });
    const sizeSelect = h("select", { class: "tm-select", "aria-label": "Size by" });
    const colorSelect = h("select", { class: "tm-select", "aria-label": "Color by" });
    const contribSelect = h("select", { class: "tm-select", "aria-label": "Contributor filter" });
    const searchInput = h("input", {
      type: "search",
      class: "tm-input tm-search-input",
      placeholder: "Jump to theorem or folder…",
      "aria-label": "Jump to theorem or folder",
      autocomplete: "off"
    });
    const acList = h("ul", { class: "tm-ac hidden", role: "listbox" });
    const searchWrap = h("div", { class: "tm-search-wrap" }, [searchInput, acList]);

    const layersBtn = h("button", { type: "button", class: "btn sm tm-layers-btn", "aria-haspopup": "true", "aria-expanded": "false" }, "Layers ▾");
    const layerChipsWrap = h("div", { class: "tm-layer-chips" });
    const layersPop = h("div", { class: "tm-layers-pop hidden", role: "dialog", "aria-label": "Overlay layers" }, [
      h("div", { class: "tm-pop-title" }, "Overlay layers"),
      layerChipsWrap,
      h("label", { class: "tm-ctl" }, [h("span", { class: "tm-ctl-lbl" }, "Contributor"), contribSelect])
    ]);
    const layersWrap = h("div", { class: "tm-layers-wrap" }, [layersBtn, layersPop]);

    const zoomOutBtn = h("button", { type: "button", class: "btn sm", title: "Zoom out", "aria-label": "Zoom out" }, "−");
    const zoomReadout = h("span", { class: "tm-zoom-val", "aria-live": "polite" }, "1.0×");
    const zoomInBtn = h("button", { type: "button", class: "btn sm", title: "Zoom in", "aria-label": "Zoom in" }, "+");
    const upBtn = h("button", { type: "button", class: "btn sm", title: "Up one level" }, "Up");
    const resetBtn = h("button", { type: "button", class: "btn sm", title: "Reset view" }, "Reset");
    const fsBtn = h("button", { type: "button", class: "btn sm fs-btn", title: "Toggle full screen" }, "⛶ Full screen");

    const toolbar = h("div", { class: "tm-toolbar" }, [
      views.length > 1 ? viewSeg : null,
      h("label", { class: "tm-ctl" }, [h("span", { class: "tm-ctl-lbl" }, "Size by"), sizeSelect]),
      h("label", { class: "tm-ctl" }, [h("span", { class: "tm-ctl-lbl" }, "Color by"), colorSelect]),
      searchWrap,
      layersWrap,
      h("div", { class: "tm-zoom-group" }, [zoomOutBtn, zoomReadout, zoomInBtn, upBtn, resetBtn, fsBtn])
    ]);
    shell.appendChild(toolbar);

    // --- Single hairline breadcrumb + legend strip ----------------------------
    const crumbsEl = h("nav", { class: "tm-crumbs", "aria-label": "Treemap zoom path" });
    const legendStrip = h("div", { class: "tm-legend-strip", "aria-live": "polite" });
    shell.appendChild(h("div", { class: "tm-meta-strip" }, [crumbsEl, legendStrip]));

    // --- Full-width canvas -----------------------------------------------------
    const canvas = h("canvas", {
      class: "tm-canvas",
      role: "img",
      tabindex: "0",
      "aria-label": "Interactive nested proof treemap. Arrow keys move the selection, Enter zooms in, Backspace goes up."
    });
    const tipEl = h("div", { class: "tm-tip tm-tooltip hidden", role: "tooltip" });
    const zoomHintEl = h("div", { class: "tm-zoom-hint" }, "Scroll or double-click to zoom");
    const tilePillTxt = h("span", null, "Loading deeper boxes…");
    const tilePill = h("div", { class: "tm-tile-pill hidden", "aria-live": "polite" }, [
      h("span", { class: "tm-spin", "aria-hidden": "true" }),
      tilePillTxt
    ]);
    const readoutTxt = h("span", { class: "tm-readout-txt" });
    const scaleSq = h("span", { class: "tm-scale-sq", "aria-hidden": "true" });
    const scaleTxt = h("span", { class: "tm-scale-txt" });
    const readoutEl = h("div", { class: "tm-readout" }, [h("span", { class: "tm-scale" }, [scaleSq, scaleTxt]), readoutTxt]);
    const canvasWrap = h("div", { class: "tm-canvas-wrap" }, [canvas, tipEl, zoomHintEl, tilePill, readoutEl]);

    // --- Selected-node bar (below canvas in stacked; side panel in sidebar) ----
    const selBar = h("section", { class: "tm-selbar", "aria-label": "Selected box details", "aria-live": "polite" });
    const bodyEl = h("div", { class: "tm-body" }, [canvasWrap, selBar]);
    shell.appendChild(bodyEl);

    const base = document.createElement("canvas");
    // Cached 1x full-world overview canvas layered behind `base` while panning or
    // zooming out so exposed margins show real map tiles instead of blank voids.
    const overviewBase = document.createElement("canvas");
    let overviewValid = false;
    let worldCache = new Map();
    let rangesDirty = false;
    let baseDirty = true;
    let cushionSprite = null;
    let cushionLight = null;
    let hatchPat = null;
    let aggPat = null;
    let hatchKey = "";
    // Camera used for the cached base raster; while the camera moves, the cached
    // bitmap is composited smoothly with overviewBase underneath and sharpened once
    // motion settles (or throttled periodically during extreme zoom swings).
    let baseCam = { x: 0, y: 0, zoom: 1 };
    let sharpenTimer = null;
    let sharpenThrottleTimer = null;
    let lastRasterAt = 0;
    let isPanning = false;
    let pendingTileFlush = false;
    let pendingTileSelRefresh = false;
    let wheelZoomLatchUntil = 0;
    let wheelGestureOwner = null; // "map" | "page" while a continuous wheel burst stays < 320ms apart
    let lastWheelEventAt = 0;
    const lastPointer = { lx: 0, ly: 0, inside: false };

    function isCameraMoving() {
      return isPanning || Boolean(state.anim) || Boolean(sharpenTimer);
    }

    function clearWorldLayout() {
      worldCache = new Map();
      overviewValid = false;
    }

    function invalidateVisualCache() {
      overviewValid = false;
    }

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

    function unitShort() {
      return SIZE_UNIT_SHORT[state.sizeCol] || "units";
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
      const baseU = String(o.repoUrl).replace(/\/+$/, "");
      const commit = String(o.pinnedCommit || "main");
      const prefix = String(o.srcPrefix || "").replace(/^\/+/, "");
      let path = target.replace(/^\/+/, "");
      if (!path.endsWith(".lean") && !path.includes("/")) path = path.replace(/\./g, "/") + ".lean";
      if (prefix && !path.startsWith(prefix)) path = prefix + path;
      const frag = node.line > 0 ? "#L" + Math.floor(node.line) : "";
      return safeHref(baseU + "/blob/" + encodeURIComponent(commit) + "/" + path + frag);
    }

    let lastCoverage = null;
    function refreshCoverage() {
      if (!state.tree || !state.tree.root) return;
      lastCoverage = computeCoverageStats(state.tree.root, client.overlay, state.activeLayers, state.contributorFilter);
      state.colorVersion++;
      renderLegend();
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
              invalidate();
              renderSelBar();
            }
          }, [
            h("span", { class: "tm-layer-dot " + dotCls }),
            h("span", { class: "tm-layer-name" }, l.title),
            isAi ? h("span", { class: "tm-badge-ai" }, "AI draft") : null,
            h("span", { class: "tm-muted" }, "(" + fmtInt(l.count) + ")")
          ]);
          layerChipsWrap.appendChild(chip);
        }
      }
      layersBtn.textContent = "Layers (" + state.activeLayers.size + " active) ▾";

      clearEl(contribSelect);
      contribSelect.appendChild(h("option", { value: "" }, "All contributors"));
      for (const a of client.overlay.authors) {
        contribSelect.appendChild(h("option", { value: a }, a));
      }
      contribSelect.value = state.contributorFilter;
    }

    function setLayersOpen(on) {
      state.layersOpen = Boolean(on);
      layersPop.classList.toggle("hidden", !state.layersOpen);
      layersBtn.setAttribute("aria-expanded", state.layersOpen ? "true" : "false");
    }
    layersBtn.addEventListener("click", (e) => {
      e.stopPropagation();
      setLayersOpen(!state.layersOpen);
    });

    function renderLegend() {
      clearEl(legendStrip);
      const mode = state.colorMode;
      const cov = lastCoverage;
      if (mode === "coverage") {
        const items = [
          ["Unreviewed", "var(--tm-unrev)", false, cov ? null : null],
          ["Human-verified", "var(--tm-human)", false, cov ? cov.humanPct : null],
          ["Dossier / note", "var(--tm-dossier)", false, cov ? cov.dossierPct : null],
          ["AI draft", "", true, cov ? cov.aiPct : null],
          ["Flagged / sorry", "var(--tm-flagged)", false, cov ? cov.flaggedPct : null]
        ];
        for (const [lbl, bg, hatch, pct] of items) {
          const sw = h("span", { class: "tm-leg-swatch" + (hatch ? " hatch" : "") });
          if (bg) sw.style.background = bg;
          legendStrip.appendChild(h("span", { class: "tm-leg-item" }, [
            sw, lbl, pct != null ? h("strong", { class: "tm-leg-pct" }, fmtPct(pct)) : null
          ]));
        }
      } else if (mode === "pillar") {
        const tbl = (state.tree && state.tree.tables && state.tree.tables.pillars) || [];
        const pal = isLightTheme() ? PILLAR_PALETTE_LIGHT : PILLAR_PALETTE_DARK;
        tbl.slice(0, 8).forEach((lbl, i) => {
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
          novelty: ["Library-backed", "Project-native", "linear-gradient(90deg, #2f7d76, #6e788a, #c68e36)"],
          bloat: ["Compact", "Dense AST", "linear-gradient(90deg, #313947, #3e82a8, #c28434)"],
          heartbeats: ["Low", "High maxHeartbeats", "linear-gradient(90deg, #313947, #b88030, #c04a50)"],
          comments: ["0% comments", "Commented", "linear-gradient(90deg, #313947, #2e9286)"],
          compress: ["Unique names", "Repetitive names", "linear-gradient(90deg, #313947, #5670ae, #8e5cb2)"]
        };
        const [lo, hi, css] = labels[mode] || ["Low", "High", "linear-gradient(90deg, #313947, #7cc4e4)"];
        grad.style.background = css;
        legendStrip.appendChild(h("span", { class: "tm-leg-item" }, [lo, grad, hi]));
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
        const label = (n.short || n.name) + (idx === 0 || isLast ? " (" + fmtCompact(nodeWeight(n)) + ")" : "");
        if (isLast) {
          crumbsEl.appendChild(h("span", { class: "tm-crumb cur", title: n.name }, label));
        } else {
          crumbsEl.appendChild(h("button", {
            type: "button",
            class: "tm-crumb",
            title: n.name + " (" + fmtInt(nodeWeight(n)) + ")",
            onclick: () => focusOnNode(n, "crumb")
          }, label));
        }
      });
      crumbsEl.scrollLeft = crumbsEl.scrollWidth;
    }

    function syncSelectors() {
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
    // Automatic deep-zoom tile loading (LRU-cached, max 3 concurrent)
    // -------------------------------------------------------------------------
    const tileQueue = [];
    let tilesInFlight = 0;
    let autoTileTimer = null;
    let tileBatchTimer = null;

    function updateTilePill() {
      const pending = tilesInFlight + tileQueue.length;
      tilePill.classList.toggle("hidden", pending === 0);
      tilePillTxt.textContent = pending > 1 ? "Loading deeper boxes… (" + pending + ")" : "Loading deeper boxes…";
    }

    function flushTileBatch() {
      if (!state.tree) return;
      pendingTileFlush = false;
      const mode = state.colorMode;
      if (mode === "bloat" || mode === "heartbeats" || mode === "comments") {
        state.ranges = computeColorMetricRanges(state.tree);
        rangesDirty = false;
      } else {
        rangesDirty = true;
      }
      if (mode === "coverage" || client.overlay.entriesByName.size > 0) {
        refreshCoverage();
      } else {
        state.colorVersion++;
      }
      invalidateVisualCache();
      baseDirty = true;
      scheduleDraw();
      if (pendingTileSelRefresh || mode === "coverage") {
        pendingTileSelRefresh = false;
        renderSelBar();
      }
    }

    function afterTileBatch(loadedNode) {
      if (loadedNode && loadedNode === state.selectedNode) pendingTileSelRefresh = true;
      if (tileBatchTimer) return;
      tileBatchTimer = setTimeout(() => {
        tileBatchTimer = null;
        if (!state.tree) return;
        // Defer redraw while the user is actively dragging, wheeling, or animating
        // so background tile arrivals never cause a mid-gesture stutter.
        if (isCameraMoving()) {
          pendingTileFlush = true;
          return;
        }
        flushTileBatch();
      }, tilesInFlight + tileQueue.length > 0 ? 180 : 60);
    }

    function pumpTiles() {
      while (tilesInFlight < AUTO_TILE_CONCURRENCY && tileQueue.length) {
        const node = tileQueue.shift();
        if (!node || node.tileLoaded || node.tileLoading || node.tileError) continue;
        const tree = state.tree;
        const spec = state.viewSpec;
        node.tileLoading = true;
        tilesInFlight++;
        client.loadTile(spec, node.tile, tree).then((payload) => {
          if (state.tree !== tree) return;
          spliceTileRows(node, payload, tree);
        }).catch((err) => {
          node.tileError = String(err && err.message || err);
        }).finally(() => {
          node.tileLoading = false;
          tilesInFlight--;
          updateTilePill();
          afterTileBatch(node);
          pumpTiles();
        });
      }
      updateTilePill();
    }

    function requestTile(node, priority) {
      if (!node || !node.tile || node.tileLoaded || node.tileLoading || node.tileError) return;
      const at = tileQueue.indexOf(node);
      if (at >= 0) {
        if (!priority) return;
        tileQueue.splice(at, 1);
      }
      if (priority) tileQueue.unshift(node);
      else tileQueue.push(node);
      pumpTiles();
    }

    function scheduleAutoTiles() {
      if (autoTileTimer) clearTimeout(autoTileTimer);
      autoTileTimer = setTimeout(scanAutoTiles, isCameraMoving() ? 280 : AUTO_TILE_DEBOUNCE_MS);
    }

    function scanAutoTiles() {
      autoTileTimer = null;
      if (o.autoTiles === false || !state.viewSpec) return;
      const vw = baseInfo.cw, vh = baseInfo.ch;
      const cands = [];
      for (const b of state.renderedBoxes) {
        const n = b.node;
        if (!n.tile || n.tileLoaded || n.tileLoading || n.tileError) continue;
        const x0 = Math.max(0, b.x), y0 = Math.max(0, b.y);
        const x1 = Math.min(vw, b.x + b.w), y1 = Math.min(vh, b.y + b.h);
        const vwid = x1 - x0, vhgt = y1 - y0;
        if (vwid >= AUTO_TILE_MIN_W && vhgt >= AUTO_TILE_MIN_H) cands.push({ n, a: vwid * vhgt });
      }
      // Drop queued tiles that scrolled out of view; keep in-flight ones.
      const want = new Set(cands.map((c) => c.n));
      for (let i = tileQueue.length - 1; i >= 0; i--) {
        if (!want.has(tileQueue[i])) tileQueue.splice(i, 1);
      }
      cands.sort((a, b) => b.a - a.a);
      for (const c of cands) requestTile(c.n, false);
      updateTilePill();
    }

    // -------------------------------------------------------------------------
    // Selection & focus
    // -------------------------------------------------------------------------
    function emitSelect(node, reason) {
      if (typeof o.onSelectNode !== "function" || !node) return;
      try {
        o.onSelectNode(nodeSelectPayload(node), {
          reason: reason || "click",
          view: state.viewId,
          focus: state.focusNode ? state.focusNode.name : "",
          raw: node
        });
      } catch (err) {
        if (typeof console !== "undefined") console.warn("onSelectNode handler failed", err);
      }
    }

    function selectNode(node, reason) {
      if (!node) return;
      const changed = node !== state.selectedNode;
      state.selectedNode = node;
      if (changed) {
        state.childrenOpen = false;
      }
      renderSelBar();
      scheduleOverlay();
      if (changed || reason === "initial") emitSelect(node, reason);
    }

    function resetCam() {
      state.anim = null;
      state.cam = { x: 0, y: 0, zoom: 1 };
      zoomReadout.textContent = "1.0×";
      canvasWrap.classList.remove("zoomed");
    }

    function focusOnNode(node, reason) {
      if (!node) return;
      state.focusNode = node;
      clearWorldLayout();
      resetCam();
      renderCrumbs();
      selectNode(node, reason || "focus");
      invalidate();
      if (node.tile && !node.tileLoaded) requestTile(node, true);
    }

    function headlineNode(tree) {
      const r = tree && tree.root;
      if (!r) return null;
      if (o.initialSelect) {
        const hit = findNodeByQuery(o.initialSelect, tree);
        if (hit) return hit;
      }
      if (!isGroupNode(r) && r.kind !== "root") return r;
      let best = null;
      for (const c of r.children) {
        if (isGroupNode(c)) continue;
        if (!best || nodeWeight(c) > nodeWeight(best)) best = c;
      }
      if (best && nodeWeight(best) >= 0.5 * nodeWeight(r)) return best;
      return r;
    }

    function findNodeByQuery(q, treeArg) {
      const tree = treeArg || state.tree;
      if (!tree) return null;
      const s = String(q || "").trim();
      if (!s) return null;
      const sl = s.toLowerCase();
      const all = tree.allNodes;
      return (tree.nodesByName && tree.nodesByName.get(s))
        || (tree.nodesById && tree.nodesById.get(s))
        || all.find((x) => x.short === s)
        || all.find((x) => String(x.name || "").toLowerCase() === sl)
        || all.find((x) => String(x.name || "").toLowerCase().endsWith("." + sl))
        || all.find((x) => String(x.name || "").toLowerCase().includes(sl))
        || null;
    }

    // -------------------------------------------------------------------------
    // Canvas: offscreen base raster + cheap overlay pass
    // -------------------------------------------------------------------------
    let drawPending = false;
    const raf = typeof requestAnimationFrame === "function" ? requestAnimationFrame : (fn) => setTimeout(fn, 16);
    const nowMs = () => (typeof performance !== "undefined" && performance.now ? performance.now() : Date.now());

    function scheduleDraw() {
      if (drawPending) return;
      drawPending = true;
      raf(() => {
        drawPending = false;
        drawCanvas();
      });
    }

    function scheduleOverlay() {
      if (drawPending) return;
      drawPending = true;
      raf(() => {
        drawPending = false;
        drawCanvas();
      });
    }

    function clampCamObj(cam, cw, ch) {
      const z = clamp(Number(cam.zoom) || 1, 1, MAX_ZOOM);
      cam.zoom = z;
      if (z <= 1 + 1e-6) {
        cam.zoom = 1;
        cam.x = 0;
        cam.y = 0;
      } else {
        cam.x = clamp(cam.x, Math.min(0, cw - cw * z), 0);
        cam.y = clamp(cam.y, Math.min(0, ch - ch * z), 0);
      }
      return cam;
    }

    function clampCam() {
      const { cw, ch } = viewSize();
      return clampCamObj(state.cam, cw, ch);
    }

    function clearSharpenTimers() {
      if (sharpenTimer) { clearTimeout(sharpenTimer); sharpenTimer = null; }
      if (sharpenThrottleTimer) { clearTimeout(sharpenThrottleTimer); sharpenThrottleTimer = null; }
    }

    function requestSharpenNow() {
      clearSharpenTimers();
      baseDirty = true;
      if (pendingTileFlush) {
        flushTileBatch();
        return;
      }
      scheduleDraw();
    }

    function invalidate(cameraOnly) {
      if (cameraOnly && state.perf.rasters > 0) {
        // Always glide on the cached bitmap while actively dragging, animating, or wheeling
        // so frames stay jitter-free at 60 fps instead of flip-flopping on a 14ms threshold.
        if (sharpenTimer) clearTimeout(sharpenTimer);
        if (!state.anim && !isPanning) {
          sharpenTimer = setTimeout(() => {
            sharpenTimer = null;
            requestSharpenNow();
          }, 120);
        }
        // During long continuous wheel zooms/pans, periodically re-raster so deep zooms stay legible.
        if (!state.anim && !sharpenThrottleTimer) {
          const sc = camScale();
          const { cw, ch } = viewSize();
          const panDx = Math.abs(state.cam.x - baseCam.x * sc);
          const panDy = Math.abs(state.cam.y - baseCam.y * sc);
          const farDrift = sc >= 2.1 || sc <= 0.48 || panDx > cw * 0.65 || panDy > ch * 0.65;
          if (farDrift && (nowMs() - lastRasterAt) >= 160) {
            sharpenThrottleTimer = setTimeout(() => {
              sharpenThrottleTimer = null;
              if (!state.anim) {
                baseDirty = true;
                scheduleDraw();
              }
            }, 40);
          }
        }
        scheduleDraw();
        return;
      }
      clearSharpenTimers();
      if (!cameraOnly) invalidateVisualCache();
      baseDirty = true;
      scheduleDraw();
    }

    function camScale() {
      return state.cam.zoom / (baseCam.zoom || 1);
    }

    /** Map a box laid out under `baseCam` into current screen space. */
    function baseToScreen(b) {
      if (b.wx != null && b.ww != null) {
        const z = state.cam.zoom;
        return {
          x: state.cam.x + b.wx * z,
          y: state.cam.y + b.wy * z,
          w: b.ww * z,
          h: b.wh * z
        };
      }
      const s = camScale();
      return { x: state.cam.x + (b.x - baseCam.x) * s, y: state.cam.y + (b.y - baseCam.y) * s, w: b.w * s, h: b.h * s };
    }

    const baseInfo = { cw: 0, ch: 0, dpr: 1 };

    function colorOf(node) {
      if (node._ck === state.colorVersion) return node._col;
      node._col = nodeColor(node, state.colorMode, state.ranges, isLightTheme());
      node._ck = state.colorVersion;
      return node._col;
    }

    function syncHoverAfterRaster() {
      if (!lastPointer.inside || isPanning || state.anim) return;
      const hit = hitTest(lastPointer.lx, lastPointer.ly);
      const next = hit ? hit.node : null;
      if (next !== state.hoveredNode) {
        state.hoveredNode = next;
      }
      if (hit && !tipEl.classList.contains("hidden")) {
        const rect = canvasWrap.getBoundingClientRect();
        showTip(hit.node, lastPointer.lx, lastPointer.ly, rect);
      } else if (!hit) {
        tipEl.classList.add("hidden");
        tipNode = null;
      }
    }

    function rasterBase(cw, ch, dpr) {
      const t0 = nowMs();
      const light = isLightTheme();
      clampCamObj(state.cam, cw, ch);
      const z = state.cam.zoom;
      const worldW = cw * z;
      const worldH = ch * z;
      const lay = layoutTreemap(state.focusNode, { x: state.cam.x, y: state.cam.y, w: worldW, h: worldH }, {
        weightOf: nodeWeight,
        viewW: cw,
        viewH: ch,
        refW: cw,
        refH: ch,
        worldCache
      });
      const t1 = nowMs();
      const pw = Math.round(cw * dpr);
      const ph = Math.round(ch * dpr);
      if (base.width !== pw || base.height !== ph) {
        base.width = pw;
        base.height = ph;
      }
      const bctx = base.getContext("2d");
      if (!bctx) return;
      bctx.setTransform(1, 0, 0, 1, 0, 0);
      bctx.fillStyle = cssVar("--bg-code", light ? "#f6f6f3" : "#0c0f13");
      bctx.fillRect(0, 0, base.width, base.height);
      if (!cushionSprite || cushionLight !== light) {
        cushionSprite = createCushionSprite(light);
        cushionLight = light;
      }
      const hk = (light ? "l" : "d") + dpr;
      if (hk !== hatchKey) {
        hatchPat = createAiHatchPattern(bctx, light, dpr);
        aggPat = createAggregatePattern(bctx, light, dpr);
        hatchKey = hk;
      }
      rasterizeBoxes(bctx, lay.boxes, {
        dpr,
        light,
        zoom: z,
        colorOf,
        weightOf: nodeWeight,
        cushion: cushionSprite,
        hatch: hatchPat,
        agg: aggPat,
        viewW: base.width,
        viewH: base.height,
        mono: cssVar("--mono", "monospace"),
        sans: cssVar("--sans", "sans-serif")
      });
      // Snapshot the 1x full-world frame as our pan/zoom-out backing canvas.
      if (Math.abs(z - 1) < 1e-6 && state.cam.x === 0 && state.cam.y === 0) {
        if (overviewBase.width !== pw || overviewBase.height !== ph) {
          overviewBase.width = pw;
          overviewBase.height = ph;
        }
        const octx = overviewBase.getContext("2d");
        if (octx) {
          octx.setTransform(1, 0, 0, 1, 0, 0);
          octx.drawImage(base, 0, 0);
          overviewValid = true;
        }
      }
      const t2 = nowMs();
      lastRasterAt = t2;
      baseCam = { x: state.cam.x, y: state.cam.y, zoom: state.cam.zoom };
      state.renderedBoxes = lay.boxes;
      state.layoutStats = lay.stats;
      const byNode = new Map();
      for (const b of lay.boxes) byNode.set(b.node, b);
      state.boxByNode = byNode;
      state.perf.layoutMs = Math.round((t1 - t0) * 10) / 10;
      state.perf.rasterMs = Math.round((t2 - t1) * 10) / 10;
      state.perf.boxes = lay.boxes.length;
      state.perf.rasters++;
      updateReadout(cw, ch);
      syncHoverAfterRaster();
      scheduleAutoTiles();
    }

    function updateReadout(cw, ch) {
      const z = state.cam.zoom;
      const st = state.layoutStats || { maxDepth: 0 };
      const fw = nodeWeight(state.focusNode);
      const perSq = fw > 0 ? (fw / Math.max(1, cw * ch * z * z)) * 144 : 0;
      scaleTxt.textContent = perSq >= 0.01 ? "≈ " + (perSq >= 10 ? fmtCompact(perSq) : perSq.toFixed(perSq >= 1 ? 1 : 2)) + " " + unitShort() : "";
      readoutTxt.textContent =
        fmtInt(state.renderedBoxes.length) + " boxes drawn · " + (st.maxDepth + 1) + " levels deep · " +
        fmtInt(fw) + " total " + unitShort() + " · " + z.toFixed(z >= 10 ? 0 : 1) + "× (max " + MAX_ZOOM + "×) · scroll or double-click to zoom · drag to pan";
      readoutEl.title = "Layout " + state.perf.layoutMs + " ms · raster " + state.perf.rasterMs + " ms · hover redraw " + state.perf.overlayMs + " ms";
    }

    function drawCanvas() {
      if (!state.tree || !state.focusNode) return;
      const rect = canvasWrap.getBoundingClientRect();
      const cw = Math.max(240, Math.floor(rect.width || canvasWrap.clientWidth || 720));
      const ch = Math.max(200, Math.floor(rect.height || canvasWrap.clientHeight || 480));
      const dpr = (typeof window !== "undefined" && window.devicePixelRatio) ? Math.min(3, window.devicePixelRatio) : 1;
      if (cw !== baseInfo.cw || ch !== baseInfo.ch || dpr !== baseInfo.dpr) {
        if (baseInfo.cw > 0 && baseInfo.ch > 0 && (cw !== baseInfo.cw || ch !== baseInfo.ch)) {
          if (state.cam.zoom > 1) {
            state.cam.x *= cw / baseInfo.cw;
            state.cam.y *= ch / baseInfo.ch;
          }
          clearWorldLayout();
        } else {
          invalidateVisualCache();
        }
        baseInfo.cw = cw; baseInfo.ch = ch; baseInfo.dpr = dpr;
        baseDirty = true;
      }
      const pw = Math.round(cw * dpr);
      const ph = Math.round(ch * dpr);
      if (canvas.width !== pw || canvas.height !== ph) {
        canvas.width = pw;
        canvas.height = ph;
      }
      if (baseDirty) {
        baseDirty = false;
        rasterBase(cw, ch, dpr);
      }
      const t0 = nowMs();
      const ctx = canvas.getContext("2d");
      if (!ctx) return;
      ctx.setTransform(1, 0, 0, 1, 0, 0);
      const sc = camScale();
      const sxDpr = canvas.width / cw;
      const syDpr = canvas.height / ch;
      if (Math.abs(sc - 1) < 1e-6 && Math.abs(state.cam.x - baseCam.x) < 1e-3 && Math.abs(state.cam.y - baseCam.y) < 1e-3) {
        ctx.drawImage(base, 0, 0);
      } else {
        clampCamObj(state.cam, cw, ch);
        ctx.fillStyle = cssVar("--bg-code", isLightTheme() ? "#f6f6f3" : "#0c0f13");
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        const z = state.cam.zoom;
        const scNow = z / (baseCam.zoom || 1);
        // Backing 1x layer fills margins seamlessly when panning or zooming out.
        if (overviewValid && overviewBase.width > 0 && overviewBase.height > 0) {
          ctx.imageSmoothingEnabled = true;
          ctx.drawImage(
            overviewBase,
            state.cam.x * sxDpr,
            state.cam.y * syDpr,
            cw * z * sxDpr,
            ch * z * syDpr
          );
        }
        // Crisp viewport `base` layered on top (pixel-exact alignment because layout is world-locked).
        const dx = (state.cam.x - baseCam.x * scNow) * sxDpr;
        const dy = (state.cam.y - baseCam.y * scNow) * syDpr;
        const dw = base.width * scNow;
        const dh = base.height * scNow;
        if (dx < canvas.width && dy < canvas.height && dx + dw > 0 && dy + dh > 0) {
          ctx.imageSmoothingEnabled = scNow < 5;
          ctx.drawImage(base, dx, dy, dw, dh);
          ctx.imageSmoothingEnabled = true;
        }
        updateReadout(cw, ch);
      }
      drawOverlay(ctx, dpr);
      state.perf.overlayMs = Math.round((nowMs() - t0) * 100) / 100;
    }

    function boxForNode(node) {
      let cur = node;
      while (cur) {
        const b = state.boxByNode.get(cur);
        if (b) return { box: b, exact: cur === node };
        cur = cur.parent;
      }
      return null;
    }

    function drawOverlay(ctx, dpr) {
      const light = isLightTheme();
      const accentCol = cssVar("--accent", light ? "#1f6f96" : "#7cc4e4");
      const CW = canvas.width, CH = canvas.height;
      const ring = (node, color, lw, glow) => {
        if (!node) return;
        const hit = boxForNode(node);
        if (!hit) return;
        const b = baseToScreen(hit.box);
        const L = lw * dpr;
        // Clip to the viewport so deep zoom never strokes 100k-px rectangles.
        const X0 = Math.max(Math.round(b.x * dpr), -8), Y0 = Math.max(Math.round(b.y * dpr), -8);
        const X1 = Math.min(Math.round((b.x + b.w) * dpr), CW + 8), Y1 = Math.min(Math.round((b.y + b.h) * dpr), CH + 8);
        if (X1 <= X0 || Y1 <= Y0) return;
        const W = Math.max(2, X1 - X0), H = Math.max(2, Y1 - Y0);
        ctx.save();
        if (!hit.exact) ctx.setLineDash([4 * dpr, 3 * dpr]);
        if (glow) {
          ctx.globalAlpha = 0.28;
          ctx.strokeStyle = color;
          ctx.lineWidth = L + 4 * dpr;
          ctx.strokeRect(X0 + L / 2, Y0 + L / 2, Math.max(0, W - L), Math.max(0, H - L));
          ctx.globalAlpha = 1;
        }
        ctx.strokeStyle = glow ? (light ? "rgba(255,255,255,0.9)" : "rgba(0,0,0,0.75)") : color;
        if (glow) {
          ctx.lineWidth = L + 1.5 * dpr;
          ctx.strokeRect(X0 + L / 2, Y0 + L / 2, Math.max(0, W - L), Math.max(0, H - L));
        }
        ctx.strokeStyle = color;
        ctx.lineWidth = L;
        ctx.strokeRect(X0 + L / 2, Y0 + L / 2, Math.max(0, W - L), Math.max(0, H - L));
        ctx.restore();
      };
      if (state.hoveredNode && state.hoveredNode !== state.selectedNode && !isPanning && !state.anim) {
        const hoverHit = state.boxByNode.get(state.hoveredNode);
        if (hoverHit) ring(state.hoveredNode, light ? "rgba(10,14,20,0.85)" : "rgba(245,248,252,0.92)", 1.5, false);
      }
      if (state.selectedNode) ring(state.selectedNode, accentCol, 2.5, true);
      if (state.flashNodeId != null && Date.now() < state.flashUntil) {
        const fn = state.tree.nodesById.get(String(state.flashNodeId));
        if (fn) ring(fn, cssVar("--amber", "#e0a95a"), 3, true);
      }
    }

    function hitTest(sx, sy) {
      const z = state.cam.zoom || 1;
      // Fast O(depth) query over cached world tree (covers freshly panned margins too).
      if (worldCache.size > 0 && state.focusNode) {
        const wx = (sx - state.cam.x) / z;
        const wy = (sy - state.cam.y) / z;
        const hitE = hitTestWorldTree(worldCache, state.focusNode, wx, wy, z);
        if (hitE) {
          const existing = state.boxByNode.get(hitE.node);
          if (existing) return existing;
          const bz = baseCam.zoom || 1;
          return {
            node: hitE.node,
            x: baseCam.x + hitE.wx * bz,
            y: baseCam.y + hitE.wy * bz,
            w: hitE.ww * bz,
            h: hitE.wh * bz,
            wx: hitE.wx, wy: hitE.wy, ww: hitE.ww, wh: hitE.wh,
            d: hitE.d, vd: hitE.vd,
            hdr: hitE.hdrW * bz,
            hdrWorld: hitE.hdrW,
            pad: hitE.padW * bz,
            chain: hitE.chain,
            cont: Boolean(hitE.kids && hitE.kids.length),
            collapsed: Boolean(hitE.collapsed)
          };
        }
      }
      const s = camScale();
      const px = baseCam.x + (sx - state.cam.x) / s;
      const py = baseCam.y + (sy - state.cam.y) / s;
      const boxes = state.renderedBoxes;
      for (let i = boxes.length - 1; i >= 0; i--) {
        const b = boxes[i];
        if (px >= b.x && px <= b.x + b.w && py >= b.y && py <= b.y + b.h) return b;
      }
      return null;
    }

    // -------------------------------------------------------------------------
    // Camera: zoom about a point, smooth fit-to-box animation
    // -------------------------------------------------------------------------
    function viewSize() {
      return { cw: baseInfo.cw || canvasWrap.clientWidth || 720, ch: baseInfo.ch || canvasWrap.clientHeight || 480 };
    }

    function setZoomReadout() {
      const z = state.cam.zoom;
      zoomReadout.textContent = z.toFixed(z >= 10 ? 0 : 1) + "×";
      canvasWrap.classList.toggle("zoomed", z > 1.02);
    }

    function applyZoomAt(factor, cx, cy) {
      state.anim = null;
      const { cw, ch } = viewSize();
      const pxv = cx != null ? cx : cw / 2;
      const pyv = cy != null ? cy : ch / 2;
      const oldZ = state.cam.zoom;
      let newZ = clamp(oldZ * factor, 1, MAX_ZOOM);
      if (factor < 1 && newZ < 1.008) newZ = 1;
      if (Math.abs(newZ - oldZ) < 1e-6) return false;
      const scale = newZ / oldZ;
      state.cam.x = pxv - (pxv - state.cam.x) * scale;
      state.cam.y = pyv - (pyv - state.cam.y) * scale;
      state.cam.zoom = newZ;
      clampCamObj(state.cam, cw, ch);
      setZoomReadout();
      invalidate(true);
      return true;
    }

    function animateZoomBy(factor, cx, cy, ms) {
      const { cw, ch } = viewSize();
      const pxv = cx != null ? cx : cw / 2;
      const pyv = cy != null ? cy : ch / 2;
      const oldZ = state.cam.zoom;
      let newZ = clamp(oldZ * factor, 1, MAX_ZOOM);
      if (factor < 1 && newZ < 1.05) newZ = 1;
      if (Math.abs(newZ - oldZ) < 1e-6) return;
      const scale = newZ / oldZ;
      const target = {
        zoom: newZ,
        x: pxv - (pxv - state.cam.x) * scale,
        y: pyv - (pyv - state.cam.y) * scale
      };
      clampCamObj(target, cw, ch);
      animateCamTo(target, ms || 190);
    }

    function animateCamTo(target, ms) {
      const { cw, ch } = viewSize();
      const clampedTarget = clampCamObj({ x: target.x, y: target.y, zoom: target.zoom }, cw, ch);
      const from = { x: state.cam.x, y: state.cam.y, zoom: state.cam.zoom };
      const dur = ms || 340;
      const t0 = nowMs();
      const reduce = typeof window !== "undefined" && window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;
      clearSharpenTimers();
      tipEl.classList.add("hidden");
      tipNode = null;
      const token = {};
      state.anim = token;
      // Interpolate in log-zoom with the screen-space center anchored along a straight world path.
      const fcx = (cw / 2 - from.x) / from.zoom, fcy = (ch / 2 - from.y) / from.zoom;
      const tcx = (cw / 2 - clampedTarget.x) / clampedTarget.zoom, tcy = (ch / 2 - clampedTarget.y) / clampedTarget.zoom;
      const step = () => {
        if (state.anim !== token) return;
        const t = reduce ? 1 : clamp((nowMs() - t0) / dur, 0, 1);
        const e = t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;
        if (t >= 1) {
          state.cam.zoom = clampedTarget.zoom;
          state.cam.x = clampedTarget.x;
          state.cam.y = clampedTarget.y;
          state.anim = null;
          setZoomReadout();
          requestSharpenNow();
          return;
        }
        const z = Math.exp(Math.log(from.zoom) + (Math.log(clampedTarget.zoom) - Math.log(from.zoom)) * e);
        const wx = fcx + (tcx - fcx) * e, wy = fcy + (tcy - fcy) * e;
        state.cam.zoom = z;
        state.cam.x = cw / 2 - wx * z;
        state.cam.y = ch / 2 - wy * z;
        clampCamObj(state.cam, cw, ch);
        setZoomReadout();
        scheduleDraw();
        raf(step);
      };
      raf(step);
    }

    /** Smoothly zoom the camera so `box` fills the view; refocus when the camera cap is reached. */
    function zoomIntoBox(baseBox) {
      if (!baseBox) return;
      const node = baseBox.node;
      const { cw, ch } = viewSize();
      const wx = baseBox.wx != null ? baseBox.wx : (baseBox.x - baseCam.x) / (baseCam.zoom || 1);
      const wy = baseBox.wy != null ? baseBox.wy : (baseBox.y - baseCam.y) / (baseCam.zoom || 1);
      const ww = baseBox.ww != null ? baseBox.ww : baseBox.w / (baseCam.zoom || 1);
      const wh = baseBox.wh != null ? baseBox.wh : baseBox.h / (baseCam.zoom || 1);
      const z = state.cam.zoom;
      const fitZ = Math.min(cw / Math.max(1e-6, ww), ch / Math.max(1e-6, wh)) * 0.94;
      const hasKids = (node.children && node.children.length > 0) || node.tile;
      if (fitZ > MAX_ZOOM || fitZ / z < 1.12) {
        if (hasKids) focusOnNode(node, "zoom");
        else selectNode(node, "zoom");
        return;
      }
      const tz = clamp(fitZ, 1, MAX_ZOOM);
      const target = { zoom: tz, x: cw / 2 - (wx + ww / 2) * tz, y: ch / 2 - (wy + wh / 2) * tz };
      clampCamObj(target, cw, ch);
      selectNode(node, "zoom");
      if (node.tile && !node.tileLoaded) requestTile(node, true);
      animateCamTo(target, 340);
    }

    // -------------------------------------------------------------------------
    // Selected-node bar & Draft PR Composer
    // -------------------------------------------------------------------------
    function navItem(node, tab) {
      return (e) => {
        if (typeof o.onNavigateItem === "function") {
          e.preventDefault();
          o.onNavigateItem(node.name, tab);
        }
      };
    }

    function renderSelBar() {
      clearEl(selBar);
      const node = state.selectedNode || state.focusNode;
      if (!node) {
        selBar.appendChild(h("p", { class: "tm-muted" }, "Select a box to see its details."));
        return;
      }
      const cov = node._cov || { humanPct: 0, dossierPct: 0, aiPct: 0, flaggedPct: 0, directEntries: [], contested: false };
      const ghUrl = resolveGithubUrl(node);
      const group = isGroupNode(node);
      const module = isModuleNode(node);
      const hasKids = (node.children && node.children.length > 0) || Boolean(node.tile);

      const ancestors = [];
      let p = node.parent;
      while (p) { ancestors.push(p.short || p.name); p = p.parent; }
      ancestors.reverse();

      // Row 1: identity
      const kindLabel = group ? (node.kind === "folder" ? "Folder" : "Group") : (module ? "File" : (node.kind || "declaration"));
      selBar.appendChild(h("div", { class: "tm-sel-id tm-insp" }, [
        h("span", { class: "tm-sel-kicker" }, "Selected"),
        h("h2", { class: "tm-sel-name", title: node.name }, [identWbr(node.name)]),
        h("span", { class: "tm-kind-badge" + (group ? " group" : "") }, kindLabel),
        node.pillar ? h("span", { class: "pill" }, node.pillar) : null,
        node.hash ? h("span", { class: "pill mono tm-hash", title: "Signature hash" }, node.hash) : null,
        node.tile && !node.tileLoaded ? h("span", { class: "pill" }, node.tileLoading ? "Loading deeper boxes…" : "More boxes inside") : null,
        node.mod ? h("span", { class: "tm-sel-mod" }, node.mod + (node.line > 0 ? ":" + node.line : "")) : null
      ]));
      if (ancestors.length) {
        selBar.appendChild(h("div", { class: "tm-sel-path tm-insp", title: ancestors.join(" › ") }, ancestors.slice(-6).join(" › ")));
      }

      // Row 2: stat pills
      const stats = h("div", { class: "tm-stat-pills" });
      const addStat = (k, v) => stats.appendChild(h("span", { class: "tm-stat-pill" }, [h("span", { class: "tm-stat-k" }, k), h("strong", { class: "tm-stat-v" }, v)]));
      addStat("Decls", fmtInt(node.sz));
      addStat("AST", isSourceMode && !node.vn ? "—" : fmtCompact(node.vn));
      addStat("LOC", fmtInt(node.loc));
      addStat("Files", fmtInt(node.mods));
      addStat("Library match", isSourceMode && !node.mathlib_pct ? "—" : fmtPct(node.mathlib_pct));
      addStat("Heartbeats", node.hb_cnt > 0 ? (fmtInt(node.hb_cnt) + " (max " + fmtCompact(node.hb_max) + ")") : "0");
      addStat("Sorry", fmtInt(node.sorry_p) + " / " + fmtInt(node.sorry_c));
      addStat("Wrapper", isSourceMode && !node.wrapper_pct ? "—" : fmtPct(node.wrapper_pct));
      if (state.tree && state.tree.hasComments) addStat("Comments", fmtPct(node.comment_pct / (node.comment_pct > 1 ? 100 : 1)));
      addStat("Human verified", fmtPct(cov.humanPct));
      selBar.appendChild(stats);

      // Row 3: actions
      const acts = h("div", { class: "tm-sel-actions" });
      if (hasKids) {
        acts.appendChild(h("button", {
          type: "button",
          class: "btn sm primary",
          onclick: () => {
            const b = state.boxByNode.get(node);
            if (b) zoomIntoBox(b);
            else focusOnNode(node, "zoom");
          }
        }, "Zoom into box"));
      }
      if (!group && node.name) {
        acts.appendChild(h("a", {
          class: "btn sm",
          href: "#item/" + encodeURIComponent(node.name) + "?tab=source",
          onclick: navItem(node, "source")
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
        acts.appendChild(h("a", { class: "btn sm", href: ghUrl, target: "_blank", rel: "noopener noreferrer" }, "Proof file ↗"));
        if (typeof o.onPeekSource === "function" && node.mod) {
          acts.appendChild(h("button", {
            type: "button",
            class: "btn sm",
            onclick: () => o.onPeekSource(node.mod, node.line > 0 ? node.line : undefined, node.name)
          }, "Peek"));
        }
      }
      acts.appendChild(h("button", {
        type: "button",
        class: "btn sm" + (state.composerOpen ? " active" : ""),
        "aria-expanded": state.composerOpen ? "true" : "false",
        onclick: () => {
          state.composerOpen = !state.composerOpen;
          if (state.composerOpen && !state.draftSource && ghUrl) state.draftSource = ghUrl;
          renderSelBar();
        }
      }, state.composerOpen ? "Hide draft composer" : "+ Annotate / Draft PR"));
      if (node.children && node.children.length) {
        acts.appendChild(h("button", {
          type: "button",
          class: "btn sm tm-kids-btn",
          "aria-expanded": state.childrenOpen ? "true" : "false",
          onclick: () => { state.childrenOpen = !state.childrenOpen; renderSelBar(); }
        }, "Children (" + fmtInt(node.children.length) + ") " + (state.childrenOpen ? "▴" : "▾")));
      }
      selBar.appendChild(acts);

      if (state.childrenOpen && node.children && node.children.length) {
        const strip = h("div", { class: "tm-kids-strip tm-child-list" });
        const kids = node.children.slice().sort((a, b) => nodeWeight(b) - nodeWeight(a)).slice(0, 36);
        for (const ch of kids) {
          strip.appendChild(h("button", {
            type: "button",
            class: "tm-kid-pill" + (isGroupNode(ch) ? " group" : ""),
            title: ch.name,
            onclick: () => {
              const b = state.boxByNode.get(ch);
              if (b && b.w >= 12 && b.h >= 12) selectNode(ch, "child");
              else jumpToNode(ch, "child");
            }
          }, [h("span", { class: "tm-kid-name" }, ch.short || ch.name), h("span", { class: "tm-kid-w" }, fmtCompact(nodeWeight(ch)))]));
        }
        if (node.children.length > kids.length) {
          strip.appendChild(h("span", { class: "tm-muted" }, "+" + fmtInt(node.children.length - kids.length) + " smaller"));
        }
        selBar.appendChild(strip);
      }

      // Notes: contested banner + active-layer entries
      if (cov.contested) {
        selBar.appendChild(h("div", { class: "tm-contested-banner", role: "alert" },
          "Contested: active layers disagree on this target (verified vs flagged)."));
      }
      if (cov.directEntries && cov.directEntries.length) {
        const annSec = h("div", { class: "tm-annots tm-annot-list" });
        for (const e of cov.directEntries.slice(0, 12)) {
          const layerMeta = client.overlay.layerMap.get(e.layer);
          const lKind = (layerMeta && layerMeta.kind) || inferLayerKind({ id: e.layer, kind: e.kind }, [e]);
          const isAi = lKind === "ai-draft" || e.draft || String(e.author || "").startsWith("ai:");
          const trustBadge = isAi
            ? h("span", { class: "tm-badge-ai" }, "AI draft")
            : (lKind === "dossier" || e.dossier_route
              ? h("span", { class: "tm-badge-note" }, "Review note")
              : h("span", { class: "tm-badge-human" }, "Human review"));
          const card = h("article", { class: "tm-annot-card" + (isAi ? " ai" : "") });
          card.appendChild(h("div", { class: "tm-annot-top" }, [
            trustBadge,
            e.status ? h("span", { class: isNegativeEntry(e) ? "tm-badge-flagged" : "pill" }, e.status) : null,
            e.author ? h("span", { class: "tm-annot-author" }, e.author) : null
          ]));
          if (e.note) card.appendChild(h("p", { class: "tm-annot-note" }, e.note.length > 360 ? e.note.slice(0, 357) + "…" : e.note));
          if (e.breaks) card.appendChild(h("p", { class: "tm-annot-breaks" }, "Caveat: " + e.breaks));
          const links = h("div", { class: "tm-annot-links" });
          const uHref = safeHref(e.url || (e.source && e.source.startsWith("http") ? e.source : ""));
          if (uHref) links.appendChild(h("a", { href: uHref, target: "_blank", rel: "noopener noreferrer" }, "Source ↗"));
          else if (e.source) links.appendChild(h("span", { class: "tm-muted" }, e.source.replace(HANDOFF_REF_RX, "")));
          if (e.dossier_route) {
            const dHref = safeHref(e.dossier_route.startsWith("#") ? e.dossier_route : ("#" + e.dossier_route));
            if (dHref) links.appendChild(h("a", { href: dHref }, "Open dossier ›"));
          }
          if (links.childNodes.length) card.appendChild(links);
          annSec.appendChild(card);
        }
        if (cov.directEntries.length > 12) {
          annSec.appendChild(h("span", { class: "tm-muted" }, "+" + fmtInt(cov.directEntries.length - 12) + " more notes"));
        }
        selBar.appendChild(annSec);
      }

      if (state.composerOpen) selBar.appendChild(renderComposer(node, ghUrl));
    }

    function renderComposer(node, ghUrl) {
      if (!state.draftSource && ghUrl) state.draftSource = ghUrl;
      const box = h("section", { class: "tm-composer", "aria-label": "Draft annotation PR composer" });

      const k = String(node.kind || "").toLowerCase();
      const targetType = k === "folder" || k === "root"
        ? "folder"
        : (isModuleNode(node) ? "module" : (isGroupNode(node) ? "namespace" : "decl"));

      box.appendChild(h("div", { class: "tm-field tm-field-wide" }, [
        h("span", null, "Target (" + targetType + ") & project"),
        h("div", { class: "tm-ro" }, (manifest.slug || o.slug || "project") + " · " + node.name + (node.hash ? (" · " + node.hash) : ""))
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
        placeholder: "Concise mathematical summary of what this declaration proves and depends on…"
      });
      noteIn.value = state.draftNote;

      const breaksIn = h("textarea", {
        class: "tm-textarea tm-textarea-sm",
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
          slug: manifest.slug || o.slug || "project",
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
        h("label", { class: "tm-field" }, [h("span", null, "Status"), statusSel]),
        h("label", { class: "tm-field" }, [h("span", null, "Author / handle"), authorIn]),
        h("label", { class: "tm-field" }, [h("span", null, "Evidence link"), sourceIn])
      ]));
      box.appendChild(h("div", { class: "tm-field-row two" }, [
        h("label", { class: "tm-field" }, [h("span", null, "Summary / mathematical note"), noteIn]),
        h("label", { class: "tm-field" }, [h("span", null, "Caveats / what breaks"), breaksIn])
      ]));
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
    function jumpToNode(node, reason) {
      if (!node) return;
      const targetFocus = (node.children && node.children.length > 0) ? node : (node.parent || state.tree.root);
      state.focusNode = targetFocus;
      clearWorldLayout();
      resetCam();
      state.flashNodeId = node.id;
      state.flashUntil = Date.now() + 1400;
      setTimeout(scheduleOverlay, 1450);
      renderCrumbs();
      selectNode(node, reason || "jump");
      invalidate();
      if (targetFocus.tile && !targetFocus.tileLoaded) requestTile(targetFocus, true);
    }

    let acActive = -1;
    function updateSearchList() {
      const q = String(searchInput.value || "").trim().toLowerCase();
      clearEl(acList);
      acActive = -1;
      if (!q || !state.tree) {
        acList.classList.add("hidden");
        return;
      }
      const hits = [];
      for (const n of state.tree.allNodes) {
        const hay = (n.name + " " + n.short).toLowerCase();
        if (hay.includes(q)) {
          hits.push(n);
          if (hits.length >= 60) break;
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
            jumpToNode(n, "jump");
          }
        }, [
          h("span", { class: "tm-ac-name", title: n.name }, n.name),
          h("span", { class: "tm-ac-meta" }, (isGroupNode(n) ? "group · " : "") + fmtCompact(nodeWeight(n)))
        ]));
      }
      acList.classList.remove("hidden");
    }

    searchInput.addEventListener("input", updateSearchList);
    searchInput.addEventListener("keydown", (e) => {
      const opts2 = Array.from(acList.querySelectorAll(".tm-ac-item[role='option']"));
      if (e.key === "ArrowDown" || e.key === "ArrowUp") {
        if (!opts2.length) return;
        e.preventDefault();
        acActive = (acActive + (e.key === "ArrowDown" ? 1 : -1) + opts2.length) % opts2.length;
        opts2.forEach((op, i) => op.classList.toggle("active", i === acActive));
      } else if (e.key === "Enter") {
        const pick = opts2[acActive >= 0 ? acActive : 0];
        if (pick) pick.click();
      } else if (e.key === "Escape") {
        acList.classList.add("hidden");
      }
    });
    const onDocClick = (e) => {
      if (!searchWrap.contains(e.target)) acList.classList.add("hidden");
      if (state.layersOpen && !layersWrap.contains(e.target)) setLayersOpen(false);
    };
    document.addEventListener("click", onDocClick);

    // -------------------------------------------------------------------------
    // Zoom, Pan, Pointer/Pinch, Wheel & Keyboard interactions
    // -------------------------------------------------------------------------
    zoomInBtn.addEventListener("click", () => animateZoomBy(1.6));
    zoomOutBtn.addEventListener("click", () => animateZoomBy(1 / 1.6));
    upBtn.addEventListener("click", () => {
      if (state.cam.zoom > 1.05) {
        animateCamTo({ x: 0, y: 0, zoom: 1 }, 280);
      } else if (state.focusNode && state.focusNode.parent) {
        focusOnNode(state.focusNode.parent, "up");
      }
    });
    resetBtn.addEventListener("click", () => {
      if (state.tree && state.tree.root) {
        if (state.focusNode === state.tree.root && state.cam.zoom > 1.02) {
          animateCamTo({ x: 0, y: 0, zoom: 1 }, 260);
        } else {
          focusOnNode(state.tree.root, "reset");
        }
      }
    });

    function setFullScreen(on) {
      state.fullScreen = Boolean(on);
      shell.classList.toggle("fs-on", state.fullScreen);
      document.body.classList.toggle("fs-lock", state.fullScreen);
      fsBtn.textContent = state.fullScreen ? "✕ Exit full screen" : "⛶ Full screen";
      invalidate();
    }

    fsBtn.addEventListener("click", () => setFullScreen(!state.fullScreen));
    const onDocKey = (e) => {
      if (e.key === "Escape") {
        if (state.layersOpen) setLayersOpen(false);
        else if (state.fullScreen) setFullScreen(false);
      }
    };
    document.addEventListener("keydown", onDocKey);

    // Track whether a continuous wheel gesture started on the page or on the treemap
    // so scrolling the page past the viewport never abruptly turns into a zoom mid-swipe.
    const onWinWheelCapture = (e) => {
      const t = nowMs();
      if (t - lastWheelEventAt > 320) {
        wheelGestureOwner = canvasWrap.contains(e.target) ? "map" : "page";
      }
      lastWheelEventAt = t;
    };
    window.addEventListener("wheel", onWinWheelCapture, { capture: true, passive: true });

    canvasWrap.addEventListener("wheel", (e) => {
      const now = nowMs();
      const ctrlZoom = e.ctrlKey || e.metaKey;
      const rect = canvasWrap.getBoundingClientRect();
      const dy = e.deltaMode === 1 ? e.deltaY * 16 : (e.deltaMode === 2 ? e.deltaY * rect.height : e.deltaY);
      if (dy === 0) return;
      if (!ctrlZoom && !state.fullScreen && wheelGestureOwner === "page") return;
      const inZoomLatch = now < wheelZoomLatchUntil;
      // Plain scroll zooms directly with no modifier key required.
      // When already resting at 1x outside fullscreen/pinch, scrolling downward passes through to the page.
      if (!ctrlZoom && !state.fullScreen && state.cam.zoom <= 1.008 && dy > 0 && !inZoomLatch) {
        wheelGestureOwner = "page";
        return;
      }
      e.preventDefault();
      const lx = e.clientX - rect.left;
      const ly = e.clientY - rect.top;
      lastPointer.lx = lx;
      lastPointer.ly = ly;
      lastPointer.inside = true;
      // Trackpad pinch gestures arrive with ctrlKey and tiny fractional deltaY values.
      const sens = (ctrlZoom && e.deltaMode === 0 && Math.abs(dy) < 25) ? 0.0085 : 0.0022;
      const factor = Math.exp(-clamp(dy, -240, 240) * sens);
      const wasZoomed = state.cam.zoom > 1.008;
      const moved = applyZoomAt(factor, lx, ly);
      // Latch briefly after a zoom-out swipe reaches 1x so residual trackpad momentum
      // doesn't abruptly yank the page down mid-gesture.
      if (moved || (wasZoomed && factor < 1) || (inZoomLatch && factor < 1)) {
        wheelZoomLatchUntil = now + 420;
      }
      if (moved) {
        tipEl.classList.add("hidden");
        tipNode = null;
      }
    }, { passive: false });

    canvasWrap.addEventListener("dblclick", (e) => {
      e.preventDefault();
      const rect = canvasWrap.getBoundingClientRect();
      const hit = hitTest(e.clientX - rect.left, e.clientY - rect.top);
      if (hit) zoomIntoBox(hit);
    });

    const activePointers = new Map();
    let dragMoved = false;
    let dragStart = null;
    let dragLast = null;
    let lastPinchDist = null;
    let lastPinchMid = null;
    let lastTapTime = 0;
    let lastTapNode = null;
    let tipNode = null;

    canvasWrap.addEventListener("pointerdown", (e) => {
      if (e.button !== 0 && e.pointerType === "mouse") return;
      if (e.target !== canvas && e.target !== canvasWrap) return;
      activePointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
      dragMoved = false;
      dragStart = { x: e.clientX, y: e.clientY };
      dragLast = { x: e.clientX, y: e.clientY };
      if (activePointers.size === 2) {
        const pts = Array.from(activePointers.values());
        lastPinchDist = Math.hypot(pts[1].x - pts[0].x, pts[1].y - pts[0].y);
        lastPinchMid = { x: (pts[0].x + pts[1].x) / 2, y: (pts[0].y + pts[1].y) / 2 };
      }
      try { canvasWrap.setPointerCapture(e.pointerId); } catch (_) { /* optional */ }
    });

    function showTip(n, lx, ly, rect) {
      if (n !== tipNode) {
        tipNode = n;
        const cov = n._cov || { humanPct: 0, aiPct: 0 };
        clearEl(tipEl);
        tipEl.appendChild(h("div", { class: "tm-tip-title" }, n.name));
        tipEl.appendChild(h("div", null, [
          (isGroupNode(n) ? "group" : (n.kind || "node")) + " · " + fmtInt(nodeWeight(n)) + " " + unitShort(),
          n.pillar ? (" · " + n.pillar) : ""
        ]));
        if (n.children && n.children.length) {
          tipEl.appendChild(h("div", { class: "tm-muted" }, fmtInt(n.children.length) + " nested boxes" + (n.tile && !n.tileLoaded ? " (more on zoom)" : "")));
        } else if (n.tile && !n.tileLoaded) {
          tipEl.appendChild(h("div", { class: "tm-muted" }, "More boxes inside; zoom in"));
        } else if (isAggregateBucket(n)) {
          tipEl.appendChild(h("div", { class: "tm-muted" }, "Rolled-up bucket of small declarations (below the export size threshold)"));
        }
        if (state.colorMode === "coverage") {
          tipEl.appendChild(h("div", null, "Human: " + fmtPct(cov.humanPct) + " · AI draft: " + fmtPct(cov.aiPct)));
        }
      }
      tipEl.style.left = clamp(lx + 14, 6, Math.max(6, rect.width - 300)) + "px";
      tipEl.style.top = clamp(ly + 14, 6, Math.max(6, rect.height - 100)) + "px";
      tipEl.classList.remove("hidden");
    }

    canvasWrap.addEventListener("pointermove", (e) => {
      const rect = canvasWrap.getBoundingClientRect();
      const lx = e.clientX - rect.left;
      const ly = e.clientY - rect.top;
      lastPointer.lx = lx;
      lastPointer.ly = ly;
      lastPointer.inside = true;

      if (activePointers.has(e.pointerId)) {
        activePointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
        if (activePointers.size === 2) {
          const pts = Array.from(activePointers.values());
          const dist = Math.hypot(pts[1].x - pts[0].x, pts[1].y - pts[0].y);
          const midX = (pts[0].x + pts[1].x) / 2;
          const midY = (pts[0].y + pts[1].y) / 2;
          if (lastPinchMid && state.cam.zoom > 1.01) {
            state.cam.x += midX - lastPinchMid.x;
            state.cam.y += midY - lastPinchMid.y;
            clampCam();
          }
          if (lastPinchDist && dist > 0) {
            isPanning = true;
            applyZoomAt(dist / lastPinchDist, midX - rect.left, midY - rect.top);
            dragMoved = true;
          }
          lastPinchDist = dist;
          lastPinchMid = { x: midX, y: midY };
          return;
        }
        if (dragStart && dragLast) {
          const totalDist = Math.hypot(e.clientX - dragStart.x, e.clientY - dragStart.y);
          const stepX = e.clientX - dragLast.x;
          const stepY = e.clientY - dragLast.y;
          dragLast = { x: e.clientX, y: e.clientY };
          if (dragMoved || totalDist > 4) {
            dragMoved = true;
            if (state.cam.zoom > 1.01) {
              state.anim = null;
              isPanning = true;
              canvasWrap.classList.add("panning");
              tipEl.classList.add("hidden");
              tipNode = null;
              state.cam.x += stepX;
              state.cam.y += stepY;
              clampCam();
              invalidate(true);
            }
          }
        }
        return;
      }

      if (e.pointerType === "touch" || state.anim) return;
      const hit = hitTest(lx, ly);
      const nextHover = hit ? hit.node : null;
      if (nextHover !== state.hoveredNode) {
        state.hoveredNode = nextHover;
        scheduleOverlay();
      }
      if (hit) showTip(hit.node, lx, ly, rect);
      else { tipEl.classList.add("hidden"); tipNode = null; }
    });

    const endPointer = (e) => {
      const wasDown = activePointers.has(e.pointerId);
      const wasPanning = isPanning;
      activePointers.delete(e.pointerId);
      if (activePointers.size < 2) { lastPinchDist = null; lastPinchMid = null; }
      if (activePointers.size === 1) {
        const rem = Array.from(activePointers.values())[0];
        dragLast = { x: rem.x, y: rem.y };
      }
      if (activePointers.size === 0) {
        isPanning = false;
        canvasWrap.classList.remove("panning");
        if (wasPanning) {
          // Sharpen immediately when drag or pinch ends instead of waiting for a debounce.
          requestSharpenNow();
        }
      }
      if (!wasDown || dragMoved) return;

      const rect = canvasWrap.getBoundingClientRect();
      const lx = e.clientX - rect.left, ly = e.clientY - rect.top;
      const hit = hitTest(lx, ly);
      if (!hit) return;
      const nowTap = Date.now();
      const isDoubleTap = e.pointerType !== "mouse" && hit.node === lastTapNode && (nowTap - lastTapTime) < 340;
      lastTapTime = nowTap;
      lastTapNode = hit.node;

      if (isDoubleTap) {
        zoomIntoBox(hit);
        return;
      }
      // Clicking a group/folder header zooms straight into it (directory-style).
      const sb = baseToScreen(hit);
      const hdrPx = hit.hdrWorld != null ? hit.hdrWorld * state.cam.zoom : (hit.hdr * camScale());
      const onHeader = hit.cont && hdrPx > 0 && ly <= sb.y + hdrPx + 1;
      if (onHeader && isGroupNode(hit.node)) {
        zoomIntoBox(hit);
        return;
      }
      selectNode(hit.node, "click");
    };

    canvasWrap.addEventListener("pointerup", endPointer);
    canvasWrap.addEventListener("pointercancel", (e) => {
      const wasPanning = isPanning;
      activePointers.delete(e.pointerId);
      lastPinchDist = null;
      lastPinchMid = null;
      if (activePointers.size === 0) {
        isPanning = false;
        canvasWrap.classList.remove("panning");
        if (wasPanning) requestSharpenNow();
      }
    });
    canvasWrap.addEventListener("pointerleave", () => {
      lastPointer.inside = false;
      tipEl.classList.add("hidden");
      tipNode = null;
      if (state.hoveredNode) {
        state.hoveredNode = null;
        scheduleOverlay();
      }
    });

    canvas.addEventListener("keydown", (e) => {
      const sel = state.selectedNode || state.focusNode;
      if (!sel) return;
      const siblings = () => {
        const par = sel.parent;
        if (!par) return [sel];
        return par.children.filter((c) => nodeWeight(c) > 0).sort((a, b) => nodeWeight(b) - nodeWeight(a));
      };
      let handled = true;
      if (e.key === "Enter" || e.key === " ") {
        const b = state.boxByNode.get(sel);
        if (b && ((sel.children && sel.children.length) || sel.tile)) zoomIntoBox(b);
        else if ((sel.children && sel.children.length) || sel.tile) focusOnNode(sel, "keyboard");
        else emitSelect(sel, "keyboard");
      } else if (e.key === "Backspace") {
        if (state.focusNode && state.focusNode.parent) focusOnNode(state.focusNode.parent, "keyboard");
      } else if (e.key === "ArrowUp") {
        if (sel.parent) selectNode(sel.parent, "keyboard");
      } else if (e.key === "ArrowDown") {
        const kids = (sel.children || []).filter((c) => nodeWeight(c) > 0).sort((a, b) => nodeWeight(b) - nodeWeight(a));
        if (kids.length) selectNode(kids[0], "keyboard");
      } else if (e.key === "ArrowLeft" || e.key === "ArrowRight") {
        const sib = siblings();
        const i = sib.indexOf(sel);
        if (sib.length > 1) selectNode(sib[(i + (e.key === "ArrowRight" ? 1 : -1) + sib.length) % sib.length], "keyboard");
      } else if (e.key === "+" || e.key === "=") {
        applyZoomAt(1.6);
      } else if (e.key === "-" || e.key === "_") {
        applyZoomAt(1 / 1.6);
      } else if (e.key === "0") {
        animateCamTo({ x: 0, y: 0, zoom: 1 }, 260);
      } else {
        handled = false;
      }
      if (handled) e.preventDefault();
    });

    let ro = null;
    if (typeof ResizeObserver === "function") {
      ro = new ResizeObserver(() => {
        const rect = canvasWrap.getBoundingClientRect();
        const ncw = Math.max(240, Math.floor(rect.width || canvasWrap.clientWidth || 720));
        const nch = Math.max(200, Math.floor(rect.height || canvasWrap.clientHeight || 480));
        if (ncw === baseInfo.cw && nch === baseInfo.ch) return;
        invalidate();
      });
      ro.observe(canvasWrap);
    }
    let themeObs = null;
    if (typeof MutationObserver === "function") {
      themeObs = new MutationObserver(() => {
        state.colorVersion++;
        cushionSprite = null;
        hatchKey = "";
        invalidateVisualCache();
        renderLegend();
        invalidate();
      });
      themeObs.observe(document.documentElement, { attributes: true, attributeFilter: ["data-theme"] });
    }

    function setSizeCol(col) {
      if (!Array.from(sizeSelect.options).some((op) => op.value === col)) return false;
      state.sizeCol = col;
      sizeSelect.value = col;
      clearWorldLayout();
      renderCrumbs();
      renderSelBar();
      invalidate();
      return true;
    }

    function setColorMode(id) {
      if (!Array.from(colorSelect.options).some((op) => op.value === id)) return false;
      state.colorMode = id;
      colorSelect.value = id;
      if (rangesDirty && state.tree && (id === "bloat" || id === "heartbeats" || id === "comments")) {
        state.ranges = computeColorMetricRanges(state.tree);
        rangesDirty = false;
      }
      state.colorVersion++;
      invalidateVisualCache();
      renderLegend();
      invalidate();
      return true;
    }

    sizeSelect.addEventListener("change", () => setSizeCol(sizeSelect.value));
    colorSelect.addEventListener("change", () => setColorMode(colorSelect.value));
    contribSelect.addEventListener("change", () => {
      state.contributorFilter = contribSelect.value;
      refreshCoverage();
      renderSelBar();
      invalidate();
    });

    async function switchView(viewId) {
      state.viewId = viewId;
      for (const btn of viewSeg.querySelectorAll("button")) {
        const active = btn.getAttribute("data-view") === viewId;
        btn.classList.toggle("active", active);
        btn.setAttribute("aria-pressed", active ? "true" : "false");
      }
      const { spec, tree } = await client.loadView(viewId);
      tileQueue.length = 0;
      clearWorldLayout();
      clearSharpenTimers();
      pendingTileFlush = false;
      pendingTileSelRefresh = false;
      rangesDirty = false;
      state.viewSpec = spec;
      state.tree = tree;
      state.ranges = computeColorMetricRanges(tree);
      state.focusNode = tree.root;
      state.selectedNode = null;
      resetCam();
      syncSelectors();
      renderLayerChips();
      refreshCoverage();
      renderCrumbs();
      selectNode(headlineNode(tree) || tree.root, "initial");
      invalidate();
    }

    for (const v of views) {
      viewSeg.appendChild(h("button", {
        type: "button",
        "data-view": v.id,
        class: v.id === state.viewId ? "active" : "",
        "aria-pressed": v.id === state.viewId ? "true" : "false",
        title: v.label,
        onclick: () => switchView(v.id)
      }, String(v.label || v.id).replace(/\s*\([^)]*\)\s*$/, "")));
    }

    await switchView(state.viewId);

    const handle = {
      root: rootEl,
      client,
      state,
      switchView,
      setView: switchView,
      focusOnNode,
      jumpToNode,
      selectNode,
      setSizeCol,
      setColorMode,
      zoomBy: (f) => applyZoomAt(f),
      getSelected: () => nodeSelectPayload(state.selectedNode),
      focusByName: (q) => {
        const hit = findNodeByQuery(q);
        if (!hit) return false;
        jumpToNode(hit, "api");
        return true;
      },
      openDraftComposer: () => {
        state.composerOpen = true;
        const ghUrl = resolveGithubUrl(state.selectedNode);
        if (!state.draftSource && ghUrl) state.draftSource = ghUrl;
        renderSelBar();
        const comp = selBar.querySelector(".tm-composer");
        if (comp && typeof comp.scrollIntoView === "function") comp.scrollIntoView({ block: "nearest" });
        return Boolean(comp);
      },
      redraw: () => invalidate(),
      diagnostics: () => ({
        drawPending,
        baseDirty,
        tilesInFlight,
        tilesQueued: tileQueue.length,
        batchPending: Boolean(tileBatchTimer),
        perf: Object.assign({}, state.perf),
        layout: state.layoutStats ? Object.assign({}, state.layoutStats) : null
      }),
      destroy: () => {
        if (ro) ro.disconnect();
        if (themeObs) themeObs.disconnect();
        document.removeEventListener("click", onDocClick);
        document.removeEventListener("keydown", onDocKey);
        window.removeEventListener("wheel", onWinWheelCapture, { capture: true });
        clearSharpenTimers();
        if (autoTileTimer) { clearTimeout(autoTileTimer); autoTileTimer = null; }
        if (tileBatchTimer) { clearTimeout(tileBatchTimer); tileBatchTimer = null; }
        if (zoomHintTimer) { clearTimeout(zoomHintTimer); zoomHintTimer = null; }
        tileQueue.length = 0;
        isPanning = false;
        state.anim = null;
      }
    };
    return handle;
  }

  // ---------------------------------------------------------------------------
  // Self-test (for #selftest=1 and Node CI verification)
  // ---------------------------------------------------------------------------
  function makeFakeCtx() {
    const calls = { fillRect: 0, drawImage: 0, rect: 0, stroke: 0, fill: 0, fillText: 0 };
    const ctx = {
      calls,
      fillStyle: "", strokeStyle: "", lineWidth: 1, font: "", textBaseline: "", globalAlpha: 1,
      fillRect() { calls.fillRect++; },
      drawImage() { calls.drawImage++; },
      beginPath() {}, closePath() {}, moveTo() {}, lineTo() {},
      rect() { calls.rect++; },
      stroke() { calls.stroke++; },
      fill() { calls.fill++; },
      fillText() { calls.fillText++; },
      measureText(t) { return { width: String(t).length * 6 }; }
    };
    return ctx;
  }

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
      cols: ["id", "p", "name", "sz", "vn", "loc", "pillar"],
      rows: [
        [2, -1, "PillarA.sub", 60, 300, 70, 0],
        [20, 0, "PillarA.leaf1", 35, 180, 40, 0],
        [21, 0, "PillarA.leaf2", 25, 120, 30, 0]
      ]
    }, tree);
    ok(spliceRes.added === 2 && subNode.children.length === 2 && subNode.tileLoaded, "lazy tile splices children cleanly");
    ok(subNode.children.every((c) => c.pillar === "Pillar A" && c.pillarIdx === 1),
      "lazy tile remaps local pillar table index to root tree palette index");

    // 4. Overlay & coverage roll-up toggling
    const ov = normalizeOverlay({
      schema: OVERLAY_SCHEMA,
      layers: [
        { id: "human/facts", title: "Human (HANDOFF.md §4)", kind: "human-review", default_on: true },
        { id: "ai/drafts", title: "AI", kind: "ai-draft", default_on: false }
      ],
      entries: {
        "PillarA.leaf1": [{ layer: "human/facts", status: "verified", author: "@alice", note: "Checked." }],
        "Other.leaf": [{ layer: "ai/drafts", status: "summary", draft: true, author: "ai:gpt", note: "Draft note." }]
      }
    });
    ok(ov.layers[0].title === "Human", "layer titles drop internal handoff references");
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

    // 6. Unary spine collapse: R -> {A, D}; A -> B (95%) -> C (94.7%) -> 40 leaves.
    const mk = (name, sz, kids, kind) => {
      const n = { id: name, name, short: name, kind: kind || "thm", sz, vn: sz, loc: sz, mods: 1, pillarIdx: 1, depth: 0, children: kids || [], parent: null, tile: "", tileLoaded: false };
      for (const k of n.children) k.parent = n;
      return n;
    };
    const leavesC = Array.from({ length: 40 }, (_, i) => mk("C.leaf" + i, 22));
    const nodeC = mk("C", 900, leavesC);
    const nodeB = mk("B", 950, [nodeC, mk("B.side", 45, [mk("B.side.a", 20), mk("B.side.b", 20)])]);
    const nodeA = mk("A", 1000, [nodeB, mk("A.side", 40)]);
    const nodeR = mk("R", 1300, [nodeA, mk("D", 290, [mk("D.a", 150), mk("D.b", 130)], "group")], "root");
    const layU = layoutTreemap(nodeR, { x: 0, y: 0, w: 960, h: 600 }, { viewW: 960, viewH: 600 });
    const bx = (n) => layU.boxes.find((b) => b.node === n);
    ok(bx(nodeA) && bx(nodeA).collapsed && bx(nodeA).hdr === 0 && bx(nodeB) && bx(nodeB).collapsed && bx(nodeB).hdr === 0,
      "unary collapse: dominated containers render as hairline frames without header strips");
    ok(bx(nodeC) && bx(nodeC).hdr >= 13 && bx(nodeC).hdr <= 15 && bx(nodeC).chain && bx(nodeC).chain.map((c) => c.name).join(">") === "A>B",
      "unary collapse: first non-dominated container carries the combined breadcrumb header");
    const fake = makeFakeCtx();
    const lbl = chainHeaderLabel(fake, bx(nodeC), (n) => n.sz, 600);
    ok(lbl === "A › B › C (900)", "unary collapse header reads A › B › C (900)");
    ok(leavesC.every((l) => bx(l)), "unary collapse keeps every leaf brick under the spine");

    // 7. Pixel-gated deep layout: 4-ary tree, depth 7 (16,384 leaves) on 1200x800.
    let leafCount = 0;
    const build = (d, name) => {
      if (d === 7) { leafCount++; return mk(name, 1); }
      const kids = [0, 1, 2, 3].map((i) => build(d + 1, name + "." + i));
      return mk(name, kids.reduce((s, k) => s + k.sz, 0) + 1, kids);
    };
    const deep = build(0, "T");
    const t0 = Date.now();
    const layD = layoutTreemap(deep, { x: 0, y: 0, w: 1200, h: 800 }, { viewW: 1200, viewH: 800 });
    const layMs = Date.now() - t0;
    ok(MAX_VISIBLE_DEPTH === 32 && MAX_ZOOM === 256, "depth cap 32 and zoom cap 256x");
    ok(layD.stats.maxDepth >= 6 && layD.boxes.length >= 20000 && leafCount === 16384,
      "pixel-gated layout paints " + layD.boxes.length + " boxes, " + (layD.stats.maxDepth + 1) + " levels deep (" + layMs + " ms)");
    ok(layD.boxes.every((b) => b.d < MAX_VISIBLE_DEPTH), "layout honors MAX_VISIBLE_DEPTH");
    const layCap = layoutTreemap(deep, { x: 0, y: 0, w: 1200, h: 800 }, { viewW: 1200, viewH: 800, maxBoxes: 600 });
    ok(layCap.stats.truncated && layCap.boxes.length <= 600 + 4, "box budget truncates breadth-first");
    const layCull = layoutTreemap(deep, { x: -3600, y: -2400, w: 9600, h: 6400 }, { viewW: 1200, viewH: 800 });
    ok(layCull.stats.culled > 0 && layCull.boxes.every((b) => b.x + b.w >= 0 && b.y + b.h >= 0 && b.x <= 1200 && b.y <= 800),
      "zoomed layout culls boxes outside the viewport");
    // Zoom invariance: world coords must never drift or flip rows across zooms 1x -> 8x.
    const by1x = new Map(layU.boxes.map((b) => [b.node, b]));
    const layU4 = layoutTreemap(nodeR, { x: -480, y: -300, w: 960 * 4, h: 600 * 4 }, { viewW: 960, viewH: 600 });
    let maxDrift = 0;
    for (const b of layU4.boxes) {
      const ref = by1x.get(b.node);
      if (!ref) continue;
      maxDrift = Math.max(maxDrift, Math.abs(b.x - (-480 + ref.x * 4)), Math.abs(b.y - (-300 + ref.y * 4)), Math.abs(b.w - ref.w * 4), Math.abs(b.h - ref.h * 4));
    }
    ok(layU4.boxes.length > 0 && maxDrift < 1e-6, "world-locked zoom layout has zero drift (max " + maxDrift.toFixed(4) + " px)");

    // 8. Offscreen raster pass (fake 2D context in Node; real canvas in browsers).
    const fctx = makeFakeCtx();
    const rres = rasterizeBoxes(fctx, layU.boxes, {
      dpr: 2,
      colorOf: () => ({ rgb: [50, 60, 70], fill: "rgb(50,60,70)", hatch: false }),
      weightOf: (n) => n.sz,
      cushion: { width: 64, height: 64 }
    });
    ok(rres.boxes === layU.boxes.length && fctx.calls.fillRect >= layU.boxes.length && fctx.calls.drawImage > 0 && fctx.calls.stroke >= 1,
      "offscreen raster fills " + rres.boxes + " boxes with " + rres.cushions + " cushions in batched strokes");
    if (hasDoc) {
      const cv = document.createElement("canvas");
      cv.width = 240;
      cv.height = 150;
      const rc = cv.getContext && cv.getContext("2d");
      if (rc && typeof rc.getImageData === "function") {
        const lay2 = layoutTreemap(nodeR, { x: 0, y: 0, w: 120, h: 75 }, { viewW: 120, viewH: 75 });
        rasterizeBoxes(rc, lay2.boxes, {
          dpr: 2,
          colorOf: (n) => nodeColor(n, "coverage", { maxAst: 1, maxHb: 1, maxComment: 0 }, false),
          weightOf: (n) => n.sz,
          cushion: createCushionSprite(false)
        });
        const px = rc.getImageData(120, 75, 1, 1).data;
        ok(px[3] > 0, "real offscreen canvas receives cushion-shaded pixels");
      }
    }

    // 9. Selection payload schema & group detection.
    const pay = nodeSelectPayload(nodeC);
    const keys = ["id", "name", "short", "kind", "mod", "line", "sz", "vn", "loc", "mods", "pillar", "hash", "isDecl", "isModule", "isGroup", "annotations", "coverage"];
    ok(pay && keys.every((k) => Object.prototype.hasOwnProperty.call(pay, k)) && pay.isDecl && !pay.isGroup, "onSelectNode payload carries the full schema");
    const gp = nodeSelectPayload(mk("Dev.Proofs", 10, [], "ns_group"));
    ok(gp.isGroup && !gp.isDecl && isGroupNode({ kind: "group" }) && isGroupNode({ kind: "folder" }) && isModuleNode({ kind: "module", name: "A.lean" }),
      "namespace / group / folder containers are never treated as theorems");

    // 10. DOM safety: no raw HTML injection anywhere in the renderer.
    const bad = "inner" + "HTML";
    ok([renderExplorer, layoutTreemap, rasterizeBoxes, nodeSelectPayload].every((fn) => String(fn).indexOf(bad) === -1),
      "renderer builds DOM without raw HTML strings");

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
    MAX_VISIBLE_DEPTH,
    MAX_ZOOM,
    TreemapClient,
    renderExplorer,
    runSelfTest,
    squarify,
    layoutTreemap,
    rasterizeBoxes,
    nodeSelectPayload,
    isGroupNode,
    isModuleNode,
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
