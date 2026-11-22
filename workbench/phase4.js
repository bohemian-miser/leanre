/* ==========================================================================
   phase4.js — leanre Phase 4 views:
     * Proof Blueprint / Decompiler (outputs/decomp/*.json, leanre.decomp/v1)
     * Live Kernel Cone Slicer & Decl Inspector (/api/kernel/slice)
     * FLIRT Coarse Structural Clusters (/api/flirt/clusters)
     * Computation & 28,904-File Dead-Code Triage (/api/decomp/compute)
   Vanilla JS, zero external dependencies. Guardrails 1-6 enforced.
   ========================================================================== */
"use strict";

window.Phase4 = (function () {
  var $ = function (s, r) { return (r || document).querySelector(s); };
  var $$ = function (s, r) { return Array.prototype.slice.call((r || document).querySelectorAll(s)); };
  var H = null; // host helpers injected by phase3.js / app.js

  var GH_COMMIT = "40e56bab026552e089d7afcfeff08d2defb9c005";
  var GH_BLOB = "https://github.com/leanprover-community/riemann-hypothesis/blob/" + GH_COMMIT + "/";
  var DECOMP_PAGE = 100;

  var S = {
    status: null,
    decompKey: "spine_map",
    decompNode: "",
    decompRole: "all",
    decompStatus: "all",
    decompVerdict: "all",
    decompQ: "",
    decompOffset: 0,
    slice: { name: "allChi", dir: "deps", depth: 2, edge_kind: "all", max_nodes: 60, stop_at: "", stop_lib: true },
    clusters: { q: "", kind: "all", pillar: "all", offset: 0 },
    compute: { q: "", bucket: "", offset: 0 }
  };

  function esc(s) { return H.esc(s); }
  function fmt(n) { return H.fmtInt(n); }
  function body() { return $("#p3Body"); }
  function qs(obj) {
    var p = new URLSearchParams();
    Object.keys(obj).forEach(function (k) { if (obj[k] !== "" && obj[k] != null) p.set(k, String(obj[k])); });
    return p.toString();
  }
  function get(path, obj) { return H.apiGet(path + (obj ? "?" + qs(obj) : "")); }
  function provTag(env) { return H.provTag(env); }
  function srcLine(env, what) { return H.srcLine(env, what); }
  function stat(label, val, env, cls) { return H.stat(label, val, env, cls); }
  function absentPanel(env, title) { return H.absentPanel(env, title); }
  function shortName(n) { return H.shortName(n); }

  function statusBadge(st) {
    st = String(st || "OPAQUE");
    return '<span class="st-badge ' + esc(st) + '">' + esc(st) + "</span>";
  }

  function ghAnchorLink(anchor, label) {
    var raw = String(anchor || "").trim();
    if (!raw) return "";
    var disp = label != null ? String(label) : raw;
    var pathPart = raw, frag = "";
    var mHash = raw.match(/^([^#]+)#L(\d+)(?:-L?(\d+))?$/);
    var mCol = raw.match(/^([^:]+):(\d+)(?:-(\d+))?$/);
    if (mHash) {
      pathPart = mHash[1];
      frag = "#L" + mHash[2] + (mHash[3] ? "-L" + mHash[3] : "");
    } else if (mCol) {
      pathPart = mCol[1];
      frag = "#L" + mCol[2] + (mCol[3] ? "-L" + mCol[3] : "");
    }
    pathPart = pathPart.replace(/^\/+/, "");
    if (pathPart.indexOf("..") >= 0 || !/^(?:src\/[A-Za-z0-9_.\-\/]+\.lean|lakefile\.toml|lake-manifest\.json|lean-toolchain)$/.test(pathPart)) {
      return esc(disp);
    }
    return '<a class="gh-link" href="' + esc(GH_BLOB + pathPart + frag) + '" target="_blank" rel="noopener">' + esc(disp) + "</a>";
  }

  function refreshStatus() {
    return get("/api/p4/status").then(function (stt) {
      S.status = stt;
      var btn = $('#p3Seg button[data-p3="blueprint"]');
      if (btn) {
        var ready = (stt.decomp_ready || 0) > 0 || (stt.compute_atlas && stt.compute_atlas.state === "ready") || (stt.trim && stt.trim.state === "ready");
        btn.dataset.state = ready ? "ready" : "absent";
        btn.title = "Proof Blueprint / Decompiler — " + (stt.decomp_ready || 0) + "/" + (stt.decomp_total || 6) + " decomp docs ready";
      }
      return stt;
    }).catch(function () { return null; });
  }

  // ------------------------------------------------------------------ BLUEPRINT: visual map + decomp docs
  var MAP_NODES = [
    { id: "main", x: 20, y: 18, w: 185, h: 58, doc: "tcb_audit", cls: "tcb", title: "Main (5 Theorems)", sub: "RH + GRH · Layer 2 TCB" },
    { id: "spine", x: 245, y: 18, w: 235, h: 58, doc: "spine_map", cls: "", title: "allChi → everyCharacter", sub: "1,409,557 decls (96.0%)" },
    { id: "diamond", x: 520, y: 18, w: 215, h: 58, doc: "spine_map", cls: "", title: "332k Shared Diamond", sub: "110,898 direct dom children" },
    { id: "theta", x: 20, y: 126, w: 170, h: 66, doc: "pillar_theta", cls: "", title: "Pillar A · Theta", sub: "543,325 decls (37.0%)" },
    { id: "galois", x: 205, y: 126, w: 170, h: 66, doc: "pillar_galois", cls: "", title: "Pillar B · Galois", sub: "95,102 decls (6.5%)" },
    { id: "window", x: 390, y: 126, w: 170, h: 66, doc: "pillar_window", cls: "", title: "Pillar C · Window", sub: "92,705 decls (6.3%)" },
    { id: "volume", x: 575, y: 126, w: 170, h: 66, doc: "pillar_volume_lit", cls: "", title: "Pillar D · Volume/Lit", sub: "80,720+ decls (5.5%+)" }
  ];
  var MAP_EDGES = [
    ["main", "spine", "dom"],
    ["spine", "diamond", "dom"],
    ["spine", "theta", "dom"],
    ["spine", "galois", "dom"],
    ["spine", "window", "dom"],
    ["spine", "volume", "dom"],
    ["diamond", "theta", "horn"],
    ["diamond", "volume", "horn"]
  ];

  function renderBlueprintSvg(docsByKey, activeKey) {
    var byId = {};
    MAP_NODES.forEach(function (n) { byId[n.id] = n; });
    var edgesSvg = MAP_EDGES.map(function (e) {
      var a = byId[e[0]], b = byId[e[1]];
      var x1 = a.x + a.w / 2, y1 = a.y + a.h;
      var x2 = b.x + b.w / 2, y2 = b.y;
      if (a.y === b.y) { x1 = a.x + a.w; y1 = a.y + a.h / 2; x2 = b.x; y2 = b.y + b.h / 2; }
      var my = (y1 + y2) / 2;
      var d = a.y === b.y ? ("M" + x1 + "," + y1 + " L" + x2 + "," + y2)
        : ("M" + x1 + "," + y1 + " C" + x1 + "," + my + " " + x2 + "," + my + " " + x2 + "," + y2);
      return '<path class="bp-edge ' + e[2] + '" d="' + d + '" marker-end="url(#bpArr)"/>';
    }).join("");
    var nodesSvg = MAP_NODES.map(function (n) {
      var info = docsByKey[n.doc] || { state: "absent" };
      var stCls = info.state === "ready" ? "ready" : "absent";
      var actCls = n.doc === activeKey ? " active" : "";
      var stTxt = info.state === "ready"
        ? (fmt(info.counts && info.counts.nodes) + " nodes · " + fmt(info.counts && info.counts.opaque) + " OPAQUE")
        : ("pending (" + (info.owner || "worker") + ")");
      return '<g class="bp-node ' + n.cls + " " + stCls + actCls + '" data-doc="' + esc(n.doc) + '" transform="translate(' + n.x + "," + n.y + ')">' +
        '<rect width="' + n.w + '" height="' + n.h + '"/>' +
        '<text class="t-title" x="10" y="20">' + esc(n.title) + "</text>" +
        '<text class="t-sub" x="10" y="36">' + esc(n.sub) + "</text>" +
        '<text class="t-st ' + (info.state === "ready" ? "ok" : "no") + '" x="10" y="' + (n.h - 8) + '">' + esc(stTxt) + "</text></g>";
    }).join("");
    return '<div class="bp-map-wrap"><svg class="bp-svg" viewBox="0 0 765 208" role="img" aria-label="Proof architecture map: Main to allChi to four pillars and 332k shared diamond">' +
      '<defs><marker id="bpArr" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">' +
      '<path d="M0,1 L8,5 L0,9 z" fill="#64748b"/></marker></defs>' +
      edgesSvg + nodesSvg + "</svg></div>";
  }

  function renderDecompSvg(doc) {
    var nodes = (doc.nodes || []).slice(0, 36);
    if (!nodes.length) return "";
    // Group nodes into depth layers (using dom.depth or topological index)
    var byDepth = {};
    var depths = [];
    nodes.forEach(function (n, idx) {
      var d = (n.dom && typeof n.dom.depth === "number") ? n.dom.depth : Math.floor(idx / 4);
      if (!byDepth[d]) { byDepth[d] = []; depths.push(d); }
      byDepth[d].push(n);
    });
    depths.sort(function (a, b) { return a - b; });
    var pos = {}, W = 210, Hn = 46, gx = 24, gy = 30;
    var maxCols = 1;
    depths.forEach(function (d, row) {
      var arr = byDepth[d];
      if (arr.length > maxCols) maxCols = arr.length;
      arr.forEach(function (n, col) {
        pos[n.id] = { x: 14 + col * (W + gx), y: 14 + row * (Hn + gy), n: n };
      });
    });
    var svgW = Math.max(720, 28 + maxCols * (W + gx));
    var svgH = Math.max(120, 28 + depths.length * (Hn + gy));
    var eSvg = (doc.edges || []).map(function (e) {
      var a = pos[e.src], b = pos[e.dst];
      if (!a || !b) return "";
      var x1 = a.x + W / 2, y1 = a.y + Hn, x2 = b.x + W / 2, y2 = b.y;
      var cls = e.rel === "horn" ? "both" : (e.rel === "type" ? "type" : "value");
      return '<line class="sl-edge ' + cls + '" x1="' + x1 + '" y1="' + y1 + '" x2="' + x2 + '" y2="' + y2 + '"/>';
    }).join("");
    var nSvg = nodes.map(function (n) {
      var p = pos[n.id];
      var cls = "sl-node" + (n.id === doc.root ? " root" : "") + (n.status === "OPAQUE" ? " stopped" : "");
      var sub = (n.role || n.kind || "") + " · " + (n.status || "") + (n.dom && n.dom.subtree ? " · sub " + fmt(n.dom.subtree) : "");
      return '<g class="' + cls + ' bp-dnode" data-id="' + esc(n.id) + '" transform="translate(' + p.x + "," + p.y + ')">' +
        '<rect width="' + W + '" height="' + Hn + '"/>' +
        '<text x="8" y="18">' + esc(shortName(n.id).slice(0, 29)) + "</text>" +
        '<text class="sub" x="8" y="34">' + esc(sub.slice(0, 34)) + "</text></g>";
    }).join("");
    var capNote = (doc.nodes || []).length > 36
      ? '<div class="dim sm" style="padding:2px 6px 4px">Diagram shows first 36 of ' + fmt(doc.nodes.length) + " nodes; all " + fmt(doc.nodes.length) + " nodes are filterable &amp; paginated below.</div>"
      : "";
    return '<div class="sl-svg-wrap">' + capNote + '<svg width="' + svgW + '" height="' + svgH + '" viewBox="0 0 ' + svgW + " " + svgH + '">' + eSvg + nSvg + "</svg></div>";
  }

  function renderDecompBody(res, container) {
    if (res.state === "absent") {
      container.innerHTML = absentPanel(res, res.title || "decompilation pillar");
      return;
    }
    var doc = res.doc || {};
    var allNodes = doc.nodes || [];
    var pins = doc.pins || {};
    var roles = ["all"];
    var verdicts = ["all"];
    allNodes.forEach(function (n) {
      if (n.role && roles.indexOf(n.role) < 0) roles.push(n.role);
      var vd = n.verdict || "unknown";
      if (verdicts.indexOf(vd) < 0) verdicts.push(vd);
    });
    if (roles.indexOf(S.decompRole) < 0) S.decompRole = "all";
    if (verdicts.indexOf(S.decompVerdict) < 0) S.decompVerdict = "all";
    var filtered = allNodes.filter(function (n) {
      if (S.decompRole !== "all" && n.role !== S.decompRole) return false;
      if (S.decompStatus !== "all" && n.status !== S.decompStatus) return false;
      if (S.decompVerdict !== "all" && (n.verdict || "unknown") !== S.decompVerdict) return false;
      if (S.decompQ) {
        var ql = S.decompQ.toLowerCase();
        var hay = (n.id + " " + (n.header || "") + " " + (n.summary || "") + " " + (n.module || "") + " " + (n.anchor || "") + " " + (n.verdict || "")).toLowerCase();
        if (hay.indexOf(ql) < 0) return false;
      }
      return true;
    });
    if (S.decompOffset >= filtered.length) S.decompOffset = 0;
    if (S.decompOffset < 0) S.decompOffset = 0;
    var pageRows = filtered.slice(S.decompOffset, S.decompOffset + DECOMP_PAGE);
    var sel = filtered.filter(function (n) { return n.id === S.decompNode; })[0] || pageRows[0] || filtered[0] || null;
    if (sel) S.decompNode = sel.id;
    var opaqueList = doc.opaque || [];
    var hornList = doc.horn || [];
    var claimsList = doc.claims || [];

    var pagerHtml = filtered.length > DECOMP_PAGE
      ? '<div class="p3-toolbar" id="bpNodePager" style="margin-top:6px">' +
        '<button class="btn sm" id="bpPrev"' + (S.decompOffset <= 0 ? " disabled" : "") + ">← Prev</button>" +
        '<span class="dim sm">showing ' + fmt(S.decompOffset + 1) + "–" + fmt(Math.min(filtered.length, S.decompOffset + DECOMP_PAGE)) + " of " + fmt(filtered.length) + "</span>" +
        '<button class="btn sm" id="bpNext"' + (S.decompOffset + DECOMP_PAGE >= filtered.length ? " disabled" : "") + ">Next →</button></div>"
      : "";

    var html = srcLine(res, (res.title || doc.pillar || "decompilation") +
      (pins.rh_mirror ? " · rh_mirror@" + pins.rh_mirror : "") +
      (pins.export_sha256 ? " · export " + String(pins.export_sha256).slice(0, 12) + "…" : "")) +
      '<div class="p3-stats">' +
      stat("decompiled nodes", fmt(allNodes.length), res) +
      stat("edges", fmt((doc.edges || []).length), res) +
      stat("Horn contracts", fmt(hornList.length), res) +
      stat("OPAQUE / unread", fmt(opaqueList.length), res) +
      stat("claims", fmt(claimsList.length), res) +
      "</div>" +
      renderDecompSvg(doc) +
      '<div class="p3-toolbar">' +
      '<div class="seg" id="bpStSeg">' + ["all", "READ", "PARTIAL", "OPAQUE"].map(function (st) {
        return '<button data-st="' + st + '"' + (S.decompStatus === st ? ' class="active"' : "") + ">" + st + "</button>";
      }).join("") + "</div>" +
      '<select id="bpRoleSel">' + roles.map(function (r) {
        return '<option value="' + esc(r) + '"' + (S.decompRole === r ? " selected" : "") + ">role: " + esc(r) + "</option>";
      }).join("") + "</select>" +
      '<select id="bpVerdSel">' + verdicts.map(function (v) {
        return '<option value="' + esc(v) + '"' + (S.decompVerdict === v ? " selected" : "") + ">verdict: " + esc(v) + "</option>";
      }).join("") + "</select>" +
      '<input type="search" id="bpNodeQ" placeholder="filter nodes, headers, summaries, anchors…" value="' + esc(S.decompQ) + '" spellcheck="false">' +
      "</div>" +
      '<div class="bp-split"><div>' +
      '<h4 class="p3-h">Contracts &amp; Declarations ' + provTag(res) + ' <span class="dim">(' + fmt(filtered.length) + ")</span></h4>" +
      '<table class="p3-table" id="bpNodeTbl"><thead><tr><th>declaration</th><th>role</th><th>status / verdict</th><th class="num">subtree</th></tr></thead><tbody>' +
      pageRows.map(function (n) {
        return '<tr class="click' + (sel && sel.id === n.id ? " sel" : "") + '" data-id="' + esc(n.id) + '"><td>' +
          (n.tag ? H.ptag(n.tag) + " " : "") + "<code>" + esc(n.id) + "</code>" +
          (n.anchor ? '<div class="dim sm">' + ghAnchorLink(n.anchor) + "</div>" : "") +
          '</td><td class="sm">' + esc(n.role || n.kind || "") + "</td><td>" +
          statusBadge(n.status) + " " + statusBadge(n.verdict || "unknown") +
          '</td><td class="num">' + (n.dom && n.dom.subtree != null ? fmt(n.dom.subtree) : "—") + "</td></tr>";
      }).join("") + "</tbody></table>" +
      pagerHtml +
      (filtered.length ? "" : '<div class="empty-state">No nodes match this filter.</div>') +
      "</div><div id=\"bpInspector\">" + renderContractInspector(sel, res) + "</div></div>";

    if (hornList.length) {
      html += '<h4 class="p3-h">Horn Logic Contracts ' + provTag(res) + ' <span class="dim">(' + fmt(hornList.length) + ")</span></h4>" +
        hornList.slice(0, 60).map(function (h) {
          return '<div class="bp-horn-row">' + (h.tag ? H.ptag(h.tag) + " " : "") +
            '<span class="dim">REQUIRES</span> ' + (h.hyps || []).map(function (x) { return "<code>" + esc(x) + "</code>"; }).join(" ∧ ") +
            ' <span class="dim">⟹ PROVES</span> <code>' + esc(h.concl || "") + "</code>" +
            (h.via ? ' <span class="dim sm">via <code>' + esc(h.via) + "</code></span>" : "") + "</div>";
        }).join("");
    }

    if (claimsList.length) {
      html += '<h4 class="p3-h">Extracted Claims &amp; Verdicts <span class="dim">(' + fmt(claimsList.length) + ")</span></h4>" +
        '<table class="p3-table"><thead><tr><th>tag</th><th>claim</th><th>anchors (40e56bab)</th></tr></thead><tbody>' +
        claimsList.map(function (c) {
          return "<tr><td>" + H.ptag(c.tag || "L") + "</td><td>" + esc(c.text || "") + '</td><td class="dim sm mono">' +
            (c.anchors || []).map(function (a) { return ghAnchorLink(a); }).join("<br>") + "</td></tr>";
        }).join("") + "</tbody></table>";
    }

    if (opaqueList.length) {
      html += '<h4 class="p3-h">Explicitly Unread / OPAQUE Symbols <span class="dim">(' + fmt(opaqueList.length) + ")</span></h4>" +
        '<div class="p3-chips">' + opaqueList.map(function (o) {
          return '<span class="st-badge OPAQUE">' + esc(o) + "</span>";
        }).join(" ") + "</div>";
    }

    container.innerHTML = html;

    $$("#bpStSeg button", container).forEach(function (b) {
      b.addEventListener("click", function () { S.decompStatus = b.dataset.st; S.decompOffset = 0; renderDecompBody(res, container); });
    });
    $("#bpRoleSel", container).addEventListener("change", function () { S.decompRole = this.value; S.decompOffset = 0; renderDecompBody(res, container); });
    $("#bpVerdSel", container).addEventListener("change", function () { S.decompVerdict = this.value; S.decompOffset = 0; renderDecompBody(res, container); });
    var prevBtn = $("#bpPrev", container), nextBtn = $("#bpNext", container);
    if (prevBtn) prevBtn.addEventListener("click", function () { S.decompOffset = Math.max(0, S.decompOffset - DECOMP_PAGE); renderDecompBody(res, container); });
    if (nextBtn) nextBtn.addEventListener("click", function () { S.decompOffset = S.decompOffset + DECOMP_PAGE; renderDecompBody(res, container); });
    var t = null;
    $("#bpNodeQ", container).addEventListener("input", function () {
      var v = this.value; clearTimeout(t);
      t = setTimeout(function () {
        S.decompQ = v;
        S.decompOffset = 0;
        renderDecompBody(res, container);
        var e = $("#bpNodeQ", container); if (e) { e.focus(); e.setSelectionRange(v.length, v.length); }
      }, 200);
    });
    $$("a.gh-link", container).forEach(function (a) {
      a.addEventListener("click", function (ev) { ev.stopPropagation(); });
    });
    $$("#bpNodeTbl tr.click, .bp-dnode", container).forEach(function (el) {
      el.addEventListener("click", function () { S.decompNode = el.dataset.id; renderDecompBody(res, container); });
    });
    wireInspectorButtons(container);
  }

  function renderContractInspector(n, env) {
    if (!n) return '<div class="empty-state">Select any node on the left to inspect its header, fields, and verdict.</div>';
    var isOpaque = n.status === "OPAQUE";
    var fields = n.fields || [];
    return '<h4 class="p3-h">Side-by-Side Contract Inspector</h4>' +
      '<div class="bp-contract' + (isOpaque ? " opaque" : "") + '">' +
      '<div class="p3-chips">' + (n.tag ? H.ptag(n.tag) : "") + " " + statusBadge(n.status) + " " + statusBadge(n.verdict || "unknown") +
      (n.role ? ' <span class="kbadge">' + esc(n.role) + "</span>" : "") +
      (n.kind ? ' <code>' + esc(n.kind) + "</code>" : "") + "</div>" +
      '<div style="margin:6px 0 4px"><b><code>' + esc(n.id) + "</code></b></div>" +
      (n.anchor ? '<div class="dim sm mono">source (40e56bab): ' + ghAnchorLink(n.anchor) + (n.module ? " · module " + esc(n.module) : "") + "</div>" : "") +
      (n.dom ? '<div class="dim sm">dominator depth ' + fmt(n.dom.depth) + " · subtree " + fmt(n.dom.subtree) + (n.dom.idom ? " · idom <code>" + esc(n.dom.idom) + "</code>" : "") + "</div>" : "") +
      (n.header ? '<div class="bp-hdr">' + esc(n.header) + "</div>" : '<div class="dim sm p3-pad">(no 1-line header recorded)</div>') +
      (n.summary ? '<p style="margin:6px 0;line-height:1.45">' + esc(n.summary) + "</p>" : "") +
      (isOpaque ? '<div class="p3-msg bad"><b>OPAQUE / UNREAD:</b> the full unfolding of this definition was not inspected — do not infer its mathematical meaning from its name alone.</div>' : "") +
      '<div class="p3-toolbar" style="margin:8px 0 4px">' +
      '<button class="btn sm primary bp-slice-go" data-decl="' + esc(n.id) + '">Slice in Kernel</button>' +
      '<button class="btn sm bp-dom-go" data-decl="' + esc(n.id) + '">Dominators</button>' +
      '<button class="btn sm bp-ann-go" data-decl="' + esc(n.id) + '">Annotate</button></div>' +
      (fields.length ? '<h4 class="p3-h">Structure / Contract Fields ' + provTag(env) + '</h4>' +
        '<table class="p3-table"><thead><tr><th>field</th><th>type (≤1-line)</th><th>grounding</th></tr></thead><tbody>' +
        fields.map(function (f) {
          var op = /OPAQUE/i.test(String(f.ground || ""));
          return "<tr><td><code>" + esc(f.name || "") + "</code></td><td><code>" + esc(f.type || "") + "</code></td><td>" +
            (op ? '<span class="st-badge OPAQUE">' + esc(f.ground) + "</span>" : '<span class="sm">' + esc(f.ground || "") + "</span>") + "</td></tr>";
        }).join("") + "</tbody></table>" : "") +
      "</div>";
  }

  function wireInspectorButtons(root) {
    $$(".bp-slice-go", root).forEach(function (b) {
      b.addEventListener("click", function () { S.slice.name = b.dataset.decl; H.open("kernel", "slice"); });
    });
    $$(".bp-dom-go", root).forEach(function (b) {
      b.addEventListener("click", function () { H.openDom(b.dataset.decl); });
    });
    $$(".bp-ann-go", root).forEach(function (b) {
      b.addEventListener("click", function () { H.annotate(b.dataset.decl, "", "decl"); });
    });
  }

  function renderBlueprintMap() {
    return get("/api/decomp/index").then(function (idx) {
      var docs = idx.docs || [];
      var byKey = {};
      docs.forEach(function (d) { byKey[d.key] = d; });
      if (!byKey[S.decompKey]) S.decompKey = (docs[0] && docs[0].key) || "spine_map";
      // Prefer an already-ready doc on first load if current key is absent
      if (byKey[S.decompKey] && byKey[S.decompKey].state === "absent") {
        var firstReady = docs.filter(function (d) { return d.state === "ready"; })[0];
        if (firstReady) S.decompKey = firstReady.key;
      }
      var cardHtml = function (d) {
        var ok = d.state === "ready";
        return '<button class="bp-card ' + (ok ? "ready" : "absent") + (d.key === S.decompKey ? " active" : "") + '" data-doc="' + esc(d.key) + '">' +
          '<div class="ttl">' + esc(d.title) + '</div><div class="rt">' + esc(d.root) + '</div><div class="meta">' +
          (ok ? (H.ptag("L") + " <b>" + fmt(d.counts.nodes) + "</b> nodes · <b>" + fmt(d.counts.horn) + "</b> Horn · " +
            (d.counts.opaque ? '<span class="st-badge OPAQUE">' + fmt(d.counts.opaque) + " OPAQUE</span>" : '<span class="st-badge READ">0 OPAQUE</span>'))
            : '<span class="dim">Not built yet (' + esc(d.owner) + ")</span>") +
          "</div></button>";
      };
      var coreDocs = docs.filter(function (d) { return d.group === "core"; });
      var deepDocs = docs.filter(function (d) { return d.group !== "core"; });
      var html = '<div class="p3-src">' + H.ptag("L") + " <b>Proof Blueprint / Decompiler</b> · " + fmt(idx.ready) + " / " + fmt(idx.total) +
        " <code>leanre.decomp/v1</code> maps dynamically loaded from <code>outputs/decomp/</code> (pinned to " + ghAnchorLink("src/Main.lean:4", "40e56bab") + "). Click any card below to inspect contracts, verdicts, and <code>OPAQUE</code> boundaries.</div>" +
        '<div class="note-blk L p3-note"><p>Every contract below is read from pinned source/export declarations — never from proof-body narration. ' +
        "Symbols whose full unfolding was not verified are marked <b>OPAQUE</b>. Kernel dependency validity is separate from mathematical peer consensus.</p></div>" +
        renderBlueprintSvg(byKey, S.decompKey) +
        '<div id="bpCards">' +
        '<div class="bp-section-lbl">Core Architecture (' + fmt(coreDocs.length) + ")</div>" +
        '<div class="bp-grid">' + coreDocs.map(cardHtml).join("") + "</div>" +
        (deepDocs.length ? '<div class="bp-section-lbl">Deep-Dive Decompilations (' + fmt(deepDocs.length) + ")</div>" +
          '<div class="bp-grid">' + deepDocs.map(cardHtml).join("") + "</div>" : "") +
        "</div>" +
        '<div id="bpDocPanel"><div class="empty-state">Loading selected pillar…</div></div>';
      body().innerHTML = html;
      $$(".bp-node, #bpCards .bp-card", body()).forEach(function (el) {
        el.addEventListener("click", function () {
          S.decompKey = el.dataset.doc;
          S.decompNode = "";
          S.decompRole = "all";
          S.decompStatus = "all";
          S.decompVerdict = "all";
          S.decompQ = "";
          S.decompOffset = 0;
          renderBlueprintMap();
        });
      });
      return get("/api/decomp/doc", { name: S.decompKey }).then(function (res) {
        var panel = $("#bpDocPanel");
        if (panel) renderDecompBody(res, panel);
        return res;
      });
    });
  }

  function renderTcbAudit() {
    return get("/api/decomp/doc", { name: "tcb_audit" }).then(function (res) {
      var wrap = document.createElement("div");
      body().innerHTML = "";
      body().appendChild(wrap);
      renderDecompBody(res, wrap);
      return res;
    });
  }

  // ------------------------------------------------------------------ BLOAT WATERFALL (VIRTUAL PROOF STRIPPER / TRIM)
  function renderTrimWaterfall() {
    return get("/api/trim").then(function (res) {
      if (res.state === "absent") { body().innerHTML = absentPanel(res, "Virtual Proof Stripper — Bloat Waterfall (trim_report.json)"); return res; }
      var d = res.data || {};
      var pins = d.pins || {};
      var base = d.baseline || {};
      var c1 = d.c1_unused_modules || {};
      var c2 = d.c2_dead_decls_in_live_modules || {};
      var c3 = d.c3_forwarding_aliases_vn1 || {};
      var c4 = d.c4_duplicate_imports_and_shims || {};
      var c5 = d.c5_clones_and_k1n_duplicates || {};
      var c6 = d.c6_unread_phantom_struct_fields || {};
      var c7 = d.c7_macro_proof_term_blowup || {};
      var c8 = d.c8_waterfall || {};
      var core = c8.irreducible_core_estimate || {};
      var headroom = c8.further_refactoring_headroom_not_in_main_waterfall || {};
      var steps = c8.steps || [];
      var baseLines = base.total_lines_wc || 1;
      var baseMods = base.total_modules || 1;

      var detail = (pins.mirror_commit ? "mirror@" + String(pins.mirror_commit).slice(0, 8) : "") +
        (pins.solution_uncompressed_sha256 ? " · export " + String(pins.solution_uncompressed_sha256).slice(0, 12) + "…" : "");

      var html = srcLine(Object.assign({}, res, { source_detail: detail }), "Virtual Proof Stripper (trim_report.json) — exact disjoint peel from 175,187 files / 17.37M lines down to irreducible kernel core") +
        '<div class="note-blk L p3-note"><p><b>Epistemic scope (Layers 1–4):</b> Exact structural bloat accounting over the kernel-verified export and pinned mirror (' +
        ghAnchorLink("src/Main.lean:4", "40e56bab") + "). Every step is strictly disjoint; size compression measures boilerplate redundancy only and is independent of mathematical peer review.</p></div>" +
        '<div class="p3-stats">' +
        stat("files (corpus → core)", fmt(base.total_modules) + " → " + fmt(core.modules) + '<div class="dim sm">' + Number(core.pct_of_corpus_modules || 0).toFixed(2) + "% kept · −" + fmt((base.total_modules || 0) - (core.modules || 0)) + " peeled</div>", res, "wide") +
        stat("source lines (wc → core)", fmt(base.total_lines_wc) + " → " + fmt(core.lines_wc) + '<div class="dim sm">' + Number(core.pct_of_corpus_lines || 0).toFixed(2) + "% · " + fmt(core.lines_wc_conservative_nonblank) + " non-blank</div>", res, "wide") +
        stat("kernel live decls", fmt(base.kernel_live_records) + " → " + fmt(core.kernel_live_decls_total) + '<div class="dim sm">' + fmt(core.kernel_project_non_aux_core_decls) + " project non-aux core</div>", res, "wide") +
        stat("kernel value nodes", fmt(base.kernel_live_value_nodes) + " → " + fmt(core.kernel_live_value_nodes_total) + '<div class="dim sm">' + Number(core.pct_of_corpus_value_nodes || 0).toFixed(2) + "% irreducible</div>", res, "wide") +
        "</div>";

      // 5-Step Disjoint Waterfall Table
      var wfBar = function (afterLines, cutLines) {
        var keepPct = Math.max(0, Math.min(100, (afterLines / baseLines) * 100));
        var cutPct = Math.max(0, Math.min(100 - keepPct, (cutLines / baseLines) * 100));
        return '<div class="wf-bar-wrap"><span class="wf-bar"><i class="keep" style="width:' + keepPct.toFixed(1) + '%"></i>' +
          (cutPct > 0 ? '<i class="cut" style="width:' + cutPct.toFixed(1) + '%"></i>' : "") +
          '</span><span class="wf-pct">' + keepPct.toFixed(1) + "%</span></div>";
      };

      html += '<h4 class="p3-h">Disjoint 5-Step Bloat Waterfall ' + provTag(res) + ' <span class="dim">(' + fmt(steps.length) + " stages)</span></h4>" +
        '<table class="p3-table" id="trimWfTbl"><thead><tr><th>stage</th><th>lines remaining (of 17.37M)</th><th class="num">files peeled → left</th><th class="num">lines peeled → left</th><th class="num">live decls</th><th class="num">value nodes</th></tr></thead><tbody>' +
        '<tr><td><b>0. Full corpus baseline</b><div class="dim sm">175,187 .lean files · 1.03 GB</div></td><td>' + wfBar(baseLines, 0) +
        '</td><td class="num">' + fmt(base.total_modules) + '</td><td class="num">' + fmt(base.total_lines_wc) +
        '</td><td class="num">' + fmt(base.kernel_live_records) + '</td><td class="num">' + fmt(base.kernel_live_value_nodes) + "</td></tr>" +
        steps.map(function (st, idx) {
          var rem = st.removed || {}, aft = st.after || {};
          return "<tr><td><b>" + (idx + 1) + ". " + esc(st.label || st.step_id) + '</b>' +
            (st.precision ? '<div class="dim sm">' + esc(st.precision) + "</div>" : "") +
            "</td><td>" + wfBar(aft.lines_wc || 0, rem.lines_wc || 0) +
            '</td><td class="num">' + (rem.modules ? '<span class="warn">−' + fmt(rem.modules) + "</span> → " : "") + "<b>" + fmt(aft.modules) + "</b>" +
            '</td><td class="num"><span class="warn">−' + fmt(rem.lines_wc) + "</span> → <b>" + fmt(aft.lines_wc) + "</b>" +
            (aft.lines_wc_conservative_nonblank && aft.lines_wc_conservative_nonblank !== aft.lines_wc
              ? '<div class="dim sm">non-blank: ' + fmt(aft.lines_wc_conservative_nonblank) + "</div>" : "") +
            '</td><td class="num">' + fmt(aft.kernel_live_decls) +
            '</td><td class="num">' + fmt(aft.kernel_live_value_nodes) + "</td></tr>";
        }).join("") + "</tbody></table>";

      // 7 Bloat Mechanisms Breakdown
      var c1Peel = c1.truly_unused_peeled || {};
      var c3Disj = c3.source_footprint_disjoint_after_step2 || {};
      var c4Raw = c4.corpus_raw_totals || {};
      var c4Stg = c4.stage_accounting_for_all_duplicate_imports || {};
      var c5Alpha = c5.alpha_body_clone || {};
      var c5K1n = (c5.kernel_k1n_type_duplicates || {}).step4b_disjoint_after_step3_and_4a || {};
      var c7Copy = c7.copy_cases || {};
      var c7Mods = c7Copy.modules || [];
      var topBloat = (c2.top_bloated_live_modules || [])[0] || null;
      var topBloatLine = topBloat && topBloat.sample_dead_decl && String(topBloat.sample_dead_decl).indexOf("@") >= 0
        ? String(topBloat.sample_dead_decl).split("@").pop() : "";
      var topBloatAnchor = topBloat && topBloat.file_path ? topBloat.file_path + (topBloatLine ? ":" + topBloatLine : "") : "";

      var copyAnchors = c7Mods.map(function (m) {
        var ln = (m.macro_hit_lines && m.macro_hit_lines[0]) ? ":" + m.macro_hit_lines[0] : "";
        return ghAnchorLink(m.file_path + ln, (m.top_decl && m.top_decl.name ? shortName(m.top_decl.name) : shortName(m.module)) + ln);
      }).join("<br>");

      var mechs = [
        {
          id: "C1", name: "Zero-kernel unused files",
          metric: fmt(c1Peel.modules) + " files peeled (" + fmt(c1Peel.lines_wc) + " lines)",
          detail: fmt((c1.alignment_gap_kept_live || {}).modules) + " alignment-gap files kept live; 28,471 unused + 239 private + 164 shims + 11 meta",
          anchor: ghAnchorLink("src/Main.lean:4", "Main.lean:4 (root)")
        },
        {
          id: "C2", name: "Dead intra-file declarations",
          metric: fmt(c2.dead_decls_in_all_live_modules) + " dead decls in " + fmt(c2.modules_with_at_least_one_dead_decl) + " live files",
          detail: fmt(c2.dead_lines_block_with_sep) + " block lines (" + fmt(c2.dead_lines_trimmed_nonblank) + " trimmed non-blank)",
          anchor: topBloatAnchor ? ghAnchorLink(topBloatAnchor, shortName(topBloat.module) + (topBloatLine ? ":" + topBloatLine : "")) : "—"
        },
        {
          id: "C3", name: "vn=1 forwarding theorem aliases",
          metric: fmt(c3.project_thm_vn1_total) + " aliases (" + fmt(c3.project_thm_vn1_global_theory_T) + " in GlobalTheory.T.*)",
          detail: fmt(c3Disj.pure_alias_live_modules_removed) + " pure-alias live files removed (" + fmt(c3Disj.total_lines_removed_step3) + " lines)",
          anchor: "GlobalTheory.T.* wrapper spine"
        },
        {
          id: "C4", name: "Duplicate import Mathlib & shims",
          metric: fmt(c4Stg.dup_mathlib_peeled_in_step3_pure_alias_files) + " / " + fmt(c4Raw.modules_with_duplicate_mathlib_import) + " in pure-alias files",
          detail: fmt(c4Stg.dup_mathlib_peeled_in_step5_surviving_core) + " surviving core dups + " + fmt(c4Raw.duplicate_project_import_lines) + " dup project imports + " + fmt(c4Raw.reexport_or_scope_only_shims_total) + " shims",
          anchor: "Step 1 / 3 / 5 accounting"
        },
        {
          id: "C5a", name: "Surviving live alpha-body clones",
          metric: fmt(c5Alpha.step4a_redundant_modules_removed) + " live modules (" + fmt(c5Alpha.step4a_surviving_clusters) + " clusters)",
          detail: fmt(c5Alpha.step4a_lines_removed) + " lines · " + fmt(c5Alpha.step4a_kernel_decls_removed) + " kernel decls (" + fmt(c5Alpha.raw_redundant_modules) + " raw across corpus)",
          anchor: "Step 4a alpha-identical bodies"
        },
        {
          id: "C5b", name: "Identical-k1n duplicate theorems",
          metric: fmt(c5K1n.redundant_user_thms) + " redundant non-aux thms (" + fmt(c5K1n.clusters) + " clusters)",
          detail: fmt(c5K1n.pure_k1n_dup_modules_removed) + " pure-dup files · " + fmt(c5K1n.source_lines_removed) + " lines · " + fmt(c5K1n.kernel_value_nodes_removed) + " value nodes",
          anchor: "Step 4b earliest-decl_id substitution"
        },
        {
          id: "C7", name: "copy_cases macro proof-term blowup",
          metric: fmt(c7Copy.top2_pair_value_nodes) + " value nodes in " + fmt(c7Copy.total_source_lines_wc) + " lines (" + fmt(c7Copy.files_total) + " files)",
          detail: "lam_copy " + fmt(c7Copy.lam_copy_value_nodes) + " + sigSpan_copy " + fmt(c7Copy.sigSpan_copy_value_nodes) + " (" + Number(c7Copy.top2_pct_of_corpus_value_nodes || 0).toFixed(2) + "% of corpus); CutCptCopy " + fmt((c7.CutCptCopy || {}).generated_live_theorems_count) + " thms · kcopy " + fmt((c7.kcopy || {}).total_live_decls) + " decls",
          anchor: copyAnchors || "—"
        }
      ];

      html += '<h4 class="p3-h">Seven Bloat Mechanisms ' + provTag(res) + ' <span class="dim">(7 mechanisms)</span></h4>' +
        '<table class="p3-table" id="trimMechTbl"><thead><tr><th>#</th><th>mechanism</th><th>exact count</th><th>breakdown</th><th>source anchor (40e56bab)</th></tr></thead><tbody>' +
        mechs.map(function (m) {
          return "<tr><td><code>" + esc(m.id) + "</code></td><td><b>" + esc(m.name) + "</b></td><td>" + esc(m.metric) +
            '</td><td class="sm dim">' + esc(m.detail) + '</td><td class="sm mono">' + m.anchor + "</td></tr>";
        }).join("") + "</tbody></table>";

      // Phantom / Unread Contract Headroom + Top Bloated Live Modules side-by-side
      var phantomRows = [];
      var litCm = c6.LiteratureCMHypothesis || {};
      if (litCm.declared_fields != null) {
        var bs = litCm.builder_subtree || {};
        phantomRows.push(["LiteratureCMHypothesis", fmt(litCm.live_projected_fields) + " / " + fmt(litCm.declared_fields) + " fields read", fmt(bs.dom_subtree_decls) + " dom decls · " + fmt(bs.exclusive_lines_wc) + " excl. lines · " + fmt(bs.dom_subtree_value_nodes) + " vn"]);
      }
      var oic = c6.OpenImageCondition || {};
      if (oic.declared_fields != null) {
        phantomRows.push(["OpenImageCondition", fmt(oic.live_projected_fields) + " / " + fmt(oic.declared_fields) + " fields read", fmt(oic.wrappers_reading_O) + " / " + fmt(oic.module_wrapper_theorems) + " wrappers read O"]);
      }
      var ols = c6.OpenLiteratureStatements || {};
      if (ols.declared_fields != null) {
        phantomRows.push(["OpenLiteratureStatements", fmt(ols.direct_projection_users) + " direct / " + fmt(ols.transitive_projection_users) + " trans. users", fmt(ols.independent_of_O_theorems) + " / " + fmt(ols.module_theorems_total) + " module theorems independent of O"]);
      }
      var lla = c6.LitLocAlt || {};
      if (lla.declared_fields != null) {
        phantomRows.push(["LitLocAlt", fmt(lla.live_projected_fields_count) + " / " + fmt(lla.declared_fields) + " fields read", fmt(lla.unread_fields_count) + " unread fields (" + (lla.unread_fields || []).join(", ") + ")"]);
      }

      var bloated = (c2.top_bloated_live_modules || []).slice(0, 15);
      html += '<div class="p3-cols"><div>' +
        '<h4 class="p3-h">Top Bloated Live Modules (Intra-File Dead Code) ' + provTag(res) + "</h4>" +
        '<table class="p3-table"><thead><tr><th>module (40e56bab)</th><th class="num">live / dead</th><th class="num">dead lines</th></tr></thead><tbody>' +
        bloated.map(function (b) {
          var ln = b.sample_dead_decl && String(b.sample_dead_decl).indexOf("@") >= 0 ? ":" + String(b.sample_dead_decl).split("@").pop() : "";
          return "<tr><td>" + ghAnchorLink((b.file_path || "") + ln, b.module || b.file_path) +
            '</td><td class="num">' + fmt(b.live_decls) + " / <span class=\"warn\">" + fmt(b.dead_decls) + "</span>" +
            '</td><td class="num">' + fmt(b.dead_block_lines) + '<div class="dim sm">(' + fmt(b.dead_trimmed_lines) + " nb)</div></td></tr>";
        }).join("") + "</tbody></table>" +
        "</div><div>" +
        '<h4 class="p3-h">Phantom / Unread Contract Headroom (Not in Waterfall) ' + provTag(res) + "</h4>" +
        '<table class="p3-table"><thead><tr><th>structure</th><th>projection usage</th><th>refactoring headroom</th></tr></thead><tbody>' +
        phantomRows.map(function (r) {
          return "<tr><td><code>" + esc(r[0]) + '</code></td><td class="sm">' + esc(r[1]) + '</td><td class="sm dim">' + esc(r[2]) + "</td></tr>";
        }).join("") + "</tbody></table>" +
        (headroom.surviving_sigset_clone_heuristic_lines != null
          ? '<div class="p3-src" style="margin-top:8px">' + provTag(res) + " Upper-bound heuristic headroom (not peeled): <code>LiteratureCMHypothesis</code> " +
            fmt(headroom.unread_LiteratureCMHypothesis_exclusive_lines) + " excl. lines · <code>copy_cases</code> " +
            fmt(headroom.copy_cases_lam_plus_sigSpan_value_nodes) + " vn · surviving <code>s1a</code> sigset clones " +
            fmt(headroom.surviving_sigset_clone_heuristic_lines) + " lines.</div>" : "") +
        "</div></div>";

      body().innerHTML = html;
      return res;
    });
  }

  // ------------------------------------------------------------------ COMPUTE & DEAD CODE
  function renderComputeAtlas() {
    return get("/api/decomp/compute", { q: S.compute.q, bucket: S.compute.bucket, limit: 100, offset: S.compute.offset }).then(function (res) {
      if (res.state === "absent") { body().innerHTML = absentPanel(res, "Computation & 28,904-file dead-code atlas"); return res; }
      var data = res.data || {};
      var ct = data.corpus_totals || {};
      var zk = data.zero_kernel_classification || {};
      var ca = data.computation_atlas || {};
      var tgt = data.target || {};
      var detail = (tgt.repo_mirror ? tgt.repo_mirror : "") + (tgt.ndjson_uncompressed_sha256 ? " · sha256 " + String(tgt.ndjson_uncompressed_sha256).slice(0, 12) + "…" : "");
      var html = srcLine(Object.assign({}, res, { source_detail: detail }), "Computation inventory (decide +kernel, kexactB, CutCptCopy, prime tables) & 28,904-file dead-code triage");

      // Top-level corpus & kernel flag summary stats
      var kfc = ca.kernel_flag_counts || {};
      var statItems = [];
      if (ct.total_modules != null) statItems.push(["total .lean modules", fmt(ct.total_modules)]);
      if (ct.kernel_covered_modules != null) statItems.push(["kernel-covered modules", fmt(ct.kernel_covered_modules)]);
      if (ct.zero_kernel_modules != null) statItems.push(["0-kernel modules", fmt(ct.zero_kernel_modules) + (ct.zero_kernel_lines_wc ? '<div class="dim sm">' + fmt(ct.zero_kernel_lines_wc) + " lines</div>" : "")]);
      if (kfc.F_OF_DECIDE) statItems.push(["live of_decide_eq_true", fmt(kfc.F_OF_DECIDE.live_decls)]);
      if (kfc.F_REFL_TRUE) statItems.push(["live Eq.refl Bool true", fmt(kfc.F_REFL_TRUE.live_decls)]);
      if (kfc.F_REDUCE_BOOL) statItems.push(["live ofReduceBool / Nat", fmt(kfc.F_REDUCE_BOOL.live_decls) + " / " + fmt(kfc.F_REDUCE_NAT ? kfc.F_REDUCE_NAT.live_decls : 0)]);
      if (statItems.length) {
        html += '<div class="p3-stats">' + statItems.map(function (st) { return stat(st[0], st[1], res); }).join("") + "</div>";
      }

      // Disjoint zero-kernel module buckets (28,904 files)
      var buckets = zk.buckets || data.dead_code_buckets || null;
      if (buckets) {
        var bRows = Array.isArray(buckets) ? buckets : Object.keys(buckets).map(function (k) {
          var v = buckets[k];
          return typeof v === "object" && v !== null ? Object.assign({ bucket: k }, v) : { bucket: k, modules: v };
        });
        bRows.sort(function (a, b) { return (b.modules || b.count || 0) - (a.modules || a.count || 0); });
        html += '<h4 class="p3-h">Zero-Kernel Module Classification (' + fmt(zk.bucket_sum_modules || ct.zero_kernel_modules) + " files · " +
          (zk.strictly_disjoint ? "strictly disjoint" : "grouped") + ") " + provTag(res) + '</h4>' +
          '<table class="p3-table" id="compBuckets"><thead><tr><th>bucket (click to filter spot-checks)</th><th class="num">modules</th><th class="num">% of 0-kernel</th><th class="num">lines</th><th>top folders</th></tr></thead><tbody>' +
          bRows.map(function (b) {
            var bn = b.bucket || b.category || b.name || "";
            var cnt = b.modules != null ? b.modules : (b.count != null ? b.count : 0);
            var pct = b.pct_of_zero != null ? Number(b.pct_of_zero).toFixed(2) + "%" : "—";
            var topF = (b.top_folders_l2 || b.top_folders_l1 || []).slice(0, 3).map(function (x) {
              if (Array.isArray(x)) return x[0] + " (" + fmt(x[1]) + ")";
              if (x && typeof x === "object") return (x.folder || x.name || "") + (x.modules != null ? " (" + fmt(x.modules) + ")" : "");
              return String(x);
            }).join(" · ");
            return '<tr class="click' + (S.compute.bucket === bn ? " sel" : "") + '" data-b="' + esc(bn) + '"><td><code>' + esc(bn) +
              '</code></td><td class="num">' + fmt(cnt) + '</td><td class="num">' + esc(pct) + '</td><td class="num">' + fmt(b.lines_wc) +
              '</td><td class="dim sm">' + esc(topF || b.description || "") + "</td></tr>";
          }).join("") + "</tbody></table>";
      }

      // Certified math computational tables (prime tables, dyadic intervals, factorial ladders)
      var cmt = ca.certified_math_table || [];
      if (cmt.length) {
        html += '<h4 class="p3-h">Certified Computational Tables &amp; Thresholds ' + provTag(res) + ' <span class="dim">(' + fmt(cmt.length) + ")</span></h4>" +
          '<table class="p3-table"><thead><tr><th>computation</th><th>status</th><th>mechanism</th><th>symbol / module</th><th>scope</th></tr></thead><tbody>' +
          cmt.map(function (r) {
            var live = String(r.status || "").toUpperCase() === "LIVE";
            return "<tr><td><b>" + esc(r.label || "") + "</b></td><td>" +
              '<span class="st-badge ' + (live ? "READ" : "OPAQUE") + '">' + esc(r.status || "") + "</span>" +
              '</td><td><code>' + esc(r.mechanism || "") + "</code></td><td><code>" + esc(r.symbol || "") + '</code><div class="dim sm">' +
              esc(r.module || "") + (r.anchor_line ? ":" + r.anchor_line : "") + '</div></td><td class="sm">' + esc(r.mathematical_scope || "") + "</td></tr>";
          }).join("") + "</tbody></table>";
      }

      // All 34 decide +kernel files
      var dkf = ca.decide_kernel_all_files || [];
      if (dkf.length) {
        html += '<h4 class="p3-h">All <code>decide +kernel</code> Files ' + provTag(res) + ' <span class="dim">(' + fmt(dkf.length) + ")</span></h4>" +
          '<table class="p3-table"><thead><tr><th>module</th><th>status</th><th class="num">hits</th><th class="num">kernel decls</th><th class="num">lines</th></tr></thead><tbody>' +
          dkf.map(function (r) {
            var live = String(r.status || "").toUpperCase() === "LIVE";
            return "<tr><td><code>" + esc(r.module || "") + '</code>' + (r.zero_bucket ? '<div class="dim sm">bucket: ' + esc(r.zero_bucket) + "</div>" : "") +
              '</td><td><span class="st-badge ' + (live ? "READ" : "OPAQUE") + '">' + esc(r.status || "") + "</span></td>" +
              '<td class="num">' + fmt(r.hit_count) + '</td><td class="num">' + fmt(r.kernel_module_decls) + '</td><td class="num">' + fmt(r.lines_wc) + "</td></tr>";
          }).join("") + "</tbody></table>";
      }

      // Spot-check dead-file triage rows
      if (Array.isArray(res.triage_rows)) {
        html += '<h4 class="p3-h">Zero-Kernel Bucket Spot-Checks ' + provTag(res) + ' <span class="dim">(' + fmt(res.triage_total) + ")</span></h4>" +
          '<div class="p3-toolbar"><input type="search" id="compQ" placeholder="filter spot-checked modules…" value="' + esc(S.compute.q) + '" spellcheck="false">' +
          (S.compute.bucket ? '<button class="btn sm" id="compClearB">bucket: ' + esc(S.compute.bucket) + " ✕</button>" : "") + "</div>" +
          '<table class="p3-table"><thead><tr><th>module</th><th>bucket</th><th class="num">lines</th><th>evidence</th></tr></thead><tbody>' +
          res.triage_rows.map(function (r) {
            return "<tr><td><code>" + esc(r.module || r.file || r.file_path || "") + "</code></td><td><code>" + esc(r.bucket || r.category || "") +
              '</code></td><td class="num">' + fmt(r.lines_wc) + '</td><td class="sm">' + esc(r.reason || r.evidence || r.note || r.summary || "") + "</td></tr>";
          }).join("") + "</tbody></table>";
      }

      body().innerHTML = html;
      $$("#compBuckets tr.click", body()).forEach(function (tr) {
        tr.addEventListener("click", function () {
          S.compute.bucket = S.compute.bucket === tr.dataset.b ? "" : tr.dataset.b;
          S.compute.offset = 0; renderComputeAtlas();
        });
      });
      if ($("#compClearB")) $("#compClearB").addEventListener("click", function () { S.compute.bucket = ""; renderComputeAtlas(); });
      var cq = $("#compQ");
      if (cq) {
        var t = null;
        cq.addEventListener("input", function () {
          var v = cq.value; clearTimeout(t);
          t = setTimeout(function () {
            S.compute.q = v; S.compute.offset = 0;
            renderComputeAtlas().then(function () { var e = $("#compQ"); if (e) { e.focus(); e.setSelectionRange(v.length, v.length); } });
          }, 250);
        });
      }
      return res;
    });
  }

  // ------------------------------------------------------------------ KERNEL: LIVE CONE SLICER
  var SLICE_PRESETS = [
    ["allChi", "allChi (1.41M)"],
    ["riemannHypothesis", "riemannHypothesis"],
    ["UpperTheory.FinalTheorems.everyCharacter", "everyCharacter"],
    ["UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter", "Pillar B: Galois"],
    ["UpperTheory.One.vwin_of_row", "Pillar C: Window"],
    ["SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt", "Pillar D: Volume"]
  ];

  function renderSliceSvg(d) {
    var nodes = d.nodes || [];
    if (!nodes.length) return '<div class="empty-state">No edges matched this slice filter.</div>';
    var byD = {}, depths = [];
    nodes.forEach(function (n) {
      if (!byD[n.depth]) { byD[n.depth] = []; depths.push(n.depth); }
      byD[n.depth].push(n);
    });
    depths.sort(function (a, b) { return a - b; });
    var W = 205, Hn = 42, gx = 18, gy = 28, pos = {}, maxCols = 1;
    depths.forEach(function (dp, row) {
      var arr = byD[dp];
      if (arr.length > maxCols) maxCols = arr.length;
      arr.forEach(function (n, col) {
        pos[n.id] = { x: 12 + col * (W + gx), y: 12 + row * (Hn + gy) };
      });
    });
    var svgW = Math.max(700, 24 + maxCols * (W + gx));
    var svgH = Math.max(100, 24 + depths.length * (Hn + gy));
    var eSvg = (d.edges || []).map(function (e) {
      var a = pos[e.src], b = pos[e.dst];
      if (!a || !b) return "";
      var cls = e.dep === "type" ? "type" : (e.dep === "type+value" ? "both" : "value");
      return '<line class="sl-edge ' + cls + '" x1="' + (a.x + W / 2) + '" y1="' + (a.y + Hn) + '" x2="' + (b.x + W / 2) + '" y2="' + b.y + '"/>';
    }).join("");
    var nSvg = nodes.map(function (n) {
      var p = pos[n.id];
      var cls = "sl-node" + (n.depth === 0 ? " root" : "") + (n.stopped ? " stopped" : "");
      var sub = n.kind + (n.subtree ? " · dom " + fmt(n.subtree) : "") + (n.stopped ? " · stop" : "");
      return '<g class="' + cls + '" data-decl="' + esc(n.id) + '" transform="translate(' + p.x + "," + p.y + ')">' +
        '<rect width="' + W + '" height="' + Hn + '"/>' +
        '<text x="7" y="17">' + esc(shortName(n.id).slice(0, 28)) + "</text>" +
        '<text class="sub" x="7" y="33">' + esc(sub.slice(0, 32)) + "</text></g>";
    }).join("");
    return '<div class="sl-svg-wrap"><svg width="' + svgW + '" height="' + svgH + '" viewBox="0 0 ' + svgW + " " + svgH + '">' + eSvg + nSvg + "</svg></div>";
  }

  function renderKernelSlice() {
    return get("/api/kernel/slice", {
      name: S.slice.name, dir: S.slice.dir, depth: S.slice.depth,
      edge_kind: S.slice.edge_kind, max_nodes: S.slice.max_nodes,
      stop_at: S.slice.stop_at, stop_lib: S.slice.stop_lib ? "1" : "0"
    }).then(function (d) {
      if (d.state === "absent") { body().innerHTML = absentPanel(d, "kernel-exact cone slicer"); return d; }
      var ctlHtml = srcLine(d, "live kernel cone slicer & single-declaration inspector (direct type/value deps, dominators, shortest path to root)") +
        '<div class="p3-chips" id="slPresets">' + SLICE_PRESETS.map(function (p) {
          return '<button class="fchip' + (S.slice.name === p[0] ? " active" : "") + '" data-name="' + esc(p[0]) + '">' + esc(p[1]) + "</button>";
        }).join("") + "</div>" +
        '<div class="p3-toolbar">' +
        '<input type="search" id="slName" value="' + esc(S.slice.name) + '" placeholder="exact declaration name (Enter)…" spellcheck="false">' +
        '<select id="slDir"><option value="deps"' + (S.slice.dir === "deps" ? " selected" : "") + '>dependencies ↓</option>' +
        '<option value="rdeps"' + (S.slice.dir === "rdeps" ? " selected" : "") + '>reverse dependents ↑</option></select>' +
        '<select id="slDepth">' + [1, 2, 3, 4].map(function (v) { return '<option value="' + v + '"' + (S.slice.depth === v ? " selected" : "") + ">depth " + v + "</option>"; }).join("") + "</select>" +
        '<select id="slEdge">' + [["all", "all edges"], ["type", "type only"], ["value", "value only"], ["both", "type+value"]].map(function (v) {
          return '<option value="' + v[0] + '"' + (S.slice.edge_kind === v[0] ? " selected" : "") + ">" + v[1] + "</option>";
        }).join("") + "</select>" +
        '<select id="slCap">' + [25, 60, 120].map(function (v) { return '<option value="' + v + '"' + (S.slice.max_nodes === v ? " selected" : "") + ">cap " + v + "</option>"; }).join("") + "</select>" +
        '<label class="chk-label"><input type="checkbox" id="slStopLib"' + (S.slice.stop_lib ? " checked" : "") + "> stop at Mathlib/Init</label>" +
        '<button class="btn sm primary" id="slGo">Slice</button></div>';

      if (!d.found) {
        var sg = (d.suggestions || []).map(function (s) {
          return '<tr><td><a href="#" class="sl-pick" data-decl="' + esc(s.name) + '">' + esc(s.name) + "</a></td><td><code>" + esc(s.kind) + "</code></td></tr>";
        }).join("");
        body().innerHTML = ctlHtml + '<div class="p3-absent"><h3>Declaration not found</h3><p><code>' + esc(d.queried || S.slice.name) +
          "</code> is not in <code>decls</code> or <code>consts</code>.</p>" +
          (sg ? '<table class="p3-table"><thead><tr><th>did you mean?</th><th>kind</th></tr></thead><tbody>' + sg + "</tbody></table>" : "") + "</div>";
      } else {
        var t = d.target;
        S.slice.name = t.name;
        var html = ctlHtml +
          '<div class="p3-stats">' +
          stat("declaration", "<code>" + esc(t.name) + "</code> <span class=\"dim sm\">" + esc(t.kind) + "</span>" +
            (t.module ? '<div class="dim sm">' + esc(t.module) + "</div>" : '<div class="warn sm">' + esc(t.module_method || "unmatched") + "</div>"), d, "wide") +
          stat("fan-in / fan-out", fmt(t.fan_in) + " / " + fmt(t.fan_out) + '<div class="dim sm">' + fmt(t.fan_out_type) + " type · " + fmt(t.fan_out_value) + " value</div>", d) +
          stat("dominator subtree (ALL)", t.dom ? fmt(t.dom.subtree) + '<div class="dim sm">depth ' + fmt(t.dom.depth) + "</div>" : "dead", d) +
          stat("slice size", fmt((d.nodes || []).length) + " nodes · " + fmt((d.edges || []).length) + " edges" + (d.truncated ? " (capped)" : ""), d) +
          (t.sighash ? stat("sighash (k1n)", '<code class="sm">' + esc(t.sighash) + "</code>", d, "wide") : "") +
          "</div>";

        if ((d.path_to_root || []).length) {
          html += '<h4 class="p3-h">Shortest Dependency Path from <code>' + esc(d.path_root || "") + "</code> " + provTag(d) + '</h4>' +
            '<div class="sl-path">' + d.path_to_root.map(function (p) {
              return '<a href="#" class="sl-pick" data-decl="' + esc(p.name) + '" title="' + esc(p.name) + '">' + esc(shortName(p.name)) + "</a>";
            }).join('<span class="arr">→</span>') + "</div>";
        }

        html += '<h4 class="p3-h">Cone Slice Graph ' + provTag(d) + ' <span class="dim sm">(blue = type edge · slate = value · teal = type+value · click any box to re-slice)</span></h4>' +
          renderSliceSvg(d) +
          '<div class="p3-cols"><div>' +
          '<h4 class="p3-h">Direct Type Dependencies ' + provTag(d) + ' <span class="dim">(' + fmt((d.direct_type_deps || []).length) + ")</span></h4>" +
          '<table class="p3-table" id="slTypeTbl"><thead><tr><th>declaration</th><th>kind</th><th>edge</th></tr></thead><tbody>' +
          (d.direct_type_deps || []).slice(0, 50).map(function (x) {
            return '<tr><td><a href="#" class="sl-pick" data-decl="' + esc(x.name) + '">' + esc(x.name) + "</a></td><td><code>" + esc(x.kind) + '</code></td><td class="sm">' + esc(x.dep) + "</td></tr>";
          }).join("") + "</tbody></table>" + ((d.direct_type_deps || []).length ? "" : '<div class="empty-state">None.</div>') +
          '<h4 class="p3-h">Direct Value-Only Dependencies ' + provTag(d) + ' <span class="dim">(' + fmt((d.direct_value_deps || []).length) + ")</span></h4>" +
          '<table class="p3-table" id="slValTbl"><thead><tr><th>declaration</th><th>kind</th><th>module</th></tr></thead><tbody>' +
          (d.direct_value_deps || []).slice(0, 50).map(function (x) {
            return '<tr><td><a href="#" class="sl-pick" data-decl="' + esc(x.name) + '">' + esc(x.name) + "</a></td><td><code>" + esc(x.kind) + '</code></td><td class="dim sm">' + esc(x.module || "—") + "</td></tr>";
          }).join("") + "</tbody></table>" + ((d.direct_value_deps || []).length ? "" : '<div class="empty-state">None.</div>') +
          "</div><div>" +
          '<h4 class="p3-h">Immediate Dominator Children (ALL) ' + provTag(d) + ' <span class="dim">(' + fmt((d.dom_children || []).length) + ")</span></h4>" +
          '<table class="p3-table"><thead><tr><th>declaration</th><th class="num">subtree</th></tr></thead><tbody>' +
          (d.dom_children || []).map(function (c) {
            return '<tr><td><a href="#" class="sl-pick" data-decl="' + esc(c.name) + '">' + esc(c.name) + '</a></td><td class="num">' + fmt(c.subtree) + "</td></tr>";
          }).join("") + "</tbody></table>" + ((d.dom_children || []).length ? "" : '<div class="empty-state">Dominator leaf (dominates nothing else).</div>') +
          '<div class="p3-toolbar"><button class="btn sm bp-dom-go" data-decl="' + esc(t.name) + '">Open in Dominator Tree</button>' +
          '<button class="btn sm primary bp-ann-go" data-decl="' + esc(t.name) + '">Annotate</button></div>' +
          "</div></div>";
        body().innerHTML = html;
      }

      var apply = function () {
        S.slice.name = ($("#slName").value || "").trim();
        S.slice.dir = $("#slDir").value;
        S.slice.depth = Number($("#slDepth").value) || 2;
        S.slice.edge_kind = $("#slEdge").value;
        S.slice.max_nodes = Number($("#slCap").value) || 60;
        S.slice.stop_lib = $("#slStopLib").checked;
        renderKernelSlice();
      };
      $("#slGo").addEventListener("click", apply);
      $("#slName").addEventListener("keydown", function (ev) { if (ev.key === "Enter") apply(); });
      ["#slDir", "#slDepth", "#slEdge", "#slCap", "#slStopLib"].forEach(function (sel) {
        $(sel).addEventListener("change", apply);
      });
      $$("#slPresets button").forEach(function (b) {
        b.addEventListener("click", function () { S.slice.name = b.dataset.name; renderKernelSlice(); });
      });
      $$(".sl-pick, .sl-node", body()).forEach(function (el) {
        el.addEventListener("click", function (ev) { ev.preventDefault(); S.slice.name = el.dataset.decl; renderKernelSlice(); });
      });
      wireInspectorButtons(body());
      return d;
    });
  }

  // ------------------------------------------------------------------ FLIRT: COARSE CLUSTERS
  function renderFlirtClusters() {
    return get("/api/flirt/clusters", { q: S.clusters.q, kind: S.clusters.kind, pillar: S.clusters.pillar, limit: 100, offset: S.clusters.offset }).then(function (d) {
      if (d.state === "absent") { body().innerHTML = absentPanel(d, "FLIRT coarse structural clustering"); return d; }
      var sm = d.summary || {};
      var kc = d.kind_counts || {}, pc = d.pillar_counts || {};
      var html = srcLine(d, "FLIRT coarse kernel-aware blueprint clusters (collapsing compiler auxiliaries, CutCptCopy shells, statement wrappers & k1n duplicates)") +
        '<div class="p3-stats">' + Object.keys(sm).slice(0, 8).map(function (k) {
          var v = sm[k];
          if (typeof v === "object" && v !== null) return "";
          var val = k === "collapse_pct" ? Number(v).toFixed(2) + "%" : (typeof v === "number" ? fmt(v) : esc(v));
          return stat(k.replace(/_/g, " "), val, d);
        }).join("") + "</div>" +
        '<div class="p3-toolbar">' +
        (Object.keys(pc).length ? '<div class="seg" id="flClPillar"><button data-p="all"' + (S.clusters.pillar === "all" ? ' class="active"' : "") + ">all</button>" +
          Object.keys(pc).sort().map(function (p) {
            return '<button data-p="' + esc(p) + '"' + (S.clusters.pillar === p ? ' class="active"' : "") + ">" + esc(p.replace(/^pillar_/, "")) + " (" + fmt(pc[p]) + ")</button>";
          }).join("") + "</div>" : "") +
        (Object.keys(kc).length > 1 ? '<select id="flClKind"><option value="all">all kinds</option>' + Object.keys(kc).sort().map(function (k) {
          return '<option value="' + esc(k) + '"' + (S.clusters.kind === k ? " selected" : "") + ">" + esc(k) + " (" + fmt(kc[k]) + ")</option>";
        }).join("") + "</select>" : "") +
        '<input type="search" id="flClQ" placeholder="filter clusters by root, folder, domain…" value="' + esc(S.clusters.q) + '" spellcheck="false"></div>' +
        '<table class="p3-table" id="flClTbl"><thead><tr><th>cluster ' + provTag(d) + '</th><th>pillar / kind</th><th class="num">live → core</th><th>root declaration</th><th>domain &amp; top folders</th></tr></thead><tbody>' +
        (d.rows || []).map(function (r) {
          var cid = r.cluster_id || r.id || "";
          var rep = r.root_decl || r.representative || r.name || "";
          var liveN = r.live_decls != null ? r.live_decls : (r.size || 0);
          var coreN = r.effective_core_decls;
          var pct = r.collapse_pct != null ? " (−" + Number(r.collapse_pct).toFixed(1) + "%)" : "";
          var folders = (r.top_folders_l2 || []).slice(0, 3).map(function (x) {
            if (Array.isArray(x)) return x[0] + (x[1] != null ? " (" + fmt(x[1]) + ")" : "");
            if (x && typeof x === "object") return (x.folder || x.name || "") + (x.decls != null ? " (" + fmt(x.decls) + ")" : "");
            return String(x);
          }).join(" · ");
          var cf = r.compute_flags;
          var flagArr = Array.isArray(cf) ? cf : (cf && typeof cf === "object" ? Object.keys(cf).filter(function (k) { return cf[k]; }).map(function (k) { return k + ":" + cf[k]; }) : []);
          var flags = flagArr.map(function (f) { return '<span class="kbadge warn">' + esc(f) + "</span>"; }).join(" ");
          return "<tr><td><code>" + esc(cid) + "</code>" + (r.title_hint ? '<div class="dim sm">' + esc(r.title_hint) + "</div>" : "") +
            '</td><td class="sm"><b>' + esc(r.pillar || "") + '</b><div class="dim">' + esc(r.kind || "") + '</div></td>' +
            '<td class="num">' + fmt(liveN) + (coreN != null ? '<div class="dim sm">core ' + fmt(coreN) + pct + "</div>" : "") +
            (r.live_modules != null ? '<div class="dim sm">' + fmt(r.live_modules) + " mods</div>" : "") +
            '</td><td><a href="#" class="sl-pick" data-decl="' + esc(rep) + '">' + esc(rep) + "</a>" +
            (r.idom_name ? '<div class="dim sm">idom: ' + esc(shortName(r.idom_name)) + "</div>" : "") +
            '</td><td class="sm">' + (r.tier1_top_domain ? '<span class="kbadge def">' + esc(r.tier1_top_domain) + "</span> " : "") + flags +
            (folders ? '<div class="dim sm">' + esc(folders) + "</div>" : "") + "</td></tr>";
        }).join("") + "</tbody></table>" + ((d.rows || []).length ? "" : '<div class="empty-state">No clusters match.</div>');
      body().innerHTML = html;
      $$("#flClPillar button").forEach(function (b) { b.addEventListener("click", function () { S.clusters.pillar = b.dataset.p; S.clusters.offset = 0; renderFlirtClusters(); }); });
      if ($("#flClKind")) $("#flClKind").addEventListener("change", function () { S.clusters.kind = this.value; S.clusters.offset = 0; renderFlirtClusters(); });
      var cq = $("#flClQ");
      if (cq) {
        var t = null;
        cq.addEventListener("input", function () {
          var v = cq.value; clearTimeout(t);
          t = setTimeout(function () { S.clusters.q = v; S.clusters.offset = 0; renderFlirtClusters(); }, 250);
        });
      }
      $$(".sl-pick", body()).forEach(function (el) {
        el.addEventListener("click", function (ev) { ev.preventDefault(); S.slice.name = el.dataset.decl; H.open("kernel", "slice"); });
      });
      return d;
    });
  }

  // ------------------------------------------------------------------ self-test (called from phase3.js selfTest)
  var FORBIDDEN = /RH is proved|RH is proven|proves RH\b|RH has been proved|Riemann Hypothesis is proved|Riemann Hypothesis is proven|proof of RH is valid/i;

  function selfTest(assert) {
    function checkText(label) {
      assert(!$(".p3-absent.err", body()), "P4 " + label + ": no runtime render error");
      var txt = body().textContent || "";
      assert(!/\[object Object\]/.test(txt), "P4 " + label + ": no unformatted [object Object] in rendered UI");
      assert(!FORBIDDEN.test(txt), "P4 " + label + ": no 'RH is proved'-style wording");
      var stats = $$(".p3-stat", body());
      assert(stats.every(function (s) { return !!$(".ptag-L, .fx-tag", s); }), "P4 " + label + ": every stat carries [L]/FIXTURE (" + stats.length + ")");
    }
    return refreshStatus()
      .then(function (stt) {
        assert(stt && stt.decomp && stt.compute_atlas && stt.trim && stt.flirt_clusters && stt.kernel_slice, "P4 status reports decomp, compute_atlas, trim, flirt_clusters, kernel_slice");
        assert(!!$('#p3Seg button[data-p3="blueprint"]'), "P4 toolbar has Blueprint button");
      })
      // 1. Blueprint Proof Map (dynamic discovery + pinned GitHub links + large-doc pagination)
      .then(function () { return H.open("blueprint", "map"); })
      .then(function () {
        assert($$(".bp-node", body()).length === 7, "P4 blueprint map renders 7 architecture boxes (Main, Spine, Diamond, 4 Pillars)");
        var cards = $$("#bpCards .bp-card", body());
        assert(cards.length >= 6, "P6 blueprint dynamically discovers core + deep-dive decomp docs (" + cards.length + ")");
        var ghLinks = $$("a.gh-link", body());
        assert(ghLinks.length > 0 && ghLinks.every(function (a) { return a.href.indexOf(GH_BLOB) === 0; }), "P6 blueprint anchors link to pinned 40e56bab upstream commit (" + ghLinks.length + ")");
        checkText("blueprint map");
        var catBtn = $('#bpCards .bp-card[data-doc="published_catalogue"]', body());
        if (catBtn) {
          S.decompKey = "published_catalogue";
          S.decompOffset = 0;
          return renderBlueprintMap().then(function () {
            var rows = $$("#bpNodeTbl tbody tr", body());
            assert(rows.length > 0 && rows.length <= DECOMP_PAGE, "P6 large published_catalogue paginates smoothly (<= " + DECOMP_PAGE + " rows, got " + rows.length + ")");
            assert(!!$("#bpNodePager", body()), "P6 large published_catalogue renders pagination controls");
            checkText("blueprint published_catalogue");
            S.decompKey = "spine_map";
            S.decompOffset = 0;
          });
        }
      })
      // 2. TCB Audit tab
      .then(function () { return H.open("blueprint", "tcb"); })
      .then(function () {
        assert(!!$(".p3-absent, .p3-src", body()), "P4 TCB audit tab renders either live decomp or explicit 'Not built yet'");
        checkText("blueprint tcb");
      })
      // 3. Compute & Dead Code tab
      .then(function () { return H.open("blueprint", "compute"); })
      .then(function () {
        assert(!!$(".p3-absent, .p3-src", body()), "P4 compute & dead-code tab renders either live atlas or explicit 'Not built yet'");
        checkText("blueprint compute");
      })
      // 4. Bloat Waterfall (Virtual Proof Stripper / Trim) tab
      .then(function () { return H.open("blueprint", "trim"); })
      .then(function (res) {
        assert(!!$(".p3-absent:not(.err), .p3-src", body()), "P6 Bloat Waterfall tab renders either live trim report or explicit 'Not built yet'");
        if (res && res.state === "ready") {
          assert($$("#trimWfTbl tbody tr", body()).length === 6, "P6 Bloat Waterfall renders baseline + 5 disjoint peel stages");
          assert($$("#trimMechTbl tbody tr", body()).length === 7, "P6 Bloat Waterfall renders all 7 bloat mechanisms");
          var ghLinks = $$("a.gh-link", body());
          assert(ghLinks.length > 0 && ghLinks.every(function (a) { return a.href.indexOf(GH_BLOB) === 0; }), "P6 Bloat Waterfall anchors point to pinned 40e56bab commit (" + ghLinks.length + ")");
        }
        checkText("blueprint trim");
      })
      // 5. Kernel Cone Slicer
      .then(function () { S.slice.name = ""; S.slice.depth = 2; S.slice.edge_kind = "all"; return H.open("kernel", "slice"); })
      .then(function (d) {
        checkText("kernel slice default");
        if (!d || d.state === "absent") {
          assert(!!$(".p3-absent", body()), "P4 kernel slice: absent kernel shows 'Not built yet'");
          return;
        }
        assert(d.found && (d.nodes || []).length > 0, "P4 kernel slice: default target returns live cone nodes");
        assert(!!$(".sl-svg-wrap svg", body()), "P4 kernel slice: renders interactive SVG cone diagram");
        S.slice.name = "No.Such.Decl.__p4selftest";
        return renderKernelSlice().then(function (miss) {
          assert(miss.found === false && /Declaration not found/.test(body().textContent), "P4 kernel slice: unknown decl handled gracefully");
          S.slice.name = "allChi"; S.slice.edge_kind = "type";
          return renderKernelSlice();
        }).then(function (t) {
          if (t.state === "ready") {
            assert(t.found && t.target.name === "allChi" && (t.path_to_root || []).length >= 2, "P4 kernel slice: real allChi shows shortest path from root");
            assert((t.edges || []).every(function (e) { return e.dep === "type" || e.dep === "type+value"; }), "P4 kernel slice: edge_kind=type filters out value-only edges");
          }
          S.slice.edge_kind = "all";
        });
      })
      // 5. FLIRT Clusters tab
      .then(function () { return H.open("flirt", "clusters"); })
      .then(function () {
        assert(!!$(".p3-absent:not(.err), .p3-src", body()), "P4 FLIRT clusters tab renders either live clusters or explicit 'Not built yet'");
        if ($(".p3-src", body())) {
          assert($$("#flClTbl tbody tr").length > 0, "P4 FLIRT clusters tab renders live cluster rows");
        }
        checkText("flirt clusters");
      });
  }

  function init(helpers) {
    H = helpers;
    if (window.location.protocol === "file:") return Promise.resolve();
    return refreshStatus();
  }

  return {
    init: init,
    refreshStatus: refreshStatus,
    renderBlueprintMap: renderBlueprintMap,
    renderTcbAudit: renderTcbAudit,
    renderComputeAtlas: renderComputeAtlas,
    renderTrimWaterfall: renderTrimWaterfall,
    renderKernelSlice: renderKernelSlice,
    renderFlirtClusters: renderFlirtClusters,
    selfTest: selfTest,
    state: S
  };
})();
