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
    hygiene: { decl: "allChi", cone_depth: 0, only: "all" },
    portability: { island: "" },
    clusters: { q: "", kind: "all", pillar: "all", offset: 0 },
    atlas: { status: "all", severity: "all", pillar: "all", q: "", offset: 0 },
    bundles: { only: "all", sort: "score", q: "", offset: 0 },
    compute: { q: "", bucket: "", offset: 0 },
    circuit: {
      open: false,
      mode: "macro",
      target: "",
      theme: "dark",
      max_nodes: 0,
      exact_case: false,
      filter: "",
      presets: [],
      history: [],
      lastRes: null,
      selectedNode: null,
      hoveredNode: null,
      scale: 1,
      tx: 16,
      ty: 16,
      inSelfTest: false,
      stageWired: false
    }
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
      if (stt && stt.project) {
        var proj = stt.project;
        if (proj.pinned_commit && proj.upstream_url_template) {
          var tmpl = String(proj.upstream_url_template);
          if (tmpl.indexOf("https://github.com/") === 0 && tmpl.indexOf("/blob/{commit}/") > 0) {
            GH_COMMIT = String(proj.pinned_commit);
            GH_BLOB = tmpl.split("/blob/{commit}/")[0] + "/blob/" + GH_COMMIT + "/";
          }
        }
      }
      var btn = $('#p3Seg button[data-p3="blueprint"]');
      if (btn) {
        var ready = (stt.decomp_ready || 0) > 0 || (stt.compute_atlas && stt.compute_atlas.state === "ready") || (stt.trim && stt.trim.state === "ready") || (stt.bundles && stt.bundles.state === "ready") || (stt.portability && stt.portability.state === "ready");
        btn.dataset.state = ready ? "ready" : "absent";
        btn.title = "Proof Blueprint / Decompiler — " + (stt.decomp_ready || 0) + "/" + (stt.decomp_total || 6) + " decomp docs ready";
      }
      var cBtn = $("#circuitTabBtn");
      if (cBtn && stt && stt.circuit) {
        cBtn.dataset.state = stt.circuit.state === "ready" ? "ready" : "absent";
        cBtn.title = "Interactive 3-level Proof Circuit visualizer — " + stt.circuit.state;
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
      '<button class="btn sm bp-circuit-go" data-decl="' + esc(n.id) + '" data-cmode="' + (n.kind === "inductive" ? "bundle" : "theorem") + '">Proof Circuit</button>' +
      '<button class="btn sm bp-hyg-go" data-decl="' + esc(n.id) + '">Check Hygiene</button>' +
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
      b.addEventListener("click", function () { closeCircuit(); S.slice.name = b.dataset.decl; H.open("kernel", "slice"); });
    });
    $$(".bp-circuit-go", root).forEach(function (b) {
      b.addEventListener("click", function () {
        openCircuit({ mode: b.dataset.cmode || "theorem", target: b.dataset.decl, exact_case: false });
      });
    });
    $$(".bp-hyg-go", root).forEach(function (b) {
      b.addEventListener("click", function () { closeCircuit(); S.hygiene.decl = b.dataset.decl; S.hygiene.cone_depth = 0; H.open("kernel", "hygiene"); });
    });
    $$(".bp-dom-go", root).forEach(function (b) {
      b.addEventListener("click", function () { closeCircuit(); H.openDom(b.dataset.decl); });
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

  // ------------------------------------------------------------------ UNREAD BUNDLES (5,497-STRUCTURE AUDIT)
  function renderBundles() {
    return get("/api/bundles", {
      only: S.bundles.only,
      sort: S.bundles.sort,
      q: S.bundles.q,
      limit: 50,
      offset: S.bundles.offset
    }).then(function (d) {
      if (d.state === "absent") { body().innerHTML = absentPanel(d, "Unread Bundles (5,497-structure unread-field census)"); return d; }
      var sm = d.summary || {};
      var pp = sm.prop_partition || {};
      var tp = sm.type_partition || {};
      var pins = d.pins || {};
      var detail = (pins.source_mode || "source+kernel") + (pins.elapsed_seconds != null ? " · " + pins.elapsed_seconds + "s cached" : "");
      var rows = d.rows || [];
      var total = d.total || 0;
      var pagerHtml = total > 50
        ? '<div class="p3-toolbar" id="bundlesPager" style="margin-top:6px">' +
          '<button class="btn sm" id="bunPrev"' + (S.bundles.offset <= 0 ? " disabled" : "") + ">← Prev</button>" +
          '<span class="dim sm">showing ' + fmt(S.bundles.offset + 1) + "–" + fmt(Math.min(total, S.bundles.offset + 50)) + " of " + fmt(total) + "</span>" +
          '<button class="btn sm" id="bunNext"' + (S.bundles.offset + 50 >= total ? " disabled" : "") + ">Next →</button></div>"
        : "";

      var html = srcLine(Object.assign({}, d, { source_detail: detail }), "Exact 1-constructor structure unread-field census (excludes helper theorems like Used.adm, separates casesOn/recOn eliminators, flags 0-field Type* placeholders & abbrev := True slots)") +
        '<div class="p3-stats">' +
        stat("live 1-ctor structures", fmt(sm.total_live_1ctor_project_inductives) + '<div class="dim sm">: Prop ' + fmt(pp.total) + " · : Type* " + fmt(tp.total) + "</div>", d, "wide") +
        stat("unread (no casesOn/recOn)", fmt((pp.partial_nocases || 0) + (pp.zero_proj_nocases || 0) + (tp.partial_nocases || 0) + (tp.zero_proj_nocases || 0)) +
          '<div class="dim sm">0-proj: ' + fmt((pp.zero_proj_nocases || 0) + (tp.zero_proj_nocases || 0)) + " · eliminated (casesOn): " + fmt(sm.eliminated_cases_on_count) + "</div>", d, "wide") +
        stat("0-field Type* placeholders", fmt(sm.empty_placeholders_count) + '<div class="dim sm">LPTiedPlaceholder · NTiedGPlaceholder</div>', d, "wide") +
        stat("abbrev/def := True slots", fmt(sm.true_abbrev_slots_count) + '<div class="dim sm">literal : True fields: ' + fmt(sm.literal_true_field_hits_count) + "</div>", d, "wide") +
        "</div>" +
        '<div class="p3-toolbar">' +
        '<div class="seg" id="bunOnlySeg">' + [["all", "all unread + placeholders"], ["prop", ": Prop"], ["type", ": Type*"], ["placeholder", "0-field placeholders"]].map(function (v) {
          return '<button data-only="' + v[0] + '"' + (S.bundles.only === v[0] ? ' class="active"' : "") + ">" + esc(v[1]) + "</button>";
        }).join("") + "</div>" +
        '<select id="bunSort">' + [["score", "sort: weighted score"], ["dom", "sort: max caller dom"], ["ratio", "sort: unread ratio"], ["unread", "sort: unread fields"], ["cone", "sort: cone score"]].map(function (v) {
          return '<option value="' + v[0] + '"' + (S.bundles.sort === v[0] ? " selected" : "") + ">" + esc(v[1]) + "</option>";
        }).join("") + "</select>" +
        '<input type="search" id="bunQ" placeholder="filter structure, module, unread field, top caller…" value="' + esc(S.bundles.q) + '" spellcheck="false">' +
        "</div>" +
        '<h4 class="p3-h">Unread Structure Bundles ' + provTag(d) + ' <span class="dim">(' + fmt(total) + " matching)</span></h4>" +
        '<table class="p3-table" id="bundlesTbl"><thead><tr><th>structure &amp; source (40e56bab)</th><th>kind</th><th class="num">proj / total</th><th class="num">unread</th><th class="num">fan-in / max dom</th><th class="num">score</th><th>unread fields &amp; excluded helpers</th></tr></thead><tbody>' +
        rows.map(function (r) {
          var unr = r.unread_field_names || [];
          var excl = r.helper_subdecls_excluded || [];
          var ratioPct = r.total_fields ? (100 * (r.unread_ratio || 0)).toFixed(1) + "%" : "—";
          return "<tr><td>" +
            '<a href="#" class="sl-pick" data-decl="' + esc(r.name) + '">' + esc(r.name) + "</a>" +
            (r.anchor ? '<div class="dim sm">' + ghAnchorLink(r.anchor) + "</div>" : (r.module ? '<div class="dim sm">' + esc(r.module) + "</div>" : "")) +
            (r.top_caller ? '<div class="dim sm">top caller: <code>' + esc(shortName(r.top_caller)) + "</code></div>" : "") +
            '</td><td class="sm"><span class="kbadge">' + esc(r.universe_kind || "") + "</span>" +
            (r.is_placeholder ? ' <span class="st-badge placeholder">0-field</span>' : "") +
            '<div class="dim">' + esc(r.source_kind || "") + "</div>" +
            '</td><td class="num">' + fmt(r.projected_fields) + " / " + fmt(r.total_fields) +
            '</td><td class="num"><b class="warn">' + fmt(r.unread_fields) + '</b><div class="dim sm">' + esc(ratioPct) + "</div>" +
            '</td><td class="num">' + fmt(r.fan_in) + '<div class="dim sm">dom ' + fmt(r.max_caller_dom_sub) + "</div>" +
            '</td><td class="num"><b>' + fmt(Math.round(r.weighted_score || 0)) + "</b>" +
            '</td><td class="sm">' +
            (unr.length ? '<div><span class="dim">unread:</span> ' + unr.slice(0, 8).map(function (f) { return '<span class="ev-tok">' + esc(f) + "</span>"; }).join("") + (unr.length > 8 ? ' <span class="dim">+' + fmt(unr.length - 8) + "</span>" : "") + "</div>" : "") +
            (excl.length ? '<div class="dim sm" style="margin-top:3px">helpers excl: ' + excl.slice(0, 5).map(esc).join(", ") + (excl.length > 5 ? "…" : "") + "</div>" : "") +
            "</td></tr>";
        }).join("") + "</tbody></table>" +
        (rows.length ? "" : '<div class="empty-state">No bundles match this filter.</div>') +
        pagerHtml;

      var phs = d.placeholders || [];
      var tslots = d.true_slots || [];
      html += '<div class="p3-cols"><div>' +
        '<h4 class="p3-h">Empty 0-Field Placeholders ' + provTag(d) + ' <span class="dim">(' + fmt(phs.length) + ")</span></h4>" +
        '<table class="p3-table"><thead><tr><th>structure (40e56bab)</th><th>kind</th><th class="num">fan-in</th><th class="num">max dom</th></tr></thead><tbody>' +
        phs.map(function (p) {
          return "<tr><td><a href=\"#\" class=\"sl-pick\" data-decl=\"" + esc(p.name) + "\">" + esc(p.name) + "</a>" +
            (p.anchor ? '<div class="dim sm">' + ghAnchorLink(p.anchor) + "</div>" : "") +
            '</td><td class="sm"><span class="st-badge placeholder">' + esc(p.universe_kind || "") + "</span></td>" +
            '<td class="num">' + fmt(p.fan_in) + '</td><td class="num">' + fmt(p.max_caller_dom_sub) + "</td></tr>";
        }).join("") + "</tbody></table>" +
        "</div><div>" +
        '<h4 class="p3-h"><code>abbrev/def := True</code> Slots ' + provTag(d) + ' <span class="dim">(' + fmt(tslots.length) + ")</span></h4>" +
        '<table class="p3-table"><thead><tr><th>declaration (40e56bab)</th><th class="num">fan-in</th><th>referenced by</th></tr></thead><tbody>' +
        tslots.map(function (ts) {
          var refs = (ts.referenced_by_structures || []).slice(0, 3).map(shortName).join(", ");
          return "<tr><td><a href=\"#\" class=\"sl-pick\" data-decl=\"" + esc(ts.name) + "\">" + esc(ts.name) + "</a>" +
            (ts.anchor ? '<div class="dim sm">' + ghAnchorLink(ts.anchor) + "</div>" : "") +
            '</td><td class="num">' + fmt(ts.fan_in) + '</td><td class="dim sm">' + esc(refs || "—") + "</td></tr>";
        }).join("") + "</tbody></table>" +
        "</div></div>";

      body().innerHTML = html;
      $$("#bunOnlySeg button", body()).forEach(function (b) {
        b.addEventListener("click", function () { S.bundles.only = b.dataset.only; S.bundles.offset = 0; renderBundles(); });
      });
      $("#bunSort", body()).addEventListener("change", function () { S.bundles.sort = this.value; S.bundles.offset = 0; renderBundles(); });
      var bPrev = $("#bunPrev", body()), bNext = $("#bunNext", body());
      if (bPrev) bPrev.addEventListener("click", function () { S.bundles.offset = Math.max(0, S.bundles.offset - 50); renderBundles(); });
      if (bNext) bNext.addEventListener("click", function () { S.bundles.offset = S.bundles.offset + 50; renderBundles(); });
      var bq = $("#bunQ", body());
      if (bq) {
        var t = null;
        bq.addEventListener("input", function () {
          var v = bq.value; clearTimeout(t);
          t = setTimeout(function () {
            S.bundles.q = v; S.bundles.offset = 0;
            renderBundles().then(function () { var e = $("#bunQ", body()); if (e) { e.focus(); e.setSelectionRange(v.length, v.length); } });
          }, 220);
        });
      }
      $$(".sl-pick", body()).forEach(function (el) {
        el.addEventListener("click", function (ev) { ev.preventDefault(); S.slice.name = el.dataset.decl; H.open("kernel", "slice"); });
      });
      return d;
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
          '<button class="btn sm" id="slHygBtn" data-decl="' + esc(t.name) + '">Check Hygiene (Live)</button>' +
          '<button class="btn sm bp-hyg-go" data-decl="' + esc(t.name) + '">Full Hygiene Tab</button>' +
          '<button class="btn sm primary bp-ann-go" data-decl="' + esc(t.name) + '">Annotate</button></div>' +
          '<div id="slHygOut"></div>' +
          "</div></div>";
        body().innerHTML = html;
      }

      var slHygBtn = $("#slHygBtn", body());
      if (slHygBtn) {
        slHygBtn.addEventListener("click", function () {
          var out = $("#slHygOut", body());
          if (!out) return;
          out.innerHTML = '<div class="hyg-inline dim">Running live kernel hygiene audit…</div>';
          get("/api/hygiene", { decl: slHygBtn.dataset.decl, cone_depth: 0, only: "all" }).then(function (hr) {
            if (!hr || hr.state === "absent") {
              out.innerHTML = '<div class="hyg-inline dim">Hygiene auditor unavailable (kernel.db absent).</div>';
              return;
            }
            if (!hr.found) {
              out.innerHTML = '<div class="hyg-inline dim">Declaration not found in kernel.db.</div>';
              return;
            }
            var sm = hr.summary || {};
            var bc = sm.by_category || {};
            var d0 = (hr.decls || [])[0] || {};
            var fnds = d0.findings || [];
            out.innerHTML = '<div class="hyg-inline">' +
              '<div>' + H.ptag("L") + ' <b>Live Hygiene</b> (<code>depth=0</code>, ' + esc(String(hr.elapsed_s != null ? hr.elapsed_s : "?")) + 's): ' +
              (fnds.length ? statusBadge("dropped") + " <b>" + fmt(fnds.length) + "</b> finding(s)" : '<span class="st-badge clean">CLEAN (0 findings)</span>') +
              ' · <span class="dim sm">dropped=' + fmt(bc.dropped || 0) + ' · True-slots=' + fmt(bc.true_slot || 0) + ' · tuple-unread=' + fmt(bc.tuple_unread || 0) + '</span></div>' +
              (fnds.length ? fnds.slice(0, 8).map(function (f) {
                return '<div class="hyg-find-row">' + statusBadge(f.category || "dropped") + ' <code>' + esc(f.kind || "") + '</code> ' + esc(f.detail || "") + '</div>';
              }).join("") : (d0.status && d0.status !== "ok" ? '<div class="dim sm" style="margin-top:4px">source status: <code>' + esc(d0.status) + '</code></div>' : "")) +
              "</div>";
          }).catch(function (err) {
            out.innerHTML = '<div class="hyg-inline dim">Hygiene error: ' + esc(err && err.message || err) + "</div>";
          });
        });
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

  // ------------------------------------------------------------------ FLIRT: 141-CLUSTER BLINDED ATLAS
  function renderFlirtAtlas() {
    return get("/api/flirt/atlas", {
      status: S.atlas.status,
      severity: S.atlas.severity,
      pillar: S.atlas.pillar,
      q: S.atlas.q,
      limit: 150,
      offset: S.atlas.offset
    }).then(function (d) {
      if (d.state === "absent") { body().innerHTML = absentPanel(d, "141-Cluster Blinded FLIRT Atlas (cluster_labels_141.json)"); return d; }
      var tot = d.totals || {};
      var sc = d.status_counts || {};
      var svc = d.severity_counts || {};
      var pc = d.pillar_counts || {};
      var rows = d.rows || [];
      var detail = d.mirror_commit ? "mirror@" + String(d.mirror_commit).slice(0, 8) : "";

      var html = srcLine(Object.assign({}, d, { source_detail: detail }), "141-Cluster Blinded FLIRT Atlas — [L] cluster counts & source paths vs name-blinded [M] AI-draft labels (zero proof bodies read)") +
        '<div class="note-blk M p3-note"><p>' + H.ptag("M") + ' <span class="ai-chip">AI DRAFT</span> <b>Name-blinded labels are heuristic machine drafts:</b> generated solely from blinded declaration headers, Mathlib opens, and 1–2-hop Mathlib primitives with all project identifiers stripped. Inner proof bodies remain <b>OPAQUE</b>. Structural counts, directory paths, and 40e56bab anchors are ' + H.ptag("L") + " extracted.</p></div>" +
        '<div class="p3-stats">' +
        stat("coarse clusters", fmt(tot.clusters_count) + '<div class="dim sm">' + fmt(tot.live_decls) + " → " + fmt(tot.effective_core_decls) + " core (−" + Number(tot.collapse_pct || 0).toFixed(1) + "%)</div>", d, "wide") +
        stat("cross_domain_misplaced", fmt(sc.cross_domain_misplaced || 0) + '<div class="dim sm">' + fmt(svc.high || 0) + " high · " + fmt(svc.moderate || 0) + " moderate severity</div>", d) +
        stat("partial_drift", fmt(sc.partial_drift || 0) + '<div class="dim sm">' + fmt(svc.low || 0) + " low severity</div>", d) +
        stat("aligned", fmt(sc.aligned || 0) + '<div class="dim sm">matches directory domain</div>', d) +
        "</div>" +
        '<div class="p3-toolbar">' +
        '<div class="seg" id="flAtStSeg">' + [
          ["all", "all (" + fmt(tot.clusters_count || 0) + ")"],
          ["cross_domain_misplaced", "cross_domain_misplaced (" + fmt(sc.cross_domain_misplaced || 0) + ")"],
          ["partial_drift", "partial_drift (" + fmt(sc.partial_drift || 0) + ")"],
          ["aligned", "aligned (" + fmt(sc.aligned || 0) + ")"]
        ].map(function (v) {
          return '<button data-st="' + v[0] + '"' + (S.atlas.status === v[0] ? ' class="active"' : "") + ">" + esc(v[1]) + "</button>";
        }).join("") + "</div>" +
        '<select id="flAtSev">' + ["all", "high", "moderate", "low", "none"].map(function (sv) {
          return '<option value="' + sv + '"' + (S.atlas.severity === sv ? " selected" : "") + ">severity: " + sv + (sv !== "all" ? " (" + fmt(svc[sv] || 0) + ")" : "") + "</option>";
        }).join("") + "</select>" +
        '<select id="flAtPillar"><option value="all">pillar: all</option>' + Object.keys(pc).sort().map(function (p) {
          return '<option value="' + esc(p) + '"' + (S.atlas.pillar === p ? " selected" : "") + ">" + esc(p) + " (" + fmt(pc[p]) + ")</option>";
        }).join("") + "</select>" +
        '<input type="search" id="flAtQ" placeholder="filter ID, blinded label, domain, folder, root…" value="' + esc(S.atlas.q) + '" spellcheck="false">' +
        "</div>" +
        '<h4 class="p3-h">Blinded Cluster Labels vs Directory Mismatch Audit ' + provTag(d) + ' <span class="dim">(' + fmt(d.total) + " matching)</span></h4>" +
        '<table class="p3-table" id="flAtlasTbl"><thead><tr><th>cluster &amp; size ' + provTag(d) + '</th><th>blinded label ' + H.ptag("M") + '</th><th>source directory vs mismatch audit</th><th>representative anchors (40e56bab)</th></tr></thead><tbody>' +
        rows.map(function (r) {
          var ct = r.counts || {};
          var bl = r.blinded_label || {};
          var ma = r.mismatch_audit || {};
          var reps = (r.top3_rep_decls || []).slice(0, 3);
          var toks = (bl.evidence_tokens || []).slice(0, 6);
          var expDom = (ma.folder_expected_domains || []).join(", ");
          var repLinks = reps.map(function (rep) {
            var anchor = rep.module ? ("src/" + String(rep.module).replace(/\./g, "/") + ".lean" + (rep.line ? ":" + rep.line : "")) : "";
            var lbl = shortName(rep.name || rep.module || "") + (rep.line ? ":" + rep.line : "");
            return anchor ? ghAnchorLink(anchor, lbl) : "<code>" + esc(lbl) + "</code>";
          }).join("<br>");
          return "<tr><td><code>" + esc(r.cluster_id || "") + '</code> <span class="dim sm">' + esc(String(r.pillar || "").replace(/^pillar_/, "")) + "</span>" +
            '<div class="sm"><b>' + fmt(ct.live_decls) + "</b> → " + fmt(ct.effective_core_decls) + ' <span class="dim">(−' + Number(ct.collapse_pct || 0).toFixed(1) + "%)</span></div>" +
            '<div class="dim sm">' + fmt(ct.live_modules) + " mods · " + fmt(ct.total_lines_wc) + "L</div>" +
            '</td><td><div>' + H.ptag("M") + ' <span class="ai-chip">AI DRAFT</span> <b>' + esc(String(bl.label || "").replace(/^\[M\]\s*/, "")) + "</b></div>" +
            '<div class="sm" style="margin-top:3px"><span class="kbadge def">' + esc(bl.primary_domain || "") + "</span>" +
            (bl.secondary_domain ? ' <span class="kbadge">' + esc(bl.secondary_domain) + "</span>" : "") +
            (bl.confidence != null ? ' <span class="dim">conf ' + Number(bl.confidence).toFixed(2) + "</span>" : "") + "</div>" +
            (toks.length ? "<div>" + toks.map(function (tk) { return '<span class="ev-tok">' + esc(tk) + "</span>"; }).join("") + "</div>" : "") +
            (bl.uncertainty_note ? '<div class="dim sm" style="margin-top:3px">' + esc(bl.uncertainty_note) + "</div>" : "") +
            "</td><td><div>" + statusBadge(ma.status || "unknown") + " " + statusBadge(ma.severity || "none") + "</div>" +
            '<div class="sm" style="margin-top:4px"><code>' + esc(ma.folder_l2 || "") + "</code>" +
            (expDom ? ' <span class="dim">(exp: ' + esc(expDom) + ")</span>" : "") + "</div>" +
            (ma.misfile_module_pct != null ? '<div class="dim sm">misfile rate: ' + Number(ma.misfile_module_pct).toFixed(1) + "%" + (ma.ns_bulk_remapped ? " · bulk-remapped" : "") + "</div>" : "") +
            (ma.reason ? '<div class="dim sm" style="margin-top:2px">' + esc(ma.reason) + "</div>" : "") +
            '</td><td class="sm"><div><a href="#" class="sl-pick" data-decl="' + esc(r.root_decl || "") + '" title="' + esc(r.root_decl || "") + '">root: ' + esc(shortName(r.root_decl || "")) + "</a></div>" +
            (repLinks ? '<div style="margin-top:4px">' + repLinks + "</div>" : "") +
            "</td></tr>";
        }).join("") + "</tbody></table>" +
        (rows.length ? "" : '<div class="empty-state">No clusters match this filter.</div>');

      body().innerHTML = html;
      $$("#flAtStSeg button", body()).forEach(function (b) {
        b.addEventListener("click", function () { S.atlas.status = b.dataset.st; S.atlas.offset = 0; renderFlirtAtlas(); });
      });
      $("#flAtSev", body()).addEventListener("change", function () { S.atlas.severity = this.value; S.atlas.offset = 0; renderFlirtAtlas(); });
      $("#flAtPillar", body()).addEventListener("change", function () { S.atlas.pillar = this.value; S.atlas.offset = 0; renderFlirtAtlas(); });
      var aq = $("#flAtQ", body());
      if (aq) {
        var t = null;
        aq.addEventListener("input", function () {
          var v = aq.value; clearTimeout(t);
          t = setTimeout(function () {
            S.atlas.q = v; S.atlas.offset = 0;
            renderFlirtAtlas().then(function () { var e = $("#flAtQ", body()); if (e) { e.focus(); e.setSelectionRange(v.length, v.length); } });
          }, 220);
        });
      }
      $$(".sl-pick", body()).forEach(function (el) {
        el.addEventListener("click", function (ev) { ev.preventDefault(); S.slice.name = el.dataset.decl; H.open("kernel", "slice"); });
      });
      return d;
    });
  }

  // ------------------------------------------------------------------ PORTABILITY GEMS
  function renderPortability() {
    var params = S.portability.island ? { island: S.portability.island } : {};
    return get("/api/portability", params).then(function (d) {
      if (d.state === "absent") { body().innerHTML = absentPanel(d, "Mathlib-Portability Gems (outputs/portability_gems.json)"); return d; }
      var sm = d.summary || {};
      var allIslands = d.islands_all || d.islands || [];
      var targets = d.targets || [];
      var ov = d.overlap || {};
      var mat = ov.project_decls_matrix || [];
      var jmat = ov.project_jaccard_matrix || [];
      var mNames = ov.short_names || ov.target_names || [];
      var mFull = ov.target_names || mNames;
      var mIsl = ov.island_ids || [];

      var pins = d.pins || {};
      var detail = [pins.source_mode, pins.dom_tree ? "dom=" + pins.dom_tree : ""].filter(Boolean).join(" · ");
      var html = srcLine(Object.assign({}, d, { source_detail: detail }),
        "Mathlib-Portability Islands — standalone spec-only dependency cones, external Mathlib boundaries, and pairwise project-overlap matrix") +
        '<div class="p3-stats">' +
        stat("pairwise-disjoint islands", fmt(sm.pairwise_disjoint_islands) + " / " + fmt(sm.islands_count) + '<div class="dim sm">0 shared project decls across islands</div>', d) +
        stat("standalone-ready gems", fmt(sm.standalone_ready_count) + " / " + fmt(sm.targets_count) + '<div class="dim sm">' + fmt(sm.scoped_count) + " scoped</div>", d) +
        stat("union project cone", fmt(sm.union_project_decls) + '<div class="dim sm">' + fmt(sm.union_module_count) + " modules</div>", d) +
        stat("union Mathlib boundary", fmt(sm.union_external_decls) + '<div class="dim sm">' + fmt(sm.union_total_decls) + " total union decls</div>", d) +
        "</div>";

      if (allIslands.length) {
        html += '<div class="p3-toolbar" style="margin-bottom:8px">' +
          '<span class="bp-section-lbl" style="margin:0">Pairwise-Disjoint Mathlib-Portable Islands (' + fmt(allIslands.length) + ')</span>' +
          (S.portability.island ? '<button class="btn sm" id="portClearIsl">Show all islands ✕</button>' : '<span class="dim sm">Click an island card to filter via <code>?island=...</code></span>') +
          "</div>" +
          '<div class="port-grid" id="portIslands">' +
          allIslands.map(function (isl) {
            var isAct = S.portability.island && (S.portability.island.toLowerCase() === String(isl.slug || "").toLowerCase() || S.portability.island.toLowerCase() === String(isl.id || "").toLowerCase());
            var prefs = (isl.top_mathlib_prefixes || []).slice(0, 4).map(function (p) {
              return '<span class="ev-tok">' + esc(p.prefix) + " (" + fmt(p.distinct_decls) + ")</span>";
            }).join("");
            return '<button class="port-card' + (isAct ? " active" : "") + '" data-isl="' + esc(isl.slug || isl.id) + '">' +
              '<div class="ttl"><span>Island ' + fmt(isl.index) + " · <code>" + esc(isl.slug || isl.lead_short) + "</code></span>" +
              '<span class="st-badge ' + (isl.pairwise_disjoint ? "clean" : "scoped") + '">' + (isl.pairwise_disjoint ? "0 overlap" : "shared") + "</span></div>" +
              '<div class="sub">' + esc((isl.member_shorts || []).join(" + ")) + "</div>" +
              '<div class="meta">' +
              (isl.tiers || []).map(function (tr) { return statusBadge(tr); }).join(" ") +
              ' <span><b>' + fmt(isl.max_project_decls) + '</b> proj</span>' +
              ' · <span>spec <b>' + fmt(isl.min_spec_cone_project_decls) + (isl.max_spec_cone_project_decls !== isl.min_spec_cone_project_decls ? "–" + fmt(isl.max_spec_cone_project_decls) : "") + '</b></span>' +
              ' · <span>ext <b>' + fmt(isl.max_direct_external_decls) + "</b></span></div>" +
              '<div>' + prefs + "</div></button>";
          }).join("") + "</div>";
      }

      if (d.found === false) {
        html += '<div class="p3-absent"><h3>Island not found</h3><p>No portability island matched <code>' + esc(d.queried_island || S.portability.island) + "</code>.</p></div>";
      } else {
        html += '<h4 class="p3-h">Portable Targets &amp; Mathlib Boundaries ' + provTag(d) + ' <span class="dim">(' + fmt(targets.length) + ")</span></h4>" +
          '<table class="p3-table" id="portTargetsTbl"><thead><tr><th>theorem &amp; module</th><th>tier &amp; soundness</th><th class="num">project / spec cone</th><th>top Mathlib boundary prefixes</th><th>actions</th></tr></thead><tbody>' +
          targets.map(function (t) {
            var cone = t.cone || {};
            var bnd = t.boundary || {};
            var cont = t.contamination || {};
            var mod = String(t.module || "");
            var modAnchor = mod ? ("src/" + mod.replace(/\./g, "/") + ".lean") : "";
            var prefs = (bnd.top_external_prefixes || []).slice(0, 6).map(function (p) {
              return '<span class="ev-tok" title="' + esc(fmt(p.call_edges) + " call edges, " + fmt(p.type_decls) + " type decls") + '">' + esc(p.prefix) + " (" + fmt(p.distinct_decls) + ")</span>";
            }).join("");
            var reasons = (cont.reasons || []).slice(0, 2).join("; ");
            var mega = (cont.mega_records || []).length;
            return '<tr><td><div><code>' + esc(t.name || "") + "</code></div>" +
              '<div class="dim sm">' + (modAnchor ? ghAnchorLink(modAnchor, mod) : esc(mod)) +
              (t.island_slug ? ' · <span class="kbadge">' + esc(t.island_slug) + "</span>" : "") + "</div></td>" +
              '<td><div>' + statusBadge(cont.tier || "unknown") +
              (cont.has_sorry ? ' <span class="st-badge OPAQUE">sorry</span>' : ' <span class="st-badge clean">0 sorry</span>') +
              (mega ? ' <span class="st-badge scoped">' + fmt(mega) + " mega-rec</span>" : "") + "</div>" +
              '<div class="dim sm" style="margin-top:3px">' + esc(reasons) + "</div></td>" +
              '<td class="num"><b>' + fmt(cone.project_decls) + '</b> proj<div class="dim sm">spec ' + fmt(cone.spec_cone_project_decls) + " proj / " + fmt(cone.spec_cone_total_decls) + ' tot</div>' +
              '<div class="dim sm">dom ' + fmt(cone.dom_subtree_size) + " · " + fmt(cone.module_count) + " mods</div></td>" +
              '<td><div class="dim sm">' + fmt(bnd.direct_external_decls) + " direct ext decls · " + fmt(bnd.distinct_prefixes_total) + " prefixes</div><div>" + prefs + "</div></td>" +
              '<td><div class="p3-toolbar" style="margin:0;gap:4px"><button class="btn sm bp-slice-go" data-decl="' + esc(t.name || "") + '">Slice</button>' +
              '<button class="btn sm bp-hyg-go" data-decl="' + esc(t.name || "") + '">Hygiene</button></div></td></tr>';
          }).join("") + "</tbody></table>";

        if (mat.length && mNames.length === mat.length) {
          html += '<h4 class="p3-h">Pairwise Project-Declaration Overlap Matrix ' + provTag(d) + ' <span class="dim sm">(diagonal = project cone size · off-diagonal = shared project decls &amp; Jaccard · 0 = disjoint)</span></h4>' +
            '<div class="port-mat-wrap"><table class="port-mat" id="portOverlapTbl"><thead><tr><th>target</th>' +
            mNames.map(function (nm, ci) {
              return '<th class="col-h" title="' + esc(mFull[ci] || nm) + '">' + esc(nm.length > 18 ? nm.slice(0, 17) + "…" : nm) + "</th>";
            }).join("") + "</tr></thead><tbody>" +
            mat.map(function (row, ri) {
              return '<tr><th title="' + esc(mFull[ri] || mNames[ri]) + '"><code>' + esc(mNames[ri]) + '</code>' +
                (mIsl[ri] ? ' <span class="dim sm">[' + esc(mIsl[ri].replace("island_", "I")) + "]</span>" : "") + "</th>" +
                row.map(function (val, ci) {
                  var jv = (jmat[ri] && jmat[ri][ci] != null) ? Number(jmat[ri][ci]) : (ri === ci ? 1 : 0);
                  var cls = ri === ci ? "hm-self" : (val === 0 ? "hm-0" : (jv >= 0.7 ? "hm-hi" : (jv >= 0.2 ? "hm-mid" : "hm-lo")));
                  var title = (mFull[ri] || "") + " ∩ " + (mFull[ci] || "") + ": " + fmt(val) + " project decls (Jaccard " + (jv * 100).toFixed(1) + "%)";
                  return '<td class="' + cls + '" title="' + esc(title) + '">' + fmt(val) +
                    (ri !== ci && val > 0 ? '<span class="jacc">' + (jv * 100).toFixed(1) + "%</span>" : "") + "</td>";
                }).join("") + "</tr>";
            }).join("") + "</tbody></table></div>";
        }
      }

      body().innerHTML = html;
      $$("#portIslands .port-card", body()).forEach(function (btn) {
        btn.addEventListener("click", function () {
          var slug = btn.dataset.isl;
          S.portability.island = (S.portability.island === slug) ? "" : slug;
          renderPortability();
        });
      });
      var clr = $("#portClearIsl", body());
      if (clr) clr.addEventListener("click", function () { S.portability.island = ""; renderPortability(); });
      wireInspectorButtons(body());
      return d;
    });
  }

  // ------------------------------------------------------------------ KERNEL: LIVE PROOF HYGIENE
  function getHygienePresets() {
    var proj = S.status && S.status.project;
    if (proj && Array.isArray(proj.headline_roots) && proj.headline_roots.length && !proj.rh_gates) {
      return proj.headline_roots.slice(0, 6).map(function (r) { return [r, shortName(r)]; });
    }
    return [
      ["allChi", "allChi"],
      ["riemannHypothesis", "riemannHypothesis"],
      ["GroundTheory.Arith.SchemeCoh.finiteH_of_isProper", "finiteH_of_isProper"],
      ["FunctorialResolution.EmbeddedResolution.strongResolutionOfSingularitiesCharZero", "strongResolution"],
      ["MainStatements.Hodge.Free.abelianHodgeDeRham'", "abelianHodgeDeRham'"],
      ["PositivityTheory.Lit1.GEN.globalEulerChar_full", "globalEulerChar_full"]
    ];
  }

  function renderKernelHygiene() {
    var presets = getHygienePresets();
    if (!S.hygiene.decl && presets.length) S.hygiene.decl = presets[0][0];
    return get("/api/hygiene", {
      decl: S.hygiene.decl,
      cone_depth: S.hygiene.cone_depth,
      only: S.hygiene.only
    }).then(function (d) {
      if (d.state === "absent") { body().innerHTML = absentPanel(d, "live kernel proof-hygiene auditor"); return d; }
      var sm = d.summary || {};
      var bc = sm.by_category || {};
      var decls = d.decls || [];
      var detail = [d.src_root ? "src=" + d.src_root : "", d.elapsed_s != null ? d.elapsed_s + "s" : "", d.truncated ? "truncated" : ""].filter(Boolean).join(" · ");

      var ctlHtml = srcLine(Object.assign({}, d, { source_detail: detail }),
        "live proof-hygiene auditor (dropped binders / intro _, True dummy slots, unread And-tuple legs; bounded cone_depth ≤ 2)") +
        '<div class="p3-chips" id="hygPresets">' + presets.map(function (p) {
          return '<button class="fchip' + (S.hygiene.decl === p[0] ? " active" : "") + '" data-decl="' + esc(p[0]) + '">' + esc(p[1]) + "</button>";
        }).join("") + "</div>" +
        '<div class="p3-toolbar">' +
        '<input type="search" id="hygDecl" value="' + esc(S.hygiene.decl) + '" placeholder="exact declaration name (Enter)…" spellcheck="false">' +
        '<select id="hygDepth">' + [
          [0, "cone depth 0 (target only)"],
          [1, "cone depth 1 (1-hop project)"],
          [2, "cone depth 2 (2-hop project, max)"]
        ].map(function (v) {
          return '<option value="' + v[0] + '"' + (Number(S.hygiene.cone_depth) === v[0] ? " selected" : "") + ">" + esc(v[1]) + "</option>";
        }).join("") + "</select>" +
        '<select id="hygOnly">' + [
          ["all", "all checks"],
          ["dropped", "dropped binders / intro _"],
          ["true_slot", "True dummy slots"],
          ["tuple_unread", "unread And-tuple legs"]
        ].map(function (v) {
          return '<option value="' + v[0] + '"' + (S.hygiene.only === v[0] ? " selected" : "") + ">" + esc(v[1]) + "</option>";
        }).join("") + "</select>" +
        '<button class="btn sm primary" id="hygGo">Run Hygiene</button></div>';

      if (d.found === false) {
        var sg = (d.suggestions || []).map(function (s) {
          return '<tr><td><a href="#" class="hyg-pick" data-decl="' + esc(s.name) + '">' + esc(s.name) + "</a></td><td><code>" + esc(s.kind) + "</code></td></tr>";
        }).join("");
        body().innerHTML = ctlHtml + '<div class="p3-absent"><h3>Declaration not found</h3><p><code>' + esc(d.queried || S.hygiene.decl) +
          "</code> was not found in <code>kernel.db</code>.</p>" +
          (sg ? '<table class="p3-table"><thead><tr><th>did you mean?</th><th>kind</th></tr></thead><tbody>' + sg + "</tbody></table>" : "") + "</div>";
      } else {
        var html = ctlHtml +
          '<div class="p3-stats">' +
          stat("decls audited", fmt(sm.decls_audited) + '<div class="dim sm">depth ' + fmt(S.hygiene.cone_depth) + (d.truncated ? " (capped)" : "") + "</div>", d) +
          stat("decls with findings", fmt(sm.decls_with_findings) + '<div class="dim sm">' + fmt(sm.total_findings) + " total finding(s)</div>", d) +
          stat("dropped binders", fmt(bc.dropped || 0) + '<div class="dim sm">unused / intro _</div>', d) +
          stat("True dummy slots", fmt(bc.true_slot || 0) + '<div class="dim sm">: True / trivial</div>', d) +
          stat("unread tuple legs", fmt(bc.tuple_unread || 0) + '<div class="dim sm">And / Prod imbalance</div>', d) +
          "</div>" +
          '<h4 class="p3-h">Audited Declarations &amp; Hygiene Findings ' + provTag(d) + ' <span class="dim">(' + fmt(decls.length) + ")</span></h4>" +
          '<table class="p3-table" id="hygTbl"><thead><tr><th class="num">hop</th><th>declaration &amp; anchor</th><th>status</th><th>findings (heuristic source + kernel)</th><th>actions</th></tr></thead><tbody>' +
          decls.map(function (r) {
            var fnds = r.findings || [];
            var findHtml = fnds.length
              ? fnds.map(function (f) {
                return '<div class="hyg-find-row">' + statusBadge(f.category || "dropped") + ' <code>' + esc(f.kind || "") + "</code>" +
                  (f.line_no ? ' <span class="dim sm">L' + fmt(f.line_no) + "</span>" : "") +
                  '<div class="sm">' + esc(f.detail || "") + "</div></div>";
              }).join("")
              : (r.status === "ok" ? '<span class="st-badge clean">CLEAN</span> <span class="dim sm">0 findings</span>' : '<span class="dim sm">' + esc(r.status || "") + "</span>");
            return '<tr><td class="num dim">' + fmt(r.hop) + '</td><td><code>' + esc(r.name || "") + '</code> <span class="dim sm">' + esc(r.kind || "") + "</span>" +
              (r.anchor ? '<div class="dim sm">' + ghAnchorLink(r.anchor) + "</div>" : (r.module ? '<div class="dim sm">' + esc(r.module) + "</div>" : "")) +
              (r.header ? '<div class="bp-hdr" style="margin:4px 0 0;font-size:10.5px">' + esc(r.header) + "</div>" : "") +
              '</td><td>' + statusBadge(r.status === "ok" ? (fnds.length ? "PARTIAL" : "clean") : "OPAQUE") +
              "</td><td>" + findHtml +
              '</td><td><button class="btn sm bp-slice-go" data-decl="' + esc(r.name || "") + '">Slice</button></td></tr>';
          }).join("") + "</tbody></table>";
        body().innerHTML = html;
      }

      var apply = function () {
        S.hygiene.decl = ($("#hygDecl").value || "").trim();
        S.hygiene.cone_depth = Math.max(0, Math.min(2, Number($("#hygDepth").value) || 0));
        S.hygiene.only = $("#hygOnly").value || "all";
        if (S.hygiene.decl) renderKernelHygiene();
      };
      $("#hygGo").addEventListener("click", apply);
      $("#hygDecl").addEventListener("keydown", function (ev) { if (ev.key === "Enter") apply(); });
      ["#hygDepth", "#hygOnly"].forEach(function (sel) { $(sel).addEventListener("change", apply); });
      $$("#hygPresets button").forEach(function (b) {
        b.addEventListener("click", function () { S.hygiene.decl = b.dataset.decl; renderKernelHygiene(); });
      });
      $$(".hyg-pick", body()).forEach(function (el) {
        el.addEventListener("click", function (ev) { ev.preventDefault(); S.hygiene.decl = el.dataset.decl; renderKernelHygiene(); });
      });
      wireInspectorButtons(body());
      return d;
    });
  }

  // ------------------------------------------------------------------ INTERACTIVE 3-LEVEL PROOF CIRCUIT TAB
  function dom(tag, attrs, children) {
    var node = document.createElement(tag);
    if (attrs) {
      Object.keys(attrs).forEach(function (k) {
        var v = attrs[k];
        if (v === null || v === undefined) return;
        if (k === "className") node.className = String(v);
        else if (k === "textContent") node.textContent = String(v);
        else if (k === "style" && typeof v === "object") Object.assign(node.style, v);
        else if (k.indexOf("on") === 0 && typeof v === "function") node.addEventListener(k.slice(2), v);
        else node.setAttribute(k, String(v));
      });
    }
    if (children !== undefined && children !== null) {
      var arr = Array.isArray(children) ? children : [children];
      arr.forEach(function (c) {
        if (c === null || c === undefined || c === false) return;
        node.appendChild(typeof c === "string" || typeof c === "number" ? document.createTextNode(String(c)) : c);
      });
    }
    return node;
  }

  function clearEl(node) {
    if (!node) return;
    while (node.firstChild) node.removeChild(node.firstChild);
  }

  function ghAnchorNode(anchor, label) {
    var raw = String(anchor || "").trim();
    if (!raw) return null;
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
      return dom("span", { className: "mono", textContent: disp });
    }
    var href = GH_BLOB + pathPart + frag;
    if (href.indexOf("https://github.com/") !== 0) {
      return dom("span", { className: "mono", textContent: disp });
    }
    return dom("a", { className: "gh-link", href: href, target: "_blank", rel: "noopener noreferrer", textContent: disp });
  }

  function sanitizeSvgElement(svgEl) {
    if (!svgEl) return;
    var badTags = svgEl.querySelectorAll("script,foreignObject,iframe,object,embed");
    Array.prototype.slice.call(badTags).forEach(function (n) { n.remove(); });
    var all = [svgEl].concat(Array.prototype.slice.call(svgEl.querySelectorAll("*")));
    all.forEach(function (el) {
      Array.prototype.slice.call(el.attributes || []).forEach(function (at) {
        var nm = at.name.toLowerCase();
        var vl = String(at.value || "").trim().toLowerCase();
        if (nm.indexOf("on") === 0) el.removeAttribute(at.name);
        else if ((nm === "href" || nm === "xlink:href") && vl.indexOf("javascript:") === 0) el.removeAttribute(at.name);
      });
    });
  }

  function mountSafeSvg(stageEl, svgText) {
    clearEl(stageEl);
    var parser = new DOMParser();
    var doc = parser.parseFromString(String(svgText || ""), "image/svg+xml");
    if (!doc || doc.querySelector("parsererror") || !doc.documentElement || doc.documentElement.nodeName.toLowerCase() !== "svg") {
      stageEl.appendChild(dom("div", { className: "p3-absent err cir-stage-msg" }, [
        dom("h3", { textContent: "Invalid SVG payload" }),
        dom("p", { textContent: "The circuit SVG response could not be parsed as well-formed XML." })
      ]));
      return null;
    }
    sanitizeSvgElement(doc.documentElement);
    var imported = document.importNode(doc.documentElement, true);
    stageEl.appendChild(imported);
    return imported;
  }

  function circuitApiParams(override) {
    var c = S.circuit;
    var p = {
      mode: (override && override.mode) || c.mode || "macro",
      theme: (override && override.theme) || c.theme || "dark"
    };
    var tgt = (override && override.target !== undefined) ? override.target : c.target;
    if (p.mode !== "macro" && tgt) p.target = tgt;
    var mn = (override && override.max_nodes !== undefined) ? override.max_nodes : c.max_nodes;
    if (mn && Number(mn) >= 2) p.max_nodes = Number(mn);
    var ec = (override && override.exact_case !== undefined) ? override.exact_case : c.exact_case;
    if (ec) p.exact_case = "1";
    if (override && override.format) p.format = override.format;
    if (override && override.download) p.download = "1";
    return p;
  }

  function circuitUrl(override) {
    return "/api/circuit?" + qs(circuitApiParams(override));
  }

  function applyCircuitTransform() {
    var stg = $("#circuitStage");
    if (!stg) return;
    stg.style.transform = "translate(" + S.circuit.tx + "px," + S.circuit.ty + "px) scale(" + S.circuit.scale + ")";
  }

  function fitCircuitStage() {
    var wrap = $("#circuitStageWrap");
    var stg = $("#circuitStage");
    if (!wrap || !stg) return;
    var svg = stg.querySelector("svg");
    if (!svg) return;
    var sw = Number(svg.getAttribute("width")) || (svg.viewBox && svg.viewBox.baseVal && svg.viewBox.baseVal.width) || 1280;
    var sh = Number(svg.getAttribute("height")) || (svg.viewBox && svg.viewBox.baseVal && svg.viewBox.baseVal.height) || 720;
    var cw = wrap.clientWidth || 1000;
    var ch = wrap.clientHeight || 620;
    S.circuit.scale = Math.max(0.22, Math.min(1.2, Math.min((cw - 24) / sw, (ch - 24) / sh)));
    S.circuit.tx = Math.max(8, (cw - sw * S.circuit.scale) / 2);
    S.circuit.ty = Math.max(8, (ch - sh * S.circuit.scale) / 2);
    applyCircuitTransform();
  }

  function applyCircuitHighlight() {
    var stg = $("#circuitStage");
    if (!stg) return;
    var q = (S.circuit.filter || "").trim().toLowerCase();
    var res = S.circuit.lastRes;
    var payload = (res && res.payload) || {};
    var nodeMap = {};
    (payload.nodes || []).forEach(function (n) { nodeMap[n.id] = n; });
    (payload.binders || []).forEach(function (b) { nodeMap[b.id] = b; });

    $$(".circuit-node", stg).forEach(function (g) {
      var nid = g.getAttribute("data-node-id") || "";
      var obj = nodeMap[nid] || {};
      var hay = ((obj.label || "") + " " + (obj.full_name || "") + " " + (obj.tooltip || "") + " " + (obj.badge || "") + " " + (obj.type || "")).toLowerCase();
      var hit = q ? hay.indexOf(q) >= 0 : false;
      g.classList.toggle("dim", Boolean(q && !hit));
      g.classList.toggle("hl", hit);
    });
    $$(".circuit-pin", stg).forEach(function (g) {
      var pname = g.getAttribute("data-pin") || "";
      var hit = q ? pname.toLowerCase().indexOf(q) >= 0 : false;
      g.classList.toggle("dim", Boolean(q && !hit));
      g.classList.toggle("hl", hit);
    });
  }

  function wireCircuitStageInteractions() {
    if (S.circuit.stageWired) return;
    var wrap = $("#circuitStageWrap");
    if (!wrap) return;
    S.circuit.stageWired = true;
    var dragging = false, startX = 0, startY = 0, originTx = 0, originTy = 0;
    S.circuit._dragMoved = 0;

    wrap.addEventListener("pointerdown", function (ev) {
      if (ev.button !== 0) return;
      dragging = true;
      startX = ev.clientX;
      startY = ev.clientY;
      originTx = S.circuit.tx;
      originTy = S.circuit.ty;
      S.circuit._dragMoved = 0;
      wrap.classList.add("dragging");
    });
    window.addEventListener("pointermove", function (ev) {
      if (!dragging) return;
      var dx = ev.clientX - startX;
      var dy = ev.clientY - startY;
      S.circuit._dragMoved = Math.max(S.circuit._dragMoved, Math.hypot(dx, dy));
      S.circuit.tx = originTx + dx;
      S.circuit.ty = originTy + dy;
      applyCircuitTransform();
    });
    window.addEventListener("pointerup", function () {
      if (!dragging) return;
      dragging = false;
      wrap.classList.remove("dragging");
    });
    wrap.addEventListener("wheel", function (ev) {
      ev.preventDefault();
      var rect = wrap.getBoundingClientRect();
      var mx = ev.clientX - rect.left;
      var my = ev.clientY - rect.top;
      var factor = ev.deltaY < 0 ? 1.12 : 0.89;
      var ns = Math.max(0.18, Math.min(4.0, S.circuit.scale * factor));
      S.circuit.tx = mx - (mx - S.circuit.tx) * (ns / S.circuit.scale);
      S.circuit.ty = my - (my - S.circuit.ty) * (ns / S.circuit.scale);
      S.circuit.scale = ns;
      applyCircuitTransform();
    }, { passive: false });
  }

  function makeLegendPill(label, colorKey) {
    return dom("span", { className: "cir-pill " + (colorKey || "slate") }, [
      dom("i", { className: "sw" }),
      dom("span", { textContent: label })
    ]);
  }

  function renderCircuitLegendBar(payload) {
    var bar = $("#circuitLegendBar");
    if (!bar) return;
    clearEl(bar);
    var canonical = [
      ["read", "emerald"],
      ["unread", "slate"],
      ["cond →", "amber"],
      ["True stub", "crimson"],
      ["dropped binder", "crimson"],
      ["motif repeat ×N", "violet"]
    ];
    canonical.forEach(function (it) { bar.appendChild(makeLegendPill(it[0], it[1])); });
    if (payload && Array.isArray(payload.badges) && payload.badges.length) {
      bar.appendChild(dom("span", { className: "spacer" }));
      payload.badges.slice(0, 5).forEach(function (b) {
        bar.appendChild(makeLegendPill(String(b.label || ""), String(b.color_key || "cyan")));
      });
    }
  }

  function renderCircuitTopAndSubBars(res) {
    var top = $("#circuitTopBar");
    var sub = $("#circuitSubBar");
    if (!top || !sub) return;
    var c = S.circuit;
    clearEl(top);
    clearEl(sub);

    // Top bar: Title + [L] + 3-level Zoom Switcher + Breadcrumbs + Back to Graph
    top.appendChild(dom("span", { className: "pane-title p3-title", textContent: "Proof Circuit" }));
    top.appendChild(dom("span", { className: "ptag ptag-L", title: "L: extracted from kernel.db and source", textContent: "L" }));

    var modeSeg = dom("div", { className: "seg", id: "cirModeSeg", role: "tablist" }, [
      ["macro", "Zoom 0: Macro Repo"],
      ["bundle", "Zoom 1: Record Pin-Board"],
      ["theorem", "Zoom 2: Theorem Step-Wiring"]
    ].map(function (m) {
      return dom("button", {
        "data-cmode": m[0],
        className: c.mode === m[0] ? "active" : "",
        textContent: m[1],
        onclick: function () {
          if (m[0] === "macro") {
            openCircuit({ mode: "macro", target: "", exact_case: false });
          } else {
            var presets = c.presets || [];
            var firstMatch = presets.filter(function (p) { return p.mode === m[0]; })[0];
            var curTarget = (c.mode === m[0] && c.target) ? c.target : (firstMatch ? firstMatch.target : c.target);
            if (curTarget) {
              openCircuit({ mode: m[0], target: curTarget, exact_case: Boolean(firstMatch && firstMatch.target === curTarget && firstMatch.exact_case) });
            } else {
              c.mode = m[0];
              renderCircuitTopAndSubBars(c.lastRes);
              var inp = $("#cirTargetInput");
              if (inp) inp.focus();
            }
          }
        }
      });
    }));
    top.appendChild(modeSeg);

    if (c.history.length > 1) {
      top.appendChild(dom("button", {
        className: "btn sm",
        id: "cirHistBack",
        textContent: "← Back",
        title: "Step back in Proof Circuit zoom history",
        onclick: function () {
          if (c.history.length > 1) {
            c.history.pop();
            var prev = c.history[c.history.length - 1];
            openCircuit({ mode: prev.mode, target: prev.target, exact_case: prev.exact_case, skipHistory: true });
          }
        }
      }));
    }

    var crumbs = dom("div", { className: "cir-crumbs", id: "cirCrumbs" });
    c.history.slice(-5).forEach(function (h, idx, arr) {
      if (idx > 0) crumbs.appendChild(dom("span", { className: "cir-crumb-sep", textContent: "›" }));
      var isCur = idx === arr.length - 1;
      crumbs.appendChild(dom("button", {
        className: "cir-crumb" + (isCur ? " cur" : ""),
        title: h.mode + (h.target ? ": " + h.target : ""),
        textContent: (h.mode === "macro" ? "Macro" : shortName(h.target || h.mode)) + (h.mode !== "macro" ? " [" + h.mode[0].toUpperCase() + "]" : ""),
        onclick: function () {
          if (isCur) return;
          var absIdx = c.history.length - arr.length + idx;
          c.history = c.history.slice(0, absIdx + 1);
          openCircuit({ mode: h.mode, target: h.target, exact_case: h.exact_case, skipHistory: true });
        }
      }));
    });
    top.appendChild(crumbs);
    top.appendChild(dom("div", { className: "spacer" }));
    top.appendChild(dom("button", {
      className: "btn sm",
      id: "circuitBackBtn",
      textContent: "← Back to Graph",
      onclick: function () { closeCircuit(); }
    }));

    // Sub bar row 1: Showcase preset pills
    var presets = (res && Array.isArray(res.presets) && res.presets.length) ? res.presets : c.presets;
    if (presets && presets.length) {
      var pRow = dom("div", { className: "cir-presets", id: "cirPresets" });
      presets.forEach(function (pr) {
        var isAct = c.mode === pr.mode && ((pr.mode === "macro") || (c.target && (c.target === pr.target || shortName(c.target) === pr.label)));
        var btn = dom("button", {
          className: "cir-preset" + (isAct ? " active" : ""),
          "data-preset-id": pr.id || "",
          title: pr.mode + (pr.target ? " · " + pr.target : ""),
          onclick: function () {
            openCircuit({ mode: pr.mode, target: pr.target || "", exact_case: Boolean(pr.exact_case) });
          }
        }, [
          dom("span", { textContent: pr.label || pr.target || "Macro Repo" }),
          pr.tag ? dom("span", { className: "tag", textContent: pr.tag }) : null
        ]);
        pRow.appendChild(btn);
      });
      sub.appendChild(pRow);
    }

    // Sub bar row 2: Search input + highlight filter + Theme + Pan/Zoom + Exports
    var ctlRow = dom("div", { className: "cir-bar-row" });
    var targetInput = dom("input", {
      type: "search",
      id: "cirTargetInput",
      className: "cir-input",
      value: c.target || "",
      placeholder: c.mode === "bundle" ? "Structure / Prop-def name (Enter)…" : "Decl or structure name (Enter)…",
      spellcheck: "false"
    });
    var submitTarget = function () {
      var val = (targetInput.value || "").trim();
      if (!val) {
        openCircuit({ mode: "macro", target: "", exact_case: false });
        return;
      }
      var nextMode = c.mode === "macro" ? "theorem" : c.mode;
      openCircuit({ mode: nextMode, target: val, exact_case: false });
    };
    targetInput.addEventListener("keydown", function (ev) { if (ev.key === "Enter") submitTarget(); });

    var filterInput = dom("input", {
      type: "search",
      id: "cirFilterInput",
      className: "cir-input cir-filter",
      value: c.filter || "",
      placeholder: "Highlight nodes/pins…",
      spellcheck: "false"
    });
    filterInput.addEventListener("input", function () {
      S.circuit.filter = filterInput.value || "";
      applyCircuitHighlight();
    });

    ctlRow.appendChild(targetInput);
    ctlRow.appendChild(dom("button", { className: "btn sm primary", id: "cirLoadBtn", textContent: "Load", onclick: submitTarget }));
    ctlRow.appendChild(filterInput);
    ctlRow.appendChild(dom("div", { className: "spacer" }));
    ctlRow.appendChild(dom("button", {
      className: "btn sm",
      id: "cirThemeBtn",
      textContent: "Theme: " + (c.theme === "dark" ? "Dark" : "Light"),
      title: "Toggle SVG dark/light theme",
      onclick: function () {
        S.circuit.theme = (S.circuit.theme === "dark") ? "light" : "dark";
        openCircuit({ mode: S.circuit.mode, target: S.circuit.target, exact_case: S.circuit.exact_case, skipHistory: true });
      }
    }));
    ctlRow.appendChild(dom("button", {
      className: "btn sm", id: "cirZoomIn", textContent: "+", title: "Zoom in",
      onclick: function () { S.circuit.scale = Math.min(4.0, S.circuit.scale * 1.2); applyCircuitTransform(); }
    }));
    ctlRow.appendChild(dom("button", {
      className: "btn sm", id: "cirZoomOut", textContent: "−", title: "Zoom out",
      onclick: function () { S.circuit.scale = Math.max(0.18, S.circuit.scale / 1.2); applyCircuitTransform(); }
    }));
    ctlRow.appendChild(dom("button", {
      className: "btn sm", id: "cirZoomFit", textContent: "Fit", title: "Fit circuit to viewport",
      onclick: fitCircuitStage
    }));
    ctlRow.appendChild(dom("button", {
      className: "btn sm", id: "cirDownloadSvg", textContent: "Download SVG", title: "Download crisp vector SVG",
      onclick: function () {
        var svgTxt = S.circuit.lastRes && S.circuit.lastRes.svg;
        if (!svgTxt) return;
        var blob = new Blob([svgTxt], { type: "image/svg+xml;charset=utf-8" });
        var url = URL.createObjectURL(blob);
        var a = document.createElement("a");
        a.href = url;
        a.download = "leanre_circuit_" + (S.circuit.mode || "diagram") + ".svg";
        document.body.appendChild(a);
        a.click();
        a.remove();
        URL.revokeObjectURL(url);
      }
    }));
    ctlRow.appendChild(dom("button", {
      className: "btn sm", id: "cirOpenHtml", textContent: "Open Standalone HTML", title: "Open self-contained zero-CDN pan/zoom HTML in new tab",
      onclick: function () {
        window.open(circuitUrl({ format: "html" }), "_blank", "noopener");
      }
    }));
    sub.appendChild(ctlRow);
  }

  function renderCircuitDrawer(item, isHover) {
    var drawer = $("#circuitDrawer");
    if (!drawer) return;
    clearEl(drawer);

    var res = S.circuit.lastRes;
    var payload = (res && res.payload) || null;
    if (!payload) {
      drawer.appendChild(dom("div", { className: "cir-drawer-hd", textContent: "Inspector" }));
      drawer.appendChild(dom("div", { className: "cir-drawer-sub", textContent: "Select or hover a circuit node to inspect stats, pin status, motif counts, and source anchors." }));
      return;
    }

    var meta = payload.meta || {};
    var stats = payload.stats || {};
    var targetInfo = meta.target_info || {};

    var headerLabel = isHover ? "Hover Preview" : (item ? "Selected Node" : "Circuit Summary");
    drawer.appendChild(dom("div", { className: "cir-drawer-hd" }, [
      dom("span", { textContent: headerLabel }),
      dom("span", { className: "st-badge READ", textContent: String(payload.mode || "").toUpperCase() })
    ]));

    if (!item) {
      drawer.appendChild(dom("div", { className: "cir-drawer-title", textContent: payload.target || payload.title || "Macro Proof-Circuit" }));
      var topAnchor = (payload.pins && payload.pins.anchor) || meta.anchor || targetInfo.anchor || "";
      if (topAnchor) {
        var lnk = ghAnchorNode(topAnchor, topAnchor);
        if (lnk) drawer.appendChild(dom("div", { className: "cir-drawer-sub" }, ["Source: ", lnk]));
      }
      var kv = dom("div", { className: "cir-drawer-kv" });
      var addKv = function (k, v) {
        if (v === null || v === undefined || v === "") return;
        kv.appendChild(dom("div", { className: "k", textContent: k }));
        kv.appendChild(dom("div", { className: "v", textContent: String(v) }));
      };
      addKv("Nodes / Wires", fmt(stats.node_count) + " / " + fmt(stats.wire_count));
      if (payload.mode === "macro") {
        addKv("Live / Dead", fmt(stats.live_decls) + " / " + fmt(stats.dead_decls));
        addKv("Shared Diamond", fmt(stats.shared_diamond_decls) + " decls (" + fmt(stats.shared_diamond_roots) + " roots)");
        addKv("Motif Clusters", fmt(stats.motif_clusters_count));
        addKv("Portable Islands", fmt(stats.islands_count));
      } else if (payload.mode === "bundle") {
        addKv("Fields (Pins)", fmt(stats.total_fields) + " (" + fmt(stats.projected_fields) + " read, " + fmt(stats.unread_fields) + " unread)");
        addKv("Cond / True", fmt(stats.conditional_prop_fields) + " cond · " + fmt(stats.literal_true_fields) + " True stub");
        addKv("Producers", fmt(stats.producers_total) + " total (" + fmt(stats.producers_shown) + " shown)");
        addKv("Consumers", fmt(stats.consumers_total) + " total · " + fmt(stats.consumers_dropped_input) + "/" + fmt(stats.consumers_audited) + " drop input");
      } else if (payload.mode === "theorem") {
        addKv("Kind", stats.decl_kind || "—");
        addKv("Binders", fmt(stats.binders_used) + " used · " + fmt(stats.binders_dropped) + " dropped");
        addKv("Steps", fmt(stats.steps_count));
        addKv("Fan-in / Out", fmt(stats.fan_in) + " / " + fmt(stats.fan_out));
        if (meta.sighash) addKv("k1n Sighash", meta.sighash);
        if (meta.hygiene_findings_count != null) addKv("Hygiene Hits", fmt(meta.hygiene_findings_count));
      }
      drawer.appendChild(kv);

      if (payload.target) {
        var acts = dom("div", { className: "cir-drawer-acts" });
        if (payload.mode !== "bundle") {
          acts.appendChild(dom("button", {
            className: "btn sm", textContent: "Zoom 1: Bundle",
            onclick: function () { openCircuit({ mode: "bundle", target: payload.target, exact_case: true }); }
          }));
        }
        if (payload.mode !== "theorem") {
          acts.appendChild(dom("button", {
            className: "btn sm", textContent: "Zoom 2: Theorem",
            onclick: function () { openCircuit({ mode: "theorem", target: payload.target, exact_case: true }); }
          }));
        }
        acts.appendChild(dom("button", {
          className: "btn sm", textContent: "Slice in Kernel",
          onclick: function () { closeCircuit(); S.slice.name = payload.target; H.open("kernel", "slice"); }
        }));
        acts.appendChild(dom("button", {
          className: "btn sm", textContent: "Check Hygiene",
          onclick: function () { closeCircuit(); S.hygiene.decl = payload.target; S.hygiene.cone_depth = 0; H.open("kernel", "hygiene"); }
        }));
        drawer.appendChild(acts);
      }

      if (Array.isArray(meta.semantic_badges) && meta.semantic_badges.length) {
        drawer.appendChild(dom("div", { className: "cir-drawer-hd", textContent: "Hygiene & Semantic Pins" }));
        var bl = dom("div", { className: "cir-drawer-list" });
        meta.semantic_badges.slice(0, 6).forEach(function (sb) {
          bl.appendChild(dom("div", { className: "cir-drawer-item" }, [
            makeLegendPill(sb.label || "pin", sb.color_key || "amber"),
            sb.detail ? dom("div", { className: "dim sm", style: { marginTop: "3px" }, textContent: sb.detail }) : null
          ]));
        });
        drawer.appendChild(bl);
      }
      drawer.appendChild(dom("div", { className: "cir-drawer-sub", textContent: "Click any zoomable node to cross-zoom across Macro → Bundle → Theorem. Drag to pan, wheel to zoom." }));
      return;
    }

    // Specific node or pin inspected
    var titleTxt = item.full_name || item.name || item.label || item.id || "";
    drawer.appendChild(dom("div", { className: "cir-drawer-title", textContent: titleTxt }));
    var badgeRow = dom("div", { className: "cir-drawer-acts" });
    if (item.kind) badgeRow.appendChild(dom("span", { className: "st-badge", textContent: item.kind }));
    if (item.status) badgeRow.appendChild(makeLegendPill(item.status, item.color_key || (item.status === "dropped" || item.status === "dangling" || item.status === "literal_true" || item.status === "true_slot" ? "crimson" : (item.status === "conditional_prop" || item.status === "default_zero" ? "amber" : "emerald"))));
    if (item.badge) badgeRow.appendChild(dom("span", { className: "ev-tok", textContent: item.badge }));
    drawer.appendChild(badgeRow);

    var nodeAnchor = item.anchor || (item._isPin ? (targetInfo.anchor || "") : (item.line_no && meta.anchor ? meta.anchor.replace(/:\d+$/, ":" + item.line_no) : ""));
    if (nodeAnchor) {
      var aNode = ghAnchorNode(nodeAnchor, nodeAnchor);
      if (aNode) drawer.appendChild(dom("div", { className: "cir-drawer-sub" }, ["Source: ", aNode]));
    }

    var nkv = dom("div", { className: "cir-drawer-kv" });
    var addNkv = function (k, v) {
      if (v === null || v === undefined || v === "") return;
      nkv.appendChild(dom("div", { className: "k", textContent: k }));
      nkv.appendChild(dom("div", { className: "v", textContent: String(v) }));
    };
    var m = item.metrics || {};
    if (item._isPin) {
      addNkv("Pin Status", item.status);
      addNkv("Projected", item.projected ? "yes" : "no (0 callers)");
      if (item.fan_in != null) addNkv("Fan-in", fmt(item.fan_in));
      if (item.is_conditional_prop) addNkv("Conditional", "P → Q");
      if (item.is_literal_true) addNkv("Stub", "literal : True");
      if (item.type) addNkv("Type", item.type);
    } else {
      if (item.type) addNkv("Type", item.type);
      if (item.line_no != null) addNkv("Line", "L" + item.line_no);
      if (m.subtree_size != null) addNkv("Dom Subtree", fmt(m.subtree_size) + (m.pct_live != null ? " (" + m.pct_live + "%)" : ""));
      if (m.dom_subtree_size != null && m.subtree_size == null) addNkv("Dom Subtree", fmt(m.dom_subtree_size));
      if (m.fan_in != null) addNkv("Fan-in", fmt(m.fan_in));
      if (m.fan_out != null) addNkv("Fan-out", fmt(m.fan_out));
      if (item.k1n_count != null) addNkv("Motif k1n", "×" + fmt(item.k1n_count));
      if (m.k1n_count != null) addNkv("Motif k1n", "×" + fmt(m.k1n_count));
      if (m.count != null && m.scheme) addNkv("Motif Repeat", m.scheme + " ×" + fmt(m.count));
      if (m.sighash) addNkv("Sighash", m.sighash);
      if (m.max_project_decls != null) addNkv("Project Cone", fmt(m.max_project_decls) + " decls · disjoint=" + String(m.pairwise_disjoint));
      if (m.total_fields != null) addNkv("Pins", fmt(m.projected) + " read · " + fmt(m.unread) + " unread · " + fmt(m.conditional_prop) + " cond · " + fmt(m.literal_true) + " True");
      if (item.drops_target) addNkv("Hygiene", "DROPPED / unplugged bundle input");
      if (item.producer_role) addNkv("Producer Role", item.producer_role);
      if (item.tooltip) addNkv("Summary", item.tooltip);
    }
    drawer.appendChild(nkv);

    if (Array.isArray(item.badges) && item.badges.length) {
      drawer.appendChild(dom("div", { className: "cir-drawer-hd", textContent: "Node Badges" }));
      var nbWrap = dom("div", { className: "cir-drawer-acts" });
      item.badges.forEach(function (b) { nbWrap.appendChild(makeLegendPill(b.label || "", b.color_key || "amber")); });
      drawer.appendChild(nbWrap);
    }

    if (Array.isArray(item.callees) && item.callees.length) {
      drawer.appendChild(dom("div", { className: "cir-drawer-hd", textContent: "Step Callees (k1n)" }));
      var cl = dom("div", { className: "cir-drawer-list" });
      item.callees.forEach(function (ce) {
        cl.appendChild(dom("button", {
          className: "cir-sugg-btn",
          title: ce.name,
          textContent: (ce.short || shortName(ce.name)) + " ×" + fmt(ce.k1n_count),
          onclick: function () { openCircuit({ mode: "theorem", target: ce.name, exact_case: true }); }
        }));
      });
      drawer.appendChild(cl);
    }

    var zt = item.zoom_target || null;
    var pivotName = (zt && zt.target) || (item.full_name && /^[A-Za-z_][A-Za-z0-9_.']*$/.test(item.full_name) ? item.full_name : "");
    if (pivotName) {
      var nActs = dom("div", { className: "cir-drawer-acts" });
      if (zt && zt.mode && zt.target) {
        nActs.appendChild(dom("button", {
          className: "btn sm primary",
          textContent: "Cross-Zoom (" + zt.mode + ") →",
          onclick: function () { openCircuit({ mode: zt.mode, target: zt.target, exact_case: true }); }
        }));
      }
      nActs.appendChild(dom("button", {
        className: "btn sm",
        textContent: "As Bundle (Z1)",
        onclick: function () { openCircuit({ mode: "bundle", target: pivotName, exact_case: false }); }
      }));
      nActs.appendChild(dom("button", {
        className: "btn sm",
        textContent: "As Theorem (Z2)",
        onclick: function () { openCircuit({ mode: "theorem", target: pivotName, exact_case: false }); }
      }));
      nActs.appendChild(dom("button", {
        className: "btn sm",
        textContent: "Slice",
        onclick: function () { closeCircuit(); S.slice.name = pivotName; H.open("kernel", "slice"); }
      }));
      nActs.appendChild(dom("button", {
        className: "btn sm",
        textContent: "Hygiene",
        onclick: function () { closeCircuit(); S.hygiene.decl = pivotName; S.hygiene.cone_depth = 0; H.open("kernel", "hygiene"); }
      }));
      drawer.appendChild(nActs);
    }
  }

  function wireMountedCircuitSvg(svgEl, payload) {
    if (!svgEl || !payload) return;
    var tip = $("#circuitTip");
    var nodeById = {};
    (payload.nodes || []).forEach(function (n) { nodeById[n.id] = n; });
    (payload.binders || []).forEach(function (b) { nodeById[b.id] = b; });
    var pinByName = {};
    var chipNode = (payload.nodes || []).filter(function (n) { return n.kind === "chip"; })[0];
    if (chipNode && Array.isArray(chipNode.pins)) {
      chipNode.pins.forEach(function (p) { pinByName[p.name] = Object.assign({ _isPin: true }, p); });
    }

    $$(".circuit-node", svgEl).forEach(function (g) {
      var nid = g.getAttribute("data-node-id") || "";
      var obj = nodeById[nid] || { id: nid, label: nid };
      g.addEventListener("mouseenter", function () {
        S.circuit.hoveredNode = obj;
        renderCircuitDrawer(obj, true);
        if (tip) {
          tip.textContent = obj.tooltip || obj.full_name || obj.label || nid;
          tip.style.display = "block";
        }
      });
      g.addEventListener("mousemove", function (ev) {
        if (!tip) return;
        tip.style.left = Math.min(window.innerWidth - 440, ev.clientX + 14) + "px";
        tip.style.top = Math.min(window.innerHeight - 110, ev.clientY + 14) + "px";
      });
      g.addEventListener("mouseleave", function () {
        S.circuit.hoveredNode = null;
        if (tip) tip.style.display = "none";
        renderCircuitDrawer(S.circuit.selectedNode, false);
      });
      g.addEventListener("click", function (ev) {
        if ((S.circuit._dragMoved || 0) > 4) return;
        ev.stopPropagation();
        if (tip) tip.style.display = "none";
        $$(".circuit-node.selected, .circuit-pin.selected", svgEl).forEach(function (x) { x.classList.remove("selected"); });
        g.classList.add("selected");
        S.circuit.selectedNode = obj;
        renderCircuitDrawer(obj, false);

        var zmode = g.getAttribute("data-zoom-mode") || "";
        var ztgt = g.getAttribute("data-zoom-target") || "";
        if (zmode && ztgt) {
          if (S.circuit.mode === "macro" && obj.metrics && obj.metrics.sample_kind === "inductive") {
            zmode = "bundle";
          }
          openCircuit({ mode: zmode, target: ztgt, exact_case: true });
        }
      });
    });

    $$(".circuit-pin", svgEl).forEach(function (g) {
      var pname = g.getAttribute("data-pin") || "";
      var pObj = pinByName[pname] || { _isPin: true, name: pname, status: "projected" };
      g.addEventListener("mouseenter", function () {
        S.circuit.hoveredNode = pObj;
        renderCircuitDrawer(pObj, true);
        if (tip) {
          tip.textContent = pname + " [" + (pObj.status || "") + "]" + (pObj.type ? " : " + pObj.type : "");
          tip.style.display = "block";
        }
      });
      g.addEventListener("mousemove", function (ev) {
        if (!tip) return;
        tip.style.left = Math.min(window.innerWidth - 440, ev.clientX + 14) + "px";
        tip.style.top = Math.min(window.innerHeight - 110, ev.clientY + 14) + "px";
      });
      g.addEventListener("mouseleave", function () {
        S.circuit.hoveredNode = null;
        if (tip) tip.style.display = "none";
        renderCircuitDrawer(S.circuit.selectedNode, false);
      });
      g.addEventListener("click", function (ev) {
        if ((S.circuit._dragMoved || 0) > 4) return;
        ev.stopPropagation();
        $$(".circuit-node.selected, .circuit-pin.selected", svgEl).forEach(function (x) { x.classList.remove("selected"); });
        g.classList.add("selected");
        S.circuit.selectedNode = pObj;
        renderCircuitDrawer(pObj, false);
      });
    });
  }

  function closeCircuit() {
    S.circuit.open = false;
    var pane = $("#circuitPane");
    if (pane) pane.classList.remove("show");
    var btn = $("#circuitTabBtn");
    if (btn) btn.classList.remove("active");
    var tip = $("#circuitTip");
    if (tip) tip.style.display = "none";
  }

  function openCircuit(opts) {
    opts = opts || {};
    var c = S.circuit;
    c.open = true;
    if (opts.mode) c.mode = opts.mode;
    if (opts.target !== undefined) c.target = opts.target;
    if (opts.theme) c.theme = opts.theme;
    if (opts.exact_case !== undefined) c.exact_case = Boolean(opts.exact_case);
    if (opts.max_nodes !== undefined) c.max_nodes = Number(opts.max_nodes) || 0;
    if (c.mode === "macro") c.target = "";

    // Show #circuitPane cleanly and deactivate sibling overlays
    var pane = $("#circuitPane");
    if (pane) pane.classList.add("show");
    var p3p = $("#p3Pane");
    if (p3p) p3p.classList.remove("show");
    var tmp = $("#treemapPane");
    if (tmp) tmp.classList.remove("show");
    $$("#p3Seg button").forEach(function (b) { b.classList.remove("active"); });
    var tmBtn = $("#toggleTreemapBtn");
    if (tmBtn) tmBtn.classList.remove("primary");
    var tabBtn = $("#circuitTabBtn");
    if (tabBtn) tabBtn.classList.add("active");

    wireCircuitStageInteractions();

    // Update breadcrumb trail + browser history
    if (!opts.skipHistory) {
      var last = c.history[c.history.length - 1];
      if (!last || last.mode !== c.mode || last.target !== c.target) {
        c.history.push({ mode: c.mode, target: c.target, exact_case: c.exact_case });
        if (c.history.length > 24) c.history.shift();
      }
      if (!c.inSelfTest && window.history && typeof window.history.pushState === "function") {
        var hash = "#circuit=1&cmode=" + encodeURIComponent(c.mode) + (c.target ? "&ctarget=" + encodeURIComponent(c.target) : "");
        try {
          window.history.pushState({ leanreCircuit: true, mode: c.mode, target: c.target, exact_case: c.exact_case }, "", hash);
        } catch (e) { /* ignore in sandboxed contexts */ }
      }
    }

    var wrap = $("#circuitStageWrap");
    if (wrap) wrap.setAttribute("data-theme", c.theme);
    renderCircuitTopAndSubBars(c.lastRes);

    var stage = $("#circuitStage");
    if (window.location.protocol === "file:") {
      clearEl(stage);
      stage.appendChild(dom("div", { className: "p3-absent cir-stage-msg" }, [
        dom("h3", { textContent: "Local server required" }),
        dom("p", { textContent: "Start `python3 workbench/server.py` and open http://127.0.0.1:8420 to browse interactive 3-level Proof Circuits." })
      ]));
      renderCircuitLegendBar(null);
      renderCircuitDrawer(null, false);
      return Promise.resolve(null);
    }

    clearEl(stage);
    stage.style.transform = "none";
    stage.appendChild(dom("div", { className: "empty-state cir-stage-msg", textContent: "Rendering Proof Circuit (" + c.mode + (c.target ? " · " + c.target : "") + ")…" }));

    return get("/api/circuit", circuitApiParams()).then(function (res) {
      c.lastRes = res;
      c.selectedNode = null;
      c.hoveredNode = null;
      if (res && Array.isArray(res.presets) && res.presets.length) {
        c.presets = res.presets;
      }
      renderCircuitTopAndSubBars(res);

      if (!res || res.state === "absent") {
        clearEl(stage);
        stage.style.transform = "none";
        stage.appendChild(dom("div", { className: "p3-absent cir-stage-msg" }, [
          dom("h3", { textContent: "Not built yet — Proof Circuit" }),
          dom("p", { textContent: (res && res.message) || "kernel.db is not available yet." })
        ]));
        renderCircuitLegendBar(null);
        renderCircuitDrawer(null, false);
        return res;
      }

      if (res.found === false) {
        clearEl(stage);
        stage.style.transform = "none";
        var suggBox = dom("div", { className: "p3-absent cir-stage-msg" }, [
          dom("h3", { textContent: "Target not found in kernel.db" }),
          dom("p", { textContent: (res.message || ("No match for " + (res.queried || c.target))) })
        ]);
        if (Array.isArray(res.suggestions) && res.suggestions.length) {
          var sWrap = dom("div", { style: { marginTop: "8px" } });
          res.suggestions.forEach(function (sg) {
            sWrap.appendChild(dom("button", {
              className: "cir-sugg-btn",
              textContent: sg.name + " (" + sg.kind + ")",
              onclick: function () {
                openCircuit({ mode: sg.kind === "inductive" ? "bundle" : c.mode, target: sg.name, exact_case: true });
              }
            }));
          });
          suggBox.appendChild(sWrap);
        }
        stage.appendChild(suggBox);
        renderCircuitLegendBar(null);
        renderCircuitDrawer(null, false);
        return res;
      }

      var payload = res.payload || {};
      if (payload.target) c.target = payload.target;
      renderCircuitLegendBar(payload);
      var svgEl = mountSafeSvg(stage, res.svg || "");
      wireMountedCircuitSvg(svgEl, payload);
      fitCircuitStage();
      applyCircuitHighlight();
      renderCircuitDrawer(null, false);
      return res;
    }).catch(function (err) {
      clearEl(stage);
      stage.style.transform = "none";
      stage.appendChild(dom("div", { className: "p3-absent err cir-stage-msg" }, [
        dom("h3", { textContent: "Circuit request failed" }),
        dom("p", { textContent: String((err && err.message) || err) })
      ]));
      renderCircuitLegendBar(null);
      renderCircuitDrawer(null, false);
      return null;
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
        assert(stt && stt.decomp && stt.compute_atlas && stt.trim && stt.bundles && stt.portability && stt.hygiene && stt.circuit && stt.flirt_clusters && stt.flirt_atlas && stt.kernel_slice, "P4/P6 status reports decomp, compute_atlas, trim, bundles, portability, hygiene, circuit, flirt_clusters, flirt_atlas, kernel_slice");
        assert(!!$('#p3Seg button[data-p3="blueprint"]'), "P4 toolbar has Blueprint button");
        assert(!!$("#circuitTabBtn"), "R7 toolbar has Proof Circuit button");
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
      // 4b. Unread Bundles (5,497-structure census)
      .then(function () { S.bundles.only = "all"; S.bundles.sort = "score"; S.bundles.q = ""; S.bundles.offset = 0; return H.open("blueprint", "bundles"); })
      .then(function (res) {
        assert(!!$(".p3-absent:not(.err), .p3-src", body()), "P6 Unread Bundles tab renders either live census or explicit 'Not built yet'");
        if (res && res.state === "ready") {
          assert(res.summary && res.summary.total_live_1ctor_project_inductives >= 5000, "P6 Unread Bundles reports full 5,497-structure live 1-ctor corpus (" + (res.summary && res.summary.total_live_1ctor_project_inductives) + ")");
          assert($$("#bundlesTbl tbody tr", body()).length > 0, "P6 Unread Bundles renders structure rows");
          var ghLinks = $$("a.gh-link", body());
          assert(ghLinks.length > 0 && ghLinks.every(function (a) { return a.href.indexOf(GH_BLOB) === 0; }), "P6 Unread Bundles anchors point to pinned 40e56bab commit (" + ghLinks.length + ")");
        }
        checkText("blueprint bundles");
      })
      // 4c. Portability Gems (4 pairwise-disjoint Mathlib-portable islands + overlap matrix)
      .then(function () { S.portability.island = ""; return H.open("blueprint", "portability"); })
      .then(function (res) {
        assert(!!$(".p3-absent:not(.err), .p3-src", body()), "P6 Portability Gems tab renders either live report or explicit 'Not built yet'");
        if (res && res.state === "ready") {
          assert(res.summary && res.summary.islands_count >= 4 && res.summary.pairwise_disjoint_islands >= 4, "P6 Portability Gems reports 4 pairwise-disjoint Mathlib-portable islands");
          assert($$("#portIslands .port-card", body()).length >= 4, "P6 Portability Gems renders 4 island filter cards");
          assert($$("#portTargetsTbl tbody tr", body()).length >= 6, "P6 Portability Gems renders portable target rows");
          assert($$("#portOverlapTbl tbody tr", body()).length >= 6, "P6 Portability Gems renders pairwise overlap matrix");
          checkText("blueprint portability");
          S.portability.island = "finiteH_of_isProper";
          return renderPortability().then(function (f) {
            assert(f && f.found === true && (f.islands || []).length === 1 && $$("#portTargetsTbl tbody tr", body()).length === 1, "P6 Portability Gems ?island=finiteH_of_isProper filters to single island");
            S.portability.island = "";
          });
        }
        checkText("blueprint portability");
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
      // 5b. Live Kernel Proof Hygiene
      .then(function () { S.hygiene.decl = "allChi"; S.hygiene.cone_depth = 0; S.hygiene.only = "all"; return H.open("kernel", "hygiene"); })
      .then(function (res) {
        assert(!!$(".p3-absent:not(.err), .p3-src", body()), "P6 Kernel Hygiene tab renders either live audit or explicit 'Not built yet'");
        if (res && res.state === "ready") {
          assert(res.found === true && $$("#hygTbl tbody tr", body()).length >= 1, "P6 Kernel Hygiene audits live declaration allChi");
          checkText("kernel hygiene");
          S.hygiene.decl = "No.Such.Decl.__hygselftest";
          return renderKernelHygiene().then(function (miss) {
            assert(miss && miss.found === false && /Declaration not found/.test(body().textContent), "P6 Kernel Hygiene handles unknown decl gracefully");
            S.hygiene.decl = "allChi";
          });
        }
        checkText("kernel hygiene");
      })
      // 5. FLIRT Clusters tab
      .then(function () { return H.open("flirt", "clusters"); })
      .then(function () {
        assert(!!$(".p3-absent:not(.err), .p3-src", body()), "P4 FLIRT clusters tab renders either live clusters or explicit 'Not built yet'");
        if ($(".p3-src", body())) {
          assert($$("#flClTbl tbody tr").length > 0, "P4 FLIRT clusters tab renders live cluster rows");
        }
        checkText("flirt clusters");
      })
      // 6. 141-Cluster Blinded FLIRT Atlas tab
      .then(function () { S.atlas.status = "all"; S.atlas.severity = "all"; S.atlas.pillar = "all"; S.atlas.q = ""; return H.open("flirt", "atlas"); })
      .then(function (res) {
        assert(!!$(".p3-absent:not(.err), .p3-src", body()), "P6 141-Cluster Atlas tab renders either live atlas or explicit 'Not built yet'");
        if (res && res.state === "ready") {
          assert(res.totals && res.totals.clusters_count === 141, "P6 141-Cluster Atlas reports all 141 clusters");
          assert($$("#flAtlasTbl tbody tr", body()).length === 141, "P6 141-Cluster Atlas renders all 141 cluster rows");
          assert($$("#flAtlasTbl .ai-chip", body()).length >= 141, "P6 141-Cluster Atlas marks blinded [M] labels as AI DRAFT");
          var ghLinks = $$("a.gh-link", body());
          assert(ghLinks.length > 0 && ghLinks.every(function (a) { return a.href.indexOf(GH_BLOB) === 0; }), "P6 141-Cluster Atlas anchors point to pinned 40e56bab commit (" + ghLinks.length + ")");
          checkText("flirt atlas");
          S.atlas.status = "cross_domain_misplaced";
          return renderFlirtAtlas().then(function (f) {
            assert(f && f.total > 0 && $$("#flAtlasTbl tbody tr", body()).length === f.total, "P6 141-Cluster Atlas mismatch filter works (cross_domain_misplaced=" + (f && f.total) + ")");
            S.atlas.status = "all";
          });
        }
        checkText("flirt atlas");
      })
      // 7. Interactive 3-level Proof Circuit tab (Macro -> Bundle -> Theorem + cross-zoom)
      .then(function () {
        S.circuit.inSelfTest = true;
        S.circuit.history = [];
        S.circuit.theme = "dark";
        S.circuit.filter = "";
        return openCircuit({ mode: "macro", target: "", exact_case: false });
      })
      .then(function (res) {
        var pane = $("#circuitPane");
        assert(pane && pane.classList.contains("show"), "R7 Proof Circuit opens #circuitPane overlay");
        var txt = (pane && pane.textContent) || "";
        assert(!/\[object Object\]/.test(txt) && !FORBIDDEN.test(txt), "R7 Proof Circuit macro has clean wording and no [object Object]");
        if (!res || res.state === "absent") {
          assert(!!$(".p3-absent", pane), "R7 Proof Circuit absent kernel shows 'Not built yet'");
          closeCircuit();
          S.circuit.inSelfTest = false;
          return;
        }
        assert(res.found === true && !!$("#circuitStage svg"), "R7 Proof Circuit Zoom 0 macro mounts crisp SVG");
        assert($$("#circuitStage .circuit-node").length >= 2, "R7 Proof Circuit Zoom 0 renders interactive .circuit-node elements");
        assert($$("#circuitLegendBar .cir-pill").length >= 6, "R7 Proof Circuit renders legend pill bar");
        assert(($("#circuitDrawer").textContent || "").length > 20, "R7 Proof Circuit side inspector drawer populated");

        // Toggle theme dark -> light
        return openCircuit({ mode: "macro", target: "", theme: "light", skipHistory: true }).then(function (lres) {
          assert(lres && lres.theme === "light" && $("#circuitStage svg").getAttribute("data-theme") === "light", "R7 Proof Circuit theme toggle switches SVG to light theme");
          S.circuit.theme = "dark";
          var presets = S.circuit.presets || [];
          var bPreset = presets.filter(function (p) { return p.mode === "bundle"; })[0];
          if (!bPreset) return null;
          return openCircuit({ mode: "bundle", target: bPreset.target, exact_case: Boolean(bPreset.exact_case) }).then(function (bres) {
            assert(bres && bres.found === true && !!$("#circuitStage svg"), "R7 Proof Circuit Zoom 1 bundle mounts SVG (" + bPreset.label + ")");
            assert($$("#circuitStage .circuit-pin").length >= 1, "R7 Proof Circuit Zoom 1 renders IC field pins");
            var zoomNode = $('#circuitStage .circuit-node[data-zoom-target]:not([data-zoom-target=""])');
            if (zoomNode) {
              var beforeHist = S.circuit.history.length;
              zoomNode.dispatchEvent(new MouseEvent("click", { bubbles: true }));
              assert(S.circuit.history.length >= beforeHist, "R7 Proof Circuit click-to-cross-zoom triggered from Zoom 1 node");
            }
            var tPreset = presets.filter(function (p) { return p.mode === "theorem"; })[0];
            if (!tPreset) return null;
            return openCircuit({ mode: "theorem", target: tPreset.target, exact_case: Boolean(tPreset.exact_case) }).then(function (tres) {
              assert(tres && tres.found === true && !!$("#circuitStage svg"), "R7 Proof Circuit Zoom 2 theorem mounts SVG (" + tPreset.label + ")");
              assert($$("#cirCrumbs .cir-crumb").length >= 2, "R7 Proof Circuit maintains multi-level breadcrumb history");
            });
          });
        }).then(function () {
          closeCircuit();
          S.circuit.inSelfTest = false;
        });
      });
  }

  function wireCircuitGlobalHooks() {
    var tabBtn = $("#circuitTabBtn");
    if (tabBtn && !tabBtn.dataset.wired) {
      tabBtn.dataset.wired = "1";
      tabBtn.addEventListener("click", function () {
        if (S.circuit.open) {
          closeCircuit();
        } else {
          openCircuit({ mode: S.circuit.mode || "macro", target: S.circuit.target || "" });
        }
      });
    }
    ["#modeSeg", "#p3Seg", "#toggleTreemapBtn", "#invBar"].forEach(function (sel) {
      var el = $(sel);
      if (el && !el.dataset.circuitCloseWired) {
        el.dataset.circuitCloseWired = "1";
        el.addEventListener("click", function () { closeCircuit(); }, true);
      }
    });
    if (!window._leanreCircuitPopWired) {
      window._leanreCircuitPopWired = true;
      window.addEventListener("popstate", function (ev) {
        if (ev.state && ev.state.leanreCircuit) {
          openCircuit({
            mode: ev.state.mode || "macro",
            target: ev.state.target || "",
            exact_case: Boolean(ev.state.exact_case),
            skipHistory: true
          });
        } else if (S.circuit.open && window.location.hash.indexOf("circuit=1") < 0) {
          closeCircuit();
        }
      });
    }
  }

  function parseCircuitHash() {
    var out = {};
    (window.location.hash || "").replace(/^#/, "").split("&").forEach(function (kv) {
      var idx = kv.indexOf("=");
      if (idx > 0) out[kv.slice(0, idx)] = decodeURIComponent(kv.slice(idx + 1));
    });
    return out;
  }

  function init(helpers) {
    H = helpers;
    wireCircuitGlobalHooks();
    if (window.location.protocol === "file:") return Promise.resolve();
    var hq = parseCircuitHash();
    return refreshStatus().then(function (stt) {
      if (hq.circuit === "1" && hq.selftest !== "1") {
        openCircuit({
          mode: hq.cmode || "macro",
          target: hq.ctarget || "",
          theme: hq.ctheme || "dark",
          exact_case: hq.cexact === "1"
        });
      }
      return stt;
    });
  }

  return {
    init: init,
    refreshStatus: refreshStatus,
    renderBlueprintMap: renderBlueprintMap,
    renderTcbAudit: renderTcbAudit,
    renderComputeAtlas: renderComputeAtlas,
    renderTrimWaterfall: renderTrimWaterfall,
    renderBundles: renderBundles,
    renderPortability: renderPortability,
    renderKernelSlice: renderKernelSlice,
    renderKernelHygiene: renderKernelHygiene,
    renderFlirtClusters: renderFlirtClusters,
    renderFlirtAtlas: renderFlirtAtlas,
    openCircuit: openCircuit,
    closeCircuit: closeCircuit,
    selfTest: selfTest,
    state: S
  };
})();
