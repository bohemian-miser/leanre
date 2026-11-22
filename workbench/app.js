/* ==========================================================================
   app.js — leanre ("Ghidra for Lean") Interactive Workbench Controller
   Connects to workbench/server.py (SQLite-backed) with graceful static
   fallback for workbench_bundle.json / file:// opening.
   Includes #selftest=1 headless verification harness.
   ========================================================================== */
"use strict";

(function () {
  var $ = function (s, r) { return (r || document).querySelector(s); };
  var $$ = function (s, r) { return Array.prototype.slice.call((r || document).querySelectorAll(s)); };

  function esc(s) {
    return String(s == null ? "" : s).replace(/[&<>"]/g, function (c) {
      return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c];
    });
  }

  function fmtInt(n) {
    if (n == null || isNaN(n)) return "—";
    return Number(n).toLocaleString("en-US");
  }

  function fmtBytes(b) {
    if (b == null || isNaN(b)) return "—";
    if (b >= 1e9) return (b / 1e9).toFixed(2) + " GB";
    if (b >= 1e6) return (b / 1e6).toFixed(1) + " MB";
    if (b >= 1e3) return (b / 1e3).toFixed(1) + " KB";
    return b + " B";
  }

  function ptag(code) {
    code = String(code || "").replace(/[\[\]]/g, "").trim();
    var info = window.EXPLAIN_KB && window.EXPLAIN_KB.PROVENANCE[code];
    var title = info ? (code + ": " + info.label + " — " + info.desc) : code;
    return '<span class="ptag ptag-' + esc(code) + '" title="' + esc(title) + '">' + esc(code) + "</span>";
  }

  function formatInlineCode(txt) {
    return esc(txt).replace(/`([^`]+)`/g, "<code>$1</code>");
  }

  function flagBadge(f) {
    var danger = /kexactB|kcopy|CutCptCopy|addDecl|sorry|axiom|unsafe|native_decide|implemented_by/i.test(f);
    var warn = /decide_kernel|slow_con_leche|lean4lean_timeout|run_tac|BuildAid|OpenLiterature/i.test(f);
    var cls = danger ? "taint" : (warn ? "warn" : (f === "tcb_def" ? "def" : (f === "horn" ? "horn" : "")));
    return '<span class="kbadge ' + cls + '">' + esc(f) + "</span>";
  }

  // Application State
  var st = {
    live: false,
    bundle: null,
    overview: null,
    investigations: [],
    activeInvIdx: -1,
    activeStepIdx: 0,
    leftTab: "tree",       // "tree" | "results"
    rightTab: "decompiled",// "decompiled" | "forensics" | "explain"
    centerView: "graph",   // "graph" | "treemap" | "p3" (Phase 3 overlay, see phase3.js)
    annotTarget: null,     // {name, sighash, target} when the Annotate tab was opened for a kernel decl
    graphMode: "imports",  // "imports" | "horn" | "taint" | "tcb"
    graphRoot: "Main",
    depth: 2,
    maxNodes: 60,
    activeFlag: "",
    activeNs: "",
    expandedNs: { Development: true, Formalism: true },
    selectedName: "Main",
    selectedKind: "module",
    selectedDetail: null,
    searchResults: []
  };

  var graphView = null;
  var treemapView = null;

  // ------------------------------------------------------------------ API Layer
  function apiGet(url) {
    return fetch(url, { cache: "no-store" }).then(function (resp) {
      if (!resp.ok) throw new Error("HTTP " + resp.status + " on " + url);
      return resp.json();
    });
  }

  function normalizeBundleSubgraph(sub, mode) {
    if (!sub) return { root: "", mode: mode, nodes: [], edges: [] };
    var nodes = (sub.nodes || []).map(function (n) {
      var role = n.role || (
        n.kind === "tcb_def" ? "tcb_def" :
        n.kind === "tcb_thm" ? "tcb_thm" :
        n.kind === "horn_prop" ? "horn_prop" :
        n.kind === "forensic" ? "forensic" :
        (n.id === "Main" || n.id === "Statements" || n.id === "riemannHypothesis") ? "entry" : "normal"
      );
      return {
        id: n.id,
        inspect_name: n.inspect_name || n.id,
        label: n.label || n.id,
        sublabel: n.sublabel || n.group || n.kind || "",
        kind: n.kind || "module",
        role: role,
        layer: n.layer,
        is_root: !!n.is_root || n.id === sub.root,
        on_dom_spine: !!n.on_dom_spine,
        on_main_path: !!n.on_main_path,
        metrics: n.metrics || {
          lines: n.lines,
          dom: n.dom_subtree_size,
          fi: n.fan_in,
          fo: n.fan_out
        },
        flags: n.flags || []
      };
    });
    var edges = (sub.edges || []).map(function (e) {
      return {
        src: e.src,
        dst: e.dst,
        label: e.label || e.kind || "",
        kind: e.kind || (mode === "taint" ? "taint" : (mode === "tcb" ? "tcb" : "import")),
        is_dom: !!e.is_dom || e.kind === "dom",
        is_highlight: !!e.is_highlight
      };
    });
    return {
      root: sub.root || "",
      mode: sub.mode || mode,
      direction_hint: sub.direction_hint || "",
      truncated: !!sub.truncated,
      nodes: nodes,
      edges: edges
    };
  }

  function setConnStatus(isLive, label) {
    st.live = isLive;
    var badge = $("#connBadge");
    badge.className = isLive ? "live" : "static";
    badge.innerHTML = '<span class="dot"></span>' + esc(label);
    $("#fallbackBanner").classList.toggle("show", !isLive);
  }

  function loadInitialData() {
    var isFile = window.location.protocol === "file:";
    if (isFile) {
      return loadStaticFallback();
    }
    return Promise.all([
      apiGet("/api/overview"),
      apiGet("/api/investigations")
    ]).then(function (pair) {
      var ov = pair[0];
      var inv = pair[1];
      st.overview = ov;
      st.investigations = (inv && inv.investigations) || [];
      var mods = (ov.overview && ov.overview.corpus_stats && (ov.overview.corpus_stats.modules || ov.overview.corpus_stats.module_count)) || 0;
      if (ov.db_ready) {
        setConnStatus(true, "LIVE SQLITE · " + (mods ? fmtInt(mods) + " MODULES" : "CONNECTED"));
      } else {
        setConnStatus(false, "DB PENDING · FALLBACK MODE");
      }
      renderOverviewChrome();
      return loadInvestigation(0, 0);
    }).catch(function () {
      return loadStaticFallback();
    });
  }

  function loadStaticFallback() {
    setConnStatus(false, "STATIC FALLBACK · RUN server.py FOR FULL 175K DB");
    return fetch("../outputs/workbench_bundle.json").then(function (r) {
      if (!r.ok) throw new Error("No bundle");
      return r.json();
    }).then(function (bundle) {
      applyBundle(bundle);
    }).catch(function () {
      // Minimal graceful state if opened via file:// with CORS blocking local JSON
      st.overview = { mode: "offline", db_ready: false, meta: {}, overview: { namespaces: [], forensic_counts: {} } };
      st.investigations = [];
      renderOverviewChrome();
      renderEmptyStaticState();
    });
  }

  function applyBundle(bundle) {
    st.bundle = bundle;
    st.overview = {
      mode: "static_bundle",
      db_ready: false,
      meta: bundle.meta || {},
      overview: bundle.overview || {}
    };
    st.investigations = bundle.investigations || [];
    var mods = (bundle.overview && bundle.overview.corpus_stats && (bundle.overview.corpus_stats.modules || bundle.overview.corpus_stats.module_count)) || 175187;
    setConnStatus(false, "STATIC BUNDLE · " + fmtInt(mods) + " MODULES (LIMITED)");
    renderOverviewChrome();
    if (st.investigations.length) {
      loadInvestigation(0, 0);
    }
  }

  function renderEmptyStaticState() {
    $("#inspSub").textContent = "Offline — launch server.py or click Load workbench_bundle.json";
    $("#graphLegend").style.display = "none";
    $("#leftBody").innerHTML =
      '<div class="empty-state">Browser security blocked local JSON loading over <code>file://</code>.<br><br>' +
      "Run <code>python3 workbench/server.py</code> from the <code>leanre</code> repo root and open <code>http://127.0.0.1:8420</code>, or use the Load Bundle button above.</div>";
    $("#rightBody").innerHTML =
      '<div class="note-blk A"><h4>Launch Live Workbench</h4>' +
      "<p>To search all 175,187 modules, 1.06M declarations, Horn clauses, and 51,692 TCB declarations interactively:</p>" +
      '<div class="decomp-box">cd leanre   # your checkout\npython3 workbench/server.py</div>' +
      "<p>Then open <b>http://127.0.0.1:8420</b> in your browser.</p></div>";
  }

  // ------------------------------------------------------------------ Overview / Left Pane Chrome
  function renderOverviewChrome() {
    var ov = (st.overview && st.overview.overview) || {};
    var fcounts = ov.forensic_counts || {};
    var tcbStats = ov.tcb_stats || {};
    var hornStats = ov.horn_stats || {};

    // Top Investigation Buttons
    var invBar = $("#invBar");
    var presets = st.investigations.length ? st.investigations : [
      { id: "recon_main", title: "1. Recon main()" },
      { id: "tcb_xray", title: "2. TCB X-Ray" },
      { id: "ai_forensics", title: "3. AI Forensics" },
      { id: "namespace_reality", title: "4. Namespace Reality" }
    ];
    invBar.innerHTML = presets.map(function (p, idx) {
      var label = p.title.replace(/^\d+\.\s*/, "");
      return '<button class="inv-btn' + (idx === st.activeInvIdx ? " active" : "") + '" data-inv="' + idx + '">' +
        '<span class="num">' + (idx + 1) + "</span>" + esc(label) + "</button>";
    }).join("");
    $$(".inv-btn", invBar).forEach(function (b) {
      b.addEventListener("click", function () {
        loadInvestigation(Number(b.dataset.inv), 0);
      });
    });

    // Forensic Filter Chips
    var chipsDef = [
      { flag: "kexactB", label: "kexactB", cls: "danger", cnt: fcounts.kexactB_modules || fcounts.kexactB || 0 },
      { flag: "CutCptCopy", label: "CutCptCopy", cls: "danger", cnt: fcounts.CutCptCopy || 0 },
      { flag: "kcopy", label: "kcopy", cls: "danger", cnt: fcounts.kcopy || 0 },
      { flag: "decide_kernel", label: "decide +kernel", cls: "warn", cnt: fcounts.decide_kernel_modules || fcounts.decide_kernel || 0 },
      { flag: "slow_con_leche", label: "slowest con-leche", cls: "warn", cnt: fcounts.slow_con_leche || (ov.slowest_con_leche || []).length || 5 },
      { flag: "lean4lean_timeout", label: "fuel timeouts", cls: "warn", cnt: fcounts.lean4lean_timeout || (ov.timeout_modules || []).length || 5 },
      { flag: "run_tac", label: "run_tac", cls: "warn", cnt: fcounts.run_tac || 0 },
      { flag: "horn_spine", label: "Horn spine", cls: "", cnt: hornStats.horn_decls || hornStats.horn_edges || "" },
      { flag: "tcb_def", label: "TCB defs", cls: "", cnt: tcbStats.definitions_count || tcbStats.definitions || 11261 }
    ];
    var fwrap = $("#forensicChips");
    fwrap.innerHTML = chipsDef.map(function (c) {
      var active = st.activeFlag === c.flag ? " active" : "";
      var cntHtml = c.cnt !== "" && c.cnt != null ? '<span class="cnt">' + esc(fmtInt(c.cnt)) + "</span>" : "";
      return '<button class="fchip ' + c.cls + active + '" data-flag="' + esc(c.flag) + '">' +
        esc(c.label) + " " + cntHtml + "</button>";
    }).join("");
    $$(".fchip", fwrap).forEach(function (btn) {
      btn.addEventListener("click", function () {
        var fl = btn.dataset.flag;
        if (st.activeFlag === fl) {
          st.activeFlag = "";
        } else {
          st.activeFlag = fl;
          st.activeNs = "";
        }
        renderForensicChipStates();
        if (st.activeFlag) {
          st.leftTab = "results";
          updateLeftTabButtons();
          runSearch();
          // If it's a taint/forensic flag, also offer taint graph automatically if user clicks a danger/warn chip
          if (["kexactB", "CutCptCopy", "kcopy", "decide_kernel", "slow_con_leche", "lean4lean_timeout", "run_tac"].indexOf(st.activeFlag) >= 0) {
            setCenterView("graph");
            loadSubgraph("tag:" + st.activeFlag, "taint", 3);
          } else if (st.activeFlag === "horn_spine") {
            setCenterView("graph");
            loadSubgraph("RiemannHypothesis", "horn", 2);
          } else if (st.activeFlag === "tcb_def") {
            setCenterView("graph");
            loadSubgraph("riemannHypothesis", "tcb", 2);
          }
        } else {
          st.leftTab = "tree";
          updateLeftTabButtons();
          renderLeftPane();
        }
      });
    });

    // Populate Treemap data
    var nsRows = normalizeNamespaceRows(ov.namespaces || []);
    if (treemapView) {
      treemapView.setData(nsRows);
    }

    renderLeftPane();
  }

  function renderForensicChipStates() {
    $$("#forensicChips .fchip").forEach(function (b) {
      b.classList.toggle("active", b.dataset.flag === st.activeFlag);
    });
  }

  function normalizeNamespaceRows(raw) {
    // Handle both flat namespace_stats rows and nested tree formats gracefully
    var out = [];
    raw.forEach(function (r) {
      if (r.prefix) {
        out.push(r);
      } else if (r.name) {
        out.push({
          prefix: r.name,
          depth: r.depth || 1,
          parent: r.parent || null,
          module_count: r.module_count || r.files || 0,
          lines_wc: r.lines_wc || r.lines || 0,
          decl_count: r.decl_count || r.decls || 0,
          shim_count: r.shim_count || 0,
          forensic_hit_count: r.forensic_hit_count || 0,
          top_decl_prefixes: r.top_decl_prefixes || []
        });
        (r.children || []).forEach(function (ch) {
          out.push({
            prefix: ch.prefix || ch.name,
            depth: 2,
            parent: r.name,
            module_count: ch.module_count || ch.files || 0,
            lines_wc: ch.lines_wc || ch.lines || 0,
            decl_count: ch.decl_count || ch.decls || 0,
            shim_count: ch.shim_count || 0,
            forensic_hit_count: ch.forensic_hit_count || 0,
            top_decl_prefixes: ch.top_decl_prefixes || []
          });
        });
      }
    });
    return out;
  }

  function updateLeftTabButtons() {
    $$(".left-tabs button").forEach(function (b) {
      b.classList.toggle("active", b.dataset.ltab === st.leftTab);
    });
  }

  function renderLeftPane() {
    var body = $("#leftBody");
    if (st.leftTab === "results") {
      renderSearchResults(body);
      return;
    }
    var ov = (st.overview && st.overview.overview) || {};
    var rows = normalizeNamespaceRows(ov.namespaces || []);
    if (!rows.length) {
      body.innerHTML = '<div class="empty-state">No namespace index loaded yet.</div>';
      return;
    }
    var top = rows.filter(function (r) { return r.depth === 1; }).sort(function (a, b) { return b.module_count - a.module_count; });
    var byParent = {};
    rows.filter(function (r) { return r.depth === 2; }).forEach(function (r) {
      (byParent[r.parent] = byParent[r.parent] || []).push(r);
    });
    Object.keys(byParent).forEach(function (k) {
      byParent[k].sort(function (a, b) { return b.module_count - a.module_count; });
    });
    var totalMods = top.reduce(function (s, r) { return s + (r.module_count || 0); }, 0) || 1;

    var html = "";
    top.forEach(function (r) {
      var kids = byParent[r.prefix] || [];
      var exp = !!st.expandedNs[r.prefix];
      var pct = (r.module_count / totalMods * 100);
      html += '<div class="ns-row" data-ns="' + esc(r.prefix) + '" data-toggle="' + (kids.length ? "1" : "0") + '">' +
        '<span class="ns-caret">' + (kids.length ? (exp ? "▾" : "▸") : "·") + "</span>" +
        '<span class="ns-name">' + esc(r.prefix) + "</span>" +
        '<span class="ns-count">' + fmtInt(r.module_count) + "</span>" +
        "</div>" +
        '<div class="ns-bar-wrap"><div class="ns-bar" style="width:' + Math.max(1, pct).toFixed(1) + '%"></div></div>';
      if (exp && kids.length) {
        kids.slice(0, 20).forEach(function (ch) {
          var isMis = ch.prefix === "Development.AbelianVarietyTheory";
          var cpct = (ch.module_count / totalMods * 100);
          var shortCh = ch.prefix.replace(r.prefix + ".", "");
          html += '<div class="ns-row child" data-ns-pick="' + esc(ch.prefix) + '">' +
            '<span class="ns-caret">' + (isMis ? "!" : "└") + "</span>" +
            '<span class="ns-name" style="' + (isMis ? "color:#fbbf24" : "") + '">' + esc(shortCh) + "</span>" +
            '<span class="ns-count">' + fmtInt(ch.module_count) + " (" + cpct.toFixed(1) + "%)</span>" +
            "</div>";
        });
      }
    });

    body.innerHTML = html;

    $$(".ns-row[data-ns]", body).forEach(function (row) {
      row.addEventListener("click", function () {
        var ns = row.dataset.ns;
        if (row.dataset.toggle === "1") {
          st.expandedNs[ns] = !st.expandedNs[ns];
          renderLeftPane();
        } else {
          pickNamespace(ns);
        }
      });
    });
    $$(".ns-row[data-ns-pick]", body).forEach(function (row) {
      row.addEventListener("click", function () {
        pickNamespace(row.dataset.nsPick);
      });
    });
  }

  function pickNamespace(ns) {
    st.activeNs = ns;
    st.activeFlag = "";
    renderForensicChipStates();
    st.leftTab = "results";
    updateLeftTabButtons();
    runSearch();
  }

  function renderSearchResults(container) {
    var list = st.searchResults || [];
    var header = "";
    if (st.activeFlag || st.activeNs) {
      header = '<div style="padding:4px 10px 6px;display:flex;align-items:center;justify-content:space-between;border-bottom:1px solid var(--border);font-size:11px;color:var(--text-muted)">' +
        '<span>Filter: <b style="color:#fff">' + esc(st.activeFlag || st.activeNs) + "</b> (" + list.length + ")</span>" +
        '<button class="btn sm" id="clearFilterBtn">clear</button></div>';
    }
    if (!list.length) {
      container.innerHTML = header + '<div class="empty-state">No matching symbols. Try searching <code>Main</code>, <code>riemannZeta</code>, <code>Gz</code>, or click a forensic filter chip.</div>';
      var cb0 = $("#clearFilterBtn", container);
      if (cb0) cb0.addEventListener("click", clearFilters);
      return;
    }
    var html = header + list.map(function (item, idx) {
      var sel = item.id === st.selectedName || item.name === st.selectedName ? " selected" : "";
      var kcls = item.kind === "tcb" ? (item.flags && item.flags.indexOf("tcb_def") >= 0 ? "def" : "thm")
        : (item.kind === "forensic" ? "taint" : (item.kind === "horn" ? "horn" : ""));
      var meta = [];
      if (item.lines != null) meta.push(fmtInt(item.lines) + "L");
      if (item.dom_subtree_size) meta.push("dom:" + fmtInt(item.dom_subtree_size));
      if (item.hops_to_main != null) meta.push("hops:" + item.hops_to_main);
      if (item.depth_from_rh != null && item.depth_from_rh >= 0) meta.push("d_rh:" + item.depth_from_rh);
      return '<div class="sym-item' + sel + '" data-ridx="' + idx + '">' +
        '<div class="sym-top"><span class="kbadge ' + kcls + '">' + esc(item.subkind || item.kind) + '</span>' +
        '<span class="sym-name" title="' + esc(item.name) + '">' + esc(item.display || item.name) + "</span></div>" +
        (item.snippet ? '<div class="sym-snip" title="' + esc(item.snippet) + '">' + esc(item.snippet) + "</div>" : "") +
        '<div class="sym-sub">' + esc(meta.join(" · ")) + "</div>" +
        "</div>";
    }).join("");

    container.innerHTML = html;
    var cb = $("#clearFilterBtn", container);
    if (cb) cb.addEventListener("click", clearFilters);

    $$(".sym-item", container).forEach(function (el) {
      el.addEventListener("click", function () {
        var item = list[Number(el.dataset.ridx)];
        if (!item) return;
        setCenterView("graph");
        if (item.kind === "tcb") {
          inspectEntity(item.name, "tcb");
          loadSubgraph(item.name, "tcb", st.depth);
        } else if (item.kind === "horn") {
          inspectEntity(item.module, "module");
          loadSubgraph(item.name, "horn", st.depth);
        } else if (item.kind === "forensic") {
          inspectEntity(item.module, "module");
          loadSubgraph(item.module, "taint", 3);
        } else {
          inspectEntity(item.module || item.name, "module");
          loadSubgraph(item.module || item.name, "imports", st.depth);
        }
      });
    });
  }

  function clearFilters() {
    st.activeFlag = "";
    st.activeNs = "";
    $("#searchInput").value = "";
    renderForensicChipStates();
    st.leftTab = "tree";
    updateLeftTabButtons();
    renderLeftPane();
  }

  var searchTimer = null;
  function scheduleSearch() {
    clearTimeout(searchTimer);
    searchTimer = setTimeout(runSearch, 160);
  }

  function runSearch() {
    var q = ($("#searchInput").value || "").trim();
    var scope = $("#searchScope").value || "all";
    if (!q && !st.activeFlag && !st.activeNs && scope === "all") {
      st.leftTab = "tree";
      updateLeftTabButtons();
      renderLeftPane();
      return Promise.resolve();
    }
    st.leftTab = "results";
    updateLeftTabButtons();

    if (!st.live) {
      // Static bundle search over sample nodes
      var qlow = q.toLowerCase();
      var found = [];
      var seen = {};
      var samples = (st.bundle && st.bundle.sample_subgraphs) || {};
      Object.keys(samples).forEach(function (mk) {
        ((samples[mk] && samples[mk].nodes) || []).forEach(function (n) {
          if (seen[n.id]) return;
          if (!qlow || n.id.toLowerCase().indexOf(qlow) >= 0) {
            seen[n.id] = true;
            found.push({
              id: n.id, name: n.id, display: n.label || n.id,
              kind: mk === "tcb" ? "tcb" : "module", subkind: n.kind || mk,
              module: n.id, lines: n.lines, dom_subtree_size: n.dom_subtree_size, flags: n.flags || []
            });
          }
        });
      });
      st.searchResults = found.slice(0, 50);
      renderLeftPane();
      return Promise.resolve();
    }

    var params = new URLSearchParams();
    if (q) params.set("q", q);
    params.set("kind", scope);
    if (st.activeFlag) params.set("flag", st.activeFlag);
    if (st.activeNs) params.set("ns", st.activeNs);
    params.set("limit", "60");

    return apiGet("/api/search?" + params.toString()).then(function (data) {
      st.searchResults = data.results || [];
      renderLeftPane();
      return data;
    }).catch(function (err) {
      $("#leftBody").innerHTML = '<div class="empty-state">Search error: ' + esc(err.message) + "</div>";
    });
  }

  // ------------------------------------------------------------------ Center View (Graph / Treemap)
  function setCenterView(v) {
    st.centerView = v;
    $("#treemapPane").classList.toggle("show", v === "treemap");
    $("#p3Pane").classList.toggle("show", v === "p3");
    if (v !== "p3") $$("#p3Seg button").forEach(function (b) { b.classList.remove("active"); });
    $("#toggleTreemapBtn").classList.toggle("primary", v === "treemap");
    if (v === "treemap" && treemapView) {
      setTimeout(function () { treemapView.draw(); }, 20);
    }
  }

  function updateModeButtons() {
    $$("#modeSeg button").forEach(function (b) {
      b.classList.toggle("active", b.dataset.mode === st.graphMode);
    });
    updateGraphLegend();
  }

  function updateGraphLegend() {
    var m = st.graphMode;
    var items;
    if (m === "tcb") {
      items = [
        ["#34d399", "Headline Theorem"],
        ["#38bdf8", "Definition (Audit Target)"],
        ["#94a3b8", "Theorem (Kernel-Checked)"],
        ["#f87171", "Axiom"]
      ];
    } else if (m === "horn") {
      items = [
        ["#34d399", "Headline Prop"],
        ["#2dd4bf", "Interface Prop / PROVES"],
        ["#f59e0b", "REQUIRES Premise"],
        ["#60a5fa", "Bridge Theorem"]
      ];
    } else if (m === "taint") {
      items = [
        ["#f87171", "Forensic Hotspot / Taint Path"],
        ["#f59e0b", "Compute / Slow Hotspot"],
        ["#34d399", "Main.lean Entry"]
      ];
    } else {
      items = [
        ["#34d399", "Entry / Dominator Edge"],
        ["#2dd4bf", "Proof Spine / Crux"],
        ["#60a5fa", "Classical (~200L)"],
        ["#f87171", "Forensic Bypass"],
        ["#f59e0b", "Slow / Timeout"],
        ["#7dd3fc", "Major Hub"]
      ];
    }
    $("#graphLegend").style.display = "flex";
    $("#graphLegend").innerHTML = items.map(function (it) {
      return '<span class="lg-item"><i class="lg-swatch" style="background:' + it[0] + '"></i>' + esc(it[1]) + "</span>";
    }).join("");
  }

  function loadSubgraph(root, mode, depth, opts) {
    opts = opts || {};
    st.graphMode = mode || st.graphMode;
    st.graphRoot = root || st.graphRoot;
    if (depth != null) {
      st.depth = depth;
      $("#depthSelect").value = String(depth);
    }
    updateModeButtons();

    if (!st.live) {
      var sample = (st.bundle && st.bundle.sample_subgraphs && st.bundle.sample_subgraphs[st.graphMode]) || null;
      var norm = normalizeBundleSubgraph(sample, st.graphMode);
      renderGraphData(norm, opts.selectId);
      return Promise.resolve(norm);
    }

    var params = new URLSearchParams();
    params.set("root", st.graphRoot);
    params.set("mode", st.graphMode);
    params.set("depth", String(st.depth));
    params.set("max_nodes", String(st.maxNodes));

    $("#graphHudStats").textContent = "Loading " + st.graphMode + " subgraph…";
    return apiGet("/api/subgraph?" + params.toString()).then(function (data) {
      renderGraphData(data, opts.selectId);
      return data;
    }).catch(function (err) {
      $("#graphHudStats").textContent = "Error: " + err.message;
    });
  }

  function renderGraphData(data, selectId) {
    if (window.Phase3) window.Phase3.applyOverlay(data); // annotation renames from enabled layers
    graphView.render(data, false);
    var nCnt = (data.nodes || []).length;
    var eCnt = (data.edges || []).length;
    $("#graphHudStats").textContent =
      data.mode.toUpperCase() + " · " + nCnt + " nodes · " + eCnt + " edges" +
      (data.truncated ? " (capped)" : "");
    $("#graphHudDir").textContent = data.direction_hint || "";
    if (selectId) {
      var nodes = data.nodes || [];
      var hit = nodes.find(function (n) { return n.id === selectId; }) ||
                nodes.find(function (n) { return n.id === "prop:" + selectId || n.inspect_name === selectId; });
      if (hit) {
        graphView.select(hit.id);
        if (nodes.length > 26 || graphView.getScale() < 0.48) {
          graphView.focusNode(hit.id);
        }
      }
    }
  }

  function expandNodeInGraph(node) {
    if (!node || !st.live) return Promise.resolve();
    var target = node.inspect_name || node.id;
    var mode = st.graphMode;
    var params = new URLSearchParams();
    params.set("root", target);
    params.set("mode", mode);
    params.set("depth", "1");
    params.set("max_nodes", "28");

    return apiGet("/api/subgraph?" + params.toString()).then(function (sub) {
      var cur = graphView.getData();
      var nodeMap = {};
      var edgeMap = {};
      var mergedNodes = [];
      var mergedEdges = [];

      (cur.nodes || []).forEach(function (n) { nodeMap[n.id] = n; mergedNodes.push(n); });
      (sub.nodes || []).forEach(function (n) {
        if (!nodeMap[n.id] && mergedNodes.length < 130) {
          var copy = Object.assign({}, n, { is_root: false });
          delete copy.layer; // let topological layout place merged graph cleanly
          nodeMap[n.id] = copy;
          mergedNodes.push(copy);
        }
      });
      // Clear layers so newly merged subgraph re-layers coherently
      mergedNodes.forEach(function (n) { delete n.layer; });

      (cur.edges || []).concat(sub.edges || []).forEach(function (e) {
        var k = e.src + "->" + e.dst + ":" + e.kind;
        if (!edgeMap[k] && nodeMap[e.src] && nodeMap[e.dst]) {
          edgeMap[k] = true;
          mergedEdges.push(e);
        }
      });

      var next = Object.assign({}, cur, { nodes: mergedNodes, edges: mergedEdges });
      graphView.render(next, true);
      graphView.select(node.id);
      $("#graphHudStats").textContent =
        next.mode.toUpperCase() + " · " + mergedNodes.length + " nodes · " + mergedEdges.length + " edges (expanded)";
      return next;
    });
  }

  // ------------------------------------------------------------------ Investigations Walkthrough
  function loadInvestigation(invIdx, stepIdx) {
    var inv = st.investigations[invIdx];
    if (!inv) return Promise.resolve();
    st.activeInvIdx = invIdx;
    st.activeStepIdx = stepIdx || 0;

    $$("#invBar .inv-btn").forEach(function (b) {
      b.classList.toggle("active", Number(b.dataset.inv) === invIdx);
    });

    var steps = inv.steps || [];
    var step = steps[st.activeStepIdx] || null;
    var bar = $("#walkthrough");
    if (step) {
      bar.classList.add("show");
      $("#wtStepBadge").textContent = inv.title.split(".")[0] + " · STEP " + (st.activeStepIdx + 1) + "/" + steps.length;
      var prov = step.provenance ? ptag(step.provenance) : "";
      $("#wtBody").innerHTML = prov + "<strong>" + formatInlineCode(step.title) + ":</strong> " + formatInlineCode(step.text);
      $("#wtPrev").disabled = st.activeStepIdx <= 0;
      $("#wtNext").textContent = st.activeStepIdx >= steps.length - 1 ? "Done ✓" : "Next ▶";
    } else {
      bar.classList.remove("show");
    }

    var ov = (st.overview && st.overview.overview) || {};
    var nsSet = {};
    normalizeNamespaceRows(ov.namespaces || []).forEach(function (r) { nsSet[r.prefix] = r; });

    var mode = (step && step.mode) || inv.mode || "imports";
    var focus = (step && step.focus_node) || inv.root || "Main";
    var isNsFocus = !!nsSet[focus];
    var desiredView = (step && step.view) || inv.view ||
      (inv.id === "namespace_reality" && (st.activeStepIdx === 0 || isNsFocus) ? "treemap" : "graph");
    setCenterView(desiredView);

    if (desiredView === "treemap" && treemapView) {
      if (isNsFocus && nsSet[focus].depth === 1) {
        treemapView.setFilterParent(focus);
        if ($("#tmFilterSelect")) $("#tmFilterSelect").value = focus;
      } else {
        treemapView.setFilterParent(null);
        if ($("#tmFilterSelect")) $("#tmFilterSelect").value = "";
      }
    }

    var root;
    if (step && step.root) {
      root = step.root;
    } else if (mode === "taint" && focus && focus !== "Main") {
      // Trace the exact forensic hotspot's shortest path straight up to Main!
      root = focus;
    } else {
      root = inv.root || focus;
    }
    var depth = (step && step.depth) || (mode === "taint" ? 3 : (mode === "horn" ? 1 : 2));
    if (step && step.right_tab) {
      setRightTab(step.right_tab);
    }

    var p1;
    if (!st.live && inv.nodes && inv.nodes.length) {
      var norm = normalizeBundleSubgraph({ root: root, mode: mode, nodes: inv.nodes, edges: inv.edges || [] }, mode);
      st.graphMode = mode;
      updateModeButtons();
      renderGraphData(norm, focus);
      p1 = Promise.resolve();
    } else if (desiredView === "graph") {
      p1 = loadSubgraph(root, mode, depth, { selectId: focus }).then(function (data) {
        // If focus_node isn't inside the returned subgraph, pivot directly to focus_node so user sees it!
        var nodes = (data && data.nodes) || [];
        var hasFocus = nodes.some(function (n) {
          return n.id === focus || n.inspect_name === focus || n.id === "prop:" + focus;
        });
        if (!hasFocus && focus && focus !== root && focus.indexOf("tag:") !== 0 && !isNsFocus) {
          return loadSubgraph(focus, mode, depth, { selectId: focus });
        }
        return data;
      });
    } else {
      p1 = Promise.resolve();
    }

    var inspectTarget = (inv.id === "recon_main" && st.activeStepIdx === 0)
      ? "Main"
      : (focus.indexOf("prop:") === 0 ? focus.slice(5) : (focus.indexOf("tag:") === 0 ? "Main" : focus));
    var inspectKind = mode === "tcb" ? "tcb" : "module";
    if (isNsFocus) {
      // Populate synthetic namespace summary card cleanly from verified namespace_stats
      var nsRow = nsSet[focus];
      st.selectedName = focus;
      st.selectedDetail = {
        found: true,
        entity_kind: "module",
        name: focus,
        module: {
          name: focus,
          file_path: "src/" + focus.replace(/\./g, "/") + "/",
          namespace_top: nsRow.parent || focus,
          namespace_l2: focus,
          lines: nsRow.lines_eof || nsRow.lines_wc,
          lines_wc: nsRow.lines_wc,
          bytes: nsRow.bytes,
          trailing_nl: false,
          decl_count: nsRow.decl_count,
          fan_in: 0, fan_out: 0, bfs_depth: 0,
          dom_subtree_size: nsRow.module_count,
          dom_subtree_lines: nsRow.lines_wc,
          clone_cluster_size: 0, zlib_ratio: 0,
          forensic_flags: []
        },
        imports: [], imported_by: [], imported_by_total: 0,
        declarations: [], horn_clauses: [], forensic_hits: [],
        shortest_path_to_main: [], dominator_chain: []
      };
      renderInspectorHeader();
      renderRightBody();
      return p1;
    }
    return Promise.all([p1, inspectEntity(inspectTarget, inspectKind)]);
  }

  // ------------------------------------------------------------------ Right Inspector
  function setRightTab(tab) {
    st.rightTab = tab;
    $$("#rightTabs button").forEach(function (b) {
      b.classList.toggle("active", b.dataset.rtab === tab);
    });
    renderRightBody();
  }

  function inspectEntity(name, kind) {
    if (!name) return Promise.resolve();
    st.selectedName = name;
    st.selectedKind = kind || "module";
    $("#inspName").textContent = name;
    $("#inspSub").textContent = "Loading…";

    if (!st.live) {
      st.selectedDetail = { found: false, entity_kind: st.selectedKind, name: name };
      renderInspectorHeader();
      renderRightBody();
      return Promise.resolve();
    }

    var params = new URLSearchParams();
    params.set("name", name);
    if (kind) params.set("kind", kind);
    return apiGet("/api/module?" + params.toString()).then(function (data) {
      st.selectedDetail = data;
      renderInspectorHeader();
      renderRightBody();
      return data;
    }).catch(function (err) {
      $("#inspSub").textContent = "Error: " + err.message;
    });
  }

  function renderInspectorHeader() {
    var d = st.selectedDetail;
    var name = (d && d.name) || st.selectedName;
    $("#inspName").textContent = name;
    $("#inspAlias").innerHTML = window.Phase3 ? window.Phase3.aliasHtml(name) : "";

    if (!d || !d.found) {
      $("#inspSub").textContent = st.live ? "Symbol not found in SQLite index." : "Static fallback mode — launch server.py for full declaration details.";
      $("#inspActions").innerHTML = "";
      return;
    }

    if (d.entity_kind === "tcb" && d.tcb_detail) {
      var t = d.tcb_detail;
      $("#inspSub").innerHTML =
        ptag("L") + flagBadge(t.is_definition ? "tcb_def" : "tcb_thm") +
        " <code>" + esc(t.kind) + "</code> · " + esc(t.module_prefix) +
        (t.depth_from_rh >= 0 ? " · depth from RH: <b>" + t.depth_from_rh + "</b>" : "");
      $("#inspActions").innerHTML =
        '<button class="btn sm primary" id="actPivot">Pivot TCB Graph Here</button>' +
        '<button class="btn sm" id="actCopy">Copy Name</button>';
      $("#actPivot").addEventListener("click", function () { setCenterView("graph"); loadSubgraph(name, "tcb", st.depth, { selectId: name }); });
      $("#actCopy").addEventListener("click", function () { copyText(name); });
      return;
    }

    var m = d.module || {};
    var flagsHtml = (m.forensic_flags || []).map(flagBadge).join(" ");
    $("#inspSub").innerHTML =
      ptag("L") + esc(m.file_path || "") + " · " + fmtInt(m.lines) + "L · " + fmtInt(m.decl_count) + " decls " + flagsHtml;

    $("#inspActions").innerHTML =
      '<button class="btn sm primary" id="actPivot">Pivot Imports Here</button>' +
      '<button class="btn sm" id="actHorn">Horn Flow</button>' +
      '<button class="btn sm" id="actTaint">Trace to Main</button>' +
      '<button class="btn sm" id="actCopy">Copy Name</button>';
    $("#actPivot").addEventListener("click", function () { setCenterView("graph"); loadSubgraph(name, "imports", st.depth, { selectId: name }); });
    $("#actHorn").addEventListener("click", function () { setCenterView("graph"); loadSubgraph(name, "horn", 2); });
    $("#actTaint").addEventListener("click", function () { setCenterView("graph"); loadSubgraph(name, "taint", 3, { selectId: name }); });
    $("#actCopy").addEventListener("click", function () { copyText(name); });
  }

  function copyText(txt) {
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(txt).catch(function () {});
    }
  }

  function renderRightBody() {
    var body = $("#rightBody");
    var d = st.selectedDetail;

    if (st.rightTab === "annotate") {
      var at = st.annotTarget && st.annotTarget.name === st.selectedName ? st.annotTarget
        : { name: st.selectedName, sighash: "", target: st.selectedKind === "module" ? "module" : "decl" };
      return window.Phase3.renderAnnotateTab(body, at.name, at.sighash, at.target);
    }
    if (st.rightTab === "explain") {
      renderExplainTab(body, d);
      return;
    }
    if (!d || !d.found) {
      body.innerHTML = '<div class="empty-state">Select any node on the graph or symbol tree to inspect its decompiled contracts, RE metrics, and forensic paths.</div>';
      return;
    }
    if (st.rightTab === "decompiled") {
      renderDecompiledTab(body, d);
    } else {
      renderForensicsTab(body, d);
    }
  }

  function renderDecompiledTab(body, d) {
    if (d.entity_kind === "tcb" && d.tcb_detail) {
      var t = d.tcb_detail;
      var code =
        '<span class="dc-cmt">// [L] Semantic TCB Declaration (challenge.ndjson)</span>\n' +
        '<span class="dc-kw">' + esc(t.kind.toUpperCase()) + "</span> <span class=\"dc-sym\">" + esc(t.name) + "</span>\n" +
        '<span class="dc-cmt">// audit class: ' + (t.is_definition ? "HUMAN-AUDITABLE DEFINITION" : "KERNEL-CHECKED THEOREM") + "</span>\n" +
        '<span class="dc-cmt">// expression AST nodes: ' + fmtInt(t.expr_nodes) + "  |  dominator subtree: " + fmtInt(t.dom_subtree_size) + "</span>\n";
      var defDeps = (t.deps || []).filter(function (x) { return x.is_definition; });
      if (defDeps.length) {
        code += "\n<span class=\"dc-req\">DEPENDS_ON_DEFINITIONS</span> (\n";
        defDeps.slice(0, 14).forEach(function (dep) {
          code += "  " + esc(dep.name) + "  <span class=\"dc-cmt\">/* " + esc(dep.kind) + " · " + esc(dep.edge_kind) + " */</span>\n";
        });
        code += ")";
      }

      var html = '<div class="sec-h"><span>TCB Contract Summary</span><span>' + ptag("L") + "</span></div>" +
        '<div class="decomp-box">' + code + "</div>";

      html += '<div class="sec-h"><span>Direct Dependencies (' + (t.deps || []).length + ")</span><span>click to inspect</span></div>";
      if ((t.deps || []).length) {
        html += '<div class="path-list">' + t.deps.slice(0, 30).map(function (dep) {
          return '<div class="path-hop" data-jump-tcb="' + esc(dep.name) + '">' +
            flagBadge(dep.is_definition ? "tcb_def" : "tcb_thm") +
            '<span class="nm">' + esc(dep.name) + "</span>" +
            '<span class="kbadge">' + esc(dep.edge_kind) + "</span></div>";
        }).join("") + "</div>";
      } else {
        html += '<div class="empty-state">Leaf primitive in challenge.ndjson.</div>';
      }

      html += '<div class="sec-h"><span>Used By (' + fmtInt(t.used_by_total) + ")</span></div>";
      if ((t.used_by || []).length) {
        html += '<div class="path-list">' + t.used_by.slice(0, 20).map(function (u) {
          return '<div class="path-hop" data-jump-tcb="' + esc(u.name) + '">' +
            flagBadge(u.is_definition ? "tcb_def" : "tcb_thm") +
            '<span class="nm">' + esc(u.name) + "</span></div>";
        }).join("") + "</div>";
      }
      body.innerHTML = html;
      wireJumpLinks(body);
      return;
    }

    // Module Decompiled View: Horn pseudocode + fair-use 1-line signatures
    var m = d.module || {};
    var horns = d.horn_clauses || [];
    var decls = d.declarations || [];
    var hits = d.forensic_hits || [];

    var pseudo = '<span class="dc-cmt">// [L] Decompiled Interface — ' + esc(m.file_path || d.name) + "</span>\n";
    pseudo += '<span class="dc-kw">MODULE</span> <span class="dc-sym">' + esc(d.name) + "</span>";
    if (m.is_shim) pseudo += '  <span class="dc-flag">/* IMPORT-ONLY SHIM */</span>';
    pseudo += "\n";
    if (m.imports_mathlib) pseudo += '<span class="dc-cmt">// imports Mathlib wholesale</span>\n';

    if (horns.length) {
      pseudo += "\n<span class=\"dc-cmt\">// Extracted Dependency-Injection Horn Contracts (" + horns.length + ")</span>\n";
      horns.slice(0, 12).forEach(function (h) {
        pseudo += '<span class="dc-kw">CONTRACT</span> <span class="dc-sym">' + esc(h.decl) + "</span>  <span class=\"dc-cmt\">// L" + h.line_no + "</span>\n";
        if (h.requires && h.requires.length) {
          h.requires.forEach(function (rq) {
            pseudo += '  <span class="dc-req">REQUIRES</span>  ' + esc(rq) + "\n";
          });
        }
        if (h.proves) {
          pseudo += '  <span class="dc-prov">⟹ PROVES</span>  ' + esc(h.proves) + "\n";
        }
      });
    } else {
      pseudo += '<span class="dc-cmt">// No multi-premise Horn contracts detected in this module\'s headers.</span>\n';
    }
    if (hits.length) {
      pseudo += "\n<span class=\"dc-flag\">// FORENSIC ALERTS (" + hits.length + "): " +
        hits.map(function (h) { return h.tag + "@L" + h.line_no; }).slice(0, 8).join(", ") + "</span>\n";
    }

    var html2 = '<div class="sec-h"><span>Decompiled Horn Pseudocode</span><span>' + ptag("L") + "</span></div>" +
      '<div class="decomp-box">' + pseudo + "</div>";

    html2 += '<div class="sec-h"><span>Declaration Signatures (' + decls.length + " shown)</span><span>fair-use 1-line headers</span></div>";
    if (decls.length) {
      html2 += decls.slice(0, 40).map(function (dl) {
        var kcls = dl.kind === "theorem" || dl.kind === "lemma" ? "thm" : "def";
        var tags = (dl.forensic_tags || []).map(flagBadge).join(" ");
        return '<div class="decl-row">' +
          '<div class="dhead"><span class="kbadge ' + kcls + '">' + esc(dl.kind) + '</span>' +
          '<span class="dname">' + esc(dl.name) + '</span>' + tags +
          '<span class="dline">L' + dl.line_no + "</span></div>" +
          '<div class="dsig">' + esc(dl.signature_snippet) + "</div>" +
          "</div>";
      }).join("");
    } else {
      html2 += '<div class="empty-state">No top-level declarations (pure import shim or re-export file).</div>';
    }

    // Direct imports & importers cross-refs
    html2 += '<div class="sec-h"><span>Direct Project Imports (' + (d.imports || []).length + ")</span><span>upstream</span></div>";
    if ((d.imports || []).length) {
      html2 += '<div class="path-list">' + d.imports.slice(0, 25).map(function (im) {
        return '<div class="path-hop" data-jump-mod="' + esc(im.name) + '">' +
          '<span class="nm">' + esc(im.name) + "</span>" +
          '<span class="kbadge">dom:' + fmtInt(im.dom_subtree_size) + "</span></div>";
      }).join("") + "</div>";
    } else {
      html2 += '<div class="empty-state">Leaf module (imports Mathlib/Init only).</div>';
    }

    html2 += '<div class="sec-h"><span>Imported By (' + fmtInt(d.imported_by_total) + ")</span><span>downstream</span></div>";
    if ((d.imported_by || []).length) {
      html2 += '<div class="path-list">' + d.imported_by.slice(0, 20).map(function (im) {
        return '<div class="path-hop" data-jump-mod="' + esc(im.name) + '">' +
          '<span class="nm">' + esc(im.name) + "</span>" +
          '<span class="kbadge">dom:' + fmtInt(im.dom_subtree_size) + "</span></div>";
      }).join("") + "</div>";
    } else {
      html2 += '<div class="empty-state">Top-level root (not imported by any project module).</div>';
    }

    body.innerHTML = html2;
    wireJumpLinks(body);
  }

  function renderForensicsTab(body, d) {
    var ov = (st.overview && st.overview.overview) || {};
    var meta = (st.overview && st.overview.meta) || {};
    var html = "";

    if (d.entity_kind === "tcb" && d.tcb_detail) {
      var t = d.tcb_detail;
      html += '<div class="sec-h"><span>TCB Structural Metrics</span><span>' + ptag("L") + "</span></div>";
      html += '<div class="mgrid">' +
        mcell("Kind", t.kind, t.is_definition ? "ok" : "") +
        mcell("Depth from RH", t.depth_from_rh >= 0 ? String(t.depth_from_rh) : "GRH-only", "") +
        mcell("Dominator Subtree", fmtInt(t.dom_subtree_size), "") +
        mcell("Expr AST Nodes", fmtInt(t.expr_nodes), "") +
        mcell("Fan-In (Used By)", fmtInt(t.fan_in), "") +
        mcell("Fan-Out (Deps)", fmtInt(t.fan_out), "") +
        "</div>";

      if ((d.dominator_chain || []).length) {
        html += '<div class="sec-h"><span>TCB Dominator Chain</span></div>' +
          '<div class="path-list">' + d.dominator_chain.map(function (nm, i) {
            return '<div class="path-hop" data-jump-tcb="' + esc(nm) + '"><span class="idx">' + i + '</span><span class="nm">' + esc(nm) + "</span></div>";
          }).join("") + "</div>";
      }

      // Global TCB breakdown
      var tstats = ov.tcb_stats || {};
      var tkinds = ov.tcb_kind_counts || tstats.kind_counts || {};
      html += '<div class="sec-h"><span>Full Challenge TCB Summary (51,692 decls)</span><span>' + ptag("L") + "</span></div>";
      html += '<div class="mgrid">' +
        mcell("Total Decls", fmtInt(tstats.decl_count || 51692), "ok") +
        mcell("Definitions (Audit)", fmtInt(tstats.definitions_count || 11261) + " (" + (tstats.definitions_pct || 21.78) + "%)", "warn") +
        mcell("Pure Def-to-Def Cone", fmtInt(tstats.pure_def_cone_count || 2570) + " defs", "ok") +
        mcell("Dirichlet GRH Delta", "+" + fmtInt(tstats.extra_for_dirichlet_grh || 470) + " decls", "") +
        mcell("Theorems (Checked)", fmtInt(tkinds.thm || tstats.theorems_count || 40431), "") +
        mcell("Inductives (Bundled)", fmtInt(tkinds.inductive || 969) + " → " + fmtInt(tstats.unpacked_constants_est || 53722) + " consts", "") +
        "</div>";

      if ((ov.tcb_namespaces || []).length) {
        html += '<div class="sec-h"><span>Top Mathlib TCB Namespaces</span></div>' +
          '<table class="rtable"><thead><tr><th>Namespace</th><th>Total</th><th>Defs</th><th>Thms</th></tr></thead><tbody>' +
          ov.tcb_namespaces.slice(0, 12).map(function (ns) {
            return "<tr><td class='mono'>" + esc(ns.prefix) + "</td><td class='mono'>" + fmtInt(ns.total) +
              "</td><td class='mono' style='color:var(--c-select)'>" + fmtInt(ns.defs) +
              "</td><td class='mono'>" + fmtInt(ns.thms) + "</td></tr>";
          }).join("") + "</tbody></table>";
      }
      body.innerHTML = html;
      wireJumpLinks(body);
      return;
    }

    var m = d.module || {};
    html += '<div class="sec-h"><span>Reverse-Engineering Module Metrics</span><span>' + ptag("L") + "</span></div>";
    html += '<div class="mgrid">' +
      mcell("Logical Lines / wc -l", fmtInt(m.lines) + " / " + fmtInt(m.lines_wc), "") +
      mcell("File Size", fmtBytes(m.bytes), "") +
      mcell("Dominator Subtree", fmtInt(m.dom_subtree_size) + " mods", m.dom_subtree_size >= 1000 ? "ok" : "") +
      mcell("Unlock Radius (Lines)", fmtInt(m.dom_subtree_lines), "") +
      mcell("Fan-In / Fan-Out", fmtInt(m.fan_in) + " / " + fmtInt(m.fan_out), "") +
      mcell("BFS Depth from Main", String(m.bfs_depth != null ? m.bfs_depth : "—"), "") +
      mcell("Trailing Newline (\\n)", m.trailing_nl ? "Present (175,187/175,187)" : "Missing", m.trailing_nl ? "ok" : "warn") +
      mcell("Dup Imports / Clones", "dup:" + fmtInt(m.dup_imports) + " · cl:" + fmtInt(m.clone_cluster_size) + " · z:" + (m.zlib_ratio ? m.zlib_ratio.toFixed(2) : "—"), m.dup_imports ? "warn" : "") +
      "</div>";

    // Forensic Hits in this module
    var hits = d.forensic_hits || [];
    html += '<div class="sec-h"><span>Forensic Hits in This Module (' + hits.length + ")</span><span>" + ptag("L") + "</span></div>";
    if (hits.length) {
      html += '<table class="rtable"><thead><tr><th>Tag</th><th>Line</th><th>Snippet</th></tr></thead><tbody>' +
        hits.map(function (h) {
          return "<tr><td>" + flagBadge(h.tag) + "</td><td class='mono'>L" + h.line_no +
            "</td><td class='mono' style='word-break:break-word'>" + esc(h.snippet || h.decl_name || "") + "</td></tr>";
        }).join("") + "</tbody></table>";
    } else {
      html += '<div class="note-blk L"><p>' + ptag("L") + "Zero metaprogramming / bypass / timeout forensic hits in this module.</p></div>";
    }

    // Shortest Path to Main
    var spath = d.shortest_path_to_main || [];
    if (spath.length) {
      html += '<div class="sec-h"><span>Shortest Path to Main (' + Math.max(0, spath.length - 1) + " hops)</span></div>" +
        '<div class="path-list">' + spath.map(function (nm, idx) {
          return '<div class="path-hop" data-jump-mod="' + esc(nm) + '"><span class="idx">' + idx + '</span><span class="nm">' + esc(nm) + "</span></div>";
        }).join("") + "</div>";
    }

    // Dominator Chain
    var dchain = d.dominator_chain || [];
    if (dchain.length) {
      html += '<div class="sec-h"><span>Dominator Chain to Main</span></div>' +
        '<div class="path-list">' + dchain.map(function (nm, idx) {
          return '<div class="path-hop" data-jump-mod="' + esc(nm) + '"><span class="idx">D' + idx + '</span><span class="nm">' + esc(nm) + "</span></div>";
        }).join("") + "</div>";
    }

    // Global Profiler Hotspots (Slowest con-leche & 5 lean4lean timeout modules)
    var slowest = ov.slowest_con_leche || [];
    var timeouts = ov.timeout_modules || [];
    if (slowest.length) {
      html += '<div class="sec-h"><span>5 Slowest con-leche Declarations</span><span>' + ptag("C") + ptag("L") + "</span></div>" +
        '<table class="rtable"><thead><tr><th>Decl / Mechanism</th><th>Time</th></tr></thead><tbody>' +
        slowest.map(function (s) {
          var mod = s.module || "";
          var label = s.target_decl || s.decl || s.name || mod;
          var sec = s.con_leche_seconds != null ? s.con_leche_seconds + "s" : (s.seconds != null ? s.seconds + "s" : "");
          var mech = s.mechanism ? '<div style="font-size:10.5px;color:var(--text-muted);margin-top:2px">' + formatInlineCode(s.mechanism) + "</div>" : "";
          return '<tr style="cursor:pointer" data-jump-mod="' + esc(mod) + '"><td class="mono">' +
            "<b>" + esc(label) + "</b>" +
            '<div style="font-size:10px;color:var(--text-dim)">' + esc(mod) + (s.hops_to_main != null ? " · " + s.hops_to_main + " hops" : "") + "</div>" + mech + "</td>" +
            '<td class="mono" style="color:var(--c-note);white-space:nowrap">' + esc(sec) + "</td></tr>";
        }).join("") + "</tbody></table>";
    }
    if (timeouts.length) {
      html += '<div class="sec-h"><span>5 lean4lean Default-Fuel Timeout Modules</span><span>' + ptag("C") + ptag("L") + "</span></div>" +
        '<div class="path-list">' + timeouts.map(function (t) {
          var mod = typeof t === "string" ? t : (t.module || t.name || "");
          return '<div class="path-hop" data-jump-mod="' + esc(mod) + '">' +
            flagBadge("decide_kernel") + '<span class="nm">' + esc(mod) + "</span></div>";
        }).join("") + "</div>";
    }

    // Corpus-wide BinDiff v1 Fingerprint & Acceptance Gate Summary
    var bindiff = meta.bindiff_v1 || {};
    var gates = meta.acceptance_gates || {};
    if (Object.keys(bindiff).length || Object.keys(gates).length) {
      html += '<div class="sec-h"><span>Corpus Acceptance & BinDiff v1 Snapshot</span><span>' + ptag("L") + "</span></div>";
      html += '<div class="decomp-box">' + esc(JSON.stringify({ acceptance_gates: gates, bindiff_v1: bindiff }, null, 2)) + "</div>";
    }

    body.innerHTML = html;
    wireJumpLinks(body);
  }

  function mcell(k, v, cls) {
    return '<div class="mcell"><div class="mk">' + esc(k) + '</div><div class="mv ' + (cls || "") + '">' + esc(v) + "</div></div>";
  }

  function renderExplainTab(body, d) {
    var name = (d && d.name) || st.selectedName || "";
    var entry = window.EXPLAIN_KB ? window.EXPLAIN_KB.lookup(name, d) : null;
    var html = "";

    if (entry) {
      html += '<div class="sec-h"><span>' + esc(entry.title) + "</span></div>";
      entry.blocks.forEach(function (blk) {
        var extraCls = blk.head && /Where this analogy breaks/i.test(blk.head) ? "M" : blk.tag;
        html += '<div class="note-blk ' + esc(extraCls) + '">' +
          "<h4>" + ptag(blk.tag) + esc(blk.head) + "</h4>" +
          "<p>" + esc(blk.text) + "</p></div>";
      });
      if (entry.labs && entry.labs.length) {
        html += '<div class="sec-h"><span>Playable Math Labs (Interactive)</span></div>';
        entry.labs.forEach(function (lab) {
          html += '<div class="lab-cta"><div class="ltxt"><b>' + esc(lab.title) + "</b>" + esc(lab.desc) + "</div>" +
            '<a class="btn primary sm" href="' + esc(lab.href) + '" target="_blank" rel="noopener">Open Lab ↗</a></div>';
        });
      }
    } else {
      // Strict Anti-Slop Fallback: NEVER hallucinate math explanations for unaudited deep modules!
      var m = (d && d.module) || {};
      html += '<div class="sec-h"><span>Verified Facts Only — No Speculative Prose</span></div>';
      html += '<div class="note-blk L"><h4>' + ptag("L") + "Observed Structural Position</h4>" +
        "<p><b>" + esc(name) + "</b> resides in folder <code>" + esc(m.namespace_l2 || m.namespace_top || "—") +
        "</code> (" + fmtInt(m.lines) + " lines, " + fmtInt(m.decl_count) + " declarations, fan-in " + fmtInt(m.fan_in) +
        ", fan-out " + fmtInt(m.fan_out) + ", dominates " + fmtInt(m.dom_subtree_size) + " modules).</p></div>";
      html += '<div class="note-blk C"><h4>Anti-Slop Guardrail Active</h4>' +
        "<p>No hand-audited mathematical explanation exists for this internal module yet. Directory names in this 175,187-file proof frequently mislead — inspect the <b>Decompiled</b> tab's verbatim <code>[L]</code> declaration signatures and Horn contracts instead of extrapolating from the folder path.</p></div>";
      html += '<div class="lab-cta"><div class="ltxt"><b>Explore the Big Picture in RH·MAP</b>Interactive concept map + playable Gz(x), Finite Fields, and Chebyshev labs.</div>' +
        '<a class="btn primary sm" href="../prototypes/concept_map_demo.html" target="_blank" rel="noopener">Open RH·MAP ↗</a></div>';
    }

    // Provenance Legend Footer
    html += '<div class="sec-h"><span>Epistemic Provenance Legend (Guardrail 2)</span></div>' +
      '<div style="font-size:11px;color:var(--text-muted);line-height:1.6">' +
      ptag("L") + "Verbatim Lean / DB scan &nbsp; " +
      ptag("A") + "Alpöge 4-page note &nbsp; " +
      ptag("C") + "Cited community audit &nbsp; " +
      ptag("S") + "Standard maths &nbsp; " +
      ptag("M") + "RE/CS analogy (with break note)" +
      "</div>";

    body.innerHTML = html;
  }

  function wireJumpLinks(container) {
    $$("[data-jump-mod]", container).forEach(function (el) {
      el.addEventListener("click", function () {
        var target = el.dataset.jumpMod;
        setCenterView("graph");
        inspectEntity(target, "module");
        loadSubgraph(target, st.graphMode === "tcb" ? "imports" : st.graphMode, st.depth, { selectId: target });
      });
    });
    $$("[data-jump-tcb]", container).forEach(function (el) {
      el.addEventListener("click", function () {
        var target = el.dataset.jumpTcb;
        setCenterView("graph");
        inspectEntity(target, "tcb");
        loadSubgraph(target, "tcb", st.depth, { selectId: target });
      });
    });
  }

  // ------------------------------------------------------------------ Splitters & Wiring
  function wireSplitter(handle, pane, side) {
    var drag = false;
    handle.addEventListener("pointerdown", function (ev) {
      drag = true;
      handle.classList.add("dragging");
      try { handle.setPointerCapture(ev.pointerId); } catch (e) {}
    });
    handle.addEventListener("pointermove", function (ev) {
      if (!drag) return;
      var w;
      if (side === "left") {
        w = Math.max(220, Math.min(480, ev.clientX));
      } else {
        w = Math.max(320, Math.min(680, window.innerWidth - ev.clientX));
      }
      pane.style.width = w + "px";
      if (graphView) graphView.redrawMinimap();
      if (st.centerView === "treemap" && treemapView) treemapView.draw();
    });
    function stop() { drag = false; handle.classList.remove("dragging"); }
    handle.addEventListener("pointerup", stop);
    handle.addEventListener("pointercancel", stop);
  }

  function wireUI() {
    graphView = window.GraphView.create({
      viewport: $("#graphViewport"),
      svg: $("#graphSvg"),
      minimapCanvas: $("#minimapCanvas"),
      minimapWrap: $("#minimapWrap"),
      onSelect: function (node) {
        var nm = node.inspect_name || node.id;
        var kind = (node.kind === "tcb_def" || node.kind === "tcb_thm") ? "tcb" : "module";
        inspectEntity(nm, kind);
      },
      onExpand: function (node) {
        expandNodeInGraph(node);
      }
    });

    treemapView = window.TreemapView.create({
      canvas: $("#tmCanvas"),
      tip: $("#tmTip"),
      onSelectNs: function (nsItem) {
        pickNamespace(nsItem.prefix);
        // Also display AbelianVarietyTheory explanation if clicked
        if (nsItem.prefix.indexOf("AbelianVarietyTheory") >= 0) {
          st.selectedName = nsItem.prefix;
          st.selectedDetail = {
            found: true,
            entity_kind: "module",
            name: nsItem.prefix,
            module: {
              name: nsItem.prefix,
              file_path: "src/" + nsItem.prefix.replace(/\./g, "/") + "/",
              namespace_top: nsItem.parent || nsItem.prefix,
              namespace_l2: nsItem.prefix,
              lines: nsItem.lines_wc,
              lines_wc: nsItem.lines_wc,
              bytes: nsItem.bytes,
              decl_count: nsItem.decl_count,
              fan_in: 0, fan_out: 0, dom_subtree_size: nsItem.module_count,
              forensic_flags: []
            }
          };
          renderInspectorHeader();
          setRightTab("explain");
        }
      }
    });

    window.Phase3.init({
      esc: esc, fmtInt: fmtInt, ptag: ptag, apiGet: apiGet, copyText: copyText,
      setCenterView: setCenterView,
      inspect: inspectEntity,
      shortName: function (n) { n = String(n || ""); var p = n.split("."); return p.length > 2 ? "…" + p.slice(-2).join(".") : n; },
      // Open the right-pane Annotate tab for a name (kernel decl or module); returns a promise.
      annotate: function (name, sighash, target) {
        st.annotTarget = { name: name, sighash: sighash || "", target: target || "decl" };
        var ready = target === "module" ? inspectEntity(name, "module") : Promise.resolve().then(function () {
          st.selectedName = name; st.selectedKind = "decl";
          st.selectedDetail = { found: false, entity_kind: "decl", name: name };
          $("#inspName").textContent = name;
          $("#inspAlias").innerHTML = window.Phase3.aliasHtml(name);
          $("#inspSub").textContent = "Kernel declaration — see the Kernel-Exact view for its dependency facts.";
          $("#inspActions").innerHTML = "";
        });
        return ready.then(function () {
          st.rightTab = "annotate";
          $$("#rightTabs button").forEach(function (b) { b.classList.toggle("active", b.dataset.rtab === "annotate"); });
          return renderRightBody();
        });
      },
      onOverlayChanged: function () {
        $("#inspAlias").innerHTML = window.Phase3.aliasHtml(st.selectedName);
        if (graphView && st.centerView === "graph") {
          var data = graphView.getData();
          if (data && (data.nodes || []).length) graphView.render(window.Phase3.applyOverlay(data), true);
        }
      }
    });

    wireSplitter($("#splitLeft"), $("#leftPane"), "left");
    wireSplitter($("#splitRight"), $("#rightPane"), "right");

    // Search & Left tabs
    $("#searchInput").addEventListener("input", scheduleSearch);
    $("#searchScope").addEventListener("change", runSearch);
    $$(".left-tabs button").forEach(function (b) {
      b.addEventListener("click", function () {
        st.leftTab = b.dataset.ltab;
        updateLeftTabButtons();
        renderLeftPane();
      });
    });

    // Graph toolbar
    $$("#modeSeg button").forEach(function (b) {
      b.addEventListener("click", function () {
        var mode = b.dataset.mode;
        setCenterView("graph");
        var root = st.graphRoot;
        if (mode === "tcb" && st.selectedKind !== "tcb") root = "riemannHypothesis";
        else if (mode === "taint" && !root.startsWith("tag:") && root === "Main") root = "tag:kexactB";
        else if (mode === "horn" && root === "Main") root = "RiemannHypothesis";
        else if (mode === "imports" && (root.startsWith("tag:") || st.selectedKind === "tcb")) root = "Main";
        loadSubgraph(root, mode, mode === "taint" ? 3 : st.depth);
      });
    });

    $("#depthSelect").addEventListener("change", function () {
      st.depth = Number(this.value) || 2;
      loadSubgraph(st.graphRoot, st.graphMode, st.depth);
    });
    $("#maxNodesSelect").addEventListener("change", function () {
      st.maxNodes = Number(this.value) || 60;
      loadSubgraph(st.graphRoot, st.graphMode, st.depth);
    });
    $("#chkEdgeLabels").addEventListener("change", function () {
      graphView.setOptions({ showEdgeLabels: this.checked });
    });
    $("#chkDomPath").addEventListener("change", function () {
      graphView.setOptions({ highlightDom: this.checked });
    });
    $("#expandBtn").addEventListener("click", function () {
      var data = graphView.getData();
      var found = (data.nodes || []).find(function (n) { return n.id === st.selectedName || n.inspect_name === st.selectedName; });
      if (found) expandNodeInGraph(found);
    });
    $("#fitBtn").addEventListener("click", function () { graphView.fit(true); });
    $("#gZoomIn").addEventListener("click", function () { graphView.zoomIn(); });
    $("#gZoomOut").addEventListener("click", function () { graphView.zoomOut(); });
    $("#gZoomFit").addEventListener("click", function () { graphView.fit(true); });

    $("#toggleTreemapBtn").addEventListener("click", function () {
      setCenterView(st.centerView === "treemap" ? "graph" : "treemap");
    });

    // Treemap controls
    $$("#tmMetricSeg button").forEach(function (b) {
      b.addEventListener("click", function () {
        $$("#tmMetricSeg button").forEach(function (x) { x.classList.remove("active"); });
        b.classList.add("active");
        treemapView.setMetric(b.dataset.metric);
      });
    });
    $("#tmFilterSelect").addEventListener("change", function () {
      treemapView.setFilterParent(this.value || null);
    });
    $("#tmBackGraphBtn").addEventListener("click", function () { setCenterView("graph"); });

    // Right Tabs
    $$("#rightTabs button").forEach(function (b) {
      b.addEventListener("click", function () { setRightTab(b.dataset.rtab); });
    });

    // Walkthrough controls
    $("#wtPrev").addEventListener("click", function () {
      if (st.activeStepIdx > 0) loadInvestigation(st.activeInvIdx, st.activeStepIdx - 1);
    });
    $("#wtNext").addEventListener("click", function () {
      var inv = st.investigations[st.activeInvIdx];
      if (!inv) return;
      if (st.activeStepIdx < (inv.steps || []).length - 1) {
        loadInvestigation(st.activeInvIdx, st.activeStepIdx + 1);
      } else {
        $("#walkthrough").classList.remove("show");
      }
    });
    $("#wtClose").addEventListener("click", function () { $("#walkthrough").classList.remove("show"); });

    // Local bundle upload fallback (useful when opened directly via file://)
    var bInput = $("#bundleFileInput");
    if (bInput) {
      $("#loadBundleBtn").addEventListener("click", function () { bInput.click(); });
      bInput.addEventListener("change", function () {
        var file = bInput.files && bInput.files[0];
        if (!file) return;
        var reader = new FileReader();
        reader.onload = function () {
          try {
            applyBundle(JSON.parse(reader.result));
          } catch (e) {
            alert("Invalid JSON bundle: " + e.message);
          }
        };
        reader.readAsText(file);
      });
    }

    // Keyboard shortcuts
    window.addEventListener("keydown", function (ev) {
      if (ev.target && /INPUT|SELECT|TEXTAREA/.test(ev.target.tagName)) {
        if (ev.key === "Escape") ev.target.blur();
        return;
      }
      if (ev.key === "/") { ev.preventDefault(); $("#searchInput").focus(); }
      else if (ev.key === "f") { graphView.fit(true); }
      else if (ev.key === "1") { loadInvestigation(0, 0); }
      else if (ev.key === "2") { loadInvestigation(1, 0); }
      else if (ev.key === "3") { loadInvestigation(2, 0); }
      else if (ev.key === "4") { loadInvestigation(3, 0); }
    });

    window.addEventListener("resize", function () {
      if (graphView) graphView.redrawMinimap();
      if (st.centerView === "treemap" && treemapView) treemapView.draw();
    });
  }

  // ------------------------------------------------------------------ Self-Test Harness (#selftest=1)
  function runSelfTest() {
    var errs = [];
    var checks = 0;
    var phase2Checks = 0;
    var p3Note = "";
    function assert(cond, msg) {
      checks++;
      if (!cond) errs.push("FAIL: " + msg);
    }

    window.addEventListener("error", function (ev) {
      errs.push("window.onerror: " + ev.message);
    });

    return Promise.resolve()
      .then(function () {
        assert(st.overview != null, "overview loaded");
        if (st.live) {
          var cs = (st.overview.overview && st.overview.overview.corpus_stats) || {};
          assert((cs.modules || cs.module_count || 0) >= 175000, "real 175k+ modules in overview");
          assert((st.overview.overview.namespaces || []).length > 0, "namespace stats populated");
        }
        assert(st.investigations.length === 4, "4 investigations loaded (got " + st.investigations.length + ")");
      })
      // Exercise all 4 investigations
      .then(function () { return loadInvestigation(0, 0); })
      .then(function () { assert((graphView.getData().nodes || []).length > 0, "inv 0 renders graph nodes"); return loadInvestigation(0, 1); })
      .then(function () { return loadInvestigation(1, 0); })
      .then(function () { assert(st.graphMode === "tcb" && (graphView.getData().nodes || []).length > 0, "inv 1 TCB graph renders"); })
      .then(function () { return loadInvestigation(2, 0); })
      .then(function () { assert(st.graphMode === "taint" && (graphView.getData().nodes || []).length > 0, "inv 2 Taint graph renders"); })
      .then(function () { return loadInvestigation(3, 0); })
      .then(function () {
        assert(st.centerView === "treemap", "inv 3 opens treemap");
        treemapView.setMetric("lines_wc");
        treemapView.setMetric("decl_count");
        treemapView.setMetric("module_count");
        checks += 3;
        setCenterView("graph");
      })
      // Exercise all 4 view modes explicitly
      .then(function () { return loadSubgraph("Main", "imports", 2); })
      .then(function (d) { assert(d && (d.nodes || []).length > 0, "mode imports"); })
      .then(function () { return loadSubgraph("RiemannHypothesis", "horn", 2); })
      .then(function (d) { assert(d && (d.nodes || []).length > 0, "mode horn"); })
      .then(function () { return loadSubgraph("tag:kexactB", "taint", 3); })
      .then(function (d) { assert(d && (d.nodes || []).length > 0, "mode taint"); })
      .then(function () { return loadSubgraph("riemannHypothesis", "tcb", 2); })
      .then(function (d) { assert(d && (d.nodes || []).length > 0, "mode tcb"); })
      // Exercise search + forensic chips + node expand + all 3 inspector tabs
      .then(function () {
        $("#searchInput").value = "MainConclusion";
        return runSearch();
      })
      .then(function () {
        assert(st.searchResults.length > 0, "search 'MainConclusion' returns hits");
        $("#searchInput").value = "";
        st.activeFlag = "kexactB";
        return runSearch();
      })
      .then(function () {
        assert(st.searchResults.length > 0, "forensic chip 'kexactB' returns hits");
        clearFilters();
        return loadSubgraph("Main", "imports", 1);
      })
      .then(function (d) {
        var first = (d && d.nodes && d.nodes[0]) || null;
        assert(first != null, "root node exists for expand");
        return first ? expandNodeInGraph(first) : null;
      })
      .then(function () {
        return inspectEntity("Main", "module");
      })
      .then(function () {
        setRightTab("decompiled"); checks++;
        setRightTab("forensics"); checks++;
        setRightTab("explain"); checks++;
        assert($("#rightBody").textContent.length > 80, "explain tab rendered content");
        return inspectEntity("riemannZeta", "tcb");
      })
      .then(function () {
        setRightTab("decompiled"); checks++;
        setRightTab("forensics"); checks++;
        setRightTab("explain"); checks++;
      })
      // ---- Phase 3: kernel-exact, FLIRT and annotation views (phase3.js) ----
      .then(function () {
        phase2Checks = checks;
        return window.Phase3.selfTest(assert);
      })
      .then(function (note) { p3Note = note || ""; })
      .catch(function (e) {
        errs.push("Unhandled promise rejection: " + (e && e.stack ? e.stack : String(e)));
      })
      .then(function () {
        if (!phase2Checks) phase2Checks = checks;
        var out = document.createElement("pre");
        out.id = "selftest";
        out.style.cssText = "position:fixed;left:10px;bottom:10px;z-index:9999;background:#090c11ee;border:1px solid " +
          (errs.length ? "#f87171" : "#34d399") + ";color:" + (errs.length ? "#fecaca" : "#6ee7b7") +
          ";padding:8px 12px;border-radius:6px;font:12px var(--mono);max-width:75vw;white-space:pre-wrap";
        out.textContent = errs.length
          ? "SELFTEST FAIL (" + errs.length + " errors / " + checks + " checks)\n" + errs.join("\n")
          : "SELFTEST PASS — " + checks + " checks, 0 errors (live=" + st.live + ")\n" +
            phase2Checks + " Phase 2 checks + " + (checks - phase2Checks) + " Phase 3 checks · " + p3Note;
        out.dataset.checks = String(checks);
        out.dataset.phase2 = String(phase2Checks);
        out.dataset.errors = String(errs.length);
        document.body.appendChild(out);
      });
  }

  function parseHash() {
    var out = {};
    (window.location.hash || "").replace(/^#/, "").split("&").forEach(function (kv) {
      var idx = kv.indexOf("=");
      if (idx > 0) out[kv.slice(0, idx)] = decodeURIComponent(kv.slice(idx + 1));
    });
    return out;
  }

  // Boot
  wireUI();
  var hq = parseHash();
  loadInitialData().then(function () {
    if (hq.selftest === "1") {
      return runSelfTest();
    }
    var chain = Promise.resolve();
    if (hq.inv != null && st.investigations[Number(hq.inv)]) {
      chain = chain.then(function () { return loadInvestigation(Number(hq.inv), Number(hq.step || 0)); });
    } else if (hq.mode || hq.root) {
      chain = chain.then(function () {
        var mode = hq.mode || "imports";
        var root = hq.root || "Main";
        var depth = Number(hq.depth || (mode === "imports" && root === "Main" ? 3 : 2));
        setCenterView(hq.view === "treemap" ? "treemap" : "graph");
        return Promise.all([
          loadSubgraph(root, mode, depth, { selectId: hq.select || root }),
          inspectEntity(hq.select || root, mode === "tcb" ? "tcb" : "module")
        ]);
      });
    }
    if (hq.rtab) {
      chain = chain.then(function () { setRightTab(hq.rtab); });
    }
    if (hq.p3) {
      // deep link: #p3=kernel|flirt|annot&sub=<subview>[&node=<decl>][&path=<id>]
      chain = chain.then(function () {
        var ps = window.Phase3.state;
        if (hq.node) ps.k.domNode = hq.node;
        if (hq.path) ps.k.pathId = Number(hq.path) || 0;
        return window.Phase3.open(hq.p3, hq.sub || "");
      });
    }
    if (hq.flag) {
      chain = chain.then(function () {
        st.activeFlag = hq.flag;
        renderForensicChipStates();
        return runSearch();
      });
    }
    return chain;
  });
})();
