/* ==========================================================================
   graph_view.js — Ghidra / Binary Ninja style layered DAG Graph View
   Pure SVG + Canvas minimap, pan/zoom, barycenter crossing minimization,
   basic-block node cards, edge routing, dominator highlighting, expand hook.
   ========================================================================== */
"use strict";

window.GraphView = (function () {
  var NS = "http://www.w3.org/2000/svg";
  var NODE_W = 224;
  var NODE_H = 72;
  var GAP_X = 36;
  var GAP_Y = 74;

  var ROLE_STYLE = {
    entry:     { hdr: "#0e3828", bar: "#34d399", badge: "ENTRY",   bcol: "#34d399" },
    forensic:  { hdr: "#3b151a", bar: "#f87171", badge: "TAINT",   bcol: "#f87171" },
    slow:      { hdr: "#38250a", bar: "#f59e0b", badge: "HOTSPOT", bcol: "#f59e0b" },
    crux:      { hdr: "#0e3330", bar: "#2dd4bf", badge: "CRUX",    bcol: "#2dd4bf" },
    classical: { hdr: "#132944", bar: "#60a5fa", badge: "CLASSIC", bcol: "#60a5fa" },
    tcb_def:   { hdr: "#0e2e44", bar: "#38bdf8", badge: "DEF",     bcol: "#38bdf8" },
    tcb_thm:   { hdr: "#1b2333", bar: "#94a3b8", badge: "THM",     bcol: "#94a3b8" },
    horn_prop: { hdr: "#0d2d33", bar: "#2dd4bf", badge: "PROP",    bcol: "#2dd4bf" },
    hub:       { hdr: "#17273d", bar: "#7dd3fc", badge: "HUB",     bcol: "#7dd3fc" },
    normal:    { hdr: "#171f2d", bar: "#58657c", badge: "MOD",     bcol: "#8392ab" }
  };

  function svgEl(tag, attrs) {
    var el = document.createElementNS(NS, tag);
    if (attrs) {
      Object.keys(attrs).forEach(function (k) { el.setAttribute(k, String(attrs[k])); });
    }
    return el;
  }

  function clamp(v, a, b) { return v < a ? a : (v > b ? b : v); }

  function fmtNum(n) {
    if (n == null || isNaN(n)) return "—";
    if (n >= 1000000) return (n / 1000000).toFixed(2) + "M";
    if (n >= 10000) return (n / 1000).toFixed(1) + "k";
    if (n >= 1000) return (n / 1000).toFixed(2) + "k";
    return String(n);
  }

  function trunc(s, n) {
    s = String(s || "");
    return s.length <= n ? s : s.slice(0, n - 1) + "…";
  }

  function create(opts) {
    var viewport = opts.viewport;
    var svg = opts.svg;
    var minimapCanvas = opts.minimapCanvas;
    var minimapWrap = opts.minimapWrap;
    var onSelect = opts.onSelect || function () {};
    var onExpand = opts.onExpand || function () {};

    var state = {
      data: { nodes: [], edges: [], mode: "imports", root: "" },
      pos: {},         // id -> {x, y}
      bounds: { minX: 0, minY: 0, maxX: 800, maxY: 600 },
      selectedId: null,
      showEdgeLabels: true,
      highlightDom: false,
      tx: 40,
      ty: 40,
      scale: 1
    };

    var gRoot = null;
    var nodeEls = {};
    var edgeEls = [];

    function initSvgDefs() {
      svg.innerHTML = "";
      var defs = svgEl("defs");
      var markers = [
        ["arr-import",    "#506587"],
        ["arr-dom",       "#34d399"],
        ["arr-taint",     "#f87171"],
        ["arr-horn_req",  "#f59e0b"],
        ["arr-horn_prov", "#2dd4bf"],
        ["arr-tcb",       "#4b7bb5"],
        ["arr-tcb_val",   "#64748b"],
        ["arr-hot",       "#38bdf8"]
      ];
      markers.forEach(function (m) {
        var mk = svgEl("marker", {
          id: m[0], viewBox: "0 0 10 10", refX: "9", refY: "5",
          markerWidth: "6", markerHeight: "6", orient: "auto"
        });
        mk.appendChild(svgEl("path", { d: "M0,1 L10,5 L0,9 z", fill: m[1] }));
        defs.appendChild(mk);
      });
      svg.appendChild(defs);
      gRoot = svgEl("g", { id: "gWorld" });
      svg.appendChild(gRoot);
    }

    // Layered DAG layout with barycenter crossing minimization
    function layout(data) {
      var nodes = data.nodes || [];
      var edges = data.edges || [];
      var byId = {};
      var inAdj = {};
      var outAdj = {};
      nodes.forEach(function (n) {
        byId[n.id] = n;
        inAdj[n.id] = [];
        outAdj[n.id] = [];
      });
      edges.forEach(function (e) {
        if (byId[e.src] && byId[e.dst] && e.src !== e.dst) {
          outAdj[e.src].push(e.dst);
          inAdj[e.dst].push(e.src);
        }
      });

      // Assign layers
      var layerOf = {};
      var hasExplicit = nodes.length > 0 && nodes.every(function (n) { return typeof n.layer === "number"; });
      if (hasExplicit) {
        nodes.forEach(function (n) { layerOf[n.id] = n.layer; });
      } else {
        // Topological longest-path layering (robust to cycles)
        var indeg = {};
        var q = [];
        nodes.forEach(function (n) {
          indeg[n.id] = inAdj[n.id].length;
          if (indeg[n.id] === 0) {
            layerOf[n.id] = 0;
            q.push(n.id);
          }
        });
        var head = 0;
        while (head < q.length) {
          var u = q[head++];
          var lu = layerOf[u] || 0;
          outAdj[u].forEach(function (v) {
            if (layerOf[v] == null || layerOf[v] < lu + 1) layerOf[v] = lu + 1;
            indeg[v]--;
            if (indeg[v] === 0) q.push(v);
          });
        }
        // Any nodes left in cycles get placed at layer 0
        nodes.forEach(function (n) { if (layerOf[n.id] == null) layerOf[n.id] = 0; });
      }

      // Normalize layers to 0..L
      var minL = Infinity;
      nodes.forEach(function (n) { if (layerOf[n.id] < minL) minL = layerOf[n.id]; });
      if (!isFinite(minL)) minL = 0;
      var layers = {};
      var maxL = 0;
      nodes.forEach(function (n) {
        var l = layerOf[n.id] - minL;
        layerOf[n.id] = l;
        if (l > maxL) maxL = l;
        if (!layers[l]) layers[l] = [];
        layers[l].push(n.id);
      });

      // Initial deterministic sort within each layer: root first, then high dom/fan_in, then name
      for (var l = 0; l <= maxL; l++) {
        if (!layers[l]) continue;
        layers[l].sort(function (a, b) {
          var na = byId[a], nb = byId[b];
          if (na.is_root !== nb.is_root) return na.is_root ? -1 : 1;
          var da = (na.metrics && na.metrics.dom) || 0;
          var db = (nb.metrics && nb.metrics.dom) || 0;
          if (da !== db) return db - da;
          return a < b ? -1 : (a > b ? 1 : 0);
        });
      }

      // Barycenter sweeps (3 passes) to minimize edge crossings
      function orderOf(l) {
        var m = {};
        (layers[l] || []).forEach(function (id, idx) { m[id] = idx; });
        return m;
      }
      for (var pass = 0; pass < 3; pass++) {
        // Top-down
        for (l = 1; l <= maxL; l++) {
          if (!layers[l] || layers[l].length < 2) continue;
          var prevOrd = orderOf(l - 1);
          var score = {};
          layers[l].forEach(function (id, idx) {
            var sum = 0, cnt = 0;
            inAdj[id].forEach(function (p) { if (prevOrd[p] != null) { sum += prevOrd[p]; cnt++; } });
            score[id] = cnt ? sum / cnt : idx;
          });
          layers[l].sort(function (a, b) { return score[a] - score[b]; });
        }
        // Bottom-up
        for (l = maxL - 1; l >= 0; l--) {
          if (!layers[l] || layers[l].length < 2) continue;
          var nextOrd = orderOf(l + 1);
          var score2 = {};
          layers[l].forEach(function (id, idx) {
            var sum = 0, cnt = 0;
            outAdj[id].forEach(function (c) { if (nextOrd[c] != null) { sum += nextOrd[c]; cnt++; } });
            score2[id] = cnt ? sum / cnt : idx;
          });
          layers[l].sort(function (a, b) { return score2[a] - score2[b]; });
        }
      }

      // Wrap very wide layers (>8 nodes) into sub-rows so graphs stay legible instead of ultra-wide
      var pos = {};
      var curY = 40;
      var maxCols = 7;
      var minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;

      for (l = 0; l <= maxL; l++) {
        var arr = layers[l] || [];
        if (!arr.length) continue;
        var rows = Math.ceil(arr.length / maxCols);
        for (var r = 0; r < rows; r++) {
          var slice = arr.slice(r * maxCols, (r + 1) * maxCols);
          var rowW = slice.length * NODE_W + (slice.length - 1) * GAP_X;
          var startX = -rowW / 2;
          slice.forEach(function (id, idx) {
            var x = startX + idx * (NODE_W + GAP_X);
            var y = curY;
            pos[id] = { x: x, y: y };
            if (x < minX) minX = x;
            if (y < minY) minY = y;
            if (x + NODE_W > maxX) maxX = x + NODE_W;
            if (y + NODE_H > maxY) maxY = y + NODE_H;
          });
          curY += NODE_H + (r < rows - 1 ? 26 : GAP_Y);
        }
      }

      if (!isFinite(minX)) { minX = 0; minY = 0; maxX = 400; maxY = 300; }
      state.pos = pos;
      state.bounds = { minX: minX - 60, minY: minY - 60, maxX: maxX + 60, maxY: maxY + 60 };
    }

    function applyTransform() {
      if (!gRoot) return;
      gRoot.setAttribute("transform", "translate(" + state.tx.toFixed(1) + "," + state.ty.toFixed(1) + ") scale(" + state.scale.toFixed(4) + ")");
      drawMinimap();
    }

    function fit(animate) {
      var w = viewport.clientWidth || 700;
      var h = viewport.clientHeight || 500;
      var b = state.bounds;
      var bw = Math.max(100, b.maxX - b.minX);
      var bh = Math.max(100, b.maxY - b.minY);
      var s = clamp(Math.min(w / bw, h / bh) * 0.92, 0.16, 1.25);
      state.scale = s;
      state.tx = w / 2 - ((b.minX + b.maxX) / 2) * s;
      state.ty = h / 2 - ((b.minY + b.maxY) / 2) * s;
      applyTransform();
    }

    function focusNode(id) {
      var p = state.pos[id];
      if (!p) return;
      var w = viewport.clientWidth || 700;
      var h = viewport.clientHeight || 500;
      state.scale = clamp(Math.max(state.scale, 0.85), 0.5, 1.35);
      state.tx = w / 2 - (p.x + NODE_W / 2) * state.scale;
      state.ty = h / 2 - (p.y + NODE_H / 2) * state.scale;
      applyTransform();
    }

    function zoomAt(cx, cy, factor) {
      var next = clamp(state.scale * factor, 0.12, 2.5);
      var ratio = next / state.scale;
      state.tx = cx - (cx - state.tx) * ratio;
      state.ty = cy - (cy - state.ty) * ratio;
      state.scale = next;
      applyTransform();
    }

    function buildMetricsText(n) {
      var m = n.metrics || {};
      if (n.kind === "horn_prop") return "Prop / logical contract";
      if (n.kind === "horn_thm") {
        var pts = [];
        if (m.reqs != null) pts.push("req:" + m.reqs);
        if (m.dom) pts.push("dom:" + fmtNum(m.dom));
        if (m.lines) pts.push(m.lines + "L");
        return pts.join("  ");
      }
      if (n.kind === "tcb_def" || n.kind === "tcb_thm") {
        var tp = [];
        if (m.depth != null && m.depth >= 0) tp.push("d_rh:" + m.depth);
        if (m.dom) tp.push("dom:" + fmtNum(m.dom));
        if (m.fi != null) tp.push("in:" + fmtNum(m.fi));
        if (m.fo != null) tp.push("out:" + fmtNum(m.fo));
        return tp.join("  ");
      }
      var parts = [];
      if (m.lines != null) parts.push(fmtNum(m.lines) + "L");
      if (m.dom != null && m.dom > 0) parts.push("dom:" + fmtNum(m.dom));
      if (m.fi != null) parts.push("in:" + fmtNum(m.fi));
      if (m.fo != null) parts.push("out:" + fmtNum(m.fo));
      return parts.join("  ");
    }

    function render(data, keepSelect) {
      state.data = data || { nodes: [], edges: [], mode: "imports", root: "" };
      if (!keepSelect) state.selectedId = null;
      initSvgDefs();
      layout(state.data);

      var gEdges = svgEl("g", { class: "g-edges" });
      var gLabels = svgEl("g", { class: "g-labels" });
      var gNodes = svgEl("g", { class: "g-nodes" });
      gRoot.appendChild(gEdges);
      gRoot.appendChild(gLabels);
      gRoot.appendChild(gNodes);

      nodeEls = {};
      edgeEls = [];

      // Draw edges
      (state.data.edges || []).forEach(function (e) {
        var pa = state.pos[e.src];
        var pb = state.pos[e.dst];
        if (!pa || !pb) return;
        var ax = pa.x + NODE_W / 2;
        var ay = pa.y + NODE_H;
        var bx = pb.x + NODE_W / 2;
        var by = pb.y;
        var dStr;
        var lx, ly;

        if (pb.y >= pa.y + NODE_H - 4) {
          // Standard downward edge
          var dy = Math.max(24, (by - ay) * 0.5);
          dStr = "M" + ax.toFixed(1) + "," + ay.toFixed(1) +
                 " C" + ax.toFixed(1) + "," + (ay + dy).toFixed(1) +
                 " " + bx.toFixed(1) + "," + (by - dy).toFixed(1) +
                 " " + bx.toFixed(1) + "," + (by - 2).toFixed(1);
          lx = (ax + bx) / 2;
          ly = (ay + by) / 2;
        } else if (Math.abs(pa.y - pb.y) < 10) {
          // Same-row horizontal arch
          var sx = ax < bx ? pa.x + NODE_W : pa.x;
          var tx = ax < bx ? pb.x : pb.x + NODE_W;
          var sy = pa.y + NODE_H / 2;
          var arch = -26;
          dStr = "M" + sx.toFixed(1) + "," + sy.toFixed(1) +
                 " Q" + ((sx + tx) / 2).toFixed(1) + "," + (sy + arch).toFixed(1) +
                 " " + tx.toFixed(1) + "," + sy.toFixed(1);
          lx = (sx + tx) / 2;
          ly = sy + arch * 0.65;
        } else {
          // Upward / back edge (route around side cleanly)
          ay = pa.y;
          by = pb.y + NODE_H;
          var side = (ax >= bx ? 1 : -1) * 44;
          dStr = "M" + ax.toFixed(1) + "," + ay.toFixed(1) +
                 " C" + (ax + side).toFixed(1) + "," + (ay - 30).toFixed(1) +
                 " " + (bx + side).toFixed(1) + "," + (by + 30).toFixed(1) +
                 " " + bx.toFixed(1) + "," + (by + 2).toFixed(1);
          lx = (ax + bx) / 2 + side * 0.7;
          ly = (ay + by) / 2;
        }

        var kind = e.kind || "import";
        var markerId = "arr-" + (["dom", "taint", "horn_req", "horn_prov", "tcb", "tcb_val"].indexOf(kind) >= 0 ? kind : "import");
        var path = svgEl("path", {
          d: dStr,
          class: "g-edge " + kind,
          "marker-end": "url(#" + markerId + ")"
        });
        gEdges.appendChild(path);

        var lbl = null;
        if (e.label) {
          lbl = svgEl("text", {
            x: lx.toFixed(1),
            y: (ly - 3).toFixed(1),
            "text-anchor": "middle",
            class: "g-elabel"
          });
          lbl.textContent = e.label;
          lbl.style.display = state.showEdgeLabels ? "" : "none";
          gLabels.appendChild(lbl);
        }

        edgeEls.push({ edge: e, path: path, lbl: lbl, defaultMarker: markerId });
      });

      // Draw basic-block nodes
      (state.data.nodes || []).forEach(function (n) {
        var p = state.pos[n.id];
        if (!p) return;
        var rs = ROLE_STYLE[n.role] || ROLE_STYLE.normal;
        var g = svgEl("g", {
          class: "g-node" + (n.is_root ? " root" : ""),
          transform: "translate(" + p.x.toFixed(1) + "," + p.y.toFixed(1) + ")",
          "data-id": n.id
        });

        // Main block body
        g.appendChild(svgEl("rect", { width: NODE_W, height: NODE_H, class: "blk-bg" }));
        // Top header bar (Binary Ninja / Ghidra block header)
        g.appendChild(svgEl("rect", { x: 1, y: 1, width: NODE_W - 2, height: 20, fill: rs.hdr, class: "blk-hdr" }));
        // Left semantic indicator bar
        g.appendChild(svgEl("rect", { x: 1, y: 1, width: 3.5, height: NODE_H - 2, fill: rs.bar, rx: 1.5 }));
        // Header bottom hairline
        g.appendChild(svgEl("line", { x1: 1, y1: 21, x2: NODE_W - 1, y2: 21, stroke: "#263246", "stroke-width": 1 }));

        // Header badge (right) + sublabel (left)
        var badgeTxt = (n.flags && n.flags.length && n.role === "forensic") ? trunc(n.flags[0], 11) : rs.badge;
        var sub = svgEl("text", { x: 10, y: 14.5, class: "blk-sub" });
        sub.textContent = trunc(n.sublabel || n.kind || "", 22);
        g.appendChild(sub);

        var bdg = svgEl("text", { x: NODE_W - 8, y: 14.5, "text-anchor": "end", class: "blk-badge", fill: rs.bcol });
        bdg.textContent = badgeTxt;
        g.appendChild(bdg);

        // Main title
        var title = svgEl("text", { x: 10, y: 40, class: "blk-title" });
        title.textContent = trunc(n.label || n.id, 27);
        g.appendChild(title);

        // Bottom metric strip
        var meta = svgEl("text", { x: 10, y: 59, class: "blk-meta" });
        meta.textContent = trunc(buildMetricsText(n), 31);
        g.appendChild(meta);

        // Native tooltip with full name
        var tt = svgEl("title");
        tt.textContent = n.id + (n.flags && n.flags.length ? "  [" + n.flags.join(", ") + "]" : "");
        g.appendChild(tt);

        g.addEventListener("click", function (ev) {
          ev.stopPropagation();
          select(n.id);
          onSelect(n);
        });
        g.addEventListener("dblclick", function (ev) {
          ev.stopPropagation();
          onExpand(n);
        });

        gNodes.appendChild(g);
        nodeEls[n.id] = { node: n, el: g };
      });

      fit(false);
      updateHighlights();
    }

    function select(id) {
      state.selectedId = id;
      updateHighlights();
    }

    function setOptions(o) {
      if (o.showEdgeLabels != null) {
        state.showEdgeLabels = !!o.showEdgeLabels;
        edgeEls.forEach(function (it) {
          if (it.lbl) it.lbl.style.display = state.showEdgeLabels ? "" : "none";
        });
      }
      if (o.highlightDom != null) {
        state.highlightDom = !!o.highlightDom;
        updateHighlights();
      }
    }

    function updateHighlights() {
      var sel = state.selectedId;
      var neigh = {};
      if (sel) {
        neigh[sel] = true;
        edgeEls.forEach(function (it) {
          if (it.edge.src === sel || it.edge.dst === sel) {
            neigh[it.edge.src] = true;
            neigh[it.edge.dst] = true;
          }
        });
      }

      Object.keys(nodeEls).forEach(function (id) {
        var entry = nodeEls[id];
        var dim = false;
        if (state.highlightDom && !entry.node.on_dom_spine && !entry.node.on_main_path && !entry.node.is_root) {
          dim = true;
        }
        if (sel && !neigh[id] && !state.highlightDom) {
          dim = true;
        }
        entry.el.classList.toggle("selected", id === sel);
        entry.el.classList.toggle("dim", dim);
      });

      edgeEls.forEach(function (it) {
        var e = it.edge;
        var hot = sel && (e.src === sel || e.dst === sel);
        var dim = false;
        if (state.highlightDom && !e.is_dom && !e.is_highlight && e.kind !== "taint") {
          dim = true;
        } else if (sel && !hot && !state.highlightDom) {
          dim = true;
        }
        it.path.classList.toggle("hot", !!hot);
        it.path.classList.toggle("dim", dim);
        it.path.setAttribute("marker-end", "url(#" + (hot ? "arr-hot" : it.defaultMarker) + ")");
        if (it.lbl) it.lbl.classList.toggle("dim", dim);
      });

      drawMinimap();
    }

    function drawMinimap() {
      if (!minimapCanvas) return;
      var w = minimapCanvas.clientWidth;
      var h = minimapCanvas.clientHeight;
      if (!w || !h) return;
      var dpr = window.devicePixelRatio || 1;
      if (minimapCanvas.width !== Math.round(w * dpr) || minimapCanvas.height !== Math.round(h * dpr)) {
        minimapCanvas.width = Math.round(w * dpr);
        minimapCanvas.height = Math.round(h * dpr);
      }
      var ctx = minimapCanvas.getContext("2d");
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx.clearRect(0, 0, w, h);

      var b = state.bounds;
      var bw = Math.max(100, b.maxX - b.minX);
      var bh = Math.max(100, b.maxY - b.minY);
      var s = Math.min(w / bw, h / bh) * 0.92;
      var ox = (w - bw * s) / 2 - b.minX * s;
      var oy = (h - bh * s) / 2 - b.minY * s;

      // Edges
      ctx.strokeStyle = "rgba(100, 125, 160, 0.35)";
      ctx.lineWidth = 0.8;
      (state.data.edges || []).forEach(function (e) {
        var pa = state.pos[e.src], pb = state.pos[e.dst];
        if (!pa || !pb) return;
        ctx.beginPath();
        ctx.moveTo(ox + (pa.x + NODE_W / 2) * s, oy + (pa.y + NODE_H / 2) * s);
        ctx.lineTo(ox + (pb.x + NODE_W / 2) * s, oy + (pb.y + NODE_H / 2) * s);
        ctx.stroke();
      });

      // Nodes
      (state.data.nodes || []).forEach(function (n) {
        var p = state.pos[n.id];
        if (!p) return;
        var rs = ROLE_STYLE[n.role] || ROLE_STYLE.normal;
        ctx.fillStyle = n.id === state.selectedId ? "#ffffff" : rs.bar;
        ctx.fillRect(ox + p.x * s, oy + p.y * s, Math.max(3, NODE_W * s), Math.max(2, NODE_H * s));
      });

      // Viewport rect
      var vw = viewport.clientWidth || 700;
      var vh = viewport.clientHeight || 500;
      var vx0 = -state.tx / state.scale;
      var vy0 = -state.ty / state.scale;
      var vx1 = vx0 + vw / state.scale;
      var vy1 = vy0 + vh / state.scale;
      ctx.strokeStyle = "#38bdf8";
      ctx.lineWidth = 1.25;
      ctx.strokeRect(
        clamp(ox + vx0 * s, 0, w),
        clamp(oy + vy0 * s, 0, h),
        Math.min((vx1 - vx0) * s, w),
        Math.min((vy1 - vy0) * s, h)
      );

      state._mm = { ox: ox, oy: oy, s: s };
    }

    // Pan & Zoom handlers
    function wireInteractions() {
      var drag = null;
      viewport.addEventListener("wheel", function (ev) {
        ev.preventDefault();
        var r = viewport.getBoundingClientRect();
        var factor = Math.exp(-ev.deltaY * (ev.ctrlKey ? 0.01 : 0.0016));
        zoomAt(ev.clientX - r.left, ev.clientY - r.top, factor);
      }, { passive: false });

      viewport.addEventListener("pointerdown", function (ev) {
        if (ev.target.closest && (ev.target.closest("#graphZoomBtns") || ev.target.closest("#minimapWrap"))) return;
        if (ev.target.closest && ev.target.closest(".g-node")) return;
        drag = { x: ev.clientX, y: ev.clientY, tx: state.tx, ty: state.ty, moved: 0 };
        viewport.classList.add("grabbing");
        try { viewport.setPointerCapture(ev.pointerId); } catch (e) {}
      });
      viewport.addEventListener("pointermove", function (ev) {
        if (!drag) return;
        var dx = ev.clientX - drag.x;
        var dy = ev.clientY - drag.y;
        drag.moved = Math.max(drag.moved, Math.abs(dx) + Math.abs(dy));
        state.tx = drag.tx + dx;
        state.ty = drag.ty + dy;
        applyTransform();
      });
      function endDrag() {
        if (drag && drag.moved <= 4) {
          select(null);
        }
        drag = null;
        viewport.classList.remove("grabbing");
      }
      viewport.addEventListener("pointerup", endDrag);
      viewport.addEventListener("pointercancel", endDrag);

      if (minimapWrap) {
        minimapWrap.addEventListener("pointerdown", function (ev) {
          ev.stopPropagation();
          if (!state._mm) return;
          var r = minimapWrap.getBoundingClientRect();
          var wx = (ev.clientX - r.left - state._mm.ox) / state._mm.s;
          var wy = (ev.clientY - r.top - state._mm.oy) / state._mm.s;
          var vw = viewport.clientWidth || 700;
          var vh = viewport.clientHeight || 500;
          state.tx = vw / 2 - wx * state.scale;
          state.ty = vh / 2 - wy * state.scale;
          applyTransform();
        });
      }
    }

    wireInteractions();

    return {
      render: render,
      select: select,
      fit: fit,
      focusNode: focusNode,
      zoomIn: function () { zoomAt((viewport.clientWidth || 700) / 2, (viewport.clientHeight || 500) / 2, 1.3); },
      zoomOut: function () { zoomAt((viewport.clientWidth || 700) / 2, (viewport.clientHeight || 500) / 2, 1 / 1.3); },
      setOptions: setOptions,
      redrawMinimap: drawMinimap,
      getData: function () { return state.data; },
      getScale: function () { return state.scale; }
    };
  }

  return { create: create };
})();
