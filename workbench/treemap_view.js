/* ==========================================================================
   treemap_view.js — Interactive Squarified Namespace Reality Check Treemap
   Visualizes all 175,187 files / 17.37M lines / 1.06M decls from real
   namespace_stats, exposing folder-name vs. inner-declaration misnomers.
   ========================================================================== */
"use strict";

window.TreemapView = (function () {
  var PALETTE = {
    Development:       { fill: "#14263b", stroke: "#2d5580", accent: "#38bdf8" },
    Formalism:         { fill: "#102d2a", stroke: "#1f6158", accent: "#2dd4bf" },
    GroundTheory:      { fill: "#282212", stroke: "#5c4a1d", accent: "#f59e0b" },
    ReciprocityTheory: { fill: "#182921", stroke: "#2c5e46", accent: "#34d399" },
    CompanionTheory:   { fill: "#24222c", stroke: "#484963", accent: "#94a3b8" },
    PositivityTheory:  { fill: "#2b191b", stroke: "#633238", accent: "#f87171" },
    Lemmata:           { fill: "#1a2433", stroke: "#3b506e", accent: "#7dd3fc" },
    Supplements:       { fill: "#112f22", stroke: "#286e4e", accent: "#34d399" },
    BuildAid:          { fill: "#2e1a15", stroke: "#693629", accent: "#fb923c" },
    Main:              { fill: "#112f22", stroke: "#34d399", accent: "#34d399" },
    Statements:        { fill: "#112f22", stroke: "#34d399", accent: "#34d399" }
  };

  function topLib(prefix) {
    return String(prefix || "").split(".")[0] || "Other";
  }

  function fmtInt(n) {
    if (n == null) return "0";
    return Number(n).toLocaleString("en-US");
  }

  function fmtCompact(n) {
    if (n >= 1e6) return (n / 1e6).toFixed(2) + "M";
    if (n >= 1e3) return (n / 1e3).toFixed(1) + "k";
    return String(n);
  }

  // Binary-split squarified layout (deterministic, zero deps, clean aspect ratios)
  function layoutRects(items, x, y, w, h, totalVal, out) {
    if (!items.length || w <= 1 || h <= 1 || totalVal <= 0) return;
    if (items.length === 1) {
      out.push({ item: items[0], x: x, y: y, w: w, h: h });
      return;
    }
    var half = totalVal / 2;
    var acc = 0;
    var split = 1;
    for (var i = 0; i < items.length - 1; i++) {
      acc += items[i]._val;
      split = i + 1;
      if (acc >= half) break;
    }
    var left = items.slice(0, split);
    var right = items.slice(split);
    var leftSum = left.reduce(function (s, it) { return s + it._val; }, 0);
    var rightSum = totalVal - leftSum;
    var frac = leftSum / totalVal;

    if (w >= h) {
      var lw = w * frac;
      layoutRects(left, x, y, lw, h, leftSum, out);
      layoutRects(right, x + lw, y, w - lw, h, rightSum, out);
    } else {
      var lh = h * frac;
      layoutRects(left, x, y, w, lh, leftSum, out);
      layoutRects(right, x, y + lh, w, h - lh, rightSum, out);
    }
  }

  function create(opts) {
    var canvas = opts.canvas;
    var tip = opts.tip;
    var onSelectNs = opts.onSelectNs || function () {};
    var state = {
      rows: [],
      metric: "module_count", // module_count | lines_wc | decl_count
      filterParent: null,     // null = all depth-2 (or depth-1 fallback)
      rects: [],
      hoverIdx: -1
    };

    function getDisplayItems() {
      var rows = state.rows || [];
      if (!rows.length) return [];
      var items;
      if (state.filterParent) {
        items = rows.filter(function (r) { return r.parent === state.filterParent; });
        if (!items.length) {
          items = rows.filter(function (r) { return r.prefix === state.filterParent; });
        }
      } else {
        // Prefer depth-2 leaves + depth-1 folders that have no depth-2 children
        var hasChild = {};
        rows.forEach(function (r) { if (r.depth === 2 && r.parent) hasChild[r.parent] = true; });
        items = rows.filter(function (r) {
          return r.depth === 2 || (r.depth === 1 && !hasChild[r.prefix]);
        });
        if (!items.length) items = rows.slice();
      }
      var metric = state.metric;
      var cleaned = items
        .map(function (r) {
          var v = Number(r[metric] || r.module_count || 0);
          return Object.assign({}, r, { _val: Math.max(0, v) });
        })
        .filter(function (r) { return r._val > 0; });
      cleaned.sort(function (a, b) { return b._val - a._val; });
      return cleaned;
    }

    function draw() {
      if (!canvas) return;
      var w = canvas.clientWidth;
      var h = canvas.clientHeight;
      if (!w || !h) return;
      var dpr = window.devicePixelRatio || 1;
      if (canvas.width !== Math.round(w * dpr) || canvas.height !== Math.round(h * dpr)) {
        canvas.width = Math.round(w * dpr);
        canvas.height = Math.round(h * dpr);
      }
      var ctx = canvas.getContext("2d");
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx.clearRect(0, 0, w, h);

      var items = getDisplayItems();
      var total = items.reduce(function (s, it) { return s + it._val; }, 0);
      var rects = [];
      layoutRects(items, 0, 0, w, h, total, rects);
      state.rects = rects;

      rects.forEach(function (rc, idx) {
        var it = rc.item;
        var lib = topLib(it.prefix);
        var pal = PALETTE[lib] || { fill: "#18202c", stroke: "#314059", accent: "#94a3b8" };
        var isMisnomer = it.prefix === "Development.AbelianVarietyTheory";
        var pad = 2;
        var rx = rc.x + pad;
        var ry = rc.y + pad;
        var rw = Math.max(0, rc.w - pad * 2);
        var rh = Math.max(0, rc.h - pad * 2);
        if (rw < 1 || rh < 1) return;

        ctx.fillStyle = isMisnomer ? "#241d11" : pal.fill;
        ctx.fillRect(rx, ry, rw, rh);

        ctx.strokeStyle = idx === state.hoverIdx ? "#38bdf8" : (isMisnomer ? "#d97706" : pal.stroke);
        ctx.lineWidth = idx === state.hoverIdx ? 2 : 1;
        ctx.strokeRect(rx + 0.5, ry + 0.5, rw - 1, rh - 1);

        // Top stripe for misnomer / big tiles
        if (rh > 26 && rw > 40) {
          ctx.fillStyle = isMisnomer ? "#f59e0b" : pal.accent;
          ctx.fillRect(rx, ry, rw, 2.5);
        }

        // Labels inside tiles when space allows
        var pct = total > 0 ? (it._val / total * 100) : 0;
        if (rw > 72 && rh > 34) {
          ctx.save();
          ctx.beginPath();
          ctx.rect(rx + 5, ry + 5, rw - 10, rh - 10);
          ctx.clip();

          ctx.font = "600 11.5px ui-monospace, Menlo, Consolas, monospace";
          ctx.fillStyle = "#e6edf7";
          var shortName = it.prefix.replace(/^Development\./, "Dev.");
          ctx.fillText(shortName, rx + 7, ry + 19);

          ctx.font = "11px ui-monospace, Menlo, Consolas, monospace";
          ctx.fillStyle = isMisnomer ? "#fbbf24" : "#9eb0cc";
          var mLabel = state.metric === "lines_wc"
            ? fmtCompact(it.lines_wc) + " lines"
            : (state.metric === "decl_count" ? fmtCompact(it.decl_count) + " decls" : fmtInt(it.module_count) + " files");
          ctx.fillText(mLabel + " (" + pct.toFixed(1) + "%)", rx + 7, ry + 35);

          // Show top actual inner declaration namespaces on large tiles!
          if (rh > 66 && rw > 150) {
            var topPfx = it.top_decl_prefixes || [];
            if (isMisnomer) {
              ctx.font = "600 11px -apple-system, sans-serif";
              ctx.fillStyle = "#fde68a";
              ctx.fillText("MISNOMER: folder says AbelianVarietyTheory,", rx + 7, ry + 56);
              ctx.fillText("but actual inner Lean namespaces are:", rx + 7, ry + 72);
              if (rh > 120 && topPfx.length) {
                ctx.font = "11px ui-monospace, Menlo, Consolas, monospace";
                topPfx.slice(0, 6).forEach(function (tp, k) {
                  var nm = typeof tp === "string" ? tp : (tp.prefix || tp.name || tp[0] || "");
                  var cn = (tp && typeof tp === "object" && !Array.isArray(tp)) ? (tp.count || tp.decls) : (Array.isArray(tp) ? tp[1] : null);
                  ctx.fillStyle = k === 0 ? "#fbbf24" : "#c6d0e0";
                  ctx.fillText("• " + nm + (cn ? " (" + fmtInt(cn) + " decls)" : ""), rx + 11, ry + 96 + k * 18);
                });
                ctx.fillStyle = "#8392ab";
                ctx.font = "10.5px ui-monospace, Menlo, Consolas, monospace";
                ctx.fillText(fmtInt(it.lines_wc) + " lines · " + fmtInt(it.decl_count) + " decls · click to browse", rx + 7, ry + 96 + Math.min(6, topPfx.length) * 18 + 14);
              }
            } else if (topPfx.length) {
              ctx.font = "10.5px ui-monospace, Menlo, Consolas, monospace";
              ctx.fillStyle = "#8392ab";
              var names = topPfx.slice(0, 2).map(function (p) {
                return typeof p === "string" ? p : (p.prefix || p.name || p[0] || "");
              }).filter(Boolean).join(", ");
              if (names) ctx.fillText("inner: " + names, rx + 7, ry + 53);
              if (rh > 100 && rw > 180) {
                ctx.fillStyle = "#6b7b95";
                ctx.fillText(fmtCompact(it.lines_wc) + "L · " + fmtCompact(it.decl_count) + " decls", rx + 7, ry + 70);
              }
            }
          }
          ctx.restore();
        }
      });
    }

    function hitTest(mx, my) {
      for (var i = 0; i < state.rects.length; i++) {
        var r = state.rects[i];
        if (mx >= r.x && mx <= r.x + r.w && my >= r.y && my <= r.y + r.h) return i;
      }
      return -1;
    }

    function formatTopPrefixes(topPfx) {
      if (!topPfx || !topPfx.length) return "—";
      return topPfx.slice(0, 4).map(function (p) {
        if (typeof p === "string") return p;
        if (Array.isArray(p)) return p[0] + " (" + fmtCompact(p[1]) + ")";
        return (p.prefix || p.name || "?") + (p.count ? " (" + fmtCompact(p.count) + ")" : "");
      }).join(", ");
    }

    canvas.addEventListener("mousemove", function (ev) {
      var rect = canvas.getBoundingClientRect();
      var mx = ev.clientX - rect.left;
      var my = ev.clientY - rect.top;
      var idx = hitTest(mx, my);
      if (idx !== state.hoverIdx) {
        state.hoverIdx = idx;
        draw();
      }
      if (idx >= 0 && tip) {
        var it = state.rects[idx].item;
        var tot = state.rects.reduce(function (s, r) { return s + r.item._val; }, 0);
        var pct = tot ? (it._val / tot * 100).toFixed(2) : "0";
        var html =
          "<div style='font-family:var(--mono);font-weight:700;color:#fff;margin-bottom:4px'>" + it.prefix + "</div>" +
          "<div style='font-family:var(--mono);font-size:11px;color:#b6c4da'>" +
          "Files: <b>" + fmtInt(it.module_count) + "</b> · Lines: <b>" + fmtInt(it.lines_wc) + "</b> · Decls: <b>" + fmtInt(it.decl_count) + "</b><br>" +
          "Share of view: <b>" + pct + "%</b> · Shims: " + fmtInt(it.shim_count) + " · Forensic hits: " + fmtInt(it.forensic_hit_count) + "<br>" +
          "<span style='color:#f59e0b'>Inner decl prefixes:</span> " + formatTopPrefixes(it.top_decl_prefixes) +
          "</div>" +
          "<div style='color:#8392ab;font-size:10.5px;margin-top:4px'>Click tile to inspect top modules in this namespace</div>";
        tip.innerHTML = html;
        tip.style.display = "block";
        var tx = Math.min(mx + 14, Math.max(8, rect.width - 370));
        var ty = Math.min(my + 14, Math.max(8, rect.height - 130));
        tip.style.left = tx + "px";
        tip.style.top = ty + "px";
      } else if (tip) {
        tip.style.display = "none";
      }
    });

    canvas.addEventListener("mouseleave", function () {
      state.hoverIdx = -1;
      if (tip) tip.style.display = "none";
      draw();
    });

    canvas.addEventListener("click", function (ev) {
      var rect = canvas.getBoundingClientRect();
      var idx = hitTest(ev.clientX - rect.left, ev.clientY - rect.top);
      if (idx >= 0) {
        onSelectNs(state.rects[idx].item);
      }
    });

    return {
      setData: function (rows) { state.rows = rows || []; draw(); },
      setMetric: function (m) { state.metric = m || "module_count"; draw(); },
      setFilterParent: function (p) { state.filterParent = p || null; draw(); },
      draw: draw
    };
  }

  return { create: create };
})();
