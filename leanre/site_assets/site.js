/* ==========================================================================
   leanre static SPA frontend (site.js)
   Zero-CDN, hash-routed, lazy-fetched, strictly XSS-safe.
   Compatible with manifest schema `leanre.site_manifest/1` (both RH showcase
   and generic / --demo Lean 4 repositories).
   ========================================================================== */
(function () {
  "use strict";

  const $ = (sel, root) => (root || document).querySelector(sel);
  const $$ = (sel, root) => Array.from((root || document).querySelectorAll(sel));

  // ---------- Network Telemetry & Lazy Cache ----------
  const state = {
    manifest: null,
    theme: "dark",
    route: { tab: "overview", sub: "", arg: "" },
    loadedBytes: 0,
    loadedShards: new Set(),
    cacheJson: new Map(),
    cacheText: new Map(),
    searchShards: new Map(),
    circuit: {
      mode: "macro",
      target: "",
      shard: null,
      history: [],
      scale: 1,
      tx: 16,
      ty: 16,
      filter: "",
      selectorFilter: "",
      selectedItem: null,
      hoveredItem: null,
      dragMoved: 0,
      stageWired: false
    },
    findingSlug: "",
    dossierMode: "analysis", // "analysis" | "research"
    dossierSlug: "",
    dossierQ: "",
    dossierCat: "all",
    bpId: "",
    bpQ: "",
    bpStatus: "all",
    bpSort: { key: "dom", dir: "desc" },
    bpPage: 0,
    bpSelectedNode: "",
    flirt: { status: "all", severity: "all", q: "", page: 0, expanded: "" },
    atlas: { hicMode: "ratio", showTerra: true, showStreaks: true, showNamed: true, twinScope: "all", twinSort: "jaccard" },
    portability: { island: "" },
    search: { q: "", scope: "all", lastShardPrefix: "" },
    selftestRunning: false
  };

  const SHOWCASE_ORDER = [
    { mode: "macro", target: "", label: "Macro Repo", desc: "Pillars, shared diamond, motifs & islands", tag: "Zoom 0" },
    { mode: "bundle", target: "OpenLiteratureStatements", label: "OpenLiteratureStatements", desc: "152/195 dropped consumers audit", tag: "Zoom 1" },
    { mode: "theorem", target: "llOf_alt", label: "llOf_alt", desc: "11 dropped binders in proof term", tag: "Zoom 2" },
    { mode: "bundle", target: "RealInAlt", label: "RealInAlt", desc: "3 conditional_prop fields", tag: "Zoom 1" },
    { mode: "bundle", target: "HypsAlt", label: "HypsAlt", desc: "46-field Pillar A record hub", tag: "Zoom 1" },
    { mode: "theorem", target: "ch_balance", label: "ch_balance", desc: "Exact Fourier balance (dom=66)", tag: "Zoom 2" },
    { mode: "theorem", target: "linkGLOBAL7_items", label: "linkGLOBAL7_items", desc: "Global bridge item wiring", tag: "Zoom 2" },
    { mode: "theorem", target: "sEEofTT", label: "sEEofTT", desc: "Evaluation tie (5 dif_pos sites)", tag: "Zoom 2" }
  ];

  // ---------- Security & Escaping Utilities ----------
  function escapeHtml(value) {
    return String(value == null ? "" : value)
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;")
      .replace(/'/g, "&#39;");
  }

  function safeHref(url) {
    const raw = String(url == null ? "" : url).trim();
    if (!raw || /[\x00-\x1f\x7f]/.test(raw)) return null;
    if (raw.startsWith("#")) return raw;
    if (/^https?:\/\//i.test(raw)) return raw;
    if (raw.startsWith("//")) return null;
    if (/^[a-zA-Z][a-zA-Z0-9+.-]*:/.test(raw)) return null;
    return raw;
  }

  function formatBytes(bytes) {
    const n = Number(bytes) || 0;
    if (n < 1024) return n + " B";
    if (n < 1024 * 1024) return (n / 1024).toFixed(1) + " KB";
    return (n / (1024 * 1024)).toFixed(2) + " MB";
  }

  function fmtInt(n) {
    const num = Number(n);
    if (!Number.isFinite(num)) return "—";
    return num.toLocaleString("en-US");
  }

  function shortName(name) {
    const s = String(name || "");
    const idx = s.lastIndexOf(".");
    return idx >= 0 ? s.slice(idx + 1) : s;
  }

  function el(tag, attrs, children) {
    const node = document.createElement(tag);
    if (attrs) {
      for (const [k, v] of Object.entries(attrs)) {
        if (v == null || v === false) continue;
        if (k === "className") node.className = String(v);
        else if (k === "textContent") node.textContent = String(v);
        else if (k === "style" && typeof v === "object") Object.assign(node.style, v);
        else if (k.startsWith("on") && typeof v === "function") node.addEventListener(k.slice(2).toLowerCase(), v);
        else if (k === "href") {
          const safe = safeHref(v);
          if (safe) node.setAttribute("href", safe);
        } else if (v === true) node.setAttribute(k, "");
        else node.setAttribute(k, String(v));
      }
    }
    if (children != null) {
      const list = Array.isArray(children) ? children : [children];
      for (const ch of list) {
        if (ch == null || ch === false) continue;
        node.appendChild(typeof ch === "string" ? document.createTextNode(ch) : ch);
      }
    }
    return node;
  }

  function clearEl(node) {
    while (node && node.firstChild) node.removeChild(node.firstChild);
  }

  function normalizeRelPath(p) {
    const s = String(p || "").trim();
    if (!s) return "";
    if (s.startsWith("./")) return s;
    return "./" + s.replace(/^\/+/, "");
  }

  function updateNetBadge() {
    const badge = $("#netBadge");
    if (!badge) return;
    const count = state.loadedShards.size;
    badge.textContent = "loaded: " + formatBytes(state.loadedBytes) + " · " + count + (count === 1 ? " shard" : " shards");
  }

  function recordLoad(key, byteLen) {
    if (!state.loadedShards.has(key)) {
      state.loadedShards.add(key);
      state.loadedBytes += Math.max(0, Number(byteLen) || 0);
      updateNetBadge();
    }
  }

  async function fetchText(relPath) {
    const key = normalizeRelPath(relPath);
    if (!key) throw new Error("Empty shard path");
    if (state.cacheText.has(key)) return state.cacheText.get(key);
    const resp = await fetch(key, { credentials: "same-origin" });
    if (!resp.ok) throw new Error("HTTP " + resp.status + " for " + key);
    const txt = await resp.text();
    const blen = new TextEncoder().encode(txt).length;
    recordLoad(key, blen);
    state.cacheText.set(key, txt);
    return txt;
  }

  async function fetchJson(relPath) {
    const key = normalizeRelPath(relPath);
    if (!key) throw new Error("Empty shard path");
    if (state.cacheJson.has(key)) return state.cacheJson.get(key);
    const resp = await fetch(key, { credentials: "same-origin" });
    if (!resp.ok) throw new Error("HTTP " + resp.status + " for " + key);
    const txt = await resp.text();
    const blen = new TextEncoder().encode(txt).length;
    recordLoad(key, blen);
    const obj = JSON.parse(txt);
    state.cacheJson.set(key, obj);
    return obj;
  }

  // ---------- Pinned GitHub Link Builder ----------
  function buildGithubUrl(pathOrAnchor, lineOpt) {
    const m = state.manifest;
    if (!m || !m.repo_url) return null;
    const base = safeHref(String(m.repo_url).replace(/\/+$/, ""));
    if (!base || !/^https?:\/\//i.test(base)) return null;
    const commit = String(m.pinned_commit || "main").trim();
    const prefix = String(m.src_prefix || "").replace(/^\/+/, "");
    let raw = String(pathOrAnchor || "").trim();
    if (!raw) return null;

    let frag = "";
    const mHash = raw.match(/^([^#]+)#L(\d+)(?:-L?(\d+))?$/);
    const mCol = raw.match(/^([^:]+):(\d+)(?:-(\d+))?$/);
    if (mHash) {
      raw = mHash[1];
      frag = "#L" + mHash[2] + (mHash[3] ? "-L" + mHash[3] : "");
    } else if (mCol) {
      raw = mCol[1];
      frag = "#L" + mCol[2] + (mCol[3] ? "-L" + mCol[3] : "");
    }
    if (!frag && lineOpt && Number(lineOpt) > 0) {
      frag = "#L" + Math.floor(Number(lineOpt));
    }

    raw = raw.replace(/^\/+/, "");
    if (raw.includes("..")) return null;
    // Convert module name like Development.Foo.Bar into Development/Foo/Bar.lean
    if (!raw.endsWith(".lean") && !raw.includes("/") && /^[A-Za-z0-9_'.]+$/.test(raw)) {
      raw = raw.replace(/\./g, "/") + ".lean";
    }
    if (prefix && !raw.startsWith(prefix)) {
      raw = prefix + raw;
    }
    return safeHref(base + "/blob/" + encodeURIComponent(commit) + "/" + raw + frag);
  }

  function makeGithubAnchor(pathOrAnchor, lineOpt, labelOpt) {
    const url = buildGithubUrl(pathOrAnchor, lineOpt);
    const text = labelOpt || (pathOrAnchor ? String(pathOrAnchor) + (lineOpt && !String(pathOrAnchor).includes(":") && !String(pathOrAnchor).includes("#L") ? ":" + lineOpt : "") : "");
    if (!url) return el("code", { textContent: text || "—" });
    return el("a", { href: url, target: "_blank", rel: "noopener noreferrer", className: "mono", textContent: text });
  }

  // ---------- Strict XSS-Safe SVG Mounter (DOMParser + Allowlist Strip) ----------
  const FORBIDDEN_SVG_TAGS = new Set(["script", "foreignobject", "iframe", "object", "embed", "link", "meta", "audio", "video"]);

  function sanitizeSvgTree(rootEl) {
    const stack = [rootEl];
    while (stack.length) {
      const node = stack.pop();
      if (!node || node.nodeType !== 1) continue;
      const tag = String(node.localName || node.tagName || "").toLowerCase();
      if (FORBIDDEN_SVG_TAGS.has(tag)) {
        node.remove();
        continue;
      }
      const attrs = Array.from(node.attributes || []);
      for (const attr of attrs) {
        const name = attr.name.toLowerCase();
        const val = attr.value || "";
        if (name.startsWith("on") || name === "srcdoc") {
          node.removeAttribute(attr.name);
        } else if (name === "href" || name === "xlink:href") {
          if (!val.trim().startsWith("#")) node.removeAttribute(attr.name);
        } else if (/javascript:|vbscript:|data:text\/html/i.test(val)) {
          node.removeAttribute(attr.name);
        }
      }
      for (const ch of Array.from(node.children || [])) {
        stack.push(ch);
      }
    }
  }

  function mountSafeSvg(container, svgText) {
    clearEl(container);
    if (!svgText || typeof svgText !== "string") return null;
    const parser = new DOMParser();
    const doc = parser.parseFromString(svgText, "image/svg+xml");
    if (doc.querySelector("parsererror")) {
      container.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "SVG parse error" }),
        el("p", { textContent: "The circuit shard did not contain well-formed SVG XML." })
      ]));
      return null;
    }
    const svgEl = doc.documentElement;
    if (!svgEl || String(svgEl.localName || "").toLowerCase() !== "svg") return null;
    sanitizeSvgTree(svgEl);
    const imported = document.importNode(svgEl, true);
    container.appendChild(imported);
    return imported;
  }

  // ---------- Zero-CDN Strict XSS-Safe Markdown & Math Renderer ----------
  function prettifyMath(escapedTex) {
    let s = escapedTex;
    s = s.replace(/\\operatorname\{([^}]+)\}/g, "$1");
    s = s.replace(/\\(?:mathrm|text|mathbf|mathcal|mathsf)\{([^}]+)\}/g, "$1");
    s = s.replace(/\\mathbb\{([A-Za-z])\}/g, (_, ch) => {
      const bb = { R: "ℝ", C: "ℂ", Q: "ℚ", Z: "ℤ", N: "ℕ", F: "𝔽", A: "𝔸", P: "ℙ", H: "ℍ" };
      return bb[ch] || ch;
    });
    const repl = [
      [/\\le(?![a-zA-Z])/g, "≤"], [/\\leq(?![a-zA-Z])/g, "≤"],
      [/\\ge(?![a-zA-Z])/g, "≥"], [/\\geq(?![a-zA-Z])/g, "≥"],
      [/\\ne(?![a-zA-Z])/g, "≠"], [/\\neq(?![a-zA-Z])/g, "≠"],
      [/\\approx(?![a-zA-Z])/g, "≈"], [/\\asymp(?![a-zA-Z])/g, "≍"],
      [/\\simeq(?![a-zA-Z])/g, "≃"], [/\\sim(?![a-zA-Z])/g, "∼"],
      [/\\equiv(?![a-zA-Z])/g, "≡"], [/\\in(?![a-zA-Z])/g, "∈"],
      [/\\notin(?![a-zA-Z])/g, "∉"], [/\\subset(?![a-zA-Z])/g, "⊂"],
      [/\\subseteq(?![a-zA-Z])/g, "⊆"], [/\\to(?![a-zA-Z])/g, "→"],
      [/\\rightarrow(?![a-zA-Z])/g, "→"], [/\\mapsto(?![a-zA-Z])/g, "↦"],
      [/\\Rightarrow(?![a-zA-Z])/g, "⇒"], [/\\iff(?![a-zA-Z])/g, "⇔"],
      [/\\forall(?![a-zA-Z])/g, "∀"], [/\\exists(?![a-zA-Z])/g, "∃"],
      [/\\land(?![a-zA-Z])/g, "∧"], [/\\lor(?![a-zA-Z])/g, "∨"],
      [/\\cdot(?![a-zA-Z])/g, "·"], [/\\times(?![a-zA-Z])/g, "×"],
      [/\\otimes(?![a-zA-Z])/g, "⊗"], [/\\oplus(?![a-zA-Z])/g, "⊕"],
      [/\\infty(?![a-zA-Z])/g, "∞"], [/\\sum(?![a-zA-Z])/g, "∑"],
      [/\\prod(?![a-zA-Z])/g, "∏"], [/\\int(?![a-zA-Z])/g, "∫"],
      [/\\bigwedge(?![a-zA-Z])/g, "⋀"], [/\\wedge(?![a-zA-Z])/g, "∧"],
      [/\\alpha(?![a-zA-Z])/g, "α"], [/\\beta(?![a-zA-Z])/g, "β"],
      [/\\gamma(?![a-zA-Z])/g, "γ"], [/\\delta(?![a-zA-Z])/g, "δ"],
      [/\\varepsilon(?![a-zA-Z])/g, "ε"], [/\\epsilon(?![a-zA-Z])/g, "ε"],
      [/\\zeta(?![a-zA-Z])/g, "ζ"], [/\\eta(?![a-zA-Z])/g, "η"],
      [/\\theta(?![a-zA-Z])/g, "θ"], [/\\iota(?![a-zA-Z])/g, "ι"],
      [/\\kappa(?![a-zA-Z])/g, "κ"], [/\\lambda(?![a-zA-Z])/g, "λ"],
      [/\\mu(?![a-zA-Z])/g, "μ"], [/\\nu(?![a-zA-Z])/g, "ν"],
      [/\\xi(?![a-zA-Z])/g, "ξ"], [/\\pi(?![a-zA-Z])/g, "π"],
      [/\\rho(?![a-zA-Z])/g, "ρ"], [/\\sigma(?![a-zA-Z])/g, "σ"],
      [/\\tau(?![a-zA-Z])/g, "τ"], [/\\phi(?![a-zA-Z])/g, "φ"],
      [/\\varphi(?![a-zA-Z])/g, "φ"], [/\\chi(?![a-zA-Z])/g, "χ"],
      [/\\psi(?![a-zA-Z])/g, "ψ"], [/\\omega(?![a-zA-Z])/g, "ω"],
      [/\\Gamma(?![a-zA-Z])/g, "Γ"], [/\\Delta(?![a-zA-Z])/g, "Δ"],
      [/\\Lambda(?![a-zA-Z])/g, "Λ"], [/\\Sigma(?![a-zA-Z])/g, "Σ"],
      [/\\Omega(?![a-zA-Z])/g, "Ω"], [/\\ell(?![a-zA-Z])/g, "ℓ"],
      [/\\vee(?![a-zA-Z])/g, "∨"], [/\\pm(?![a-zA-Z])/g, "±"],
      [/\\,/g, " "], [/\\;/g, " "], [/\\!/g, ""], [/\\left/g, ""], [/\\right/g, ""]
    ];
    for (const [rx, sym] of repl) s = s.replace(rx, sym);
    s = s.replace(/\\frac\{([^}]+)\}\{([^}]+)\}/g, "($1)/($2)");
    s = s.replace(/\^\{([^}]+)\}/g, "<sup>$1</sup>");
    s = s.replace(/_\{([^}]+)\}/g, "<sub>$1</sub>");
    s = s.replace(/\^([0-9A-Za-z∨*])/g, "<sup>$1</sup>");
    s = s.replace(/_([0-9A-Za-z])/g, "<sub>$1</sub>");
    return s;
  }

  function rewriteDocHref(rawHref, sourceContext) {
    const href = String(rawHref || "").trim();
    if (!href) return null;
    if (/^https?:\/\//i.test(href)) return { href, external: true };
    if (href.startsWith("#")) return { href, external: false };
    const safe = safeHref(href);
    if (!safe) return null;

    // Rewrite relative markdown paths to SPA routes
    const clean = safe.split("#")[0].replace(/^\.\//, "");
    const mFind = clean.match(/(?:^|\/)findings\/([A-Za-z0-9_.-]+)\.md$/);
    if (mFind) return { href: "#findings/" + encodeURIComponent(mFind[1]), external: false };
    const mAn = clean.match(/(?:^|\/)analysis\/([A-Za-z0-9_.-]+)\.md$/);
    if (mAn) {
      if (mAn[1].toLowerCase() === "readme") return { href: "#dossiers", external: false };
      return { href: "#dossiers/" + encodeURIComponent(mAn[1]), external: false };
    }
    const mRes = clean.match(/(?:^|\/)research\/([A-Za-z0-9_.-]+)\.md$/);
    if (mRes) return { href: "#dossiers/research/" + encodeURIComponent(mRes[1]), external: false };
    const mBare = clean.match(/^([A-Za-z0-9_.-]+)\.md$/);
    if (mBare) {
      const slug = mBare[1];
      if (slug.toLowerCase() === "readme") {
        return { href: sourceContext === "findings" ? "#findings" : "#dossiers", external: false };
      }
      if (sourceContext === "findings") return { href: "#findings/" + encodeURIComponent(slug), external: false };
      if (sourceContext === "research") return { href: "#dossiers/research/" + encodeURIComponent(slug), external: false };
      return { href: "#dossiers/" + encodeURIComponent(slug), external: false };
    }
    return { href: safe, external: false };
  }

  function renderInlineSafe(rawText, sourceContext) {
    // 1. Escape ALL HTML first so zero untrusted tags survive!
    let s = escapeHtml(rawText);

    // 2. Protect inline code spans
    const placeholders = [];
    const hold = (htmlStr) => {
      const id = "\u0000H" + placeholders.length + "\u0000";
      placeholders.push(htmlStr);
      return id;
    };

    s = s.replace(/`([^`\n]+)`/g, (_, code) => hold("<code>" + code + "</code>"));

    // 3. Inline LaTeX $...$ (avoid matching currency like $5 and $10)
    s = s.replace(/\$([^\n$]+?)\$/g, (m, tex) => {
      if (/^\s|\s$/.test(tex)) return m;
      return hold('<span class="math-inline">' + prettifyMath(tex) + "</span>");
    });

    // 4. Markdown links [label](url) — label may contain placeholder code spans
    s = s.replace(/\[([^\]]+)\]\(([^)\s]+)\)/g, (_, label, urlEsc) => {
      const decodedUrl = urlEsc.replace(/&amp;/g, "&");
      const rw = rewriteDocHref(decodedUrl, sourceContext);
      if (!rw) return label;
      const attrs = rw.external
        ? 'href="' + escapeHtml(rw.href) + '" target="_blank" rel="noopener noreferrer"'
        : 'href="' + escapeHtml(rw.href) + '"';
      return hold("<a " + attrs + ">" + label + "</a>");
    });

    // 5. Bold and italic
    s = s.replace(/\*\*([^*\n]+)\*\*/g, "<strong>$1</strong>");
    s = s.replace(/(^|[\s(])\*([^*\n]+)\*(?=[\s).,;:!?]|$)/g, "$1<em>$2</em>");

    // 6. Evidence tags [K], [S], [L], [M]
    s = s.replace(/\[([KLSM])\]/g, '<span class="ev-tag $1">[$1]</span>');

    // 7. Restore placeholders (nested links containing inline code expand cleanly)
    for (let pass = 0; pass < 3; pass++) {
      s = s.replace(/\u0000H(\d+)\u0000/g, (_, idx) => placeholders[Number(idx)] || "");
    }
    return s;
  }

  function renderMarkdownBlockSafe(md, sourceContext) {
    const lines = String(md || "").replace(/\r\n/g, "\n").split("\n");
    const out = [];
    let i = 0;

    const isTableSep = (line) => /^\s*\|?\s*:?-{3,}:?\s*(\|\s*:?-{3,}:?\s*)+\|?\s*$/.test(line);
    const splitRow = (line) => {
      let t = line.trim();
      if (t.startsWith("|")) t = t.slice(1);
      if (t.endsWith("|")) t = t.slice(0, -1);
      return t.split("|").map((c) => c.trim());
    };

    while (i < lines.length) {
      const line = lines[i];
      const trim = line.trim();

      if (!trim) { i++; continue; }

      // Safe <details> ... </details> block support
      if (/^<details(?:\s+open)?\s*>$/i.test(trim)) {
        const isOpen = /\bopen\b/i.test(trim);
        i++;
        let summaryText = "Details";
        const inner = [];
        let depth = 1;
        while (i < lines.length && depth > 0) {
          const t = lines[i].trim();
          if (/^<details\b/i.test(t)) depth++;
          else if (/^<\/details\s*>$/i.test(t)) {
            depth--;
            if (depth === 0) { i++; break; }
          } else if (depth === 1 && /^<summary\s*>(.*)<\/summary\s*>$/i.test(t)) {
            summaryText = t.replace(/^<summary\s*>/i, "").replace(/<\/summary\s*>$/i, "").trim();
            i++;
            continue;
          }
          inner.push(lines[i]);
          i++;
        }
        out.push(
          "<details" + (isOpen ? " open" : "") + "><summary>" +
          renderInlineSafe(summaryText, sourceContext) +
          "</summary>" + renderMarkdownBlockSafe(inner.join("\n"), sourceContext) +
          "</details>"
        );
        continue;
      }

      // Fenced code blocks
      const mFence = line.match(/^\s*```([A-Za-z0-9_+-]*)\s*$/);
      if (mFence) {
        const lang = mFence[1] || "";
        i++;
        const codeLines = [];
        while (i < lines.length && !/^\s*```\s*$/.test(lines[i])) {
          codeLines.push(lines[i]);
          i++;
        }
        if (i < lines.length) i++;
        out.push('<pre><code class="lang-' + escapeHtml(lang) + '">' + escapeHtml(codeLines.join("\n")) + "</code></pre>");
        continue;
      }

      // Display math $$ ... $$
      if (trim.startsWith("$$")) {
        if (trim.length > 4 && trim.endsWith("$$")) {
          const inner = trim.slice(2, -2).trim();
          out.push('<div class="math-block">' + prettifyMath(escapeHtml(inner)) + "</div>");
          i++;
          continue;
        }
        i++;
        const mLines = [];
        while (i < lines.length && !lines[i].trim().endsWith("$$")) {
          mLines.push(lines[i]);
          i++;
        }
        if (i < lines.length) i++;
        out.push('<div class="math-block">' + prettifyMath(escapeHtml(mLines.join(" ").trim())) + "</div>");
        continue;
      }

      // Headings
      const mHead = line.match(/^(#{1,4})\s+(.+?)\s*#*$/);
      if (mHead) {
        const lvl = mHead[1].length;
        out.push("<h" + lvl + ">" + renderInlineSafe(mHead[2], sourceContext) + "</h" + lvl + ">");
        i++;
        continue;
      }

      // Horizontal rule
      if (/^(\*{3,}|-{3,}|_{3,})\s*$/.test(trim)) {
        out.push("<hr>");
        i++;
        continue;
      }

      // Blockquote
      if (trim.startsWith(">")) {
        const qLines = [];
        while (i < lines.length && lines[i].trim().startsWith(">")) {
          qLines.push(lines[i].replace(/^\s*>\s?/, ""));
          i++;
        }
        out.push("<blockquote>" + renderMarkdownBlockSafe(qLines.join("\n"), sourceContext) + "</blockquote>");
        continue;
      }

      // GFM Table
      if (line.includes("|") && i + 1 < lines.length && isTableSep(lines[i + 1])) {
        const headers = splitRow(line);
        i += 2;
        const rows = [];
        while (i < lines.length && lines[i].trim() && lines[i].includes("|")) {
          rows.push(splitRow(lines[i]));
          i++;
        }
        const thead = "<thead><tr>" + headers.map((h) => "<th>" + renderInlineSafe(h, sourceContext) + "</th>").join("") + "</tr></thead>";
        const tbody = "<tbody>" + rows.map((r) => "<tr>" + headers.map((_, ci) => "<td>" + renderInlineSafe(r[ci] || "", sourceContext) + "</td>").join("") + "</tr>").join("") + "</tbody>";
        out.push('<div class="md-table-wrap"><table>' + thead + tbody + "</table></div>");
        continue;
      }

      // Lists (unordered & ordered)
      const isUl = /^\s*[-*+]\s+/.test(line);
      const isOl = /^\s*\d+\.\s+/.test(line);
      if (isUl || isOl) {
        const tag = isUl ? "ul" : "ol";
        const rx = isUl ? /^\s*[-*+]\s+(.*)$/ : /^\s*\d+\.\s+(.*)$/;
        const items = [];
        while (i < lines.length) {
          const m = lines[i].match(rx);
          if (!m) break;
          let itemTxt = m[1];
          i++;
          while (i < lines.length && lines[i].trim() && !/^\s*([-*+]|\d+\.)\s+/.test(lines[i]) && !/^\s*(#|```|>|\|)/.test(lines[i])) {
            itemTxt += " " + lines[i].trim();
            i++;
          }
          items.push("<li>" + renderInlineSafe(itemTxt, sourceContext) + "</li>");
        }
        out.push("<" + tag + ">" + items.join("") + "</" + tag + ">");
        continue;
      }

      // Paragraph
      const pLines = [];
      while (
        i < lines.length &&
        lines[i].trim() &&
        !/^\s*(#{1,4}\s|```|\$\$|>|<details\b|[-*+]\s|\d+\.\s|[-*_]{3,}\s*$)/.test(lines[i]) &&
        !(lines[i].includes("|") && i + 1 < lines.length && isTableSep(lines[i + 1]))
      ) {
        pLines.push(lines[i].trim());
        i++;
      }
      if (pLines.length) {
        out.push("<p>" + renderInlineSafe(pLines.join(" "), sourceContext) + "</p>");
      } else {
        i++;
      }
    }
    return out.join("\n");
  }

  // ---------- Theme Handling ----------
  function initTheme() {
    let saved = "dark";
    try {
      const v = window.localStorage.getItem("leanre_site_theme");
      if (v === "light" || v === "dark") saved = v;
    } catch (_) { /* ignore */ }
    applyTheme(saved, false);
  }

  function applyTheme(theme, rerenderCircuit) {
    state.theme = theme === "light" ? "light" : "dark";
    document.documentElement.setAttribute("data-theme", state.theme);
    const icon = $("#themeIcon");
    if (icon) icon.textContent = state.theme === "dark" ? "☀" : "☾";
    try { window.localStorage.setItem("leanre_site_theme", state.theme); } catch (_) { /* ignore */ }
    if (rerenderCircuit && state.route.tab === "circuit" && state.circuit.shard) {
      mountActiveCircuitSvg();
    }
  }

  // ---------- Hash Routing ----------
  function parseHash() {
    const raw = (window.location.hash || "").replace(/^#/, "");
    const [pathPart, queryPart] = raw.split("?");
    const segs = pathPart.split("/").filter(Boolean).map((s) => {
      try { return decodeURIComponent(s); } catch (_) { return s; }
    });
    const params = new URLSearchParams(queryPart || "");
    if (raw === "selftest=1" || raw.includes("selftest=1")) params.set("selftest", "1");

    const validTabs = new Set(["overview", "circuit", "findings", "dossiers", "blueprints", "flirt", "atlas", "portability", "benchmarks", "search"]);
    let tab = segs[0] || "overview";
    if (!validTabs.has(tab)) tab = "overview";
    return {
      tab,
      sub: segs[1] || "",
      arg: segs.slice(2).join("/"),
      selftest: params.get("selftest") === "1" || window.location.search.includes("selftest=1")
    };
  }

  function navigate(hashStr, replace) {
    const target = hashStr.startsWith("#") ? hashStr : "#" + hashStr;
    if (window.location.hash === target) {
      handleRoute();
      return;
    }
    if (replace && window.history && window.history.replaceState) {
      try {
        window.history.replaceState(null, "", target);
        handleRoute();
        return;
      } catch (_) { /* fallback */ }
    }
    window.location.hash = target;
  }

  function updateNavHighlight(tab) {
    $$("#mainNav .nav-tab").forEach((btn) => {
      btn.classList.toggle("active", btn.dataset.route === tab);
    });
    const main = $("#appMain");
    if (main) main.classList.toggle("full-bleed", tab === "circuit");
  }

  function populateChromeFromManifest() {
    const m = state.manifest || {};
    document.title = (m.title || m.repo_name || "leanre") + " — leanre Proof Explorer";
    const repoBadge = $("#brandRepo");
    if (repoBadge) repoBadge.textContent = m.repo_name || "";

    const ext = $("#repoExtLink");
    if (ext) {
      const url = safeHref(m.repo_url);
      if (url && /^https?:\/\//i.test(url)) {
        const treeUrl = m.pinned_commit ? url.replace(/\/+$/, "") + "/tree/" + encodeURIComponent(m.pinned_commit) : url;
        ext.href = treeUrl;
        ext.classList.remove("hidden");
      } else {
        ext.classList.add("hidden");
      }
    }

    const st = m.stats || {};
    const addCount = (id, val) => {
      const btn = $("#" + id);
      if (!btn || val == null || val <= 0) return;
      let sp = btn.querySelector(".tab-cnt");
      if (!sp) {
        sp = el("span", { className: "tab-cnt" });
        btn.appendChild(sp);
      }
      sp.textContent = String(val);
    };
    const cirCnt = (m.circuits && ((m.circuits.bundles || []).length + (m.circuits.theorems || []).length + (m.circuits.macro ? 1 : 0))) || 0;
    addCount("tab-circuit", cirCnt);
    addCount("tab-findings", (m.findings || []).length);
    addCount("tab-dossiers", (m.dossiers || []).length);
    addCount("tab-blueprints", (m.blueprints || []).length);

    const atlasTab = $("#tab-atlas");
    if (atlasTab) {
      atlasTab.classList.toggle("hidden", !(m.assets && m.assets.atlas));
    }

    const footerMeta = $("#footerMeta");
    if (footerMeta) {
      const commitShort = m.pinned_commit ? " · commit " + String(m.pinned_commit).slice(0, 8) : "";
      const modeTag = m.demo_mode ? " · demo mode" : "";
      footerMeta.textContent = (m.repo_name || "leanre") + commitShort + modeTag + " · zero-CDN lazy static explorer";
    }
  }

  // ---------- Circuit Manifest Lookup Helpers ----------
  function findCircuitEntry(mode, target) {
    const circuits = (state.manifest && state.manifest.circuits) || {};
    if (mode === "macro") {
      return circuits.macro ? { mode: "macro", name: "Macro", short: "Macro", path: circuits.macro } : null;
    }
    const list = mode === "bundle" ? (circuits.bundles || []) : (circuits.theorems || []);
    const q = String(target || "").trim();
    if (!q) return list[0] ? Object.assign({ mode }, list[0]) : null;
    const ql = q.toLowerCase();
    const qs = shortName(q).toLowerCase();
    const match =
      list.find((x) => x.name === q || x.short === q) ||
      list.find((x) => String(x.name || "").toLowerCase() === ql || String(x.short || "").toLowerCase() === ql) ||
      list.find((x) => shortName(x.name).toLowerCase() === qs);
    return match ? Object.assign({ mode }, match) : null;
  }

  function findAnyCircuitForSymbol(symbol, pathOpt) {
    const b = findCircuitEntry("bundle", symbol);
    if (b) return b;
    const t = findCircuitEntry("theorem", symbol);
    if (t) return t;
    if (pathOpt) {
      const circuits = (state.manifest && state.manifest.circuits) || {};
      const bm = (circuits.bundles || []).find((x) => x.path === pathOpt);
      if (bm) return Object.assign({ mode: "bundle" }, bm);
      const tm = (circuits.theorems || []).find((x) => x.path === pathOpt);
      if (tm) return Object.assign({ mode: "theorem" }, tm);
    }
    return null;
  }

  // ==========================================================================
  // VIEW 1: OVERVIEW
  // ==========================================================================
  function renderOverview() {
    const main = $("#appMain");
    clearEl(main);
    const m = state.manifest || {};
    const st = m.stats || {};

    // Hero
    const heroActions = el("div", { className: "hero-actions" }, [
      el("button", {
        type: "button", className: "btn primary",
        textContent: "Open Proof Circuit →",
        onclick: () => navigate("#circuit")
      }),
      (m.findings && m.findings.length)
        ? el("button", { type: "button", className: "btn emerald", textContent: "Read Findings (" + m.findings.length + ")", onclick: () => navigate("#findings") })
        : null,
      (m.assets && m.assets.atlas)
        ? el("button", { type: "button", className: "btn", textContent: "Genome Atlas (Hi-C / Aliens)", onclick: () => navigate("#atlas") })
        : null,
      el("button", { type: "button", className: "btn", textContent: "Global Search (/)", onclick: () => navigate("#search") })
    ]);

    const metaPills = el("div", { className: "hero-meta" }, [
      m.repo_name ? el("span", { className: "pill cyan", textContent: m.repo_name }) : null,
      m.pinned_commit ? el("span", { className: "pill slate", textContent: "commit " + String(m.pinned_commit).slice(0, 8) }) : null,
      m.demo_mode ? el("span", { className: "pill amber", textContent: "demo corpus" }) : el("span", { className: "pill emerald", textContent: "3 std axioms · 0 sorryAx" }),
      st.search_shards ? el("span", { className: "pill slate", textContent: fmtInt(st.search_entries) + " indexed decls / " + st.search_shards + " lazy shards" }) : null
    ]);

    main.appendChild(el("section", { className: "hero" }, [
      el("div", { className: "hero-top" }, [
        el("div", null, [
          el("h1", { textContent: m.title || (m.repo_name ? m.repo_name + " — Proof Architecture Explorer" : "leanre Static Explorer") }),
          el("p", {
            className: "hero-sub",
            textContent: m.demo_mode
              ? "Zero-CDN lazy-fetched static proof architecture explorer built from kernel dependency graphs and interactive 3-level Proof Circuits."
              : `Zero-CDN lazy-fetched static reverse-engineering explorer of the kernel dependency graph, 3-level interactive Proof Circuits, findings, ${(m.dossiers || []).length || 0} technical dossiers, ${(m.blueprints || []).length || 0} decompilation blueprints, and 141-cluster FLIRT atlas.`
          }),
          metaPills
        ]),
        heroActions
      ])
    ]));

    // Epistemic Scope Banner
    main.appendChild(el("div", { className: "scope-banner", role: "note" }, [
      el("span", { className: "scope-tag", textContent: "Epistemic Scope" }),
      el("div", null, [
        el("strong", { textContent: "Layer 1 kernel verification ≠ Layer 4 mathematical peer review. " }),
        "Kernel export checks establish syntactic typechecking under standard axioms only (zero sorryAx / custom axioms), while decompilation blueprints and technical dossiers map statements, records, and structural wiring without claiming independent peer review of deep tactic bodies."
      ])
    ]));

    // KPI Strip
    const livePct = st.total_decls > 0 ? ((st.live_decls / st.total_decls) * 100).toFixed(1) + "% live" : "";
    const kpis = [
      { label: "Live Declarations", val: fmtInt(st.live_decls), sub: livePct || "kernel reachable", cls: "emerald" },
      { label: "Dead / Unreachable", val: fmtInt(st.dead_decls), sub: "of " + fmtInt(st.total_decls) + " total", cls: st.dead_decls > 0 ? "amber" : "" },
      { label: "Kernel Edges", val: fmtInt(st.edges), sub: fmtInt(st.total_files) + " files · " + fmtInt(st.total_lines) + " LOC", cls: "cyan" },
      { label: "Pre-rendered Circuits", val: fmtInt((m.circuits && ((m.circuits.bundles || []).length + (m.circuits.theorems || []).length + (m.circuits.macro ? 1 : 0))) || 0), sub: ((m.circuits && (m.circuits.bundles || []).length) || 0) + " bundles · " + ((m.circuits && (m.circuits.theorems || []).length) || 0) + " theorems", cls: "cyan" },
      { label: "Blueprints & Dossiers", val: fmtInt((m.blueprints || []).length) + " / " + fmtInt((m.dossiers || []).length), sub: ((m.findings || []).length) + " findings · " + ((m.research || []).length) + " research", cls: "" }
    ];
    main.appendChild(el("section", { className: "kpi-strip", "aria-label": "Repository metrics" }, kpis.map((k) =>
      el("div", { className: "kpi-card" }, [
        el("div", { className: "kpi-label", textContent: k.label }),
        el("div", { className: "kpi-val " + k.cls, textContent: k.val }),
        el("div", { className: "kpi-sub", textContent: k.sub })
      ])
    )));

    // Two-column Overview: Dominator Hierarchy + Showcase Proof Circuits
    const pillars = Array.isArray(m.overview_pillars) ? m.overview_pillars : [];
    const maxCount = Math.max(1, Number(st.live_decls) || 0, ...pillars.map((p) => Number(p.count || p.dom || p.subtree_size || 0)));

    const domTree = el("div", { className: "dom-tree" });
    if (pillars.length) {
      pillars.forEach((p, idx) => {
        const cnt = Number(p.count ?? p.dom ?? p.subtree_size ?? 0);
        const pct = Math.max(1.5, Math.min(100, (cnt / maxCount) * 100));
        const depth = Number(p.depth || 0);
        const target = p.circuit_target || p.target || p.decl || p.name || "";
        const circuitHit = (p.circuit_mode && target)
          ? (findCircuitEntry(p.circuit_mode, target) || findAnyCircuitForSymbol(target))
          : (target ? findAnyCircuitForSymbol(target) : null);
        const desc = p.note || p.description || "";
        const fillCls = idx === 0 ? "emerald" : (String(p.role || p.label || p.name || "").toLowerCase().includes("diamond") ? "amber" : (depth >= 2 ? "teal" : ""));
        const row = el("div", {
          className: "dom-row" + (circuitHit ? " clickable" : ""),
          title: circuitHit ? "Open Proof Circuit for " + circuitHit.name : (desc || p.label || p.name || ""),
          onclick: circuitHit ? () => navigate("#circuit/" + circuitHit.mode + "/" + encodeURIComponent(circuitHit.short || circuitHit.name)) : null
        }, [
          el("div", { className: "dom-name" }, [
            depth > 0 ? el("span", { className: "indent", textContent: "  ".repeat(Math.min(depth, 4)) + "└─" }) : null,
            el("div", { style: { minWidth: "0" } }, [
              el("div", { className: "lbl", textContent: p.label || p.name || target || "node" }),
              desc ? el("div", { className: "sub-note", textContent: desc }) : null
            ])
          ]),
          el("div", { className: "dom-bar-track" }, [
            el("div", { className: "dom-bar-fill " + fillCls, style: { width: pct.toFixed(1) + "%" } })
          ]),
          el("div", { className: "dom-count", textContent: fmtInt(cnt) + (p.pct_live != null ? " (" + Number(p.pct_live).toFixed(0) + "%)" : "") })
        ]);
        domTree.appendChild(row);
      });
    } else {
      domTree.appendChild(el("div", { className: "empty-card" }, [
        el("p", { textContent: "No dominator pillar breakdown in manifest. Explore the interactive Macro Proof Circuit to inspect roots and clusters." })
      ]));
    }

    // Showcase Proof Circuits Launchpad
    const showcaseGrid = el("div", { className: "showcase-chips" });
    const addedKeys = new Set();
    const pushShowcase = (mode, target, label, desc, tag, colorCls) => {
      const k = mode + ":" + target;
      if (addedKeys.has(k)) return;
      addedKeys.add(k);
      showcaseGrid.appendChild(el("button", {
        type: "button",
        className: "showcase-btn",
        onclick: () => {
          if (mode === "macro") navigate("#circuit/macro");
          else navigate("#circuit/" + mode + "/" + encodeURIComponent(target));
        }
      }, [
        el("div", { className: "sc-top" }, [
          el("span", { className: "sc-title", textContent: label }),
          el("span", { className: "pill " + (colorCls || "cyan"), textContent: tag })
        ]),
        el("div", { className: "sc-sub", textContent: desc })
      ]));
    };

    for (const sc of SHOWCASE_ORDER) {
      const hit = findCircuitEntry(sc.mode, sc.target);
      if (hit) {
        const badgeTxt = hit.badge || sc.tag;
        const cCls = sc.mode === "macro" ? "emerald" : (sc.mode === "bundle" ? "amber" : "cyan");
        pushShowcase(sc.mode, hit.short || hit.name || "", sc.label, sc.desc, badgeTxt, cCls);
      }
    }
    // Fill up with available bundles/theorems on generic/demo repos
    if (addedKeys.size < 6 && m.circuits) {
      for (const b of (m.circuits.bundles || []).slice(0, 4)) {
        pushShowcase("bundle", b.short || b.name, b.short || shortName(b.name), (b.fields || 0) + " fields · " + (b.consumers || 0) + " consumers", b.badge || "Bundle", "amber");
      }
      for (const t of (m.circuits.theorems || []).slice(0, 4)) {
        pushShowcase("theorem", t.short || t.name, t.short || shortName(t.name), "dom " + fmtInt(t.dom || 0) + " · " + (t.steps || 0) + " steps", t.badge || "Theorem", "cyan");
      }
    }

    main.appendChild(el("section", { className: "overview-grid" }, [
      el("div", { className: "panel" }, [
        el("div", { className: "section-hdr", style: { marginTop: "0" } }, [
          el("h2", { textContent: "Dominator Spine Hierarchy" }),
          el("span", { className: "sub", textContent: "Click highlighted rows to jump to Proof Circuit" })
        ]),
        domTree
      ]),
      el("div", { className: "panel" }, [
        el("div", { className: "section-hdr", style: { marginTop: "0" } }, [
          el("h2", { textContent: "Showcase Proof Circuits" }),
          el("span", { className: "sub", textContent: "Lazy-fetched SVG + pan/zoom" })
        ]),
        showcaseGrid
      ])
    ]));

    // Highlighted Findings Cards
    const findings = Array.isArray(m.findings) ? m.findings : [];
    if (findings.length) {
      main.appendChild(el("div", { className: "section-hdr" }, [
        el("h2", { textContent: "Key Findings" }),
        el("span", { className: "sub", textContent: findings.length + " curated audit chapters (fetched on click)" })
      ]));
      main.appendChild(el("section", { className: "findings-cards" }, findings.map((f) =>
        el("button", {
          type: "button",
          className: "finding-card",
          onclick: () => navigate("#findings/" + encodeURIComponent(f.slug))
        }, [
          el("div", { className: "fc-slug", textContent: f.slug + " · " + formatBytes(f.bytes || 0) }),
          el("div", { className: "fc-title", textContent: f.title || f.slug }),
          f.summary ? el("div", { className: "fc-sum", textContent: f.summary }) : null
        ])
      )));
    }
  }

  // ==========================================================================
  // VIEW 2: INTERACTIVE 3-LEVEL PROOF CIRCUIT VIEWER
  // ==========================================================================
  function applyCircuitTransform() {
    const stg = $("#cirStage");
    if (!stg) return;
    stg.style.transform = "translate(" + state.circuit.tx.toFixed(1) + "px," + state.circuit.ty.toFixed(1) + "px) scale(" + state.circuit.scale.toFixed(3) + ")";
  }

  function fitCircuitStage() {
    const wrap = $("#cirStageWrap");
    const stg = $("#cirStage");
    if (!wrap || !stg) return;
    const svg = stg.querySelector("svg");
    if (!svg) return;
    const vb = svg.viewBox && svg.viewBox.baseVal;
    const sw = (vb && vb.width) || Number(svg.getAttribute("width")) || 1200;
    const sh = (vb && vb.height) || Number(svg.getAttribute("height")) || 760;
    const cw = wrap.clientWidth || 1000;
    const ch = wrap.clientHeight || 560;
    const sc = Math.max(0.18, Math.min(1.25, Math.min((cw - 18) / sw, (ch - 18) / sh)));
    state.circuit.scale = sc;
    state.circuit.tx = Math.max(8, (cw - sw * sc) / 2);
    state.circuit.ty = Math.max(8, (ch - sh * sc) / 2);
    applyCircuitTransform();
  }

  function applyCircuitNodeHighlight() {
    const stg = $("#cirStage");
    if (!stg) return;
    const q = (state.circuit.filter || "").trim().toLowerCase();
    const payload = (state.circuit.shard && state.circuit.shard.payload) || {};
    const byId = new Map();
    for (const n of (payload.nodes || [])) byId.set(n.id, n);
    for (const b of (payload.binders || [])) byId.set(b.id, b);

    $$(".circuit-node", stg).forEach((g) => {
      const nid = g.getAttribute("data-node-id") || "";
      const obj = byId.get(nid) || {};
      const hay = ((obj.label || "") + " " + (obj.full_name || "") + " " + (obj.tooltip || "") + " " + (obj.badge || "") + " " + (obj.type || "")).toLowerCase();
      const hit = q ? hay.includes(q) : false;
      g.classList.toggle("dim", Boolean(q && !hit));
      g.classList.toggle("hl", hit);
    });
    $$(".circuit-pin", stg).forEach((g) => {
      const pn = g.getAttribute("data-pin") || "";
      const hit = q ? pn.toLowerCase().includes(q) : false;
      g.classList.toggle("dim", Boolean(q && !hit));
      g.classList.toggle("hl", hit);
    });
  }

  function renderCircuitInspector(item, isHover) {
    const box = $("#cirInspector");
    if (!box) return;
    clearEl(box);

    const shard = state.circuit.shard;
    const payload = (shard && shard.payload) || null;
    if (!payload) {
      box.appendChild(el("div", { className: "cir-ins-hd" }, [el("span", { textContent: "Inspector" })]));
      box.appendChild(el("p", { className: "cir-ins-note", textContent: "Click any circuit node or field pin to inspect metrics, cross-zoom to pre-rendered shards, or open the pinned GitHub source line." }));
      return;
    }

    const meta = payload.meta || {};
    const stats = payload.stats || {};
    const targetInfo = meta.target_info || {};

    box.appendChild(el("div", { className: "cir-ins-hd" }, [
      el("span", { textContent: isHover ? "Hover Preview" : (item ? "Selected Node" : "Circuit Summary") }),
      el("span", { className: "pill cyan", textContent: String(payload.mode || state.circuit.mode).toUpperCase() })
    ]));

    if (!item) {
      box.appendChild(el("div", { className: "cir-ins-title", textContent: payload.target || payload.title || "Macro Proof Circuit" }));
      const topAnchor = (payload.pins && payload.pins.anchor) || meta.anchor || targetInfo.anchor || "";
      if (topAnchor) {
        box.appendChild(el("div", { className: "cir-ins-note" }, ["Source: ", makeGithubAnchor(topAnchor)]));
      }

      const kv = el("div", { className: "cir-ins-kv" });
      const addKv = (k, v) => {
        if (v == null || v === "") return;
        kv.appendChild(el("div", { className: "k", textContent: k }));
        kv.appendChild(el("div", { className: "v", textContent: String(v) }));
      };
      addKv("Nodes / Wires", fmtInt(stats.node_count) + " / " + fmtInt(stats.wire_count));
      if (payload.mode === "macro") {
        addKv("Live / Dead", fmtInt(stats.live_decls) + " / " + fmtInt(stats.dead_decls));
        if (stats.shared_diamond_decls != null) addKv("Diamond", fmtInt(stats.shared_diamond_decls) + " decls");
        if (stats.motif_clusters_count != null) addKv("Motifs", fmtInt(stats.motif_clusters_count) + " non-trivial");
        if (stats.excluded_trivial_shells) addKv("Excluded", fmtInt(stats.excluded_prop_shells) + " Prop · " + fmtInt(stats.excluded_trivial_shells) + " shells");
      } else if (payload.mode === "bundle") {
        addKv("Fields", fmtInt(stats.total_fields) + " (" + fmtInt(stats.projected_fields) + " read, " + fmtInt(stats.unread_fields) + " unread)");
        addKv("Cond / True", fmtInt(stats.conditional_prop_fields) + " cond · " + fmtInt(stats.literal_true_fields) + " True");
        addKv("Producers", fmtInt(stats.producers_total));
        addKv("Consumers", fmtInt(stats.consumers_total) + " (" + fmtInt(stats.consumers_dropped_input) + " drop)");
      } else if (payload.mode === "theorem") {
        addKv("Kind", stats.decl_kind || "—");
        addKv("Binders", fmtInt(stats.binders_used) + " used · " + fmtInt(stats.binders_dropped) + " dropped");
        addKv("Steps", fmtInt(stats.steps_count));
        addKv("Fan-in / Out", fmtInt(stats.fan_in) + " / " + fmtInt(stats.fan_out));
        if (meta.sighash) addKv("k1n", meta.sighash);
      }
      box.appendChild(kv);
      box.appendChild(el("p", { className: "cir-ins-note", textContent: "Click any node to cross-zoom into pre-rendered Bundle/Theorem shards, or inspect its pinned GitHub source anchor. Drag to pan, scroll wheel to zoom." }));
      return;
    }

    // Specific Node or Pin Inspector
    const title = item.full_name || item.name || item.label || item.id || "";
    box.appendChild(el("div", { className: "cir-ins-title", textContent: title }));

    const pillRow = el("div", { className: "cir-ins-acts" });
    if (item.kind) pillRow.appendChild(el("span", { className: "pill slate", textContent: item.kind }));
    if (item.status) {
      const sCls = ["dropped", "dangling", "literal_true", "true_slot"].includes(item.status)
        ? "crimson"
        : (["conditional_prop", "default_zero", "le_refl"].includes(item.status) ? "amber" : (item.status === "unread" || item.status === "trivial_shell" ? "slate" : "emerald"));
      pillRow.appendChild(el("span", { className: "pill " + sCls, textContent: item.status }));
    }
    if (item.badge) pillRow.appendChild(el("span", { className: "pill cyan", textContent: item.badge }));
    box.appendChild(pillRow);

    const anchor = item.anchor || (item._isPin ? (targetInfo.anchor || "") : (item.line_no && meta.anchor ? meta.anchor.replace(/:\d+$/, ":" + item.line_no) : ""));
    if (anchor) {
      box.appendChild(el("div", { className: "cir-ins-note" }, ["Source: ", makeGithubAnchor(anchor)]));
    }

    // Check pre-rendered cross-zoom targets
    const zt = item.zoom_target || null;
    const pivot = (zt && zt.target) || item.full_name || item.name || "";
    const acts = el("div", { className: "cir-ins-acts" });
    const bundleHit = pivot ? findCircuitEntry("bundle", pivot) : null;
    const thmHit = pivot ? findCircuitEntry("theorem", pivot) : null;
    if (bundleHit) {
      acts.appendChild(el("button", {
        type: "button", className: "btn sm primary", textContent: "Open Bundle Circuit →",
        onclick: () => navigate("#circuit/bundle/" + encodeURIComponent(bundleHit.short || bundleHit.name))
      }));
    }
    if (thmHit) {
      acts.appendChild(el("button", {
        type: "button", className: "btn sm primary", textContent: "Open Theorem Circuit →",
        onclick: () => navigate("#circuit/theorem/" + encodeURIComponent(thmHit.short || thmHit.name))
      }));
    }
    if (anchor) {
      const gh = buildGithubUrl(anchor);
      if (gh) {
        acts.appendChild(el("a", { className: "btn sm", href: gh, target: "_blank", rel: "noopener noreferrer", textContent: "View Source ↗" }));
      }
    }
    if (acts.childNodes.length) box.appendChild(acts);
    else if (pivot && !item._isPin) {
      box.appendChild(el("div", { className: "cir-ins-note", textContent: "Not pre-rendered as a standalone circuit shard in this static build." }));
    }

    const kv = el("div", { className: "cir-ins-kv" });
    const addKv = (k, v) => {
      if (v == null || v === "") return;
      kv.appendChild(el("div", { className: "k", textContent: k }));
      kv.appendChild(el("div", { className: "v", textContent: String(v) }));
    };
    const m = item.metrics || {};
    if (item._isPin) {
      addKv("Status", item.status);
      addKv("Projected", item.projected ? "yes" : "no (0 callers)");
      if (item.fan_in != null) addKv("Fan-in", fmtInt(item.fan_in));
      if (item.is_conditional_prop) addKv("Guard", "conditional P → Q");
      if (item.is_literal_true) addKv("Stub", "literal : True");
      if (item.type) addKv("Type", item.type);
    } else {
      if (item.type) addKv("Type", item.type);
      if (item.line_no != null) addKv("Line", "L" + item.line_no);
      if (m.subtree_size != null) addKv("Dom Subtree", fmtInt(m.subtree_size) + (m.pct_live != null ? " (" + m.pct_live + "%)" : ""));
      if (m.dom_subtree_size != null && m.subtree_size == null) addKv("Dom Subtree", fmtInt(m.dom_subtree_size));
      if (m.fan_in != null) addKv("Fan-in", fmtInt(m.fan_in));
      if (m.fan_out != null) addKv("Fan-out", fmtInt(m.fan_out));
      if (m.is_trivial_shell) addKv("Shell", (m.shell_label || "Prop") + " (excluded)");
      else if (item.k1n_count != null || m.k1n_count != null) addKv("Motif k1n", "×" + fmtInt(item.k1n_count ?? m.k1n_count));
      if (m.total_fields != null) addKv("Fields", fmtInt(m.projected) + " read · " + fmtInt(m.unread) + " unread");
      if (item.drops_target) addKv("Hygiene", "DROPPED / unplugged input");
      if (item.producer_role) addKv("Producer", item.producer_role);
      if (item.tooltip) addKv("Summary", item.tooltip);
    }
    box.appendChild(kv);
  }

  function wireCircuitStageEvents() {
    const wrap = $("#cirStageWrap");
    if (!wrap || wrap.dataset.wired === "1") return;
    wrap.dataset.wired = "1";
    let dragging = false, sx = 0, sy = 0, otx = 0, oty = 0;

    wrap.addEventListener("pointerdown", (ev) => {
      if (ev.button !== 0) return;
      dragging = true;
      sx = ev.clientX;
      sy = ev.clientY;
      otx = state.circuit.tx;
      oty = state.circuit.ty;
      state.circuit.dragMoved = 0;
      wrap.classList.add("dragging");
    });
    window.addEventListener("pointermove", (ev) => {
      if (!dragging) return;
      const dx = ev.clientX - sx;
      const dy = ev.clientY - sy;
      state.circuit.dragMoved = Math.max(state.circuit.dragMoved, Math.hypot(dx, dy));
      state.circuit.tx = otx + dx;
      state.circuit.ty = oty + dy;
      applyCircuitTransform();
    });
    window.addEventListener("pointerup", () => {
      if (!dragging) return;
      dragging = false;
      wrap.classList.remove("dragging");
    });
    wrap.addEventListener("wheel", (ev) => {
      ev.preventDefault();
      const rect = wrap.getBoundingClientRect();
      const mx = ev.clientX - rect.left;
      const my = ev.clientY - rect.top;
      const factor = ev.deltaY < 0 ? 1.12 : 0.89;
      const ns = Math.max(0.16, Math.min(4.0, state.circuit.scale * factor));
      state.circuit.tx = mx - (mx - state.circuit.tx) * (ns / state.circuit.scale);
      state.circuit.ty = my - (my - state.circuit.ty) * (ns / state.circuit.scale);
      state.circuit.scale = ns;
      applyCircuitTransform();
    }, { passive: false });
  }

  function mountActiveCircuitSvg() {
    const stg = $("#cirStage");
    const shard = state.circuit.shard;
    if (!stg || !shard) return;
    const svgText = state.theme === "light"
      ? (shard.svg_light || shard.svg || shard.svg_dark || "")
      : (shard.svg_dark || shard.svg || shard.svg_light || "");

    const svgEl = mountSafeSvg(stg, svgText);
    if (!svgEl) return;

    const payload = shard.payload || {};
    const nodeById = new Map();
    for (const n of (payload.nodes || [])) nodeById.set(n.id, n);
    for (const b of (payload.binders || [])) nodeById.set(b.id, b);
    const pinByName = new Map();
    const chip = (payload.nodes || []).find((n) => n.kind === "chip");
    if (chip && Array.isArray(chip.pins)) {
      for (const p of chip.pins) pinByName.set(p.name, Object.assign({ _isPin: true }, p));
    }

    const tip = $("#circuitTip");
    const showTip = (txt, ev) => {
      if (!tip) return;
      tip.textContent = txt;
      tip.style.display = "block";
      tip.style.left = Math.min(window.innerWidth - 440, ev.clientX + 14) + "px";
      tip.style.top = Math.min(window.innerHeight - 100, ev.clientY + 14) + "px";
    };
    const hideTip = () => { if (tip) tip.style.display = "none"; };

    $$(".circuit-node", svgEl).forEach((g) => {
      const nid = g.getAttribute("data-node-id") || "";
      const obj = nodeById.get(nid) || { id: nid, label: nid };
      g.addEventListener("mouseenter", (ev) => {
        state.circuit.hoveredItem = obj;
        renderCircuitInspector(obj, true);
        showTip(obj.tooltip || obj.full_name || obj.label || nid, ev);
      });
      g.addEventListener("mousemove", (ev) => {
        if (tip && tip.style.display === "block") {
          tip.style.left = Math.min(window.innerWidth - 440, ev.clientX + 14) + "px";
          tip.style.top = Math.min(window.innerHeight - 100, ev.clientY + 14) + "px";
        }
      });
      g.addEventListener("mouseleave", () => {
        state.circuit.hoveredItem = null;
        hideTip();
        renderCircuitInspector(state.circuit.selectedItem, false);
      });
      g.addEventListener("click", (ev) => {
        if (state.circuit.dragMoved > 4) return;
        ev.stopPropagation();
        hideTip();
        $$(".circuit-node.selected, .circuit-pin.selected", svgEl).forEach((x) => x.classList.remove("selected"));
        g.classList.add("selected");
        state.circuit.selectedItem = obj;

        let zmode = g.getAttribute("data-zoom-mode") || (obj.zoom_target && obj.zoom_target.mode) || "";
        let ztgt = g.getAttribute("data-zoom-target") || (obj.zoom_target && obj.zoom_target.target) || obj.full_name || "";
        if (zmode && ztgt) {
          if (state.circuit.mode === "macro" && obj.metrics && obj.metrics.sample_kind === "inductive") {
            zmode = "bundle";
          }
          const pre = findCircuitEntry(zmode, ztgt) || findAnyCircuitForSymbol(ztgt);
          if (pre && !(pre.mode === state.circuit.mode && (pre.name === state.circuit.target || pre.short === state.circuit.target))) {
            navigate("#circuit/" + pre.mode + "/" + encodeURIComponent(pre.short || pre.name));
            return;
          }
        }
        renderCircuitInspector(obj, false);
      });
    });

    $$(".circuit-pin", svgEl).forEach((g) => {
      const pname = g.getAttribute("data-pin") || "";
      const pObj = pinByName.get(pname) || { _isPin: true, name: pname, status: "projected" };
      g.addEventListener("mouseenter", (ev) => {
        state.circuit.hoveredItem = pObj;
        renderCircuitInspector(pObj, true);
        showTip(pname + " [" + (pObj.status || "") + "]" + (pObj.type ? " : " + pObj.type : ""), ev);
      });
      g.addEventListener("mouseleave", () => {
        state.circuit.hoveredItem = null;
        hideTip();
        renderCircuitInspector(state.circuit.selectedItem, false);
      });
      g.addEventListener("click", (ev) => {
        if (state.circuit.dragMoved > 4) return;
        ev.stopPropagation();
        $$(".circuit-node.selected, .circuit-pin.selected", svgEl).forEach((x) => x.classList.remove("selected"));
        g.classList.add("selected");
        state.circuit.selectedItem = pObj;
        renderCircuitInspector(pObj, false);
      });
    });

    fitCircuitStage();
    requestAnimationFrame(fitCircuitStage);
    applyCircuitNodeHighlight();
  }

  function renderCircuitChips(mode) {
    const wrap = $("#cirChipsWrap");
    if (!wrap) return;
    clearEl(wrap);
    const circuits = (state.manifest && state.manifest.circuits) || {};
    const list = mode === "bundle" ? (circuits.bundles || []) : (mode === "theorem" ? (circuits.theorems || []) : []);
    const q = (state.circuit.selectorFilter || "").trim().toLowerCase();

    if (mode === "macro") {
      wrap.appendChild(el("span", { className: "cir-ins-note", textContent: "Macro overview active. Switch to Zoom 1 (Bundle) or Zoom 2 (Theorem) — or click any highlighted node in the SVG — to cross-zoom." }));
      return;
    }

    const filtered = list.filter((it) => {
      if (!q) return true;
      return ((it.name || "") + " " + (it.short || "") + " " + (it.badge || "")).toLowerCase().includes(q);
    });
    if (!filtered.length) {
      wrap.appendChild(el("span", { className: "cir-ins-note", textContent: "No pre-rendered " + mode + " shards match \"" + q + "\"." }));
      return;
    }
    filtered.forEach((it) => {
      const isAct = state.circuit.mode === mode && (state.circuit.target === it.name || state.circuit.target === it.short);
      wrap.appendChild(el("button", {
        type: "button",
        className: "cir-chip" + (isAct ? " active" : ""),
        title: it.name,
        onclick: () => navigate("#circuit/" + mode + "/" + encodeURIComponent(it.short || it.name))
      }, [
        el("span", { textContent: it.short || shortName(it.name) }),
        it.badge ? el("span", { className: "chip-tag", textContent: it.badge }) : null
      ]));
    });
  }

  async function renderCircuitView(subMode, argTarget) {
    const main = $("#appMain");
    const circuits = (state.manifest && state.manifest.circuits) || {};
    const mode = (subMode === "bundle" || subMode === "theorem" || subMode === "macro") ? subMode : "macro";
    const entry = findCircuitEntry(mode, argTarget) || (circuits.macro ? { mode: "macro", name: "Macro", short: "Macro", path: circuits.macro } : null);

    if (!entry) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No Proof Circuits Exported" }),
        el("p", { textContent: "This static site build does not contain pre-rendered circuit shards." })
      ]));
      return;
    }

    state.circuit.mode = entry.mode;
    state.circuit.target = entry.mode === "macro" ? "" : (entry.name || entry.short || "");
    state.circuit.selectedItem = null;
    state.circuit.hoveredItem = null;

    // Push breadcrumb history
    const last = state.circuit.history[state.circuit.history.length - 1];
    if (!last || last.mode !== state.circuit.mode || last.target !== state.circuit.target) {
      state.circuit.history.push({ mode: state.circuit.mode, target: state.circuit.target, short: entry.short || shortName(entry.name) });
      if (state.circuit.history.length > 20) state.circuit.history.shift();
    }

    clearEl(main);
    const shell = el("div", { className: "circuit-shell" });

    // Toolbar
    const modeSeg = el("div", { className: "seg", role: "tablist" }, [
      ["macro", "Zoom 0: Macro"],
      ["bundle", "Zoom 1: Bundles (" + (circuits.bundles || []).length + ")"],
      ["theorem", "Zoom 2: Theorems (" + (circuits.theorems || []).length + ")"]
    ].map(([mKey, lbl]) => el("button", {
      type: "button",
      className: state.circuit.mode === mKey ? "active" : "",
      textContent: lbl,
      onclick: () => {
        if (mKey === "macro") navigate("#circuit/macro");
        else {
          const list = mKey === "bundle" ? (circuits.bundles || []) : (circuits.theorems || []);
          const first = list[0];
          if (first) navigate("#circuit/" + mKey + "/" + encodeURIComponent(first.short || first.name));
        }
      }
    })));

    const crumbs = el("div", { className: "cir-crumbs", id: "cirCrumbs" });
    if (state.circuit.history.length > 1) {
      crumbs.appendChild(el("button", {
        type: "button", className: "btn sm", textContent: "← Back",
        onclick: () => {
          state.circuit.history.pop();
          const prev = state.circuit.history[state.circuit.history.length - 1];
          if (!prev || prev.mode === "macro") navigate("#circuit/macro");
          else navigate("#circuit/" + prev.mode + "/" + encodeURIComponent(prev.short || prev.target));
        }
      }));
    }
    state.circuit.history.slice(-5).forEach((h, idx, arr) => {
      if (idx > 0) crumbs.appendChild(el("span", { className: "cir-crumb-sep", textContent: "›" }));
      const cur = idx === arr.length - 1;
      crumbs.appendChild(el("button", {
        type: "button",
        className: "cir-crumb" + (cur ? " cur" : ""),
        textContent: h.mode === "macro" ? "Macro" : (h.short || shortName(h.target)),
        onclick: () => {
          if (cur) return;
          if (h.mode === "macro") navigate("#circuit/macro");
          else navigate("#circuit/" + h.mode + "/" + encodeURIComponent(h.short || h.target));
        }
      }));
    });

    const nodeHighlightInput = el("input", {
      type: "search", className: "input", id: "cirNodeFilter",
      placeholder: "Highlight nodes in SVG…", value: state.circuit.filter,
      style: { width: "175px", padding: "4px 8px", fontSize: "12px" },
      oninput: (ev) => { state.circuit.filter = ev.target.value; applyCircuitNodeHighlight(); }
    });

    const toolbar = el("div", { className: "cir-toolbar" }, [
      modeSeg,
      crumbs,
      el("div", { className: "spacer" }),
      nodeHighlightInput,
      el("button", { type: "button", className: "btn sm", textContent: "+", title: "Zoom in", onclick: () => { state.circuit.scale = Math.min(4, state.circuit.scale * 1.2); applyCircuitTransform(); } }),
      el("button", { type: "button", className: "btn sm", textContent: "−", title: "Zoom out", onclick: () => { state.circuit.scale = Math.max(0.16, state.circuit.scale / 1.2); applyCircuitTransform(); } }),
      el("button", { type: "button", className: "btn sm", textContent: "Fit", title: "Fit diagram", onclick: fitCircuitStage }),
      el("button", { type: "button", className: "btn sm", textContent: "1:1", title: "Reset scale", onclick: () => { state.circuit.scale = 1; state.circuit.tx = 16; state.circuit.ty = 16; applyCircuitTransform(); } }),
      el("button", {
        type: "button", className: "btn sm", textContent: "Download SVG",
        onclick: () => {
          const sh = state.circuit.shard;
          if (!sh) return;
          const txt = state.theme === "light" ? (sh.svg_light || sh.svg || sh.svg_dark) : (sh.svg_dark || sh.svg || sh.svg_light);
          if (!txt) return;
          const blob = new Blob([txt], { type: "image/svg+xml;charset=utf-8" });
          const u = URL.createObjectURL(blob);
          const a = el("a", { href: u, download: "leanre_circuit_" + state.circuit.mode + ".svg" });
          document.body.appendChild(a);
          a.click();
          a.remove();
          URL.revokeObjectURL(u);
        }
      })
    ]);

    // Selector chips bar
    const selBar = el("div", { className: "cir-selector-bar" });
    if (state.circuit.mode !== "macro") {
      selBar.appendChild(el("div", { className: "cir-selector-row" }, [
        el("input", {
          type: "search", className: "input", id: "cirChipFilter",
          placeholder: "Filter " + state.circuit.mode + " shards…",
          value: state.circuit.selectorFilter,
          style: { width: "220px", padding: "4px 8px", fontSize: "12px" },
          oninput: (ev) => { state.circuit.selectorFilter = ev.target.value; renderCircuitChips(state.circuit.mode); }
        }),
        el("span", { className: "cir-ins-note", textContent: "Select any pre-rendered " + state.circuit.mode + " shard:" })
      ]));
    }
    selBar.appendChild(el("div", { className: "cir-chips-wrap", id: "cirChipsWrap" }));

    // Legend bar
    const legBar = el("div", { className: "cir-legend-bar" }, [
      ["read / live", "emerald"], ["unread", "slate"], ["cond → / warn", "amber"], ["True stub / dropped", "crimson"], ["cross-zoomable", "cyan"]
    ].map(([lbl, cls]) => el("span", { className: "cir-leg-pill " + cls }, [el("i"), el("span", { textContent: lbl })])));

    // Stage + Inspector
    const body = el("div", { className: "cir-body" }, [
      el("div", { className: "cir-stage-wrap", id: "cirStageWrap" }, [
        el("div", { className: "cir-stage", id: "cirStage" }, [
          el("div", { className: "loading-card", style: { margin: "24px" } }, [
            el("div", { className: "spinner" }),
            el("div", { textContent: "Lazy-fetching circuit shard " + (entry.short || entry.name) + "…" })
          ])
        ])
      ]),
      el("aside", { className: "cir-inspector", id: "cirInspector", "aria-label": "Circuit node inspector" })
    ]);

    shell.appendChild(toolbar);
    shell.appendChild(selBar);
    shell.appendChild(legBar);
    shell.appendChild(body);
    main.appendChild(shell);

    renderCircuitChips(state.circuit.mode);
    wireCircuitStageEvents();

    try {
      const data = await fetchJson(entry.path);
      state.circuit.shard = data;
      mountActiveCircuitSvg();
      renderCircuitInspector(null, false);
    } catch (err) {
      const stg = $("#cirStage");
      if (stg) {
        clearEl(stg);
        stg.appendChild(el("div", { className: "empty-card", style: { margin: "24px" } }, [
          el("h3", { textContent: "Failed to fetch circuit shard" }),
          el("p", { textContent: String(err.message || err) })
        ]));
      }
    }
  }

  // ==========================================================================
  // VIEW 3: FINDINGS (`findings/*.md`)
  // ==========================================================================
  async function renderFindingsView(slugArg) {
    const main = $("#appMain");
    clearEl(main);
    const items = (state.manifest && state.manifest.findings) || [];
    if (!items.length) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No Findings Included" }),
        el("p", { textContent: "This static export has no curated findings chapters (typical for small or --demo repositories)." })
      ]));
      return;
    }

    const active = items.find((f) => f.slug === slugArg) || items.find((f) => f.slug === state.findingSlug) || items[0];
    state.findingSlug = active.slug;

    const sidebar = el("aside", { className: "doc-sidebar", "aria-label": "Findings chapters" }, [
      el("div", { className: "doc-sidebar-top" }, [
        el("strong", { textContent: "Findings (" + items.length + ")", style: { color: "var(--text-hi)", fontSize: "13px" } })
      ]),
      el("div", { className: "doc-list" }, items.map((f) =>
        el("button", {
          type: "button",
          className: "doc-item" + (f.slug === active.slug ? " active" : ""),
          onclick: () => navigate("#findings/" + encodeURIComponent(f.slug))
        }, [
          el("div", { className: "di-title", textContent: f.title || f.slug }),
          el("div", { className: "di-meta", textContent: f.slug + ".md · " + formatBytes(f.bytes || 0) })
        ])
      ))
    ]);

    const articleWrap = el("article", { className: "doc-article-wrap" }, [
      el("div", { className: "doc-article-meta" }, [
        el("span", { textContent: "findings/" + active.slug + ".md" }),
        el("span", { textContent: formatBytes(active.bytes || 0) + " · lazy-loaded" })
      ]),
      el("div", { className: "md-body", id: "findingMdBody" }, [
        el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading " + active.slug + ".md…" })])
      ])
    ]);

    main.appendChild(el("div", { className: "doc-layout" }, [sidebar, articleWrap]));

    try {
      const md = await fetchText(active.path);
      const body = $("#findingMdBody");
      if (body) body.innerHTML = renderMarkdownBlockSafe(md, "findings");
    } catch (err) {
      const body = $("#findingMdBody");
      if (body) {
        clearEl(body);
        body.appendChild(el("div", { className: "empty-card" }, [
          el("h3", { textContent: "Unable to load finding" }),
          el("p", { textContent: String(err.message || err) })
        ]));
      }
    }
  }

  // ==========================================================================
  // VIEW 4: DOSSIERS (`analysis/*.md` + `research/*.md`)
  // ==========================================================================
  function inferDossierCategory(d) {
    if (d.category) return d.category;
    const s = String(d.slug || "").toLowerCase();
    if (s.startsWith("audit_")) return "Math audits";
    if (s.startsWith("adversarial_")) return "Semantic rechecks";
    if (s.startsWith("dom1000_") || s.startsWith("dom1500_")) return "dom >= 1,000 closures";
    if (s.startsWith("pillar_") || s.startsWith("theta_") || s.startsWith("vwin_") || s.startsWith("allrows_")) return "Pillars";
    if (s.includes("hironaka") || s.includes("kato") || s.includes("siegel") || s.includes("classical") || s.includes("famous") || s.includes("harish")) return "Classical theorems";
    if (s.includes("benchmark") || s.includes("sweep") || s.includes("generic_corpus") || s.includes("portability") || s.includes("cluster_atlas") || s.includes("compute_and")) return "Benchmarks & sweeps";
    return "Core";
  }

  async function renderDossiersView(sub, arg) {
    const main = $("#appMain");
    clearEl(main);
    const dossiers = (state.manifest && state.manifest.dossiers) || [];
    const research = (state.manifest && state.manifest.research) || [];

    if (!dossiers.length && !research.length) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No Technical Dossiers Included" }),
        el("p", { textContent: "This static export has no analysis or research markdown dossiers." })
      ]));
      return;
    }

    if (sub === "research" && research.length) {
      state.dossierMode = "research";
      if (arg) state.dossierSlug = arg;
    } else if (sub) {
      state.dossierMode = "analysis";
      state.dossierSlug = sub;
    }

    const activePool = state.dossierMode === "research" ? research : dossiers;
    const active = activePool.find((x) => x.slug === state.dossierSlug) || activePool[0] || null;
    if (active) state.dossierSlug = active.slug;

    const categories = ["all"];
    if (state.dossierMode === "analysis") {
      dossiers.forEach((d) => {
        const c = inferDossierCategory(d);
        if (!categories.includes(c)) categories.push(c);
      });
    }

    const sidebarTop = el("div", { className: "doc-sidebar-top" }, [
      research.length ? el("div", { className: "seg" }, [
        el("button", {
          type: "button", className: state.dossierMode === "analysis" ? "active" : "",
          textContent: "Dossiers (" + dossiers.length + ")",
          onclick: () => { state.dossierMode = "analysis"; state.dossierSlug = ""; navigate("#dossiers"); }
        }),
        el("button", {
          type: "button", className: state.dossierMode === "research" ? "active" : "",
          textContent: "Research (" + research.length + ")",
          onclick: () => { state.dossierMode = "research"; state.dossierSlug = ""; navigate("#dossiers/research"); }
        })
      ]) : el("strong", { textContent: "Dossiers (" + dossiers.length + ")", style: { color: "var(--text-hi)", fontSize: "13px" } }),
      el("input", {
        type: "search", className: "input", id: "dossierSearchInput",
        placeholder: "Filter " + state.dossierMode + "…",
        value: state.dossierQ,
        oninput: (ev) => { state.dossierQ = ev.target.value; populateDossierList(); }
      }),
      (state.dossierMode === "analysis" && categories.length > 2) ? el("select", {
        className: "select", id: "dossierCatSel",
        onchange: (ev) => { state.dossierCat = ev.target.value; populateDossierList(); }
      }, categories.map((c) => el("option", { value: c, selected: state.dossierCat === c, textContent: c === "all" ? "All categories" : c }))) : null
    ]);

    const listEl = el("div", { className: "doc-list", id: "dossierListEl" });
    const populateDossierList = () => {
      clearEl(listEl);
      const q = state.dossierQ.trim().toLowerCase();
      const filtered = activePool.filter((d) => {
        if (state.dossierMode === "analysis" && state.dossierCat !== "all" && inferDossierCategory(d) !== state.dossierCat) return false;
        if (!q) return true;
        return ((d.title || "") + " " + (d.slug || "") + " " + inferDossierCategory(d)).toLowerCase().includes(q);
      });
      if (!filtered.length) {
        listEl.appendChild(el("div", { className: "cir-ins-note", style: { padding: "12px" }, textContent: "No matching dossiers." }));
        return;
      }
      if (state.dossierMode === "analysis") {
        const grouped = new Map();
        for (const d of filtered) {
          const cat = inferDossierCategory(d);
          if (!grouped.has(cat)) grouped.set(cat, []);
          grouped.get(cat).push(d);
        }
        for (const [cat, items] of grouped.entries()) {
          listEl.appendChild(el("div", { className: "doc-cat-hdr", textContent: cat + " (" + items.length + ")" }));
          for (const d of items) {
            listEl.appendChild(el("button", {
              type: "button",
              className: "doc-item" + (active && d.slug === active.slug ? " active" : ""),
              onclick: () => navigate("#dossiers/" + encodeURIComponent(d.slug))
            }, [
              el("div", { className: "di-title", textContent: d.title || d.slug }),
              el("div", { className: "di-meta", textContent: d.slug + ".md · " + formatBytes(d.bytes || 0) })
            ]));
          }
        }
      } else {
        for (const d of filtered) {
          listEl.appendChild(el("button", {
            type: "button",
            className: "doc-item" + (active && d.slug === active.slug ? " active" : ""),
            onclick: () => navigate("#dossiers/research/" + encodeURIComponent(d.slug))
          }, [
            el("div", { className: "di-title", textContent: d.title || d.slug }),
            el("div", { className: "di-meta", textContent: d.slug + ".md · " + formatBytes(d.bytes || 0) })
          ]));
        }
      }
    };

    const articleWrap = el("article", { className: "doc-article-wrap" });
    if (active) {
      articleWrap.appendChild(el("div", { className: "doc-article-meta" }, [
        el("span", { textContent: (state.dossierMode === "research" ? "research/" : "analysis/") + active.slug + ".md" }),
        el("span", { textContent: (state.dossierMode === "analysis" ? inferDossierCategory(active) + " · " : "") + formatBytes(active.bytes || 0) })
      ]));
      articleWrap.appendChild(el("div", { className: "md-body", id: "dossierMdBody" }, [
        el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Lazy-fetching " + active.slug + ".md…" })])
      ]));
    } else {
      articleWrap.appendChild(el("div", { className: "empty-card" }, [el("p", { textContent: "Select a dossier from the directory." })]));
    }

    main.appendChild(el("div", { className: "doc-layout" }, [
      el("aside", { className: "doc-sidebar", "aria-label": "Dossiers directory" }, [sidebarTop, listEl]),
      articleWrap
    ]));
    populateDossierList();

    if (active) {
      try {
        const md = await fetchText(active.path);
        const body = $("#dossierMdBody");
        if (body) body.innerHTML = renderMarkdownBlockSafe(md, state.dossierMode === "research" ? "research" : "analysis");
      } catch (err) {
        const body = $("#dossierMdBody");
        if (body) {
          clearEl(body);
          body.appendChild(el("div", { className: "empty-card" }, [
            el("h3", { textContent: "Failed to load dossier" }),
            el("p", { textContent: String(err.message || err) })
          ]));
        }
      }
    }
  }

  // ==========================================================================
  // VIEW 5: DECOMPILATION BLUEPRINTS (`outputs/decomp/*.json`)
  // ==========================================================================
  function normalizeBlueprintNodes(doc) {
    const raw = doc && doc.nodes;
    if (Array.isArray(raw)) {
      return raw.filter((n) => n && (n.id || n.fqn)).map((n) => Object.assign({}, n, {
        id: String(n.id || n.fqn),
        dom_sub: n.dom && n.dom.subtree != null ? Number(n.dom.subtree) : (n.dom_subtree != null ? Number(n.dom_subtree) : -1)
      }));
    }
    if (raw && typeof raw === "object") {
      return Object.entries(raw).map(([k, v]) => Object.assign({}, v, {
        id: String((v && (v.id || v.fqn)) || k),
        dom_sub: v && v.dom && v.dom.subtree != null ? Number(v.dom.subtree) : -1
      }));
    }
    return [];
  }

  function statusPillClass(st) {
    const u = String(st || "").toUpperCase();
    if (u === "READ" || u === "REAL" || u === "STANDALONE-READY" || u === "ALIGNED" || u === "PASS") return "emerald";
    if (u === "PARTIAL" || u === "WRAPPER" || u === "PROXY" || u === "SCOPED" || u === "PARTIAL_DRIFT" || u === "MODERATE") return "amber";
    if (u === "OPAQUE" || u === "DEGENERATE" || u === "VACUOUS" || u === "CROSS_DOMAIN_MISPLACED" || u === "HIGH" || u === "FAIL") return "crimson";
    return "slate";
  }

  async function renderBlueprintsView(bpArg) {
    const main = $("#appMain");
    clearEl(main);
    const bps = (state.manifest && state.manifest.blueprints) || [];
    if (!bps.length) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No Decompilation Blueprints Exported" }),
        el("p", { textContent: "This static build contains no leanre.decomp/v1 blueprint shards." })
      ]));
      return;
    }

    const active = bps.find((b) => b.id === bpArg) || bps.find((b) => b.id === state.bpId) || bps[0];
    state.bpId = active.id;

    const sidebarList = el("div", { className: "doc-list", id: "bpListEl" });
    let bpListFilter = "";
    const fillBpList = () => {
      clearEl(sidebarList);
      const q = bpListFilter.trim().toLowerCase();
      bps.filter((b) => !q || ((b.id || "") + " " + (b.title || "")).toLowerCase().includes(q)).forEach((b) => {
        sidebarList.appendChild(el("button", {
          type: "button",
          className: "doc-item" + (b.id === active.id ? " active" : ""),
          onclick: () => { state.bpPage = 0; state.bpSelectedNode = ""; navigate("#blueprints/" + encodeURIComponent(b.id)); }
        }, [
          el("div", { className: "di-title", textContent: b.title || b.id }),
          el("div", { className: "di-meta", textContent: fmtInt(b.node_count) + " nodes · " + fmtInt(b.non_opaque_count) + " read · " + formatBytes(b.bytes || 0) })
        ]));
      });
    };

    const contentBox = el("div", { id: "bpContentBox" }, [
      el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Lazy-fetching blueprint " + active.id + "…" })])
    ]);

    main.appendChild(el("div", { className: "doc-layout" }, [
      el("aside", { className: "doc-sidebar", "aria-label": "Decompilation blueprints" }, [
        el("div", { className: "doc-sidebar-top" }, [
          el("strong", { textContent: "Blueprints (" + bps.length + ")", style: { color: "var(--text-hi)", fontSize: "13px" } }),
          el("input", {
            type: "search", className: "input", placeholder: "Filter blueprints…",
            oninput: (ev) => { bpListFilter = ev.target.value; fillBpList(); }
          })
        ]),
        sidebarList
      ]),
      contentBox
    ]));
    fillBpList();

    try {
      const doc = await fetchJson(active.path);
      renderBlueprintDetail(doc, active);
    } catch (err) {
      clearEl(contentBox);
      contentBox.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Failed to load blueprint" }),
        el("p", { textContent: String(err.message || err) })
      ]));
    }
  }

  function renderBlueprintDetail(doc, metaEntry) {
    const box = $("#bpContentBox");
    if (!box) return;
    clearEl(box);

    const nodes = normalizeBlueprintNodes(doc);
    const claims = Array.isArray(doc.claims) ? doc.claims : [];
    const horn = Array.isArray(doc.horn) ? doc.horn : [];
    const PAGE = 60;

    // Filter & sort
    const q = state.bpQ.trim().toLowerCase();
    const filtered = nodes.filter((n) => {
      if (state.bpStatus !== "all" && String(n.status || "").toUpperCase() !== state.bpStatus) return false;
      if (!q) return true;
      return ((n.id || "") + " " + (n.role || "") + " " + (n.summary || "") + " " + (n.header || "") + " " + (n.anchor || "")).toLowerCase().includes(q);
    });

    const sk = state.bpSort.key;
    const mul = state.bpSort.dir === "asc" ? 1 : -1;
    filtered.sort((a, b) => {
      if (sk === "dom") return ((a.dom_sub - b.dom_sub) * mul) || a.id.localeCompare(b.id);
      const av = String(a[sk] || "").toLowerCase();
      const bv = String(b[sk] || "").toLowerCase();
      return (av.localeCompare(bv) * mul) || a.id.localeCompare(b.id);
    });

    const maxPage = Math.max(0, Math.ceil(filtered.length / PAGE) - 1);
    if (state.bpPage > maxPage) state.bpPage = 0;
    const slice = filtered.slice(state.bpPage * PAGE, (state.bpPage + 1) * PAGE);
    const sel = filtered.find((n) => n.id === state.bpSelectedNode) || slice[0] || null;
    if (sel) state.bpSelectedNode = sel.id;

    // Header
    box.appendChild(el("div", { className: "panel", style: { marginBottom: "12px" } }, [
      el("div", { className: "section-hdr", style: { margin: "0 0 8px" } }, [
        el("h2", { textContent: metaEntry.title || doc.pillar || metaEntry.id }),
        el("span", { className: "pill cyan", textContent: doc.root ? "root: " + shortName(doc.root) : metaEntry.id })
      ]),
      el("div", { className: "hero-meta", style: { marginTop: "0" } }, [
        el("span", { className: "pill emerald", textContent: fmtInt(nodes.length) + " nodes" }),
        el("span", { className: "pill slate", textContent: fmtInt((doc.edges || []).length) + " edges" }),
        el("span", { className: "pill cyan", textContent: fmtInt(claims.length) + " claims" }),
        el("span", { className: "pill amber", textContent: fmtInt(horn.length) + " Horn rules" })
      ])
    ]));

    // Controls
    const stSeg = el("div", { className: "seg" }, ["all", "READ", "PARTIAL", "OPAQUE"].map((st) =>
      el("button", {
        type: "button", className: state.bpStatus === st ? "active" : "", textContent: st,
        onclick: () => { state.bpStatus = st; state.bpPage = 0; renderBlueprintDetail(doc, metaEntry); }
      })
    ));

    box.appendChild(el("div", { className: "toolbar-row" }, [
      stSeg,
      el("input", {
        type: "search", className: "input grow", id: "bpNodeSearch",
        placeholder: "Filter declarations, summaries, headers, anchors…",
        value: state.bpQ,
        oninput: (ev) => {
          const pos = ev.target.selectionStart;
          state.bpQ = ev.target.value;
          state.bpPage = 0;
          renderBlueprintDetail(doc, metaEntry);
          const inp = $("#bpNodeSearch");
          if (inp) { inp.focus(); if (pos != null) inp.setSelectionRange(pos, pos); }
        }
      }),
      el("span", { className: "pill slate", textContent: fmtInt(filtered.length) + " shown" })
    ]));

    // Sortable Table + Side Inspector
    const makeTh = (label, key, num) => {
      const arrow = state.bpSort.key === key ? (state.bpSort.dir === "asc" ? " ▲" : " ▼") : "";
      return el("th", {
        className: "sortable" + (num ? " num" : ""),
        textContent: label + arrow,
        onclick: () => {
          if (state.bpSort.key === key) state.bpSort.dir = state.bpSort.dir === "asc" ? "desc" : "asc";
          else state.bpSort = { key, dir: key === "dom" ? "desc" : "asc" };
          renderBlueprintDetail(doc, metaEntry);
        }
      });
    };

    const tbody = el("tbody", null, slice.map((n) => {
      const cir = findAnyCircuitForSymbol(n.id);
      return el("tr", {
        className: "clickable" + (sel && sel.id === n.id ? " selected" : ""),
        onclick: () => { state.bpSelectedNode = n.id; renderBlueprintDetail(doc, metaEntry); }
      }, [
        el("td", null, [
          n.tag ? el("span", { className: "ev-tag " + (["K", "L", "S", "M"].includes(n.tag) ? n.tag : "L"), textContent: "[" + n.tag + "]", style: { marginRight: "5px" } }) : null,
          el("code", { textContent: n.id }),
          n.anchor ? el("div", { style: { fontSize: "11px", marginTop: "2px" } }, [makeGithubAnchor(n.anchor)]) : null
        ]),
        el("td", null, [
          el("span", { className: "pill " + statusPillClass(n.status), textContent: n.status || "—" }),
          n.verdict ? el("span", { className: "pill " + statusPillClass(n.verdict), textContent: n.verdict, style: { marginLeft: "4px" } }) : null
        ]),
        el("td", { className: "num", textContent: n.dom_sub >= 0 ? fmtInt(n.dom_sub) : "—" }),
        el("td", null, [
          cir ? el("button", {
            type: "button", className: "btn sm primary", textContent: "Circuit",
            onclick: (ev) => { ev.stopPropagation(); navigate("#circuit/" + cir.mode + "/" + encodeURIComponent(cir.short || cir.name)); }
          }) : el("span", { className: "cir-ins-note", textContent: n.role || n.kind || "—" })
        ])
      ]);
    }));

    const tableSide = el("div", null, [
      el("div", { className: "table-wrap" }, [
        el("table", { className: "data-table" }, [
          el("thead", null, [el("tr", null, [
            makeTh("Declaration", "id", false),
            makeTh("Status / Verdict", "status", false),
            makeTh("Dom", "dom", true),
            makeTh("Role / View", "role", false)
          ])]),
          tbody
        ])
      ]),
      filtered.length > PAGE ? el("div", { className: "pager" }, [
        el("button", { type: "button", className: "btn sm", disabled: state.bpPage <= 0, textContent: "← Prev", onclick: () => { state.bpPage--; renderBlueprintDetail(doc, metaEntry); } }),
        el("span", { textContent: "Page " + (state.bpPage + 1) + " of " + (maxPage + 1) + " (" + fmtInt(filtered.length) + " nodes)" }),
        el("button", { type: "button", className: "btn sm", disabled: state.bpPage >= maxPage, textContent: "Next →", onclick: () => { state.bpPage++; renderBlueprintDetail(doc, metaEntry); } })
      ]) : null
    ]);

    const ins = el("aside", { className: "bp-inspector" });
    if (sel) {
      const cir = findAnyCircuitForSymbol(sel.id);
      ins.appendChild(el("div", { className: "cir-ins-hd" }, [
        el("span", { textContent: "Node Contract" }),
        el("span", { className: "pill " + statusPillClass(sel.status), textContent: sel.status || "—" })
      ]));
      ins.appendChild(el("div", { className: "cir-ins-title", textContent: sel.id }));
      if (sel.header) ins.appendChild(el("div", { className: "bp-header-box", textContent: sel.header }));
      if (sel.summary) ins.appendChild(el("div", { className: "cir-ins-note", textContent: sel.summary }));
      const kv = el("div", { className: "cir-ins-kv" });
      const addKv = (k, v) => { if (v != null && v !== "") { kv.appendChild(el("div", { className: "k", textContent: k })); kv.appendChild(el("div", { className: "v", textContent: String(v) })); } };
      addKv("Kind / Role", (sel.kind || "—") + " / " + (sel.role || "—"));
      addKv("Module", sel.module || "—");
      if (sel.dom_sub >= 0) addKv("Dom Subtree", fmtInt(sel.dom_sub));
      if (sel.dom && sel.dom.idom) addKv("Immediate Dom", sel.dom.idom);
      ins.appendChild(kv);
      const acts = el("div", { className: "cir-ins-acts" });
      if (cir) {
        acts.appendChild(el("button", {
          type: "button", className: "btn sm primary", textContent: "Open Proof Circuit →",
          onclick: () => navigate("#circuit/" + cir.mode + "/" + encodeURIComponent(cir.short || cir.name))
        }));
      }
      if (sel.anchor) {
        const gh = buildGithubUrl(sel.anchor);
        if (gh) acts.appendChild(el("a", { className: "btn sm", href: gh, target: "_blank", rel: "noopener noreferrer", textContent: "GitHub Source ↗" }));
      }
      if (acts.childNodes.length) ins.appendChild(acts);
    } else {
      ins.appendChild(el("div", { className: "cir-ins-note", textContent: "No node matches the current filter." }));
    }

    box.appendChild(el("div", { className: "bp-detail-split" }, [tableSide, ins]));

    // Claims preview
    if (claims.length) {
      box.appendChild(el("div", { className: "section-hdr" }, [
        el("h2", { textContent: "Extracted Claims (" + claims.length + ")" })
      ]));
      box.appendChild(el("div", { className: "table-wrap" }, [
        el("table", { className: "data-table" }, [
          el("thead", null, [el("tr", null, [el("th", { textContent: "Tag" }), el("th", { textContent: "Claim" }), el("th", { textContent: "Anchors" })])]),
          el("tbody", null, claims.slice(0, 40).map((c) => {
            const txt = typeof c === "string" ? c : (c.text || "");
            const tag = typeof c === "string" ? "L" : (c.tag || "L");
            const ancs = (c && Array.isArray(c.anchors)) ? c.anchors : [];
            return el("tr", null, [
              el("td", null, [el("span", { className: "ev-tag " + (["K", "L", "S", "M"].includes(tag) ? tag : "L"), textContent: "[" + tag + "]" })]),
              el("td", { textContent: txt }),
              el("td", null, ancs.slice(0, 3).map((a) => el("div", null, [makeGithubAnchor(a)])))
            ]);
          }))
        ])
      ]));
    }
  }

  // ==========================================================================
  // VIEW 6: FLIRT 141-CLUSTER ATLAS
  // ==========================================================================
  async function renderFlirtView() {
    const main = $("#appMain");
    clearEl(main);
    const assetPath = state.manifest && state.manifest.assets && state.manifest.assets.cluster_labels;
    if (!assetPath) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No FLIRT Cluster Atlas Available" }),
        el("p", { textContent: "This static export does not include cluster_labels_141.json (expected on small or --demo repositories)." })
      ]));
      return;
    }

    main.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Lazy-fetching FLIRT Cluster Atlas…" })]));
    try {
      const doc = await fetchJson(assetPath);
      renderFlirtBody(doc);
    } catch (err) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Failed to load FLIRT Atlas" }),
        el("p", { textContent: String(err.message || err) })
      ]));
    }
  }

  function renderFlirtBody(doc) {
    const main = $("#appMain");
    clearEl(main);
    const clusters = Array.isArray(doc.clusters) ? doc.clusters : [];
    const totals = doc.totals || {};
    const statusCounts = totals.mismatch_status_counts || {};
    const sevCounts = totals.mismatch_severity_counts || {};
    const misplaced = Number(statusCounts.cross_domain_misplaced || clusters.filter((c) => (c.mismatch_audit && c.mismatch_audit.status) === "cross_domain_misplaced").length);
    const drift = Number(statusCounts.partial_drift || clusters.filter((c) => (c.mismatch_audit && c.mismatch_audit.status) === "partial_drift").length);
    const aligned = Number(statusCounts.aligned || clusters.filter((c) => (c.mismatch_audit && c.mismatch_audit.status) === "aligned").length);
    const highSev = Number(sevCounts.high || clusters.filter((c) => (c.mismatch_audit && c.mismatch_audit.severity) === "high").length);
    const totalN = Math.max(1, misplaced + drift + aligned);

    main.appendChild(el("div", { className: "section-hdr", style: { marginTop: "0" } }, [
      el("h2", { textContent: "FLIRT Structural Atlas (" + clusters.length + " Clusters)" }),
      el("span", { className: "sub", textContent: "Name-blinded mathematical domain [M] vs actual directory path [L]" })
    ]));

    if (doc.epistemic_note) {
      main.appendChild(el("div", { className: "scope-banner" }, [
        el("span", { className: "scope-tag", textContent: "Blinded Audit" }),
        el("div", { textContent: doc.epistemic_note })
      ]));
    }

    main.appendChild(el("section", { className: "kpi-strip" }, [
      { label: "Total Clusters", val: fmtInt(clusters.length), sub: (totals.collapse_pct != null ? totals.collapse_pct + "% core collapse" : "coarse FLIRT"), cls: "cyan" },
      { label: "Cross-Domain Misplaced", val: fmtInt(misplaced), sub: fmtInt(highSev) + " high severity", cls: "crimson" },
      { label: "Partial / Naming Drift", val: fmtInt(drift), sub: "moderate / low drift", cls: "amber" },
      { label: "Aligned", val: fmtInt(aligned), sub: "path matches domain", cls: "emerald" }
    ].map((k) => el("div", { className: "kpi-card" }, [
      el("div", { className: "kpi-label", textContent: k.label }),
      el("div", { className: "kpi-val " + k.cls, textContent: k.val }),
      el("div", { className: "kpi-sub", textContent: k.sub })
    ]))));

    // Stacked breakdown bar
    main.appendChild(el("div", { className: "stacked-bar", title: "Misplaced / Drift / Aligned" }, [
      el("div", { className: "seg-misplaced", style: { width: ((misplaced / totalN) * 100).toFixed(1) + "%" } }),
      el("div", { className: "seg-drift", style: { width: ((drift / totalN) * 100).toFixed(1) + "%" } }),
      el("div", { className: "seg-aligned", style: { width: ((aligned / totalN) * 100).toFixed(1) + "%" } })
    ]));

    // Filters
    const statusSeg = el("div", { className: "seg" }, [
      ["all", "All"], ["cross_domain_misplaced", "Misplaced"], ["partial_drift", "Drift"], ["aligned", "Aligned"]
    ].map(([k, lbl]) => el("button", {
      type: "button", className: state.flirt.status === k ? "active" : "", textContent: lbl,
      onclick: () => { state.flirt.status = k; state.flirt.page = 0; renderFlirtBody(doc); }
    })));

    const sevSel = el("select", {
      className: "select",
      onchange: (ev) => { state.flirt.severity = ev.target.value; state.flirt.page = 0; renderFlirtBody(doc); }
    }, ["all", "high", "moderate", "low", "none"].map((s) =>
      el("option", { value: s, selected: state.flirt.severity === s, textContent: "severity: " + s })
    ));

    const q = state.flirt.q.trim().toLowerCase();
    const filtered = clusters.filter((c) => {
      const ma = c.mismatch_audit || {};
      const bl = c.blinded_label || {};
      if (state.flirt.status !== "all" && ma.status !== state.flirt.status) return false;
      if (state.flirt.severity !== "all" && ma.severity !== state.flirt.severity) return false;
      if (!q) return true;
      const hay = [c.cluster_id, c.pillar, c.root_decl, bl.label, bl.primary_domain, ma.folder_l2, ma.reason].join(" ").toLowerCase();
      return hay.includes(q);
    });

    const PAGE = 50;
    const maxPage = Math.max(0, Math.ceil(filtered.length / PAGE) - 1);
    if (state.flirt.page > maxPage) state.flirt.page = 0;
    const slice = filtered.slice(state.flirt.page * PAGE, (state.flirt.page + 1) * PAGE);

    main.appendChild(el("div", { className: "toolbar-row" }, [
      statusSeg,
      sevSel,
      el("input", {
        type: "search", className: "input grow", id: "flirtSearchInput", placeholder: "Search cluster ID, domain, directory path, root decl…",
        value: state.flirt.q,
        oninput: (ev) => {
          const pos = ev.target.selectionStart;
          state.flirt.q = ev.target.value;
          state.flirt.page = 0;
          renderFlirtBody(doc);
          const inp = $("#flirtSearchInput");
          if (inp) { inp.focus(); if (pos != null) inp.setSelectionRange(pos, pos); }
        }
      }),
      el("span", { className: "pill slate", textContent: fmtInt(filtered.length) + " clusters" })
    ]));

    main.appendChild(el("div", { className: "table-wrap" }, [
      el("table", { className: "data-table" }, [
        el("thead", null, [el("tr", null, [
          el("th", { textContent: "Cluster" }),
          el("th", { textContent: "Blinded Math Domain [M]" }),
          el("th", { textContent: "Actual Directory Path [L]" }),
          el("th", { textContent: "Audit Status" }),
          el("th", { className: "num", textContent: "Live / Core" })
        ])]),
        el("tbody", null, slice.map((c) => {
          const cnt = c.counts || {};
          const bl = c.blinded_label || {};
          const ma = c.mismatch_audit || {};
          const reps = Array.isArray(c.top3_rep_decls) ? c.top3_rep_decls : [];
          return el("tr", null, [
            el("td", null, [
              el("code", { textContent: c.cluster_id }),
              el("div", { className: "cir-ins-note", textContent: c.pillar || c.kind || "" })
            ]),
            el("td", null, [
              el("span", { className: "ev-tag M", textContent: "[M]", style: { marginRight: "5px" } }),
              el("strong", { textContent: bl.label || bl.primary_domain || "—", style: { color: "var(--text-hi)" } }),
              bl.primary_domain ? el("div", { className: "cir-ins-note mono", textContent: bl.primary_domain + (bl.secondary_domain ? " / " + bl.secondary_domain : "") }) : null
            ]),
            el("td", null, [
              el("code", { textContent: ma.folder_l2 || "—" }),
              reps.length ? el("div", { style: { marginTop: "4px", fontSize: "11px" } }, reps.slice(0, 2).map((r) => {
                const u = safeHref(r.github_url) || buildGithubUrl(r.module, r.line);
                return el("div", null, [
                  u ? el("a", { href: u, target: "_blank", rel: "noopener noreferrer", className: "mono", textContent: shortName(r.name) })
                    : el("code", { textContent: shortName(r.name) })
                ]);
              })) : null
            ]),
            el("td", null, [
              el("span", { className: "pill " + statusPillClass(ma.status), textContent: ma.status || "—" }),
              ma.severity ? el("span", { className: "pill " + statusPillClass(ma.severity), textContent: ma.severity, style: { marginLeft: "4px" } }) : null,
              ma.reason ? el("div", { className: "cir-ins-note", style: { marginTop: "3px" }, textContent: ma.reason }) : null
            ]),
            el("td", { className: "num" }, [
              el("div", { textContent: fmtInt(cnt.live_decls) }),
              el("div", { className: "cir-ins-note", textContent: fmtInt(cnt.effective_core_decls) + " core" })
            ])
          ]);
        }))
      ])
    ]));

    if (filtered.length > PAGE) {
      main.appendChild(el("div", { className: "pager" }, [
        el("button", { type: "button", className: "btn sm", disabled: state.flirt.page <= 0, textContent: "← Prev", onclick: () => { state.flirt.page--; renderFlirtBody(doc); } }),
        el("span", { textContent: "Page " + (state.flirt.page + 1) + " of " + (maxPage + 1) }),
        el("button", { type: "button", className: "btn sm", disabled: state.flirt.page >= maxPage, textContent: "Next →", onclick: () => { state.flirt.page++; renderFlirtBody(doc); } })
      ]));
    }
  }

  // ==========================================================================
  // VIEW 6B: GENOME ATLAS (Hi-C 114M-Edge Matrix, Synteny & Alien-Proof Twins)
  // ==========================================================================
  const ATLAS_PILLAR_SHORT = {
    pillar_a: "A",
    pillar_d: "D",
    pillar_c: "C",
    pillar_b: "B",
    shared_diamond: "DM",
    bridge: "BR"
  };

  const SYNTENY_CORPUS_COLORS = [
    "#38bdf8", // mathlib4
    "#34d399", // lean4
    "#2dd4bf", // batteries
    "#f59e0b", // PrimeNumberTheoremAnd
    "#fb7185", // FLT
    "#60a5fa", // carleson
    "#facc15", // SpherePacking
    "#94a3b8"  // library_other
  ];

  function atlasRegionForDfs(regions, dfsIdx) {
    if (!Array.isArray(regions)) return null;
    for (const r of regions) {
      if (dfsIdx >= r.dfs_start && dfsIdx < r.dfs_end) return r;
    }
    return regions[regions.length - 1] || null;
  }

  function atlasDrawHicCanvas(canvas, hic, mode) {
    if (!canvas || !hic || !hic.tile_128) return;
    const tile = hic.tile_128;
    const N = Number(tile.size) || 128;
    const totGrid = tile.total_log1p_q8 || [];
    const ratGrid = tile.ratio_diverging_q8 || [];
    const neutral = Number(tile.neutral_ratio_q8 ?? 128);
    const scale = 4;
    const pad = 26;
    const size = N * scale;
    canvas.width = size + pad;
    canvas.height = size + pad;
    const ctx = canvas.getContext("2d");
    if (!ctx) return;

    ctx.fillStyle = "#080b14";
    ctx.fillRect(0, 0, canvas.width, canvas.height);

    // Offscreen 128x128 ImageData for crisp pixel-art blit
    const off = document.createElement("canvas");
    off.width = N;
    off.height = N;
    const octx = off.getContext("2d");
    const img = octx.createImageData(N, N);
    const data = img.data;

    for (let y = 0; y < N; y++) {
      const tRow = totGrid[y] || [];
      const rRow = ratGrid[y] || [];
      for (let x = 0; x < N; x++) {
        const idx = (y * N + x) * 4;
        const tq = Number(tRow[x] || 0);
        if (tq <= 0) {
          data[idx] = 10; data[idx + 1] = 12; data[idx + 2] = 18; data[idx + 3] = 255;
          continue;
        }
        const inten = Math.pow(tq / 255, 0.72);
        let r, g, b;
        if (mode === "density") {
          // Obsidian -> teal -> cyan -> amber hotspot
          if (inten < 0.5) {
            const u = inten * 2;
            r = Math.round(12 + u * 28);
            g = Math.round(30 + u * 165);
            b = Math.round(58 + u * 182);
          } else {
            const u = (inten - 0.5) * 2;
            r = Math.round(40 + u * 215);
            g = Math.round(195 + u * 10);
            b = Math.round(240 - u * 195);
          }
        } else {
          // Diverging cyan (#1ed7ff) <- silver (#dce2f7) -> amber (#ffaa23)
          const rq = Number(rRow[x] ?? neutral);
          const d = Math.max(-1, Math.min(1, (rq - neutral) / 127));
          let cr, cg, cb;
          if (d >= 0) {
            cr = 220 + (30 - 220) * d;
            cg = 226 + (215 - 226) * d;
            cb = 247 + (255 - 247) * d;
          } else {
            const a = -d;
            cr = 220 + (255 - 220) * a;
            cg = 226 + (170 - 226) * a;
            cb = 247 + (35 - 247) * a;
          }
          const k = 0.22 + 0.78 * inten;
          r = Math.round(10 + (cr - 10) * k);
          g = Math.round(12 + (cg - 12) * k);
          b = Math.round(18 + (cb - 18) * k);
        }
        data[idx] = r; data[idx + 1] = g; data[idx + 2] = b; data[idx + 3] = 255;
      }
    }
    octx.putImageData(img, 0, 0);
    ctx.imageSmoothingEnabled = false;
    ctx.drawImage(off, pad, pad, size, size);

    // Pillar boundary lines + labels (A | D | C | B | DM | BR)
    const ticks = (hic.pillar_ticks || []).filter((t) => ATLAS_PILLAR_SHORT[t.key]);
    ctx.strokeStyle = "rgba(226, 232, 240, 0.28)";
    ctx.lineWidth = 1;
    ctx.font = "bold 10px ui-monospace, Menlo, Consolas, monospace";
    ctx.fillStyle = "#cbd5e1";
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";

    for (const t of ticks) {
      const b0 = Number(t.bin128_start || 0);
      const b1 = Number(t.bin128_end || 0);
      const p0 = pad + b0 * scale;
      const p1 = pad + b1 * scale;
      const mid = (p0 + p1) / 2;
      if (b0 > 0.5) {
        ctx.beginPath();
        ctx.moveTo(p0 + 0.5, pad);
        ctx.lineTo(p0 + 0.5, pad + size);
        ctx.moveTo(pad, p0 + 0.5);
        ctx.lineTo(pad + size, p0 + 0.5);
        ctx.stroke();
      }
      const lbl = ATLAS_PILLAR_SHORT[t.key];
      if (p1 - p0 >= 14) {
        ctx.fillText(lbl, mid, pad / 2);
        ctx.fillText(lbl, pad / 2, mid);
      }
    }
    ctx.strokeStyle = "rgba(148, 163, 184, 0.45)";
    ctx.strokeRect(pad + 0.5, pad + 0.5, size - 1, size - 1);
  }

  function atlasDrawSyntenyCanvas(canvas, synteny, hic, opts) {
    if (!canvas || !synteny) return;
    const gm = synteny.grid_meta || {};
    const G = Number(gm.grid_size) || 128;
    const scale = 4;
    const padL = 32;
    const padB = 24;
    const padT = 14;
    const padR = 10;
    const size = G * scale;
    canvas.width = size + padL + padR;
    canvas.height = size + padT + padB;
    const ctx = canvas.getContext("2d");
    if (!ctx) return;

    ctx.fillStyle = "#080b14";
    ctx.fillRect(0, 0, canvas.width, canvas.height);

    // 1. Optional Terra Incognita vertical bands (pitch-black + subtle crimson edge)
    const ti = synteny.terra_incognita_bands || {};
    if (opts.showTerra && Array.isArray(ti.bands)) {
      for (const b of ti.bands) {
        const x0 = padL + (Number(b.bin256_start || 0) / 2) * scale;
        const x1 = padL + (Number(b.bin256_end || 0) / 2) * scale;
        const w = Math.max(2, x1 - x0);
        ctx.fillStyle = "rgba(239, 68, 68, 0.13)";
        ctx.fillRect(x0, padT, w, size);
        ctx.strokeStyle = "rgba(239, 68, 68, 0.40)";
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.moveTo(x0 + 0.5, padT); ctx.lineTo(x0 + 0.5, padT + size);
        ctx.moveTo(x0 + w - 0.5, padT); ctx.lineTo(x0 + w - 0.5, padT + size);
        ctx.stroke();
      }
    }

    // 2. Pillar vertical guides
    const ticks = ((hic && hic.pillar_ticks) || []).filter((t) => ATLAS_PILLAR_SHORT[t.key]);
    ctx.strokeStyle = "rgba(148, 163, 184, 0.22)";
    ctx.lineWidth = 1;
    ctx.font = "bold 10px ui-monospace, Menlo, Consolas, monospace";
    ctx.fillStyle = "#cbd5e1";
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    for (const t of ticks) {
      const b0 = Number(t.bin128_start || 0);
      const b1 = Number(t.bin128_end || 0);
      const x0 = padL + b0 * scale;
      const x1 = padL + b1 * scale;
      if (b0 > 0.5) {
        ctx.beginPath();
        ctx.moveTo(x0 + 0.5, padT);
        ctx.lineTo(x0 + 0.5, padT + size);
        ctx.stroke();
      }
      if (x1 - x0 >= 14) {
        ctx.fillText(ATLAS_PILLAR_SHORT[t.key], (x0 + x1) / 2, padT + size + padB / 2);
      }
    }

    // 3. Library strata horizontal guides
    const strata = Array.isArray(synteny.library_strata) ? synteny.library_strata : [];
    const nLib = Math.max(1, Number(synteny.n_library_decls) || 1);
    ctx.textAlign = "right";
    for (let s = 0; s < strata.length; s++) {
      const st = strata[s];
      const frac = Number(st.lib_idx_start || 0) / nLib;
      const y = padT + (1 - frac) * size;
      if (s > 0) {
        ctx.strokeStyle = "rgba(148, 163, 184, 0.14)";
        ctx.beginPath();
        ctx.moveTo(padL, y + 0.5);
        ctx.lineTo(padL + size, y + 0.5);
        ctx.stroke();
      }
      const midFrac = ((Number(st.lib_idx_start || 0) + Number(st.lib_idx_end || 0)) / 2) / nLib;
      ctx.fillStyle = "#8fa3bf";
      ctx.fillText("L" + s, padL - 5, padT + (1 - midFrac) * size);
    }

    // 4. Binned points [proj_bin, lib_bin, total_hits, named_hits, dominant_repo_idx]
    const pts = Array.isArray(synteny.binned_points) ? synteny.binned_points : [];
    for (const pt of pts) {
      const pb = Number(pt[0]);
      const lb = Number(pt[1]);
      const tot = Number(pt[2] || 1);
      const named = Number(pt[3] || 0);
      const rIdx = Number(pt[4] || 0);
      const px = padL + pb * scale;
      const py = padT + (G - 1 - lb) * scale;
      const alpha = Math.min(0.95, 0.22 + Math.log1p(tot) * 0.16);
      ctx.fillStyle = named > 0 ? "#34d399" : (SYNTENY_CORPUS_COLORS[rIdx] || "#38bdf8");
      ctx.globalAlpha = alpha;
      ctx.fillRect(px, py, scale, scale);
    }
    ctx.globalAlpha = 1;

    // 5. Named scatter points [proj_dfs_idx, lib_order_idx, kind_idx, repo_idx, type_nodes]
    const nLive = Math.max(1, Number(synteny.n_live_decls) || 1);
    if (opts.showNamed && Array.isArray(synteny.named_scatter)) {
      for (const ns of synteny.named_scatter) {
        const px = padL + (Number(ns[0]) / nLive) * size;
        const py = padT + (1 - Number(ns[1]) / nLib) * size;
        const rIdx = Number(ns[3] || 0);
        ctx.fillStyle = SYNTENY_CORPUS_COLORS[rIdx] || "#34d399";
        ctx.beginPath();
        ctx.arc(px, py, 2.3, 0, Math.PI * 2);
        ctx.fill();
      }
    }

    // 6. Golden diagonal streaks
    if (opts.showStreaks && Array.isArray(synteny.diagonal_streaks)) {
      ctx.strokeStyle = "#facc15";
      ctx.lineWidth = 2.4;
      for (const ds of synteny.diagonal_streaks) {
        const pr = ds.proj_bin_range || [0, 0];
        const lr = ds.lib_bin_range || [0, 0];
        const x0 = padL + (Number(pr[0]) + 0.5) * scale;
        const x1 = padL + (Number(pr[1]) + 0.5) * scale;
        const y0 = padT + (G - 0.5 - Number(lr[0])) * scale;
        const y1 = padT + (G - 0.5 - Number(lr[1])) * scale;
        ctx.beginPath();
        ctx.moveTo(x0, y0);
        ctx.lineTo(x1, y1);
        ctx.stroke();
      }
    }

    ctx.strokeStyle = "rgba(148, 163, 184, 0.45)";
    ctx.lineWidth = 1;
    ctx.strokeRect(padL + 0.5, padT + 0.5, size - 1, size - 1);
  }

  function atlasTwinRatio(pair) {
    const a = Math.max(1, Number((pair.thm_a && pair.thm_a.value_nodes) || 1));
    const b = Math.max(1, Number((pair.thm_b && pair.thm_b.value_nodes) || 1));
    return Math.max(a / b, b / a);
  }

  async function renderAtlasView() {
    const main = $("#appMain");
    clearEl(main);
    const assetPath = state.manifest && state.manifest.assets && state.manifest.assets.atlas;
    if (!assetPath) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No Genome Atlas Exported" }),
        el("p", { textContent: "This static export does not include atlas_summary.json (expected on small or --demo repositories)." })
      ]));
      return;
    }

    main.appendChild(el("div", { className: "loading-card" }, [
      el("div", { className: "spinner" }),
      el("div", { textContent: "Lazy-fetching Genome Atlas (Hi-C / Synteny / Alien-Proof Twins)…" })
    ]));
    try {
      const doc = await fetchJson(assetPath);
      renderAtlasBody(doc);
    } catch (err) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Failed to load Genome Atlas" }),
        el("p", { textContent: String(err.message || err) })
      ]));
    }
  }

  function renderAtlasBody(doc) {
    const main = $("#appMain");
    clearEl(main);

    const hic = doc.hic_matrix || {};
    const et = hic.edge_totals || {};
    const aliens = doc.alien_twins || {};
    const ac = aliens.counts || {};
    const ap = aliens.partitions || {};
    const syn = doc.synteny || {};
    const ht = syn.hit_totals || {};
    const ti = syn.terra_incognita_bands || {};

    main.appendChild(el("div", { className: "section-hdr", style: { marginTop: "0" } }, [
      el("h2", { textContent: "Genome Atlas — Hi-C Contact Matrix, Cross-Library Synteny & Alien-Proof Twins" }),
      el("span", { className: "sub", textContent: (doc.schema || "leanre.atlas/1") + " · " + fmtInt(hic.n_live_decls || 0) + " live decls in dominator-DFS order" })
    ]));

    // 1. Top KPI Strip
    const allAliens = (ap.all_sampled_pairs && ap.all_sampled_pairs.alien_proof) || 0;
    const crossAliens = (ap.cross_repo_pairs && ap.cross_repo_pairs.alien_proof) || 0;
    main.appendChild(el("section", { className: "kpi-strip" }, [
      { label: "Edges Binned (Hi-C)", val: fmtInt(et.total_streamed || 0), sub: fmtInt(et.type_only || 0) + " type · " + fmtInt(et.value_only || 0) + " val · " + fmtInt(et.both || 0) + " both", cls: "cyan" },
      { label: "Non-Trivial k1n Buckets", val: fmtInt(ac.nontrivial_collision_buckets || 0), sub: fmtInt(ac.named_collision_buckets || 0) + " named · " + fmtInt(ac.excluded_trivial_thms || 0) + " shells cut", cls: "" },
      { label: "Alien-Proof Pairs (J<0.2)", val: fmtInt(allAliens), sub: fmtInt(crossAliens) + " cross-repo vs Mathlib", cls: "crimson" },
      { label: "Synteny Matches", val: fmtInt(ht.total_matches || 0), sub: fmtInt(ht.named_matches || 0) + " named · " + fmtInt(syn.n_library_decls || 0) + " lib decls", cls: "emerald" },
      { label: "Terra Incognita Bands", val: fmtInt(ti.zero_named_match_bins_256 || 0) + " / " + fmtInt(ti.eligible_project_bins_256 || 0), sub: (ti.zero_named_share_pct != null ? ti.zero_named_share_pct + "% novel bins" : "0 named library hits"), cls: "amber" }
    ].map((k) => el("div", { className: "kpi-card" }, [
      el("div", { className: "kpi-label", textContent: k.label }),
      el("div", { className: "kpi-val " + k.cls, textContent: k.val }),
      el("div", { className: "kpi-sub", textContent: k.sub })
    ]))));

    // 2. Side-by-side HTML5 Canvas Panels: Hi-C + Synteny
    const hicCanvas = el("canvas", { id: "hicCanvas", className: "atlas-canvas", "aria-label": "114M-edge Hi-C contact matrix" });
    const hicReadout = el("div", { id: "hicReadout", className: "atlas-readout", textContent: "Hover any cell on the 128×128 Hi-C canvas to inspect region coupling, edge density, and log((E_T+1)/(E_V+1)) ratio." });

    const hicModeSeg = el("div", { className: "seg" }, [
      ["ratio", "Type/Value Ratio"],
      ["density", "Total Density"]
    ].map(([k, lbl]) => el("button", {
      type: "button", className: state.atlas.hicMode === k ? "active" : "", textContent: lbl,
      onclick: () => { state.atlas.hicMode = k; renderAtlasBody(doc); }
    })));

    const hicCard = el("section", { className: "atlas-card" }, [
      el("div", { className: "atlas-card-hd" }, [
        el("h3", { textContent: "114M-Edge Dominator-DFS Hi-C Contact Matrix" }),
        hicModeSeg
      ]),
      el("div", { className: "atlas-legend" }, [
        el("span", null, [el("i", { className: "atlas-swatch", style: { background: "#1ed7ff" } }), "Type-dominant (cyan)"]),
        el("span", null, [el("i", { className: "atlas-swatch", style: { background: "#dce2f7" } }), "Balanced"]),
        el("span", null, [el("i", { className: "atlas-swatch", style: { background: "#ffaa23" } }), "Value-dominant (amber)"]),
        el("span", { textContent: "· Diagonal 256-bin share: " + (et.diagonal_256_share_pct ?? "—") + "%" })
      ]),
      el("div", { className: "atlas-canvas-wrap" }, [hicCanvas]),
      hicReadout
    ]);

    const synCanvas = el("canvas", { id: "syntenyCanvas", className: "atlas-canvas", "aria-label": "Cross-library structural synteny dot-plot" });
    const synReadout = el("div", { id: "syntenyReadout", className: "atlas-readout", textContent: "Hover the Synteny dot-plot to inspect pillar vs library stratum, diagonal streaks, and terra-incognita novel bands." });

    const synToggles = el("div", { style: { display: "flex", gap: "10px", flexWrap: "wrap", alignItems: "center" } }, [
      el("label", { className: "atlas-toggle" }, [
        el("input", { type: "checkbox", checked: state.atlas.showTerra, onchange: (ev) => { state.atlas.showTerra = ev.target.checked; atlasDrawSyntenyCanvas(synCanvas, syn, hic, state.atlas); } }),
        "Terra incognita"
      ]),
      el("label", { className: "atlas-toggle" }, [
        el("input", { type: "checkbox", checked: state.atlas.showStreaks, onchange: (ev) => { state.atlas.showStreaks = ev.target.checked; atlasDrawSyntenyCanvas(synCanvas, syn, hic, state.atlas); } }),
        "Diagonal streaks"
      ]),
      el("label", { className: "atlas-toggle" }, [
        el("input", { type: "checkbox", checked: state.atlas.showNamed, onchange: (ev) => { state.atlas.showNamed = ev.target.checked; atlasDrawSyntenyCanvas(synCanvas, syn, hic, state.atlas); } }),
        "Named scatter"
      ])
    ]);

    const byCorpus = ht.by_corpus || {};
    const corpusPills = Object.entries(byCorpus).slice(0, 6).map(([k, v], idx) =>
      el("span", null, [el("i", { className: "atlas-swatch", style: { background: SYNTENY_CORPUS_COLORS[idx % SYNTENY_CORPUS_COLORS.length] } }), k + " " + fmtInt(v)])
    );

    const synCard = el("section", { className: "atlas-card" }, [
      el("div", { className: "atlas-card-hd" }, [
        el("h3", { textContent: "Cross-Library Structural Synteny Dot-Plot" }),
        synToggles
      ]),
      el("div", { className: "atlas-legend" }, [
        ...corpusPills,
        el("span", null, [el("i", { className: "atlas-swatch", style: { background: "#facc15" } }), "Streak (" + ((syn.diagonal_streaks || []).length) + ")"])
      ]),
      el("div", { className: "atlas-canvas-wrap" }, [synCanvas]),
      synReadout
    ]);

    main.appendChild(el("div", { className: "atlas-grid" }, [hicCard, synCard]));

    // Render both canvases + wire hover inspectors
    atlasDrawHicCanvas(hicCanvas, hic, state.atlas.hicMode);
    atlasDrawSyntenyCanvas(synCanvas, syn, hic, state.atlas);

    // Wire Hi-C hover readout
    const couplingMap = new Map();
    for (const rc of (hic.region_couplings || [])) {
      couplingMap.set(rc.src_region + "->" + rc.dst_region, rc);
    }
    hicCanvas.addEventListener("mousemove", (ev) => {
      const rect = hicCanvas.getBoundingClientRect();
      const cx = ((ev.clientX - rect.left) / rect.width) * hicCanvas.width;
      const cy = ((ev.clientY - rect.top) / rect.height) * hicCanvas.height;
      const pad = 26, scale = 4;
      const bx = Math.floor((cx - pad) / scale);
      const by = Math.floor((cy - pad) / scale);
      const tile = hic.tile_128 || {};
      const N = Number(tile.size) || 128;
      if (bx < 0 || bx >= N || by < 0 || by >= N) return;
      const tq = Number((tile.total_log1p_q8 && tile.total_log1p_q8[by] && tile.total_log1p_q8[by][bx]) || 0);
      const rq = Number((tile.ratio_diverging_q8 && tile.ratio_diverging_q8[by] && tile.ratio_diverging_q8[by][bx]) ?? (tile.neutral_ratio_q8 ?? 128));
      const estEdges = tq > 0 ? Math.round(Math.expm1((tq / 255) * Number(tile.max_log1p || 1))) : 0;
      const ratioNat = (((rq - Number(tile.neutral_ratio_q8 ?? 128)) / 127) * Number(tile.ratio_clip_nat || 3.5)).toFixed(2);
      const nLive = Number(hic.n_live_decls) || 1;
      const srcReg = atlasRegionForDfs(hic.regions, Math.floor(((by + 0.5) / N) * nLive));
      const dstReg = atlasRegionForDfs(hic.regions, Math.floor(((bx + 0.5) / N) * nLive));
      const rc = (srcReg && dstReg) ? couplingMap.get(srcReg.key + "->" + dstReg.key) : null;
      const regTxt = (srcReg ? srcReg.label : "bin " + by) + " → " + (dstReg ? dstReg.label : "bin " + bx);
      const rcTxt = rc ? (" | Region total: " + fmtInt(rc.total) + " (T:" + fmtInt(rc.type_only) + " V:" + fmtInt(rc.value_only) + " B:" + fmtInt(rc.both) + ", log T/V=" + Number(rc.log_ratio_et_ev).toFixed(2) + ")") : "";
      hicReadout.textContent = "Bin (" + by + "," + bx + ") · " + regTxt + " · cell ~" + fmtInt(estEdges) + " edges · log((E_T+1)/(E_V+1))=" + ratioNat + rcTxt;
    });

    // Wire Synteny hover readout
    const synBinMap = new Map();
    for (const pt of (syn.binned_points || [])) {
      synBinMap.set(pt[0] + ":" + pt[1], pt);
    }
    synCanvas.addEventListener("mousemove", (ev) => {
      const rect = synCanvas.getBoundingClientRect();
      const cx = ((ev.clientX - rect.left) / rect.width) * synCanvas.width;
      const cy = ((ev.clientY - rect.top) / rect.height) * synCanvas.height;
      const padL = 32, padT = 14, scale = 4, G = Number((syn.grid_meta && syn.grid_meta.grid_size) || 128);
      const pb = Math.floor((cx - padL) / scale);
      const lb = G - 1 - Math.floor((cy - padT) / scale);
      if (pb < 0 || pb >= G || lb < 0 || lb >= G) return;
      const nLive = Number(syn.n_live_decls) || 1;
      const nLib = Number(syn.n_library_decls) || 1;
      const reg = atlasRegionForDfs(hic.regions, Math.floor(((pb + 0.5) / G) * nLive));
      const libIdx = Math.floor(((lb + 0.5) / G) * nLib);
      const st = (syn.library_strata || []).find((s) => libIdx >= s.lib_idx_start && libIdx < s.lib_idx_end);
      const pt = synBinMap.get(pb + ":" + lb);
      const b256 = pb * 2;
      const band = (ti.bands || []).find((b) => b256 >= b.bin256_start && b256 <= b.bin256_end);
      const streak = (syn.diagonal_streaks || []).find((ds) => {
        const pr = ds.proj_bin_range || [0, 0];
        const lr = ds.lib_bin_range || [0, 0];
        return pb >= Math.min(pr[0], pr[1]) - 1 && pb <= Math.max(pr[0], pr[1]) + 1 && lb >= Math.min(lr[0], lr[1]) - 1 && lb <= Math.max(lr[0], lr[1]) + 1;
      });
      const repos = (syn.grid_meta && syn.grid_meta.repos) || [];
      let msg = "Proj bin " + pb + " (" + (reg ? reg.label : "DFS") + ") × Lib L" + (st ? st.stratum + " [" + (st.top_namespaces || []).join(", ") + "]" : lb);
      if (pt) msg += " · " + fmtInt(pt[2]) + " hits (" + fmtInt(pt[3]) + " named, " + (repos[pt[4]] || "lib") + ")";
      if (streak) msg += " · STREAK: " + streak.library_domain + " (" + streak.length_bins + " bins, " + streak.named_hits + " named)";
      if (band) msg += " · TERRA INCOGNITA (" + fmtInt(band.decl_count) + " decls, 0 named library hits)";
      synReadout.textContent = msg;
    });

    // 3. Same-Theorem, Alien-Proof Twins Explorer
    main.appendChild(el("div", { className: "section-hdr" }, [
      el("h2", { textContent: "Same-Theorem, Alien-Proof Twins (Exact k1n Signature Collisions)" }),
      el("span", { className: "sub", textContent: "Jaccard J(A,B) = |E_V(A) ∩ E_V(B)| / |E_V(A) ∪ E_V(B)| across proof-value dependencies" })
    ]));

    // 20-bin Jaccard Histogram
    const hist = Array.isArray(aliens.jaccard_histogram_20bins) ? aliens.jaccard_histogram_20bins : [];
    if (hist.length) {
      const hMax = Math.max(1, ...hist.map((v) => Number(v) || 0));
      const bars = hist.map((cnt, idx) => {
        const lo = (idx * 0.05).toFixed(2);
        const hi = ((idx + 1) * 0.05).toFixed(2);
        const cls = idx < 4 ? "alien" : (idx < 14 ? "variant" : "clone");
        const pct = Math.max(3, Math.round((Number(cnt) / hMax) * 100));
        return el("div", { className: "hist-bar-col", title: "J ∈ [" + lo + ", " + hi + "): " + fmtInt(cnt) + " pairs" }, [
          el("div", { className: "hist-bar " + cls, style: { height: pct + "%" } })
        ]);
      });
      main.appendChild(el("div", { className: "hist-wrap" }, [
        el("div", { className: "atlas-card-hd", style: { marginBottom: "6px" } }, [
          el("strong", { textContent: "20-Bin Proof-Value Jaccard Distribution", style: { color: "var(--text-hi)", fontSize: "13px" } }),
          el("div", { className: "atlas-legend" }, [
            el("span", null, [el("i", { className: "atlas-swatch", style: { background: "var(--crimson)" } }), "Alien (<0.20): " + fmtInt(allAliens)]),
            el("span", null, [el("i", { className: "atlas-swatch", style: { background: "var(--amber)" } }), "Variant (0.20–0.70): " + fmtInt((ap.all_sampled_pairs && ap.all_sampled_pairs.variant) || 0)]),
            el("span", null, [el("i", { className: "atlas-swatch", style: { background: "var(--emerald)" } }), "Clone (≥0.70): " + fmtInt((ap.all_sampled_pairs && ap.all_sampled_pairs.clone) || 0)])
          ])
        ]),
        el("div", { className: "hist-bars" }, bars),
        el("div", { className: "hist-axis" }, [
          el("span", { textContent: "0.00 (disjoint proof)" }),
          el("span", { textContent: "0.20" }),
          el("span", { textContent: "0.50" }),
          el("span", { textContent: "0.70" }),
          el("span", { textContent: "1.00 (identical deps)" })
        ])
      ]));
    }

    // Filter tabs + sort for Alien-Proof Twins
    const scopeSeg = el("div", { className: "seg" }, [
      ["all", "All Spotlight (" + ((aliens.top_alien_pairs || []).length + (aliens.top_alien_pairs_cross_repo || []).length) + ")"],
      ["intra", "Intra-RH (" + (aliens.top_alien_pairs_intra || []).length + ")"],
      ["cross", "Cross-Repo vs Mathlib (" + (aliens.top_alien_pairs_cross_repo || []).length + ")"]
    ].map(([k, lbl]) => el("button", {
      type: "button", className: state.atlas.twinScope === k ? "active" : "", textContent: lbl,
      onclick: () => { state.atlas.twinScope = k; renderAtlasBody(doc); }
    })));

    const sortSel = el("select", {
      className: "select",
      onchange: (ev) => { state.atlas.twinSort = ev.target.value; renderAtlasBody(doc); }
    }, [
      ["jaccard", "Sort: Lowest Jaccard J"],
      ["ratio", "Sort: Largest Size Ratio (×)"],
      ["type_nodes", "Sort: Largest Type Signature"]
    ].map(([k, lbl]) => el("option", { value: k, selected: state.atlas.twinSort === k, textContent: lbl })));

    let pairPool = [];
    if (state.atlas.twinScope === "intra") pairPool = (aliens.top_alien_pairs_intra || []).slice();
    else if (state.atlas.twinScope === "cross") pairPool = (aliens.top_alien_pairs_cross_repo || []).slice();
    else {
      const seenKey = new Set();
      for (const p of [...(aliens.top_alien_pairs || []), ...(aliens.top_alien_pairs_cross_repo || [])]) {
        const key = (p.thm_a && p.thm_a.name) + "|" + (p.thm_b && p.thm_b.name);
        if (!seenKey.has(key)) { seenKey.add(key); pairPool.push(p); }
      }
    }

    pairPool.sort((a, b) => {
      if (state.atlas.twinSort === "ratio") return atlasTwinRatio(b) - atlasTwinRatio(a);
      if (state.atlas.twinSort === "type_nodes") return (Number(b.type_nodes || 0) - Number(a.type_nodes || 0));
      return (Number(a.jaccard || 0) - Number(b.jaccard || 0)) || (Number(b.type_nodes || 0) - Number(a.type_nodes || 0));
    });

    main.appendChild(el("div", { className: "toolbar-row" }, [
      scopeSeg,
      sortSel,
      el("span", { className: "pill slate", textContent: pairPool.length + " spotlight pairs" })
    ]));

    const renderSide = (thm, label) => {
      if (!thm) return el("div", { className: "twin-side" });
      const srcPath = thm.src_rel_path || thm.module || "";
      const gh = (thm.origin === "project" && srcPath) ? buildGithubUrl(srcPath, thm.line_no) : null;
      const cir = findAnyCircuitForSymbol(thm.name);
      return el("div", { className: "twin-side" }, [
        el("div", { style: { display: "flex", justifyContent: "space-between", gap: "4px", alignItems: "center" } }, [
          el("span", { className: "pill " + (thm.origin === "project" ? "cyan" : "emerald"), textContent: label + " · " + (thm.origin || "lib") }),
          el("span", { className: "twin-side-meta", textContent: "vn=" + fmtInt(thm.value_nodes) + " · |E_V|=" + fmtInt(thm.ev_size) })
        ]),
        el("div", { className: "twin-side-name", textContent: thm.name }),
        thm.module ? el("div", { className: "twin-side-meta", textContent: thm.module + (thm.line_no ? ":" + thm.line_no : "") }) : null,
        (gh || cir) ? el("div", { className: "cir-ins-acts", style: { marginTop: "3px" } }, [
          gh ? el("a", { className: "btn sm", href: gh, target: "_blank", rel: "noopener noreferrer", textContent: "Pinned Source ↗" }) : null,
          cir ? el("button", { type: "button", className: "btn sm primary", textContent: "Circuit", onclick: () => navigate("#circuit/" + cir.mode + "/" + encodeURIComponent(cir.short || cir.name)) }) : null
        ]) : null
      ]);
    };

    main.appendChild(el("div", { className: "twins-grid" }, pairPool.map((p) => {
      const ratio = atlasTwinRatio(p);
      const vnA = Number((p.thm_a && p.thm_a.value_nodes) || 0);
      const vnB = Number((p.thm_b && p.thm_b.value_nodes) || 0);
      const isCross = p.pair_scope === "cross_repo";
      const ratioNote = ratio >= 2
        ? (isCross && vnA < vnB ? ratio.toFixed(1) + "× shorter than Mathlib" : ratio.toFixed(1) + "× size ratio")
        : "";
      return el("article", { className: "twin-card" }, [
        el("div", { className: "twin-card-hd" }, [
          el("div", { style: { display: "flex", gap: "6px", flexWrap: "wrap", alignItems: "center" } }, [
            el("span", { className: "pill " + (Number(p.jaccard) === 0 ? "crimson" : "amber"), textContent: "J = " + Number(p.jaccard || 0).toFixed(4) + " (" + fmtInt(p.shared_ev_count) + "/" + fmtInt(p.union_ev_count) + ")" }),
            el("span", { className: "pill " + (isCross ? "emerald" : "cyan"), textContent: isCross ? "cross-repo" : "intra-RH" }),
            ratioNote ? el("span", { className: "pill amber", textContent: ratioNote }) : null
          ]),
          el("span", { className: "twin-side-meta", textContent: "tn=" + fmtInt(p.type_nodes) + " · bucket ×" + fmtInt(p.bucket_size) })
        ]),
        el("div", { className: "twin-sides" }, [
          renderSide(p.thm_a, "A"),
          renderSide(p.thm_b, "B")
        ]),
        el("div", { className: "twin-side-meta", textContent: "Exact signature: " + (p.sighash || "—") })
      ]);
    })));
  }

  // ==========================================================================
  // VIEW 7: PORTABILITY ISLANDS (`portability_gems.json`)
  // ==========================================================================
  function computePortabilityIslands(doc) {
    const targets = Array.isArray(doc.targets) ? doc.targets : [];
    const ov = doc.overlap || {};
    const mat = ov.project_decls_matrix;
    const n = targets.length;
    const hasMat = Array.isArray(mat) && mat.length === n;
    const visited = new Set();
    const islands = [];
    for (let i = 0; i < n; i++) {
      if (visited.has(i)) continue;
      const comp = [];
      const q = [i];
      visited.add(i);
      while (q.length) {
        const u = q.shift();
        comp.push(u);
        if (hasMat) {
          for (let v = 0; v < n; v++) {
            if (!visited.has(v) && v !== u && Number(mat[u][v]) > 0) {
              visited.add(v);
              q.push(v);
            }
          }
        }
      }
      comp.sort((a, b) => ((targets[b].cone && targets[b].cone.project_decls) || 0) - ((targets[a].cone && targets[a].cone.project_decls) || 0));
      const lead = targets[comp[0]];
      const slug = shortName(lead.name);
      islands.push({
        slug,
        indices: comp,
        targets: comp.map((idx) => targets[idx]),
        maxProj: Math.max(...comp.map((idx) => (targets[idx].cone && targets[idx].cone.project_decls) || 0)),
        tier: (lead.contamination && lead.contamination.tier) || "scoped"
      });
    }
    return islands;
  }

  async function renderPortabilityView() {
    const main = $("#appMain");
    clearEl(main);
    const assetPath = state.manifest && state.manifest.assets && state.manifest.assets.portability;
    if (!assetPath) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No Portability Analysis Exported" }),
        el("p", { textContent: "This static build does not include portability_gems.json." })
      ]));
      return;
    }

    main.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Lazy-fetching Portability Islands…" })]));
    try {
      const doc = await fetchJson(assetPath);
      renderPortabilityBody(doc);
    } catch (err) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Failed to load Portability data" }),
        el("p", { textContent: String(err.message || err) })
      ]));
    }
  }

  function renderPortabilityBody(doc) {
    const main = $("#appMain");
    clearEl(main);
    const targets = Array.isArray(doc.targets) ? doc.targets : [];
    const islands = computePortabilityIslands(doc);
    const ov = doc.overlap || {};
    const us = ov.union_summary || {};

    main.appendChild(el("div", { className: "section-hdr", style: { marginTop: "0" } }, [
      el("h2", { textContent: "Mathlib Portability Islands (" + islands.length + " Pairwise-Disjoint)" }),
      el("span", { className: "sub", textContent: fmtInt(targets.length) + " audited classical targets · union " + fmtInt(us.union_project_decls || 0) + " project decls" })
    ]));

    // Island Cards
    main.appendChild(el("div", { className: "island-grid" }, islands.map((isl) => {
      const active = state.portability.island === isl.slug;
      return el("button", {
        type: "button",
        className: "island-card" + (active ? " active" : ""),
        onclick: () => {
          state.portability.island = active ? "" : isl.slug;
          renderPortabilityBody(doc);
        }
      }, [
        el("div", { className: "ic-top" }, [
          el("span", { className: "ic-name", textContent: isl.slug }),
          el("span", { className: "pill " + statusPillClass(isl.tier), textContent: isl.tier })
        ]),
        el("div", { className: "ic-sub", textContent: isl.targets.length + " target(s) · up to " + fmtInt(isl.maxProj) + " project decls · 0 overlap with other islands" }),
        el("div", { className: "hero-meta", style: { marginTop: "2px" } }, isl.targets.map((t) => el("span", { className: "pill slate", textContent: shortName(t.name) })))
      ]);
    })));

    // Filtered Targets Table
    const activeIsland = islands.find((i) => i.slug === state.portability.island);
    const shownTargets = activeIsland ? activeIsland.targets : targets;

    main.appendChild(el("div", { className: "section-hdr" }, [
      el("h2", { textContent: activeIsland ? ("Island: " + activeIsland.slug) : "All Audited Portable Targets" }),
      activeIsland ? el("button", { type: "button", className: "btn sm", textContent: "Show all islands", onclick: () => { state.portability.island = ""; renderPortabilityBody(doc); } }) : null
    ]));

    main.appendChild(el("div", { className: "table-wrap", style: { marginBottom: "18px" } }, [
      el("table", { className: "data-table" }, [
        el("thead", null, [el("tr", null, [
          el("th", { textContent: "Target Theorem" }),
          el("th", { textContent: "Tier" }),
          el("th", { className: "num", textContent: "Project Cone" }),
          el("th", { className: "num", textContent: "Spec Cone" }),
          el("th", { textContent: "Top Mathlib Boundary" }),
          el("th", { textContent: "Circuit" })
        ])]),
        el("tbody", null, shownTargets.map((t) => {
          const cone = t.cone || {};
          const cont = t.contamination || {};
          const prefs = ((t.boundary && t.boundary.top_external_prefixes) || []).slice(0, 4).map((p) => p.prefix + " (" + p.distinct_decls + ")").join(", ");
          const cir = findAnyCircuitForSymbol(t.name);
          return el("tr", null, [
            el("td", null, [
              el("code", { textContent: t.name }),
              t.module ? el("div", { className: "cir-ins-note mono", textContent: t.module }) : null
            ]),
            el("td", null, [el("span", { className: "pill " + statusPillClass(cont.tier), textContent: cont.tier || "—" })]),
            el("td", { className: "num", textContent: fmtInt(cone.project_decls) }),
            el("td", { className: "num", textContent: fmtInt(cone.spec_cone_project_decls) }),
            el("td", { className: "mono", style: { fontSize: "11px" }, textContent: prefs || "—" }),
            el("td", null, [
              cir ? el("button", {
                type: "button", className: "btn sm primary", textContent: "Circuit",
                onclick: () => navigate("#circuit/" + cir.mode + "/" + encodeURIComponent(cir.short || cir.name))
              }) : el("span", { className: "cir-ins-note", textContent: "—" })
            ])
          ]);
        }))
      ])
    ]));

    // Pairwise Overlap Matrix
    const pMat = ov.project_decls_matrix;
    const jMat = ov.project_jaccard_matrix;
    const tNames = ov.target_names || targets.map((t) => t.name);
    if (Array.isArray(pMat) && pMat.length) {
      main.appendChild(el("div", { className: "section-hdr" }, [
        el("h2", { textContent: "Pairwise Project-Cone Overlap Matrix" }),
        el("span", { className: "sub", textContent: "Shared project declarations (and Jaccard index)" })
      ]));
      const tbl = el("table", { className: "overlap-table" }, [
        el("thead", null, [el("tr", null, [
          el("th", { textContent: "Target" }),
          ...tNames.map((nm) => el("th", { className: "col-h", title: nm, textContent: shortName(nm).slice(0, 16) }))
        ])]),
        el("tbody", null, pMat.map((row, r) => el("tr", null, [
          el("th", { title: tNames[r], textContent: shortName(tNames[r]).slice(0, 26) }),
          ...row.map((val, c) => {
            const v = Number(val) || 0;
            const jac = (jMat && jMat[r] && jMat[r][c] != null) ? Number(jMat[r][c]) : null;
            const cls = r === c ? "hm-self" : (v === 0 ? "hm-0" : (jac >= 0.7 ? "hm-hi" : (jac >= 0.2 ? "hm-mid" : "hm-lo")));
            return el("td", { className: cls }, [
              fmtInt(v),
              jac != null ? el("span", { className: "jacc", textContent: jac.toFixed(2) }) : null
            ]);
          })
        ])))
      ]);
      main.appendChild(el("div", { className: "table-wrap" }, [tbl]));
    }
  }

  // ==========================================================================
  // VIEW 8: BENCHMARKS (`xrepo_benchmark.json` + optional `trim_report.json`)
  // ==========================================================================
  async function renderBenchmarksView() {
    const main = $("#appMain");
    clearEl(main);
    const assets = (state.manifest && state.manifest.assets) || {};
    if (!assets.benchmark && !assets.trim_report) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No Cross-Repo Benchmark Data Exported" }),
        el("p", { textContent: "This static build does not include xrepo_benchmark.json or trim_report.json." })
      ]));
      return;
    }

    main.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Lazy-fetching Benchmark & Trim telemetry…" })]));
    try {
      const [bench, trim] = await Promise.all([
        assets.benchmark ? fetchJson(assets.benchmark).catch(() => null) : Promise.resolve(null),
        assets.trim_report ? fetchJson(assets.trim_report).catch(() => null) : Promise.resolve(null)
      ]);
      renderBenchmarksBody(bench, trim);
    } catch (err) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Failed to load Benchmarks" }),
        el("p", { textContent: String(err.message || err) })
      ]));
    }
  }

  function renderBenchmarksBody(bench, trim) {
    const main = $("#appMain");
    clearEl(main);

    if (bench && Array.isArray(bench.repos)) {
      const repos = bench.repos;
      const totalMod = repos.reduce((s, r) => s + (Number(r.modules) || 0), 0);
      const totalLoc = repos.reduce((s, r) => s + (Number(r.lines_wc) || 0), 0);
      const passCnt = repos.filter((r) => r.overall_status === "PASS").length;

      main.appendChild(el("div", { className: "section-hdr", style: { marginTop: "0" } }, [
        el("h2", { textContent: "Cross-Corpus Generalization Benchmark (" + repos.length + " Lean 4 Repos)" }),
        el("span", { className: "sub", textContent: "Schema " + (bench.schema || "xrepo") + " · commit " + (bench.leanre_commit || "—") })
      ]));

      main.appendChild(el("section", { className: "kpi-strip" }, [
        { label: "Repositories Tested", val: fmtInt(repos.length), sub: passCnt + "/" + repos.length + " PASS", cls: "emerald" },
        { label: "Combined Modules", val: fmtInt(totalMod), sub: fmtInt(totalLoc) + " total LOC", cls: "cyan" },
        { label: "Issues Verified", val: fmtInt((bench.xrepo_issue_verification || []).filter((x) => x.status === "PASS").length) + "/" + fmtInt((bench.xrepo_issue_verification || []).length), sub: "generic CLI fixes", cls: "emerald" }
      ].map((k) => el("div", { className: "kpi-card" }, [
        el("div", { className: "kpi-label", textContent: k.label }),
        el("div", { className: "kpi-val " + k.cls, textContent: k.val }),
        el("div", { className: "kpi-sub", textContent: k.sub })
      ]))));

      main.appendChild(el("div", { className: "table-wrap", style: { marginBottom: "18px" } }, [
        el("table", { className: "data-table" }, [
          el("thead", null, [el("tr", null, [
            el("th", { textContent: "Repository" }),
            el("th", { textContent: "Root Hub" }),
            el("th", { className: "num", textContent: "Modules" }),
            el("th", { className: "num", textContent: "Lines" }),
            el("th", { className: "num", textContent: "Decls (sorry)" }),
            el("th", { className: "num", textContent: "FLIRT Misfile %" }),
            el("th", { className: "num", textContent: "Runtime" }),
            el("th", { textContent: "Status" })
          ])]),
          el("tbody", null, repos.map((r) => {
            const ds = r.decls_source || {};
            const f1 = r.flirt_tier1 || {};
            return el("tr", null, [
              el("td", null, [
                el("strong", { textContent: r.repo, style: { color: "var(--text-hi)" } }),
                el("div", { className: "cir-ins-note mono", textContent: r.lean_toolchain || "" })
              ]),
              el("td", null, [el("code", { textContent: r.hub || r.root_module || "—" })]),
              el("td", { className: "num", textContent: fmtInt(r.modules) }),
              el("td", { className: "num", textContent: fmtInt(r.lines_wc) }),
              el("td", { className: "num", textContent: fmtInt(ds.total) + " (" + fmtInt(ds.sorry_hits || 0) + ")" }),
              el("td", { className: "num", textContent: f1.misfiles_pct != null ? Number(f1.misfiles_pct).toFixed(2) + "%" : "—" }),
              el("td", { className: "num", textContent: r.total_runtime_s != null ? Number(r.total_runtime_s).toFixed(2) + "s" : "—" }),
              el("td", null, [el("span", { className: "pill " + statusPillClass(r.overall_status), textContent: r.overall_status || "—" })])
            ]);
          }))
        ])
      ]));

      const issues = Array.isArray(bench.xrepo_issue_verification) ? bench.xrepo_issue_verification : [];
      if (issues.length) {
        main.appendChild(el("div", { className: "section-hdr" }, [
          el("h2", { textContent: "Cross-Repo Portability Verification" })
        ]));
        main.appendChild(el("div", { className: "table-wrap", style: { marginBottom: "18px" } }, [
          el("table", { className: "data-table" }, [
            el("thead", null, [el("tr", null, [
              el("th", { textContent: "ID" }),
              el("th", { textContent: "Status" }),
              el("th", { textContent: "Component" }),
              el("th", { textContent: "Verification Summary" })
            ])]),
            el("tbody", null, issues.map((iss) => el("tr", null, [
              el("td", null, [el("code", { textContent: iss.id })]),
              el("td", null, [el("span", { className: "pill " + statusPillClass(iss.status), textContent: iss.status })]),
              el("td", null, [el("code", { textContent: iss.component || "—" })]),
              el("td", null, [
                el("strong", { textContent: iss.title || "", style: { color: "var(--text-hi)" } }),
                iss.verified_685ebbb ? el("div", { className: "cir-ins-note", textContent: iss.verified_685ebbb }) : null
              ])
            ])))
          ])
        ]));
      }
    }

    if (trim) {
      const steps = (trim.c8_waterfall && trim.c8_waterfall.steps) || trim.steps || [];
      if (steps.length) {
        main.appendChild(el("div", { className: "section-hdr" }, [
          el("h2", { textContent: "Virtual Proof Stripper — Bloat Waterfall" }),
          el("span", { className: "sub", textContent: trim.schema || "leanre.trim/1" })
        ]));
        main.appendChild(el("div", { className: "table-wrap" }, [
          el("table", { className: "data-table" }, [
            el("thead", null, [el("tr", null, [
              el("th", { textContent: "Stage" }),
              el("th", { textContent: "Description" }),
              el("th", { className: "num", textContent: "Removed Decls" }),
              el("th", { className: "num", textContent: "After Decls" })
            ])]),
            el("tbody", null, steps.map((st) => el("tr", null, [
              el("td", null, [el("code", { textContent: st.step_id || "—" })]),
              el("td", { textContent: st.label || "—" }),
              el("td", { className: "num", textContent: fmtInt((st.removed && (st.removed.decls || st.removed.live_decls || st.removed.modules)) || 0) }),
              el("td", { className: "num", textContent: fmtInt((st.after && (st.after.live_decls || st.after.decls || st.after.modules)) || 0) })
            ])))
          ])
        ]));
      }
    }
  }

  // ==========================================================================
  // VIEW 9: GLOBAL SHARDED SEARCH (`/` hotkey)
  // ==========================================================================
  function getSearchShardNames() {
    const shards = state.manifest && state.manifest.search && state.manifest.search.shards;
    if (Array.isArray(shards)) return shards;
    if (shards && typeof shards === "object") return Object.keys(shards);
    return [];
  }

  function hasSearchShard(pfx) {
    const shards = state.manifest && state.manifest.search && state.manifest.search.shards;
    if (!shards) return false;
    if (Array.isArray(shards)) return shards.includes(pfx);
    if (typeof shards === "object") return Object.prototype.hasOwnProperty.call(shards, pfx);
    return false;
  }

  function searchShardPrefixesForQuery(query) {
    const m = state.manifest;
    const sMeta = (m && m.search) || {};
    const plen = Number(sMeta.shard_prefix_len) || 2;
    const raw = String(query || "").trim();
    const out = new Set();

    const probe = (token) => {
      const alnum = String(token || "").toLowerCase().replace(/[^a-z0-9]/g, "");
      if (!alnum) {
        if (hasSearchShard("_")) out.add("_");
        return;
      }
      // Longest-prefix check (supports optional 3-char sub-sharding + standard 2-char)
      for (let len = Math.min(3, alnum.length); len >= plen; len--) {
        const cand = alnum.slice(0, len);
        if (hasSearchShard(cand)) {
          out.add(cand);
          return;
        }
      }
      if (alnum.length < plen && hasSearchShard("_")) out.add("_");
    };

    // Primary: leaf_prefix2 (leaf = part after final '.')
    const leaf = raw.includes(".") ? raw.slice(raw.lastIndexOf(".") + 1) : raw;
    probe(leaf);
    // Secondary: if user typed a qualified name, also probe full string in case exporter used full-name buckets
    if (raw.includes(".")) probe(raw);
    return Array.from(out);
  }

  function resolveModuleName(rawMod, shardModPrefixes) {
    if (rawMod == null) return "";
    const dict = (Array.isArray(shardModPrefixes) && shardModPrefixes.length)
      ? shardModPrefixes
      : ((state.manifest && state.manifest.search && Array.isArray(state.manifest.search.mod_prefixes)) ? state.manifest.search.mod_prefixes : null);
    if (typeof rawMod === "number" && dict && dict[rawMod] != null) return String(dict[rawMod]);
    if (Array.isArray(rawMod) && rawMod.length >= 2 && dict && dict[rawMod[0]] != null) {
      return String(dict[rawMod[0]]) + (rawMod[1] ? "." + String(rawMod[1]) : "");
    }
    const s = String(rawMod);
    if (dict) {
      const m = s.match(/^(\d+):(.*)$/);
      if (m && dict[Number(m[1])] != null) {
        return String(dict[Number(m[1])]) + (m[2] ? "." + m[2] : "");
      }
    }
    return s;
  }

  async function loadSearchShard(prefix) {
    const sMeta = state.manifest && state.manifest.search;
    if (!sMeta || !sMeta.shard_template || !prefix || !hasSearchShard(prefix)) return { rows: [], modPrefixes: null };
    if (state.searchShards.has(prefix)) return state.searchShards.get(prefix);
    const path = String(sMeta.shard_template).replace("{prefix}", prefix);
    try {
      const data = await fetchJson(path);
      const rows = Array.isArray(data) ? data : (Array.isArray(data.entries) ? data.entries : []);
      const modPrefixes = (!Array.isArray(data) && Array.isArray(data.mod_prefixes)) ? data.mod_prefixes : null;
      const packed = { rows, modPrefixes };
      state.searchShards.set(prefix, packed);
      return packed;
    } catch (_) {
      const empty = { rows: [], modPrefixes: null };
      state.searchShards.set(prefix, empty);
      return empty;
    }
  }

  function normalizeSearchEntry(row, modPrefixes) {
    if (Array.isArray(row)) {
      return {
        name: String(row[0] || ""),
        kind: String(row[1] || "decl"),
        dom: Number(row[2] || 0),
        live: row[3] == null ? 1 : Number(row[3]),
        mod: resolveModuleName(row[4], modPrefixes),
        line: row[5] != null ? Number(row[5]) : null,
        circuitPath: row[6] || null,
        bpId: row[7] || null
      };
    }
    return {
      name: String(row.name || ""),
      kind: String(row.kind || "decl"),
      dom: Number(row.dom || 0),
      live: row.live == null ? 1 : Number(row.live),
      mod: resolveModuleName(row.mod != null ? row.mod : (row.mod_id != null ? row.mod_id : row.module), modPrefixes),
      line: row.line != null ? Number(row.line) : null,
      circuitPath: row.circuit_path || null,
      bpId: row.bp_id || null
    };
  }

  function localManifestMatches(qLower) {
    const m = state.manifest || {};
    const out = [];
    for (const f of (m.findings || [])) {
      if (((f.slug || "") + " " + (f.title || "") + " " + (f.summary || "")).toLowerCase().includes(qLower)) {
        out.push({ type: "finding", name: f.title || f.slug, sub: "findings/" + f.slug + ".md", route: "#findings/" + encodeURIComponent(f.slug) });
      }
    }
    for (const d of (m.dossiers || [])) {
      if (((d.slug || "") + " " + (d.title || "") + " " + (d.category || "")).toLowerCase().includes(qLower)) {
        out.push({ type: "dossier", name: d.title || d.slug, sub: "analysis/" + d.slug + ".md", route: "#dossiers/" + encodeURIComponent(d.slug) });
      }
    }
    for (const b of (m.blueprints || [])) {
      if (((b.id || "") + " " + (b.title || "")).toLowerCase().includes(qLower)) {
        out.push({ type: "blueprint", name: b.title || b.id, sub: fmtInt(b.node_count) + " nodes", route: "#blueprints/" + encodeURIComponent(b.id) });
      }
    }
    const cir = m.circuits || {};
    for (const cb of (cir.bundles || [])) {
      if (((cb.name || "") + " " + (cb.short || "")).toLowerCase().includes(qLower)) {
        out.push({ type: "circuit", name: cb.name, sub: "Zoom 1 Bundle · " + (cb.badge || ""), route: "#circuit/bundle/" + encodeURIComponent(cb.short || cb.name) });
      }
    }
    for (const ct of (cir.theorems || [])) {
      if (((ct.name || "") + " " + (ct.short || "")).toLowerCase().includes(qLower)) {
        out.push({ type: "circuit", name: ct.name, sub: "Zoom 2 Theorem · dom " + fmtInt(ct.dom || 0), route: "#circuit/theorem/" + encodeURIComponent(ct.short || ct.name) });
      }
    }
    return out;
  }

  let searchDebounce = null;
  function renderSearchView(initialQ) {
    const main = $("#appMain");
    clearEl(main);
    if (initialQ) state.search.q = initialQ;

    const sMeta = (state.manifest && state.manifest.search) || {};
    const inputEl = el("input", {
      type: "search",
      id: "globalSearchInput",
      className: "input search-big-input",
      placeholder: "Type ≥ 2 chars to lazy-fetch sharded index (e.g. allChi, OpenLiteratureStatements, llOf_alt, hironaka)…",
      value: state.search.q,
      autocomplete: "off",
      spellcheck: "false",
      oninput: (ev) => {
        state.search.q = ev.target.value;
        clearTimeout(searchDebounce);
        searchDebounce = setTimeout(runSearchQuery, 120);
      }
    });

    const scopeSeg = el("div", { className: "seg", style: { marginTop: "10px" } }, [
      ["all", "All"], ["decl", "Live Decls"], ["circuit", "Circuits"], ["doc", "Findings & Dossiers"], ["blueprint", "Blueprints"]
    ].map(([k, lbl]) => el("button", {
      type: "button", className: state.search.scope === k ? "active" : "", textContent: lbl,
      onclick: () => { state.search.scope = k; renderSearchView(); }
    })));

    main.appendChild(el("section", { className: "search-hero" }, [
      el("div", { className: "section-hdr", style: { margin: "0 0 10px" } }, [
        el("h2", { textContent: "Global Sharded Search" }),
        el("span", { className: "sub", textContent: fmtInt(sMeta.total_entries || 0) + " declarations across " + fmtInt(getSearchShardNames().length) + " prefix shards (fetched on demand)" })
      ]),
      inputEl,
      scopeSeg
    ]));

    main.appendChild(el("div", { id: "searchResultsBox" }));
    setTimeout(() => { if (document.activeElement !== inputEl) inputEl.focus(); }, 20);
    runSearchQuery();
  }

  async function runSearchQuery() {
    const box = $("#searchResultsBox");
    if (!box) return;
    const rawQ = (state.search.q || "").trim();
    const ql = rawQ.toLowerCase();
    clearEl(box);

    if (ql.length < 2) {
      box.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Type at least 2 characters" }),
        el("p", { textContent: "Only the matching 2-character prefix shard (e.g. data/search/al.json) is fetched and cached — keeping initial page load ultra-light." })
      ]));
      return;
    }

    const localHits = localManifestMatches(ql);
    const shardPrefixes = searchShardPrefixesForQuery(rawQ);

    const shardResults = await Promise.all(shardPrefixes.map((p) => loadSearchShard(p)));
    const seen = new Set();
    const declHits = [];
    for (const packed of shardResults) {
      for (const raw of (packed.rows || [])) {
        const e = normalizeSearchEntry(raw, packed.modPrefixes);
        if (seen.has(e.name)) continue;
        const nl = e.name.toLowerCase();
        const sl = shortName(e.name).toLowerCase();
        if (nl.includes(ql) || sl.includes(ql) || e.mod.toLowerCase().includes(ql)) {
          seen.add(e.name);
          declHits.push(e);
        }
      }
    }
    // Rank exact/prefix matches first, then dom descending
    declHits.sort((a, b) => {
      const as = shortName(a.name).toLowerCase();
      const bs = shortName(b.name).toLowerCase();
      const ap = as === ql ? 0 : (as.startsWith(ql) ? 1 : 2);
      const bp = bs === ql ? 0 : (bs.startsWith(ql) ? 1 : 2);
      return (ap - bp) || (b.dom - a.dom) || a.name.localeCompare(b.name);
    });

    const scope = state.search.scope;
    const showLocal = localHits.filter((h) => {
      if (scope === "all") return true;
      if (scope === "doc") return h.type === "finding" || h.type === "dossier";
      return h.type === scope;
    });
    const showDecls = (scope === "all" || scope === "decl") ? declHits.slice(0, 80) : [];

    if (!showLocal.length && !showDecls.length) {
      box.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No matches for \"" + rawQ + "\"" }),
        el("p", { textContent: "Searched manifest entries and prefix shard(s): " + (Array.from(shardPrefixes).join(", ") || "none") + "." })
      ]));
      return;
    }

    const panel = el("div", { className: "panel", style: { padding: "0" } });
    for (const h of showLocal.slice(0, 40)) {
      const pCls = h.type === "circuit" ? "cyan" : (h.type === "finding" ? "emerald" : (h.type === "blueprint" ? "amber" : "blue"));
      panel.appendChild(el("div", { className: "search-result-row" }, [
        el("div", { className: "sr-main" }, [
          el("div", { className: "sr-name", textContent: h.name }),
          el("div", { className: "sr-meta" }, [
            el("span", { className: "pill " + pCls, textContent: h.type }),
            el("span", { textContent: h.sub })
          ])
        ]),
        el("div", { className: "sr-acts" }, [
          el("button", { type: "button", className: "btn sm primary", textContent: "Open →", onclick: () => navigate(h.route) })
        ])
      ]));
    }

    for (const d of showDecls) {
      const cir = findAnyCircuitForSymbol(d.name, d.circuitPath);
      const ghUrl = d.mod ? buildGithubUrl(d.mod, d.line) : null;
      const acts = el("div", { className: "sr-acts" });
      if (cir) {
        acts.appendChild(el("button", {
          type: "button", className: "btn sm primary", textContent: "Circuit",
          onclick: () => navigate("#circuit/" + cir.mode + "/" + encodeURIComponent(cir.short || cir.name))
        }));
      }
      if (d.bpId) {
        acts.appendChild(el("button", {
          type: "button", className: "btn sm", textContent: "Blueprint",
          onclick: () => navigate("#blueprints/" + encodeURIComponent(d.bpId))
        }));
      }
      if (ghUrl) {
        acts.appendChild(el("a", { className: "btn sm", href: ghUrl, target: "_blank", rel: "noopener noreferrer", textContent: "Source ↗" }));
      }
      panel.appendChild(el("div", { className: "search-result-row" }, [
        el("div", { className: "sr-main" }, [
          el("div", { className: "sr-name", textContent: d.name }),
          el("div", { className: "sr-meta" }, [
            el("span", { className: "pill " + (d.live ? "emerald" : "slate"), textContent: d.kind + (d.live ? "" : " · dead") }),
            d.dom > 0 ? el("span", { textContent: "dom " + fmtInt(d.dom) }) : null,
            d.mod ? el("span", { textContent: d.mod + (d.line ? ":" + d.line : "") }) : null
          ])
        ]),
        acts
      ]));
    }
    box.appendChild(panel);
  }

  // ==========================================================================
  // DISPATCH & SELF-TEST RUNNER
  // ==========================================================================
  async function handleRoute() {
    if (!state.manifest) return;
    const r = parseHash();
    state.route = r;
    updateNavHighlight(r.tab);

    switch (r.tab) {
      case "overview": renderOverview(); break;
      case "circuit": await renderCircuitView(r.sub, r.arg); break;
      case "findings": await renderFindingsView(r.sub); break;
      case "dossiers": await renderDossiersView(r.sub, r.arg); break;
      case "blueprints": await renderBlueprintsView(r.sub); break;
      case "flirt": await renderFlirtView(); break;
      case "atlas": await renderAtlasView(); break;
      case "portability": await renderPortabilityView(); break;
      case "benchmarks": await renderBenchmarksView(); break;
      case "search": renderSearchView(r.sub); break;
      default: renderOverview(); break;
    }

    if (r.selftest && !state.selftestRunning) {
      state.selftestRunning = true;
      await runSiteSelfTest();
    }
  }

  const FORBIDDEN_WORDING = /RH is proved|RH is proven|proves RH\b|RH has been proved|Riemann Hypothesis is proved/i;

  async function runSiteSelfTest() {
    const checks = [];
    const assert = (cond, msg) => { checks.push({ ok: Boolean(cond), msg }); };

    // 1. Manifest & initial lazy-load invariant
    const m = state.manifest;
    assert(m && m.schema === "leanre.site_manifest/1", "manifest schema is leanre.site_manifest/1");
    assert(state.loadedShards.size <= 3, "initial boot stays lazy (<= 3 shards, got " + state.loadedShards.size + ")");

    // 2. XSS sanitizer checks (Markdown & SVG)
    const xssMd = renderMarkdownBlockSafe('<img src=x onerror=alert(1)> [bad](javascript:alert(1)) <script>alert(2)</script>', "findings");
    const mdDiv = el("div");
    mdDiv.innerHTML = xssMd;
    assert(
      !mdDiv.querySelector("script, img, [onerror], a"),
      "markdown renderer blocks raw HTML, onerror, and javascript: links"
    );
    const tmpDiv = el("div");
    mountSafeSvg(tmpDiv, '<svg xmlns="http://www.w3.org/2000/svg" width="100" height="40"><script>window.__xss=1</script><rect onclick="alert(1)" width="20" height="20"/></svg>');
    assert(!tmpDiv.querySelector("script") && !tmpDiv.querySelector("[onclick]"), "SVG DOMParser sanitizer strips <script> and on* handlers");

    // 3. Overview check
    renderOverview();
    const ovTxt = $("#appMain").textContent || "";
    assert(ovTxt.length > 60 && !/\[object Object\]/.test(ovTxt) && !FORBIDDEN_WORDING.test(ovTxt), "overview renders cleanly without [object Object] or forbidden wording");

    // 4. Circuit view (macro + dark/light + bundle/theorem if present)
    if (m.circuits && m.circuits.macro) {
      await renderCircuitView("macro", "");
      assert(!!$("#cirStage svg"), "circuit macro mounts sanitized SVG");
      applyTheme("light", true);
      assert(document.documentElement.getAttribute("data-theme") === "light", "light theme toggle works");
      applyTheme("dark", true);
      if (m.circuits.bundles && m.circuits.bundles.length) {
        await renderCircuitView("bundle", m.circuits.bundles[0].short || m.circuits.bundles[0].name);
        assert(!!$("#cirStage svg"), "circuit bundle shard renders SVG");
      }
      if (m.circuits.theorems && m.circuits.theorems.length) {
        await renderCircuitView("theorem", m.circuits.theorems[0].short || m.circuits.theorems[0].name);
        assert(!!$("#cirStage svg"), "circuit theorem shard renders SVG");
      }
    }

    // 5. Remaining views (gracefully handle empty or populated)
    await renderFindingsView("");
    assert(($("#appMain").textContent || "").length > 20, "findings view renders");
    await renderDossiersView("", "");
    assert(($("#appMain").textContent || "").length > 20, "dossiers view renders");
    await renderBlueprintsView("");
    assert(($("#appMain").textContent || "").length > 20, "blueprints view renders");
    await renderFlirtView();
    assert(($("#appMain").textContent || "").length > 20, "FLIRT view renders");
    if (m.assets && m.assets.atlas) {
      await renderAtlasView();
      const atlasTxt = $("#appMain").textContent || "";
      assert(!!$("#hicCanvas") && !!$("#syntenyCanvas") && !/\[object Object\]/.test(atlasTxt), "Genome Atlas renders Hi-C and Synteny canvases cleanly");
    } else {
      const aTab = $("#tab-atlas");
      assert(!aTab || aTab.classList.contains("hidden"), "Genome Atlas tab hides cleanly when atlas asset is absent");
    }
    await renderPortabilityView();
    assert(($("#appMain").textContent || "").length > 20, "portability view renders");
    await renderBenchmarksView();
    assert(($("#appMain").textContent || "").length > 20, "benchmarks view renders");

    // 6. Search shard test
    const shardNames = getSearchShardNames();
    const firstShard = shardNames.find((s) => s !== "_" && s.length >= 2) || shardNames[0] || "ma";
    renderSearchView(firstShard);
    await runSearchQuery();
    assert(!!$("#globalSearchInput"), "search view renders and runs sharded query");

    // Return to overview with pass/fail banner
    renderOverview();
    const failed = checks.filter((c) => !c.ok);
    const result = {
      pass: failed.length === 0,
      passed: checks.length - failed.length,
      failed: failed.length,
      total: checks.length,
      loaded_bytes: state.loadedBytes,
      loaded_shards: state.loadedShards.size,
      checks
    };
    window.__LEANRE_SITE_SELFTEST_RESULT = result;
    const banner = el("div", {
      id: "selftestBanner",
      className: "selftest-banner" + (result.pass ? "" : " fail"),
      textContent: (result.pass ? "SELFTEST PASS" : "SELFTEST FAIL") + " — " + result.passed + "/" + result.total + " checks (" + formatBytes(result.loaded_bytes) + " across " + result.loaded_shards + " shards)" + (failed.length ? " | FAIL: " + failed.map((f) => f.msg).join("; ") : "")
    });
    const main = $("#appMain");
    if (main) main.prepend(banner);
    return result;
  }

  window.__LEANRE_SITE_SELFTEST = runSiteSelfTest;

  // ---------- Global Chrome Wiring & Boot ----------
  function wireGlobalControls() {
    $$("#mainNav .nav-tab").forEach((btn) => {
      btn.addEventListener("click", () => navigate("#" + btn.dataset.route));
    });
    const themeBtn = $("#themeToggleBtn");
    if (themeBtn) {
      themeBtn.addEventListener("click", () => applyTheme(state.theme === "dark" ? "light" : "dark", true));
    }
    const qBtn = $("#quickSearchBtn");
    if (qBtn) {
      qBtn.addEventListener("click", () => navigate("#search"));
    }
    window.addEventListener("keydown", (ev) => {
      if (ev.key === "/" && !ev.ctrlKey && !ev.metaKey && !ev.altKey) {
        const tag = (document.activeElement && document.activeElement.tagName || "").toLowerCase();
        if (tag !== "input" && tag !== "textarea" && tag !== "select") {
          ev.preventDefault();
          navigate("#search");
        }
      }
    });
    window.addEventListener("hashchange", handleRoute);
  }

  async function boot() {
    initTheme();
    wireGlobalControls();
    try {
      state.manifest = await fetchJson("./manifest.json");
      populateChromeFromManifest();
      await handleRoute();
    } catch (err) {
      const main = $("#appMain");
      if (main) {
        clearEl(main);
        main.appendChild(el("div", { className: "empty-card" }, [
          el("h3", { textContent: "Unable to load ./manifest.json" }),
          el("p", { textContent: "Serve this directory over HTTP (e.g. `python3 -m http.server`) or GitHub Pages. Details: " + String(err.message || err) })
        ]));
      }
    }
  }

  document.addEventListener("DOMContentLoaded", boot);
})();
