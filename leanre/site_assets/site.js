/* ==========================================================================
   leanre static site frontend (site.js)
   Hash-routed, no third-party scripts, data files fetched on demand, and all
   untrusted text rendered through textContent / sanitizers.
   Compatible with manifest schema `leanre.site_manifest/1` (both the RH
   showcase and generic / --demo Lean 4 repositories).
   ========================================================================== */
(function () {
  "use strict";

  const $ = (sel, root) => (root || document).querySelector(sel);
  const $$ = (sel, root) => Array.from((root || document).querySelectorAll(sel));

  // ---------- State, fetch telemetry (internal only) & caches ----------
  const state = {
    manifest: null,
    theme: "dark",
    route: { tab: "overview", sub: "", arg: "" },
    loadedBytes: 0,
    loadedFiles: new Set(),
    cacheJson: new Map(),
    cacheText: new Map(),
    searchShards: new Map(),
    circuit: {
      mode: "macro",
      target: "",
      data: null,
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
    selftestRunning: false,
    base: "",            // "" for a standalone export, "p/<slug>/" inside a gallery
    registry: null,      // parsed projects.json (leanre.projects_registry/1) or null
    outline: null,       // parsed data/outline.json once fetched
    rail: { open: true, mode: "spine", mobileOpen: false },
    overviewLens: "spine",
    map2d: { proj: "knn", layer: "landmarks", color: "pillar", sel: -1 },
    item: { name: "", view: "summary" },
    rootManifest: null
  };

  const SHOWCASE_ORDER = [
    { mode: "macro", target: "", label: "Whole repository", desc: "The main parts of the proof and how they connect", tag: "Map" },
    { mode: "bundle", target: "OpenLiteratureStatements", label: "OpenLiteratureStatements", desc: "Most consumers ignore the hypotheses they receive (152 of 195)", tag: "Structure" },
    { mode: "theorem", target: "llOf_alt", label: "llOf_alt", desc: "11 hypotheses are accepted but never used", tag: "Theorem" },
    { mode: "bundle", target: "RealInAlt", label: "RealInAlt", desc: "Three fields that only hold under a side condition", tag: "Structure" },
    { mode: "bundle", target: "HypsAlt", label: "HypsAlt", desc: "The 46-field record that feeds part A", tag: "Structure" },
    { mode: "theorem", target: "ch_balance", label: "ch_balance", desc: "An exact Fourier balance identity", tag: "Theorem" },
    { mode: "theorem", target: "linkGLOBAL7_items", label: "linkGLOBAL7_items", desc: "How the global bridge is wired together", tag: "Theorem" },
    { mode: "theorem", target: "sEEofTT", label: "sEEofTT", desc: "An evaluation step with five case splits", tag: "Theorem" }
  ];

  const MODE_LABEL = { macro: "Repository map", bundle: "Structure", theorem: "Theorem" };

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
          if (safe) {
            node.setAttribute("href", safe);
            if (tag === "a" && !attrs.title) {
              const up = upstreamRepoOf(safe);
              if (up) node.setAttribute("title", "Upstream proof repository " + up + " at the pinned commit (independent of leanre)");
            }
          }
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

  const LEANRE_REPO_URL = "https://github.com/bohemian-miser/leanre";

  // "owner/repo" for GitHub links that are not leanre's own repository.
  function upstreamRepoOf(url) {
    const m = String(url || "").match(/^https:\/\/github\.com\/([A-Za-z0-9-]+)\/([A-Za-z0-9._-]+)/);
    if (!m) return "";
    const slug = m[1] + "/" + m[2];
    return slug.toLowerCase() === "bohemian-miser/leanre" ? "" : slug;
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

  // Resolve a manifest-relative path against the active project directory.
  function projectRelPath(p) {
    const s = String(p || "").trim().replace(/^\.\//, "").replace(/^\/+/, "");
    if (!s) return "";
    return normalizeRelPath(state.base + s);
  }

  // Internal telemetry only (read by #selftest=1); never shown in the UI.
  function recordLoad(key, byteLen) {
    if (!state.loadedFiles.has(key)) {
      state.loadedFiles.add(key);
      state.loadedBytes += Math.max(0, Number(byteLen) || 0);
    }
  }

  async function fetchText(relPath) {
    const key = projectRelPath(relPath);
    if (!key) throw new Error("Empty file path");
    if (state.cacheText.has(key)) return state.cacheText.get(key);
    const resp = await fetch(key, { credentials: "same-origin" });
    if (!resp.ok) throw new Error("HTTP " + resp.status + " for " + key);
    const txt = await resp.text();
    const blen = new TextEncoder().encode(txt).length;
    recordLoad(key, blen);
    state.cacheText.set(key, txt);
    return txt;
  }

  async function fetchJson(relPath, opts) {
    const key = (opts && opts.root) ? normalizeRelPath(relPath) : projectRelPath(relPath);
    if (!key) throw new Error("Empty file path");
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

  // Anchor link plus a small inline "src" preview button (when the link is a
  // public GitHub .lean blob that the source viewer can open).
  function makeSourceLink(pathOrAnchor, lineOpt, labelOpt, titleOpt) {
    const a = makeGithubAnchor(pathOrAnchor, lineOpt, labelOpt);
    const url = buildGithubUrl(pathOrAnchor, lineOpt);
    const btn = url ? makeSrcButton(url, titleOpt || labelOpt || String(pathOrAnchor || "")) : null;
    return btn ? el("span", { className: "src-link" }, [a, btn]) : a;
  }

  // ==========================================================================
  // LIVE LEAN 4 SOURCE VIEWER
  // Files are fetched from raw.githubusercontent.com only when the reader asks
  // for a preview. Nothing is fetched on page load, and no upstream source is
  // stored in this repository.
  // ==========================================================================
  const RAW_HOST = "raw.githubusercontent.com";
  const RAW_CACHE_CAP = 40;
  const rawCache = new Map(); // rawUrl -> text (insertion order = LRU order)
  const SRC_CONTEXT = { "15": 15, "40": 40, full: Infinity };

  // Strictly convert https://github.com/<owner>/<repo>/blob/<ref>/<path>[#Ln[-Lm]]
  // into its raw.githubusercontent.com equivalent. Anything else returns null.
  function githubBlobToRaw(blobUrl) {
    const s = String(blobUrl == null ? "" : blobUrl).trim();
    if (!s || s.length > 2048 || /[\s\x00-\x1f\x7f\\<>"`]/.test(s)) return null;
    const m = s.match(/^https:\/\/github\.com\/([A-Za-z0-9](?:[A-Za-z0-9-]{0,38}))\/([A-Za-z0-9._-]{1,100})\/blob\/([A-Za-z0-9._-]{1,100})\/([^#?]{1,1500})(?:#L(\d{1,7})(?:-L(\d{1,7}))?)?$/);
    if (!m) return null;
    const [, owner, repo, ref, path, l1, l2] = m;
    if (repo === "." || repo === ".." || ref === "." || ref === "..") return null;
    const segs = path.split("/");
    for (const seg of segs) {
      if (!seg || seg === "." || seg === "..") return null;
      if (!/^(?:[\p{L}\p{N}._'+~=,@!-]|%[0-9A-Fa-f]{2})+$/u.test(seg)) return null;
      let dec;
      try { dec = decodeURIComponent(seg); } catch (_) { return null; }
      if (dec === "." || dec === ".." || /[\/\\\x00-\x1f]/.test(dec)) return null;
    }
    const raw = "https://" + RAW_HOST + "/" + owner + "/" + repo + "/" + ref + "/" + path;
    let parsed;
    try { parsed = new URL(raw); } catch (_) { return null; }
    if (parsed.protocol !== "https:" || parsed.hostname !== RAW_HOST || parsed.username || parsed.password || parsed.port) return null;
    const line = l1 ? Number(l1) : null;
    const lineEnd = l2 ? Number(l2) : null;
    return {
      raw,
      blob: "https://github.com/" + owner + "/" + repo + "/blob/" + ref + "/" + path,
      owner, repo, ref, path,
      line: line && line > 0 ? line : null,
      lineEnd: lineEnd && line && lineEnd >= line ? lineEnd : null
    };
  }

  function isLeanBlob(url) {
    const p = githubBlobToRaw(url);
    return Boolean(p && /\.lean$/i.test(p.path));
  }

  async function fetchRawSource(rawUrl) {
    if (rawCache.has(rawUrl)) {
      const txt = rawCache.get(rawUrl);
      rawCache.delete(rawUrl);
      rawCache.set(rawUrl, txt);
      return txt;
    }
    const resp = await fetch(rawUrl, { mode: "cors", credentials: "omit", referrerPolicy: "no-referrer", cache: "force-cache" });
    if (!resp.ok) {
      const err = new Error("HTTP " + resp.status);
      err.status = resp.status;
      throw err;
    }
    const txt = await resp.text();
    rawCache.set(rawUrl, txt);
    while (rawCache.size > RAW_CACHE_CAP) rawCache.delete(rawCache.keys().next().value);
    return txt;
  }

  // ---- Lean 4 tokenizer (pure; emits [className|null, text] pairs) ----
  const LEAN_DECL_KW = new Set([
    "theorem", "lemma", "def", "abbrev", "structure", "class", "inductive", "instance", "axiom", "example",
    "opaque", "noncomputable", "private", "protected", "partial", "unsafe", "namespace", "section", "end",
    "open", "variable", "universe", "import", "where", "deriving", "mutual", "set_option", "attribute",
    "macro", "syntax", "notation", "infix", "infixl", "infixr", "prefix", "postfix", "local", "scoped", "extends", "export"
  ]);
  const LEAN_NAME_AFTER = new Set(["theorem", "lemma", "def", "abbrev", "structure", "class", "inductive", "instance", "axiom", "opaque", "namespace", "section"]);
  const LEAN_TACTIC_KW = new Set([
    "by", "have", "let", "show", "obtain", "rcases", "exact", "refine", "refine'", "apply", "rw", "rwa", "erw", "simp", "simp_all",
    "simpa", "dsimp", "intro", "intros", "rintro", "fun", "match", "with", "if", "then", "else", "calc", "constructor",
    "cases", "induction", "use", "exists", "linarith", "nlinarith", "omega", "norm_num", "positivity", "ring", "ring_nf",
    "field_simp", "gcongr", "unfold", "specialize", "exfalso", "contradiction", "assumption", "trivial", "decide",
    "aesop", "filter_upwards", "convert", "congr", "ext", "funext", "push_neg", "by_contra", "by_cases", "split",
    "at", "from", "do", "return", "for", "in", "suffices", "change", "subst", "nofun", "nomatch", "termination_by", "decreasing_by"
  ]);
  const LEAN_SORRY = new Set(["sorry", "admit"]);
  const LEAN_PUNCT = new Set("()[]{}⟨⟩,:;|←→↔∀∃λ·•$<>=+-*/^&∧∨¬≤≥≠∈∉⊆⊂∘×⁻¹∑∏∫∣%!?@#.".split(""));
  const LEAN_IDENT_RX = /^(?:«[^»\n]*»|[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜᵢ-ᵪⱼ]*)(?:\.(?:«[^»\n]*»|[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜᵢ-ᵪⱼ]*))*/u;
  const LEAN_NUM_RX = /^(?:0x[0-9A-Fa-f_]+|0b[01_]+|\d[\d_]*(?:\.\d+)?(?:[eE][+-]?\d+)?)/;

  function tokenizeLeanLine(line, st) {
    const out = [];
    const push = (cls, txt) => {
      if (!txt) return;
      const last = out[out.length - 1];
      if (last && last[0] === cls) last[1] += txt;
      else out.push([cls, txt]);
    };
    const n = line.length;
    let i = 0;
    while (i < n) {
      if (st.depth > 0) {
        const start = i;
        while (i < n && st.depth > 0) {
          if (line.startsWith("/-", i)) { st.depth++; i += 2; }
          else if (line.startsWith("-/", i)) { st.depth--; i += 2; }
          else i++;
        }
        push("tok-com", line.slice(start, i));
        continue;
      }
      const rest = line.slice(i);
      if (rest.startsWith("--")) { push("tok-com", rest); break; }
      if (rest.startsWith("/-")) { st.depth = 1; push("tok-com", "/-"); i += 2; continue; }
      const c = line[i];
      if (c === "\"") {
        let j = i + 1;
        while (j < n && line[j] !== "\"") j += line[j] === "\\" ? 2 : 1;
        push("tok-str", line.slice(i, Math.min(n, j + 1)));
        i = Math.min(n, j + 1);
        continue;
      }
      if (c === "'") {
        const mc = rest.match(/^'(?:\\.|[^'\\])'/);
        if (mc) { push("tok-str", mc[0]); i += mc[0].length; continue; }
      }
      if (rest.startsWith("@[")) {
        const close = rest.indexOf("]");
        const seg = close > 0 ? rest.slice(0, close + 1) : rest;
        push("tok-attr", seg);
        i += seg.length;
        continue;
      }
      if (/[0-9]/.test(c)) {
        const mn = rest.match(LEAN_NUM_RX);
        if (mn) { push("tok-num", mn[0]); i += mn[0].length; continue; }
      }
      const mi = rest.match(LEAN_IDENT_RX);
      if (mi) {
        let word = mi[0];
        let cls = "";
        if (LEAN_SORRY.has(word)) cls = "tok-sorry";
        else if (LEAN_DECL_KW.has(word)) cls = "tok-kw";
        else if (LEAN_TACTIC_KW.has(word)) cls = "tok-tac";
        else if (st.expectName) cls = "tok-name";
        st.expectName = LEAN_NAME_AFTER.has(word);
        push(cls, word);
        i += word.length;
        continue;
      }
      if (rest.startsWith(":=")) { push("tok-punct", ":="); i += 2; st.expectName = false; continue; }
      if (LEAN_PUNCT.has(c)) { push("tok-punct", c); i += 1; if (c !== "." ) st.expectName = false; continue; }
      push(null, c);
      i += 1;
    }
    return out;
  }

  // Identifiers carry class "" (or "tok-name"); when `links` maps an identifier
  // to a verified declaration name, it becomes an in-page link to #item/<name>.
  function renderLeanTokens(tokens, links) {
    const frag = document.createDocumentFragment();
    for (const [cls, txt] of tokens) {
      if ((cls === "" || cls === "tok-name") && links && links.has(txt)) {
        const full = links.get(txt);
        const a = document.createElement("a");
        a.className = "src-sym" + (cls ? " " + cls : "");
        a.setAttribute("href", "#item/" + encodeURIComponent(full));
        a.setAttribute("title", "Inspect " + full);
        a.textContent = txt;
        frag.appendChild(a);
      } else if (cls) {
        const sp = document.createElement("span");
        sp.className = cls;
        sp.textContent = txt;
        frag.appendChild(sp);
      } else {
        frag.appendChild(document.createTextNode(txt));
      }
    }
    return frag;
  }

  function copyText(txt) {
    try {
      if (navigator.clipboard && navigator.clipboard.writeText) return navigator.clipboard.writeText(txt).then(() => true, () => false);
    } catch (_) { /* fall through */ }
    return Promise.resolve(false);
  }

  // ---- Drawer chrome ----
  const srcView = { root: null, backdrop: null, mode: "single", specs: [], ctx: "15", seq: 0, lastFocus: null, texts: [] };

  function ensureSourceDrawer() {
    if (srcView.root) return srcView.root;
    const backdrop = el("div", { className: "src-backdrop", hidden: true, onclick: closeSourceDrawer });
    const root = el("aside", { className: "src-drawer", id: "srcDrawer", role: "dialog", "aria-modal": "true", "aria-labeledby": "srcDrawerTitle", hidden: true }, [
      el("header", { className: "src-hd" }, [
        el("div", { className: "src-hd-main" }, [
          el("div", { className: "src-title", id: "srcDrawerTitle" }),
          el("div", { className: "src-path", id: "srcDrawerPath" })
        ]),
        el("button", { type: "button", className: "icon-btn src-close", id: "srcDrawerClose", "aria-label": "Close source viewer", title: "Close (Esc)", textContent: "×", onclick: closeSourceDrawer })
      ]),
      el("div", { className: "src-toolbar" }, [
        el("div", { className: "seg", id: "srcCtxSeg", role: "group", "aria-label": "Lines of context" }, [["15", "±15"], ["40", "±40"], ["full", "Full file"]].map(([k, lbl]) =>
          el("button", { type: "button", "data-ctx": k, textContent: lbl, onclick: () => { srcView.ctx = k; rerenderSourcePanes(); } })
        )),
        el("span", { className: "src-status", id: "srcStatus", "aria-live": "polite" }),
        el("div", { className: "spacer" }),
        el("button", { type: "button", className: "btn sm", id: "srcCopyBtn", textContent: "Copy snippet", onclick: () => copySourceSnippet(0) }),
        el("a", { className: "btn sm primary", id: "srcGhBtn", target: "_blank", rel: "noopener noreferrer", textContent: "View proof file ↗" })
      ]),
      el("div", { className: "src-body", id: "srcBody" }),
      el("footer", { className: "src-foot", textContent: "Fetched live from raw.githubusercontent.com (not hosted in this repository)." })
    ]);
    document.body.appendChild(backdrop);
    document.body.appendChild(root);
    srcView.root = root;
    srcView.backdrop = backdrop;
    document.addEventListener("keydown", (ev) => {
      if (ev.key === "Escape" && srcView.root && !srcView.root.hidden) {
        ev.preventDefault();
        closeSourceDrawer();
      }
    });
    return root;
  }

  function normalizeSourceSpec(spec) {
    const s = spec || {};
    const parsed = githubBlobToRaw(s.url);
    const line = Number(s.line) > 0 ? Math.floor(Number(s.line)) : (parsed && parsed.line) || null;
    return {
      url: s.url || "",
      parsed,
      title: String(s.title || (parsed ? parsed.path.split("/").pop() : "Source")),
      label: s.label ? String(s.label) : "",
      line,
      lineEnd: parsed && parsed.lineEnd && line === parsed.line ? parsed.lineEnd : null,
      fallbackUrl: s.fallbackUrl || "",
      fallbackLabel: s.fallbackLabel || "",
      links: s.links instanceof Map ? s.links : null,
      fixtureText: typeof s._fixtureText === "string" ? s._fixtureText : null
    };
  }

  function blobLineUrl(spec, line) {
    if (!spec.parsed) return spec.url || spec.fallbackUrl || "";
    return spec.parsed.blob + (line ? "#L" + line : "");
  }

  function openSourcePeek(spec) {
    return openSourceViewer("single", [normalizeSourceSpec(spec)]);
  }

  function openSourceCompare(leftSpec, rightSpec) {
    return openSourceViewer("compare", [normalizeSourceSpec(leftSpec), normalizeSourceSpec(rightSpec)]);
  }

  async function openSourceViewer(mode, specs) {
    const root = ensureSourceDrawer();
    srcView.mode = mode;
    srcView.specs = specs;
    srcView.texts = specs.map(() => null);
    srcView.errors = specs.map(() => null);
    const seq = ++srcView.seq;
    if (root.hidden) srcView.lastFocus = document.activeElement;
    root.classList.toggle("compare", mode === "compare");
    root.hidden = false;
    srcView.backdrop.hidden = false;
    document.body.classList.add("src-open");
    requestAnimationFrame(() => root.classList.add("open"));

    const first = specs[0];
    $("#srcDrawerTitle").textContent = mode === "compare" ? "Compare sources" : first.title;
    $("#srcDrawerPath").textContent = mode === "compare"
      ? specs.map((s) => (s.label ? s.label + ": " : "") + s.title).join("  ·  ")
      : (first.parsed ? first.parsed.path + (first.line ? ":" + first.line : "") : (first.label || ""));
    const gh = $("#srcGhBtn");
    const copyBtn = $("#srcCopyBtn");
    gh.classList.toggle("hidden", mode === "compare" || !blobLineUrl(first, first.line));
    copyBtn.classList.toggle("hidden", mode === "compare");
    if (mode !== "compare") {
      const u = safeHref(blobLineUrl(first, first.line));
      if (u) gh.setAttribute("href", u); else gh.removeAttribute("href");
    }
    $("#srcStatus").textContent = "";

    const body = $("#srcBody");
    clearEl(body);
    specs.forEach((s, idx) => {
      body.appendChild(el("section", { className: "src-pane", "data-pane": String(idx) }, [
        mode === "compare" ? buildPaneHeader(s, idx) : null,
        el("div", { className: "src-scroll" }, [
          el("div", { className: "src-loading" }, [el("div", { className: "spinner" }), el("span", { textContent: "Loading source…" })])
        ])
      ]));
    });
    const closeBtn = $("#srcDrawerClose");
    if (closeBtn) closeBtn.focus({ preventScroll: true });

    await Promise.all(specs.map(async (s, idx) => {
      try {
        if (s.fixtureText != null) srcView.texts[idx] = s.fixtureText;
        else if (!s.parsed) throw Object.assign(new Error("not-github"), { code: "not-github" });
        else srcView.texts[idx] = await fetchRawSource(s.parsed.raw);
      } catch (err) {
        srcView.errors[idx] = err;
      }
      if (seq === srcView.seq) renderSourcePane(idx);
    }));
    return seq === srcView.seq;
  }

  function buildPaneHeader(spec, idx) {
    const u = safeHref(blobLineUrl(spec, spec.line));
    return el("div", { className: "src-pane-hd" }, [
      el("div", { className: "src-pane-id" }, [
        spec.label ? el("span", { className: "src-pane-tag", textContent: spec.label }) : null,
        el("span", { className: "src-pane-title", textContent: spec.title, title: spec.title })
      ]),
      el("div", { className: "src-pane-acts" }, [
        spec.parsed ? el("button", { type: "button", className: "btn sm", textContent: "Copy", onclick: () => copySourceSnippet(idx) }) : null,
        u ? el("a", { className: "btn sm", href: u, target: "_blank", rel: "noopener noreferrer", textContent: "Proof file ↗" }) : null
      ])
    ]);
  }

  function sourceErrorMessage(spec, err) {
    if (err && err.code === "not-github") {
      return spec.fallbackUrl
        ? "This declaration lives outside the pinned repository, so there is no inline preview."
        : "Inline preview is only available for files in public GitHub repositories.";
    }
    const st = err && err.status;
    if (st === 404) return "The file was not found at this commit, or the repository is private.";
    if (st === 429 || st === 403) return "GitHub is limiting requests right now. Try again in a moment.";
    if (st) return "GitHub returned an error (HTTP " + st + ").";
    return "The file could not be fetched. You may be offline.";
  }

  function rerenderSourcePanes() {
    srcView.specs.forEach((_, idx) => renderSourcePane(idx));
  }

  function sliceBounds(spec, total, ctxKey) {
    const target = Math.min(Math.max(1, spec.line || 1), Math.max(1, total));
    const end = Math.min(Math.max(target, spec.lineEnd || target), Math.max(1, total));
    const k = SRC_CONTEXT[ctxKey || srcView.ctx] ?? 15;
    if (!Number.isFinite(k) || !spec.line) {
      if (!spec.line && Number.isFinite(k)) return { from: 1, to: Math.min(total, 2 * k + 1), target: null, end: null };
      return { from: 1, to: total, target: spec.line ? target : null, end: spec.line ? end : null };
    }
    return { from: Math.max(1, target - k), to: Math.min(total, end + k), target, end };
  }

  // Build the highlighted code block for one file. Shared by the drawer and the
  // docked pane on #item pages.
  function buildSourceCode(spec, text, ctxKey, opts) {
    const o = opts || {};
    const lines = String(text).replace(/\r\n?/g, "\n").split("\n");
    if (lines.length > 1 && lines[lines.length - 1] === "") lines.pop();
    const total = lines.length;
    const b = sliceBounds(spec, total, ctxKey);
    const st = { depth: 0, expectName: false };
    for (let i = 0; i < b.from - 1; i++) tokenizeLeanLine(lines[i], st);
    const links = spec.links || null;

    const code = el("div", { className: "src-code", role: "table", "aria-label": "Source lines " + b.from + " to " + b.to });
    if (b.from > 1) {
      code.appendChild(el("button", { type: "button", className: "src-more", textContent: "Show " + fmtInt(b.from - 1) + " earlier lines", onclick: () => o.onExpand && o.onExpand() }));
    }
    let hlRow = null;
    for (let ln = b.from; ln <= b.to; ln++) {
      const isHl = b.target != null && ln >= b.target && ln <= b.end;
      const href = safeHref(blobLineUrl(spec, ln));
      const row = el("div", { className: "src-line" + (isHl ? " hl" : ""), "data-line": String(ln), role: "row" }, [
        el("a", {
          className: "src-ln", href: href || null, role: "rowheader", title: "Highlight line " + ln + " and copy its link", textContent: String(ln),
          onclick: (ev) => { ev.preventDefault(); if (o.onSelectLine) o.onSelectLine(ln); }
        }),
        el("span", { className: "src-text", role: "cell" }, [renderLeanTokens(tokenizeLeanLine(lines[ln - 1], st), links)])
      ]);
      if (isHl && !hlRow) hlRow = row;
      code.appendChild(row);
    }
    if (b.to < total) {
      code.appendChild(el("button", { type: "button", className: "src-more", textContent: "Show " + fmtInt(total - b.to) + " later lines", onclick: () => o.onExpand && o.onExpand() }));
    }
    return { code, hlRow, bounds: b, total };
  }

  function scrollToHighlight(scroller, hlRow, smooth) {
    if (!scroller || !hlRow) return;
    requestAnimationFrame(() => {
      const top = hlRow.offsetTop - scroller.clientHeight / 2 + hlRow.offsetHeight;
      try { scroller.scrollTo({ top: Math.max(0, top), behavior: smooth ? "smooth" : "auto" }); }
      catch (_) { scroller.scrollTop = Math.max(0, top); }
    });
  }

  function renderSourcePane(idx) {
    const pane = srcView.root && srcView.root.querySelector('.src-pane[data-pane="' + idx + '"]');
    if (!pane) return;
    const scroller = pane.querySelector(".src-scroll");
    clearEl(scroller);
    $$("#srcCtxSeg button").forEach((b) => b.classList.toggle("active", b.dataset.ctx === srcView.ctx));
    const spec = srcView.specs[idx];
    const err = srcView.errors[idx];
    const text = srcView.texts[idx];
    if (err || text == null) {
      if (!err) {
        scroller.appendChild(el("div", { className: "src-loading" }, [el("div", { className: "spinner" }), el("span", { textContent: "Loading source…" })]));
        return;
      }
      scroller.appendChild(buildSourceError(spec, err));
      return;
    }
    const built = buildSourceCode(spec, text, srcView.ctx, {
      onExpand: () => { srcView.ctx = "full"; rerenderSourcePanes(); },
      onSelectLine: (ln) => selectSourceLine(idx, ln)
    });
    scroller.appendChild(built.code);
    scrollToHighlight(scroller, built.hlRow, srcView.ctx === "full");
  }

  function buildSourceError(spec, err) {
    const u = safeHref(blobLineUrl(spec, spec.line));
    const alt = safeHref(spec.fallbackUrl);
    return el("div", { className: "src-error" }, [
      el("h4", { textContent: "Couldn't show this file inline" }),
      el("p", { textContent: sourceErrorMessage(spec, err) }),
      u && spec.parsed ? el("a", { className: "btn primary", href: u, target: "_blank", rel: "noopener noreferrer", textContent: "View proof file ↗" }) : null,
      alt ? el("a", { className: "btn", href: alt, target: "_blank", rel: "noopener noreferrer", textContent: spec.fallbackLabel || "Open documentation ↗" }) : null
    ]);
  }

  // Docked (in-page) source pane used on #item pages. Fetches only when called.
  async function renderDockedSource(container, rawSpec, ctxKey) {
    const spec = normalizeSourceSpec(rawSpec);
    let ctx = ctxKey || "15";
    clearEl(container);
    const status = el("span", { className: "src-status", "aria-live": "polite" });
    const seg = el("div", { className: "seg", role: "group", "aria-label": "Lines of context" });
    const scroller = el("div", { className: "src-scroll docked" }, [
      el("div", { className: "src-loading" }, [el("div", { className: "spinner" }), el("span", { textContent: "Loading source…" })])
    ]);
    const ghHref = safeHref(blobLineUrl(spec, spec.line));
    container.appendChild(el("div", { className: "src-toolbar docked" }, [
      seg, status, el("div", { className: "spacer" }),
      ghHref ? el("a", { className: "btn sm", href: ghHref, target: "_blank", rel: "noopener noreferrer", textContent: "View proof file ↗" }) : null
    ]));
    container.appendChild(scroller);
    container.appendChild(el("div", { className: "src-foot", textContent: "Fetched live from raw.githubusercontent.com (not hosted in this repository)." }));
    let text = null;
    try {
      if (spec.fixtureText != null) text = spec.fixtureText;
      else if (!spec.parsed) throw Object.assign(new Error("not-github"), { code: "not-github" });
      else text = await fetchRawSource(spec.parsed.raw);
    } catch (err) {
      clearEl(scroller);
      scroller.appendChild(buildSourceError(spec, err));
      return false;
    }
    const draw = () => {
      clearEl(seg);
      [["15", "±15"], ["40", "±40"], ["full", "Full file"]].forEach(([k, lbl]) => seg.appendChild(el("button", {
        type: "button", className: ctx === k ? "active" : "", textContent: lbl, onclick: () => { ctx = k; draw(); }
      })));
      clearEl(scroller);
      const built = buildSourceCode(spec, text, ctx, {
        onExpand: () => { ctx = "full"; draw(); },
        onSelectLine: (ln) => {
          spec.line = ln; spec.lineEnd = null;
          $$(".src-line", scroller).forEach((r) => r.classList.toggle("hl", r.dataset.line === String(ln)));
          copyText(blobLineUrl(spec, ln)).then((ok) => { status.textContent = ok ? "Link to line " + ln + " copied" : "Line " + ln; });
        }
      });
      scroller.appendChild(built.code);
      scrollToHighlight(scroller, built.hlRow, false);
    };
    draw();
    return true;
  }

  function selectSourceLine(idx, ln) {
    const spec = srcView.specs[idx];
    if (!spec) return;
    spec.line = ln;
    spec.lineEnd = null;
    const pane = srcView.root.querySelector('.src-pane[data-pane="' + idx + '"]');
    if (pane) $$(".src-line", pane).forEach((r) => r.classList.toggle("hl", r.dataset.line === String(ln)));
    const u = blobLineUrl(spec, ln);
    if (srcView.mode !== "compare") {
      const gh = $("#srcGhBtn");
      const safe = safeHref(u);
      if (gh && safe) gh.setAttribute("href", safe);
      if (spec.parsed) $("#srcDrawerPath").textContent = spec.parsed.path + ":" + ln;
    }
    copyText(u).then((ok) => {
      const s = $("#srcStatus");
      if (s) s.textContent = ok ? "Link to line " + ln + " copied" : "Line " + ln;
    });
  }

  function copySourceSnippet(idx) {
    const spec = srcView.specs[idx];
    const text = srcView.texts[idx];
    if (!spec || text == null) return;
    const lines = text.replace(/\r\n?/g, "\n").split("\n");
    const b = sliceBounds(spec, lines.length);
    const snippet = lines.slice(b.from - 1, b.to).join("\n");
    copyText(snippet).then((ok) => {
      const s = $("#srcStatus");
      if (s) s.textContent = ok ? "Copied lines " + b.from + "–" + b.to : "Copy is not available in this browser";
    });
  }

  function closeSourceDrawer() {
    if (!srcView.root || srcView.root.hidden) return;
    srcView.seq++;
    srcView.root.classList.remove("open");
    srcView.root.hidden = true;
    srcView.backdrop.hidden = true;
    document.body.classList.remove("src-open");
    const f = srcView.lastFocus;
    srcView.lastFocus = null;
    if (f && typeof f.focus === "function" && document.contains(f)) f.focus({ preventScroll: true });
  }

  function makeSrcButton(url, title, opts) {
    if (!isLeanBlob(url)) return null;
    const o = opts || {};
    return el("button", {
      type: "button",
      className: o.className || "src-peek-btn",
      title: "Preview Lean source inline",
      "aria-label": "Preview " + (title || "source") + " inline",
      textContent: o.text || "src",
      onclick: (ev) => { ev.preventDefault(); ev.stopPropagation(); openSourcePeek({ url, title, line: o.line, label: o.label, links: o.links }); }
    });
  }

  // Add a small preview button after every GitHub .lean link inside rendered Markdown.
  function decorateLeanLinks(container) {
    if (!container) return 0;
    let count = 0;
    $$("a[href]", container).forEach((a) => {
      if (a.dataset.srcDecorated === "1") return;
      const href = a.getAttribute("href") || "";
      if (!isLeanBlob(href)) return;
      a.dataset.srcDecorated = "1";
      const label = (a.textContent || "").trim();
      const btn = makeSrcButton(href, label || undefined);
      if (btn) {
        a.insertAdjacentElement("afterend", btn);
        count++;
      }
    });
    return count;
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
        el("h3", { textContent: "This diagram could not be displayed" }),
        el("p", { textContent: "The diagram file is not well-formed SVG." })
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

  // ---------- Strict XSS-Safe Markdown & Math Renderer (no third-party code) ----------
  // ---- TeX helpers (no third-party code) ----
  // Symbol substitutions shared by the HTML and plain-text paths. Input may be
  // HTML-escaped (the Markdown path) or raw text (titles, cards, search).
  const TEX_BB = { R: "ℝ", C: "ℂ", Q: "ℚ", Z: "ℤ", N: "ℕ", F: "𝔽", A: "𝔸", P: "ℙ", H: "ℍ", T: "𝕋", K: "𝕂" };
  const TEX_SYMBOLS = [
    ["leqslant", "≤"], ["geqslant", "≥"], ["leq", "≤"], ["geq", "≥"], ["le", "≤"], ["ge", "≥"], ["neq", "≠"], ["ne", "≠"],
    ["approx", "≈"], ["asymp", "≍"], ["simeq", "≃"], ["cong", "≅"], ["sim", "∼"], ["equiv", "≡"], ["ll", "≪"], ["gg", "≫"],
    ["notin", "∉"], ["in", "∈"], ["subseteq", "⊆"], ["subset", "⊂"], ["supseteq", "⊇"], ["supset", "⊃"], ["setminus", "∖"],
    ["longrightarrow", "⟶"], ["rightarrow", "→"], ["leftarrow", "←"], ["Leftrightarrow", "⇔"], ["leftrightarrow", "↔"],
    ["Rightarrow", "⇒"], ["Leftarrow", "⇐"], ["hookrightarrow", "↪"], ["twoheadrightarrow", "↠"], ["mapsto", "↦"], ["to", "→"],
    ["iff", "⇔"], ["implies", "⇒"], ["forall", "∀"], ["exists", "∃"], ["neg", "¬"], ["land", "∧"], ["lor", "∨"], ["wedge", "∧"], ["vee", "∨"],
    ["bigwedge", "⋀"], ["bigvee", "⋁"], ["bigcup", "⋃"], ["bigcap", "⋂"], ["cup", "∪"], ["cap", "∩"],
    ["cdots", "⋯"], ["ldots", "…"], ["dots", "…"], ["cdot", "·"], ["times", "×"], ["pm", "±"], ["mp", "∓"], ["circ", "∘"], ["star", "⋆"], ["ast", "∗"],
    ["otimes", "⊗"], ["oplus", "⊕"], ["infty", "∞"], ["partial", "∂"], ["nabla", "∇"], ["sum", "∑"], ["prod", "∏"], ["int", "∫"],
    ["nmid", "∤"], ["mid", "∣"], ["langle", "⟨"], ["rangle", "⟩"], ["lceil", "⌈"], ["rceil", "⌉"], ["lfloor", "⌊"], ["rfloor", "⌋"],
    ["lvert", "|"], ["rvert", "|"], ["lVert", "‖"], ["rVert", "‖"], ["prime", "′"], ["ell", "ℓ"], ["hbar", "ℏ"], ["emptyset", "∅"], ["varnothing", "∅"],
    ["varepsilon", "ε"], ["epsilon", "ε"], ["vartheta", "ϑ"], ["varphi", "φ"], ["varrho", "ϱ"],
    ["alpha", "α"], ["beta", "β"], ["gamma", "γ"], ["delta", "δ"], ["zeta", "ζ"], ["eta", "η"], ["theta", "θ"], ["iota", "ι"], ["kappa", "κ"],
    ["lambda", "λ"], ["mu", "μ"], ["nu", "ν"], ["xi", "ξ"], ["pi", "π"], ["rho", "ρ"], ["sigma", "σ"], ["tau", "τ"], ["upsilon", "υ"],
    ["phi", "φ"], ["chi", "χ"], ["psi", "ψ"], ["omega", "ω"],
    ["Gamma", "Γ"], ["Delta", "Δ"], ["Theta", "Θ"], ["Lambda", "Λ"], ["Xi", "Ξ"], ["Pi", "Π"], ["Sigma", "Σ"], ["Upsilon", "Υ"], ["Phi", "Φ"], ["Psi", "Ψ"], ["Omega", "Ω"]
  ];
  const TEX_SYMBOL_RX = new RegExp("\\\\(" + TEX_SYMBOLS.map((x) => x[0]).sort((a, b) => b.length - a.length).join("|") + ")(?![a-zA-Z])", "g");
  const TEX_SYMBOL_MAP = new Map(TEX_SYMBOLS);

  function texReplaceSymbols(src) {
    let s = String(src == null ? "" : src);
    s = s.replace(/\\\{/g, "\u0001").replace(/\\\}/g, "\u0002").replace(/\\\|/g, "‖").replace(/\\\$/g, "$");
    s = s.replace(/\\(?:Bigl|Bigr|Biggl|Biggr|bigl|bigr|Big|big|Bigg|bigg|left|right|displaystyle|textstyle|scriptstyle|limits|nolimits)(?![a-zA-Z])/g, "");
    s = s.replace(/\\(?:operatorname\*?|mathrm|text|textrm|textit|textbf|mathbf|mathcal|mathsf|mathit|mathfrak|boldsymbol|mathscr)\s*\{([^{}]*)\}/g, "$1");
    s = s.replace(/\\mathbb\s*\{([A-Za-z])\}/g, (_, ch) => TEX_BB[ch] || ch);
    s = s.replace(/\\(?:t|d)?frac\s*\{([^{}]*)\}\s*\{([^{}]*)\}/g, (_, a, b) => (/^[\w′.]+$/.test(a) ? a : "(" + a + ")") + "/" + (/^[\w′.]+$/.test(b) ? b : "(" + b + ")"));
    s = s.replace(/\\(?:t|d)?frac\s*([0-9A-Za-z])\s*([0-9A-Za-z])/g, "$1/$2");
    s = s.replace(/\\sqrt\s*\{([^{}]*)\}/g, "√($1)");
    s = s.replace(/\\(?:qquad)(?![a-zA-Z])/g, "\u2003\u2003").replace(/\\quad(?![a-zA-Z])/g, "\u2003");
    s = s.replace(/\\[,;:]/g, " ").replace(/\\!/g, "").replace(/\\ /g, " ").replace(/~/g, " ");
    s = s.replace(TEX_SYMBOL_RX, (_, name) => TEX_SYMBOL_MAP.get(name) || name);
    return s;
  }

  const SUP_MAP = { "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹", "+": "⁺", "-": "⁻", "−": "⁻", "=": "⁼", "(": "⁽", ")": "⁾", n: "ⁿ", i: "ⁱ", k: "ᵏ", s: "ˢ", "*": "*", "∨": "ᵛ", "′": "′" };
  const SUB_MAP = { "0": "₀", "1": "₁", "2": "₂", "3": "₃", "4": "₄", "5": "₅", "6": "₆", "7": "₇", "8": "₈", "9": "₉", "+": "₊", "-": "₋", "=": "₌", "(": "₍", ")": "₎", a: "ₐ", e: "ₑ", o: "ₒ", x: "ₓ", i: "ᵢ", j: "ⱼ", k: "ₖ", n: "ₙ", m: "ₘ", p: "ₚ", s: "ₛ", t: "ₜ", r: "ᵣ" };
  const toScript = (txt, map, mark) => {
    const chars = Array.from(txt);
    return chars.every((c) => map[c]) ? chars.map((c) => map[c]).join("") : mark + (chars.length > 1 ? "(" + txt + ")" : txt);
  };

  // TeX fragment -> plain Unicode text (for titles, cards, crumbs, search).
  function texToPlain(tex) {
    let s = texReplaceSymbols(tex);
    s = s.replace(/\^\{([^{}]*)\}/g, (_, t) => toScript(t, SUP_MAP, "^"));
    s = s.replace(/_\{([^{}]*)\}/g, (_, t) => toScript(t, SUB_MAP, "_"));
    s = s.replace(/\^([0-9A-Za-z∨*′])/g, (_, t) => toScript(t, SUP_MAP, "^"));
    s = s.replace(/_([0-9A-Za-z])/g, (_, t) => toScript(t, SUB_MAP, "_"));
    s = s.replace(/\\([A-Za-z]+)/g, "$1").replace(/[{}]/g, "");
    return s.replace(/\u0001/g, "{").replace(/\u0002/g, "}").replace(/\s+/g, " ").trim();
  }

  // Inline math is $...$ with no space just inside the dollars and no digit
  // right after the closing one, so prices such as "$5 and $10" stay text.
  const INLINE_MATH_RX = /\$(?!\$)(?=\S)((?:\\.|[^$\\\n]){1,400}?)(?<=[^\s\\])\$(?![\d$])/g;

  function plainTextFromTex(text) {
    return String(text == null ? "" : text)
      .replace(/\$\$([^$]+)\$\$/g, (_, t) => texToPlain(t))
      .replace(INLINE_MATH_RX, (_, t) => texToPlain(t));
  }

  // TeX fragment -> DOM (math span with real <sup>/<sub>), built only with
  // createElement/textContent.
  function renderTexSafe(tex) {
    const span = document.createElement("span");
    span.className = "math-inline";
    const s = texReplaceSymbols(tex);
    const rx = /([\^_])(?:\{([^{}]*)\}|([0-9A-Za-z∨*′]))/g;
    let last = 0;
    let m;
    const addText = (t) => { if (t) span.appendChild(document.createTextNode(t.replace(/\\([A-Za-z]+)/g, "$1").replace(/[{}]/g, "").replace(/\u0001/g, "{").replace(/\u0002/g, "}"))); };
    while ((m = rx.exec(s))) {
      addText(s.slice(last, m.index));
      const node = document.createElement(m[1] === "^" ? "sup" : "sub");
      node.textContent = texToPlain(m[2] != null ? m[2] : m[3]);
      span.appendChild(node);
      last = rx.lastIndex;
    }
    addText(s.slice(last));
    return span;
  }

  // Text with $...$ segments -> DOM fragment (plain text + math spans).
  function renderTextWithTex(text) {
    const frag = document.createDocumentFragment();
    const src = String(text == null ? "" : text);
    let last = 0;
    INLINE_MATH_RX.lastIndex = 0;
    let m;
    while ((m = INLINE_MATH_RX.exec(src))) {
      if (m.index > last) frag.appendChild(document.createTextNode(src.slice(last, m.index)));
      frag.appendChild(renderTexSafe(m[1]));
      last = INLINE_MATH_RX.lastIndex;
    }
    if (last < src.length) frag.appendChild(document.createTextNode(src.slice(last)));
    return frag;
  }

  // Escaped TeX -> HTML string with only <sup>/<sub> tags added (Markdown path;
  // the input has already been HTML-escaped, so nothing else can appear).
  function prettifyMath(escapedTex) {
    let s = texReplaceSymbols(escapedTex);
    s = s.replace(/\^\{([^{}]*)\}/g, "<sup>$1</sup>");
    s = s.replace(/_\{([^{}]*)\}/g, "<sub>$1</sub>");
    s = s.replace(/\^([0-9A-Za-z∨*′])/g, "<sup>$1</sup>");
    s = s.replace(/_([0-9A-Za-z])/g, "<sub>$1</sub>");
    s = s.replace(/\\([A-Za-z]+)/g, "$1").replace(/[{}]/g, "");
    return s.replace(/\u0001/g, "{").replace(/\u0002/g, "}");
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
    s = s.replace(INLINE_MATH_RX, (m, tex) => hold('<span class="math-inline">' + prettifyMath(tex) + "</span>"));

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

  // Where a document's local reproduction commands live on GitHub.
  function verifyLocallyHref(docPath) {
    const p = String(docPath || "");
    if (!state.base && /^(findings|analysis|research)\/[A-Za-z0-9_.-]+\.md$/.test(p)) return "https://github.com/bohemian-miser/leanre/blob/main/" + p;
    return "https://github.com/bohemian-miser/leanre#reproducing-the-audit";
  }

  function renderMarkdownBlockSafe(md, sourceContext, docPath) {
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
        summaryText = summaryText.replace(/&amp;/g, "&");
        // "Verify locally" blocks hold commands for a local clone (kernel
        // database, mirrored sources). Keep prose and anchors; replace the
        // command blocks with one quiet pointer to the repository.
        if (/^verify locally\b/i.test(summaryText)) {
          const kept = [];
          let inFence = false;
          let dropped = false;
          for (const ln of inner) {
            if (/^\s*```/.test(ln)) { inFence = !inFence; dropped = true; continue; }
            if (!inFence) kept.push(ln);
          }
          out.push(
            "<details class=\"verify-note\"" + (isOpen ? " open" : "") + "><summary>" +
            renderInlineSafe(summaryText, sourceContext) + "</summary>" +
            (dropped ? "<p class=\"md-quiet\">Commands for checking this against your own clone are kept in the source file. <a href=\"" + escapeHtml(verifyLocallyHref(docPath)) + "\" target=\"_blank\" rel=\"noopener noreferrer\">" + escapeHtml(verifyLocallyHref(docPath).includes("/blob/") ? "See verification commands in " + docPath + " on GitHub ↗" : "See verification commands on GitHub ↗") + "</a></p>" : "") +
            renderMarkdownBlockSafe(kept.join("\n"), sourceContext, docPath) +
            "</details>"
          );
          continue;
        }
        out.push(
          "<details" + (isOpen ? " open" : "") + "><summary>" +
          renderInlineSafe(summaryText, sourceContext) +
          "</summary>" + renderMarkdownBlockSafe(inner.join("\n"), sourceContext, docPath) +
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
        out.push("<blockquote>" + renderMarkdownBlockSafe(qLines.join("\n"), sourceContext, docPath) + "</blockquote>");
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
    if (rerenderCircuit && state.route.tab === "circuit" && state.circuit.data) {
      mountActiveCircuitSvg();
    } else if (rerenderCircuit && state.manifest && ["atlas", "overview", "item"].includes(state.route.tab)) {
      handleRoute({ keepScroll: true });
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

    const validTabs = new Set(["overview", "circuit", "findings", "dossiers", "blueprints", "flirt", "atlas", "portability", "benchmarks", "search", "experiments", "item", "projects"]);
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
    document.title = (m.repo_name ? m.repo_name + " — " : "") + "leanre";
    const repoBadge = $("#brandRepo");
    if (repoBadge) repoBadge.textContent = m.repo_name || "";

    const ext = $("#repoExtLink");
    let treeUrl = null;
    if (ext) {
      const url = safeHref(m.repo_url);
      if (url && /^https?:\/\//i.test(url)) {
        treeUrl = m.pinned_commit ? url.replace(/\/+$/, "") + "/tree/" + encodeURIComponent(m.pinned_commit) : url;
        ext.href = treeUrl;
        ext.classList.remove("hidden");
      } else {
        ext.classList.add("hidden");
      }
    }

    // Show only the tabs this project has data for (routes keep working).
    const a = m.assets || {};
    const cir = m.circuits || {};
    const visible = {
      circuit: Boolean(cir.macro || (cir.bundles || []).length || (cir.theorems || []).length),
      findings: (m.findings || []).length > 0,
      dossiers: (m.dossiers || []).length + (m.research || []).length > 0,
      blueprints: (m.blueprints || []).length > 0,
      flirt: Boolean(a.cluster_labels || a.flirt_tier1),
      atlas: Boolean(a.atlas || a.module_matrix || a.embedding_2d),
      portability: Boolean(a.portability),
      benchmarks: Boolean(a.benchmark || a.trim_report)
    };
    for (const [k, on] of Object.entries(visible)) {
      const tab = $("#tab-" + k);
      if (tab) tab.classList.toggle("hidden", !on);
    }

    const footerMeta = $("#footerMeta");
    if (footerMeta) {
      clearEl(footerMeta);
      const up = upstreamRepoOf(m.repo_url);
      const items = [
        el("span", { textContent: "leanre" }),
        el("span", { textContent: "AGPL-3.0-or-later" }),
        el("a", { href: LEANRE_REPO_URL, target: "_blank", rel: "noopener noreferrer", title: "leanre tool and explorer on GitHub", textContent: "leanre on GitHub ↗" })
      ];
      if (up && treeUrl && !m.demo_mode) {
        items.push(el("a", { className: "fm-proof", href: treeUrl, target: "_blank", rel: "noopener noreferrer", textContent: "Analyzed proof: " + up + (m.pinned_commit ? " @ " + String(m.pinned_commit).slice(0, 8) : "") + " ↗" }));
        items.push(el("span", { className: "fm-proof", textContent: "Independent analysis — not affiliated with the Lean community or the proof authors" }));
      }
      items.forEach((node, idx) => {
        if (idx) footerMeta.appendChild(el("span", { className: "sep" + (node.classList.contains("fm-proof") ? " fm-proof" : ""), textContent: "·", "aria-hidden": "true" }));
        footerMeta.appendChild(node);
      });
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
  // PROJECTS: multi-proof gallery (projects.json + p/<slug>/)
  // ==========================================================================
  const SAFE_PROJECT_PATH = /^[A-Za-z0-9._\/-]*$/;
  const PROJECT_GROUPS = [
    ["kernel", "Kernel exports"],
    ["ai-assisted", "AI-assisted formalizations"],
    ["human-baseline", "Community formalizations"],
    ["demo", "Demo"],
    ["other", "Other"]
  ];

  function projectBaseFor(entry) {
    const p = String((entry && entry.path) || "").trim().replace(/^\.\/?/, "").replace(/\/+$/, "");
    if (!p || p === ".") return "";
    if (!SAFE_PROJECT_PATH.test(p) || p.split("/").some((seg) => seg === ".." || seg === "." || seg === "")) return null;
    return p + "/";
  }

  function parseRegistry(doc) {
    if (!doc || typeof doc !== "object" || !Array.isArray(doc.projects)) return null;
    const out = [];
    const seen = new Set();
    for (const p of doc.projects) {
      if (!p || typeof p !== "object") continue;
      const slug = String(p.slug || "").trim();
      if (!/^[A-Za-z0-9._-]{1,80}$/.test(slug) || seen.has(slug)) continue;
      const base = projectBaseFor(p);
      if (base == null) continue;
      seen.add(slug);
      out.push(Object.assign({}, p, { slug, _base: base }));
    }
    return out.length ? { schema: String(doc.schema || ""), projects: out } : null;
  }

  async function loadRegistry() {
    try {
      return parseRegistry(await fetchJson("./projects.json", { root: true }));
    } catch (_) {
      return null; // standalone exports have no registry
    }
  }

  function projectFromManifest(m, base) {
    const st = (m && m.stats) || {};
    const slug = String(m.slug || m.repo_name || "project");
    const title = m.title && !/leanre/i.test(m.title) ? m.title : (m.repo_name || slug);
    const nF = (m.findings || []).length, nD = (m.dossiers || []).length;
    return {
      slug, title, _base: base, _root: base === "",
      tagline: m.tagline || m.description || (st.edges && !m.source_only ? "Kernel export with dependency diagrams" + (nF ? ", " + nF + " findings" : "") + (nD ? " and " + nD + " dossiers" : "") + "." : ""),
      repo_url: m.repo_url || "", pinned_commit: m.pinned_commit || "",
      files: st.total_files, lines: st.total_lines, decls: st.total_decls,
      sorry: st.sorry_count, sorry_files: st.sorry_files, axioms: st.axioms,
      has_kernel_export: !m.source_only && !m.demo_mode, source_only: Boolean(m.source_only),
      category: m.category || (m.demo_mode ? "demo" : (m.source_only ? "other" : "kernel")),
      license: m.license || ""
    };
  }

  // Projects shown in the switcher and on #projects: the registry, plus the
  // root export itself when it is a project the registry does not list.
  function projectList() {
    const list = state.registry ? state.registry.projects.slice() : [];
    if (state.rootManifest) {
      const rp = projectFromManifest(state.rootManifest, "");
      if (!list.some((p) => p.slug === rp.slug || p._base === "")) list.unshift(rp);
    }
    return list;
  }

  function currentProjectSlug() {
    const m = state.manifest || {};
    const hit = projectList().find((p) => p._base === state.base);
    return hit ? hit.slug : (m.slug || m.repo_name || "");
  }

  function projectUrl(p, hash) {
    const q = p && p._base ? "?p=" + encodeURIComponent(p.slug) : "";
    return window.location.pathname + q + (hash || "#overview");
  }

  function closeProjectMenu() {
    const menu = $("#projMenu");
    if (menu && !menu.hidden) {
      menu.hidden = true;
      const b = $("#projBtn");
      if (b) b.setAttribute("aria-expanded", "false");
    }
  }

  function renderProjectSwitcher() {
    const host = $("#projSwitch");
    const pill = $("#brandRepo");
    if (!host) return;
    clearEl(host);
    const list = projectList();
    if (!state.registry || !list.length) {
      host.classList.add("hidden");
      if (pill) pill.classList.remove("hidden");
      return;
    }
    if (pill) pill.classList.add("hidden");
    host.classList.remove("hidden");
    const cur = state.manifest ? currentProjectSlug() : "";
    const label = state.manifest ? (state.manifest.repo_name || state.manifest.slug || cur) : "All proofs";
    const menu = el("div", { className: "proj-menu", id: "projMenu", role: "menu", hidden: true });
    const btn = el("button", {
      type: "button", className: "proj-btn", id: "projBtn", "aria-haspopup": "menu", "aria-expanded": "false", "aria-controls": "projMenu", title: "Switch proof",
      onclick: async (ev) => {
        ev.stopPropagation();
        const opening = menu.hidden;
        if (opening && state.base && !state.rootManifest && !state.rootTried && !projectList().some((p) => p._base === "")) {
          state.rootTried = true;
          try {
            const rm = await fetchJson("./manifest.json", { root: true });
            if (rm && rm.schema) { state.rootManifest = rm; renderProjectSwitcher(); const b2 = $("#projBtn"); if (b2) b2.click(); return; }
          } catch (_) { /* no root project */ }
        }
        menu.hidden = !opening;
        btn.setAttribute("aria-expanded", opening ? "true" : "false");
        if (opening) { const f = menu.querySelector(".proj-item.active") || menu.querySelector(".proj-item"); if (f) f.focus(); }
      }
    }, [el("span", { className: "proj-btn-lbl", textContent: label }), el("span", { className: "proj-caret", "aria-hidden": "true", textContent: "▾" })]);
    for (const p of list) {
      const active = Boolean(state.manifest) && p.slug === cur;
      menu.appendChild(el("a", { className: "proj-item" + (active ? " active" : ""), role: "menuitem", href: projectUrl(p, "#overview"), "aria-current": active ? "true" : null }, [
        el("span", { className: "proj-item-slug", textContent: p.slug }),
        p.title && p.title !== p.slug ? el("span", { className: "proj-item-title", textContent: p.title }) : null
      ]));
    }
    menu.appendChild(el("div", { className: "proj-sep", role: "separator" }));
    menu.appendChild(el("a", { className: "proj-item all", role: "menuitem", href: "#projects", onclick: closeProjectMenu, textContent: "All proofs (" + list.length + ") ›" }));
    menu.addEventListener("keydown", (ev) => {
      if (ev.key === "Escape") { ev.stopPropagation(); closeProjectMenu(); btn.focus(); }
      if (ev.key === "ArrowDown" || ev.key === "ArrowUp") {
        ev.preventDefault();
        const items = $$(".proj-item", menu);
        const i = items.indexOf(document.activeElement);
        const n = items[(i + (ev.key === "ArrowDown" ? 1 : -1) + items.length) % items.length];
        if (n) n.focus();
      }
    });
    host.appendChild(btn);
    host.appendChild(menu);
  }

  async function renderProjectsHome() {
    const main = $("#appMain");
    clearEl(main);
    if (!state.rootManifest && state.base) {
      try {
        const rm = await fetchJson("./manifest.json", { root: true });
        if (rm && rm.schema) state.rootManifest = rm;
      } catch (_) { /* gallery root without its own project */ }
    }
    const list = projectList();
    main.appendChild(el("header", { className: "page-head" }, [
      el("h1", { textContent: "Proofs" }),
      el("p", { className: "page-lede", textContent: list.length > 1
        ? "Lean 4 formalizations read with the same tools. Kernel exports come with dependency diagrams and edge data; source-only scans map modules, imports and declarations."
        : "Only one proof is published here." })
    ]));
    const cur = state.manifest ? currentProjectSlug() : "";
    const groupOf = (p) => (p.has_kernel_export && !p.source_only && p.category !== "demo") ? "kernel" : (PROJECT_GROUPS.some(([k]) => k === p.category) ? p.category : "other");
    for (const [gk, glabel] of PROJECT_GROUPS) {
      const items = list.filter((p) => groupOf(p) === gk);
      if (!items.length) continue;
      main.appendChild(el("div", { className: "section-hdr" }, [el("h2", { textContent: glabel })]));
      main.appendChild(el("div", { className: "proj-grid" }, items.map((p) => {
        const facts = [
          p.files ? fmtInt(p.files) + " files" : null,
          p.lines ? fmtInt(p.lines) + " lines" : null,
          p.decls ? fmtInt(p.decls) + " declarations" : null
        ].filter(Boolean).join(" · ");
        let sorryTxt = null;
        if (p.proof_sorry != null) {
          sorryTxt = fmtInt(p.proof_sorry) + " proof sorry" + (Number(p.challenge_sorry) ? " (+" + fmtInt(p.challenge_sorry) + " in challenge specs)" : "");
        } else if (p.sorry != null) {
          sorryTxt = Number(p.sorry) ? fmtInt(p.sorry) + " sorry" + (p.sorry_files ? " in " + fmtInt(p.sorry_files) + " files" : "") : "no sorry";
        }
        const checks = [
          sorryTxt,
          p.axioms != null ? (Number(p.axioms) ? fmtInt(p.axioms) + " custom axioms" : "no custom axioms") : null
        ].filter(Boolean).join(" · ");
        const license = p.license || (p.slug === "riemann-hypothesis" ? "None (no license)" : "Not stated");
        const repo = safeHref(p.repo_url);
        const isCur = p.slug === cur;
        return el("article", { className: "proj-card" + (isCur ? " current" : "") }, [
          el("div", { className: "proj-card-top" }, [
            el("h3", { textContent: p.title || p.slug }),
            el("span", { className: "proj-card-slug", textContent: p.slug })
          ]),
          p.tagline ? el("p", { className: "proj-card-tag", textContent: p.tagline }) : null,
          facts ? el("p", { className: "proj-card-facts", textContent: facts }) : null,
          checks ? el("p", { className: "proj-card-facts", textContent: checks }) : null,
          el("p", { className: "proj-card-license" }, [el("span", { className: "license-badge", textContent: "License: " + license })]),
          el("div", { className: "cir-ins-acts" }, [
            isCur ? el("a", { className: "btn sm", href: "#overview", textContent: "Overview ›" }) : el("a", { className: "btn sm primary", href: projectUrl(p, "#overview"), textContent: "Open ›" }),
            repo ? el("a", { className: "btn sm", href: repo, target: "_blank", rel: "noopener noreferrer", textContent: "Proof source ↗" }) : null
          ])
        ]);
      })));
    }
    main.appendChild(el("details", { className: "add-proof" }, [
      el("summary", { textContent: "Add your own Lean proof" }),
      el("p", { textContent: "Any public Lean 4 repository can be added. leanre scans the source (and a kernel export, if you have one) and writes a static folder that any web server can host." }),
      el("p", { textContent: "You need git and Python 3.11 or newer. A source scan needs no Lean toolchain; kernel diagrams need an NDJSON export, described in the README." }),
      el("pre", null, [el("code", { textContent: "git clone https://github.com/bohemian-miser/leanre && cd leanre\npython3 -m leanre.leanre gallery add path/to/your-repo \\\n    --out-dir site --slug your-proof --title \"Your proof\" \\\n    --repo-url https://github.com/you/your-proof --pinned-commit <sha>\npython3 -m http.server --directory site 8000" })]),
      el("p", null, [el("a", { href: LEANRE_REPO_URL + "#readme", target: "_blank", rel: "noopener noreferrer", textContent: "Read the README for kernel exports ↗" })]),
      el("p", { textContent: "This writes site/p/your-proof/ and updates site/projects.json. To publish it here, open a pull request that adds the p/your-proof/ folder and its entry in projects.json." })
    ]));
  }

  // ==========================================================================
  // OUTLINE RAIL + BREADCRUMBS
  // ==========================================================================
  const TAB_LABEL = {
    overview: "Overview", circuit: "Diagrams", findings: "Findings", dossiers: "Dossiers", blueprints: "Blueprints",
    flirt: "Clusters", atlas: "Edge Map", portability: "Islands", benchmarks: "Benchmarks", search: "Search",
    experiments: "Moved", item: "Declaration", projects: "Proofs"
  };

  function isMobileRail() {
    return window.matchMedia ? window.matchMedia("(max-width: 900px)").matches : false;
  }

  function initRailState() {
    try {
      const v = window.localStorage.getItem("leanre_site_rail");
      if (v === "closed") state.rail.open = false;
      const md = window.localStorage.getItem("leanre_site_rail_mode");
      if (md === "spine" || md === "topics" || md === "folders") state.rail.mode = md;
    } catch (_) { /* ignore */ }
  }

  function applyRailVisibility() {
    const rail = $("#outlineRail");
    const hasRail = Boolean(rail && !rail.hidden);
    const mobile = isMobileRail();
    document.body.classList.toggle("rail-on", hasRail && !mobile && state.rail.open);
    document.body.classList.toggle("rail-mobile-open", hasRail && mobile && state.rail.mobileOpen);
    const t = $("#railToggleBtn");
    if (t) {
      t.classList.toggle("hidden", !hasRail);
      t.setAttribute("aria-expanded", String(mobile ? state.rail.mobileOpen : state.rail.open));
    }
  }

  function toggleRail(force) {
    if (isMobileRail()) {
      state.rail.mobileOpen = force != null ? Boolean(force) : !state.rail.mobileOpen;
    } else {
      state.rail.open = force != null ? Boolean(force) : !state.rail.open;
      try { window.localStorage.setItem("leanre_site_rail", state.rail.open ? "open" : "closed"); } catch (_) { /* ignore */ }
    }
    applyRailVisibility();
    if (state.route.tab === "circuit") requestAnimationFrame(fitCircuitStage);
  }

  async function ensureOutline() {
    if (state.outline) return state.outline;
    const p = state.manifest && state.manifest.assets && state.manifest.assets.outline;
    if (!p) return null;
    try {
      const o = await fetchJson(p);
      state.outline = (o && typeof o === "object") ? o : null;
    } catch (_) {
      state.outline = null;
    }
    return state.outline;
  }

  function railModes() {
    const m = state.manifest || {};
    const a = m.assets || {};
    const o = state.outline || {};
    const modes = [];
    if ((o.spine && o.spine.length) || (m.overview_pillars && m.overview_pillars.length)) modes.push(["spine", "Proof Spine"]);
    if ((o.clusters && o.clusters.length) || a.outline || a.cluster_labels) modes.push(["topics", "Topics"]);
    if ((o.folders && o.folders.length) || a.outline || (m.top_modules && m.top_modules.length)) modes.push(["folders", "Folders"]);
    return modes;
  }

  function currentItemName() {
    const r = state.route || {};
    return r.tab === "item" ? [r.sub, r.arg].filter(Boolean).join("/") : "";
  }

  function railRow(o) {
    const attrs = {
      className: "rail-row" + (o.active ? " active" : "") + (o.cls ? " " + o.cls : ""),
      style: o.depth ? { paddingLeft: (10 + Math.min(4, o.depth) * 12) + "px" } : null,
      title: o.title || null,
      "aria-current": o.active ? "page" : null
    };
    const kids = [
      el("span", { className: "rail-lbl", textContent: o.label }),
      o.count != null && o.count !== "" ? el("span", { className: "rail-cnt", textContent: typeof o.count === "number" ? fmtCompact(o.count) : String(o.count) }) : null
    ];
    if (o.href) return el("a", Object.assign(attrs, { href: o.href, onclick: o.onclick || null }), kids);
    return el("button", Object.assign(attrs, { type: "button", onclick: o.onclick || null }), kids);
  }

  function renderRail() {
    const rail = $("#outlineRail");
    if (!rail) return;
    clearEl(rail);
    const modes = state.manifest ? railModes() : [];
    if (!modes.length) {
      rail.hidden = true;
      applyRailVisibility();
      return;
    }
    rail.hidden = false;
    if (!modes.some(([k]) => k === state.rail.mode)) state.rail.mode = modes[0][0];
    rail.appendChild(el("div", { className: "rail-hd" }, [
      el("div", { className: "rail-modes", role: "tablist", "aria-label": "Outline view" }, modes.map(([k, lbl]) => el("button", {
        type: "button", role: "tab", "aria-selected": k === state.rail.mode ? "true" : "false",
        className: k === state.rail.mode ? "active" : "", textContent: lbl,
        onclick: () => {
          state.rail.mode = k;
          try { window.localStorage.setItem("leanre_site_rail_mode", k); } catch (_) { /* ignore */ }
          renderRail();
        }
      }))),
      el("button", { type: "button", className: "rail-close", "aria-label": "Close outline", title: "Close outline", textContent: "×", onclick: () => toggleRail(false) })
    ]));
    const list = el("div", { className: "rail-list", id: "railList" });
    rail.appendChild(list);
    applyRailVisibility();
    fillRailList(list, state.rail.mode);
  }

  async function fillRailList(list, mode) {
    const m = state.manifest || {};
    const a = m.assets || {};
    if (mode !== "spine" && !state.outline && a.outline) {
      list.appendChild(el("div", { className: "rail-note", textContent: "Loading…" }));
      await ensureOutline();
      if (!list.isConnected) return;
      clearEl(list);
    }
    const o = state.outline || {};
    const cur = currentItemName();
    const closeOnMobile = () => { if (isMobileRail()) toggleRail(false); };

    if (mode === "spine") {
      const items = (o.spine && o.spine.length) ? o.spine : (m.overview_pillars || []).map((p) => ({
        name: p.decl || p.target || "", label: p.label || p.name, dom: p.subtree_size ?? p.count ?? p.dom, depth: p.depth,
        circuit_mode: p.circuit_mode, circuit_target: p.circuit_target, note: p.note || p.description
      }));
      list.appendChild(el("div", { className: "rail-note", textContent: "Ordered by exclusive subtree size (declarations reached only through this node)." }));
      for (const it of items) {
        const nm = it.name || "";
        const label = it.label || it.short || shortName(nm) || "—";
        const href = nm ? "#item/" + encodeURIComponent(nm)
          : (it.circuit_mode && it.circuit_target ? "#circuit/" + it.circuit_mode + "/" + encodeURIComponent(it.circuit_target) : null);
        list.appendChild(railRow({ label, count: Number(it.dom) || null, depth: Number(it.depth) || 0, href, active: Boolean(nm) && nm === cur, title: [nm, it.note].filter(Boolean).join(" — "), onclick: closeOnMobile }));
      }
      return;
    }

    if (mode === "topics") {
      let clusters = o.clusters;
      if ((!clusters || !clusters.length) && a.cluster_labels) {
        try {
          const doc = await fetchJson(a.cluster_labels);
          clusters = (doc.clusters || []).map((c) => ({
            id: c.cluster_id, label: (c.blinded_label && c.blinded_label.label) || c.pillar || c.cluster_id,
            count: c.counts && c.counts.live_decls, mismatch_status: c.mismatch_audit && c.mismatch_audit.status
          }));
        } catch (_) { clusters = []; }
        if (!list.isConnected) return;
      }
      list.appendChild(el("div", { className: "rail-note", textContent: "Groups of declarations with the same structural shape, labeled by topic." }));
      for (const c of (clusters || [])) {
        const label = String(c.label || c.id || "").replace(/^\[M\]\s*/, "");
        list.appendChild(railRow({
          label, count: Number(c.count) || null, title: (c.id || "") + (c.mismatch_status === "cross_domain_misplaced" ? " · in an unexpected folder" : ""),
          cls: c.mismatch_status === "cross_domain_misplaced" ? "flag" : "",
          href: "#flirt",
          onclick: () => { state.flirt.q = String(c.id || ""); state.flirt.status = "all"; state.flirt.page = 0; closeOnMobile(); if (state.route.tab === "flirt") handleRoute(); }
        }));
      }
      return;
    }

    // Folders
    let folders = o.folders;
    if ((!folders || !folders.length) && m.top_modules && m.top_modules.length) {
      const byDir = new Map();
      for (const t of m.top_modules) {
        const fp = String(t.file_path || String(t.module || "").replace(/\./g, "/") + ".lean");
        const dir = fp.includes("/") ? fp.slice(0, fp.lastIndexOf("/")) : "(top level)";
        if (!byDir.has(dir)) byDir.set(dir, { path: dir, files: 0, top_modules: [] });
        const d = byDir.get(dir);
        d.files++;
        d.top_modules.push({ module: t.module, file: fp, decls: t.decl_count });
      }
      folders = Array.from(byDir.values()).sort((x, y) => y.files - x.files);
    }
    const st = m.stats || {};
    if (Number(st.flirt_misfiles) >= 20 || a.cluster_labels) {
      list.appendChild(el("div", { className: "rail-note" }, [
        "Folder names here are not a reliable guide to content. ",
        el("a", { href: "#flirt", textContent: "Clusters compares the two ›" })
      ]));
    }
    if (o.folder_stats && o.folder_stats.total_dirs > (folders || []).length) {
      list.appendChild(el("div", { className: "rail-note", textContent: "The " + fmtInt((folders || []).length) + " largest of " + fmtInt(o.folder_stats.total_dirs) + " folders." }));
    }
    const flist = folders || [];
    const topCount = new Map();
    for (const f of flist) { const top = String(f.path || f.name || "").split("/")[0]; topCount.set(top, (topCount.get(top) || 0) + 1); }
    const groups = new Map();
    for (const f of flist) {
      const path = String(f.path || f.name || "");
      const segs = path.split("/");
      const key = (topCount.get(segs[0]) > 25 && segs.length > 1) ? segs.slice(0, 2).join("/") : segs[0];
      if (!groups.has(key)) groups.set(key, { key, files: 0, folders: [] });
      const g = groups.get(key);
      g.files += Number(f.files) || 0;
      g.folders.push(f);
    }
    const folderRow = (f, groupKey) => {
      const path = String(f.path || f.name || "");
      const rel = path === groupKey ? "(this folder)" : path.slice(groupKey.length).replace(/^\//, "");
      const kids = el("div", { className: "rail-kids", hidden: true });
      const row = railRow({
        label: rel, depth: 1, count: f.files != null ? Number(f.files) : null, cls: "folder", title: path + (f.decls ? " · " + fmtInt(f.decls) + " declarations" : ""),
        onclick: () => {
          kids.hidden = !kids.hidden;
          row.classList.toggle("open", !kids.hidden);
          if (!kids.hidden && !kids.childNodes.length) {
            for (const tm of (f.top_modules || []).slice(0, 12)) {
              const mod = String(tm.module || "");
              kids.appendChild(railRow({ label: shortName(mod), title: mod, count: tm.decls != null ? Number(tm.decls) : null, depth: 2, href: "#item/" + encodeURIComponent(mod), onclick: closeOnMobile }));
            }
            kids.appendChild(railRow({ label: "Search this folder ›", depth: 2, cls: "muted", href: "#search/" + encodeURIComponent(path.replace(/\//g, ".")), onclick: closeOnMobile }));
          }
        }
      });
      return [row, kids];
    };
    for (const g of Array.from(groups.values()).sort((x, y) => y.files - x.files)) {
      const kids = el("div", { className: "rail-kids", hidden: true });
      const row = railRow({
        label: g.key.replace(/\//g, "."), count: g.files || null, cls: "folder group", title: g.key + " · " + g.folders.length + " folders",
        onclick: () => {
          kids.hidden = !kids.hidden;
          row.classList.toggle("open", !kids.hidden);
          if (!kids.hidden && !kids.childNodes.length) {
            for (const f of g.folders) folderRow(f, g.key).forEach((n) => kids.appendChild(n));
          }
        }
      });
      list.appendChild(row);
      list.appendChild(kids);
    }
  }

  function crumbLeaf(r) {
    return plainTextFromTex(crumbLeafRaw(r));
  }

  function crumbLeafRaw(r) {
    const m = state.manifest || {};
    if (r.tab === "circuit") return r.arg ? shortName(r.arg) : (r.sub === "macro" ? "Repository map" : "");
    if (r.tab === "findings" && r.sub) { const f = (m.findings || []).find((x) => x.slug === r.sub); return f ? (f.title || f.slug) : r.sub; }
    if (r.tab === "dossiers" && r.sub) {
      if (r.sub === "research") { const d = (m.research || []).find((x) => x.slug === r.arg); return d ? (d.title || d.slug) : "Research"; }
      const d = (m.dossiers || []).find((x) => x.slug === r.sub); return d ? (d.title || d.slug) : r.sub;
    }
    if (r.tab === "blueprints" && r.sub) { const b = (m.blueprints || []).find((x) => x.id === r.sub); return b ? (b.title || b.id) : r.sub; }
    if (r.tab === "item") return shortName(currentItemName());
    if (r.tab === "search" && r.sub) return "“" + r.sub + "”";
    return "";
  }

  function updateCrumbs(r) {
    const bar = $("#crumbBar");
    if (!bar) return;
    clearEl(bar);
    const parts = [];
    if (state.registry) parts.push(["Proofs", "#projects"]);
    if (r.tab !== "projects" && state.manifest) parts.push([state.manifest.repo_name || state.manifest.slug || "Project", "#overview"]);
    if (r.tab !== "overview" && r.tab !== "projects") parts.push([TAB_LABEL[r.tab] || r.tab, "#" + r.tab]);
    const leaf = crumbLeaf(r);
    if (leaf) parts.push([leaf, null]);
    if (parts.length < 2) { bar.classList.add("hidden"); return; }
    bar.classList.remove("hidden");
    parts.forEach(([lbl, href], i) => {
      const last = i === parts.length - 1;
      if (i) bar.appendChild(el("span", { className: "crumb-sep", "aria-hidden": "true", textContent: "›" }));
      bar.appendChild(last || !href
        ? el("span", { className: "crumb cur", "aria-current": last ? "page" : null, textContent: lbl })
        : el("a", { className: "crumb", href, textContent: lbl }));
    });
  }

  // ==========================================================================
  // 2D MAP (embedding_2d.json) + MODULE MATRIX (source-only projects)
  // ==========================================================================
  const MAP_PALETTE = ["#7cc4e4", "#e0a95a", "#6fcf9f", "#c7a6f5", "#e2777a", "#66c6b8", "#d7b46a", "#8fb3ea", "#f09fc7", "#a6d4a0", "#b8a07e", "#9aa4b2"];

  function cssVar(name, fallback) {
    try {
      const v = getComputedStyle(document.documentElement).getPropertyValue(name).trim();
      return v || fallback;
    } catch (_) { return fallback; }
  }

  function map2dPoints(layer, proj) {
    const F = {};
    (layer.fields || []).forEach((f, i) => { F[f] = i; });
    const T = layer.tables || {};
    const xk = proj === "pca" ? "px" : "ux";
    const yk = proj === "pca" ? "py" : "uy";
    const get = (p, k) => (F[k] != null ? p[F[k]] : undefined);
    return (layer.points || []).map((p, i) => ({
      i,
      x: Number(get(p, xk)) || 0,
      y: Number(get(p, yk)) || 0,
      name: String(get(p, "name") || ""),
      short: String(get(p, "short") || shortName(get(p, "name"))),
      label: String(get(p, "label") || "").replace(/^\[M\]\s*/, ""),
      id: String(get(p, "id") || ""),
      dom: Number(get(p, "dom")) || 0,
      pillar: (T.pillars || [])[get(p, "pillar_idx")] || "",
      pillarIdx: Number(get(p, "pillar_idx")) || 0,
      dir: (T.dirs || [])[get(p, "dir_idx")] || "",
      dirIdx: Number(get(p, "dir_idx")) || 0,
      kind: (T.kinds || [])[get(p, "kind_idx")] || "",
      cluster: (T.clusters || [])[get(p, "cluster_idx")] || "",
      mod: String(F.mod != null ? (get(p, "mod") || "") : ((T.mods || [])[get(p, "mod_idx")] || "")),
      line: get(p, "line") != null ? Number(get(p, "line")) : null,
      terms: (get(p, "top_term_idxs") || []).map((t) => (T.vocab_terms || [])[t]).filter(Boolean),
      nn: (get(p, "nn_idx") || []).filter((j) => Number.isInteger(j)),
      drift: Number(get(p, "drift")) || 0
    }));
  }

  function map2dColor(pt, mode) {
    if (mode === "drift") {
      const t = Math.max(0, Math.min(1, pt.drift));
      const a = [91, 127, 166], b = [224, 169, 90];
      return "rgb(" + a.map((v, k) => Math.round(v + (b[k] - v) * t)).join(",") + ")";
    }
    if (mode === "folder") return MAP_PALETTE[pt.dirIdx % MAP_PALETTE.length];
    return MAP_PALETTE[pt.pillarIdx % MAP_PALETTE.length];
  }

  // Plain names for the proof's main parts (pillar codes used in the data).
  const PART_NAMES = {
    A: "Theta & local matching",
    B: "Galois & étale tower",
    C: "Windowed Ш¹",
    D: "Arakelov covolume",
    LIT: "Theta / toroidal core",
    DM: "Shared diamond",
    BR: "Zeta bridge"
  };
  function partName(code) {
    const c = String(code || "");
    return PART_NAMES[c] ? PART_NAMES[c] + " (" + c + ")" : (c ? "Part " + c : "");
  }

  function map2dColorKey(pt, mode) {
    return mode === "folder" ? pt.dirIdx : (mode === "drift" ? -1 : pt.pillarIdx);
  }

  // View window helpers (data coordinates, aspect-locked to the canvas).
  const MAP_W = 760, MAP_H = 560, MAP_PAD = 22;
  function map2dFitWindow(pts, onlyIdx) {
    let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
    const use = onlyIdx ? onlyIdx.map((j) => pts[j]).filter(Boolean) : pts;
    for (const p of use) { x0 = Math.min(x0, p.x); x1 = Math.max(x1, p.x); y0 = Math.min(y0, p.y); y1 = Math.max(y1, p.y); }
    if (!Number.isFinite(x0)) { x0 = -1; x1 = 1; y0 = -1; y1 = 1; }
    const mx = Math.max(1e-6, x1 - x0) * (onlyIdx ? 0.35 : 0.02);
    const my = Math.max(1e-6, y1 - y0) * (onlyIdx ? 0.35 : 0.02);
    return map2dAspect({ x0: x0 - mx, x1: x1 + mx, y0: y0 - my, y1: y1 + my });
  }
  function map2dAspect(win) {
    const want = (MAP_W - 2 * MAP_PAD) / (MAP_H - 2 * MAP_PAD);
    let w = win.x1 - win.x0, h = win.y1 - win.y0;
    const cx = (win.x0 + win.x1) / 2, cy = (win.y0 + win.y1) / 2;
    if (w / h > want) h = w / want; else w = h * want;
    return { x0: cx - w / 2, x1: cx + w / 2, y0: cy - h / 2, y1: cy + h / 2 };
  }
  function map2dToScreen(win, x, y) {
    return [
      MAP_PAD + ((x - win.x0) / (win.x1 - win.x0)) * (MAP_W - 2 * MAP_PAD),
      MAP_H - MAP_PAD - ((y - win.y0) / (win.y1 - win.y0)) * (MAP_H - 2 * MAP_PAD)
    ];
  }
  function map2dToData(win, sx, sy) {
    return [
      win.x0 + ((sx - MAP_PAD) / (MAP_W - 2 * MAP_PAD)) * (win.x1 - win.x0),
      win.y0 + ((MAP_H - MAP_PAD - sy) / (MAP_H - 2 * MAP_PAD)) * (win.y1 - win.y0)
    ];
  }

  function drawMap2d(canvas, pts, opts) {
    canvas.width = MAP_W;
    canvas.height = MAP_H;
    const ctx = canvas.getContext("2d");
    if (!ctx || !pts.length) return;
    const win = opts.win || map2dFitWindow(pts);
    const zoom = opts.zoom || 1;
    ctx.fillStyle = cssVar("--bg-code", "#0c0f13");
    ctx.fillRect(0, 0, MAP_W, MAP_H);
    const hidden = opts.hidden || new Set();
    const rScale = Math.min(2.2, 1 + Math.log2(zoom) * 0.25);
    for (const p of pts) {
      const [sx, sy] = map2dToScreen(win, p.x, p.y);
      p.sx = sx; p.sy = sy;
      p.r = (1.8 + Math.min(4.2, Math.log10(1 + p.dom) * 0.75)) * rScale;
      p.vis = !hidden.has(map2dColorKey(p, opts.color)) && sx > -10 && sx < MAP_W + 10 && sy > -10 && sy < MAP_H + 10;
    }
    const sel = opts.sel >= 0 ? pts[opts.sel] : null;
    const nnSet = new Set(sel ? sel.nn : []);
    ctx.globalAlpha = sel ? 0.32 : 0.82;
    for (const p of pts) {
      if (!p.vis || (sel && (p === sel || nnSet.has(p.i)))) continue;
      ctx.fillStyle = map2dColor(p, opts.color);
      ctx.beginPath();
      ctx.arc(p.sx, p.sy, p.r, 0, Math.PI * 2);
      ctx.fill();
    }
    ctx.globalAlpha = 1;
    const hiColor = cssVar("--text-hi", "#eceff3");
    if (sel) {
      ctx.strokeStyle = cssVar("--text-muted", "#8c96a5");
      ctx.lineWidth = 1.2;
      ctx.setLineDash([4, 3]);
      for (const j of sel.nn) {
        const q = pts[j];
        if (!q) continue;
        ctx.beginPath(); ctx.moveTo(sel.sx, sel.sy); ctx.lineTo(q.sx, q.sy); ctx.stroke();
      }
      ctx.setLineDash([]);
      for (const j of sel.nn) {
        const q = pts[j];
        if (!q) continue;
        ctx.fillStyle = map2dColor(q, opts.color);
        ctx.beginPath(); ctx.arc(q.sx, q.sy, q.r + 1, 0, Math.PI * 2); ctx.fill();
        ctx.strokeStyle = hiColor; ctx.lineWidth = 1; ctx.stroke();
      }
      ctx.fillStyle = map2dColor(sel, opts.color);
      ctx.beginPath(); ctx.arc(sel.sx, sel.sy, sel.r + 2.5, 0, Math.PI * 2); ctx.fill();
      ctx.strokeStyle = hiColor; ctx.lineWidth = 2; ctx.stroke();
    }
    // Labels for the largest visible declarations once zoomed in.
    if (zoom >= 1.8 || (sel && opts.labelSel)) {
      ctx.font = "11px " + cssVar("--sans", "sans-serif");
      ctx.textBaseline = "middle";
      const placed = [];
      const fits = (b) => b.x >= 2 && b.y >= 2 && b.x + b.w <= MAP_W - 2 && b.y + b.h <= MAP_H - 2 &&
        !placed.some((o) => b.x < o.x + o.w && b.x + b.w > o.x && b.y < o.y + o.h && b.y + b.h > o.y);
      const cand = pts.filter((p) => p.vis).sort((a, b) => (b === sel) - (a === sel) || b.dom - a.dom);
      const maxLabels = zoom >= 1.8 ? 18 : 1;
      for (const p of cand) {
        if (placed.length >= maxLabels) break;
        const txt = (opts.layer === "clusters_141" ? (p.label || p.id) : p.short).slice(0, 30);
        const w = ctx.measureText(txt).width + 6;
        const box = { x: p.sx + p.r + 3, y: p.sy - 7, w, h: 14 };
        if (!fits(box)) { box.x = p.sx - p.r - 3 - w; if (!fits(box)) continue; }
        placed.push(box);
        ctx.fillStyle = cssVar("--bg-code", "#0c0f13");
        ctx.globalAlpha = 0.78;
        ctx.fillRect(box.x, box.y, box.w, box.h);
        ctx.globalAlpha = 1;
        ctx.fillStyle = hiColor;
        ctx.fillText(txt, box.x + 3, box.y + 7);
      }
    }
    if (opts.box) {
      const b = opts.box;
      ctx.strokeStyle = cssVar("--accent", "#7cc4e4");
      ctx.lineWidth = 1;
      ctx.setLineDash([3, 3]);
      ctx.strokeRect(Math.min(b.x0, b.x1) + 0.5, Math.min(b.y0, b.y1) + 0.5, Math.abs(b.x1 - b.x0), Math.abs(b.y1 - b.y0));
      ctx.setLineDash([]);
      ctx.fillStyle = cssVar("--accent-bg", "rgba(124,196,228,0.1)");
      ctx.fillRect(Math.min(b.x0, b.x1), Math.min(b.y0, b.y1), Math.abs(b.x1 - b.x0), Math.abs(b.y1 - b.y0));
    }
  }

  function map2dCanvasXY(canvas, ev) {
    const rect = canvas.getBoundingClientRect();
    return [((ev.clientX - rect.left) / rect.width) * canvas.width, ((ev.clientY - rect.top) / rect.height) * canvas.height];
  }

  function map2dHit(canvas, pts, ev) {
    const [cx, cy] = map2dCanvasXY(canvas, ev);
    let best = -1, bd = 81;
    for (const p of pts) {
      if (!p.vis) continue;
      const d = (p.sx - cx) * (p.sx - cx) + (p.sy - cy) * (p.sy - cy);
      if (d < bd) { bd = d; best = p.i; }
    }
    return best;
  }

  function declActions(name, mod, line, opts) {
    const o = opts || {};
    const acts = el("div", { className: "cir-ins-acts" });
    if (name) acts.appendChild(el("a", { className: "btn sm" + (o.primary ? " primary" : ""), href: "#item/" + encodeURIComponent(name), textContent: "Inspect ›" }));
    const gh = mod ? buildGithubUrl(mod, line) : null;
    if (gh) {
      const peek = makeSrcButton(gh, name || mod, { className: "btn sm", text: "Source", links: o.links });
      if (peek) acts.appendChild(peek);
      if (!o.noGithub) acts.appendChild(el("a", { className: "btn sm", href: gh, target: "_blank", rel: "noopener noreferrer", textContent: "Proof file ↗" }));
    }
    return acts;
  }

  function renderMap2dDetail(box, pt, pts, layerKey, onPick) {
    clearEl(box);
    if (!pt) {
      box.appendChild(el("p", { className: "cir-ins-note", textContent: "Click a dot to see what it is, its vocabulary and its five nearest neighbors." }));
      return;
    }
    const title = layerKey === "clusters_141" ? (pt.label || pt.id) : pt.short;
    box.appendChild(el("div", { className: "cir-ins-title", textContent: title }));
    if (layerKey === "clusters_141") box.appendChild(el("div", { className: "cir-ins-note mono", textContent: pt.id + " · represented by " + pt.short }));
    else box.appendChild(el("div", { className: "cir-ins-note mono", textContent: pt.name }));
    const kv = el("div", { className: "cir-ins-kv" });
    const add = (k, v) => { if (v == null || v === "") return; kv.appendChild(el("div", { className: "k", textContent: k })); kv.appendChild(el("div", { className: "v", textContent: String(v) })); };
    add("Kind", pt.kind);
    add("Exclusive subtree", pt.dom ? fmtInt(pt.dom) : "");
    add("Part", partName(pt.pillar));
    add("Folder", pt.dir);
    add("Module", pt.mod ? pt.mod + (pt.line ? ":" + pt.line : "") : "");
    add("Cluster", pt.cluster);
    add("Neighbors elsewhere", Math.round(pt.drift * 10) + " of 10 nearest live in another folder");
    box.appendChild(kv);
    if (pt.terms.length) {
      box.appendChild(el("div", { className: "map-sub", textContent: "Vocabulary" }));
      box.appendChild(el("div", { className: "map-terms", textContent: pt.terms.slice(0, 6).join(" · ") }));
    }
    if (pt.nn.length) {
      box.appendChild(el("div", { className: "map-sub", textContent: "Nearest neighbors" }));
      box.appendChild(el("div", { className: "map-nn" }, pt.nn.slice(0, 5).map((j) => {
        const q = pts[j];
        return q ? el("button", { type: "button", className: "map-nn-btn", title: q.name, textContent: layerKey === "clusters_141" ? (q.label || q.id) : q.short, onclick: () => onPick(j) }) : null;
      })));
    }
    box.appendChild(declActions(pt.name, pt.mod, pt.line, { primary: true }));
  }

  // Mounts the interactive 2D map into `host`. Used on #atlas and the overview lens.
  async function mountMap2d(host, opts) {
    const o = opts || {};
    const path = state.manifest && state.manifest.assets && state.manifest.assets.embedding_2d;
    if (!path || !host) return false;
    clearEl(host);
    host.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading…" })]));
    let doc;
    try { doc = await fetchJson(path); } catch (err) {
      clearEl(host);
      host.appendChild(el("div", { className: "empty-card" }, [el("h3", { textContent: "Could not load the 2D map" }), el("p", { textContent: String(err.message || err) })]));
      return false;
    }
    if (!host.isConnected) return false;
    const layers = doc.layers || {};
    const st = state.map2d;
    if (!layers[st.layer]) st.layer = layers.landmarks ? "landmarks" : Object.keys(layers)[0];
    const layer = layers[st.layer];
    if (!layer) { clearEl(host); return false; }
    clearEl(host);
    const viewKey = st.layer + "|" + st.proj;
    if (st.viewKey !== viewKey) { st.viewKey = viewKey; st.win = null; st.zoom = 1; st.hidden = new Set(); }
    if (!(st.hidden instanceof Set)) st.hidden = new Set();
    if (!st.tool) st.tool = "pan";

    const metrics = layer.metrics || {};
    const drift = metrics.drift || {};
    const mk = metrics[st.proj === "pca" ? "pca2" : "knn2"] || {};
    if (!o.compact) {
      host.appendChild(el("p", { className: "section-lede", textContent: "Each dot is a declaration, placed by the Mathlib vocabulary its statement uses, so nearby dots draw on similar mathematics." + (drift.dom1k_nn1_diff_folder_pct != null ? " " + drift.dom1k_nn1_diff_folder_pct + "% of declarations with 1,000 or more dependants have their nearest neighbor in a different folder." : "") }));
    }
    const seg = (items, key) => el("div", { className: "seg" }, items.map(([k, lbl]) => el("button", {
      type: "button", className: st[key] === k ? "active" : "", textContent: lbl,
      onclick: () => { st[key] = k; if (key === "layer") st.sel = -1; if (key === "color") st.hidden = new Set(); mountMap2d(host, o); }
    })));
    host.appendChild(el("div", { className: "toolbar-row" }, [
      seg([["knn", "Nonlinear (k-NN)"], ["pca", "Linear (PCA)"]], "proj"),
      Object.keys(layers).length > 1 ? seg([["landmarks", "Landmarks (" + fmtInt((layers.landmarks || {}).count || 0) + ")"], ["clusters_141", "Clusters (" + fmtInt((layers.clusters_141 || {}).count || 0) + ")"]].filter(([k]) => layers[k]), "layer") : null,
      seg([["pillar", "Part"], ["folder", "Folder"], ["drift", "Drift"]], "color"),
      !o.compact && mk.knn_preservation != null ? el("span", { className: "toolbar-count", title: "How well the flat layout keeps each point's true nearest neighbors", textContent: "Neighbor preservation " + Number(mk.knn_preservation).toFixed(2) + " · trustworthiness " + Number(mk.trustworthiness).toFixed(2) }) : null
    ]));

    const pts = map2dPoints(layer, st.proj);
    if (st.sel >= pts.length) st.sel = -1;
    const fullWin = map2dFitWindow(pts);
    if (!st.win) st.win = fullWin;
    const fullW = fullWin.x1 - fullWin.x0;
    const zoomOf = (win) => Math.max(1, fullW / (win.x1 - win.x0));

    const canvas = el("canvas", { className: "map2d-canvas", tabindex: "0", "aria-label": "2D map of declarations. Scroll to zoom, drag to pan, double-click to reset." });
    const tip = el("div", { className: "map-tip", hidden: true, role: "tooltip" });
    const detail = el("aside", { className: "map2d-detail" });
    const legend = el("div", { className: "map-legend" });
    const zoomOut = el("span", { className: "map-zoom", textContent: "1.0×" });
    const findStatus = el("span", { className: "map-find-status", "aria-live": "polite" });
    const fitNbBtn = el("button", { type: "button", className: "btn sm", textContent: "Fit neighbors", disabled: st.sel < 0 });
    const toolSeg = el("div", { className: "seg" }, [["pan", "Pan"], ["box", "Box zoom"]].map(([k, lbl]) => el("button", {
      type: "button", className: st.tool === k ? "active" : "", textContent: lbl, title: k === "box" ? "Drag a rectangle to zoom (or hold Shift while dragging)" : "Drag to move the map",
      onclick: (ev) => { st.tool = k; $$("button", toolSeg).forEach((b) => b.classList.toggle("active", b === ev.currentTarget)); canvas.style.cursor = k === "box" ? "crosshair" : "grab"; }
    })));
    const findInput = el("input", { type: "search", className: "input map-find", placeholder: "Find declaration…", "aria-label": "Find a declaration on the map" });

    let box = null;
    const redraw = () => {
      st.zoom = zoomOf(st.win);
      zoomOut.textContent = st.zoom.toFixed(1) + "×";
      fitNbBtn.disabled = st.sel < 0;
      drawMap2d(canvas, pts, { win: st.win, zoom: st.zoom, sel: st.sel, color: st.color, hidden: st.hidden, box, layer: st.layer, labelSel: true });
    };
    const setWin = (win) => {
      let w = map2dAspect(win);
      const minW = fullW / 40;
      if (w.x1 - w.x0 < minW) {
        const cx = (w.x0 + w.x1) / 2, cy = (w.y0 + w.y1) / 2, k = minW / (w.x1 - w.x0);
        w = map2dAspect({ x0: cx - (cx - w.x0) * k, x1: cx + (w.x1 - cx) * k, y0: cy - (cy - w.y0) * k, y1: cy + (w.y1 - cy) * k });
      }
      if (w.x1 - w.x0 >= fullW) w = fullWin;
      st.win = w;
      redraw();
    };
    const zoomAt = (sx, sy, factor) => {
      const [dx, dy] = map2dToData(st.win, sx, sy);
      const w = st.win;
      setWin({ x0: dx - (dx - w.x0) / factor, x1: dx + (w.x1 - dx) / factor, y0: dy - (dy - w.y0) / factor, y1: dy + (w.y1 - dy) / factor });
    };
    const zoomTo = (j, level) => {
      const p = pts[j];
      if (!p) return;
      const w = fullW / level, h = (fullWin.y1 - fullWin.y0) / level;
      setWin({ x0: p.x - w / 2, x1: p.x + w / 2, y0: p.y - h / 2, y1: p.y + h / 2 });
    };
    const pick = (j) => {
      st.sel = j;
      redraw();
      renderMap2dDetail(detail, j >= 0 ? pts[j] : null, pts, st.layer, pick);
    };
    const resetView = () => { box = null; setWin(fullWin); };
    fitNbBtn.addEventListener("click", () => {
      if (st.sel < 0) return;
      setWin(map2dFitWindow(pts, [st.sel].concat(pts[st.sel].nn)));
    });
    const runFind = () => {
      const q = findInput.value.trim().toLowerCase();
      if (!q) { findStatus.textContent = ""; return; }
      const nameOf = (p) => (st.layer === "clusters_141" ? (p.label + " " + p.id + " " + p.short) : p.short).toLowerCase();
      const hit = pts.find((p) => p.short.toLowerCase() === q || p.name.toLowerCase() === q)
        || pts.find((p) => nameOf(p).startsWith(q))
        || pts.find((p) => nameOf(p).includes(q) || p.name.toLowerCase().includes(q));
      if (!hit) { findStatus.textContent = "No match on this map"; return; }
      findStatus.textContent = "";
      if (st.hidden.has(map2dColorKey(hit, st.color))) { st.hidden.delete(map2dColorKey(hit, st.color)); buildLegend(); }
      st.sel = hit.i;
      zoomTo(hit.i, Math.max(6, st.zoom));
      renderMap2dDetail(detail, hit, pts, st.layer, pick);
    };
    findInput.addEventListener("keydown", (ev) => { if (ev.key === "Enter") { ev.preventDefault(); runFind(); } });
    findInput.addEventListener("change", runFind);

    const buildLegend = () => {
      clearEl(legend);
      const tbl = layer.tables || {};
      let keys = [];
      if (st.color === "pillar") {
        keys = (tbl.pillars || []).map((code, k) => [k, partName(code)]);
      } else if (st.color === "folder") {
        const counts = new Map();
        for (const p of pts) counts.set(p.dirIdx, (counts.get(p.dirIdx) || 0) + 1);
        keys = Array.from(counts.entries()).sort((a, b) => b[1] - a[1]).slice(0, 12).map(([k]) => [k, String((tbl.dirs || [])[k] || "folder " + k).split(".").slice(-1)[0]]);
      }
      if (!keys.length) {
        legend.appendChild(el("span", { className: "map-legend-note" }, [el("i", { className: "atlas-swatch", style: { background: "rgb(91,127,166)" } }), "neighbors in the same folder"]));
        legend.appendChild(el("span", { className: "map-legend-note" }, [el("i", { className: "atlas-swatch", style: { background: "rgb(224,169,90)" } }), "neighbors elsewhere"]));
        return;
      }
      for (const [k, label] of keys) {
        const color = MAP_PALETTE[k % MAP_PALETTE.length];
        const off = st.hidden.has(k);
        const pill = el("button", {
          type: "button", className: "map-pill" + (off ? " off" : ""), "aria-pressed": off ? "false" : "true",
          title: "Click to show or hide · double-click to show only this", textContent: label
        });
        pill.prepend(el("i", { className: "atlas-swatch", style: { background: color } }));
        let clickT = null;
        pill.addEventListener("click", () => {
          clearTimeout(clickT);
          clickT = setTimeout(() => {
            if (st.hidden.has(k)) st.hidden.delete(k); else st.hidden.add(k);
            buildLegend(); redraw();
          }, 220);
        });
        pill.addEventListener("dblclick", () => {
          clearTimeout(clickT);
          const all = keys.map(([kk]) => kk);
          const solo = all.every((kk) => kk === k || st.hidden.has(kk)) && !st.hidden.has(k);
          st.hidden = new Set(solo ? [] : all.filter((kk) => kk !== k));
          if (st.color === "folder" && !solo) for (const p of pts) if (p.dirIdx !== k) st.hidden.add(p.dirIdx);
          buildLegend(); redraw();
        });
        legend.appendChild(pill);
      }
      if (st.color === "folder") legend.appendChild(el("span", { className: "map-legend-note", textContent: "Top 12 of " + fmtInt((tbl.dirs || []).length) + " folders" }));
    };

    const showTip = (j, cx, cy) => {
      if (j < 0) { tip.hidden = true; return; }
      const p = pts[j];
      clearEl(tip);
      tip.appendChild(el("div", { className: "map-tip-name", textContent: st.layer === "clusters_141" ? (p.label || p.id) : p.short }));
      const lines = [
        p.pillar ? partName(p.pillar) : null,
        p.dir ? "Folder: " + p.dir : null,
        p.dom ? fmtInt(p.dom) + " in exclusive subtree" : null,
        Math.round(p.drift * 10) + " of 10 nearest neighbors in other folders"
      ].filter(Boolean);
      for (const t of lines) tip.appendChild(el("div", { textContent: t }));
      tip.hidden = false;
      const wrap = canvas.parentElement.getBoundingClientRect();
      const cr = canvas.getBoundingClientRect();
      const px = (cx / canvas.width) * cr.width + (cr.left - wrap.left);
      const py = (cy / canvas.height) * cr.height + (cr.top - wrap.top);
      tip.style.left = Math.min(wrap.width - 250, px + 14) + "px";
      tip.style.top = Math.max(4, Math.min(wrap.height - 90, py + 14)) + "px";
    };

    // Pointer interactions: drag to pan, Box zoom (or Shift+drag), click to select.
    let drag = null;
    canvas.style.cursor = st.tool === "box" ? "crosshair" : "grab";
    canvas.addEventListener("pointerdown", (ev) => {
      if (ev.button !== 0) return;
      const [cx, cy] = map2dCanvasXY(canvas, ev);
      drag = { cx, cy, win: Object.assign({}, st.win), moved: 0, box: st.tool === "box" || ev.shiftKey };
      try { canvas.setPointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
      if (!drag.box) canvas.style.cursor = "grabbing";
    });
    canvas.addEventListener("pointermove", (ev) => {
      const [cx, cy] = map2dCanvasXY(canvas, ev);
      if (drag) {
        drag.moved = Math.max(drag.moved, Math.hypot(cx - drag.cx, cy - drag.cy));
        if (drag.box) {
          box = { x0: drag.cx, y0: drag.cy, x1: cx, y1: cy };
          redraw();
        } else if (drag.moved > 2) {
          const kx = (drag.win.x1 - drag.win.x0) / (MAP_W - 2 * MAP_PAD);
          const ky = (drag.win.y1 - drag.win.y0) / (MAP_H - 2 * MAP_PAD);
          const dx = (cx - drag.cx) * kx, dy = (cy - drag.cy) * ky;
          st.win = { x0: drag.win.x0 - dx, x1: drag.win.x1 - dx, y0: drag.win.y0 + dy, y1: drag.win.y1 + dy };
          redraw();
        }
        tip.hidden = true;
        return;
      }
      const j = map2dHit(canvas, pts, ev);
      canvas.style.cursor = j >= 0 ? "pointer" : (st.tool === "box" ? "crosshair" : "grab");
      showTip(j, cx, cy);
    });
    const endDrag = (ev) => {
      if (!drag) return;
      const d = drag;
      drag = null;
      canvas.style.cursor = st.tool === "box" ? "crosshair" : "grab";
      if (d.box && box && Math.abs(box.x1 - box.x0) > 6 && Math.abs(box.y1 - box.y0) > 6) {
        const [ax, ay] = map2dToData(st.win, Math.min(box.x0, box.x1), Math.max(box.y0, box.y1));
        const [bx, by] = map2dToData(st.win, Math.max(box.x0, box.x1), Math.min(box.y0, box.y1));
        box = null;
        setWin({ x0: ax, x1: bx, y0: ay, y1: by });
        return;
      }
      box = null;
      if (d.moved <= 3 && ev && ev.type === "pointerup") {
        const j = map2dHit(canvas, pts, ev);
        if (j >= 0) { pick(j); return; }
      }
      redraw();
    };
    canvas.addEventListener("pointerup", endDrag);
    canvas.addEventListener("pointercancel", endDrag);
    canvas.addEventListener("pointerleave", () => { tip.hidden = true; });
    canvas.addEventListener("wheel", (ev) => {
      if (o.compact && !(ev.ctrlKey || ev.metaKey) && st.zoom <= 1.01) return;
      ev.preventDefault();
      const [cx, cy] = map2dCanvasXY(canvas, ev);
      zoomAt(cx, cy, Math.exp(-ev.deltaY * 0.0016));
    }, { passive: false });
    canvas.addEventListener("dblclick", (ev) => { ev.preventDefault(); resetView(); });
    canvas.addEventListener("keydown", (ev) => {
      if (ev.key === "+" || ev.key === "=") { ev.preventDefault(); zoomAt(MAP_W / 2, MAP_H / 2, 1.5); }
      else if (ev.key === "-") { ev.preventDefault(); zoomAt(MAP_W / 2, MAP_H / 2, 1 / 1.5); }
      else if (ev.key === "0") { ev.preventDefault(); resetView(); }
    });

    const mapTools = el("div", { className: "map-tools" }, [
      toolSeg,
      el("button", { type: "button", className: "btn sm", title: "Zoom in", "aria-label": "Zoom in", textContent: "+", onclick: () => zoomAt(MAP_W / 2, MAP_H / 2, 1.6) }),
      el("button", { type: "button", className: "btn sm", title: "Zoom out", "aria-label": "Zoom out", textContent: "−", onclick: () => zoomAt(MAP_W / 2, MAP_H / 2, 1 / 1.6) }),
      el("button", { type: "button", className: "btn sm", title: "Show the whole map (or double-click it)", textContent: "Reset", onclick: resetView }),
      zoomOut,
      fitNbBtn,
      el("div", { className: "spacer" }),
      findInput,
      findStatus
    ]);
    host.appendChild(el("div", { className: "map2d-grid" + (o.compact ? " compact" : "") }, [
      el("div", { className: "map2d-main" }, [
        mapTools,
        el("div", { className: "atlas-canvas-wrap map2d-wrap" }, [canvas, tip]),
        legend
      ]),
      detail
    ]));
    buildLegend();
    redraw();
    renderMap2dDetail(detail, st.sel >= 0 ? pts[st.sel] : null, pts, st.layer, pick);
    host._map2d = { pts, pick, zoomTo, resetView, runFind: (q) => { findInput.value = q; runFind(); }, state: st };
    return true;
  }

  function drawModuleMatrix(canvas, mm, sel) {
    const grid = Array.isArray(mm.grid) ? mm.grid : [];
    const G = Number(mm.grid_size) || grid.length || 1;
    const scale = Math.max(4, Math.floor(512 / G));
    const pad = 10;
    const size = G * scale;
    canvas.width = size + 2 * pad;
    canvas.height = size + 2 * pad;
    const ctx = canvas.getContext("2d");
    if (!ctx) return { scale, pad, G };
    ctx.fillStyle = canvasBg();
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    let mx = 1;
    for (const row of grid) for (const v of (row || [])) mx = Math.max(mx, Number(v) || 0);
    const lmx = Math.log1p(mx);
    for (let r = 0; r < G; r++) {
      const row = grid[r] || [];
      for (let c = 0; c < G; c++) {
        const v = Number(row[c]) || 0;
        if (v <= 0) continue;
        const t = Math.pow(Math.log1p(v) / lmx, 0.8);
        let R, Gc, B;
        if (isLightTheme()) {
          [R, Gc, B] = t < 0.6 ? mix([214, 228, 238], [40, 128, 170], t / 0.6) : mix([40, 128, 170], [180, 83, 9], (t - 0.6) / 0.4);
        } else {
          R = Math.round(30 + t * (t > 0.6 ? 200 : 70));
          Gc = Math.round(70 + t * 140);
          B = Math.round(110 + t * (t > 0.6 ? 20 : 130));
        }
        ctx.fillStyle = "rgb(" + R + "," + Gc + "," + B + ")";
        ctx.fillRect(pad + c * scale, pad + r * scale, scale, scale);
      }
    }
    ctx.strokeStyle = canvasInk(0.14);
    ctx.lineWidth = 1;
    let prevTop = null;
    for (const rg of (mm.regions || [])) {
      const b0 = Number(rg.bin_start || 0);
      const top = String(rg.key || "").split(".")[0];
      const changed = prevTop !== null && top !== prevTop;
      prevTop = top;
      if (b0 <= 0 || !changed) continue;
      const p = pad + b0 * scale + 0.5;
      ctx.beginPath(); ctx.moveTo(p, pad); ctx.lineTo(p, pad + size); ctx.moveTo(pad, p); ctx.lineTo(pad + size, p); ctx.stroke();
    }
    ctx.strokeStyle = canvasInk(0.4);
    ctx.strokeRect(pad + 0.5, pad + 0.5, size - 1, size - 1);
    if (sel) {
      ctx.strokeStyle = "#7cc4e4";
      ctx.lineWidth = 2;
      ctx.strokeRect(pad + sel.c * scale - 1, pad + sel.r * scale - 1, scale + 2, scale + 2);
    }
    return { scale, pad, G };
  }

  const EDGE_ROLE = { type: "in the statement", value: "in the proof", both: "statement and proof" };

  function trayHeader(title, sub, onClose) {
    return el("div", { className: "tray-hd" }, [
      el("div", null, [el("strong", { textContent: title }), sub ? el("span", { className: "tray-sub", textContent: sub }) : null]),
      el("button", { type: "button", className: "icon-btn", "aria-label": "Close", title: "Close", textContent: "×", onclick: onClose })
    ]);
  }

  function declTrayRow(d) {
    return el("div", { className: "tray-row" }, [
      el("div", { className: "tray-main" }, [
        el("span", { className: "tray-name", title: d.name, textContent: d.short || shortName(d.name) }),
        el("span", { className: "tray-meta", textContent: [d.kind, d.dom ? fmtInt(d.dom) + " in subtree" : null, d.mod ? shortName(d.mod) + (d.line ? ":" + d.line : "") : null].filter(Boolean).join(" · ") })
      ]),
      declActions(d.name, d.mod, d.line, { noGithub: true })
    ]);
  }

  // e = [src_name, dst_name, edge_role, src_mod, src_line, dst_mod, dst_line]
  function edgeTrayRow(e) {
    const [sName, dName, role, sMod, sLine, dMod, dLine] = e;
    const sUrl = sMod ? buildGithubUrl(sMod, sLine) : null;
    const dUrl = dMod ? buildGithubUrl(dMod, dLine) : null;
    const canCompare = isLeanBlob(sUrl) || isLeanBlob(dUrl);
    return el("div", { className: "tray-row" }, [
      el("div", { className: "tray-main" }, [
        el("span", { className: "tray-name", title: sName + " → " + dName }, [
          el("a", { href: "#item/" + encodeURIComponent(sName), textContent: shortName(sName) }),
          el("span", { className: "tray-arrow", textContent: " → " }),
          el("a", { href: "#item/" + encodeURIComponent(dName), textContent: shortName(dName) })
        ]),
        el("span", { className: "tray-meta", textContent: (EDGE_ROLE[role] || role || "") + (sMod ? " · " + shortName(sMod) : "") })
      ]),
      el("div", { className: "cir-ins-acts" }, [
        el("a", { className: "btn sm", href: "#item/" + encodeURIComponent(sName), textContent: "Inspect ›" }),
        sUrl ? makeSrcButton(sUrl, sName, { className: "btn sm", text: "Source" }) : null,
        canCompare ? el("button", { type: "button", className: "btn sm", textContent: "Compare A ↔ B", onclick: () => openSourceCompare(
          { url: sUrl || "", title: sName, line: sLine, label: "A" },
          { url: dUrl || "", title: dName, line: dLine, label: "B" }
        ) }) : null
      ])
    ]);
  }

  function moduleTrayRow(t) {
    const url = safeHref(t.url) || buildGithubUrl(t.name || t.module, 1);
    const name = t.name || t.module || "";
    return el("div", { className: "tray-row" }, [
      el("div", { className: "tray-main" }, [
        el("span", { className: "tray-name", title: name, textContent: name }),
        el("span", { className: "tray-meta", textContent: [t.decl_count != null ? fmtInt(t.decl_count) + " declarations" : null, t.fan_in != null ? "imported by " + fmtInt(t.fan_in) : null].filter(Boolean).join(" · ") })
      ]),
      el("div", { className: "cir-ins-acts" }, [
        el("a", { className: "btn sm", href: "#item/" + encodeURIComponent(name), textContent: "Inspect ›" }),
        url ? makeSrcButton(url, name, { className: "btn sm", text: "Source" }) : null
      ])
    ]);
  }

  function renderModuleMatrixBody(mm) {
    const main = $("#appMain");
    clearEl(main);
    main.appendChild(el("header", { className: "page-head" }, [
      el("h1", { textContent: "Module Matrix" }),
      el("p", { className: "page-lede", textContent: "Imports between the " + fmtInt(mm.n_modules || 0) + " modules, ordered so that each folder sits in one block. " + (mm.diagonal_near_pct != null ? mm.diagonal_near_pct + "% of the " + fmtInt(mm.n_edges || 0) + " imports stay near the diagonal, inside or next to their own folder." : "") })
    ]));
    const canvas = el("canvas", { className: "atlas-canvas", id: "moduleMatrixCanvas", "aria-label": "Module import matrix" });
    const readout = el("div", { className: "atlas-readout", textContent: "Hover a cell to see which folders it connects; click it to list the modules and imports inside." });
    const tray = el("div", { className: "cell-tray", hidden: true });
    main.appendChild(el("section", { className: "atlas-card" }, [
      el("div", { className: "atlas-card-hd" }, [el("h3", { textContent: "Imports by folder" })]),
      el("p", { className: "atlas-explain", textContent: "Each cell counts imports from the modules in its row to the modules in its column. Brighter cells hold more imports." }),
      el("div", { className: "atlas-canvas-wrap" }, [canvas]),
      el("p", { className: "atlas-axis", textContent: "Rows import columns. Lines mark where the top-level folder changes." }),
      readout,
      tray
    ]));
    let geo = drawModuleMatrix(canvas, mm, null);
    const cellAt = (ev) => {
      const rect = canvas.getBoundingClientRect();
      const cx = ((ev.clientX - rect.left) / rect.width) * canvas.width;
      const cy = ((ev.clientY - rect.top) / rect.height) * canvas.height;
      const c = Math.floor((cx - geo.pad) / geo.scale);
      const r = Math.floor((cy - geo.pad) / geo.scale);
      return (r < 0 || c < 0 || r >= geo.G || c >= geo.G) ? null : { r, c };
    };
    const binLabel = (i) => ((mm.bins || [])[i] || {}).label || "block " + i;
    canvas.addEventListener("mousemove", (ev) => {
      const cell = cellAt(ev);
      if (!cell) return;
      const v = Number(((mm.grid || [])[cell.r] || [])[cell.c]) || 0;
      readout.textContent = binLabel(cell.r) + " → " + binLabel(cell.c) + " · " + fmtInt(v) + " imports";
      canvas.style.cursor = v > 0 ? "pointer" : "crosshair";
    });
    canvas.addEventListener("click", (ev) => {
      const cell = cellAt(ev);
      if (!cell) return;
      geo = drawModuleMatrix(canvas, mm, cell);
      const samples = (mm.cell_samples || {})[cell.r + "," + cell.c] || [];
      const rowB = (mm.bins || [])[cell.r] || {};
      const colB = (mm.bins || [])[cell.c] || {};
      clearEl(tray);
      tray.hidden = false;
      tray.appendChild(trayHeader(binLabel(cell.r) + " → " + binLabel(cell.c), fmtInt(Number(((mm.grid || [])[cell.r] || [])[cell.c]) || 0) + " imports", () => { tray.hidden = true; geo = drawModuleMatrix(canvas, mm, null); }));
      tray.appendChild(el("div", { className: "tray-cols" }, [
        el("div", null, [el("h4", { textContent: "Row: largest modules" }), ...((rowB.top_modules || []).slice(0, 4).map(moduleTrayRow))]),
        el("div", null, [el("h4", { textContent: "Column: largest modules" }), ...((colB.top_modules || []).slice(0, 4).map(moduleTrayRow))])
      ]));
      if (samples.length) {
        tray.appendChild(el("h4", { textContent: "Sample imports in this cell" }));
        for (const sm of samples.slice(0, 6)) {
          tray.appendChild(edgeTrayRow([sm.src, sm.dst, "", sm.src, 1, sm.dst, 1]));
        }
      }
    });
    const mapHost = el("section", { className: "map2d-section", id: "map2dSection" });
    if (state.manifest.assets && state.manifest.assets.embedding_2d) {
      main.appendChild(el("div", { className: "section-hdr" }, [el("h2", { textContent: "2D Map" })]));
      main.appendChild(mapHost);
      mountMap2d(mapHost);
    }
  }

  // ==========================================================================
  // DECLARATION INSPECTOR (#item/<name>)
  // ==========================================================================
  async function findSearchEntry(name) {
    const sMeta = state.manifest && state.manifest.search;
    if (!sMeta || !name) return null;
    const packs = await Promise.all(searchShardPrefixesForQuery(name).map((p) => loadSearchShard(p)));
    let loose = null;
    for (const pk of packs) {
      for (const raw of (pk.rows || [])) {
        const e = normalizeSearchEntry(raw, pk.modPrefixes);
        if (e.name === name) return e;
        if (!loose && !name.includes(".") && shortName(e.name) === name) loose = e;
      }
    }
    return loose;
  }

  function cachedAsset(key) {
    const p = state.manifest && state.manifest.assets && state.manifest.assets[key];
    return p ? (state.cacheJson.get(projectRelPath(p)) || null) : null;
  }

  function moduleFromOutline(name) {
    const m = state.manifest || {};
    const tm = (m.top_modules || []).find((t) => t.module === name);
    if (tm) return { module: name, file: tm.file_path, decls: tm.decl_count };
    for (const f of ((state.outline && state.outline.folders) || [])) {
      const hit = (f.top_modules || []).find((t) => t.module === name);
      if (hit) return { module: name, file: hit.file, decls: hit.decls, folder: f.path };
    }
    return null;
  }

  async function gatherItemInfo(name) {
    await ensureOutline();
    const info = { name, short: shortName(name), kind: "", mod: "", line: null, dom: null, live: null, circuit: null, bpId: null, isModule: false, spine: null, found: false };
    const e = await findSearchEntry(name);
    if (e) {
      Object.assign(info, { name: e.name, short: shortName(e.name), kind: e.kind, mod: e.mod, line: e.line, dom: e.dom || null, live: e.live, bpId: e.bpId, found: true });
      info.circuit = findAnyCircuitForSymbol(e.name, e.circuitPath);
    }
    const sp = ((state.outline && state.outline.spine) || []).find((s) => s.name === info.name);
    if (sp) {
      info.spine = sp;
      info.found = true;
      info.kind = info.kind || sp.kind || "";
      info.mod = info.mod || sp.mod || "";
      info.line = info.line || sp.line || null;
      info.dom = info.dom || sp.dom || null;
    }
    if (!info.circuit) info.circuit = findAnyCircuitForSymbol(info.name);
    const atlas = cachedAsset("atlas");
    if (atlas && !info.line) {
      for (const bin of ((atlas.hic_matrix && atlas.hic_matrix.bin_catalog) || [])) {
        const d = (bin || []).find((x) => x.name === info.name);
        if (d) { info.line = d.line; info.mod = info.mod || d.mod; info.kind = info.kind || d.kind; break; }
      }
    }
    if (!info.found) {
      const mod = moduleFromOutline(name);
      const looksModule = /^[A-Z][A-Za-z0-9_']*(\.[A-Z][A-Za-z0-9_']*)+$/.test(name);
      if (mod || (e && e.kind === "module")) { Object.assign(info, { isModule: true, kind: "module", mod: name, found: true, decls: mod && mod.decls }); }
      else if (looksModule && state.manifest.source_only) { Object.assign(info, { isModule: true, kind: "module", mod: name }); }
    }
    if (info.kind === "module") info.isModule = true;
    info.neighbors = (state.outline && state.outline.neighbors && state.outline.neighbors[info.name]) || null;
    if (!info.neighbors && info.circuit && info.circuit.path) {
      try {
        const data = await fetchJson(info.circuit.path);
        const nodes = (data.payload && data.payload.nodes) || [];
        const pick = (kind) => nodes.filter((n) => n.kind === kind && n.full_name && !/\s/.test(n.full_name)).map((n) => ({ name: n.full_name, rel: "" }));
        const dep = pick("callee"), use = pick("caller");
        if (dep.length || use.length) info.neighbors = { used_by: use, depends_on: dep, fromDiagram: true };
      } catch (_) { /* optional */ }
    }
    return info;
  }

  // Map of identifier -> declaration name, built only from names we know are
  // related to this item (neighbors, diagram nodes, twins). No fuzzy matching.
  function buildKnownLinks(info, extraNames) {
    const full = new Set();
    const add = (n) => { if (n && typeof n === "string" && n !== info.name) full.add(n); };
    if (info.neighbors) {
      for (const x of (info.neighbors.used_by || [])) add(x.name);
      for (const x of (info.neighbors.depends_on || [])) add(x.name);
    }
    for (const n of (extraNames || [])) add(n);
    const links = new Map();
    const shortCount = new Map();
    for (const n of full) { const s = shortName(n); shortCount.set(s, (shortCount.get(s) || 0) + 1); }
    for (const n of full) {
      links.set(n, n);
      const s = shortName(n);
      if (shortCount.get(s) === 1 && s.length > 2) links.set(s, n);
    }
    return links;
  }

  function neighborList(title, arrow, items) {
    return el("div", { className: "nb-col" }, [
      el("div", { className: "nb-hd", textContent: title + " " + arrow }),
      items && items.length
        ? el("ul", { className: "nb-list" }, items.slice(0, 8).map((x) => el("li", null, [
          el("a", { href: "#item/" + encodeURIComponent(x.name), title: x.name, textContent: shortName(x.name) }),
          x.rel ? el("span", { className: "nb-rel", textContent: EDGE_ROLE[x.rel === "type" ? "type" : (x.rel === "value" ? "value" : "both")] || x.rel }) : null
        ])).concat(items.length > 8 ? [el("li", { className: "nb-more", textContent: "and " + fmtInt(items.length - 8) + " more" })] : []))
        : el("p", { className: "nb-empty", textContent: "Not recorded for this declaration." })
    ]);
  }

  async function renderItemView(rawName) {
    const main = $("#appMain");
    clearEl(main);
    const name = String(rawName || "").trim();
    if (!name) { navigate("#search", true); return; }
    if (state.item.name !== name) { state.item.name = name; state.item.view = "summary"; }
    main.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Looking up " + shortName(name) + "…" })]));
    const info = await gatherItemInfo(name);
    if (state.route.tab !== "item" || currentItemName() !== name) return;
    clearEl(main);
    updateCrumbs(state.route);

    const gh = info.mod ? buildGithubUrl(info.mod, info.isModule ? null : info.line) : null;
    const meta = [
      info.kind || null,
      !info.isModule && info.mod ? info.mod + (info.line ? ":" + info.line : "") : null,
      info.dom ? fmtInt(info.dom) + " declarations in exclusive subtree" : null,
      info.live === 0 ? "unreachable" : null
    ].filter(Boolean).join(" · ");
    main.appendChild(el("header", { className: "item-head" }, [
      el("h1", { className: "item-title", textContent: info.short || name }),
      info.name !== info.short ? el("div", { className: "item-full", textContent: info.name }) : null,
      meta ? el("p", { className: "item-meta", textContent: meta }) : null,
      !info.found ? el("p", { className: "quiet-note", textContent: "This name is not in the declaration index for this proof." + (gh ? " The source link is inferred from its name." : "") }) : null,
      (!state.manifest.source_only && !state.manifest.demo_mode && info.found && !info.isModule && info.live !== 0)
        ? el("p", { className: "item-axioms", textContent: "Axioms: at most propext, Classical.choice and Quot.sound, with no sorryAx, inherited from the kernel check of the main theorems." })
        : null
    ]));

    if (!info.isModule) {
      const nb = info.neighbors || {};
      main.appendChild(el("section", { className: "nb-strip", "aria-label": "Connections" }, [
        neighborList("Used by", "↑", nb.used_by),
        el("div", { className: "nb-col nb-self" }, [
          el("div", { className: "nb-hd", textContent: "This declaration" }),
          el("div", { className: "nb-self-name", textContent: info.short }),
          info.spine && info.spine.note ? el("p", { className: "nb-empty", textContent: info.spine.note }) : null
        ]),
        neighborList("Depends on", "↓", nb.depends_on)
      ]));
    }

    const views = [["summary", "Summary"]];
    if (info.circuit) views.push(["diagram", "Diagram"]);
    if (gh) views.push(["source", "Lean Source"]);
    if (!info.isModule && ((state.manifest.assets || {}).embedding_2d || (state.manifest.assets || {}).atlas)) views.push(["twins", "Compare / Twins"]);
    views.push(["docs", "Dossiers"]);
    if (!views.some(([k]) => k === state.item.view)) state.item.view = "summary";
    const body = el("div", { className: "item-body", id: "itemBody" });
    main.appendChild(el("div", { className: "toolbar-row item-tabs" }, [
      el("div", { className: "seg", role: "tablist" }, views.map(([k, lbl]) => el("button", {
        type: "button", role: "tab", "aria-selected": state.item.view === k ? "true" : "false", className: state.item.view === k ? "active" : "", textContent: lbl,
        onclick: () => { state.item.view = k; renderItemView(name); }
      }))),
      el("div", { className: "spacer" }),
      gh && state.item.view !== "source" ? el("a", { className: "btn sm", href: gh, target: "_blank", rel: "noopener noreferrer", textContent: "View proof file ↗" }) : null
    ]));
    main.appendChild(body);
    await renderItemBody(body, info, gh);
  }

  async function renderItemBody(body, info, gh) {
    const m = state.manifest || {};
    const view = state.item.view;
    if (view === "summary") {
      const kv = el("div", { className: "cir-ins-kv item-kv" });
      const add = (k, v) => { if (v == null || v === "") return; kv.appendChild(el("div", { className: "k", textContent: k })); kv.appendChild(el("div", { className: "v", textContent: String(v) })); };
      add("Full name", info.name);
      add("Kind", info.kind);
      add(info.isModule ? "File" : "Module", info.isModule ? String(info.mod).replace(/\./g, "/") + ".lean" : info.mod);
      add("Line", info.line);
      add("Exclusive subtree", info.dom ? fmtInt(info.dom) : "");
      if (info.spine) {
        add("Role", info.spine.role);
        add("Reached through", info.spine.idom);
      }
      add("Declarations", info.decls != null ? fmtInt(info.decls) : "");
      body.appendChild(kv);
      const acts = el("div", { className: "cir-ins-acts" });
      if (info.circuit) acts.appendChild(el("a", { className: "btn sm primary", href: "#circuit/" + info.circuit.mode + "/" + encodeURIComponent(info.circuit.short || info.circuit.name), textContent: "Open full diagram ›" }));
      if (info.bpId) acts.appendChild(el("a", { className: "btn sm", href: "#blueprints/" + encodeURIComponent(info.bpId), textContent: "Blueprint ›" }));
      acts.appendChild(el("a", { className: "btn sm", href: "#search/" + encodeURIComponent(info.short), textContent: "Search similar names ›" }));
      body.appendChild(acts);
      const docs = docsMentioning(info.short, false);
      if (docs.length) {
        body.appendChild(el("div", { className: "map-sub", textContent: "Mentioned in" }));
        body.appendChild(el("ul", { className: "item-docs" }, docs.slice(0, 8).map((d) => el("li", null, [el("a", { href: d.route, textContent: d.title + " ›" })]))));
      }
      return;
    }

    if (view === "diagram" && info.circuit) {
      const box = el("div", { className: "lens-box item-diagram" }, [el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading diagram…" })])]);
      body.appendChild(box);
      body.appendChild(el("div", { className: "cir-ins-acts" }, [el("a", { className: "btn sm primary", href: "#circuit/" + info.circuit.mode + "/" + encodeURIComponent(info.circuit.short || info.circuit.name), textContent: "Open full diagram ›" })]));
      try {
        const data = await fetchJson(info.circuit.path);
        const svgText = state.theme === "light" ? (data.svg_light || data.svg || data.svg_dark) : (data.svg_dark || data.svg || data.svg_light);
        mountSafeSvg(box, svgText || "");
      } catch (err) {
        clearEl(box);
        box.appendChild(el("p", { className: "cir-ins-note", textContent: "Could not load the diagram: " + String(err.message || err) }));
      }
      return;
    }

    if (view === "source" && gh) {
      let extra = [];
      if (info.circuit) {
        try {
          const data = await fetchJson(info.circuit.path);
          const p = data.payload || {};
          extra = (p.nodes || []).concat(p.binders || []).map((n) => n.full_name).filter(Boolean);
        } catch (_) { /* optional */ }
      }
      const host = el("div", { className: "item-source" });
      body.appendChild(host);
      await renderDockedSource(host, { url: gh, title: info.name, line: info.isModule ? null : info.line, links: buildKnownLinks(info, extra) });
      return;
    }

    if (view === "twins") {
      const host = el("div", { className: "item-twins" }, [el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Looking for relatives…" })])]);
      body.appendChild(host);
      const a = m.assets || {};
      const [emb, atlas] = await Promise.all([
        a.embedding_2d ? fetchJson(a.embedding_2d).catch(() => null) : null,
        a.atlas ? fetchJson(a.atlas).catch(() => null) : null
      ]);
      clearEl(host);
      const mySpec = { url: gh || "", title: info.name, line: info.line, label: "A" };
      let any = false;
      if (emb && emb.layers && emb.layers.landmarks) {
        const pts = map2dPoints(emb.layers.landmarks, "knn");
        const me = pts.find((p) => p.name === info.name);
        if (me && me.nn.length) {
          any = true;
          host.appendChild(el("div", { className: "map-sub", textContent: "Closest in vocabulary (2D map neighbors)" }));
          if (me.terms.length) host.appendChild(el("p", { className: "map-terms", textContent: "Its statement draws on: " + me.terms.slice(0, 6).join(" · ") }));
          host.appendChild(el("div", { className: "tray-list" }, me.nn.slice(0, 5).map((j) => {
            const q = pts[j];
            if (!q) return null;
            const qUrl = q.mod ? buildGithubUrl(q.mod, q.line) : "";
            return el("div", { className: "tray-row" }, [
              el("div", { className: "tray-main" }, [
                el("a", { className: "tray-name", href: "#item/" + encodeURIComponent(q.name), title: q.name, textContent: q.short }),
                el("span", { className: "tray-meta", textContent: [q.kind, q.dir, q.dom ? fmtInt(q.dom) + " in subtree" : null].filter(Boolean).join(" · ") })
              ]),
              el("div", { className: "cir-ins-acts" }, [
                el("a", { className: "btn sm", href: "#item/" + encodeURIComponent(q.name), textContent: "Inspect ›" }),
                (isLeanBlob(gh) || isLeanBlob(qUrl)) ? el("button", { type: "button", className: "btn sm", textContent: "Compare side-by-side", onclick: () => openSourceCompare(mySpec, { url: qUrl || "", title: q.name, line: q.line, label: "B" }) }) : null
              ])
            ]);
          })));
        }
      }
      const al = atlas && atlas.alien_twins;
      if (al) {
        const pairs = [].concat(al.top_alien_pairs || [], al.top_alien_pairs_intra || [], al.top_alien_pairs_cross_repo || []);
        const seen = new Set();
        const mine = pairs.filter((p) => {
          const k = (p.thm_a && p.thm_a.name) + "|" + (p.thm_b && p.thm_b.name);
          if (seen.has(k)) return false;
          seen.add(k);
          return (p.thm_a && p.thm_a.name === info.name) || (p.thm_b && p.thm_b.name === info.name);
        });
        if (mine.length) {
          any = true;
          host.appendChild(el("div", { className: "map-sub", textContent: "Same statement, different proof" }));
          for (const p of mine) {
            const other = p.thm_a.name === info.name ? p.thm_b : p.thm_a;
            const os = atlasTwinSourceSpec(other, "B");
            host.appendChild(el("div", { className: "tray-row" }, [
              el("div", { className: "tray-main" }, [
                el("a", { className: "tray-name", href: "#item/" + encodeURIComponent(other.name), title: other.name, textContent: shortName(other.name) }),
                el("span", { className: "tray-meta", textContent: "overlap J = " + Number(p.jaccard || 0).toFixed(3) + " · " + (other.origin === "project" ? "this project" : other.origin) })
              ]),
              el("div", { className: "cir-ins-acts" }, [
                el("button", { type: "button", className: "btn sm", textContent: "Compare side-by-side", onclick: () => openSourceCompare(mySpec, os) })
              ])
            ]));
          }
        }
      }
      if (!any) host.appendChild(el("p", { className: "cir-ins-note", textContent: "No close relatives were found for this declaration in the precomputed data." }));
      return;
    }

    if (view === "docs") {
      const host = el("div", { className: "item-docs-view" });
      body.appendChild(host);
      const quick = docsMentioning(info.short, false);
      host.appendChild(el("p", { className: "cir-ins-note", textContent: quick.length ? "Titles and summaries that mention " + info.short + ":" : "No title or summary mentions " + info.short + "." }));
      if (quick.length) host.appendChild(el("ul", { className: "item-docs" }, quick.map((d) => el("li", null, [el("a", { href: d.route, textContent: d.title + " ›" })]))));
      const all = docsMentioning("", true);
      if (all.length) {
        const out = el("div", { className: "item-docs-full" });
        const btn = el("button", {
          type: "button", className: "btn sm", textContent: "Search the full text of " + fmtInt(all.length) + " documents",
          onclick: async () => {
            btn.disabled = true;
            clearEl(out);
            const status = el("p", { className: "cir-ins-note", textContent: "Searching…" });
            out.appendChild(status);
            const rx = new RegExp("(^|[^A-Za-z0-9_'.])" + info.short.replace(/[.*+?^${}()|[\]\\]/g, "\\$&") + "(?![A-Za-z0-9_'])");
            const hits = [];
            let done = 0;
            for (const d of all) {
              try {
                const txt = await fetchText(d.path);
                const n = (txt.match(new RegExp(rx.source, "g")) || []).length;
                if (n) hits.push(Object.assign({ n }, d));
              } catch (_) { /* skip */ }
              done++;
              status.textContent = "Searched " + done + " of " + all.length + "…";
            }
            hits.sort((x, y) => y.n - x.n);
            status.textContent = hits.length ? "Found in " + hits.length + " documents:" : "Not mentioned in any document.";
            if (hits.length) out.appendChild(el("ul", { className: "item-docs" }, hits.map((d) => el("li", null, [el("a", { href: d.route, textContent: d.title + " ›" }), el("span", { className: "nb-rel", textContent: d.n + (d.n === 1 ? " mention" : " mentions") })]))));
          }
        });
        host.appendChild(btn);
        host.appendChild(out);
      }
    }
  }

  function docsMentioning(word, all) {
    const m = state.manifest || {};
    const out = [];
    const w = String(word || "").toLowerCase();
    const take = (d, route) => {
      if (all || (w && ((d.title || "") + " " + (d.summary || "")).toLowerCase().includes(w))) out.push({ title: plainTextFromTex(d.title || d.slug), route, path: d.path });
    };
    for (const f of (m.findings || [])) take(f, "#findings/" + encodeURIComponent(f.slug));
    for (const d of (m.dossiers || [])) take(d, "#dossiers/" + encodeURIComponent(d.slug));
    for (const d of (m.research || [])) take(d, "#dossiers/research/" + encodeURIComponent(d.slug));
    return out;
  }

  function renderExperimentsView() {
    const main = $("#appMain");
    clearEl(main);
    main.appendChild(el("div", { className: "empty-card" }, [
      el("h3", { textContent: "This page has moved" }),
      el("p", { textContent: "The dependency views now live under Edge Map, and other formalizations are listed under Proofs." }),
      el("div", { className: "cir-ins-acts" }, [
        el("a", { className: "btn sm", href: "#atlas", textContent: "Edge Map ›" }),
        state.registry ? el("a", { className: "btn sm", href: "#projects", textContent: "Proofs ›" }) : null
      ])
    ]));
  }

  // ==========================================================================
  // CLUSTERS for source-only projects (flirt_tier1.json)
  // ==========================================================================
  function renderTier1Body(doc) {
    const main = $("#appMain");
    clearEl(main);
    const ms = doc.misfile_scoring || {};
    const mi = doc.mathlib_import_stats || {};
    const bp = doc.boilerplate_stats || {};
    const dup = Number((bp.alpha_body_clone || {}).redundant_modules || 0) + Number((bp.sigset_clone || {}).redundant_modules || 0);
    main.appendChild(el("header", { className: "page-head" }, [
      el("h1", { textContent: "Clusters" }),
      el("p", { className: "page-lede", textContent: "Files whose namespace, imports or vocabulary suggest they belong in a different folder, and modules that repeat each other. This is a source-only scan, so the signals come from names and imports rather than proofs." })
    ]));
    main.appendChild(el("section", { className: "kpi-strip" }, [
      { val: fmtInt(doc.file_count), label: "Files", sub: doc.total_lines_wc ? fmtInt(doc.total_lines_wc) + " lines" : "" },
      { val: fmtInt(ms.alertable_misfiles_total || 0), label: "Possibly misfiled", sub: ms.alertable_pct_of_corpus != null ? ms.alertable_pct_of_corpus + "% of files" : "" },
      { val: fmtInt(mi.modules_importing_whole_mathlib || 0), label: "Import all of Mathlib", sub: "rather than specific modules" },
      { val: fmtInt(dup), label: "Near-duplicate modules", sub: "identical bodies or statement sets" }
    ].map((k) => el("div", { className: "kpi-card" }, [el("div", { className: "kpi-val", textContent: k.val }), el("div", { className: "kpi-label", textContent: k.label }), k.sub ? el("div", { className: "kpi-sub", textContent: k.sub }) : null]))));
    const rows = (doc.top_misfiles || []).slice(0, 60);
    if (rows.length) {
      main.appendChild(el("div", { className: "section-hdr" }, [el("h2", { textContent: "Possibly misfiled" })]));
      main.appendChild(el("div", { className: "table-wrap" }, [el("table", { className: "data-table" }, [
        el("thead", null, [el("tr", null, [el("th", { textContent: "File" }), el("th", { textContent: "Namespace vs folder" }), el("th", { textContent: "Topic: observed vs expected" }), el("th", { textContent: "Signal" })])]),
        el("tbody", null, rows.map((r) => el("tr", null, [
          el("td", null, [el("code", { textContent: r.module || r.file_path || "—" }), r.file_path ? el("div", { className: "bp-anchor" }, [makeSourceLink(r.file_path, null, r.file_path, r.module)]) : null]),
          el("td", null, [el("code", { textContent: r.declared_ns || "—" }), el("div", { className: "cir-ins-note mono", textContent: r.folder_ns || "" })]),
          el("td", { textContent: String(r.domain_observed || "—").replace(/_/g, " ") + " vs " + String(r.domain_expected || "—").replace(/_/g, " ") }),
          el("td", { textContent: String(r.band || "").replace(/_/g, " ") })
        ])))
      ])]));
    }
    const BP_LABEL = { alpha_body_clone: "Identical proof bodies", sigset_clone: "Identical statement sets", import_shim: "Import-only shims", statement_wrapper: "Statement wrappers" };
    const bpRows = Object.keys(BP_LABEL).filter((k) => bp[k]);
    if (bpRows.length) {
      main.appendChild(el("div", { className: "section-hdr" }, [el("h2", { textContent: "Repetition" })]));
      main.appendChild(el("div", { className: "table-wrap" }, [el("table", { className: "data-table" }, [
        el("thead", null, [el("tr", null, [el("th", { textContent: "Pattern" }), el("th", { className: "num", textContent: "Groups" }), el("th", { className: "num", textContent: "Modules" }), el("th", { className: "num", textContent: "Redundant" }), el("th", { className: "num", textContent: "Largest group" })])]),
        el("tbody", null, bpRows.map((k) => el("tr", null, [
          el("td", { textContent: BP_LABEL[k] }), el("td", { className: "num", textContent: fmtInt(bp[k].clusters) }), el("td", { className: "num", textContent: fmtInt(bp[k].modules) }),
          el("td", { className: "num", textContent: fmtInt(bp[k].redundant_modules) }), el("td", { className: "num", textContent: fmtInt(bp[k].largest_cluster) })
        ])))
      ])]));
    }
  }

  // ==========================================================================
  // VIEW 1: OVERVIEW
  // ==========================================================================
  // Split text so that names of structures/theorems with their own diagram
  // become links to those diagrams (e.g. "OpenLiteratureStatements").
  function linkCircuitNames(text) {
    const circuits = (state.manifest && state.manifest.circuits) || {};
    const names = [];
    for (const b of (circuits.bundles || [])) if ((b.short || "").length > 6) names.push(["bundle", b.short]);
    for (const t of (circuits.theorems || [])) if ((t.short || "").length > 6) names.push(["theorem", t.short]);
    if (!names.length) return [String(text)];
    const byName = new Map(names.map(([mode, nm]) => [nm, mode]));
    const rx = new RegExp("\\b(" + names.map(([, nm]) => nm.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).sort((a, b) => b.length - a.length).join("|") + ")\\b", "g");
    const out = [];
    let last = 0;
    let mm;
    const src = String(text);
    while ((mm = rx.exec(src))) {
      if (mm.index > last) out.push(src.slice(last, mm.index));
      const nm = mm[1];
      out.push(el("a", { className: "inline-diagram", href: "#circuit/" + byName.get(nm) + "/" + encodeURIComponent(nm), title: "Open the diagram for " + nm, textContent: nm, onclick: (ev) => ev.stopPropagation() }));
      last = rx.lastIndex;
    }
    if (last < src.length) out.push(src.slice(last));
    return out;
  }

  function overviewLenses() {
    const m = state.manifest || {};
    const a = m.assets || {};
    const out = [["spine", "Spine"]];
    if (m.circuits && m.circuits.macro) out.push(["diagram", "Diagram"]);
    if (a.atlas || a.module_matrix) out.push(["edges", "Edge Map"]);
    if (a.embedding_2d) out.push(["map", "2D Map"]);
    return out;
  }

  async function renderOverviewLens(host, domTree) {
    const m = state.manifest || {};
    const a = m.assets || {};
    const lens = state.overviewLens;
    clearEl(host);
    if (lens === "spine") {
      host.appendChild(el("p", { className: "section-lede", textContent: m.source_only
        ? "Each bar counts the modules that can only be reached through that one (its dominator subtree in the import graph). Click a row to inspect it."
        : "Each bar counts the declarations that can only be reached through that part (its dominator subtree). Click a row to inspect it." }));
      host.appendChild(domTree);
      return;
    }
    const lede = el("p", { className: "section-lede" });
    const box = el("div", { className: "lens-box" }, [el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading…" })])]);
    const more = el("div", { className: "cir-ins-acts" });
    host.appendChild(lede);
    host.appendChild(box);
    host.appendChild(more);
    try {
      if (lens === "diagram") {
        lede.textContent = "The repository map: the main theorems at the top and the parts they rest on below.";
        const data = await fetchJson(m.circuits.macro);
        if (state.overviewLens !== lens || !box.isConnected) return;
        const svgText = state.theme === "light" ? (data.svg_light || data.svg || data.svg_dark) : (data.svg_dark || data.svg || data.svg_light);
        mountSafeSvg(box, svgText || "");
        more.appendChild(el("a", { className: "btn sm", href: "#circuit/macro", textContent: "Open the full diagram ›" }));
      } else if (lens === "edges") {
        const canvas = el("canvas", { className: "atlas-canvas lens-canvas", "aria-label": "Edge map" });
        if (a.atlas) {
          lede.textContent = "Every dependency edge, ordered by the dominator tree. Brighter cells hold more edges; cyan cells are mostly statement edges and amber cells mostly proof edges.";
          const doc = await fetchJson(a.atlas);
          if (state.overviewLens !== lens || !box.isConnected) return;
          clearEl(box);
          box.appendChild(canvas);
          atlasDrawHicCanvas(canvas, doc.hic_matrix || {}, "ratio");
        } else {
          lede.textContent = "Imports between modules, ordered so that each folder sits in one block.";
          const mm = await fetchJson(a.module_matrix);
          if (state.overviewLens !== lens || !box.isConnected) return;
          clearEl(box);
          box.appendChild(canvas);
          drawModuleMatrix(canvas, mm, null);
        }
        more.appendChild(el("a", { className: "btn sm", href: "#atlas", textContent: "Open the Edge Map ›" }));
      } else if (lens === "map") {
        lede.textContent = "Declarations placed by the Mathlib vocabulary their statements use. Click a dot to see its neighbors.";
        clearEl(box);
        box.classList.add("lens-map");
        await mountMap2d(box, { compact: true });
        more.appendChild(el("a", { className: "btn sm", href: "#atlas/map", textContent: "Open the 2D Map ›" }));
      }
    } catch (err) {
      clearEl(box);
      box.appendChild(el("p", { className: "cir-ins-note", textContent: "Could not load this view: " + String(err.message || err) }));
    }
  }

  function renderOverview() {
    const main = $("#appMain");
    clearEl(main);
    const m = state.manifest || {};
    const st = m.stats || {};

    // Hero: one title, a two-sentence description computed from the manifest,
    // a quiet scope note, and three actions.
    const repo = m.repo_name || "this repository";
    const nFind = (m.findings || []).length;
    const nDos = (m.dossiers || []).length;
    const nBp = (m.blueprints || []).length;
    const countPhrase = (n, one, many) => fmtInt(n) + " " + (n === 1 ? one : many);
    const docParts = [];
    if (nFind) docParts.push(countPhrase(nFind, "finding", "findings"));
    if (nDos) docParts.push(countPhrase(nDos, "dossier", "dossiers"));
    if (nBp) docParts.push(countPhrase(nBp, "blueprint", "blueprints"));
    const joinList = (xs) => xs.length <= 1 ? (xs[0] || "") : xs.slice(0, -1).join(", ") + " and " + xs[xs.length - 1];
    const liveTxt = st.live_decls ? fmtInt(st.live_decls) + " reachable declarations" : "declarations";
    const sentence1 = "This site maps how the " + liveTxt + " in " + repo + " depend on one another, which parts carry the weight of the proof, and which hypotheses are actually used.";
    const sentence2 = docParts.length
      ? "It collects " + joinList(docParts) + ", and every diagram and table links to the exact line of Lean source at a pinned commit."
      : "Every diagram and table links to the exact line of Lean source at a pinned commit.";

    const heroActions = el("div", { className: "hero-actions" }, [
      (m.circuits && m.circuits.macro) ? el("a", { className: "btn primary", href: "#circuit", textContent: "Explore diagrams ›" }) : null,
      nFind ? el("a", { className: "btn", href: "#findings", textContent: "Read findings ›" }) : null,
      el("a", { className: "btn", href: "#search", textContent: "Search declarations ›" }),
      state.registry && projectList().length > 1 ? el("a", { className: "btn quiet", href: "#projects", textContent: "All " + projectList().length + " proofs ›" }) : null
    ]);

    const scopeNote = m.scope_note || (m.repo_name === "riemann-hypothesis"
      ? "Scope: the 5 headline theorems concern ζ(s) and Dirichlet L-functions over ℚ only, not Dedekind or Hecke L-functions; the author folder named DedekindLFunctions is a misnomer."
      : "");
    main.appendChild(el("section", { className: "hero" }, [
      el("h1", { textContent: m.demo_mode ? "How " + repo + " fits together" : "How the " + repo + " proof fits together" }),
      el("p", { className: "hero-sub", textContent: sentence1 + " " + sentence2 }),
      scopeNote ? el("p", { className: "hero-scope", textContent: plainTextFromTex(scopeNote) }) : null,
      m.source_only
        ? el("p", { className: "hero-note", role: "note", textContent: "Note: this is a source-only scan. Nothing here was checked by Lean's kernel, and none of it is independent mathematical peer review." })
        : el("p", { className: "hero-note", role: "note" }, [
          "Note: passing Lean's kernel confirms the logic under the standard axioms (",
          el("code", { textContent: "propext" }), ", ",
          el("code", { textContent: "Classical.choice" }), ", ",
          el("code", { textContent: "Quot.sound" }),
          "); it is not independent mathematical peer review."
        ]),
      heroActions
    ]));

    // Key numbers
    const nCir = (m.circuits && ((m.circuits.bundles || []).length + (m.circuits.theorems || []).length + (m.circuits.macro ? 1 : 0))) || 0;
    const kpis = [
      { label: "Reachable declarations", val: fmtInt(st.live_decls), sub: st.total_decls ? "of " + fmtInt(st.total_decls) + " in total" : "" },
      { label: "Unreachable", val: fmtInt(st.dead_decls), sub: "not reached from the main theorems" },
      { label: "Dependency edges", val: fmtInt(st.edges), sub: fmtInt(st.total_files) + " files · " + fmtInt(st.total_lines) + " lines" },
      { label: "Diagrams", val: fmtInt(nCir), sub: ((m.circuits && (m.circuits.bundles || []).length) || 0) + " structures · " + ((m.circuits && (m.circuits.theorems || []).length) || 0) + " theorems" }
    ];
    main.appendChild(el("section", { className: "kpi-strip", "aria-label": "Key numbers" }, kpis.map((k) =>
      el("div", { className: "kpi-card" }, [
        el("div", { className: "kpi-val", textContent: k.val }),
        el("div", { className: "kpi-label", textContent: k.label }),
        k.sub ? el("div", { className: "kpi-sub", textContent: k.sub }) : null
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
        const declName = p.decl || "";
        const circuitHit = (p.circuit_mode && target)
          ? (findCircuitEntry(p.circuit_mode, target) || findAnyCircuitForSymbol(target))
          : (target ? findAnyCircuitForSymbol(target) : null);
        const rowHref = declName ? "#item/" + encodeURIComponent(declName)
          : (circuitHit ? "#circuit/" + circuitHit.mode + "/" + encodeURIComponent(circuitHit.short || circuitHit.name) : "");
        const desc = p.note || p.description || "";
        const fillCls = idx === 0 ? "emerald" : (String(p.role || p.label || p.name || "").toLowerCase().includes("diamond") ? "amber" : (depth >= 2 ? "teal" : ""));
        const row = el("div", {
          className: "dom-row" + (rowHref ? " clickable" : ""),
          role: rowHref ? "link" : null,
          tabindex: rowHref ? "0" : null,
          title: rowHref ? (declName ? "Inspect " + declName : "Open the diagram for " + circuitHit.name) : (desc || p.label || p.name || ""),
          onclick: rowHref ? () => navigate(rowHref) : null,
          onkeydown: rowHref ? (ev) => { if (ev.key === "Enter") navigate(rowHref); } : null
        }, [
          el("div", { className: "dom-name" }, [
            depth > 0 ? el("span", { className: "indent", textContent: "  ".repeat(Math.min(depth, 4)) + "└─" }) : null,
            el("div", { style: { minWidth: "0" } }, [
              el("div", { className: "lbl", textContent: p.label || p.name || target || "node" }),
              desc ? el("div", { className: "sub-note" }, linkCircuitNames(desc)) : null
            ])
          ]),
          el("div", { className: "dom-bar-track" }, [
            el("div", { className: "dom-bar-fill " + fillCls, style: { width: pct.toFixed(1) + "%" } })
          ]),
          el("div", { className: "dom-count", textContent: fmtInt(cnt) + (p.pct_live != null ? " (" + Number(p.pct_live).toFixed(0) + "%)" : "") }),
          el("span", { className: "nav-glyph", "aria-hidden": "true", textContent: rowHref ? "›" : "" })
        ]);
        domTree.appendChild(row);
      });
    } else {
      domTree.appendChild(el("div", { className: "empty-card" }, [
        el("p", { textContent: "No breakdown of the main parts is available. The repository map in Diagrams shows the roots and their clusters." })
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
          el("span", { className: "sc-tag", textContent: tag + " ›" })
        ]),
        el("div", { className: "sc-sub", textContent: desc })
      ]));
    };

    for (const sc of SHOWCASE_ORDER) {
      const hit = findCircuitEntry(sc.mode, sc.target);
      if (hit) {
        pushShowcase(sc.mode, hit.short || hit.name || "", sc.label, sc.desc, sc.tag);
      }
    }
    // Fill up with available structures/theorems on generic/demo repos
    if (addedKeys.size < 6 && m.circuits) {
      for (const b of (m.circuits.bundles || []).slice(0, 4)) {
        pushShowcase("bundle", b.short || b.name, b.short || shortName(b.name), (b.fields || 0) + " fields · used by " + (b.consumers || 0), "Structure");
      }
      for (const t of (m.circuits.theorems || []).slice(0, 4)) {
        pushShowcase("theorem", t.short || t.name, t.short || shortName(t.name), (t.steps || 0) + " proof steps", "Theorem");
      }
    }

    const lenses = overviewLenses();
    if (!lenses.some(([k]) => k === state.overviewLens)) state.overviewLens = "spine";
    const lensBody = el("div", { className: "lens-body", id: "lensBody" });
    const lensSeg = el("div", { className: "seg", role: "tablist", "aria-label": "View" }, lenses.map(([k, lbl]) => el("button", {
      type: "button", role: "tab", "aria-selected": state.overviewLens === k ? "true" : "false", className: state.overviewLens === k ? "active" : "", textContent: lbl,
      onclick: () => {
        state.overviewLens = k;
        $$("button", lensSeg).forEach((b) => { const on = b.textContent === lbl; b.classList.toggle("active", on); b.setAttribute("aria-selected", on ? "true" : "false"); });
        renderOverviewLens(lensBody, domTree);
      }
    })));
    main.appendChild(el("section", { className: "overview-grid" }, [
      el("div", { className: "panel lens-panel" }, [
        el("div", { className: "section-hdr lens-hd", style: { marginTop: "0" } }, [
          el("h2", { textContent: "At a glance" }),
          lenses.length > 1 ? lensSeg : null
        ]),
        lensBody
      ]),
      el("div", { className: "panel" }, [
        el("div", { className: "section-hdr", style: { marginTop: "0" } }, [
          el("h2", { textContent: "Places to start" })
        ]),
        el("p", { className: "section-lede", textContent: "Selected diagrams. Drag to pan and scroll to zoom once inside." }),
        showcaseGrid
      ])
    ]));
    renderOverviewLens(lensBody, domTree);

    // Findings
    const findings = Array.isArray(m.findings) ? m.findings : [];
    if (findings.length) {
      main.appendChild(el("div", { className: "section-hdr" }, [
        el("h2", { textContent: "Findings" }),
        el("a", { className: "sub", href: "#findings", textContent: "All findings ›" })
      ]));
      main.appendChild(el("section", { className: "findings-cards" }, findings.map((f) =>
        el("button", {
          type: "button",
          className: "finding-card",
          onclick: () => navigate("#findings/" + encodeURIComponent(f.slug))
        }, [
          el("div", { className: "fc-title" }, [renderTextWithTex(f.title || f.slug), el("span", { className: "nav-glyph", "aria-hidden": "true", textContent: " ›" })]),
          f.summary ? el("div", { className: "fc-sum", textContent: plainTextFromTex(f.summary) }) : null
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
    const payload = (state.circuit.data && state.circuit.data.payload) || {};
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

    const cdata = state.circuit.data;
    const payload = (cdata && cdata.payload) || null;
    if (!payload) {
      box.appendChild(el("div", { className: "cir-ins-hd" }, [el("span", { textContent: "Details" })]));
      box.appendChild(el("p", { className: "cir-ins-note", textContent: "Click a node or a field to see its details and source." }));
      return;
    }

    const meta = payload.meta || {};
    const stats = payload.stats || {};
    const targetInfo = meta.target_info || {};
    const modeKey = String(payload.mode || state.circuit.mode);

    box.appendChild(el("div", { className: "cir-ins-hd" }, [
      el("span", { textContent: isHover ? "Preview" : (item ? "Selected" : "Summary") }),
      el("span", { className: "cir-ins-mode", textContent: MODE_LABEL[modeKey] || modeKey })
    ]));

    if (!item) {
      box.appendChild(el("div", { className: "cir-ins-title", textContent: payload.target || payload.title || "Repository map" }));
      const topAnchor = (payload.pins && payload.pins.anchor) || meta.anchor || targetInfo.anchor || "";
      if (topAnchor) {
        box.appendChild(el("div", { className: "cir-ins-note" }, ["Source: ", makeSourceLink(topAnchor, null, null, payload.target || payload.title)]));
      }

      const kv = el("div", { className: "cir-ins-kv" });
      const addKv = (k, v) => {
        if (v == null || v === "") return;
        kv.appendChild(el("div", { className: "k", textContent: k }));
        kv.appendChild(el("div", { className: "v", textContent: String(v) }));
      };
      addKv("Nodes / links", fmtInt(stats.node_count) + " / " + fmtInt(stats.wire_count));
      if (payload.mode === "macro") {
        addKv("Reachable", fmtInt(stats.live_decls) + " (" + fmtInt(stats.dead_decls) + " unreachable)");
        if (stats.shared_diamond_decls != null) addKv("Shared core", fmtInt(stats.shared_diamond_decls) + ((state.manifest || {}).source_only ? " modules" : " declarations"));
        if (stats.motif_clusters_count != null) addKv("Repeated shapes", fmtInt(stats.motif_clusters_count));
        if (stats.excluded_trivial_shells) addKv("Hidden", fmtInt(stats.excluded_prop_shells) + " Prop · " + fmtInt(stats.excluded_trivial_shells) + " trivial wrappers");
      } else if (payload.mode === "bundle") {
        addKv("Fields", fmtInt(stats.total_fields) + " (" + fmtInt(stats.projected_fields) + " used, " + fmtInt(stats.unread_fields) + " unused)");
        addKv("Conditional", fmtInt(stats.conditional_prop_fields) + " · trivially True: " + fmtInt(stats.literal_true_fields));
        addKv("Built by", fmtInt(stats.producers_total));
        addKv("Used by", fmtInt(stats.consumers_total) + " (" + fmtInt(stats.consumers_dropped_input) + " ignore it)");
      } else if (payload.mode === "theorem") {
        addKv("Kind", stats.decl_kind || "—");
        addKv("Hypotheses", fmtInt(stats.binders_used) + " used · " + fmtInt(stats.binders_dropped) + " unused");
        addKv("Proof steps", fmtInt(stats.steps_count));
        addKv("Used by / uses", fmtInt(stats.fan_in) + " / " + fmtInt(stats.fan_out));
        if (meta.sighash) addKv("Signature hash", meta.sighash);
      }
      box.appendChild(kv);
      box.appendChild(el("p", { className: "cir-ins-note", textContent: "Click a node to open its own diagram where there is one, or to see its source. Drag to pan; scroll to zoom." }));
      return;
    }

    // Specific Node or Pin Inspector
    const title = item.full_name || item.name || item.label || item.id || "";
    box.appendChild(el("div", { className: "cir-ins-title", textContent: title }));

    const pillRow = el("div", { className: "cir-ins-acts" });
    if (item.kind) pillRow.appendChild(el("span", { className: "pill", textContent: item.kind }));
    if (item.status) {
      const sCls = ["dropped", "dangling", "literal_true", "true_slot"].includes(item.status)
        ? "crimson"
        : (["conditional_prop", "default_zero", "le_refl"].includes(item.status) ? "amber" : (item.status === "unread" || item.status === "trivial_shell" ? "slate" : "emerald"));
      pillRow.appendChild(el("span", { className: "pill " + sCls, textContent: String(item.status).replace(/_/g, " ") }));
    }
    if (item.badge) pillRow.appendChild(el("span", { className: "pill", textContent: item.badge }));
    box.appendChild(pillRow);

    const anchor = item.anchor || (item._isPin ? (targetInfo.anchor || "") : (item.line_no && meta.anchor ? meta.anchor.replace(/:\d+$/, ":" + item.line_no) : ""));
    if (anchor) {
      box.appendChild(el("div", { className: "cir-ins-note" }, ["Source: ", makeGithubAnchor(anchor)]));
    }

    // Diagrams available for this node
    const zt = item.zoom_target || null;
    const pivot = (zt && zt.target) || item.full_name || item.name || "";
    const acts = el("div", { className: "cir-ins-acts" });
    const bundleHit = pivot ? findCircuitEntry("bundle", pivot) : null;
    const thmHit = pivot ? findCircuitEntry("theorem", pivot) : null;
    if (bundleHit) {
      acts.appendChild(el("button", {
        type: "button", className: "btn sm primary", textContent: "Open structure diagram ›",
        onclick: () => navigate("#circuit/bundle/" + encodeURIComponent(bundleHit.short || bundleHit.name))
      }));
    }
    if (thmHit) {
      acts.appendChild(el("button", {
        type: "button", className: "btn sm primary", textContent: "Open theorem diagram ›",
        onclick: () => navigate("#circuit/theorem/" + encodeURIComponent(thmHit.short || thmHit.name))
      }));
    }
    if (!item._isPin && (item.full_name || item.name)) {
      acts.appendChild(el("a", { className: "btn sm", href: "#item/" + encodeURIComponent(item.full_name || item.name), textContent: "Inspect ›" }));
    }
    if (anchor) {
      const gh = buildGithubUrl(anchor);
      if (gh) {
        const known = new Map();
        for (const n of ((cdata && cdata.payload && cdata.payload.nodes) || [])) if (n.full_name) { known.set(n.full_name, n.full_name); known.set(shortName(n.full_name), n.full_name); }
        const peek = makeSrcButton(gh, title, { className: "btn sm", text: "Show source inline", links: known });
        if (peek) acts.appendChild(peek);
        acts.appendChild(el("a", { className: "btn sm", href: gh, target: "_blank", rel: "noopener noreferrer", textContent: "View proof file ↗" }));
      }
    }
    if (acts.childNodes.length) box.appendChild(acts);
    else if (pivot && !item._isPin) {
      box.appendChild(el("div", { className: "cir-ins-note", textContent: "There is no separate diagram for this declaration." }));
    }

    const kv = el("div", { className: "cir-ins-kv" });
    const addKv = (k, v) => {
      if (v == null || v === "") return;
      kv.appendChild(el("div", { className: "k", textContent: k }));
      kv.appendChild(el("div", { className: "v", textContent: String(v) }));
    };
    const m = item.metrics || {};
    if (item._isPin) {
      addKv("Status", String(item.status || "").replace(/_/g, " "));
      addKv("Used", item.projected ? "yes" : "no (never read)");
      if (item.fan_in != null) addKv("Read by", fmtInt(item.fan_in));
      if (item.is_conditional_prop) addKv("Form", "conditional, P → Q");
      if (item.is_literal_true) addKv("Form", "trivially True");
      if (item.type) addKv("Type", item.type);
    } else {
      if (item.type) addKv("Type", item.type);
      if (item.line_no != null) addKv("Line", "L" + item.line_no);
      if (m.subtree_size != null) addKv("Exclusive subtree", fmtInt(m.subtree_size) + (m.pct_live != null ? " (" + m.pct_live + "%)" : ""));
      if (m.dom_subtree_size != null && m.subtree_size == null) addKv("Exclusive subtree", fmtInt(m.dom_subtree_size));
      if (m.fan_in != null) addKv("Used by", fmtInt(m.fan_in));
      if (m.fan_out != null) addKv("Uses", fmtInt(m.fan_out));
      if (m.is_trivial_shell) addKv("Wrapper", (m.shell_label || "Prop") + " (hidden)");
      else if (item.k1n_count != null || m.k1n_count != null) addKv("Same-shape copies", "×" + fmtInt(item.k1n_count ?? m.k1n_count));
      if (m.total_fields != null) addKv("Fields", fmtInt(m.projected) + " used · " + fmtInt(m.unread) + " unused");
      if (item.drops_target) addKv("Note", "its input is never used");
      if (item.producer_role) addKv("Role", item.producer_role);
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
    const cdata = state.circuit.data;
    if (!stg || !cdata) return;
    const svgText = state.theme === "light"
      ? (cdata.svg_light || cdata.svg || cdata.svg_dark || "")
      : (cdata.svg_dark || cdata.svg || cdata.svg_light || "");

    const svgEl = mountSafeSvg(stg, svgText);
    if (!svgEl) return;

    const payload = cdata.payload || {};
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
      wrap.appendChild(el("span", { className: "cir-ins-note", textContent: "Choose Structures or Theorems above, or click a highlighted node, to open a more detailed diagram." }));
      return;
    }

    const filtered = list.filter((it) => {
      if (!q) return true;
      return ((it.name || "") + " " + (it.short || "") + " " + (it.badge || "")).toLowerCase().includes(q);
    });
    if (!filtered.length) {
      wrap.appendChild(el("span", { className: "cir-ins-note", textContent: "No diagrams match \"" + q + "\"." }));
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
        el("h3", { textContent: "No diagrams" }),
        el("p", { textContent: "This build does not include any diagrams." })
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
      ["macro", "Repository"],
      ["bundle", "Structures (" + (circuits.bundles || []).length + ")"],
      ["theorem", "Theorems (" + (circuits.theorems || []).length + ")"]
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
        textContent: h.mode === "macro" ? "Repository" : (h.short || shortName(h.target)),
        onclick: () => {
          if (cur) return;
          if (h.mode === "macro") navigate("#circuit/macro");
          else navigate("#circuit/" + h.mode + "/" + encodeURIComponent(h.short || h.target));
        }
      }));
    });

    const nodeHighlightInput = el("input", {
      type: "search", className: "input", id: "cirNodeFilter",
      placeholder: "Highlight nodes…", value: state.circuit.filter,
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
          const sh = state.circuit.data;
          if (!sh) return;
          const txt = state.theme === "light" ? (sh.svg_light || sh.svg || sh.svg_dark) : (sh.svg_dark || sh.svg || sh.svg_light);
          if (!txt) return;
          const blob = new Blob([txt], { type: "image/svg+xml;charset=utf-8" });
          const u = URL.createObjectURL(blob);
          const a = el("a", { href: u, download: "leanre_diagram_" + state.circuit.mode + ".svg" });
          document.body.appendChild(a);
          a.click();
          a.remove();
          URL.revokeObjectURL(u);
        }
      })
    ]);

    // Diagram picker
    const selBar = el("div", { className: "cir-selector-bar" });
    if (state.circuit.mode !== "macro") {
      selBar.appendChild(el("div", { className: "cir-selector-row" }, [
        el("input", {
          type: "search", className: "input", id: "cirChipFilter",
          placeholder: state.circuit.mode === "bundle" ? "Filter structures…" : "Filter theorems…",
          value: state.circuit.selectorFilter,
          style: { width: "220px", padding: "4px 8px", fontSize: "12px" },
          oninput: (ev) => { state.circuit.selectorFilter = ev.target.value; renderCircuitChips(state.circuit.mode); }
        })
      ]));
    }
    selBar.appendChild(el("div", { className: "cir-chips-wrap", id: "cirChipsWrap" }));

    // Legend bar
    const legBar = el("div", { className: "cir-legend-bar" }, [
      ["used", "emerald"], ["unused", "slate"], ["conditional", "amber"], ["trivial or ignored", "crimson"], ["has its own diagram", "cyan"]
    ].map(([lbl, cls]) => el("span", { className: "cir-leg-pill " + cls }, [el("i"), el("span", { textContent: lbl })])));

    // Stage + Inspector
    const body = el("div", { className: "cir-body" }, [
      el("div", { className: "cir-stage-wrap", id: "cirStageWrap" }, [
        el("div", { className: "cir-stage", id: "cirStage" }, [
          el("div", { className: "loading-card", style: { margin: "24px" } }, [
            el("div", { className: "spinner" }),
            el("div", { textContent: "Loading diagram…" })
          ])
        ])
      ]),
      el("aside", { className: "cir-inspector", id: "cirInspector", "aria-label": "Diagram details" })
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
      state.circuit.data = data;
      mountActiveCircuitSvg();
      renderCircuitInspector(null, false);
    } catch (err) {
      const stg = $("#cirStage");
      if (stg) {
        clearEl(stg);
        stg.appendChild(el("div", { className: "empty-card", style: { margin: "24px" } }, [
          el("h3", { textContent: "Could not load this diagram" }),
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
        el("h3", { textContent: "No findings" }),
        el("p", { textContent: "This build has no findings chapters." })
      ]));
      return;
    }

    const active = items.find((f) => f.slug === slugArg) || items.find((f) => f.slug === state.findingSlug) || items[0];
    state.findingSlug = active.slug;

    const sidebar = el("aside", { className: "doc-sidebar", "aria-label": "Findings" }, [
      el("div", { className: "doc-sidebar-top" }, [
        el("strong", { className: "doc-sidebar-title", textContent: "Findings" })
      ]),
      el("div", { className: "doc-list" }, items.map((f) =>
        el("button", {
          type: "button",
          className: "doc-item" + (f.slug === active.slug ? " active" : ""),
          onclick: () => navigate("#findings/" + encodeURIComponent(f.slug))
        }, [
          el("div", { className: "di-title", textContent: plainTextFromTex(f.title || f.slug) })
        ])
      ))
    ]);

    const articleWrap = el("article", { className: "doc-article-wrap" }, [
      el("div", { className: "md-body", id: "findingMdBody" }, [
        el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading…" })])
      ])
    ]);

    main.appendChild(el("div", { className: "doc-layout" }, [sidebar, articleWrap]));

    try {
      const md = await fetchText(active.path);
      const body = $("#findingMdBody");
      if (body) {
        body.innerHTML = renderMarkdownBlockSafe(md, "findings", "findings/" + active.slug + ".md");
        decorateLeanLinks(body);
      }
    } catch (err) {
      const body = $("#findingMdBody");
      if (body) {
        clearEl(body);
        body.appendChild(el("div", { className: "empty-card" }, [
          el("h3", { textContent: "Could not load this finding" }),
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
        el("h3", { textContent: "No dossiers" }),
        el("p", { textContent: "This build has no dossiers or research notes." })
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
      ]) : el("strong", { className: "doc-sidebar-title", textContent: "Dossiers" }),
      el("input", {
        type: "search", className: "input", id: "dossierSearchInput",
        placeholder: state.dossierMode === "research" ? "Filter research notes…" : "Filter dossiers…",
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
          listEl.appendChild(el("div", { className: "doc-cat-hdr", textContent: cat }));
          for (const d of items) {
            listEl.appendChild(el("button", {
              type: "button",
              className: "doc-item" + (active && d.slug === active.slug ? " active" : ""),
              onclick: () => navigate("#dossiers/" + encodeURIComponent(d.slug))
            }, [
              el("div", { className: "di-title", textContent: plainTextFromTex(d.title || d.slug) })
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
            el("div", { className: "di-title", textContent: plainTextFromTex(d.title || d.slug) })
          ]));
        }
      }
    };

    const articleWrap = el("article", { className: "doc-article-wrap" });
    if (active) {
      if (state.dossierMode === "analysis") {
        articleWrap.appendChild(el("div", { className: "doc-article-meta" }, [
          el("span", { textContent: inferDossierCategory(active) })
        ]));
      }
      articleWrap.appendChild(el("div", { className: "md-body", id: "dossierMdBody" }, [
        el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading…" })])
      ]));
    } else {
      articleWrap.appendChild(el("div", { className: "empty-card" }, [el("p", { textContent: "Choose a dossier from the list." })]));
    }

    main.appendChild(el("div", { className: "doc-layout" }, [
      el("aside", { className: "doc-sidebar", "aria-label": "Dossiers" }, [sidebarTop, listEl]),
      articleWrap
    ]));
    populateDossierList();

    if (active) {
      try {
        const md = await fetchText(active.path);
        const body = $("#dossierMdBody");
        if (body) {
          body.innerHTML = renderMarkdownBlockSafe(md, state.dossierMode === "research" ? "research" : "analysis", (state.dossierMode === "research" ? "research/" : "analysis/") + active.slug + ".md");
          decorateLeanLinks(body);
        }
      } catch (err) {
        const body = $("#dossierMdBody");
        if (body) {
          clearEl(body);
          body.appendChild(el("div", { className: "empty-card" }, [
            el("h3", { textContent: "Could not load this dossier" }),
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
        el("h3", { textContent: "No blueprints" }),
        el("p", { textContent: "This build does not include any blueprints." })
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
          el("div", { className: "di-meta", textContent: fmtInt(b.node_count) + " declarations · " + fmtInt(b.non_opaque_count) + " read" })
        ]));
      });
    };

    const contentBox = el("div", { id: "bpContentBox" }, [
      el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading blueprint…" })])
    ]);

    main.appendChild(el("div", { className: "doc-layout" }, [
      el("aside", { className: "doc-sidebar", "aria-label": "Blueprints" }, [
        el("div", { className: "doc-sidebar-top" }, [
          el("strong", { className: "doc-sidebar-title", textContent: "Blueprints" }),
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
        el("h3", { textContent: "Could not load this blueprint" }),
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
    box.appendChild(el("div", { className: "bp-head" }, [
      el("h2", { textContent: metaEntry.title || doc.pillar || metaEntry.id }),
      el("p", { className: "bp-head-meta", textContent: [
        doc.root ? "Root: " + shortName(doc.root) : null,
        fmtInt(nodes.length) + " declarations",
        fmtInt((doc.edges || []).length) + " edges",
        claims.length ? fmtInt(claims.length) + " claims" : null,
        horn.length ? fmtInt(horn.length) + " rules" : null
      ].filter(Boolean).join(" · ") })
    ]));

    // Controls
    const stSeg = el("div", { className: "seg" }, [["all", "All"], ["READ", "Read"], ["PARTIAL", "Partial"], ["OPAQUE", "Opaque"]].map(([st, lbl]) =>
      el("button", {
        type: "button", className: state.bpStatus === st ? "active" : "", textContent: lbl,
        onclick: () => { state.bpStatus = st; state.bpPage = 0; renderBlueprintDetail(doc, metaEntry); }
      })
    ));

    box.appendChild(el("div", { className: "toolbar-row" }, [
      stSeg,
      el("input", {
        type: "search", className: "input grow", id: "bpNodeSearch",
        placeholder: "Filter by name, summary or file…",
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
      el("span", { className: "toolbar-count", textContent: fmtInt(filtered.length) + " shown" })
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
          n.anchor ? el("div", { className: "bp-anchor" }, [makeSourceLink(n.anchor, null, null, n.id)]) : null
        ]),
        el("td", null, [
          el("span", { className: "pill " + statusPillClass(n.status), textContent: n.status || "—" }),
          n.verdict ? el("span", { className: "pill " + statusPillClass(n.verdict), textContent: n.verdict, style: { marginLeft: "4px" } }) : null
        ]),
        el("td", { className: "num", textContent: n.dom_sub >= 0 ? fmtInt(n.dom_sub) : "—" }),
        el("td", null, [
          cir ? el("button", {
            type: "button", className: "btn sm", textContent: "Diagram ›",
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
            makeTh("Status", "status", false),
            makeTh("Subtree", "dom", true),
            makeTh("Role", "role", false)
          ])]),
          tbody
        ])
      ]),
      filtered.length > PAGE ? el("div", { className: "pager" }, [
        el("button", { type: "button", className: "btn sm", disabled: state.bpPage <= 0, textContent: "← Previous", onclick: () => { state.bpPage--; renderBlueprintDetail(doc, metaEntry); } }),
        el("span", { textContent: "Page " + (state.bpPage + 1) + " of " + (maxPage + 1) + " (" + fmtInt(filtered.length) + " declarations)" }),
        el("button", { type: "button", className: "btn sm", disabled: state.bpPage >= maxPage, textContent: "Next →", onclick: () => { state.bpPage++; renderBlueprintDetail(doc, metaEntry); } })
      ]) : null
    ]);

    const ins = el("aside", { className: "bp-inspector" });
    if (sel) {
      const cir = findAnyCircuitForSymbol(sel.id);
      ins.appendChild(el("div", { className: "cir-ins-hd" }, [
        el("span", { textContent: "Declaration" }),
        el("span", { className: "pill " + statusPillClass(sel.status), textContent: sel.status || "—" })
      ]));
      ins.appendChild(el("div", { className: "cir-ins-title", textContent: sel.id }));
      if (sel.header) ins.appendChild(el("div", { className: "bp-header-box", textContent: sel.header }));
      if (sel.summary) ins.appendChild(el("div", { className: "cir-ins-note", textContent: sel.summary }));
      const kv = el("div", { className: "cir-ins-kv" });
      const addKv = (k, v) => { if (v != null && v !== "") { kv.appendChild(el("div", { className: "k", textContent: k })); kv.appendChild(el("div", { className: "v", textContent: String(v) })); } };
      addKv("Kind / role", (sel.kind || "—") + " / " + (sel.role || "—"));
      addKv("Module", sel.module || "—");
      if (sel.dom_sub >= 0) addKv("Exclusive subtree", fmtInt(sel.dom_sub));
      if (sel.dom && sel.dom.idom) addKv("Reached through", sel.dom.idom);
      ins.appendChild(kv);
      const acts = el("div", { className: "cir-ins-acts" });
      if (cir) {
        acts.appendChild(el("button", {
          type: "button", className: "btn sm", textContent: "Open diagram ›",
          onclick: () => navigate("#circuit/" + cir.mode + "/" + encodeURIComponent(cir.short || cir.name))
        }));
      }
      acts.insertBefore(el("a", { className: "btn sm primary", href: "#item/" + encodeURIComponent(sel.id), textContent: "Inspect ›" }), acts.firstChild);
      if (sel.anchor) {
        const gh = buildGithubUrl(sel.anchor);
        if (gh) {
          const peek = makeSrcButton(gh, sel.id, { className: "btn sm", text: "Show source inline" });
          if (peek) acts.appendChild(peek);
          acts.appendChild(el("a", { className: "btn sm", href: gh, target: "_blank", rel: "noopener noreferrer", textContent: "View proof file ↗" }));
        }
      }
      if (acts.childNodes.length) ins.appendChild(acts);
    } else {
      ins.appendChild(el("div", { className: "cir-ins-note", textContent: "Nothing matches the current filter." }));
    }

    box.appendChild(el("div", { className: "bp-detail-split" }, [tableSide, ins]));

    // Claims preview
    if (claims.length) {
      box.appendChild(el("div", { className: "section-hdr" }, [
        el("h2", { textContent: "Claims" }),
        el("span", { className: "sub", textContent: claims.length > 40 ? "First 40 of " + fmtInt(claims.length) : fmtInt(claims.length) + " in total" })
      ]));
      box.appendChild(el("div", { className: "table-wrap" }, [
        el("table", { className: "data-table" }, [
          el("thead", null, [el("tr", null, [el("th", { textContent: "Evidence" }), el("th", { textContent: "Claim" }), el("th", { textContent: "Source" })])]),
          el("tbody", null, claims.slice(0, 40).map((c) => {
            const txt = typeof c === "string" ? c : (c.text || "");
            const tag = typeof c === "string" ? "L" : (c.tag || "L");
            const ancs = (c && Array.isArray(c.anchors)) ? c.anchors : [];
            return el("tr", null, [
              el("td", null, [el("span", { className: "ev-tag " + (["K", "L", "S", "M"].includes(tag) ? tag : "L"), textContent: "[" + tag + "]" })]),
              el("td", { textContent: txt }),
              el("td", null, ancs.slice(0, 3).map((a) => el("div", null, [makeSourceLink(a)])))
            ]);
          }))
        ])
      ]));
    }
  }

  // ==========================================================================
  // VIEW 6: CLUSTERS (name-blinded structural clusters)
  // ==========================================================================
  async function renderFlirtView() {
    const main = $("#appMain");
    clearEl(main);
    const assetPath = state.manifest && state.manifest.assets && state.manifest.assets.cluster_labels;
    const tier1 = state.manifest && state.manifest.assets && state.manifest.assets.flirt_tier1;
    if (!assetPath && tier1) {
      main.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading clusters…" })]));
      try {
        renderTier1Body(await fetchJson(tier1));
      } catch (err) {
        clearEl(main);
        main.appendChild(el("div", { className: "empty-card" }, [el("h3", { textContent: "Could not load clusters" }), el("p", { textContent: String(err.message || err) })]));
      }
      return;
    }
    if (!assetPath) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No cluster data" }),
        el("p", { textContent: "This build does not include cluster labels." })
      ]));
      return;
    }

    main.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading clusters…" })]));
    try {
      const doc = await fetchJson(assetPath);
      renderFlirtBody(doc);
    } catch (err) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Could not load clusters" }),
        el("p", { textContent: String(err.message || err) })
      ]));
    }
  }

  // Turn an audit reason string into one plain sentence (or nothing).
  function clusterReasonText(reason) {
    const r = String(reason || "");
    const m = r.match(/Blinded \(([^)]*)\)(?: and Tier1 \(([^)]*)\))?.*?folder '([^']*)' expected \[([^\]]*)\]/);
    if (!m) return "";
    const nice = (x) => String(x || "").replace(/'/g, "").replace(/_/g, " ").replace(/\+/g, " + ").trim();
    return "Reads as " + nice(m[1]) + (m[2] && m[2] !== m[1] ? " (names suggest " + nice(m[2]) + ")" : "") + "; the folder " + m[3] + " suggests " + nice(m[4]) + ".";
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

    main.appendChild(el("header", { className: "page-head" }, [
      el("h1", { textContent: "Clusters" }),
      el("p", { className: "page-lede", textContent: fmtInt(clusters.length) + " groups of declarations that share the same structural shape. Each group was labeled by a reader who saw only the mathematics, with names and file paths hidden; the label is then compared with the folder the code actually lives in." })
    ]));

    if (doc.epistemic_note) {
      main.appendChild(el("p", { className: "quiet-note", textContent: "Labels are heuristic. They are inferred from statements and imports only; proofs were not read." }));
    }

    main.appendChild(el("section", { className: "kpi-strip" }, [
      { label: "Clusters", val: fmtInt(clusters.length), sub: (totals.collapse_pct != null ? totals.collapse_pct + "% of declarations fall in the largest groups" : "") },
      { label: "In an unexpected folder", val: fmtInt(misplaced), sub: fmtInt(highSev) + " clearly out of place" },
      { label: "Partly mismatched", val: fmtInt(drift), sub: "folder and topic only partly agree" },
      { label: "Folder matches topic", val: fmtInt(aligned), sub: "" }
    ].map((k) => el("div", { className: "kpi-card" }, [
      el("div", { className: "kpi-val", textContent: k.val }),
      el("div", { className: "kpi-label", textContent: k.label }),
      k.sub ? el("div", { className: "kpi-sub", textContent: k.sub }) : null
    ]))));

    // Stacked breakdown bar
    main.appendChild(el("div", { className: "stacked-bar", title: "Unexpected folder / partly mismatched / matches" }, [
      el("div", { className: "seg-misplaced", style: { width: ((misplaced / totalN) * 100).toFixed(1) + "%" } }),
      el("div", { className: "seg-drift", style: { width: ((drift / totalN) * 100).toFixed(1) + "%" } }),
      el("div", { className: "seg-aligned", style: { width: ((aligned / totalN) * 100).toFixed(1) + "%" } })
    ]));

    // Filters
    const statusSeg = el("div", { className: "seg" }, [
      ["all", "All"], ["cross_domain_misplaced", "Unexpected folder"], ["partial_drift", "Partly mismatched"], ["aligned", "Matches"]
    ].map(([k, lbl]) => el("button", {
      type: "button", className: state.flirt.status === k ? "active" : "", textContent: lbl,
      onclick: () => { state.flirt.status = k; state.flirt.page = 0; renderFlirtBody(doc); }
    })));

    const sevSel = el("select", {
      className: "select",
      "aria-label": "Severity",
      onchange: (ev) => { state.flirt.severity = ev.target.value; state.flirt.page = 0; renderFlirtBody(doc); }
    }, [["all", "Any severity"], ["high", "High"], ["moderate", "Moderate"], ["low", "Low"], ["none", "None"]].map(([s, lbl]) =>
      el("option", { value: s, selected: state.flirt.severity === s, textContent: lbl })
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
        type: "search", className: "input grow", id: "flirtSearchInput", placeholder: "Search by cluster, topic, folder or declaration…",
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
      el("span", { className: "toolbar-count", textContent: fmtInt(filtered.length) + " clusters" })
    ]));

    main.appendChild(el("div", { className: "table-wrap" }, [
      el("table", { className: "data-table" }, [
        el("thead", null, [el("tr", null, [
          el("th", { textContent: "Cluster" }),
          el("th", { textContent: "Topic (blind label)" }),
          el("th", { textContent: "Folder" }),
          el("th", { textContent: "Match" }),
          el("th", { className: "num", textContent: "Declarations" })
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
              el("strong", { textContent: String(bl.label || bl.primary_domain || "—").replace(/^\[M\]\s*/, ""), style: { color: "var(--text-hi)", fontWeight: "600" } }),
              bl.primary_domain ? el("div", { className: "cir-ins-note mono", textContent: bl.primary_domain + (bl.secondary_domain ? " / " + bl.secondary_domain : "") }) : null
            ]),
            el("td", null, [
              el("code", { textContent: ma.folder_l2 || "—" }),
              reps.length ? el("div", { style: { marginTop: "4px", fontSize: "11px" } }, reps.slice(0, 2).map((r) => {
                const u = safeHref(r.github_url) || buildGithubUrl(r.module, r.line);
                const peek = u ? makeSrcButton(u, r.name) : null;
                return el("div", { className: "src-link" }, [
                  u ? el("a", { href: u, target: "_blank", rel: "noopener noreferrer", className: "mono", textContent: shortName(r.name) })
                    : el("code", { textContent: shortName(r.name) }),
                  peek
                ]);
              })) : null
            ]),
            el("td", null, [
              el("span", { className: "pill " + statusPillClass(ma.status), textContent: String(ma.status || "—").replace(/_/g, " ") }),
              ma.severity ? el("span", { className: "pill", textContent: ma.severity, style: { marginLeft: "4px" } }) : null,
              clusterReasonText(ma.reason) ? el("div", { className: "cir-ins-note", style: { marginTop: "3px" }, textContent: clusterReasonText(ma.reason) }) : null
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
        el("button", { type: "button", className: "btn sm", disabled: state.flirt.page <= 0, textContent: "← Previous", onclick: () => { state.flirt.page--; renderFlirtBody(doc); } }),
        el("span", { textContent: "Page " + (state.flirt.page + 1) + " of " + (maxPage + 1) }),
        el("button", { type: "button", className: "btn sm", disabled: state.flirt.page >= maxPage, textContent: "Next →", onclick: () => { state.flirt.page++; renderFlirtBody(doc); } })
      ]));
    }
  }

  // ==========================================================================
  // VIEW 6B: EDGE MAP (dependency contact matrix, Mathlib overlap, same-statement pairs)
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

  // Canvas colors that follow the light/dark theme.
  const isLightTheme = () => state.theme === "light";
  const canvasBgRGB = () => (isLightTheme() ? [250, 250, 247] : [10, 12, 18]);
  const canvasBg = () => (isLightTheme() ? "#fafaf7" : "#080b14");
  const canvasInk = (a) => (isLightTheme() ? "rgba(30, 41, 59, " + a + ")" : "rgba(226, 232, 240, " + a + ")");
  const canvasLabel = () => (isLightTheme() ? "#334155" : "#cbd5e1");
  const mix = (a, b, t) => a.map((v, k) => Math.round(v + (b[k] - v) * t));

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

    ctx.fillStyle = canvasBg();
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
          const e0 = canvasBgRGB();
          data[idx] = e0[0]; data[idx + 1] = e0[1]; data[idx + 2] = e0[2]; data[idx + 3] = 255;
          continue;
        }
        const inten = Math.pow(tq / 255, 0.72);
        let r, g, b;
        if (mode === "density" && isLightTheme()) {
          const c = inten < 0.5 ? mix([236, 242, 246], [56, 150, 186], inten * 2) : mix([56, 150, 186], [180, 83, 9], (inten - 0.5) * 2);
          r = c[0]; g = c[1]; b = c[2];
        } else if (mode === "density") {
          // Dark -> teal -> cyan -> amber hotspot
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
          if (isLightTheme()) {
            const col = d >= 0 ? mix([148, 163, 184], [2, 132, 199], d) : mix([148, 163, 184], [217, 119, 6], -d);
            const c = mix(canvasBgRGB(), col, 0.25 + 0.75 * inten);
            r = c[0]; g = c[1]; b = c[2];
          } else {
            r = Math.round(10 + (cr - 10) * k);
            g = Math.round(12 + (cg - 12) * k);
            b = Math.round(18 + (cb - 18) * k);
          }
        }
        data[idx] = r; data[idx + 1] = g; data[idx + 2] = b; data[idx + 3] = 255;
      }
    }
    octx.putImageData(img, 0, 0);
    ctx.imageSmoothingEnabled = false;
    ctx.drawImage(off, pad, pad, size, size);

    // Pillar boundary lines + labels (A | D | C | B | DM | BR)
    const ticks = (hic.pillar_ticks || []).filter((t) => ATLAS_PILLAR_SHORT[t.key]);
    ctx.strokeStyle = canvasInk(0.28);
    ctx.lineWidth = 1;
    ctx.font = "bold 10px ui-monospace, Menlo, Consolas, monospace";
    ctx.fillStyle = canvasLabel();
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
    ctx.strokeStyle = canvasInk(0.4);
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

    ctx.fillStyle = canvasBg();
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
    ctx.strokeStyle = canvasInk(0.2);
    ctx.lineWidth = 1;
    ctx.font = "bold 10px ui-monospace, Menlo, Consolas, monospace";
    ctx.fillStyle = canvasLabel();
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
        ctx.strokeStyle = canvasInk(0.12);
        ctx.beginPath();
        ctx.moveTo(padL, y + 0.5);
        ctx.lineTo(padL + size, y + 0.5);
        ctx.stroke();
      }
      const midFrac = ((Number(st.lib_idx_start || 0) + Number(st.lib_idx_end || 0)) / 2) / nLib;
      ctx.fillStyle = canvasLabel();
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

    ctx.strokeStyle = canvasInk(0.4);
    ctx.lineWidth = 1;
    ctx.strokeRect(padL + 0.5, padT + 0.5, size - 1, size - 1);
  }

  function atlasTwinRatio(pair) {
    const a = Math.max(1, Number((pair.thm_a && pair.thm_a.value_nodes) || 1));
    const b = Math.max(1, Number((pair.thm_b && pair.thm_b.value_nodes) || 1));
    return Math.max(a / b, b / a);
  }

  function fmtCompact(n) {
    const v = Number(n) || 0;
    if (v >= 1e9) return (v / 1e9).toFixed(1).replace(/\.0$/, "") + "B";
    if (v >= 1e6) return Math.round(v / 1e6) + "M";
    if (v >= 1e4) return Math.round(v / 1e3) + "K";
    return fmtInt(v);
  }

  async function renderAtlasView(sub) {
    const main = $("#appMain");
    clearEl(main);
    const a = (state.manifest && state.manifest.assets) || {};
    const assetPath = a.atlas;
    if (!assetPath && !a.module_matrix && !a.embedding_2d) {
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "No edge map" }),
        el("p", { textContent: "This build does not include the dependency matrix." })
      ]));
      return;
    }

    main.appendChild(el("div", { className: "loading-card" }, [
      el("div", { className: "spinner" }),
      el("div", { textContent: "Loading…" })
    ]));
    try {
      if (assetPath) renderAtlasBody(await fetchJson(assetPath));
      else if (a.module_matrix) renderModuleMatrixBody(await fetchJson(a.module_matrix));
      else {
        clearEl(main);
        main.appendChild(el("header", { className: "page-head" }, [el("h1", { textContent: "2D Map" })]));
        const host = el("section", { className: "map2d-section", id: "map2dSection" });
        main.appendChild(host);
        await mountMap2d(host);
      }
      if (sub === "map") {
        const sec = $("#map2dSection");
        if (sec) requestAnimationFrame(() => sec.scrollIntoView({ block: "start" }));
      }
    } catch (err) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Could not load the edge map" }),
        el("p", { textContent: String(err.message || err) })
      ]));
    }
  }

  // Source spec for one side of a same-statement pair (project side: pinned
  // GitHub blob; library side: documentation link only).
  function atlasTwinSourceSpec(thm, label) {
    if (!thm) return null;
    const srcPath = thm.src_rel_path || thm.module || "";
    const gh = (thm.origin === "project" && srcPath) ? buildGithubUrl(srcPath, thm.line_no) : (safeHref(thm.github_url) || null);
    const docs = /mathlib/i.test(String(thm.origin || "")) && thm.name
      ? "https://leanprover-community.github.io/mathlib4_docs/find/?pattern=" + encodeURIComponent(String(thm.name).replace(/^_root_\./, "")) + "#doc"
      : "";
    return {
      url: gh || "",
      title: thm.name,
      line: thm.line_no || null,
      label,
      peekable: Boolean(gh && isLeanBlob(gh)),
      fallbackUrl: docs,
      fallbackLabel: "Mathlib docs ↗"
    };
  }

  function openHicTray(tray, canvas, hic, cell, couplingMap) {
    const meta = hic.cell_samples_meta || {};
    const G32 = Number(meta.grid_size) || 32;
    const r32 = Math.floor((cell.by * G32) / cell.N);
    const c32 = Math.floor((cell.bx * G32) / cell.N);
    atlasDrawHicCanvas(canvas, hic, state.atlas.hicMode);
    const ctx = canvas.getContext("2d");
    if (ctx) {
      const step = (cell.N / G32) * 4;
      ctx.strokeStyle = "#ffffff";
      ctx.lineWidth = 2;
      ctx.strokeRect(26 + c32 * step, 26 + r32 * step, step, step);
    }
    const nLive = Number(hic.n_live_decls) || 1;
    const srcReg = atlasRegionForDfs(hic.regions, Math.floor(((cell.by + 0.5) / cell.N) * nLive));
    const dstReg = atlasRegionForDfs(hic.regions, Math.floor(((cell.bx + 0.5) / cell.N) * nLive));
    const samples = (hic.cell_samples || {})[r32 + "," + c32] || [];
    const regionSamples = (srcReg && dstReg && hic.region_edge_samples) ? (hic.region_edge_samples[srcReg.key + "->" + dstReg.key] || []) : [];
    const rc = (srcReg && dstReg) ? couplingMap.get(srcReg.key + "->" + dstReg.key) : null;
    const cat = hic.bin_catalog || [];
    const rowDecls = cat[cell.by] || [];
    const colDecls = cat[cell.bx] || [];
    clearEl(tray);
    tray.hidden = false;
    tray.appendChild(trayHeader((srcReg ? srcReg.label : "Row " + cell.by) + " → " + (dstReg ? dstReg.label : "Column " + cell.bx), rc ? fmtInt(rc.total) + " edges between these parts" : "", () => { tray.hidden = true; atlasDrawHicCanvas(canvas, hic, state.atlas.hicMode); }));
    tray.appendChild(el("div", { className: "tray-cols" }, [
      el("div", null, [el("h4", { textContent: "Row: leading declarations" }), ...(rowDecls.length ? rowDecls.map(declTrayRow) : [el("p", { className: "nb-empty", textContent: "None recorded." })])]),
      el("div", null, [el("h4", { textContent: "Column: leading declarations" }), ...(colDecls.length ? colDecls.map(declTrayRow) : [el("p", { className: "nb-empty", textContent: "None recorded." })])])
    ]));
    if (samples.length) {
      tray.appendChild(el("h4", { textContent: "Sample edges in this block" }));
      samples.slice(0, 6).forEach((e) => tray.appendChild(edgeTrayRow(e)));
    } else {
      tray.appendChild(el("p", { className: "nb-empty", textContent: "No edges are recorded in this block." }));
    }
    if (regionSamples.length) {
      tray.appendChild(el("h4", { textContent: "Bridges between these parts" }));
      regionSamples.slice(0, 4).forEach((e) => tray.appendChild(edgeTrayRow(e)));
    }
  }

  function openSyntenyTray(tray, syn, hic, pb, lb) {
    const ms = syn.match_samples || {};
    let key = pb + "," + lb;
    let found = ms[key];
    if (!found) {
      let best = null, bd = Infinity;
      for (let dx = -2; dx <= 2; dx++) {
        for (let dy = -2; dy <= 2; dy++) {
          const k = (pb + dx) + "," + (lb + dy);
          if (ms[k] && dx * dx + dy * dy < bd) { bd = dx * dx + dy * dy; best = k; }
        }
      }
      if (best) { key = best; found = ms[best]; }
    }
    const [kb, kl] = key.split(",").map(Number);
    const G = Number((syn.grid_meta && syn.grid_meta.grid_size) || 128);
    const nLive = Number(syn.n_live_decls) || 1;
    const reg = atlasRegionForDfs(hic.regions, Math.floor(((kb + 0.5) / G) * nLive));
    const libLabel = (syn.lib_bins || [])[kl] || ("layer " + kl);
    clearEl(tray);
    tray.hidden = false;
    tray.appendChild(trayHeader((reg ? reg.label : "Proof position " + kb) + " ↔ " + libLabel, found ? fmtInt(found.length) + " sample matches" : "", () => { tray.hidden = true; }));
    if (!found || !found.length) {
      tray.appendChild(el("p", { className: "nb-empty", textContent: "No matches are recorded near this point. Try a brighter dot." }));
      return;
    }
    // m = [proj_name, proj_mod, proj_line, lib_name, lib_repo, type_nodes, match_kind]
    for (const mt of found.slice(0, 8)) {
      const [pName, pMod, pLine, lName, lRepo, tn, kind] = mt;
      const docs = /mathlib/i.test(String(lRepo || "")) ? "https://leanprover-community.github.io/mathlib4_docs/find/?pattern=" + encodeURIComponent(String(lName).startsWith("_private.") ? shortName(lName) : String(lName)) + "#doc" : "";
      const pUrl = pMod ? buildGithubUrl(pMod, pLine) : null;
      tray.appendChild(el("div", { className: "tray-row" }, [
        el("div", { className: "tray-main" }, [
          el("span", { className: "tray-name", title: pName + " ↔ " + lName }, [
            el("a", { href: "#item/" + encodeURIComponent(pName), textContent: shortName(pName) }),
            el("span", { className: "tray-arrow", textContent: " ↔ " }),
            el("span", { textContent: shortName(lName) })
          ]),
          el("span", { className: "tray-meta", textContent: [lRepo, kind === "k1n" ? "same signature hash" : kind, tn ? "statement size " + fmtInt(tn) : null].filter(Boolean).join(" · ") })
        ]),
        el("div", { className: "cir-ins-acts" }, [
          el("a", { className: "btn sm", href: "#item/" + encodeURIComponent(pName), textContent: "Inspect ›" }),
          pUrl ? makeSrcButton(pUrl, pName, { className: "btn sm", text: "Source" }) : null,
          docs ? el("a", { className: "btn sm", href: docs, target: "_blank", rel: "noopener noreferrer", textContent: "Mathlib docs ↗" }) : null
        ])
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
    const totalEdges = Number(et.total_streamed || 0);
    const nLib = Number(syn.n_library_decls || 0);

    main.appendChild(el("header", { className: "page-head" }, [
      el("h1", { textContent: "Dependency Matrix & Duplicate Proofs" }),
      el("p", { className: "page-lede", textContent: "Three views of the same dependency graph. Declarations are laid out in one fixed order (" + fmtInt(hic.n_live_decls || 0) + " reachable declarations, grouped by the part of the proof that owns them), so each part sits in one contiguous block." }),
      el("p", { className: "quiet-note", textContent: "Several numbers below rely on a normalized statement hash: a fingerprint of a declaration's statement with names erased. Two theorems with the same hash state the same thing up to renaming." })
    ]));

    // Key numbers
    const allAliens = (ap.all_sampled_pairs && ap.all_sampled_pairs.alien_proof) || 0;
    const crossAliens = (ap.cross_repo_pairs && ap.cross_repo_pairs.alien_proof) || 0;
    main.appendChild(el("section", { className: "kpi-strip" }, [
      { label: "Dependency edges", val: fmtInt(totalEdges), sub: fmtInt(et.type_only || 0) + " in statements · " + fmtInt(et.value_only || 0) + " in proofs · " + fmtInt(et.both || 0) + " both" },
      { label: "Shared signatures", val: fmtInt(ac.nontrivial_collision_buckets || 0), sub: "groups of theorems with the same statement shape" },
      { label: "Same statement, different proof", val: fmtInt(allAliens), sub: "pairs sharing under 20% of lemmas · " + fmtInt(crossAliens) + " against Mathlib" },
      { label: "Mathlib matches", val: fmtInt(ht.total_matches || 0), sub: fmtInt(ht.named_matches || 0) + " by name" },
      { label: "Unmatched regions", val: fmtInt(ti.zero_named_match_bins_256 || 0) + " of " + fmtInt(ti.eligible_project_bins_256 || 0), sub: (ti.zero_named_share_pct != null ? ti.zero_named_share_pct + "% of the ordering has no named Mathlib match" : "no named Mathlib match") }
    ].map((k) => el("div", { className: "kpi-card" }, [
      el("div", { className: "kpi-val", textContent: k.val }),
      el("div", { className: "kpi-label", textContent: k.label }),
      k.sub ? el("div", { className: "kpi-sub", textContent: k.sub }) : null
    ]))));

    // Edge contact map + Mathlib overlap dot-plot
    const pillarTicks = (hic.pillar_ticks || []).filter((t) => ATLAS_PILLAR_SHORT[t.key] && /^pillar_/.test(t.key));
    const pillarLetters = pillarTicks.map((t) => ATLAS_PILLAR_SHORT[t.key]);
    const joinLetters = (xs) => xs.length <= 1 ? (xs[0] || "") : xs.slice(0, -1).join(", ") + " and " + xs[xs.length - 1];
    const hicExplain = "All " + fmtCompact(totalEdges) + " directed edges. Rows and columns are slices of the declarations in dominator-tree order (a depth-first walk), and a cell counts edges from declarations in its row to declarations in its column. Most edges point forward to declarations listed later, above the diagonal; the sparser lower-left holds edges back into earlier parts" +
      (pillarLetters.length >= 2 ? ", and empty strips between columns " + joinLetters(pillarLetters) + " show those parts rarely use each other." : ".");
    const partLegend = (hic.pillar_ticks || []).filter((t) => ATLAS_PILLAR_SHORT[t.key]).map((t) => ATLAS_PILLAR_SHORT[t.key]).filter((c, i, arr) => arr.indexOf(c) === i)
      .map((c) => c + " " + (PART_NAMES[c] || c)).join(" · ");

    const hicCanvas = el("canvas", { id: "hicCanvas", className: "atlas-canvas", "aria-label": "Edge contact map" });
    const hicReadout = el("div", { id: "hicReadout", className: "atlas-readout", textContent: "Hover a cell to see which parts it connects; click it to list the declarations and edges inside." });
    const hicTray = el("div", { className: "cell-tray", id: "hicTray", hidden: true });

    const hicModeSeg = el("div", { className: "seg" }, [
      ["ratio", "Statements vs proofs"],
      ["density", "Density"]
    ].map(([k, lbl]) => el("button", {
      type: "button", className: state.atlas.hicMode === k ? "active" : "", textContent: lbl,
      onclick: () => { state.atlas.hicMode = k; renderAtlasBody(doc); }
    })));

    const hicCard = el("section", { className: "atlas-card" }, [
      el("div", { className: "atlas-card-hd" }, [
        el("h3", { textContent: "Edge Contact Map" }),
        hicModeSeg
      ]),
      el("p", { className: "atlas-explain", textContent: hicExplain }),
      el("div", { className: "atlas-legend" }, state.atlas.hicMode === "ratio" ? [
        el("span", null, [el("i", { className: "atlas-swatch", style: { background: "#1ed7ff" } }), "Mostly statement edges"]),
        el("span", null, [el("i", { className: "atlas-swatch", style: { background: "#dce2f7" } }), "Balanced"]),
        el("span", null, [el("i", { className: "atlas-swatch", style: { background: "#ffaa23" } }), "Mostly proof edges"]),
        et.diagonal_256_share_pct != null ? el("span", { textContent: "Near the diagonal: " + et.diagonal_256_share_pct + "%" }) : null
      ] : [
        el("span", { textContent: "Brighter cells hold more edges (log scale)." })
      ]),
      el("div", { className: "atlas-canvas-wrap" }, [hicCanvas]),
      el("p", { className: "atlas-axis", textContent: "Rows use columns." + (partLegend ? " Parts: " + partLegend + "." : "") }),
      hicReadout,
      hicTray
    ]);

    const synCanvas = el("canvas", { id: "syntenyCanvas", className: "atlas-canvas", "aria-label": "Mathlib overlap dot-plot" });
    const synReadout = el("div", { id: "syntenyReadout", className: "atlas-readout", textContent: "Hover the plot to see which part of the proof and which library layer a point compares; click a dot to list the matches." });
    const synTray = el("div", { className: "cell-tray", id: "synTray", hidden: true });

    const synToggles = el("div", { className: "atlas-toggles" }, [
      el("label", { className: "atlas-toggle" }, [
        el("input", { type: "checkbox", checked: state.atlas.showTerra, onchange: (ev) => { state.atlas.showTerra = ev.target.checked; atlasDrawSyntenyCanvas(synCanvas, syn, hic, state.atlas); } }),
        "Unmatched regions"
      ]),
      el("label", { className: "atlas-toggle" }, [
        el("input", { type: "checkbox", checked: state.atlas.showStreaks, onchange: (ev) => { state.atlas.showStreaks = ev.target.checked; atlasDrawSyntenyCanvas(synCanvas, syn, hic, state.atlas); } }),
        "Diagonal runs"
      ]),
      el("label", { className: "atlas-toggle" }, [
        el("input", { type: "checkbox", checked: state.atlas.showNamed, onchange: (ev) => { state.atlas.showNamed = ev.target.checked; atlasDrawSyntenyCanvas(synCanvas, syn, hic, state.atlas); } }),
        "Name matches"
      ])
    ]);

    const byCorpus = ht.by_corpus || {};
    const corpusPills = Object.entries(byCorpus).slice(0, 6).map(([k, v], idx) =>
      el("span", null, [el("i", { className: "atlas-swatch", style: { background: SYNTENY_CORPUS_COLORS[idx % SYNTENY_CORPUS_COLORS.length] } }), k + " " + fmtInt(v)])
    );

    const synCard = el("section", { className: "atlas-card" }, [
      el("div", { className: "atlas-card-hd" }, [
        el("h3", { textContent: "Mathlib Overlap Dot-Plot" }),
        synToggles
      ]),
      el("p", { className: "atlas-explain", textContent: "Compares this proof's signatures against " + fmtInt(nLib) + " standard library declarations. Each dot is a match; a diagonal run follows the library in order, and shaded columns have no match by name." }),
      el("div", { className: "atlas-legend" }, [
        ...corpusPills,
        el("span", null, [el("i", { className: "atlas-swatch", style: { background: "#facc15" } }), "Diagonal run (" + ((syn.diagonal_streaks || []).length) + ")"])
      ]),
      el("div", { className: "atlas-canvas-wrap" }, [synCanvas]),
      synReadout,
      synTray
    ]);

    main.appendChild(el("div", { className: "atlas-grid" }, [hicCard, synCard]));

    atlasDrawHicCanvas(hicCanvas, hic, state.atlas.hicMode);
    atlasDrawSyntenyCanvas(synCanvas, syn, hic, state.atlas);

    // Contact map hover readout
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
      const ratioNat = ((rq - Number(tile.neutral_ratio_q8 ?? 128)) / 127) * Number(tile.ratio_clip_nat || 3.5);
      const nLive = Number(hic.n_live_decls) || 1;
      const srcReg = atlasRegionForDfs(hic.regions, Math.floor(((by + 0.5) / N) * nLive));
      const dstReg = atlasRegionForDfs(hic.regions, Math.floor(((bx + 0.5) / N) * nLive));
      const rc = (srcReg && dstReg) ? couplingMap.get(srcReg.key + "->" + dstReg.key) : null;
      const regTxt = (srcReg ? srcReg.label : "row " + by) + " → " + (dstReg ? dstReg.label : "column " + bx);
      const lean = Math.abs(ratioNat) < 0.25 ? "balanced" : (ratioNat > 0 ? "mostly statement edges" : "mostly proof edges");
      const rcTxt = rc ? " · between these parts: " + fmtInt(rc.total) + " edges" : "";
      hicReadout.textContent = regTxt + " · about " + fmtInt(estEdges) + " edges in this cell, " + (tq > 0 ? lean : "none") + rcTxt;
    });

    // Dot-plot hover readout
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
      const nL = Number(syn.n_library_decls) || 1;
      const reg = atlasRegionForDfs(hic.regions, Math.floor(((pb + 0.5) / G) * nLive));
      const libIdx = Math.floor(((lb + 0.5) / G) * nL);
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
      let msg = (reg ? reg.label : "Proof position " + pb) + " × library layer L" + (st ? st.stratum + " (" + (st.top_namespaces || []).join(", ") + ")" : lb);
      if (pt) msg += " · " + fmtInt(pt[2]) + " matches (" + fmtInt(pt[3]) + " by name, mostly " + (repos[pt[4]] || "library") + ")";
      if (streak) msg += " · diagonal run in " + streak.library_domain + " (" + streak.length_bins + " steps)";
      if (band) msg += " · no match by name across " + fmtInt(band.decl_count) + " declarations";
      synReadout.textContent = msg;
    });

    // Click a contact-map cell: declarations in its row/column and sample edges.
    const hicCellAt = (ev) => {
      const rect = hicCanvas.getBoundingClientRect();
      const cx = ((ev.clientX - rect.left) / rect.width) * hicCanvas.width;
      const cy = ((ev.clientY - rect.top) / rect.height) * hicCanvas.height;
      const N = Number((hic.tile_128 || {}).size) || 128;
      const bx = Math.floor((cx - 26) / 4);
      const by = Math.floor((cy - 26) / 4);
      return (bx < 0 || bx >= N || by < 0 || by >= N) ? null : { bx, by, N };
    };
    hicCanvas.addEventListener("click", (ev) => {
      const cell = hicCellAt(ev);
      if (!cell) return;
      openHicTray(hicTray, hicCanvas, hic, cell, couplingMap);
    });
    synCanvas.addEventListener("click", (ev) => {
      const rect = synCanvas.getBoundingClientRect();
      const cx = ((ev.clientX - rect.left) / rect.width) * synCanvas.width;
      const cy = ((ev.clientY - rect.top) / rect.height) * synCanvas.height;
      const G = Number((syn.grid_meta && syn.grid_meta.grid_size) || 128);
      const pb = Math.floor((cx - 32) / 4);
      const lb = G - 1 - Math.floor((cy - 14) / 4);
      if (pb < 0 || pb >= G || lb < 0 || lb >= G) return;
      openSyntenyTray(synTray, syn, hic, pb, lb);
    });

    // 2D map
    if (state.manifest.assets && state.manifest.assets.embedding_2d) {
      main.appendChild(el("div", { className: "section-hdr" }, [el("h2", { textContent: "2D Map" })]));
      const mapHost = el("section", { className: "map2d-section", id: "map2dSection" });
      main.appendChild(mapHost);
      mountMap2d(mapHost);
    }

    // Same statement, different proof
    main.appendChild(el("div", { className: "section-hdr" }, [
      el("h2", { textContent: "Same Statement, Different Proof" })
    ]));
    main.appendChild(el("p", { className: "section-lede", textContent: "Theorem pairs with the same type signature whose proofs share almost no lemmas. Overlap J is the share of proof dependencies the two have in common (0 means none, 1 means identical)." }));

    const hist = Array.isArray(aliens.jaccard_histogram_20bins) ? aliens.jaccard_histogram_20bins : [];
    if (hist.length) {
      const hMax = Math.max(1, ...hist.map((v) => Number(v) || 0));
      const bars = hist.map((cnt, idx) => {
        const lo = (idx * 0.05).toFixed(2);
        const hi = ((idx + 1) * 0.05).toFixed(2);
        const cls = idx < 4 ? "alien" : (idx < 14 ? "variant" : "clone");
        const pct = Math.max(3, Math.round((Number(cnt) / hMax) * 100));
        return el("div", { className: "hist-bar-col", title: "Overlap " + lo + "–" + hi + ": " + fmtInt(cnt) + " pairs" }, [
          el("div", { className: "hist-bar " + cls, style: { height: pct + "%" } })
        ]);
      });
      main.appendChild(el("div", { className: "hist-wrap" }, [
        el("div", { className: "atlas-card-hd", style: { marginBottom: "6px" } }, [
          el("strong", { className: "hist-title", textContent: "How much do proofs of the same statement overlap?" }),
          el("div", { className: "atlas-legend" }, [
            el("span", null, [el("i", { className: "atlas-swatch", style: { background: "var(--crimson)" } }), "Different (under 0.20): " + fmtInt(allAliens)]),
            el("span", null, [el("i", { className: "atlas-swatch", style: { background: "var(--amber)" } }), "Partly shared: " + fmtInt((ap.all_sampled_pairs && ap.all_sampled_pairs.variant) || 0)]),
            el("span", null, [el("i", { className: "atlas-swatch", style: { background: "var(--emerald)" } }), "Near-identical (0.70+): " + fmtInt((ap.all_sampled_pairs && ap.all_sampled_pairs.clone) || 0)])
          ])
        ]),
        el("div", { className: "hist-bars" }, bars),
        el("div", { className: "hist-axis" }, [
          el("span", { textContent: "0 · no shared lemmas" }),
          el("span", { textContent: "0.20" }),
          el("span", { textContent: "0.50" }),
          el("span", { textContent: "0.70" }),
          el("span", { textContent: "1 · same lemmas" })
        ])
      ]));
    }

    const nIntra = (aliens.top_alien_pairs_intra || []).length;
    const nCross = (aliens.top_alien_pairs_cross_repo || []).length;
    const scopeSeg = el("div", { className: "seg" }, [
      ["all", "All"],
      ["intra", "Within this project (" + nIntra + ")"],
      ["cross", "Against Mathlib (" + nCross + ")"]
    ].map(([k, lbl]) => el("button", {
      type: "button", className: state.atlas.twinScope === k ? "active" : "", textContent: lbl,
      onclick: () => { state.atlas.twinScope = k; renderAtlasBody(doc); }
    })));

    const sortSel = el("select", {
      className: "select",
      "aria-label": "Sort pairs",
      onchange: (ev) => { state.atlas.twinSort = ev.target.value; renderAtlasBody(doc); }
    }, [
      ["jaccard", "Lowest overlap first"],
      ["ratio", "Largest size difference first"],
      ["type_nodes", "Longest statement first"]
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
      el("span", { className: "toolbar-count", textContent: pairPool.length + " pairs" })
    ]));

    const renderSide = (thm, label, spec) => {
      if (!thm) return el("div", { className: "twin-side" });
      const cir = findAnyCircuitForSymbol(thm.name);
      const isProject = thm.origin === "project";
      const ghHref = spec && spec.url ? safeHref(spec.url) : null;
      const docHref = spec && !ghHref && spec.fallbackUrl ? safeHref(spec.fallbackUrl) : null;
      return el("div", { className: "twin-side" }, [
        el("div", { className: "twin-side-top" }, [
          el("span", { className: "twin-side-tag", textContent: label + " · " + (isProject ? "this project" : (thm.origin || "library")) }),
          el("span", { className: "twin-side-meta", textContent: "proof size " + fmtInt(thm.value_nodes) + " · " + fmtInt(thm.ev_size) + " lemmas" })
        ]),
        el("div", { className: "twin-side-name", textContent: thm.name }),
        thm.module ? el("div", { className: "twin-side-meta", textContent: thm.module + (thm.line_no ? ":" + thm.line_no : "") }) : null,
        el("div", { className: "cir-ins-acts", style: { marginTop: "3px" } }, [
          isProject ? el("a", { className: "btn sm", href: "#item/" + encodeURIComponent(thm.name), textContent: "Inspect ›" }) : null,
          ghHref ? el("a", { className: "btn sm", href: ghHref, target: "_blank", rel: "noopener noreferrer", textContent: "Proof file ↗" }) : null,
          docHref ? el("a", { className: "btn sm", href: docHref, target: "_blank", rel: "noopener noreferrer", textContent: "Mathlib docs ↗" }) : null,
          cir ? el("a", { className: "btn sm", href: "#circuit/" + cir.mode + "/" + encodeURIComponent(cir.short || cir.name), textContent: "Diagram ›" }) : null
        ])
      ]);
    };

    main.appendChild(el("div", { className: "twins-grid" }, pairPool.map((p) => {
      const ratio = atlasTwinRatio(p);
      const vnA = Number((p.thm_a && p.thm_a.value_nodes) || 0);
      const vnB = Number((p.thm_b && p.thm_b.value_nodes) || 0);
      const isCross = p.pair_scope === "cross_repo";
      const ratioNote = ratio >= 2
        ? (isCross && vnA < vnB ? ratio.toFixed(1) + "× shorter than Mathlib" : ratio.toFixed(1) + "× difference in proof size")
        : "";
      const specA = atlasTwinSourceSpec(p.thm_a, "A");
      const specB = atlasTwinSourceSpec(p.thm_b, "B");
      const peekBtn = (spec, txt) => (spec && spec.peekable)
        ? el("button", { type: "button", className: "btn sm", textContent: txt, title: "Preview Lean source inline", onclick: () => openSourcePeek(spec) })
        : null;
      const canCompare = (specA && specA.peekable) || (specB && specB.peekable);
      return el("article", { className: "twin-card" }, [
        el("div", { className: "twin-card-hd" }, [
          el("div", { className: "twin-card-facts" }, [
            el("span", { className: "twin-j", textContent: "Overlap J = " + Number(p.jaccard || 0).toFixed(3) }),
            el("span", { textContent: fmtInt(p.shared_ev_count) + " of " + fmtInt(p.union_ev_count) + " lemmas shared" }),
            el("span", { textContent: isCross ? "against Mathlib" : "within this project" }),
            ratioNote ? el("span", { textContent: ratioNote }) : null
          ])
        ]),
        el("div", { className: "twin-sides" }, [
          renderSide(p.thm_a, "A", specA),
          renderSide(p.thm_b, "B", specB)
        ]),
        el("div", { className: "twin-card-ft" }, [
          el("span", { className: "twin-side-meta", title: "Structural signature hash shared by both statements", textContent: "Signature " + (p.sighash || "—") + (p.bucket_size ? " · shared by " + fmtInt(p.bucket_size) + " theorems" : "") }),
          el("div", { className: "cir-ins-acts" }, [
            peekBtn(specA, "Peek A"),
            peekBtn(specB, "Peek B"),
            canCompare ? el("button", { type: "button", className: "btn sm primary", textContent: "Compare side-by-side", onclick: () => openSourceCompare(specA, specB) }) : null
          ])
        ])
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
        el("h3", { textContent: "No island data" }),
        el("p", { textContent: "This build does not include the portability analysis." })
      ]));
      return;
    }

    main.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading…" })]));
    try {
      const doc = await fetchJson(assetPath);
      renderPortabilityBody(doc);
    } catch (err) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Could not load the islands" }),
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

    main.appendChild(el("header", { className: "page-head" }, [
      el("h1", { textContent: "Islands" }),
      el("p", { className: "page-lede", textContent: fmtInt(targets.length) + " classical results, grouped by the project code they rely on. The " + islands.length + " groups share no project declarations with one another, so each could be lifted out on its own; together they use " + fmtInt(us.union_project_decls || 0) + " project declarations." })
    ]));

    // Island Cards
    main.appendChild(el("div", { className: "island-grid" }, islands.map((isl) => {
      const active = state.portability.island === isl.slug;
      return el("button", {
        type: "button",
        className: "island-card" + (active ? " active" : ""),
        "aria-pressed": active ? "true" : "false",
        onclick: () => {
          state.portability.island = active ? "" : isl.slug;
          renderPortabilityBody(doc);
        }
      }, [
        el("div", { className: "ic-top" }, [
          el("span", { className: "ic-name", textContent: isl.slug }),
          el("span", { className: "pill " + statusPillClass(isl.tier), textContent: isl.tier })
        ]),
        el("div", { className: "ic-sub", textContent: isl.targets.length + (isl.targets.length === 1 ? " result" : " results") + " · up to " + fmtInt(isl.maxProj) + " project declarations" }),
        el("div", { className: "ic-members", textContent: isl.targets.map((t) => shortName(t.name)).join(" · ") })
      ]);
    })));

    // Filtered Targets Table
    const activeIsland = islands.find((i) => i.slug === state.portability.island);
    const shownTargets = activeIsland ? activeIsland.targets : targets;

    main.appendChild(el("div", { className: "section-hdr" }, [
      el("h2", { textContent: activeIsland ? ("Island: " + activeIsland.slug) : "All results" }),
      activeIsland ? el("button", { type: "button", className: "btn sm", textContent: "Show all", onclick: () => { state.portability.island = ""; renderPortabilityBody(doc); } }) : null
    ]));

    main.appendChild(el("div", { className: "table-wrap", style: { marginBottom: "18px" } }, [
      el("table", { className: "data-table" }, [
        el("thead", null, [el("tr", null, [
          el("th", { textContent: "Result" }),
          el("th", { textContent: "Tier" }),
          el("th", { className: "num", textContent: "Project deps" }),
          el("th", { className: "num", textContent: "Statement deps" }),
          el("th", { textContent: "Main Mathlib dependencies" }),
          el("th", { textContent: "Diagram" })
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
                type: "button", className: "btn sm", textContent: "Diagram ›",
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
        el("h2", { textContent: "Overlap between results" }),
        el("span", { className: "sub", textContent: "Shared project declarations, with the Jaccard index underneath" })
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
        el("h3", { textContent: "No benchmark data" }),
        el("p", { textContent: "This build does not include benchmark results." })
      ]));
      return;
    }

    main.appendChild(el("div", { className: "loading-card" }, [el("div", { className: "spinner" }), el("div", { textContent: "Loading…" })]));
    try {
      const [bench, trim] = await Promise.all([
        assets.benchmark ? fetchJson(assets.benchmark).catch(() => null) : Promise.resolve(null),
        assets.trim_report ? fetchJson(assets.trim_report).catch(() => null) : Promise.resolve(null)
      ]);
      renderBenchmarksBody(bench, trim);
    } catch (err) {
      clearEl(main);
      main.appendChild(el("div", { className: "empty-card" }, [
        el("h3", { textContent: "Could not load benchmarks" }),
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

      main.appendChild(el("header", { className: "page-head" }, [
        el("h1", { textContent: "Benchmarks" }),
        el("p", { className: "page-lede", textContent: "The same analysis run on " + repos.length + " other Lean 4 repositories, to check that it is not tuned to a single project." + (bench.leanre_commit ? " Tool version " + bench.leanre_commit + "." : "") })
      ]));

      main.appendChild(el("section", { className: "kpi-strip" }, [
        { label: "Repositories", val: fmtInt(repos.length), sub: passCnt + " of " + repos.length + " pass" },
        { label: "Modules", val: fmtInt(totalMod), sub: fmtInt(totalLoc) + " lines" },
        { label: "Checks passed", val: fmtInt((bench.xrepo_issue_verification || []).filter((x) => x.status === "PASS").length) + " of " + fmtInt((bench.xrepo_issue_verification || []).length), sub: "portability checks" }
      ].map((k) => el("div", { className: "kpi-card" }, [
        el("div", { className: "kpi-val", textContent: k.val }),
        el("div", { className: "kpi-label", textContent: k.label }),
        el("div", { className: "kpi-sub", textContent: k.sub })
      ]))));

      main.appendChild(el("div", { className: "table-wrap", style: { marginBottom: "18px" } }, [
        el("table", { className: "data-table" }, [
          el("thead", null, [el("tr", null, [
            el("th", { textContent: "Repository" }),
            el("th", { textContent: "Root module" }),
            el("th", { className: "num", textContent: "Modules" }),
            el("th", { className: "num", textContent: "Lines" }),
            el("th", { className: "num", textContent: "Declarations (sorry)" }),
            el("th", { className: "num", textContent: "Misfiled" }),
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
          el("h2", { textContent: "Portability checks" })
        ]));
        main.appendChild(el("div", { className: "table-wrap", style: { marginBottom: "18px" } }, [
          el("table", { className: "data-table" }, [
            el("thead", null, [el("tr", null, [
              el("th", { textContent: "Check" }),
              el("th", { textContent: "Status" }),
              el("th", { textContent: "Component" }),
              el("th", { textContent: "What was checked" })
            ])]),
            el("tbody", null, issues.map((iss) => el("tr", null, [
              el("td", null, [el("strong", { textContent: iss.title || iss.id || "", style: { color: "var(--text-hi)", fontWeight: "600" } })]),
              el("td", null, [el("span", { className: "pill " + statusPillClass(iss.status), textContent: String(iss.status || "").toLowerCase() })]),
              el("td", null, [el("code", { textContent: iss.component || "—" })]),
              el("td", { textContent: (Object.keys(iss).filter((k) => /^verified/.test(k)).map((k) => iss[k]).find(Boolean)) || "" })
            ])))
          ])
        ]));
      }
    }

    if (trim) {
      const steps = (trim.c8_waterfall && trim.c8_waterfall.steps) || trim.steps || [];
      if (steps.length) {
        main.appendChild(el("div", { className: "section-hdr" }, [
          el("h2", { textContent: "Trimming unused declarations" }),
          el("span", { className: "sub", textContent: "How much of the repository each step removes" })
        ]));
        main.appendChild(el("div", { className: "table-wrap" }, [
          el("table", { className: "data-table" }, [
            el("thead", null, [el("tr", null, [
              el("th", { textContent: "Step" }),
              el("th", { textContent: "Description" }),
              el("th", { className: "num", textContent: "Removed" }),
              el("th", { className: "num", textContent: "Remaining" })
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
  // VIEW 9: SEARCH (prefix-indexed data files, `/` hotkey)
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
        out.push({ type: "finding", name: plainTextFromTex(f.title || f.slug), sub: "findings/" + f.slug + ".md", route: "#findings/" + encodeURIComponent(f.slug) });
      }
    }
    for (const d of (m.dossiers || [])) {
      if (((d.slug || "") + " " + (d.title || "") + " " + (d.category || "")).toLowerCase().includes(qLower)) {
        out.push({ type: "dossier", name: plainTextFromTex(d.title || d.slug), sub: "analysis/" + d.slug + ".md", route: "#dossiers/" + encodeURIComponent(d.slug) });
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
        out.push({ type: "circuit", name: cb.name, sub: "Structure diagram" + (cb.badge ? " · " + cb.badge : ""), route: "#circuit/bundle/" + encodeURIComponent(cb.short || cb.name) });
      }
    }
    for (const ct of (cir.theorems || [])) {
      if (((ct.name || "") + " " + (ct.short || "")).toLowerCase().includes(qLower)) {
        out.push({ type: "circuit", name: ct.name, sub: "Theorem diagram", route: "#circuit/theorem/" + encodeURIComponent(ct.short || ct.name) });
      }
    }
    return out;
  }

  const SEARCH_TYPE_LABEL = { circuit: "diagram", finding: "finding", dossier: "dossier", blueprint: "blueprint" };

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
      placeholder: "Search declarations, findings and dossiers…",
      "aria-label": "Search",
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
      ["all", "All"], ["decl", "Declarations"], ["circuit", "Diagrams"], ["doc", "Findings & dossiers"], ["blueprint", "Blueprints"]
    ].map(([k, lbl]) => el("button", {
      type: "button", className: state.search.scope === k ? "active" : "", textContent: lbl,
      onclick: () => { state.search.scope = k; renderSearchView(); }
    })));

    main.appendChild(el("section", { className: "search-hero" }, [
      el("h1", { textContent: "Search" }),
      el("p", { className: "page-lede", textContent: (sMeta.total_entries
        ? "Searching " + fmtInt(sMeta.total_entries) + " indexed declarations" + (((state.manifest || {}).stats || {}).total_decls > sMeta.total_entries ? " (of " + fmtInt(state.manifest.stats.total_decls) + " in total)" : "")
        : "Searching declarations") + ", plus findings, dossiers, blueprints and diagrams." }),
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
        el("h3", { textContent: "Type at least two characters" }),
        el("p", { textContent: "Search matches declaration names and modules, as well as findings, dossiers, blueprints and diagrams." })
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
        el("p", { textContent: "Try a shorter part of the name, or a different spelling." })
      ]));
      return;
    }

    const panel = el("div", { className: "panel search-results", style: { padding: "0" } });
    for (const h of showLocal.slice(0, 40)) {
      panel.appendChild(el("div", { className: "search-result-row" }, [
        el("div", { className: "sr-main" }, [
          el("div", { className: "sr-name", textContent: h.name }),
          el("div", { className: "sr-meta" }, [
            el("span", { className: "sr-type", textContent: SEARCH_TYPE_LABEL[h.type] || h.type }),
            el("span", { textContent: h.sub })
          ])
        ]),
        el("div", { className: "sr-acts" }, [
          el("a", { className: "btn sm", href: h.route, textContent: "Open ›" })
        ])
      ]));
    }

    for (const d of showDecls) {
      const cir = findAnyCircuitForSymbol(d.name, d.circuitPath);
      const ghUrl = d.mod ? buildGithubUrl(d.mod, d.line) : null;
      const acts = el("div", { className: "sr-acts" });
      acts.appendChild(el("a", { className: "btn sm primary", href: "#item/" + encodeURIComponent(d.name), textContent: "Inspect ›" }));
      if (ghUrl && d.line) {
        const peek = makeSrcButton(ghUrl, d.name);
        if (peek) acts.appendChild(peek);
      }
      if (cir) {
        acts.appendChild(el("button", {
          type: "button", className: "btn sm", textContent: "Diagram ›",
          onclick: () => navigate("#circuit/" + cir.mode + "/" + encodeURIComponent(cir.short || cir.name))
        }));
      }
      if (d.bpId) {
        acts.appendChild(el("button", {
          type: "button", className: "btn sm", textContent: "Blueprint ›",
          onclick: () => navigate("#blueprints/" + encodeURIComponent(d.bpId))
        }));
      }
      if (ghUrl) {
        acts.appendChild(el("a", { className: "btn sm", href: ghUrl, target: "_blank", rel: "noopener noreferrer", textContent: "Proof file ↗" }));
      }
      panel.appendChild(el("div", { className: "search-result-row" }, [
        el("div", { className: "sr-main" }, [
          el("div", { className: "sr-name", textContent: d.name }),
          el("div", { className: "sr-meta" }, [
            el("span", { className: "sr-type", textContent: d.kind + (d.live ? "" : " · unreachable") }),
            d.dom > 0 ? el("span", { title: "Declarations reachable only through this one (dominator subtree)", textContent: fmtInt(d.dom) + " in subtree" }) : null,
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
  async function handleRoute(ev) {
    const keepScroll = Boolean(ev && ev.keepScroll);
    const r = parseHash();
    updateNavHighlight(r.tab);
    closeProjectMenu();
    if (!state.manifest) {
      if (state.registry && state.booted) {
        state.route = r;
        updateCrumbs(r);
        await renderProjectsHome();
      }
      return;
    }
    state.route = r;
    closeSourceDrawer();
    if (state.rail.mobileOpen) { state.rail.mobileOpen = false; applyRailVisibility(); }
    updateCrumbs(r);
    renderRail();
    document.body.classList.toggle("route-projects", r.tab === "projects");
    if (!keepScroll) window.scrollTo(0, 0);

    switch (r.tab) {
      case "overview": renderOverview(); break;
      case "circuit": await renderCircuitView(r.sub, r.arg); break;
      case "findings": await renderFindingsView(r.sub); break;
      case "dossiers": await renderDossiersView(r.sub, r.arg); break;
      case "blueprints": await renderBlueprintsView(r.sub); break;
      case "flirt": await renderFlirtView(); break;
      case "atlas": await renderAtlasView(r.sub); break;
      case "portability": await renderPortabilityView(); break;
      case "benchmarks": await renderBenchmarksView(); break;
      case "search": renderSearchView(r.sub); break;
      case "item": await renderItemView([r.sub, r.arg].filter(Boolean).join("/")); break;
      case "projects": await renderProjectsHome(); break;
      case "experiments": await renderExperimentsView(); break;
      default: renderOverview(); break;
    }

    if (r.selftest && !state.selftestRunning) {
      state.selftestRunning = true;
      await runSiteSelfTest();
    }
  }

  const FORBIDDEN_WORDING = /RH is proved|RH is proven|proves RH\b|RH has been proved|Riemann Hypothesis is proved/i;
  // Implementation vocabulary that must never leak into visible UI copy.
  const UI_SLOP_WORDING = /zero-cdn|lazy[- ]?fetch|lazy static|lazy-loaded|\bshards?\b|pre-rendered|leanre\.site|epistemic scope|genome atlas|hi-c|alien-proof|\bflirt\b|brainstorm|two-arm|personas|youtuber|guardrail|scratch telemetry|cli friction|tromp binder|licence|neighbour|colour|labelled|behaviour|analyse|\bcentre\b/i;

  // Visible chrome + view text, excluding authored Markdown bodies and data rows.
  function visibleUiText() {
    const parts = [document.title];
    const hdr = $(".topbar");
    if (hdr) parts.push(hdr.innerText || hdr.textContent || "");
    const ftr = $(".site-footer");
    if (ftr) parts.push(ftr.innerText || ftr.textContent || "");
    const main = $("#appMain");
    if (main) {
      const clone = main.cloneNode(true);
      clone.querySelectorAll(".md-body, .data-table tbody, .search-results, .twin-side-name, .twin-side-meta, .cir-chips-wrap, .doc-list, .dom-tree, .showcase-chips, .findings-cards, .island-grid, .bp-head, .bp-inspector, .overlap-table, .cir-inspector, .atlas-readout, .quiet-note, .tray-row, .map2d-detail, .item-head, .nb-strip, .item-body, .proj-card-tag, .proj-card h3, .exp-list, .lens-box, select").forEach((n) => n.remove());
      parts.push(clone.textContent || "");
      $$("input[placeholder]", main).forEach((i) => parts.push(i.getAttribute("placeholder") || ""));
    }
    return parts.join("\n");
  }

  async function runSourceViewerSelfTest(assert) {
    const blob = "https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L12-L14";
    const p = githubBlobToRaw(blob);
    assert(p && p.raw === "https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean" && p.line === 12 && p.lineEnd === 14,
      "githubBlobToRaw converts pinned blob URLs with line ranges");
    const bad = [
      "https://evil.example/leanprover-community/x/blob/main/a.lean",
      "http://github.com/a/b/blob/main/a.lean",
      "https://github.com.evil.example/a/b/blob/main/a.lean",
      "https://github.com/a/b/blob/main/../../x.lean",
      "https://github.com/a/b/blob/main/%2e%2e/x.lean",
      "https://github.com/a/b/tree/main/a.lean",
      "https://user@github.com/a/b/blob/main/a.lean",
      "javascript:alert(1)//github.com/a/b/blob/main/a.lean",
      "https://github.com/a/b/blob/main/a.lean?raw=1"
    ];
    assert(bad.every((u) => githubBlobToRaw(u) === null), "githubBlobToRaw rejects non-GitHub, traversal and malformed URLs");

    const st = { depth: 0, expectName: false };
    const toks = tokenizeLeanLine("theorem foo (h : x = 1) : True := by simp -- note", st);
    const clsOf = (txt) => (toks.find((t) => t[1] === txt) || [])[0];
    assert(clsOf("theorem") === "tok-kw" && clsOf("foo") === "tok-name" && clsOf("by") === "tok-tac" && clsOf("simp") === "tok-tac" && clsOf("1") === "tok-num" && clsOf("-- note") === "tok-com",
      "Lean tokenizer classifies keywords, names, tactics, numbers and comments");
    const st2 = { depth: 0, expectName: false };
    tokenizeLeanLine("/- open /- nested -/ still", st2);
    const t2 = tokenizeLeanLine("comment -/ def bar := \"s\" sorry", st2);
    assert(st2.depth === 0 && t2[0][0] === "tok-com" && t2.some((t) => t[0] === "tok-str") && t2.some((t) => t[0] === "tok-sorry"),
      "Lean tokenizer tracks nested block comments, strings and sorry across lines");

    const fixture = [
      "import Mathlib",
      "",
      "/-- A doc comment with <img src=x onerror=alert(1)> inside. -/",
      "theorem demo_target (n : Nat) : n + 0 = n := by",
      "  simp",
      "",
      "def <script>alert(2)</script> := 0"
    ].join("\n");
    const ok = await openSourcePeek({ url: "https://github.com/example-owner/example-repo/blob/0123456789abcdef0123456789abcdef01234567/Demo/Basic.lean#L4", title: "demo_target", _fixtureText: fixture });
    const drawer = $("#srcDrawer");
    const hl = drawer && drawer.querySelector(".src-line.hl");
    assert(ok && drawer && !drawer.hidden && hl && hl.dataset.line === "4" && !!drawer.querySelector(".src-line .tok-kw"),
      "source viewer renders a fixture with the target line highlighted");
    assert(drawer && !drawer.querySelector("img, script, [onerror]") && /onerror=alert/.test(drawer.textContent || ""),
      "source viewer renders file text as inert text (no HTML injection)");
    const gh = $("#srcGhBtn");
    assert(gh && gh.getAttribute("href") === "https://github.com/example-owner/example-repo/blob/0123456789abcdef0123456789abcdef01234567/Demo/Basic.lean#L4",
      "source viewer links to the pinned GitHub line");
    srcView.ctx = "full";
    rerenderSourcePanes();
    assert(drawer.querySelectorAll(".src-line").length === 7, "full-file context shows every line");
    srcView.ctx = "15";
    closeSourceDrawer();
    assert(drawer.hidden, "source viewer closes cleanly");

    await openSourceCompare(
      { url: "https://github.com/example-owner/example-repo/blob/main/A.lean#L1", title: "A", label: "A", _fixtureText: "theorem a : True := trivial" },
      { url: "", title: "Mathlib.foo", label: "B", fallbackUrl: "https://leanprover-community.github.io/mathlib4_docs/find/?pattern=foo#doc", fallbackLabel: "Mathlib docs ↗" }
    );
    assert(drawer.querySelectorAll(".src-pane").length === 2 && !!drawer.querySelector('.src-pane[data-pane="1"] .src-error') && !!drawer.querySelector('.src-pane[data-pane="0"] .src-line'),
      "side-by-side viewer renders one pane and a graceful error card for the other");
    closeSourceDrawer();

    const md = el("div");
    md.innerHTML = renderMarkdownBlockSafe("See [Main.lean:12](" + blob + ") and [docs](https://example.org/x).", "findings");
    const n = decorateLeanLinks(md);
    assert(n === 1 && md.querySelectorAll(".src-peek-btn").length === 1, "Markdown .lean links gain exactly one inline preview button");
  }

  async function runSiteSelfTest() {
    const checks = [];
    const assert = (cond, msg) => { checks.push({ ok: Boolean(cond), msg }); };

    // Record any request that leaves this origin while the self-test runs.
    const externalRequests = [];
    const origFetch = window.fetch;
    window.fetch = function (input, init) {
      try {
        const u = new URL(typeof input === "string" ? input : (input && input.url) || "", window.location.href);
        if (u.origin !== window.location.origin) externalRequests.push(u.href);
      } catch (_) { /* ignore */ }
      return origFetch.apply(this, arguments);
    };
    const slopHits = [];
    const checkSlop = (label) => {
      const txt = visibleUiText();
      const mm = txt.match(UI_SLOP_WORDING);
      if (mm) slopHits.push(label + ": \"" + mm[0] + "\"");
    };

    try {
    // 1. Manifest & initial load invariant
    const m = state.manifest;
    assert(m && m.schema === "leanre.site_manifest/1", "manifest schema is leanre.site_manifest/1");
    assert(state.loadedFiles.size <= 3, "initial load fetches at most 3 files (got " + state.loadedFiles.size + ")");
    assert(!$("#netBadge") && !$("#tab-search"), "header has no transfer badge and no duplicate search tab");

    // 2. XSS sanitizer checks (Markdown & SVG)
    const xssMd = renderMarkdownBlockSafe('<img src=x onerror=alert(1)> [bad](javascript:alert(1)) <script>alert(2)</script>', "findings");
    const mdDiv = el("div");
    mdDiv.innerHTML = xssMd;
    assert(
      !mdDiv.querySelector("script, img, [onerror], a"),
      "markdown renderer blocks raw HTML, onerror, and javascript: links"
    );
    const vDiv = el("div");
    vDiv.innerHTML = renderMarkdownBlockSafe("<details>\n<summary>Verify locally &amp; pinned anchors</summary>\n\n```bash\npython3 -c \"import sqlite3\"\n```\n\n- keep this anchor\n</details>", "findings", "findings/example.md");
    assert(!/sqlite3|python3/.test(vDiv.textContent) && /keep this anchor/.test(vDiv.textContent) && vDiv.querySelector('a[href="https://github.com/bohemian-miser/leanre/blob/main/findings/example.md"]') && /Verify locally & pinned/.test(vDiv.querySelector("summary").textContent),
      "\"Verify locally\" blocks hide local commands behind a link to the repository");
    const tmpDiv = el("div");
    mountSafeSvg(tmpDiv, '<svg xmlns="http://www.w3.org/2000/svg" width="100" height="40"><script>window.__xss=1</script><rect onclick="alert(1)" width="20" height="20"/></svg>');
    assert(!tmpDiv.querySelector("script") && !tmpDiv.querySelector("[onclick]"), "SVG DOMParser sanitizer strips <script> and on* handlers");

    // 3. Overview check
    renderOverview();
    const ovTxt = $("#appMain").textContent || "";
    assert(ovTxt.length > 60 && !/\[object Object\]/.test(ovTxt) && !FORBIDDEN_WORDING.test(ovTxt), "overview renders cleanly without [object Object] or forbidden wording");
    assert(!!$(".hero h1") && $$(".hero h1").length === 1 && !!$(".hero-note"), "overview hero has one title and a quiet scope note");
    checkSlop("overview");

    // 4. Diagrams (macro + dark/light + structure/theorem if present)
    if (m.circuits && m.circuits.macro) {
      updateNavHighlight("circuit");
      assert($$("#mainNav .nav-tab.active").length === 1 && !!$("#tab-circuit.active"), "exactly one nav tab is highlighted on Diagrams");
      await renderCircuitView("macro", "");
      assert(!!$("#cirStage svg"), "repository diagram mounts sanitized SVG");
      checkSlop("diagrams");
      applyTheme("light", true);
      assert(document.documentElement.getAttribute("data-theme") === "light", "light theme toggle works");
      applyTheme("dark", true);
      if (m.circuits.bundles && m.circuits.bundles.length) {
        await renderCircuitView("bundle", m.circuits.bundles[0].short || m.circuits.bundles[0].name);
        assert(!!$("#cirStage svg"), "structure diagram renders SVG");
      }
      if (m.circuits.theorems && m.circuits.theorems.length) {
        await renderCircuitView("theorem", m.circuits.theorems[0].short || m.circuits.theorems[0].name);
        assert(!!$("#cirStage svg"), "theorem diagram renders SVG");
      }
      updateNavHighlight("overview");
    }

    // 5. Remaining views (gracefully handle empty or populated)
    await renderFindingsView("");
    assert(($("#appMain").textContent || "").length > 20, "findings view renders");
    checkSlop("findings");
    await renderDossiersView("", "");
    assert(($("#appMain").textContent || "").length > 20, "dossiers view renders");
    checkSlop("dossiers");
    await renderBlueprintsView("");
    assert(($("#appMain").textContent || "").length > 20, "blueprints view renders");
    checkSlop("blueprints");
    await renderFlirtView();
    assert(($("#appMain").textContent || "").length > 20, "clusters view renders");
    checkSlop("clusters");
    if (m.assets && m.assets.atlas) {
      await renderAtlasView();
      const atlasTxt = $("#appMain").textContent || "";
      assert(!!$("#hicCanvas") && !!$("#syntenyCanvas") && !/\[object Object\]/.test(atlasTxt), "edge map renders both canvases cleanly");
      checkSlop("edge map");
    } else {
      const aTab = $("#tab-atlas");
      assert(!aTab || aTab.classList.contains("hidden"), "edge map tab hides cleanly when its data is absent");
    }
    await renderPortabilityView();
    assert(($("#appMain").textContent || "").length > 20, "islands view renders");
    checkSlop("islands");
    await renderBenchmarksView();
    assert(($("#appMain").textContent || "").length > 20, "benchmarks view renders");
    checkSlop("benchmarks");

    // 6. Search index test
    const shardNames = getSearchShardNames();
    const firstShard = shardNames.find((s) => s !== "_" && s.length >= 2) || shardNames[0] || "ma";
    renderSearchView(firstShard);
    await runSearchQuery();
    assert(!!$("#globalSearchInput"), "search view renders and runs a query");
    checkSlop("search");

    // 7. Projects, outline rail, breadcrumbs, lenses, inspector, experiments
    const reg = parseRegistry({ schema: "leanre.projects_registry/1", projects: [
      { slug: "good-one", path: "p/good-one", title: "Good" },
      { slug: "bad", path: "p/../../etc" },
      { slug: "../evil", path: "p/x" },
      { slug: "root-one", path: "." }
    ] });
    assert(reg && reg.projects.length === 2 && reg.projects[0]._base === "p/good-one/" && reg.projects[1]._base === "",
      "projects registry parser keeps safe entries and rejects traversal");
    if (state.registry) {
      await renderProjectsHome();
      assert($$(".proj-card").length >= 1 && !!$(".add-proof"), "projects home lists proofs and explains how to add one");
      checkSlop("projects");
      assert(!!$("#projBtn") && !$("#projMenu").querySelector("script"), "project switcher is present");
    }
    renderRail();
    const railModesNow = railModes();
    if (railModesNow.length) {
      assert(!$("#outlineRail").hidden && $$("#outlineRail .rail-row").length > 0, "outline rail lists the proof spine");
    }
    updateCrumbs({ tab: "findings", sub: (m.findings && m.findings[0] && m.findings[0].slug) || "" });
    assert($$("#crumbBar .crumb").length >= 2 || !(m.findings || []).length, "breadcrumb bar shows the path to the current page");
    const linkFrag = renderLeanTokens(tokenizeLeanLine("exact foo_bar h", { depth: 0, expectName: false }), new Map([["foo_bar", "Ns.foo_bar"]]));
    const linkHost = el("div", null, [linkFrag]);
    const symA = linkHost.querySelector("a.src-sym");
    assert(symA && symA.getAttribute("href") === "#item/Ns.foo_bar" && linkHost.querySelectorAll("a").length === 1, "source viewer links only verified symbol names");

    const lenses = overviewLenses();
    renderOverview();
    if (lenses.some(([k]) => k === "diagram")) {
      state.overviewLens = "diagram";
      await renderOverviewLens($("#lensBody"), el("div"));
      assert(!!$("#lensBody .lens-box svg"), "overview diagram lens mounts the repository map");
      state.overviewLens = "spine";
    }

    const probeName = (((state.outline && state.outline.spine) || [])[0] || {}).name
      || ((m.overview_pillars || []).find((p) => p.decl) || {}).decl
      || ((m.circuits && m.circuits.theorems && m.circuits.theorems[0]) || {}).name || "";
    if (probeName) {
      state.route = { tab: "item", sub: probeName, arg: "" };
      state.item.view = "summary";
      await renderItemView(probeName);
      assert(!!$(".item-title") && ($(".item-title").textContent || "").length > 0 && !!$(".item-tabs"), "declaration inspector renders for " + shortName(probeName));
      checkSlop("item");
    }

    if (m.assets && m.assets.atlas) {
      await renderAtlasView("");
      const cv = $("#hicCanvas");
      if (cv) {
        const rc = cv.getBoundingClientRect();
        cv.dispatchEvent(new MouseEvent("click", { bubbles: true, clientX: rc.left + rc.width * 0.3, clientY: rc.top + rc.height * 0.3 }));
        assert(!$("#hicTray").hidden && $$("#hicTray .tray-row").length > 0, "clicking the contact map opens a tray of declarations and edges");
      }
    } else if (m.assets && m.assets.module_matrix) {
      await renderAtlasView("");
      assert(!!$("#moduleMatrixCanvas"), "source-only projects show the module matrix");
    }
    if (m.assets && m.assets.embedding_2d) {
      if (!$("#map2dSection")) await renderAtlasView("map");
      let canvas = null;
      for (let i = 0; i < 60 && !canvas; i++) { canvas = $("#map2dSection .map2d-canvas"); if (!canvas) await new Promise((r) => setTimeout(r, 50)); }
      assert(!!canvas, "2D map renders");
      if (canvas) {
        const rc = canvas.getBoundingClientRect();
        let hit = false;
        for (let gy = 0.1; gy < 0.95 && !hit; gy += 0.05) {
          for (let gx = 0.1; gx < 0.95 && !hit; gx += 0.05) {
            const pe = { bubbles: true, clientX: rc.left + rc.width * gx, clientY: rc.top + rc.height * gy, button: 0, pointerId: 7 };
            canvas.dispatchEvent(new PointerEvent("pointerdown", pe));
            canvas.dispatchEvent(new PointerEvent("pointerup", pe));
            hit = !!$("#map2dSection .map2d-detail .cir-ins-title");
          }
        }
        assert(hit, "clicking a 2D map dot shows its details and neighbors");
      }
    }
    renderExperimentsView();
    assert(!$("#tab-experiments") && !!$("#appMain .empty-card a[href='#atlas']"), "old experiments route shows a short pointer instead of the study");
    const hiddenActive = $$("#mainNav .nav-tab.active.hidden").length;
    assert(hiddenActive === 0, "no hidden tab is highlighted");

    // 7b. Math typography, 2D map controls, light canvases, favicon
    assert(plainTextFromTex("$\\operatorname{Re}(s) > 1/2$ except at $s=1$") === "Re(s) > 1/2 except at s=1" && plainTextFromTex("costs $5 and $10") === "costs $5 and $10" && plainTextFromTex("$\\mathrm{Ш}^1$ over $\\mathbb{Q}$") === "Ш¹ over ℚ",
      "TeX is converted to plain text without touching prices");
    const texSpan = renderTexSafe("x^{2} + \\chi_{1}");
    assert(texSpan.querySelector("sup") && texSpan.querySelector("sub") && /χ/.test(texSpan.textContent) && !texSpan.querySelector("script"), "TeX renders to DOM with sup/sub elements");
    const mdMath = el("div");
    mdMath.innerHTML = renderMarkdownBlockSafe("Here $\\operatorname{Re}(s) > \\tfrac{1}{2}$ holds.", "findings");
    assert(/Re\(s\) > 1\/2/.test(mdMath.textContent) && !mdMath.textContent.includes("$") && mdMath.querySelector(".math-inline"), "long inline math in Markdown renders");
    const fav = document.querySelector('link[rel="icon"]');
    assert(fav && /^data:image\/svg\+xml/.test(fav.getAttribute("href") || ""), "favicon is inline (no extra request)");
    if (m.assets && m.assets.atlas) {
      applyTheme("light", false);
      await renderAtlasView("");
      const hc = $("#hicCanvas");
      const px = hc && hc.getContext("2d").getImageData(2, 2, 1, 1).data;
      assert(px && px[0] > 200 && px[1] > 200, "contact map paints a light background in the light theme");
      applyTheme("dark", false);
    }
    if (m.assets && m.assets.embedding_2d) {
      const host2 = $("#map2dSection") || (await renderAtlasView("map"), $("#map2dSection"));
      for (let i = 0; i < 60 && !(host2 && host2._map2d); i++) await new Promise((r) => setTimeout(r, 50));
      const api = host2 && host2._map2d;
      if (api) {
        api.resetView();
        const target = api.pts.slice().sort((x, y) => y.dom - x.dom)[0];
        api.runFind(target.short);
        assert(api.state.sel === target.i && api.state.zoom >= 5.9, "2D map search jumps to and zooms on a declaration");
        const zoomTxt = ($("#map2dSection .map-zoom") || {}).textContent || "";
        assert(/×$/.test(zoomTxt) && parseFloat(zoomTxt) >= 5.9, "2D map shows the zoom level");
        const pill = $("#map2dSection .map-pill");
        if (pill) {
          pill.click();
          await new Promise((r) => setTimeout(r, 280));
          assert(api.state.hidden.size === 1 && $("#map2dSection .map-pill.off"), "legend pills hide a group when clicked");
          $("#map2dSection .map-pill.off").click();
          await new Promise((r) => setTimeout(r, 280));
        }
        api.resetView();
        assert(Math.abs(api.state.zoom - 1) < 0.01, "2D map reset returns to the whole map");
        assert(/Theta & local matching|Galois/.test(($("#map2dSection .map-legend") || {}).textContent || "") || !(m.repo_name === "riemann-hypothesis"), "2D map legend uses plain part names");
      }
    }

    // 8. Live source viewer (fixture only; no network)
    await runSourceViewerSelfTest(assert);

    assert(slopHits.length === 0, "no implementation jargon in visible UI text" + (slopHits.length ? " (" + slopHits.join("; ") + ")" : ""));
    assert(externalRequests.length === 0, "no external network requests during self-test" + (externalRequests.length ? " (" + externalRequests.slice(0, 3).join(", ") + ")" : ""));
    } catch (err) {
      assert(false, "self-test threw: " + String((err && err.message) || err));
    } finally {
      window.fetch = origFetch;
    }

    // Return to overview with pass/fail banner
    renderOverview();
    const failed = checks.filter((c) => !c.ok);
    const result = {
      pass: failed.length === 0,
      passed: checks.length - failed.length,
      failed: failed.length,
      total: checks.length,
      loaded_bytes: state.loadedBytes,
      loaded_files: state.loadedFiles.size,
      external_requests: externalRequests.length,
      checks
    };
    window.__LEANRE_SITE_SELFTEST_RESULT = result;
    const banner = el("div", {
      id: "selftestBanner",
      className: "selftest-banner" + (result.pass ? "" : " fail"),
      textContent: (result.pass ? "SELFTEST PASS" : "SELFTEST FAIL") + " — " + result.passed + "/" + result.total + " checks (" + formatBytes(result.loaded_bytes) + ", " + result.loaded_files + " files)" + (failed.length ? " | FAIL: " + failed.map((f) => f.msg).join("; ") : "")
    });
    const main = $("#appMain");
    if (main) main.prepend(banner);
    return result;
  }

  window.__LEANRE_SITE_SELFTEST = runSiteSelfTest;
  window.leanreSource = { githubBlobToRaw, openSourcePeek, openSourceCompare, close: closeSourceDrawer };

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
    const railBtn = $("#railToggleBtn");
    if (railBtn) railBtn.addEventListener("click", () => toggleRail());
    document.addEventListener("click", (ev) => {
      const sw = $("#projSwitch");
      if (sw && !sw.contains(ev.target)) closeProjectMenu();
      if (state.rail.mobileOpen) {
        const rail = $("#outlineRail");
        const btn = $("#railToggleBtn");
        if (rail && !rail.contains(ev.target) && btn && !btn.contains(ev.target)) toggleRail(false);
      }
    });
    document.addEventListener("keydown", (ev) => {
      if (ev.key === "Escape") {
        closeProjectMenu();
        if (state.rail.mobileOpen) toggleRail(false);
      }
    });
    let resizeT = null;
    window.addEventListener("resize", () => {
      clearTimeout(resizeT);
      resizeT = setTimeout(applyRailVisibility, 120);
    });
  }

  async function boot() {
    initTheme();
    initRailState();
    wireGlobalControls();
    updateNavHighlight(parseHash().tab);
    // projects.json is read only when we know a gallery exists: inside one
    // (?p=<slug>), or when the manifest names a registry.
    const wanted = new URLSearchParams(window.location.search).get("p") || "";
    if (wanted) state.registry = await loadRegistry();
    const entry = wanted && state.registry ? state.registry.projects.find((p) => p.slug === wanted) : null;
    if (entry) state.base = entry._base;
    try {
      state.manifest = await fetchJson("./manifest.json");
      if (!state.base) state.rootManifest = state.manifest;
      if (!wanted) {
        const hasKey = Object.prototype.hasOwnProperty.call(state.manifest, "registry");
        if (!hasKey || state.manifest.registry) state.registry = await loadRegistry();
      }
      populateChromeFromManifest();
      renderProjectSwitcher();
      state.booted = true;
      await handleRoute();
      // Upgrade the outline once the page is idle (same-origin data only).
      const idle = window.requestIdleCallback || ((fn) => setTimeout(fn, 1200));
      if (state.manifest.assets && state.manifest.assets.outline) {
        idle(() => { ensureOutline().then((o) => { if (o && state.rail.mode === "spine") renderRail(); }); });
      }
    } catch (err) {
      if (!state.registry && !wanted) state.registry = await loadRegistry();
      if (state.registry) {
        // A gallery root without its own project: show the list of proofs.
        state.manifest = null;
        state.booted = true;
        $$("#mainNav .nav-tab").forEach((b) => b.classList.add("hidden"));
        renderProjectSwitcher();
        renderRail();
        await handleRoute();
        return;
      }
      const main = $("#appMain");
      if (main) {
        clearEl(main);
        main.appendChild(el("div", { className: "empty-card" }, [
          el("h3", { textContent: "Could not load the site data" }),
          el("p", { textContent: "This page needs to be served over HTTP (for example `python3 -m http.server`) or from GitHub Pages. Details: " + String(err.message || err) })
        ]));
      }
    }
  }

  document.addEventListener("DOMContentLoaded", boot);
})();
