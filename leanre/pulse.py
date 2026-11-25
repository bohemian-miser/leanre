#!/usr/bin/env python3
"""leanre.pulse — Fast, corpus-agnostic forensic pulse & structure telemetry (`leanre.pulse/1`).

Clean-room Python stdlib module that walks any Lean 4 source tree (optionally
enriched with a `kernel.db` from `lean4export`) and emits a compact `pulse.json`
summary (~50–150 KB, zero `.lean` proof bodies) covering:

  * Import-reachability vs. kernel-liveness contrast (catches files imported by
    the build DAG that emit 0 live kernel declarations).
  * Module kind breakdown (`math`, `restate` single-theorem forwarding shims,
    `imports`-only barrels, `setup` modules).
  * Stacked length-bucket histograms (lines) & cross-file neighbor `zlib`
    dictionary-compression repetition histograms (`math` vs. `restate`).
  * Notation scope breakdown (`local` vs `scoped` vs `global`) and macro/syntax/elab
    counts, with exact line numbers for top files.
  * Numeric literal & digit-density audit (checks for hidden lookup tables).
  * Tactic/keyword usage counts (`have`, `rw`, `exact`, `simp`, `decide`,
    `native_decide`, `sorry`, etc.) & whole-`Mathlib` import share.
  * Longest intra-project import chain (DAG topological DP) + exact transitive
    dependents (bitwise DP over the reverse import DAG).
  * Top directory heat aggregates (for linked minimap / treemap highlighting) and
    clickable sample module jump-lists per diagnostic tag.

Zero raw proof bodies and zero absolute host paths are written to outputs.
License: AGPL-3.0-or-later.
"""
from __future__ import annotations

import argparse
import collections
import concurrent.futures
import datetime
import json
import os
import re
import sqlite3
import statistics
import sys
import time
import zlib
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

PULSE_SCHEMA = "leanre.pulse/1"

_IMPORT_RE = re.compile(r"^\s*(?:(?:public|private)\s+)?import\s+(?:all\s+)?([^\s;]+)\s*$")
_DECL_HEAD_RE = re.compile(
    r"^(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local|meta|@\[[^\]]*\])\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque|example)\b"
)
_NOTATION_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(local|scoped)\s+)?(?:(private|protected)\s+)?"
    r"(?:infixl|infixr|infix|prefix|postfix|notation)\b"
)
_MACRO_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:local|scoped|private|protected)\s+)*"
    r"(macro_rules|macro|syntax_cat|declare_syntax_cat|syntax|elab_rules|elab)\b"
)
_HEARTBEAT_RE = re.compile(r"\bset_option\s+maxHeartbeats\s+(\d+)")
_RESTATE_BODY_RE = re.compile(
    r":=\s*(?:by\s*\n?\s*(?:first\s*\|\s*exact|exact|rfl|assumption|trivial)\b|[A-Za-z_][A-Za-z0-9_.]*(?:\s*$|[\s\n]+$))"
)
_FIRST_EXACT_RE = re.compile(r":=\s*by\s+first\s*\|\s*exact\b")
_NUM_LIT_RE = re.compile(r"(?<![A-Za-z0-9_'])\d+(?:\.\d+)?(?![A-Za-z0-9_'])")
_DECIDE_KERNEL_RE = re.compile(r"\bdecide\s*\+\s*kernel\b|\bkernel_decide\b")
_NATIVE_DECIDE_RE = re.compile(r"\bnative_decide\b")
_SORRY_RE = re.compile(r"(?<![A-Za-z0-9_'])(?:sorry|admit)(?![A-Za-z0-9_'])")
_IDENT_RE = re.compile(r"(?<![A-Za-z0-9_'])([A-Za-z_][A-Za-z0-9_']*)")

_TACTIC_KEYS: Tuple[str, ...] = (
    "have",
    "rw",
    "exact",
    "simp",
    "obtain",
    "rfl",
    "refine",
    "intro",
    "apply",
    "let",
    "cases",
    "rcases",
    "omega",
    "ring",
    "linarith",
    "nlinarith",
    "norm_num",
    "calc",
    "ext",
    "constructor",
    "decide",
    "grind",
    "aesop",
    "native_decide",
    "sorry",
)
_TACTIC_SET: Set[str] = set(_TACTIC_KEYS)

_LENGTH_BINS: Tuple[Tuple[str, int, int], ...] = (
    ("1–3", 1, 3),
    ("4–9", 4, 9),
    ("10–31", 10, 31),
    ("32–99", 32, 99),
    ("100–315", 100, 315),
    ("316–999", 316, 999),
    ("1,000+", 1000, 10**9),
)

_SKEPTIC_TERMS: Tuple[Tuple[str, str, re.Pattern[str]], ...] = (
    ("Stepanov", "Stepanov (auxiliary polynomial method)", re.compile(r"Stepanov", re.I)),
    ("HarderNarasimhan", "Harder–Narasimhan filtration", re.compile(r"Harder[-_ ]?Narasimhan", re.I)),
    ("Vandiver", "Vandiver conjecture / criterion", re.compile(r"Vandiver", re.I)),
    ("WeilBound", "Weil bound / Kloosterman reference", re.compile(r"WeilBound")),
    ("Siegel", "Siegel / Landau–Siegel", re.compile(r"\bSiegel", re.I)),
    ("Theta", "Theta / Shimura / Weil lift", re.compile(r"Theta")),
    ("Eisenstein", "Eisenstein series / congruence", re.compile(r"Eisenstein", re.I)),
    ("Satake", "Satake parameter / isomorphism", re.compile(r"Satake", re.I)),
    ("Arakelov", "Arakelov covolume / height", re.compile(r"Arakelov", re.I)),
    ("Frobenius", "Frobenius / ramification", re.compile(r"Frobenius", re.I)),
    ("Kodaira", "Kodaira–Spencer map", re.compile(r"Kodaira", re.I)),
    ("Galois", "Galois representation / cohomology", re.compile(r"Galois", re.I)),
    ("Selberg", "Selberg trace / class", re.compile(r"Selberg", re.I)),
    ("CellSystem", "Cell system / blow-up", re.compile(r"CellSystem|BlowUp|blowup", re.I)),
    ("Euler", "Euler / Navier–Stokes equation", re.compile(r"NavierStokes|Euler", re.I)),
    ("ExplicitFormula", "Explicit formula", re.compile(r"ExplicitFormula", re.I)),
)

_BOILERPLATE_PREFIXES = (
    "import ",
    "public import ",
    "open ",
    "namespace ",
    "end ",
    "section",
    "variable ",
    "universe ",
    "set_option ",
    "attribute ",
    "noncomputable section",
)


def strip_lean_comments_and_strings(text: str) -> Tuple[str, int]:
    """Strip Lean 4 nested `/- ... -/` block comments & `--` line comments cleanly.

    Returns ``(code_text, comment_bytes)`` preserving line count (`\\n` newlines)
    so 1-based line numbers stay identical to the source file.
    """
    out: List[str] = []
    n = len(text)
    i = 0
    block_depth = 0
    in_str = False
    comment_chars = 0
    while i < n:
        ch = text[i]
        if block_depth > 0:
            if ch == "/" and i + 1 < n and text[i + 1] == "-":
                block_depth += 1
                comment_chars += 2
                i += 2
            elif ch == "-" and i + 1 < n and text[i + 1] == "/":
                block_depth -= 1
                comment_chars += 2
                i += 2
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                comment_chars += 1
                i += 1
            continue
        if in_str:
            out.append(" " if ch != "\n" else "\n")
            if ch == "\\" and i + 1 < n:
                out.append(" " if text[i + 1] != "\n" else "\n")
                i += 2
                continue
            if ch == '"':
                in_str = False
            i += 1
            continue
        if ch == "/" and i + 1 < n and text[i + 1] == "-":
            block_depth = 1
            comment_chars += 2
            i += 2
            continue
        if ch == "-" and i + 1 < n and text[i + 1] == "-":
            j = text.find("\n", i)
            if j < 0:
                comment_chars += n - i
                break
            comment_chars += j - i
            out.append("\n")
            i = j + 1
            continue
        if ch == '"':
            in_str = True
            out.append('"')
            i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out), comment_chars


def _dir_worker(task: Tuple[str, str, List[Tuple[str, str]]]) -> List[Dict[str, Any]]:
    """Scan all sorted `.lean` files inside one directory for neighbor `zdict` & metrics."""
    src_dir, dir_rel, items = task
    prev_raw: Optional[bytes] = None
    out: List[Dict[str, Any]] = []
    for mod_name, rel_path in items:
        fpath = os.path.join(src_dir, rel_path)
        try:
            with open(fpath, "rb") as fh:
                raw = fh.read()
        except OSError:
            continue
        n_bytes = len(raw)
        text = raw.decode("utf-8", errors="replace")
        raw_lines = text.splitlines()
        n_lines = len(raw_lines) if raw_lines else (1 if raw else 0)

        # Standalone zlib size and conditional neighbor-primed zlib size (`zdict`)
        c_self = zlib.compressobj(level=6, method=zlib.DEFLATED, wbits=15)
        z_self = len(c_self.compress(raw) + c_self.flush())
        if prev_raw is not None and z_self > 0:
            zdict = prev_raw[-32768:]
            c_cond = zlib.compressobj(level=6, method=zlib.DEFLATED, wbits=15, zdict=zdict)
            z_cond = len(c_cond.compress(raw) + c_cond.flush())
            rep_pct = max(0, min(100, int(round(100.0 - 100.0 * z_cond / max(z_self, 1)))))
        else:
            rep_pct = -1
        prev_raw = raw

        code, comment_chars = strip_lean_comments_and_strings(text)
        code_lines = code.splitlines()

        imports: List[str] = []
        imports_mathlib = False
        decl_count = 0
        decl_kinds: Dict[str, int] = {}
        body_nonempty_lines = 0
        non_import_lines: List[str] = []
        local_not = 0
        scoped_not = 0
        global_not = 0
        first_scoped_line = 0
        first_global_line = 0
        first_local_line = 0
        macro_cnt = 0
        first_macro_line = 0
        max_hb = 0
        digit_chars = 0
        nonspace_code_chars = 0
        num_lits = 0
        long_lits = 0
        first_long_lit_line = 0

        for lno, ln in enumerate(code_lines, 1):
            st = ln.strip()
            if not st:
                continue
            m_imp = _IMPORT_RE.match(st)
            if m_imp:
                target = m_imp.group(1)
                if target == "Mathlib":
                    imports_mathlib = True
                imports.append(target)
                continue
            body_nonempty_lines += 1
            non_import_lines.append(st)

            m_decl = _DECL_HEAD_RE.match(st)
            if m_decl:
                dk = m_decl.group(1)
                decl_count += 1
                decl_kinds[dk] = decl_kinds.get(dk, 0) + 1

            m_not = _NOTATION_RE.match(st)
            if m_not:
                scope = m_not.group(1) or ""
                if scope == "local":
                    local_not += 1
                    if not first_local_line:
                        first_local_line = lno
                elif scope == "scoped":
                    scoped_not += 1
                    if not first_scoped_line:
                        first_scoped_line = lno
                else:
                    global_not += 1
                    if not first_global_line:
                        first_global_line = lno

            if _MACRO_RE.match(st):
                macro_cnt += 1
                if not first_macro_line:
                    first_macro_line = lno

            if "maxHeartbeats" in st:
                m_hb = _HEARTBEAT_RE.search(st)
                if m_hb:
                    v = int(m_hb.group(1))
                    if v > max_hb:
                        max_hb = v
                continue  # skip numeric digits of set_option maxHeartbeats

            # Count code digits excluding imports & set_option maxHeartbeats lines
            for ch in st:
                if not ch.isspace():
                    nonspace_code_chars += 1
                    if "0" <= ch <= "9":
                        digit_chars += 1
            for m_num in _NUM_LIT_RE.finditer(st):
                num_lits += 1
                tok = m_num.group(0).replace(".", "")
                if len(tok) >= 7:
                    long_lits += 1
                    if not first_long_lit_line:
                        first_long_lit_line = lno

        # Classify kind: imports | restate | setup | math
        has_decide_kernel = bool(_DECIDE_KERNEL_RE.search(code))
        has_native_decide = bool(_NATIVE_DECIDE_RE.search(code))
        has_sorry = bool(_SORRY_RE.search(code))

        # Check for single-theorem restatement shim (`first | exact` or thin single-decl alias)
        is_restate = False
        if body_nonempty_lines == 0:
            kind = "imports"
        elif decl_count == 0:
            non_boil = [s for s in non_import_lines if not s.startswith(_BOILERPLATE_PREFIXES) and s != "end"]
            kind = "imports" if not non_boil else "setup"
        elif decl_count == 1 and (decl_kinds.get("theorem", 0) + decl_kinds.get("lemma", 0)) == 1:
            if _FIRST_EXACT_RE.search(code):
                kind = "restate"
                is_restate = True
            else:
                kind = "math"
        else:
            kind = "math"

        # Tactic token counts (code only, comments stripped)
        tac_counts: Dict[str, int] = {}
        for m_id in _IDENT_RE.finditer(code):
            w = m_id.group(1)
            if w in _TACTIC_SET:
                tac_counts[w] = tac_counts.get(w, 0) + 1

        # High-signal concept term hits inside own module path or non-import body
        body_code = mod_name + "\n" + "\n".join(non_import_lines)
        term_mask = 0
        for idx, (_key, _lbl, rx) in enumerate(_SKEPTIC_TERMS):
            if rx.search(body_code):
                term_mask |= (1 << idx)

        digit_pct = (100.0 * digit_chars / nonspace_code_chars) if nonspace_code_chars > 0 else 0.0

        out.append({
            "mod": mod_name,
            "rel": rel_path,
            "dir": dir_rel,
            "bytes": n_bytes,
            "z_bytes": z_self,
            "lines": n_lines,
            "comment_chars": comment_chars,
            "rep": rep_pct,
            "kind": kind,
            "restate": is_restate,
            "decls": decl_count,
            "decl_kinds": decl_kinds,
            "imports": imports,
            "imports_mathlib": imports_mathlib,
            "not_local": local_not,
            "not_scoped": scoped_not,
            "not_global": global_not,
            "not_lines": (first_local_line, first_scoped_line, first_global_line),
            "macros": macro_cnt,
            "macro_line": first_macro_line,
            "hb": max_hb,
            "num_lits": num_lits,
            "long_lits": long_lits,
            "long_line": first_long_lit_line,
            "digit_pct": round(digit_pct, 2),
            "nonspace": nonspace_code_chars,
            "digits": digit_chars,
            "tactics": tac_counts,
            "term_mask": term_mask,
            "decide_kernel": has_decide_kernel,
            "native_decide": has_native_decide,
            "sorry": has_sorry,
        })
    return out


def _length_bin_idx(n_lines: int) -> int:
    for i, (_lbl, lo, hi) in enumerate(_LENGTH_BINS):
        if lo <= n_lines <= hi:
            return i
    return 0


def _compute_import_dag_metrics(
    mods: List[str],
    edges_out: Dict[int, List[int]],
    skip_bits: bool = False,
) -> Tuple[List[int], List[int], List[int], List[int]]:
    """Return ``(longest_chain_indices, in_deg, trans_dependents, longest_depth)``.

    Edge direction: ``src -> dst`` means ``src`` imports ``dst`` (so ``src``
    depends on ``dst``). ``longest_chain`` begins at a leaf module importing no
    project module and ends at the highest-depth root module.
    ``trans_dependents[dst]`` is the exact number of modules ``u != dst`` from
    which ``dst`` is reachable via intra-project imports.
    """
    n = len(mods)
    if n == 0:
        return [], [], [], []
    out_cnt = [0] * n
    rev_in: List[List[int]] = [[] for _ in range(n)]  # dst -> list of importers (src)
    for src, dsts in edges_out.items():
        if not dsts:
            continue
        uniq = list(dict.fromkeys(dsts))
        out_cnt[src] = len(uniq)
        for dst in uniq:
            rev_in[dst].append(src)
    in_deg = [len(rev_in[i]) for i in range(n)]

    # Bottom-up topological order (leaves first: out_cnt == 0 -> roots last)
    rem_out = out_cnt[:]
    q = collections.deque(i for i in range(n) if rem_out[i] == 0)
    topo: List[int] = []
    depth = [1] * n
    pred = [-1] * n
    while q:
        u = q.popleft()
        topo.append(u)
        du = depth[u]
        for importer in rev_in[u]:
            if du + 1 > depth[importer]:
                depth[importer] = du + 1
                pred[importer] = u
            rem_out[importer] -= 1
            if rem_out[importer] == 0:
                q.append(importer)

    # Reconstruct longest import chain (leaf -> ... -> root)
    best_u = 0
    for i in range(n):
        if depth[i] > depth[best_u] or (depth[i] == depth[best_u] and mods[i] < mods[best_u]):
            best_u = i
    chain_rev: List[int] = []
    seen_c: Set[int] = set()
    cur = best_u
    while cur >= 0 and cur not in seen_c:
        seen_c.add(cur)
        chain_rev.append(cur)
        cur = pred[cur]
    chain = list(reversed(chain_rev))

    # Reverse topo-order exact transitive dependent count via Python int bitsets.
    # For very large cyclic edges or skip_bits, fall back gracefully.
    trans_dep = [0] * n
    if not skip_bits and len(topo) == n:
        # Process roots first (`reversed(topo)`): each bit marks an ancestor importer.
        # Assign compact bit order closest to roots first, freeing each parent bitset once
        # all its imported children have read it.
        rev_order = list(reversed(topo))
        rem_need = [0] * n
        for src, dsts in edges_out.items():
            rem_need[src] = len(set(dsts))
        # Direct storage for reachable importer bitmasks
        bits: Dict[int, int] = {}
        for pos, u in enumerate(rev_order):
            mask = 0
            for importer in rev_in[u]:
                ib = bits.get(importer, 0)
                mask |= ib
                rem_need[importer] -= 1
                if rem_need[importer] <= 0 and importer in bits:
                    del bits[importer]
            trans_dep[u] = mask.bit_count()
            # Only add u's own bit if some other module will consume it
            if out_cnt[u] > 0:
                bits[u] = mask | (1 << pos)
    else:
        for i in range(n):
            trans_dep[i] = in_deg[i]

    return chain, in_deg, trans_dep, depth


def _load_kernel_live_modules(kernel_db: Optional[str]) -> Optional[Dict[str, int]]:
    """Return mapping ``module_name -> live_decl_count`` from `kernel.db`, if present."""
    if not kernel_db or not os.path.isfile(kernel_db) or os.path.islink(kernel_db):
        return None
    real = os.path.realpath(kernel_db)
    conn = sqlite3.connect(f"file:{real}?mode=ro", uri=True)
    try:
        conn.execute("PRAGMA query_only=1")
        has_dm = conn.execute(
            "SELECT 1 FROM sqlite_master WHERE type='table' AND name='decl_module'"
        ).fetchone()
        if not has_dm:
            return None
        out: Dict[str, int] = {}
        for mod, cnt in conn.execute(
            "SELECT dm.module, COUNT(*) "
            "FROM decl_module dm JOIN decls d ON d.id = dm.decl_id "
            "WHERE d.live_mask > 0 AND dm.module IS NOT NULL AND dm.module != '' "
            "GROUP BY dm.module"
        ):
            out[str(mod)] = int(cnt)
        return out
    finally:
        conn.close()


def _top_ns_of(mod_name: str, depth: int = 1) -> str:
    parts = mod_name.split(".")
    if len(parts) <= depth:
        return parts[0] if parts else mod_name
    return ".".join(parts[:depth])


def _folder_path_of(rel_path: str, depth: int = 2) -> str:
    parts = [p for p in rel_path.replace("\\", "/").split("/")[:-1] if p]
    if not parts:
        return "(root)"
    return "/".join(parts[:depth])


def build_pulse(
    src_dir: str,
    *,
    slug: str = "project",
    kernel_db: Optional[str] = None,
    workers: int = 0,
    compute_trans_deps: bool = True,
    max_samples: int = 30,
) -> Dict[str, Any]:
    """Scan ``src_dir`` and return a compact `leanre.pulse/1` JSON-ready dict."""
    t0 = time.monotonic()
    src_real = os.path.realpath(src_dir)
    if not os.path.isdir(src_real):
        raise FileNotFoundError(f"Source directory not found: {src_dir}")

    # Group `.lean` files deterministically by directory for neighbor-zdict compression
    by_dir: Dict[str, List[Tuple[str, str]]] = collections.defaultdict(list)
    for root, dirs, files in os.walk(src_real):
        dirs[:] = sorted(d for d in dirs if not d.startswith(".") and d != ".lake")
        for fn in sorted(files):
            if not fn.endswith(".lean"):
                continue
            full = os.path.join(root, fn)
            if os.path.islink(full):
                continue
            rel = os.path.relpath(full, src_real).replace(os.sep, "/")
            mod = rel[:-5].replace("/", ".")
            dir_rel = os.path.dirname(rel).replace(os.sep, "/") or "."
            by_dir[dir_rel].append((mod, rel))

    tasks: List[Tuple[str, str, List[Tuple[str, str]]]] = [
        (src_real, d, sorted(v, key=lambda x: x[1])) for d, v in sorted(by_dir.items())
    ]

    if workers <= 0:
        total_files_est = sum(len(t[2]) for t in tasks)
        if total_files_est < 200:
            workers = 1
        else:
            workers = min(32, max(2, (os.cpu_count() or 4)))

    records: List[Dict[str, Any]] = []
    if workers <= 1 or len(tasks) <= 2:
        for t in tasks:
            records.extend(_dir_worker(t))
    else:
        with concurrent.futures.ProcessPoolExecutor(max_workers=workers) as ex:
            for chunk in ex.map(_dir_worker, tasks, chunksize=max(1, min(64, len(tasks) // (workers * 2) or 1))):
                records.extend(chunk)

    records.sort(key=lambda r: r["mod"])
    n_mods = len(records)
    mod_to_idx = {r["mod"]: i for i, r in enumerate(records)}
    mods = [r["mod"] for r in records]

    # Build intra-project import edges (`src -> dst`)
    edges_out: Dict[int, List[int]] = {}
    project_edge_count = 0
    for i, r in enumerate(records):
        dsts = [mod_to_idx[imp] for imp in r["imports"] if imp in mod_to_idx and mod_to_idx[imp] != i]
        if dsts:
            uniq = list(dict.fromkeys(dsts))
            edges_out[i] = uniq
            project_edge_count += len(uniq)

    chain_idx, in_deg, trans_dep, longest_depth = _compute_import_dag_metrics(
        mods, edges_out, skip_bits=not compute_trans_deps
    )

    kernel_live = _load_kernel_live_modules(kernel_db)

    # Accumulate totals & histograms
    total_bytes = 0
    total_zbytes = 0
    total_lines = 0
    total_comment_chars = 0
    total_decls = 0
    decl_kind_totals: Dict[str, int] = collections.Counter()
    kind_counts: Dict[str, int] = collections.Counter()
    kind_bytes: Dict[str, int] = collections.Counter()
    kind_lines: Dict[str, int] = collections.Counter()
    whole_mathlib_count = 0
    unimported_non_root = 0
    len_hist = [[0, 0] for _ in _LENGTH_BINS]  # [math_or_other, restate]
    rep_hist = [[0, 0] for _ in range(10)]  # 0-10 .. 90-100
    rep_first_in_dir = 0
    math_reps: List[int] = []
    restate_reps: List[int] = []
    line_vals: List[int] = []

    not_local_total = 0
    not_scoped_total = 0
    not_global_total = 0
    not_module_cnt = 0
    scoped_not_mods: List[Dict[str, Any]] = []
    global_not_mods: List[Dict[str, Any]] = []
    local_not_top: List[Tuple[int, str, int]] = []
    macro_total = 0
    macro_mod_cnt = 0
    macro_top: List[Tuple[int, str, int]] = []

    hb_mod_cnt = 0
    hb_max_val = 0
    hb_top: List[Tuple[int, str]] = []

    num_lits_total = 0
    long_lits_total = 0
    long_lit_mods = 0
    digit_top: List[Tuple[float, int, int, str, int]] = []

    tactic_totals: Dict[str, int] = collections.Counter()
    term_counts = [0] * len(_SKEPTIC_TERMS)
    term_samples: List[List[str]] = [[] for _ in _SKEPTIC_TERMS]
    term_dirs: List[Dict[str, int]] = [collections.Counter() for _ in _SKEPTIC_TERMS]

    decide_kernel_mods: List[str] = []
    native_decide_mods: List[str] = []
    sorry_mods: List[str] = []
    restate_samples: List[str] = []
    zero_live_mods_count = 0
    zero_live_lines = 0
    zero_live_bytes = 0
    zero_live_samples: List[Tuple[int, str]] = []
    zero_live_dirs: Dict[str, int] = collections.Counter()

    # Compact folder heat map (`ns/l2` up to depth 2 & depth 1) for linked minimap highlight
    dir_agg: Dict[str, List[int]] = {}
    # [n_mods, lines, restate, zero_live, not_local+scoped+global, macros, hb_cnt, long_lits, mathlib]
    def _bump_dir(key: str, r: Dict[str, Any], is_zero_live: bool) -> None:
        slot = dir_agg.get(key)
        if slot is None:
            slot = [0, 0, 0, 0, 0, 0, 0, 0, 0]
            dir_agg[key] = slot
        slot[0] += 1
        slot[1] += r["lines"]
        if r["restate"]:
            slot[2] += 1
        if is_zero_live:
            slot[3] += 1
        slot[4] += r["not_local"] + r["not_scoped"] + r["not_global"]
        slot[5] += r["macros"]
        if r["hb"] > 0:
            slot[6] += 1
        slot[7] += r["long_lits"]
        if r["imports_mathlib"]:
            slot[8] += 1

    single_decl_count = 0
    zero_decl_count = 0
    for i, r in enumerate(records):
        total_bytes += r["bytes"]
        total_zbytes += r["z_bytes"]
        total_lines += r["lines"]
        total_comment_chars += r["comment_chars"]
        total_decls += r["decls"]
        line_vals.append(r["lines"])
        if r["decls"] == 1:
            single_decl_count += 1
        elif r["decls"] == 0:
            zero_decl_count += 1
        for dk, cnt in r["decl_kinds"].items():
            decl_kind_totals[dk] += cnt
        k = r["kind"]
        kind_counts[k] += 1
        kind_bytes[k] += r["bytes"]
        kind_lines[k] += r["lines"]
        if r["imports_mathlib"]:
            whole_mathlib_count += 1
        if in_deg[i] == 0 and r["mod"] != "Main" and not r["mod"].endswith(".Main"):
            unimported_non_root += 1

        bi = _length_bin_idx(r["lines"])
        len_hist[bi][1 if r["restate"] else 0] += 1

        rep = r["rep"]
        if rep < 0:
            rep_first_in_dir += 1
        else:
            rb = min(9, rep // 10)
            rep_hist[rb][1 if r["restate"] else 0] += 1
            if r["restate"]:
                restate_reps.append(rep)
            elif k == "math":
                math_reps.append(rep)

        if r["restate"] and len(restate_samples) < max_samples:
            restate_samples.append(r["mod"])

        nt_l, nt_s, nt_g = r["not_local"], r["not_scoped"], r["not_global"]
        if nt_l or nt_s or nt_g:
            not_module_cnt += 1
            not_local_total += nt_l
            not_scoped_total += nt_s
            not_global_total += nt_g
            if nt_s:
                scoped_not_mods.append({"mod": r["mod"], "count": nt_s, "line": r["not_lines"][1]})
            if nt_g:
                global_not_mods.append({"mod": r["mod"], "count": nt_g, "line": r["not_lines"][2]})
            if nt_l:
                local_not_top.append((nt_l, r["mod"], r["not_lines"][0]))

        if r["macros"] > 0:
            macro_total += r["macros"]
            macro_mod_cnt += 1
            macro_top.append((r["macros"], r["mod"], r["macro_line"]))

        if r["hb"] > 0:
            hb_mod_cnt += 1
            if r["hb"] > hb_max_val:
                hb_max_val = r["hb"]
            hb_top.append((r["hb"], r["mod"]))

        num_lits_total += r["num_lits"]
        if r["long_lits"] > 0:
            long_lits_total += r["long_lits"]
            long_lit_mods += 1
        if r["nonspace"] >= 80 and r["digit_pct"] >= 3.0:
            digit_top.append((r["digit_pct"], r["num_lits"], r["lines"], r["mod"], r["bytes"]))

        for tk, tc in r["tactics"].items():
            tactic_totals[tk] += tc

        if r["decide_kernel"]:
            decide_kernel_mods.append(r["mod"])
        if r["native_decide"]:
            native_decide_mods.append(r["mod"])
        if r["sorry"]:
            sorry_mods.append(r["mod"])

        is_zl = False
        if kernel_live is not None:
            if kernel_live.get(r["mod"], 0) == 0:
                is_zl = True
                zero_live_mods_count += 1
                zero_live_lines += r["lines"]
                zero_live_bytes += r["bytes"]
                zero_live_samples.append((r["lines"], r["mod"]))
                zero_live_dirs[_folder_path_of(r["rel"], 2)] += 1

        l1 = _folder_path_of(r["rel"], 1)
        l2 = _folder_path_of(r["rel"], 2)
        _bump_dir(l1, r, is_zl)
        if l2 != l1:
            _bump_dir(l2, r, is_zl)

        tm = r["term_mask"]
        if tm:
            for ti in range(len(_SKEPTIC_TERMS)):
                if tm & (1 << ti):
                    term_counts[ti] += 1
                    term_dirs[ti][l2] += 1
                    if len(term_samples[ti]) < max_samples:
                        term_samples[ti].append(r["mod"])

    local_not_top.sort(key=lambda x: (-x[0], x[1]))
    macro_top.sort(key=lambda x: (-x[0], x[1]))
    hb_top.sort(key=lambda x: (-x[0], x[1]))
    digit_top.sort(key=lambda x: (-x[0], -x[1], x[3]))
    zero_live_samples.sort(key=lambda x: (-x[0], x[1]))

    # Top transitive dependent hubs & direct in-degree hubs
    top_trans_idx = sorted(range(n_mods), key=lambda i: (-trans_dep[i], -in_deg[i], mods[i]))[:15]
    top_indeg_idx = sorted(range(n_mods), key=lambda i: (-in_deg[i], -trans_dep[i], mods[i]))[:15]

    chain_out = []
    for ci in chain_idx:
        r = records[ci]
        chain_out.append({
            "m": r["mod"],
            "l": r["lines"],
            "d": r["decls"],
            "p": _top_ns_of(r["mod"], 1),
            "r": 1 if r["restate"] else 0,
            "live": (kernel_live.get(r["mod"], 0) if kernel_live is not None else None),
        })

    zero_in_deg_total = sum(1 for i in range(n_mods) if in_deg[i] == 0)

    liveness_contrast: Dict[str, Any] = {
        "total_modules": n_mods,
        "total_lines": total_lines,
        "total_bytes": total_bytes,
        "total_zbytes": total_zbytes,
        "project_import_edges": project_edge_count,
        "avg_imports_per_module": round(project_edge_count / max(n_mods, 1), 2),
        "zero_indeg_modules": zero_in_deg_total,
        "unimported_non_root": unimported_non_root,
        "whole_mathlib_imports": whole_mathlib_count,
        "whole_mathlib_pct": round(100.0 * whole_mathlib_count / max(n_mods, 1), 2),
        "comment_chars": total_comment_chars,
        "has_kernel_liveness": kernel_live is not None,
    }
    if kernel_live is not None:
        liveness_contrast.update({
            "kernel_live_modules": n_mods - zero_live_mods_count,
            "zero_live_kernel_modules": zero_live_mods_count,
            "zero_live_kernel_lines": zero_live_lines,
            "zero_live_kernel_bytes": zero_live_bytes,
            "zero_live_kernel_pct": round(100.0 * zero_live_mods_count / max(n_mods, 1), 2),
            "zero_live_top_dirs": [
                {"dir": d, "count": c} for d, c in sorted(zero_live_dirs.items(), key=lambda x: (-x[1], x[0]))[:16]
            ],
            "zero_live_samples": [
                {"mod": m, "lines": ln} for ln, m in zero_live_samples[:max_samples]
            ],
        })

    # Include concept/skeptic terms (keep zero-hit checks for RH/general forensic value)
    term_rows = []
    for ti, (key, label, _rx) in enumerate(_SKEPTIC_TERMS):
        top_d = sorted(term_dirs[ti].items(), key=lambda x: (-x[1], x[0]))[:8]
        term_rows.append({
            "id": key,
            "label": label,
            "count": term_counts[ti],
            "top_dirs": [{"dir": d, "count": c} for d, c in top_d],
            "samples": term_samples[ti][:max_samples],
        })

    # Keep top 80 dir heat entries by module count (always keeping all depth-1 namespaces)
    dir_rows = []
    for dk, vals in sorted(dir_agg.items(), key=lambda x: (0 if "/" not in x[0] else 1, -x[1][0], x[0])):
        if "/" in dk and len(dir_rows) >= 120:
            continue
        dir_rows.append({
            "dir": dk,
            "mods": vals[0],
            "lines": vals[1],
            "restate": vals[2],
            "zero_live": vals[3],
            "notations": vals[4],
            "macros": vals[5],
            "hb": vals[6],
            "long_lits": vals[7],
            "mathlib": vals[8],
        })

    elapsed = round(time.monotonic() - t0, 2)
    return {
        "schema": PULSE_SCHEMA,
        "slug": slug,
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "elapsed_s": elapsed,
        "summary": {
            "modules": n_mods,
            "lines": total_lines,
            "bytes": total_bytes,
            "zbytes": total_zbytes,
            "median_lines": int(round(statistics.median(line_vals))) if line_vals else 0,
            "max_lines": max(line_vals) if line_vals else 0,
            "decls_regex": total_decls,
            "single_decl_modules": single_decl_count,
            "zero_decl_modules": zero_decl_count,
            "longest_chain_len": len(chain_out),
            "median_math_rep_pct": int(round(statistics.median(math_reps))) if math_reps else None,
            "median_restate_rep_pct": int(round(statistics.median(restate_reps))) if restate_reps else None,
            "exact_trans_deps": bool(compute_trans_deps),
        },
        "liveness": liveness_contrast,
        "module_kinds": [
            {
                "kind": k,
                "count": int(kind_counts.get(k, 0)),
                "lines": int(kind_lines.get(k, 0)),
                "bytes": int(kind_bytes.get(k, 0)),
                "pct": round(100.0 * kind_counts.get(k, 0) / max(n_mods, 1), 2),
            }
            for k in ("math", "restate", "imports", "setup")
            if kind_counts.get(k, 0) > 0 or k in ("math", "restate")
        ],
        "restate_samples": restate_samples,
        "decl_kinds": dict(sorted(decl_kind_totals.items(), key=lambda x: (-x[1], x[0]))),
        "length_histogram": {
            "labels": [b[0] for b in _LENGTH_BINS],
            "math": [row[0] for row in len_hist],
            "restate": [row[1] for row in len_hist],
        },
        "neighbor_zdict_histogram": {
            "labels": [f"{i * 10}–{(i + 1) * 10}%" for i in range(10)],
            "math": [row[0] for row in rep_hist],
            "restate": [row[1] for row in rep_hist],
            "first_in_dir": rep_first_in_dir,
            "median_math_pct": int(round(statistics.median(math_reps))) if math_reps else None,
            "median_restate_pct": int(round(statistics.median(restate_reps))) if restate_reps else None,
        },
        "notations": {
            "total": not_local_total + not_scoped_total + not_global_total,
            "modules": not_module_cnt,
            "local": not_local_total,
            "scoped": not_scoped_total,
            "global": not_global_total,
            "scoped_list": scoped_not_mods[:40],
            "global_list": global_not_mods[:40],
            "top_local": [{"mod": m, "count": c, "line": ln} for c, m, ln in local_not_top[:20]],
        },
        "macros": {
            "total": macro_total,
            "modules": macro_mod_cnt,
            "top": [{"mod": m, "count": c, "line": ln} for c, m, ln in macro_top[:25]],
        },
        "heartbeats": {
            "modules": hb_mod_cnt,
            "pct": round(100.0 * hb_mod_cnt / max(n_mods, 1), 2),
            "max": hb_max_val,
            "top": [{"mod": m, "val": v} for v, m in hb_top[:20]],
        },
        "numeric_literals": {
            "total": num_lits_total,
            "per_module": round(num_lits_total / max(n_mods, 1), 1),
            "long_7plus": long_lits_total,
            "long_7plus_modules": long_lit_mods,
            "high_digit_20pct": sum(1 for r in records if r["nonspace"] >= 80 and r["digit_pct"] >= 20.0),
            "top_digit_pct": [
                {"mod": m, "digit_pct": dp, "literals": nl, "lines": ln, "bytes": nb}
                for dp, nl, ln, m, nb in digit_top[:20]
            ],
        },
        "tactics": [
            {"name": k, "count": int(tactic_totals.get(k, 0))}
            for k in sorted(_TACTIC_KEYS, key=lambda x: (-tactic_totals.get(x, 0), x))
            if tactic_totals.get(k, 0) > 0 or k in ("decide", "native_decide", "sorry")
        ],
        "special_flags": {
            "decide_kernel": {"count": len(decide_kernel_mods), "samples": decide_kernel_mods[:max_samples]},
            "native_decide": {"count": len(native_decide_mods), "samples": native_decide_mods[:max_samples]},
            "sorry": {"count": len(sorry_mods), "samples": sorry_mods[:max_samples]},
        },
        "longest_chain": chain_out,
        "top_transitive_dependents": [
            {
                "mod": records[i]["mod"],
                "dependents": trans_dep[i],
                "pct": round(100.0 * trans_dep[i] / max(n_mods, 1), 1),
                "indeg": in_deg[i],
                "lines": records[i]["lines"],
                "live": (kernel_live.get(records[i]["mod"], 0) if kernel_live is not None else None),
            }
            for i in top_trans_idx
            if trans_dep[i] > 0
        ],
        "top_indeg": [
            {
                "mod": records[i]["mod"],
                "indeg": in_deg[i],
                "dependents": trans_dep[i],
                "lines": records[i]["lines"],
                "live": (kernel_live.get(records[i]["mod"], 0) if kernel_live is not None else None),
            }
            for i in top_indeg_idx
            if in_deg[i] > 0
        ],
        "terms": term_rows,
        "dir_heat": dir_rows,
    }


def write_pulse(pulse_obj: Dict[str, Any], out_path: str) -> int:
    """Safely write `pulse.json` (refuses symlinks)."""
    if os.path.islink(out_path):
        raise ValueError(f"Refusing to write through symlink: {out_path}")
    parent = os.path.dirname(os.path.abspath(out_path))
    if parent:
        os.makedirs(parent, exist_ok=True)
    raw = json.dumps(pulse_obj, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    with open(out_path, "wb") as fh:
        fh.write(raw)
    return len(raw)


def _main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="Compute leanre.pulse/1 forensic source & DAG telemetry.")
    ap.add_argument("--src", required=True, help="Root directory containing .lean source files")
    ap.add_argument("--out", required=True, help="Output pulse.json path")
    ap.add_argument("--slug", default="project", help="Project slug recorded in pulse.json")
    ap.add_argument("--kernel-db", default=None, help="Optional kernel.db for zero-live-kernel module contrast")
    ap.add_argument("--workers", type=int, default=0, help="Worker processes (0 = auto)")
    ap.add_argument("--no-trans-deps", action="store_true", help="Skip bitwise transitive-dependent DP")
    args = ap.parse_args(list(argv) if argv is not None else None)
    data = build_pulse(
        args.src,
        slug=args.slug,
        kernel_db=args.kernel_db,
        workers=args.workers,
        compute_trans_deps=not args.no_trans_deps,
    )
    nb = write_pulse(data, args.out)
    print(
        f"[pulse] {args.slug}: {data['summary']['modules']:,} modules, "
        f"{data['summary']['lines']:,} lines, chain={data['summary']['longest_chain_len']}, "
        f"restate={next((x['count'] for x in data['module_kinds'] if x['kind']=='restate'), 0):,}, "
        f"notations={data['notations']['local']}L/{data['notations']['scoped']}S/{data['notations']['global']}G, "
        f"bytes={nb:,} ({data['elapsed_s']}s)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())
