#!/usr/bin/env python3
"""FLIRT Tier 1 -- deterministic fingerprinting, misfile detection & boilerplate collapse.

    python3 leanre/flirt/tier1.py --src data/rh_mirror/src --expect-files 175187 --threads 24

Outputs:
  * outputs/flirt/tier1.db           (SQLite, gitignored; schema in docs/FLIRT.md)
  * outputs/flirt/tier1_summary.json (small committed report; identifiers, counts, hashes only)

Design & Guardrails:
  * 100% deterministic, zero ML, stdlib only.
  * Never stores or commits raw `.lean` source text or proof bodies.
  * Fingerprints use ONLY imports, `open` namespaces, and declaration headers
    (via `sighash.iter_source_decls` + `sighash.source_sig`), never proof bodies.
  * Reproduces BOTH the Phase-2 literal-2-component namespace split of
    `Development.AbelianVarietyTheory` (39,212 / 14,165 / 11,592 of 457,031 decls;
    counting rule stated explicitly) AND the true Lean-scoped namespace split
    (`_root_.` stripped, `section`/`namespace`/`end` tracked).
  * Flags semantic & structural misfiles generically (no hardcoded module/decl names)
    via five transparent signals: namespace mismatch, folder-local namespace rarity,
    folder-path vs observed-domain conflict, TF-IDF sibling-centroid cosine distance,
    and project-import graph isolation.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import math
import multiprocessing
import os
import re
import sqlite3
import subprocess
import sys
import time
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
LEANRE = os.path.dirname(HERE)
REPO = os.path.dirname(LEANRE)
if LEANRE not in sys.path:
    sys.path.insert(0, LEANRE)

import sighash  # noqa: E402

OUT_DIR = os.path.join(REPO, "outputs", "flirt")
DEFAULT_DB = os.path.join(OUT_DIR, "tier1.db")
DEFAULT_SUMMARY = os.path.join(OUT_DIR, "tier1_summary.json")
DEFAULT_SRC = os.path.join(REPO, "data", "rh_mirror", "src")
DEFAULT_KERNEL_DB = os.path.join(REPO, "outputs", "kernel", "kernel.db")
MAX_THREADS = 16
SCHEMA_VERSION = "leanre.flirt.tier1/2"

# ---------------------------------------------------------------------------
# Phase-2 exact namespace-prefix / clone rules (for independent F1 reproduction)
# ---------------------------------------------------------------------------
_RE_IMPORT = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z_][^\s]*)"
)
_RE_OPEN = re.compile(r"^\s*open\s+(.+)$")
_RE_P2_NS_OPEN = re.compile(r"^\s*namespace\s+([A-Za-z_][\w.'₀-₉]*)")
_RE_P2_NS_END = re.compile(r"^\s*end(?:\s+([A-Za-z_][\w.'₀-₉]*))?\s*$")
_RE_P2_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\b"
    r"(?:\s+([^\s:({\[⦃]+))?"
)
_RE_ROOT_ESCAPE = re.compile(r"\b_root_\.")

# Forensic / computational markers (tracked per enclosing declaration)
_FORENSIC_MARKERS: List[Tuple[str, re.Pattern]] = [
    ("decide_kernel", re.compile(r"\bdecide\s*\+kernel\b")),
    ("kexactB", re.compile(r"\bkexactB\b|\bkc%|\bkq%|\bkd%|\btr_via\b|\btr_clause\b")),
    ("kcopy", re.compile(r"\bkcopy\b|#kcopy_probe\b")),
    ("CutCptCopy", re.compile(r"\bCutCptCopy\b|\bcutCptCopy\b|\bcopy_decl\b")),
    ("addDecl", re.compile(r"\baddDecl\b|\baddAndCompile\b")),
    ("run_tac", re.compile(r"\brun_tac\b|\brun_cmd\b|\brun_elab\b")),
]
_RE_WRAPPER_BODY = re.compile(r"\bfirst\s*\|\s*exact\b")

# Exact Phase-2 clone normalization table (mirrors leanre/scanner.py)
_P2_LEAN_KEYWORDS: Set[str] = set(
    """simp only at exact rw intro intros have by nlinarith refine obtain apply norm_num linarith
    rcases with field_simp ring_nf positivity gcongr omega constructor ext push_cast exact_mod_cast
    by_cases calc ring funext congr unfold show filter_upwards specialize induction zero succ simpa
    using ih this subst cases theorem lemma def instance structure fun trans aesop tauto decide
    import open namespace end variable section noncomputable private protected abbrev class where
    match if then else do let in return for pure classical by_contra contradiction exfalso
    left right use refine' exact? apply? simp_all dsimp change clear revert generalize rfl
    rwa erw linear_combination polyrith abel group module norm_cast cast exact_mod_cast
    conv lhs rhs arg enter pattern repeat try first all_goals any_goals focus swap rotate_left
    trivial assumption done sorry admit axiom opaque inductive mutual deriving extends""".split()
)
_RE_P2_NORM_TOK = re.compile(r"[A-Za-z_][\w.'₀-₉]*|\d+")

# ---------------------------------------------------------------------------
# Deterministic Mathematical / Infrastructure Domain Lexicon
# ---------------------------------------------------------------------------
# Maps Mathlib/Lean-core header type-tokens, `open` namespaces, `Mathlib.*`
# subimport segments, and CamelCase folder-path cues to 11 clean domains.
# Zero proof bodies are scanned for tokens (except the explicit `decide +kernel`
# / metaprogramming forensic marker).
DOMAIN_KEYWORDS: Dict[str, Tuple[str, ...]] = {
    "prime_elem_arith": (
        "prime", "primes", "primecounting", "centralbinom", "arithmeticfunction",
        "vonmangoldt", "totient", "coprime", "factorization", "minfac", "primorial",
        "chebyshev", "primerecip", "nat.prime", "nat.primes", "nat.totient",
        "nat.primecounting", "nat.centralbinom", "nat.coprime", "nat.gcd", "nat.lcm",
        "nat.log", "zmod", "divisors", "primefactors", "moebius", "mobius",
        "mangoldt", "bertrand", "dyadicprime",
    ),
    "analytic_nt_zeta": (
        "riemannzeta", "riemannhypothesis", "dirichletcharacter", "lfunction",
        "lseries", "mulchar", "addchar", "completedriemannzeta", "hurwitzzeta",
        "eulerproduct", "heckel", "automorphic", "automorphicl", "zeta", "dirichlet",
        "artinl", "mellin", "completedzeta", "gamma",
    ),
    "complex_real_analysis": (
        "analyticat", "analyticon", "differentiable", "differentiableon",
        "hasderivat", "deriv", "fderiv", "continuous", "continuouson", "tendsto",
        "filter", "metric", "metricspace", "normedspace", "normedfield",
        "normedring", "normedaddcommgroup", "innerproductspace", "completespace",
        "asymptotics", "isbigo", "islittleo", "fourier", "schwartz", "bumpfunction",
        "liouville", "holomorphic", "meromorphic", "real.log", "real.exp", "real.pi",
        "complex.exp", "complex.log", "complex.arg", "complex.abs", "complex.re",
        "complex.im", "continuouslinearmap", "banach", "hilbert", "spectral",
        "harmonic", "bessel", "curvature", "hermitian",
    ),
    "measure_integration": (
        "measuretheory", "measure", "volume", "integrable", "integral", "lintegral",
        "measurable", "measurablespace", "measurepreserving", "addhaar", "haar",
        "ennreal", "nnreal", "bochner", "fubini", "ae", "aemeasurable",
        "aestronglymeasurable", "locallyintegrable", "probabilitytheory",
        "periodintegral", "periodintegrals", "radon",
    ),
    "algebraic_geometry": (
        "algebraicgeometry", "scheme", "spec", "locallyringedspace", "presheaf",
        "sheaf", "categorytheory", "limits", "monoidalcategory", "cartesianmonoidalcategory",
        "abelian", "abelianvariety", "abelianvarieties", "abelianscheme", "projective",
        "variety", "varieties", "divisor", "divisors", "divisorproofs", "primespectrum",
        "localization", "islocalring", "etale", "etalecohomology", "cohomology",
        "picard", "jacobian", "motive", "shimura", "moduli", "crystallin",
        "singularities", "resolution", "morphisms", "functor", "adjunction",
        "monobj", "quasicoherent", "polarized", "polarization", "linebundle",
        "chern", "intersection", "chow", "degeneration", "degenerations",
    ),
    "padic_local_fields": (
        "padic", "padics", "padicint", "padicnorm", "valuation", "valued", "withzero",
        "adiccompletion", "teichmuller", "hensel", "isdiscretevaluationring", "dvr",
        "localfield", "wittvector", "numberfield", "ringofintegers", "infiniteplace",
        "finiteplace", "height", "heights", "adeles", "adelering", "adele", "idele",
        "isdedekinddomain", "dedekind", "ramification", "inertia", "frobenius",
        "place", "places", "localglobal", "padicnumbers", "padicsubsetsums",
    ),
    "linear_matrix_rep": (
        "matrix", "linearmap", "linearequiv", "module", "submodule", "tensorproduct",
        "bilinform", "quadraticform", "sesqform", "unitary", "speciallineargroup",
        "generallineargroup", "representation", "eigenvalues", "eigenvector", "det",
        "trace", "basis", "dual", "orthogonal", "symplectic", "reductive",
        "reductivegroups", "iwasawa", "parabolic", "hecke", "lattice", "lattices",
        "gram", "weyl", "rootdata", "liealgebra", "harishchandra", "pieri", "schur",
    ),
    "algebra_rings_poly": (
        "commring", "ring", "semiring", "field", "divisionring", "polynomial",
        "mvpolynomial", "powerseries", "mvpowerseries", "algebra", "alghom",
        "algequiv", "ringhom", "subring", "subfield", "ideal", "galois",
        "intermediatefield", "minpoly", "isintegral", "isalgebraic", "subgroup",
        "quotientgroup", "isdomain", "isfractionring", "isalgclosed", "algclosed",
        "jacobson", "krull", "weierstrass", "dualnumber", "noetherian", "artinian",
        "homogeneousideal", "homogeneousideals",
    ),
    "topology_manifold": (
        "topologicalspace", "topology", "isopen", "isclosed", "iscompact",
        "locallycompactspace", "t2space", "homeomorph", "uniformspace",
        "chartedspace", "manifold", "smooth", "partitionofunity", "fiberbundle",
        "clopen", "connected", "compact", "hausdorff", "stoneweierstrass",
    ),
    "computational_kernel_check": (
        "bool", "list", "array", "bytearray", "bitvec", "decidable", "decidableeq",
        "decidablepred", "decide_kernel", "nat.blt", "nat.ble", "uint64", "uint32",
        "fin.foldl", "list.all", "list.pairwise",
    ),
    "meta_lean_elab": (
        "lean", "lean.meta", "lean.elab", "lean.expr", "tactic", "termelabm",
        "metam", "commandelabm", "syntax", "environment", "adddecl", "kexactb",
        "kcopy", "cutcptcopy", "run_tac", "buildaid",
    ),
}

# Build fast lowercase keyword -> set of domains lookup
_KW_TO_DOMAINS: Dict[str, List[str]] = collections.defaultdict(list)
for _dom, _kws in DOMAIN_KEYWORDS.items():
    for _kw in _kws:
        _KW_TO_DOMAINS[_kw].append(_dom)

# Also map neutral/generic tokens that should NEVER pollute Mathlib TF-IDF centroids
_STOP_TOKENS: Set[str] = {
    "Prop", "Type", "Sort", "True", "False", "Eq", "Ne", "And", "Or", "Not",
    "Iff", "Exists", "HEq", "Unit", "PUnit", "Empty", "PEmpty", "Option",
    "Prod", "Sum", "Sigma", "PSigma", "PProd", "Subtype", "Set", "Function",
    "Classical", "Nonempty", "Inhabited", "Unique", "Nontrivial", "CharZero",
    "NeZero", "LE", "LT", "GE", "GT", "Add", "Mul", "Sub", "Div", "Pow",
    "Neg", "Inv", "Zero", "One", "OfNat", "HAdd", "HMul", "HSub", "HDiv",
    "HPow", "HSMul", "SMul", "Coe", "Fin", "Nat", "Int", "Rat", "Real", "Complex",
    "Finset", "Fintype", "Multiset", "Order", "LinearOrder", "PartialOrder",
    "Preorder", "Lattice", "CompleteLattice", "Finite", "Countable", "Infinite",
}

_RE_CAMEL = re.compile(r"[A-Z]+(?=[A-Z][a-z]|\b)|[A-Z]?[a-z]+|\d+")

# Phase 4 calibrated anomaly scoring weights (sum = 1.0, documented in docs/FLIRT.md).
# Systematic bulk folder->namespace remappings (e.g. 99.9% of AbelianVarietyTheory
# declaring GlobalTheory.*) are detected automatically and separated into the
# `bulk_namespace_remapping` band instead of inflating misfile alerts.
MISFILE_WEIGHTS = {
    "ns_outlier": 0.28,
    "folder_domain_conflict": 0.28,
    "centroid_distance": 0.24,
    "graph_isolation": 0.20,
}
NON_BULK_FOREIGN_NS_BONUS = 0.05
WRAPPER_DAMPING = 0.50
BULK_REMAP_MIN_MODULES = 20
BULK_REMAP_MIN_SHARE = 0.10


def _split_camel(name: str) -> List[str]:
    """Split dotted/CamelCase/snake_case path into lowercase words + full segments."""
    out: List[str] = []
    for seg in name.split("."):
        low = seg.lower()
        if low:
            out.append(low)
        for part in seg.split("_"):
            for w in _RE_CAMEL.findall(part):
                wl = w.lower()
                if len(wl) >= 3:
                    out.append(wl)
    return out


def infer_expected_domains(folder_ns: str) -> Set[str]:
    """Infer expected mathematical domain(s) from folder path segments alone."""
    words = _split_camel(folder_ns)
    doms: Set[str] = set()
    # Check both full path segments (e.g. 'abelianvarietytheory', 'divisorproofs')
    # and CamelCase sub-words ('abelian', 'variety', 'divisor', 'padic', 'integral')
    for w in words:
        if w in _KW_TO_DOMAINS:
            doms.update(_KW_TO_DOMAINS[w])
        else:
            # Substring match for compound folder words like 'AbelianVarietyTheory'
            for kw, ds in _KW_TO_DOMAINS.items():
                if len(kw) >= 6 and kw in w:
                    doms.update(ds)
    return doms


def _token_domains(tok: str) -> List[str]:
    """Map one Mathlib/core identifier or import/open token to domain(s)."""
    low = tok.lower()
    if low in _KW_TO_DOMAINS:
        return _KW_TO_DOMAINS[low]
    tail = low.rsplit(".", 1)[-1]
    if tail in _KW_TO_DOMAINS:
        return _KW_TO_DOMAINS[tail]
    # Check path components of dotted Mathlib names like Mathlib.RingTheory.Ideal.Krull
    if "." in low:
        hits: List[str] = []
        for seg in low.split("."):
            if seg in _KW_TO_DOMAINS:
                hits.extend(_KW_TO_DOMAINS[seg])
        if hits:
            return hits
    # Check CamelCase subwords for compound Mathlib type names (e.g. PrimeCounting, LocalRing)
    hits = []
    for w in _RE_CAMEL.findall(tok.rsplit(".", 1)[-1]):
        wl = w.lower()
        if len(wl) >= 5 and wl in _KW_TO_DOMAINS:
            hits.extend(_KW_TO_DOMAINS[wl])
    return hits


def _p2_normalize_for_clone(lines: Sequence[str]) -> str:
    """Exact Phase-2 body alpha-normalization (matches leanre/scanner.py)."""
    def _sub(m: re.Match) -> str:
        tok = m.group(0)
        if tok[0].isdigit():
            return "0"
        return tok if tok in _P2_LEAN_KEYWORDS else "x"
    return "\n".join(_RE_P2_NORM_TOK.sub(_sub, ln.strip()) for ln in lines if ln.strip())


def _extract_p2_ns2(clean_lines: Sequence[str]) -> collections.Counter:
    """Exact Phase-2 literal-2-component namespace extraction (mirrors scanner.py)."""
    ns_stack: List[str] = []
    ctr: collections.Counter = collections.Counter()
    for line_idx, ln in enumerate(clean_lines):
        if not ln or ln[0] == " " or ln[0] == "\t":
            continue
        m_ns = _RE_P2_NS_OPEN.match(ln)
        if m_ns:
            ns_stack.append(m_ns.group(1))
            continue
        m_end = _RE_P2_NS_END.match(ln)
        if m_end:
            if ns_stack:
                end_nm = m_end.group(1)
                if end_nm is None or ns_stack[-1] == end_nm:
                    ns_stack.pop()
            continue
        m_decl = _RE_P2_DECL.match(ln)
        if m_decl:
            raw_name = m_decl.group(2) or f"_anon_{line_idx + 1}"
            if ns_stack and not raw_name.startswith(ns_stack[0] + "."):
                full_name = ".".join(ns_stack) + "." + raw_name
            else:
                full_name = raw_name
            parts = full_name.split(".")
            ctr[f"{parts[0]}.{parts[1]}" if len(parts) >= 2 else parts[0]] += 1
    return ctr


def _is_std_import(imp: str) -> bool:
    head = imp.split(".", 1)[0]
    return head in ("Mathlib", "Lean", "Batteries", "Std", "Init", "Aesop", "Qq", "ProofWidgets", "ImportGraph")


def _scan_batch(args: Tuple[str, List[Tuple[str, str]]]) -> List[Dict[str, Any]]:
    """Worker: scan a batch of `(module_name, rel_path)` files."""
    src_root, items = args
    out: List[Dict[str, Any]] = []
    for mod_name, rel_path in items:
        abs_path = os.path.join(src_root, rel_path)
        with open(abs_path, "rb") as f:
            raw_bytes = f.read()
        lines_wc = raw_bytes.count(b"\n")
        text = raw_bytes.decode("utf-8", errors="replace")
        clean_text = sighash.strip_comments(text)
        clean_lines = clean_text.split("\n")

        # 1. Imports, opens, body lines, shim detection
        mathlib_all_count = 0
        mathlib_subimports: Set[str] = set()
        proj_imports: Set[str] = set()
        opens: Set[str] = set()
        body_lines: List[str] = []
        has_non_import = False
        raw_import_count = 0

        for ln in clean_lines:
            s = ln.strip()
            if not s:
                continue
            m_imp = _RE_IMPORT.match(ln)
            if m_imp:
                raw_import_count += 1
                imp = m_imp.group(1)
                if imp == "Mathlib":
                    mathlib_all_count += 1
                elif _is_std_import(imp):
                    mathlib_subimports.add(imp)
                else:
                    proj_imports.add(imp)
            else:
                has_non_import = True
                body_lines.append(ln)
                if s.startswith("open "):
                    m_op = _RE_OPEN.match(ln)
                    if m_op:
                        toks = m_op.group(1).strip().split()
                        if toks and toks[-1] == "in":
                            toks = toks[:-1]
                        for t in toks:
                            if t in ("scoped",):
                                continue
                            if t in ("hiding", "renaming") or t.startswith("("):
                                break
                            opens.add(t)

        is_shim = 1 if (raw_import_count > 0 and not has_non_import) else 0

        # 2. Exact Phase-2 alpha-renamed file-body clone hash
        if body_lines:
            norm_body = _p2_normalize_for_clone(body_lines)
            alpha_clone_sig = hashlib.blake2b(norm_body.encode("utf-8"), digest_size=8).hexdigest()
        else:
            alpha_clone_sig = "shim_empty"

        # 3. Exact Phase-2 literal-2-comp declaration prefixes (for F1)
        p2_ns2 = dict(_extract_p2_ns2(clean_lines))

        # 4. True Lean-scoped declarations & header signatures (zero proof bodies!)
        lean_decl_names: List[str] = []
        lean_ns2: collections.Counter = collections.Counter()
        decl_lines: List[Tuple[int, str]] = []
        sig_items: List[str] = []
        raw_header_toks: collections.Counter = collections.Counter()
        decl_ns_opens: List[Tuple[str, Tuple[str, ...]]] = []
        uses_root_escape = 1 if _RE_ROOT_ESCAPE.search(clean_text) else 0

        for d in sighash.iter_source_decls(clean_text, with_sig=True):
            nm = d["name"]
            lean_decl_names.append(nm)
            decl_lines.append((d["line"], nm))
            parts = nm.split(".")
            lean_ns2[f"{parts[0]}.{parts[1]}" if len(parts) >= 2 else parts[0]] += 1
            r = sighash.source_sig(d["var_binders"] + d["binders"], d["type"])
            sig_items.append(f"{d['kind']}:{r['s1t']}")
            # Collect free tokens from canonical header token stream (already
            # stripped of proof bodies, bound variables `#k`, universes `u#k`, keywords).
            # Also capture Lean 4 dot-notation suffixes on bound vars (e.g. `#0.Prime`)
            # when the suffix is in the Mathlib domain lexicon.
            for tok in r["tokens_n"]:
                if tok.startswith("#") and "." in tok:
                    field = tok.split(".", 1)[1]
                    if field.lower() in _KW_TO_DOMAINS:
                        raw_header_toks[field] += 1
                elif (len(tok) >= 2
                        and not tok.startswith("#")
                        and not tok.startswith("u#")
                        and tok[0].isalpha()
                        and tok not in sighash._KEYWORDS):
                    raw_header_toks[tok] += 1
            decl_ns_opens.append((d["namespace"], tuple(d["opens"])))

        decl_count = len(lean_decl_names)
        if sig_items:
            sig_items.sort()
            sigset_hash = hashlib.sha256("\n".join(sig_items).encode("utf-8")).hexdigest()[:16]
        else:
            sigset_hash = "empty"

        # 5. Statement-wrapper detection (deterministic structural pattern)
        base_mod = mod_name.rsplit(".", 1)[-1]
        is_stmt_wrapper = 0
        wrapper_kind = ""
        if decl_count == 1 and lines_wc <= 15 and base_mod.endswith("Statement"):
            is_stmt_wrapper = 1
            if _RE_WRAPPER_BODY.search(clean_text) and uses_root_escape:
                wrapper_kind = "root_exact_forward"
            elif uses_root_escape:
                wrapper_kind = "root_statement_wrapper"
            else:
                wrapper_kind = "statement_wrapper"

        # 6. Lightweight forensic markers tracked per enclosing declaration
        forensic_flags: Set[str] = set()
        flagged_decls: List[Tuple[str, str, int]] = []  # (flag, decl_name, line_no)
        if any(k in clean_text for k in ("+kernel", "kexactB", "kc%", "kq%", "kd%", "tr_via",
                                         "tr_clause", "kcopy", "CutCptCopy", "cutCptCopy",
                                         "copy_decl", "addDecl", "addAndCompile",
                                         "run_tac", "run_cmd", "run_elab")):
            ptr = 0
            cur_decl = ""
            n_dl = len(decl_lines)
            for idx_l, cln in enumerate(clean_lines):
                lno = idx_l + 1
                while ptr < n_dl and decl_lines[ptr][0] <= lno:
                    cur_decl = decl_lines[ptr][1]
                    ptr += 1
                for tag, rx in _FORENSIC_MARKERS:
                    if rx.search(cln):
                        forensic_flags.add(tag)
                        if cur_decl and len(flagged_decls) < 20:
                            flagged_decls.append((tag, cur_decl, lno))

        # Deduplicate (ns, opens) contexts for Pass-2 project-local token filtering
        uniq_ctx = sorted(set(decl_ns_opens))[:8]
        out.append({
            "module": mod_name,
            "file_path": rel_path,
            "lines_wc": lines_wc,
            "decl_count": decl_count,
            "is_shim": is_shim,
            "is_stmt_wrapper": is_stmt_wrapper,
            "wrapper_kind": wrapper_kind,
            "mathlib_all_count": mathlib_all_count,
            "mathlib_subimports": sorted(mathlib_subimports),
            "proj_imports": sorted(proj_imports),
            "opens": sorted(opens),
            "p2_ns2": p2_ns2,
            "lean_ns2": dict(lean_ns2),
            "lean_decl_names": lean_decl_names,
            "uses_root_escape": uses_root_escape,
            "raw_header_toks": dict(raw_header_toks),
            "ctx": uniq_ctx,
            "sigset_hash": sigset_hash,
            "alpha_clone_sig": alpha_clone_sig,
            "forensic_flags": sorted(forensic_flags),
            "flagged_decls": flagged_decls,
        })
    return out


def discover_modules(src_dir: str) -> List[Tuple[str, str]]:
    """Return sorted [(module_name, rel_path), ...] for all `.lean` files under `src_dir`."""
    items: List[Tuple[str, str]] = []
    for dirpath, dirnames, filenames in os.walk(src_dir):
        dirnames[:] = sorted(d for d in dirnames if d not in (".lake", ".git", "build"))
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                full = os.path.join(dirpath, fn)
                rel = os.path.relpath(full, src_dir)
                mod = rel[:-5].replace(os.sep, ".")
                items.append((mod, rel))
    items.sort(key=lambda x: x[0])
    return items


def _git_head(path: str) -> Optional[str]:
    try:
        r = subprocess.run(
            ["git", "-C", path, "rev-parse", "HEAD"],
            capture_output=True, text=True, timeout=5, check=False,
        )
        return r.stdout.strip() if r.returncode == 0 else None
    except Exception:
        return None


def _ns_mismatch_score(declared_ns: str, folder_ns: str, module_name: str) -> Tuple[float, str]:
    """Compare declared 2-comp namespace against folder path namespace."""
    if not declared_ns:
        return 0.0, "no_decls"
    f_parts = folder_ns.split(".") if folder_ns else []
    if not f_parts:
        # Top-level root module like Main.lean or Statements.lean
        return 0.0, "root_module"
    d_parts = declared_ns.split(".")
    if d_parts[0] != f_parts[0]:
        return 1.0, "foreign_top_ns"
    if len(d_parts) >= 2 and len(f_parts) >= 2 and d_parts[1] != f_parts[1]:
        return 0.5, "sub_ns_mismatch"
    return 0.0, "match"


def _cosine_distance(a: Dict[str, float], b: Dict[str, float]) -> float:
    if not a or not b:
        return 0.0
    dot = 0.0
    na = 0.0
    for k, va in a.items():
        na += va * va
        vb = b.get(k)
        if vb is not None:
            dot += va * vb
    if na <= 0.0:
        return 0.0
    nb = sum(v * v for v in b.values())
    if nb <= 0.0:
        return 0.0
    sim = min(1.0, max(0.0, dot / (math.sqrt(na) * math.sqrt(nb))))
    return round(1.0 - sim, 4)


# ---------------------------------------------------------------------------
# SQLite Schema (documented in docs/FLIRT.md)
# ---------------------------------------------------------------------------
SCHEMA_SQL = """
CREATE TABLE meta (
    key TEXT PRIMARY KEY,
    value_json TEXT NOT NULL
);

CREATE TABLE module_fingerprints (
    module TEXT PRIMARY KEY,
    file_path TEXT NOT NULL,
    folder_ns TEXT NOT NULL,
    folder_l2 TEXT NOT NULL,
    folder_l3 TEXT NOT NULL,
    lines_wc INTEGER NOT NULL,
    decl_count INTEGER NOT NULL,
    is_shim INTEGER NOT NULL,
    is_statement_wrapper INTEGER NOT NULL,
    imports_mathlib_all INTEGER NOT NULL,
    mathlib_subimports_json TEXT NOT NULL,
    proj_import_count INTEGER NOT NULL,
    same_folder_import_ratio REAL NOT NULL,
    opens_json TEXT NOT NULL,
    declared_ns_primary TEXT NOT NULL,
    declared_ns_all_json TEXT NOT NULL,
    uses_root_escape INTEGER NOT NULL,
    top_domain TEXT NOT NULL,
    domain_vector_json TEXT NOT NULL,
    type_tokens_top_json TEXT NOT NULL,
    fp_hash TEXT NOT NULL,
    sigset_hash TEXT NOT NULL,
    alpha_clone_sig TEXT NOT NULL,
    forensic_flags_json TEXT NOT NULL
);

CREATE TABLE misfiles (
    rank INTEGER PRIMARY KEY,
    module TEXT UNIQUE NOT NULL,
    file_path TEXT NOT NULL,
    declared_ns TEXT NOT NULL,
    folder_ns TEXT NOT NULL,
    folder_l2 TEXT NOT NULL,
    score REAL NOT NULL,
    tier TEXT NOT NULL,
    ns_mismatch_kind TEXT NOT NULL,
    ns_count_in_folder INTEGER NOT NULL,
    ns_rarity_in_folder REAL NOT NULL,
    domain_expected TEXT NOT NULL,
    domain_observed TEXT NOT NULL,
    folder_domain_conflict REAL NOT NULL,
    centroid_distance REAL NOT NULL,
    graph_isolation REAL NOT NULL,
    is_statement_wrapper INTEGER NOT NULL,
    flag_decl TEXT,
    reason TEXT NOT NULL,
    provenance TEXT NOT NULL,
    band TEXT NOT NULL,
    is_bulk_remap INTEGER NOT NULL
);

CREATE TABLE bulk_namespace_remappings (
    folder_l2 TEXT NOT NULL,
    declared_top_ns TEXT NOT NULL,
    module_count INTEGER NOT NULL,
    folder_non_shim_count INTEGER NOT NULL,
    share_of_folder REAL NOT NULL,
    PRIMARY KEY (folder_l2, declared_top_ns)
) WITHOUT ROWID;

CREATE TABLE namespace_folder_matrix (
    folder_l2 TEXT NOT NULL,
    counting_rule TEXT NOT NULL,
    declared_ns TEXT NOT NULL,
    decl_count INTEGER NOT NULL,
    module_count INTEGER NOT NULL,
    PRIMARY KEY (folder_l2, counting_rule, declared_ns)
) WITHOUT ROWID;

CREATE TABLE boilerplate_clusters (
    cluster_id TEXT PRIMARY KEY,
    kind TEXT NOT NULL,
    size INTEGER NOT NULL,
    redundant_modules INTEGER NOT NULL,
    total_lines INTEGER NOT NULL,
    representative TEXT NOT NULL,
    sig_hash TEXT NOT NULL,
    summary TEXT NOT NULL,
    sample_members_json TEXT NOT NULL
);

CREATE TABLE boilerplate_members (
    cluster_id TEXT NOT NULL,
    module TEXT NOT NULL,
    lines_wc INTEGER NOT NULL,
    PRIMARY KEY (cluster_id, module)
) WITHOUT ROWID;

CREATE TABLE folder_fingerprints (
    folder TEXT NOT NULL,
    depth INTEGER NOT NULL,
    module_count INTEGER NOT NULL,
    non_shim_count INTEGER NOT NULL,
    decl_count INTEGER NOT NULL,
    lines_wc INTEGER NOT NULL,
    mathlib_all_count INTEGER NOT NULL,
    expected_domains_json TEXT NOT NULL,
    top_domains_json TEXT NOT NULL,
    top_declared_ns_json TEXT NOT NULL,
    top_type_tokens_json TEXT NOT NULL,
    PRIMARY KEY (folder, depth)
) WITHOUT ROWID;
"""

INDEX_SQL = """
CREATE INDEX idx_mf_folder_l2 ON module_fingerprints(folder_l2);
CREATE INDEX idx_mf_folder_l3 ON module_fingerprints(folder_l3);
CREATE INDEX idx_mf_decl_ns ON module_fingerprints(declared_ns_primary);
CREATE INDEX idx_mf_top_dom ON module_fingerprints(top_domain);
CREATE INDEX idx_mf_fp_hash ON module_fingerprints(fp_hash);
CREATE INDEX idx_mf_sigset ON module_fingerprints(sigset_hash);
CREATE INDEX idx_mf_alpha ON module_fingerprints(alpha_clone_sig);

CREATE INDEX idx_misfiles_score ON misfiles(score DESC);
CREATE INDEX idx_misfiles_folder_l2 ON misfiles(folder_l2, score DESC);
CREATE INDEX idx_misfiles_decl_ns ON misfiles(declared_ns);
CREATE INDEX idx_misfiles_flag_decl ON misfiles(flag_decl);
CREATE INDEX idx_misfiles_tier ON misfiles(tier, score DESC);
CREATE INDEX idx_misfiles_band ON misfiles(band, score DESC);

CREATE INDEX idx_nfm_lookup ON namespace_folder_matrix(folder_l2, counting_rule, decl_count DESC);
CREATE INDEX idx_bc_kind ON boilerplate_clusters(kind, size DESC);
CREATE INDEX idx_bm_mod ON boilerplate_members(module);
"""


def _calibrate_bands_against_kernel(
    kernel_db: str,
    band_samples: Dict[str, List[Tuple[str, str]]],
    band_totals: Dict[str, int],
) -> Optional[Dict[str, Any]]:
    """Independent [L] precision check against outputs/kernel/kernel.db (mode=ro).

    For each calibrated band, checks a deterministic sample of up to 400 modules:
      * kernel_live_rate: fraction with >=1 live declaration in solution.ndjson.zst
      * kernel_zero_expected_domain_rate: among live modules whose folder path implies
        an expected domain (e.g. algebraic_geometry for AbelianVarietyTheory/DivisorProofs),
        fraction whose actual kernel `type`-dependency library constants (`edges.kind IN (1,3)`)
        contain ZERO Mathlib constants matching that expected domain!
    """
    if not kernel_db or not os.path.exists(kernel_db):
        return None
    ck = sqlite3.connect(f"file:{kernel_db}?mode=ro", uri=True)
    try:
        live_mods = {
            r[0] for r in ck.execute(
                "SELECT DISTINCT module FROM decl_module WHERE module IS NOT NULL"
            )
        }
        out: Dict[str, Any] = {
            "kernel_db": os.path.relpath(kernel_db, REPO) if os.path.abspath(kernel_db).startswith(REPO) else kernel_db,
            "method": (
                "Deterministic stride sample (up to 400 modules/band) cross-checked against "
                "outputs/kernel/kernel.db live decls and 1-hop kernel type-dependency library constants."
            ),
            "bands": {},
        }
        for band, pairs in band_samples.items():
            tot = band_totals.get(band, len(pairs))
            live_cnt = sum(1 for m, _ in pairs if m in live_mods)
            # Deterministic stride sample of up to 400 modules with an expected folder domain
            with_exp = [(m, ed) for m, ed in pairs if ed and ed != "unspecified" and m in live_mods]
            if len(with_exp) > 400:
                step = len(with_exp) / 400.0
                sampled = [with_exp[int(k * step)] for k in range(400)]
            else:
                sampled = with_exp

            zero_expected = 0
            checked_with_lib = 0
            for mod, exp_str in sampled:
                exp_set = set(exp_str.split("+"))
                # Query 1-hop type-dependency target names for declarations in `mod`
                dep_names = [
                    r[0] for r in ck.execute(
                        """
                        SELECT DISTINCT d2.name
                        FROM decl_module dm
                        JOIN edges e ON e.src = dm.decl_id AND e.kind IN (1, 3)
                        JOIN decls d2 ON d2.id = e.dst
                        LEFT JOIN decl_module dm2 ON dm2.decl_id = d2.id
                        WHERE dm.module = ?
                          AND (dm2.module IS NULL OR dm2.method LIKE 'unmatched:%library%')
                        LIMIT 150
                        """,
                        (mod,),
                    )
                ]
                if not dep_names:
                    continue
                checked_with_lib += 1
                hit_expected = False
                for dn in dep_names:
                    for dom in _token_domains(dn):
                        if dom in exp_set:
                            hit_expected = True
                            break
                    if hit_expected:
                        break
                if not hit_expected:
                    zero_expected += 1

            out["bands"][band] = {
                "total_modules": tot,
                "live_modules": live_cnt,
                "live_rate": round(live_cnt / max(1, tot), 4),
                "sampled_live_with_expected_domain": len(sampled),
                "checked_with_kernel_lib_type_deps": checked_with_lib,
                "kernel_zero_expected_domain_count": zero_expected,
                "kernel_domain_conflict_precision": round(zero_expected / checked_with_lib, 4) if checked_with_lib else None,
            }
        return out
    finally:
        ck.close()


def run_tier1(
    src_dir: str = DEFAULT_SRC,
    db_path: str = DEFAULT_DB,
    summary_path: Optional[str] = DEFAULT_SUMMARY,
    threads: int = MAX_THREADS,
    expect_files: Optional[int] = None,
    kernel_db: Optional[str] = DEFAULT_KERNEL_DB,
    verbose: bool = True,
) -> Dict[str, Any]:
    """Run Tier 1 end-to-end: scan -> fingerprint -> score misfiles -> collapse boilerplate."""
    t0 = time.time()
    threads = max(1, min(threads, MAX_THREADS))
    items = discover_modules(src_dir)
    n_files = len(items)
    if expect_files is not None and n_files != expect_files:
        raise RuntimeError(
            f"Expected {expect_files} .lean files under {src_dir}, found {n_files}"
        )
    if verbose:
        print(f"[tier1] discovered {n_files:,} .lean files under {src_dir} ({time.time()-t0:.1f}s)", flush=True)

    module_set: Set[str] = {m for m, _ in items}
    chunk = max(50, min(600, (n_files + threads * 8 - 1) // (threads * 8)))
    batches = [(src_dir, items[i:i + chunk]) for i in range(0, n_files, chunk)]

    # Pass 1: parallel file parse
    t1 = time.time()
    recs: List[Dict[str, Any]] = []
    if threads == 1 or len(batches) <= 1:
        for b in batches:
            recs.extend(_scan_batch(b))
    else:
        with multiprocessing.get_context("fork").Pool(processes=threads) as pool:
            for batch_res in pool.imap(_scan_batch, batches, chunksize=1):
                recs.extend(batch_res)
    if verbose:
        print(f"[tier1] parsed {len(recs):,} files on {threads} threads in {time.time()-t1:.1f}s", flush=True)

    # Pass 2: build in-memory project-local Lexicon & aggregate folder/namespace statistics
    t2 = time.time()
    all_decl_names: Set[str] = set()
    for r in recs:
        all_decl_names.update(r["lean_decl_names"])
    lexicon = sighash.Lexicon(all_decl_names)
    del all_decl_names

    # Folder statistics & namespace matrices
    p2_matrix_decls: Dict[Tuple[str, str], int] = collections.Counter()
    p2_matrix_mods: Dict[Tuple[str, str], int] = collections.Counter()
    lean_matrix_decls: Dict[Tuple[str, str], int] = collections.Counter()
    lean_matrix_mods: Dict[Tuple[str, str], int] = collections.Counter()
    folder_l2_ns_mod_counts: Dict[str, collections.Counter] = collections.defaultdict(collections.Counter)
    folder_l2_top_ns_counts: Dict[str, collections.Counter] = collections.defaultdict(collections.Counter)
    folder_l2_non_shim: collections.Counter = collections.Counter()
    folder_l3_proj_imp_sum: collections.Counter = collections.Counter()
    folder_l3_count: collections.Counter = collections.Counter()

    # Pre-compute per-module Mathlib/core feature bags and document frequencies for IDF
    mod_features: List[Dict[str, float]] = []
    mod_domains: List[Dict[str, float]] = []
    mod_top_toks: List[List[str]] = []
    mod_primary_ns: List[str] = []
    mod_folder_meta: List[Tuple[str, str, str, int, float]] = []  # (folder_ns, l2, l3, proj_cnt, same_l2_ratio)
    doc_freq: collections.Counter = collections.Counter()

    # Fast cache for checking whether a token is project-local in a (ns, opens) context
    # Many modules share identical (ns, opens) or global names; cache (tok, ns, opens) -> bool
    # Wait: even faster — cache plain tok -> is_in_lexicon first, and only run resolve_source
    # for tokens not obviously in _STOP_TOKENS / standard Mathlib prefixes.
    lex_names = lexicon.names
    # Fast exact prefilter: if the first component of `tok` never appears as ANY segment
    # of any lexicon name, `lexicon.resolve_source(tok, ...)` is guaranteed to return None.
    lex_first_segs: Set[str] = set()
    for nm in lex_names:
        for seg in nm.split("."):
            lex_first_segs.add(seg)
    resolve_cache: Dict[Tuple[str, str, Tuple[str, ...]], bool] = {}
    _STD_PREFIXES = ("Mathlib.", "Lean.", "Nat.", "Int.", "Rat.", "Real.", "Complex.",
                     "Finset.", "Set.", "List.", "Array.", "Option.", "Bool.", "String.",
                     "Filter.", "Topology.", "MeasureTheory.", "CategoryTheory.",
                     "AlgebraicGeometry.", "LinearMap.", "Matrix.", "Polynomial.",
                     "PowerSeries.", "Submodule.", "Ideal.", "RingHom.", "AlgHom.",
                     "MonoidHom.", "NumberField.", "Padic.", "DirichletCharacter.",
                     "LSeries.", "ArithmeticFunction.", "ZMod.", "ENNReal.", "NNReal.")

    for r in recs:
        mod = r["module"]
        parts = mod.split(".")
        folder_ns = ".".join(parts[:-1]) if len(parts) > 1 else ""
        folder_l2 = f"{parts[0]}.{parts[1]}" if len(parts) >= 2 else parts[0]
        folder_l3 = f"{parts[0]}.{parts[1]}.{parts[2]}" if len(parts) >= 3 else folder_l2

        # Exact project imports (filtered to modules actually in this tree)
        proj_imps = [imp for imp in r["proj_imports"] if imp in module_set and imp != mod]
        p_cnt = len(proj_imps)
        if p_cnt > 0:
            same_l2 = sum(
                1 for imp in proj_imps
                if (f"{imp.split('.')[0]}.{imp.split('.')[1]}" if "." in imp else imp) == folder_l2
            ) / p_cnt
        else:
            same_l2 = -1.0
        mod_folder_meta.append((folder_ns, folder_l2, folder_l3, p_cnt, round(same_l2, 4)))
        folder_l3_proj_imp_sum[folder_l3] += p_cnt
        folder_l3_count[folder_l3] += 1

        # Namespace matrices (BOTH rules!)
        for ns2, cnt in r["p2_ns2"].items():
            p2_matrix_decls[(folder_l2, ns2)] += cnt
            p2_matrix_mods[(folder_l2, ns2)] += 1
        for ns2, cnt in r["lean_ns2"].items():
            lean_matrix_decls[(folder_l2, ns2)] += cnt
            lean_matrix_mods[(folder_l2, ns2)] += 1

        # Primary true Lean-scoped declared namespace
        if r["lean_ns2"]:
            prim_ns = sorted(r["lean_ns2"].items(), key=lambda kv: (-kv[1], kv[0]))[0][0]
            folder_l2_ns_mod_counts[folder_l2][prim_ns] += 1
            folder_l2_top_ns_counts[folder_l2][prim_ns.split(".", 1)[0]] += 1
            folder_l2_non_shim[folder_l2] += 1
        else:
            prim_ns = ""
        mod_primary_ns.append(prim_ns)

        # Build Mathlib/core feature vector (imports + standard opens + non-local header type-tokens + forensic computational)
        feat: Dict[str, float] = collections.defaultdict(float)
        dom_w: Dict[str, float] = collections.defaultdict(float)
        std_tok_counts: collections.Counter = collections.Counter()

        # 1) Granular Mathlib.* subimports (high weight: 3.0 each)
        for imp in r["mathlib_subimports"]:
            feat[f"imp:{imp}"] += 3.0
            for d in _token_domains(imp):
                dom_w[d] += 3.0

        # 2) Non-project `open` namespaces (weight: 2.0 each)
        for op in r["opens"]:
            # Skip project-local namespaces (anything matching a top-level project folder or lexicon prefix)
            top_op = op.split(".", 1)[0]
            if top_op in ("Development", "Formalism", "GroundTheory", "CompanionTheory",
                          "ReciprocityTheory", "PositivityTheory", "GlobalTheory",
                          "UpperTheory", "LateralTheory", "BuildAid", "Supplements", "Lemmata"):
                continue
            if op in lex_names:
                continue
            feat[f"open:{op}"] += 2.0
            for d in _token_domains(op):
                dom_w[d] += 2.0

        # 3) Header type-tokens (non-local only!)
        ctx = r["ctx"]
        for tok, cnt in r["raw_header_toks"].items():
            if tok in _STOP_TOKENS:
                continue
            is_local = False
            if not tok.startswith(_STD_PREFIXES):
                if tok in lex_names:
                    is_local = True
                elif tok.split(".", 1)[0] in lex_first_segs:
                    for ns_c, op_c in ctx:
                        ck = (tok, ns_c, op_c)
                        hit = resolve_cache.get(ck)
                        if hit is None:
                            hit = lexicon.resolve_source(tok, ns_c, op_c) is not None
                            if len(resolve_cache) < 500000:
                                resolve_cache[ck] = hit
                        if hit:
                            is_local = True
                            break
            if is_local:
                continue
            w = 1.0 + math.log2(cnt)
            std_tok_counts[tok] += cnt
            feat[f"tok:{tok}"] += w
            for d in _token_domains(tok):
                dom_w[d] += w

        # 4) Computational kernel-check marker (decide +kernel / metaprogramming)
        for fl in r["forensic_flags"]:
            feat[f"flag:{fl}"] += 3.0
            for d in _token_domains(fl):
                dom_w[d] += 3.0

        # Keep top 24 features per module for fast, sharp centroid similarity
        if len(feat) > 24:
            top_f = dict(sorted(feat.items(), key=lambda kv: (-kv[1], kv[0]))[:24])
        else:
            top_f = dict(feat)
        for k in top_f:
            doc_freq[k] += 1
        mod_features.append(top_f)
        mod_domains.append(dict(dom_w))
        mod_top_toks.append([t for t, _ in std_tok_counts.most_common(15)])

    # Compute IDF weights and folder centroids (L3 primary, L2 fallback)
    idf: Dict[str, float] = {
        k: math.log((1.0 + n_files) / (1.0 + df)) + 1.0
        for k, df in doc_freq.items()
    }
    l3_centroid: Dict[str, Dict[str, float]] = collections.defaultdict(lambda: collections.defaultdict(float))
    l3_n_vec: collections.Counter = collections.Counter()
    l2_centroid: Dict[str, Dict[str, float]] = collections.defaultdict(lambda: collections.defaultdict(float))
    l2_n_vec: collections.Counter = collections.Counter()

    mod_tfidf: List[Dict[str, float]] = []
    for i, feat in enumerate(mod_features):
        _, l2, l3, _, _ = mod_folder_meta[i]
        tv = {k: v * idf[k] for k, v in feat.items()}
        norm = math.sqrt(sum(v * v for v in tv.values()))
        if norm > 0.0:
            tv = {k: v / norm for k, v in tv.items()}
            if recs[i]["is_shim"] == 0:
                c3 = l3_centroid[l3]
                c2 = l2_centroid[l2]
                for k, v in tv.items():
                    c3[k] += v
                    c2[k] += v
                l3_n_vec[l3] += 1
                l2_n_vec[l2] += 1
        mod_tfidf.append(tv)

    # Normalize & trim centroids to top 64 terms each
    def _finalize_centroid(raw: Dict[str, Dict[str, float]]) -> Dict[str, Dict[str, float]]:
        res: Dict[str, Dict[str, float]] = {}
        for folder, vec in raw.items():
            if len(vec) > 64:
                vec = dict(sorted(vec.items(), key=lambda kv: (-kv[1], kv[0]))[:64])
            norm = math.sqrt(sum(v * v for v in vec.values()))
            res[folder] = {k: v / norm for k, v in vec.items()} if norm > 0.0 else {}
        return res

    l3_cent_norm = _finalize_centroid(l3_centroid)
    l2_cent_norm = _finalize_centroid(l2_centroid)

    # Detect systematic bulk folder_l2 -> foreign top_ns remappings automatically
    # (e.g. Development.AbelianVarietyTheory declaring GlobalTheory.* across 99.9% of modules).
    bulk_remap_pairs: Set[Tuple[str, str]] = set()
    bulk_remap_rows: List[Tuple[str, str, int, int, float]] = []
    for fl2, top_ctr in sorted(folder_l2_top_ns_counts.items()):
        f_top = fl2.split(".", 1)[0]
        tot_ns = max(1, folder_l2_non_shim[fl2])
        for d_top, cnt in sorted(top_ctr.items(), key=lambda kv: (-kv[1], kv[0])):
            if d_top != f_top and cnt >= BULK_REMAP_MIN_MODULES and (cnt / tot_ns) >= BULK_REMAP_MIN_SHARE:
                bulk_remap_pairs.add((fl2, d_top))
                bulk_remap_rows.append((fl2, d_top, cnt, tot_ns, round(cnt / tot_ns, 4)))
    bulk_remap_rows.sort(key=lambda x: (-x[2], x[0], x[1]))

    # Score misfiles & prepare SQLite rows
    mf_rows: List[Tuple[Any, ...]] = []
    misfile_candidates: List[Dict[str, Any]] = []
    all_band_counts: collections.Counter = collections.Counter()
    all_band_modules: Dict[str, List[Tuple[str, str]]] = collections.defaultdict(list)

    alpha_groups: Dict[str, List[Tuple[str, int]]] = collections.defaultdict(list)
    sigset_groups: Dict[str, List[Tuple[str, int]]] = collections.defaultdict(list)
    wrapper_groups: Dict[Tuple[str, str], List[Tuple[str, int]]] = collections.defaultdict(list)
    shim_members: List[Tuple[str, int]] = []

    # Folder fingerprint aggregation
    ff_agg: Dict[Tuple[str, int], Dict[str, Any]] = {}

    def _ff(folder: str, depth: int) -> Dict[str, Any]:
        key = (folder, depth)
        d = ff_agg.get(key)
        if d is None:
            d = {
                "module_count": 0, "non_shim_count": 0, "decl_count": 0,
                "lines_wc": 0, "mathlib_all_count": 0,
                "domains": collections.Counter(),
                "ns": collections.Counter(),
                "toks": collections.Counter(),
            }
            ff_agg[key] = d
        return d

    total_decls = 0
    total_lines_wc = 0
    dup_mathlib_files = 0
    mathlib_all_files = 0
    mathlib_subimport_files = 0

    for i, r in enumerate(recs):
        mod = r["module"]
        folder_ns, folder_l2, folder_l3, p_cnt, same_l2_ratio = mod_folder_meta[i]
        prim_ns = mod_primary_ns[i]
        dom_w = mod_domains[i]
        top_toks = mod_top_toks[i]

        total_decls += r["decl_count"]
        total_lines_wc += r["lines_wc"]
        if r["mathlib_all_count"] >= 1:
            mathlib_all_files += 1
        if r["mathlib_all_count"] >= 2:
            dup_mathlib_files += 1
        if r["mathlib_subimports"]:
            mathlib_subimport_files += 1

        # Normalize domain distribution
        dom_total = sum(dom_w.values())
        if dom_total > 0:
            dom_dist = {k: round(v / dom_total, 4) for k, v in sorted(dom_w.items(), key=lambda kv: (-kv[1], kv[0]))}
            top_domain = next(iter(dom_dist))
        else:
            dom_dist = {}
            top_domain = "none"

        fp_payload = json.dumps({
            "sub": r["mathlib_subimports"],
            "dom": top_domain,
            "toks": sorted(top_toks),
        }, sort_keys=True, separators=(",", ":"))
        fp_hash = hashlib.sha256(fp_payload.encode("utf-8")).hexdigest()[:16]

        mf_rows.append((
            mod, r["file_path"], folder_ns, folder_l2, folder_l3,
            r["lines_wc"], r["decl_count"], r["is_shim"], r["is_stmt_wrapper"],
            r["mathlib_all_count"], json.dumps(r["mathlib_subimports"]),
            p_cnt, same_l2_ratio, json.dumps(r["opens"][:30]),
            prim_ns, json.dumps(r["lean_ns2"], sort_keys=True),
            r["uses_root_escape"], top_domain, json.dumps(dom_dist),
            json.dumps(top_toks), fp_hash, r["sigset_hash"],
            r["alpha_clone_sig"], json.dumps(r["forensic_flags"]),
        ))

        # Folder aggregates (depth 2 and depth 3)
        for fld, dp in ((folder_l2, 2), (folder_l3, 3)):
            if dp == 3 and folder_l3 == folder_l2:
                continue
            fd = _ff(fld, dp)
            fd["module_count"] += 1
            if not r["is_shim"]:
                fd["non_shim_count"] += 1
            fd["decl_count"] += r["decl_count"]
            fd["lines_wc"] += r["lines_wc"]
            if r["mathlib_all_count"] >= 1:
                fd["mathlib_all_count"] += 1
            if top_domain != "none":
                fd["domains"][top_domain] += 1
            if prim_ns:
                fd["ns"][prim_ns] += 1
            for t in top_toks[:6]:
                fd["toks"][t] += 1

        # Boilerplate grouping
        if r["is_shim"]:
            shim_members.append((mod, r["lines_wc"]))
        else:
            if r["alpha_clone_sig"] != "shim_empty":
                alpha_groups[r["alpha_clone_sig"]].append((mod, r["lines_wc"]))
            if r["decl_count"] >= 1 and r["sigset_hash"] != "empty":
                sigset_groups[r["sigset_hash"]].append((mod, r["lines_wc"]))
            if r["is_stmt_wrapper"]:
                wrapper_groups[(folder_l2, r["wrapper_kind"])].append((mod, r["lines_wc"]))

        # Calibrated anomaly scoring & 4-band classification (all non-shim modules with >= 1 decl)
        if not r["is_shim"] and r["decl_count"] >= 1 and folder_ns:
            ns_mism, mism_kind = _ns_mismatch_score(prim_ns, folder_ns, mod)
            ns_cnt_in_folder = folder_l2_ns_mod_counts[folder_l2].get(prim_ns, 0)
            folder_ns_tot = max(1, folder_l2_non_shim[folder_l2])
            ns_rarity = round(1.0 - (ns_cnt_in_folder / folder_ns_tot), 5)
            d_top = prim_ns.split(".", 1)[0] if prim_ns else ""
            is_foreign_top = bool(prim_ns and d_top != folder_l2.split(".", 1)[0])
            is_bulk = 1 if (folder_l2, d_top) in bulk_remap_pairs else 0
            ns_outlier = (
                (1.0 / (1.0 + math.log10(max(1, ns_cnt_in_folder))))
                if (ns_mism > 0.0 or ns_cnt_in_folder <= 5)
                else 0.0
            )

            # Refine mismatch kind for UI/report clarity
            if mism_kind == "foreign_top_ns":
                if ns_cnt_in_folder <= 5:
                    mism_kind = "isolated_foreign_ns"
                elif r["uses_root_escape"]:
                    mism_kind = "root_escape_foreign_ns"
                else:
                    mism_kind = "pervasive_foreign_ns"

            expected_doms = infer_expected_domains(folder_ns)
            if expected_doms and dom_total >= 3.0:
                matched_mass = sum(dom_dist.get(d, 0.0) for d in expected_doms)
                dom_conflict = round(max(0.0, 1.0 - matched_mass), 4)
            else:
                dom_conflict = 0.0

            cent = l3_cent_norm.get(folder_l3) if l3_n_vec[folder_l3] >= 5 else l2_cent_norm.get(folder_l2, {})
            if l3_n_vec[folder_l3] >= 5 and l3_n_vec[folder_l3] <= 30:
                # Leave-one-out sibling centroid on small folders so a module does not dilute its own outlier distance
                raw_c = l3_centroid[folder_l3]
                loo = {k: v - mod_tfidf[i].get(k, 0.0) for k, v in raw_c.items() if v - mod_tfidf[i].get(k, 0.0) > 1e-9}
                cent_dist = _cosine_distance(mod_tfidf[i], loo)
            else:
                cent_dist = _cosine_distance(mod_tfidf[i], cent)

            folder_avg_imps = folder_l3_proj_imp_sum[folder_l3] / max(1, folder_l3_count[folder_l3])
            if p_cnt == 0 and folder_avg_imps >= 0.5:
                graph_iso = 1.0
            elif p_cnt > 0:
                graph_iso = round(max(0.0, 1.0 - same_l2_ratio), 4)
            else:
                graph_iso = 0.0

            raw_score = (
                MISFILE_WEIGHTS["ns_outlier"] * ns_outlier
                + MISFILE_WEIGHTS["folder_domain_conflict"] * dom_conflict
                + MISFILE_WEIGHTS["centroid_distance"] * cent_dist
                + MISFILE_WEIGHTS["graph_isolation"] * graph_iso
            )
            if is_foreign_top and not is_bulk:
                raw_score = min(1.0, raw_score + NON_BULK_FOREIGN_NS_BONUS)
            score = round(raw_score * (WRAPPER_DAMPING if r["is_stmt_wrapper"] else 1.0), 4)

            exp_doms_str = "+".join(sorted(expected_doms)) if expected_doms else "unspecified"
            # Multi-band calibration: cleanly separates true extreme/cross-domain outliers from
            # systematic bulk folder->namespace remappings (solving the Phase 3 67% noise problem).
            if (not r["is_stmt_wrapper"] and r["decl_count"] >= 3 and ns_cnt_in_folder <= 3
                    and dom_conflict >= 0.90 and cent_dist >= 0.85 and graph_iso >= 0.90
                    and score >= 0.90):
                band = "extreme_outlier"
            elif (not r["is_stmt_wrapper"] and r["decl_count"] >= 2
                    and dom_conflict >= 0.85 and cent_dist >= 0.75 and score >= 0.80):
                band = "cross_domain_misfile"
            elif (not r["is_stmt_wrapper"] and score >= 0.65
                    and (not is_bulk or (ns_cnt_in_folder <= 5 and cent_dist >= 0.65))):
                band = "isolated_ns_outlier"
            elif is_bulk:
                band = "bulk_namespace_remapping"
            else:
                band = "normal"

            all_band_counts[band] += 1
            all_band_modules[band].append((mod, exp_doms_str))

            # Store ONLY genuine calibrated anomaly bands in the alertable `misfiles` table
            # (`extreme_outlier` + `cross_domain_misfile` -> tier='high'; `isolated_ns_outlier` -> tier='medium').
            # Systematic `bulk_namespace_remapping` rows are documented separately in `bulk_namespace_remappings`.
            if band in ("extreme_outlier", "cross_domain_misfile", "isolated_ns_outlier"):
                tier = "high" if band in ("extreme_outlier", "cross_domain_misfile") else "medium"
                flag_decl = None
                if r["flagged_decls"]:
                    flag_decl = r["flagged_decls"][0][1]
                elif r["lean_decl_names"]:
                    flag_decl = r["lean_decl_names"][0]

                obs_doms_str = "+".join(list(dom_dist.keys())[:2]) if dom_dist else "none"
                reasons = [f"band={band}"]
                if ns_mism > 0 or ns_cnt_in_folder <= 5:
                    bulk_note = ", bulk-remapped folder" if is_bulk else ""
                    reasons.append(
                        f"declared_ns={prim_ns} vs folder={folder_ns} ({mism_kind}, {ns_cnt_in_folder}/{folder_ns_tot} in {folder_l2}{bulk_note})"
                    )
                if dom_conflict >= 0.5:
                    reasons.append(f"domain={obs_doms_str} vs folder_expected={exp_doms_str} (conflict={dom_conflict:.2f})")
                if cent_dist >= 0.5:
                    reasons.append(f"sibling_centroid_dist={cent_dist:.2f}")
                if graph_iso >= 0.8:
                    reasons.append("0 project imports (isolated island)" if p_cnt == 0 else f"cross-folder imports ({p_cnt}, same_l2={same_l2_ratio:.2f})")
                if r["forensic_flags"]:
                    fl_txt = ",".join(r["forensic_flags"])
                    if r["flagged_decls"]:
                        reasons.append(f"flags={fl_txt} ({r['flagged_decls'][0][1]})")
                    else:
                        reasons.append(f"flags={fl_txt}")

                misfile_candidates.append({
                    "module": mod,
                    "file_path": r["file_path"],
                    "declared_ns": prim_ns,
                    "folder_ns": folder_ns,
                    "folder_l2": folder_l2,
                    "score": score,
                    "tier": tier,
                    "band": band,
                    "is_bulk_remap": is_bulk,
                    "ns_mismatch_kind": mism_kind,
                    "ns_count_in_folder": ns_cnt_in_folder,
                    "ns_rarity_in_folder": ns_rarity,
                    "domain_expected": exp_doms_str,
                    "domain_observed": obs_doms_str,
                    "folder_domain_conflict": dom_conflict,
                    "centroid_distance": cent_dist,
                    "graph_isolation": graph_iso,
                    "is_statement_wrapper": r["is_stmt_wrapper"],
                    "flag_decl": flag_decl,
                    "reason": "; ".join(reasons),
                    "decl_count": r["decl_count"],
                    "lines_wc": r["lines_wc"],
                    "provenance": "L",
                })

    # Rank misfiles deterministically (strictly descending by score so monotonicity holds!)
    misfile_candidates.sort(key=lambda x: (-x["score"], -x["decl_count"], x["module"]))
    misfile_rows = [
        (
            rank, m["module"], m["file_path"], m["declared_ns"], m["folder_ns"],
            m["folder_l2"], m["score"], m["tier"], m["ns_mismatch_kind"],
            m["ns_count_in_folder"], m["ns_rarity_in_folder"], m["domain_expected"],
            m["domain_observed"], m["folder_domain_conflict"], m["centroid_distance"],
            m["graph_isolation"], m["is_statement_wrapper"], m["flag_decl"],
            m["reason"], m["provenance"], m["band"], m["is_bulk_remap"],
        )
        for rank, m in enumerate(misfile_candidates, 1)
    ]

    # Build boilerplate_clusters + boilerplate_members
    bc_rows: List[Tuple[Any, ...]] = []
    bm_rows: List[Tuple[Any, ...]] = []
    cluster_stats: Dict[str, Dict[str, int]] = {}

    def _add_cluster(cid: str, kind: str, sig_h: str, members: List[Tuple[str, int]], summary_txt: str) -> None:
        members_s = sorted(members, key=lambda x: x[0])
        sz = len(members_s)
        tot_ln = sum(ln for _, ln in members_s)
        rep = members_s[0][0]
        sample = [m for m, _ in members_s[:10]]
        bc_rows.append((cid, kind, sz, max(0, sz - 1), tot_ln, rep, sig_h, summary_txt, json.dumps(sample)))
        for m, ln in members_s:
            bm_rows.append((cid, m, ln))

    # 1) Exact Phase-2 alpha-renamed body clones
    alpha_multi = [(sig, mems) for sig, mems in alpha_groups.items() if len(mems) >= 2]
    alpha_multi.sort(key=lambda x: (-len(x[1]), x[0]))
    for idx, (sig, mems) in enumerate(alpha_multi, 1):
        _add_cluster(
            f"alpha:{idx:04d}", "alpha_body_clone", sig, mems,
            f"Exact alpha-renamed file-body clone ({len(mems)} modules, {sum(l for _, l in mems)} lines)",
        )
    cluster_stats["alpha_body_clone"] = {
        "clusters": len(alpha_multi),
        "modules": sum(len(m) for _, m in alpha_multi),
        "redundant_modules": sum(len(m) - 1 for _, m in alpha_multi),
        "largest_cluster": len(alpha_multi[0][1]) if alpha_multi else 0,
    }

    # 2) Signature-set (s1t multiset) clones (statement-identical modules across proof bodies)
    sigset_multi = [(sig, mems) for sig, mems in sigset_groups.items() if len(mems) >= 2]
    sigset_multi.sort(key=lambda x: (-len(x[1]), x[0]))
    for idx, (sig, mems) in enumerate(sigset_multi, 1):
        _add_cluster(
            f"sigset:{idx:04d}", "sigset_clone", sig, mems,
            f"Identical normalized declaration signature-set s1t ({len(mems)} modules)",
        )
    cluster_stats["sigset_clone"] = {
        "clusters": len(sigset_multi),
        "modules": sum(len(m) for _, m in sigset_multi),
        "redundant_modules": sum(len(m) - 1 for _, m in sigset_multi),
        "largest_cluster": len(sigset_multi[0][1]) if sigset_multi else 0,
    }

    # 3) Import-only shims
    if shim_members:
        _add_cluster(
            "shim:0001", "import_shim", "shim_empty", shim_members,
            f"Import-only re-export shims with 0 declarations ({len(shim_members)} modules)",
        )
    cluster_stats["import_shim"] = {
        "clusters": 1 if shim_members else 0,
        "modules": len(shim_members),
        "redundant_modules": len(shim_members),
        "largest_cluster": len(shim_members),
    }

    # 4) Auto-generated *Statement forwarding wrappers
    wrap_multi = [(k, mems) for k, mems in wrapper_groups.items() if len(mems) >= 2]
    wrap_multi.sort(key=lambda x: (-len(x[1]), x[0]))
    for idx, ((fl2, wkind), mems) in enumerate(wrap_multi, 1):
        wh = hashlib.sha256(f"{fl2}:{wkind}".encode("utf-8")).hexdigest()[:16]
        _add_cluster(
            f"wrapper:{idx:04d}", "statement_wrapper", wh, mems,
            f"Single-decl *Statement wrapper ({wkind}) under {fl2} ({len(mems)} modules)",
        )
    cluster_stats["statement_wrapper"] = {
        "clusters": len(wrap_multi),
        "modules": sum(len(m) for _, m in wrap_multi),
        "redundant_modules": sum(len(m) for _, m in wrap_multi),
        "total_statement_wrappers": sum(len(m) for m in wrapper_groups.values()),
        "largest_cluster": len(wrap_multi[0][1]) if wrap_multi else 0,
    }

    # Namespace-folder matrix rows (BOTH counting rules!)
    nfm_rows: List[Tuple[Any, ...]] = []
    for (fl2, ns2), dcnt in sorted(p2_matrix_decls.items()):
        nfm_rows.append((fl2, "phase2_literal_2comp", ns2, dcnt, p2_matrix_mods[(fl2, ns2)]))
    for (fl2, ns2), dcnt in sorted(lean_matrix_decls.items()):
        nfm_rows.append((fl2, "lean_scoped_2comp", ns2, dcnt, lean_matrix_mods[(fl2, ns2)]))

    # Folder fingerprint rows
    ff_rows: List[Tuple[Any, ...]] = []
    for (fld, dp), d in sorted(ff_agg.items(), key=lambda kv: (kv[0][1], -kv[1]["module_count"], kv[0][0])):
        exp_d = sorted(infer_expected_domains(fld))
        ff_rows.append((
            fld, dp, d["module_count"], d["non_shim_count"], d["decl_count"],
            d["lines_wc"], d["mathlib_all_count"], json.dumps(exp_d),
            json.dumps(d["domains"].most_common(6)),
            json.dumps(d["ns"].most_common(8)),
            json.dumps(d["toks"].most_common(12)),
        ))

    # Extract F1 Development.AbelianVarietyTheory split under BOTH counting rules
    avt = "Development.AbelianVarietyTheory"
    avt_p2_all = sorted(
        [(ns, cnt, p2_matrix_mods[(avt, ns)]) for (fl, ns), cnt in p2_matrix_decls.items() if fl == avt],
        key=lambda x: (-x[1], x[0]),
    )
    avt_lean_all = sorted(
        [(ns, cnt, lean_matrix_mods[(avt, ns)]) for (fl, ns), cnt in lean_matrix_decls.items() if fl == avt],
        key=lambda x: (-x[1], x[0]),
    )
    f1_avt_split = {
        "folder_l2": avt,
        "modules": ff_agg.get((avt, 2), {}).get("module_count", 0),
        "phase2_literal_2comp": {
            "counting_rule": (
                "Column-0 keyword declarations under Development.AbelianVarietyTheory grouped by "
                "first 2 name components using Phase-2 scanner.py rules (literal `_root_.` kept "
                "as component 0; anonymous `end` pops namespace stack)."
            ),
            "total_decls": sum(x[1] for x in avt_p2_all),
            "top_namespaces": [
                {"namespace": ns, "decls": cnt, "modules": mcnt}
                for ns, cnt, mcnt in avt_p2_all[:12]
            ],
        },
        "lean_scoped_2comp": {
            "counting_rule": (
                "Column-0 named declarations under Development.AbelianVarietyTheory grouped by "
                "first 2 name components using true Lean scoping (`_root_.` stripped; `section` / "
                "`namespace` / multi-component `end` tracked via sighash.iter_source_decls)."
            ),
            "total_decls": sum(x[1] for x in avt_lean_all),
            "top_namespaces": [
                {"namespace": ns, "decls": cnt, "modules": mcnt}
                for ns, cnt, mcnt in avt_lean_all[:12]
            ],
        },
    }

    # Verify whether GlobalTheory.PrimeRecip.table_ok's module was flagged (generic check!)
    known_misfile_hit = None
    for rank, m in enumerate(misfile_candidates, 1):
        if m["flag_decl"] == "GlobalTheory.PrimeRecip.table_ok" or m["declared_ns"] == "GlobalTheory.PrimeRecip":
            known_misfile_hit = {
                "rank": rank,
                "module": m["module"],
                "file_path": m["file_path"],
                "declared_ns": m["declared_ns"],
                "folder_ns": m["folder_ns"],
                "score": m["score"],
                "tier": m["tier"],
                "band": m["band"],
                "flag_decl": m["flag_decl"],
                "reason": m["reason"],
            }
            break

    # Independent kernel-grounded precision calibration per band (read-only kernel.db, if available)
    kernel_cal = _calibrate_bands_against_kernel(
        kernel_db or "",
        {b: all_band_modules[b] for b in ("extreme_outlier", "cross_domain_misfile", "isolated_ns_outlier", "bulk_namespace_remapping")},
        dict(all_band_counts),
    )

    mirror_root = os.path.dirname(os.path.abspath(src_dir))
    mirror_commit = _git_head(mirror_root)
    elapsed = round(time.time() - t0, 2)

    calibrated_bands = {
        b: {
            "count": int(all_band_counts.get(b, 0)),
            "pct_of_corpus": round(100.0 * all_band_counts.get(b, 0) / max(1, n_files), 3),
        }
        for b in ("extreme_outlier", "cross_domain_misfile", "isolated_ns_outlier", "bulk_namespace_remapping", "normal")
    }

    meta_dict: Dict[str, Any] = {
        "schema": SCHEMA_VERSION,
        "provenance": f"[L] extracted deterministically from {os.path.relpath(src_dir, REPO) if os.path.abspath(src_dir).startswith(REPO) else src_dir}" + (f"@{mirror_commit[:8]}" if mirror_commit else ""),
        "mirror_commit": mirror_commit,
        "file_count": n_files,
        "total_lines_wc": total_lines_wc,
        "total_decls_lean_scoped": total_decls,
        "tier1_lexicon_names": len(lexicon),
        "tier1_lexicon_id": lexicon.id,
        "mathlib_import_stats": {
            "modules_importing_whole_mathlib": mathlib_all_files,
            "modules_with_duplicate_mathlib_import": dup_mathlib_files,
            "modules_with_granular_mathlib_subimports": mathlib_subimport_files,
        },
        "misfile_scoring": {
            "weights": MISFILE_WEIGHTS,
            "non_bulk_foreign_ns_bonus": NON_BULK_FOREIGN_NS_BONUS,
            "wrapper_damping": WRAPPER_DAMPING,
            "bulk_remap_rule": f"foreign top_ns with >= {BULK_REMAP_MIN_MODULES} modules and >= {int(BULK_REMAP_MIN_SHARE*100)}% of folder_l2",
            "alertable_misfiles_total": len(misfile_candidates),
            "alertable_pct_of_corpus": round(100.0 * len(misfile_candidates) / max(1, n_files), 3),
            "high_tier_count": sum(1 for m in misfile_candidates if m["tier"] == "high"),
            "medium_tier_count": sum(1 for m in misfile_candidates if m["tier"] == "medium"),
            "calibrated_bands": calibrated_bands,
            "kernel_precision_calibration": kernel_cal,
        },
        "bulk_namespace_remappings": [
            {
                "folder_l2": r[0], "declared_top_ns": r[1],
                "module_count": r[2], "folder_non_shim_count": r[3], "share_of_folder": r[4],
            }
            for r in bulk_remap_rows
        ],
        "f1_abelian_variety_split": f1_avt_split,
        "f1_known_misfile_check": known_misfile_hit,
        "boilerplate_stats": cluster_stats,
        "elapsed_seconds": elapsed,
    }

    # Atomic SQLite write
    t3 = time.time()
    os.makedirs(os.path.dirname(os.path.abspath(db_path)), exist_ok=True)
    tmp_db = (db_path[:-3] + "_building.db") if db_path.endswith(".db") else (db_path + ".building")
    for suf in ("", "-wal", "-shm", "-journal"):
        if os.path.exists(tmp_db + suf):
            os.remove(tmp_db + suf)
    conn = sqlite3.connect(tmp_db)
    try:
        conn.executescript("PRAGMA journal_mode=OFF; PRAGMA synchronous=OFF; PRAGMA temp_store=MEMORY;" + SCHEMA_SQL)
        for k, v in meta_dict.items():
            conn.execute("INSERT INTO meta(key, value_json) VALUES (?, ?)", (k, json.dumps(v, sort_keys=True, ensure_ascii=False)))
        conn.executemany(
            "INSERT INTO module_fingerprints VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            mf_rows,
        )
        conn.executemany(
            "INSERT INTO misfiles VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            misfile_rows,
        )
        conn.executemany("INSERT INTO bulk_namespace_remappings VALUES (?,?,?,?,?)", bulk_remap_rows)
        conn.executemany("INSERT INTO namespace_folder_matrix VALUES (?,?,?,?,?)", nfm_rows)
        conn.executemany("INSERT INTO boilerplate_clusters VALUES (?,?,?,?,?,?,?,?,?)", bc_rows)
        conn.executemany("INSERT INTO boilerplate_members VALUES (?,?,?)", bm_rows)
        conn.executemany("INSERT INTO folder_fingerprints VALUES (?,?,?,?,?,?,?,?,?,?,?)", ff_rows)
        conn.executescript(INDEX_SQL)
        conn.execute("ANALYZE;")
        conn.commit()
    finally:
        conn.close()
    os.replace(tmp_db, db_path)

    # Compact committed summary JSON (identifiers, counts, hashes, scores — ZERO raw .lean text!)
    summary_obj = {
        **meta_dict,
        "top_misfiles": [
            {
                "rank": rank,
                "module": m["module"],
                "file_path": m["file_path"],
                "declared_ns": m["declared_ns"],
                "folder_ns": m["folder_ns"],
                "score": m["score"],
                "tier": m["tier"],
                "band": m["band"],
                "is_bulk_remap": m["is_bulk_remap"],
                "ns_mismatch_kind": m["ns_mismatch_kind"],
                "domain_expected": m["domain_expected"],
                "domain_observed": m["domain_observed"],
                "centroid_distance": m["centroid_distance"],
                "graph_isolation": m["graph_isolation"],
                "decl_count": m["decl_count"],
                "lines_wc": m["lines_wc"],
                "flag_decl": m["flag_decl"],
                "reason": m["reason"],
                "provenance": "L",
            }
            for rank, m in enumerate(misfile_candidates[:100], 1)
        ],
        "top_boilerplate_clusters": {
            kind: [
                {
                    "cluster_id": r[0], "kind": r[1], "size": r[2],
                    "redundant_modules": r[3], "total_lines": r[4],
                    "representative": r[5], "sig_hash": r[6],
                    "summary": r[7], "sample_members": json.loads(r[8]),
                }
                for r in bc_rows if r[1] == kind
            ][:20]
            for kind in ("alpha_body_clone", "sigset_clone", "import_shim", "statement_wrapper")
        },
        "top_folder_l2_fingerprints": [
            {
                "folder": r[0], "modules": r[2], "decls": r[4], "lines_wc": r[5],
                "mathlib_all_count": r[6],
                "expected_domains": json.loads(r[7]),
                "top_domains": json.loads(r[8]),
                "top_declared_ns": json.loads(r[9])[:5],
                "top_type_tokens": json.loads(r[10])[:8],
            }
            for r in ff_rows if r[1] == 2
        ][:40],
    }

    if summary_path:
        os.makedirs(os.path.dirname(os.path.abspath(summary_path)), exist_ok=True)
        with open(summary_path, "w", encoding="utf-8") as f:
            json.dump(summary_obj, f, indent=2, sort_keys=True, ensure_ascii=False)
            f.write("\n")

    if verbose:
        print(
            f"[tier1] wrote {db_path} ({len(mf_rows):,} fingerprints, {len(misfile_rows):,} misfiles, "
            f"{len(bc_rows):,} boilerplate clusters) in {time.time()-t3:.1f}s (total {time.time()-t0:.1f}s)",
            flush=True,
        )
    return summary_obj


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="FLIRT Tier 1: deterministic fingerprinting, misfiles & boilerplate collapse")
    ap.add_argument("--src", default=DEFAULT_SRC, help="Lean src/ directory")
    ap.add_argument("--db", default=DEFAULT_DB, help="Output SQLite DB path")
    ap.add_argument("--summary", default=DEFAULT_SUMMARY, help="Output compact summary JSON path")
    ap.add_argument("--threads", type=int, default=MAX_THREADS, help=f"Worker processes (cap {MAX_THREADS})")
    ap.add_argument("--expect-files", type=int, default=None, help="Assert exact .lean file count")
    ap.add_argument("--kernel-db", default=DEFAULT_KERNEL_DB, help="Optional read-only kernel.db for band precision calibration")
    ap.add_argument("--quiet", action="store_true")
    a = ap.parse_args(argv)
    s = run_tier1(
        src_dir=a.src,
        db_path=a.db,
        summary_path=a.summary or None,
        threads=a.threads,
        expect_files=a.expect_files,
        kernel_db=a.kernel_db or None,
        verbose=not a.quiet,
    )
    if not a.quiet:
        avt = s["f1_abelian_variety_split"]["phase2_literal_2comp"]["top_namespaces"][:3]
        print("[tier1] F1 AbelianVarietyTheory (phase2_literal_2comp):", [(x["namespace"], x["decls"]) for x in avt])
        print("[tier1] F1 known misfile check:", s["f1_known_misfile_check"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
