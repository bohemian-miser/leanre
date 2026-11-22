#!/usr/bin/env python3
"""FLIRT Tier 2 -- kernel-exact matching & ground-truth audit against outputs/kernel/kernel.db.

    python3 leanre/flirt/tier2_kernel.py [--db outputs/flirt/tier2.db] [--kernel-db outputs/kernel/kernel.db]
    python3 leanre/flirt/tier2.py kernel

Consumes `kernel`'s SQLite database (`outputs/kernel/kernel.db`, schema in docs/KERNEL.md):
  - decls(id, name, kind, type_nodes, live_mask, stmt_mask, sighash, sighash_anon)
  - consts(name, decl_id, ckind, sighash, sighash_anon)
  - decl_module(decl_id, module, method, src_decl_id)

What this adds to `outputs/flirt/tier2.db`:
  1. `kernel_matches`: project constants whose kernel-elaborated type hash (`k1n` or `k1a`)
     equals that of a library constant present in the proof's export. For `ckind='thm'`
     (propositions), matching `k1n` means identical elaborated statement modulo binder
     names, binder info, universe parameter names, and mdata (docs/SIGHASH.md). For
     non-theorems (`def`, `opaque`, `induct`, ...), it means identical elaborated type
     signature only -- never identical definition body.
  2. Real-world ground-truth controls appended to `controls` (and summarized in `meta['kernel']`):
     - `kernel_lib_coverage`: share of export library constants found by exact name in our
       pinned dependency corpora (mathlib4, lean4, batteries).
     - `kernel_source_recall`: among project theorems whose `k1n` matches a pinned corpus
       theorem (real-world positives, both sides present in source tables), what fraction did
       source-level `s1n` / `s1t` / `strong` catch?
     - `kernel_source_precision`: among source-level theorem matches where both the proof
       decl and matched corpus decl appear in `kernel.db`, what fraction share the same `k1n`?

Never cross-compares `k1*` with `s1*` (they live in different spaces). All numbers are [L].
"""
from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sqlite3
import sys
import time
from typing import Any, Dict, List, Optional, Set, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
LEANRE = os.path.dirname(HERE)
REPO = os.path.dirname(LEANRE)
for _p in (LEANRE, HERE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

try:
    import sighash as _sighash  # type: ignore
    _norm_const_name = _sighash.norm_const_name
except Exception:  # pragma: no cover
    def _norm_const_name(name: str) -> str:
        if name.startswith("_private."):
            idx = name.find(".0.")
            if idx != -1:
                return name[idx + 3:]
        return name


DB_PATH = os.path.join(REPO, "outputs", "flirt", "tier2.db")
KERNEL_DB = os.path.join(REPO, "outputs", "kernel", "kernel.db")
DEP_REPOS = ("mathlib4", "lean4", "batteries")
_RE_COMPILER_AUX = re.compile(
    r"\._(?:proof|simp|sunfold|closed|unary|rarg|cstage|lambda|let)(?:_|\b)|\.(?:match|eq)_\d+(?:\.|$)"
)

# Known external/core top-level prefixes used only as a fallback when a constant has
# decl_module.module IS NULL and its name (or proper prefix) is not in DEP_REPOS corpus_sigs.
_LIB_TOP_PREFIXES = frozenset({
    "Init", "Std", "Lean", "Mathlib", "Batteries", "Aesop", "Qq", "Plausible",
    "ProofWidgets", "ImportGraph", "Cli", "Lake", "IO", "System",
    # Core prelude / Init root constants
    "Quot", "Eq", "HEq", "Nat", "Int", "Bool", "Prop", "PUnit", "Unit", "Empty", "PEmpty",
    "List", "Array", "ByteArray", "FloatArray", "String", "Substring", "Char", "Float",
    "UInt8", "UInt16", "UInt32", "UInt64", "USize", "Fin", "BitVec", "Subtype", "Sigma",
    "PSigma", "Prod", "PProd", "Sum", "PSum", "Option", "Except", "And", "Or", "Not", "Iff",
    "Exists", "True", "False", "Decidable", "DecidableEq", "DecidablePred", "DecidableRel",
    "WellFounded", "Acc", "Nonempty", "Classical", "Functor", "Applicative", "Monad",
    "Inhabited", "OfNat", "Add", "HAdd", "Sub", "HSub", "Mul", "HMul", "Div", "HDiv",
    "Mod", "HMod", "Pow", "HPow", "Neg", "LE", "LT", "GE", "GT", "BEq", "Ord", "Hashable",
    "ToString", "Repr", "GetElem", "Membership", "HasSubset", "Singleton", "EmptyCollection",
    "Insert", "Union", "Inter", "SDiff", "Complement", "Set", "Function", "Relation",
    "Equiv", "Order", "Preorder", "PartialOrder", "LinearOrder", "Lattice", "Ring", "Group",
    "Monoid", "Semiring", "Field", "Module", "Algebra", "CategoryTheory", "MeasureTheory",
    "Topology", "Filter", "Finset", "Fintype", "Multiset", "Polynomial", "Matrix", "Real",
    "Complex", "Rat", "NNReal", "ENNReal", "ENat", "ZMod", "Padic", "PadicInt", "WithTop",
    "WithBot", "WithZero", "AddMonoid", "AddGroup", "AddCommGroup", "AddCommMonoid",
    "CommMonoid", "CommGroup", "CommRing", "CommSemiring", "DivisionRing", "IsDomain",
    "CharZero", "NeZero", "Nontrivial", "Unique", "Subsingleton", "Fact", "Dite", "Ite",
    "dite", "ite", "cond", "id", "flip", "absurd", "False", "True", "congrArg", "congrFun",
    "congr", "funext", "propext", "Classical", "Choice", "Nonempty", "AutoParam", "OptParam",
    "outParam", "semiOutParam", "noConfusion", "brecOn", "below", "ibelow", "casesOn",
    "recOn", "binductionOn", "sizeOf", "SizeOf",
})

KERNEL_SCHEMA = """
DROP TABLE IF EXISTS kernel_matches;
DROP TABLE IF EXISTS kernel_const_origin;
CREATE TABLE kernel_matches (
    decl_id INTEGER NOT NULL,
    const_name TEXT NOT NULL,
    ckind TEXT NOT NULL,
    module TEXT,
    live_mask INTEGER NOT NULL,
    stmt_mask INTEGER NOT NULL,
    type_nodes INTEGER NOT NULL,
    sig_size INTEGER NOT NULL,
    is_aux INTEGER NOT NULL,
    variant TEXT NOT NULL,           -- k1n | k1a
    sighash TEXT NOT NULL,
    n_candidates INTEGER NOT NULL,
    lib_const_name TEXT NOT NULL,
    lib_ckind TEXT NOT NULL,
    lib_origin TEXT NOT NULL,        -- library_corpus | library_corpus_aux | library_other
    lib_repo TEXT,
    lib_commit_sha TEXT,
    lib_license TEXT,
    same_short_name INTEGER NOT NULL,
    provenance TEXT NOT NULL,        -- always 'L'
    PRIMARY KEY (const_name, variant)
);
CREATE INDEX kernel_matches_ckind ON kernel_matches(ckind, variant);
CREATE INDEX kernel_matches_module ON kernel_matches(module);
CREATE INDEX kernel_matches_sighash ON kernel_matches(sighash);
CREATE TABLE kernel_const_origin (
    origin TEXT PRIMARY KEY,
    n_consts INTEGER NOT NULL,
    n_thms INTEGER NOT NULL
);
"""


def _rate(a: int, b: int) -> Optional[float]:
    return (a / b) if b else None


def _classify_const(
    const_name: str,
    module: Optional[str],
    method: Optional[str],
    corpus_exact: Dict[str, Tuple[str, int]],
    proj_tops: Set[str],
) -> Tuple[str, Optional[str], Optional[int]]:
    """Classify one kernel constant into (origin, repo, corpus_id).

    Counting / classification rule (explicit, deterministic):
      1. If decl_module.module IS NOT NULL -> 'project'.
      2. Else let norm = norm_const_name(const_name).
         a. If norm is an exact name in corpus_sigs for DEP_REPOS -> 'library_corpus'.
         b. Else if a proper dot-prefix of norm is in corpus_sigs for DEP_REPOS
            (e.g. inductive ctor/rec, `_proof_1`, `match_1`) -> 'library_corpus_aux'.
         c. Else if `method` starts with 'generated' or top component is in `proj_tops`
            (a top-level project module prefix from outputs/leanre.db / proof_sigs) ->
            'project_unaligned'.
         d. Else if top component is in _LIB_TOP_PREFIXES or `method` indicates an
            external/mathlib/core bucket -> 'library_other'.
         e. Else -> 'project_unaligned'.
    """
    if module is not None:
        return ("project", None, None)
    mlow = (method or "").lower()
    if mlow.startswith("unmatched:project") or mlow.startswith("generated"):
        return ("project_unaligned", None, None)
    norm = _norm_const_name(const_name)
    hit = corpus_exact.get(norm)
    if hit is not None:
        return ("library_corpus", hit[0], hit[1])
    # Check proper dot-prefixes (longest first)
    cur = norm
    while True:
        dot = cur.rfind(".")
        if dot <= 0:
            break
        cur = cur[:dot]
        hit = corpus_exact.get(cur)
        if hit is not None:
            return ("library_corpus_aux", hit[0], hit[1])
    top = norm.split(".", 1)[0]
    if "library" in mlow or "external" in mlow or top in _LIB_TOP_PREFIXES or any(
            tok in mlow for tok in ("mathlib", "lean", "init", "std", "batteries")):
        return ("library_other", None, None)
    if top in proj_tops:
        return ("project_unaligned", None, None)
    return ("project_unaligned", None, None)


def _repo_priority(repo: Optional[str]) -> int:
    if repo == "mathlib4":
        return 0
    if repo == "lean4":
        return 1
    if repo == "batteries":
        return 2
    return 3


def run(
    db_path: str = DB_PATH,
    kernel_db: str = KERNEL_DB,
    verbose: bool = True,
) -> Dict[str, Any]:
    """Read kernel.db (read-only), populate kernel_matches + kernel controls in tier2.db."""
    t0 = time.time()
    if not os.path.exists(db_path):
        raise FileNotFoundError(f"tier2.db not found: {db_path}")
    if not os.path.exists(kernel_db):
        raise FileNotFoundError(f"kernel.db not found: {kernel_db}")

    kconn = sqlite3.connect(f"file:{kernel_db}?mode=ro", uri=True)
    tconn = sqlite3.connect(db_path)

    # Verify required tables & columns in kernel.db
    kcols = {r[1] for r in kconn.execute("PRAGMA table_info(consts)")}
    need_c = {"name", "decl_id", "ckind", "sighash", "sighash_anon"}
    if not need_c <= kcols:
        raise RuntimeError(f"kernel.db consts missing columns {need_c - kcols}; found {sorted(kcols)}")
    dcols = {r[1] for r in kconn.execute("PRAGMA table_info(decls)")}
    kmeta = {}
    if kconn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='meta'").fetchone():
        for k, v in kconn.execute("SELECT key, value_json FROM meta"):
            try:
                kmeta[k] = json.loads(v)
            except Exception:
                kmeta[k] = v

    # Load pinned dependency corpus names from tier2.db
    commit_by_repo = dict(tconn.execute("SELECT repo, commit_sha FROM corpora"))
    license_by_repo = dict(tconn.execute("SELECT repo, license FROM corpora"))
    # name -> (repo, corpus_id), preferring mathlib4 > lean4 > batteries
    corpus_exact: Dict[str, Tuple[str, int]] = {}
    corpus_ids_by_name: Dict[str, List[int]] = collections.defaultdict(list)
    for cid, repo, name in tconn.execute(
            "SELECT id, repo, name FROM corpus_sigs WHERE repo IN ('mathlib4','lean4','batteries') "
            "ORDER BY id"):
        corpus_ids_by_name[name].append(cid)
        prev = corpus_exact.get(name)
        if prev is None or _repo_priority(repo) < _repo_priority(prev[0]):
            corpus_exact[name] = (repo, cid)

    # Project top-level namespaces from proof_sigs (excluding standard library names)
    proj_tops: Set[str] = set()
    for (mod,) in tconn.execute("SELECT DISTINCT module FROM proof_sigs"):
        top = mod.split(".", 1)[0]
        if top not in _LIB_TOP_PREFIXES:
            proj_tops.add(top)
    for (nm,) in tconn.execute("SELECT DISTINCT name FROM proof_sigs"):
        top = nm.split(".", 1)[0]
        if top not in _LIB_TOP_PREFIXES:
            proj_tops.add(top)

    # Load decl metadata + decl_module from kernel.db
    decl_info: Dict[int, Tuple[int, int, int]] = {}  # decl_id -> (type_nodes, live_mask, stmt_mask)
    has_live = "live_mask" in dcols
    has_stmt = "stmt_mask" in dcols
    has_tnodes = "type_nodes" in dcols
    sel_d = (
        "SELECT id, "
        + ("type_nodes" if has_tnodes else "0") + ", "
        + ("live_mask" if has_live else "0") + ", "
        + ("stmt_mask" if has_stmt else "0")
        + " FROM decls"
    )
    for did, tn, lm, sm in kconn.execute(sel_d):
        decl_info[did] = (tn or 0, lm or 0, sm or 0)

    decl_mod: Dict[int, Tuple[Optional[str], Optional[str], Optional[int]]] = {}
    if kconn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='decl_module'").fetchone():
        for did, mod, meth, sdid in kconn.execute(
                "SELECT decl_id, module, method, src_decl_id FROM decl_module"):
            decl_mod[did] = (mod, meth, sdid)

    # Pass 1: classify all constants in kernel.db and index library constants by k1n / k1a
    origin_counts: Dict[str, List[int]] = collections.defaultdict(lambda: [0, 0])  # [all, thm]
    # hash -> list of (const_name, ckind, origin, repo, corpus_id)
    lib_by_k1n: Dict[str, List[Tuple[str, str, str, Optional[str], Optional[int]]]] = collections.defaultdict(list)
    lib_by_k1a: Dict[str, List[Tuple[str, str, str, Optional[str], Optional[int]]]] = collections.defaultdict(list)
    lib_k1n_by_name: Dict[str, str] = {}
    proj_consts: List[Tuple[int, str, str, Optional[str], int, int, int, int, int, Optional[str], Optional[str]]] = []
    proj_thm_k1n: Set[str] = set()
    proj_thm_k1a: Set[str] = set()
    n_null_hash = 0
    has_sig_size = "sig_size" in kcols
    sel_c = (
        "SELECT name, decl_id, ckind, sighash, sighash_anon, "
        + ("sig_size" if has_sig_size else "0")
        + " FROM consts"
    )

    for cname, did, ckind, k1n, k1a, ssize in kconn.execute(sel_c):
        mod, meth, _sdid = decl_mod.get(did, (None, None, None))
        origin, repo, cid = _classify_const(cname, mod, meth, corpus_exact, proj_tops)
        origin_counts[origin][0] += 1
        if ckind == "thm":
            origin_counts[origin][1] += 1
        if not k1n:
            n_null_hash += 1
            continue
        if origin.startswith("library_"):
            rec = (cname, ckind, origin, repo, cid)
            lib_by_k1n[k1n].append(rec)
            if k1a:
                lib_by_k1a[k1a].append(rec)
            norm = _norm_const_name(cname)
            if norm not in lib_k1n_by_name:
                lib_k1n_by_name[norm] = k1n
        else:
            tn, lm, sm = decl_info.get(did, (0, 0, 0))
            is_aux = int((meth or "").startswith("aux_prefix:") or bool(_RE_COMPILER_AUX.search(cname)))
            proj_consts.append((did, cname, ckind, mod, lm, sm, tn, int(ssize or tn), is_aux, k1n, k1a))
            if ckind == "thm":
                proj_thm_k1n.add(k1n)
                if k1a:
                    proj_thm_k1a.add(k1a)

    # Pass 2: match project constants against library constants on k1n and k1a
    tconn.executescript(KERNEL_SCHEMA)
    for orig, (nc, nt) in sorted(origin_counts.items()):
        tconn.execute("INSERT INTO kernel_const_origin VALUES (?,?,?)", (orig, nc, nt))

    km_rows: List[Tuple] = []
    # Track kernel-verified (project_thm, set of matched library corpus names) for recall audit
    # key = (module, norm_name) -> (type_nodes, set of lib corpus names)
    gt_proj_to_lib: Dict[Tuple[str, str], Tuple[int, Set[str]]] = {}
    proj_k1n_by_mod_name: Dict[Tuple[str, str], str] = {}
    proj_k1n_by_name: Dict[str, str] = {}

    for did, cname, ckind, mod, lm, sm, tn, ssize, is_aux, k1n, k1a in proj_consts:
        norm = _norm_const_name(cname)
        short = norm.rsplit(".", 1)[-1]
        if ckind == "thm" and k1n and not is_aux:
            if mod is not None:
                proj_k1n_by_mod_name[(mod, norm)] = k1n
            proj_k1n_by_name[norm] = k1n
        for variant, h, idx in (("k1n", k1n, lib_by_k1n), ("k1a", k1a, lib_by_k1a)):
            if not h:
                continue
            cands = idx.get(h)
            if not cands:
                continue
            # Prefer same ckind, then library_corpus over aux/other, then same short name, then mathlib4
            best = min(cands, key=lambda r: (
                r[1] != ckind,
                r[2] != "library_corpus",
                r[0].rsplit(".", 1)[-1] != short,
                _repo_priority(r[3]),
                r[0],
            ))
            lib_name, lib_ckind, lib_origin, lib_repo, _lib_cid = best
            km_rows.append((
                did, cname, ckind, mod, lm, sm, tn, ssize, is_aux, variant, h, len(cands),
                lib_name, lib_ckind, lib_origin, lib_repo,
                commit_by_repo.get(lib_repo) if lib_repo else None,
                license_by_repo.get(lib_repo) if lib_repo else None,
                int(lib_name.rsplit(".", 1)[-1] == short), "L",
            ))
            if variant == "k1n" and ckind == "thm" and not is_aux and mod is not None:
                lib_corpus_names = {
                    _norm_const_name(r[0]) for r in cands
                    if r[1] == "thm" and r[2] == "library_corpus"
                }
                if lib_corpus_names:
                    prev = gt_proj_to_lib.get((mod, norm))
                    if prev is None:
                        gt_proj_to_lib[(mod, norm)] = (tn, set(lib_corpus_names))
                    else:
                        prev[1].update(lib_corpus_names)

    tconn.executemany(
        "INSERT INTO kernel_matches VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", km_rows)

    # Pass 3: real-world ground-truth controls
    tconn.execute("DELETE FROM controls WHERE control LIKE 'kernel_%'")
    ctl_rows: List[Tuple] = []

    # 3a. Library self-match coverage: library constants in kernel.db found in pinned DEP_REPOS
    n_lib_all = sum(v[0] for k, v in origin_counts.items() if k.startswith("library_"))
    n_lib_thm = sum(v[1] for k, v in origin_counts.items() if k.startswith("library_"))
    n_lib_cov_exact = origin_counts["library_corpus"][0]
    n_lib_cov_aux = origin_counts["library_corpus_aux"][0]
    n_lib_thm_exact = origin_counts["library_corpus"][1]
    n_lib_thm_aux = origin_counts["library_corpus_aux"][1]
    ctl_rows.append((
        "kernel_lib_coverage", "all_consts", 0, n_lib_all,
        n_lib_cov_exact + n_lib_cov_aux, 0, n_lib_all - n_lib_cov_exact - n_lib_cov_aux,
        1.0 if (n_lib_cov_exact + n_lib_cov_aux) else None,
        _rate(n_lib_cov_exact + n_lib_cov_aux, n_lib_all), None,
        f"exact={n_lib_cov_exact}, aux_prefix={n_lib_cov_aux}, other={origin_counts['library_other'][0]} "
        "(pinned mathlib4/lean4/batteries coverage of export library constants)",
    ))
    ctl_rows.append((
        "kernel_lib_coverage", "thm_only", 0, n_lib_thm,
        n_lib_thm_exact + n_lib_thm_aux, 0, n_lib_thm - n_lib_thm_exact - n_lib_thm_aux,
        1.0 if (n_lib_thm_exact + n_lib_thm_aux) else None,
        _rate(n_lib_thm_exact + n_lib_thm_aux, n_lib_thm), None,
        f"exact={n_lib_thm_exact}, aux_prefix={n_lib_thm_aux}, other={origin_counts['library_other'][1]} "
        "(export library theorems found in pinned dependency corpora)",
    ))

    # 3b. Real-world source-matcher recall on kernel-verified (project_thm, corpus_thm) k1n pairs
    # Load proof_sigs lookup: (module, name) -> (proof_id, n_tokens)
    proof_lookup: Dict[Tuple[str, str], Tuple[int, int]] = {}
    for pid, mod, name, ntok in tconn.execute(
            "SELECT id, module, name, n_tokens FROM proof_sigs WHERE kind IN ('theorem','lemma')"):
        proof_lookup[(mod, name)] = (pid, ntok)

    # Load source matches for proof_ids: (proof_id, variant) -> (grade, set of matched corpus names)
    src_match_grade: Dict[Tuple[int, str], str] = {}
    src_match_names: Dict[Tuple[int, str], Set[str]] = collections.defaultdict(set)
    for pid, var, grade, cname in tconn.execute(
            "SELECT m.proof_id, m.variant, m.grade, s.name "
            "FROM matches m JOIN match_candidates mc USING (proof_id, variant) "
            "JOIN corpus_sigs s ON s.id=mc.corpus_id"):
        src_match_grade[(pid, var)] = grade
        src_match_names[(pid, var)].add(cname)

    # Evaluate across type_nodes cutoffs (0 = all, 10 = non-trivial DAG)
    for min_tn in (0, 10):
        gt_eval: List[Tuple[int, int, Set[str]]] = []
        for (mod, norm), (tn, lib_names) in gt_proj_to_lib.items():
            if tn < min_tn:
                continue
            pl = proof_lookup.get((mod, norm))
            if pl is not None:
                gt_eval.append((pl[0], pl[1], lib_names))
        n_gt = len(gt_eval)
        for var, req_strong in (("s1n", False), ("s1t", False), ("s1t_strong", True)):
            base_var = "s1t" if var == "s1t_strong" else var
            tp = 0
            for pid, _ntok, lib_names in gt_eval:
                g = src_match_grade.get((pid, base_var))
                if g is None:
                    continue
                if req_strong and g != "strong":
                    continue
                # Hit counts as TP if any k1n-identical corpus theorem was among the candidates
                if src_match_names.get((pid, base_var), set()) & lib_names:
                    tp += 1
            ctl_rows.append((
                "kernel_source_recall", var, min_tn, n_gt, tp, None, n_gt - tp,
                None, _rate(tp, n_gt), None,
                "min_tokens column = min kernel type_nodes; real-world recall of source Tier 2 "
                "on kernel-identical (k1n) project-vs-corpus theorem pairs",
            ))

    # 3c. Real-world kernel-verified precision of source-level theorem matches
    # Among source theorem matches where BOTH proof decl and matched corpus decl exist in kernel.db
    for var, grade_filter in (("s1n", "strong"), ("s1t", "strong"), ("s1t", "all")):
        q_sql = (
            "SELECT p.module, p.name, m.corpus_name, m.grade "
            "FROM matches m JOIN proof_sigs p ON p.id=m.proof_id "
            "WHERE m.variant=? AND p.kind IN ('theorem','lemma')"
        )
        args: List[Any] = [var]
        if grade_filter == "strong":
            q_sql += " AND m.grade='strong'"
        n_both = 0
        tp = 0
        fp = 0
        for pmod, pname, cname, _gr in tconn.execute(q_sql, args):
            pk = proj_k1n_by_mod_name.get((pmod, pname)) or proj_k1n_by_name.get(pname)
            lk = lib_k1n_by_name.get(cname)
            if pk is None or lk is None:
                continue
            n_both += 1
            if pk == lk:
                tp += 1
            else:
                fp += 1
        ctl_rows.append((
            "kernel_source_precision", f"{var}_{grade_filter}", 0, n_both, tp, fp, None,
            _rate(tp, n_both), None, _rate(fp, n_both),
            "real-world kernel precision: source theorem matches whose both sides appear in "
            "kernel.db and agree (tp) vs disagree (fp) on kernel k1n",
        ))

    tconn.executemany("INSERT OR REPLACE INTO controls VALUES (?,?,?,?,?,?,?,?,?,?,?)", ctl_rows)

    # Summarize kernel results in meta['kernel']
    def q1(sql: str, *a: Any) -> Any:
        return tconn.execute(sql, a).fetchone()[0]

    def qall(sql: str, *a: Any) -> List[Tuple]:
        return tconn.execute(sql, a).fetchall()

    k_summary: Dict[str, Any] = {
        "kernel_db": os.path.relpath(kernel_db, REPO) if kernel_db.startswith(REPO) else kernel_db,
        "kernel_input_meta": {
            k: kmeta[k] for k in ("input", "counts", "sighash", "schema_version",
                                  "input_path", "compressed_sha256", "uncompressed_sha256",
                                  "n_decls", "n_consts")
            if k in kmeta
        },
        "classification_rule": (
            "project = decl_module.module IS NOT NULL; library_corpus = unaligned + exact name in "
            "pinned mathlib4/lean4/batteries corpus_sigs; library_corpus_aux = unaligned + proper "
            "dot-prefix in those corpora; library_other = unaligned + known core/library prefix; "
            "project_unaligned = remaining unaligned constants."
        ),
        "origin_counts": {orig: {"consts": nc, "thms": nt} for orig, (nc, nt) in sorted(origin_counts.items())},
        "null_sighash_consts": n_null_hash,
        "matches": {},
        "k1a_note": (
            "Library constants never mention project-local constants, so library k1a == library k1n. "
            "Therefore project-vs-library k1a matches equal project-vs-library k1n matches; k1a's "
            "name-independent collapse operates on project-vs-project statements (reported below)."
        ),
        "project_thm_hash_collapse": {
            "project_thms_hashed": sum(1 for r in proj_consts if r[2] == "thm"),
            "distinct_k1n": len(proj_thm_k1n),
            "distinct_k1a": len(proj_thm_k1a),
        },
        "controls": [
            {k: v for k, v in zip(
                ("control", "variant", "min_tokens", "n", "tp", "fp", "fn", "precision", "recall", "fpr", "note"), r)
             if v is not None}
            for r in ctl_rows
        ],
        "elapsed_seconds": round(time.time() - t0, 2),
    }

    for var in ("k1n", "k1a"):
        for bucket, cond in (("thm_all", "ckind='thm'"),
                             ("thm_named", "ckind='thm' AND is_aux=0"),
                             ("thm_named_corpus_exact", "ckind='thm' AND is_aux=0 AND lib_origin='library_corpus' AND lib_ckind='thm'"),
                             ("thm_named_nontrivial_tn10", "ckind='thm' AND is_aux=0 AND type_nodes>=10"),
                             ("thm_live", "ckind='thm' AND live_mask<>0"),
                             ("thm_nontrivial_tn10", "ckind='thm' AND type_nodes>=10"),
                             ("non_thm_typeshape", "ckind<>'thm'")):
            row = qall(
                f"SELECT COUNT(*), COUNT(DISTINCT sighash), COALESCE(SUM(same_short_name),0), "
                f"COALESCE(SUM(lib_origin='library_corpus'),0) "
                f"FROM kernel_matches WHERE variant=? AND {cond}", var)[0]
            k_summary["matches"][f"{var}_{bucket}"] = {
                "project_consts": row[0],
                "distinct_sighashes": row[1],
                "same_short_name": row[2],
                "matched_to_pinned_corpus_exact": row[3],
                "by_lib_repo": dict(qall(
                    f"SELECT COALESCE(lib_repo, lib_origin), COUNT(*) FROM kernel_matches "
                    f"WHERE variant=? AND {cond} GROUP BY 1 ORDER BY 2 DESC", var)),
            }

    k_summary["top_matched_library_thms"] = [
        dict(zip(("lib_const_name", "lib_repo", "sig_size", "project_thms"), r))
        for r in qall(
            "SELECT lib_const_name, COALESCE(lib_repo, lib_origin), MIN(sig_size), COUNT(*) "
            "FROM kernel_matches WHERE variant='k1n' AND ckind='thm' AND is_aux=0 "
            "AND lib_origin='library_corpus' AND lib_ckind='thm' "
            "GROUP BY sighash ORDER BY 4 DESC, 3 DESC, 1 LIMIT 25")
    ]

    tconn.execute("INSERT OR REPLACE INTO meta VALUES ('kernel', ?)",
                  (json.dumps(k_summary, sort_keys=True),))
    tconn.commit()
    tconn.close()
    kconn.close()
    if verbose:
        print(f"[tier2_kernel] done in {k_summary['elapsed_seconds']}s: "
              f"k1n thm matches={k_summary['matches']['k1n_thm_all']['project_consts']:,} "
              f"(tn>=10: {k_summary['matches']['k1n_thm_nontrivial_tn10']['project_consts']:,}), "
              f"non-thm={k_summary['matches']['k1n_non_thm_typeshape']['project_consts']:,}",
              flush=True)
    return k_summary


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--db", default=DB_PATH)
    ap.add_argument("--kernel-db", default=KERNEL_DB)
    a = ap.parse_args(argv)
    res = run(a.db, a.kernel_db)
    print(json.dumps({k: res[k] for k in ("origin_counts", "matches", "controls")}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
