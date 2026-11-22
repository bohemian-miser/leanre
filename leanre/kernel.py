#!/usr/bin/env python3
"""leanre.kernel -- Python wrapper & post-processor for the native Rust kernel extractor.

Orchestrates `leanre/kernel-rs` (leanre-kernel) over lean4export NDJSON v3.1.0
exports (challenge.ndjson.zst / solution.ndjson.zst), verifies K1 SHA-256 digests,
populates K5 taint tables (`taint_sources`, `taint_paths` with edge-by-edge graph
validation) and K6 `decl -> .lean` module alignment (`decl_module` against
`outputs/leanre.db`, with optional clean source-namespace rescan via `sighash`),
checks the K3 challenge regression, and emits a compact `outputs/kernel_report.json`.

Stdlib only (Python 3.9+); never copies raw `.lean` proof bodies into outputs.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import multiprocessing
import os
import shutil
import sqlite3
import subprocess
import sys
import time
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

# Canonical pinned digests [L] (HANDOFF.md §4, data/MANIFEST.md, docs/PHASE3_GATES.md K1/K3)
EXPECTED_SOLUTION_BYTES = 7_699_933_588
EXPECTED_SOLUTION_SHA256 = "61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381"
EXPECTED_SOLUTION_UNCOMPRESSED_BYTES = 61_570_595_788
EXPECTED_SOLUTION_UNCOMPRESSED_SHA256 = "5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e"

EXPECTED_CHALLENGE_BYTES = 46_881_299
EXPECTED_CHALLENGE_SHA256 = "c24ef99dab3556a52c7fb886e03cf22a242f3b96f82ae4cc40539e5d2f678ac6"
EXPECTED_CHALLENGE_UNCOMPRESSED_BYTES = 350_862_311
EXPECTED_CHALLENGE_UNCOMPRESSED_SHA256 = "bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9"

EDGE_KIND_NAMES = {1: "type", 2: "value", 3: "both"}

# Kernel-pattern flags emitted by leanre/kernel-rs/src/walk.rs
F_REFL_TRUE = 1
F_OF_DECIDE = 2
F_REDUCE_BOOL = 4
F_REDUCE_NAT = 8
F_SORRY = 16
F_TRUST_COMPILER = 32

# Known Lean 4 / Init / Std / Batteries / Mathlib top-level namespaces that are NOT
# project-specific namespaces even if the project occasionally adds lemmas inside them.
_STDLIB_TOP_PREFIXES = frozenset({
    "Init", "Lean", "Std", "Batteries", "Mathlib", "Aesop", "Qq", "ProofWidgets",
    "Nat", "Int", "Rat", "Real", "Complex", "NNReal", "ENNReal", "EReal", "Float",
    "Fin", "Finset", "Fintype", "Multiset", "Set", "List", "Array", "Vector", "ByteArray",
    "BitVec", "UInt8", "UInt16", "UInt32", "UInt64", "USize", "Int8", "Int16", "Int32", "Int64",
    "String", "Substring", "Char", "Bool", "Prop", "Sort", "Type", "Unit", "PUnit", "Empty", "PEmpty",
    "Option", "Except", "Sum", "PSum", "Prod", "PProd", "Sigma", "PSigma", "Subtype", "ULift", "PLift",
    "Eq", "HEq", "And", "Or", "Not", "Iff", "Exists", "True", "False", "Classical", "Decidable", "Quot",
    "Function", "Pi", "Equiv", "RelIso", "OrderIso", "Embedding", "RelEmbedding", "OrderEmbedding",
    "Filter", "Topology", "TopologicalSpace", "UniformSpace", "Metric", "MetricSpace", "EMetric",
    "MeasureTheory", "MeasurableSpace", "ProbabilityTheory", "CategoryTheory", "AlgebraicGeometry",
    "AlgebraicTopology", "NumberTheory", "Combinatorics", "Analysis", "LinearAlgebra", "RepresentationTheory",
    "Polynomial", "MvPolynomial", "PowerSeries", "LaurentSeries", "Matrix", "LinearMap", "LinearEquiv",
    "ContinuousLinearMap", "ContinuousLinearEquiv", "LinearIsometry", "LinearIsometryEquiv",
    "Module", "Submodule", "Algebra", "Subalgebra", "RingHom", "MonoidHom", "AddMonoidHom", "MulHom",
    "Ideal", "Subring", "Subgroup", "AddSubgroup", "Submonoid", "Subsemiring", "Subfield", "IntermediateField",
    "Group", "AddGroup", "CommGroup", "Monoid", "CommMonoid", "Semigroup", "Ring", "CommRing", "Semiring",
    "Field", "DivisionRing", "EuclideanDomain", "PrincipalIdealRing", "UniqueFactorizationMonoid",
    "NormedSpace", "NormedAddCommGroup", "InnerProductSpace", "CompleteSpace", "SeparableSpace",
    "Order", "Preorder", "PartialOrder", "LinearOrder", "Lattice", "CompleteLattice", "BoundedOrder",
    "DirichletCharacter", "LSeries", "ArithmeticFunction", "ZMod", "AddChar", "MulChar", "Units",
    "Continuous", "ContinuousOn", "ContinuousAt", "Differentiable", "DifferentiableOn", "AnalyticAt",
    "AnalyticOn", "Meromorphic", "HasDerivAt", "HasFDerivAt", "ContinuousMap", "BoundedContinuousFunction",
    "Acc", "WellFounded", "SizeOf", "Inhabited", "Nonempty", "Subsingleton", "Unique", "DecidableEq",
    "BEq", "Ord", "Hashable", "Repr", "ToString", "OfNat", "Add", "Sub", "Mul", "Div", "Mod", "Pow",
    "HAdd", "HSub", "HMul", "HDiv", "HMod", "HPow", "Neg", "Inv", "LE", "LT", "Min", "Max", "Abs",
    "IO", "System", "Task", "Thunk", "StateM", "ReaderM", "ExceptT", "StateT", "ReaderT", "Id",
    "Monad", "Functor", "Applicative", "Alternative", "Pure", "Bind", "Seq", "LawfulMonad",
    "IsEmpty", "IsUnit", "IsDomain", "IsField", "IsLocalRing", "IsRegularLocalRing", "IsDedekindDomain", "IsNoetherian",
    "Derivation",
    "IsCompact", "IsOpen", "IsClosed", "IsConnected", "IsPreconnected", "IsBounded", "IsLinearMap",
    "Padic", "PadicInt", "PadicNorm", "RatFunc", "Localization", "FractionRing", "Valuation", "AbsoluteValue",
    "ModularForm", "UpperHalfPlane", "EllipticCurve", "WeierstrassCurve", "MatrixGroup", "SpecialLinearGroup",
    "GeneralLinearGroup", "ComplexConjugate", "starRingEnd", "riemannZeta", "RiemannHypothesis",
    "hurwitzZeta", "completedRiemannZeta", "Gamma", "Complex", "Real", "Circle", "AddCircle",
    "SimpleGraph", "Digraph", "Quiver", "Trees", "Convex", "Affine", "Projective", "Manifold", "Smooth",
    "ChartedSpace", "ModelWithCorners", "Bundle", "FiberBundle", "VectorBundle", "TangentBundle",
    "MvPowerSeries", "FormalMultilinearSeries", "ContinuousMultilinearMap", "MultilinearMap",
    "TensorProduct", "AlternatingMap", "ExteriorAlgebra", "CliffordAlgebra", "FreeAlgebra", "FreeModule",
    "DirectSum", "Finsupp", "DFinsupp", "LocallyFinsupp", "CompactlySupported", "SchwartzMap",
    "FourierTransform", "MellinTransform", "Bochner", "Integral", "Measure", "Volume", "Haar",
    "Galois", "SplittingField", "AlgebraicClosure", "Separable", "Normal", "IsGalois", "NumberField",
    "RingOfIntegers", "FractionalIdeal", "ClassGroup", "DedekindDomain", "HeightOneSpectrum",
    "Adeles", "FiniteAdeleRing", "InfiniteAdeleRing", "AdeleRing", "IdeleGroup",
    "propext", "sorryAx", "of_decide_eq_true", "decide", "congrArg", "congrFun", "congr", "funext",
    "absurd", "False", "True", "id", "comp", "flip", "const", "ite", "dite", "cond", "optParam",
    "autoParam", "outParam", "semiOutParam", "eagerReduce", "lcProof", "by_contra", "cast", "eqRec",
})

CUT_CPT_COPY_MODULE = "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMainCpt"
CUT_CPT_COPY_LINE = 945
CUT_CPT_COPY_PREFIX = "Formalism.FourierDecayAlt.P."

TAINT_FORENSIC_TAGS = (
    "kexactB",
    "kcopy",
    "decide_kernel",
    "lean4lean_timeout",
    "slow_con_leche",
    "addDecl",
    "CutCptCopy",
)


def default_crate_dir() -> str:
    return os.path.join(_HERE, "kernel-rs")


def default_binary_path() -> str:
    return os.path.join(default_crate_dir(), "target", "release", "leanre-kernel")


def build_binary(crate_dir: Optional[str] = None, verbose: bool = True) -> str:
    cdir = crate_dir or default_crate_dir()
    cmd = ["cargo", "build", "--release"]
    if verbose:
        print(f"[kernel] building Rust extractor in {cdir} ...", file=sys.stderr)
    res = subprocess.run(cmd, cwd=cdir, capture_output=not verbose, text=True)
    if res.returncode != 0:
        raise RuntimeError(f"cargo build --release failed ({res.returncode}): {res.stderr or ''}")
    return os.path.join(cdir, "target", "release", "leanre-kernel")


def _file_sha256(path: str) -> Tuple[int, str]:
    h = hashlib.sha256()
    n = 0
    with open(path, "rb") as f:
        while True:
            b = f.read(1 << 20)
            if not b:
                break
            h.update(b)
            n += len(b)
    return n, h.hexdigest()


# ---------------------------------------------------------------------------
# Source-tree clean namespace rescan (optional, via sighash.iter_source_decls)
# ---------------------------------------------------------------------------

def _scan_batch_worker(args: Tuple[str, List[str]]) -> List[Tuple[str, str, int]]:
    import sighash  # sibling module
    src_dir, rel_paths = args
    out: List[Tuple[str, str, int]] = []
    for rel in rel_paths:
        mod = rel[:-5].replace(os.sep, ".")
        full = os.path.join(src_dir, rel)
        try:
            with open(full, "r", encoding="utf-8", errors="replace") as f:
                txt = f.read()
        except OSError:
            continue
        for d in sighash.iter_source_decls(txt, with_sig=False):
            nm = d.get("name")
            if nm:
                out.append((nm, mod, int(d.get("line", 0))))
    return out


def scan_source_decl_modules(
    src_dir: str, workers: int = 16
) -> Tuple[Dict[str, Tuple[str, int]], Dict[Tuple[str, int], str], int]:
    """Scan `.lean` files using `sighash.iter_source_decls` (correct anonymous `end`
    and `_root_` scoping). Returns:
      - `src_exact`: qualified_name -> (module, line_no) (lowest (module, line_no))
      - `src_by_mod_line`: (module, line_no) -> qualified_name
      - `n_files`: number of `.lean` files scanned
    """
    rels: List[str] = []
    for root, dirs, files in os.walk(src_dir):
        dirs.sort()
        files.sort()
        for fn in files:
            if fn.endswith(".lean"):
                rels.append(os.path.relpath(os.path.join(root, fn), src_dir))
    rels.sort()
    n_files = len(rels)
    if not rels:
        return {}, {}, 0
    workers = max(1, min(workers, 32, len(rels)))
    batch_sz = max(64, (len(rels) + workers * 4 - 1) // (workers * 4))
    batches = [(src_dir, rels[i : i + batch_sz]) for i in range(0, len(rels), batch_sz)]
    src_exact: Dict[str, Tuple[str, int]] = {}
    src_by_mod_line: Dict[Tuple[str, int], str] = {}
    if workers == 1:
        results = [_scan_batch_worker(b) for b in batches]
    else:
        with multiprocessing.Pool(processes=workers) as pool:
            results = pool.map(_scan_batch_worker, batches)
    for chunk in results:
        for nm, mod, ln in chunk:
            prev = src_exact.get(nm)
            if prev is None or (mod, ln) < prev:
                src_exact[nm] = (mod, ln)
            src_by_mod_line[(mod, ln)] = nm
    return src_exact, src_by_mod_line, n_files


def _parse_private_module(name: str) -> Optional[str]:
    """Extract `<Mod>` from `_private.<Mod>.0.<rest>`, or None if not a private name."""
    if not name.startswith("_private."):
        return None
    parts = name.split(".")
    for i in range(1, len(parts)):
        if parts[i] == "0":
            if i > 1 and i + 1 < len(parts):
                return ".".join(parts[1:i])
            return None
    return None


def _proper_prefixes(name: str) -> Iterable[str]:
    """Yield proper dot-prefixes of `name`, longest first."""
    pos = name.rfind(".")
    while pos > 0:
        yield name[:pos]
        pos = name.rfind(".", 0, pos)


def _is_cut_cpt_generated(
    name: str, known_names: Set[str], cut_manual_names: Set[str]
) -> bool:
    """True iff `name` (or an auxiliary of it) matches a `CutCptCopy` (`cpt_copy_thms`)
    `addDecl`-generated `*Cpt` declaration under `Formalism.FourierDecayAlt.P.` whose
    non-`Cpt` template exists in the source tree and which is not declared verbatim in source.
    """
    if not name.startswith(CUT_CPT_COPY_PREFIX) or name in cut_manual_names:
        return False
    # Check `name` itself and proper prefixes (for `fooCpt._proof_1`, `fooCpt.eq_1`, etc.)
    cand = name
    while True:
        if cand.endswith("Cpt") and len(cand) > len(CUT_CPT_COPY_PREFIX) + 3:
            base = cand[:-3]
            if base in known_names and cand not in cut_manual_names:
                return True
        pos = cand.rfind(".")
        if pos <= len(CUT_CPT_COPY_PREFIX) - 1:
            break
        cand = cand[:pos]
    return False


# ---------------------------------------------------------------------------
# Enrichment: K6 decl_module + K5 taint_sources / taint_paths + validation
# ---------------------------------------------------------------------------

def enrich_kernel_db(
    kernel_db_path: str,
    leanre_db_path: Optional[str] = None,
    src_dir: Optional[str] = None,
    workers: int = 24,
    max_pattern_taint_sources: int = 5000,
    verbose: bool = True,
) -> Dict[str, Any]:
    """Populate `decl_module`, `taint_sources`, `taint_paths` and validate all taint edges."""
    t0 = time.time()
    project_modules: Set[str] = set()
    ldb_exact: Dict[str, Tuple[str, int]] = {}
    ldb_unroot: Dict[str, Tuple[str, int]] = {}
    ldb_by_mod_line: Dict[Tuple[str, int], int] = {}
    ldb_multi_names = 0
    ldb_total_rows = 0
    tcb_library_names: Set[str] = set()
    forensic_hits_raw: List[Tuple[str, str, int, Optional[str]]] = []
    ldb_rev_imports: Dict[str, List[str]] = collections.defaultdict(list)

    if leanre_db_path and os.path.exists(leanre_db_path):
        lconn = sqlite3.connect(f"file:{os.path.abspath(leanre_db_path)}?mode=ro", uri=True)
        try:
            project_modules = {r[0] for r in lconn.execute("SELECT name FROM modules")}
            seen_multi: Set[str] = set()
            for did, nm, mod, ln in lconn.execute("SELECT id, name, module, line_no FROM declarations ORDER BY id"):
                ldb_total_rows += 1
                if (mod, int(ln)) not in ldb_by_mod_line:
                    ldb_by_mod_line[(mod, int(ln))] = int(did)
                if nm not in ldb_exact:
                    ldb_exact[nm] = (mod, int(did))
                elif ldb_exact[nm][0] != mod:
                    seen_multi.add(nm)
                if nm.startswith("_root_."):
                    stripped = nm[7:]
                    if stripped not in ldb_unroot:
                        ldb_unroot[stripped] = (mod, int(did))
            ldb_multi_names = len(seen_multi)
            # Everything in challenge TCB except the 5 Main headlines and 4 Statements defs is library
            headline_and_stmt = {
                "riemannHypothesis", "riemannZeta_eq_zero_re",
                "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re",
                "LFunction_eq_zero_re_of_isPrimitive",
                "RiemannZetaZerosOnLine", "DirichletLNonvanishingRightOfHalf",
                "DirichletLZerosOnLine", "PrimitiveDirichletLZerosOnLine",
            }
            try:
                for (nm,) in lconn.execute("SELECT name FROM tcb_decls"):
                    if nm not in headline_and_stmt and not nm.startswith("RiemannZetaZerosOnLine.") and not nm.startswith("DirichletL") and not nm.startswith("PrimitiveDirichletL"):
                        tcb_library_names.add(nm)
            except sqlite3.OperationalError:
                pass
            try:
                placeholders = ",".join("?" for _ in TAINT_FORENSIC_TAGS)
                for tag, mod, ln, dnm in lconn.execute(
                    f"SELECT tag, module, line_no, decl_name FROM forensic_hits WHERE tag IN ({placeholders}) ORDER BY tag, module, line_no, id",
                    TAINT_FORENSIC_TAGS,
                ):
                    forensic_hits_raw.append((tag, mod, int(ln or 0), dnm))
            except sqlite3.OperationalError:
                pass
            # Load reverse module edges only around lean4lean_timeout modules (fast targeted BFS)
            timeout_mods = sorted({mod for tag, mod, _ln, _dnm in forensic_hits_raw if tag == "lean4lean_timeout"})
            if timeout_mods:
                try:
                    q_imp: collections.deque = collections.deque((m, 0) for m in timeout_mods)
                    seen_imp: Set[str] = set(timeout_mods)
                    while q_imp:
                        cm, cd = q_imp.popleft()
                        if cd > 6:
                            continue
                        imps = [r[0] for r in lconn.execute("SELECT src FROM module_edges WHERE dst = ? ORDER BY src", (cm,))]
                        ldb_rev_imports[cm] = imps
                        for im in imps:
                            if im not in seen_imp and cd < 6:
                                seen_imp.add(im)
                                q_imp.append((im, cd + 1))
                except sqlite3.OperationalError:
                    pass
        finally:
            lconn.close()
        if verbose:
            print(
                f"[kernel] loaded leanre.db: {len(project_modules):,} modules, {ldb_total_rows:,} decl rows "
                f"({len(ldb_exact):,} distinct, {len(ldb_unroot):,} _root_. stripped), {len(forensic_hits_raw):,} forensic hits",
                file=sys.stderr,
            )

    src_exact: Dict[str, Tuple[str, int]] = {}
    src_by_mod_line: Dict[Tuple[str, int], str] = {}
    src_files_scanned = 0
    if src_dir and os.path.isdir(src_dir):
        ts = time.time()
        src_exact, src_by_mod_line, src_files_scanned = scan_source_decl_modules(src_dir, workers=workers)
        if verbose:
            print(
                f"[kernel] source rescan ({src_files_scanned:,} .lean files -> {len(src_exact):,} qualified names) "
                f"in {time.time() - ts:.1f}s",
                file=sys.stderr,
            )

    # Dynamic project top-level namespace prefixes (names defined inside project that are not stdlib).
    # When clean source rescan (`src_exact`) is available, derive prefixes from it so Phase 2's
    # anonymous-`end` popped names cannot pollute project prefixes.
    top_counts: collections.Counter = collections.Counter()
    if src_exact:
        for nm in src_exact:
            top_counts[nm.split(".", 1)[0]] += 1
    else:
        for nm in ldb_exact:
            clean = nm[7:] if nm.startswith("_root_.") else nm
            top_counts[clean.split(".", 1)[0]] += 1
    project_top_prefixes: Set[str] = {
        p for p, cnt in top_counts.items() if cnt >= 10 and p not in _STDLIB_TOP_PREFIXES
    }
    project_top_prefixes.update({
        "Formalism", "GlobalTheory", "UpperTheory", "PositivityTheory",
        "CompanionTheory", "Development", "Supplements", "PI", "Statements", "BuildAid",
    })
    project_top_prefixes -= _STDLIB_TOP_PREFIXES

    # Known source names (for CutCptCopy base-template & reassoc verification)
    known_source_names: Set[str] = set(src_exact.keys()) if src_exact else (set(ldb_exact.keys()) | set(ldb_unroot.keys()))
    cut_manual_names: Set[str] = {
        nm for nm in known_source_names if nm.startswith(CUT_CPT_COPY_PREFIX) and nm.endswith("Cpt")
    }

    conn = sqlite3.connect(kernel_db_path)
    conn.execute("PRAGMA journal_mode=OFF;")
    conn.execute("PRAGMA synchronous=OFF;")
    conn.execute("PRAGMA cache_size=-1000000;")
    conn.execute("PRAGMA temp_store=MEMORY;")

    try:
        # Load core decls & roots from kernel.db
        decls_rows: List[Tuple[int, str, str, int, int]] = conn.execute(
            "SELECT id, name, kind, flags, live_mask FROM decls ORDER BY id"
        ).fetchall()
        roots_rows: List[Tuple[int, str, int, str]] = conn.execute(
            "SELECT id, name, decl_id, grp FROM roots ORDER BY id"
        ).fetchall()
        name_to_decl_id: Dict[str, int] = {nm: did for did, nm, _k, _f, _lm in decls_rows}
        decl_id_to_name: Dict[int, str] = {did: nm for did, nm, _k, _f, _lm in decls_rows}
        decl_id_to_kind: Dict[int, str] = {did: kd for did, _nm, kd, _f, _lm in decls_rows}
        decl_id_to_flags: Dict[int, int] = {did: fl for did, _nm, _k, fl, _lm in decls_rows}
        decl_id_to_live: Dict[int, int] = {did: lm for did, _nm, _k, _f, lm in decls_rows}

        # Drop & recreate enrichment tables so `enrich` is cleanly idempotent
        conn.executescript(
            """
            DROP TABLE IF EXISTS decl_module;
            DROP TABLE IF EXISTS taint_paths;
            DROP TABLE IF EXISTS taint_sources;
            CREATE TABLE decl_module(
                decl_id INTEGER PRIMARY KEY,
                module TEXT,
                method TEXT NOT NULL,
                src_decl_id INTEGER
            );
            CREATE TABLE taint_sources(
                id INTEGER PRIMARY KEY,
                class TEXT NOT NULL,
                decl_id INTEGER NOT NULL,
                origin TEXT NOT NULL,
                module TEXT,
                line_no INTEGER,
                detail TEXT NOT NULL
            );
            CREATE TABLE taint_paths(
                source_id INTEGER NOT NULL,
                root_id INTEGER NOT NULL,
                hop INTEGER NOT NULL,
                decl_id INTEGER NOT NULL,
                edge_kind INTEGER,
                PRIMARY KEY(source_id, root_id, hop)
            ) WITHOUT ROWID;
            """
        )

        # ---- Step A: K6 decl -> module alignment ----------------------------
        align_rows: List[Tuple[int, Optional[str], str, Optional[int]]] = []
        method_counts: collections.Counter = collections.Counter()
        method_counts_live: collections.Counter = collections.Counter()
        ldb_only_counts: collections.Counter = collections.Counter()
        matched_modules_all: Set[str] = set()
        matched_modules_live: Set[str] = set()
        matched_ldb_decl_ids: Set[int] = set()
        cut_cpt_decl_ids: List[int] = []
        unmatched_proj_samples: List[str] = []
        unmatched_ext_top: collections.Counter = collections.Counter()
        decl_to_module: Dict[int, Optional[str]] = {}
        decl_to_method: Dict[int, str] = {}

        have_ldb = bool(project_modules)
        have_src = bool(src_exact)
        phase2_bogus_collisions_avoided = 0

        for did, nm, _kind, _flags, lm in decls_rows:
            is_live = lm != 0
            # Track leanre.db-only classification for transparent K6 comparison
            ldb_only_hit = False
            if have_ldb:
                if nm in ldb_exact:
                    ldb_only_counts["leanre_db:exact"] += 1
                    ldb_only_hit = True
                elif nm in ldb_unroot:
                    ldb_only_counts["leanre_db:strip_root"] += 1
                    ldb_only_hit = True
                else:
                    pmod = _parse_private_module(nm)
                    if pmod is not None:
                        if pmod in project_modules:
                            ldb_only_counts["private_module"] += 1
                            ldb_only_hit = True
                        else:
                            ldb_only_counts["unmatched:external_private"] += 1
                    else:
                        hit_aux = False
                        for pref in _proper_prefixes(nm):
                            if pref in ldb_exact or pref in ldb_unroot:
                                hit_aux = True
                                break
                        if hit_aux:
                            ldb_only_counts["aux_prefix:leanre_db"] += 1
                            ldb_only_hit = True
                        else:
                            ldb_only_counts["unmatched:leanre_db_only"] += 1

            mod: Optional[str] = None
            method: str = ""
            src_did: Optional[int] = None

            if not have_ldb and not have_src:
                method = "unmatched:no_source_index"
            elif have_src:
                # Authoritative Lean-scoped source map (`sighash.iter_source_decls`) FIRST so
                # Phase 2's anonymous-`end` namespace-popping bug cannot falsely align core/Mathlib
                # names (e.g. `Std.*`, `PLift.*`, `Height.*`, `Inter`, `Inv`, `Ext`) to project files.
                pmod = _parse_private_module(nm)
                if pmod is not None:
                    if not have_ldb or pmod in project_modules:
                        mod = pmod
                        method = "private_module"
                    else:
                        method = "unmatched:external_private"
                elif nm in src_exact and (not have_ldb or src_exact[nm][0] in project_modules):
                    smod, sln = src_exact[nm]
                    mod = smod
                    if nm in ldb_exact and ldb_exact[nm][0] == smod:
                        method = "leanre_db:exact"
                        src_did = ldb_exact[nm][1]
                    elif nm in ldb_unroot and ldb_unroot[nm][0] == smod:
                        method = "leanre_db:strip_root"
                        src_did = ldb_unroot[nm][1]
                    else:
                        method = "source_rescan:exact"
                        src_did = ldb_by_mod_line.get((smod, sln))
                else:
                    # Proper dot-prefixes in authoritative `src_exact` (auxiliaries like ._proof_1, .mk, .match_1)
                    for pref in _proper_prefixes(nm):
                        if pref in src_exact and (not have_ldb or src_exact[pref][0] in project_modules):
                            smod, sln = src_exact[pref]
                            mod = smod
                            if pref in ldb_exact and ldb_exact[pref][0] == smod:
                                method = "aux_prefix:leanre_db"
                                src_did = ldb_exact[pref][1]
                            elif pref in ldb_unroot and ldb_unroot[pref][0] == smod:
                                method = "aux_prefix:leanre_db"
                                src_did = ldb_unroot[pref][1]
                            else:
                                method = "aux_prefix:source_rescan"
                                src_did = ldb_by_mod_line.get((smod, sln))
                            break
                    if not method:
                        if ldb_only_hit:
                            phase2_bogus_collisions_avoided += 1
                        if (
                            (not have_ldb or CUT_CPT_COPY_MODULE in project_modules)
                            and _is_cut_cpt_generated(nm, known_source_names, cut_manual_names)
                        ):
                            mod = CUT_CPT_COPY_MODULE
                            method = "generated:CutCptCopy"
                            cut_cpt_decl_ids.append(did)
                        elif nm in tcb_library_names:
                            method = "unmatched:challenge_library"
                        else:
                            p0 = nm.split(".", 1)[0]
                            if p0 in project_top_prefixes:
                                segs = nm.split(".")
                                if any(s.startswith("inst") and len(s) > 4 and s[4:5].isupper() for s in segs):
                                    method = "unmatched:project_auto_instance"
                                elif nm.endswith("_assoc") and nm[:-6] in known_source_names:
                                    method = "unmatched:project_reassoc_attr"
                                else:
                                    method = "unmatched:project_namespace_other"
                                    if len(unmatched_proj_samples) < 40:
                                        unmatched_proj_samples.append(nm)
                            else:
                                method = "unmatched:library_or_external"
                                unmatched_ext_top[p0] += 1
            elif nm in ldb_exact:
                mod, src_did = ldb_exact[nm]
                method = "leanre_db:exact"
            elif nm in ldb_unroot:
                mod, src_did = ldb_unroot[nm]
                method = "leanre_db:strip_root"
            else:
                pmod = _parse_private_module(nm)
                if pmod is not None:
                    if pmod in project_modules:
                        mod = pmod
                        method = "private_module"
                    else:
                        method = "unmatched:external_private"
                else:
                    for pref in _proper_prefixes(nm):
                        if pref in ldb_exact:
                            mod, src_did = ldb_exact[pref]
                            method = "aux_prefix:leanre_db"
                            break
                        if pref in ldb_unroot:
                            mod, src_did = ldb_unroot[pref]
                            method = "aux_prefix:leanre_db"
                            break
                    if not method:
                        if (
                            CUT_CPT_COPY_MODULE in project_modules
                            and _is_cut_cpt_generated(nm, known_source_names, cut_manual_names)
                        ):
                            mod = CUT_CPT_COPY_MODULE
                            method = "generated:CutCptCopy"
                            cut_cpt_decl_ids.append(did)
                        elif nm in tcb_library_names:
                            method = "unmatched:challenge_library"
                        else:
                            p0 = nm.split(".", 1)[0]
                            if p0 in project_top_prefixes:
                                segs = nm.split(".")
                                if any(s.startswith("inst") and len(s) > 4 and s[4:5].isupper() for s in segs):
                                    method = "unmatched:project_auto_instance"
                                elif nm.endswith("_assoc") and nm[:-6] in known_source_names:
                                    method = "unmatched:project_reassoc_attr"
                                else:
                                    method = "unmatched:project_namespace_other"
                                    if len(unmatched_proj_samples) < 40:
                                        unmatched_proj_samples.append(nm)
                            else:
                                method = "unmatched:library_or_external"
                                unmatched_ext_top[p0] += 1

            align_rows.append((did, mod, method, src_did))
            decl_to_module[did] = mod
            decl_to_method[did] = method
            method_counts[method] += 1
            if is_live:
                method_counts_live[method] += 1
            if mod is not None:
                matched_modules_all.add(mod)
                if is_live:
                    matched_modules_live.add(mod)
            if src_did is not None:
                matched_ldb_decl_ids.add(src_did)

        h_dm = hashlib.sha256()
        with conn:
            conn.executemany(
                "INSERT INTO decl_module(decl_id, module, method, src_decl_id) VALUES (?,?,?,?)",
                align_rows,
            )
            conn.execute("CREATE INDEX decl_module_mod ON decl_module(module);")
            conn.execute("CREATE INDEX decl_module_method ON decl_module(method);")
        for did, mod, method, src_did in align_rows:
            h_dm.update(f"{did}\t{mod or ''}\t{method}\t{'' if src_did is None else src_did}\n".encode("utf-8"))

        # ---- Step B: K5 taint_sources + taint_paths -------------------------
        # Deduplicated by (class, decl_id)
        sources_map: Dict[Tuple[str, int], Tuple[str, Optional[str], Optional[int], str]] = {}
        unmapped_forensic: collections.Counter = collections.Counter()
        unmapped_forensic_examples: Dict[str, List[str]] = collections.defaultdict(list)
        forensic_hit_counts: Dict[Tuple[str, int], int] = collections.Counter()

        # 1. Source-level forensic hits from leanre.db
        for tag, mod, ln, dnm in forensic_hits_raw:
            did_hit: Optional[int] = None
            resolved_by = ""
            if dnm:
                cands = [dnm]
                if dnm.startswith("_root_."):
                    cands.append(dnm[7:])
                # Check source rescan name at exact (module, line_no) if present
                rescan_nm = src_by_mod_line.get((mod, ln))
                if rescan_nm and rescan_nm not in cands:
                    cands.append(rescan_nm)
                for c in cands:
                    if c in name_to_decl_id:
                        did_hit = name_to_decl_id[c]
                        resolved_by = "exact"
                        break
                    # Check private variant _private.<mod>.0.<c>
                    priv = f"_private.{mod}.0.{c}"
                    if priv in name_to_decl_id:
                        did_hit = name_to_decl_id[priv]
                        resolved_by = "private"
                        break
            else:
                rescan_nm = src_by_mod_line.get((mod, ln))
                if rescan_nm and rescan_nm in name_to_decl_id:
                    did_hit = name_to_decl_id[rescan_nm]
                    resolved_by = "line_rescan"

            if did_hit is None:
                unmapped_forensic[tag] += 1
                if len(unmapped_forensic_examples[tag]) < 10:
                    unmapped_forensic_examples[tag].append(f"{mod}:{ln}:{dnm or '<module-level>'}")
                continue

            key = (tag, did_hit)
            forensic_hit_counts[key] += 1
            if key not in sources_map:
                sources_map[key] = (
                    "source-hit:leanre.db",
                    mod,
                    ln,
                    f"forensic_hit tag={tag} resolved={resolved_by} at {mod}:{ln}",
                )

            # For `decide +kernel` / `lean4lean_timeout` / `slow_con_leche`, Lean 4 elaborates
            # `by decide +kernel` into a compiler-generated `._proof_1_1` (or `._proof_1`) auxiliary
            # holding the actual `Eq.refl Bool true` / `of_decide_eq_true` kernel reduction (and
            # `lean4lean-default-fuel-timeouts.log` / `con-leche-master.log` cite `._proof_1_1` directly).
            if tag in ("lean4lean_timeout", "slow_con_leche", "decide_kernel"):
                outer_nm = decl_id_to_name[did_hit]
                for suf in ("._proof_1_1", "._proof_1"):
                    aux_nm = outer_nm + suf
                    aux_did = name_to_decl_id.get(aux_nm)
                    if aux_did is None:
                        continue
                    aux_flags = decl_id_to_flags.get(aux_did, 0)
                    if tag in ("lean4lean_timeout", "slow_con_leche") or (aux_flags & (F_REFL_TRUE | F_OF_DECIDE)):
                        aux_key = (tag, aux_did)
                        if aux_key not in sources_map:
                            sources_map[aux_key] = (
                                "source-hit:leanre.db+aux_proof",
                                mod,
                                ln,
                                f"kernel reduction auxiliary for {outer_nm} ({mod}:{ln}, flags={aux_flags})",
                            )

        # Annotate hit multiplicities cleanly
        for key, cnt in forensic_hit_counts.items():
            if cnt > 1:
                orig, mod, ln, det = sources_map[key]
                sources_map[key] = (orig, mod, ln, f"{det} ({cnt} hits)")

        # 2. CutCptCopy generated declarations
        for did in cut_cpt_decl_ids:
            key = ("CutCptCopy", did)
            if key not in sources_map:
                sources_map[key] = (
                    "generated-copy",
                    CUT_CPT_COPY_MODULE,
                    CUT_CPT_COPY_LINE,
                    f"addDecl-generated *Cpt copy via cpt_copy_thms ({CUT_CPT_COPY_MODULE}:{CUT_CPT_COPY_LINE})",
                )

        # 3. Kernel-pattern flags directly from kernel expression terms
        decide_pattern_all: List[int] = []
        decide_pattern_live: List[int] = []
        pattern_totals: collections.Counter = collections.Counter()

        for did, nm, _kind, flags, lm in decls_rows:
            if flags & F_OF_DECIDE:
                pattern_totals["decide_kernel_pattern_all"] += 1
                decide_pattern_all.append(did)
                if lm != 0:
                    pattern_totals["decide_kernel_pattern_live"] += 1
                    decide_pattern_live.append(did)
            if (flags & F_REDUCE_BOOL) or nm in ("Lean.ofReduceBool", "Lean.reduceBool"):
                pattern_totals["ofReduceBool"] += 1
                sources_map[("ofReduceBool", did)] = (
                    "kernel-pattern:reduceBool",
                    decl_to_module.get(did),
                    None,
                    "constant Lean.ofReduceBool/reduceBool or direct reference",
                )
            if (flags & F_REDUCE_NAT) or nm in ("Lean.ofReduceNat", "Lean.reduceNat"):
                pattern_totals["ofReduceNat"] += 1
                sources_map[("ofReduceNat", did)] = (
                    "kernel-pattern:reduceNat",
                    decl_to_module.get(did),
                    None,
                    "constant Lean.ofReduceNat/reduceNat or direct reference",
                )
            if (flags & F_TRUST_COMPILER) or nm == "Lean.trustCompiler":
                pattern_totals["trustCompiler"] += 1
                sources_map[("trustCompiler", did)] = (
                    "kernel-pattern:trustCompiler",
                    decl_to_module.get(did),
                    None,
                    "constant Lean.trustCompiler or direct reference",
                )
            if (flags & F_SORRY) or nm == "sorryAx":
                pattern_totals["sorryAx"] += 1
                sources_map[("sorryAx", did)] = (
                    "kernel-pattern:sorryAx",
                    decl_to_module.get(did),
                    None,
                    "sorryAx or direct reference to sorryAx",
                )

        # Include decide_kernel_pattern sources (capped if huge, prioritizing live then ascending decl_id)
        decide_selected = decide_pattern_live[:max_pattern_taint_sources]
        if len(decide_selected) < max_pattern_taint_sources:
            rem = max_pattern_taint_sources - len(decide_selected)
            live_set = set(decide_selected)
            decide_selected.extend([d for d in decide_pattern_all if d not in live_set][:rem])
        for did in decide_selected:
            key = ("decide_kernel_pattern", did)
            if key not in sources_map:
                sources_map[key] = (
                    "kernel-pattern:of_decide_eq_true_refl",
                    decl_to_module.get(did),
                    None,
                    "value contains `of_decide_eq_true _ _ (Eq.refl Bool true)`",
                )

        # Deterministic ordering of taint_sources
        ordered_sources = sorted(sources_map.items(), key=lambda kv: (kv[0][0], kv[0][1]))
        source_rows: List[Tuple[int, str, int, str, Optional[str], Optional[int], str]] = []
        for sid, ((cls, did), (origin, mod, ln, detail)) in enumerate(ordered_sources, start=1):
            source_rows.append((sid, cls, did, origin, mod, ln, detail))

        # Reconstruct shortest paths from each root to each reachable taint source using `reach`
        # Load `reach` only for needed walks? Loading per-root parent dict in memory for 1.47M decls
        # would be ~50MB per root; doing one root at a time keeps memory tiny (~60MB) and is super fast!
        path_rows: List[Tuple[int, int, int, int, Optional[int]]] = []
        edge_pairs_needed: Set[Tuple[int, int]] = set()
        raw_paths: List[Tuple[int, int, List[int]]] = []

        live_sources_by_root: Dict[int, List[Tuple[int, int]]] = collections.defaultdict(list)
        for sid, _cls, did, _orig, _mod, _ln, _det in source_rows:
            lm = decl_id_to_live.get(did, 0)
            for rid, _rname, _rdecl, _rgrp in roots_rows:
                if lm & (1 << rid):
                    live_sources_by_root[rid].append((sid, did))

        for rid, _rname, rdecl, _rgrp in roots_rows:
            targets = live_sources_by_root.get(rid)
            if not targets:
                continue
            # Query parent pointers on demand via indexed PK(root_id, decl_id)
            parent_cache: Dict[int, Optional[int]] = {}
            for sid, target_did in targets:
                chain: List[int] = []
                cur: Optional[int] = target_did
                seen_loop: Set[int] = set()
                while cur is not None:
                    if cur in seen_loop:
                        raise RuntimeError(f"cycle in reach table for root {rid} at decl {cur}")
                    seen_loop.add(cur)
                    chain.append(cur)
                    if cur == rdecl:
                        break
                    if cur not in parent_cache:
                        row = conn.execute(
                            "SELECT parent FROM reach WHERE root_id = ? AND decl_id = ?",
                            (rid, cur),
                        ).fetchone()
                        if row is None:
                            raise RuntimeError(f"missing reach row for root {rid}, decl {cur}")
                        parent_cache[cur] = row[0]
                    cur = parent_cache[cur]
                if not chain or chain[-1] != rdecl:
                    raise RuntimeError(f"reach parent walk from {target_did} did not end at root {rdecl}")
                chain.reverse()
                raw_paths.append((sid, rid, chain))
                for u, v in zip(chain, chain[1:]):
                    edge_pairs_needed.add((u, v))

        # Look up exact edge kinds from `edges` table (PK(src, dst))
        edge_kind_map: Dict[Tuple[int, int], int] = {}
        for u, v in sorted(edge_pairs_needed):
            row = conn.execute("SELECT kind FROM edges WHERE src = ? AND dst = ?", (u, v)).fetchone()
            if row is None:
                raise RuntimeError(f"taint path edge ({u} -> {v}) not present in edges table!")
            edge_kind_map[(u, v)] = int(row[0])

        for sid, rid, chain in raw_paths:
            path_rows.append((sid, rid, 0, chain[0], None))
            for hop_idx, (u, v) in enumerate(zip(chain, chain[1:]), start=1):
                path_rows.append((sid, rid, hop_idx, v, edge_kind_map[(u, v)]))

        with conn:
            conn.executemany(
                "INSERT INTO taint_sources(id, class, decl_id, origin, module, line_no, detail) VALUES (?,?,?,?,?,?,?)",
                source_rows,
            )
            conn.executemany(
                "INSERT INTO taint_paths(source_id, root_id, hop, decl_id, edge_kind) VALUES (?,?,?,?,?)",
                path_rows,
            )
            conn.execute("CREATE INDEX taint_sources_class ON taint_sources(class, decl_id);")
            conn.execute("CREATE INDEX taint_sources_decl ON taint_sources(decl_id);")
            conn.execute("CREATE INDEX taint_paths_hop0 ON taint_paths(hop, root_id, source_id);")

        # ---- Independent edge-by-edge validation of EVERY stored taint path (K5) ----
        val_summary = validate_taint_paths(conn)
        if val_summary["failures"] > 0:
            raise RuntimeError(f"taint path validation failed: {val_summary}")

        # Content hashes of enrichment tables (determinism receipt K7)
        h_ts = hashlib.sha256()
        for row in source_rows:
            h_ts.update(f"{row[0]}\t{row[1]}\t{row[2]}\t{row[3]}\t{row[4] or ''}\t{'' if row[5] is None else row[5]}\t{row[6]}\n".encode("utf-8"))
        h_tp = hashlib.sha256()
        for row in path_rows:
            h_tp.update(f"{row[0]}\t{row[1]}\t{row[2]}\t{row[3]}\t{'' if row[4] is None else row[4]}\n".encode("utf-8"))

        # Summarize alignment & taint
        total_decls = len(decls_rows)
        total_live = sum(1 for _d, _n, _k, _f, lm in decls_rows if lm != 0)
        matched_all = sum(cnt for m, cnt in method_counts.items() if not m.startswith("unmatched:"))
        matched_live = sum(cnt for m, cnt in method_counts_live.items() if not m.startswith("unmatched:"))
        unmatched_all = total_decls - matched_all
        unmatched_live = total_live - matched_live
        ldb_only_matched = sum(cnt for m, cnt in ldb_only_counts.items() if not m.startswith("unmatched:"))

        alignment_summary = {
            "total_decls": total_decls,
            "total_live_decls": total_live,
            "matched_all": matched_all,
            "matched_all_pct": round(100.0 * matched_all / max(1, total_decls), 2),
            "unmatched_all": unmatched_all,
            "unmatched_all_pct": round(100.0 * unmatched_all / max(1, total_decls), 2),
            "matched_live": matched_live,
            "matched_live_pct": round(100.0 * matched_live / max(1, total_live), 2),
            "unmatched_live": unmatched_live,
            "by_method": dict(sorted(method_counts.items())),
            "by_method_live": dict(sorted(method_counts_live.items())),
            "leanre_db_only_matched": ldb_only_matched,
            "leanre_db_only_by_method": dict(sorted(ldb_only_counts.items())),
            "phase2_bogus_collisions_avoided": phase2_bogus_collisions_avoided,
            "leanre_db_modules_total": len(project_modules),
            "leanre_db_modules_covered_all": len(matched_modules_all),
            "leanre_db_modules_covered_live": len(matched_modules_live),
            "leanre_db_decl_rows_total": ldb_total_rows,
            "leanre_db_decl_rows_covered": len(matched_ldb_decl_ids),
            "leanre_db_multi_module_names": ldb_multi_names,
            "source_rescan_files": src_files_scanned,
            "source_rescan_names": len(src_exact),
            "unmatched_external_top20": dict(unmatched_ext_top.most_common(20)),
            "unmatched_project_samples": unmatched_proj_samples[:20],
        }

        taint_by_class: Dict[str, Dict[str, Any]] = {}
        cls_sources = collections.Counter(r[1] for r in source_rows)
        cls_live_sources = collections.Counter(r[1] for r in source_rows if decl_id_to_live.get(r[2], 0) != 0)
        cls_paths = collections.Counter()
        cls_min_hop: Dict[str, int] = {}
        sid_to_cls = {r[0]: r[1] for r in source_rows}
        for sid, _rid, chain in raw_paths:
            c = sid_to_cls[sid]
            cls_paths[c] += 1
            hops = len(chain) - 1
            if c not in cls_min_hop or hops < cls_min_hop[c]:
                cls_min_hop[c] = hops
        for c in sorted(set(cls_sources) | set(TAINT_FORENSIC_TAGS) | {"ofReduceBool", "ofReduceNat", "trustCompiler", "sorryAx", "decide_kernel_pattern"}):
            taint_by_class[c] = {
                "sources": cls_sources.get(c, 0),
                "live_sources": cls_live_sources.get(c, 0),
                "paths": cls_paths.get(c, 0),
                "min_hops": cls_min_hop.get(c),
            }

        # Build structured per-module `lean4lean_timeout` audit directly from decl_module + leanre.db
        mod_to_live_decls: Dict[str, List[Dict[str, Any]]] = collections.defaultdict(list)
        for did, mod, method, _sdid in align_rows:
            if mod is not None and decl_id_to_live.get(did, 0) != 0:
                mod_to_live_decls[mod].append({
                    "decl_id": did,
                    "name": decl_id_to_name[did],
                    "kind": decl_id_to_kind[did],
                    "flags": decl_id_to_flags[did],
                    "live_mask": decl_id_to_live[did],
                    "method": method,
                })

        timeout_entries: List[Dict[str, Any]] = []
        seen_timeout_mods: Set[str] = set()
        for tag, mod, ln, dnm in forensic_hits_raw:
            if tag != "lean4lean_timeout" or mod in seen_timeout_mods:
                continue
            seen_timeout_mods.add(mod)
            live_list = mod_to_live_decls.get(mod, [])
            aux_nm = f"{dnm}._proof_1_1" if dnm else None
            # Trace shortest import chain from `mod` to the first module with >=1 live kernel decl
            import_chain_to_live: List[Dict[str, Any]] = []
            if not live_list and mod in ldb_rev_imports:
                q_c: collections.deque = collections.deque([(mod, [mod])])
                vis_c: Set[str] = {mod}
                found_chain: Optional[List[str]] = None
                while q_c:
                    cm, path = q_c.popleft()
                    if cm != mod and len(mod_to_live_decls.get(cm, [])) > 0:
                        found_chain = path
                        break
                    for im in ldb_rev_imports.get(cm, []):
                        if im not in vis_c:
                            vis_c.add(im)
                            q_c.append((im, path + [im]))
                if found_chain:
                    import_chain_to_live = [
                        {"module": pm, "kernel_live_decls": len(mod_to_live_decls.get(pm, []))}
                        for pm in found_chain
                    ]
            timeout_entries.append({
                "module": mod,
                "line_no": ln,
                "source_decl": dnm,
                "source_decl_in_kernel": bool(dnm and dnm in name_to_decl_id),
                "timeout_aux_proof": aux_nm,
                "timeout_aux_proof_in_kernel": bool(aux_nm and aux_nm in name_to_decl_id),
                "timeout_aux_proof_decl_id": name_to_decl_id.get(aux_nm) if aux_nm else None,
                "timeout_aux_proof_flags": decl_id_to_flags.get(name_to_decl_id[aux_nm], 0) if (aux_nm and aux_nm in name_to_decl_id) else None,
                "module_live_decls_count": len(live_list),
                "module_live_decls": live_list,
                "direct_importers": ldb_rev_imports.get(mod, []),
                "import_chain_to_first_live_module": import_chain_to_live,
            })

        dyadic_smallloop = "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.SmallLoop"
        lean4lean_timeout_audit: Dict[str, Any] = {
            "total_timeout_modules": len(timeout_entries),
            "live_timeout_modules": sum(1 for e in timeout_entries if e["module_live_decls_count"] > 0),
            "dead_timeout_modules": sum(1 for e in timeout_entries if e["module_live_decls_count"] == 0),
            "live_decls_across_timeout_modules": sum(e["module_live_decls_count"] for e in timeout_entries),
            "modules": timeout_entries,
            "dyadic_smallloop_disambiguation": {
                "module": dyadic_smallloop,
                "in_leanre_db": dyadic_smallloop in project_modules,
                "kernel_live_decls_count": len(mod_to_live_decls.get(dyadic_smallloop, [])),
                "note": "Distinct from ChebyshevPrimeBounds.SmallLoop (whose 9 kernel decls are all live).",
            } if dyadic_smallloop in project_modules else None,
        }

        taint_summary = {
            "total_sources": len(source_rows),
            "total_paths": len(raw_paths),
            "total_path_hops": len(path_rows),
            "by_class": taint_by_class,
            "pattern_totals": dict(sorted(pattern_totals.items())),
            "pattern_cap": max_pattern_taint_sources,
            "unmapped_forensic_hits": dict(sorted(unmapped_forensic.items())),
            "unmapped_forensic_examples": dict(sorted(unmapped_forensic_examples.items())),
            "lean4lean_timeout_audit": lean4lean_timeout_audit,
            "validation": val_summary,
        }

        # Update meta table cleanly (keeping entries compact <=4096B for workbench)
        ch_row = conn.execute("SELECT value_json FROM meta WHERE key = 'content_hashes'").fetchone()
        ch_map = json.loads(ch_row[0]) if ch_row else {}
        ch_map["decl_module"] = h_dm.hexdigest()
        ch_map["taint_sources"] = h_ts.hexdigest()
        ch_map["taint_paths"] = h_tp.hexdigest()
        compact_align = {
            "total_decls": total_decls,
            "matched_all": matched_all,
            "unmatched_all": unmatched_all,
            "matched_all_pct": alignment_summary["matched_all_pct"],
            "leanre_db_only_matched": ldb_only_matched,
            "modules_covered_live": len(matched_modules_live),
            "modules_total": len(project_modules),
            "by_method": alignment_summary["by_method"],
        }
        compact_taint = {
            "total_sources": len(source_rows),
            "total_paths": len(raw_paths),
            "validation": val_summary,
            "pattern_totals": taint_summary["pattern_totals"],
            "lean4lean_timeout_modules": {
                "total": lean4lean_timeout_audit["total_timeout_modules"],
                "live": lean4lean_timeout_audit["live_timeout_modules"],
                "dead": lean4lean_timeout_audit["dead_timeout_modules"],
                "live_decls_in_live_modules": lean4lean_timeout_audit["live_decls_across_timeout_modules"],
            },
            "classes": {k: {"sources": v["sources"], "paths": v["paths"], "min_hops": v["min_hops"]} for k, v in taint_by_class.items() if v["sources"] > 0 or k in ("ofReduceBool", "sorryAx", "CutCptCopy", "kexactB")},
        }
        with conn:
            conn.execute("INSERT OR REPLACE INTO meta(key, value_json) VALUES (?, ?)", ("content_hashes", json.dumps(ch_map, sort_keys=True)))
            conn.execute("INSERT OR REPLACE INTO meta(key, value_json) VALUES (?, ?)", ("alignment_summary", json.dumps(compact_align, sort_keys=True)))
            conn.execute("INSERT OR REPLACE INTO meta(key, value_json) VALUES (?, ?)", ("taint_summary", json.dumps(compact_taint, sort_keys=True)))
            conn.execute("ANALYZE;")

        elapsed = round(time.time() - t0, 2)
        if verbose:
            print(
                f"[kernel] enriched in {elapsed:.2f}s: decl_module matched {matched_all:,}/{total_decls:,} "
                f"({alignment_summary['matched_all_pct']}%), taint {len(source_rows):,} sources -> "
                f"{len(raw_paths):,} validated paths ({val_summary['edges_validated']:,} edges, 0 failures)",
                file=sys.stderr,
            )
        return {
            "elapsed_s": elapsed,
            "alignment": alignment_summary,
            "taint": taint_summary,
            "content_hashes": ch_map,
        }
    finally:
        conn.close()


def validate_taint_paths(conn: sqlite3.Connection) -> Dict[str, Any]:
    """Independently verify EVERY row in `taint_paths` against `roots`, `taint_sources`, and `edges`."""
    roots = {int(r[0]): int(r[1]) for r in conn.execute("SELECT id, decl_id FROM roots")}
    sources = {int(r[0]): int(r[1]) for r in conn.execute("SELECT id, decl_id FROM taint_sources")}
    edge_cache: Dict[Tuple[int, int], Optional[int]] = {}
    paths_checked = 0
    edges_checked = 0
    failures: List[str] = []

    def lookup_edge(u: int, v: int) -> Optional[int]:
        k = (u, v)
        if k not in edge_cache:
            row = conn.execute("SELECT kind FROM edges WHERE src = ? AND dst = ?", (u, v)).fetchone()
            edge_cache[k] = None if row is None else int(row[0])
        return edge_cache[k]

    cur_key: Optional[Tuple[int, int]] = None
    cur_hops: List[Tuple[int, int, Optional[int]]] = []

    def check_one(key: Tuple[int, int], hops: List[Tuple[int, int, Optional[int]]]) -> None:
        nonlocal paths_checked, edges_checked
        paths_checked += 1
        sid, rid = key
        if sid not in sources:
            failures.append(f"unknown source_id {sid}")
            return
        if rid not in roots:
            failures.append(f"unknown root_id {rid}")
            return
        if not hops:
            failures.append(f"empty path ({sid},{rid})")
            return
        if hops[0][0] != 0 or hops[0][1] != roots[rid]:
            failures.append(f"path ({sid},{rid}) hop 0 mismatch: {hops[0]} expected root decl {roots[rid]}")
        if hops[-1][1] != sources[sid]:
            failures.append(f"path ({sid},{rid}) final decl mismatch: {hops[-1]} expected {sources[sid]}")
        for idx, (hop, did, ek) in enumerate(hops):
            if hop != idx:
                failures.append(f"path ({sid},{rid}) non-contiguous hop {hop} at index {idx}")
                break
            if idx == 0:
                if ek is not None:
                    failures.append(f"path ({sid},{rid}) hop 0 should have NULL edge_kind, got {ek}")
            else:
                u = hops[idx - 1][1]
                v = did
                stored = lookup_edge(u, v)
                edges_checked += 1
                if stored is None:
                    failures.append(f"path ({sid},{rid}) hop {idx}: edge ({u}->{v}) missing from edges table")
                elif stored != ek:
                    failures.append(f"path ({sid},{rid}) hop {idx}: edge ({u}->{v}) kind {ek} != stored {stored}")

    for sid, rid, hop, did, ek in conn.execute(
        "SELECT source_id, root_id, hop, decl_id, edge_kind FROM taint_paths ORDER BY source_id, root_id, hop"
    ):
        key = (int(sid), int(rid))
        if cur_key is not None and key != cur_key:
            check_one(cur_key, cur_hops)
            cur_hops = []
        cur_key = key
        cur_hops.append((int(hop), int(did), None if ek is None else int(ek)))
    if cur_key is not None:
        check_one(cur_key, cur_hops)

    return {
        "paths_validated": paths_checked,
        "edges_validated": edges_checked,
        "unique_edges_checked": len(edge_cache),
        "failures": len(failures),
        "failure_examples": failures[:20],
    }


def extract_sample_taint_paths(conn: sqlite3.Connection, per_class: int = 3) -> Dict[str, List[Dict[str, Any]]]:
    """Extract shortest sample taint paths per class (declaration identifiers + edge kinds only)."""
    out: Dict[str, List[Dict[str, Any]]] = {}
    classes = [r[0] for r in conn.execute("SELECT DISTINCT class FROM taint_sources ORDER BY class")]
    for cls in classes:
        rows = conn.execute(
            """
            SELECT s.id, s.decl_id, d.name, s.origin, s.module, s.line_no, p.root_id, r.name,
                   (SELECT MAX(q.hop) FROM taint_paths q WHERE q.source_id = p.source_id AND q.root_id = p.root_id) AS hops
            FROM taint_paths p
            JOIN taint_sources s ON s.id = p.source_id
            JOIN decls d ON d.id = s.decl_id
            JOIN roots r ON r.id = p.root_id
            WHERE p.hop = 0 AND s.class = ?
            ORDER BY hops ASC, p.root_id ASC, s.id ASC
            LIMIT ?
            """,
            (cls, per_class),
        ).fetchall()
        samples: List[Dict[str, Any]] = []
        for sid, sdid, sname, origin, mod, ln, rid, rname, hops in rows:
            chain = conn.execute(
                """
                SELECT p.hop, d.name, d.kind, p.edge_kind, m.module
                FROM taint_paths p
                JOIN decls d ON d.id = p.decl_id
                LEFT JOIN decl_module m ON m.decl_id = p.decl_id
                WHERE p.source_id = ? AND p.root_id = ?
                ORDER BY p.hop
                """,
                (sid, rid),
            ).fetchall()
            samples.append({
                "source_id": sid,
                "source_decl": sname,
                "source_module": mod,
                "source_line": ln,
                "origin": origin,
                "root": rname,
                "hops": hops,
                "path": [
                    {
                        "hop": h,
                        "decl": nm,
                        "kind": kd,
                        "edge_kind": None if ek is None else EDGE_KIND_NAMES.get(int(ek), str(ek)),
                        "module": m,
                    }
                    for h, nm, kd, ek, m in chain
                ],
            })
        out[cls] = samples
    return out


def verify_k3_regression(
    challenge_db: str,
    leanre_db: str,
    challenge_stats_path: Optional[str] = None,
    ref_sighash_nolex_sha: Optional[str] = None,
    ref_sighash_lex_sha: Optional[str] = None,
) -> Dict[str, Any]:
    """Run exact K3 regression comparing `challenge_db` against Phase 2 `leanre_db`."""
    k = sqlite3.connect(f"file:{os.path.abspath(challenge_db)}?mode=ro", uri=True)
    p = sqlite3.connect(f"file:{os.path.abspath(leanre_db)}?mode=ro", uri=True)
    try:
        k_decls = set(k.execute("SELECT name, kind FROM decls"))
        p_decls = set(p.execute("SELECT name, kind FROM tcb_decls"))
        k_edges = {
            (s, d, EDGE_KIND_NAMES[int(ek)])
            for s, d, ek in k.execute(
                "SELECT ds.name, dd.name, e.kind FROM edges e "
                "JOIN decls ds ON ds.id = e.src JOIN decls dd ON dd.id = e.dst"
            )
        }
        p_edges = set(p.execute("SELECT src, dst, edge_kind FROM tcb_edges"))

        # Check STMT_ALL dominator tree exact match
        tid = k.execute("SELECT id FROM dom_trees WHERE label = 'STMT_ALL'").fetchone()[0]
        k_dom = {
            nm: (dp, int(sz))
            for nm, dp, sz in k.execute(
                "SELECT d.name, dp.name, dm.subtree_size FROM dom dm "
                "JOIN decls d ON d.id = dm.decl_id LEFT JOIN decls dp ON dp.id = dm.idom "
                "WHERE dm.tree_id = ?",
                (tid,),
            )
        }
        p_dom = {
            nm: (None if dp == "__HEADLINES__" else dp, int(sz))
            for nm, dp, sz in p.execute(
                "SELECT name, dom_parent, dom_subtree_size FROM tcb_decls WHERE depth_from_any >= 0"
            )
        }

        # Check def-cone, GRH delta, sorryAx
        defcone_union = int(k.execute("SELECT COUNT(*) FROM decls WHERE defcone_mask != 0").fetchone()[0])
        stmt_rh0 = int(k.execute("SELECT COUNT(*) FROM decls WHERE (stmt_mask & 1) != 0").fetchone()[0])
        stmt_rh_both = int(k.execute("SELECT COUNT(*) FROM decls WHERE (stmt_mask & 3) != 0").fetchone()[0])
        stmt_grh_extra_vs_rh0 = int(
            k.execute("SELECT COUNT(*) FROM decls WHERE (stmt_mask & 28) != 0 AND (stmt_mask & 1) = 0").fetchone()[0]
        )
        stmt_grh_extra_vs_rh_both = int(
            k.execute("SELECT COUNT(*) FROM decls WHERE (stmt_mask & 28) != 0 AND (stmt_mask & 3) = 0").fetchone()[0]
        )
        sorry_row = k.execute("SELECT id, fan_in, live_mask, stmt_mask FROM decls WHERE name = 'sorryAx'").fetchone()
        sorry_users = []
        if sorry_row is not None:
            sorry_users = [
                {"name": nm, "edge_kind": EDGE_KIND_NAMES[int(ek)]}
                for nm, ek in k.execute(
                    "SELECT d.name, e.kind FROM edges e JOIN decls d ON d.id = e.src WHERE e.dst = ? ORDER BY d.id",
                    (sorry_row[0],),
                )
            ]

        # Sighash TSV SHA-256 over consts
        h_sig = hashlib.sha256()
        n_consts = 0
        for nm, ck, sh, sha, sz, nl in k.execute(
            "SELECT name, ckind, sighash, sighash_anon, sig_size, n_local FROM consts ORDER BY id"
        ):
            n_consts += 1
            role = "ind" if ck == "induct" else ck
            h_sig.update(f"{nm}\t{role}\t{sh[4:]}\t{sha[4:]}\t{sz}\t{nl}\n".encode("utf-8"))
        sighash_tsv_sha = h_sig.hexdigest()

        checks = {
            "decls_51692_exact_set": (len(k_decls) == 51692 and k_decls == p_decls),
            "edges_1206518_exact_typed_set": (len(k_edges) == 1206518 and k_edges == p_edges),
            "stmt_all_dom_exact_match": (k_dom == p_dom and len(k_dom) == 51687),
            "defcone_2570": (defcone_union == 2570),
            "grh_extra_vs_rh_470": (stmt_grh_extra_vs_rh0 == 470),
            "sorry_fan_in_5_value_only_not_in_stmt": (
                sorry_row is not None
                and int(sorry_row[1]) == 5
                and int(sorry_row[3]) == 0
                and len(sorry_users) == 5
                and all(u["edge_kind"] == "value" for u in sorry_users)
            ),
        }
        if ref_sighash_nolex_sha:
            checks["sighash_tsv_sha_nolex"] = (sighash_tsv_sha == ref_sighash_nolex_sha)
        if ref_sighash_lex_sha:
            checks["sighash_tsv_sha_lex"] = (sighash_tsv_sha == ref_sighash_lex_sha)

        inp_meta = json.loads(k.execute("SELECT value_json FROM meta WHERE key = 'input'").fetchone()[0])
        res = {
            "all_passed": all(checks.values()),
            "checks": checks,
            "input": inp_meta,
            "counts": {
                "decls": len(k_decls),
                "consts": n_consts,
                "edges": len(k_edges),
                "stmt_cone_rh0": stmt_rh0,
                "stmt_cone_rh_both": stmt_rh_both,
                "grh_extra_vs_rh0": stmt_grh_extra_vs_rh0,
                "grh_extra_vs_rh_both": stmt_grh_extra_vs_rh_both,
                "defcone_union": defcone_union,
                "sorry_fan_in": int(sorry_row[1]) if sorry_row else 0,
                "sorry_users": sorry_users,
                "sighash_tsv_sha256": sighash_tsv_sha,
            },
        }
        if challenge_stats_path and os.path.exists(challenge_stats_path):
            with open(challenge_stats_path, "r", encoding="utf-8") as f:
                cst = json.load(f)
            res["oracle_failures_total"] = cst["dominators"]["oracle_failures_total"]
            res["checks"]["oracle_zero_failures"] = (res["oracle_failures_total"] == 0)
            res["all_passed"] = all(res["checks"].values())
        return res
    finally:
        k.close()
        p.close()


def build_report(
    run_stats: Dict[str, Any],
    enrich_res: Dict[str, Any],
    kernel_db_path: str,
    k3_result: Optional[Dict[str, Any]] = None,
    determinism: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    """Assemble the compact, git-committable `outputs/kernel_report.json` (K1-K7 receipts)."""
    conn = sqlite3.connect(f"file:{os.path.abspath(kernel_db_path)}?mode=ro", uri=True)
    try:
        sample_paths = extract_sample_taint_paths(conn, per_class=3)
    finally:
        conn.close()

    db_bytes, db_sha = _file_sha256(kernel_db_path)
    inp = run_stats["input"]
    decls = run_stats["declarations"]
    is_solution = (inp.get("file_sha256") == EXPECTED_SOLUTION_SHA256)

    k1 = {
        "provenance": "L",
        "file_bytes": inp["file_bytes"],
        "file_sha256": inp["file_sha256"],
        "uncompressed_bytes": inp["uncompressed_bytes"],
        "uncompressed_sha256": inp["uncompressed_sha256"],
        "matches_expected_solution": (
            inp["file_bytes"] == EXPECTED_SOLUTION_BYTES
            and inp["file_sha256"] == EXPECTED_SOLUTION_SHA256
            and inp["uncompressed_bytes"] == EXPECTED_SOLUTION_UNCOMPRESSED_BYTES
            and inp["uncompressed_sha256"] == EXPECTED_SOLUTION_UNCOMPRESSED_SHA256
        ),
    }

    n_rec = decls["records"]
    n_const = decls["constants_unpacked"]
    ind = decls["inductive"]
    k2 = {
        "provenance": "L",
        "counting_rules": {
            "declaration_records": (
                "1 per top-level declaration JSON record in the NDJSON stream "
                "(thm + def + opaque + axiom + quot + inductive; each inductive record folds its types, ctors, and recursors). "
                "Matches con-leche fold-record counting."
            ),
            "constants_unpacked": (
                "1 per kernel constant added to the environment: "
                "thm + def + opaque + axiom + quot + inductive.types + inductive.ctors + inductive.recs. "
                "Matches nanoda constant-level counting."
            ),
        },
        "measured_records": n_rec,
        "measured_constants_unpacked": n_const,
        "by_kind": decls["by_kind"],
        "inductive_breakdown": ind,
        "unpacked_minus_records": n_const - n_rec,
        "reconciliation": {
            "con_leche_reference": 1_468_418,
            "con_leche_delta_vs_records": n_rec - 1_468_418,
            "nanoda_reference_nasqret": 1_484_733,
            "nanoda_delta_vs_constants": n_const - 1_484_733,
            "formula_check": (
                decls["by_kind"]["thm"]
                + decls["by_kind"]["def"]
                + decls["by_kind"]["opaque"]
                + decls["by_kind"]["axiom"]
                + decls["by_kind"]["quot"]
                + ind["types"]
                + ind["ctors"]
                + ind["recs"]
                == n_const
            ),
        },
        "unsafe_records": decls["unsafe_records"],
        "partial_records": decls["partial_records"],
        "records_in_mutual_all_group": decls["records_in_mutual_all_group"],
    }

    # Trim dominator trees to top-25 per tree to keep JSON compact & readable
    dom_trees_compact = []
    for t in run_stats["dominators"]["trees"]:
        dom_trees_compact.append({
            "id": t["id"],
            "label": t["label"],
            "view": t["view"],
            "root_ids": t["root_ids"],
            "n_nodes": t["n_nodes"],
            "max_depth": t["max_depth"],
            "top25": t["top50"][:25],
        })

    return {
        "schema_version": run_stats["tool"]["schema_version"],
        "provenance": "L",
        "epistemic_note": (
            "Layer 1/2/3 instrumentation only: kernel graph & axiom extraction records what the "
            "Lean 4.33.1 export contains (Layer 1 syntactic DAG / Layer 2 TCB visibility); it is "
            "not a mathematical refereeing claim (Layer 4)."
        ),
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "tool": run_stats["tool"],
        "export_meta": run_stats["export_meta"],
        "stream": run_stats["stream"],
        "k1_integrity": k1,
        "k2_counts": k2,
        "k3_challenge_regression": k3_result,
        "k4_live_dead_and_axioms": {
            "roots": run_stats["roots"],
            "groups": run_stats["groups"],
            "union": run_stats["union"],
            "edges": run_stats["edges"],
            "axioms": run_stats["axioms"],
            "special": run_stats["special"],
            "kernel_pattern_flags": run_stats["kernel_pattern_flags"],
        },
        "k5_dominators_and_taint": {
            "dominator_algorithm": run_stats["dominators"]["algorithm"],
            "dominator_oracle": run_stats["dominators"]["oracle"],
            "dominator_oracle_failures_total": run_stats["dominators"]["oracle_failures_total"],
            "dominator_trees": dom_trees_compact,
            "taint_summary": enrich_res["taint"],
            "lean4lean_timeout_audit": enrich_res["taint"].get("lean4lean_timeout_audit"),
            "sample_taint_paths": sample_paths,
        },
        "k6_module_alignment": enrich_res["alignment"],
        "k7_performance_and_determinism": {
            "rust_extract_timings_s": run_stats["run"]["timings"],
            "enrich_elapsed_s": enrich_res["elapsed_s"],
            "peak_rss_kib": run_stats["run"]["peak_rss_kib"],
            "peak_rss_gib": round(run_stats["run"]["peak_rss_kib"] / 1048576.0, 3),
            "store_bytes": run_stats["run"]["store_bytes"],
            "kernel_db_bytes": db_bytes,
            "kernel_db_sha256": db_sha,
            "content_hashes": enrich_res["content_hashes"],
            "determinism": determinism,
        },
        "sighash": run_stats["sighash"],
        "is_full_solution": is_solution,
    }


def run_pipeline(
    input_path: str,
    out_dir: str,
    leanre_db: Optional[str] = None,
    src_dir: Optional[str] = None,
    lexicon: Optional[str] = None,
    report_path: Optional[str] = None,
    threads: int = 48,
    workers: int = 24,
    oracle_random: int = 1000,
    oracle_top: int = 50,
    roots: Optional[Sequence[str]] = None,
    expect_sha256: Optional[str] = None,
    expect_uncompressed_sha256: Optional[str] = None,
    binary_path: Optional[str] = None,
    auto_build: bool = True,
    k3_result: Optional[Dict[str, Any]] = None,
    determinism: Optional[Dict[str, Any]] = None,
    verbose: bool = True,
) -> Dict[str, Any]:
    """End-to-end atomic build of `<out_dir>/kernel.db` + optional `kernel_report.json`."""
    bin_path = binary_path or default_binary_path()
    if not os.path.exists(bin_path):
        if auto_build:
            bin_path = build_binary(verbose=verbose)
        else:
            raise FileNotFoundError(f"leanre-kernel binary not found at {bin_path}")

    os.makedirs(out_dir, exist_ok=True)
    stage_dir = os.path.join(out_dir, f".building-{os.getpid()}")
    if os.path.exists(stage_dir):
        shutil.rmtree(stage_dir)
    os.makedirs(stage_dir, exist_ok=True)

    try:
        cmd = [
            bin_path,
            "extract",
            "--input", input_path,
            "--out-dir", stage_dir,
            "--threads", str(min(max(1, threads), 64)),
            "--oracle-random", str(oracle_random),
            "--oracle-top", str(oracle_top),
        ]
        if lexicon:
            cmd.extend(["--local-lexicon", lexicon])
        if roots:
            for r in roots:
                cmd.extend(["--root", r])
        if verbose:
            print(f"[kernel] running: {' '.join(cmd)}", file=sys.stderr)
        res = subprocess.run(cmd)
        if res.returncode != 0:
            raise RuntimeError(f"leanre-kernel extract exited with {res.returncode}")

        stage_db = os.path.join(stage_dir, "kernel.db")
        stage_stats = os.path.join(stage_dir, "run_stats.json")
        with open(stage_stats, "r", encoding="utf-8") as f:
            run_stats = json.load(f)

        inp = run_stats["input"]
        if expect_sha256 and inp["file_sha256"] != expect_sha256:
            raise ValueError(f"compressed SHA-256 mismatch: got {inp['file_sha256']} expected {expect_sha256}")
        if expect_uncompressed_sha256 and inp["uncompressed_sha256"] != expect_uncompressed_sha256:
            raise ValueError(
                f"uncompressed SHA-256 mismatch: got {inp['uncompressed_sha256']} expected {expect_uncompressed_sha256}"
            )

        enrich_res = enrich_kernel_db(
            stage_db,
            leanre_db_path=leanre_db,
            src_dir=src_dir,
            workers=workers,
            verbose=verbose,
        )

        final_db = os.path.join(out_dir, "kernel.db")
        final_stats = os.path.join(out_dir, "run_stats.json")
        os.replace(stage_db, final_db)
        os.replace(stage_stats, final_stats)
    finally:
        if os.path.exists(stage_dir):
            shutil.rmtree(stage_dir, ignore_errors=True)

    rep = build_report(
        run_stats,
        enrich_res,
        final_db,
        k3_result=k3_result,
        determinism=determinism,
    )
    if report_path:
        os.makedirs(os.path.dirname(os.path.abspath(report_path)), exist_ok=True)
        tmp_rep = report_path + ".tmp"
        with open(tmp_rep, "w", encoding="utf-8") as f:
            json.dump(rep, f, indent=2, ensure_ascii=False)
            f.write("\n")
        os.replace(tmp_rep, report_path)
    return rep


def default_kernel_db_path() -> str:
    return os.path.join(_REPO_ROOT, "outputs", "kernel", "kernel.db")


FLAG_NAMES: Tuple[Tuple[int, str], ...] = (
    (F_REFL_TRUE, "refl_true"),
    (F_OF_DECIDE, "of_decide_eq_true_refl"),
    (F_REDUCE_BOOL, "reduceBool"),
    (F_REDUCE_NAT, "reduceNat"),
    (F_SORRY, "sorryAx"),
    (F_TRUST_COMPILER, "trustCompiler"),
)

_EDGE_KIND_SETS: Dict[str, Tuple[int, ...]] = {
    "both": (1, 2, 3),
    "all": (1, 2, 3),
    "type": (1, 3),
    "value": (2, 3),
    "type-only": (1,),
    "value-only": (2,),
    "type+value": (3,),
}


def decode_flags(flags: int) -> List[str]:
    return [name for bit, name in FLAG_NAMES if flags & bit]


def _open_kernel_ro(kernel_db_path: str) -> sqlite3.Connection:
    if not os.path.exists(kernel_db_path):
        raise FileNotFoundError(f"kernel DB not found: {kernel_db_path}")
    return sqlite3.connect(f"file:{os.path.abspath(kernel_db_path)}?mode=ro", uri=True)


def _resolve_decl_id(conn: sqlite3.Connection, decl: str) -> Tuple[int, str, Optional[str]]:
    """Resolve `decl` by exact `decls.name`, falling back to `consts.name` -> `decl_id`.
    Returns `(decl_id, primary_name, resolved_from_const_or_None)`.
    """
    row = conn.execute("SELECT id, name FROM decls WHERE name = ?", (decl,)).fetchone()
    if row is not None:
        return int(row[0]), str(row[1]), None
    crow = conn.execute(
        "SELECT c.decl_id, d.name FROM consts c JOIN decls d ON d.id = c.decl_id WHERE c.name = ?",
        (decl,),
    ).fetchone()
    if crow is not None:
        return int(crow[0]), str(crow[1]), decl
    raise LookupError(f"declaration not found in kernel.db: {decl}")


def _resolve_dom_tree(conn: sqlite3.Connection, tree: str) -> Tuple[int, str, str]:
    row = conn.execute(
        "SELECT id, label, view FROM dom_trees WHERE label = ?",
        (tree,),
    ).fetchone()
    if row is None:
        avail = [r[0] for r in conn.execute("SELECT label FROM dom_trees ORDER BY id")]
        raise ValueError(f"unknown dominator tree {tree!r}; available: {avail}")
    return int(row[0]), str(row[1]), str(row[2])


def _normalize_stop_rules(stop_at: Sequence[str]) -> List[str]:
    rules: List[str] = []
    for item in stop_at:
        for part in str(item).split(","):
            s = part.strip()
            if s and s not in rules:
                rules.append(s)
    return rules


def _matches_stop(name: str, module: Optional[str], stop_rules: Sequence[str]) -> bool:
    for rule in stop_rules:
        if rule == "@external":
            if module is None:
                return True
            continue
        if name == rule or name.startswith(rule + "."):
            return True
        if module is not None and (module == rule or module.startswith(rule + ".")):
            return True
    return False


def slice_decl(
    kernel_db_path: str,
    decl: str,
    direction: str = "backward",
    depth: int = 3,
    max_nodes: int = 200,
    edge_kind: str = "both",
    stop_at: Sequence[str] = (),
    tree: str = "ALL",
) -> Dict[str, Any]:
    """Extract a bounded, kernel-exact backward/forward dependency cone around `decl`.

    Always opens `kernel_db_path` read-only (`mode=ro`) with parameterized SQL.
    - `direction`: `backward` (dependencies `src -> dst`), `forward` (dependents `dst -> src`), or `both`.
    - `edge_kind`: `both` / `all` (kinds 1,2,3), `type` (1,3), `value` (2,3),
      `type-only` (1), `value-only` (2), `type+value` (3).
    - `stop_at`: namespace/module prefixes, exact decl names, or `@external` (module IS NULL).
      Boundary nodes matching `stop_at` are included (`stopped: true`) and not expanded further.
    """
    if direction not in ("backward", "forward", "both"):
        raise ValueError(f"invalid direction {direction!r} (expected backward|forward|both)")
    if depth < 0:
        raise ValueError(f"depth must be >= 0, got {depth}")
    if max_nodes < 1:
        raise ValueError(f"max_nodes must be >= 1, got {max_nodes}")
    if edge_kind not in _EDGE_KIND_SETS:
        raise ValueError(f"invalid edge_kind {edge_kind!r}; expected one of {sorted(_EDGE_KIND_SETS)}")

    kinds = _EDGE_KIND_SETS[edge_kind]
    kind_ph = ",".join("?" for _ in kinds)
    stop_rules = _normalize_stop_rules(stop_at)

    conn = _open_kernel_ro(kernel_db_path)
    try:
        center_id, center_name, resolved_from = _resolve_decl_id(conn, decl)
        tree_id, tree_label, tree_view = _resolve_dom_tree(conn, tree)

        meta_cache: Dict[int, Tuple[str, Optional[str]]] = {}

        def get_name_mod(did: int) -> Tuple[str, Optional[str]]:
            hit = meta_cache.get(did)
            if hit is not None:
                return hit
            r = conn.execute(
                "SELECT d.name, m.module FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id WHERE d.id = ?",
                (did,),
            ).fetchone()
            val = (str(r[0]), r[1]) if r is not None else ("", None)
            meta_cache[did] = val
            return val

        get_name_mod(center_id)

        # node_id -> [min_hop, dir_mask (1=back, 2=fwd), stopped]
        visited: Dict[int, List[Any]] = {center_id: [0, 0, False]}
        truncated = False

        def bfs_dir(go_backward: bool, dir_bit: int) -> None:
            nonlocal truncated
            q: collections.deque = collections.deque([(center_id, 0)])
            seen_dir: Set[int] = {center_id}
            sql = (
                f"SELECT dst FROM edges WHERE src = ? AND kind IN ({kind_ph}) ORDER BY dst"
                if go_backward
                else f"SELECT src FROM edges WHERE dst = ? AND kind IN ({kind_ph}) ORDER BY src"
            )
            while q:
                u, h = q.popleft()
                if h >= depth:
                    continue
                if u != center_id and visited[u][2]:
                    continue
                for (nb,) in conn.execute(sql, (u, *kinds)):
                    nb_id = int(nb)
                    if nb_id in seen_dir:
                        continue
                    if nb_id not in visited:
                        if len(visited) >= max_nodes:
                            truncated = True
                            continue
                        nm, mod = get_name_mod(nb_id)
                        st = _matches_stop(nm, mod, stop_rules) if stop_rules else False
                        visited[nb_id] = [h + 1, dir_bit, st]
                    else:
                        if h + 1 < visited[nb_id][0]:
                            visited[nb_id][0] = h + 1
                        visited[nb_id][1] |= dir_bit
                    seen_dir.add(nb_id)
                    if not visited[nb_id][2] and (h + 1) < depth:
                        q.append((nb_id, h + 1))

        if direction in ("backward", "both"):
            bfs_dir(True, 1)
        if direction in ("forward", "both"):
            bfs_dir(False, 2)

        node_ids = sorted(visited.keys())
        node_info: Dict[int, Dict[str, Any]] = {}
        # Fetch full node metadata in parameterized chunks
        chunk_sz = 400
        for i in range(0, len(node_ids), chunk_sz):
            ch = node_ids[i : i + chunk_sz]
            ph = ",".join("?" for _ in ch)
            rows = conn.execute(
                f"SELECT d.id, d.name, d.kind, d.live_mask, d.stmt_mask, d.defcone_mask, d.flags, "
                f"       d.fan_in, d.fan_out, d.fan_out_type, d.fan_out_value, d.sighash, "
                f"       m.module, m.method, dm.depth, dm.subtree_size, dp.name "
                f"FROM decls d "
                f"LEFT JOIN decl_module m ON m.decl_id = d.id "
                f"LEFT JOIN dom dm ON dm.tree_id = ? AND dm.decl_id = d.id "
                f"LEFT JOIN decls dp ON dp.id = dm.idom "
                f"WHERE d.id IN ({ph})",
                (tree_id, *ch),
            ).fetchall()
            for r in rows:
                did = int(r[0])
                hop, dmask, stopped = visited[did]
                if did == center_id:
                    dstr = "center"
                elif dmask == 1:
                    dstr = "backward"
                elif dmask == 2:
                    dstr = "forward"
                else:
                    dstr = "both"
                node_info[did] = {
                    "id": did,
                    "name": r[1],
                    "kind": r[2],
                    "module": r[12],
                    "method": r[13],
                    "hop": hop,
                    "direction": dstr,
                    "stopped": bool(stopped),
                    "live_mask": int(r[3]),
                    "stmt_mask": int(r[4]),
                    "defcone_mask": int(r[5]),
                    "flags": int(r[6]),
                    "flag_names": decode_flags(int(r[6])),
                    "fan_in": int(r[7]),
                    "fan_out": int(r[8]),
                    "fan_out_type": int(r[9]),
                    "fan_out_value": int(r[10]),
                    "sighash": r[11],
                    "dom_depth": None if r[14] is None else int(r[14]),
                    "dom_subtree": None if r[15] is None else int(r[15]),
                    "idom": r[16],
                }

        # Induced edges among `node_ids` matching `edge_kind`
        node_set = set(node_ids)
        edges_out: List[Dict[str, Any]] = []
        for i in range(0, len(node_ids), chunk_sz):
            ch = node_ids[i : i + chunk_sz]
            ph = ",".join("?" for _ in ch)
            for s_id, d_id, ek in conn.execute(
                f"SELECT src, dst, kind FROM edges WHERE src IN ({ph}) AND kind IN ({kind_ph}) ORDER BY src, dst",
                (*ch, *kinds),
            ):
                si, di, eki = int(s_id), int(d_id), int(ek)
                if di in node_set:
                    edges_out.append({
                        "src_id": si,
                        "dst_id": di,
                        "src": node_info[si]["name"],
                        "dst": node_info[di]["name"],
                        "kind": eki,
                        "kind_name": EDGE_KIND_NAMES.get(eki, str(eki)),
                    })

        nodes_sorted = sorted(node_info.values(), key=lambda x: (x["hop"], x["id"]))
        center_obj = dict(node_info[center_id])
        if resolved_from is not None:
            center_obj["resolved_from_const"] = resolved_from
        return {
            "schema": "leanre.kernel.slice/1",
            "provenance": "L",
            "kernel_db": os.path.basename(kernel_db_path),
            "center": center_obj,
            "params": {
                "decl": decl,
                "direction": direction,
                "depth": depth,
                "max_nodes": max_nodes,
                "edge_kind": edge_kind,
                "edge_kind_codes": list(kinds),
                "stop_at": stop_rules,
                "tree": tree_label,
                "tree_view": tree_view,
            },
            "truncated": truncated,
            "node_count": len(nodes_sorted),
            "edge_count": len(edges_out),
            "nodes": nodes_sorted,
            "edges": edges_out,
        }
    finally:
        conn.close()


def format_slice_text(res: Dict[str, Any]) -> str:
    c = res["center"]
    p = res["params"]
    lines = [
        f"[L] kernel slice: {c['name']} ({c['kind']}, id={c['id']}, mod={c['module'] or 'unmatched'})",
        f"    direction={p['direction']} depth={p['depth']} edge_kind={p['edge_kind']} max_nodes={p['max_nodes']}"
        + (f" stop_at={p['stop_at']}" if p["stop_at"] else "")
        + f" -> {res['node_count']} nodes, {res['edge_count']} edges"
        + (" [TRUNCATED]" if res["truncated"] else ""),
    ]
    by_hop: Dict[int, List[Dict[str, Any]]] = collections.defaultdict(list)
    for n in res["nodes"]:
        by_hop[n["hop"]].append(n)
    for hop in sorted(by_hop):
        lines.append(f"  hop {hop} ({len(by_hop[hop])} nodes):")
        for n in by_hop[hop]:
            tags = []
            if n["direction"] != "center":
                tags.append(n["direction"])
            if n["stopped"]:
                tags.append("STOPPED")
            if n["dom_subtree"] is not None:
                tags.append(f"dom={n['dom_subtree']:,}")
            if n["flag_names"]:
                tags.append("flags=" + ",".join(n["flag_names"]))
            mod = n["module"] or (n["method"] or "unmatched")
            lines.append(f"    [{n['kind']:9s}] {n['name']}  ({mod}; {' '.join(tags)})")
    if res["edges"]:
        lines.append(f"  edges ({res['edge_count']}):")
        for e in res["edges"]:
            lines.append(f"    {e['src']} --[{e['kind_name']}]--> {e['dst']}")
    return "\n".join(lines)


def _dot_escape(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")


def format_slice_dot(res: Dict[str, Any]) -> str:
    kind_fill = {
        "thm": "#dbeafe",
        "def": "#dcfce7",
        "inductive": "#fef3c7",
        "axiom": "#fee2e2",
        "opaque": "#f3e8ff",
        "quot": "#e2e8f0",
    }
    edge_style = {
        1: 'color="#2563eb", label="type"',
        2: 'color="#64748b", style="dashed", label="value"',
        3: 'color="#7c3aed", penwidth="1.6", label="both"',
    }
    center_id = res["center"]["id"]
    lines = [
        "digraph kernel_slice {",
        '  rankdir=TB;',
        '  node [fontname="Helvetica", fontsize=10, style="filled", shape=box];',
        '  edge [fontname="Helvetica", fontsize=9];',
    ]
    for n in res["nodes"]:
        nid = f"n{n['id']}"
        lbl = f"{n['name']}\n[{n['kind']} hop={n['hop']}"
        if n["dom_subtree"] is not None:
            lbl += f" dom={n['dom_subtree']}"
        lbl += "]"
        fill = kind_fill.get(n["kind"], "#f8fafc")
        extra = ""
        if n["id"] == center_id:
            extra = ', shape=doubleoctagon, penwidth="2.0"'
        elif n["stopped"]:
            extra = ', style="filled,dashed"'
        lines.append(f'  {nid} [label="{_dot_escape(lbl)}", fillcolor="{fill}"{extra}];')
    for e in res["edges"]:
        st = edge_style.get(e["kind"], 'color="#334155"')
        lines.append(f"  n{e['src_id']} -> n{e['dst_id']} [{st}];")
    lines.append("}")
    return "\n".join(lines)


def inspect_type_deps(
    kernel_db_path: str,
    decl: str,
    tree: str = "ALL",
    limit: int = 50,
) -> Dict[str, Any]:
    """Inspect a declaration's direct type deps, value-only deps, dependents,
    dominator context (idom chain + children), and exact shortest paths to live roots.
    """
    if limit < 0:
        raise ValueError(f"limit must be >= 0, got {limit}")
    conn = _open_kernel_ro(kernel_db_path)
    try:
        did, _name, resolved_from = _resolve_decl_id(conn, decl)
        tree_id, tree_label, tree_view = _resolve_dom_tree(conn, tree)

        drow = conn.execute(
            "SELECT d.id, d.name, d.kind, d.n_consts, d.type_nodes, d.value_nodes, "
            "       d.fan_in, d.fan_out, d.fan_out_type, d.fan_out_value, d.flags, "
            "       d.live_mask, d.stmt_mask, d.defcone_mask, d.attrs, d.sighash, d.sighash_anon, "
            "       m.module, m.method "
            "FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id WHERE d.id = ?",
            (did,),
        ).fetchone()
        assert drow is not None
        consts = [
            {
                "id": int(r[0]),
                "name": r[1],
                "ckind": r[2],
                "ord": int(r[3]),
                "sighash": r[4],
                "sighash_anon": r[5],
                "sig_size": None if r[6] is None else int(r[6]),
                "n_local": None if r[7] is None else int(r[7]),
            }
            for r in conn.execute(
                "SELECT id, name, ckind, ord, sighash, sighash_anon, sig_size, n_local "
                "FROM consts WHERE decl_id = ? ORDER BY ord",
                (did,),
            )
        ]

        decl_obj: Dict[str, Any] = {
            "id": int(drow[0]),
            "name": drow[1],
            "kind": drow[2],
            "n_consts": int(drow[3]),
            "type_nodes": int(drow[4]),
            "value_nodes": int(drow[5]),
            "fan_in": int(drow[6]),
            "fan_out": int(drow[7]),
            "fan_out_type": int(drow[8]),
            "fan_out_value": int(drow[9]),
            "flags": int(drow[10]),
            "flag_names": decode_flags(int(drow[10])),
            "live_mask": int(drow[11]),
            "stmt_mask": int(drow[12]),
            "defcone_mask": int(drow[13]),
            "attrs": int(drow[14]),
            "sighash": drow[15],
            "sighash_anon": drow[16],
            "module": drow[17],
            "module_method": drow[18],
            "consts": consts,
        }
        if resolved_from is not None:
            decl_obj["resolved_from_const"] = resolved_from

        def _fetch_neighbors(sql: str, params: Tuple[Any, ...]) -> Tuple[int, List[Dict[str, Any]]]:
            all_rows = conn.execute(sql, params).fetchall()
            total = len(all_rows)
            shown = all_rows if limit == 0 else all_rows[:limit]
            return total, [
                {
                    "id": int(r[0]),
                    "name": r[1],
                    "kind": r[2],
                    "edge_kind": int(r[3]),
                    "edge_kind_name": EDGE_KIND_NAMES.get(int(r[3]), str(r[3])),
                    "module": r[4],
                    "dom_subtree": None if r[5] is None else int(r[5]),
                    "live_mask": int(r[6]),
                }
                for r in shown
            ]

        type_total, type_deps = _fetch_neighbors(
            "SELECT d.id, d.name, d.kind, e.kind, m.module, dm.subtree_size, d.live_mask "
            "FROM edges e "
            "JOIN decls d ON d.id = e.dst "
            "LEFT JOIN decl_module m ON m.decl_id = d.id "
            "LEFT JOIN dom dm ON dm.tree_id = ? AND dm.decl_id = d.id "
            "WHERE e.src = ? AND e.kind IN (1, 3) "
            "ORDER BY COALESCE(dm.subtree_size, -1) DESC, d.id ASC",
            (tree_id, did),
        )
        val_total, val_deps = _fetch_neighbors(
            "SELECT d.id, d.name, d.kind, e.kind, m.module, dm.subtree_size, d.live_mask "
            "FROM edges e "
            "JOIN decls d ON d.id = e.dst "
            "LEFT JOIN decl_module m ON m.decl_id = d.id "
            "LEFT JOIN dom dm ON dm.tree_id = ? AND dm.decl_id = d.id "
            "WHERE e.src = ? AND e.kind = 2 "
            "ORDER BY COALESCE(dm.subtree_size, -1) DESC, d.id ASC",
            (tree_id, did),
        )
        dep_total = int(drow[6])
        dep_limit_sql = "" if limit == 0 else " LIMIT ?"
        dep_params: Tuple[Any, ...] = (tree_id, did) if limit == 0 else (tree_id, did, limit)
        dependents = [
            {
                "id": int(r[0]),
                "name": r[1],
                "kind": r[2],
                "edge_kind": int(r[3]),
                "edge_kind_name": EDGE_KIND_NAMES.get(int(r[3]), str(r[3])),
                "module": r[4],
                "dom_subtree": None if r[5] is None else int(r[5]),
                "live_mask": int(r[6]),
            }
            for r in conn.execute(
                "SELECT d.id, d.name, d.kind, e.kind, m.module, dm.subtree_size, d.live_mask "
                "FROM edges e "
                "JOIN decls d ON d.id = e.src "
                "LEFT JOIN decl_module m ON m.decl_id = d.id "
                "LEFT JOIN dom dm ON dm.tree_id = ? AND dm.decl_id = d.id "
                "WHERE e.dst = ? "
                "ORDER BY COALESCE(dm.subtree_size, -1) DESC, d.id ASC" + dep_limit_sql,
                dep_params,
            )
        ]

        # Dominator context: idom, chain up to virtual root, and immediate children
        dom_row = conn.execute(
            "SELECT dm.idom, dm.depth, dm.subtree_size, dp.name "
            "FROM dom dm LEFT JOIN decls dp ON dp.id = dm.idom "
            "WHERE dm.tree_id = ? AND dm.decl_id = ?",
            (tree_id, did),
        ).fetchone()
        if dom_row is None:
            dom_obj: Dict[str, Any] = {
                "tree": tree_label,
                "view": tree_view,
                "found": False,
                "idom": None,
                "depth": None,
                "subtree_size": 0,
                "chain_to_root": [],
                "children_total": 0,
                "children": [],
            }
        else:
            chain: List[Dict[str, Any]] = [
                {"id": did, "name": drow[1], "kind": drow[2], "depth": int(dom_row[1]), "subtree_size": int(dom_row[2])}
            ]
            cur = dom_row[0]
            guard = 0
            while cur is not None and guard < 10000:
                up = conn.execute(
                    "SELECT d.id, d.name, d.kind, dm.idom, dm.depth, dm.subtree_size "
                    "FROM dom dm JOIN decls d ON d.id = dm.decl_id "
                    "WHERE dm.tree_id = ? AND dm.decl_id = ?",
                    (tree_id, int(cur)),
                ).fetchone()
                if up is None:
                    break
                chain.append({
                    "id": int(up[0]),
                    "name": up[1],
                    "kind": up[2],
                    "depth": int(up[4]),
                    "subtree_size": int(up[5]),
                })
                cur = up[3]
                guard += 1
            chain.reverse()
            ch_total = int(
                conn.execute("SELECT COUNT(*) FROM dom WHERE tree_id = ? AND idom = ?", (tree_id, did)).fetchone()[0]
            )
            ch_limit_sql = "" if limit == 0 else " LIMIT ?"
            ch_params: Tuple[Any, ...] = (tree_id, did) if limit == 0 else (tree_id, did, limit)
            children = [
                {
                    "id": int(r[0]),
                    "name": r[1],
                    "kind": r[2],
                    "depth": int(r[3]),
                    "subtree_size": int(r[4]),
                    "module": r[5],
                }
                for r in conn.execute(
                    "SELECT d.id, d.name, d.kind, dm.depth, dm.subtree_size, m.module "
                    "FROM dom dm JOIN decls d ON d.id = dm.decl_id "
                    "LEFT JOIN decl_module m ON m.decl_id = d.id "
                    "WHERE dm.tree_id = ? AND dm.idom = ? "
                    "ORDER BY dm.subtree_size DESC, dm.decl_id ASC" + ch_limit_sql,
                    ch_params,
                )
            ]
            dom_obj = {
                "tree": tree_label,
                "view": tree_view,
                "found": True,
                "idom": dom_row[3],
                "depth": int(dom_row[1]),
                "subtree_size": int(dom_row[2]),
                "chain_to_root": chain,
                "children_total": ch_total,
                "children": children,
            }

        # Exact shortest path from each live headline root via `reach` + `edges`
        paths_to_roots: List[Dict[str, Any]] = []
        live_mask = int(drow[11])
        stmt_mask = int(drow[12])
        for rid, rname, rdecl, rgrp in conn.execute("SELECT id, name, decl_id, grp FROM roots ORDER BY id"):
            rid_i, rdecl_i = int(rid), int(rdecl)
            if not (live_mask & (1 << rid_i)):
                continue
            rev_ids: List[int] = []
            cur_id: Optional[int] = did
            seen_p: Set[int] = set()
            while cur_id is not None and cur_id not in seen_p:
                seen_p.add(cur_id)
                rev_ids.append(cur_id)
                if cur_id == rdecl_i:
                    break
                prow = conn.execute(
                    "SELECT parent FROM reach WHERE root_id = ? AND decl_id = ?",
                    (rid_i, cur_id),
                ).fetchone()
                cur_id = None if (prow is None or prow[0] is None) else int(prow[0])
            rev_ids.reverse()
            path_entries: List[Dict[str, Any]] = []
            for hop_idx, pid in enumerate(rev_ids):
                prow2 = conn.execute(
                    "SELECT d.name, d.kind, m.module FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id WHERE d.id = ?",
                    (pid,),
                ).fetchone()
                ek: Optional[int] = None
                if hop_idx > 0:
                    erow = conn.execute(
                        "SELECT kind FROM edges WHERE src = ? AND dst = ?",
                        (rev_ids[hop_idx - 1], pid),
                    ).fetchone()
                    ek = None if erow is None else int(erow[0])
                path_entries.append({
                    "hop": hop_idx,
                    "id": pid,
                    "name": prow2[0] if prow2 else "",
                    "kind": prow2[1] if prow2 else "",
                    "edge_kind": ek,
                    "edge_kind_name": None if ek is None else EDGE_KIND_NAMES.get(ek, str(ek)),
                    "module": prow2[2] if prow2 else None,
                })
            paths_to_roots.append({
                "root_id": rid_i,
                "root_name": rname,
                "group": rgrp,
                "hops": max(0, len(path_entries) - 1),
                "in_stmt_cone": bool(stmt_mask & (1 << rid_i)),
                "path": path_entries,
            })

        return {
            "schema": "leanre.kernel.type_deps/1",
            "provenance": "L",
            "kernel_db": os.path.basename(kernel_db_path),
            "decl": decl_obj,
            "type_deps_total": type_total,
            "type_deps": type_deps,
            "value_only_deps_total": val_total,
            "value_only_deps": val_deps,
            "dependents_total": dep_total,
            "dependents": dependents,
            "dominators": dom_obj,
            "paths_to_roots": paths_to_roots,
        }
    finally:
        conn.close()


def format_type_deps_text(res: Dict[str, Any]) -> str:
    d = res["decl"]
    dom = res["dominators"]
    lines = [
        f"[L] {d['name']}  ({d['kind']}, id={d['id']}, module={d['module'] or d['module_method']})",
        f"    live_mask=0x{d['live_mask']:x} stmt_mask=0x{d['stmt_mask']:x} defcone_mask=0x{d['defcone_mask']:x} "
        f"flags={d['flags']}({','.join(d['flag_names']) or 'none'})",
        f"    fan_in={d['fan_in']:,} fan_out={d['fan_out']:,} (type={d['fan_out_type']:,}, value={d['fan_out_value']:,}) "
        f"expr_nodes=(type={d['type_nodes']:,}, value={d['value_nodes']:,})",
        f"    sighash={d['sighash']}  sighash_anon={d['sighash_anon']}",
    ]
    if dom["found"]:
        chain_s = " -> ".join(f"{c['name']}({c['subtree_size']:,})" for c in dom["chain_to_root"])
        lines.append(f"  Dominators [{dom['tree']}]: idom={dom['idom'] or '<VIRTUAL_ROOT>'} depth={dom['depth']} subtree={dom['subtree_size']:,} children={dom['children_total']:,}")
        lines.append(f"    chain: {chain_s}")
        for ch in dom["children"][:20]:
            lines.append(f"    child [{ch['kind']:9s}] {ch['name']}  (subtree={ch['subtree_size']:,}, mod={ch['module'] or 'unmatched'})")
    else:
        lines.append(f"  Dominators [{dom['tree']}]: unreachable")
    lines.append(f"  Type dependencies ({len(res['type_deps'])}/{res['type_deps_total']}):")
    for x in res["type_deps"]:
        lines.append(f"    --[{x['edge_kind_name']:5s}]--> [{x['kind']:9s}] {x['name']}  (mod={x['module'] or 'unmatched'}, dom={x['dom_subtree']})")
    lines.append(f"  Value-only dependencies ({len(res['value_only_deps'])}/{res['value_only_deps_total']}):")
    for x in res["value_only_deps"]:
        lines.append(f"    --[value]--> [{x['kind']:9s}] {x['name']}  (mod={x['module'] or 'unmatched'}, dom={x['dom_subtree']})")
    lines.append(f"  Direct dependents ({len(res['dependents'])}/{res['dependents_total']}):")
    for x in res["dependents"][:20]:
        lines.append(f"    <--[{x['edge_kind_name']:5s}]-- [{x['kind']:9s}] {x['name']}  (mod={x['module'] or 'unmatched'}, dom={x['dom_subtree']})")
    if res["paths_to_roots"]:
        best = min(res["paths_to_roots"], key=lambda p: (p["hops"], p["root_id"]))
        lines.append(f"  Shortest path to root ({best['root_name']}, {best['hops']} hops; live in {len(res['paths_to_roots'])} roots):")
        for h in best["path"]:
            pre = f"    [{h['hop']:2d}] " + (f"--[{h['edge_kind_name']}]--> " if h["edge_kind_name"] else "ROOT ")
            lines.append(f"{pre}{h['name']} ({h['kind']}, {h['module'] or 'unmatched'})")
    else:
        lines.append("  Shortest path to root: DEAD (unreachable from all roots)")
    return "\n".join(lines)


def register_cli(sub: Any, dest: str = "kernel_func") -> argparse.ArgumentParser:
    """Attach `kernel` subcommand to an argparse subparsers object (for leanre.py wiring)."""
    p = sub.add_parser("kernel", help="Kernel-exact graph extractor (Rust) + taint & module alignment")
    sp = p.add_subparsers(dest="kernel_cmd", required=True)

    p_b = sp.add_parser("build", help="Compile leanre/kernel-rs in release mode")
    p_b.set_defaults(**{dest: _cmd_build})

    p_e = sp.add_parser("extract", help="Stream-extract NDJSON export -> kernel.db + enrichment + report")
    p_e.add_argument("--input", required=True, help="Path to solution.ndjson.zst or challenge.ndjson.zst")
    p_e.add_argument("--out-dir", required=True, help="Output directory for kernel.db and run_stats.json")
    p_e.add_argument("--leanre-db", default=None, help="Phase 2 outputs/leanre.db for alignment & forensic hits")
    p_e.add_argument("--src-dir", default=None, help="Optional data/rh_mirror/src for clean namespace rescan")
    p_e.add_argument("--lexicon", default=None, help="Optional project-local lexicon for k1a")
    p_e.add_argument("--report", default=None, help="Optional path to write compact kernel_report.json")
    p_e.add_argument("--threads", type=int, default=48, help="Rust worker threads (capped at 64)")
    p_e.add_argument("--workers", type=int, default=24, help="Python source-rescan workers")
    p_e.add_argument("--oracle-random", type=int, default=1000)
    p_e.add_argument("--oracle-top", type=int, default=50)
    p_e.add_argument("--root", action="append", default=None, help="Override root NAME[:GROUP] (repeatable)")
    p_e.add_argument("--expect-sha256", default=None)
    p_e.add_argument("--expect-uncompressed-sha256", default=None)
    p_e.set_defaults(**{dest: _cmd_extract})

    p_n = sp.add_parser("enrich", help="Populate decl_module + taint_sources + taint_paths on an existing kernel.db")
    p_n.add_argument("--kernel-db", required=True)
    p_n.add_argument("--run-stats", default=None, help="Path to run_stats.json (defaults next to kernel.db)")
    p_n.add_argument("--leanre-db", default=None)
    p_n.add_argument("--src-dir", default=None)
    p_n.add_argument("--workers", type=int, default=24)
    p_n.add_argument("--report", default=None)
    p_n.set_defaults(**{dest: _cmd_enrich})

    p_k3 = sp.add_parser("verify-k3", help="Verify exact K3 challenge regression against Phase 2 leanre.db")
    p_k3.add_argument("--challenge-db", required=True)
    p_k3.add_argument("--leanre-db", required=True)
    p_k3.add_argument("--challenge-stats", default=None)
    p_k3.add_argument("--ref-sighash-lex-sha", default=None)
    p_k3.add_argument("--ref-sighash-nolex-sha", default=None)
    p_k3.set_defaults(**{dest: _cmd_verify_k3})

    p_v = sp.add_parser("validate-taint", help="Validate every taint_paths edge against stored edges table")
    p_v.add_argument("--kernel-db", required=True)
    p_v.set_defaults(**{dest: _cmd_validate_taint})

    p_sl = sp.add_parser("slice", help="Kernel-exact backward/forward cone slicer around a declaration")
    p_sl.add_argument("decl", help="Exact declaration (or constant) name in kernel.db")
    p_sl.add_argument("--kernel-db", default=default_kernel_db_path(), help="Path to kernel.db (default: outputs/kernel/kernel.db)")
    p_sl.add_argument("--direction", choices=("backward", "forward", "both"), default="backward")
    p_sl.add_argument("--depth", type=int, default=3, help="Max BFS hops from decl (default: 3)")
    p_sl.add_argument("--max-nodes", type=int, default=200, help="Max nodes in slice (default: 200)")
    p_sl.add_argument(
        "--edge-kind",
        choices=("type", "value", "both", "all", "type-only", "value-only", "type+value"),
        default="both",
        help="Edge filter: type (1,3), value (2,3), both/all (1,2,3), type-only (1), value-only (2), type+value (3)",
    )
    p_sl.add_argument("--stop-at", action="append", default=[], help="Stop expanding at prefix/decl or @external (repeatable)")
    p_sl.add_argument("--tree", default="ALL", help="Dominator tree label for node annotations (default: ALL)")
    p_sl.add_argument("--format", choices=("text", "json", "dot"), default=None, help="Output format")
    p_sl.add_argument("--json", action="store_true", help="Emit JSON output (alias for --format json)")
    p_sl.add_argument("--dot", action="store_true", help="Emit Graphviz DOT output (alias for --format dot)")
    p_sl.add_argument("--out", default=None, help="Optional file path to write output")
    p_sl.set_defaults(**{dest: _cmd_slice})

    p_td = sp.add_parser("type-deps", help="Inspect type deps, value-only deps, dom children, and paths-to-root")
    p_td.add_argument("decl", help="Exact declaration (or constant) name in kernel.db")
    p_td.add_argument("--kernel-db", default=default_kernel_db_path(), help="Path to kernel.db (default: outputs/kernel/kernel.db)")
    p_td.add_argument("--tree", default="ALL", help="Dominator tree label (default: ALL)")
    p_td.add_argument("--limit", type=int, default=50, help="Max items per section, 0=unlimited (default: 50)")
    p_td.add_argument("--json", action="store_true", help="Emit JSON output")
    p_td.add_argument("--out", default=None, help="Optional file path to write output")
    p_td.set_defaults(**{dest: _cmd_type_deps})

    return p


def _cmd_build(args: argparse.Namespace) -> int:
    path = build_binary(verbose=True)
    print(path)
    return 0


def _cmd_extract(args: argparse.Namespace) -> int:
    rep = run_pipeline(
        input_path=args.input,
        out_dir=args.out_dir,
        leanre_db=args.leanre_db,
        src_dir=args.src_dir,
        lexicon=args.lexicon,
        report_path=args.report,
        threads=args.threads,
        workers=args.workers,
        oracle_random=args.oracle_random,
        oracle_top=args.oracle_top,
        roots=args.root,
        expect_sha256=args.expect_sha256,
        expect_uncompressed_sha256=args.expect_uncompressed_sha256,
    )
    print(json.dumps({
        "k1_sha256": rep["k1_integrity"]["file_sha256"],
        "k2_records": rep["k2_counts"]["measured_records"],
        "k2_constants": rep["k2_counts"]["measured_constants_unpacked"],
        "k4_union_live": rep["k4_live_dead_and_axioms"]["union"]["live"],
        "k4_union_dead": rep["k4_live_dead_and_axioms"]["union"]["dead"],
        "k5_oracle_failures": rep["k5_dominators_and_taint"]["dominator_oracle_failures_total"],
        "k5_taint_paths": rep["k5_dominators_and_taint"]["taint_summary"]["total_paths"],
        "k6_matched_pct": rep["k6_module_alignment"]["matched_all_pct"],
        "k7_db_sha256": rep["k7_performance_and_determinism"]["kernel_db_sha256"],
    }, indent=2))
    return 0


def _cmd_enrich(args: argparse.Namespace) -> int:
    res = enrich_kernel_db(
        args.kernel_db,
        leanre_db_path=args.leanre_db,
        src_dir=args.src_dir,
        workers=args.workers,
    )
    if args.report:
        st_path = args.run_stats or os.path.join(os.path.dirname(os.path.abspath(args.kernel_db)), "run_stats.json")
        with open(st_path, "r", encoding="utf-8") as f:
            run_stats = json.load(f)
        rep = build_report(run_stats, res, args.kernel_db)
        os.makedirs(os.path.dirname(os.path.abspath(args.report)), exist_ok=True)
        with open(args.report, "w", encoding="utf-8") as f:
            json.dump(rep, f, indent=2, ensure_ascii=False)
            f.write("\n")
    print(json.dumps({"elapsed_s": res["elapsed_s"], "taint_validation": res["taint"]["validation"], "matched_all_pct": res["alignment"]["matched_all_pct"]}, indent=2))
    return 0


def _cmd_verify_k3(args: argparse.Namespace) -> int:
    res = verify_k3_regression(
        args.challenge_db,
        args.leanre_db,
        challenge_stats_path=args.challenge_stats,
        ref_sighash_nolex_sha=args.ref_sighash_nolex_sha,
        ref_sighash_lex_sha=args.ref_sighash_lex_sha,
    )
    print(json.dumps(res, indent=2))
    return 0 if res["all_passed"] else 1


def _cmd_validate_taint(args: argparse.Namespace) -> int:
    conn = sqlite3.connect(f"file:{os.path.abspath(args.kernel_db)}?mode=ro", uri=True)
    try:
        res = validate_taint_paths(conn)
    finally:
        conn.close()
    print(json.dumps(res, indent=2))
    return 0 if res["failures"] == 0 else 1


def _write_or_print(text: str, out_path: Optional[str]) -> None:
    if out_path:
        os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
        with open(out_path, "w", encoding="utf-8") as f:
            f.write(text)
            if not text.endswith("\n"):
                f.write("\n")
    else:
        print(text)


def _cmd_slice(args: argparse.Namespace) -> int:
    fmt = args.format
    if args.dot and args.json:
        print("error: specify at most one of --dot / --json", file=sys.stderr)
        return 2
    if fmt is None:
        fmt = "dot" if args.dot else ("json" if args.json else "text")
    try:
        res = slice_decl(
            kernel_db_path=args.kernel_db,
            decl=args.decl,
            direction=args.direction,
            depth=args.depth,
            max_nodes=args.max_nodes,
            edge_kind=args.edge_kind,
            stop_at=args.stop_at,
            tree=args.tree,
        )
    except (LookupError, ValueError, FileNotFoundError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    if fmt == "json":
        text = json.dumps(res, indent=2, ensure_ascii=False)
    elif fmt == "dot":
        text = format_slice_dot(res)
    else:
        text = format_slice_text(res)
    _write_or_print(text, args.out)
    return 0


def _cmd_type_deps(args: argparse.Namespace) -> int:
    try:
        res = inspect_type_deps(
            kernel_db_path=args.kernel_db,
            decl=args.decl,
            tree=args.tree,
            limit=args.limit,
        )
    except (LookupError, ValueError, FileNotFoundError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    text = json.dumps(res, indent=2, ensure_ascii=False) if args.json else format_type_deps_text(res)
    _write_or_print(text, args.out)
    return 0


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(prog="leanre-kernel", description="Kernel-exact graph pipeline")
    sub = ap.add_subparsers(dest="top", required=True)
    register_cli(sub, dest="kernel_func")
    # Also allow running subcommands directly without repeating `kernel`
    argv_list = list(sys.argv[1:] if argv is None else argv)
    if argv_list and argv_list[0] not in ("kernel", "-h", "--help"):
        argv_list = ["kernel"] + argv_list
    args = ap.parse_args(argv_list)
    return int(args.kernel_func(args))


if __name__ == "__main__":
    sys.exit(main())
