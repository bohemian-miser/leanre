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
import array
import bisect
import collections
import hashlib
import json
import multiprocessing
import os
import re
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

_RH_SPECIFIC_TAINT_CLASSES = frozenset({
    "CutCptCopy",
    "kexactB",
    "kcopy",
    "slow_con_leche",
    "lean4lean_timeout",
    "addDecl",
})


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


def _scan_enclosing_spans(text: str) -> List[Tuple[int, str, Optional[str]]]:
    """Scan a Lean file into sorted `(line_no, kind, qualified_name_or_None)` spans.

    Tracks `namespace`/`section`/`mutual`/`end` scoping (including multi-component
    `end A.B` and `_root_.`) AND explicitly records anonymous `example` blocks with
    `name=None` so lines inside an `example ... := by` block are NEVER falsely
    attributed to a preceding named `theorem`/`lemma`/`def`.
    """
    import sighash  # sibling module

    lines = sighash.strip_comments(text).split("\n")
    scopes: List[Tuple[str, str]] = [("file", "")]
    spans: List[Tuple[int, str, Optional[str]]] = []
    re_cmd = sighash._RE_CMD
    re_ident = sighash._RE_IDENT
    keywords = sighash._KEYWORDS
    decl_kinds = frozenset({
        "theorem", "lemma", "def", "abbrev", "structure", "class",
        "instance", "inductive", "opaque", "axiom", "alias",
    })
    re_indented_example = re.compile(
        r"^\s+(?:@\[[^\]]*\]\s*)*"
        r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local|public|meta)\s+)*"
        r"example\b"
    )
    for idx, ln in enumerate(lines):
        line_no = idx + 1
        if not ln:
            continue
        if ln[0].isspace():
            if re_indented_example.match(ln):
                spans.append((line_no, "example", None))
            continue
        m = re_cmd.match(ln)
        if m is None:
            continue
        cmd = m.group(1)
        rest = ln[m.end():].strip()
        if cmd == "namespace":
            scopes.append(("ns", rest.split()[0] if rest else ""))
        elif cmd == "section":
            scopes.append(("sec", rest.split()[0] if rest else ""))
        elif cmd == "mutual":
            scopes.append(("mutual", ""))
        elif cmd == "end":
            want = len(rest.split()[0].split(".")) if rest else 1
            got = 0
            while len(scopes) > 1 and got < want:
                _sk, sname = scopes.pop()
                got += max(1, len(sname.split("."))) if sname else 1
            spans.append((line_no, "end", None))
        elif cmd == "example":
            spans.append((line_no, "example", None))
        elif cmd in decl_kinds:
            r2 = rest
            if cmd == "class" and r2.startswith(("inductive ", "abbrev ")):
                r2 = r2.split(None, 1)[1]
            if cmd == "instance" and r2.startswith("("):
                # Skip optional `(priority := ...)` before instance name
                close_i = r2.find(")")
                if close_i >= 0:
                    r2 = r2[close_i + 1:].strip()
            m2 = re_ident.match(r2)
            raw_name = m2.group(0) if m2 else ""
            if raw_name in keywords:
                raw_name = ""
            if raw_name:
                ns = ".".join(sn for sk, sn in scopes if sk == "ns" and sn)
                if raw_name.startswith("_root_."):
                    full = raw_name[7:]
                else:
                    full = f"{ns}.{raw_name}" if ns else raw_name
                spans.append((line_no, cmd, full))
            else:
                spans.append((line_no, cmd, None))
    return spans


def resolve_enclosing_source_decl(
    src_dir: str,
    module: str,
    line_no: int,
    span_cache: Optional[Dict[str, Tuple[List[int], List[Tuple[int, str, Optional[str]]]]]] = None,
) -> Optional[Tuple[str, Optional[str]]]:
    """Return `(enclosing_kind, qualified_name_or_None)` for `(module, line_no)` under `src_dir`.

    Returns `("example", None)` when `line_no` lies inside an anonymous `example` block,
    `(kind, qualified_name)` when inside a named declaration, or `None` if source file
    cannot be resolved.
    """
    if not src_dir or not module or line_no <= 0:
        return None
    cache = span_cache if span_cache is not None else {}
    cached = cache.get(module)
    if cached is None:
        rel = module.replace(".", os.sep) + ".lean"
        fpath, _err = _safe_resolve_src_path(src_dir, rel)
        if fpath is None:
            cache[module] = ([], [])
            return None
        try:
            with open(fpath, "r", encoding="utf-8", errors="replace") as f:
                spans = _scan_enclosing_spans(f.read())
        except OSError:
            cache[module] = ([], [])
            return None
        cached = ([s[0] for s in spans], spans)
        cache[module] = cached
    starts, spans = cached
    if not starts:
        return None
    pos = bisect.bisect_right(starts, line_no) - 1
    if pos < 0:
        return None
    _ln, kind, qname = spans[pos]
    return (kind, qname)


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
        lconn = sqlite3.connect(f"file:{os.path.realpath(leanre_db_path)}?mode=ro", uri=True)
        lconn.execute("PRAGMA query_only=1")
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
                decl_id INTEGER,
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
        # Deduplicated by (class, decl_id) for named decls, plus explicit
        # (class, module, line_no) rows with decl_id=NULL for anonymous `example` blocks.
        sources_map: Dict[Tuple[str, int], Tuple[str, Optional[str], Optional[int], str]] = {}
        anon_sources_map: Dict[Tuple[str, str, int], Tuple[str, Optional[str], Optional[int], str]] = {}
        unmapped_forensic: collections.Counter = collections.Counter()
        unmapped_forensic_examples: Dict[str, List[str]] = collections.defaultdict(list)
        forensic_hit_counts: Dict[Tuple[str, int], int] = collections.Counter()

        # Index `._proof_*` auxiliaries by parent decl name (captures `._proof_1_1`, `._proof_1_2`, ...)
        proof_aux_by_parent: Dict[str, List[int]] = collections.defaultdict(list)
        mod_to_decl_ids: Dict[str, List[int]] = collections.defaultdict(list)
        for did, nm, _k, _f, _lm in decls_rows:
            if "._proof_" in nm:
                proof_aux_by_parent[nm.split("._proof_", 1)[0]].append(did)
            dmod = decl_to_module.get(did)
            if dmod is not None:
                mod_to_decl_ids[dmod].append(did)
        enclosing_span_cache: Dict[str, Tuple[List[int], List[Tuple[int, str, Optional[str]]]]] = {}

        # 1. Source-level forensic hits from leanre.db
        for tag, mod, ln, dnm in forensic_hits_raw:
            did_hit: Optional[int] = None
            resolved_by = ""
            enclosing_nm: Optional[str] = None
            if src_dir and os.path.isdir(src_dir) and mod and ln > 0:
                enc = resolve_enclosing_source_decl(src_dir, mod, ln, enclosing_span_cache)
                if enc is not None:
                    enc_kind, enc_qname = enc
                    if enc_kind == "example":
                        # Anonymous `example ... := by` block: record explicitly with decl_id=NULL
                        # instead of falsely attributing to a preceding theorem/lemma/def.
                        akey = (tag, mod, ln)
                        if akey not in anon_sources_map:
                            anon_sources_map[akey] = (
                                "source-hit:anonymous_example",
                                mod,
                                ln,
                                f"anonymous example tag={tag} at {mod}:{ln}",
                            )
                        continue
                    if enc_kind == "end":
                        unmapped_forensic[tag] += 1
                        if len(unmapped_forensic_examples[tag]) < 10:
                            unmapped_forensic_examples[tag].append(f"{mod}:{ln}:<after-end>")
                        continue
                    if enc_qname:
                        enclosing_nm = enc_qname

            cands: List[str] = []
            if enclosing_nm:
                cands.append(enclosing_nm)
            if dnm:
                if dnm not in cands:
                    cands.append(dnm)
                if dnm.startswith("_root_.") and dnm[7:] not in cands:
                    cands.append(dnm[7:])
            rescan_nm = src_by_mod_line.get((mod, ln))
            if rescan_nm and rescan_nm not in cands:
                cands.append(rescan_nm)

            for idx_c, c in enumerate(cands):
                if c in name_to_decl_id:
                    did_hit = name_to_decl_id[c]
                    resolved_by = "enclosing_rescan" if (enclosing_nm and c == enclosing_nm and c != dnm) else ("exact" if dnm else "line_rescan")
                    break
                priv = f"_private.{mod}.0.{c}"
                if priv in name_to_decl_id:
                    did_hit = name_to_decl_id[priv]
                    resolved_by = "private"
                    break

            # Fallback for bare declaration names (e.g. `discr_of_cyclic` in leanre.db) within `mod`
            if did_hit is None and dnm and "." not in dnm and mod in mod_to_decl_ids:
                suffix = "." + dnm
                mod_matches = [
                    mdid for mdid in mod_to_decl_ids[mod]
                    if decl_id_to_name[mdid].endswith(suffix)
                    and not decl_id_to_name[mdid].startswith("_private.")
                ]
                if len(mod_matches) == 1:
                    did_hit = mod_matches[0]
                    resolved_by = "module_suffix"

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
            # `by decide +kernel` into compiler-generated `._proof_1_*` / `._proof_1` auxiliaries
            # holding the actual `Eq.refl Bool true` / `of_decide_eq_true` kernel reduction.
            if tag in ("lean4lean_timeout", "slow_con_leche", "decide_kernel"):
                outer_nm = decl_id_to_name[did_hit]
                for aux_did in proof_aux_by_parent.get(outer_nm, ()):
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

        # Deterministic ordering of taint_sources (named decls first, then anonymous examples)
        ordered_sources = sorted(sources_map.items(), key=lambda kv: (kv[0][0], kv[0][1]))
        ordered_anon = sorted(anon_sources_map.items(), key=lambda kv: (kv[0][0], kv[0][1], kv[0][2]))
        source_rows: List[Tuple[int, str, Optional[int], str, Optional[str], Optional[int], str]] = []
        sid_cur = 1
        for (cls, did), (origin, mod, ln, detail) in ordered_sources:
            source_rows.append((sid_cur, cls, did, origin, mod, ln, detail))
            sid_cur += 1
        for (cls, _amod, _aln), (origin, mod, ln, detail) in ordered_anon:
            source_rows.append((sid_cur, cls, None, origin, mod, ln, detail))
            sid_cur += 1

        # Reconstruct shortest paths from each root to each reachable taint source using `reach`
        # Load `reach` only for needed walks? Loading per-root parent dict in memory for 1.47M decls
        # would be ~50MB per root; doing one root at a time keeps memory tiny (~60MB) and is super fast!
        path_rows: List[Tuple[int, int, int, int, Optional[int]]] = []
        edge_pairs_needed: Set[Tuple[int, int]] = set()
        raw_paths: List[Tuple[int, int, List[int]]] = []

        live_sources_by_root: Dict[int, List[Tuple[int, int]]] = collections.defaultdict(list)
        for sid, _cls, did, _orig, _mod, _ln, _det in source_rows:
            if did is None:
                continue
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
            did_s = "" if row[2] is None else str(row[2])
            h_ts.update(f"{row[0]}\t{row[1]}\t{did_s}\t{row[3]}\t{row[4] or ''}\t{'' if row[5] is None else row[5]}\t{row[6]}\n".encode("utf-8"))
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
        cls_live_sources = collections.Counter(
            r[1] for r in source_rows if r[2] is not None and decl_id_to_live.get(r[2], 0) != 0
        )
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

        lean4lean_timeout_audit: Dict[str, Any] = {
            "total_timeout_modules": len(timeout_entries),
            "live_timeout_modules": sum(1 for e in timeout_entries if e["module_live_decls_count"] > 0),
            "dead_timeout_modules": sum(1 for e in timeout_entries if e["module_live_decls_count"] == 0),
            "live_decls_across_timeout_modules": sum(e["module_live_decls_count"] for e in timeout_entries),
            "modules": timeout_entries,
        }
        dyadic_smallloop = "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.SmallLoop"
        if dyadic_smallloop in project_modules:
            lean4lean_timeout_audit["dyadic_smallloop_disambiguation"] = {
                "module": dyadic_smallloop,
                "in_leanre_db": True,
                "kernel_live_decls_count": len(mod_to_live_decls.get(dyadic_smallloop, [])),
                "note": "Distinct from ChebyshevPrimeBounds.SmallLoop (whose 9 kernel decls are all live).",
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
    sources = {
        int(r[0]): (None if r[1] is None else int(r[1]))
        for r in conn.execute("SELECT id, decl_id FROM taint_sources")
    }
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
    k = _open_kernel_ro(challenge_db)
    p = _open_kernel_ro(leanre_db)
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


def _discover_extract_config(
    input_path: str,
    src_dir: Optional[str] = None,
    config: Optional[Any] = None,
) -> Any:
    """Load `leanre.toml` from `--config` or auto-discover relative to `src_dir`/`input_path`/cwd.

    Never auto-picks the leanre tool repository's own RH `leanre.toml` when extracting
    a separate/generic repository unless `input_path` or `src_dir` lives under its tree.
    """
    try:
        import config as config_mod
    except ImportError:  # pragma: no cover - package import fallback
        from leanre import config as config_mod

    if config is not None:
        return config_mod.coerce_config(config)

    repo_toml = os.path.realpath(os.path.join(_REPO_ROOT, config_mod.DEFAULT_CONFIG_FILENAME))
    rh_mirror_dir = os.path.realpath(os.path.join(_REPO_ROOT, "data", "rh_mirror"))
    in_real = os.path.realpath(input_path)
    src_real = os.path.realpath(src_dir) if src_dir else ""
    allow_repo_toml = (
        (in_real == rh_mirror_dir or in_real.startswith(rh_mirror_dir + os.sep))
        or (src_real != "" and (src_real == rh_mirror_dir or src_real.startswith(rh_mirror_dir + os.sep)))
    )

    starts: List[str] = []
    if src_dir:
        starts.append(src_dir)
    starts.append(os.path.dirname(os.path.abspath(input_path)))
    starts.append(os.getcwd())

    for st in starts:
        found = config_mod.find_config(start_dir=st)
        if found is None:
            continue
        if os.path.realpath(str(found)) == repo_toml and not allow_repo_toml:
            continue
        return config_mod.load_config(str(found))
    return config_mod.LeanreConfig.empty()


def build_report(
    run_stats: Dict[str, Any],
    enrich_res: Dict[str, Any],
    kernel_db_path: str,
    k3_result: Optional[Dict[str, Any]] = None,
    determinism: Optional[Dict[str, Any]] = None,
    include_rh_reference: Optional[bool] = None,
) -> Dict[str, Any]:
    """Assemble the compact, git-committable `outputs/kernel_report.json` (K1-K7 receipts)."""
    conn = _open_kernel_ro(kernel_db_path)
    try:
        sample_paths = extract_sample_taint_paths(conn, per_class=3)
    finally:
        conn.close()

    db_bytes, db_sha = _file_sha256(kernel_db_path)
    inp = run_stats["input"]
    decls = run_stats["declarations"]
    is_solution = (inp.get("file_sha256") == EXPECTED_SOLUTION_SHA256)
    has_rh_root = any(r.get("name") == "riemannHypothesis" for r in (run_stats.get("roots") or []))
    is_rh = (is_solution or has_rh_root) if include_rh_reference is None else bool(include_rh_reference)

    k1: Dict[str, Any] = {
        "provenance": "L",
        "file_bytes": inp["file_bytes"],
        "file_sha256": inp["file_sha256"],
        "uncompressed_bytes": inp["uncompressed_bytes"],
        "uncompressed_sha256": inp["uncompressed_sha256"],
    }
    if is_rh:
        k1["matches_expected_solution"] = (
            inp["file_bytes"] == EXPECTED_SOLUTION_BYTES
            and inp["file_sha256"] == EXPECTED_SOLUTION_SHA256
            and inp["uncompressed_bytes"] == EXPECTED_SOLUTION_UNCOMPRESSED_BYTES
            and inp["uncompressed_sha256"] == EXPECTED_SOLUTION_UNCOMPRESSED_SHA256
        )

    n_rec = decls["records"]
    n_const = decls["constants_unpacked"]
    ind = decls["inductive"]
    reconciliation: Dict[str, Any] = {
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
    }
    if is_rh:
        reconciliation = {
            "con_leche_reference": 1_468_418,
            "con_leche_delta_vs_records": n_rec - 1_468_418,
            "nanoda_reference_nasqret": 1_484_733,
            "nanoda_delta_vs_constants": n_const - 1_484_733,
            **reconciliation,
        }

    k2 = {
        "provenance": "L",
        "counting_rules": {
            "declaration_records": (
                "1 per top-level declaration JSON record in the NDJSON stream "
                "(thm + def + opaque + axiom + quot + inductive; each inductive record folds its types, ctors, and recursors)."
                + (" Matches con-leche fold-record counting." if is_rh else "")
            ),
            "constants_unpacked": (
                "1 per kernel constant added to the environment: "
                "thm + def + opaque + axiom + quot + inductive.types + inductive.ctors + inductive.recs."
                + (" Matches nanoda constant-level counting." if is_rh else "")
            ),
        },
        "measured_records": n_rec,
        "measured_constants_unpacked": n_const,
        "by_kind": decls["by_kind"],
        "inductive_breakdown": ind,
        "unpacked_minus_records": n_const - n_rec,
        "reconciliation": reconciliation,
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

    taint_summary_out = dict(enrich_res["taint"])
    if not is_rh and isinstance(taint_summary_out.get("by_class"), dict):
        taint_summary_out["by_class"] = {
            k: v
            for k, v in taint_summary_out["by_class"].items()
            if k not in _RH_SPECIFIC_TAINT_CLASSES or (v.get("sources", 0) > 0)
        }

    lean_ver = ((run_stats.get("export_meta") or {}).get("lean") or {}).get("version") or "4"
    rep: Dict[str, Any] = {
        "schema_version": run_stats["tool"]["schema_version"],
        "provenance": "L",
        "epistemic_note": (
            f"Layer 1/2/3 instrumentation only: kernel graph & axiom extraction records what the "
            f"Lean {lean_ver} export contains (Layer 1 syntactic DAG / Layer 2 TCB visibility); it is "
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
            "taint_summary": taint_summary_out,
            "lean4lean_timeout_audit": taint_summary_out.get("lean4lean_timeout_audit"),
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
    }
    if is_rh:
        rep["is_full_solution"] = is_solution
    return rep


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
    config: Optional[Any] = None,
    rh_reference: Optional[bool] = None,
) -> Dict[str, Any]:
    """End-to-end atomic build of `<out_dir>/kernel.db` + optional `kernel_report.json`."""
    bin_path = binary_path or default_binary_path()
    if not os.path.exists(bin_path):
        if auto_build:
            bin_path = build_binary(verbose=verbose)
        else:
            raise FileNotFoundError(f"leanre-kernel binary not found at {bin_path}")

    cfg = _discover_extract_config(input_path, src_dir=src_dir, config=config)
    if roots is None and getattr(cfg, "source_path", None):
        cfg_roots = cfg.kernel_root_specs()
        if cfg_roots:
            roots = cfg_roots
            if verbose:
                print(f"[kernel] loaded {len(roots)} root(s) from {cfg.source_path}", file=sys.stderr)
    if src_dir is None and getattr(cfg, "source_path", None):
        cand_src = cfg.resolve_src_dir()
        if cand_src and os.path.isdir(cand_src):
            src_dir = cand_src
    if rh_reference is None and getattr(cfg, "source_path", None) and getattr(cfg, "rh_gates", False):
        rh_reference = True

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
        include_rh_reference=rh_reference,
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


def default_src_root() -> str:
    return os.path.join(_REPO_ROOT, "data", "rh_mirror", "src")


STANDARD_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})

_DIRECTION_ALIASES: Dict[str, str] = {
    "backward": "backward",
    "bwd": "backward",
    "forward": "forward",
    "fwd": "forward",
    "both": "both",
}

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
    real = os.path.realpath(kernel_db_path)
    if not os.path.isfile(real):
        raise FileNotFoundError(f"kernel DB not found: {kernel_db_path}")
    conn = sqlite3.connect(f"file:{real}?mode=ro", uri=True)
    conn.execute("PRAGMA query_only=1")
    return conn


def _has_table(conn: sqlite3.Connection, table_name: str) -> bool:
    row = conn.execute(
        "SELECT 1 FROM sqlite_master WHERE type IN ('table', 'view') AND name = ?",
        (table_name,),
    ).fetchone()
    return row is not None


def _has_decl_module_rows(conn: sqlite3.Connection) -> bool:
    if not _has_table(conn, "decl_module"):
        return False
    row = conn.execute("SELECT 1 FROM decl_module LIMIT 1").fetchone()
    return row is not None


def _is_project_decl(
    name: str,
    module: Optional[str],
    method: Optional[str],
    has_dm_rows: bool,
) -> bool:
    """Return True iff the declaration belongs to the project (not Mathlib/Init/Std/Lean)."""
    if has_dm_rows:
        if method == "unmatched:no_source_index":
            pass
        else:
            return (module is not None) or (bool(method) and method.startswith("unmatched:project"))
    if name.startswith("_private."):
        parts = name.split(".")
        if len(parts) > 1 and parts[1] in _STDLIB_TOP_PREFIXES:
            return False
        return True
    if "._@." in name:
        after = name.split("._@.", 1)[1].split(".", 1)[0]
        if after in _STDLIB_TOP_PREFIXES:
            return False
    top = name.split(".", 1)[0]
    return top not in _STDLIB_TOP_PREFIXES


def _chunks(seq: Sequence[int], size: int = 900) -> Iterable[Sequence[int]]:
    for i in range(0, len(seq), size):
        yield seq[i : i + size]


def _escape_like(s: str) -> str:
    return s.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")


def _escape_glob(s: str) -> str:
    return re.sub(r"([*?\[])", r"[\1]", s)


def _rel_display_path(path: str, base_dir: Optional[str] = None) -> str:
    """Return a clean relative path without leaking absolute host/home directories."""
    ap = os.path.abspath(path)
    if base_dir:
        try:
            rel = os.path.relpath(ap, os.path.abspath(base_dir))
            if not rel.startswith(".."):
                return rel.replace(os.sep, "/")
        except ValueError:
            pass
    try:
        rel = os.path.relpath(ap, _REPO_ROOT)
        if not rel.startswith(".."):
            return rel.replace(os.sep, "/")
    except ValueError:
        pass
    return os.path.basename(ap)


def _safe_resolve_src_path(src_root: str, rel_path: str) -> Tuple[Optional[str], Optional[str]]:
    """Symlink-safe resolution of `rel_path` strictly inside `src_root`.

    Returns `(resolved_abs_path, None)` on success, or `(None, error_code)` where
    `error_code` is one of `src_root_missing`, `unsafe_path`, `symlink_escape`,
    `file_not_found`.
    """
    if not src_root:
        return None, "src_root_missing"
    real_root = os.path.realpath(src_root)
    if not os.path.isdir(real_root):
        return None, "src_root_missing"
    if not rel_path or "\x00" in rel_path:
        return None, "unsafe_path"
    norm = rel_path.replace("\\", "/").strip()
    if norm.startswith("/") or re.match(r"^[A-Za-z]:", norm):
        return None, "unsafe_path"
    raw_parts = [p for p in norm.split("/") if p]
    if not raw_parts or any(p in (".", "..") for p in raw_parts):
        return None, "unsafe_path"

    # Support both `src/Foo/Bar.lean` and `Foo/Bar.lean` regardless of whether `src_root`
    # points to `<repo>/src` or `<repo>`.
    candidate_rel_lists: List[List[str]] = [raw_parts]
    if raw_parts[0] == "src" and len(raw_parts) > 1 and os.path.basename(real_root) == "src":
        candidate_rel_lists.append(raw_parts[1:])
    elif raw_parts[0] != "src" and os.path.isdir(os.path.join(real_root, "src")):
        candidate_rel_lists.append(["src", *raw_parts])

    saw_symlink_escape = False
    for parts in candidate_rel_lists:
        cur = real_root
        escaped = False
        missing = False
        for seg in parts:
            nxt = os.path.join(cur, seg)
            if os.path.islink(nxt):
                target_real = os.path.realpath(nxt)
                try:
                    in_root = os.path.commonpath([real_root, target_real]) == real_root
                except ValueError:
                    in_root = False
                # Refuse symlinks inside src_root (escaping or otherwise untrusted)
                saw_symlink_escape = True
                escaped = True
                if not in_root:
                    return None, "symlink_escape"
                break
            if not os.path.lexists(nxt):
                missing = True
                break
            cur = nxt
        if escaped or missing:
            continue
        real_cand = os.path.realpath(cur)
        try:
            if os.path.commonpath([real_root, real_cand]) != real_root:
                return None, "symlink_escape"
        except ValueError:
            return None, "symlink_escape"
        if os.path.isfile(real_cand):
            return real_cand, None
    if saw_symlink_escape:
        return None, "symlink_escape"
    return None, "file_not_found"


def _resolve_decl_id(
    conn: sqlite3.Connection,
    decl: str,
    *,
    allow_suffix: bool = True,
    allow_const_folding: bool = True,
) -> Tuple[int, str, Optional[str]]:
    """Resolve `decl` by exact-case exact match -> module-prefixed -> exact-case suffix
    -> partially-qualified `Prefix.*.Leaf` -> case-insensitive fallback.

    When `allow_const_folding=False` (e.g. `kernel callers`), folded constructors/recursors
    in `consts` are NOT silently mapped to their parent inductive; instead an explicit
    diagnostic `LookupError` is raised if found in `consts` without a standalone `decls` row.
    Never raises raw `KeyError`; raises `LookupError` with candidate suggestions on miss/ambiguity.
    Returns `(decl_id, primary_name, resolved_from_or_None)`.
    """
    q = decl.strip()
    if not q:
        raise LookupError("empty declaration query")

    def _exact(name: str) -> Optional[Tuple[int, str, Optional[str]]]:
        row = conn.execute("SELECT id, name FROM decls WHERE name = ?", (name,)).fetchone()
        if row is not None:
            return int(row[0]), str(row[1]), (None if name == q else q)
        if allow_const_folding and _has_table(conn, "consts"):
            crow = conn.execute(
                "SELECT c.decl_id, d.name FROM consts c JOIN decls d ON d.id = c.decl_id WHERE c.name = ?",
                (name,),
            ).fetchone()
            if crow is not None:
                return int(crow[0]), str(crow[1]), q
        return None

    hit = _exact(q)
    if hit is not None:
        return hit
    if q.startswith("_root_."):
        hit = _exact(q[7:])
        if hit is not None:
            return hit

    has_dm = _has_decl_module_rows(conn)

    # Module-prefixed form, e.g. `Main.riemannHypothesis` where `riemannHypothesis` lives in module `Main`
    if "." in q and has_dm:
        parts = q.split(".")
        for split_idx in range(len(parts) - 1, 0, -1):
            mod_cand = ".".join(parts[:split_idx])
            tail_cand = ".".join(parts[split_idx:])
            rows = conn.execute(
                "SELECT d.id, d.name FROM decls d "
                "JOIN decl_module m ON m.decl_id = d.id "
                "WHERE d.name = ? AND (m.module = ? OR m.module LIKE ? ESCAPE '\\') "
                "ORDER BY d.id LIMIT 5",
                (tail_cand, mod_cand, f"%.{_escape_like(mod_cand)}"),
            ).fetchall()
            if len(rows) == 1:
                return int(rows[0][0]), str(rows[0][1]), q

    def _pick_or_raise(cands: Sequence[Tuple[Any, ...]], label: str) -> Optional[Tuple[int, str, Optional[str]]]:
        if not cands:
            return None
        if len(cands) == 1:
            return int(cands[0][0]), str(cands[0][1]), q
        pub = [c for c in cands if not str(c[1]).startswith("_private.")]
        if len(pub) == 1:
            return int(pub[0][0]), str(pub[0][1]), q
        ranked = sorted(
            pub or cands,
            key=lambda c: (
                0 if _is_project_decl(str(c[1]), c[2], c[3], has_dm) else 1,
                1 if "._proof_" in str(c[1]) else 0,
                len(str(c[1])),
                str(c[1]),
            ),
        )
        sample = ", ".join(str(c[1]) for c in ranked[:8])
        more = f" (+{len(cands) - 8} more)" if len(cands) > 8 else ""
        raise LookupError(f"ambiguous {label} {q!r} ({len(cands)} matches): {sample}{more}")

    def _query_cands(where_sql: str, params: Tuple[Any, ...]) -> List[Tuple[Any, ...]]:
        if has_dm:
            return conn.execute(
                "SELECT d.id, d.name, m.module, m.method FROM decls d "
                "LEFT JOIN decl_module m ON m.decl_id = d.id "
                f"WHERE {where_sql} ORDER BY d.id LIMIT 200",
                params,
            ).fetchall()
        return [
            (r[0], r[1], None, None)
            for r in conn.execute(
                f"SELECT id, name FROM decls WHERE {where_sql} ORDER BY id LIMIT 200",
                params,
            ).fetchall()
        ]

    if allow_suffix:
        q_clean = q[7:] if q.startswith("_root_.") else q
        glob_esc = _escape_glob(q_clean)
        # 1. Exact-case suffix match (so `theorem zFRDirichlet : ZFRDirichlet` never collides!)
        exact_case_cands = _query_cands("d.name GLOB ?", (f"*.{glob_esc}",))
        picked = _pick_or_raise(exact_case_cands, "declaration suffix")
        if picked is not None:
            return picked

        # 2. Partially-qualified `Prefix.Leaf` match -> `Prefix.*.Leaf` (exact case)
        if "." in q_clean:
            pfx, leaf = q_clean.rsplit(".", 1)
            if pfx and leaf:
                epfx, eleaf = _escape_glob(pfx), _escape_glob(leaf)
                gap_cands = _query_cands(
                    "(d.name GLOB ? OR d.name GLOB ?)",
                    (f"{epfx}.*.{eleaf}", f"*.{epfx}.*.{eleaf}"),
                )
                picked = _pick_or_raise(gap_cands, "partially-qualified declaration")
                if picked is not None:
                    return picked

        # 3. Case-insensitive fallback (exact then suffix) only when exact-case found nothing
        nocase_exact = _query_cands("d.name = ? COLLATE NOCASE", (q_clean,))
        picked = _pick_or_raise(nocase_exact, "declaration (case-insensitive)")
        if picked is not None:
            return picked

        like_pat = f"%.{_escape_like(q_clean)}"
        nocase_cands = _query_cands("d.name LIKE ? ESCAPE '\\'", (like_pat,))
        picked = _pick_or_raise(nocase_cands, "declaration suffix")
        if picked is not None:
            return picked

    # When const folding is disabled (e.g. `kernel callers`), report folded constructor/recursor
    # constants explicitly instead of silently returning the parent inductive's edges.
    if not allow_const_folding and _has_table(conn, "consts"):
        q_clean = q[7:] if q.startswith("_root_.") else q
        crows = conn.execute(
            "SELECT c.name, c.ckind, d.name FROM consts c JOIN decls d ON d.id = c.decl_id WHERE c.name = ? LIMIT 5",
            (q_clean,),
        ).fetchall()
        if not crows and allow_suffix:
            crows = conn.execute(
                "SELECT c.name, c.ckind, d.name FROM consts c JOIN decls d ON d.id = c.decl_id "
                "WHERE c.name GLOB ? ORDER BY length(c.name), c.name LIMIT 10",
                (f"*.{_escape_glob(q_clean)}",),
            ).fetchall()
        if len(crows) == 1:
            cname, ckind, parent_nm = str(crows[0][0]), str(crows[0][1]), str(crows[0][2])
            raise LookupError(
                f"{ckind} constant {cname!r} is folded into {parent_nm!r} in kernel.db "
                f"(edges are per-declaration and cannot isolate `{cname}`; "
                f"use `leanre bundles --instantiations {parent_nm}` or query {parent_nm!r} directly)"
            )
        if len(crows) > 1:
            sample = ", ".join(f"{r[0]} (->{r[2]})" for r in crows[:6])
            raise LookupError(f"folded constant {q!r} matches multiple parent declarations: {sample}")

    # Helpful near-miss candidates on last dot-component when query had a guessed namespace
    hint = ""
    if "." in q:
        leaf = q.rsplit(".", 1)[-1]
        if len(leaf) >= 3:
            near = conn.execute(
                "SELECT name FROM decls WHERE name = ? OR name LIKE ? ESCAPE '\\' "
                "ORDER BY length(name), name LIMIT 10",
                (leaf, f"%.{_escape_like(leaf)}"),
            ).fetchall()
            if near:
                hint = " (candidates: " + ", ".join(str(r[0]) for r in near[:8]) + ")"
    raise LookupError(f"declaration not found in kernel.db: {decl}{hint}")


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
    project_only: bool = False,
) -> Dict[str, Any]:
    """Extract a bounded, kernel-exact backward/forward dependency cone around `decl`.

    Always opens `kernel_db_path` read-only (`mode=ro` + `PRAGMA query_only=1`) with parameterized SQL.
    - `direction`: `backward`/`bwd` (dependencies `src -> dst`), `forward`/`fwd` (dependents `dst -> src`), or `both`.
    - `edge_kind`: `both` / `all` (kinds 1,2,3), `type` (1,3), `value` (2,3),
      `type-only` (1), `value-only` (2), `type+value` (3).
    - `stop_at`: namespace/module prefixes, exact decl names, or `@external` (module IS NULL).
      Boundary nodes matching `stop_at` are included (`stopped: true`) and not expanded further.
    - `project_only`: exclude Mathlib/Init/Std/Lean external nodes during traversal.
    """
    norm_dir = _DIRECTION_ALIASES.get(direction)
    if norm_dir is None:
        raise ValueError(f"invalid direction {direction!r} (expected backward|bwd|forward|fwd|both)")
    direction = norm_dir
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
        has_dm = _has_decl_module_rows(conn)

        meta_cache: Dict[int, Tuple[str, Optional[str], Optional[str]]] = {}

        def get_name_mod(did: int) -> Tuple[str, Optional[str], Optional[str]]:
            hit = meta_cache.get(did)
            if hit is not None:
                return hit
            if has_dm:
                r = conn.execute(
                    "SELECT d.name, m.module, m.method FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id WHERE d.id = ?",
                    (did,),
                ).fetchone()
                val = (str(r[0]), r[1], r[2]) if r is not None else ("", None, None)
            else:
                r = conn.execute("SELECT name FROM decls WHERE id = ?", (did,)).fetchone()
                val = (str(r[0]), None, None) if r is not None else ("", None, None)
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
                        nm, mod, meth = get_name_mod(nb_id)
                        if project_only and not _is_project_decl(nm, mod, meth, has_dm):
                            seen_dir.add(nb_id)
                            continue
                        if len(visited) >= max_nodes:
                            truncated = True
                            continue
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
                "project_only": project_only,
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

        dom_children_trunc = dom_obj["children_total"] > len(dom_obj["children"])
        dom_obj["children_truncated"] = dom_children_trunc
        type_trunc = type_total > len(type_deps)
        val_trunc = val_total > len(val_deps)
        dep_trunc = dep_total > len(dependents)
        any_trunc = type_trunc or val_trunc or dep_trunc or dom_children_trunc

        return {
            "schema": "leanre.kernel.type_deps/1",
            "provenance": "L",
            "kernel_db": os.path.basename(kernel_db_path),
            "decl": decl_obj,
            "limit": limit,
            "total": type_total + val_total,
            "truncated": any_trunc,
            "type_deps_truncated": type_trunc,
            "value_only_deps_truncated": val_trunc,
            "dependents_truncated": dep_trunc,
            "sections": {
                "type_deps": {"shown": len(type_deps), "total": type_total, "truncated": type_trunc},
                "value_only_deps": {"shown": len(val_deps), "total": val_total, "truncated": val_trunc},
                "dependents": {"shown": len(dependents), "total": dep_total, "truncated": dep_trunc},
                "dom_children": {"shown": len(dom_obj["children"]), "total": dom_obj["children_total"], "truncated": dom_children_trunc},
            },
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
    trunc_hdr = " [TRUNCATED; pass --limit 0 for all]" if res.get("truncated") else ""
    lines = [
        f"[L] {d['name']}  ({d['kind']}, id={d['id']}, module={d['module'] or d['module_method']}){trunc_hdr}",
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
        for ch in dom["children"]:
            lines.append(f"    child [{ch['kind']:9s}] {ch['name']}  (subtree={ch['subtree_size']:,}, mod={ch['module'] or 'unmatched'})")
        if dom["children_total"] > len(dom["children"]):
            lines.append(f"    ... showing {len(dom['children'])} of {dom['children_total']:,}; pass --limit 0 for all")
    else:
        lines.append(f"  Dominators [{dom['tree']}]: unreachable")
    lines.append(f"  Type dependencies ({len(res['type_deps'])}/{res['type_deps_total']}):")
    for x in res["type_deps"]:
        lines.append(f"    --[{x['edge_kind_name']:5s}]--> [{x['kind']:9s}] {x['name']}  (mod={x['module'] or 'unmatched'}, dom={x['dom_subtree']})")
    if res["type_deps_total"] > len(res["type_deps"]):
        lines.append(f"    ... showing {len(res['type_deps'])} of {res['type_deps_total']:,}; pass --limit 0 for all")
    lines.append(f"  Value-only dependencies ({len(res['value_only_deps'])}/{res['value_only_deps_total']}):")
    for x in res["value_only_deps"]:
        lines.append(f"    --[value]--> [{x['kind']:9s}] {x['name']}  (mod={x['module'] or 'unmatched'}, dom={x['dom_subtree']})")
    if res["value_only_deps_total"] > len(res["value_only_deps"]):
        lines.append(f"    ... showing {len(res['value_only_deps'])} of {res['value_only_deps_total']:,}; pass --limit 0 for all")
    lines.append(f"  Direct dependents ({len(res['dependents'])}/{res['dependents_total']}):")
    for x in res["dependents"]:
        lines.append(f"    <--[{x['edge_kind_name']:5s}]-- [{x['kind']:9s}] {x['name']}  (mod={x['module'] or 'unmatched'}, dom={x['dom_subtree']})")
    if res["dependents_total"] > len(res["dependents"]):
        lines.append(f"    ... showing {len(res['dependents'])} of {res['dependents_total']:,}; pass --limit 0 for all")
    if res["paths_to_roots"]:
        best = min(res["paths_to_roots"], key=lambda p: (p["hops"], p["root_id"]))
        lines.append(f"  Shortest path to root ({best['root_name']}, {best['hops']} hops; live in {len(res['paths_to_roots'])} roots):")
        for h in best["path"]:
            pre = f"    [{h['hop']:2d}] " + (f"--[{h['edge_kind_name']}]--> " if h["edge_kind_name"] else "ROOT ")
            lines.append(f"{pre}{h['name']} ({h['kind']}, {h['module'] or 'unmatched'})")
    else:
        lines.append("  Shortest path to root: DEAD (unreachable from all roots)")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Co-evolution audit & inspection subcommands:
#   cone-audit, stats, callers, anchor (+ markdown blob-link verifier)
# ---------------------------------------------------------------------------

class _ConeGraphCache:
    """Memory-compact adjacency cache (`array('Q')` of dst ids) reused across targets."""

    def __init__(self) -> None:
        self.out_edges: Dict[int, "array.array[int]"] = {}

    def ensure_loaded(self, conn: sqlite3.Connection, ids: Sequence[int]) -> None:
        missing = [u for u in ids if u not in self.out_edges]
        if not missing:
            return
        buckets: Dict[int, List[int]] = {u: [] for u in missing}
        for chunk in _chunks(missing, 900):
            ph = ",".join("?" for _ in chunk)
            for src, dst in conn.execute(
                f"SELECT src, dst FROM edges WHERE src IN ({ph})",
                chunk,
            ):
                buckets[int(src)].append(int(dst))
        for u, dsts in buckets.items():
            self.out_edges[u] = array.array("Q", dsts)

    def backward_cone(self, conn: sqlite3.Connection, start_id: int) -> Set[int]:
        seen: Set[int] = {start_id}
        frontier: List[int] = [start_id]
        while frontier:
            self.ensure_loaded(conn, frontier)
            nxt: List[int] = []
            for u in frontier:
                for dst in self.out_edges[u]:
                    if dst not in seen:
                        seen.add(dst)
                        nxt.append(dst)
            frontier = nxt
        return seen


def _matches_flag_prefix(name: str, module: Optional[str], prefix: str) -> bool:
    """Match a namespace or module prefix/component such as `Published.` or `Examples₂`."""
    if not prefix:
        return False
    if prefix.endswith("."):
        dot_p = "." + prefix
        if name.startswith(prefix) or dot_p in name:
            return True
        if module and (module.startswith(prefix) or dot_p in module):
            return True
        return False
    p_dot = prefix + "."
    dot_p = "." + prefix
    dot_p_dot = "." + prefix + "."
    if name == prefix or name.startswith(p_dot) or dot_p_dot in name or name.endswith(dot_p):
        return True
    if module and (module == prefix or module.startswith(p_dot) or dot_p_dot in module or module.endswith(dot_p)):
        return True
    return False


def _mod_prefix_key(module: str, depth: int = 2) -> str:
    parts = module.split(".")
    return ".".join(parts[:depth]) if len(parts) >= depth else module


def _aggregate_cone_ids(
    conn: sqlite3.Connection,
    cone_ids: Set[int],
    *,
    has_dm: bool,
    has_taint: bool,
    project_only: bool,
    filter_mod_re: Optional[re.Pattern[str]],
    filter_mod_raw: Optional[str],
    flag_prefixes: Sequence[str],
    top_mods: int,
) -> Dict[str, Any]:
    """Exact, untruncated aggregation over a set of declaration IDs in `kernel.db`."""
    sorted_ids = sorted(cone_ids)
    total = len(sorted_ids)
    proj_count = 0
    proj_with_mod = 0
    proj_unmatched = 0
    ext_count = 0

    by_kind: collections.Counter = collections.Counter()
    by_kind_proj: collections.Counter = collections.Counter()
    by_kind_ext: collections.Counter = collections.Counter()

    axioms_all: List[Dict[str, Any]] = []
    project_opaques: List[Dict[str, Any]] = []
    project_modules: collections.Counter = collections.Counter()
    project_mod_prefixes: collections.Counter = collections.Counter()

    # Soundness & reduction flags split project vs external
    flag_defs = (
        ("sorryAx", F_SORRY, True),
        ("ofReduceBool", F_REDUCE_BOOL, True),
        ("ofReduceNat", F_REDUCE_NAT, True),
        ("trustCompiler", F_TRUST_COMPILER, True),
        ("refl_true", F_REFL_TRUE, False),
        ("of_decide_eq_true_refl", F_OF_DECIDE, False),
    )
    flag_stats: Dict[str, Dict[str, Any]] = {
        fname: {"total": 0, "project": 0, "external": 0, **({"decls": []} if keep_list else {})}
        for fname, _bit, keep_list in flag_defs
    }

    flag_prefix_hits: Dict[str, Dict[str, Any]] = {
        p: {
            "count": 0,
            "project_count": 0,
            "external_count": 0,
            "modules": set(),
            "decls": [],
            "by_kind": collections.Counter(),
            "decls_by_kind": collections.defaultdict(list),
        }
        for p in flag_prefixes
    }
    filter_mod_hits: Dict[str, List[str]] = collections.defaultdict(list)
    filter_mod_decl_count = 0

    id_is_proj: Dict[int, bool] = {}
    id_meta_small: Dict[int, Tuple[str, Optional[str]]] = {}

    for chunk in _chunks(sorted_ids, 900):
        ph = ",".join("?" for _ in chunk)
        if has_dm:
            rows = conn.execute(
                f"SELECT d.id, d.name, d.kind, d.flags, m.module, m.method "
                f"FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id "
                f"WHERE d.id IN ({ph})",
                chunk,
            ).fetchall()
        else:
            rows = [
                (r[0], r[1], r[2], r[3], None, None)
                for r in conn.execute(
                    f"SELECT id, name, kind, flags FROM decls WHERE id IN ({ph})",
                    chunk,
                ).fetchall()
            ]
        for did_raw, nm_raw, kd_raw, fl_raw, mod, meth in rows:
            did = int(did_raw)
            nm = str(nm_raw)
            kd = str(kd_raw)
            fl = int(fl_raw)
            is_proj = _is_project_decl(nm, mod, meth, has_dm)
            id_is_proj[did] = is_proj
            id_meta_small[did] = (nm, mod)

            by_kind[kd] += 1
            if is_proj:
                proj_count += 1
                by_kind_proj[kd] += 1
                if mod is not None:
                    proj_with_mod += 1
                    project_modules[mod] += 1
                    project_mod_prefixes[_mod_prefix_key(mod, 2)] += 1
                else:
                    proj_unmatched += 1
            else:
                ext_count += 1
                by_kind_ext[kd] += 1

            if kd == "axiom":
                axioms_all.append({
                    "id": did,
                    "name": nm,
                    "module": mod,
                    "is_project": is_proj,
                    "is_standard": nm in STANDARD_AXIOMS,
                })
            if kd == "opaque" and is_proj:
                project_opaques.append({"id": did, "name": nm, "module": mod})

            # Kernel flags (also catch the raw constant declarations themselves)
            for fname, bit, keep_list in flag_defs:
                hit = bool(fl & bit)
                if not hit:
                    if fname == "sorryAx" and nm == "sorryAx":
                        hit = True
                    elif fname == "ofReduceBool" and nm in ("Lean.ofReduceBool", "Lean.reduceBool"):
                        hit = True
                    elif fname == "ofReduceNat" and nm in ("Lean.ofReduceNat", "Lean.reduceNat"):
                        hit = True
                    elif fname == "trustCompiler" and nm == "Lean.trustCompiler":
                        hit = True
                if hit:
                    fs = flag_stats[fname]
                    fs["total"] += 1
                    if is_proj:
                        fs["project"] += 1
                    else:
                        fs["external"] += 1
                    if keep_list:
                        fs["decls"].append({"id": did, "name": nm, "module": mod, "is_project": is_proj})

            if flag_prefixes and (not project_only or is_proj):
                for pref in flag_prefixes:
                    if _matches_flag_prefix(nm, mod, pref):
                        fp = flag_prefix_hits[pref]
                        fp["count"] += 1
                        if is_proj:
                            fp["project_count"] += 1
                        else:
                            fp["external_count"] += 1
                        if mod is not None:
                            fp["modules"].add(mod)
                        fp["decls"].append(nm)
                        fp["by_kind"][kd] += 1
                        fp["decls_by_kind"][kd].append(nm)

            if filter_mod_re is not None and mod is not None:
                if not project_only or is_proj:
                    if filter_mod_re.search(mod):
                        filter_mod_decl_count += 1
                        filter_mod_hits[mod].append(nm)

    # Taint sources inside the cone, split strictly project vs external
    taint_by_class: Dict[str, Dict[str, Any]] = {}
    for base_cls in ("decide_kernel", "decide_kernel_pattern"):
        taint_by_class[base_cls] = {
            "total": 0,
            "project": 0,
            "external": 0,
            "project_decls": [],
            "external_decls": [],
        }
    if has_taint:
        seen_taint_pairs: Set[Tuple[str, int]] = set()
        for chunk in _chunks(sorted_ids, 900):
            ph = ",".join("?" for _ in chunk)
            for cls, did_raw, origin, tmod, tln in conn.execute(
                f"SELECT class, decl_id, origin, module, line_no FROM taint_sources WHERE decl_id IN ({ph})",
                chunk,
            ):
                if did_raw is None:
                    continue
                did = int(did_raw)
                pair = (str(cls), did)
                if pair in seen_taint_pairs:
                    continue
                seen_taint_pairs.add(pair)
                entry = taint_by_class.setdefault(
                    str(cls),
                    {"total": 0, "project": 0, "external": 0, "project_decls": [], "external_decls": []},
                )
                is_proj = id_is_proj.get(did, False)
                nm, dmod = id_meta_small.get(did, ("", tmod))
                rec = {
                    "id": did,
                    "name": nm,
                    "module": tmod or dmod,
                    "line_no": tln,
                    "origin": origin,
                }
                entry["total"] += 1
                if is_proj:
                    entry["project"] += 1
                    entry["project_decls"].append(rec)
                else:
                    entry["external"] += 1
                    entry["external_decls"].append(rec)
        for entry in taint_by_class.values():
            entry["project_decls"].sort(key=lambda r: (r["name"], r["id"]))
            entry["external_decls"].sort(key=lambda r: (r["name"], r["id"]))

    axioms_all.sort(key=lambda a: (0 if a["is_standard"] else 1, a["name"]))
    standard_axioms = [a["name"] for a in axioms_all if a["is_standard"]]
    custom_axioms = [a["name"] for a in axioms_all if not a["is_standard"]]
    project_custom_axioms = [a["name"] for a in axioms_all if (not a["is_standard"]) and a["is_project"]]
    project_opaques.sort(key=lambda o: (o["module"] or "", o["name"]))

    kinds_order = ("thm", "def", "inductive", "axiom", "opaque", "quot")
    kind_dict = {k: by_kind.get(k, 0) for k in kinds_order}
    kind_proj_dict = {k: by_kind_proj.get(k, 0) for k in kinds_order}
    kind_ext_dict = {k: by_kind_ext.get(k, 0) for k in kinds_order}

    top_n = max(0, top_mods)
    top_prefixes_list = [
        {"prefix": pref, "decls": cnt}
        for pref, cnt in project_mod_prefixes.most_common(top_n)
    ]
    top_exact_mods_list = [
        {"module": m, "decls": cnt}
        for m, cnt in project_modules.most_common(top_n)
    ]

    flag_prefix_out: Dict[str, Any] = {}
    fp_kinds_order = ("axiom", "opaque", "thm", "def", "inductive", "quot")
    for pref in flag_prefixes:
        fp = flag_prefix_hits[pref]
        decls_sorted = sorted(fp["decls"])
        fp_by_kind: Dict[str, int] = {k: fp["by_kind"].get(k, 0) for k in fp_kinds_order}
        for k, v in sorted(fp["by_kind"].items()):
            if k not in fp_by_kind:
                fp_by_kind[k] = v
        extra_kinds = [k for k in sorted(fp["decls_by_kind"]) if k not in fp_kinds_order]
        fp_decls_by_kind: Dict[str, List[str]] = {
            k: sorted(fp["decls_by_kind"][k])
            for k in (*fp_kinds_order, *extra_kinds)
            if fp["decls_by_kind"].get(k)
        }
        flag_prefix_out[pref] = {
            "count": fp["count"],
            "project_count": fp["project_count"],
            "external_count": fp["external_count"],
            "modules_count": len(fp["modules"]),
            "modules": sorted(fp["modules"]),
            "by_kind": fp_by_kind,
            "decls_by_kind": fp_decls_by_kind,
            "decls": decls_sorted,
        }

    filter_mod_out: Optional[Dict[str, Any]] = None
    if filter_mod_re is not None:
        matched_mods = [
            {
                "module": m,
                "decl_count": len(nms),
                "sample_decls": sorted(nms)[:10],
            }
            for m, nms in sorted(filter_mod_hits.items(), key=lambda kv: (-len(kv[1]), kv[0]))
        ]
        filter_mod_out = {
            "regex": filter_mod_raw,
            "matched_modules_count": len(matched_mods),
            "matched_decls_count": filter_mod_decl_count,
            "modules": matched_mods,
        }

    return {
        "counts": {
            "total": total,
            "project": proj_count,
            "project_with_module": proj_with_mod,
            "project_unmatched_auto": proj_unmatched,
            "external": ext_count,
            "project_modules": len(project_modules),
            "by_kind": kind_dict,
            "by_kind_project": kind_proj_dict,
            "by_kind_external": kind_ext_dict,
        },
        "axioms": {
            "total": len(axioms_all),
            "standard": standard_axioms,
            "custom": custom_axioms,
            "project_custom": project_custom_axioms,
            "all": axioms_all,
        },
        "soundness_flags": flag_stats,
        "taints": dict(sorted(taint_by_class.items())),
        "project_opaques": {
            "count": len(project_opaques),
            "decls": project_opaques,
        },
        "top_module_prefixes": top_prefixes_list,
        "top_modules": top_exact_mods_list,
        "flag_prefix_matches": flag_prefix_out,
        "filter_mod": filter_mod_out,
    }


def cone_audit_decls(
    kernel_db_path: str,
    decls: Sequence[str],
    *,
    project_only: bool = False,
    filter_mod: Optional[str] = None,
    flag_prefixes: Sequence[str] = (),
    top_mods: int = 15,
    tree: str = "ALL",
    continue_on_error: bool = False,
) -> Dict[str, Any]:
    """Exact, untruncated backward transitive cone audit over `edges` for one or more decls."""
    if not decls:
        raise ValueError("at least one declaration is required for cone-audit")
    if top_mods < 0:
        raise ValueError(f"top_mods must be >= 0, got {top_mods}")

    filter_mod_re: Optional[re.Pattern[str]] = None
    if filter_mod is not None:
        try:
            filter_mod_re = re.compile(filter_mod)
        except re.error as e:
            raise ValueError(f"invalid --filter-mod regex {filter_mod!r}: {e}") from e

    norm_flag_prefixes = _normalize_stop_rules(flag_prefixes)

    t0 = time.time()
    conn = _open_kernel_ro(kernel_db_path)
    try:
        tree_id, tree_label, tree_view = _resolve_dom_tree(conn, tree)
        has_dm = _has_decl_module_rows(conn)
        has_taint = _has_table(conn, "taint_sources")
        cache = _ConeGraphCache()

        targets_out: List[Dict[str, Any]] = []
        errors: List[Dict[str, Any]] = []
        union_ids: Set[int] = set()

        for q in decls:
            try:
                did, name, resolved_from = _resolve_decl_id(conn, q, allow_suffix=True)
            except LookupError as e:
                if not continue_on_error:
                    raise
                errors.append({"query": q, "error": str(e)})
                continue
            if has_dm:
                drow = conn.execute(
                    "SELECT d.kind, d.live_mask, d.fan_in, d.fan_out, m.module, m.method, dm.subtree_size "
                    "FROM decls d "
                    "LEFT JOIN decl_module m ON m.decl_id = d.id "
                    "LEFT JOIN dom dm ON dm.tree_id = ? AND dm.decl_id = d.id "
                    "WHERE d.id = ?",
                    (tree_id, did),
                ).fetchone()
            else:
                drow = conn.execute(
                    "SELECT d.kind, d.live_mask, d.fan_in, d.fan_out, NULL, NULL, dm.subtree_size "
                    "FROM decls d "
                    "LEFT JOIN dom dm ON dm.tree_id = ? AND dm.decl_id = d.id "
                    "WHERE d.id = ?",
                    (tree_id, did),
                ).fetchone()
            assert drow is not None
            cone_ids = cache.backward_cone(conn, did)
            union_ids |= cone_ids
            agg = _aggregate_cone_ids(
                conn,
                cone_ids,
                has_dm=has_dm,
                has_taint=has_taint,
                project_only=project_only,
                filter_mod_re=filter_mod_re,
                filter_mod_raw=filter_mod,
                flag_prefixes=norm_flag_prefixes,
                top_mods=top_mods,
            )
            target_meta: Dict[str, Any] = {
                "query": q,
                "id": did,
                "name": name,
                "kind": drow[0],
                "live_mask": int(drow[1]),
                "fan_in": int(drow[2]),
                "fan_out": int(drow[3]),
                "module": drow[4],
                "method": drow[5],
                "dom_subtree": None if drow[6] is None else int(drow[6]),
            }
            if resolved_from is not None:
                target_meta["resolved_from"] = resolved_from
            targets_out.append({"target": target_meta, **agg})

        union_agg: Optional[Dict[str, Any]] = None
        if len(targets_out) > 1:
            union_agg = _aggregate_cone_ids(
                conn,
                union_ids,
                has_dm=has_dm,
                has_taint=has_taint,
                project_only=project_only,
                filter_mod_re=filter_mod_re,
                filter_mod_raw=filter_mod,
                flag_prefixes=norm_flag_prefixes,
                top_mods=top_mods,
            )

        return {
            "schema": "leanre.kernel.cone_audit/1",
            "provenance": "L",
            "kernel_db": os.path.basename(kernel_db_path),
            "elapsed_s": round(time.time() - t0, 3),
            "params": {
                "decls": list(decls),
                "project_only": project_only,
                "filter_mod": filter_mod,
                "flag_prefixes": norm_flag_prefixes,
                "top_mods": top_mods,
                "tree": tree_label,
                "tree_view": tree_view,
                "continue_on_error": continue_on_error,
            },
            "targets": targets_out,
            "errors": errors,
            "union": union_agg,
        }
    finally:
        conn.close()


def _format_cone_section(label: str, agg: Dict[str, Any], project_only: bool) -> List[str]:
    c = agg["counts"]
    ax = agg["axioms"]
    sf = agg["soundness_flags"]
    lines = [label]
    lines.append(
        f"  cone: total={c['total']:,}  project={c['project']:,} "
        f"(with_mod={c['project_with_module']:,}, auto={c['project_unmatched_auto']:,}, mods={c['project_modules']:,})  "
        f"external={c['external']:,}"
    )
    bk = c["by_kind_project"] if project_only else c["by_kind"]
    bk_lbl = "kinds (project)" if project_only else "kinds (total)"
    lines.append(
        f"  {bk_lbl}: thm={bk['thm']:,} def={bk['def']:,} ind={bk['inductive']:,} "
        f"axiom={bk['axiom']:,} opaque={bk['opaque']:,} quot={bk['quot']:,}"
    )
    if not project_only:
        bkp = c["by_kind_project"]
        lines.append(
            f"  kinds (project): thm={bkp['thm']:,} def={bkp['def']:,} ind={bkp['inductive']:,} "
            f"axiom={bkp['axiom']:,} opaque={bkp['opaque']:,} quot={bkp['quot']:,}"
        )
    lines.append(
        f"  axioms ({ax['total']}): standard={ax['standard']}  custom={ax['custom']}"
        + (f"  project_custom={ax['project_custom']}" if ax["project_custom"] else "")
    )
    lines.append(
        f"  soundness flags: sorryAx={sf['sorryAx']['total']} "
        f"ofReduceBool={sf['ofReduceBool']['total']} "
        f"ofReduceNat={sf['ofReduceNat']['total']} "
        f"trustCompiler={sf['trustCompiler']['total']} "
        f"refl_true={sf['refl_true']['total']:,} (proj={sf['refl_true']['project']:,}, ext={sf['refl_true']['external']:,}) "
        f"of_decide={sf['of_decide_eq_true_refl']['total']:,} (proj={sf['of_decide_eq_true_refl']['project']:,}, ext={sf['of_decide_eq_true_refl']['external']:,})"
    )
    po = agg["project_opaques"]
    lines.append(f"  project opaques: {po['count']}")
    for o in po["decls"][:15]:
        lines.append(f"    opaque {o['name']}  ({o['module'] or 'unmatched'})")
    if po["count"] > 15:
        lines.append(f"    ... (+{po['count'] - 15} more)")

    taints = agg["taints"]
    if taints:
        t_parts = [
            f"{cls}={tv['total']} (proj={tv['project']}, ext={tv['external']})"
            for cls, tv in taints.items()
            if tv["total"] > 0 or cls in ("decide_kernel", "decide_kernel_pattern")
        ]
        lines.append("  taints: " + ", ".join(t_parts))
        for cls, tv in taints.items():
            if tv["project"] > 0:
                sample = ", ".join(r["name"] for r in tv["project_decls"][:8])
                more = f" (+{tv['project'] - 8} more)" if tv["project"] > 8 else ""
                lines.append(f"    [{cls} project ({tv['project']})]: {sample}{more}")

    if agg["top_module_prefixes"]:
        pref_str = ", ".join(f"{x['prefix']}({x['decls']:,})" for x in agg["top_module_prefixes"])
        lines.append(f"  top module prefixes: {pref_str}")

    if agg["flag_prefix_matches"]:
        lines.append("  flag-prefix matches:")
        for pref, fp in agg["flag_prefix_matches"].items():
            bk = fp.get("by_kind") or {}
            kind_parts = [
                f"{k}={bk[k]:,}"
                for k in ("axiom", "opaque", "thm", "def", "inductive", "quot")
                if bk.get(k, 0) > 0
            ]
            kind_str = ("; " + ", ".join(kind_parts)) if kind_parts else ""
            lines.append(
                f"    {pref}: {fp['count']:,} decls (proj={fp['project_count']:,}, ext={fp['external_count']:,}, "
                f"mods={fp['modules_count']:,}{kind_str})"
            )
            dbk = fp.get("decls_by_kind") or {}
            if dbk:
                for kd, nms in dbk.items():
                    sample = ", ".join(nms[:8])
                    more = f" (+{len(nms) - 8} more)" if len(nms) > 8 else ""
                    lines.append(f"      [{kd} ({len(nms):,})]: {sample}{more}")
            elif fp["decls"]:
                sample = ", ".join(fp["decls"][:8])
                more = f" (+{len(fp['decls']) - 8} more)" if len(fp["decls"]) > 8 else ""
                lines.append(f"      -> {sample}{more}")

    fm = agg["filter_mod"]
    if fm is not None:
        lines.append(
            f"  filter-mod /{fm['regex']}/: {fm['matched_modules_count']} modules, {fm['matched_decls_count']:,} decls"
        )
        for m in fm["modules"]:
            sample = ", ".join(m["sample_decls"][:5])
            lines.append(f"    {m['module']} ({m['decl_count']:,}): {sample}")
    return lines


def format_cone_audit_text(res: Dict[str, Any]) -> str:
    p = res["params"]
    errs = res.get("errors") or []
    err_s = f", {len(errs)} error(s)" if errs else ""
    lines = [
        f"[L] kernel cone-audit ({len(res['targets'])} target(s){err_s}, tree={p['tree']}, "
        f"project_only={p['project_only']}, {res['elapsed_s']:.2f}s)"
    ]
    for item in res["targets"]:
        t = item["target"]
        dom_s = "unreachable" if t["dom_subtree"] is None else f"{t['dom_subtree']:,}"
        hdr = (
            f"Target: {t['name']}  ({t['kind']}, id={t['id']}, dom={dom_s}, "
            f"fan_in={t['fan_in']:,}, fan_out={t['fan_out']:,}, mod={t['module'] or t['method'] or 'unmatched'})"
        )
        lines.extend(_format_cone_section(hdr, item, p["project_only"]))
    if res["union"] is not None:
        lines.extend(_format_cone_section("Union across all targets:", res["union"], p["project_only"]))
    if errs:
        lines.append(f"Unresolved targets ({len(errs)}):")
        for e in errs:
            lines.append(f"  {e['query']}: {e['error']}")
    return "\n".join(lines)


_RE_ANCHOR_DECL_HDR = re.compile(
    r"^\s*(?:set_option\s+[^\n]*\bin\s*\n\s*)*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local|public|meta)\s+)*"
    r"(structure|class|inductive)\b"
)
_RE_ANCHOR_TERM_STOP = re.compile(
    r"^(?:end(?:\s|$)|namespace\s|section\b|example\b|mutual\b|variable\b|open\b|theorem\b|lemma\b|def\b|abbrev\b|"
    r"structure\b|class\b|inductive\b|instance\b|opaque\b|axiom\b|deriving\b|attribute\b|set_option\b|"
    r"universe\b|export\b|#|@\[|/-)"
)


def _get_struct_member_lines(
    stripped_lines: List[str],
    parent_line: int,
    decl_starts_sorted: List[int],
    member_cache: Dict[int, Tuple[str, Dict[str, int]]],
) -> Tuple[str, Dict[str, int]]:
    """Extract `{field_or_ctor_name: 1based_line}` for a `structure`/`class`/`inductive` at `parent_line`."""
    hit = member_cache.get(parent_line)
    if hit is not None:
        return hit
    n_lines = len(stripped_lines)
    if parent_line < 1 or parent_line > n_lines:
        res: Tuple[str, Dict[str, int]] = ("", {})
        member_cache[parent_line] = res
        return res

    next_idx = bisect.bisect_right(decl_starts_sorted, parent_line)
    end_line = (decl_starts_sorted[next_idx] - 1) if next_idx < len(decl_starts_sorted) else n_lines
    chunk: List[Tuple[int, str]] = []
    for lno in range(parent_line, end_line + 1):
        ln = stripped_lines[lno - 1]
        if lno > parent_line and ln and not ln[0].isspace() and _RE_ANCHOR_TERM_STOP.match(ln):
            break
        chunk.append((lno, ln))

    chunk_text = "\n".join(ln for _, ln in chunk)
    m_hdr = _RE_ANCHOR_DECL_HDR.match(chunk_text)
    if not m_hdr:
        res = ("", {})
        member_cache[parent_line] = res
        return res
    kw = m_hdr.group(1)

    # Scan from keyword end to find depth-0 header terminator (`where` / `:=` / `|`)
    depth = 0
    open_ch = "([{⦃⟨"
    close_ch = ")]}⦄⟩"
    i = m_hdr.end()
    cn = len(chunk_text)
    term: Optional[str] = None
    term_end = cn
    while i < cn:
        ch = chunk_text[i]
        if ch in open_ch:
            depth += 1
        elif ch in close_ch:
            depth = max(0, depth - 1)
        elif depth == 0:
            if chunk_text.startswith(":=", i):
                term = ":="
                term_end = i + 2
                break
            if (
                chunk_text.startswith("where", i)
                and (i == 0 or not (chunk_text[i - 1].isalnum() or chunk_text[i - 1] in "_.'"))
                and (i + 5 >= cn or not (chunk_text[i + 5].isalnum() or chunk_text[i + 5] in "_'"))
            ):
                term = "where"
                term_end = i + 5
                break
            if ch == "\n":
                j = i + 1
                while j < cn and chunk_text[j] in " \t":
                    j += 1
                if j < cn and chunk_text[j] == "|":
                    term = "|"
                    term_end = j
                    break
        i += 1

    members: Dict[str, int] = {}
    if term is None:
        res = (kw, members)
        member_cache[parent_line] = res
        return res

    term_line = parent_line + chunk_text[:term_end].count("\n")
    if kw == "inductive" or term == "|":
        for lno, ln in chunk:
            if lno < term_line:
                continue
            s = ln
            if lno == term_line and term == "where":
                widx = ln.find("where")
                if widx >= 0:
                    s = ln[widx + 5 :]
            mc = re.match(r"^\s*\|\s*([^\s:()\[\]{}⦃⦄]+)", s)
            if mc:
                members.setdefault(mc.group(1), lno)
        res = (kw, members)
        member_cache[parent_line] = res
        return res

    # `structure` / `class` with `where` or `:=`: parse field start lines by indentation
    tail_pairs: List[Tuple[int, str]] = []
    for lno, ln in chunk:
        if lno < term_line:
            continue
        if lno == term_line:
            off_in_line = term_end - (chunk_text.rfind("\n", 0, term_end) + 1)
            rest_ln = ln[off_in_line:].strip()
            if rest_ln:
                tail_pairs.append((lno, "  " + rest_ln))
        else:
            tail_pairs.append((lno, ln))

    base_ind: Optional[int] = None
    for lno, ln in tail_pairs:
        s = ln.strip()
        if not s:
            continue
        if re.match(r"^deriving\b", s) and (len(ln) - len(ln.lstrip())) == 0:
            break
        m_ctor = re.match(r"^([^\s:()\[\]{}⦃⦄]+)\s*::\s*(.*)$", s)
        if m_ctor:
            members.setdefault(m_ctor.group(1), lno)
            if not m_ctor.group(2).strip():
                continue
        ind = len(ln) - len(ln.lstrip())
        if base_ind is None:
            base_ind = ind
        if ind <= base_ind:
            s_clean = re.sub(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*", "", s)
            mf = re.match(r"^([^\s:()\[\]{}⦃⦄]+)", s_clean)
            if mf:
                fname = mf.group(1)
                if fname not in _HYGIENE_STOP_WORDS and not fname.startswith(("|", "deriving")):
                    members.setdefault(fname, lno)
    res = (kw, members)
    member_cache[parent_line] = res
    return res


def _load_file_decl_index(
    abs_path: str,
    cache: Dict[str, Tuple[List[str], List[str], Dict[str, int], Dict[str, List[int]], List[int], Dict[int, Tuple[str, Dict[str, int]]]]],
) -> Tuple[List[str], List[str], Dict[str, int], Dict[str, List[int]], List[int], Dict[int, Tuple[str, Dict[str, int]]]]:
    """Parse `.lean` file once into `(raw_lines, stripped_lines, exact_name_to_line, tail_name_to_lines, decl_starts, member_cache)`."""
    hit = cache.get(abs_path)
    if hit is not None:
        return hit
    import sighash  # sibling module

    with open(abs_path, "r", encoding="utf-8", errors="replace") as f:
        text = f.read()
    raw_lines = text.splitlines()
    stripped_lines = sighash.strip_comments(text).splitlines()
    exact_map: Dict[str, int] = {}
    tail_map: Dict[str, List[int]] = collections.defaultdict(list)
    decl_starts_set: Set[int] = set()
    for d in sighash.iter_source_decls(text, with_sig=False):
        nm = d.get("name")
        ln = int(d.get("line", 0))
        if nm and ln > 0:
            exact_map.setdefault(nm, ln)
            tail = nm.rsplit(".", 1)[-1]
            tail_map[tail].append(ln)
            decl_starts_set.add(ln)
    val = (raw_lines, stripped_lines, exact_map, dict(tail_map), sorted(decl_starts_set), {})
    cache[abs_path] = val
    return val


def _clean_header_line(raw_line: str, max_len: int = 160) -> str:
    """Return a clean 1-line declaration header without proof bodies."""
    s = raw_line.strip()
    cut = s.find(":= by")
    if cut >= 0:
        s = s[:cut].rstrip()
    if len(s) > max_len:
        s = s[: max_len - 1].rstrip() + "…"
    return s


def _resolve_decl_source_anchor(
    name: str,
    module: Optional[str],
    src_root: str,
    file_cache: Dict[str, Tuple[List[str], List[str], Dict[str, int], Dict[str, List[int]], List[int], Dict[int, Tuple[str, Dict[str, int]]]]],
) -> Dict[str, Any]:
    """Map a declaration `(name, module)` to `(module, path, line_no, header)` on disk (resolving `Struct.field` directly)."""
    if not module:
        return {
            "name": name,
            "module": None,
            "path": None,
            "line_no": None,
            "header": None,
            "status": "external",
        }
    rel = module.replace(".", os.sep) + ".lean"
    abs_path, err = _safe_resolve_src_path(src_root, rel)
    if abs_path is None:
        return {
            "name": name,
            "module": module,
            "path": rel.replace(os.sep, "/"),
            "line_no": None,
            "header": None,
            "status": err or "file_not_found",
        }
    disp_path = _rel_display_path(abs_path, os.path.dirname(os.path.realpath(src_root)) if os.path.basename(os.path.realpath(src_root)) == "src" else src_root)
    raw_lines, stripped_lines, exact_map, tail_map, decl_starts_sorted, member_cache = _load_file_decl_index(abs_path, file_cache)

    # Candidate resolution order: exact name, un-privatized name, structure field / inductive ctor, parent_prefix, tail
    lookup_name = name
    if name.startswith("_private."):
        parts = name.split(".")
        for i in range(1, len(parts)):
            if parts[i] == "0" and i + 1 < len(parts):
                lookup_name = ".".join(parts[i + 1 :])
                break

    line_no: Optional[int] = exact_map.get(lookup_name)
    match_kind = "exact"
    parent_name: Optional[str] = None
    parent_line: Optional[int] = None
    if line_no is None:
        for pref in _proper_prefixes(lookup_name):
            if pref in exact_map:
                pline = exact_map[pref]
                rest = lookup_name[len(pref) + 1 :]
                if rest and "." not in rest and not rest.startswith(("_proof_", "match_", "_simp_", "eq_")):
                    pkw, members = _get_struct_member_lines(stripped_lines, pline, decl_starts_sorted, member_cache)
                    if rest in members:
                        line_no = members[rest]
                        match_kind = "ctor" if pkw == "inductive" else "field"
                        parent_name = pref
                        parent_line = pline
                        break
                line_no = pline
                match_kind = "parent_prefix"
                break
    if line_no is None:
        tail = lookup_name.rsplit(".", 1)[-1]
        t_lines = tail_map.get(tail)
        if t_lines:
            line_no = t_lines[0]
            match_kind = "tail"

    if line_no is None or line_no < 1 or line_no > len(raw_lines):
        return {
            "name": name,
            "module": module,
            "path": disp_path,
            "line_no": None,
            "header": None,
            "status": "symbol_not_found_in_file",
        }
    header = _clean_header_line(raw_lines[line_no - 1])
    out: Dict[str, Any] = {
        "name": name,
        "module": module,
        "path": disp_path,
        "line_no": line_no,
        "header": header,
        "status": "ok",
        "match_kind": match_kind,
    }
    if parent_name is not None:
        out["parent_name"] = parent_name
        out["parent_line"] = parent_line
    return out


def _detect_forwarding_alias_source(
    abs_path: str,
    decl_name: str,
    target_name: str,
    file_cache: Dict[str, Dict[str, Any]],
) -> bool:
    """Return True if source body of `decl_name` is a trivial 1-hop forwarding wrapper around `target_name`."""
    span = _extract_decl_source_span(abs_path, decl_name, file_cache)
    if span is None:
        return False
    body = span["body_text"].strip()
    if not body:
        return False
    tail = target_name.rsplit(".", 1)[-1]
    tpat = re.escape(tail)
    if re.match(rf"^@?(?:_root_\.)?(?:[A-Za-z0-9_.'\u2080-\u2089]+\.)?{tpat}(?:\.\{{[^}}]*\}})?(?:\s|$)", body):
        return True
    if _is_pure_tuple_alias_body(body, target_name):
        return True
    return False


def stats_decls(
    kernel_db_path: str,
    decls: Sequence[str],
    *,
    tree: str = "ALL",
    src_root: Optional[str] = None,
    continue_on_error: bool = False,
    with_alias: bool = False,
) -> Dict[str, Any]:
    """Batch lookup of core kernel metrics (and optional disk anchors / 1-hop alias_of hints) for declarations."""
    if not decls:
        raise ValueError("at least one declaration is required for stats")
    conn = _open_kernel_ro(kernel_db_path)
    try:
        tree_id, tree_label, tree_view = _resolve_dom_tree(conn, tree)
        has_dm = _has_decl_module_rows(conn)
        root_legend: List[Dict[str, Any]] = []
        if _has_table(conn, "roots"):
            root_legend = [
                {"id": int(r[0]), "bit": 1 << int(r[0]), "name": str(r[1]), "group": str(r[2])}
                for r in conn.execute("SELECT id, name, grp FROM roots ORDER BY id")
            ]
        file_cache: Dict[str, Any] = {}
        hyg_file_cache: Dict[str, Dict[str, Any]] = {}
        eff_src_root = src_root or (default_src_root() if with_alias and os.path.isdir(default_src_root()) else None)
        rows_out: List[Dict[str, Any]] = []
        errors: List[Dict[str, Any]] = []
        for q in decls:
            try:
                did, _name, resolved_from = _resolve_decl_id(conn, q, allow_suffix=True)
            except LookupError as e:
                if not continue_on_error:
                    raise
                errors.append({"query": q, "error": str(e)})
                continue
            if has_dm:
                r = conn.execute(
                    "SELECT d.id, d.name, d.kind, d.fan_in, d.fan_out, d.fan_out_type, d.fan_out_value, "
                    "       d.type_nodes, d.value_nodes, d.flags, d.live_mask, d.stmt_mask, d.defcone_mask, "
                    "       m.module, m.method, dm.subtree_size, dm.depth, dp.name "
                    "FROM decls d "
                    "LEFT JOIN decl_module m ON m.decl_id = d.id "
                    "LEFT JOIN dom dm ON dm.tree_id = ? AND dm.decl_id = d.id "
                    "LEFT JOIN decls dp ON dp.id = dm.idom "
                    "WHERE d.id = ?",
                    (tree_id, did),
                ).fetchone()
            else:
                r = conn.execute(
                    "SELECT d.id, d.name, d.kind, d.fan_in, d.fan_out, d.fan_out_type, d.fan_out_value, "
                    "       d.type_nodes, d.value_nodes, d.flags, d.live_mask, d.stmt_mask, d.defcone_mask, "
                    "       NULL, NULL, dm.subtree_size, dm.depth, dp.name "
                    "FROM decls d "
                    "LEFT JOIN dom dm ON dm.tree_id = ? AND dm.decl_id = d.id "
                    "LEFT JOIN decls dp ON dp.id = dm.idom "
                    "WHERE d.id = ?",
                    (tree_id, did),
                ).fetchone()
            assert r is not None
            live_mask_val = int(r[10])
            fan_out_val = int(r[6])
            val_nodes = int(r[8])
            entry: Dict[str, Any] = {
                "query": q,
                "id": int(r[0]),
                "name": str(r[1]),
                "kind": str(r[2]),
                "module": r[13],
                "method": r[14],
                "dom_subtree": None if r[15] is None else int(r[15]),
                "dom_depth": None if r[16] is None else int(r[16]),
                "idom": r[17],
                "fan_in": int(r[3]),
                "fan_out": int(r[4]),
                "fan_out_type": int(r[5]),
                "fan_out_value": fan_out_val,
                "type_nodes": int(r[7]),
                "value_nodes": val_nodes,
                "flags": int(r[9]),
                "flag_names": decode_flags(int(r[9])),
                "live_mask": live_mask_val,
                "live_roots": [rt["name"] for rt in root_legend if live_mask_val & rt["bit"]],
                "stmt_mask": int(r[11]),
                "defcone_mask": int(r[12]),
            }
            if resolved_from is not None:
                entry["resolved_from"] = resolved_from
            if src_root:
                anc = _resolve_decl_source_anchor(entry["name"], entry["module"], src_root, file_cache)
                entry["anchor"] = (
                    f"{anc['path']}:{anc['line_no']}"
                    if anc["status"] == "ok" and anc["path"] and anc["line_no"]
                    else anc["status"]
                )
            # Inexpensive kernel 1-hop alias check (`value_nodes == 1` & `fan_out_value == 1`) + optional source check
            if fan_out_val == 1 and (val_nodes == 1 or with_alias):
                arows = conn.execute(
                    "SELECT d2.name, d2.kind FROM edges e JOIN decls d2 ON d2.id = e.dst "
                    "WHERE e.src = ? AND e.kind IN (2, 3) LIMIT 2",
                    (did,),
                ).fetchall()
                if len(arows) == 1 and str(arows[0][1]) in ("thm", "def", "axiom", "opaque"):
                    tgt_nm = str(arows[0][0])
                    if val_nodes == 1:
                        entry["alias_of"] = tgt_nm
                    elif with_alias and eff_src_root and entry["module"]:
                        rel = str(entry["module"]).replace(".", os.sep) + ".lean"
                        ap, _err = _safe_resolve_src_path(eff_src_root, rel)
                        if ap is not None and _detect_forwarding_alias_source(ap, entry["name"], tgt_nm, hyg_file_cache):
                            entry["alias_of"] = tgt_nm
            rows_out.append(entry)
        return {
            "schema": "leanre.kernel.stats/1",
            "provenance": "L",
            "kernel_db": os.path.basename(kernel_db_path),
            "tree": tree_label,
            "tree_view": tree_view,
            "live_roots_legend": root_legend,
            "errors_count": len(errors),
            "errors": errors,
            "decls": rows_out,
        }
    finally:
        conn.close()


def _format_live_roots_legend(roots: Sequence[Dict[str, Any]]) -> str:
    if not roots:
        return "live bitmask: 0=dead; sum of 2^root_id bits across live roots"
    shown = ", ".join(f"{r['bit']}={r['name']}" for r in roots[:8])
    more = f" (+{len(roots) - 8} more)" if len(roots) > 8 else ""
    all_mask = sum(int(r["bit"]) for r in roots)
    return f"live bitmask (0=dead, {all_mask}=all {len(roots)} roots): {shown}{more}"


def format_stats_text(res: Dict[str, Any], *, table: bool = False) -> str:
    decls = res["decls"]
    errs = res.get("errors") or []
    roots = res.get("live_roots_legend") or []
    has_anchor = any("anchor" in d for d in decls)
    alias_rows = [(d["name"], d["alias_of"]) for d in decls if d.get("alias_of")]
    cols = [
        "name", "kind", "module", "dom", "fan_in", "fan_out",
        "tn", "vn", "flags", "live",
    ]
    if has_anchor:
        cols.append("anchor")

    def _row_vals(d: Dict[str, Any]) -> List[str]:
        vals = [
            d["name"],
            d["kind"],
            d["module"] or (d["method"] or "unmatched"),
            "-" if d["dom_subtree"] is None else f"{d['dom_subtree']:,}",
            f"{d['fan_in']:,}",
            f"{d['fan_out']:,}",
            f"{d['type_nodes']:,}",
            f"{d['value_nodes']:,}",
            ",".join(d["flag_names"]) if d["flag_names"] else "0",
            str(d["live_mask"]),
        ]
        if has_anchor:
            vals.append(str(d.get("anchor", "-")))
        return vals

    rows = [_row_vals(d) for d in decls]
    if table:
        lines = [
            "| " + " | ".join(cols) + " |",
            "| " + " | ".join("---:" if c in ("dom", "fan_in", "fan_out", "tn", "vn", "live") else "---" for c in cols) + " |",
        ]
        for rv in rows:
            lines.append("| " + " | ".join(rv) + " |")
        if alias_rows:
            lines.append("")
            for nm, tgt in alias_rows:
                lines.append(f"alias_of: {nm} := {tgt}")
        if rows:
            lines.append("")
            lines.append(_format_live_roots_legend(roots))
        if errs:
            lines.append("")
            lines.append(f"Unresolved targets ({len(errs)}):")
            for e in errs:
                lines.append(f"  {e['query']}: {e['error']}")
        return "\n".join(lines)

    widths = [max([len(cols[i])] + [len(r[i]) for r in rows]) for i in range(len(cols))]
    right_cols = {3, 4, 5, 6, 7, 9}
    hdr = "  ".join(
        cols[i].rjust(widths[i]) if i in right_cols else cols[i].ljust(widths[i])
        for i in range(len(cols))
    )
    sep = "  ".join("-" * widths[i] for i in range(len(cols)))
    err_s = f", {len(errs)} error(s)" if errs else ""
    lines = [f"[L] kernel stats ({len(decls)} decl(s){err_s}, tree={res['tree']})"]
    if rows:
        lines.extend([hdr, sep])
        for rv in rows:
            lines.append(
                "  ".join(
                    rv[i].rjust(widths[i]) if i in right_cols else rv[i].ljust(widths[i])
                    for i in range(len(cols))
                )
            )
        for nm, tgt in alias_rows:
            lines.append(f"  alias_of: {nm} := {tgt}")
        lines.append(_format_live_roots_legend(roots))
    if errs:
        lines.append(f"Unresolved targets ({len(errs)}):")
        for e in errs:
            lines.append(f"  {e['query']}: {e['error']}")
    return "\n".join(lines)


def _collect_callers_for_decl(
    conn: sqlite3.Connection,
    *,
    kernel_db_path: str,
    center_id: int,
    decl_query: str,
    resolved_from: Optional[str],
    depth: int,
    project_only: bool,
    grouped: bool,
    sort_by: str,
    limit: int,
    tree_id: int,
    tree_label: str,
    tree_view: str,
    has_dm: bool,
    meta_cache: Dict[int, Dict[str, Any]],
) -> Dict[str, Any]:
    def fetch_meta(ids: Sequence[int]) -> None:
        miss = [i for i in ids if i not in meta_cache]
        if not miss:
            return
        for ch in _chunks(miss, 900):
            ph = ",".join("?" for _ in ch)
            if has_dm:
                sql = (
                    f"SELECT d.id, d.name, d.kind, d.fan_in, d.fan_out, d.live_mask, d.flags, "
                    f"       m.module, m.method, dm.subtree_size "
                    f"FROM decls d "
                    f"LEFT JOIN decl_module m ON m.decl_id = d.id "
                    f"LEFT JOIN dom dm ON dm.tree_id = ? AND dm.decl_id = d.id "
                    f"WHERE d.id IN ({ph})"
                )
            else:
                sql = (
                    f"SELECT d.id, d.name, d.kind, d.fan_in, d.fan_out, d.live_mask, d.flags, "
                    f"       NULL, NULL, dm.subtree_size "
                    f"FROM decls d "
                    f"LEFT JOIN dom dm ON dm.tree_id = ? AND dm.decl_id = d.id "
                    f"WHERE d.id IN ({ph})"
                )
            for r in conn.execute(sql, (tree_id, *ch)):
                did = int(r[0])
                nm = str(r[1])
                mod = r[7]
                meth = r[8]
                meta_cache[did] = {
                    "id": did,
                    "name": nm,
                    "kind": str(r[2]),
                    "fan_in": int(r[3]),
                    "fan_out": int(r[4]),
                    "live_mask": int(r[5]),
                    "flags": int(r[6]),
                    "module": mod,
                    "method": meth,
                    "is_project": _is_project_decl(nm, mod, meth, has_dm),
                    "dom_subtree": None if r[9] is None else int(r[9]),
                }

    def sort_key(node: Dict[str, Any]) -> Tuple[Any, ...]:
        dom_v = -(node["dom_subtree"] if node["dom_subtree"] is not None else -1)
        if sort_by == "dom":
            return (dom_v, -node["fan_in"], node["name"])
        if sort_by == "fan_in":
            return (-node["fan_in"], dom_v, node["name"])
        return (node["name"], dom_v)

    fetch_meta([center_id])
    center_obj = dict(meta_cache[center_id])
    center_obj["query"] = decl_query
    if resolved_from is not None:
        center_obj["resolved_from"] = resolved_from

    expanded: Set[int] = {center_id}
    frontier: List[int] = [center_id]
    hops_out: List[Dict[str, Any]] = []
    any_truncated = False

    for hop in range(1, depth + 1):
        if not frontier:
            break
        by_parent: Dict[int, List[Tuple[int, int]]] = {p: [] for p in frontier}
        discovered: Set[int] = set()
        for ch in _chunks(frontier, 900):
            ph = ",".join("?" for _ in ch)
            for src, dst, ek in conn.execute(
                f"SELECT src, dst, kind FROM edges WHERE dst IN ({ph})",
                ch,
            ):
                si, di, eki = int(src), int(dst), int(ek)
                by_parent[di].append((si, eki))
                discovered.add(si)
        fetch_meta(sorted(discovered))

        groups_out: List[Dict[str, Any]] = []
        next_frontier_set: Set[int] = set()
        hop_total_raw = 0
        hop_shown_raw = 0

        ordered_parents = sorted(frontier, key=lambda pid: sort_key(meta_cache[pid]))
        for pid in ordered_parents:
            raw_edges = by_parent.get(pid, [])
            entries: List[Dict[str, Any]] = []
            for cid, ek in raw_edges:
                if cid == center_id:
                    continue
                cm = meta_cache.get(cid)
                if cm is None:
                    continue
                if project_only and not cm["is_project"]:
                    continue
                item = dict(cm)
                item["edge_kind"] = ek
                item["edge_kind_name"] = EDGE_KIND_NAMES.get(ek, str(ek))
                item["parent_id"] = pid
                item["parent_name"] = meta_cache[pid]["name"]
                entries.append(item)
            entries.sort(key=sort_key)
            total_for_parent = len(entries)
            hop_total_raw += total_for_parent
            if limit > 0 and len(entries) > limit:
                entries = entries[:limit]
                any_truncated = True
            hop_shown_raw += len(entries)
            for e in entries:
                if e["id"] not in expanded:
                    next_frontier_set.add(e["id"])
            if entries or total_for_parent > 0:
                groups_out.append({
                    "parent_id": pid,
                    "parent_name": meta_cache[pid]["name"],
                    "parent_dom_subtree": meta_cache[pid]["dom_subtree"],
                    "callers_total": total_for_parent,
                    "callers_shown": len(entries),
                    "truncated": total_for_parent > len(entries),
                    "callers": entries,
                })

        if not groups_out:
            break
        hops_out.append({
            "hop": hop,
            "parents_count": len(groups_out),
            "callers_total": hop_total_raw,
            "callers_shown": hop_shown_raw,
            "groups": groups_out,
        })
        expanded |= next_frontier_set
        frontier = sorted(next_frontier_set)

    return {
        "schema": "leanre.kernel.callers/1",
        "provenance": "L",
        "kernel_db": os.path.basename(kernel_db_path),
        "center": center_obj,
        "params": {
            "decl": decl_query,
            "depth": depth,
            "project_only": project_only,
            "grouped": grouped,
            "sort": sort_by,
            "limit": limit,
            "tree": tree_label,
            "tree_view": tree_view,
        },
        "truncated": any_truncated,
        "hops": hops_out,
    }


def callers_decl(
    kernel_db_path: str,
    decl: str,
    *,
    depth: int = 2,
    project_only: bool = False,
    grouped: bool = False,
    sort_by: str = "dom",
    limit: int = 50,
    tree: str = "ALL",
    continue_on_error: bool = False,
) -> Dict[str, Any]:
    """Upward reverse-edge walk from `decl`, grouped by hop and parent, sorted by `dom`/`fan_in`/`name`."""
    if depth < 0:
        raise ValueError(f"depth must be >= 0, got {depth}")
    if limit < 0:
        raise ValueError(f"limit must be >= 0, got {limit}")
    if sort_by not in ("dom", "fan_in", "name"):
        raise ValueError(f"invalid sort {sort_by!r} (expected dom|fan_in|name)")

    conn = _open_kernel_ro(kernel_db_path)
    try:
        tree_id, tree_label, tree_view = _resolve_dom_tree(conn, tree)
        has_dm = _has_decl_module_rows(conn)
        try:
            center_id, _center_name, resolved_from = _resolve_decl_id(
                conn, decl, allow_suffix=True, allow_const_folding=False
            )
        except LookupError as e:
            if not continue_on_error:
                raise
            return {
                "schema": "leanre.kernel.callers/1",
                "provenance": "L",
                "kernel_db": os.path.basename(kernel_db_path),
                "center": None,
                "params": {
                    "decl": decl,
                    "depth": depth,
                    "project_only": project_only,
                    "grouped": grouped,
                    "sort": sort_by,
                    "limit": limit,
                    "tree": tree_label,
                    "tree_view": tree_view,
                    "continue_on_error": True,
                },
                "truncated": False,
                "errors_count": 1,
                "errors": [{"query": decl, "error": str(e)}],
                "hops": [],
            }
        meta_cache: Dict[int, Dict[str, Any]] = {}
        return _collect_callers_for_decl(
            conn,
            kernel_db_path=kernel_db_path,
            center_id=center_id,
            decl_query=decl,
            resolved_from=resolved_from,
            depth=depth,
            project_only=project_only,
            grouped=grouped,
            sort_by=sort_by,
            limit=limit,
            tree_id=tree_id,
            tree_label=tree_label,
            tree_view=tree_view,
            has_dm=has_dm,
            meta_cache=meta_cache,
        )
    finally:
        conn.close()


def callers_decls(
    kernel_db_path: str,
    decls: Sequence[str],
    *,
    depth: int = 2,
    project_only: bool = False,
    grouped: bool = False,
    sort_by: str = "dom",
    limit: int = 50,
    tree: str = "ALL",
    continue_on_error: bool = False,
) -> Dict[str, Any]:
    """Batch upward reverse-edge walk for one or more declarations."""
    if not decls:
        raise ValueError("at least one declaration is required for callers")
    if depth < 0:
        raise ValueError(f"depth must be >= 0, got {depth}")
    if limit < 0:
        raise ValueError(f"limit must be >= 0, got {limit}")
    if sort_by not in ("dom", "fan_in", "name"):
        raise ValueError(f"invalid sort {sort_by!r} (expected dom|fan_in|name)")

    conn = _open_kernel_ro(kernel_db_path)
    try:
        tree_id, tree_label, tree_view = _resolve_dom_tree(conn, tree)
        has_dm = _has_decl_module_rows(conn)
        meta_cache: Dict[int, Dict[str, Any]] = {}
        targets: List[Dict[str, Any]] = []
        errors: List[Dict[str, Any]] = []
        for q in decls:
            try:
                center_id, _center_name, resolved_from = _resolve_decl_id(
                    conn, q, allow_suffix=True, allow_const_folding=False
                )
            except LookupError as e:
                if not continue_on_error:
                    raise
                errors.append({"query": q, "error": str(e)})
                continue
            targets.append(
                _collect_callers_for_decl(
                    conn,
                    kernel_db_path=kernel_db_path,
                    center_id=center_id,
                    decl_query=q,
                    resolved_from=resolved_from,
                    depth=depth,
                    project_only=project_only,
                    grouped=grouped,
                    sort_by=sort_by,
                    limit=limit,
                    tree_id=tree_id,
                    tree_label=tree_label,
                    tree_view=tree_view,
                    has_dm=has_dm,
                    meta_cache=meta_cache,
                )
            )
        return {
            "schema": "leanre.kernel.callers_batch/1",
            "provenance": "L",
            "kernel_db": os.path.basename(kernel_db_path),
            "params": {
                "decls": list(decls),
                "depth": depth,
                "project_only": project_only,
                "grouped": grouped,
                "sort": sort_by,
                "limit": limit,
                "tree": tree_label,
                "tree_view": tree_view,
                "continue_on_error": continue_on_error,
            },
            "truncated": any(t["truncated"] for t in targets),
            "errors_count": len(errors),
            "errors": errors,
            "targets": targets,
        }
    finally:
        conn.close()


def _format_single_callers_lines(res: Dict[str, Any], *, grouped: Optional[bool] = None) -> List[str]:
    c = res["center"]
    p = res["params"]
    use_grouped = p["grouped"] if grouped is None else grouped
    dom_s = "unreachable" if c["dom_subtree"] is None else f"{c['dom_subtree']:,}"
    lines = [
        f"[L] kernel callers: {c['name']} ({c['kind']}, id={c['id']}, dom={dom_s}, "
        f"fan_in={c['fan_in']:,}, mod={c['module'] or c['method'] or 'unmatched'})",
        f"    depth={p['depth']} sort={p['sort']} limit={p['limit']} project_only={p['project_only']} "
        f"grouped={use_grouped}" + (" [TRUNCATED]" if res["truncated"] else ""),
    ]
    if not res["hops"]:
        lines.append("  (no callers found)")
        return lines

    for h in res["hops"]:
        lines.append(f"  hop {h['hop']} ({h['callers_shown']}/{h['callers_total']} callers across {h['parents_count']} parent(s)):")
        if use_grouped:
            for g in h["groups"]:
                pdom = "-" if g["parent_dom_subtree"] is None else f"{g['parent_dom_subtree']:,}"
                trunc_s = f" [+{g['callers_total'] - g['callers_shown']} truncated]" if g["truncated"] else ""
                lines.append(f"    parent {g['parent_name']} (dom={pdom}, {g['callers_shown']}/{g['callers_total']}){trunc_s}:")
                for cl in g["callers"]:
                    cdom = "-" if cl["dom_subtree"] is None else f"{cl['dom_subtree']:,}"
                    lines.append(
                        f"      [{cl['kind']:9s}] {cl['name']}  "
                        f"(dom={cdom}, fan_in={cl['fan_in']:,}, edge={cl['edge_kind_name']}, mod={cl['module'] or cl['method'] or 'unmatched'})"
                    )
        else:
            flat = [cl for g in h["groups"] for cl in g["callers"]]
            if p["sort"] == "dom":
                flat.sort(key=lambda x: (-(x["dom_subtree"] if x["dom_subtree"] is not None else -1), -x["fan_in"], x["name"]))
            elif p["sort"] == "fan_in":
                flat.sort(key=lambda x: (-x["fan_in"], -(x["dom_subtree"] if x["dom_subtree"] is not None else -1), x["name"]))
            else:
                flat.sort(key=lambda x: x["name"])
            for cl in flat:
                cdom = "-" if cl["dom_subtree"] is None else f"{cl['dom_subtree']:,}"
                lines.append(
                    f"    [{cl['kind']:9s}] {cl['name']}  <--[{cl['edge_kind_name']}]-- {cl['parent_name']}  "
                    f"(dom={cdom}, fan_in={cl['fan_in']:,}, mod={cl['module'] or cl['method'] or 'unmatched'})"
                )
    return lines


def format_callers_text(res: Dict[str, Any], *, grouped: Optional[bool] = None) -> str:
    errs = res.get("errors") or []
    if "targets" in res:
        p = res["params"]
        err_s = f", {len(errs)} error(s)" if errs else ""
        lines = [
            f"[L] kernel callers ({len(res['targets'])} target(s){err_s}, depth={p['depth']}, sort={p['sort']}, limit={p['limit']})"
        ]
        for item in res["targets"]:
            lines.extend(_format_single_callers_lines(item, grouped=grouped))
        if errs:
            lines.append(f"Unresolved targets ({len(errs)}):")
            for e in errs:
                lines.append(f"  {e['query']}: {e['error']}")
        return "\n".join(lines)
    if res.get("center") is None:
        lines = ["[L] kernel callers (0 targets, 1 error(s))", "Unresolved targets (1):"]
        for e in errs:
            lines.append(f"  {e['query']}: {e['error']}")
        return "\n".join(lines)
    return "\n".join(_format_single_callers_lines(res, grouped=grouped))


_RE_BLOB_URL = re.compile(
    r"^https?://[^/\s)]+/[^/\s)]+/[^/\s)]+/blob/([^/\s#)]+)/([^#\s)]+)#L(\d+)(?:-L(\d+))?$"
)
_RE_RAW_LINKIES = re.compile(r"#L\d+\b")
_RE_LEAN_SYM = re.compile(
    r"^[A-Za-z_\u0370-\u03ff\u00c0-\u024f][A-Za-z0-9_'\u0370-\u03ff\u00c0-\u024f\u2080-\u2089\u2070-\u209f.]*$"
)


def _iter_markdown_links(md_text: str) -> Iterable[Tuple[int, str, str]]:
    """Yield `(md_line_no, link_text, url)` for markdown links outside fenced code blocks."""
    in_fence = False
    for line_no, line in enumerate(md_text.splitlines(), start=1):
        stripped = line.lstrip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        i = 0
        n = len(line)
        while i < n:
            if line[i] == "[" and (i == 0 or line[i - 1] != "!"):
                # Scan balanced `[ ... ]` respecting inline backticks
                depth = 1
                j = i + 1
                in_bt = False
                while j < n and depth > 0:
                    ch = line[j]
                    if ch == "`":
                        in_bt = not in_bt
                    elif not in_bt:
                        if ch == "[":
                            depth += 1
                        elif ch == "]":
                            depth -= 1
                    j += 1
                if depth == 0 and j < n and line[j] == "(":
                    # Scan balanced `( ... )`
                    pdepth = 1
                    k = j + 1
                    while k < n and pdepth > 0:
                        if line[k] == "(":
                            pdepth += 1
                        elif line[k] == ")":
                            pdepth -= 1
                        k += 1
                    if pdepth == 0:
                        ltext = line[i + 1 : j - 1]
                        lurl = line[j + 1 : k - 1].strip()
                        yield line_no, ltext, lurl
                        i = k
                        continue
            i += 1


def _extract_symbol_candidates(link_text: str) -> Tuple[List[str], bool]:
    """Return `(symbol_tokens, is_prose)` for a markdown link's visible label."""
    s = link_text.strip()
    # Strip outer markdown formatting (`...`, **...**, *...*)
    while len(s) >= 2 and (
        (s.startswith("`") and s.endswith("`") and "`" not in s[1:-1])
        or (s.startswith("**") and s.endswith("**"))
        or (s.startswith("*") and s.endswith("*") and "*" not in s[1:-1])
    ):
        if s.startswith("**"):
            s = s[2:-2].strip()
        else:
            s = s[1:-1].strip()
    if not s:
        return [], True

    # Direct Lean identifier or qualified name (e.g. `Per.BdRp`, `GlobalTheory.qExpansion_E₄`)
    if _RE_LEAN_SYM.match(s):
        toks = [s]
        tail = s.rsplit(".", 1)[-1]
        if tail and tail != s:
            toks.append(tail)
        return toks, False

    # Brace shorthand like `Per.{Ainf,BdR}`
    m_brace = re.match(r"^([A-Za-z0-9_.'\u2080-\u2089]+)\.\{([^}]+)\}$", s)
    if m_brace:
        inner = [x.strip() for x in m_brace.group(2).split(",") if x.strip()]
        return inner, False

    # Backticked identifier(s) inside label
    bt = re.findall(r"`([^`]+)`", s)
    sym_bt: List[str] = []
    for item in bt:
        it = item.strip()
        if _RE_LEAN_SYM.match(it):
            sym_bt.append(it)
            tail = it.rsplit(".", 1)[-1]
            if tail and tail != it:
                sym_bt.append(tail)
    if sym_bt:
        return sym_bt, False

    return [], True


_RE_STRUCT_HEADER = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local|public|meta)\s+)*"
    r"(structure|class)\s+([A-Za-z_\u0370-\u03ff\u00c0-\u024f][^\s:({\[⦃]*)"
)


def _extract_clause_without_other_links(line: str, ltext: str, lurl: str) -> str:
    """Return the sentence/clause around `[ltext](lurl)` on `line`, with other markdown links removed."""
    needle = f"[{ltext}]({lurl})"
    pos = line.find(needle)
    if pos < 0:
        return ltext
    # Mask other `[...](...)` spans on `line` so adjacent links don't pollute context
    chars = list(line)
    i = 0
    n = len(line)
    while i < n:
        if line[i] == "[" and (i == 0 or line[i - 1] != "!"):
            depth = 1
            j = i + 1
            in_bt = False
            while j < n and depth > 0:
                ch = line[j]
                if ch == "`":
                    in_bt = not in_bt
                elif not in_bt:
                    if ch == "[":
                        depth += 1
                    elif ch == "]":
                        depth -= 1
                j += 1
            if depth == 0 and j < n and line[j] == "(":
                pdepth = 1
                k = j + 1
                while k < n and pdepth > 0:
                    if line[k] == "(":
                        pdepth += 1
                    elif line[k] == ")":
                        pdepth -= 1
                    k += 1
                if pdepth == 0:
                    if i != pos:
                        for m_idx in range(i, k):
                            chars[m_idx] = " "
                    else:
                        # Strip the URL portion of our own link, keeping `ltext`
                        for m_idx in range(j, k):
                            chars[m_idx] = " "
                    i = k
                    continue
        i += 1
    masked = "".join(chars)
    lo = 0
    for sep in (". ", "; "):
        hit = masked.rfind(sep, 0, pos)
        if hit >= 0:
            lo = max(lo, hit + len(sep))
    hi = len(masked)
    link_end = pos + len(needle)
    for sep in (". ", "; "):
        hit = masked.find(sep, link_end)
        if hit >= 0:
            hi = min(hi, hit)
    return masked[lo:hi]


def _find_named_struct_field(
    ctx: str,
    ltext: str,
    struct_short: str,
    members: Dict[str, int],
    target_ln: int,
) -> Optional[Tuple[str, int]]:
    """Return `(field_name, field_line)` if `ctx` / `ltext` references a field of `struct_short`."""
    if not members:
        return None
    # If the visible link text explicitly names `struct_short` (without naming any field), it's intentional
    ltext_names_struct = _token_in_line(struct_short, ltext)
    if ltext_names_struct and not any(
        fn != struct_short and _token_in_line(fn, ltext) for fn in members
    ):
        return None
    for fname, fln in members.items():
        if fln == target_ln or fname == struct_short or len(fname) < 2:
            continue
        if re.search(rf"(?<![{_HYGIENE_IDENT_CONT}.]){re.escape(struct_short)}\.{re.escape(fname)}(?![{_HYGIENE_IDENT_CONT}])", ctx):
            return fname, fln
        if re.search(rf"`\.?{re.escape(fname)}`", ctx):
            return fname, fln
        if re.search(rf"(?<![{_HYGIENE_IDENT_CONT}])\.{re.escape(fname)}(?![{_HYGIENE_IDENT_CONT}])", ctx):
            return fname, fln
        if re.search(rf"\b(?:field|projection|slot)\s+{re.escape(fname)}\b", ctx, re.I):
            return fname, fln
        if len(fname) >= 3 and ("_" in fname or any(c.isupper() for c in fname[1:])) and _token_in_line(fname, ctx):
            return fname, fln
    return None


def _token_in_line(tok: str, line: str) -> bool:
    pat = r"(?<![A-Za-z0-9_'\u2080-\u2089])" + re.escape(tok) + r"(?![A-Za-z0-9_'\u2080-\u2089])"
    return re.search(pat, line) is not None


def verify_markdown_anchors(
    md_paths: Sequence[str],
    src_root: str,
    *,
    near_window: int = 3,
) -> Dict[str, Any]:
    """Verify every GitHub blob `#L<line>` anchor and check for raw Linkies violations in markdown files."""
    file_index_cache: Dict[str, Any] = {}
    results_by_file: List[Dict[str, Any]] = []
    total_blob_links = 0
    ok_links = 0
    broken_links = 0
    linkies_violations = 0
    total_warnings = 0

    for md_path in md_paths:
        if not os.path.isfile(md_path):
            broken_links += 1
            results_by_file.append({
                "md_file": _rel_display_path(md_path),
                "error": "md_file_not_found",
                "total_blob_links": 0,
                "ok_links": 0,
                "broken_links": 1,
                "linkies_violations": 0,
                "warnings_count": 0,
                "issues": [{"kind": "md_file_not_found", "md_line": 0, "detail": f"missing file: {md_path}"}],
                "warnings": [],
            })
            continue

        with open(md_path, "r", encoding="utf-8", errors="replace") as f:
            md_text = f.read()
        md_lines = md_text.splitlines()

        f_total = 0
        f_ok = 0
        f_broken = 0
        f_linkies = 0
        issues: List[Dict[str, Any]] = []
        warnings: List[Dict[str, Any]] = []

        for md_ln, ltext, lurl in _iter_markdown_links(md_text):
            if _RE_RAW_LINKIES.search(ltext):
                f_linkies += 1
                linkies_violations += 1
                issues.append({
                    "kind": "raw_linkies_violation",
                    "md_line": md_ln,
                    "link_text": ltext,
                    "url": lurl,
                    "detail": "raw `#L<line>` inside [link text]",
                })

            m = _RE_BLOB_URL.match(lurl)
            if not m:
                continue
            f_total += 1
            total_blob_links += 1
            commit_sha, rel_path, ln_str, end_ln_str = m.group(1), m.group(2), m.group(3), m.group(4)
            target_ln = int(ln_str)
            target_end_ln = int(end_ln_str) if end_ln_str else target_ln

            abs_path, err = _safe_resolve_src_path(src_root, rel_path)
            if abs_path is None:
                f_broken += 1
                broken_links += 1
                issues.append({
                    "kind": err or "file_not_found",
                    "md_line": md_ln,
                    "link_text": ltext,
                    "path": rel_path,
                    "line_no": target_ln,
                    "commit": commit_sha,
                    "detail": f"{err}: {rel_path}",
                })
                continue

            src_lines, stripped_lines, _em, _tm, decl_starts_sorted, member_cache = _load_file_decl_index(
                abs_path, file_index_cache
            )
            n_lines = len(src_lines)
            if target_ln < 1 or target_ln > n_lines or target_end_ln < target_ln or target_end_ln > n_lines:
                f_broken += 1
                broken_links += 1
                issues.append({
                    "kind": "line_out_of_bounds",
                    "md_line": md_ln,
                    "link_text": ltext,
                    "path": rel_path,
                    "line_no": target_ln,
                    "max_line": n_lines,
                    "detail": f"line {target_ln}..{target_end_ln} out of bounds (1..{n_lines})",
                })
                continue

            exact_line_txt = src_lines[target_ln - 1]
            syms, is_prose = _extract_symbol_candidates(ltext)

            def _maybe_warn_struct_header() -> None:
                nonlocal total_warnings
                m_sh = _RE_STRUCT_HEADER.match(exact_line_txt)
                if not m_sh:
                    return
                struct_short = m_sh.group(2).rsplit(".", 1)[-1]
                if struct_short in syms:
                    return
                _pkw, members = _get_struct_member_lines(
                    stripped_lines, target_ln, decl_starts_sorted, member_cache
                )
                if not members:
                    return
                raw_md_ln = md_lines[md_ln - 1] if 1 <= md_ln <= len(md_lines) else ltext
                ctx = _extract_clause_without_other_links(raw_md_ln, ltext, lurl)
                hit = _find_named_struct_field(ctx, ltext, struct_short, members, target_ln)
                if hit is not None:
                    fname, fln = hit
                    total_warnings += 1
                    warnings.append({
                        "kind": "structure_header_for_field",
                        "md_line": md_ln,
                        "link_text": ltext,
                        "structure": struct_short,
                        "field": fname,
                        "expected_line": fln,
                        "path": rel_path,
                        "line_no": target_ln,
                        "detail": (
                            f"link targets `{struct_short}` structure header at {rel_path}#L{target_ln}, "
                            f"while context names field `{fname}` (at #L{fln})"
                        ),
                    })

            if is_prose or not syms:
                _maybe_warn_struct_header()
                f_ok += 1
                ok_links += 1
                continue

            if any(_token_in_line(tok, exact_line_txt) for tok in syms):
                _maybe_warn_struct_header()
                f_ok += 1
                ok_links += 1
                continue

            # Check nearby lines (`±near_window`) for attribute lines / multi-line headers
            lo = max(1, target_ln - near_window)
            hi = min(n_lines, target_end_ln + near_window)
            found_near = False
            for probe_ln in range(lo, hi + 1):
                if any(_token_in_line(tok, src_lines[probe_ln - 1]) for tok in syms):
                    found_near = True
                    break
            if found_near:
                _maybe_warn_struct_header()
                f_ok += 1
                ok_links += 1
            else:
                f_broken += 1
                broken_links += 1
                issues.append({
                    "kind": "symbol_mismatch",
                    "md_line": md_ln,
                    "link_text": ltext,
                    "expected_symbols": syms,
                    "path": rel_path,
                    "line_no": target_ln,
                    "line_header": _clean_header_line(exact_line_txt, max_len=120),
                    "detail": f"symbol {syms[0]!r} not found at {rel_path}#L{target_ln} (±{near_window})",
                })

        results_by_file.append({
            "md_file": _rel_display_path(md_path),
            "total_blob_links": f_total,
            "ok_links": f_ok,
            "broken_links": f_broken,
            "linkies_violations": f_linkies,
            "warnings_count": len(warnings),
            "issues": issues,
            "warnings": warnings,
        })

    return {
        "files_checked": len(md_paths),
        "total_blob_links": total_blob_links,
        "ok_links": ok_links,
        "broken_links": broken_links,
        "linkies_violations": linkies_violations,
        "warnings_count": total_warnings,
        "all_passed": (broken_links == 0 and linkies_violations == 0),
        "files": results_by_file,
    }


def anchor_decls(
    kernel_db_path: str,
    decls: Sequence[str],
    *,
    src_root: Optional[str] = None,
    verify_md: Sequence[str] = (),
) -> Dict[str, Any]:
    """Map declarations to `(module, path, line_no, header)` on disk and/or verify markdown `#L` links."""
    sroot = src_root or default_src_root()
    decl_anchors: List[Dict[str, Any]] = []
    decl_errors = 0

    if decls:
        conn = _open_kernel_ro(kernel_db_path)
        try:
            has_dm = _has_decl_module_rows(conn)
            file_cache: Dict[str, Any] = {}
            for q in decls:
                try:
                    did, name, resolved_from = _resolve_decl_id(conn, q, allow_suffix=True)
                except LookupError as e:
                    decl_errors += 1
                    decl_anchors.append({
                        "query": q,
                        "name": None,
                        "module": None,
                        "path": None,
                        "line_no": None,
                        "header": None,
                        "status": "not_found",
                        "error": str(e),
                    })
                    continue
                mod: Optional[str] = None
                if has_dm:
                    mrow = conn.execute("SELECT module FROM decl_module WHERE decl_id = ?", (did,)).fetchone()
                    if mrow is not None:
                        mod = mrow[0]
                anc = _resolve_decl_source_anchor(name, mod, sroot, file_cache)
                anc["query"] = q
                anc["id"] = did
                if resolved_from is not None:
                    anc["resolved_from"] = resolved_from
                if anc["status"] not in ("ok", "external"):
                    decl_errors += 1
                decl_anchors.append(anc)
        finally:
            conn.close()

    md_report: Optional[Dict[str, Any]] = None
    if verify_md:
        md_report = verify_markdown_anchors(verify_md, sroot)

    all_passed = (decl_errors == 0) and (md_report is None or md_report["all_passed"])
    return {
        "schema": "leanre.kernel.anchor/1",
        "provenance": "L",
        "src_root": _rel_display_path(sroot),
        "all_passed": all_passed,
        "decl_errors": decl_errors,
        "decls": decl_anchors,
        "verify_md": md_report,
    }


def format_anchor_text(res: Dict[str, Any]) -> str:
    lines = [f"[L] kernel anchor (src_root={res['src_root']}, all_passed={res['all_passed']})"]
    if res["decls"]:
        lines.append(f"  declarations ({len(res['decls'])}):")
        for d in res["decls"]:
            if d["status"] == "ok":
                lines.append(f"    {d['name']}  ->  {d['path']}:{d['line_no']}  [{d['module']}]")
                if d.get("header"):
                    lines.append(f"      {d['header']}")
            else:
                extra = f" ({d['error']})" if d.get("error") else ""
                lines.append(f"    {d.get('name') or d['query']}  ->  [{d['status']}]{extra}")
    md = res.get("verify_md")
    if md is not None:
        wc = int(md.get("warnings_count", 0))
        warn_s = f", {wc} warning(s)" if wc else ""
        lines.append(
            f"  markdown verification: {md['files_checked']} file(s), "
            f"{md['ok_links']}/{md['total_blob_links']} blob links ok, "
            f"{md['broken_links']} broken, {md['linkies_violations']} raw Linkies violation(s){warn_s}"
        )
        for fr in md["files"]:
            st = "PASS" if (fr["broken_links"] == 0 and fr["linkies_violations"] == 0) else "FAIL"
            fwc = int(fr.get("warnings_count", 0))
            fwarn_s = f", {fwc} warning(s)" if fwc else ""
            lines.append(
                f"    [{st}] {fr['md_file']}: {fr['ok_links']}/{fr['total_blob_links']} ok, "
                f"{fr['broken_links']} broken, {fr['linkies_violations']} linkies{fwarn_s}"
            )
            for iss in fr["issues"]:
                lines.append(f"      L{iss['md_line']} [{iss['kind']}]: {iss['detail']}")
            for wrn in fr.get("warnings") or []:
                lines.append(f"      L{wrn['md_line']} [warning:{wrn['kind']}]: {wrn['detail']}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Proof-hygiene auditor (`leanre kernel hygiene`)
# ---------------------------------------------------------------------------

_HYGIENE_OPEN = "([{⦃⟨"
_HYGIENE_CLOSE = ")]}⦄⟩"
_HYGIENE_IDENT_START = r"A-Za-z_\u00c0-\u024f\u0370-\u03ff\u1d00-\u1dbf\u2100-\u214f\U0001d400-\U0001d7ff"
_HYGIENE_IDENT_CONT = r"A-Za-z0-9_'\u00c0-\u024f\u0370-\u03ff\u1d00-\u1dbf\u2070-\u209f\u2100-\u214f\U0001d400-\U0001d7ff"
_RE_HYGIENE_IDENT = re.compile(rf"[{_HYGIENE_IDENT_START}][{_HYGIENE_IDENT_CONT}]*")
_RE_HYGIENE_DECL_START = re.compile(
    r"^\s*(?:set_option\s+[^\n]*\bin\s*\n\s*)*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local|public|meta)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom)\b"
)
_RE_TOPLEVEL_CMD_LINE = re.compile(
    r"^(?:import|open|namespace|section|end|variable|universe|set_option|attribute|#check|#print|#eval|mutual)\b"
)
_RE_IMPLICIT_CTX_TACTIC = re.compile(
    rf"(?<![{_HYGIENE_IDENT_CONT}.])(?:assumption|linarith|nlinarith|positivity|omega|aesop|tauto|contradiction|grind|simp_all|solve_by_elim)(?![{_HYGIENE_IDENT_CONT}])"
    r"|simp\s*\[\s*\*\s*\]"
    rf"|(?<![{_HYGIENE_IDENT_CONT}.])(?:exact|apply|refine)\s+@"
)
_RE_COMBINATOR_PREFIX = re.compile(
    r"(?:Finset|Multiset|Set|List|Filter|DFinsupp|MeasureTheory)\."
    r"|(?<![A-Za-z0-9_])(?:finsum|∑|∏|ZeroFreeOn|Closed(?:\.[A-Za-z0-9_]+)?|Row(?:\.[A-Za-z0-9_]+)?|cauchyPowerSeries)\b"
    r"|\.(?:imp|mono|map|and|of_class|of_sel|sum_congr|sum_nonneg|prod_pos|sum_le_sum|sum_eq_zero|sum_filter|sep)\s*$"
)
_RE_UPPERCASE_SHORT = re.compile(rf"^[A-ZΑ-Ω][A-Za-z0-9_'₀-₉₁-₉]{{0,3}}$")
_HYGIENE_STOP_WORDS = frozenset({
    "by", "in", "at", "with", "where", "fun", "match", "if", "then", "else",
    "let", "have", "show", "from", "do", "return", "for", "of", "rfl",
    "trivial", "sorry", "admit", "exact", "apply", "intro", "intros", "rintro",
    "obtain", "rcases", "cases", "induction", "refine", "use", "constructor",
    "ext", "simp", "dsimp", "rw", "rwa", "erw", "linarith", "nlinarith",
    "omega", "ring", "abel", "positivity", "norm_num", "decide", "aesop",
    "tauto", "assumption", "contradiction", "exfalso", "subst", "clear",
    "revert", "generalize", "specialize", "calc", "set", "rename_i",
    "by_cases", "by_contra", "push_neg", "left", "right",
})
_HYGIENE_AUX_MARKERS = ("._proof_", "._simp_", ".match_", "._cstage", "._closed_", "._rarg")


def _mask_lean_strings(text: str) -> str:
    """Replace contents of double-quoted Lean string literals with spaces, preserving newlines."""
    out: List[str] = []
    i = 0
    n = len(text)
    in_str = False
    while i < n:
        ch = text[i]
        if not in_str:
            if ch == '"':
                in_str = True
                out.append('"')
            else:
                out.append(ch)
            i += 1
        else:
            if ch == "\\" and i + 1 < n:
                out.append(" ")
                out.append("\n" if text[i + 1] == "\n" else " ")
                i += 2
            elif ch == '"':
                in_str = False
                out.append('"')
                i += 1
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
    return "".join(out)


def _build_line_offsets(text: str) -> List[int]:
    """Return 0-based char start offset of each line in `text`."""
    offs = [0]
    pos = text.find("\n")
    while pos >= 0:
        offs.append(pos + 1)
        pos = text.find("\n", pos + 1)
    return offs


def _offset_to_line(line_offsets: List[int], offset: int, base_line: int = 1) -> int:
    return base_line + max(0, bisect.bisect_right(line_offsets, offset) - 1)


def _count_ident_refs(ident: str, text: str) -> int:
    if not ident or ident == "_" or not text:
        return 0
    pat = rf"(?<![{_HYGIENE_IDENT_CONT}.]){re.escape(ident)}(?![{_HYGIENE_IDENT_CONT}])"
    return len(re.findall(pat, text))


def _compact_snippet(s: str, max_len: int = 100) -> str:
    flat = " ".join(s.split())
    if len(flat) <= max_len:
        return flat
    return flat[: max_len - 1].rstrip() + "…"


def _is_compiler_aux_name(name: str) -> bool:
    return any(m in name for m in _HYGIENE_AUX_MARKERS)


def _load_hygiene_file_data(
    abs_path: str,
    cache: Dict[str, Dict[str, Any]],
) -> Dict[str, Any]:
    hit = cache.get(abs_path)
    if hit is not None:
        return hit
    import sighash  # sibling module

    with open(abs_path, "r", encoding="utf-8", errors="replace") as f:
        raw_text = f.read()
    stripped_text = sighash.strip_comments(raw_text)
    masked_text = _mask_lean_strings(stripped_text)
    raw_lines = raw_text.split("\n")
    masked_lines = masked_text.split("\n")
    spans = _scan_enclosing_spans(raw_text)
    exact_map: Dict[str, int] = {}
    tail_map: Dict[str, List[int]] = collections.defaultdict(list)
    for d in sighash.iter_source_decls(raw_text, with_sig=False):
        nm = d.get("name")
        ln = int(d.get("line", 0))
        if nm and ln > 0:
            exact_map.setdefault(nm, ln)
            tail = nm.rsplit(".", 1)[-1]
            tail_map[tail].append(ln)
    data = {
        "raw_lines": raw_lines,
        "masked_lines": masked_lines,
        "spans": spans,
        "span_starts": [s[0] for s in spans],
        "exact_map": exact_map,
        "tail_map": dict(tail_map),
    }
    cache[abs_path] = data
    return data


def _extract_decl_source_span(
    abs_path: str,
    decl_name: str,
    file_cache: Dict[str, Dict[str, Any]],
) -> Optional[Dict[str, Any]]:
    """Locate `decl_name` in `abs_path` and parse its header, binders, type, and body."""
    fdata = _load_hygiene_file_data(abs_path, file_cache)
    raw_lines: List[str] = fdata["raw_lines"]
    masked_lines: List[str] = fdata["masked_lines"]
    spans: List[Tuple[int, str, Optional[str]]] = fdata["spans"]
    span_starts: List[int] = fdata["span_starts"]
    exact_map: Dict[str, int] = fdata["exact_map"]
    tail_map: Dict[str, List[int]] = fdata["tail_map"]

    lookup_name = decl_name
    if decl_name.startswith("_private."):
        parts = decl_name.split(".")
        for i in range(1, len(parts)):
            if parts[i] == "0" and i + 1 < len(parts):
                lookup_name = ".".join(parts[i + 1 :])
                break

    start_line: Optional[int] = exact_map.get(lookup_name)
    resolved_via_parent = False
    if start_line is None:
        for pref in _proper_prefixes(lookup_name):
            if pref in exact_map:
                start_line = exact_map[pref]
                resolved_via_parent = True
                break
    if start_line is None:
        tail = lookup_name.rsplit(".", 1)[-1]
        t_lines = tail_map.get(tail)
        if t_lines:
            start_line = t_lines[0]
    if start_line is None or start_line < 1 or start_line > len(masked_lines):
        return None

    # Find end line from the next top-level span after `start_line`
    next_idx = bisect.bisect_right(span_starts, start_line)
    end_line = (span_starts[next_idx] - 1) if next_idx < len(span_starts) else len(masked_lines)
    # Trim trailing top-level non-declaration commands / blank lines
    while end_line > start_line:
        ln_txt = masked_lines[end_line - 1]
        if not ln_txt.strip():
            end_line -= 1
            continue
        if not ln_txt[0].isspace() and _RE_TOPLEVEL_CMD_LINE.match(ln_txt):
            end_line -= 1
            continue
        break

    slice_masked = "\n".join(masked_lines[start_line - 1 : end_line])
    slice_raw = "\n".join(raw_lines[start_line - 1 : end_line])
    line_offsets = _build_line_offsets(slice_masked)

    m = _RE_HYGIENE_DECL_START.match(slice_masked)
    if not m:
        return None
    keyword = m.group(1)
    pos = m.end()
    n = len(slice_masked)
    # Skip optional `(priority := ...)` on `instance` or `inductive`/`abbrev` after `class`
    while pos < n and slice_masked[pos].isspace():
        pos += 1
    if keyword == "class" and slice_masked.startswith(("inductive ", "abbrev "), pos):
        pos = slice_masked.find(" ", pos) + 1
        while pos < n and slice_masked[pos].isspace():
            pos += 1
    if keyword == "instance" and pos < n and slice_masked[pos] == "(":
        depth_p = 1
        j = pos + 1
        while j < n and depth_p > 0:
            if slice_masked[j] == "(":
                depth_p += 1
            elif slice_masked[j] == ")":
                depth_p -= 1
            j += 1
        if depth_p == 0:
            pos = j
            while pos < n and slice_masked[pos].isspace():
                pos += 1

    # Skip declaration name (and optional universe params `.{u, v}`)
    name_start = pos
    while pos < n and not slice_masked[pos].isspace() and slice_masked[pos] not in ":({[⦃":
        pos += 1
    short_name = slice_masked[name_start:pos].strip()
    if pos < n and slice_masked[pos] == "{" and pos > name_start and slice_masked[pos - 1] == ".":
        close_u = slice_masked.find("}", pos + 1)
        if close_u >= 0:
            short_name = short_name[:-1]
            pos = close_u + 1

    # Scan header binders (before depth-0 `:`, `:=`, `where`, `extends`) and type/body split
    header_binders: List[Dict[str, Any]] = []
    type_start: Optional[int] = None
    type_end: Optional[int] = None
    body_start: Optional[int] = None
    body_kind: Optional[str] = None

    depth = 0
    binder_open_idx: Optional[int] = None
    binder_open_ch: str = ""
    i = pos
    while i < n:
        ch = slice_masked[i]
        if ch in _HYGIENE_OPEN:
            if depth == 0 and type_start is None:
                binder_open_idx = i
                binder_open_ch = ch
            depth += 1
            i += 1
            continue
        if ch in _HYGIENE_CLOSE:
            depth = max(0, depth - 1)
            if depth == 0 and type_start is None and binder_open_idx is not None:
                b_txt = slice_masked[binder_open_idx : i + 1]
                b_line = _offset_to_line(line_offsets, binder_open_idx, start_line)
                header_binders.extend(_parse_binder_group(b_txt, binder_open_ch, b_line))
                binder_open_idx = None
            i += 1
            continue
        if depth == 0:
            if slice_masked.startswith(":=", i):
                if type_start is not None and type_end is None:
                    type_end = i
                body_start = i + 2
                body_kind = ":="
                break
            if (
                slice_masked.startswith("where", i)
                and (i == 0 or not (slice_masked[i - 1].isalnum() or slice_masked[i - 1] in "_.'"))
                and (i + 5 >= n or not (slice_masked[i + 5].isalnum() or slice_masked[i + 5] in "_'"))
            ):
                if type_start is not None and type_end is None:
                    type_end = i
                body_start = i + 5
                body_kind = "where"
                break
            if ch == ":" and type_start is None:
                type_start = i + 1
                i += 1
                continue
        i += 1

    if type_start is not None and type_end is None:
        type_end = n
    type_expr = slice_masked[type_start:type_end].strip() if (type_start is not None and type_end is not None) else ""
    type_offset = type_start if type_start is not None else pos
    if type_start is not None:
        while type_offset < (type_end or n) and slice_masked[type_offset].isspace():
            type_offset += 1
    body_text = slice_masked[body_start:] if body_start is not None else ""
    body_offset = body_start if body_start is not None else n

    return {
        "start_line": start_line,
        "end_line": end_line,
        "resolved_via_parent": resolved_via_parent,
        "keyword": keyword,
        "short_name": short_name,
        "header_line": _clean_header_line(raw_lines[start_line - 1]),
        "slice_masked": slice_masked,
        "slice_raw": slice_raw,
        "line_offsets": line_offsets,
        "header_binders": header_binders,
        "type_expr": type_expr,
        "type_offset": type_offset,
        "body_text": body_text,
        "body_offset": body_offset,
        "body_kind": body_kind,
    }


def _find_depth0_colon(s: str) -> int:
    """Find first depth-0 `:` (not `:=`) inside a binder group."""
    depth = 0
    n = len(s)
    for i, ch in enumerate(s):
        if ch in _HYGIENE_OPEN:
            depth += 1
        elif ch in _HYGIENE_CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and ch == ":" and not s.startswith(":=", i):
            return i
    return -1


def _find_depth0_assign(s: str) -> int:
    depth = 0
    for i, ch in enumerate(s):
        if ch in _HYGIENE_OPEN:
            depth += 1
        elif ch in _HYGIENE_CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and s.startswith(":=", i):
            return i
    return -1


def _parse_binder_group(group_text: str, open_ch: str, line_no: int) -> List[Dict[str, Any]]:
    """Parse `(a b : T)` / `{a : T}` / `[Inst]` / `⦃a : T⦄` into binder dicts."""
    if len(group_text) < 2:
        return []
    inner = group_text[1:-1].strip()
    if not inner:
        return []
    if open_ch == "[":
        kind = "instance"
    elif open_ch == "{":
        kind = "implicit"
    elif open_ch == "⦃":
        kind = "strict_implicit"
    else:
        kind = "explicit"

    colon_idx = _find_depth0_colon(inner)
    if colon_idx < 0:
        if kind == "instance":
            return [{"name": None, "kind": "instance", "type": inner, "default": None, "line_no": line_no}]
        # Bare names without type annotation e.g. `(a b)` or `{α}`
        names = [tok for tok in inner.split() if tok == "_" or _RE_HYGIENE_IDENT.fullmatch(tok)]
        return [{"name": nm, "kind": kind, "type": "", "default": None, "line_no": line_no} for nm in names]

    lhs = inner[:colon_idx].strip()
    rhs = inner[colon_idx + 1 :].strip()
    default_val: Optional[str] = None
    asgn_idx = _find_depth0_assign(rhs)
    if asgn_idx >= 0:
        default_val = rhs[asgn_idx + 2 :].strip()
        rhs = rhs[:asgn_idx].strip()

    names = [tok for tok in lhs.split() if tok == "_" or _RE_HYGIENE_IDENT.fullmatch(tok)]
    if not names:
        if kind == "instance":
            return [{"name": None, "kind": "instance", "type": inner, "default": default_val, "line_no": line_no}]
        return []
    return [
        {"name": nm, "kind": kind, "type": rhs, "default": default_val, "line_no": line_no}
        for nm in names
    ]


def _is_ident_cont_ch(ch: str) -> bool:
    if not ch:
        return False
    return ch.isalnum() or ch in "_'" or ("\u2070" <= ch <= "\u209f")


def _at_quantifier_or_lambda(
    s: str,
    i: int,
    *,
    include_forall: bool = True,
    include_exists: bool = True,
    include_fun: bool = True,
) -> int:
    """Return keyword length (> 0) if `s[i:]` starts a quantifier/lambda binder keyword at a word boundary."""
    n = len(s)
    if i < 0 or i >= n:
        return 0
    ch = s[i]
    prev_ch = s[i - 1] if i > 0 else ""
    if include_forall:
        if ch == "∀" and not _is_ident_cont_ch(prev_ch):
            return 1
        if (
            ch == "f"
            and s.startswith("forall", i)
            and prev_ch != "."
            and not _is_ident_cont_ch(prev_ch)
            and (i + 6 >= n or not _is_ident_cont_ch(s[i + 6]))
        ):
            return 6
    if include_exists:
        if ch in ("∃", "Σ") and not _is_ident_cont_ch(prev_ch):
            return 1
        for kw in ("Exists", "Sigma", "PSigma"):
            klen = len(kw)
            if (
                ch == kw[0]
                and s.startswith(kw, i)
                and prev_ch != "."
                and not _is_ident_cont_ch(prev_ch)
                and (i + klen >= n or not _is_ident_cont_ch(s[i + klen]))
            ):
                return klen
    if include_fun:
        if ch == "λ" and not _is_ident_cont_ch(prev_ch):
            return 1
        if (
            ch == "f"
            and s.startswith("fun", i)
            and prev_ch != "."
            and not _is_ident_cont_ch(prev_ch)
            and (i + 3 >= n or not _is_ident_cont_ch(s[i + 3]))
        ):
            return 3
    return 0


def _find_quantifier_comma(s: str, start_idx: int) -> int:
    """Find the depth-0 `,` closing a quantifier header starting after `∀`/`∃`, matching inner quantifiers in `: T`."""
    n = len(s)
    j = start_idx
    depth = 0
    q_need = 1
    saw_colon = False
    while j < n:
        ch = s[j]
        if ch in _HYGIENE_OPEN:
            depth += 1
            j += 1
            continue
        if ch in _HYGIENE_CLOSE:
            depth = max(0, depth - 1)
            j += 1
            continue
        if depth == 0:
            if ch == ":" and not s.startswith(":=", j):
                saw_colon = True
            elif ch == ",":
                q_need -= 1
                if q_need <= 0:
                    return j
            elif saw_colon:
                kw_len = _at_quantifier_or_lambda(s, j, include_fun=False)
                if kw_len > 0:
                    q_need += 1
                    j += kw_len
                    continue
        j += 1
    return -1


def _count_exists_binder_vars(bpart: str) -> int:
    """Count number of existential witness variables bound in `∃ <bpart>,` (e.g. `∃ c e0 : ℕ,` -> 2)."""
    s = bpart.strip()
    if not s:
        return 1
    count = 0
    i = 0
    n = len(s)
    saw_bracketed = False
    while i < n and s[i].isspace():
        i += 1
    if i < n and s[i] in "({[⦃":
        depth = 0
        g_start: Optional[int] = None
        g_open = ""
        k = 0
        while k < n:
            ch = s[k]
            if ch in _HYGIENE_OPEN:
                if depth == 0:
                    g_start = k
                    g_open = ch
                    saw_bracketed = True
                depth += 1
            elif ch in _HYGIENE_CLOSE:
                depth = max(0, depth - 1)
                if depth == 0 and g_start is not None:
                    grp = s[g_start : k + 1]
                    parsed = _parse_binder_group(grp, g_open, 0)
                    count += max(1, len(parsed))
                    g_start = None
            k += 1
    if not saw_bracketed:
        cidx = _find_depth0_colon(s)
        if cidx >= 0:
            lhs = s[:cidx].strip()
            count = sum(1 for tok in lhs.split() if tok == "_" or _RE_HYGIENE_IDENT.fullmatch(tok))
        elif any(rel in s for rel in ("∈", "∉", "≤", "<", "≥", ">", "≠", "∣")):
            m_b = _RE_HYGIENE_IDENT.match(s)
            count = 1 if m_b else 1
        else:
            count = sum(1 for tok in s.split() if tok == "_" or _RE_HYGIENE_IDENT.fullmatch(tok))
    return max(1, count)


def _split_app_with_trailing_lambda(s: str) -> List[str]:
    """Like `_split_top_level_app_args`, keeping a trailing unparenthesized `fun`/`λ` arg as 1 token."""
    tokens: List[str] = []
    depth = 0
    start: Optional[int] = None
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if depth == 0 and start is None and len(tokens) >= 1:
            if _at_quantifier_or_lambda(s, i, include_forall=False, include_exists=False, include_fun=True) > 0:
                tokens.append(s[i:].strip())
                return tokens
        if ch in _HYGIENE_OPEN:
            if depth == 0 and start is None:
                start = i
            depth += 1
        elif ch in _HYGIENE_CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and ch.isspace():
            if start is not None:
                tokens.append(s[start:i])
                start = None
        else:
            if start is None:
                start = i
        i += 1
    if start is not None:
        tokens.append(s[start:])
    return tokens


def _extract_lambda_body(expr: str) -> Optional[str]:
    """Return the body after `=>` or `↦` for a `(fun ... => body)` / `fun ... ↦ body` term."""
    s = _strip_outer_parens(expr)
    kw_len = _at_quantifier_or_lambda(s, 0, include_forall=False, include_exists=False, include_fun=True)
    if kw_len <= 0:
        return None
    j = kw_len
    n = len(s)
    depth = 0
    while j < n:
        ch = s[j]
        if ch in _HYGIENE_OPEN:
            depth += 1
        elif ch in _HYGIENE_CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0:
            if s.startswith("=>", j):
                return s[j + 2 :].strip()
            if ch == "↦":
                return s[j + 1 :].strip()
        j += 1
    return None


def _parse_type_telescope(
    type_expr: str,
    type_offset: int,
    line_offsets: List[int],
    base_line: int,
) -> Tuple[List[Dict[str, Any]], str]:
    """Peel top-level `∀`/`forall` binders and `→`/`->` arrows from `type_expr`.

    Stops before `∃`/`Exists`/`Σ`/`fun`/`λ`/`↔` so existentials and lambdas are
    not swallowed as arrow slots. Returns `(slots, return_type)` where each slot
    has `{index, kind, name, type, line_no}`.
    """
    slots: List[Dict[str, Any]] = []
    s = type_expr
    cur_rel = 0
    n = len(s)

    while cur_rel < n:
        while cur_rel < n and s[cur_rel].isspace():
            cur_rel += 1
        if cur_rel >= n:
            break

        # Check for leading `∀` or `forall`
        is_forall = False
        after_kw = cur_rel
        kw_forall = _at_quantifier_or_lambda(s, cur_rel, include_forall=True, include_exists=False, include_fun=False)
        if kw_forall > 0:
            is_forall = True
            after_kw = cur_rel + kw_forall

        if is_forall:
            comma_pos = _find_quantifier_comma(s, after_kw)
            if comma_pos < 0:
                break
            bpart = s[after_kw:comma_pos]
            # Only treat as bracketed binder groups when `bpart` begins with `(`/etc., not `∀ x : F (A ⊕ B),`
            parsed_groups: List[Dict[str, Any]] = []
            saw_bracketed = False
            if bpart.lstrip().startswith(("(", "{", "[", "⦃")):
                k = 0
                bn = len(bpart)
                b_depth = 0
                g_start: Optional[int] = None
                g_open = ""
                while k < bn:
                    ch = bpart[k]
                    if ch in _HYGIENE_OPEN:
                        if b_depth == 0:
                            g_start = k
                            g_open = ch
                            saw_bracketed = True
                        b_depth += 1
                    elif ch in _HYGIENE_CLOSE:
                        b_depth = max(0, b_depth - 1)
                        if b_depth == 0 and g_start is not None:
                            bline = _offset_to_line(line_offsets, type_offset + after_kw + g_start, base_line)
                            parsed_groups.extend(_parse_binder_group(bpart[g_start : k + 1], g_open, bline))
                            g_start = None
                    k += 1
            if not saw_bracketed:
                # Bare `∀ x : T, ...` or `∀ x ∈ S, ...` or `∀ x y, ...`
                bline = _offset_to_line(line_offsets, type_offset + after_kw, base_line)
                b_strip = bpart.strip()
                cidx = _find_depth0_colon(b_strip)
                if cidx >= 0:
                    lhs_nms = [t for t in b_strip[:cidx].split() if t == "_" or _RE_HYGIENE_IDENT.fullmatch(t)]
                    rhs_ty = b_strip[cidx + 1 :].strip()
                    for nm in lhs_nms:
                        parsed_groups.append({"name": nm, "kind": "explicit", "type": rhs_ty, "line_no": bline})
                elif "∈" in b_strip or "≤" in b_strip or "<" in b_strip or "≥" in b_strip or ">" in b_strip:
                    # Bounded quantifier `∀ x ∈ S, ...` introduces 2 arguments: `x` and proof `x ∈ S`
                    m_b = _RE_HYGIENE_IDENT.match(b_strip)
                    if m_b:
                        parsed_groups.append({"name": m_b.group(0), "kind": "explicit", "type": "", "line_no": bline})
                        parsed_groups.append({"name": None, "kind": "arrow", "type": b_strip, "line_no": bline})
                else:
                    for tok in b_strip.split():
                        if tok == "_" or _RE_HYGIENE_IDENT.fullmatch(tok):
                            parsed_groups.append({"name": tok, "kind": "explicit", "type": "", "line_no": bline})
            for g in parsed_groups:
                slots.append({
                    "index": len(slots),
                    "kind": g["kind"],
                    "name": g["name"],
                    "type": g["type"],
                    "line_no": g["line_no"],
                })
            cur_rel = comma_pos + 1
            continue

        # Stop immediately if remaining type begins with `∃`/`Exists`/`Σ`/`fun`/`λ`
        if _at_quantifier_or_lambda(s, cur_rel, include_forall=False) > 0:
            break

        # Look for top-level `→` or `->` at depth 0, stopping at unparenthesized quantifiers/lambdas/`↔`
        depth = 0
        arrow_pos = -1
        arrow_len = 0
        hit_quant_or_iff = False
        j = cur_rel
        while j < n:
            ch = s[j]
            if ch in _HYGIENE_OPEN:
                depth += 1
            elif ch in _HYGIENE_CLOSE:
                depth = max(0, depth - 1)
            elif depth == 0:
                if _at_quantifier_or_lambda(s, j) > 0 or ch == "↔":
                    hit_quant_or_iff = True
                    break
                if ch == "→":
                    arrow_pos = j
                    arrow_len = 1
                    break
                if s.startswith("->", j):
                    arrow_pos = j
                    arrow_len = 2
                    break
            j += 1
        if hit_quant_or_iff:
            break
        if arrow_pos >= 0:
            lhs = s[cur_rel:arrow_pos].strip()
            line_no = _offset_to_line(line_offsets, type_offset + cur_rel, base_line)
            slots.append({
                "index": len(slots),
                "kind": "arrow",
                "name": None,
                "type": lhs,
                "line_no": line_no,
            })
            cur_rel = arrow_pos + arrow_len
            continue
        break

    return slots, s[cur_rel:].strip()


def _strip_outer_parens(s: str) -> str:
    s = s.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        depth = 0
        matched_end = False
        for i, ch in enumerate(s):
            if ch in _HYGIENE_OPEN:
                depth += 1
            elif ch in _HYGIENE_CLOSE:
                depth -= 1
                if depth == 0:
                    matched_end = (i == len(s) - 1)
                    break
        if matched_end:
            s = s[1:-1].strip()
        else:
            break
    return s


def _split_depth0_op(s: str, op: str, *, stop_at_quantifier: bool = False) -> List[str]:
    parts: List[str] = []
    depth = 0
    start = 0
    i = 0
    n = len(s)
    olen = len(op)
    while i < n:
        ch = s[i]
        if ch in _HYGIENE_OPEN:
            depth += 1
            i += 1
            continue
        if ch in _HYGIENE_CLOSE:
            depth = max(0, depth - 1)
            i += 1
            continue
        if depth == 0:
            if stop_at_quantifier and _at_quantifier_or_lambda(s, i, include_forall=True, include_exists=True, include_fun=False) > 0:
                break
            if s.startswith(op, i):
                parts.append(s[start:i].strip())
                i += olen
                start = i
                continue
        i += 1
    parts.append(s[start:].strip())
    return [p for p in parts if p]


def _split_top_level_app_args(s: str) -> List[str]:
    """Split `Head arg1 arg2 ...` at depth-0 whitespace."""
    tokens: List[str] = []
    depth = 0
    start: Optional[int] = None
    for i, ch in enumerate(s):
        if ch in _HYGIENE_OPEN:
            if depth == 0 and start is None:
                start = i
            depth += 1
        elif ch in _HYGIENE_CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and ch.isspace():
            if start is not None:
                tokens.append(s[start:i])
                start = None
        else:
            if start is None:
                start = i
    if start is not None:
        tokens.append(s[start:])
    return tokens


def _split_conjuncts(return_type: str) -> Tuple[Optional[str], List[str], int]:
    """Detect whether `return_type` (after peeling outer `∃`/`∀`/`→`) is a 2+ conjunct `And`/`Prod`.

    Returns `(tuple_kind_or_None, legs, exists_depth)`.
    """
    cur = _strip_outer_parens(return_type)
    exists_depth = 0
    for _ in range(24):
        if not cur:
            return None, [], exists_depth
        # Peel leading `∃ ...,` / `Σ ...,` / `∀ ...,` FIRST because in Lean 4 quantifiers have lower
        # precedence than `∧` (`∃ x, P ∧ Q` parses as `∃ x, (P ∧ Q)`, whereas `(∃ x, P) ∧ Q`
        # starts with `(` and will NOT match here).
        kw_ex = _at_quantifier_or_lambda(cur, 0, include_forall=False, include_exists=True, include_fun=False)
        if kw_ex > 0:
            comma = _find_quantifier_comma(cur, kw_ex)
            if comma >= 0:
                exists_depth += _count_exists_binder_vars(cur[kw_ex:comma])
                cur = _strip_outer_parens(cur[comma + 1 :])
                continue
        kw_all = _at_quantifier_or_lambda(cur, 0, include_forall=True, include_exists=False, include_fun=False)
        if kw_all > 0:
            comma = _find_quantifier_comma(cur, kw_all)
            if comma >= 0:
                cur = _strip_outer_parens(cur[comma + 1 :])
                continue

        # `↔` binds looser than `→` and `∧`; do not split across `↔`
        if len(_split_depth0_op(cur, "↔", stop_at_quantifier=True)) >= 2:
            return None, [], exists_depth

        # Check depth-0 `→` before `∧` ONLY if `→` is actually present outside quantifiers
        arrow_parts = _split_depth0_op(cur, "→", stop_at_quantifier=True)
        if len(arrow_parts) >= 2:
            if (
                len(_split_depth0_op(arrow_parts[0], "∧", stop_at_quantifier=True)) < 2
                and len(_split_depth0_op(arrow_parts[0], "×", stop_at_quantifier=True)) < 2
            ):
                cur = _strip_outer_parens(" → ".join(arrow_parts[1:]))
                continue
            return None, [], exists_depth

        # Check depth-0 `∧` (stopping before unparenthesized quantifiers on RHS like `1 ≤ c ∧ ∀ e ≥ e0, ...`)
        and_parts = _split_depth0_op(cur, "∧", stop_at_quantifier=True)
        if len(and_parts) >= 2:
            return "And", and_parts, exists_depth
        # Check depth-0 `×`
        prod_parts = _split_depth0_op(cur, "×", stop_at_quantifier=True)
        if len(prod_parts) >= 2:
            return "Prod", prod_parts, exists_depth
        # Check prefix `And A B` / `Prod A B` / `PProd A B`
        app_toks = _split_top_level_app_args(cur)
        if len(app_toks) == 3 and app_toks[0] in ("And", "Prod", "PProd"):
            head = app_toks[0]
            legs = [_strip_outer_parens(app_toks[1])]
            rhs = _strip_outer_parens(app_toks[2])
            # Flatten right-nested `And A (And B C)`
            while True:
                sub = _split_top_level_app_args(rhs)
                if len(sub) == 3 and sub[0] == head:
                    legs.append(_strip_outer_parens(sub[1]))
                    rhs = _strip_outer_parens(sub[2])
                else:
                    legs.append(rhs)
                    break
            return head, legs, exists_depth
        break
    return None, [], exists_depth


def _parse_intro_tokens(clause: str) -> List[Tuple[str, bool]]:
    """Parse tokens from an `intro` / `intros` clause.

    Returns list of `(token_name, is_pattern)` where `is_pattern=True` marks destructured
    `⟨...⟩` patterns (counted as 1 telescope slot, not individual wildcards).
    """
    out: List[Tuple[str, bool]] = []
    i = 0
    n = len(clause)
    while i < n:
        while i < n and clause[i].isspace():
            i += 1
        if i >= n:
            break
        if clause[i] in ";·|" or clause.startswith("<;>", i) or clause.startswith("=>", i) or clause.startswith(":=", i):
            break
        if clause[i] in "⟨({[":
            open_ch = clause[i]
            depth = 1
            j = i + 1
            while j < n and depth > 0:
                if clause[j] in _HYGIENE_OPEN:
                    depth += 1
                elif clause[j] in _HYGIENE_CLOSE:
                    depth -= 1
                j += 1
            grp = clause[i:j]
            if open_ch == "(" and ":" in grp:
                b = _parse_binder_group(grp, "(", 0)
                if b:
                    for item in b:
                        out.append((item["name"] or "_", False))
                else:
                    out.append((grp, True))
            else:
                out.append((grp, True))
            i = j
            continue
        m = _RE_HYGIENE_IDENT.match(clause, i)
        if m:
            tok = m.group(0)
            if tok in _HYGIENE_STOP_WORDS and tok not in ("_",):
                break
            out.append((tok, False))
            i = m.end()
            continue
        # Unknown punctuation ends intro token list
        break
    return out


def _iter_fun_binders(body: str, body_offset: int, line_offsets: List[int], base_line: int) -> Iterable[Dict[str, Any]]:
    """Yield `{start, end, line_no, binders: [(name, kind)], binder_types, lambda_body}` for `fun ... =>` / `λ ... =>`."""
    pat = re.compile(rf"(?<![{_HYGIENE_IDENT_CONT}.])(?:fun|λ)(?![{_HYGIENE_IDENT_CONT}])")
    n = len(body)
    for m in pat.finditer(body):
        pos = m.end()
        # Scan until depth-0 `=>` (bounded to keep scanning crisp and avoid `fun | ... =>` misfires)
        depth = 0
        arrow = -1
        j = pos
        nl_count = 0
        while j < n and nl_count <= 4:
            ch = body[j]
            if ch == "\n":
                nl_count += 1
            if ch in _HYGIENE_OPEN:
                depth += 1
            elif ch in _HYGIENE_CLOSE:
                depth = max(0, depth - 1)
            elif depth == 0:
                if body.startswith("=>", j):
                    arrow = j
                    arrow_len = 2
                    break
                if ch == "↦":
                    arrow = j
                    arrow_len = 1
                    break
                if ch == "|" or body.startswith(":=", j):
                    break
            j += 1
        if arrow < 0:
            continue
        bstr = body[pos:arrow].strip()
        if not bstr:
            continue
        # Parse binder tokens inside `bstr`
        binders: List[Tuple[str, str]] = []
        binder_types: List[str] = []
        k = 0
        bn = len(bstr)
        ok = True
        while k < bn:
            while k < bn and bstr[k].isspace():
                k += 1
            if k >= bn:
                break
            ch = bstr[k]
            if ch in _HYGIENE_OPEN:
                gdepth = 1
                g = k + 1
                while g < bn and gdepth > 0:
                    if bstr[g] in _HYGIENE_OPEN:
                        gdepth += 1
                    elif bstr[g] in _HYGIENE_CLOSE:
                        gdepth -= 1
                    g += 1
                if gdepth != 0:
                    ok = False
                    break
                if ch == "⟨":
                    binders.append((bstr[k:g], "pattern"))
                    binder_types.append("")
                else:
                    for item in _parse_binder_group(bstr[k:g], ch, 0):
                        binders.append((item["name"] or "_", item["kind"]))
                        binder_types.append(item.get("type", ""))
                k = g
                continue
            im = _RE_HYGIENE_IDENT.match(bstr, k)
            if im:
                binders.append((im.group(0), "explicit"))
                binder_types.append("")
                k = im.end()
                continue
            ok = False
            break
        if not ok or not binders:
            continue
        yield {
            "start": m.start(),
            "end": arrow + arrow_len,
            "line_no": _offset_to_line(line_offsets, body_offset + m.start(), base_line),
            "binders": binders,
            "binder_types": binder_types,
            "raw_binders": bstr,
            "lambda_body": body[arrow + arrow_len :],
        }


def _collect_inner_telescopes(
    span: Dict[str, Any],
    extra_spans: Sequence[Dict[str, Any]] = (),
) -> List[List[Dict[str, Any]]]:
    """Extract inner `∀` / `forall` binder telescopes from a decl's type, body, and expanded DefProps."""
    telescopes: List[List[Dict[str, Any]]] = []
    seen_keys: Set[Tuple[Tuple[Optional[str], str], ...]] = set()
    sources: List[Tuple[str, int, List[int], int]] = [
        (span["type_expr"], span["type_offset"], span["line_offsets"], span["start_line"]),
        (span["body_text"], span["body_offset"], span["line_offsets"], span["start_line"]),
    ]
    for esp in extra_spans:
        sources.append((esp["body_text"], esp["body_offset"], esp["line_offsets"], esp["start_line"]))
        if esp.get("type_expr"):
            sources.append((esp["type_expr"], esp["type_offset"], esp["line_offsets"], esp["start_line"]))

    pat = re.compile(rf"∀|(?<![{_HYGIENE_IDENT_CONT}.])forall(?![{_HYGIENE_IDENT_CONT}])")
    for text, base_off, loffs, bline in sources:
        if not text:
            continue
        for m in pat.finditer(text):
            slots, _ret = _parse_type_telescope(text[m.start() :], base_off + m.start(), loffs, bline)
            if not slots:
                continue
            sig_key = tuple((sl.get("name"), sl["kind"]) for sl in slots[:24])
            if sig_key not in seen_keys:
                seen_keys.add(sig_key)
                telescopes.append(slots)
    return telescopes


def _match_inner_telescope(
    toks: Sequence[Tuple[str, bool]],
    inner_telescopes: Sequence[List[Dict[str, Any]]],
) -> Optional[List[Dict[str, Any]]]:
    """Match an `intro`/`fun` binder token sequence against a known inner `∀` telescope slice."""
    if not toks or not inner_telescopes:
        return None
    best: Optional[Tuple[int, List[Dict[str, Any]]]] = None
    nt = len(toks)
    for slots in inner_telescopes:
        if len(slots) < nt:
            continue
        max_off = len(slots) - nt
        for off in range(min(max_off + 1, 8)):
            sub = slots[off : off + nt]
            score = 0
            saw_inst = False
            for i, (tok, is_pat) in enumerate(toks):
                sk = sub[i]["kind"]
                sname = sub[i].get("name")
                if is_pat:
                    continue
                if tok == "_":
                    if sk == "instance":
                        score += 2
                        saw_inst = True
                else:
                    if sname and tok == sname:
                        score += 3
                    elif sname and sk == "explicit" and tok[0].isupper() == sname[0].isupper():
                        score += 1
            if saw_inst and score >= 4:
                if best is None or score > best[0]:
                    best = (score, sub)
    return best[1] if best is not None else None


def _expand_def_telescope(
    conn: sqlite3.Connection,
    did: int,
    initial_slots: List[Dict[str, Any]],
    return_type: str,
    *,
    has_dm: bool,
    sroot: str,
    src_fallback: Dict[str, Tuple[str, int]],
    file_cache: Dict[str, Dict[str, Any]],
    def_edge_cache: Dict[int, List[Tuple[int, str, Optional[str]]]],
    max_hops: int = 8,
) -> Tuple[List[Dict[str, Any]], str, List[Dict[str, Any]]]:
    """Expand Prop/Type-`def`/`abbrev` return types (up to `max_hops`) into the active `intro`/`fun` telescope."""
    slots = list(initial_slots)
    cur_did = did
    cur_ret = return_type
    extra_spans: List[Dict[str, Any]] = []
    visited: Set[int] = {did}

    def _get_def_deps(src_id: int, include_val: bool) -> List[Tuple[int, str, Optional[str]]]:
        ckey = src_id if include_val else -src_id
        if ckey in def_edge_cache:
            return def_edge_cache[ckey]
        k_clause = "e.kind IN (1, 2, 3)" if include_val else "e.kind IN (1, 3)"
        if has_dm:
            rows = conn.execute(
                f"SELECT d.id, d.name, m.module "
                f"FROM edges e JOIN decls d ON d.id = e.dst "
                f"LEFT JOIN decl_module m ON m.decl_id = d.id "
                f"WHERE e.src = ? AND {k_clause} AND d.kind = 'def'",
                (src_id,),
            ).fetchall()
        else:
            rows = [
                (r[0], r[1], None)
                for r in conn.execute(
                    f"SELECT d.id, d.name FROM edges e JOIN decls d ON d.id = e.dst "
                    f"WHERE e.src = ? AND {k_clause} AND d.kind = 'def'",
                    (src_id,),
                ).fetchall()
            ]
        out: List[Tuple[int, str, Optional[str]]] = []
        for cid, cnm, cmod in rows:
            cnm_s = str(cnm)
            rmod = cmod or (src_fallback[cnm_s][0] if cnm_s in src_fallback else None)
            if rmod:
                out.append((int(cid), cnm_s, str(rmod)))
        def_edge_cache[ckey] = out
        return out

    sort_or_prop_re = re.compile(
        r"^(?:Prop|Type(?:\s*\*|\s+\S+|\.\{[^}]*\})?|Sort(?:\s*\*|\s+\S+|\.\{[^}]*\})?)$"
    )

    for hop in range(max_hops):
        cand_expr = _strip_outer_parens(cur_ret)
        if not cand_expr:
            break
        # Peel any newly exposed `∀`/`→` before matching the head `def`
        if cand_expr.startswith(("∀", "forall")):
            more_slots, cand_ret = _parse_type_telescope(cand_expr, 0, [0], 1)
            if more_slots:
                for sl in more_slots:
                    nsl = dict(sl)
                    nsl["index"] = len(slots)
                    slots.append(nsl)
                cur_ret = cand_ret
                cand_expr = _strip_outer_parens(cur_ret)

        app_toks = _split_app_with_trailing_lambda(cand_expr)
        if not app_toks:
            break
        raw_head = app_toks[0]
        is_at_app = raw_head.startswith("@")
        head = raw_head.lstrip("@")
        head = re.sub(r"\.\{[^}]*\}$", "", head)
        if head.startswith("_root_."):
            head = head[7:]
        if not head or head in ("∀", "forall", "∃", "Exists", "And", "Prod", "PProd", "True", "False"):
            break

        cands = _get_def_deps(cur_did, include_val=(hop > 0))
        matched: Optional[Tuple[int, str, Optional[str]]] = None
        exact_hits = [c for c in cands if c[1] == head]
        if len(exact_hits) == 1:
            matched = exact_hits[0]
        else:
            suf_hits = [c for c in cands if c[1].endswith("." + head)]
            if len(suf_hits) == 1:
                matched = suf_hits[0]
            else:
                tail_h = head.rsplit(".", 1)[-1]
                tail_hits = [c for c in cands if c[1] == tail_h or c[1].endswith("." + tail_h)]
                if len(tail_hits) == 1:
                    matched = tail_hits[0]
        if matched is None:
            break

        m_id, m_name, m_mod = matched
        if m_id in visited or not m_mod:
            break
        visited.add(m_id)
        rel = m_mod.replace(".", os.sep) + ".lean"
        dpath, _err = _safe_resolve_src_path(sroot, rel)
        if dpath is None:
            break
        dspan = _extract_decl_source_span(dpath, m_name, file_cache)
        if dspan is None or dspan["keyword"] not in ("def", "abbrev"):
            break
        dspan["decl_id"] = m_id
        extra_spans.append(dspan)
        dbody = dspan["body_text"]
        if not dbody.strip():
            break
        sub_slots: List[Dict[str, Any]] = []
        hbs = dspan.get("header_binders") or []
        if len(app_toks) == 1 and hbs:
            sub_slots.extend(dict(hb) for hb in hbs)
        body_slots, next_ret = _parse_type_telescope(dbody, dspan["body_offset"], dspan["line_offsets"], dspan["start_line"])
        sub_slots.extend(body_slots)
        # Beta-reduce higher-order `DefProp fun ... ↦ body` combinators (e.g. `AllFin fun R _ _ _ F ↦ ...`)
        app_args = app_toks[1:]
        if app_args and hbs:
            pos_hbs = list(hbs) if is_at_app else [hb for hb in hbs if hb.get("kind") == "explicit"]
            nr_toks = _split_top_level_app_args(_strip_outer_parens(next_ret))
            nr_head = nr_toks[0].lstrip("@") if nr_toks else ""
            for a_idx, hb in enumerate(pos_hbs):
                if a_idx >= len(app_args):
                    break
                hb_nm = hb.get("name")
                if hb_nm and hb_nm == nr_head:
                    lam_body = _extract_lambda_body(app_args[a_idx])
                    if lam_body:
                        next_ret = lam_body
                        break
        texpr_flat = " ".join(_strip_outer_parens(dspan["type_expr"]).split())
        if not sub_slots and texpr_flat and not sort_or_prop_re.fullmatch(texpr_flat):
            tslots, tret = _parse_type_telescope(
                dspan["type_expr"], dspan["type_offset"], dspan["line_offsets"], dspan["start_line"]
            )
            if len(app_toks) - 1 < len(tslots):
                sub_slots = tslots[max(0, len(app_toks) - 1) :]
                next_ret = tret
        if sub_slots:
            for sl in sub_slots:
                nsl = dict(sl)
                nsl["index"] = len(slots)
                slots.append(nsl)
        cur_did = m_id
        if next_ret == cur_ret and not sub_slots:
            break
        cur_ret = next_ret

    # Peel any final `∀` exposed after the last hop (e.g. from higher-order `fun ... ↦ ∀ ...`)
    final_cand = _strip_outer_parens(cur_ret)
    if final_cand.startswith(("∀", "forall")):
        more_slots, final_ret = _parse_type_telescope(final_cand, 0, [0], 1)
        if more_slots:
            for sl in more_slots:
                nsl = dict(sl)
                nsl["index"] = len(slots)
                slots.append(nsl)
            cur_ret = final_ret

    return slots, cur_ret, extra_spans


def _is_heuristic_instance_token(
    tokens: Sequence[Tuple[str, str]],
    idx: int,
    binder_types: Optional[Sequence[str]] = None,
    *,
    allow_single_lower_run: bool = False,
) -> bool:
    """Detect unexpanded `[Inst]` wildcards like `{Ω} _ _`, `(E : Type) _ _ _`, or `E _ _ _`."""
    if idx < 0 or idx >= len(tokens):
        return False
    nm, kd = tokens[idx]
    if nm != "_":
        return False
    if kd in ("instance", "implicit", "strict_implicit"):
        return True
    # Measure contiguous `_` run containing `idx`
    rstart = idx
    while rstart > 0 and tokens[rstart - 1][0] == "_":
        rstart -= 1
    rend = idx
    while rend + 1 < len(tokens) and tokens[rend + 1][0] == "_":
        rend += 1
    run_len = rend - rstart + 1
    if rstart <= 0:
        return False
    prev_nm, prev_kd = tokens[rstart - 1]
    if prev_kd in ("implicit", "strict_implicit") or prev_nm.startswith(("{", "⦃")):
        return True
    if binder_types and rstart - 1 < len(binder_types):
        pty = binder_types[rstart - 1].strip()
        if pty in ("Type", "Type*", "Sort*") or pty.startswith(("Type ", "Type*", "Sort ")):
            return True
    if _RE_UPPERCASE_SHORT.fullmatch(prev_nm) and run_len >= 2:
        return True
    if allow_single_lower_run and len(prev_nm) == 1 and prev_nm.isalpha() and run_len >= 2:
        return True
    return False


def _classify_nested_fun_noise(
    fitem: Dict[str, Any],
    body: str,
    inner_telescopes: Sequence[List[Dict[str, Any]]],
) -> Tuple[Optional[str], int, List[str]]:
    """Classify nested `fun ... =>` wildcards, filtering `[Inst]`, `Finset`/set membership, and combinators."""
    binders: List[Tuple[str, str]] = fitem["binders"]
    btypes: List[str] = fitem.get("binder_types") or [""] * len(binders)
    matched_inner = _match_inner_telescope([(bn, bk == "pattern") for bn, bk in binders], inner_telescopes)
    non_inst_indices: List[int] = []
    inst_suppressed = 0
    for idx, (bn, bk) in enumerate(binders):
        if bn != "_" or bk in ("instance", "pattern"):
            continue
        if matched_inner is not None and idx < len(matched_inner) and matched_inner[idx]["kind"] == "instance":
            continue
        if _is_heuristic_instance_token(binders, idx, btypes, allow_single_lower_run=True):
            inst_suppressed += 1
            continue
        non_inst_indices.append(idx)

    if not non_inst_indices:
        if inst_suppressed > 0:
            return "instance_wildcard", inst_suppressed, [str(i) for i in range(len(binders)) if binders[i][0] == "_"]
        return None, 0, []

    raw_pre = body[max(0, fitem["start"] - 240) : fitem["start"]]
    stmt_starts = list(
        re.finditer(
            r"(?:^|\n)[ \t]{0,6}(?:·\s*)?(?:have|haveI|let|set|obtain|rcases|refine|exact|apply|intro|rw|simp|calc)\b",
            raw_pre,
        )
    )
    pre = raw_pre[stmt_starts[-1].start() :] if stmt_starts else body[max(0, fitem["start"] - 120) : fitem["start"]]
    lbody_head = fitem["lambda_body"].lstrip()[:90]
    pos_labels = [f"#{i}" for i in non_inst_indices]

    if re.search(r"(?:Finset|Multiset|Set|List|Filter|DFinsupp|MeasureTheory)\.|∑|∏|\bfinsum_|\bmem_|∀\s+\S+\s+∈\b", pre):
        return "membership_lambda", len(non_inst_indices), pos_labels
    if _RE_COMBINATOR_PREFIX.search(pre):
        return "combinator_lambda", len(non_inst_indices), pos_labels
    if re.match(
        r"^(?:⟨|\(?\s*(?:0|1|rfl|inferInstance|True|trivial|one_ne_zero|riemannZeta_one_ne_zero)(?![A-Za-z0-9_])"
        r"|by\s+(?:positivity|ring|simp|rfl)|sq_nonneg|norm_nonneg|Real\.exp|Finset\.mem_union"
        r"|[A-Za-z_][A-Za-z0-9_']*(?:\.(?:1|2|left|right|fst|snd|down|up))+)",
        lbody_head,
    ):
        return "combinator_lambda", len(non_inst_indices), pos_labels
    if len(non_inst_indices) >= 4 and (lbody_head.startswith(("⟨", "?_")) or pre.rstrip().endswith("(")):
        return "combinator_lambda", len(non_inst_indices), pos_labels
    if re.search(r"\brefine\s+⟨[^⟨⟩\n]*,\s*(?:[^,\n]*,\s*)?$", pre) and re.match(r"^\?_(?:\s|$|⟩|,|\))", lbody_head):
        return "combinator_lambda", len(non_inst_indices), pos_labels
    # Explicit 2-arg membership pattern `fun c _ => ...` inside `.sum`/`.prod`/collection helper
    if len(binders) == 2 and binders[0][0] != "_" and binders[1][0] == "_" and re.search(
        r"(?:\.sum|\.prod|\.filter|\.image|\.sep|\.map|\.congr|\.single_le|\ball\b|\bball\b)", pre
    ):
        return "membership_lambda", len(non_inst_indices), pos_labels

    return None, len(non_inst_indices), pos_labels


def _extract_balanced_angle(s: str, open_idx: int) -> Optional[Tuple[str, int]]:
    """Return `(inner_text, close_end_idx)` for balanced `⟨...⟩` starting at `open_idx`."""
    if open_idx < 0 or open_idx >= len(s) or s[open_idx] != "⟨":
        return None
    depth = 0
    for j in range(open_idx, len(s)):
        ch = s[j]
        if ch in _HYGIENE_OPEN:
            depth += 1
        elif ch in _HYGIENE_CLOSE:
            depth -= 1
            if depth == 0 and ch == "⟩":
                return s[open_idx + 1 : j], j + 1
    return None


def _is_obtain_inst_run(items: Sequence[str], idx: int, has_infer_inst: bool) -> bool:
    """Detect Lean `[Inst]` witnesses destructured as `⟨O', _, ..., ζ⟩` or `⟨B, _, P⟩` with `inferInstance`."""
    if idx <= 0 or idx >= len(items) or items[idx].strip() != "_":
        return False
    rstart = idx
    while rstart > 0 and items[rstart - 1].strip() == "_":
        rstart -= 1
    rend = idx
    while rend + 1 < len(items) and items[rend + 1].strip() == "_":
        rend += 1
    run_len = rend - rstart + 1
    if rstart <= 0:
        return False
    prev_tok = items[rstart - 1].strip()
    if re.fullmatch(r"[A-ZΑ-Ω][A-Za-z0-9_'₀-₉₁-₉]{0,4}", prev_tok):
        if run_len >= 2:
            return True
        if has_infer_inst and (len(prev_tok) <= 2 or prev_tok.endswith("'")):
            return True
    return False


def _audit_dropped_binders(
    span: Dict[str, Any],
    telescope: List[Dict[str, Any]],
    *,
    inner_telescopes: Sequence[List[Dict[str, Any]]] = (),
    is_class_type: Optional[Callable[[str], bool]] = None,
) -> List[Dict[str, Any]]:
    """Heuristic source audit for dropped/unused binders (`_`, `_h`, `intro _`, `fun _ =>`, `obtain ⟨a, _, b⟩`)."""
    findings: List[Dict[str, Any]] = []
    keyword = span["keyword"]
    body = span["body_text"]
    body_offset = span["body_offset"]
    line_offsets = span["line_offsets"]
    base_line = span["start_line"]
    type_expr = span["type_expr"]
    header_binders = span["header_binders"]

    if keyword in ("axiom", "opaque", "structure", "class", "inductive") or not body.strip():
        return findings

    has_implicit_tactic = _RE_IMPLICIT_CTX_TACTIC.search(body) is not None

    # 1. Header parameter binders
    for idx, b in enumerate(header_binders):
        bname = b.get("name")
        bkind = b.get("kind")
        btype = b.get("type", "")
        bline = b.get("line_no", base_line)
        if bkind == "instance" or bname is None:
            continue
        is_cls = bool(is_class_type is not None and btype and is_class_type(btype))
        if bname == "_":
            if bkind == "explicit":
                item: Dict[str, Any] = {
                    "category": "dropped",
                    "kind": "explicit_wildcard_binder",
                    "confidence": "heuristic_source",
                    "line_no": bline,
                    "binder": "_",
                    "binder_index": idx,
                    "binder_pos": f"header #{idx}",
                    "param_type": _compact_snippet(btype, 110) if btype else None,
                    "detail": f"explicit wildcard binder `(_ : {_compact_snippet(btype, 80)})`",
                }
                if is_cls:
                    item["suppression_reason"] = "local_class_instance"
                findings.append(item)
            continue
        refs_body = _count_ident_refs(bname, body)
        if refs_body > 0:
            continue
        later_sig = " ".join(hb.get("type", "") for hb in header_binders[idx + 1 :]) + " " + type_expr
        refs_sig = _count_ident_refs(bname, later_sig)
        if bname.startswith("_"):
            if refs_sig == 0:
                item = {
                    "category": "dropped",
                    "kind": "unused_underscore_binder",
                    "confidence": "heuristic_source",
                    "line_no": bline,
                    "binder": bname,
                    "binder_index": idx,
                    "binder_pos": f"header #{idx} ({bname})",
                    "param_type": _compact_snippet(btype, 110) if btype else None,
                    "implicit_tactic_in_body": has_implicit_tactic,
                    "detail": f"underscore binder `{bname}` has 0 references in body",
                }
                if is_cls:
                    item["suppression_reason"] = "local_class_instance"
                elif has_implicit_tactic:
                    item["suppression_reason"] = "implicit_ctx_tactic"
                findings.append(item)
        elif bkind == "explicit" and refs_sig == 0:
            item = {
                "category": "dropped",
                "kind": "unused_named_binder",
                "confidence": "heuristic_source",
                "line_no": bline,
                "binder": bname,
                "binder_index": idx,
                "binder_pos": f"header #{idx} ({bname})",
                "param_type": _compact_snippet(btype, 110) if btype else None,
                "implicit_tactic_in_body": has_implicit_tactic,
                "detail": f"named binder `{bname}` has 0 references in signature or body",
            }
            if is_cls:
                item["suppression_reason"] = "local_class_instance"
            elif has_implicit_tactic:
                item["suppression_reason"] = "implicit_ctx_tactic"
            findings.append(item)

    def _slot_referenced_later(slot_idx: int, slot_name: Optional[str]) -> bool:
        if not slot_name or slot_name == "_":
            return False
        later_txt = " ".join(sl.get("type", "") for sl in telescope[slot_idx + 1 :])
        if _count_ident_refs(slot_name, later_txt) > 0:
            return True
        ret_start = span["type_expr"]
        _slots_unused, ret_ty = _parse_type_telescope(ret_start, span["type_offset"], line_offsets, base_line)
        return _count_ident_refs(slot_name, ret_ty) > 0

    def _binder_pos_label(toks_seq: Sequence[Tuple[str, str]], tok_idx: int, slot: Optional[Dict[str, Any]], cur_slot_idx: int) -> Tuple[str, Optional[str]]:
        sname = slot.get("name") if slot else None
        if slot is not None:
            if sname:
                return f"slot #{cur_slot_idx} ({sname})", sname
            return f"slot #{cur_slot_idx}", None
        prev_named = [nm for nm, _ in toks_seq[:tok_idx] if nm not in ("_",)]
        if prev_named:
            return f"arg #{tok_idx} (after `{prev_named[-1]}`)", None
        return f"arg #{tok_idx}", None

    body_stripped = body.lstrip()
    lead_ws = len(body) - len(body_stripped)
    consumed_body_end = lead_ws

    # 2. Leading `:= by` intro sequence aligned with expanded telescope (and inner `intro _` / `obtain ⟨... _, ...⟩`)
    is_tactic_body = bool(re.match(r"^by(?:\s|$)", body_stripped))
    if is_tactic_body:
        after_by_pos = lead_ws + 2
        lines_after = body[after_by_pos:].split("\n")
        rel_cursor = after_by_pos
        slot_cursor = 0
        in_leading_intros = True

        for raw_ln in lines_after:
            ln_start = rel_cursor
            ln_end = rel_cursor + len(raw_ln)
            rel_cursor = ln_end + 1
            st = raw_ln.strip()
            if not st:
                continue
            if in_leading_intros and st == "classical":
                consumed_body_end = ln_end
                continue
            m_intro = re.match(r"^\s*(intro|intros)\b(.*)$", raw_ln)
            if in_leading_intros and m_intro:
                consumed_body_end = ln_end
                clause = m_intro.group(2)
                toks = _parse_intro_tokens(clause)
                tok_pairs = [(t, "pattern" if ip else "explicit") for t, ip in toks]
                line_no = _offset_to_line(line_offsets, body_offset + ln_start, base_line)
                rest_body = body[ln_end:]
                rest_implicit = _RE_IMPLICIT_CTX_TACTIC.search(rest_body) is not None
                ctx_snip = _compact_snippet(raw_ln, 90)
                for tidx, (tok, is_pat) in enumerate(toks):
                    slot = telescope[slot_cursor] if slot_cursor < len(telescope) else None
                    cur_slot_idx = slot_cursor
                    slot_cursor += 1
                    if is_pat:
                        continue
                    slot_kind = slot["kind"] if slot else None
                    slot_type = slot["type"] if slot else None
                    is_slot_cls = bool(is_class_type is not None and slot_type and is_class_type(slot_type))
                    if tok == "_":
                        if slot_kind == "instance":
                            continue
                        is_heu_inst = (slot is None) and _is_heuristic_instance_token(tok_pairs, tidx)
                        bpos, sname = _binder_pos_label(tok_pairs, tidx, slot, cur_slot_idx)
                        item = {
                            "category": "dropped",
                            "kind": "intro_wildcard",
                            "confidence": "heuristic_source",
                            "line_no": line_no,
                            "binder": "_",
                            "binder_index": tidx,
                            "binder_pos": bpos,
                            "slot_name": sname,
                            "slot_index": cur_slot_idx if slot is not None else None,
                            "param_type": _compact_snippet(slot_type, 110) if slot_type else None,
                            "binder_context": ctx_snip,
                            "detail": (
                                f"`intro _` discards slot #{cur_slot_idx} ({_compact_snippet(slot_type, 90)})"
                                if slot_type
                                else f"`intro _` discards argument at {bpos}"
                            ),
                        }
                        if is_slot_cls:
                            item["suppression_reason"] = "local_class_instance"
                        elif is_heu_inst:
                            item["suppression_reason"] = "instance_wildcard"
                        findings.append(item)
                    elif tok != "rfl":
                        if slot_kind == "instance":
                            continue
                        refs_rest = _count_ident_refs(tok, rest_body)
                        if refs_rest > 0:
                            continue
                        if slot_kind in ("implicit", "strict_implicit") and not tok.startswith("_"):
                            if _slot_referenced_later(cur_slot_idx, slot["name"] if slot else tok):
                                continue
                        bpos, sname = _binder_pos_label(tok_pairs, tidx, slot, cur_slot_idx)
                        if tok.startswith("_"):
                            item = {
                                "category": "dropped",
                                "kind": "intro_unused_underscore",
                                "confidence": "heuristic_source",
                                "line_no": line_no,
                                "binder": tok,
                                "binder_index": tidx,
                                "binder_pos": bpos,
                                "slot_name": sname,
                                "slot_index": cur_slot_idx if slot is not None else None,
                                "param_type": _compact_snippet(slot_type, 110) if slot_type else None,
                                "implicit_tactic_in_body": rest_implicit,
                                "binder_context": ctx_snip,
                                "detail": (
                                    f"`intro {tok}` (slot #{cur_slot_idx}: {_compact_snippet(slot_type, 80)}) has 0 references"
                                    if slot_type
                                    else f"`intro {tok}` has 0 references in remaining proof"
                                ),
                            }
                            if is_slot_cls:
                                item["suppression_reason"] = "local_class_instance"
                            elif rest_implicit:
                                item["suppression_reason"] = "implicit_ctx_tactic"
                            findings.append(item)
                        elif slot is not None and slot_kind in ("arrow", "explicit"):
                            if _slot_referenced_later(cur_slot_idx, slot.get("name")):
                                continue
                            item = {
                                "category": "dropped",
                                "kind": "intro_unused_binder",
                                "confidence": "heuristic_source",
                                "line_no": line_no,
                                "binder": tok,
                                "binder_index": tidx,
                                "binder_pos": bpos,
                                "slot_name": sname,
                                "slot_index": cur_slot_idx,
                                "param_type": _compact_snippet(slot_type, 110) if slot_type else None,
                                "implicit_tactic_in_body": rest_implicit,
                                "binder_context": ctx_snip,
                                "detail": (
                                    f"`intro {tok}` (slot #{cur_slot_idx}: {_compact_snippet(slot_type, 80)}) has 0 references"
                                    if slot_type
                                    else f"`intro {tok}` has 0 references in remaining proof"
                                ),
                            }
                            if is_slot_cls:
                                item["suppression_reason"] = "local_class_instance"
                            elif rest_implicit:
                                item["suppression_reason"] = "implicit_ctx_tactic"
                            findings.append(item)
                continue
            in_leading_intros = False
            # Scan nested `intro ... _ ...` inside tactic body
            m_nested = re.match(r"^\s*(?:·\s*)?(intro|intros)\b(.*)$", raw_ln)
            if m_nested:
                toks = _parse_intro_tokens(m_nested.group(2))
                tok_pairs = [(t, "pattern" if ip else "explicit") for t, ip in toks]
                matched_inner = _match_inner_telescope(toks, inner_telescopes)
                line_no = _offset_to_line(line_offsets, body_offset + ln_start, base_line)
                ctx_snip = _compact_snippet(raw_ln, 90)
                for tidx, (tok, is_pat) in enumerate(toks):
                    if not is_pat and tok == "_":
                        islot = matched_inner[tidx] if (matched_inner and tidx < len(matched_inner)) else None
                        if islot is not None and islot["kind"] == "instance":
                            continue
                        ity = islot.get("type") if islot else None
                        is_heu_inst = _is_heuristic_instance_token(tok_pairs, tidx)
                        is_icls = bool(is_class_type is not None and ity and is_class_type(ity))
                        bpos, sname = _binder_pos_label(tok_pairs, tidx, islot, tidx)
                        if is_icls:
                            sreason = "local_class_instance"
                        elif is_heu_inst:
                            sreason = "instance_wildcard"
                        else:
                            sreason = "nested_intro_wildcard"
                        findings.append({
                            "category": "dropped",
                            "kind": "intro_wildcard",
                            "confidence": "heuristic_source",
                            "line_no": line_no,
                            "binder": "_",
                            "binder_index": tidx,
                            "binder_pos": bpos,
                            "slot_name": sname,
                            "slot_index": tidx if islot is not None else None,
                            "param_type": _compact_snippet(ity, 110) if ity else None,
                            "binder_context": ctx_snip,
                            "suppression_reason": sreason,
                            "detail": (
                                f"nested `intro _` discards {bpos}"
                                + (f" ({_compact_snippet(ity, 80)})" if ity else "")
                            ),
                        })
    else:
        # 3. Term-mode leading `fun ... =>` aligned with telescope
        for fitem in _iter_fun_binders(body, body_offset, line_offsets, base_line):
            if fitem["start"] != lead_ws:
                break
            consumed_body_end = fitem["end"]
            slot_cursor = 0
            btypes = fitem.get("binder_types") or [""] * len(fitem["binders"])
            lam_implicit = _RE_IMPLICIT_CTX_TACTIC.search(fitem["lambda_body"]) is not None
            ctx_snip = _compact_snippet(f"fun {fitem['raw_binders']} =>", 90)
            for tidx, (bname, bkind) in enumerate(fitem["binders"]):
                slot = telescope[slot_cursor] if slot_cursor < len(telescope) else None
                cur_slot_idx = slot_cursor
                slot_cursor += 1
                if bkind in ("instance", "pattern"):
                    continue
                slot_kind = slot["kind"] if slot else None
                slot_type = slot["type"] if slot else None
                is_slot_cls = bool(is_class_type is not None and slot_type and is_class_type(slot_type))
                if bname == "_":
                    if slot_kind == "instance" or bkind in ("implicit", "strict_implicit"):
                        continue
                    is_heu_inst = (slot is None) and _is_heuristic_instance_token(fitem["binders"], tidx, btypes)
                    bpos, sname = _binder_pos_label(fitem["binders"], tidx, slot, cur_slot_idx)
                    item = {
                        "category": "dropped",
                        "kind": "fun_wildcard",
                        "confidence": "heuristic_source",
                        "line_no": fitem["line_no"],
                        "binder": "_",
                        "binder_index": tidx,
                        "binder_pos": bpos,
                        "slot_name": sname,
                        "slot_index": cur_slot_idx if slot is not None else None,
                        "param_type": _compact_snippet(slot_type, 110) if slot_type else None,
                        "binder_context": ctx_snip,
                        "detail": (
                            f"`fun _ =>` discards slot #{cur_slot_idx} ({_compact_snippet(slot_type, 90)})"
                            if slot_type
                            else f"`fun _ =>` discards argument at {bpos}"
                        ),
                    }
                    if is_slot_cls:
                        item["suppression_reason"] = "local_class_instance"
                    elif is_heu_inst:
                        item["suppression_reason"] = "instance_wildcard"
                    findings.append(item)
                else:
                    if slot_kind == "instance":
                        continue
                    if _count_ident_refs(bname, fitem["lambda_body"]) == 0:
                        if slot_kind in ("implicit", "strict_implicit") and not bname.startswith("_"):
                            if _slot_referenced_later(cur_slot_idx, slot["name"] if slot else bname):
                                continue
                        if bname.startswith("_") or (
                            slot is not None
                            and slot_kind in ("arrow", "explicit")
                            and not _slot_referenced_later(cur_slot_idx, slot.get("name"))
                        ):
                            bpos, sname = _binder_pos_label(fitem["binders"], tidx, slot, cur_slot_idx)
                            item = {
                                "category": "dropped",
                                "kind": "fun_unused_underscore" if bname.startswith("_") else "fun_unused_binder",
                                "confidence": "heuristic_source",
                                "line_no": fitem["line_no"],
                                "binder": bname,
                                "binder_index": tidx,
                                "binder_pos": bpos,
                                "slot_name": sname,
                                "slot_index": cur_slot_idx if slot is not None else None,
                                "param_type": _compact_snippet(slot_type, 110) if slot_type else None,
                                "implicit_tactic_in_body": lam_implicit,
                                "binder_context": ctx_snip,
                                "detail": f"`fun {bname} =>` has 0 references in lambda body",
                            }
                            if is_slot_cls:
                                item["suppression_reason"] = "local_class_instance"
                            elif lam_implicit:
                                item["suppression_reason"] = "implicit_ctx_tactic"
                            findings.append(item)
            break

    # 4. Nested `fun ... _ ... =>` inside remaining body (separate `combinator_fun_wildcard` kind!)
    for fitem in _iter_fun_binders(body, body_offset, line_offsets, base_line):
        if fitem["start"] < consumed_body_end:
            continue
        reason, wc_count, pos_labels = _classify_nested_fun_noise(fitem, body, inner_telescopes)
        if wc_count > 0:
            ctx_snip = _compact_snippet(f"fun {fitem['raw_binders']} =>", 90)
            item = {
                "category": "dropped",
                "kind": "combinator_fun_wildcard",
                "confidence": "heuristic_source",
                "line_no": fitem["line_no"],
                "binder": "_",
                "binder_pos": ", ".join(pos_labels) if pos_labels else None,
                "slot_index": None,
                "param_type": None,
                "count": wc_count,
                "binder_context": ctx_snip,
                "detail": f"nested `fun ... _ ... =>` discards {wc_count} binder(s) ({ctx_snip})",
            }
            if reason is not None:
                item["suppression_reason"] = reason
            findings.append(item)

    # 5. Discarded Prop/proof components in `obtain ⟨a, _, b⟩ := ...` / `rcases ... with ⟨a, _, b⟩`
    if is_tactic_body:
        has_infer_inst = "inferInstance" in body
        rel_cursor = 0
        for raw_ln in body.split("\n"):
            ln_start = rel_cursor
            rel_cursor += len(raw_ln) + 1
            m_ob = re.search(r"\b(?:obtain|rcases\b[^\n]*?\bwith)\s+⟨", raw_ln)
            if not m_ob:
                continue
            ang = _extract_balanced_angle(raw_ln, m_ob.end() - 1)
            if ang is None:
                continue
            items = _split_angle_tuple(ang[0])
            if not items:
                continue
            discard_idxs = [
                idx for idx, it in enumerate(items)
                if it.strip() == "_" and not _is_obtain_inst_run(items, idx, has_infer_inst)
            ]
            if discard_idxs:
                line_no = _offset_to_line(line_offsets, body_offset + ln_start, base_line)
                pos_s = ", ".join(f"#{i}" for i in discard_idxs[:6])
                findings.append({
                    "category": "dropped",
                    "kind": "obtain_discarded",
                    "confidence": "heuristic_source",
                    "line_no": line_no,
                    "binder": "_",
                    "positions": discard_idxs,
                    "binder_pos": f"component(s) {pos_s}",
                    "binder_context": _compact_snippet(raw_ln, 90),
                    "detail": f"`obtain/rcases` discards component(s) {pos_s} in `⟨{_compact_snippet(ang[0], 60)}⟩`",
                })

    return findings


_RE_TRIVIAL_WORD = re.compile(rf"(?<![{_HYGIENE_IDENT_CONT}.])(True\.intro|trivial)(?![{_HYGIENE_IDENT_CONT}])")
_RE_FIELD_TRUE_DEF = re.compile(
    rf"^\s*([{_HYGIENE_IDENT_START}][{_HYGIENE_IDENT_CONT}]*)\b[^\n]*?(?::\s*(?:_root_\.)?True\b|:=\s*(?:(?:_root_\.)?True(?:\.intro)?|trivial)\b)"
)
_RE_RECORD_FIELD_TRUE = re.compile(
    rf"(?<![{_HYGIENE_IDENT_CONT}.])([{_HYGIENE_IDENT_START}][{_HYGIENE_IDENT_CONT}]*)\s*:=\s*(?:(_root_\.)?True(?:\.intro)?|trivial)(?![{_HYGIENE_IDENT_CONT}])"
)
_RE_TACTIC_LEAD_BEFORE_TRIVIAL = re.compile(
    r"(?:^|[;·|]|<;>|=>|:=|\b(?:by|exact|apply|then|else|do)\b)\s*$"
)
_RE_TOP_OR_UNIV_CTX = re.compile(
    rf"(?:∈|∉)\s*\(?\s*(?:⊤|Set\.univ)(?![{_HYGIENE_IDENT_CONT}])"
    rf"|⟨\s*(?:⊤|Set\.univ)(?![{_HYGIENE_IDENT_CONT}])"
    rf"|(?<![{_HYGIENE_IDENT_CONT}.])(?:⊤|Set\.univ)(?![{_HYGIENE_IDENT_CONT}])"
    rf"|\b(?:isOpen_univ|mem_univ)\b"
)


def _is_true_type_expr(s: str) -> bool:
    st = _strip_outer_parens(s)
    return st in ("True", "_root_.True")


def _is_top_or_univ_trivial_ctx(body: str, match_start: int, type_expr: str = "") -> bool:
    """Detect `trivial` witnessing `x ∈ ⊤` / `x ∈ Set.univ` / `(⊤ : Opens)` membership."""
    win_start = max(0, match_start - 180)
    pre = body[win_start:match_start]
    stmt_hits = list(
        re.finditer(
            r"(?:^|\n)[ \t]*(?:·[ \t]*)?(?:have|haveI|let|letI|set|obtain|rcases|refine|exact|apply|intro|by_cases)\b",
            pre,
        )
    )
    if stmt_hits:
        pre = pre[stmt_hits[-1].start() :]
    if _RE_TOP_OR_UNIV_CTX.search(pre):
        return True
    if re.search(r"(?:disjoint|mem_|subset|[∈∉⊆])", pre):
        prior = body[max(0, match_start - 400) : match_start]
        if (type_expr and _RE_TOP_OR_UNIV_CTX.search(type_expr)) or _RE_TOP_OR_UNIV_CTX.search(prior):
            return True
    return False


def _collect_span_local_vars(span: Dict[str, Any]) -> Set[str]:
    """Collect locally bound variable names from declaration headers, intros, obtain/rcases/choose/have/let/fun."""
    lvars: Set[str] = set()

    def _add_tok(tok: str) -> None:
        s = tok.strip()
        if not s or s == "_" or s in _HYGIENE_STOP_WORDS:
            return
        if _RE_HYGIENE_IDENT.fullmatch(s):
            lvars.add(s)

    def _add_idents_in_pat(pat: str) -> None:
        for t in _RE_HYGIENE_IDENT.findall(pat):
            _add_tok(t)

    for b in span.get("header_binders") or ():
        bn = b.get("name")
        if bn:
            _add_tok(str(bn))

    body = span.get("body_text") or ""
    if not body:
        return lvars

    for m in re.finditer(r"^\s*(?:·\s*)?(?:intro|intros|rintro)\b([^\n]*)", body, re.M):
        for tok, is_pat in _parse_intro_tokens(m.group(1)):
            if is_pat:
                _add_idents_in_pat(tok)
            else:
                _add_tok(tok)

    for fitem in _iter_fun_binders(body, 0, [0], 1):
        for bn, bk in fitem.get("binders") or ():
            if bk == "pattern":
                _add_idents_in_pat(bn)
            else:
                _add_tok(bn)

    for m in re.finditer(r"\b(?:obtain|rcases\b[^\n]*?\bwith)\s+⟨", body):
        ang = _extract_balanced_angle(body, m.end() - 1)
        if ang is not None and len(ang[0]) <= 1200:
            _add_idents_in_pat(ang[0])

    for m in re.finditer(rf"(?<![{_HYGIENE_IDENT_CONT}.])choose[!?]*\s+([\s\S]{{1,300}}?)\s+\busing(?![{_HYGIENE_IDENT_CONT}])", body):
        if ";" not in m.group(1) and ":=" not in m.group(1):
            _add_idents_in_pat(m.group(1))

    for m in re.finditer(
        rf"(?<![{_HYGIENE_IDENT_CONT}.])(?:haveI?|letI?|set)\s+([{_HYGIENE_IDENT_START}][{_HYGIENE_IDENT_CONT}]*)(?![{_HYGIENE_IDENT_CONT}])", body
    ):
        _add_tok(m.group(1))

    return lvars


def _extract_call_head_before(body: str, match_start: int) -> Optional[str]:
    """Extract the callee head if `match_start` passes `trivial`/`True.intro` as a function arg (not in `⟨...⟩`)."""
    i = match_start - 1
    stop_min = max(0, match_start - 220)
    depth = 0
    stmt_start = stop_min
    while i >= stop_min:
        ch = body[i]
        if ch in _HYGIENE_CLOSE:
            depth += 1
            i -= 1
            continue
        if ch in _HYGIENE_OPEN:
            if depth > 0:
                depth -= 1
                i -= 1
                continue
            if ch == "⟨" and not body[i + 1 : match_start].strip():
                return None
            stmt_start = i + 1
            break
        if depth == 0:
            if ch in ",;\n·|$":
                if ch == "," and not body[i + 1 : match_start].strip():
                    return None
                stmt_start = i + 1
                break
            if i >= 1 and body[i - 1 : i + 1] in (":=", "=>", "<|"):
                stmt_start = i + 1
                break
            if ch == "↦":
                stmt_start = i + 1
                break
        i -= 1
    prefix = body[stmt_start:match_start].strip()
    if not prefix:
        return None
    toks = _split_top_level_app_args(prefix)
    while toks and toks[0] in ("exact", "refine", "apply", "by", "from", "with", "show", "return"):
        toks.pop(0)
    if not toks:
        return None
    return toks[0].lstrip("@") or None


def _audit_true_slots(
    span: Dict[str, Any],
    telescope: List[Dict[str, Any]],
    return_type: str,
    kernel_true_edges: Tuple[bool, bool],
) -> List[Dict[str, Any]]:
    """Detect `: True` / `:= True` dummy slots, `∧ True ∧` conjuncts, and passed literal `trivial` / `True.intro`."""
    findings: List[Dict[str, Any]] = []
    keyword = span["keyword"]
    line_offsets = span["line_offsets"]
    base_line = span["start_line"]
    body = span["body_text"]
    body_offset = span["body_offset"]
    type_expr = span["type_expr"]
    k_type_true, k_val_true = kernel_true_edges

    # 1. Header binders typed `: True` or defaulting to `:= trivial` / `True.intro`
    for b in span["header_binders"]:
        bty = b.get("type", "")
        bdef = b.get("default")
        bname = b.get("name") or "_"
        if _is_true_type_expr(bty) or (bdef and bdef.strip() in ("trivial", "True.intro", "_root_.True.intro")):
            findings.append({
                "category": "true_slot",
                "kind": "true_binder",
                "confidence": "heuristic_source",
                "line_no": b.get("line_no", base_line),
                "binder": bname,
                "kernel_true_type_edge": k_type_true,
                "detail": f"binder `({bname} : {_compact_snippet(bty or 'True', 40)})` is a `True` dummy slot",
            })

    # 2. Telescope `→ True →` / `∀ (h : True),` slots
    for sl in telescope:
        if _is_true_type_expr(sl.get("type", "")):
            findings.append({
                "category": "true_slot",
                "kind": "true_arrow_slot",
                "confidence": "heuristic_source",
                "line_no": sl.get("line_no", base_line),
                "slot_index": sl["index"],
                "kernel_true_type_edge": k_type_true,
                "detail": f"signature slot #{sl['index']} has literal type `True`",
            })

    # 3. Return type literally `True`, `def`/`abbrev` body literally `True`, or `∧ True ∧` conjuncts
    if _is_true_type_expr(return_type):
        findings.append({
            "category": "true_slot",
            "kind": "true_return_type",
            "confidence": "heuristic_source",
            "line_no": base_line,
            "kernel_true_type_edge": k_type_true,
            "detail": f"`{keyword}` return type is literal `True`",
        })
    elif keyword in ("def", "abbrev"):
        if _is_true_type_expr(body):
            findings.append({
                "category": "true_slot",
                "kind": "true_def_body",
                "confidence": "heuristic_source",
                "line_no": _offset_to_line(line_offsets, body_offset, base_line),
                "kernel_true_value_edge": k_val_true,
                "detail": f"`{keyword}` body is literal `:= True`",
            })
        else:
            for c_idx, rel_off in _collect_def_conjunct_true_slots(body):
                findings.append({
                    "category": "true_slot",
                    "kind": "conjunct_true_slot",
                    "confidence": "heuristic_source",
                    "line_no": _offset_to_line(line_offsets, body_offset + rel_off, base_line),
                    "conjunct_index": c_idx,
                    "kernel_true_value_edge": k_val_true,
                    "detail": f"`{keyword}` conjunct #{c_idx} is literal `True`",
                })

    # 4. Structure / class field definitions typed `: True` or `:= True` / `:= trivial`
    seen_field_offsets: Set[int] = set()
    if keyword in ("structure", "class") and span["body_kind"] == "where":
        rel = 0
        for ln in body.split("\n"):
            mf = _RE_FIELD_TRUE_DEF.match(ln)
            if mf:
                fname = mf.group(1)
                if fname not in _HYGIENE_STOP_WORDS:
                    lno = _offset_to_line(line_offsets, body_offset + rel, base_line)
                    findings.append({
                        "category": "true_slot",
                        "kind": "true_field_slot",
                        "confidence": "heuristic_source",
                        "line_no": lno,
                        "field": fname,
                        "detail": f"structure field `{fname}` has `True`/`trivial` dummy slot",
                    })
                    seen_field_offsets.add(lno)
            rel += len(ln) + 1

    # 5. Record / `where` field assignments `field := True | trivial | True.intro`
    captured_trivial_positions: Set[int] = set()
    if body:
        for mf in _RE_RECORD_FIELD_TRUE.finditer(body):
            fname = mf.group(1)
            if fname in _HYGIENE_STOP_WORDS:
                continue
            lno = _offset_to_line(line_offsets, body_offset + mf.start(), base_line)
            if lno in seen_field_offsets:
                captured_trivial_positions.add(mf.end())
                continue
            findings.append({
                "category": "true_slot",
                "kind": "true_field_assign",
                "confidence": "heuristic_source",
                "line_no": lno,
                "field": fname,
                "kernel_true_value_edge": k_val_true,
                "detail": f"field assignment `{_compact_snippet(mf.group(0), 60)}`",
            })
            captured_trivial_positions.add(mf.end())

    # 6. Passed literal `trivial` / `True.intro` in term / argument positions
    if body:
        local_vars = _collect_span_local_vars(span) if ("trivial" in body or "True.intro" in body) else set()
        for mt in _RE_TRIVIAL_WORD.finditer(body):
            if mt.end() in captured_trivial_positions:
                continue
            tok = mt.group(1)
            lno = _offset_to_line(line_offsets, body_offset + mt.start(), base_line)
            ln_start = body.rfind("\n", 0, mt.start()) + 1
            before_on_line = body[ln_start : mt.start()]
            callee = _extract_call_head_before(body, mt.start()) if local_vars else None
            callee_base = callee.split(".", 1)[0] if callee else ""
            is_act_prem = bool(callee_base and callee_base in local_vars)
            if tok == "True.intro":
                item: Dict[str, Any] = {
                    "category": "true_slot",
                    "kind": "passed_true_intro",
                    "confidence": "heuristic_source",
                    "line_no": lno,
                    "token": tok,
                    "kernel_true_value_edge": k_val_true,
                    "detail": "literal `True.intro` term passed in body",
                }
                if is_act_prem:
                    item["role"] = "activating_premise"
                    item["premise_callee"] = callee
                    item["suppression_reason"] = "activating_premise"
                findings.append(item)
                continue
            # For `trivial`, distinguish term-argument / tuple position from standalone tactic `by trivial`
            if _RE_TACTIC_LEAD_BEFORE_TRIVIAL.search(before_on_line):
                continue
            item = {
                "category": "true_slot",
                "kind": "passed_trivial_arg",
                "confidence": "heuristic_source",
                "line_no": lno,
                "token": tok,
                "kernel_true_value_edge": k_val_true,
                "detail": "literal `trivial` passed as argument/tuple slot",
            }
            if is_act_prem:
                item["role"] = "activating_premise"
                item["premise_callee"] = callee
                item["suppression_reason"] = "activating_premise"
            elif _is_top_or_univ_trivial_ctx(body, mt.start(), type_expr=type_expr):
                item["suppression_reason"] = "top_univ_membership"
            findings.append(item)

    return findings


def _find_dite_zero_branches(body: str) -> List[Tuple[int, str]]:
    """Linear O(N) scan for dependent `if h : P then ... else 0` branches in `def`/`abbrev` bodies."""
    if "if" not in body or "else" not in body or "0" not in body:
        return []
    out: List[Tuple[int, str]] = []
    n = len(body)
    depth = 0
    i = 0

    def _kw(pos: int, word: str) -> bool:
        wlen = len(word)
        if not body.startswith(word, pos):
            return False
        if pos > 0 and (body[pos - 1] == "." or _is_ident_cont_ch(body[pos - 1])):
            return False
        if pos + wlen < n and _is_ident_cont_ch(body[pos + wlen]):
            return False
        return True

    while i < n:
        ch = body[i]
        if ch in _HYGIENE_OPEN:
            depth += 1
            i += 1
            continue
        if ch in _HYGIENE_CLOSE:
            depth = max(0, depth - 1)
            i += 1
            continue
        if _kw(i, "if"):
            base_depth = depth
            j = i + 2
            cur_d = base_depth
            then_pos = -1
            else_pos = -1
            if_nest = 0
            while j < n:
                cj = body[j]
                if cj in _HYGIENE_OPEN:
                    cur_d += 1
                    j += 1
                    continue
                if cj in _HYGIENE_CLOSE:
                    if cur_d <= base_depth:
                        break
                    cur_d -= 1
                    j += 1
                    continue
                if cur_d == base_depth:
                    if then_pos < 0 and _kw(j, "then"):
                        then_pos = j
                        j += 4
                        continue
                    if then_pos >= 0:
                        if _kw(j, "if"):
                            if_nest += 1
                            j += 2
                            continue
                        if _kw(j, "else"):
                            if if_nest == 0:
                                else_pos = j
                                break
                            if_nest -= 1
                            j += 4
                            continue
                j += 1
            if then_pos > i and else_pos > then_pos:
                hdr = body[i + 2 : then_pos].strip()
                m_cb = re.match(rf"^([{_HYGIENE_IDENT_START}][{_HYGIENE_IDENT_CONT}]*)\s*:(?!=)", hdr)
                if m_cb:
                    k = else_pos + 4
                    while k < n and body[k].isspace():
                        k += 1
                    # Extract single else branch expression
                    ed = 0
                    e_end = k
                    ln_s = body.rfind("\n", 0, i) + 1
                    if_indent = len(body[ln_s:i]) - len(body[ln_s:i].lstrip(" "))
                    while e_end < min(n, k + 80):
                        ec = body[e_end]
                        if ec in _HYGIENE_OPEN:
                            ed += 1
                        elif ec in _HYGIENE_CLOSE:
                            if ed == 0:
                                break
                            ed -= 1
                        elif ed == 0 and ec in ";,":
                            break
                        elif ed == 0 and ec == "\n":
                            nxt = e_end + 1
                            while nxt < n and body[nxt] == " ":
                                nxt += 1
                            if nxt >= n or (nxt - (e_end + 1)) <= if_indent:
                                break
                        e_end += 1
                    ebody = _strip_outer_parens(body[k:e_end])
                    if re.fullmatch(r"0(?:\s*:\s*\S.*)?", ebody, re.S):
                        out.append((else_pos, m_cb.group(1)))
            i += 2
            continue
        i += 1
    return out


_RE_LE_REFL_TERM = re.compile(rf"(?<![{_HYGIENE_IDENT_CONT}.])(?:le_refl\s+_|le_rfl)(?![{_HYGIENE_IDENT_CONT}])")


def _audit_semantic_flags(span: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Opt-in high-signal semantic flags (`default_zero_branch` on defs, `le_refl_closure` in constructor tuples)."""
    findings: List[Dict[str, Any]] = []
    keyword = span["keyword"]
    body = span["body_text"]
    if keyword in ("axiom", "opaque", "structure", "class", "inductive") or not body.strip():
        return findings
    line_offsets = span["line_offsets"]
    body_offset = span["body_offset"]
    base_line = span["start_line"]

    # 1. Zero-default dependent branch `if h : ... then ... else 0` in def/abbrev
    if keyword in ("def", "abbrev"):
        for else_pos, cond_binder in _find_dite_zero_branches(body):
            lno = _offset_to_line(line_offsets, body_offset + else_pos, base_line)
            findings.append({
                "category": "semantic",
                "kind": "default_zero_branch",
                "confidence": "semantic_heuristic",
                "line_no": lno,
                "cond_binder": cond_binder,
                "detail": f"`{keyword}` dependent `if {cond_binder} : ... then ... else 0` returns zero outside hypothesis",
            })

    # 2. Constructor-tuple self-witnessed `le_refl _` / `le_rfl` closures
    if "le_refl" in body or "le_rfl" in body:
        by_line: Dict[int, int] = collections.Counter()
        n = len(body)
        for m in _RE_LE_REFL_TERM.finditer(body):
            # Confirm direct component of an enclosing `⟨..., le_refl _, ...⟩` tuple
            j = m.end()
            while j < n and body[j] in " \t\n\r)":
                j += 1
            if j >= n or body[j] not in (",", "⟩"):
                continue
            k = m.start() - 1
            while k >= 0 and body[k] in " \t\n\r(":
                k -= 1
            if k < 0 or body[k] not in (",", "⟨"):
                continue
            if body[j] == "," and body[k] == ",":
                # Also verify we are inside an enclosing `⟨...⟩` (not a generic `(...)`)
                d = 0
                p = m.start() - 1
                in_angle = False
                while p >= max(0, m.start() - 1200):
                    cp = body[p]
                    if cp in _HYGIENE_CLOSE:
                        d += 1
                    elif cp in _HYGIENE_OPEN:
                        if d == 0:
                            in_angle = (cp == "⟨")
                            break
                        d -= 1
                    p -= 1
                if not in_angle:
                    continue
            lno = _offset_to_line(line_offsets, body_offset + m.start(), base_line)
            by_line[lno] += 1
        for lno, cnt in sorted(by_line.items()):
            findings.append({
                "category": "semantic",
                "kind": "le_refl_closure",
                "confidence": "semantic_heuristic",
                "line_no": lno,
                "count": cnt,
                "detail": (
                    f"constructor tuple closes inequality with self-witnessed `le_refl _` / `le_rfl` ({cnt}x)"
                    if cnt > 1
                    else "constructor tuple closes inequality with self-witnessed `le_refl _` / `le_rfl`"
                ),
            })

    return findings


def _split_depth0_op_spans(s: str, base_off: int, op: str) -> List[Tuple[str, int]]:
    """Like `_split_depth0_op`, returning `(stripped_part, rel_offset_in_root)`."""
    out: List[Tuple[str, int]] = []
    depth = 0
    start = 0
    i = 0
    n = len(s)
    olen = len(op)
    while i < n:
        ch = s[i]
        if ch in _HYGIENE_OPEN:
            depth += 1
            i += 1
            continue
        if ch in _HYGIENE_CLOSE:
            depth = max(0, depth - 1)
            i += 1
            continue
        if depth == 0 and s.startswith(op, i):
            seg = s[start:i]
            lead = len(seg) - len(seg.lstrip())
            part = seg.strip()
            if part:
                out.append((part, base_off + start + lead))
            i += olen
            start = i
            continue
        i += 1
    seg = s[start:]
    lead = len(seg) - len(seg.lstrip())
    part = seg.strip()
    if part:
        out.append((part, base_off + start + lead))
    return out


def _strip_outer_parens_with_offset(s: str, base_off: int) -> Tuple[str, int]:
    cur = s
    off = base_off
    lead = len(cur) - len(cur.lstrip())
    cur = cur.strip()
    off += lead
    while len(cur) >= 2 and cur[0] == "(" and cur[-1] == ")":
        depth = 0
        matched_end = False
        for i, ch in enumerate(cur):
            if ch in _HYGIENE_OPEN:
                depth += 1
            elif ch in _HYGIENE_CLOSE:
                depth -= 1
                if depth == 0:
                    matched_end = (i == len(cur) - 1)
                    break
        if not matched_end:
            break
        inner = cur[1:-1]
        ilead = len(inner) - len(inner.lstrip())
        cur = inner.strip()
        off += 1 + ilead
    return cur, off


def _collect_def_conjunct_true_slots(body: str) -> List[Tuple[int, int]]:
    """Find literal `True` conjuncts inside a non-tactic `def`/`abbrev` predicate `∧`-chain."""
    cur, off = _strip_outer_parens_with_offset(body, 0)
    if not cur or re.match(r"^by(?:\s|$)", cur):
        return []

    for _ in range(12):
        if not cur:
            return []
        if cur.startswith(("∃", "∀")) or re.match(r"^(?:Exists|forall|fun)\b", cur) or cur.startswith("λ"):
            sep = "=>" if (cur.startswith("λ") or re.match(r"^fun\b", cur)) else ","
            depth = 0
            sep_pos = -1
            j = 0
            n = len(cur)
            while j < n:
                ch = cur[j]
                if ch in _HYGIENE_OPEN:
                    depth += 1
                elif ch in _HYGIENE_CLOSE:
                    depth = max(0, depth - 1)
                elif depth == 0 and cur.startswith(sep, j):
                    sep_pos = j
                    break
                j += 1
            if sep_pos >= 0:
                cur, off = _strip_outer_parens_with_offset(cur[sep_pos + len(sep) :], off + sep_pos + len(sep))
                continue
        arrow_spans = _split_depth0_op_spans(cur, off, "→")
        if len(arrow_spans) >= 2 and "∧" not in arrow_spans[0][0] and "×" not in arrow_spans[0][0]:
            first_end = arrow_spans[1][1]
            cur, off = _strip_outer_parens_with_offset(body[first_end : off + len(cur)], first_end)
            continue
        break

    def _flatten_and(expr: str, eoff: int, depth: int = 0) -> List[Tuple[str, int]]:
        if depth > 16:
            return [(expr, eoff)]
        st, soff = _strip_outer_parens_with_offset(expr, eoff)
        parts = _split_depth0_op_spans(st, soff, "∧")
        if len(parts) >= 2:
            out: List[Tuple[str, int]] = []
            for p_txt, p_off in parts:
                out.extend(_flatten_and(p_txt, p_off, depth + 1))
            return out
        return [(st, soff)]

    legs = _flatten_and(cur, off)
    if len(legs) < 2:
        return []
    return [(idx, rel_off) for idx, (leg_txt, rel_off) in enumerate(legs) if _is_true_type_expr(leg_txt)]


_RE_DOT_PROJ_CHAIN = re.compile(r"((?:\.(?:1|2|left|right|fst|snd))+)(?![0-9A-Za-z_'])")


def _parse_proj_chain(chain_str: str) -> List[int]:
    steps: List[int] = []
    for seg in chain_str.split("."):
        if not seg:
            continue
        if seg in ("1", "left", "fst"):
            steps.append(1)
        elif seg in ("2", "right", "snd"):
            steps.append(2)
    return steps


def _proj_steps_to_legs(steps: List[int], arity: int) -> List[int]:
    """Map a right-associated projection chain (e.g. `[2, 2, 2, 1]`) onto leg index(es) in `0..arity-1`."""
    if not steps or arity < 2:
        return []
    idx = 0
    for s in steps:
        if s == 1:
            return [min(idx, arity - 1)]
        idx += 1
        if idx >= arity - 1:
            return [arity - 1]
    # Ended on `.2` before reaching the final leg -> projects the remaining suffix tuple
    return list(range(idx, arity))


def _split_angle_tuple(inner: str) -> List[str]:
    """Split `a, b, c` at depth 0 inside `⟨...⟩`."""
    parts: List[str] = []
    depth = 0
    start = 0
    for i, ch in enumerate(inner):
        if ch in _HYGIENE_OPEN:
            depth += 1
        elif ch in _HYGIENE_CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and ch == ",":
            parts.append(inner[start:i].strip())
            start = i + 1
    parts.append(inner[start:].strip())
    return [p for p in parts if p]


def _parse_conj_combinator_tree(expr: str, depth: int = 0) -> Tuple[Any, ...]:
    """Parse bounded `.and` / `Closed.and` / `Ev.and` / `And.intro` / `⟨a, b⟩` trees into `('and', L, R)` or `('leaf', text)`."""
    if depth > 24 or len(expr) > 6000:
        return ("leaf", expr)
    s = _strip_outer_parens(expr)
    if not s:
        return ("leaf", s)
    if s.startswith("⟨"):
        ang = _extract_balanced_angle(s, 0)
        if ang is not None and ang[1] == len(s):
            parts = _split_angle_tuple(ang[0])
            if len(parts) >= 2:
                node: Tuple[Any, ...] = _parse_conj_combinator_tree(parts[-1], depth + 1)
                for p in reversed(parts[:-1]):
                    node = ("and", _parse_conj_combinator_tree(p, depth + 1), node)
                return node
    toks = _split_top_level_app_args(s)
    if not toks:
        return ("leaf", s)
    if "<|" in toks:
        pi = toks.index("<|")
        lhs_s = " ".join(toks[:pi])
        rhs_s = " ".join(toks[pi + 1 :])
        ltoks = _split_top_level_app_args(lhs_s)
        if len(ltoks) == 2 and (ltoks[0].endswith(".and") or ltoks[0].endswith(".intro")):
            return ("and", _parse_conj_combinator_tree(ltoks[1], depth + 1), _parse_conj_combinator_tree(rhs_s, depth + 1))
    t0 = toks[0]
    if (
        len(toks) >= 3
        and not t0.startswith(("(", "⟨"))
        and t0.endswith((".and", ".and'", ".intro"))
        and len(t0.split(".")) >= 2
        and t0.split(".")[-2][:1].isupper()
    ):
        if len(toks) == 3:
            return ("and", _parse_conj_combinator_tree(toks[1], depth + 1), _parse_conj_combinator_tree(toks[2], depth + 1))
        return ("and", _parse_conj_combinator_tree(toks[-2], depth + 1), _parse_conj_combinator_tree(toks[-1], depth + 1))
    if t0.endswith(".and") and len(toks) >= 2:
        return ("and", _parse_conj_combinator_tree(t0[:-4], depth + 1), _parse_conj_combinator_tree(" ".join(toks[1:]), depth + 1))
    return ("leaf", s)


def _iter_tree_leaves(node: Tuple[Any, ...], path: Tuple[int, ...] = ()) -> Iterable[Tuple[List[int], str]]:
    if node[0] == "leaf":
        yield list(path), str(node[1])
    else:
        yield from _iter_tree_leaves(node[1], path + (1,))
        yield from _iter_tree_leaves(node[2], path + (2,))


def _extract_balanced_rhs_expr(text: str, start: int, max_chars: int = 5000) -> Tuple[str, int]:
    """Extract a possibly multi-line Lean RHS expression bounded cleanly by bracket balance & indentation."""
    n = len(text)
    i = start
    while i < n and text[i].isspace():
        i += 1
    if i >= n:
        return "", i
    line_start = text.rfind("\n", 0, start) + 1
    base_indent = len(text[line_start:start]) - len(text[line_start:start].lstrip(" "))
    depth = 0
    end = i
    limit = min(n, i + max_chars)
    while end < limit:
        ch = text[end]
        if ch in _HYGIENE_OPEN:
            depth += 1
            end += 1
            continue
        if ch in _HYGIENE_CLOSE:
            if depth == 0:
                break
            depth -= 1
            end += 1
            continue
        if depth == 0 and ch == "\n":
            nxt = end + 1
            while nxt < n and text[nxt] == " ":
                nxt += 1
            nxt_indent = nxt - (end + 1)
            nxt_rest = text[nxt : nxt + 24]
            if nxt >= n or text[nxt] == "\n":
                break
            if nxt_indent <= base_indent and not nxt_rest.startswith((".", "|", "<|", ")", "⟩")):
                break
            if re.match(r"(?:have|haveI|let|letI|set|obtain|rcases|refine|exact|apply|rw|simp|intro|by_cases|·)\b", nxt_rest):
                break
        if depth == 0 and (ch == ";" or text.startswith("· ", end)):
            break
        end += 1
    return text[i:end].strip(), end


def _scan_var_projections(scope_body: str, var_name: str) -> Tuple[List[List[int]], bool]:
    """Find all `.1`/`.2` projection step chains on `var_name` (direct or `(var_name ...).1.2`) and bare whole uses."""
    pat = re.compile(rf"(?<![{_HYGIENE_IDENT_CONT}.]){re.escape(var_name)}(?![{_HYGIENE_IDENT_CONT}])")
    proj_chains: List[List[int]] = []
    bare_use = False
    n_cb = len(scope_body)
    for m in pat.finditer(scope_body):
        mp = _RE_DOT_PROJ_CHAIN.match(scope_body, m.end())
        if mp:
            steps = _parse_proj_chain(mp.group(1))
            if steps:
                proj_chains.append(steps)
                continue
        back_i = m.start() - 1
        while back_i >= 0 and (scope_body[back_i].isspace() or scope_body[back_i] == "@"):
            back_i -= 1
        matched_paren = False
        while back_i >= 0 and scope_body[back_i] == "(":
            # Ensure `var_name` is the head of `(var_name ...)`, not an inner argument `(foo var_name)`.
            inner_pre = scope_body[back_i + 1 : m.start()].strip().lstrip("@").strip()
            if inner_pre:
                break
            depth = 1
            fwd_i = back_i + 1
            while fwd_i < n_cb and depth > 0:
                if scope_body[fwd_i] in _HYGIENE_OPEN:
                    depth += 1
                elif scope_body[fwd_i] in _HYGIENE_CLOSE:
                    depth -= 1
                fwd_i += 1
            if depth != 0:
                break
            mp2 = _RE_DOT_PROJ_CHAIN.match(scope_body, fwd_i)
            if mp2:
                steps = _parse_proj_chain(mp2.group(1))
                if steps:
                    proj_chains.append(steps)
                    matched_paren = True
                    break
            back_i -= 1
            while back_i >= 0 and scope_body[back_i].isspace():
                back_i -= 1
        if matched_paren:
            continue
        pre_ctx = scope_body[max(0, m.start() - 28) : m.start()]
        m_pre = re.search(r"\b(?:And\.(left|right)|Prod\.(fst|snd)|PProd\.(fst|snd))\s*\(?\s*@?\s*$", pre_ctx)
        if m_pre:
            tok_p = next(g for g in m_pre.groups() if g is not None)
            proj_chains.append([1 if tok_p in ("left", "fst") else 2])
            continue
        bare_use = True
    return proj_chains, bare_use


def _navigate_pattern_path(pat_text: str, prefix_steps: List[int]) -> Tuple[Optional[str], List[int]]:
    """Follow `prefix_steps` through nested `⟨...⟩` destructuring patterns.

    Returns `(var_or_pat_at_rest, remaining_steps)`; `('_', [])` signals an explicit discard.
    """
    cur = _strip_outer_parens(pat_text).strip()
    steps = list(prefix_steps)
    while steps and cur.startswith("⟨"):
        ang = _extract_balanced_angle(cur, 0)
        if ang is None or ang[1] != len(cur):
            break
        parts = _split_angle_tuple(ang[0])
        if len(parts) < 2:
            break
        st = steps.pop(0)
        if st == 1:
            cur = parts[0].strip()
        elif len(parts) == 2:
            cur = parts[1].strip()
        else:
            cur = "⟨" + ", ".join(parts[1:]) + "⟩"
    return (cur or None), steps


def _collect_and_chain_bindings(
    body: str,
    line_offsets: List[int],
    body_offset: int,
    base_line: int,
    *,
    max_bindings: int = 24,
) -> List[Dict[str, Any]]:
    """Collect bounded `.and` / `Closed.and` / `Ev.and` / `And.intro` chain bindings & `.imp` targets."""
    if ".and" not in body and "And.intro" not in body:
        return []
    bindings: List[Dict[str, Any]] = []
    alias_trees: Dict[str, Tuple[Any, ...]] = {}

    def _add(tree: Tuple[Any, ...], bpat: str, scope: str, off: int, is_imp: bool = False) -> None:
        if len(bindings) >= max_bindings or tree[0] != "and":
            return
        lno = _offset_to_line(line_offsets, body_offset + off, base_line)
        bindings.append({
            "tree": tree,
            "binder": bpat.strip(),
            "scope": scope,
            "line_no": lno,
            "is_imp": is_imp,
        })

    # 1. `have v := <tree>` / `let v := <tree>` / `obtain ⟨...⟩ := <tree>`
    pat_bind = re.compile(rf"\b(?:have|let|obtain)\s+(⟨|[{_HYGIENE_IDENT_START}][{_HYGIENE_IDENT_CONT}]*)")
    for m in pat_bind.finditer(body):
        if len(bindings) >= max_bindings:
            break
        first_tok = m.group(1)
        if first_tok == "⟨":
            ang = _extract_balanced_angle(body, m.start(1))
            if ang is None or ang[1] - m.start(1) > 400:
                continue
            bpat = "⟨" + ang[0] + "⟩"
            after_b = ang[1]
        else:
            bpat = first_tok
            after_b = m.end(1)
        m_eq = re.match(r"\s*(?::[^=\n]{0,200})?:=", body[after_b : after_b + 240])
        if not m_eq:
            continue
        rhs_start = after_b + m_eq.end()
        rhs_txt, rhs_end = _extract_balanced_rhs_expr(body, rhs_start)
        if ".and" not in rhs_txt and "And.intro" not in rhs_txt:
            continue
        ast = _parse_conj_combinator_tree(rhs_txt)
        if ast[0] != "and":
            continue
        scope = body[rhs_end:]
        if not bpat.startswith("⟨"):
            alias_trees[bpat] = ast
            _add(ast, bpat, scope, m.start(), is_imp=False)
        else:
            parts = _split_angle_tuple(bpat[1:-1])
            # `obtain ⟨x0, h⟩ := <Ev.and chain>`: `h` is the `∀ x ≥ x0, ∀ i, ...` tree when `h` is projected
            if len(parts) == 2:
                v2 = parts[1].strip()
                if _RE_HYGIENE_IDENT.fullmatch(v2) and v2 != "_":
                    p2, _b2 = _scan_var_projections(scope, v2)
                    if p2:
                        _add(ast, v2, scope, m.start(), is_imp=False)
                        continue
            _add(ast, bpat, scope, m.start(), is_imp=False)

    # 2. `<tree>.imp fun ... h => scope` and `(Closed|Ev).imp (<tree>) (fun ... h => scope)`
    def _extract_imp_lambda(after_str: str, abs_after: int) -> Optional[Tuple[str, str]]:
        mf = re.match(r"\s*(\(?\s*(?:fun|λ)\s+)([^=\n]{1,160}?)=>", after_str)
        if not mf:
            return None
        bstr = mf.group(2).strip()
        last_pat = ""
        if bstr.endswith("⟩"):
            # Extract trailing `⟨...⟩` pattern
            d = 0
            k = len(bstr) - 1
            while k >= 0:
                if bstr[k] in _HYGIENE_CLOSE:
                    d += 1
                elif bstr[k] in _HYGIENE_OPEN:
                    d -= 1
                    if d == 0:
                        last_pat = bstr[k:].strip()
                        break
                k -= 1
        else:
            btoks = bstr.split()
            if btoks:
                last_pat = btoks[-1]
        if not last_pat:
            return None
        return last_pat, body[abs_after + mf.end() :]

    for m in re.finditer(r"(?:\)|⟩|[A-Za-z0-9_'])\s*\.imp(?![A-Za-z0-9_'])", body):
        if len(bindings) >= max_bindings:
            break
        dot_pos = body.find(".imp", m.start())
        i = dot_pos - 1
        while i >= 0 and body[i].isspace():
            i -= 1
        if i < 0:
            continue
        ast: Optional[Tuple[Any, ...]] = None
        if body[i] == ")":
            d = 1
            j = i - 1
            while j >= 0 and d > 0 and i - j <= 6000:
                if body[j] in _HYGIENE_CLOSE:
                    d += 1
                elif body[j] in _HYGIENE_OPEN:
                    d -= 1
                j -= 1
            if d == 0:
                ast = _parse_conj_combinator_tree(body[j + 1 : i + 1])
        else:
            m_id = re.search(rf"([{_HYGIENE_IDENT_START}][{_HYGIENE_IDENT_CONT}.]*)$", body[: i + 1])
            if m_id:
                ast = alias_trees.get(m_id.group(1))
        if ast is None or ast[0] != "and":
            continue
        lam = _extract_imp_lambda(body[dot_pos + 4 : dot_pos + 240], dot_pos + 4)
        if lam is not None:
            _add(ast, lam[0], lam[1], dot_pos, is_imp=True)

    for m in re.finditer(rf"(?<![{_HYGIENE_IDENT_CONT}.])(?:[{_HYGIENE_IDENT_START}][{_HYGIENE_IDENT_CONT}.]*\.)?(?:Closed|Ev)\.imp(?![{_HYGIENE_IDENT_CONT}])", body):
        if len(bindings) >= max_bindings:
            break
        arg_tail = body[m.end() : m.end() + 4500]
        # Extract first top-level argument `<tree>` and second `<fun ... => ...>` or `?_`
        atoks = _split_top_level_app_args(arg_tail)
        if len(atoks) < 2:
            continue
        a1 = atoks[0].strip()
        ast = alias_trees.get(a1) or _parse_conj_combinator_tree(a1)
        if ast[0] != "and":
            continue
        a1_pos = body.find(a1, m.end())
        if a1_pos < 0:
            continue
        lam_start = a1_pos + len(a1)
        lam = _extract_imp_lambda(body[lam_start : lam_start + 240], lam_start)
        if lam is not None:
            _add(ast, lam[0], lam[1], m.start(), is_imp=True)

    return bindings


def _inspect_caller_tuple_usage(
    caller_body: str,
    caller_body_offset: int,
    caller_line_offsets: List[int],
    caller_base_line: int,
    target_name: str,
    arity: int,
    exists_depth: int,
) -> Dict[str, Any]:
    """Inspect how a single caller projects/destructures a tuple-returning target declaration."""
    tail = target_name.rsplit(".", 1)[-1]
    parts = target_name.split(".")
    sym_suffixes: Set[str] = set()
    for i in range(len(parts)):
        suf = ".".join(parts[i:])
        sym_suffixes.add(suf)
        sym_suffixes.add(f"_root_.{suf}")

    def _make_sym_re(syms: Set[str]) -> re.Pattern[str]:
        ordered = sorted(syms, key=len, reverse=True)
        alt = "|".join(re.escape(x) for x in ordered)
        return re.compile(rf"(?<![{_HYGIENE_IDENT_CONT}.])(?:{alt})(?![{_HYGIENE_IDENT_CONT}])")

    def _classify_destruct_leg(pv: str, rest_after: str) -> bool:
        """Return True if destructured leg `pv` (possibly nested `⟨...⟩`) is read in `rest_after`."""
        s = pv.strip()
        if s in ("_", "-"):
            return False
        if _RE_HYGIENE_IDENT.fullmatch(s):
            return (not s.startswith("_")) and (_count_ident_refs(s, rest_after) > 0)
        if "⟨" in s:
            sub_idents = [
                tok for tok in _RE_HYGIENE_IDENT.findall(s)
                if tok != "_" and tok not in _HYGIENE_STOP_WORDS
            ]
            if not sub_idents:
                return False
            return any((not tok.startswith("_")) and (_count_ident_refs(tok, rest_after) > 0) for tok in sub_idents)
        return True

    def _record_destruct_legs(
        pat_items: Sequence[str],
        rest_after: str,
        *,
        rem_exists: int = 0,
    ) -> bool:
        offset_ex = (
            0
            if (rem_exists <= 0 or len(pat_items) <= arity)
            else min(rem_exists, len(pat_items) - arity)
        )
        leg_items = list(pat_items[offset_ex:])
        if len(leg_items) < 2:
            return False
        for li in range(min(arity, len(leg_items))):
            if li == arity - 1 and len(leg_items) > arity:
                # Surplus trailing components in `obtain ⟨a, b, c, d, e⟩` belong to an `∃`/`Σ`/nested last leg.
                tail_vars = leg_items[arity - 1 :]
                if any(_classify_destruct_leg(pv, rest_after) for pv in tail_vars):
                    read_legs.add(li)
                else:
                    discarded_legs.add(li)
            else:
                if _classify_destruct_leg(leg_items[li], rest_after):
                    read_legs.add(li)
                else:
                    discarded_legs.add(li)
        return True

    def _has_direct_rhs_proj(rhs_txt: str, rhs_m: re.Match[str]) -> bool:
        if _RE_DOT_PROJ_CHAIN.match(rhs_txt, rhs_m.end()):
            return True
        if re.match(r"\s*\.and\b", rhs_txt[rhs_m.end() :]):
            return True
        back_i = rhs_m.start() - 1
        while back_i >= 0 and (rhs_txt[back_i].isspace() or rhs_txt[back_i] == "@"):
            back_i -= 1
        while back_i >= 0 and rhs_txt[back_i] == "(":
            if rhs_txt[back_i + 1 : rhs_m.start()].strip().lstrip("@").strip():
                break
            d = 1
            f = back_i + 1
            nr = len(rhs_txt)
            while f < nr and d > 0:
                if rhs_txt[f] in _HYGIENE_OPEN:
                    d += 1
                elif rhs_txt[f] in _HYGIENE_CLOSE:
                    d -= 1
                f += 1
            if d == 0 and _RE_DOT_PROJ_CHAIN.match(rhs_txt, f):
                return True
            back_i -= 1
            while back_i >= 0 and rhs_txt[back_i].isspace():
                back_i -= 1
        return False

    tracked_syms: Set[str] = set(sym_suffixes)
    alias_exists: Dict[str, int] = {s: exists_depth for s in sym_suffixes}
    unwrapped_aliases: Set[str] = set()  # aliases where >=1 outer `∃` layer was peeled
    read_legs: Set[int] = set()
    discarded_legs: Set[int] = set()
    proj_1 = 0
    proj_2 = 0
    proj_examples: List[str] = []
    whole_value = False
    usage_lines: List[int] = []
    and_chain_whole = False
    and_chain_structured = False

    # Up to 6 passes so `obtain ⟨c₁, hc₁⟩ := mlTOf` -> `have hY' := hc₁ ...` -> `choose ... using hY'` propagates cleanly
    for _pass in range(6):
        sym_re = _make_sym_re(tracked_syms)
        new_aliases: Dict[str, int] = {}
        new_unwrapped: Set[str] = set()

        # Pass A: `obtain`/`rcases`/`choose`/`have`/`let` binding extraction & alias propagation
        rel = 0
        for raw_ln in caller_body.split("\n"):
            ln_start = rel
            ln_end = rel + len(raw_ln)
            rel = ln_end + 1
            lno = _offset_to_line(caller_line_offsets, caller_body_offset + ln_start, caller_base_line)

            # 1. `obtain`/`have`/`let` with balanced `⟨...⟩` (single-line or multi-line pattern & RHS)
            m_pat = re.search(r"\b(?:obtain|have|let)\s+⟨", raw_ln)
            if m_pat:
                ang = _extract_balanced_angle(caller_body, ln_start + m_pat.end() - 1)
                if ang is not None and ang[1] - (ln_start + m_pat.end() - 1) <= 2500:
                    after_ang_slice = caller_body[ang[1] : ang[1] + 500]
                    m_eq = re.match(r"\s*(?::[^=;]*?)?:=", after_ang_slice)
                    if m_eq:
                        rhs_start = ang[1] + m_eq.end()
                        rhs_full, rhs_end = _extract_balanced_rhs_expr(caller_body, rhs_start)
                        rhs_m = sym_re.search(rhs_full) if rhs_full else None
                        if rhs_m is not None:
                            if _parse_conj_combinator_tree(rhs_full)[0] == "and":
                                continue
                            eol_after = caller_body.find("\n", ang[1])
                            stmt_end = max(rhs_end, len(caller_body) if eol_after < 0 else eol_after)
                            rest_after = caller_body[stmt_end:]
                            pat_items = _split_angle_tuple(ang[0])
                            rhs_sym = rhs_m.group(0)
                            rem_ex = alias_exists.get(rhs_sym, exists_depth)
                            if rem_ex > 0 and 2 <= len(pat_items) <= rem_ex + 1:
                                peeled = len(pat_items) - 1
                                witness_var = pat_items[-1].strip()
                                new_rem = max(0, rem_ex - peeled)
                                if _RE_HYGIENE_IDENT.fullmatch(witness_var) and witness_var != "_":
                                    new_aliases[witness_var] = new_rem
                                    if new_rem < exists_depth:
                                        new_unwrapped.add(witness_var)
                                    usage_lines.append(lno)
                                continue
                            if _record_destruct_legs(pat_items, rest_after, rem_exists=rem_ex):
                                usage_lines.append(lno)
                                continue

            # 2. `choose ... using <sym>` destructuring (handles nested `And` conjuncts & `∃` witnesses)
            m_ch = re.match(r"^\s*(?:·\s*)?choose[!?]*(?=\s|$)", raw_ln)
            if m_ch:
                ch_region = caller_body[ln_start : ln_start + 700]
                m_ch_full = re.match(rf"^\s*(?:·\s*)?choose[!?]*\s+([\s\S]{{1,350}}?)\s+\busing(?![{_HYGIENE_IDENT_CONT}])", ch_region)
                if m_ch_full and ";" not in m_ch_full.group(1) and ":=" not in m_ch_full.group(1):
                    using_rhs, using_end = _extract_balanced_rhs_expr(caller_body, ln_start + m_ch_full.end())
                    src_m = sym_re.search(using_rhs) if using_rhs else None
                    if src_m is not None and not _has_direct_rhs_proj(using_rhs, src_m):
                        vars_toks = [t for t, _is_pat in _parse_intro_tokens(m_ch_full.group(1))]
                        if vars_toks:
                            rhs_sym = src_m.group(0)
                            rem_ex = alias_exists.get(rhs_sym, exists_depth)
                            rest_after = caller_body[max(ln_end, using_end) :]
                            if rem_ex > 0 and 2 <= len(vars_toks) <= rem_ex + 1:
                                peeled = len(vars_toks) - 1
                                last_v = vars_toks[-1].strip()
                                new_rem = max(0, rem_ex - peeled)
                                if _RE_HYGIENE_IDENT.fullmatch(last_v) and last_v != "_":
                                    new_aliases[last_v] = new_rem
                                    if new_rem < exists_depth:
                                        new_unwrapped.add(last_v)
                                    usage_lines.append(lno)
                                continue
                            if _record_destruct_legs(vars_toks, rest_after, rem_exists=rem_ex):
                                usage_lines.append(lno)
                                continue

            # 3. `rcases ... sym ... with ⟨...⟩`
            m_rc = re.match(r"^\s*(?:·\s*)?rcases\b", raw_ln)
            if m_rc:
                rc_region = caller_body[ln_start : ln_start + 700]
                m_rc_full = re.match(r"^\s*(?:·\s*)?rcases\s+([\s\S]{1,300}?)\s+\bwith\s+⟨", rc_region)
                if m_rc_full:
                    src_part = m_rc_full.group(1)
                    src_m = sym_re.search(src_part)
                    if src_m is not None:
                        if _parse_conj_combinator_tree(src_part)[0] == "and":
                            continue
                        ang_rc = _extract_balanced_angle(caller_body, ln_start + m_rc_full.end() - 1)
                        if ang_rc is not None:
                            rest_after = caller_body[ang_rc[1] :]
                            pat_items = _split_angle_tuple(ang_rc[0])
                            rhs_sym = src_m.group(0)
                            rem_ex = alias_exists.get(rhs_sym, exists_depth)
                            if rem_ex > 0 and 2 <= len(pat_items) <= rem_ex + 1:
                                peeled = len(pat_items) - 1
                                witness_var = pat_items[-1].strip()
                                new_rem = max(0, rem_ex - peeled)
                                if _RE_HYGIENE_IDENT.fullmatch(witness_var) and witness_var != "_":
                                    new_aliases[witness_var] = new_rem
                                    if new_rem < exists_depth:
                                        new_unwrapped.add(witness_var)
                                    usage_lines.append(lno)
                                continue
                            if _record_destruct_legs(pat_items, rest_after, rem_exists=rem_ex):
                                usage_lines.append(lno)
                                continue

            # 4. Plain `have v := ... sym ...` / `let v := ... sym ...` (including multi-line RHS)
            m_al = re.search(rf"(?<![{_HYGIENE_IDENT_CONT}.])(?:haveI?|letI?)\s+([{_HYGIENE_IDENT_START}][{_HYGIENE_IDENT_CONT}]*)(?![{_HYGIENE_IDENT_CONT}])", raw_ln)
            if m_al:
                vname = m_al.group(1)
                if vname not in tracked_syms:
                    after_v_slice = caller_body[ln_start + m_al.end() : ln_start + m_al.end() + 400]
                    m_eq_al = re.match(r"\s*(?::[^=;]*?)?:=", after_v_slice)
                    if m_eq_al:
                        rhs_start = ln_start + m_al.end() + m_eq_al.end()
                        rhs_full, _rhs_end = _extract_balanced_rhs_expr(caller_body, rhs_start)
                        rhs_m = sym_re.search(rhs_full) if rhs_full else None
                        if rhs_m is not None and not _has_direct_rhs_proj(rhs_full, rhs_m):
                            rhs_sym = rhs_m.group(0)
                            new_aliases[vname] = alias_exists.get(rhs_sym, exists_depth)
                            if rhs_sym in unwrapped_aliases or new_aliases[vname] < exists_depth:
                                new_unwrapped.add(vname)

        added = {k: v for k, v in new_aliases.items() if k not in tracked_syms}
        if not added:
            break
        tracked_syms.update(added.keys())
        alias_exists.update(added)
        unwrapped_aliases |= new_unwrapped

    # Pass A2: bounded `.and` / `Closed.and` / `Ev.and` / `And.intro` chain projection inspection
    sym_re = _make_sym_re(tracked_syms)
    for bnd in _collect_and_chain_bindings(caller_body, caller_line_offsets, caller_body_offset, caller_base_line):
        for lpath, ltxt in _iter_tree_leaves(bnd["tree"]):
            ltoks = _split_top_level_app_args(ltxt)
            lhead = ltoks[0].lstrip("@") if ltoks else ""
            if not (lhead and sym_re.fullmatch(lhead)):
                continue
            target_var, rem_path = _navigate_pattern_path(bnd["binder"], lpath)
            if target_var is None or target_var in ("_", "-"):
                and_chain_structured = True
                usage_lines.append(bnd["line_no"])
                discarded_legs.update(range(arity))
                continue
            if not rem_path and target_var.startswith("⟨"):
                ang_leaf = _extract_balanced_angle(target_var, 0)
                if ang_leaf is not None:
                    pitems = _split_angle_tuple(ang_leaf[0])
                    if _record_destruct_legs(pitems, bnd["scope"]):
                        and_chain_structured = True
                        usage_lines.append(bnd["line_no"])
                continue
            if not _RE_HYGIENE_IDENT.fullmatch(target_var):
                continue
            pchains, bare_use = _scan_var_projections(bnd["scope"], target_var)
            if bare_use:
                and_chain_whole = True
            for steps in pchains:
                if len(steps) <= len(rem_path):
                    if rem_path[: len(steps)] == steps:
                        and_chain_whole = True
                    continue
                if steps[: len(rem_path)] != rem_path:
                    continue
                sub_steps = steps[len(rem_path) :]
                and_chain_structured = True
                usage_lines.append(bnd["line_no"])
                if sub_steps[0] == 1:
                    proj_1 += 1
                else:
                    proj_2 += 1
                for li in _proj_steps_to_legs(sub_steps, arity):
                    read_legs.add(li)
                if len(proj_examples) < 6:
                    proj_examples.append("." + ".".join(str(x) for x in sub_steps))

    # Pass B: scan all dot projections `(_root_.sym ...).1`, `(@_root_.sym ...).1`, `sym.2.1`, `And.left (sym ...)`
    saw_any_ref = False
    saw_structured_use = bool(read_legs or discarded_legs or and_chain_structured)

    for m in sym_re.finditer(caller_body):
        saw_any_ref = True
        lno = _offset_to_line(caller_line_offsets, caller_body_offset + m.start(), caller_base_line)
        # 1. Direct projection immediately after `sym`: `sym.1` / `sym.2.1` / `sym.left`
        mp = _RE_DOT_PROJ_CHAIN.match(caller_body, m.end())
        if mp:
            steps = _parse_proj_chain(mp.group(1))
            if steps:
                saw_structured_use = True
                usage_lines.append(lno)
                if steps[0] == 1:
                    proj_1 += 1
                else:
                    proj_2 += 1
                for li in _proj_steps_to_legs(steps, arity):
                    read_legs.add(li)
                if len(proj_examples) < 6:
                    proj_examples.append(mp.group(1))
                continue

        # 2. Parenthesized call projection: `(_root_.sym arg1 arg2).1`, `(@_root_.sym arg1 arg2).2.1`
        back_i = m.start() - 1
        while back_i >= 0 and (caller_body[back_i].isspace() or caller_body[back_i] == "@"):
            back_i -= 1
        matched_paren_proj = False
        while back_i >= 0 and caller_body[back_i] == "(":
            if caller_body[back_i + 1 : m.start()].strip().lstrip("@").strip():
                break
            depth = 1
            fwd_i = back_i + 1
            n_cb = len(caller_body)
            while fwd_i < n_cb and depth > 0:
                if caller_body[fwd_i] in _HYGIENE_OPEN:
                    depth += 1
                elif caller_body[fwd_i] in _HYGIENE_CLOSE:
                    depth -= 1
                fwd_i += 1
            if depth != 0:
                break
            mp2 = _RE_DOT_PROJ_CHAIN.match(caller_body, fwd_i)
            if mp2:
                steps = _parse_proj_chain(mp2.group(1))
                if steps:
                    saw_structured_use = True
                    usage_lines.append(lno)
                    if steps[0] == 1:
                        proj_1 += 1
                    else:
                        proj_2 += 1
                    for li in _proj_steps_to_legs(steps, arity):
                        read_legs.add(li)
                    if len(proj_examples) < 6:
                        proj_examples.append(mp2.group(1))
                    matched_paren_proj = True
                    break
            # Check outer wrapping parens `((sym ...)).1`
            back_i -= 1
            while back_i >= 0 and caller_body[back_i].isspace():
                back_i -= 1
        if matched_paren_proj:
            continue

        # 3. Prefix projector `And.left` / `And.right` / `Prod.fst` / `Prod.snd` right before `@?(sym` or `@?sym`
        pre_ctx = caller_body[max(0, m.start() - 28) : m.start()]
        m_pre = re.search(r"\b(?:And\.(left|right)|Prod\.(fst|snd)|PProd\.(fst|snd))\s*\(?\s*@?\s*$", pre_ctx)
        if m_pre:
            tok_p = next(g for g in m_pre.groups() if g is not None)
            step = 1 if tok_p in ("left", "fst") else 2
            saw_structured_use = True
            usage_lines.append(lno)
            if step == 1:
                proj_1 += 1
            else:
                proj_2 += 1
            for li in _proj_steps_to_legs([step], arity):
                read_legs.add(li)
            if len(proj_examples) < 6:
                proj_examples.append("." + tok_p)
            continue

    if and_chain_whole and not and_chain_structured:
        whole_value = True
    elif saw_any_ref and not saw_structured_use and not unwrapped_aliases:
        whole_value = True

    return {
        "read_legs": sorted(read_legs),
        "discarded_legs": sorted(discarded_legs - read_legs),
        "proj_1": proj_1,
        "proj_2": proj_2,
        "proj_examples": proj_examples,
        "whole_value": whole_value,
        "line_no": min(usage_lines) if usage_lines else caller_base_line,
        "tail": tail,
    }


def _is_pure_tuple_alias_body(body_text: str, target_name: str) -> bool:
    """Detect 1-hop forwarding wrappers (`first | exact @_root_.Foo | ...` or `(fun ... => Foo ...)`)."""
    if not body_text:
        return False
    tail = target_name.rsplit(".", 1)[-1]
    if "⟨" in body_text or _RE_DOT_PROJ_CHAIN.search(body_text):
        return False
    return bool(re.search(rf"\b(?:exact|apply|first\s*\|)\b[\s\S]*\b{re.escape(tail)}\b", body_text))


def _audit_tuple_unread(
    conn: sqlite3.Connection,
    did: int,
    decl_name: str,
    tuple_kind: str,
    legs: List[str],
    exists_depth: int,
    *,
    has_dm: bool,
    sroot: str,
    src_fallback: Dict[str, Tuple[str, int]],
    file_cache: Dict[str, Dict[str, Any]],
    kernel_tuple_type_edges: List[str],
    max_callers: int = 50,
) -> Tuple[Dict[str, Any], List[Dict[str, Any]]]:
    """Inspect callers of a tuple/`And`-returning declaration (with 1-hop pure alias unwrapping)."""
    arity = len(legs)

    def _query_project_callers(dst_id: int) -> List[Tuple[int, str, str, Optional[str]]]:
        if has_dm:
            crows = conn.execute(
                "SELECT d.id, d.name, d.kind, m.module, m.method "
                "FROM edges e "
                "JOIN decls d ON d.id = e.src "
                "LEFT JOIN decl_module m ON m.decl_id = d.id "
                "WHERE e.dst = ? ORDER BY d.id",
                (dst_id,),
            ).fetchall()
        else:
            crows = [
                (r[0], r[1], r[2], None, None)
                for r in conn.execute(
                    "SELECT d.id, d.name, d.kind FROM edges e JOIN decls d ON d.id = e.src WHERE e.dst = ? ORDER BY d.id",
                    (dst_id,),
                ).fetchall()
            ]
        out: List[Tuple[int, str, str, Optional[str]]] = []
        for cid, cnm, ckd, cmod, cmeth in crows:
            cnm_s = str(cnm)
            if _is_compiler_aux_name(cnm_s):
                continue
            if not _is_project_decl(cnm_s, cmod, cmeth, has_dm):
                continue
            resolved_mod = cmod
            if resolved_mod is None and cnm_s in src_fallback:
                resolved_mod = src_fallback[cnm_s][0]
            out.append((int(cid), cnm_s, str(ckd), resolved_mod))
        return out

    proj_callers = _query_project_callers(did)
    callers_total = len(proj_callers)
    callers_truncated = callers_total > max_callers
    proj_callers = proj_callers[:max_callers]

    leg_read_counts = [0] * arity
    leg_discard_counts = [0] * arity
    total_proj_1 = 0
    total_proj_2 = 0
    whole_value_callers = 0
    callers_inspected = 0
    caller_details: List[Dict[str, Any]] = []
    alias_unwrap_cands: List[Tuple[int, str, int, int]] = []  # (cid, cnm, c_edepth, detail_idx)

    for cid, cnm, ckd, cmod in proj_callers:
        if not cmod:
            continue
        rel = cmod.replace(".", os.sep) + ".lean"
        cpath, _err = _safe_resolve_src_path(sroot, rel)
        if cpath is None:
            continue
        cspan = _extract_decl_source_span(cpath, cnm, file_cache)
        if cspan is None or not cspan["body_text"]:
            continue
        callers_inspected += 1
        usage = _inspect_caller_tuple_usage(
            cspan["body_text"],
            cspan["body_offset"],
            cspan["line_offsets"],
            cspan["start_line"],
            decl_name,
            arity,
            exists_depth,
        )
        total_proj_1 += usage["proj_1"]
        total_proj_2 += usage["proj_2"]
        if usage["whole_value"]:
            whole_value_callers += 1
            _ctel, cret = _parse_type_telescope(
                cspan["type_expr"], cspan["type_offset"], cspan["line_offsets"], cspan["start_line"]
            )
            c_tk, c_legs, c_edepth = _split_conjuncts(cret)
            if c_tk == tuple_kind and len(c_legs) == arity and _is_pure_tuple_alias_body(cspan["body_text"], decl_name):
                alias_unwrap_cands.append((cid, cnm, c_edepth, len(caller_details)))
        for li in usage["read_legs"]:
            leg_read_counts[li] += 1
        for li in usage["discarded_legs"]:
            leg_discard_counts[li] += 1
        caller_details.append({
            "name": cnm,
            "kind": ckd,
            "module": cmod,
            "line_no": usage["line_no"],
            "proj_1": usage["proj_1"],
            "proj_2": usage["proj_2"],
            "proj_examples": usage["proj_examples"],
            "read_legs": usage["read_legs"],
            "discarded_legs": usage["discarded_legs"],
            "whole_value": usage["whole_value"],
        })

    # Unwrap 1-hop pure alias wrappers (e.g. `GlobalTheory.T.*`) so downstream `.1`/`.2` projections aren't shadowed
    unwrapped_aliases_count = 0
    seen_2hop: Set[int] = {did} | {cid for cid, _nm, _kd, _mod in proj_callers}
    for alias_id, alias_nm, alias_edepth, detail_idx in alias_unwrap_cands[:5]:
        gc_all = [g for g in _query_project_callers(alias_id) if g[0] not in seen_2hop][:max_callers]
        if not gc_all:
            continue
        unwrapped_any = False
        for gcid, gcnm, gckd, gcmod in gc_all:
            if not gcmod:
                continue
            grel = gcmod.replace(".", os.sep) + ".lean"
            gpath, _err = _safe_resolve_src_path(sroot, grel)
            if gpath is None:
                continue
            gspan = _extract_decl_source_span(gpath, gcnm, file_cache)
            if gspan is None or not gspan["body_text"]:
                continue
            seen_2hop.add(gcid)
            unwrapped_any = True
            callers_inspected += 1
            usage2 = _inspect_caller_tuple_usage(
                gspan["body_text"],
                gspan["body_offset"],
                gspan["line_offsets"],
                gspan["start_line"],
                alias_nm,
                arity,
                alias_edepth,
            )
            total_proj_1 += usage2["proj_1"]
            total_proj_2 += usage2["proj_2"]
            if usage2["whole_value"]:
                whole_value_callers += 1
            for li in usage2["read_legs"]:
                leg_read_counts[li] += 1
            for li in usage2["discarded_legs"]:
                leg_discard_counts[li] += 1
            caller_details.append({
                "name": gcnm,
                "kind": gckd,
                "module": gcmod,
                "line_no": usage2["line_no"],
                "proj_1": usage2["proj_1"],
                "proj_2": usage2["proj_2"],
                "proj_examples": usage2["proj_examples"],
                "read_legs": usage2["read_legs"],
                "discarded_legs": usage2["discarded_legs"],
                "whole_value": usage2["whole_value"],
                "forwarded_via": alias_nm,
            })
        if unwrapped_any:
            unwrapped_aliases_count += 1
            whole_value_callers = max(0, whole_value_callers - 1)
            caller_details[detail_idx]["whole_value"] = False
            caller_details[detail_idx]["forwarded_alias"] = True

    unread_indices = [i for i in range(arity) if leg_read_counts[i] == 0]
    discarded_indices = [i for i in range(arity) if leg_discard_counts[i] > 0]
    one_sided_dot = (total_proj_1 > 0 and total_proj_2 == 0) or (total_proj_2 > 0 and total_proj_1 == 0)

    conjuncts_out = [
        {
            "index": i,
            "expr": _compact_snippet(legs[i], 100),
            "read_callers": leg_read_counts[i],
            "discarded_callers": leg_discard_counts[i],
        }
        for i in range(arity)
    ]

    summary = {
        "tuple_kind": tuple_kind,
        "arity": arity,
        "exists_depth": exists_depth,
        "kernel_type_edges": kernel_tuple_type_edges,
        "callers_total": callers_total,
        "callers_inspected": callers_inspected,
        "callers_truncated": callers_truncated,
        "unwrapped_aliases": unwrapped_aliases_count,
        "whole_value_callers": whole_value_callers,
        "proj_1_count": total_proj_1,
        "proj_2_count": total_proj_2,
        "unread_indices": unread_indices,
        "discarded_indices": discarded_indices,
        "one_sided_dot_projection": one_sided_dot,
        "conjuncts": conjuncts_out,
        "callers": caller_details,
    }

    findings: List[Dict[str, Any]] = []
    # Never emit tuple_unread when all conjuncts are read (`unread_indices == []`)
    if callers_inspected > 0 and unread_indices:
        has_global_unread = (whole_value_callers == 0) and (
            total_proj_1 > 0 or total_proj_2 > 0 or any(c["read_legs"] or c["discarded_legs"] for c in caller_details)
        )
        if has_global_unread or discarded_indices or one_sided_dot:
            reasons: List[str] = []
            if has_global_unread:
                leg_lbls = ", ".join(f"#{i}({_compact_snippet(legs[i], 40)})" for i in unread_indices[:5])
                reasons.append(f"unread leg(s): {leg_lbls}")
            if discarded_indices:
                d_lbls = ", ".join(f"#{i}({_compact_snippet(legs[i], 40)})" for i in discarded_indices[:5])
                reasons.append(f"explicitly discarded leg(s): {d_lbls}")
            if one_sided_dot:
                reasons.append(f"one-sided dot projection (.1={total_proj_1} vs .2={total_proj_2})")
            findings.append({
                "category": "tuple_unread",
                "kind": "conjunct_projection_imbalance",
                "confidence": "heuristic_source",
                "tuple_kind": tuple_kind,
                "arity": arity,
                "proj_1_count": total_proj_1,
                "proj_2_count": total_proj_2,
                "unread_indices": unread_indices,
                "discarded_indices": discarded_indices,
                "kernel_type_edges": kernel_tuple_type_edges,
                "detail": f"{tuple_kind}({arity} legs) across {callers_inspected} caller(s): " + "; ".join(reasons),
            })

    return summary, findings


def _audit_and_chain_consumers(
    conn: sqlite3.Connection,
    did: int,
    span: Dict[str, Any],
    *,
    has_dm: bool,
    sroot: str,
    src_fallback: Dict[str, Tuple[str, int]],
    file_cache: Dict[str, Dict[str, Any]],
) -> List[Dict[str, Any]]:
    """Consumer-side check for `.and`/`Closed.and`/`Ev.and` chains projecting only a subset of a leaf's conjuncts."""
    body = span["body_text"]
    if ".and" not in body and "And.intro" not in body:
        return []
    bindings = _collect_and_chain_bindings(
        body, span["line_offsets"], span["body_offset"], span["start_line"]
    )
    if not bindings:
        return []

    if has_dm:
        dep_rows = conn.execute(
            "SELECT d.id, d.name, m.module, m.method "
            "FROM edges e JOIN decls d ON d.id = e.dst "
            "LEFT JOIN decl_module m ON m.decl_id = d.id "
            "WHERE e.src = ?",
            (did,),
        ).fetchall()
    else:
        dep_rows = [
            (r[0], r[1], None, None)
            for r in conn.execute(
                "SELECT d.id, d.name FROM edges e JOIN decls d ON d.id = e.dst WHERE e.src = ?",
                (did,),
            ).fetchall()
        ]
    proj_deps: List[Tuple[int, str, str]] = []
    for dep_id, dep_nm, dep_mod, dep_meth in dep_rows:
        dnm_s = str(dep_nm)
        if _is_compiler_aux_name(dnm_s) or not _is_project_decl(dnm_s, dep_mod, dep_meth, has_dm):
            continue
        rmod = dep_mod or (src_fallback[dnm_s][0] if dnm_s in src_fallback else None)
        if rmod:
            proj_deps.append((int(dep_id), dnm_s, str(rmod)))
    if not proj_deps:
        return []

    def _match_dep(head: str) -> Optional[Tuple[int, str, str]]:
        h = re.sub(r"\.\{[^}]*\}$", "", head.lstrip("@"))
        if h.startswith("_root_."):
            h = h[7:]
        if not h:
            return None
        exact = [d for d in proj_deps if d[1] == h]
        if len(exact) == 1:
            return exact[0]
        suf = [d for d in proj_deps if d[1].endswith("." + h)]
        if len(suf) == 1:
            return suf[0]
        tail_h = h.rsplit(".", 1)[-1]
        tails = [d for d in proj_deps if d[1] == tail_h or d[1].endswith("." + tail_h)]
        return tails[0] if len(tails) == 1 else None

    findings: List[Dict[str, Any]] = []
    seen_leaf_decls: Set[str] = set()
    for bnd in bindings:
        for lpath, ltxt in _iter_tree_leaves(bnd["tree"]):
            ltoks = _split_top_level_app_args(ltxt)
            if not ltoks:
                continue
            target_var, rem_path = _navigate_pattern_path(bnd["binder"], lpath)
            if target_var is None or not _RE_HYGIENE_IDENT.fullmatch(target_var):
                continue
            pchains, bare_use = _scan_var_projections(bnd["scope"], target_var)
            if bare_use:
                continue
            sub_projs: List[List[int]] = []
            passed_whole = False
            for steps in pchains:
                if len(steps) <= len(rem_path):
                    if rem_path[: len(steps)] == steps:
                        passed_whole = True
                        break
                    continue
                if steps[: len(rem_path)] == rem_path:
                    sub_projs.append(steps[len(rem_path) :])
            if passed_whole or not sub_projs:
                continue
            dep_hit = _match_dep(ltoks[0])
            if dep_hit is None or dep_hit[1] in seen_leaf_decls:
                continue
            _dep_id, dep_nm, dep_mod = dep_hit
            rel = dep_mod.replace(".", os.sep) + ".lean"
            dpath, _err = _safe_resolve_src_path(sroot, rel)
            if dpath is None:
                continue
            dspan = _extract_decl_source_span(dpath, dep_nm, file_cache)
            if dspan is None or not dspan["type_expr"]:
                continue
            _dtel, dret = _parse_type_telescope(
                dspan["type_expr"], dspan["type_offset"], dspan["line_offsets"], dspan["start_line"]
            )
            tk, dep_legs, _dex = _split_conjuncts(dret)
            if tk is None or len(dep_legs) < 2:
                continue
            arity = len(dep_legs)
            read_legs: Set[int] = set()
            for sub in sub_projs:
                for li in _proj_steps_to_legs(sub, arity):
                    read_legs.add(li)
            unread = [i for i in range(arity) if i not in read_legs]
            if not unread:
                continue
            seen_leaf_decls.add(dep_nm)
            proj_strs = ["." + ".".join(str(x) for x in s) for s in sub_projs[:6]]
            unread_lbls = ", ".join(f"#{i}({_compact_snippet(dep_legs[i], 40)})" for i in unread[:5])
            findings.append({
                "category": "tuple_unread",
                "kind": "conjunct_projection_imbalance",
                "confidence": "heuristic_source",
                "line_no": bnd["line_no"],
                "tuple_kind": tk,
                "arity": arity,
                "leaf": _compact_snippet(ltxt, 60),
                "leaf_decl": dep_nm,
                "read_indices": sorted(read_legs),
                "unread_indices": unread,
                "proj_examples": proj_strs,
                "detail": (
                    f"`.and` chain leaf `{_compact_snippet(ltxt, 45)}` ({tk} {arity} legs) "
                    f"only projects {proj_strs}; unread leg(s): {unread_lbls}"
                ),
            })
    return findings


def _build_small_src_fallback(src_root: str, max_files: int = 500) -> Dict[str, Tuple[str, int]]:
    """Lightweight source index fallback when `kernel.db` has no `decl_module` table (e.g. tiny_demo)."""
    if not src_root or not os.path.isdir(src_root):
        return {}
    lean_files: List[str] = []
    for root, dirs, files in os.walk(src_root):
        dirs.sort()
        files.sort()
        for fn in files:
            if fn.endswith(".lean"):
                lean_files.append(os.path.relpath(os.path.join(root, fn), src_root))
                if len(lean_files) > max_files:
                    return {}
    if not lean_files:
        return {}
    src_exact, _by_ml, _nf = scan_source_decl_modules(src_root, workers=1)
    return src_exact


_HYGIENE_CORE_CLASS_HEADS = frozenset({
    "Subsingleton", "Unique", "Nonempty", "Inhabited", "Decidable", "DecidableEq",
    "DecidablePred", "DecidableRel", "Fintype", "Finite", "Infinite", "Countable",
    "Nontrivial", "Fact", "NeZero", "Zero", "One", "Add", "Mul", "Group", "AddGroup",
    "CommGroup", "AddCommGroup", "Ring", "CommRing", "Field", "DivisionRing",
    "Module", "Algebra", "TopologicalSpace", "IsTopologicalGroup", "DiscreteTopology",
    "T2Space", "CompactSpace", "LocallyCompactSpace", "ConnectedSpace", "Category",
    "Functor.Faithful", "Functor.Full", "Mono", "Epi", "IsIso", "IsEmpty",
    "MeasurableSpace", "MeasureSpace", "NormedAddCommGroup", "NormedSpace",
    "LocallyOfFinitePresentation", "QuasiCompact", "QuasiSeparated", "IsNoetherian",
    "IsNoetherianRing", "IsDomain", "IsIntegralDomain", "IsLocalRing",
    "IsPrincipalIdealRing", "IsDedekindDomain", "IsReduced", "ZeroLEOneClass",
    "CharZero", "CompleteLattice", "Lattice", "SemilatticeInf", "SemilatticeSup",
    "PartialOrder", "LinearOrder", "Preorder",
})
_HYGIENE_NON_CLASS_HEADS = frozenset({
    "Prop", "Type", "Sort", "True", "False", "Eq", "HEq", "Iff", "And", "Or", "Not",
    "Exists", "Subtype", "Prod", "PProd", "Sum", "Sigma", "PSigma", "Nat", "Int",
    "Bool", "Char", "String", "Fin", "List", "Array", "Set", "Finset", "Multiset",
    "Option", "Real", "Complex", "Unit", "PUnit", "Empty", "PEmpty", "Vector",
    "Matrix", "Submodule", "Ideal", "LinearMap",
})


def hygiene_decls(
    kernel_db_path: str,
    decls: Sequence[str],
    *,
    src_root: Optional[str] = None,
    cone_depth: int = 0,
    only: str = "all",
    max_decls: int = 200,
    max_callers: int = 50,
    continue_on_error: bool = False,
    include_noisy: bool = False,
    strict_binders: bool = False,
    include_semantic: bool = False,
) -> Dict[str, Any]:
    """Generic Lean 4 proof-hygiene auditor (`dropped`, `true_slot`, `tuple_unread`, opt-in `semantic`).

    Opens `kernel_db_path` strictly read-only (`mode=ro` + `PRAGMA query_only=1`).
    """
    if not decls:
        raise ValueError("at least one declaration is required for hygiene")
    if cone_depth < 0:
        raise ValueError(f"cone_depth must be >= 0, got {cone_depth}")
    if max_decls < 1:
        raise ValueError(f"max_decls must be >= 1, got {max_decls}")
    if only not in ("dropped", "true_slot", "tuple_unread", "semantic", "all"):
        raise ValueError(f"invalid --only filter {only!r} (expected dropped|true_slot|tuple_unread|semantic|all)")

    sroot = src_root or default_src_root()
    t0 = time.time()
    conn = _open_kernel_ro(kernel_db_path)
    try:
        has_dm = _has_decl_module_rows(conn)
        has_dm_mapped = has_dm and (
            conn.execute("SELECT 1 FROM decl_module WHERE module IS NOT NULL LIMIT 1").fetchone() is not None
        )
        has_consts = _has_table(conn, "consts")
        src_fallback = _build_small_src_fallback(sroot) if not has_dm_mapped else {}

        # Resolve target declarations
        target_ids: List[Tuple[int, str, str, Optional[str]]] = []  # (did, name, query, resolved_from)
        target_id_set: Set[int] = set()
        errors: List[Dict[str, Any]] = []
        for q in decls:
            try:
                did, name, resolved_from = _resolve_decl_id(conn, q, allow_suffix=True)
            except LookupError as e:
                if not continue_on_error:
                    raise
                errors.append({"query": q, "error": str(e)})
                continue
            if did not in target_id_set:
                target_id_set.add(did)
                target_ids.append((did, name, q, resolved_from))

        # Optional shallow backward project-only cone expansion
        worklist: List[Tuple[int, int]] = [(did, 0) for did, _nm, _q, _rf in target_ids]
        visited_hops: Dict[int, int] = {did: 0 for did, _nm, _q, _rf in target_ids}
        truncated = False
        if cone_depth > 0 and worklist:
            q_bfs: collections.deque = collections.deque(worklist)
            while q_bfs:
                u, h = q_bfs.popleft()
                if h >= cone_depth:
                    continue
                if has_dm:
                    nrows = conn.execute(
                        "SELECT d.id, d.name, m.module, m.method "
                        "FROM edges e JOIN decls d ON d.id = e.dst "
                        "LEFT JOIN decl_module m ON m.decl_id = d.id "
                        "WHERE e.src = ? ORDER BY d.id",
                        (u,),
                    ).fetchall()
                else:
                    nrows = [
                        (r[0], r[1], None, None)
                        for r in conn.execute(
                            "SELECT d.id, d.name FROM edges e JOIN decls d ON d.id = e.dst WHERE e.src = ? ORDER BY d.id",
                            (u,),
                        ).fetchall()
                    ]
                for nb_id_raw, nb_nm, nb_mod, nb_meth in nrows:
                    nb_id = int(nb_id_raw)
                    if nb_id in visited_hops:
                        continue
                    nb_nm_s = str(nb_nm)
                    if _is_compiler_aux_name(nb_nm_s):
                        continue
                    if not _is_project_decl(nb_nm_s, nb_mod, nb_meth, has_dm):
                        continue
                    if len(visited_hops) >= max_decls:
                        truncated = True
                        break
                    visited_hops[nb_id] = h + 1
                    worklist.append((nb_id, h + 1))
                    if h + 1 < cone_depth:
                        q_bfs.append((nb_id, h + 1))
                if truncated:
                    break

        # Fetch kernel metadata + special `True`/`And`/`Prod`/`PProd` edges in chunks
        all_ids = [did for did, _h in worklist]
        meta_by_id: Dict[int, Dict[str, Any]] = {}
        special_type_edges: Dict[int, Set[str]] = collections.defaultdict(set)
        special_val_edges: Dict[int, Set[str]] = collections.defaultdict(set)
        special_names = ("True", "And", "Prod", "PProd")
        sp_ph = ",".join("?" for _ in special_names)
        sp_id_to_name: Dict[int, str] = {
            int(r[0]): str(r[1])
            for r in conn.execute(f"SELECT id, name FROM decls WHERE name IN ({sp_ph})", special_names)
        }
        sp_ids = sorted(sp_id_to_name.keys())

        for ch in _chunks(all_ids, 900):
            ph = ",".join("?" for _ in ch)
            if has_dm:
                rows = conn.execute(
                    f"SELECT d.id, d.name, d.kind, d.fan_in, d.fan_out, d.live_mask, m.module, m.method "
                    f"FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id WHERE d.id IN ({ph})",
                    ch,
                ).fetchall()
            else:
                rows = [
                    (r[0], r[1], r[2], r[3], r[4], r[5], None, None)
                    for r in conn.execute(
                        f"SELECT id, name, kind, fan_in, fan_out, live_mask FROM decls WHERE id IN ({ph})",
                        ch,
                    ).fetchall()
                ]
            for r in rows:
                did = int(r[0])
                nm = str(r[1])
                mod = r[6]
                if mod is None and nm in src_fallback:
                    mod = src_fallback[nm][0]
                meta_by_id[did] = {
                    "id": did,
                    "name": nm,
                    "kind": str(r[2]),
                    "fan_in": int(r[3]),
                    "fan_out": int(r[4]),
                    "live_mask": int(r[5]),
                    "module": mod,
                    "method": r[7],
                }
            if sp_ids:
                sph = ",".join("?" for _ in sp_ids)
                for esrc, edst, ek in conn.execute(
                    f"SELECT src, dst, kind FROM edges WHERE src IN ({ph}) AND dst IN ({sph})",
                    (*ch, *sp_ids),
                ):
                    snm = sp_id_to_name[int(edst)]
                    eki = int(ek)
                    if eki in (1, 3):
                        special_type_edges[int(esrc)].add(snm)
                    if eki in (2, 3):
                        special_val_edges[int(esrc)].add(snm)

        query_by_id = {did: (q, rf) for did, _nm, q, rf in target_ids}
        file_cache: Dict[str, Dict[str, Any]] = {}
        def_edge_cache: Dict[int, List[Tuple[int, str, Optional[str]]]] = {}
        ind_edge_cache: Dict[int, List[Tuple[int, str, Optional[str], Optional[str]]]] = {}
        class_id_cache: Dict[int, bool] = {}
        class_head_cache: Dict[Tuple[int, str], bool] = {}

        def _get_ind_edges(src_id: int) -> List[Tuple[int, str, Optional[str], Optional[str]]]:
            if src_id in ind_edge_cache:
                return ind_edge_cache[src_id]
            if has_dm:
                rows_i = conn.execute(
                    "SELECT d.id, d.name, m.module, m.method "
                    "FROM edges e JOIN decls d ON d.id = e.dst "
                    "LEFT JOIN decl_module m ON m.decl_id = d.id "
                    "WHERE e.src = ? AND e.kind IN (1, 3) AND d.kind = 'inductive'",
                    (src_id,),
                ).fetchall()
            else:
                rows_i = [
                    (r[0], r[1], None, None)
                    for r in conn.execute(
                        "SELECT d.id, d.name FROM edges e JOIN decls d ON d.id = e.dst "
                        "WHERE e.src = ? AND e.kind IN (1, 3) AND d.kind = 'inductive'",
                        (src_id,),
                    ).fetchall()
                ]
            out_i = [(int(r[0]), str(r[1]), r[2], r[3]) for r in rows_i]
            ind_edge_cache[src_id] = out_i
            return out_i

        def _is_class_id(dst_id: int, dst_name: str, dst_mod: Optional[str], dst_meth: Optional[str]) -> bool:
            if dst_id in class_id_cache:
                return class_id_cache[dst_id]
            rmod = dst_mod or (src_fallback[dst_name][0] if dst_name in src_fallback else None)
            if _is_project_decl(dst_name, rmod, dst_meth, has_dm) and rmod:
                rel = str(rmod).replace(".", os.sep) + ".lean"
                dpath, _err = _safe_resolve_src_path(sroot, rel)
                if dpath is not None:
                    dspan = _extract_decl_source_span(dpath, dst_name, file_cache)
                    if dspan is not None:
                        res_p = dspan["keyword"] == "class"
                        class_id_cache[dst_id] = res_p
                        return res_p
            short = dst_name.rsplit(".", 1)[-1]
            if has_consts:
                ctors = conn.execute(
                    "SELECT name FROM consts WHERE decl_id = ? AND ckind = 'ctor' LIMIT 2",
                    (dst_id,),
                ).fetchall()
                if ctors and len(ctors) != 1:
                    class_id_cache[dst_id] = False
                    return False
            hit = conn.execute(
                "SELECT 1 FROM edges e JOIN decls s ON s.id = e.src "
                "WHERE e.dst = ? AND e.kind IN (1, 3) "
                "AND (s.name GLOB ? OR s.name GLOB ?) AND s.name NOT GLOB '*._*' LIMIT 1",
                (dst_id, f"inst{short}*", f"*.inst{short}*"),
            ).fetchone()
            res_e = hit is not None
            class_id_cache[dst_id] = res_e
            return res_e

        def _make_class_type_checker(cand_dids: List[int]) -> Callable[[str], bool]:
            def _is_class_type(type_str: str) -> bool:
                s = _strip_outer_parens(type_str)
                if not s:
                    return False
                for _ in range(8):
                    kw_all = _at_quantifier_or_lambda(s, 0, include_forall=True, include_exists=False, include_fun=False)
                    if kw_all > 0:
                        comma = _find_quantifier_comma(s, kw_all)
                        if comma < 0:
                            break
                        s = _strip_outer_parens(s[comma + 1 :])
                    else:
                        break
                if not s:
                    return False
                toks = _split_top_level_app_args(s)
                if not toks:
                    return False
                head = toks[0].lstrip("@")
                head = re.sub(r"\.\{[^}]*\}$", "", head)
                if head.startswith("_root_."):
                    head = head[7:]
                if not head or any(ch in head for ch in "=<≤≥∈∉∀∃λ→↔"):
                    return False
                short = head.rsplit(".", 1)[-1]
                if not short or not short[0].isupper():
                    return False
                if short in _HYGIENE_NON_CLASS_HEADS or head in _HYGIENE_NON_CLASS_HEADS:
                    return False
                if head in _HYGIENE_CORE_CLASS_HEADS or short in _HYGIENE_CORE_CLASS_HEADS:
                    return True
                for cdid in cand_dids:
                    ckey = (cdid, head)
                    if ckey in class_head_cache:
                        if class_head_cache[ckey]:
                            return True
                        continue
                    matched_ind: Optional[Tuple[int, str, Optional[str], Optional[str]]] = None
                    for d_id, d_nm, d_mod, d_meth in _get_ind_edges(cdid):
                        if d_nm == head or d_nm.endswith("." + head) or d_nm.rsplit(".", 1)[-1] == short:
                            matched_ind = (d_id, d_nm, d_mod, d_meth)
                            break
                    res_cls = _is_class_id(*matched_ind) if matched_ind is not None else False
                    class_head_cache[ckey] = res_cls
                    if res_cls:
                        return True
                return False

            return _is_class_type

        disp_base = os.path.dirname(os.path.realpath(sroot)) if os.path.basename(os.path.realpath(sroot)) == "src" else sroot

        want_dropped = only in ("all", "dropped")
        want_true = only in ("all", "true_slot")
        want_tuple = only in ("all", "tuple_unread")
        want_semantic = include_semantic or (only == "semantic")

        decl_reports: List[Dict[str, Any]] = []
        cat_counts: Dict[str, int] = {"dropped": 0, "true_slot": 0, "tuple_unread": 0}
        if want_semantic:
            cat_counts["semantic"] = 0
        sup_by_reason: Dict[str, int] = collections.Counter()
        sup_by_kind: Dict[str, int] = collections.Counter()
        sup_total = 0
        sem_hints_avail = 0
        decls_with_findings = 0

        for did, hop in worklist:
            meta = meta_by_id.get(did)
            if meta is None:
                continue
            nm = meta["name"]
            mod = meta["module"]
            q_info = query_by_id.get(did)

            entry: Dict[str, Any] = {
                "id": did,
                "name": nm,
                "kind": meta["kind"],
                "hop": hop,
                "module": mod,
                "anchor": None,
                "status": "ok",
                "findings": [],
            }
            if q_info is not None:
                entry["query"] = q_info[0]
                if q_info[1] is not None:
                    entry["resolved_from"] = q_info[1]

            if not mod:
                entry["status"] = "external_or_unmapped"
                decl_reports.append(entry)
                continue

            rel = mod.replace(".", os.sep) + ".lean"
            abs_path, err = _safe_resolve_src_path(sroot, rel)
            if abs_path is None:
                entry["status"] = err or "file_not_found"
                decl_reports.append(entry)
                continue

            span = _extract_decl_source_span(abs_path, nm, file_cache)
            if span is None:
                entry["status"] = "symbol_not_found_in_file"
                decl_reports.append(entry)
                continue

            disp_path = _rel_display_path(abs_path, disp_base)
            entry["anchor"] = f"{disp_path}:{span['start_line']}"
            entry["line_no"] = span["start_line"]
            entry["end_line"] = span["end_line"]
            entry["header"] = span["header_line"]

            # Skip child projection duplicates that resolve back to parent `structure`/`class`/`inductive`
            if span.get("resolved_via_parent") and span["keyword"] in ("structure", "class", "inductive"):
                entry["deduplicated_parent_projection"] = True
                decl_reports.append(entry)
                continue

            telescope, return_type = _parse_type_telescope(
                span["type_expr"], span["type_offset"], span["line_offsets"], span["start_line"]
            )

            raw_findings: List[Dict[str, Any]] = []
            if want_dropped:
                exp_telescope, _exp_ret, extra_spans = _expand_def_telescope(
                    conn,
                    did,
                    telescope,
                    return_type,
                    has_dm=has_dm,
                    sroot=sroot,
                    src_fallback=src_fallback,
                    file_cache=file_cache,
                    def_edge_cache=def_edge_cache,
                )
                cand_dids = [did] + [int(sp["decl_id"]) for sp in extra_spans if sp.get("decl_id")]
                inner_teles = _collect_inner_telescopes(span, extra_spans)
                raw_findings.extend(
                    _audit_dropped_binders(
                        span,
                        exp_telescope,
                        inner_telescopes=inner_teles,
                        is_class_type=_make_class_type_checker(cand_dids),
                    )
                )
            if want_true:
                k_true = ("True" in special_type_edges[did], "True" in special_val_edges[did])
                raw_findings.extend(_audit_true_slots(span, telescope, return_type, k_true))
            if want_tuple:
                tuple_kind, legs, exists_depth = _split_conjuncts(return_type)
                if tuple_kind is not None and len(legs) >= 2:
                    k_tup_edges = sorted(x for x in special_type_edges[did] if x in ("And", "Prod", "PProd"))
                    tsum, tfind = _audit_tuple_unread(
                        conn,
                        did,
                        nm,
                        tuple_kind,
                        legs,
                        exists_depth,
                        has_dm=has_dm,
                        sroot=sroot,
                        src_fallback=src_fallback,
                        file_cache=file_cache,
                        kernel_tuple_type_edges=k_tup_edges,
                        max_callers=max_callers,
                    )
                    entry["tuple_summary"] = tsum
                    raw_findings.extend(tfind)
                raw_findings.extend(
                    _audit_and_chain_consumers(
                        conn,
                        did,
                        span,
                        has_dm=has_dm,
                        sroot=sroot,
                        src_fallback=src_fallback,
                        file_cache=file_cache,
                    )
                )
            sem_raw = _audit_semantic_flags(span)
            if want_semantic:
                raw_findings.extend(sem_raw)
            elif sem_raw and only == "all":
                sem_hints_avail += len(sem_raw)

            findings: List[Dict[str, Any]] = []
            decl_sup = 0
            for f in raw_findings:
                sreason = f.get("suppression_reason")
                if sreason is not None:
                    keep = include_noisy or (strict_binders and sreason == "implicit_ctx_tactic")
                    if not keep:
                        decl_sup += 1
                        sup_total += 1
                        sup_by_reason[sreason] += 1
                        sup_by_kind[f.get("kind", "unknown")] += 1
                        continue
                    f["noise_tier"] = "noisy"
                findings.append(f)

            if decl_sup > 0:
                entry["suppressed_count"] = decl_sup
            entry["findings"] = findings
            if findings:
                decls_with_findings += 1
                for f in findings:
                    cat = f.get("category")
                    if cat in cat_counts:
                        cat_counts[cat] += 1
            decl_reports.append(entry)

        summary_out: Dict[str, Any] = {
            "decls_audited": len(decl_reports),
            "decls_with_findings": decls_with_findings,
            "total_findings": sum(cat_counts.values()),
            "by_category": cat_counts,
            "suppressed_counts": {
                "total": sup_total,
                "by_reason": dict(sorted(sup_by_reason.items())),
                "by_kind": dict(sorted(sup_by_kind.items())),
            },
            "errors_count": len(errors),
        }
        if sem_hints_avail > 0:
            summary_out["semantic_hints_available"] = sem_hints_avail

        return {
            "schema": "leanre.kernel.hygiene/1",
            "provenance": "L+heuristic_source",
            "kernel_db": os.path.basename(kernel_db_path),
            "src_root": _rel_display_path(sroot),
            "elapsed_s": round(time.time() - t0, 3),
            "params": {
                "decls": list(decls),
                "cone_depth": cone_depth,
                "only": only,
                "max_decls": max_decls,
                "continue_on_error": continue_on_error,
                "include_noisy": include_noisy,
                "strict_binders": strict_binders,
                "include_semantic": want_semantic,
            },
            "truncated": truncated,
            "summary": summary_out,
            "errors": errors,
            "decls": decl_reports,
        }
    finally:
        conn.close()


def format_hygiene_text(res: Dict[str, Any]) -> str:
    p = res["params"]
    s = res["summary"]
    bc = s["by_category"]
    sc = s.get("suppressed_counts") or {}
    sup_tot = int(sc.get("total", 0))
    sup_s = f", suppressed={sup_tot}" if sup_tot else ""
    trunc_s = " [TRUNCATED]" if res.get("truncated") else ""
    err_s = f", errors={s['errors_count']}" if s.get("errors_count") else ""
    sem_part = f", semantic={bc['semantic']}" if "semantic" in bc else ""
    lines = [
        f"[L+heuristic_source] kernel hygiene (audited={s['decls_audited']}, "
        f"with_findings={s['decls_with_findings']}, findings={s['total_findings']} "
        f"[dropped={bc['dropped']}, true_slot={bc['true_slot']}, tuple_unread={bc['tuple_unread']}{sem_part}], "
        f"cone_depth={p['cone_depth']}, only={p['only']}{sup_s}{err_s}, {res['elapsed_s']:.2f}s){trunc_s}"
    ]
    clean_cone_count = 0
    for d in res["decls"]:
        findings = d.get("findings") or []
        if d["hop"] > 0 and not findings:
            clean_cone_count += 1
            continue
        anc = d.get("anchor") or d.get("status") or "unmapped"
        hop_s = f" hop={d['hop']}" if p["cone_depth"] > 0 else ""
        lines.append(f"  {d['name']}  ({d['kind']}{hop_s}, {anc}) -> {len(findings)} finding(s)")
        for f in findings:
            cat = f["category"]
            kd = f["kind"]
            lno = f.get("line_no")
            loc_s = f"L{lno} " if lno is not None else ""
            conf = f.get("confidence", "heuristic_source")
            tactic_note = " [implicit-ctx tactic present]" if f.get("implicit_tactic_in_body") else ""
            role_note = f" [role={f['role']}]" if f.get("role") else ""
            lines.append(f"    [{cat}:{kd} {conf}] {loc_s}{f['detail']}{tactic_note}{role_note}")
        tsum = d.get("tuple_summary")
        if tsum is not None and (findings or d["hop"] == 0):
            lines.append(
                f"    tuple_summary: {tsum['tuple_kind']}({tsum['arity']} legs), "
                f"callers={tsum['callers_inspected']}/{tsum['callers_total']}, "
                f".1={tsum['proj_1_count']} .2={tsum['proj_2_count']}, "
                f"whole={tsum['whole_value_callers']}, unread={tsum['unread_indices']}"
            )
            for cd in tsum["callers"][:10]:
                via_s = f" [via {cd['forwarded_via']}]" if cd.get("forwarded_via") else (" [alias]" if cd.get("forwarded_alias") else "")
                lines.append(
                    f"      caller {cd['name']} (L{cd['line_no']}): "
                    f".1={cd['proj_1']} .2={cd['proj_2']} read={cd['read_legs']} "
                    f"discarded={cd['discarded_legs']}"
                    + (" [whole]" if cd["whole_value"] else "")
                    + via_s
                    + (f" projs={cd['proj_examples']}" if cd["proj_examples"] else "")
                )
    if clean_cone_count > 0:
        lines.append(f"  ({clean_cone_count} clean cone declaration(s) omitted)")
    if sup_tot > 0:
        by_r = sc.get("by_reason") or {}
        br_s = ", ".join(f"{k}={v}" for k, v in by_r.items())
        lines.append(f"  ({sup_tot} noisy finding(s) suppressed: {br_s}; pass --include-noisy / --strict-binders to inspect)")
    sem_avail = int(s.get("semantic_hints_available", 0))
    if sem_avail > 0:
        lines.append(f"  ({sem_avail} semantic flag hint(s) available: pass --semantic to inspect)")
    errs = res.get("errors") or []
    if errs:
        lines.append(f"  Unresolved targets ({len(errs)}):")
        for e in errs:
            lines.append(f"    {e['query']}: {e['error']}")
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
    p_e.add_argument("--config", default=None, help="Optional path to leanre.toml config file for roots/src_dir")
    p_e.add_argument("--rh-reference", action="store_true", help="Include RH reference reconciliation figures in kernel_report.json")
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
    p_sl.add_argument("decl", help="Exact declaration (or constant/suffix) name in kernel.db")
    p_sl.add_argument("--kernel-db", default=default_kernel_db_path(), help="Path to kernel.db (default: outputs/kernel/kernel.db)")
    p_sl.add_argument(
        "--direction", "--dir",
        dest="direction",
        choices=("backward", "bwd", "forward", "fwd", "both"),
        default="backward",
        help="Traversal direction: backward|bwd, forward|fwd, or both (default: backward)",
    )
    p_sl.add_argument("--depth", type=int, default=3, help="Max BFS hops from decl (default: 3)")
    p_sl.add_argument("--max-nodes", type=int, default=200, help="Max nodes in slice (default: 200)")
    p_sl.add_argument(
        "--edge-kind",
        choices=("type", "value", "both", "all", "type-only", "value-only", "type+value"),
        default="both",
        help="Edge filter: type (1,3), value (2,3), both/all (1,2,3), type-only (1), value-only (2), type+value (3)",
    )
    p_sl.add_argument("--stop-at", action="append", default=[], help="Stop expanding at prefix/decl or @external (repeatable)")
    p_sl.add_argument("--project-only", action="store_true", help="Exclude external (Mathlib/Init/Std/Lean) nodes from slice")
    p_sl.add_argument("--tree", default="ALL", help="Dominator tree label for node annotations (default: ALL)")
    p_sl.add_argument("--format", choices=("text", "json", "dot"), default=None, help="Output format")
    p_sl.add_argument("--json", action="store_true", help="Emit JSON output (alias for --format json)")
    p_sl.add_argument("--dot", action="store_true", help="Emit Graphviz DOT output (alias for --format dot)")
    p_sl.add_argument("--out", default=None, help="Optional file path to write output")
    p_sl.set_defaults(**{dest: _cmd_slice})

    p_td = sp.add_parser("type-deps", help="Inspect type deps, value-only deps, dom children, and paths-to-root")
    p_td.add_argument("decl", help="Exact declaration (or constant/suffix) name in kernel.db")
    p_td.add_argument("--kernel-db", default=default_kernel_db_path(), help="Path to kernel.db (default: outputs/kernel/kernel.db)")
    p_td.add_argument("--tree", default="ALL", help="Dominator tree label (default: ALL)")
    p_td.add_argument("--limit", type=int, default=50, help="Max items per section, 0=unlimited (default: 50)")
    p_td.add_argument("--json", action="store_true", help="Emit JSON output")
    p_td.add_argument("--out", default=None, help="Optional file path to write output")
    p_td.set_defaults(**{dest: _cmd_type_deps})

    p_ca = sp.add_parser("cone-audit", help="Exact, untruncated backward cone audit (axioms, taints, opaques, modules)")
    p_ca.add_argument("decls", nargs="+", help="One or more declaration names (exact, const, or unique suffix)")
    p_ca.add_argument("--kernel-db", default=default_kernel_db_path(), help="Path to kernel.db (default: outputs/kernel/kernel.db)")
    p_ca.add_argument("--project-only", action="store_true", help="Focus breakdowns & filters on project declarations")
    p_ca.add_argument("--filter-mod", default=None, help="Regex to match module names inside the backward cone")
    p_ca.add_argument("--flag-prefix", action="append", default=[], help="Flag namespace/module prefixes (e.g. Published., Examples₂; repeatable)")
    p_ca.add_argument("--top-mods", type=int, default=15, help="Top N module prefixes to report (default: 15)")
    p_ca.add_argument("--tree", default="ALL", help="Dominator tree label (default: ALL)")
    p_ca.add_argument("--continue-on-error", action="store_true", help="Report missing/ambiguous targets instead of aborting multi-decl batches")
    p_ca.add_argument("--json", action="store_true", help="Emit JSON output")
    p_ca.add_argument("--out", default=None, help="Optional file path to write output")
    p_ca.set_defaults(**{dest: _cmd_cone_audit})

    p_st = sp.add_parser(
        "stats",
        help="Compact batch lookup of declaration metrics in kernel.db",
        description=(
            "Compact batch lookup of declaration metrics in kernel.db. "
            "The `live` column is a bitmask over roots (0=dead; bit 1<<id per root in `roots`, "
            "e.g. live=31 = 1+2+4+8+16 across 5 roots)."
        ),
    )
    p_st.add_argument("decls", nargs="+", help="One or more declaration names (exact, module-prefixed, or unique suffix)")
    p_st.add_argument("--kernel-db", default=default_kernel_db_path(), help="Path to kernel.db (default: outputs/kernel/kernel.db)")
    p_st.add_argument("--tree", default="ALL", help="Dominator tree label (default: ALL)")
    p_st.add_argument("--src-root", default=None, help="Optional source root to resolve disk file:line anchors")
    p_st.add_argument("--with-alias", action="store_true", help="Inspect source bodies for 1-hop forwarding aliases beyond value_nodes==1")
    p_st.add_argument("--continue-on-error", action="store_true", help="Report missing/ambiguous targets instead of aborting batch")
    p_st.add_argument("--table", action="store_true", help="Format output as a Markdown table")
    p_st.add_argument("--json", action="store_true", help="Emit JSON output")
    p_st.add_argument("--out", default=None, help="Optional file path to write output")
    p_st.set_defaults(**{dest: _cmd_stats})

    p_cl = sp.add_parser("callers", help="Upward reverse-edge caller walk grouped by hop and parent")
    p_cl.add_argument("decls", nargs="+", help="One or more declaration names (exact, const, or unique suffix)")
    p_cl.add_argument("--kernel-db", default=default_kernel_db_path(), help="Path to kernel.db (default: outputs/kernel/kernel.db)")
    p_cl.add_argument("--depth", type=int, default=2, help="Max upward hops (default: 2)")
    p_cl.add_argument("--project-only", action="store_true", help="Include only project callers")
    p_cl.add_argument("--grouped", action="store_true", help="Group output hierarchically by hop and parent")
    p_cl.add_argument("--sort", choices=("dom", "fan_in", "name"), default="dom", help="Sort order (default: dom)")
    p_cl.add_argument("--limit", type=int, default=50, help="Max callers per parent, 0=unlimited (default: 50)")
    p_cl.add_argument("--tree", default="ALL", help="Dominator tree label (default: ALL)")
    p_cl.add_argument("--continue-on-error", action="store_true", help="Report missing/ambiguous targets instead of aborting multi-decl batches")
    p_cl.add_argument("--json", action="store_true", help="Emit JSON output")
    p_cl.add_argument("--out", default=None, help="Optional file path to write output")
    p_cl.set_defaults(**{dest: _cmd_callers})

    p_an = sp.add_parser("anchor", help="Map declarations to disk (module, path, line, header) and verify Markdown #L links")
    p_an.add_argument("decls", nargs="*", help="Zero or more declaration names to anchor on disk")
    p_an.add_argument("--verify-md", nargs="+", action="extend", default=[], help="Markdown file(s) whose GitHub blob #L links to verify")
    p_an.add_argument("--src-root", default=default_src_root(), help="Source root directory (default: data/rh_mirror/src)")
    p_an.add_argument("--kernel-db", default=default_kernel_db_path(), help="Path to kernel.db (default: outputs/kernel/kernel.db)")
    p_an.add_argument("--json", action="store_true", help="Emit JSON output")
    p_an.add_argument("--out", default=None, help="Optional file path to write output")
    p_an.set_defaults(**{dest: _cmd_anchor})

    p_hy = sp.add_parser("hygiene", help="Audit declarations for dropped/unused binders, True/trivial dummy slots, and tuple projection imbalance")
    p_hy.add_argument("decls", nargs="+", help="One or more declaration names (exact, const, module-prefixed, or unique suffix)")
    p_hy.add_argument("--kernel-db", default=default_kernel_db_path(), help="Path to kernel.db (default: outputs/kernel/kernel.db)")
    p_hy.add_argument("--src-root", default=default_src_root(), help="Source root directory (default: data/rh_mirror/src)")
    p_hy.add_argument("--cone-depth", type=int, default=0, help="Optional shallow backward project-cone depth (default: 0)")
    p_hy.add_argument(
        "--only",
        choices=("dropped", "true_slot", "tuple_unread", "semantic", "all"),
        default="all",
        help="Restrict findings to one category (default: all)",
    )
    p_hy.add_argument("--max-decls", type=int, default=200, help="Max declarations when --cone-depth > 0 (default: 200)")
    p_hy.add_argument("--continue-on-error", action="store_true", help="Report missing/ambiguous targets instead of aborting batch")
    p_hy.add_argument("--include-noisy", action="store_true", help="Show suppressed noisy findings (implicit-ctx, [Inst], local classes, activating-premise True)")
    p_hy.add_argument("--strict-binders", action="store_true", help="Show unused-binder findings even when implicit-context tactics are present in proof body")
    p_hy.add_argument("--semantic", "--include-semantic", dest="include_semantic", action="store_true", help="Include opt-in semantic flags (default_zero_branch, le_refl_closure)")
    p_hy.add_argument("--json", action="store_true", help="Emit JSON output")
    p_hy.add_argument("--out", default=None, help="Optional file path to write output")
    p_hy.set_defaults(**{dest: _cmd_hygiene})

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
        config=getattr(args, "config", None),
        rh_reference=True if getattr(args, "rh_reference", False) else None,
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
    conn = _open_kernel_ro(args.kernel_db)
    try:
        res = validate_taint_paths(conn)
    finally:
        conn.close()
    print(json.dumps(res, indent=2))
    return 0 if res["failures"] == 0 else 1


def _write_or_print(text: str, out_path: Optional[str]) -> None:
    if out_path:
        if os.path.islink(out_path):
            raise ValueError(f"refusing to write through symlink: {out_path}")
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
            project_only=bool(getattr(args, "project_only", False)),
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


def _cmd_cone_audit(args: argparse.Namespace) -> int:
    try:
        res = cone_audit_decls(
            kernel_db_path=args.kernel_db,
            decls=args.decls,
            project_only=args.project_only,
            filter_mod=args.filter_mod,
            flag_prefixes=args.flag_prefix,
            top_mods=args.top_mods,
            tree=args.tree,
            continue_on_error=bool(getattr(args, "continue_on_error", False)),
        )
    except (LookupError, ValueError, FileNotFoundError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    text = json.dumps(res, indent=2, ensure_ascii=False) if args.json else format_cone_audit_text(res)
    _write_or_print(text, args.out)
    if res.get("errors"):
        if not res["targets"]:
            return 1
        print(f"warning: {len(res['errors'])} target(s) failed to resolve", file=sys.stderr)
    return 0


def _cmd_stats(args: argparse.Namespace) -> int:
    try:
        res = stats_decls(
            kernel_db_path=args.kernel_db,
            decls=args.decls,
            tree=args.tree,
            src_root=args.src_root,
            continue_on_error=bool(getattr(args, "continue_on_error", False)),
            with_alias=bool(getattr(args, "with_alias", False)),
        )
    except (LookupError, ValueError, FileNotFoundError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    text = json.dumps(res, indent=2, ensure_ascii=False) if args.json else format_stats_text(res, table=args.table)
    _write_or_print(text, args.out)
    if res.get("errors"):
        if not res["decls"]:
            return 1
        print(f"warning: {len(res['errors'])} target(s) failed to resolve", file=sys.stderr)
    return 0


def _cmd_callers(args: argparse.Namespace) -> int:
    decls_list = list(args.decls)
    cont = bool(getattr(args, "continue_on_error", False))
    try:
        if len(decls_list) == 1:
            res = callers_decl(
                kernel_db_path=args.kernel_db,
                decl=decls_list[0],
                depth=args.depth,
                project_only=args.project_only,
                grouped=args.grouped,
                sort_by=args.sort,
                limit=args.limit,
                tree=args.tree,
                continue_on_error=cont,
            )
        else:
            res = callers_decls(
                kernel_db_path=args.kernel_db,
                decls=decls_list,
                depth=args.depth,
                project_only=args.project_only,
                grouped=args.grouped,
                sort_by=args.sort,
                limit=args.limit,
                tree=args.tree,
                continue_on_error=cont,
            )
    except (LookupError, ValueError, FileNotFoundError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    text = json.dumps(res, indent=2, ensure_ascii=False) if args.json else format_callers_text(res, grouped=args.grouped)
    _write_or_print(text, args.out)
    if res.get("errors"):
        has_any = bool(res.get("targets")) if "targets" in res else (res.get("center") is not None)
        if not has_any:
            return 1
        print(f"warning: {len(res['errors'])} target(s) failed to resolve", file=sys.stderr)
    return 0


def _cmd_anchor(args: argparse.Namespace) -> int:
    if not args.decls and not args.verify_md:
        print("error: specify at least one <decl> or --verify-md <file.md>", file=sys.stderr)
        return 2
    try:
        res = anchor_decls(
            kernel_db_path=args.kernel_db,
            decls=args.decls,
            src_root=args.src_root,
            verify_md=args.verify_md,
        )
    except (LookupError, ValueError, FileNotFoundError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    text = json.dumps(res, indent=2, ensure_ascii=False) if args.json else format_anchor_text(res)
    _write_or_print(text, args.out)
    return 0 if res["all_passed"] else 1


def _cmd_hygiene(args: argparse.Namespace) -> int:
    try:
        res = hygiene_decls(
            kernel_db_path=args.kernel_db,
            decls=args.decls,
            src_root=args.src_root,
            cone_depth=args.cone_depth,
            only=args.only,
            max_decls=args.max_decls,
            continue_on_error=bool(getattr(args, "continue_on_error", False)),
            include_noisy=bool(getattr(args, "include_noisy", False)),
            strict_binders=bool(getattr(args, "strict_binders", False)),
            include_semantic=bool(getattr(args, "include_semantic", False)),
        )
    except (LookupError, ValueError, FileNotFoundError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    text = json.dumps(res, indent=2, ensure_ascii=False) if args.json else format_hygiene_text(res)
    _write_or_print(text, args.out)
    if res.get("errors"):
        if not res["decls"]:
            return 1
        print(f"warning: {len(res['errors'])} target(s) failed to resolve", file=sys.stderr)
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
