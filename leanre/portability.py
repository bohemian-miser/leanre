#!/usr/bin/env python3
"""leanre.portability — Generic, spec-only Mathlib-portability & standalone cone analyzer.

Answers for any target declaration(s) in any `kernel.db`:
  "How self-contained is this theorem, and what would it take to extract or port to Mathlib?"

Capabilities:
  1. Exact transitive `value`+`type` cone metrics: total, project-only, and external
     (Mathlib/Std/Lean/Init) declaration counts, specification cone (`type` from `thm`,
     `type`+`value` from `def`/`inductive`/`opaque`/`quot`/`axiom`), `dom` subtree size,
     `decl_module` count, `thm/def/inductive/axiom/opaque/quot` split, `value_nodes=1`
     forwarding aliases inside the project cone, and total `value_nodes`.
  2. Direct external boundary inventory: top N external namespace prefixes directly
     referenced by project declarations inside the cone (distinct decls, type decls, edges).
  3. Contamination & structural coupling score (`standalone-ready` / `scoped` / `coupled`):
     checks non-standard axioms, `sorryAx`, `reduceBool`/`trustCompiler` flags,
     `decide_kernel` & soundness taints (`taint_sources` + `flags=1/3`), project `opaque`
     declarations, generic mega-record coupling (1-constructor structures with `>= 40`
     fields inside the cone and how many fields the cone actually projects), and
     project root directories touched.
  4. Multi-target shared overlap matrices (`project`, `external`, `full`, and Jaccard)
     plus combined union cone totals.

Guardrails:
  - Python 3.9+ stdlib only; zero third-party dependencies.
  - Opens SQLite strictly read-only (`file:<real>?mode=ro` + `PRAGMA query_only=1`).
  - Zero `.lean` source code or proof bodies emitted; zero absolute host/home paths in outputs.
"""
from __future__ import annotations

import argparse
import array
import collections
import json
import os
import re
import sqlite3
import sys
import time
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

try:
    import bundles as _bundles_mod
except ImportError:  # pragma: no cover
    _bundles_mod = None  # type: ignore[assignment]

SCHEMA_VERSION = "leanre.portability/1"

DEFAULT_KERNEL_DB = os.path.join(_REPO_ROOT, "outputs", "kernel", "kernel.db")
DEFAULT_SRC_ROOT = os.path.join(_REPO_ROOT, "data", "rh_mirror", "src")

STANDARD_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})

# Kernel-pattern flags from `leanre/kernel-rs/src/walk.rs`
F_REFL_TRUE = 1
F_OF_DECIDE = 2
F_REDUCE_BOOL = 4
F_REDUCE_NAT = 8
F_SORRY = 16
F_TRUST_COMPILER = 32

# Soundness-relevant source/generated taint classes in `taint_sources`
SOUNDNESS_TAINT_CLASSES = frozenset({
    "decide_kernel",
    "kexactB",
    "kcopy",
    "CutCptCopy",
    "lean4lean_timeout",
    "slow_con_leche",
})

ELIM_LEAF_NAMES = frozenset({"casesOn", "recOn", "rec"})
_KERNEL_SKIP_AUX = frozenset({
    "casesOn",
    "recOn",
    "rec",
    "noConfusion",
    "noConfusionType",
    "brecOn",
    "binductionOn",
    "mk",
    "inj",
    "injEq",
    "sizeOf_spec",
})

_MULTI_SEG_EXT_ROOTS = frozenset({
    "Mathlib",
    "Lean",
    "Std",
    "Init",
    "Batteries",
    "Aesop",
    "Qq",
    "ProofWidgets",
})

# Fallback top-level external prefixes used ONLY when a raw `kernel.db` has no `decl_module`
# rows and no `--project-prefix` override was supplied.
_FALLBACK_STDLIB_PREFIXES = frozenset({
    "Init", "Lean", "Std", "Batteries", "Mathlib", "Aesop", "Qq", "ProofWidgets",
    "Nat", "Int", "Rat", "Real", "Complex", "NNReal", "ENNReal", "EReal", "Float",
    "Fin", "Finset", "Fintype", "Multiset", "Set", "List", "Array", "Vector", "ByteArray",
    "BitVec", "UInt8", "UInt16", "UInt32", "UInt64", "USize", "Int8", "Int16", "Int32", "Int64",
    "String", "Substring", "Char", "Bool", "Prop", "Sort", "Type", "Unit", "PUnit", "Empty", "PEmpty",
    "Option", "Except", "Sum", "PSum", "Prod", "PProd", "Sigma", "PSigma", "Subtype", "ULift", "PLift",
    "Eq", "HEq", "And", "Or", "Not", "Iff", "Exists", "True", "False", "Classical", "Decidable", "Quot",
    "Function", "Pi", "Equiv", "RelIso", "OrderIso", "Embedding", "Filter", "Topology",
    "TopologicalSpace", "UniformSpace", "Metric", "MetricSpace", "EMetric", "MeasureTheory",
    "MeasurableSpace", "ProbabilityTheory", "CategoryTheory", "AlgebraicGeometry", "AlgebraicTopology",
    "NumberTheory", "Combinatorics", "Analysis", "LinearAlgebra", "RepresentationTheory",
    "Polynomial", "MvPolynomial", "PowerSeries", "LaurentSeries", "Matrix", "LinearMap", "LinearEquiv",
    "ContinuousLinearMap", "ContinuousLinearEquiv", "Module", "Submodule", "Algebra", "Subalgebra",
    "RingHom", "MonoidHom", "AddMonoidHom", "MulHom", "Ideal", "Subring", "Subgroup", "AddSubgroup",
    "Submonoid", "Subsemiring", "Subfield", "IntermediateField", "Group", "AddGroup", "CommGroup",
    "Monoid", "CommMonoid", "Semigroup", "Ring", "CommRing", "Semiring", "Field", "DivisionRing",
    "NormedSpace", "NormedAddCommGroup", "InnerProductSpace", "CompleteSpace", "Order", "Preorder",
    "PartialOrder", "LinearOrder", "Lattice", "CompleteLattice", "DirichletCharacter", "LSeries",
    "ArithmeticFunction", "ZMod", "AddChar", "MulChar", "Units", "Continuous", "ContinuousOn",
    "Differentiable", "AnalyticAt", "Meromorphic", "HasDerivAt", "ContinuousMap", "Acc", "WellFounded",
    "SizeOf", "Inhabited", "Nonempty", "Subsingleton", "Unique", "DecidableEq", "BEq", "Ord",
    "Hashable", "Repr", "ToString", "OfNat", "Add", "Sub", "Mul", "Div", "Mod", "Pow", "HAdd",
    "HSub", "HMul", "HDiv", "HMod", "HPow", "Neg", "Inv", "LE", "LT", "Min", "Max", "Abs",
    "IO", "System", "Task", "Thunk", "StateM", "ReaderM", "ExceptT", "StateT", "ReaderT", "Id",
    "Monad", "Functor", "Applicative", "IsEmpty", "IsUnit", "IsDomain", "IsField", "IsLocalRing",
    "IsRegularLocalRing", "IsDedekindDomain", "IsNoetherian", "Derivation", "IsCompact", "IsOpen",
    "IsClosed", "Padic", "PadicInt", "PadicNorm", "RatFunc", "Localization", "FractionRing",
    "Valuation", "ModularForm", "UpperHalfPlane", "EllipticCurve", "WeierstrassCurve",
    "SpecialLinearGroup", "GeneralLinearGroup", "riemannZeta", "RiemannHypothesis", "hurwitzZeta",
    "completedRiemannZeta", "Gamma", "Circle", "AddCircle", "SimpleGraph", "Quiver", "ChartedSpace",
    "MvPowerSeries", "TensorProduct", "AlternatingMap", "ExteriorAlgebra", "CliffordAlgebra",
    "FreeAlgebra", "FreeModule", "DirectSum", "Finsupp", "DFinsupp", "SchwartzMap", "NumberField",
    "RingOfIntegers", "FractionalIdeal", "ClassGroup", "DedekindDomain", "HeightOneSpectrum",
    "Adeles", "FiniteAdeleRing", "InfiniteAdeleRing", "AdeleRing", "IdeleGroup",
    "propext", "sorryAx", "of_decide_eq_true", "decide", "congrArg", "congrFun", "congr", "funext",
    "absurd", "id", "comp", "flip", "const", "ite", "dite", "cond", "optParam", "autoParam",
    "outParam", "semiOutParam", "eagerReduce", "lcProof", "by_contra", "cast", "eqRec",
})


def connect_ro(path: str) -> sqlite3.Connection:
    """Open an existing SQLite database strictly in read-only URI mode (`mode=ro`)."""
    real = os.path.realpath(path)
    if not os.path.isfile(real):
        raise FileNotFoundError(f"Missing SQLite database: {path}")
    conn = sqlite3.connect(f"file:{real}?mode=ro", uri=True)
    conn.execute("PRAGMA query_only=1")
    return conn


def _rel_repo_path(path: Optional[str]) -> Optional[str]:
    """Format a path relative to repository root so no host/home path leaks."""
    if not path:
        return None
    ap = os.path.abspath(path)
    try:
        rel = os.path.relpath(ap, _REPO_ROOT)
        if not rel.startswith(".."):
            return rel.replace(os.sep, "/")
    except ValueError:
        pass
    return os.path.basename(ap)


def _safe_write_json(out_path: str, payload: Any, compact: bool = False) -> None:
    """Write JSON report to `out_path`, refusing symlink targets."""
    if os.path.islink(out_path):
        raise ValueError(f"Refusing to write through symlink: {out_path}")
    parent = os.path.dirname(os.path.abspath(out_path))
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        if compact:
            json.dump(payload, f, separators=(",", ":"), ensure_ascii=False)
        else:
            json.dump(payload, f, indent=2, ensure_ascii=False)
        f.write("\n")


def _has_table(conn: sqlite3.Connection, table_name: str) -> bool:
    row = conn.execute(
        "SELECT 1 FROM sqlite_master WHERE type IN ('table', 'view') AND name = ?",
        (table_name,),
    ).fetchone()
    return row is not None


def _chunks(seq: Sequence[int], size: int = 900) -> Iterable[Sequence[int]]:
    for i in range(0, len(seq), size):
        yield seq[i : i + size]


def external_namespace_prefix(name: str) -> str:
    """Normalize an external Lean declaration name to a clean library/domain prefix."""
    if not name:
        return "<anonymous>"
    if name.startswith("_private."):
        parts = name.split(".")
        for idx in range(1, len(parts)):
            if parts[idx] == "0" and idx > 1:
                mod_parts = parts[1:idx]
                if mod_parts[0] in _MULTI_SEG_EXT_ROOTS and len(mod_parts) >= 2:
                    return f"{mod_parts[0]}.{mod_parts[1]}"
                return mod_parts[0]
    if "._@." in name:
        after = name.split("._@.", 1)[1].split(".")
        if after and after[0] in _MULTI_SEG_EXT_ROOTS and len(after) >= 2:
            return f"{after[0]}.{after[1]}"
        if after and after[0]:
            return after[0]
    parts = name.split(".")
    if len(parts) >= 2 and parts[0] in _MULTI_SEG_EXT_ROOTS:
        return f"{parts[0]}.{parts[1]}"
    return parts[0]


def resolve_target_decl(conn: sqlite3.Connection, query: str) -> Tuple[int, str, Optional[str]]:
    """Resolve `query` by exact `decls.name`, `consts.name`, or unambiguous `.suffix` match."""
    q = query.strip()
    if not q:
        raise ValueError("Empty declaration query")
    row = conn.execute("SELECT id, name FROM decls WHERE name = ?", (q,)).fetchone()
    if row is not None:
        return int(row[0]), str(row[1]), None
    if _has_table(conn, "consts"):
        crow = conn.execute(
            "SELECT c.decl_id, d.name FROM consts c JOIN decls d ON d.id = c.decl_id WHERE c.name = ?",
            (q,),
        ).fetchone()
        if crow is not None:
            return int(crow[0]), str(crow[1]), q
    if "." not in q:
        cands = conn.execute(
            "SELECT id, name FROM decls WHERE name LIKE ? ORDER BY id",
            (f"%.{q}",),
        ).fetchall()
    else:
        cands = conn.execute(
            "SELECT id, name FROM decls WHERE name LIKE ? ORDER BY id",
            (f"%.{q}",),
        ).fetchall()
    if len(cands) == 1:
        return int(cands[0][0]), str(cands[0][1]), q
    if len(cands) > 1:
        public_cands = [c for c in cands if not str(c[1]).startswith("_private.")]
        if len(public_cands) == 1:
            return int(public_cands[0][0]), str(public_cands[0][1]), q
        sample = ", ".join(str(c[1]) for c in cands[:8])
        more = f" (+{len(cands) - 8} more)" if len(cands) > 8 else ""
        raise LookupError(f"Ambiguous declaration suffix {q!r} ({len(cands)} matches): {sample}{more}")
    raise LookupError(f"Declaration not found in kernel.db: {q!r}")


class _ConeGraphCache:
    """Memory-compact adjacency cache (`(dst << 2) | edge_kind` in `array('Q')`) across targets."""

    def __init__(self) -> None:
        self.out_edges: Dict[int, "array.array[int]"] = {}

    def ensure_loaded(self, conn: sqlite3.Connection, ids: Sequence[int]) -> None:
        missing = [u for u in ids if u not in self.out_edges]
        if not missing:
            return
        buckets: Dict[int, List[int]] = {u: [] for u in missing}
        for chunk in _chunks(missing, 900):
            ph = ",".join("?" for _ in chunk)
            for src, dst, kind in conn.execute(
                f"SELECT src, dst, kind FROM edges WHERE src IN ({ph})",
                chunk,
            ):
                buckets[int(src)].append((int(dst) << 2) | (int(kind) & 3))
        for u, packed in buckets.items():
            self.out_edges[u] = array.array("Q", packed)

    def full_cone(self, conn: sqlite3.Connection, start_id: int) -> Set[int]:
        seen: Set[int] = {start_id}
        frontier: List[int] = [start_id]
        while frontier:
            self.ensure_loaded(conn, frontier)
            nxt: List[int] = []
            for u in frontier:
                for packed in self.out_edges[u]:
                    dst = packed >> 2
                    if dst not in seen:
                        seen.add(dst)
                        nxt.append(dst)
            frontier = nxt
        return seen

    def direct_type_cone(self, start_id: int) -> Set[int]:
        """Pure `type`-edge transitive closure (`edges.kind IN (1, 3)`)."""
        seen: Set[int] = {start_id}
        frontier: List[int] = [start_id]
        while frontier:
            nxt: List[int] = []
            for u in frontier:
                for packed in self.out_edges.get(u, ()):
                    ek = packed & 3
                    if ek in (1, 3):
                        dst = packed >> 2
                        if dst not in seen:
                            seen.add(dst)
                            nxt.append(dst)
            frontier = nxt
        return seen

    def spec_cone(self, start_id: int, kind_by_id: Dict[int, str]) -> Set[int]:
        """Specification cone: follows `type` edges from `thm`s and `type`+`value` from non-`thm`s."""
        seen: Set[int] = {start_id}
        frontier: List[int] = [start_id]
        while frontier:
            nxt: List[int] = []
            for u in frontier:
                is_thm = kind_by_id.get(u) == "thm"
                for packed in self.out_edges.get(u, ()):
                    ek = packed & 3
                    if is_thm and ek == 2:
                        continue
                    dst = packed >> 2
                    if dst not in seen:
                        seen.add(dst)
                        nxt.append(dst)
            frontier = nxt
        return seen


def _classify_is_project(
    name: str,
    module: Optional[str],
    method: Optional[str],
    project_prefixes: Sequence[str],
    has_decl_module_rows: bool,
) -> bool:
    if project_prefixes:
        for pfx in project_prefixes:
            if name == pfx or name.startswith(pfx + "."):
                return True
            if module and (module == pfx or module.startswith(pfx + ".")):
                return True
        return False
    if has_decl_module_rows:
        return (module is not None) or (bool(method) and method.startswith("unmatched:project"))
    # Raw unenriched `kernel.db` fallback
    if name.startswith("_private."):
        parts = name.split(".")
        if len(parts) > 1 and parts[1] in _FALLBACK_STDLIB_PREFIXES:
            return False
        return True
    if "._@." in name:
        after = name.split("._@.", 1)[1].split(".", 1)[0]
        if after in _FALLBACK_STDLIB_PREFIXES:
            return False
    top = name.split(".", 1)[0]
    return top not in _FALLBACK_STDLIB_PREFIXES


def _inspect_structure_meta(
    conn: sqlite3.Connection,
    sid: int,
    sname: str,
    smod: Optional[str],
    real_src_root: Optional[str],
    parsed_mod_cache: Dict[str, Dict[str, Dict[str, Any]]],
) -> Dict[str, Any]:
    """Inspect declared/kernel field projections and eliminators for a 1-ctor structure."""
    s_info: Optional[Dict[str, Any]] = None
    if real_src_root and smod and _bundles_mod is not None:
        if smod not in parsed_mod_cache:
            fpath = _bundles_mod._safe_resolve_module(real_src_root, smod)
            if fpath:
                with open(fpath, "r", encoding="utf-8", errors="replace") as f:
                    parsed_mod_cache[smod] = _bundles_mod.parse_lean_structures_in_text(f.read(), smod)
            else:
                parsed_mod_cache[smod] = {}
        s_info = parsed_mod_cache[smod].get(sname)

    lo = sname + "."
    hi = sname + "/"
    lo_len = len(lo)
    rows = conn.execute(
        """
        SELECT d.id, d.name, d.kind, d.fan_out, d.fan_out_type, e.kind
        FROM decls d
        LEFT JOIN edges e ON e.src = d.id AND e.dst = ?
        WHERE d.name >= ? AND d.name < ?
        """,
        (sid, lo, hi),
    ).fetchall()

    direct: Dict[str, Tuple[int, str, int, int, Optional[int]]] = {}
    elim_ids: List[int] = []
    for cdid, cnm, cknd, fo, fot, ek in rows:
        leaf = str(cnm)[lo_len:]
        if "." in leaf:
            continue
        if leaf in ELIM_LEAF_NAMES:
            elim_ids.append(int(cdid))
            continue
        direct[leaf] = (int(cdid), str(cknd), int(fo), int(fot), None if ek is None else int(ek))

    if s_info is not None:
        own_fields: List[str] = list(s_info["fields"])
        field_decl_ids = [direct[f][0] for f in own_fields if f in direct]
        extends_list: List[str] = list(s_info["extends"])
        total_fields = len(own_fields)
        projected_in_db = len(field_decl_ids)
    else:
        kproj_leaves = sorted(
            leaf
            for leaf, (_cid, cknd, fo, fot, ek) in direct.items()
            if cknd in ("def", "thm")
            and ek == 3
            and fo == fot
            and leaf not in _KERNEL_SKIP_AUX
            and not leaf.startswith("_")
        )
        field_decl_ids = [direct[leaf][0] for leaf in kproj_leaves]
        extends_list = []
        total_fields = len(kproj_leaves)
        projected_in_db = len(kproj_leaves)

    return {
        "decl_id": sid,
        "name": sname,
        "module": smod,
        "total_fields": total_fields,
        "projected_in_db": projected_in_db,
        "field_decl_ids": field_decl_ids,
        "elim_ids": elim_ids,
        "extends": extends_list,
    }


def _score_contamination(
    *,
    non_standard_axioms: Sequence[str],
    has_sorry: bool,
    proj_flags: Dict[str, int],
    ext_flags: Dict[str, int],
    proj_opaques: Sequence[str],
    proj_taints: Dict[str, int],
    mega_records: Sequence[Dict[str, Any]],
    significant_root_dirs: Sequence[str],
    vn1_forwarding_aliases: int,
    spec_cone_project_decls: int,
    project_decls: int,
) -> Tuple[str, List[str]]:
    """Classify a target cone into `standalone-ready`, `scoped`, or `coupled` with exact reasons."""
    coupled_reasons: List[str] = []
    if non_standard_axioms:
        coupled_reasons.append(f"non-standard axioms: {', '.join(non_standard_axioms)}")
    if has_sorry:
        coupled_reasons.append("contains sorryAx / F_SORRY")
    if proj_flags["reduce_bool"] or ext_flags["reduce_bool"]:
        coupled_reasons.append(
            f"reduceBool flag hits (proj={proj_flags['reduce_bool']}, ext={ext_flags['reduce_bool']})"
        )
    if proj_flags["trust_compiler"] or ext_flags["trust_compiler"]:
        coupled_reasons.append(
            f"trustCompiler flag hits (proj={proj_flags['trust_compiler']}, ext={ext_flags['trust_compiler']})"
        )
    if proj_opaques:
        coupled_reasons.append(f"{len(proj_opaques)} project opaque decl(s)")
    soundness_hits = {
        cls: cnt for cls, cnt in sorted(proj_taints.items()) if cls in SOUNDNESS_TAINT_CLASSES and cnt > 0
    }
    if soundness_hits:
        summary = ", ".join(f"{k}={v}" for k, v in soundness_hits.items())
        coupled_reasons.append(f"project taint_sources ({summary})")

    non_sig_sparse_mega = [
        m
        for m in mega_records
        if m["role"] != "target_signature"
        and not m["is_eliminated_in_cone"]
        and m["projected_ratio_in_cone"] < 0.5
    ]
    if len(mega_records) >= 2:
        coupled_reasons.append(
            f"{len(mega_records)} mega-records (>={mega_records[0]['threshold']} fields) in project cone"
        )
    elif non_sig_sparse_mega:
        m0 = non_sig_sparse_mega[0]
        coupled_reasons.append(
            f"sparse ambient mega-record {m0['name']} ({m0['projected_in_cone']}/{m0['total_fields']} fields projected)"
        )
    if project_decls > 50_000:
        coupled_reasons.append(f"large cross-pillar project cone ({project_decls:,} project decls > 50,000)")

    if coupled_reasons:
        return "coupled", coupled_reasons

    scoped_reasons: List[str] = []
    if mega_records:
        for m in mega_records:
            scoped_reasons.append(
                f"mega-record {m['name']} ({m['projected_in_cone']}/{m['total_fields']} fields in cone; {m['role']})"
            )
    if len(significant_root_dirs) >= 3:
        scoped_reasons.append(
            f"touches {len(significant_root_dirs)} significant project root dirs ({', '.join(significant_root_dirs)})"
        )
    if vn1_forwarding_aliases >= 50:
        scoped_reasons.append(f"{vn1_forwarding_aliases:,} vn=1 forwarding aliases in project cone (>=50)")
    if spec_cone_project_decls >= 500:
        scoped_reasons.append(
            f"statement spec cone unfolds through {spec_cone_project_decls:,} project decls (>=500)"
        )

    if scoped_reasons:
        return "scoped", scoped_reasons

    ready_reasons = [
        "standard axioms only, 0 sorryAx/reduceBool/trustCompiler/project-opaque/decide_kernel",
        f"0 mega-records and {spec_cone_project_decls:,} project spec-cone decls across "
        f"{max(1, len(significant_root_dirs))} primary root dir(s)",
    ]
    return "standalone-ready", ready_reasons


def analyze_portability(
    decls: Sequence[str],
    kernel_db_path: str = DEFAULT_KERNEL_DB,
    src_root: Optional[str] = DEFAULT_SRC_ROOT,
    no_src: bool = False,
    project_prefixes: Sequence[str] = (),
    tree: str = "ALL",
    top_boundary: int = 20,
    mega_threshold: int = 40,
    filter_mod: Optional[str] = None,
) -> Dict[str, Any]:
    """Compute exact standalone portability, boundary, coupling, and overlap metrics."""
    t0 = time.time()
    if not decls:
        raise ValueError("At least one target declaration is required")
    if top_boundary < 1:
        raise ValueError(f"--top-boundary must be >= 1, got {top_boundary}")
    if mega_threshold < 1:
        raise ValueError(f"--mega-threshold must be >= 1, got {mega_threshold}")
    mod_rx = re.compile(filter_mod) if filter_mod else None

    norm_prefixes = [p.strip().rstrip(".") for p in project_prefixes if p and p.strip()]

    real_src_root: Optional[str] = None
    if not no_src and src_root:
        if os.path.isdir(src_root):
            real_src_root = os.path.realpath(src_root)
        elif os.path.abspath(src_root) != os.path.abspath(DEFAULT_SRC_ROOT):
            raise FileNotFoundError(f"Missing --src-root directory: {src_root}")

    conn = connect_ro(kernel_db_path)
    try:
        has_decl_module_tbl = _has_table(conn, "decl_module")
        has_decl_module_rows = False
        if has_decl_module_tbl:
            has_decl_module_rows = (
                conn.execute("SELECT 1 FROM decl_module LIMIT 1").fetchone() is not None
            )
        has_consts_tbl = _has_table(conn, "consts")
        has_dom_trees = _has_table(conn, "dom_trees") and _has_table(conn, "dom")
        has_taint_sources = _has_table(conn, "taint_sources")

        tree_id: Optional[int] = None
        tree_label: Optional[str] = None
        if has_dom_trees:
            trow = conn.execute(
                "SELECT id, label FROM dom_trees WHERE label = ?",
                (tree,),
            ).fetchone()
            if trow is not None:
                tree_id, tree_label = int(trow[0]), str(trow[1])
            elif tree != "ALL":
                avail = [r[0] for r in conn.execute("SELECT label FROM dom_trees ORDER BY id")]
                raise ValueError(f"Unknown dominator tree {tree!r}; available: {avail}")

        # 1. Resolve all target declarations
        resolved_targets: List[Tuple[str, int, str, Optional[str]]] = []
        for q in decls:
            did, fqn, resolved_from = resolve_target_decl(conn, q)
            resolved_targets.append((q, did, fqn, resolved_from))

        # 2. Compute transitive cones using shared compact adjacency cache
        graph_cache = _ConeGraphCache()
        full_cones: List[Set[int]] = []
        union_all: Set[int] = set()
        for _q, did, _fqn, _rf in resolved_targets:
            c = graph_cache.full_cone(conn, did)
            full_cones.append(c)
            union_all.update(c)

        # 3. Load declaration & module metadata once over `union_all`
        meta_by_id: Dict[int, Tuple[str, str, int, int, int, int, Optional[str], Optional[str], Optional[str]]] = {}
        kind_by_id: Dict[int, str] = {}
        is_proj_by_id: Dict[int, bool] = {}

        union_sorted = sorted(union_all)
        for chunk in _chunks(union_sorted, 900):
            ph = ",".join("?" for _ in chunk)
            if has_decl_module_tbl:
                sql = (
                    f"SELECT d.id, d.name, d.kind, d.type_nodes, d.value_nodes, d.fan_out_value, "
                    f"       d.flags, d.sighash, dm.module, dm.method "
                    f"FROM decls d LEFT JOIN decl_module dm ON dm.decl_id = d.id "
                    f"WHERE d.id IN ({ph})"
                )
            else:
                sql = (
                    f"SELECT d.id, d.name, d.kind, d.type_nodes, d.value_nodes, d.fan_out_value, "
                    f"       d.flags, d.sighash, NULL, NULL "
                    f"FROM decls d WHERE d.id IN ({ph})"
                )
            for r in conn.execute(sql, chunk):
                _id = int(r[0])
                _nm = str(r[1])
                _knd = str(r[2])
                _tn = int(r[3])
                _vn = int(r[4])
                _fov = int(r[5])
                _fl = int(r[6])
                _sh = None if r[7] is None else str(r[7])
                _mod = None if r[8] is None else str(r[8])
                _meth = None if r[9] is None else str(r[9])
                meta_by_id[_id] = (_nm, _knd, _tn, _vn, _fov, _fl, _sh, _mod, _meth)
                kind_by_id[_id] = _knd
                is_proj_by_id[_id] = _classify_is_project(
                    _nm, _mod, _meth, norm_prefixes, has_decl_module_rows
                )

        # 4. Load `taint_sources` rows if present
        taint_by_decl: Dict[int, List[Tuple[str, Optional[str], Optional[int]]]] = collections.defaultdict(list)
        if has_taint_sources:
            for chunk in _chunks(union_sorted, 900):
                ph = ",".join("?" for _ in chunk)
                for cls, tdid, tmod, tln in conn.execute(
                    f"SELECT class, decl_id, module, line_no FROM taint_sources WHERE decl_id IN ({ph})",
                    chunk,
                ):
                    taint_by_decl[int(tdid)].append(
                        (str(cls), None if tmod is None else str(tmod), None if tln is None else int(tln))
                    )

        # 5. Identify 1-ctor project inductives across `union_all` & inspect structure fields once
        proj_ind_ids = [
            uid for uid in union_sorted if is_proj_by_id.get(uid, False) and kind_by_id.get(uid) == "inductive"
        ]
        one_ctor_ids: Set[int] = set()
        if proj_ind_ids:
            if has_consts_tbl:
                ctor_counts: Dict[int, int] = collections.Counter()
                for chunk in _chunks(proj_ind_ids, 900):
                    ph = ",".join("?" for _ in chunk)
                    for cdid, cnt in conn.execute(
                        f"SELECT decl_id, COUNT(*) FROM consts WHERE ckind = 'ctor' AND decl_id IN ({ph}) GROUP BY decl_id",
                        chunk,
                    ):
                        ctor_counts[int(cdid)] = int(cnt)
                one_ctor_ids = {uid for uid in proj_ind_ids if ctor_counts.get(uid, 0) == 1}
            else:
                one_ctor_ids = set(proj_ind_ids)

        parsed_mod_cache: Dict[str, Dict[str, Dict[str, Any]]] = {}
        struct_meta_by_id: Dict[int, Dict[str, Any]] = {}
        for sid in sorted(one_ctor_ids):
            snm, _sk, _stn, _svn, _sfov, _sfl, _ssh, smod, _smeth = meta_by_id[sid]
            smeta = _inspect_structure_meta(conn, sid, snm, smod, real_src_root, parsed_mod_cache)
            struct_meta_by_id[sid] = smeta

        # 6. Build per-target portability dossiers
        proj_cones: List[Set[int]] = []
        ext_cones: List[Set[int]] = []
        target_reports: List[Dict[str, Any]] = []

        for idx, (query_str, did, fqn, resolved_from) in enumerate(resolved_targets):
            c = full_cones[idx]
            tc = graph_cache.direct_type_cone(did)
            sc = graph_cache.spec_cone(did, kind_by_id)

            direct_target_type_ids = {
                (packed >> 2)
                for packed in graph_cache.out_edges.get(did, ())
                if (packed & 3) in (1, 3)
            }

            proj_set: Set[int] = set()
            ext_set: Set[int] = set()
            mods: Set[str] = set()
            root_dirs_counter: collections.Counter[str] = collections.Counter()
            kind_total: collections.Counter[str] = collections.Counter()
            kind_proj: collections.Counter[str] = collections.Counter()

            vn1_thm = 0
            vn1_def = 0
            tot_vn = 0
            proj_vn = 0
            tot_tn = 0
            proj_tn = 0

            axioms_in_cone: List[str] = []
            proj_opaques: List[str] = []
            ext_opaque_cnt = 0
            sorry_cnt = 0

            proj_flags = {
                "refl_true_flags1": 0,
                "of_decide_flags3": 0,
                "reduce_bool": 0,
                "reduce_nat": 0,
                "sorry": 0,
                "trust_compiler": 0,
            }
            ext_flags = dict(proj_flags)

            proj_taints: collections.Counter[str] = collections.Counter()
            ext_taints: collections.Counter[str] = collections.Counter()
            proj_soundness_hits: List[Dict[str, Any]] = []

            cone_1ctor_ids: List[int] = []

            for uid in sorted(c):
                nm, knd, tn, vn, fov, fl, _sh, mod, _meth = meta_by_id[uid]
                is_p = is_proj_by_id[uid]
                kind_total[knd] += 1
                tot_vn += vn
                tot_tn += tn

                if knd == "axiom":
                    axioms_in_cone.append(nm)
                if nm == "sorryAx" or (fl & F_SORRY):
                    sorry_cnt += 1

                fl_bucket = proj_flags if is_p else ext_flags
                if (fl & (F_REFL_TRUE | F_OF_DECIDE)) == F_REFL_TRUE:
                    fl_bucket["refl_true_flags1"] += 1
                if fl & F_OF_DECIDE:
                    fl_bucket["of_decide_flags3"] += 1
                if fl & F_REDUCE_BOOL:
                    fl_bucket["reduce_bool"] += 1
                if fl & F_REDUCE_NAT:
                    fl_bucket["reduce_nat"] += 1
                if fl & F_SORRY:
                    fl_bucket["sorry"] += 1
                if fl & F_TRUST_COMPILER:
                    fl_bucket["trust_compiler"] += 1

                if is_p:
                    proj_set.add(uid)
                    kind_proj[knd] += 1
                    proj_vn += vn
                    proj_tn += tn
                    if mod:
                        mods.add(mod)
                        root_dirs_counter[mod.split(".", 1)[0]] += 1
                    if vn == 1 and fov == 1:
                        if knd == "thm":
                            vn1_thm += 1
                        elif knd == "def":
                            vn1_def += 1
                    if knd == "opaque":
                        proj_opaques.append(nm)
                    if uid in one_ctor_ids:
                        cone_1ctor_ids.append(uid)
                    for tcls, tmod, tln in taint_by_decl.get(uid, ()):
                        proj_taints[tcls] += 1
                        if tcls in SOUNDNESS_TAINT_CLASSES and len(proj_soundness_hits) < 15:
                            proj_soundness_hits.append({
                                "class": tcls,
                                "decl": nm,
                                "module": tmod or mod,
                                "line": tln,
                            })
                else:
                    ext_set.add(uid)
                    if knd == "opaque":
                        ext_opaque_cnt += 1
                    for tcls, _tmod, _tln in taint_by_decl.get(uid, ()):
                        ext_taints[tcls] += 1

            proj_cones.append(proj_set)
            ext_cones.append(ext_set)

            # Dominator context
            dom_size: Optional[int] = None
            dom_depth: Optional[int] = None
            idom_name: Optional[str] = None
            if tree_id is not None:
                drow = conn.execute(
                    "SELECT dm.subtree_size, dm.depth, dp.name "
                    "FROM dom dm LEFT JOIN decls dp ON dp.id = dm.idom "
                    "WHERE dm.tree_id = ? AND dm.decl_id = ?",
                    (tree_id, did),
                ).fetchone()
                if drow is not None:
                    dom_size = int(drow[0])
                    dom_depth = int(drow[1])
                    idom_name = None if drow[2] is None else str(drow[2])

            # Direct boundary inventory (`proj_set -> ext_set`)
            direct_ext_all: Set[int] = set()
            direct_ext_type: Set[int] = set()
            direct_call_edges = 0
            pfx_decls: Dict[str, Set[int]] = collections.defaultdict(set)
            pfx_type_decls: Dict[str, Set[int]] = collections.defaultdict(set)
            pfx_edges: collections.Counter[str] = collections.Counter()

            for u in proj_set:
                for packed in graph_cache.out_edges.get(u, ()):
                    dst = packed >> 2
                    if dst in ext_set:
                        ek = packed & 3
                        direct_call_edges += 1
                        direct_ext_all.add(dst)
                        pfx = external_namespace_prefix(meta_by_id[dst][0])
                        pfx_decls[pfx].add(dst)
                        pfx_edges[pfx] += 1
                        if ek in (1, 3):
                            direct_ext_type.add(dst)
                            pfx_type_decls[pfx].add(dst)

            ranked_prefixes = sorted(
                pfx_decls.keys(),
                key=lambda p: (-len(pfx_decls[p]), -pfx_edges[p], p),
            )
            top_prefixes = [
                {
                    "prefix": p,
                    "distinct_decls": len(pfx_decls[p]),
                    "type_decls": len(pfx_type_decls[p]),
                    "call_edges": int(pfx_edges[p]),
                }
                for p in ranked_prefixes[:top_boundary]
            ]

            # Mega-record coupling inside `cone`
            mega_records: List[Dict[str, Any]] = []
            for sid in cone_1ctor_ids:
                smeta = struct_meta_by_id[sid]
                tot_f = smeta["total_fields"]
                if tot_f < mega_threshold:
                    continue
                proj_in_cone_cnt = sum(1 for fid in smeta["field_decl_ids"] if fid in c)
                elim_in_cone = any(eid in c for eid in smeta["elim_ids"])
                in_tgt_type = sid in direct_target_type_ids
                role = "target_signature" if in_tgt_type else "internal_or_context"
                ratio = round(proj_in_cone_cnt / tot_f, 4) if tot_f > 0 else 0.0
                mega_records.append({
                    "name": smeta["name"],
                    "module": smeta["module"],
                    "threshold": mega_threshold,
                    "total_fields": tot_f,
                    "projected_in_cone": proj_in_cone_cnt,
                    "projected_in_db": smeta["projected_in_db"],
                    "projected_ratio_in_cone": ratio,
                    "in_target_type": in_tgt_type,
                    "is_eliminated_in_cone": elim_in_cone,
                    "role": role,
                })
            mega_records.sort(key=lambda m: (-m["total_fields"], m["name"]))

            # Root directories & concentration
            sorted_roots = sorted(root_dirs_counter.items(), key=lambda kv: (-kv[1], kv[0]))
            mapped_proj_total = sum(v for _k, v in sorted_roots)
            sig_roots = [
                rname
                for rname, rcnt in sorted_roots
                if (mapped_proj_total > 0 and rcnt / mapped_proj_total >= 0.01) or rcnt >= 200
            ]
            top_root_share = (
                round(sorted_roots[0][1] / mapped_proj_total, 4) if sorted_roots and mapped_proj_total > 0 else 0.0
            )

            axioms_sorted = sorted(set(axioms_in_cone))
            std_axioms = [a for a in axioms_sorted if a in STANDARD_AXIOMS]
            non_std_axioms = [a for a in axioms_sorted if a not in STANDARD_AXIOMS]

            spec_proj_cnt = sum(1 for uid in sc if is_proj_by_id.get(uid, False) and uid != did)
            type_proj_cnt = sum(1 for uid in tc if is_proj_by_id.get(uid, False))
            vn1_total = vn1_thm + vn1_def

            tier, reasons = _score_contamination(
                non_standard_axioms=non_std_axioms,
                has_sorry=(sorry_cnt > 0),
                proj_flags=proj_flags,
                ext_flags=ext_flags,
                proj_opaques=proj_opaques,
                proj_taints=dict(proj_taints),
                mega_records=mega_records,
                significant_root_dirs=sig_roots,
                vn1_forwarding_aliases=vn1_total,
                spec_cone_project_decls=spec_proj_cnt,
                project_decls=len(proj_set),
            )

            t_nm, t_knd, t_tn, t_vn, _t_fov, _t_fl, t_sh, t_mod, _t_meth = meta_by_id[did]
            target_entry: Dict[str, Any] = {
                "query": query_str,
                "resolved_from": resolved_from,
                "decl_id": did,
                "name": t_nm,
                "kind": t_knd,
                "module": t_mod,
                "sighash": t_sh,
                "decl_type_nodes": t_tn,
                "decl_value_nodes": t_vn,
                "cone": {
                    "total_decls": len(c),
                    "project_decls": len(proj_set),
                    "external_decls": len(ext_set),
                    "dom_subtree_size": dom_size,
                    "dom_depth": dom_depth,
                    "idom": idom_name,
                    "spec_cone_total_decls": len(sc),
                    "spec_cone_project_decls": spec_proj_cnt,
                    "direct_type_cone_decls": len(tc),
                    "direct_type_cone_project_decls": type_proj_cnt,
                    "module_count": len(mods),
                    "kind_split_total": {
                        "thm": int(kind_total["thm"]),
                        "def": int(kind_total["def"]),
                        "inductive": int(kind_total["inductive"]),
                        "axiom": int(kind_total["axiom"]),
                        "opaque": int(kind_total["opaque"]),
                        "quot": int(kind_total["quot"]),
                    },
                    "kind_split_project": {
                        "thm": int(kind_proj["thm"]),
                        "def": int(kind_proj["def"]),
                        "inductive": int(kind_proj["inductive"]),
                        "axiom": int(kind_proj["axiom"]),
                        "opaque": int(kind_proj["opaque"]),
                        "quot": int(kind_proj["quot"]),
                    },
                    "vn1_forwarding_aliases": vn1_total,
                    "vn1_thm_aliases": vn1_thm,
                    "vn1_def_aliases": vn1_def,
                    "total_value_nodes": tot_vn,
                    "project_value_nodes": proj_vn,
                    "total_type_nodes": tot_tn,
                    "project_type_nodes": proj_tn,
                },
                "boundary": {
                    "direct_external_decls": len(direct_ext_all),
                    "direct_external_type_decls": len(direct_ext_type),
                    "direct_call_edges": direct_call_edges,
                    "distinct_prefixes_total": len(ranked_prefixes),
                    "top_external_prefixes": top_prefixes,
                },
                "contamination": {
                    "tier": tier,
                    "reasons": reasons,
                    "axioms": axioms_sorted,
                    "standard_axioms": std_axioms,
                    "non_standard_axioms": non_std_axioms,
                    "has_sorry": bool(sorry_cnt > 0),
                    "sorry_decls": sorry_cnt,
                    "kernel_flags": {
                        "project": proj_flags,
                        "external": ext_flags,
                    },
                    "taint_sources": {
                        "available": has_taint_sources,
                        "project_by_class": dict(sorted(proj_taints.items())),
                        "external_by_class": dict(sorted(ext_taints.items())),
                        "project_soundness_hits": proj_soundness_hits,
                    },
                    "opaques": {
                        "project_count": len(proj_opaques),
                        "project_names": sorted(proj_opaques)[:20],
                        "external_count": ext_opaque_cnt,
                    },
                    "project_1ctor_structures_in_cone": len(cone_1ctor_ids),
                    "mega_records": [
                        {k: v for k, v in m.items() if k != "threshold"} for m in mega_records
                    ],
                    "project_root_dirs": dict(sorted_roots),
                    "root_dirs_count": len(sorted_roots),
                    "significant_root_dirs": sig_roots,
                    "top_root_dir_share": top_root_share,
                },
            }
            if mod_rx is not None:
                matched_mods = sorted(m for m in mods if mod_rx.search(m))
                matched_decls = [
                    meta_by_id[uid][0]
                    for uid in sorted(proj_set)
                    if (meta_by_id[uid][7] and mod_rx.search(meta_by_id[uid][7]))
                    or mod_rx.search(meta_by_id[uid][0])
                ]
                target_entry["module_filter"] = {
                    "pattern": filter_mod,
                    "matching_module_count": len(matched_mods),
                    "matching_modules": matched_mods[:50],
                    "matching_decl_count": len(matched_decls),
                    "matching_decls_sample": matched_decls[:50],
                }
            target_reports.append(target_entry)

        # 7. Pairwise overlap matrices & union summary
        n_t = len(resolved_targets)
        proj_mat: List[List[int]] = [[0] * n_t for _ in range(n_t)]
        ext_mat: List[List[int]] = [[0] * n_t for _ in range(n_t)]
        full_mat: List[List[int]] = [[0] * n_t for _ in range(n_t)]
        proj_jaccard: List[List[float]] = [[0.0] * n_t for _ in range(n_t)]

        for i in range(n_t):
            for j in range(i, n_t):
                p_inter = len(proj_cones[i] & proj_cones[j])
                e_inter = len(ext_cones[i] & ext_cones[j])
                f_inter = len(full_cones[i] & full_cones[j])
                p_union = len(proj_cones[i]) + len(proj_cones[j]) - p_inter
                jac = round(p_inter / p_union, 4) if p_union > 0 else 1.0
                proj_mat[i][j] = proj_mat[j][i] = p_inter
                ext_mat[i][j] = ext_mat[j][i] = e_inter
                full_mat[i][j] = full_mat[j][i] = f_inter
                proj_jaccard[i][j] = proj_jaccard[j][i] = jac

        union_proj = set().union(*proj_cones) if proj_cones else set()
        union_ext = set().union(*ext_cones) if ext_cones else set()
        union_mods = {
            meta_by_id[uid][7]
            for uid in union_proj
            if meta_by_id[uid][7] is not None
        }

        if norm_prefixes:
            cls_mode = "project_prefix_override"
        elif has_decl_module_rows:
            cls_mode = "decl_module"
        else:
            cls_mode = "namespace_heuristic"

        elapsed = round(time.time() - t0, 2)
        return {
            "schema": SCHEMA_VERSION,
            "pins": {
                "kernel_db": _rel_repo_path(kernel_db_path),
                "src_root": _rel_repo_path(real_src_root) if real_src_root else None,
                "source_mode": "source+kernel" if real_src_root else "kernel_only",
                "classification_mode": cls_mode,
                "dom_tree": tree_label,
                "top_boundary": top_boundary,
                "mega_threshold": mega_threshold,
                "elapsed_seconds": elapsed,
            },
            "targets": target_reports,
            "overlap": {
                "target_names": [t["name"] for t in target_reports],
                "project_decls_matrix": proj_mat,
                "external_decls_matrix": ext_mat,
                "full_decls_matrix": full_mat,
                "project_jaccard_matrix": proj_jaccard,
                "union_summary": {
                    "union_total_decls": len(union_all),
                    "union_project_decls": len(union_proj),
                    "union_external_decls": len(union_ext),
                    "union_module_count": len(union_mods),
                },
            },
        }
    finally:
        conn.close()


def format_portability_text(rep: Dict[str, Any]) -> str:
    """Format a concise human-readable CLI report for `leanre portability`."""
    pins = rep["pins"]
    targets = rep["targets"]
    ov = rep["overlap"]
    us = ov["union_summary"]

    lines: List[str] = [
        (
            f"leanre portability ({rep['schema']}) — mode={pins['source_mode']}, "
            f"classify={pins['classification_mode']}, tree={pins['dom_tree'] or 'none'} "
            f"({pins['elapsed_seconds']}s)"
        ),
        (
            f"Targets: {len(targets)} | Union cone: {us['union_total_decls']:,} total "
            f"({us['union_project_decls']:,} project across {us['union_module_count']:,} modules, "
            f"{us['union_external_decls']:,} external)"
        ),
        "",
        (
            f"{'#':>2}  {'Tier':<16} {'dom':>8} {'proj':>8} {'spec_p':>6} {'ext':>8} "
            f"{'full':>9} {'mods':>5} {'vn=1':>5} {'mega':>4}  {'Target'}"
        ),
        "-" * 110,
    ]

    for idx, t in enumerate(targets, 1):
        c = t["cone"]
        ct = t["contamination"]
        dom_s = "-" if c["dom_subtree_size"] is None else f"{c['dom_subtree_size']:,}"
        lines.append(
            f"{idx:>2}  {ct['tier']:<16} {dom_s:>8} {c['project_decls']:>8,} "
            f"{c['spec_cone_project_decls']:>6,} {c['external_decls']:>8,} "
            f"{c['total_decls']:>9,} {c['module_count']:>5,} {c['vn1_forwarding_aliases']:>5,} "
            f"{len(ct['mega_records']):>4}  {t['name']}"
        )

    for idx, t in enumerate(targets, 1):
        c = t["cone"]
        b = t["boundary"]
        ct = t["contamination"]
        kp = c["kind_split_project"]
        kt = c["kind_split_total"]
        lines.append("")
        lines.append(f"[{idx}] {t['name']} ({t['kind']}, id={t['decl_id']}, mod={t['module'] or 'unmatched'})")
        lines.append(
            f"  cone       : proj={c['project_decls']:,} (thm={kp['thm']:,}, def={kp['def']:,}, ind={kp['inductive']:,}) | "
            f"ext={c['external_decls']:,} | full={c['total_decls']:,} (ax={kt['axiom']}, opq={kt['opaque']}) | "
            f"value_nodes={c['total_value_nodes']:,} (proj={c['project_value_nodes']:,})"
        )
        rdirs = ", ".join(f"{k}:{v:,}" for k, v in list(ct["project_root_dirs"].items())[:6]) or "none"
        lines.append(
            f"  coupling   : {ct['tier']} — {'; '.join(ct['reasons'])} | root_dirs=[{rdirs}]"
        )
        taints_p = ", ".join(f"{k}:{v}" for k, v in ct["taint_sources"]["project_by_class"].items()) or "none"
        fl_p = ct["kernel_flags"]["project"]
        lines.append(
            f"  tcb/taint  : axioms={ct['axioms']} | proj_flags=(f1={fl_p['refl_true_flags1']}, "
            f"f3={fl_p['of_decide_flags3']}, redBool={fl_p['reduce_bool']}, tc={fl_p['trust_compiler']}) | "
            f"proj_taint={taints_p}"
        )
        if ct["mega_records"]:
            m_str = ", ".join(
                f"{m['name']} ({m['projected_in_cone']}/{m['total_fields']} in cone, {m['role']})"
                for m in ct["mega_records"][:5]
            )
            lines.append(f"  mega>=40   : {m_str}")
        top_b = ", ".join(
            f"{p['prefix']}({p['distinct_decls']})" for p in b["top_external_prefixes"][:8]
        )
        lines.append(
            f"  boundary   : {b['direct_external_decls']:,} direct ext decls ({b['direct_call_edges']:,} edges) — {top_b}"
        )

    if len(targets) >= 2:
        lines.append("")
        lines.append("Shared project-declaration overlap matrix:")
        short = [nm.rsplit(".", 1)[-1][:12] for nm in ov["target_names"]]
        lines.append("              " + "  ".join(f"{s:>12}" for s in short))
        for i, s in enumerate(short):
            row_s = "  ".join(f"{ov['project_decls_matrix'][i][j]:>12,}" for j in range(len(short)))
            lines.append(f"  {s:<12}{row_s}")

    return "\n".join(lines)


def _collect_target_args(args: argparse.Namespace) -> List[str]:
    out: List[str] = list(getattr(args, "decls", None) or [])
    tf = getattr(args, "targets_file", None)
    if tf:
        with open(tf, "r", encoding="utf-8") as f:
            for raw in f:
                s = raw.split("#", 1)[0].strip()
                if s:
                    out.append(s)
    return out


def cmd_portability(args: argparse.Namespace) -> int:
    """CLI handler for `leanre portability` (`0` on success, non-zero on error)."""
    try:
        targets = _collect_target_args(args)
        rep = analyze_portability(
            decls=targets,
            kernel_db_path=args.kernel_db,
            src_root=None if args.no_src else args.src_root,
            no_src=args.no_src,
            project_prefixes=args.project_prefix or (),
            tree=args.tree,
            top_boundary=args.top_boundary,
            mega_threshold=args.mega_threshold,
            filter_mod=getattr(args, "filter_mod", None),
        )
    except (FileNotFoundError, LookupError, ValueError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    if args.out:
        try:
            _safe_write_json(args.out, rep, compact=bool(args.compact))
        except (ValueError, OSError) as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1

    if args.json:
        if args.compact:
            print(json.dumps(rep, separators=(",", ":"), ensure_ascii=False))
        else:
            print(json.dumps(rep, indent=2, ensure_ascii=False))
    elif not args.out:
        print(format_portability_text(rep))
    else:
        print(format_portability_text(rep))
    return 0


def add_portability_parser(sub: Any, dest: str = "portability_func") -> argparse.ArgumentParser:
    """Attach `leanre portability` subcommand to `leanre/leanre.py` argparse subparsers."""
    p = sub.add_parser(
        "portability",
        help="Generic spec-only Mathlib-portability, boundary & standalone cone analyzer",
    )
    p.add_argument(
        "decls",
        nargs="*",
        help="One or more target declaration names (exact FQN, constant name, or unique .suffix)",
    )
    p.add_argument(
        "--targets-file",
        default=None,
        help="Optional newline-delimited file of target declarations (# comments allowed)",
    )
    p.add_argument(
        "--kernel-db",
        default=DEFAULT_KERNEL_DB,
        help="Path to kernel.db (opened strictly mode=ro + PRAGMA query_only=1)",
    )
    p.add_argument(
        "--src-root",
        "--src",
        dest="src_root",
        default=DEFAULT_SRC_ROOT,
        help="Optional Lean src/ root for exact 1-ctor structure field counts",
    )
    p.add_argument(
        "--no-src",
        action="store_true",
        help="Run strictly from kernel.db without reading .lean files",
    )
    p.add_argument(
        "--project-prefix",
        action="append",
        default=[],
        help="Explicit project namespace/module prefix override (repeatable)",
    )
    p.add_argument(
        "--tree",
        default="ALL",
        help="Dominator tree label in dom_trees (default: ALL)",
    )
    p.add_argument(
        "--top-boundary",
        type=int,
        default=20,
        help="Number of top external boundary namespace prefixes to report (default: 20)",
    )
    p.add_argument(
        "--mega-threshold",
        type=int,
        default=40,
        help="Minimum field count to flag a 1-ctor structure as a mega-record (default: 40)",
    )
    p.add_argument(
        "--filter-mod",
        default=None,
        help="Optional regex to match/count module or declaration names inside each project cone",
    )
    p.add_argument("--json", action="store_true", help="Emit JSON report to stdout")
    p.add_argument("--compact", action="store_true", help="Emit compact single-line JSON")
    p.add_argument("--out", default=None, help="Optional output path to write JSON report")
    p.set_defaults(**{dest: cmd_portability, "func": cmd_portability})
    return p


register_cli = add_portability_parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        prog="leanre-portability",
        description="Generic spec-only Mathlib-portability & standalone cone analyzer",
    )
    sub = ap.add_subparsers(dest="cmd", required=True)
    add_portability_parser(sub, dest="portability_func")
    argv_list = list(sys.argv[1:] if argv is None else argv)
    if argv_list and argv_list[0] not in ("portability", "-h", "--help"):
        argv_list = ["portability"] + argv_list
    elif not argv_list:
        argv_list = ["portability", "--help"]
    args = ap.parse_args(argv_list)
    return int(cmd_portability(args))


if __name__ == "__main__":
    sys.exit(main())
