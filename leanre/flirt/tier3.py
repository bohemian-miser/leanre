#!/usr/bin/env python3
"""FLIRT Tier 3 -- name-blinded AI labeling on cluster boundaries (Gate F3).

Pipeline:
  1. `prepare`  -- deterministically select pilot cluster boundaries, build a fail-closed
                   Mathlib/Lean4/Batteries identifier allowlist, generate BOTH blinded
                   (`outputs/flirt/tier3_blinded_prompts.jsonl`) and unblinded
                   (`outputs/flirt/cache/tier3_unblinded_prompts.jsonl`) prompt packs,
                   and run the strict leak test proving ZERO project folder/file/decl
                   identifiers survive in any blinded prompt.
  2. `leak-test`-- standalone deterministic verifier over any blinded prompt pack JSONL.
  3. `ingest`   -- ingest blinded + unblinded model label JSON files, compute deterministic
                   blinded-vs-unblinded agreement metrics (exact match, Cohen's kappa,
                   top-2 overlap, label Jaccard, per-cohort breakdown), and write labels
                   ONLY into a separate `ai-draft` annotation layer (`leanre.annot/1`,
                   `default_on: false`, `draft: true`, provenance `[M]` + `breaks`,
                   never `[L]` facts).

Guardrails (research/04_verification_and_roadmap.md §2 & §4 item 4):
  * Strictly header-only (binders + result types + Mathlib imports/opens): ZERO proof bodies.
  * Fail-closed name blinding: every non-allowlisted identifier in the blinded data payload
    is replaced by a deterministic opaque ID (`C##`, `M##`, `D###`, `P###`, `#k`, `u#k`).
  * AI labels are NEVER presented as facts (`[L]`); they live solely in an off-by-default
    `ai-draft` layer with tag `M` and an explicit `breaks` caveat.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import re
import sqlite3
import sys
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
LEANRE = os.path.dirname(HERE)
REPO = os.path.dirname(LEANRE)
for _p in (LEANRE, HERE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import annot  # noqa: E402
import sighash  # noqa: E402
import tier1  # noqa: E402

OUT_DIR = os.path.join(REPO, "outputs", "flirt")
CACHE_DIR = os.path.join(OUT_DIR, "cache")
DEFAULT_ALLOWLIST = os.path.join(CACHE_DIR, "std_allowlist.txt")
DEFAULT_LEXICON = os.path.join(CACHE_DIR, "lexicon_rh.txt")
DEFAULT_BLINDED = os.path.join(OUT_DIR, "tier3_blinded_prompts.jsonl")
DEFAULT_BLINDED_RAW = os.path.join(CACHE_DIR, "tier3_blinded_raw_prompts.jsonl")
DEFAULT_UNBLINDED = os.path.join(CACHE_DIR, "tier3_unblinded_prompts.jsonl")
DEFAULT_MANIFEST = os.path.join(CACHE_DIR, "tier3_manifest.json")
DEFAULT_PACK = os.path.join(OUT_DIR, "tier3_ai_draft_pack.jsonl")
DEFAULT_PILOT_JSON = os.path.join(OUT_DIR, "tier3_pilot.json")
DEFAULT_SRC = os.path.join(REPO, "data", "rh_mirror", "src")
DEFAULT_TIER1_DB = os.path.join(OUT_DIR, "tier1.db")
DEFAULT_LEANRE_DB = os.path.join(REPO, "outputs", "leanre.db")
DEFAULT_KERNEL_DB = os.path.join(REPO, "outputs", "kernel", "kernel.db")
DEFAULT_CLUSTERS_JSON = os.path.join(OUT_DIR, "clusters.json")
CORPORA_DIR = os.path.join(REPO, "data", "corpora")

SCHEMA_VERSION = "leanre.flirt.tier3/2"
AI_LAYER_ID = "ai/flirt-tier3-pilot"
AI_LAYER_TITLE = "FLIRT Tier 3 — Name-Blinded AI Draft Labels (1-2 Hop Unfolded)"
AI_LAYER_DESC = (
    "Heuristic AI-draft cluster boundary labels generated strictly from name-blinded Lean "
    "declaration headers, Mathlib imports/opens, and 1-2-hop unfolded Mathlib/Lean-core "
    "contract primitives (zero proof bodies, zero project names). Off by default; never [L] facts."
)
DEFAULT_BREAKS = (
    "Heuristic AI draft inferred solely from name-blinded declaration headers, Mathlib "
    "imports/opens, and 1-2-hop unfolded Mathlib/Lean-core contract primitives (zero proof "
    "bodies read, all project identifiers replaced with opaque IDs). Breaks when contract "
    "definitions sit >2 hops deep or use generic Mathlib types for specialized objects; "
    "must be human-verified before promotion out of ai-draft."
)

# Closed domain taxonomy shared with Tier 1 (plus other_mixed for genuinely mixed/unclear clusters)
DOMAIN_TAXONOMY: Tuple[str, ...] = tuple(sorted(tier1.DOMAIN_KEYWORDS.keys())) + ("other_mixed",)

# Built-in Lean 4 / Mathlib core symbol fallback (used when data/corpora is absent, e.g. unit tests)
CORE_ALLOWLIST_TOKENS: Set[str] = set("""
Nat Int Rat Real Complex NNReal ENNReal Bool Char String Unit PUnit Empty PEmpty
True False Eq Ne Iff And Or Not Exists HEq LE LT GE GT Prop Type Sort
List Array Option Fin Finset Fintype Multiset Set Subtype Prod PProd Sum PSum Sigma PSigma
Equiv Function Matrix Polynomial MvPolynomial PowerSeries MvPowerSeries ZMod Padic PadicInt
DirichletCharacter MulChar AddChar ArithmeticFunction LSeries LFunction riemannZeta RiemannHypothesis
Ring CommRing Semiring CommSemiring Field DivisionRing Group CommGroup AddGroup AddCommGroup
Monoid CommMonoid Module Algebra Submodule Ideal Subgroup Subring Subfield Units
RingHom MonoidHom LinearMap LinearEquiv AlgHom AlgEquiv ContinuousLinearMap
NumberField IsFractionRing IsIntegralClosure IsDedekindDomain IsDomain CharZero NeZero
Nontrivial Unique Inhabited Decidable DecidableEq DecidablePred LinearOrder PartialOrder
Preorder Lattice CompleteLattice TopologicalSpace MetricSpace UniformSpace NormedSpace
NormedField NormedRing NormedAddCommGroup InnerProductSpace CompleteSpace T2Space
CompactSpace LocallyCompactSpace SecondCountableTopology MeasurableSpace Measure MeasureTheory
Filter Tendsto Continuous ContinuousOn Differentiable DifferentiableOn AnalyticAt AnalyticOn
Integrable Measurable AEMeasurable AEStronglyMeasurable LocallyIntegrable IsOpen IsClosed
IsCompact Finite Countable Infinite Classical Nonempty Prime primeCounting centralBinom
vonMangoldt totient Coprime gcd lcm log exp pi arg re im abs norm dist smul
AlgebraicGeometry Scheme Spec LocallyRingedSpace Presheaf Sheaf CategoryTheory Limits
MonoidalCategory CartesianMonoidalCategory Abelian PrimeSpectrum Localization IsLocalRing
Valuation Valued WithZero AdicCompletion Teichmuller Hensel IsDiscreteValuationRing
BilinForm QuadraticForm Representation Basis Dual det trace TensorProduct
SchwartzMap HasTemperateGrowth iteratedDeriv deriv fderiv Volume volume integral lintegral
MeasurePreserving AddHaar Haar BigOperators Pointwise Topology Manifold Smooth ChartedSpace
Mathlib Lean Batteries Std Init Meta Elab Expr Tactic Syntax Environment
range filter map card length head tail all any Pairwise succ zero one add mul sub div pow
true false some none nil cons fst snd val mem subset union inter sdiff compl
""".split())

# Static structural tokens allowed in blinded prompt JSON (schema fields, decl kinds, generic flags)
SCHEMA_SAFE_TOKENS: Set[str] = {
    "cluster_id", "module_count", "boundary_modules_shown", "total_lines",
    "imports_summary", "mathlib_whole", "mathlib_subimports",
    "intra_cluster_edges", "external_cluster_imports", "external_cluster_importers",
    "std_opens", "omitted_project_opens_count", "generic_flags", "declarations",
    "id", "module", "kind", "signature_blinded", "n_tokens", "n_local",
    "prompt_sha256", "blinded", "schema",
    "theorem", "lemma", "def", "abbrev", "structure", "class", "instance",
    "inductive", "opaque", "axiom", "example", "alias",
    "kernel_decide", "metaprogram_decl_emitter", "tactic_metaprogram",
    "true", "false", "null", "leanre", "flirt", "tier3", "leanre.flirt.tier3",
    "unfolded_type_context", "unfold_hops", "direct_mathlib_deps",
    "opaque_symbol_unfoldings", "opaque_id", "std_primitives", "top_unfolded_mathlib",
}

_RE_TYPECLASS_NOISE = re.compile(
    r"(?:\.(?:to[A-Z]|inst[A-Z]|dec[A-Z]|decidable|mk$|rec$|casesOn$|noConfusion$|ofNat$|cast$)|^inst[A-Z])"
)
_GENERIC_ALGEBRA_NOISE: Set[str] = {
    "Semiring", "CommSemiring", "Semifield", "DivisionSemiring", "DivisionRing",
    "AddMonoid", "AddCommMonoid", "AddGroup", "AddCommGroup", "AddSemigroup", "AddCommSemigroup",
    "Monoid", "CommMonoid", "Semigroup", "CommSemigroup", "GroupWithZero", "CommGroupWithZero",
    "MonoidWithZero", "CommMonoidWithZero", "MulZeroClass", "MulZeroOneClass", "AddZeroClass",
    "ZeroLEOneClass", "IsOrderedRing", "IsOrderedAddMonoid", "IsStrictOrderedRing",
    "PartialOrder", "Preorder", "LinearOrder", "Lattice", "SemilatticeSup", "SemilatticeInf",
    "DistribLattice", "CompleteLattice", "BoundedOrder", "OrderTop", "OrderBot",
    "SetLike", "FunLike", "DFunLike", "EquivLike", "RelHomClass", "RingHomClass",
    "AddHom", "MulHom", "ZeroHom", "OneHom", "CharZero", "IsCancelAdd", "NoZeroDivisors",
    "InvolutiveNeg", "SubNegMonoid", "SubNegZeroMonoid", "DivInvMonoid", "DivInvOneMonoid",
    "Nat", "Int", "Rat", "Real", "Complex", "Bool", "Fin", "Set", "List", "Finset", "Fintype",
}

# Ubiquitous Lean/Init core plumbing excluded from unfolded Mathlib summaries so
# 1-2-hop unfolded context highlights domain-informative Mathlib types & definitions.
_PLUMBING_PREFIXES: Tuple[str, ...] = (
    "Eq", "HEq", "And", "Or", "Not", "Iff", "Exists", "True", "False", "Unit", "PUnit",
    "Empty", "PEmpty", "Prod", "PProd", "Sum", "PSum", "Sigma", "PSigma", "Subtype",
    "Option", "OfNat", "HAdd", "HSub", "HMul", "HDiv", "HPow", "HSMul", "HMod", "HAppend",
    "Add", "Sub", "Mul", "Div", "Pow", "SMul", "Neg", "Inv", "Zero", "One", "Mod",
    "LE", "LT", "GE", "GT", "BEq", "Ord", "Decidable", "Classical", "propext", "Quot",
    "Nonempty", "Inhabited", "Unique", "Nontrivial", "NeZero", "AutoParam", "OptParam",
    "outParam", "semiOutParam", "id", "Function", "Coe", "Cast", "Nat.cast", "Int.cast",
    "Rat.cast", "OfScientific", "Neg.neg", "Inv.inv", "Zero.zero", "One.one",
    "Ne", "GT.gt", "GE.ge", "LT.lt", "LE.le", "Membership", "HasSubset", "HasSSubset",
    "Union", "Inter", "SDiff", "Compl", "EmptyCollection", "Singleton", "Insert",
    "ite", "dite", "cond", "Bool.true", "Bool.false", "Nat.zero", "Nat.succ", "Nat.add",
    "Nat.mul", "Nat.sub", "Nat.div", "Nat.mod", "Nat.pow", "Nat.le", "Nat.lt",
    "Int.ofNat", "Int.negSucc", "Fin.mk", "Fin.val", "Set.mem", "Set.univ",
    "inst", "Lean.ofReduceBool", "sorryAx", "congrArg", "congrFun", "funext",
)


class KernelTypeUnfolder:
    """Read-only 1-2-hop kernel contract unfolder over outputs/kernel/kernel.db (mode=ro).

    For a declaration `d`:
      * Hop 1: inspects `d`'s kernel `type` dependencies (`edges.kind IN (1, 3)`).
      * Hop 2: for each project-local contract (`def`/`inductive`/`opaque`/`axiom`, NEVER
        `thm` proof bodies!) referenced in `d`'s type, follows its `type`+`value` edges
        (and 1 more contract hop if `unfold_hops >= 2`) to collect verified, domain-informative
        Mathlib/Lean-core primitives.
    Fail-closed: every emitted constant is verified via `std_allowlist` AND must not appear
    in `project_lexicon` or `PROJECT_FORBIDDEN_ROOTS`.
    """

    def __init__(
        self,
        kernel_db: str,
        project_lexicon: sighash.Lexicon,
        std_allowlist: StdAllowlist,
        tier2_lib_tokens: Optional[Set[str]] = None,
    ):
        self._conn = sqlite3.connect(f"file:{kernel_db}?mode=ro", uri=True)
        self._lex = project_lexicon
        self._al = std_allowlist
        self._t2_lib = tier2_lib_tokens
        self._decl_cache: Dict[str, Optional[Tuple[int, str]]] = {}
        self._edges_cache: Dict[Tuple[int, bool], List[Tuple[int, str, str]]] = {}

    def close(self) -> None:
        self._conn.close()

    def _lookup(self, name: str) -> Optional[Tuple[int, str]]:
        if name not in self._decl_cache:
            row = self._conn.execute(
                "SELECT id, kind FROM decls WHERE name = ?", (name,)
            ).fetchone()
            self._decl_cache[name] = (int(row[0]), str(row[1])) if row else None
        return self._decl_cache[name]

    def _deps(self, decl_id: int, type_only: bool) -> List[Tuple[int, str, str]]:
        key = (decl_id, type_only)
        res = self._edges_cache.get(key)
        if res is None:
            sql = (
                "SELECT d.id, d.name, d.kind FROM edges e JOIN decls d ON d.id = e.dst "
                "WHERE e.src = ? AND e.kind IN (1, 3) LIMIT 300"
                if type_only
                else "SELECT d.id, d.name, d.kind FROM edges e JOIN decls d ON d.id = e.dst "
                "WHERE e.src = ? LIMIT 300"
            )
            res = [(int(r[0]), str(r[1]), str(r[2])) for r in self._conn.execute(sql, (decl_id,))]
            if len(self._edges_cache) < 50000:
                self._edges_cache[key] = res
        return res

    def _is_informative_std(self, name: str) -> bool:
        if not name or name.startswith("_") or "._" in name:
            return False
        if _RE_TYPECLASS_NOISE.search(name):
            return False
        if name in _GENERIC_ALGEBRA_NOISE:
            return False
        top = name.split(".", 1)[0]
        if top in PROJECT_FORBIDDEN_ROOTS:
            return False
        if self._lex.is_local(name):
            return False
        for pref in _PLUMBING_PREFIXES:
            if name == pref or name.startswith(pref + "."):
                return False
        if not self._al.is_allowed(name):
            return False
        # Extra safety: if tier2 library token set is provided, verify every dot component
        # with len >= 5 is a known library token so zero-trust leak greppers pass 100%!
        if self._t2_lib is not None:
            for part in name.split("."):
                if len(part) >= 5 and part not in self._t2_lib and part not in CORE_ALLOWLIST_TOKENS:
                    return False
        return True

    def unfold_cluster(
        self,
        decl_names: Sequence[str],
        opaque_name_fn: Any,
        unfold_hops: int = 2,
        max_symbols: int = 12,
        max_prims_per_sym: int = 12,
    ) -> Dict[str, Any]:
        """Return fail-closed `unfolded_type_context` dict for a cluster's boundary decls."""
        direct_std: collections.Counter = collections.Counter()
        all_unfolded: collections.Counter = collections.Counter()
        sym_unfoldings: List[Dict[str, Any]] = []
        seen_proj: Set[int] = set()

        for dname in decl_names:
            info = self._lookup(dname)
            if info is None:
                continue
            did, dkind = info
            # For theorems: inspect type edges only (NEVER proof value!).
            # For def/inductive/opaque/axiom contracts: inspect type+value edges.
            type_only = (dkind == "thm")
            for cid, cname, ckind in self._deps(did, type_only=type_only):
                if self._is_informative_std(cname):
                    direct_std[cname] += 1
                    all_unfolded[cname] += 1
                elif ckind != "thm" and cid not in seen_proj and len(seen_proj) < max_symbols:
                    # Project-local contract (`def`/`inductive`/`opaque`) referenced by boundary decl!
                    seen_proj.add(cid)
                    prims: collections.Counter = collections.Counter()
                    hop2_contracts: List[int] = []
                    for g_id, g_name, g_kind in self._deps(cid, type_only=False):
                        if self._is_informative_std(g_name):
                            prims[g_name] += 1
                            all_unfolded[g_name] += 1
                        elif unfold_hops >= 2 and g_kind != "thm" and len(hop2_contracts) < 10:
                            hop2_contracts.append(g_id)
                    if unfold_hops >= 2:
                        for h2_id in hop2_contracts:
                            for g2_id, g2_name, _ in self._deps(h2_id, type_only=False):
                                if self._is_informative_std(g2_name):
                                    prims[g2_name] += 1
                                    all_unfolded[g2_name] += 1
                    if prims:
                        sym_id = opaque_name_fn(cname)
                        sym_unfoldings.append({
                            "opaque_id": sym_id,
                            "kind": ckind,
                            "std_primitives": [k for k, _ in prims.most_common(max_prims_per_sym)],
                        })

        return {
            "unfold_hops": unfold_hops,
            "direct_mathlib_deps": [k for k, _ in direct_std.most_common(20)],
            "opaque_symbol_unfoldings": sym_unfoldings,
            "top_unfolded_mathlib": [k for k, _ in all_unfolded.most_common(25)],
        }

_RE_OPAQUE_ID = re.compile(r"^(?:C\d+|M\d+|D\d+|P\d+|f\d+|u#\d+|EXT\d+|NS\d+)$")
_RE_ALPHA_TOK = re.compile(r"u#\d+|[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)*")

# Project-specific top-level folder / namespace prefixes that must NEVER pass as library tokens
PROJECT_FORBIDDEN_ROOTS: Set[str] = {
    "Development", "Formalism", "GroundTheory", "CompanionTheory",
    "ReciprocityTheory", "PositivityTheory", "BuildAid", "Supplements", "Lemmata",
    "GlobalTheory", "UpperTheory", "LateralTheory", "AbelianVarietyTheory",
    "DivisorProofs", "InvFiveLogLeSumInvPrimes", "PrimeRecip",
    "IndefiniteRowSideFullHecke", "MainTheoremsAll", "OpenLiteratureStatements",
    "CutCptCopy", "kexactB", "kcopy", "StatementOC", "RhOfRight", "MainConclusion",
}

_FLAG_GENERIC_MAP: Dict[str, str] = {
    "decide_kernel": "kernel_decide",
    "kexactB": "metaprogram_decl_emitter",
    "kcopy": "metaprogram_decl_emitter",
    "CutCptCopy": "metaprogram_decl_emitter",
    "addDecl": "metaprogram_decl_emitter",
    "run_tac": "tactic_metaprogram",
}

_LABEL_STOPWORDS: Set[str] = {
    "the", "of", "and", "in", "on", "for", "to", "a", "an", "with", "over", "via",
    "by", "from", "at", "as", "into", "about", "using", "based", "cluster", "module",
    "modules", "theory", "proof", "proofs", "lemmas", "theorems", "definitions",
    "boundary", "bounds", "properties", "results", "helper", "helpers", "checks",
}


class StdAllowlist:
    """Fail-closed Mathlib + Lean 4 + Batteries public identifier allowlist."""

    def __init__(self, full_names: Iterable[str], extra_tokens: Iterable[str] = ()):
        self.full_names: Set[str] = set()
        self.tokens: Set[str] = set(CORE_ALLOWLIST_TOKENS) | set(sighash._KEYWORDS)
        for nm in full_names:
            if not nm:
                continue
            top = nm.split(".", 1)[0]
            if top in PROJECT_FORBIDDEN_ROOTS:
                continue
            self.full_names.add(nm)
            for part in nm.split("."):
                if len(part) >= 2 and part not in PROJECT_FORBIDDEN_ROOTS:
                    self.tokens.add(part)
        for t in extra_tokens:
            if t and t not in PROJECT_FORBIDDEN_ROOTS:
                self.tokens.add(t)
        # Ensure forbidden project roots are never in the allowlist
        self.tokens.difference_update(PROJECT_FORBIDDEN_ROOTS)
        self._id: Optional[str] = None

    @property
    def id(self) -> str:
        if self._id is None:
            data = ("\n".join(sorted(self.tokens)) + "\n").encode("utf-8")
            self._id = hashlib.sha256(data).hexdigest()[:16]
        return self._id

    def is_allowed(self, ident: str) -> bool:
        """True iff `ident` is a verified standard Mathlib/Lean4/Batteries identifier."""
        if not ident or ident in PROJECT_FORBIDDEN_ROOTS:
            return False
        if ident in self.full_names or ident in self.tokens:
            return True
        parts = ident.split(".")
        if len(parts) > 1 and all(
            (p in self.tokens or p.isdigit()) and p not in PROJECT_FORBIDDEN_ROOTS
            for p in parts
        ):
            return True
        return False

    def save(self, path: str) -> None:
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            for nm in sorted(self.full_names):
                f.write(nm + "\n")

    @classmethod
    def load(cls, path: str) -> "StdAllowlist":
        with open(path, "r", encoding="utf-8") as f:
            return cls(line.rstrip("\n") for line in f)


def build_std_allowlist(
    corpora_dir: str = CORPORA_DIR,
    out_path: Optional[str] = DEFAULT_ALLOWLIST,
    workers: int = 16,
) -> StdAllowlist:
    """Build pinned library allowlist strictly from Mathlib + Lean4 + Batteries."""
    dirs = [
        os.path.join(corpora_dir, "mathlib4", "Mathlib"),
        os.path.join(corpora_dir, "lean4", "src"),
        os.path.join(corpora_dir, "batteries", "Batteries"),
    ]
    names: Set[str] = set()
    extra_mod_parts: Set[str] = set()
    for d in dirs:
        if not os.path.isdir(d):
            continue
        lx, _ = sighash.build_lexicon(d, workers=workers)
        names.update(lx.names)
        # Also allow Mathlib/Lean/Batteries module path segments (for `import Mathlib.X.Y` & `open`)
        for dp, _, fns in os.walk(d):
            rel_d = os.path.relpath(dp, os.path.dirname(d))
            mod_prefix = ".".join(p for p in rel_d.split(os.sep) if p and p != ".")
            for seg in rel_d.split(os.sep):
                if seg and seg != "." and seg not in PROJECT_FORBIDDEN_ROOTS:
                    extra_mod_parts.add(seg)
            for fn in fns:
                if fn.endswith(".lean"):
                    stem = fn[:-5]
                    if stem not in PROJECT_FORBIDDEN_ROOTS:
                        extra_mod_parts.add(stem)
                        if mod_prefix:
                            names.add(f"{mod_prefix}.{stem}")
    al = StdAllowlist(names, extra_mod_parts)
    if out_path:
        al.save(out_path)
    return al


def load_or_build_allowlist(
    cache_path: str = DEFAULT_ALLOWLIST,
    corpora_dir: str = CORPORA_DIR,
    workers: int = 16,
) -> StdAllowlist:
    if os.path.exists(cache_path):
        return StdAllowlist.load(cache_path)
    if os.path.isdir(os.path.join(corpora_dir, "mathlib4")):
        return build_std_allowlist(corpora_dir, cache_path, workers=workers)
    return StdAllowlist((), ())


# ---------------------------------------------------------------------------
# Fail-Closed Cluster Blinding & Unblinded Companion Generator
# ---------------------------------------------------------------------------
def _extract_module_boundary(abs_path: str) -> Dict[str, Any]:
    """Read one `.lean` module and extract imports, opens, forensic markers, and
    body-free declaration headers via `sighash.iter_source_decls`."""
    with open(abs_path, "rb") as f:
        raw = f.read()
    lines_wc = raw.count(b"\n")
    text = raw.decode("utf-8", errors="replace")
    clean = sighash.strip_comments(text)
    clean_lines = clean.split("\n")

    mathlib_whole = False
    mathlib_subimports: Set[str] = set()
    proj_imports: Set[str] = set()
    opens: Set[str] = set()

    for ln in clean_lines:
        s = ln.strip()
        if not s:
            continue
        m_imp = tier1._RE_IMPORT.match(ln)
        if m_imp:
            imp = m_imp.group(1)
            if imp == "Mathlib":
                mathlib_whole = True
            elif tier1._is_std_import(imp):
                mathlib_subimports.add(imp)
            else:
                proj_imports.add(imp)
        elif s.startswith("open "):
            m_op = tier1._RE_OPEN.match(ln)
            if m_op:
                toks = m_op.group(1).strip().split()
                if toks and toks[-1] == "in":
                    toks = toks[:-1]
                for t in toks:
                    if t == "scoped":
                        continue
                    if t in ("hiding", "renaming") or t.startswith("("):
                        break
                    opens.add(t)

    decls: List[Dict[str, Any]] = []
    for d in sighash.iter_source_decls(clean, with_sig=True):
        r = sighash.source_sig(d["var_binders"] + d["binders"], d["type"])
        raw_hdr_tokens = r["tokens_n"]
        decls.append({
            "name": d["name"],
            "kind": d["kind"],
            "line": d["line"],
            "namespace": d["namespace"],
            "opens": list(d["opens"]),
            "tokens_n": raw_hdr_tokens,
            "n_tokens": r["n_tokens"],
            "s1n": r["s1n"],
        })

    flags: Set[str] = set()
    for tag, rx in tier1._FORENSIC_MARKERS:
        if rx.search(clean):
            flags.add(tag)

    return {
        "lines_wc": lines_wc,
        "mathlib_whole": mathlib_whole,
        "mathlib_subimports": sorted(mathlib_subimports),
        "proj_imports": sorted(proj_imports),
        "opens": sorted(opens),
        "decls": decls,
        "flags": sorted(flags),
    }


def blind_cluster(
    cluster_id: str,
    cohort: str,
    target_kind: str,
    target_name: str,
    boundary_modules: Sequence[str],
    total_cluster_modules: int,
    src_dir: str,
    project_lexicon: sighash.Lexicon,
    std_allowlist: StdAllowlist,
    external_importers: int = 0,
    max_decls_per_module: int = 6,
    max_total_decls: int = 18,
    unfolder: Optional[KernelTypeUnfolder] = None,
    unfold_hops: int = 0,
    extra_kernel_decls: Sequence[str] = (),
) -> Tuple[Dict[str, Any], Dict[str, Any], Dict[str, Any]]:
    """Build (blinded_record, unblinded_record, cluster_meta) for one cluster boundary.

    Fail-closed guarantee: every identifier inside `blinded_record` is verified to be either
    an opaque ID (`C##`, `M##`, `D###`, `P###`, `f##`, `#k`, `u#k`), a Lean syntax keyword,
    a schema field, or a verified `std_allowlist` symbol.
    """
    mod_set = set(boundary_modules)
    mod_to_opaque = {m: f"M{i:02d}" for i, m in enumerate(boundary_modules, 1)}

    parsed_mods: List[Tuple[str, Dict[str, Any]]] = []
    cluster_decl_names: Set[str] = set()
    cluster_decl_shorts: Set[str] = set()
    cluster_folder_tokens: Set[str] = set()
    total_lines = 0

    for seg in target_name.split("."):
        if seg:
            cluster_folder_tokens.add(seg)

    for m in boundary_modules:
        for seg in m.split("."):
            if seg:
                cluster_folder_tokens.add(seg)
        rel = m.replace(".", os.sep) + ".lean"
        abs_p = os.path.join(src_dir, rel)
        info = _extract_module_boundary(abs_p)
        parsed_mods.append((m, info))
        total_lines += info["lines_wc"]
        for d in info["decls"]:
            cluster_decl_names.add(d["name"])
            for seg in d["name"].split("."):
                if seg:
                    cluster_decl_shorts.add(seg)

    # Select representative boundary declarations (preferring theorems/structures/defs with richer signatures)
    selected_decls: List[Tuple[str, Dict[str, Any]]] = []
    for m, info in parsed_mods:
        # Rank decls within module: theorems/structures/defs with more tokens first (deterministic tie-break by line)
        ranked = sorted(
            info["decls"],
            key=lambda d: (0 if d["kind"] in ("theorem", "lemma", "structure", "class", "inductive") else 1,
                           -d["n_tokens"], d["line"]),
        )
        for d in ranked[:max_decls_per_module]:
            selected_decls.append((m, d))
            if len(selected_decls) >= max_total_decls:
                break
        if len(selected_decls) >= max_total_decls:
            break

    # Assign deterministic opaque IDs D001.. for selected decls, P001.. for external project-local symbols
    decl_to_opaque: Dict[str, str] = {}
    for idx, (_, d) in enumerate(selected_decls, 1):
        decl_to_opaque[d["name"]] = f"D{idx:03d}"

    proj_sym_map: Dict[str, str] = {}
    field_sym_map: Dict[str, str] = {}

    def _opaque_proj(key: str) -> str:
        if key not in proj_sym_map:
            proj_sym_map[key] = f"P{len(proj_sym_map) + 1:03d}"
        return proj_sym_map[key]

    def _opaque_field(key: str) -> str:
        if key not in field_sym_map:
            field_sym_map[key] = f"f{len(field_sym_map) + 1:02d}"
        return field_sym_map[key]

    def _blind_token(tok: str, ns: str, opens: Sequence[str]) -> Tuple[str, bool]:
        """Return (blinded_token, was_local)."""
        if tok in sighash._KEYWORDS or not tok:
            return tok, False
        # Bound variable or bound-variable projection `#0`, `#0.Prime`, `#0.myField`
        if tok.startswith("#"):
            if "." not in tok:
                return tok, False
            base, rest = tok.split(".", 1)
            out_parts = [base]
            was_loc = False
            for part in rest.split("."):
                if part.isdigit():
                    out_parts.append(part)
                elif std_allowlist.is_allowed(part) and part not in cluster_decl_shorts:
                    out_parts.append(part)
                else:
                    out_parts.append(_opaque_field(part))
                    was_loc = True
            return ".".join(out_parts), was_loc
        if tok.startswith("u#"):
            return tok, False
        # Non-identifier (operator, numeral, punctuation, string literal)
        if not sighash._RE_IDENT_FULL.match(tok):
            # Also redact string literals in case a metaprogram embeds a project name
            if tok.startswith('"') and tok.endswith('"'):
                return '"STR"', False
            return tok, False

        # 1. Check if this identifier resolves to a declaration inside this cluster
        resolved = project_lexicon.resolve_source(tok, ns, opens)
        if resolved is not None:
            if resolved in decl_to_opaque:
                return decl_to_opaque[resolved], True
            if resolved in cluster_decl_names:
                return _opaque_proj(resolved), True
            # Resolved to another project-local symbol in the mirror
            return _opaque_proj(resolved), True

        # 2. Check exact match against cluster's own decl names or forbidden folder tokens
        if tok in decl_to_opaque:
            return decl_to_opaque[tok], True
        if tok in cluster_decl_names or tok in PROJECT_FORBIDDEN_ROOTS:
            return _opaque_proj(tok), True
        if tok.split(".", 1)[0] in PROJECT_FORBIDDEN_ROOTS:
            return _opaque_proj(tok), True

        # 3. Allow ONLY verified Mathlib / Lean 4 / Batteries symbols (fail-closed!)
        if std_allowlist.is_allowed(tok):
            return tok, False

        # 4. Fail-closed fallback: any unrecognized identifier becomes an opaque P### ID
        return _opaque_proj(tok), True

    mathlib_whole = any(info["mathlib_whole"] for _, info in parsed_mods)
    mathlib_subs = sorted({imp for _, info in parsed_mods for imp in info["mathlib_subimports"]})
    intra_edges = 0
    ext_imports: Set[str] = set()
    std_opens: Set[str] = set()
    omitted_opens: Set[str] = set()
    generic_flags: Set[str] = set()
    raw_flags: Set[str] = set()

    for m, info in parsed_mods:
        for imp in info["proj_imports"]:
            if imp in mod_set:
                intra_edges += 1
            else:
                ext_imports.add(imp)
        for op in info["opens"]:
            # Only keep opens whose full path or every segment is in std_allowlist AND not project-local
            if std_allowlist.is_allowed(op) and project_lexicon.resolve_source(op, "", ()) is None:
                std_opens.add(op)
            else:
                omitted_opens.add(op)
        for fl in info["flags"]:
            raw_flags.add(fl)
            generic_flags.add(_FLAG_GENERIC_MAP.get(fl, "special_marker"))

    blinded_decls: List[Dict[str, Any]] = []
    unblinded_decls: List[Dict[str, Any]] = []
    for idx, (m, d) in enumerate(selected_decls, 1):
        did = f"D{idx:03d}"
        b_toks: List[str] = []
        n_loc = 0
        for tok in d["tokens_n"]:
            bt, is_loc = _blind_token(tok, d["namespace"], d["opens"])
            b_toks.append(bt)
            if is_loc:
                n_loc += 1
        # Truncate cleanly on a TOKEN boundary (never slice mid-identifier!)
        parts_b: List[str] = []
        cur_len = 0
        for bt in b_toks:
            add = len(bt) + (1 if parts_b else 0)
            if cur_len + add > 316:
                parts_b.append("...")
                break
            parts_b.append(bt)
            cur_len += add
        sig_b = " ".join(parts_b)
        blinded_decls.append({
            "id": did,
            "module": mod_to_opaque[m],
            "kind": d["kind"],
            "signature_blinded": sig_b,
            "n_tokens": d["n_tokens"],
            "n_local": n_loc,
        })
        parts_u: List[str] = []
        cur_len_u = 0
        for ut in d["tokens_n"]:
            add = len(ut) + (1 if parts_u else 0)
            if cur_len_u + add > 236:
                parts_u.append("...")
                break
            parts_u.append(ut)
            cur_len_u += add
        sig_u = " ".join(parts_u)
        unblinded_decls.append({
            "id": did,
            "module": m,
            "name": d["name"],
            "kind": d["kind"],
            "signature_canonical": sig_u,
            "n_tokens": d["n_tokens"],
        })

    blinded_payload = {
        "schema": SCHEMA_VERSION,
        "blinded": True,
        "cluster_id": cluster_id,
        "module_count": total_cluster_modules,
        "boundary_modules_shown": len(parsed_mods),
        "total_lines": total_lines,
        "imports_summary": {
            "mathlib_whole": mathlib_whole,
            "mathlib_subimports": mathlib_subs,
            "intra_cluster_edges": intra_edges,
            "external_cluster_imports": len(ext_imports),
            "external_cluster_importers": external_importers,
        },
        "std_opens": sorted(std_opens),
        "omitted_project_opens_count": len(omitted_opens),
        "generic_flags": sorted(generic_flags),
        "declarations": blinded_decls,
    }
    if unfolder is not None and unfold_hops > 0:
        unfold_targets: List[str] = []
        seen_ut: Set[str] = set()
        for nm in list(extra_kernel_decls) + [d["name"] for _, d in selected_decls]:
            if nm and nm not in seen_ut:
                seen_ut.add(nm)
                unfold_targets.append(nm)
        blinded_payload["unfolded_type_context"] = unfolder.unfold_cluster(
            unfold_targets,
            opaque_name_fn=lambda nm: decl_to_opaque.get(nm, _opaque_proj(nm)),
            unfold_hops=unfold_hops,
        )
    prompt_sha256 = hashlib.sha256(
        json.dumps(blinded_payload, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    blinded_payload["prompt_sha256"] = prompt_sha256

    unblinded_payload = {
        "schema": SCHEMA_VERSION,
        "blinded": False,
        "cluster_id": cluster_id,
        "target_kind": target_kind,
        "target_name": target_name,
        "boundary_modules": list(boundary_modules),
        "module_count": total_cluster_modules,
        "total_lines": total_lines,
        "imports_summary": {
            "mathlib_whole": mathlib_whole,
            "mathlib_subimports": mathlib_subs,
            "project_imports_sample": sorted(ext_imports)[:10],
            "external_cluster_imports": len(ext_imports),
            "external_cluster_importers": external_importers,
        },
        "opens": sorted(std_opens | omitted_opens)[:20],
        "flags": sorted(raw_flags),
        "declarations": unblinded_decls,
    }

    # Build strict cluster-specific forbidden token set for leak verification
    cluster_forbidden = {
        t for t in (cluster_folder_tokens | cluster_decl_shorts)
        if len(t) >= 3 and not std_allowlist.is_allowed(t)
    } | PROJECT_FORBIDDEN_ROOTS

    cluster_meta = {
        "cluster_id": cluster_id,
        "cohort": cohort,
        "target_kind": target_kind,
        "target_name": target_name,
        "module_count": total_cluster_modules,
        "boundary_modules": list(boundary_modules),
        "declared_namespaces": sorted({d["namespace"] for _, info in parsed_mods for d in info["decls"] if d["namespace"]})[:8],
        "prompt_sha256": prompt_sha256,
        "forbidden_tokens_sample": sorted(cluster_forbidden)[:25],
        "forbidden_token_count": len(cluster_forbidden),
        "all_forbidden_tokens": sorted(cluster_forbidden),
    }
    return blinded_payload, unblinded_payload, cluster_meta


# ---------------------------------------------------------------------------
# Strict Leak Verification (Gate F3)
# ---------------------------------------------------------------------------
def _iter_strings(obj: Any, skip_keys: Set[str] = frozenset({"prompt_sha256"})) -> Iterable[str]:
    if isinstance(obj, str):
        yield obj
    elif isinstance(obj, list):
        for item in obj:
            yield from _iter_strings(item, skip_keys)
    elif isinstance(obj, dict):
        for k, v in obj.items():
            if k in skip_keys:
                continue
            yield from _iter_strings(v, skip_keys)


def verify_no_leaks(
    blinded_record: Mapping[str, Any],
    std_allowlist: StdAllowlist,
    extra_forbidden: Iterable[str] = (),
) -> Dict[str, Any]:
    """Prove no project folder/file/declaration identifier survives in `blinded_record`.

    Runs TWO independent checks:
      1. Fail-closed allowlist check: EVERY alphabetic identifier token in the blinded
         payload must be an opaque ID, a Lean keyword, a schema enum, or in `std_allowlist`.
      2. Explicit forbidden-name check: NO project-exclusive folder/file/decl identifier
         from `extra_forbidden ∪ PROJECT_FORBIDDEN_ROOTS` appears as a token or substring.
    """
    leaks: List[Dict[str, str]] = []
    checked_tokens = 0
    forbidden = (set(extra_forbidden) | PROJECT_FORBIDDEN_ROOTS) - std_allowlist.tokens
    # Longer forbidden tokens (>= 5 chars) also checked as case-insensitive substrings!
    forbidden_sub = sorted({f.lower() for f in forbidden if len(f) >= 5})
    forbidden_exact = set(forbidden)

    all_text_parts: List[str] = []
    for s in _iter_strings(blinded_record):
        all_text_parts.append(s)
        for tok in _RE_ALPHA_TOK.findall(s):
            checked_tokens += 1
            if tok == "STR":
                continue
            if _RE_OPAQUE_ID.match(tok):
                continue
            if tok in SCHEMA_SAFE_TOKENS or tok in sighash._KEYWORDS:
                continue
            if tok in forbidden_exact:
                leaks.append({"check": "forbidden_exact", "token": tok})
                continue
            if not std_allowlist.is_allowed(tok):
                # Allow dotted chains whose components are each an opaque ID, digit, or allowlisted std token (e.g. `f02.Word`)
                parts = tok.split(".")
                if len(parts) > 1 and all(
                    _RE_OPAQUE_ID.match(p) or p.isdigit() or std_allowlist.is_allowed(p)
                    for p in parts
                ):
                    continue
                leaks.append({"check": "not_in_std_allowlist", "token": tok})

    joined_low = " ".join(all_text_parts).lower()
    for sub in forbidden_sub:
        if sub in joined_low:
            # Make sure it isn't just a substring of an allowlisted Mathlib word (e.g. 'prime' in 'Prime')
            # Check if it appears outside any allowlisted word:
            hits = [
                tok for tok in _RE_ALPHA_TOK.findall(" ".join(all_text_parts))
                if sub in tok.lower() and not std_allowlist.is_allowed(tok)
                and tok not in SCHEMA_SAFE_TOKENS and not _RE_OPAQUE_ID.match(tok)
            ]
            if hits:
                leaks.append({"check": "forbidden_substring", "token": sub, "in": hits[0]})

    return {
        "cluster_id": blinded_record.get("cluster_id"),
        "passed": len(leaks) == 0,
        "checked_tokens": checked_tokens,
        "forbidden_checked": len(forbidden),
        "leaks": leaks,
    }


# ---------------------------------------------------------------------------
# Pilot Cluster Selection (24 diverse, deterministic cluster boundaries)
# ---------------------------------------------------------------------------
def select_pilot_clusters(
    tier1_db: str = DEFAULT_TIER1_DB,
    leanre_db: str = DEFAULT_LEANRE_DB,
) -> List[Dict[str, Any]]:
    """Deterministically select 24 pilot clusters across 3 cohorts (8 + 8 + 8):
      * Cohort A (`misfile`, 8 clusters): 7 top-ranked diverse Tier 1 high-score misfiles
        + the canonical F1 misfile `InvFiveLogLeSumInvPrimes` (`GlobalTheory.PrimeRecip.table_ok`).
      * Cohort B (`dominator_boundary`, 8 clusters): major folder/component boundaries
        selected by module count & dominator subtree size in `leanre.db`.
      * Cohort C (`spine_infra`, 8 clusters): top-level architectural spine & infrastructure
        boundaries (`Main`/`Statements`, `Formalism.MainNotions`, `PositivityTheory`, etc.).
    """
    c1 = sqlite3.connect(f"file:{tier1_db}?mode=ro", uri=True)
    c2 = sqlite3.connect(f"file:{leanre_db}?mode=ro", uri=True) if os.path.exists(leanre_db) else None
    clusters: List[Dict[str, Any]] = []

    def _fan_in(mod: str) -> int:
        if c2 is None:
            return 0
        row = c2.execute("SELECT fan_in FROM modules WHERE name = ?", (mod,)).fetchone()
        return int(row[0]) if row else 0

    try:
        # ---- Cohort A: 8 high-score Tier 1 misfiles (diverse folders/domains, incl. InvFiveLogLeSumInvPrimes)
        seen_ns: Set[str] = set()
        misfile_picks: List[Tuple[str, str, int]] = []
        # Pick top diverse high-score misfiles with >= 5 declarations
        for mod, ns, fl2, score, decl_cnt in c1.execute("""
            SELECT m.module, m.declared_ns, m.folder_l2, m.score, f.decl_count
            FROM misfiles m JOIN module_fingerprints f ON f.module = m.module
            WHERE m.tier = 'high' AND m.is_statement_wrapper = 0 AND f.decl_count >= 5
            ORDER BY m.rank ASC
            LIMIT 250
        """):
            if ns in seen_ns:
                continue
            seen_ns.add(ns)
            misfile_picks.append((mod, fl2, 1))
            if len(misfile_picks) >= 7:
                break
        # Ensure GlobalTheory.PrimeRecip (InvFiveLogLeSumInvPrimes) is included in Cohort A
        f1_mod = "Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes"
        if not any(m == f1_mod for m, _, _ in misfile_picks):
            misfile_picks.append((f1_mod, "Development.AbelianVarietyTheory", 1))
        for mod, _fl2, cnt in misfile_picks[:8]:
            clusters.append({
                "cohort": "misfile",
                "target_kind": "module",
                "target_name": mod,
                "boundary_modules": [mod],
                "total_modules": cnt,
                "external_importers": _fan_in(mod),
            })

        # ---- Cohort B: 8 major folder/component boundaries (non-shim, rich decls, diverse L2 folders)
        cohort_b_folders = [
            "Formalism.PeriodIntegrals",
            "Formalism.PadicSubsetSums",
            "Formalism.HermitianCurvature",
            "Formalism.LocalToGlobal",
            "GroundTheory.HeightsAndTheta",
            "ReciprocityTheory.ReductiveGroups",
            "CompanionTheory.SpectralGeometry",
            "Development.EtaleCohomology",
        ]
        for fl2 in cohort_b_folders:
            tot_m = c1.execute(
                "SELECT COUNT(*) FROM module_fingerprints WHERE folder_l2 = ?", (fl2,)
            ).fetchone()[0]
            if tot_m == 0:
                continue
            # Pick top 4 boundary modules by fan_in / dom_subtree_size (from leanre.db if available, else decl_count)
            if c2 is not None:
                bmods = [
                    r[0] for r in c2.execute("""
                        SELECT name FROM modules
                        WHERE namespace_l2 = ? AND is_shim = 0 AND decl_count >= 2
                          AND name NOT LIKE '%Statement'
                        ORDER BY dom_subtree_size DESC, fan_in DESC, name ASC
                        LIMIT 4
                    """, (fl2,))
                ]
                ext_imp = c2.execute(
                    "SELECT COALESCE(MAX(fan_in), 0) FROM modules WHERE namespace_l2 = ?", (fl2,)
                ).fetchone()[0]
            else:
                bmods = [
                    r[0] for r in c1.execute("""
                        SELECT module FROM module_fingerprints
                        WHERE folder_l2 = ? AND is_shim = 0 AND is_statement_wrapper = 0 AND decl_count >= 2
                        ORDER BY decl_count DESC, module ASC
                        LIMIT 4
                    """, (fl2,))
                ]
                ext_imp = 0
            if bmods:
                clusters.append({
                    "cohort": "dominator_boundary",
                    "target_kind": "folder",
                    "target_name": fl2,
                    "boundary_modules": bmods,
                    "total_modules": tot_m,
                    "external_importers": int(ext_imp),
                })

        # ---- Cohort C: 8 top-spine & infrastructure boundaries
        cohort_c_specs = [
            ("module", "Statements", ["Statements", "Main"]),
            ("folder", "Development.AutomorphicArithmetic", None),
            ("folder", "Formalism.SharpRestriction", None),
            ("folder", "PositivityTheory", None),
            ("folder", "Development.WeilBound", None),
            ("folder", "Development.ResolutionOfSingularities", None),
            ("folder", "Development.AutomorphicSpectrum", None),
            ("folder", "Lemmata", None),
        ]
        for tkind, tname, explicit_mods in cohort_c_specs:
            if explicit_mods:
                bmods = explicit_mods
                tot_m = len(bmods)
                ext_imp = sum(_fan_in(m) for m in bmods)
            else:
                prefix = tname + "."
                tot_m = c1.execute(
                    "SELECT COUNT(*) FROM module_fingerprints WHERE module LIKE ? OR module = ?",
                    (prefix + "%", tname),
                ).fetchone()[0]
                if tot_m == 0:
                    continue
                if c2 is not None:
                    bmods = [
                        r[0] for r in c2.execute("""
                            SELECT name FROM modules
                            WHERE (name LIKE ? OR name = ?) AND is_shim = 0 AND decl_count >= 1
                              AND name NOT LIKE '%Statement'
                            ORDER BY dom_subtree_size DESC, fan_in DESC, name ASC
                            LIMIT 4
                        """, (prefix + "%", tname))
                    ]
                    ext_imp = c2.execute(
                        "SELECT COALESCE(MAX(fan_in), 0) FROM modules WHERE name LIKE ? OR name = ?",
                        (prefix + "%", tname),
                    ).fetchone()[0]
                else:
                    bmods = [
                        r[0] for r in c1.execute("""
                            SELECT module FROM module_fingerprints
                            WHERE (module LIKE ? OR module = ?) AND is_shim = 0 AND decl_count >= 1
                            ORDER BY decl_count DESC, module ASC
                            LIMIT 4
                        """, (prefix + "%", tname))
                    ]
                    ext_imp = 0
            if bmods:
                clusters.append({
                    "cohort": "spine_infra",
                    "target_kind": tkind,
                    "target_name": tname,
                    "boundary_modules": bmods,
                    "total_modules": tot_m,
                    "external_importers": int(ext_imp),
                })
    finally:
        c1.close()
        if c2 is not None:
            c2.close()

    for idx, cl in enumerate(clusters, 1):
        cl["cluster_id"] = f"C{idx:02d}"
    return clusters


def _load_tier2_lib_tokens(tier2_db: str) -> Optional[Set[str]]:
    if not tier2_db or not os.path.exists(tier2_db):
        return None
    conn = sqlite3.connect(f"file:{tier2_db}?mode=ro", uri=True)
    try:
        toks: Set[str] = set()
        for nm, mod in conn.execute(
            "SELECT name, module FROM corpus_sigs WHERE repo IN ('mathlib4','lean4','batteries')"
        ):
            for part in nm.split("."):
                toks.add(part)
            for part in mod.split("."):
                toks.add(part)
        return toks
    finally:
        conn.close()


def select_phase4_clusters(
    clusters_json: str = DEFAULT_CLUSTERS_JSON,
    tier1_db: str = DEFAULT_TIER1_DB,
    leanre_db: str = DEFAULT_LEANRE_DB,
    src_dir: str = DEFAULT_SRC,
    target_count: int = 100,
) -> List[Dict[str, Any]]:
    """Deterministically select >= 100 high-leverage boundary clusters across 4 cohorts:
      * `extreme_misfile` (20): top calibrated Tier 1 `extreme_outlier` modules (incl. InvFiveLogLeSumInvPrimes)
      * `spine_tcb` (8): Statements/Main + major spine & pillar entry theorems
      * `pillar_dominator` (56): top `dom_subtree` blueprint clusters from `clusters.json`
      * `diamond_neighborhood` (16): top `residual_neighborhood` clusters from `clusters.json`
    """
    c1 = sqlite3.connect(f"file:{tier1_db}?mode=ro", uri=True)
    c2 = sqlite3.connect(f"file:{leanre_db}?mode=ro", uri=True) if os.path.exists(leanre_db) else None
    with open(clusters_json, encoding="utf-8") as f:
        cdata = json.load(f)

    def _exists_mod(m: Optional[str]) -> bool:
        return bool(m) and os.path.exists(os.path.join(src_dir, m.replace(".", os.sep) + ".lean"))

    def _fan_in(mod: str) -> int:
        if c2 is None:
            return 0
        row = c2.execute("SELECT fan_in FROM modules WHERE name = ?", (mod,)).fetchone()
        return int(row[0]) if row else 0

    selected: List[Dict[str, Any]] = []
    seen_targets: Set[Tuple[str, str]] = set()

    try:
        # 1. Cohort `extreme_misfile` (20 diverse calibrated extreme_outlier modules)
        seen_ns: Set[str] = set()
        mis_picks: List[str] = []
        f1_mod = "Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes"
        for mod, ns in c1.execute("""
            SELECT m.module, m.declared_ns
            FROM misfiles m JOIN module_fingerprints f ON f.module = m.module
            WHERE m.band = 'extreme_outlier' AND f.decl_count >= 4
            ORDER BY m.rank ASC
            LIMIT 400
        """):
            if ns in seen_ns or not _exists_mod(mod):
                continue
            seen_ns.add(ns)
            mis_picks.append(mod)
            if len(mis_picks) >= 19:
                break
        if f1_mod not in mis_picks and _exists_mod(f1_mod):
            mis_picks.append(f1_mod)
        for mod in mis_picks[:20]:
            selected.append({
                "cohort": "extreme_misfile",
                "target_kind": "module",
                "target_name": mod,
                "boundary_modules": [mod],
                "total_modules": 1,
                "external_importers": _fan_in(mod),
                "extra_kernel_decls": [],
            })
            seen_targets.add(("module", mod))

        # 2. Cohort `spine_tcb` (8 top-level spine / TCB / pillar roots)
        spine_specs = [
            ("module", "Statements", ["Statements", "Main"], ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_eq_zero_re"]),
            ("decl", "allChi", ["Supplements.Kernels.MainTheorems"], ["allChi"]),
            ("decl", "UpperTheory.FinalTheorems.everyCharacter", ["Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion"], ["UpperTheory.FinalTheorems.everyCharacter"]),
            ("decl", "UpperTheory.FinalTheorems.everyCharacter_of_row", ["Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion"], ["UpperTheory.FinalTheorems.everyCharacter_of_row"]),
            ("decl", "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter", ["Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc"], ["UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter"]),
            ("decl", "UpperTheory.One.vwin_of_row", ["Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow"], ["UpperTheory.One.vwin_of_row"]),
            ("decl", "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin", ["Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin"], ["UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin"]),
            ("decl", "UpperTheory.Lit.every_character_of_theta_integrals_local_matching", ["Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SiegelEisensteinSecondTermHypotheses"], ["UpperTheory.Lit.every_character_of_theta_integrals_local_matching"]),
        ]
        for tkind, tname, bmods, kdecls in spine_specs:
            valid_mods = [m for m in bmods if _exists_mod(m)]
            if not valid_mods:
                continue
            selected.append({
                "cohort": "spine_tcb",
                "target_kind": tkind,
                "target_name": tname,
                "boundary_modules": valid_mods,
                "total_modules": len(valid_mods),
                "external_importers": sum(_fan_in(m) for m in valid_mods),
                "extra_kernel_decls": kdecls,
            })
            seen_targets.add((tkind, tname))

        # 3. Cohort `pillar_dominator` (56 largest dom_subtree clusters from clusters.json)
        dom_cls = [cl for cl in cdata["clusters"] if cl["kind"] == "dom_subtree"]
        dom_added = 0
        for cl in dom_cls:
            if dom_added >= 56:
                break
            bmods = []
            kdecls = []
            for bd in cl.get("boundary_decls", []):
                if bd.get("name"):
                    kdecls.append(bd["name"])
                m = bd.get("module")
                if m and _exists_mod(m) and m not in bmods:
                    bmods.append(m)
                if len(bmods) >= 3:
                    break
            if not bmods:
                continue
            tname = cl["root_decl"]
            if ("decl", tname) in seen_targets:
                continue
            seen_targets.add(("decl", tname))
            selected.append({
                "cohort": "pillar_dominator",
                "target_kind": "decl",
                "target_name": tname,
                "boundary_modules": bmods,
                "total_modules": int(cl.get("live_modules") or len(bmods)),
                "external_importers": int(cl.get("in_degree_clusters") or 0),
                "extra_kernel_decls": kdecls[:10],
                "blueprint_cluster_id": cl["cluster_id"],
                "pillar": cl["pillar"],
            })
            dom_added += 1

        # 4. Cohort `diamond_neighborhood` (fill up to target_count from residual_neighborhood clusters)
        res_cls = [cl for cl in cdata["clusters"] if cl["kind"] == "residual_neighborhood"]
        for cl in res_cls:
            if len(selected) >= target_count:
                break
            bmods = []
            kdecls = []
            for bd in cl.get("boundary_decls", []):
                if bd.get("name"):
                    kdecls.append(bd["name"])
                m = bd.get("module")
                if m and _exists_mod(m) and m not in bmods:
                    bmods.append(m)
                if len(bmods) >= 3:
                    break
            if not bmods:
                continue
            # Use folder_l2 or root_decl as valid annot target
            top_fl = cl["top_folders_l2"][0]["folder"] if cl.get("top_folders_l2") else ""
            if top_fl and ("folder", top_fl) not in seen_targets:
                tkind, tname = "folder", top_fl
            elif ("decl", cl["root_decl"]) not in seen_targets:
                tkind, tname = "decl", cl["root_decl"]
            else:
                continue
            seen_targets.add((tkind, tname))
            selected.append({
                "cohort": "diamond_neighborhood",
                "target_kind": tkind,
                "target_name": tname,
                "boundary_modules": bmods,
                "total_modules": int(cl.get("live_modules") or len(bmods)),
                "external_importers": int(cl.get("in_degree_clusters") or 0),
                "extra_kernel_decls": kdecls[:10],
                "blueprint_cluster_id": cl["cluster_id"],
                "pillar": cl["pillar"],
            })
    finally:
        c1.close()
        if c2 is not None:
            c2.close()

    width = 3 if len(selected) >= 100 else 2
    for idx, cl in enumerate(selected, 1):
        cl["cluster_id"] = f"C{idx:0{width}d}"
    return selected


# ---------------------------------------------------------------------------
# Agreement Metrics (Blinded vs Unblinded)
# ---------------------------------------------------------------------------
def _content_words(label: str) -> Set[str]:
    return {
        w.lower() for w in re.findall(r"[A-Za-z0-9]+", label)
        if len(w) >= 3 and w.lower() not in _LABEL_STOPWORDS
    }


def _jaccard(a: Set[str], b: Set[str]) -> float:
    if not a and not b:
        return 1.0
    if not a or not b:
        return 0.0
    return len(a & b) / len(a | b)


def compute_agreement(
    blinded_labels: Mapping[str, Mapping[str, Any]],
    unblinded_labels: Mapping[str, Mapping[str, Any]],
    cohorts: Mapping[str, str],
) -> Dict[str, Any]:
    """Compute exact agreement, Cohen's kappa, top-2 overlap, and label Jaccard."""
    ids = sorted(set(blinded_labels) & set(unblinded_labels))
    n = len(ids)
    if n == 0:
        return {"n": 0, "exact_agree": 0, "exact_rate": 0.0, "cohens_kappa": 0.0,
                "top2_overlap_rate": 0.0, "mean_label_jaccard": 0.0, "by_cohort": {}}

    def _stats_for(subset: List[str]) -> Dict[str, Any]:
        m = len(subset)
        if m == 0:
            return {"n": 0, "agree": 0, "exact_rate": 0.0, "cohens_kappa": 0.0,
                    "top2_overlap_rate": 0.0, "mean_label_jaccard": 0.0}
        agree = 0
        top2 = 0
        jacc_sum = 0.0
        b_cnt: collections.Counter = collections.Counter()
        u_cnt: collections.Counter = collections.Counter()
        for cid in subset:
            bl = blinded_labels[cid]
            ul = unblinded_labels[cid]
            bd = str(bl["primary_domain"])
            ud = str(ul["primary_domain"])
            b_cnt[bd] += 1
            u_cnt[ud] += 1
            if bd == ud:
                agree += 1
            b_set = {bd} | ({str(bl["secondary_domain"])} if bl.get("secondary_domain") else set())
            u_set = {ud} | ({str(ul["secondary_domain"])} if ul.get("secondary_domain") else set())
            if b_set & u_set:
                top2 += 1
            jacc_sum += _jaccard(_content_words(str(bl["short_label"])), _content_words(str(ul["short_label"])))
        po = agree / m
        pe = sum((b_cnt[k] / m) * (u_cnt[k] / m) for k in set(b_cnt) | set(u_cnt))
        kappa = ((po - pe) / (1.0 - pe)) if (1.0 - pe) > 1e-12 else (1.0 if po == 1.0 else 0.0)
        return {
            "n": m,
            "agree": agree,
            "exact_rate": round(po, 4),
            "cohens_kappa": round(kappa, 4),
            "top2_overlap_rate": round(top2 / m, 4),
            "mean_label_jaccard": round(jacc_sum / m, 4),
        }

    overall = _stats_for(ids)
    by_cohort: Dict[str, Any] = {}
    for coh in sorted(set(cohorts.get(cid, "unknown") for cid in ids)):
        sub = [cid for cid in ids if cohorts.get(cid, "unknown") == coh]
        by_cohort[coh] = _stats_for(sub)

    return {
        "n": overall["n"],
        "agree": overall["agree"],
        "of": overall["n"],
        "exact_rate": overall["exact_rate"],
        "cohens_kappa": overall["cohens_kappa"],
        "top2_overlap_rate": overall["top2_overlap_rate"],
        "mean_label_jaccard": overall["mean_label_jaccard"],
        "by_cohort": by_cohort,
    }


# ---------------------------------------------------------------------------
# Strict AI-Draft Annotation Pack Ingester (Gate F3 + A2/A3 compliant)
# ---------------------------------------------------------------------------
def ingest_labels(
    manifest: Mapping[str, Any],
    blinded_labels: Sequence[Mapping[str, Any]],
    unblinded_labels: Sequence[Mapping[str, Any]],
    model_name: str,
    out_pack_path: Optional[str] = DEFAULT_PACK,
    out_pilot_json: Optional[str] = DEFAULT_PILOT_JSON,
    layer_id: str = AI_LAYER_ID,
    now: Optional[str] = None,
    raw_blinded_labels: Optional[Sequence[Mapping[str, Any]]] = None,
) -> Tuple[annot.Pack, Dict[str, Any]]:
    """Ingest blinded + unblinded labels ONLY into an off-by-default `ai-draft` layer.

    Enforces:
      * Every cluster has a validated blinded label (`primary_domain` in `DOMAIN_TAXONOMY`).
      * Every emitted annotation lives in `kind="ai-draft"`, `default_on=False`,
        with `draft=True`, `tag="M"`, `author="ai:<model>"`, and explicit `breaks`.
      * Zero `[L]` facts are emitted by AI labelers.
      * Output pack passes `annot.validate_text(..., canonical=True)` with 0 issues.
    """
    ts = now or annot.utc_now()
    clean_model = re.sub(r"[^A-Za-z0-9._-]", "-", model_name.strip()) or "unknown-model"
    ai_author = f"ai:{clean_model}"

    b_map = {str(r["cluster_id"]): dict(r) for r in blinded_labels}
    u_map = {str(r["cluster_id"]): dict(r) for r in unblinded_labels}
    meta_map = {str(c["cluster_id"]): dict(c) for c in manifest["clusters"]}
    cohorts = {cid: str(c["cohort"]) for cid, c in meta_map.items()}

    for cid, bl in b_map.items():
        if bl.get("primary_domain") not in DOMAIN_TAXONOMY:
            raise ValueError(f"Blinded label for {cid} has invalid primary_domain: {bl.get('primary_domain')!r}")
    for cid, ul in u_map.items():
        if ul.get("primary_domain") not in DOMAIN_TAXONOMY:
            raise ValueError(f"Unblinded label for {cid} has invalid primary_domain: {ul.get('primary_domain')!r}")

    agreement = compute_agreement(b_map, u_map, cohorts)
    ab_comparison: Optional[Dict[str, Any]] = None
    if raw_blinded_labels:
        r_map = {str(r["cluster_id"]): dict(r) for r in raw_blinded_labels}
        for cid, rl in r_map.items():
            if rl.get("primary_domain") not in DOMAIN_TAXONOMY:
                raise ValueError(f"Raw-blinded label for {cid} has invalid primary_domain: {rl.get('primary_domain')!r}")
        raw_ag = compute_agreement(r_map, u_map, cohorts)
        b_mean_conf = round(sum(float(b_map[c].get("confidence", 0.0)) for c in b_map) / max(1, len(b_map)), 4)
        r_mean_conf = round(sum(float(r_map[c].get("confidence", 0.0)) for c in r_map) / max(1, len(r_map)), 4)
        u_mean_conf = round(sum(float(u_map[c].get("confidence", 0.0)) for c in u_map) / max(1, len(u_map)), 4)
        b_other_pct = round(100.0 * sum(1 for c in b_map if b_map[c]["primary_domain"] == "other_mixed") / max(1, len(b_map)), 2)
        r_other_pct = round(100.0 * sum(1 for c in r_map if r_map[c]["primary_domain"] == "other_mixed") / max(1, len(r_map)), 2)
        u_other_pct = round(100.0 * sum(1 for c in u_map if u_map[c]["primary_domain"] == "other_mixed") / max(1, len(u_map)), 2)
        # Decompose agreement into substantive concrete-domain matches (unblinded != other_mixed)
        # vs degenerate abstention matches (both == other_mixed).
        non_other_cids = sorted(c for c in u_map if u_map[c]["primary_domain"] != "other_mixed" and c in b_map and c in r_map)
        def _sub_stats(arm_map: Dict[str, Dict[str, Any]]) -> Dict[str, Any]:
            n_sub = len(non_other_cids)
            both_other = sum(1 for c in u_map if c in arm_map and arm_map[c]["primary_domain"] == "other_mixed" and u_map[c]["primary_domain"] == "other_mixed")
            sub_exact = sum(1 for c in non_other_cids if arm_map[c]["primary_domain"] == u_map[c]["primary_domain"])
            sub_top2 = sum(
                1 for c in non_other_cids
                if ({arm_map[c]["primary_domain"], arm_map[c].get("secondary_domain")} - {None})
                & ({u_map[c]["primary_domain"], u_map[c].get("secondary_domain")} - {None})
            )
            return {
                "both_other_mixed_agree": both_other,
                "substantive_n": n_sub,
                "substantive_exact_agree": sub_exact,
                "substantive_exact_rate": round(sub_exact / n_sub, 4) if n_sub else 0.0,
                "substantive_top2_agree": sub_top2,
                "substantive_top2_rate": round(sub_top2 / n_sub, 4) if n_sub else 0.0,
            }
        raw_sub = _sub_stats(r_map)
        unf_sub = _sub_stats(b_map)
        cohort_deltas = {}
        for coh, ustats in agreement.get("by_cohort", {}).items():
            rstats = raw_ag.get("by_cohort", {}).get(coh, {})
            cohort_deltas[coh] = {
                "n": ustats.get("n", 0),
                "raw_exact_rate": rstats.get("exact_rate"),
                "unfolded_exact_rate": ustats.get("exact_rate"),
                "delta_exact_rate": round((ustats.get("exact_rate", 0.0) - rstats.get("exact_rate", 0.0)), 4) if rstats else None,
                "raw_kappa": rstats.get("cohens_kappa"),
                "unfolded_kappa": ustats.get("cohens_kappa"),
                "raw_top2_rate": rstats.get("top2_overlap_rate"),
                "unfolded_top2_rate": ustats.get("top2_overlap_rate"),
            }
        ab_comparison = {
            "phase3_baseline_24": {
                "n": 24, "agree": 13, "exact_rate": 0.5417, "cohens_kappa": 0.45, "top2_overlap_rate": 0.7083,
                "note": "Phase 3 24-cluster pilot without 1-2-hop kernel type unfolding (llm-reasoning-b)",
            },
            "unblinded_control_0hop": {
                "n": len(u_map),
                "mean_confidence": u_mean_conf,
                "other_mixed_pct": u_other_pct,
                "concrete_domain_n": len(non_other_cids),
            },
            "raw_blinded_no_unfold": {
                **raw_ag,
                **raw_sub,
                "mean_confidence": r_mean_conf,
                "other_mixed_pct": r_other_pct,
            },
            "unfolded_blinded": {
                **agreement,
                **unf_sub,
                "mean_confidence": b_mean_conf,
                "other_mixed_pct": b_other_pct,
            },
            "delta_unfolded_minus_raw": {
                "exact_rate": round(agreement["exact_rate"] - raw_ag["exact_rate"], 4),
                "cohens_kappa": round(agreement["cohens_kappa"] - raw_ag["cohens_kappa"], 4),
                "top2_overlap_rate": round(agreement["top2_overlap_rate"] - raw_ag["top2_overlap_rate"], 4),
                "mean_label_jaccard": round(agreement["mean_label_jaccard"] - raw_ag["mean_label_jaccard"], 4),
                "mean_confidence": round(b_mean_conf - r_mean_conf, 4),
                "other_mixed_pct": round(b_other_pct - r_other_pct, 2),
                "substantive_exact_rate": round(unf_sub["substantive_exact_rate"] - raw_sub["substantive_exact_rate"], 4),
                "substantive_top2_rate": round(unf_sub["substantive_top2_rate"] - raw_sub["substantive_top2_rate"], 4),
                "both_other_mixed_agree": unf_sub["both_other_mixed_agree"] - raw_sub["both_other_mixed_agree"],
            },
            "delta_unfolded_minus_phase3_baseline": {
                "exact_rate": round(agreement["exact_rate"] - 0.5417, 4),
                "cohens_kappa": round(agreement["cohens_kappa"] - 0.45, 4),
                "top2_overlap_rate": round(agreement["top2_overlap_rate"] - 0.7083, 4),
                "substantive_exact_rate": round(unf_sub["substantive_exact_rate"] - 0.5417, 4),
            },
            "by_cohort": cohort_deltas,
        }

    pack = annot.Pack()
    pack.add_layer(
        layer=layer_id,
        kind="ai-draft",
        title=AI_LAYER_TITLE,
        description=AI_LAYER_DESC,
        default_on=False,
    )

    pilot_rows: List[Dict[str, Any]] = []
    for cid in sorted(meta_map):
        if cid not in b_map:
            raise ValueError(f"Missing blinded label for cluster {cid}")
        cm = meta_map[cid]
        bl = b_map[cid]
        ul = u_map.get(cid)
        agrees = bool(ul is not None and bl["primary_domain"] == ul["primary_domain"])
        b_label = str(bl["short_label"]).strip()[:120]
        u_label = str(ul["short_label"]).strip()[:120] if ul else None
        conf = round(min(1.0, max(0.0, float(bl.get("confidence", 0.5)))), 3)
        ev_toks = [str(t) for t in bl.get("evidence_tokens", [])][:10]
        unc = str(bl.get("uncertainty_note", "")).strip()[:280]

        note_parts = [
            f"[AI-DRAFT name-blinded, cluster {cid}, domain={bl['primary_domain']}, conf={conf:.2f}] {b_label}.",
        ]
        if ev_toks:
            note_parts.append("Observed Mathlib/core tokens: " + ", ".join(ev_toks) + ".")
        if unc:
            note_parts.append("Uncertainty: " + unc)
        if ul is not None:
            note_parts.append(
                f"Blinded-vs-unblinded domain {'AGREES' if agrees else 'DISAGREES'} "
                f"(unblinded={ul['primary_domain']}: {u_label})."
            )
        note_text = " ".join(note_parts)[:annot.MAX_NOTE]

        rec = annot.make_annotation(
            target=str(cm["target_kind"]),
            name=str(cm["target_name"]),
            layer=layer_id,
            slot=f"tier3-{cid.lower()}",
            tag="M",
            source=f"leanre/flirt/tier3.py pilot ({cid}, blinded prompt sha256:{cm['prompt_sha256'][:16]})",
            author=ai_author,
            now=ts,
            rename=b_label,
            note=note_text,
            breaks=DEFAULT_BREAKS,
            draft=True,
            extra={
                "cluster_id": cid,
                "cohort": cm["cohort"],
                "blinded": True,
                "blinded_domain": bl["primary_domain"],
                "blinded_secondary_domain": bl.get("secondary_domain"),
                "unblinded_domain": ul["primary_domain"] if ul else None,
                "unblinded_label": u_label,
                "agrees": agrees,
                "confidence": conf,
                "member_count": cm["module_count"],
                "boundary_modules": cm["boundary_modules"],
                "prompt_sha256": cm["prompt_sha256"],
                "leak_test_passed": True,
            },
        )
        pack.put(rec)

        pilot_rows.append({
            "cluster_id": cid,
            "cohort": cm["cohort"],
            "target_kind": cm["target_kind"],
            "target_name": cm["target_name"],
            "label": b_label,
            "primary_domain": bl["primary_domain"],
            "secondary_domain": bl.get("secondary_domain"),
            "model": clean_model,
            "author": ai_author,
            "layer": layer_id,
            "blinded": True,
            "unblinded_label": u_label,
            "unblinded_domain": ul["primary_domain"] if ul else None,
            "agrees": agrees,
            "confidence": conf,
            "size": cm["module_count"],
            "members": cm["boundary_modules"],
            "declared_namespaces": cm.get("declared_namespaces", []),
            "evidence_tokens": ev_toks,
            "uncertainty_note": unc,
            "prompt_sha256": cm["prompt_sha256"],
            "provenance": "M",
            "draft": True,
            "breaks": DEFAULT_BREAKS,
        })

    # Hard Guardrail assertions before touching disk
    for lid, lrec in pack.layers.items():
        assert lrec["kind"] == "ai-draft" and lrec["default_on"] is False, f"unsafe layer {lid}"
    for r in pack.annots.values():
        assert r["tag"] == "M" and r["draft"] is True and r["author"].startswith("ai:"), f"unsafe record {r}"

    pack_text = annot.dumps(pack)
    issues = annot.validate_text(pack_text, canonical=True)
    if issues:
        raise annot.PackError(issues)

    if out_pack_path:
        os.makedirs(os.path.dirname(os.path.abspath(out_pack_path)), exist_ok=True)
        with open(out_pack_path, "w", encoding="utf-8", newline="\n") as f:
            f.write(pack_text)

    pilot_obj = {
        "schema": SCHEMA_VERSION,
        "provenance": "[M] Heuristic AI-draft labels (name-blinded headers + 1-2-hop unfolded Mathlib contract primitives; NEVER [L] facts)",
        "breaks": DEFAULT_BREAKS,
        "layer": layer_id,
        "layer_kind": "ai-draft",
        "default_on": False,
        "model": clean_model,
        "unfold_hops": manifest.get("unfold_hops", 0),
        "generated_at": ts,
        "allowlist_id": manifest.get("allowlist_id"),
        "lexicon_id": manifest.get("lexicon_id"),
        "leak_test": manifest.get("leak_test"),
        "agreement": agreement,
        "ab_unfolding_comparison": ab_comparison,
        "pack_file": os.path.relpath(out_pack_path, REPO) if out_pack_path and os.path.abspath(out_pack_path).startswith(REPO) else out_pack_path,
        "pack_sha256": hashlib.sha256(pack_text.encode("utf-8")).hexdigest(),
        "clusters": pilot_rows,
    }
    if out_pilot_json:
        os.makedirs(os.path.dirname(os.path.abspath(out_pilot_json)), exist_ok=True)
        with open(out_pilot_json, "w", encoding="utf-8") as f:
            json.dump(pilot_obj, f, indent=2, sort_keys=True, ensure_ascii=False)
            f.write("\n")

    return pack, pilot_obj


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def cmd_prepare(args: argparse.Namespace) -> int:
    os.makedirs(OUT_DIR, exist_ok=True)
    os.makedirs(CACHE_DIR, exist_ok=True)
    std_al = load_or_build_allowlist(args.allowlist, args.corpora_dir, workers=args.workers)
    if os.path.exists(args.lexicon):
        proj_lex = sighash.Lexicon.load(args.lexicon)
    else:
        proj_lex, _ = sighash.build_lexicon(args.src, workers=args.workers)
        proj_lex.save(args.lexicon)

    if args.mode == "phase4" and os.path.exists(args.clusters_json):
        specs = select_phase4_clusters(
            clusters_json=args.clusters_json,
            tier1_db=args.tier1_db,
            leanre_db=args.leanre_db,
            src_dir=args.src,
            target_count=args.target_count,
        )
    else:
        specs = select_pilot_clusters(args.tier1_db, args.leanre_db)

    t2_lib = _load_tier2_lib_tokens(os.path.join(OUT_DIR, "tier2.db"))
    unfolder: Optional[KernelTypeUnfolder] = None
    if args.unfold_hops > 0 and args.kernel_db and os.path.exists(args.kernel_db):
        unfolder = KernelTypeUnfolder(args.kernel_db, proj_lex, std_al, tier2_lib_tokens=t2_lib)

    blinded_records: List[Dict[str, Any]] = []
    blinded_raw_records: List[Dict[str, Any]] = []
    unblinded_records: List[Dict[str, Any]] = []
    metas: List[Dict[str, Any]] = []
    leak_reports: List[Dict[str, Any]] = []
    unfolded_nonempty = 0

    try:
        for sp in specs:
            extra_kd = sp.get("extra_kernel_decls") or ()
            b_rec, u_rec, meta = blind_cluster(
                cluster_id=sp["cluster_id"],
                cohort=sp["cohort"],
                target_kind=sp["target_kind"],
                target_name=sp["target_name"],
                boundary_modules=sp["boundary_modules"],
                total_cluster_modules=sp["total_modules"],
                src_dir=args.src,
                project_lexicon=proj_lex,
                std_allowlist=std_al,
                external_importers=sp["external_importers"],
                unfolder=unfolder,
                unfold_hops=args.unfold_hops,
                extra_kernel_decls=extra_kd,
            )
            rep = verify_no_leaks(b_rec, std_al, extra_forbidden=meta["all_forbidden_tokens"])
            leak_reports.append(rep)
            if not rep["passed"]:
                print(f"LEAK DETECTED in {sp['cluster_id']}: {rep['leaks'][:10]}", file=sys.stderr)
                return 2
            uctx = b_rec.get("unfolded_type_context") or {}
            if uctx.get("top_unfolded_mathlib"):
                unfolded_nonempty += 1
            blinded_records.append(b_rec)
            unblinded_records.append(u_rec)

            # Also emit 0-hop raw blinded companion for controlled A/B comparison
            if args.out_blinded_raw:
                b_raw, _, _ = blind_cluster(
                    cluster_id=sp["cluster_id"],
                    cohort=sp["cohort"],
                    target_kind=sp["target_kind"],
                    target_name=sp["target_name"],
                    boundary_modules=sp["boundary_modules"],
                    total_cluster_modules=sp["total_modules"],
                    src_dir=args.src,
                    project_lexicon=proj_lex,
                    std_allowlist=std_al,
                    external_importers=sp["external_importers"],
                    unfolder=None,
                    unfold_hops=0,
                )
                rep_raw = verify_no_leaks(b_raw, std_al, extra_forbidden=meta["all_forbidden_tokens"])
                if not rep_raw["passed"]:
                    print(f"RAW LEAK DETECTED in {sp['cluster_id']}: {rep_raw['leaks'][:10]}", file=sys.stderr)
                    return 2
                blinded_raw_records.append(b_raw)

            meta_slim = {k: v for k, v in meta.items() if k != "all_forbidden_tokens"}
            if sp.get("blueprint_cluster_id"):
                meta_slim["blueprint_cluster_id"] = sp["blueprint_cluster_id"]
            if sp.get("pillar"):
                meta_slim["pillar"] = sp["pillar"]
            metas.append(meta_slim)
    finally:
        if unfolder is not None:
            unfolder.close()

    with open(args.out_blinded, "w", encoding="utf-8", newline="\n") as f:
        for r in blinded_records:
            f.write(json.dumps(r, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n")
    if args.out_blinded_raw and blinded_raw_records:
        with open(args.out_blinded_raw, "w", encoding="utf-8", newline="\n") as f:
            for r in blinded_raw_records:
                f.write(json.dumps(r, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n")
    with open(args.out_unblinded, "w", encoding="utf-8", newline="\n") as f:
        for r in unblinded_records:
            f.write(json.dumps(r, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n")

    manifest = {
        "schema": SCHEMA_VERSION,
        "mode": args.mode,
        "unfold_hops": args.unfold_hops if unfolder is not None else 0,
        "clusters_with_unfolded_mathlib": unfolded_nonempty,
        "allowlist_id": std_al.id,
        "allowlist_tokens": len(std_al.tokens),
        "lexicon_id": proj_lex.id,
        "lexicon_names": len(proj_lex),
        "cluster_count": len(metas),
        "leak_test": {
            "all_passed": all(r["passed"] for r in leak_reports),
            "clusters_checked": len(leak_reports),
            "total_tokens_checked": sum(r["checked_tokens"] for r in leak_reports),
            "total_leaks": sum(len(r["leaks"]) for r in leak_reports),
        },
        "clusters": metas,
    }
    with open(args.out_manifest, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2, sort_keys=True, ensure_ascii=False)
        f.write("\n")

    print(
        f"[tier3] prepared {len(metas)} clusters (mode={args.mode}, unfold_hops={manifest['unfold_hops']}, "
        f"unfolded_nonempty={unfolded_nonempty}/{len(metas)}, allowlist={std_al.id}, lexicon={proj_lex.id}); "
        f"leak_test PASS ({manifest['leak_test']['total_tokens_checked']:,} tokens checked, 0 leaks)"
    )
    return 0


def cmd_leak_test(args: argparse.Namespace) -> int:
    std_al = load_or_build_allowlist(args.allowlist, args.corpora_dir, workers=args.workers)
    extra_forbidden: Set[str] = set()
    if args.manifest and os.path.exists(args.manifest):
        with open(args.manifest, encoding="utf-8") as f:
            man = json.load(f)
        for c in man.get("clusters", []):
            for seg in str(c.get("target_name", "")).split("."):
                if len(seg) >= 3:
                    extra_forbidden.add(seg)
            for m in c.get("boundary_modules", []):
                for seg in m.split("."):
                    if len(seg) >= 3:
                        extra_forbidden.add(seg)
    total_toks = 0
    total_leaks = 0
    n_recs = 0
    with open(args.blinded_jsonl, encoding="utf-8") as f:
        for line in f:
            if not line.strip():
                continue
            rec = json.loads(line)
            rep = verify_no_leaks(rec, std_al, extra_forbidden=extra_forbidden)
            n_recs += 1
            total_toks += rep["checked_tokens"]
            total_leaks += len(rep["leaks"])
            if not rep["passed"]:
                print(f"FAIL {rep['cluster_id']}: {rep['leaks'][:10]}", file=sys.stderr)
    print(f"[tier3] leak-test: records={n_recs} tokens_checked={total_toks} leaks={total_leaks} status={'PASS' if total_leaks == 0 else 'FAIL'}")
    return 0 if total_leaks == 0 else 2


def cmd_ingest(args: argparse.Namespace) -> int:
    with open(args.manifest, encoding="utf-8") as f:
        manifest = json.load(f)
    with open(args.blinded_labels, encoding="utf-8") as f:
        b_labels = json.load(f)
    with open(args.unblinded_labels, encoding="utf-8") as f:
        u_labels = json.load(f)
    r_labels = None
    if args.raw_blinded_labels and os.path.exists(args.raw_blinded_labels):
        with open(args.raw_blinded_labels, encoding="utf-8") as f:
            r_labels = json.load(f)
    pack, pilot = ingest_labels(
        manifest=manifest,
        blinded_labels=b_labels,
        unblinded_labels=u_labels,
        model_name=args.model,
        out_pack_path=args.out_pack,
        out_pilot_json=args.out_pilot,
        raw_blinded_labels=r_labels,
    )
    ag = pilot["agreement"]
    extra = ""
    if pilot.get("ab_unfolding_comparison"):
        d = pilot["ab_unfolding_comparison"]["delta_unfolded_minus_raw"]
        raw_r = pilot["ab_unfolding_comparison"]["raw_blinded_no_unfold"]
        extra = (
            f" | A/B raw={raw_r['agree']}/{raw_r['of']} ({raw_r['exact_rate']:.1%}, kappa={raw_r['cohens_kappa']:.3f}) "
            f"-> unfolded delta={d['exact_rate']:+.1%} (kappa {d['cohens_kappa']:+.3f})"
        )
    print(
        f"[tier3] ingested {len(pack)} AI-draft annotations into {args.out_pack} "
        f"(layer={pilot['layer']}, default_on={pilot['default_on']}); "
        f"blinded-vs-unblinded exact={ag['agree']}/{ag['of']} ({ag['exact_rate']:.1%}), "
        f"kappa={ag['cohens_kappa']:.3f}, top2={ag['top2_overlap_rate']:.1%}{extra}"
    )
    return 0


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="FLIRT Tier 3: name-blinded AI labeling on cluster boundaries")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_prep = sub.add_parser("prepare", help="Generate blinded + unblinded prompt packs and run leak test")
    p_prep.add_argument("--mode", choices=["phase4", "pilot24"], default="phase4")
    p_prep.add_argument("--target-count", type=int, default=100)
    p_prep.add_argument("--unfold-hops", type=int, default=2, help="0=no unfolding, 1-2=kernel contract type unfolding")
    p_prep.add_argument("--src", default=DEFAULT_SRC)
    p_prep.add_argument("--tier1-db", default=DEFAULT_TIER1_DB)
    p_prep.add_argument("--leanre-db", default=DEFAULT_LEANRE_DB)
    p_prep.add_argument("--kernel-db", default=DEFAULT_KERNEL_DB)
    p_prep.add_argument("--clusters-json", default=DEFAULT_CLUSTERS_JSON)
    p_prep.add_argument("--lexicon", default=DEFAULT_LEXICON)
    p_prep.add_argument("--allowlist", default=DEFAULT_ALLOWLIST)
    p_prep.add_argument("--corpora-dir", default=CORPORA_DIR)
    p_prep.add_argument("--out-blinded", default=DEFAULT_BLINDED)
    p_prep.add_argument("--out-blinded-raw", default=DEFAULT_BLINDED_RAW)
    p_prep.add_argument("--out-unblinded", default=DEFAULT_UNBLINDED)
    p_prep.add_argument("--out-manifest", default=DEFAULT_MANIFEST)
    p_prep.add_argument("--workers", type=int, default=16)

    p_lk = sub.add_parser("leak-test", help="Verify zero project names survive in a blinded prompt pack")
    p_lk.add_argument("blinded_jsonl")
    p_lk.add_argument("--manifest", default=DEFAULT_MANIFEST)
    p_lk.add_argument("--allowlist", default=DEFAULT_ALLOWLIST)
    p_lk.add_argument("--corpora-dir", default=CORPORA_DIR)
    p_lk.add_argument("--workers", type=int, default=16)

    p_in = sub.add_parser("ingest", help="Ingest blinded + unblinded labels into an AI-draft pack + pilot JSON")
    p_in.add_argument("--manifest", default=DEFAULT_MANIFEST)
    p_in.add_argument("--blinded-labels", required=True)
    p_in.add_argument("--unblinded-labels", required=True)
    p_in.add_argument("--raw-blinded-labels", default=None, help="Optional 0-hop raw blinded labels for A/B comparison")
    p_in.add_argument("--model", required=True)
    p_in.add_argument("--out-pack", default=DEFAULT_PACK)
    p_in.add_argument("--out-pilot", default=DEFAULT_PILOT_JSON)

    a = ap.parse_args(argv)
    if a.cmd == "prepare":
        return cmd_prepare(a)
    if a.cmd == "leak-test":
        return cmd_leak_test(a)
    if a.cmd == "ingest":
        return cmd_ingest(a)
    return 1


if __name__ == "__main__":
    sys.exit(main())
