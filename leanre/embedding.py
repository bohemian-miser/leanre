#!/usr/bin/env python3
"""leanre.embedding -- 2D TF-IDF + Randomized SVD + k-NN UMAP-style Proof Map.

Builds an interactive two-granularity 2D embedding over read-only `kernel.db`
(and optional `leanre.db`, `cluster_labels_141.json`, `portability_gems.json`):

  1. `clusters_141`: Dominator-frontier blueprint clusters (`~141` on RH, or
     adaptive subtree/namespace clusters on smaller/synthetic corpora),
     represented by TF-IDF vectors of outgoing library/core constants.
  2. `landmarks`: Up to `~1,800` live named declarations (ALL `dom >= 1,000`
     hubs, cluster roots, portability targets, top `structure`/`class` hubs,
     and high-centrality project declarations), represented by bounded multi-hop
     TF-IDF bags of outgoing library/core dependencies plus structural type
     features (`kind`, `log1p(dom)`, `log1p(type_nodes)`, `log1p(value_nodes)`,
     `type_ratio = E_T / (E_T + E_V)`).

Both layers run:
  - Truncated randomized SVD (`k = 24`) on L2-normalized feature vectors.
  - `pca2`: Isotropic linear projection onto top-2 singular coordinates in `[-1, 1]`.
  - `knn2`: Deterministic (`seed = 42`) 180-step UMAP-style 2D attraction-repulsion
    graph embedding over `k = 15` cosine neighbors in the 24-dim SVD space.
  - Real `15`-NN preservation, trustworthiness `T(15)`, and `10`-NN namespace-drift
    metrics across source directories.

Guardrails:
  - Generic Python 3.11+ + `numpy` (no `scikit-learn` / `umap-learn` / `scipy`).
  - Strictly read-only SQLite access (`mode=ro` + `PRAGMA query_only=1`).
  - Zero `.lean` proof bodies and zero workstation absolute paths in outputs.
"""
from __future__ import annotations

import argparse
import array
import collections
import contextlib
import json
import math
import multiprocessing as mp
import os
import random
import re
import sqlite3
import sys
import tempfile
import time
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

try:
    import numpy as np  # type: ignore[import-not-found]
except ImportError:  # pragma: no cover
    np = None  # type: ignore[assignment]

try:
    from leanre import atlas  # type: ignore[import-not-found]
    from leanre import graph as _graph  # type: ignore[import-not-found]
except ImportError:  # pragma: no cover
    import atlas  # type: ignore[no-redef]
    import graph as _graph  # type: ignore[no-redef]

SCHEMA_VERSION = "leanre.embedding_2d/1"

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))

DEFAULT_KERNEL_DB = "outputs/kernel/kernel.db"
DEFAULT_LEANRE_DB = "outputs/leanre.db"
DEFAULT_CLUSTER_LABELS = "outputs/flirt/cluster_labels_141.json"
DEFAULT_PORTABILITY = "outputs/portability_gems.json"
DEFAULT_OUT_JSON = "outputs/embedding_2d.json"

HYGIENE_FLAGS: Tuple[str, ...] = ("clean", "decide_kernel", "alias_vn1", "high_drift")
SOURCE_KINDS: Tuple[str, ...] = ("root", "core", "leaf", "challenge", "orphan")
SOURCE_STATUSES: Tuple[str, ...] = (
    "clean",
    "challenge_sorry",
    "proof_sorry",
    "axiom",
    "decide_kernel",
    "unreached",
)

# Compiler-generated auxiliary declarations (keep `_private.` user decls!)
_COMPILER_AUX_RE = re.compile(
    r"(?:\._proof_|\._simp_|\._eq_|\._congr_|\._unfold|\._sunfold"
    r"|\._cstage|\._hyg|\.match_\d+|\._unary|\._mutual|\._lambda_"
    r"|\._abel_|\._ring_|\._omega_|\._linarith_|\._norm_num_|\._positivity_|\._gcongr_|\._decide_)"
)

# Concrete Mathlib/Lean typeclass-instance and parent-coercion boilerplate
_TC_BOILERPLATE_RE = re.compile(
    r"(?:^|\.)(?:inst[A-Z0-9_]|to[A-Z]|"
    r"(?:partialOrder|linearOrder|preorder|lattice|completeLattice|"
    r"semiring|commSemiring|ring|commRing|field|divisionRing|semifield|nonUnital\w+|"
    r"addCommGroup|addGroup|addCommMonoid|addMonoid|addZeroClass|commGroup|group|commMonoid|monoid|"
    r"fintype|finite|decidableEq|decidablePred|decidableRel|decidable|"
    r"setLike|funLike|coeFun|inhabited|nonempty|nontrivial|charZero|neZero|"
    r"topologicalSpace|metricSpace|emetricSpace|uniformSpace|measurableSpace|"
    r"normedSpace|normedField|commNormedRing|normedRing|normedAddCommGroup|innerProductSpace|completeSpace|"
    r"module|algebra|leftModule|rightModule|distribMulAction|mulAction|smulWithZero|"
    r"hasQuotient|subsingleton|unique|ordered\w+|strictOrdered\w+|canonicallyOrdered\w+|"
    r"zero|one|add|mul|sub|div|neg|inv|pow|smul|le|lt|bot|top|sup|inf)(?:_[0-9]+)?$)"
)

# Ubiquitous Lean kernel / algebraic coercion primitives excluded from TF-IDF vocabulary
_STOP_EXACT = frozenset({
    "Eq", "Eq.refl", "Eq.ndrec", "Eq.mpr", "Eq.mp", "Eq.symm", "Eq.trans",
    "Eq.casesOn", "Eq.rec", "Eq.recOn", "of_eq_true", "eq_self", "rfl",
    "HEq", "HEq.refl", "HEq.symm", "HEq.trans",
    "True", "True.intro", "False", "False.elim", "absurd",
    "And", "And.intro", "And.left", "And.right", "And.casesOn",
    "Or", "Or.inl", "Or.inr", "Or.elim", "Or.casesOn",
    "Not", "Ne", "Iff", "Iff.intro", "Iff.mp", "Iff.mpr",
    "Exists", "Exists.intro", "Exists.elim", "Exists.casesOn",
    "Prop", "Sort", "Type", "Nat", "Nat.zero", "Nat.succ", "Nat.cast",
    "Int.cast", "Rat.cast",
    "Bool", "Bool.true", "Bool.false",
    "PUnit", "PUnit.unit", "Unit", "Unit.unit",
    "OfNat.ofNat", "Zero.zero", "One.one",
    "id", "Function.comp", "congr", "congrArg", "congrFun", "congrFun'", "funext", "propext",
    "Classical.choice", "Classical.propDecidable", "Classical.em",
    "Classical.dec", "Classical.decEq", "Classical.decPred", "Decidable.decide", "Quot.sound",
    "Membership.mem", "DFunLike.coe", "AutoParam", "optParam", "outParam",
    "Subtype", "Subtype.mk", "Subtype.val", "Sigma", "Sigma.mk", "Sigma.fst", "Sigma.snd",
    "Prod", "Prod.mk", "Prod.fst", "Prod.snd", "ite", "dite", "cond",
    "decide", "of_decide_eq_true", "Lean.ofReduceBool",
    "CommSemiring.toSemiring", "Semiring.toNonAssocSemiring", "CommRing.toCommSemiring",
    "Ring.toSemiring", "AddCommMonoid.toAddMonoid", "AddCommGroup.toAddCommMonoid",
    "CommMonoid.toMonoid", "CommGroup.toGroup", "Field.toCommRing",
    "Algebra.id", "RingHom.id", "MonoidHom.id", "LinearMap.id",
    "HMul.hMul", "HAdd.hAdd", "HSub.hSub", "HDiv.hDiv", "HPow.hPow", "HSMul.hSMul",
    "Neg.neg", "Inv.inv", "LE.le", "LT.lt", "GE.ge", "GT.gt",
    "Coe.coe", "CoeTC.coe", "CoeT.coe", "CoeHTCT.coe",
})

# Pillar palette (distinct high-contrast dark-mode RGB colors)
_PILLAR_RGB: Dict[str, Tuple[int, int, int]] = {
    "A": (56, 189, 248),     # cyan-sky (Theta / Local Matching)
    "B": (251, 146, 60),     # orange (Galois Local-Global)
    "C": (192, 132, 252),    # violet (Automorphic Window)
    "D": (244, 63, 94),      # rose-crimson (Arakelov Covolume)
    "DM": (52, 211, 153),    # emerald (Shared Diamond)
    "LIT": (250, 204, 21),   # gold (Literature / Spine)
    "BR": (148, 163, 184),   # slate (Bridge & External Roots)
    "MAIN": (56, 189, 248),
    "LIB": (148, 163, 184),
}

_PILLAR_ROOT_NAMES: Dict[str, str] = {
    "UpperTheory.Lit.every_character_of_theta_integrals_local_matching": "pillar_theta",
    "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter": "pillar_galois",
    "UpperTheory.One.vwin_of_row": "pillar_window",
    "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin": "pillar_volume_lit",
    "allChi": "shared_diamond",
}


def is_compiler_aux(name: str) -> bool:
    """Return True for compiler/tactic auxiliary decls (keeps `_private.` user decls)."""
    return bool(_COMPILER_AUX_RE.search(name))


def is_typeclass_boilerplate(name: str, kind: str = "def") -> bool:
    """Return True for concrete Mathlib/Lean typeclass instances & coercion projections."""
    if name in _STOP_EXACT:
        return True
    if ".Internal." in name or name.endswith(".Internal"):
        return True
    # In Lean 4, `Prop`-valued typeclass instances have kernel kind `thm` while data classes have `def`.
    if kind != "inductive":
        if ".inst" in name or _TC_BOILERPLATE_RE.search(name):
            return True
    return False


def _strip_cluster_tag(label: str) -> str:
    """Strip internal `[M] ` / `[K] ` / `[L] ` tags from display cluster labels."""
    return re.sub(r"^\[[A-Z]+\]\s*", "", str(label or "")).strip()


def short_decl_name(name: str) -> str:
    """Extract a readable short leaf name for UI labels."""
    clean = name[7:] if name.startswith("_root_.") else name
    if clean.startswith("_private.") and ".0." in clean:
        clean = clean.split(".0.", 1)[1]
    parts = clean.split(".")
    if len(parts) >= 2 and parts[-1] in ("mk", "rec", "recOn", "casesOn", "toFun", "inj", "ext", "0"):
        return ".".join(parts[-2:])
    return parts[-1]


def dir_top_from_module(name: str, module: Optional[str]) -> str:
    """Return normalized top-2 directory/module prefix (`dir_top`)."""
    if module:
        parts = module.split(".")
        return ".".join(parts[:2]) if len(parts) >= 2 else parts[0]
    clean = name[7:] if name.startswith("_root_.") else name
    if clean.startswith("_private."):
        rest = clean[len("_private.") :]
        if ".0." in rest:
            mod_part = rest.split(".0.", 1)[0]
            parts = mod_part.split(".")
            return ".".join(parts[:2]) if len(parts) >= 2 else parts[0]
    return atlas.top_namespace(clean, parts_keep=2)


def _pillar_code_for_region(region_key: str, decl_name: str = "") -> str:
    """Map an `atlas` DFS region key to a short pillar code (`A`/`B`/`C`/`D`/`DM`/`BR`/`LIT`)."""
    if region_key == "pillar_a":
        return "A"
    if region_key == "pillar_b":
        return "B"
    if region_key == "pillar_c":
        return "C"
    if region_key == "pillar_d":
        return "D"
    if region_key == "shared_diamond":
        return "DM"
    if region_key == "bridge":
        return "BR"
    if region_key == "spine_0":
        if decl_name in ("allChi", "UpperTheory.FinalTheorems.everyCharacter", "UpperTheory.FinalTheorems.everyCharacter_of_row"):
            return "DM"
        return "LIT"
    if region_key.startswith(("spine_", "tail_")):
        return "LIT"
    if region_key.startswith("q"):
        return region_key.upper()
    return "MAIN"


# ---------------------------------------------------------------------------
# Truncated Randomized SVD, k-NN UMAP-style Projection & Evaluation Metrics
# ---------------------------------------------------------------------------

def _as_py_rows(M: Any) -> List[List[float]]:
    if np is not None and isinstance(M, np.ndarray):
        return [[float(x) for x in row] for row in M.tolist()]
    return [[float(x) for x in row] for row in M]


def _py_svd_top_k(rows: List[List[float]], k: int, seed: int = 42, n_iter: int = 5) -> Tuple[List[List[float]], List[float], List[List[float]]]:
    """Deterministic pure-stdlib truncated SVD via subspace iteration."""
    n = len(rows)
    d = len(rows[0]) if n > 0 else 0
    k_eff = min(int(k), n, d)
    if k_eff <= 0 or n == 0 or d == 0:
        return ([[] for _ in range(n)], [], [[] for _ in range(0)])

    rng = random.Random(seed)
    # Orthonormalize `k_eff` columns in R^d via modified Gram-Schmidt
    basis: List[List[float]] = []
    for col_i in range(k_eff):
        v = [rng.gauss(0.0, 1.0) for _ in range(d)]
        for prev in basis:
            dot = sum(a * b for a, b in zip(v, prev))
            v = [a - dot * b for a, b in zip(v, prev)]
        norm = math.sqrt(sum(x * x for x in v))
        if norm < 1e-12:
            v = [1.0 if j == (col_i % d) else 0.0 for j in range(d)]
            for prev in basis:
                dot = sum(a * b for a, b in zip(v, prev))
                v = [a - dot * b for a, b in zip(v, prev)]
            norm = max(1e-12, math.sqrt(sum(x * x for x in v)))
        basis.append([x / norm for x in v])

    for _ in range(max(4, n_iter)):
        # Y = X @ V^T  (n x k_eff), then Z = X^T @ Y (d x k_eff)
        Y_cols: List[List[float]] = []
        for b in basis:
            Y_cols.append([sum(row[j] * b[j] for j in range(d)) for row in rows])
        new_basis: List[List[float]] = []
        for col_i in range(k_eff):
            y_col = Y_cols[col_i]
            z = [0.0] * d
            for i in range(n):
                yi = y_col[i]
                if yi != 0.0:
                    row = rows[i]
                    for j in range(d):
                        z[j] += row[j] * yi
            for prev in new_basis:
                dot = sum(a * b for a, b in zip(z, prev))
                z = [a - dot * b for a, b in zip(z, prev)]
            norm = math.sqrt(sum(x * x for x in z))
            if norm < 1e-12:
                z = list(basis[col_i])
                for prev in new_basis:
                    dot = sum(a * b for a, b in zip(z, prev))
                    z = [a - dot * b for a, b in zip(z, prev)]
                norm = max(1e-12, math.sqrt(sum(x * x for x in z)))
            new_basis.append([x / norm for x in z])
        basis = new_basis

    U_cols: List[List[float]] = []
    S_vals: List[float] = []
    Vt_rows: List[List[float]] = []
    for b in basis:
        u_col = [sum(row[j] * b[j] for j in range(d)) for row in rows]
        sv = math.sqrt(sum(x * x for x in u_col))
        if sv > 1e-12:
            u_norm = [x / sv for x in u_col]
        else:
            u_norm = [0.0] * n
        # Deterministic column sign
        max_i = max(range(n), key=lambda idx: abs(u_norm[idx])) if n > 0 else 0
        if n > 0 and u_norm[max_i] < 0.0:
            u_norm = [-x for x in u_norm]
            b = [-x for x in b]
        U_cols.append(u_norm)
        S_vals.append(sv)
        Vt_rows.append(b)

    # Sort descending by singular value
    order = sorted(range(k_eff), key=lambda j: -S_vals[j])
    S_sorted = [S_vals[j] for j in order]
    Vt_sorted = [Vt_rows[j] for j in order]
    U_rows = [[U_cols[j][i] for j in order] for i in range(n)]
    return U_rows, S_sorted, Vt_sorted


def randomized_svd(
    X: Any,
    k: int = 24,
    seed: int = 42,
    n_iter: int = 5,
) -> Tuple[Any, Any, Any]:
    """Compute deterministic truncated randomized SVD (`U, S, Vt`) with pure-stdlib fallback."""
    if np is None:
        rows = _as_py_rows(X)
        return _py_svd_top_k(rows, k=k, seed=seed, n_iter=n_iter)

    X64 = np.asarray(X, dtype=np.float64)
    n, d = X64.shape
    k_eff = min(int(k), n, d)
    if k_eff <= 0 or n == 0 or d == 0:
        return (
            np.zeros((n, 0), dtype=np.float64),
            np.zeros((0,), dtype=np.float64),
            np.zeros((0, d), dtype=np.float64),
        )

    # Use exact SVD directly when matrix is tiny (fast and zero stochastic error)
    if min(n, d) <= max(64, k_eff + 8):
        U, S, Vt = np.linalg.svd(X64, full_matrices=False)
        U = U[:, :k_eff].copy()
        S = S[:k_eff].copy()
        Vt = Vt[:k_eff, :].copy()
    else:
        rng = np.random.default_rng(seed)
        oversample = min(12, min(n, d) - k_eff)
        q_dim = k_eff + oversample
        omega = rng.standard_normal((d, q_dim))
        Y = X64 @ omega
        for _ in range(n_iter):
            Q, _ = np.linalg.qr(Y, mode="reduced")
            Z, _ = np.linalg.qr(X64.T @ Q, mode="reduced")
            Y = X64 @ Z
        Q, _ = np.linalg.qr(Y, mode="reduced")
        B = Q.T @ X64
        Ub, S_all, Vt_all = np.linalg.svd(B, full_matrices=False)
        U = (Q @ Ub)[:, :k_eff].copy()
        S = S_all[:k_eff].copy()
        Vt = Vt_all[:k_eff, :].copy()

    # Deterministic column sign convention
    for j in range(k_eff):
        col = U[:, j]
        idx = int(np.argmax(np.abs(col)))
        if col[idx] < 0.0:
            U[:, j] = -col
            Vt[j, :] = -Vt[j, :]
    return U, S, Vt


def normalize_2d_isotropic(coords: Any) -> Any:
    """Isotropically scale 2D coordinates into `[-1, 1]^2` preserving aspect & Euclidean metric."""
    if np is None:
        rows = _as_py_rows(coords)
        n = len(rows)
        if n == 0:
            return []
        c = [([r[0], 0.0] if len(r) == 1 else ([0.0, 0.0] if len(r) == 0 else [r[0], r[1]])) for r in rows]
        min0 = min(r[0] for r in c)
        max0 = max(r[0] for r in c)
        min1 = min(r[1] for r in c)
        max1 = max(r[1] for r in c)
        mid0 = 0.5 * (min0 + max0)
        mid1 = 0.5 * (min1 + max1)
        half_span = max(1e-9, 0.5 * max(max0 - min0, max1 - min1))
        return [
            [max(-1.0, min(1.0, (r[0] - mid0) / half_span)), max(-1.0, min(1.0, (r[1] - mid1) / half_span))]
            for r in c
        ]

    n = coords.shape[0]
    if n == 0:
        return np.zeros((0, 2), dtype=np.float64)
    c = np.asarray(coords, dtype=np.float64)
    if c.shape[1] == 1:
        c = np.hstack([c, np.zeros((n, 1), dtype=np.float64)])
    elif c.shape[1] == 0:
        return np.zeros((n, 2), dtype=np.float64)
    mins = c.min(axis=0)
    maxs = c.max(axis=0)
    mid = 0.5 * (mins + maxs)
    half_span = float(max(1e-9, 0.5 * float(np.max(maxs - mins))))
    out = (c - mid[None, :]) / half_span
    return np.clip(out, -1.0, 1.0)


def compute_cosine_knn(Z: Any, k_nn: int = 15) -> Tuple[Any, Any]:
    """Compute exact top-`k_nn` cosine neighbors `(nn_idx, nn_sim)` in high-dim SVD space."""
    if np is None:
        rows = _as_py_rows(Z)
        n = len(rows)
        if n <= 1:
            return [[] for _ in range(n)], [[] for _ in range(n)]
        k_eff = min(int(k_nn), n - 1)
        zn = []
        for r in rows:
            nr = max(1e-12, math.sqrt(sum(x * x for x in r)))
            zn.append([x / nr for x in r])
        nn_idx_py: List[List[int]] = []
        nn_sim_py: List[List[float]] = []
        for i in range(n):
            zi = zn[i]
            sims = []
            for j in range(n):
                if j == i:
                    continue
                s = max(-1.0, min(1.0, sum(a * b for a, b in zip(zi, zn[j]))))
                sims.append((-s, j, s))
            sims.sort()
            top = sims[:k_eff]
            nn_idx_py.append([t[1] for t in top])
            nn_sim_py.append([t[2] for t in top])
        return nn_idx_py, nn_sim_py

    n = Z.shape[0]
    if n <= 1:
        return np.zeros((n, 0), dtype=np.int32), np.zeros((n, 0), dtype=np.float64)
    k_eff = min(int(k_nn), n - 1)
    Z64 = np.asarray(Z, dtype=np.float64)
    norms = np.linalg.norm(Z64, axis=1, keepdims=True)
    Zn = Z64 / np.maximum(norms, 1e-12)
    sim = np.clip(Zn @ Zn.T, -1.0, 1.0)
    np.fill_diagonal(sim, -2.0)

    if k_eff == n - 1:
        nn_idx = np.argsort(-sim, axis=1)[:, :k_eff]
        rows = np.arange(n)[:, None]
        nn_sim = sim[rows, nn_idx]
        return nn_idx.astype(np.int32), nn_sim

    nn_idx = np.argpartition(-sim, kth=k_eff - 1, axis=1)[:, :k_eff]
    rows = np.arange(n)[:, None]
    nn_sim = sim[rows, nn_idx]
    order = np.argsort(-nn_sim, axis=1)
    nn_idx = nn_idx[rows, order]
    nn_sim = nn_sim[rows, order]
    return nn_idx.astype(np.int32), nn_sim


def _knn2_umap_with_sim(
    Z_svd: Any,
    pca2: Any,
    k_nn: int = 15,
    n_steps: int = 180,
    seed: int = 42,
    a: float = 1.6,
    b: float = 0.9,
    n_neg: int = 16,
    rep_scale: float = 0.25,
    alpha0: float = 1.4,
) -> Tuple[Any, Any, Any]:
    """Internal UMAP-style layout returning `(Y2, nn_idx, nn_sim)` (with stdlib fallback)."""
    if np is None:
        z_rows = _as_py_rows(Z_svd)
        n = len(z_rows)
        nn_idx, nn_sim = compute_cosine_knn(z_rows, k_nn=k_nn)
        if n <= 2:
            return normalize_2d_isotropic(pca2), nn_idx, nn_sim
        p_rows = _as_py_rows(pca2)
        Y = [([r[0], 0.0] if len(r) < 2 else [r[0], r[1]]) for r in p_rows]
        m0 = sum(r[0] for r in Y) / n
        m1 = sum(r[1] for r in Y) / n
        Y = [[r[0] - m0, r[1] - m1] for r in Y]
        sd = math.sqrt(sum(r[0] * r[0] + r[1] * r[1] for r in Y) / (2 * n))
        rng = random.Random(seed)
        if sd > 1e-12:
            Y = [[r[0] / sd, r[1] / sd] for r in Y]
        else:
            Y = [[rng.gauss(0.0, 0.5), rng.gauss(0.0, 0.5)] for _ in range(n)]
        edge_w: Dict[Tuple[int, int], float] = {}
        for i in range(n):
            k_eff = len(nn_idx[i])
            if k_eff == 0:
                continue
            dists = [math.sqrt(max(0.0, 2.0 * (1.0 - nn_sim[i][pos]))) for pos in range(k_eff)]
            rho = dists[0]
            sigma = max(1e-3, sum(d - rho for d in dists) / k_eff)
            for pos in range(k_eff):
                j = nn_idx[i][pos]
                w_ij = math.exp(-max(0.0, dists[pos] - rho) / sigma)
                key = (i, j) if i < j else (j, i)
                prev = edge_w.get(key)
                edge_w[key] = w_ij if prev is None else (prev + w_ij - prev * w_ij)
        edges_list = [(u, v, w) for (u, v), w in edge_w.items()]
        n_neg_eff = min(int(n_neg), max(1, n - 1))
        for step in range(n_steps):
            lr = alpha0 * (1.0 - step / float(max(1, n_steps)))
            grad = [[0.0, 0.0] for _ in range(n)]
            for u, v, w in edges_list:
                dx = Y[u][0] - Y[v][0]
                dy = Y[u][1] - Y[v][1]
                d2 = dx * dx + dy * dy + 1e-6
                db = d2 ** b
                ca = (-2.0 * a * b * (d2 ** (b - 1.0)) / (1.0 + a * db)) * w
                grad[u][0] += ca * dx
                grad[u][1] += ca * dy
                grad[v][0] -= ca * dx
                grad[v][1] -= ca * dy
            for u in range(n):
                for _ in range(n_neg_eff):
                    v = rng.randrange(0, n)
                    if v == u:
                        v = (v + 1) % n
                    dx = Y[u][0] - Y[v][0]
                    dy = Y[u][1] - Y[v][1]
                    d2 = dx * dx + dy * dy + 1e-4
                    cr = (2.0 * b / ((0.03 + d2) * (1.0 + a * (d2 ** b)))) * rep_scale
                    grad[u][0] += cr * dx
                    grad[u][1] += cr * dy
            for i in range(n):
                gn = math.hypot(grad[i][0], grad[i][1])
                sc = min(1.0, 4.0 / max(gn, 1e-12))
                Y[i][0] += lr * grad[i][0] * sc
                Y[i][1] += lr * grad[i][1] * sc
            m0 = sum(r[0] for r in Y) / n
            m1 = sum(r[1] for r in Y) / n
            for i in range(n):
                Y[i][0] -= m0
                Y[i][1] -= m1
        return normalize_2d_isotropic(Y), nn_idx, nn_sim

    n = Z_svd.shape[0]
    if n <= 2:
        nn_idx, nn_sim = compute_cosine_knn(Z_svd, k_nn=k_nn)
        return normalize_2d_isotropic(pca2), nn_idx, nn_sim

    nn_idx, nn_sim = compute_cosine_knn(Z_svd, k_nn=k_nn)
    k_eff = nn_idx.shape[1]

    # Fuzzy simplicial directed probabilities -> symmetric edge weights
    dists = np.sqrt(np.maximum(0.0, 2.0 * (1.0 - nn_sim)))
    rho = dists[:, 0:1]
    sigma = np.maximum(1e-3, np.mean(dists - rho, axis=1, keepdims=True))
    p_cond = np.exp(-np.maximum(0.0, dists - rho) / sigma)

    edge_w = {}
    for i in range(n):
        for pos in range(k_eff):
            j = int(nn_idx[i, pos])
            w_ij = float(p_cond[i, pos])
            key = (i, j) if i < j else (j, i)
            prev = edge_w.get(key)
            if prev is None:
                edge_w[key] = w_ij
            else:
                edge_w[key] = prev + w_ij - prev * w_ij

    u_arr = np.fromiter((k[0] for k in edge_w), dtype=np.int32, count=len(edge_w))
    v_arr = np.fromiter((k[1] for k in edge_w), dtype=np.int32, count=len(edge_w))
    w_arr = np.fromiter(edge_w.values(), dtype=np.float64, count=len(edge_w))

    # Initialize from spectral pca2 coordinates
    Y = np.asarray(pca2, dtype=np.float64).copy()
    if Y.shape[1] < 2:
        Y = np.hstack([Y, np.zeros((n, 2 - Y.shape[1]), dtype=np.float64)])
    Y -= Y.mean(axis=0, keepdims=True)
    sd = float(np.std(Y))
    if sd > 1e-12:
        Y /= sd
    else:
        rng_init = np.random.default_rng(seed)
        Y = rng_init.normal(0.0, 0.5, size=(n, 2))

    rng = np.random.default_rng(seed)
    n_neg_eff = min(int(n_neg), max(1, n - 1))

    for step in range(n_steps):
        lr = alpha0 * (1.0 - step / float(max(1, n_steps)))
        grad = np.zeros_like(Y)

        # Attractive force along k-NN edges
        diff = Y[u_arr] - Y[v_arr]
        d2 = np.sum(diff * diff, axis=1) + 1e-6
        db = d2 ** b
        coeff_a = (-2.0 * a * b * (d2 ** (b - 1.0)) / (1.0 + a * db)) * w_arr
        f_a = coeff_a[:, None] * diff
        np.add.at(grad, u_arr, f_a)
        np.add.at(grad, v_arr, -f_a)

        # Repulsive force on deterministically sampled negative pairs
        neg_u = np.repeat(np.arange(n, dtype=np.int32), n_neg_eff)
        neg_v = rng.integers(0, n, size=n * n_neg_eff, dtype=np.int32)
        same = neg_v == neg_u
        if np.any(same):
            neg_v[same] = (neg_v[same] + 1) % n
        diff_n = Y[neg_u] - Y[neg_v]
        d2_n = np.sum(diff_n * diff_n, axis=1) + 1e-4
        db_n = d2_n ** b
        coeff_r = (2.0 * b / ((0.03 + d2_n) * (1.0 + a * db_n))) * rep_scale
        f_r = coeff_r[:, None] * diff_n
        np.add.at(grad, neg_u, f_r)

        gnorm = np.linalg.norm(grad, axis=1, keepdims=True)
        clip = np.minimum(1.0, 4.0 / np.maximum(gnorm, 1e-12))
        Y += lr * grad * clip
        Y -= Y.mean(axis=0, keepdims=True)

    return normalize_2d_isotropic(Y), nn_idx, nn_sim


def knn2_umap_embedding(
    Z_svd: Any,
    pca2: Any,
    k_nn: int = 15,
    n_steps: int = 180,
    seed: int = 42,
    a: float = 1.6,
    b: float = 0.9,
    n_neg: int = 16,
    rep_scale: float = 0.25,
    alpha0: float = 1.4,
) -> Tuple[Any, Any]:
    """Run deterministic vectorized UMAP-style 2D k-NN attraction-repulsion embedding."""
    Y, nn_idx, _ = _knn2_umap_with_sim(
        Z_svd, pca2, k_nn=k_nn, n_steps=n_steps, seed=seed, a=a, b=b,
        n_neg=n_neg, rep_scale=rep_scale, alpha0=alpha0,
    )
    return Y, nn_idx


def evaluate_embedding_quality(
    Z_svd: Any,
    Y2: Any,
    nn_hi: Any,
) -> Dict[str, float]:
    """Measure exact `k`-NN neighborhood preservation and trustworthiness `T(k)`."""
    if np is None:
        z_rows = _as_py_rows(Z_svd)
        y_rows = _as_py_rows(Y2)
        n = len(z_rows)
        k = len(nn_hi[0]) if n > 0 else 0
        if n <= 2 or k <= 0:
            return {"knn_preservation": 1.0, "trustworthiness": 1.0}
        nn_lo: List[List[int]] = []
        for i in range(n):
            xi, yi = y_rows[i][0], y_rows[i][1]
            dists = sorted(
                ((xi - y_rows[j][0]) ** 2 + (yi - y_rows[j][1]) ** 2, j)
                for j in range(n) if j != i
            )
            nn_lo.append([t[1] for t in dists[:k]])
        overlap_sum = sum(len(set(nn_hi[i]) & set(nn_lo[i])) / float(k) for i in range(n))
        knn_pres = overlap_sum / float(n)
        denom = n * k * (2 * n - 3 * k - 1)
        if denom <= 0:
            trust = 1.0
        else:
            zn = []
            for r in z_rows:
                nr = max(1e-12, math.sqrt(sum(x * x for x in r)))
                zn.append([x / nr for x in r])
            t_sum = 0.0
            for i in range(n):
                s_hi = set(nn_hi[i])
                zi = zn[i]
                sims = sorted(
                    (-sum(a * b for a, b in zip(zi, zn[j])), j)
                    for j in range(n)
                )
                rank_of = {j: r_idx for r_idx, (_, j) in enumerate(sims)}
                for j_i in nn_lo[i]:
                    if j_i not in s_hi:
                        t_sum += max(0, rank_of[j_i] - k)
            trust = max(0.0, min(1.0, 1.0 - (2.0 * t_sum / float(denom))))
        return {
            "knn_preservation": round(float(knn_pres), 4),
            "trustworthiness": round(float(trust), 4),
        }

    n = Z_svd.shape[0]
    k = nn_hi.shape[1]
    if n <= 2 or k <= 0:
        return {"knn_preservation": 1.0, "trustworthiness": 1.0}

    sq = np.sum(Y2 * Y2, axis=1, keepdims=True)
    d2 = np.maximum(0.0, sq + sq.T - 2.0 * (Y2 @ Y2.T))
    np.fill_diagonal(d2, np.inf)
    if k == n - 1:
        nn_lo = np.argsort(d2, axis=1)[:, :k]
    else:
        nn_lo = np.argpartition(d2, kth=k - 1, axis=1)[:, :k]

    overlap_sum = 0.0
    for i in range(n):
        s_hi = set(nn_hi[i].tolist())
        s_lo = set(nn_lo[i].tolist())
        overlap_sum += len(s_hi & s_lo) / float(k)
    knn_pres = overlap_sum / float(n)

    # Trustworthiness T(k): penalize false 2D neighbors by excess high-dim rank
    denom = n * k * (2 * n - 3 * k - 1)
    if denom <= 0:
        trust = 1.0
    else:
        Zn = Z_svd / np.maximum(np.linalg.norm(Z_svd, axis=1, keepdims=True), 1e-12)
        sim = Zn @ Zn.T
        np.fill_diagonal(sim, 2.0)
        ranks = np.argsort(np.argsort(-sim, axis=1), axis=1)
        t_sum = 0.0
        for i in range(n):
            s_hi = set(nn_hi[i].tolist())
            for j in nn_lo[i]:
                j_i = int(j)
                if j_i not in s_hi:
                    t_sum += max(0, int(ranks[i, j_i]) - k)
        trust = max(0.0, min(1.0, 1.0 - (2.0 * t_sum / float(denom))))

    return {
        "knn_preservation": round(float(knn_pres), 4),
        "trustworthiness": round(float(trust), 4),
    }


def compute_sim_and_uniq(
    nn_sim: Any,
    dup_counts: Sequence[int],
) -> Tuple[List[float], List[float]]:
    """Compute `(sim_nn1, uniq)` from high-dim cosine similarities and duplicate group sizes."""
    n = len(dup_counts)
    if n == 0:
        return [], []
    sim_rows = _as_py_rows(nn_sim)
    sim_nn1: List[float] = []
    raw_nov: List[float] = []
    for i in range(n):
        row = sim_rows[i] if i < len(sim_rows) else []
        if row:
            s1 = max(0.0, min(1.0, float(row[0])))
            k_use = min(5, len(row))
            mean_s = sum(max(0.0, min(1.0, float(row[j]))) for j in range(k_use)) / float(k_use)
            nov = max(0.0, min(1.0, 1.0 - mean_s))
        else:
            s1 = 0.0
            nov = 1.0
        sim_nn1.append(round(s1, 4))
        raw_nov.append(nov)

    if n <= 1:
        norm_nov = [1.0] * n
    else:
        lo = min(raw_nov)
        if n >= 20:
            s_nov = sorted(raw_nov)
            hi = s_nov[min(n - 1, int(0.98 * (n - 1)))]
        else:
            hi = max(raw_nov)
        span = hi - lo
        if span > 1e-6:
            norm_nov = [min(1.0, max(0.0, (r - lo) / span)) for r in raw_nov]
        else:
            norm_nov = [min(1.0, max(0.0, r)) for r in raw_nov]

    uniq_scores: List[float] = []
    for i in range(n):
        dc = max(1, int(dup_counts[i]))
        down = 1.0 / (1.0 + math.log2(dc)) if dc > 1 else 1.0
        uniq_scores.append(round(max(0.0, min(1.0, norm_nov[i] * down)), 4))
    return sim_nn1, uniq_scores


def compute_namespace_drift(
    nn_hi: Any,
    dir_tops: Sequence[str],
    is_dom1k: Sequence[bool],
    k_drift: int = 10,
) -> Tuple[List[float], Dict[str, Any]]:
    """Compute per-point fraction of `k_drift` nearest math neighbors from a different directory."""
    n = len(dir_tops)
    k_avail = (len(nn_hi[0]) if n > 0 else 0) if np is None else int(nn_hi.shape[1])
    if n <= 1 or k_avail == 0:
        return [0.0] * n, {
            "k_neighbors": 0,
            "mean_drift_all": 0.0,
            "mean_drift_dom1k": 0.0,
            "dom1k_count": int(sum(1 for x in is_dom1k if x)),
            "dom1k_nn1_diff_folder_pct": 0.0,
        }

    k_eff = min(int(k_drift), k_avail)
    drifts: List[float] = []
    dom1k_drifts: List[float] = []
    dom1k_nn1_diff = 0
    dom1k_cnt = 0

    for i in range(n):
        d_i = dir_tops[i]
        nbrs = nn_hi[i][:k_eff] if np is None else nn_hi[i, :k_eff]
        diff_cnt = sum(1 for j in nbrs if dir_tops[int(j)] != d_i)
        frac = round(diff_cnt / float(k_eff), 4)
        drifts.append(frac)
        if is_dom1k[i]:
            dom1k_cnt += 1
            dom1k_drifts.append(frac)
            if dir_tops[int(nbrs[0])] != d_i:
                dom1k_nn1_diff += 1

    return drifts, {
        "k_neighbors": k_eff,
        "mean_drift_all": round(sum(drifts) / float(n), 4),
        "mean_drift_dom1k": round(sum(dom1k_drifts) / float(max(1, dom1k_cnt)), 4),
        "dom1k_count": int(dom1k_cnt),
        "dom1k_nn1_diff_folder_pct": round(100.0 * dom1k_nn1_diff / float(max(1, dom1k_cnt)), 2),
    }


# ---------------------------------------------------------------------------
# Cluster Partition Reconstruction & Parallel Outgoing-Dependency Aggregation
# ---------------------------------------------------------------------------

_SH_EMB_DB: str = ""
_SH_EMB_CL: Any = None
_SH_EMB_EXT: Any = None
_SH_EMB_LIB: Any = None
_SH_EMB_NCL: int = 0
_SH_EMB_NEXT: int = 0


def _cluster_edge_worker(bounds: Tuple[int, int]) -> Tuple[Any, Any, Any]:
    """Count `(cluster_idx, ext_vocab_idx)` outgoing edges plus per-cluster `(lib, tot)` edges."""
    lo, hi = bounds
    ncl = _SH_EMB_NCL
    next_v = _SH_EMB_NEXT
    cl_arr = _SH_EMB_CL
    ex_arr = _SH_EMB_EXT
    lib_arr = _SH_EMB_LIB
    counts = np.zeros(ncl * next_v, dtype=np.int64)
    cl_lib = np.zeros(ncl, dtype=np.int64)
    cl_tot = np.zeros(ncl, dtype=np.int64)
    can_pack = int(cl_arr.shape[0]) < (1 << 30)

    with contextlib.closing(atlas.connect_ro(_SH_EMB_DB, mmap_bytes=8_589_934_592)) as con:
        if can_pack:
            cur = con.execute(
                "SELECT ((src << 32) | dst) FROM edges WHERE src >= ? AND src < ?",
                (lo, hi),
            )
            while True:
                rows = cur.fetchmany(250_000)
                if not rows:
                    break
                packed = np.fromiter((r[0] for r in rows), dtype=np.int64, count=len(rows))
                src = packed >> 32
                dst = packed & 0xFFFFFFFF
                c = cl_arr[src]
                cmask = c >= 0
                if np.any(cmask):
                    c_valid = c[cmask].astype(np.int64)
                    d_valid = dst[cmask]
                    cl_tot += np.bincount(c_valid, minlength=ncl)
                    is_l = lib_arr[d_valid] > 0
                    if np.any(is_l):
                        cl_lib += np.bincount(c_valid[is_l], minlength=ncl)
                    if next_v > 0:
                        v = ex_arr[d_valid]
                        vmask = v >= 0
                        if np.any(vmask):
                            idx = c_valid[vmask] * next_v + v[vmask].astype(np.int64)
                            counts += np.bincount(idx, minlength=ncl * next_v)
        else:
            max_id = int(cl_arr.shape[0])
            cur = con.execute(
                "SELECT src, dst FROM edges WHERE src >= ? AND src < ?",
                (lo, hi),
            )
            while True:
                rows = cur.fetchmany(100_000)
                if not rows:
                    break
                for s_i, d_i in rows:
                    if 0 <= s_i < max_id and 0 <= d_i < max_id:
                        c_i = int(cl_arr[s_i])
                        if c_i >= 0:
                            cl_tot[c_i] += 1
                            if lib_arr[d_i] > 0:
                                cl_lib[c_i] += 1
                            if next_v > 0:
                                v_i = int(ex_arr[d_i])
                                if v_i >= 0:
                                    counts[c_i * next_v + v_i] += 1
    return counts, cl_lib, cl_tot


def _build_cluster_partition(
    con: sqlite3.Connection,
    n_total: int,
    name_of: Sequence[str],
    kind_of: Sequence[str],
    live_of: Sequence[int],
    fan_in_of: Sequence[int],
    mod_of: Sequence[Optional[str]],
    sub_sz: Sequence[int],
    children: Dict[int, List[int]],
    dom_roots_top: Sequence[int],
    tin_by_id: Sequence[int],
    reg_by_dfs: Sequence[str],
    cluster_labels_map: Dict[str, Dict[str, Any]],
) -> Tuple[List[Dict[str, Any]], np.ndarray]:
    """Deterministically partition live declarations into coarse blueprint clusters."""
    n_live = int(sum(live_of))
    name_to_id = {name_of[i]: i for i in range(n_total) if name_of[i]}

    if n_live >= 5000:
        split_threshold = 25000
        min_dom_cluster = 1500
        min_residual_cluster = 1500
    else:
        split_threshold = max(4, n_live // 6)
        min_dom_cluster = max(2, n_live // 12)
        min_residual_cluster = 1

    pillar_id_map = {name_to_id[nm]: pil for nm, pil in _PILLAR_ROOT_NAMES.items() if nm in name_to_id}
    roots_sorted = sorted(dom_roots_top, key=lambda r: (-sub_sz[r], r))
    primary_root = roots_sorted[0] if roots_sorted else -1

    pillar_of: Dict[int, str] = {}
    for r in roots_sorted:
        start_pil = pillar_id_map.get(r, "tcb_mathlib_core" if r != primary_root else "shared_diamond")
        st = [(r, start_pil)]
        while st:
            u, pil = st.pop()
            cp = pillar_id_map.get(u, pil)
            pillar_of[u] = cp
            for ch in children.get(u, ()):
                st.append((ch, cp))

    def _collect_subtree(root_u: int) -> List[int]:
        out: List[int] = []
        st = [root_u]
        while st:
            x = st.pop()
            out.append(x)
            st.extend(children.get(x, ()))
        return out

    dom_cluster_roots: List[int] = []
    residual_nodes: List[int] = []
    tcb_nodes: List[int] = []

    def _walk(u: int) -> None:
        ch = sorted(children.get(u, ()), key=lambda c: (-sub_sz[c], c))
        big = [c for c in ch if sub_sz[c] >= min_dom_cluster]
        if sub_sz[u] >= split_threshold and big:
            residual_nodes.append(u)
            for c in ch:
                if sub_sz[c] < min_dom_cluster:
                    residual_nodes.extend(_collect_subtree(c))
            for c in big:
                _walk(c)
        else:
            dom_cluster_roots.append(u)

    for r in roots_sorted:
        if sub_sz[r] >= min_dom_cluster:
            _walk(r)
        else:
            tcb_nodes.extend(_collect_subtree(r))

    raw_clusters: List[Dict[str, Any]] = []
    for u in dom_cluster_roots:
        mems = _collect_subtree(u)
        raw_clusters.append({
            "kind": "dom_subtree",
            "flirt_pillar": pillar_of.get(u, "shared_diamond"),
            "root_decl_id": u,
            "root_decl": name_of[u],
            "members": mems,
            "title_hint": name_of[u],
        })

    res_groups: Dict[Tuple[str, str], List[int]] = collections.defaultdict(list)
    for did in residual_nodes:
        pil = pillar_of.get(did, "shared_diamond")
        dt = dir_top_from_module(name_of[did], mod_of[did]) if mod_of[did] else "<library_or_unmatched>"
        res_groups[(pil, dt)].append(did)

    small_tails: Dict[str, List[int]] = collections.defaultdict(list)
    for (pil, fl2), mems in sorted(res_groups.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        if len(mems) >= min_residual_cluster:
            rep = max(mems, key=lambda x: (sub_sz[x], fan_in_of[x], -x))
            raw_clusters.append({
                "kind": "residual_neighborhood",
                "flirt_pillar": pil,
                "root_decl_id": rep,
                "root_decl": name_of[rep],
                "members": mems,
                "title_hint": f"{pil}::{fl2}",
            })
        else:
            small_tails[pil].extend(mems)

    for pil, mems in sorted(small_tails.items()):
        if not mems:
            continue
        rep = max(mems, key=lambda x: (sub_sz[x], fan_in_of[x], -x))
        raw_clusters.append({
            "kind": "residual_tail",
            "flirt_pillar": pil,
            "root_decl_id": rep,
            "root_decl": name_of[rep],
            "members": mems,
            "title_hint": f"{pil}::<residual_tail>",
        })

    if tcb_nodes:
        rep = max(tcb_nodes, key=lambda x: (fan_in_of[x], sub_sz[x], -x))
        raw_clusters.append({
            "kind": "tcb_library_root",
            "flirt_pillar": "tcb_mathlib_core",
            "root_decl_id": rep,
            "root_decl": name_of[rep],
            "members": tcb_nodes,
            "title_hint": "TCB & Shared Mathlib/Core Library",
        })

    raw_clusters.sort(key=lambda c: (-len(c["members"]), c["flirt_pillar"], c["title_hint"]))

    cluster_idx_of = np.full(n_total, -1, dtype=np.int32)
    for idx, cl in enumerate(raw_clusters):
        cid = f"BP{idx + 1:03d}"
        cl["cluster_id"] = cid
        for did in cl["members"]:
            cluster_idx_of[did] = idx

        # Dominant folder, pillar, and label
        rep_id = int(cl["root_decl_id"])
        tin = tin_by_id[rep_id] if 0 <= rep_id < len(tin_by_id) else -1
        reg_key = reg_by_dfs[tin] if (0 <= tin < len(reg_by_dfs)) else ""
        if cl["flirt_pillar"] == "tcb_mathlib_core":
            pil_code = "BR"
        elif reg_key:
            pil_code = _pillar_code_for_region(reg_key, cl["root_decl"])
        else:
            pil_code = "MAIN"
        cl["pillar"] = pil_code

        dir_ctr: collections.Counter[str] = collections.Counter()
        for did in cl["members"]:
            if mod_of[did]:
                dir_ctr[dir_top_from_module(name_of[did], mod_of[did])] += 1
        cl["dir_top"] = (
            dir_ctr.most_common(1)[0][0]
            if dir_ctr
            else dir_top_from_module(cl["root_decl"], mod_of[rep_id])
        )
        lbl_meta = cluster_labels_map.get(cid, {})
        blind = lbl_meta.get("blinded_label") if isinstance(lbl_meta.get("blinded_label"), dict) else {}
        cl["label"] = _strip_cluster_tag(str(blind.get("label") or cl["title_hint"]))
        cl["root_kind"] = kind_of[rep_id]
        cl["root_mod"] = mod_of[rep_id]

    return raw_clusters, cluster_idx_of


def _build_clusters_layer(
    kernel_db_path: str,
    raw_clusters: Sequence[Dict[str, Any]],
    cluster_idx_of: Any,
    cand_ext_ids: Sequence[int],
    n_total: int,
    name_of: Sequence[str],
    type_ratio_of: Sequence[float],
    line_of_id: Dict[int, int],
    *,
    is_lib_arr: Any = None,
    dup_count_of_id: Optional[Sequence[int]] = None,
    lib_match_of_id: Optional[Sequence[int]] = None,
    dk_ids: Optional[Set[int]] = None,
    vn_of: Optional[Sequence[int]] = None,
    kind_of: Optional[Sequence[str]] = None,
    max_vocab: int = 768,
    k_svd: int = 24,
    k_nn: int = 15,
    n_steps: int = 180,
    seed: int = 42,
    workers: int = 0,
) -> Dict[str, Any]:
    """Compute TF-IDF + SVD(k=24) + `pca2` + `knn2` over the blueprint clusters."""
    global _SH_EMB_DB, _SH_EMB_CL, _SH_EMB_EXT, _SH_EMB_LIB, _SH_EMB_NCL, _SH_EMB_NEXT
    m_cl = len(raw_clusters)
    n_cand = len(cand_ext_ids)

    base_fields = [
        "id", "name", "short", "label", "kind_idx", "dom",
        "pillar_idx", "dir_idx", "mod", "line",
        "px", "py", "ux", "uy",
        "top_term_idxs", "nn_idx", "drift", "type_ratio",
        "sim_nn1", "uniq", "lib_sim", "dup_count", "hygiene_flag",
    ]

    if m_cl == 0:
        return {
            "count": 0,
            "svd_explained_variance_ratios": [],
            "svd_explained_variance_sum": 0.0,
            "metrics": {
                "pca2": {"knn_preservation": 1.0, "trustworthiness": 1.0},
                "knn2": {"knn_preservation": 1.0, "trustworthiness": 1.0},
                "drift": {"k_neighbors": 0, "mean_drift_all": 0.0, "mean_drift_dom1k": 0.0, "dom1k_count": 0, "dom1k_nn1_diff_folder_pct": 0.0},
            },
            "tables": {
                "pillars": [],
                "dirs": [],
                "kinds": [],
                "vocab_terms": [],
                "hygiene_flags": list(HYGIENE_FLAGS),
            },
            "fields": base_fields,
            "points": [],
            "_decoded": [],
        }

    ext_arr = np.full(n_total, -1, dtype=np.int32)
    for j, did in enumerate(cand_ext_ids):
        ext_arr[did] = j
    if is_lib_arr is None:
        is_lib_arr = np.zeros(n_total, dtype=np.uint8)

    _SH_EMB_DB = kernel_db_path
    _SH_EMB_CL = cluster_idx_of
    _SH_EMB_EXT = ext_arr
    _SH_EMB_LIB = is_lib_arr
    _SH_EMB_NCL = m_cl
    _SH_EMB_NEXT = n_cand

    if workers <= 0:
        workers = min(16, os.cpu_count() or 4)
    use_mp = (
        workers > 1
        and n_total >= 50_000
        and "fork" in mp.get_all_start_methods()
    )
    if use_mp:
        step = (n_total + workers - 1) // workers
        shards = [(i * step, min(n_total, (i + 1) * step)) for i in range(workers)]
        shards = [s for s in shards if s[0] < s[1]]
        with mp.get_context("fork").Pool(len(shards)) as pool:
            parts = pool.map(_cluster_edge_worker, shards)
        mat = sum(p[0] for p in parts).reshape((m_cl, n_cand)) if n_cand > 0 else np.zeros((m_cl, 0), dtype=np.int64)
        cl_lib_edges = sum(p[1] for p in parts)
        cl_tot_edges = sum(p[2] for p in parts)
    else:
        c_raw, cl_lib_edges, cl_tot_edges = _cluster_edge_worker((0, n_total))
        mat = c_raw.reshape((m_cl, n_cand)) if n_cand > 0 else np.zeros((m_cl, 0), dtype=np.int64)

    _SH_EMB_CL = None
    _SH_EMB_EXT = None
    _SH_EMB_LIB = None

    if n_cand > 0:
        df = np.sum(mat > 0, axis=0)
        min_df = 2 if m_cl >= 10 else 1
        max_df = int(0.85 * m_cl) if m_cl >= 6 else m_cl
        keep = (df >= min_df) & (df <= max_df)
        if not np.any(keep):
            keep = df >= 1
        idf = np.log((1.0 + m_cl) / (1.0 + df))
        tf_log = np.log1p(mat.astype(np.float64))
        energy = np.sum((tf_log * idf[None, :]) ** 2, axis=0) * keep
        v_take = min(int(max_vocab), int(np.count_nonzero(keep)))
        if v_take > 0:
            top_cols = np.argsort(-energy)[:v_take]
            vocab_ids = [int(cand_ext_ids[int(j)]) for j in top_cols]
            X_tf = tf_log[:, top_cols] * idf[None, top_cols]
        else:
            vocab_ids = []
            X_tf = np.zeros((m_cl, 0), dtype=np.float64)
    else:
        vocab_ids = []
        X_tf = np.zeros((m_cl, 0), dtype=np.float64)

    # Smooth fallback features if a cluster has zero TF-IDF terms
    row_norms = np.linalg.norm(X_tf, axis=1, keepdims=True)
    if X_tf.shape[1] == 0:
        X = np.ones((m_cl, 2), dtype=np.float64) / math.sqrt(2.0)
    else:
        X = X_tf / np.maximum(row_norms, 1e-12)

    U, S, _Vt = randomized_svd(X, k=k_svd, seed=seed)
    Z_svd = U * S[None, :] if S.size > 0 else np.zeros((m_cl, 2), dtype=np.float64)
    tot_ss = float(np.sum(X * X))
    exp_ratios = [round(float(sv * sv / tot_ss), 5) for sv in S] if tot_ss > 0 else []
    exp_sum = round(float(sum(exp_ratios)), 4)

    pca2 = normalize_2d_isotropic(Z_svd[:, :2] if Z_svd.shape[1] >= 2 else Z_svd)
    knn2, nn_hi, nn_sim = _knn2_umap_with_sim(Z_svd, pca2, k_nn=k_nn, n_steps=n_steps, seed=seed)

    m_pca = evaluate_embedding_quality(Z_svd, pca2, nn_hi)
    m_knn = evaluate_embedding_quality(Z_svd, knn2, nn_hi)

    dir_tops = [str(c["dir_top"]) for c in raw_clusters]
    is_dom1k = [True] * m_cl
    drifts, drift_stats = compute_namespace_drift(nn_hi, dir_tops, is_dom1k, k_drift=10)

    dup_counts = [
        max(1, int(dup_count_of_id[int(cl["root_decl_id"])])) if dup_count_of_id is not None else 1
        for cl in raw_clusters
    ]
    sim_nn1_list, uniq_list = compute_sim_and_uniq(nn_sim, dup_counts)

    # Intern compact lookup tables
    pillars_tbl = sorted({str(c["pillar"]) for c in raw_clusters})
    dirs_tbl = sorted(set(dir_tops))
    kinds_tbl = sorted({str(c["root_kind"]) for c in raw_clusters})
    pil_map = {v: i for i, v in enumerate(pillars_tbl)}
    dir_map = {v: i for i, v in enumerate(dirs_tbl)}
    knd_map = {v: i for i, v in enumerate(kinds_tbl)}
    vocab_terms = [name_of[did] for did in vocab_ids]

    points_compact: List[List[Any]] = []
    decoded: List[Dict[str, Any]] = []
    for i, cl in enumerate(raw_clusters):
        if X_tf.shape[1] > 0 and float(row_norms[i, 0]) > 1e-12:
            top_j = [int(j) for j in np.argsort(-X_tf[i])[:4] if X_tf[i, j] > 0.0]
        else:
            top_j = []
        nbr5 = [int(j) for j in nn_hi[i, :5]]
        rep_id = int(cl["root_decl_id"])
        line_no = line_of_id.get(rep_id)
        tr_val = round(float(cl.get("type_ratio", 0.5)), 4)
        px, py = round(float(pca2[i, 0]), 4), round(float(pca2[i, 1]), 4)
        ux, uy = round(float(knn2[i, 0]), 4), round(float(knn2[i, 1]), 4)
        short = short_decl_name(cl["root_decl"])

        tot_e = int(cl_tot_edges[i])
        lib_e = int(cl_lib_edges[i])
        edge_lib_frac = (lib_e / float(tot_e)) if tot_e > 0 else 0.0
        if is_lib_arr[rep_id] > 0:
            lib_sim_val = 1.0
        elif lib_match_of_id is not None and lib_match_of_id[rep_id]:
            lib_sim_val = round(max(edge_lib_frac, 0.5 + 0.5 * edge_lib_frac), 4)
        else:
            lib_sim_val = round(max(0.0, min(1.0, edge_lib_frac)), 4)

        has_dk = bool(dk_ids and any(int(m_id) in dk_ids for m_id in cl["members"]))
        is_alias = bool(vn_of is not None and vn_of[rep_id] == 1 and (kind_of is None or kind_of[rep_id] in ("thm", "def")))
        if has_dk:
            hyg = 1
        elif is_alias:
            hyg = 2
        elif drifts[i] >= 0.70:
            hyg = 3
        else:
            hyg = 0

        points_compact.append([
            cl["cluster_id"],
            cl["root_decl"],
            short,
            cl["label"],
            knd_map[str(cl["root_kind"])],
            len(cl["members"]),
            pil_map[str(cl["pillar"])],
            dir_map[dir_tops[i]],
            cl["root_mod"],
            line_no,
            px, py,
            ux, uy,
            top_j,
            nbr5,
            drifts[i],
            tr_val,
            sim_nn1_list[i],
            uniq_list[i],
            lib_sim_val,
            dup_counts[i],
            hyg,
        ])
        decoded.append({
            "id": cl["cluster_id"],
            "name": cl["root_decl"],
            "short": short,
            "label": cl["label"],
            "kind": str(cl["root_kind"]),
            "dom": len(cl["members"]),
            "pillar": str(cl["pillar"]),
            "dir_top": dir_tops[i],
            "mod": cl["root_mod"],
            "line": line_no,
            "px": px,
            "py": py,
            "ux": ux,
            "uy": uy,
            "top_terms": [vocab_terms[j] for j in top_j],
            "nn_idx": nbr5,
            "drift": drifts[i],
            "type_ratio": tr_val,
            "sim_nn1": sim_nn1_list[i],
            "uniq": uniq_list[i],
            "lib_sim": lib_sim_val,
            "dup_count": dup_counts[i],
            "hygiene_flag": HYGIENE_FLAGS[hyg],
        })

    return {
        "count": m_cl,
        "svd_explained_variance_ratios": exp_ratios,
        "svd_explained_variance_sum": exp_sum,
        "metrics": {
            "pca2": m_pca,
            "knn2": m_knn,
            "drift": drift_stats,
        },
        "tables": {
            "pillars": pillars_tbl,
            "dirs": dirs_tbl,
            "kinds": kinds_tbl,
            "vocab_terms": vocab_terms,
            "hygiene_flags": list(HYGIENE_FLAGS),
        },
        "fields": base_fields,
        "points": points_compact,
        "_decoded": decoded,
    }


# ---------------------------------------------------------------------------
# Landmarks Selection & Bounded Multi-Hop TF-IDF Embedding
# ---------------------------------------------------------------------------

def _select_landmarks(
    n_total: int,
    name_of: Sequence[str],
    kind_of: Sequence[str],
    live_of: Sequence[int],
    fan_in_of: Sequence[int],
    tn_of: Sequence[int],
    sub_sz: Sequence[int],
    mod_of: Sequence[Optional[str]],
    origin_of: Sequence[str],
    raw_clusters: Sequence[Dict[str, Any]],
    lean_kind_by_id: Dict[int, str],
    portability_ids: Sequence[int],
    max_landmarks: int = 1800,
) -> Tuple[List[int], Set[int]]:
    """Select `~1,500–2,000` live named declarations covering hubs, structures & islands."""
    selected: List[int] = []
    seen: Set[int] = set()
    dom1k_set: Set[int] = set()
    name_to_id = {name_of[i]: i for i in range(n_total) if name_of[i]}

    def _add(did: int) -> None:
        if 0 <= did < n_total and did not in seen and live_of[did] and not is_compiler_aux(name_of[did]):
            seen.add(did)
            selected.append(did)

    # 1. ALL live non-compiler-aux `dom >= 1,000` declarations
    dom1k_cands = [
        (-sub_sz[did], did)
        for did in range(n_total)
        if live_of[did] and sub_sz[did] >= 1000 and not is_compiler_aux(name_of[did])
    ]
    dom1k_cands.sort()
    for _, did in dom1k_cands:
        _add(did)
        dom1k_set.add(did)

    # 2. Curated showcase landmarks, cluster roots, and standalone portability gems
    for _, _, dname in atlas.DEFAULT_LANDMARKS:
        did = name_to_id.get(dname)
        if did is not None:
            _add(did)
    for cl in raw_clusters:
        _add(int(cl["root_decl_id"]))
    for pid in portability_ids:
        _add(int(pid))

    # 3. Top `structure` / `class` (or `inductive`) hubs by fan_in
    struct_cands = [
        (-fan_in_of[did], -sub_sz[did], did)
        for did in range(n_total)
        if live_of[did]
        and did not in seen
        and origin_of[did] == "project"
        and not is_compiler_aux(name_of[did])
        and (lean_kind_by_id.get(did) in ("structure", "class") or kind_of[did] == "inductive")
    ]
    struct_cands.sort()
    struct_cap = max(20, min(350, max_landmarks // 5))
    for _, _, did in struct_cands[:struct_cap]:
        if len(selected) >= max_landmarks:
            break
        _add(did)

    # 4. Fill remaining slots with top live named project decls (subtree + fan_in + type_nodes)
    proj_cands = [
        (-(sub_sz[did] * 2 + fan_in_of[did] + tn_of[did]), did)
        for did in range(n_total)
        if live_of[did]
        and did not in seen
        and origin_of[did] == "project"
        and mod_of[did] is not None
        and not is_compiler_aux(name_of[did])
    ]
    proj_cands.sort()
    for _, did in proj_cands:
        if len(selected) >= max_landmarks:
            break
        _add(did)

    # Fallback on tiny DBs where `mod_of` may be sparse: allow remaining live named decls
    if len(selected) < min(max_landmarks, 32):
        any_cands = [
            (-(sub_sz[did] * 2 + fan_in_of[did] + tn_of[did]), did)
            for did in range(n_total)
            if live_of[did] and did not in seen and not is_compiler_aux(name_of[did])
        ]
        any_cands.sort()
        for _, did in any_cands:
            if len(selected) >= max_landmarks:
                break
            _add(did)

    return selected, dom1k_set


def _build_landmarks_layer(
    con: sqlite3.Connection,
    selected: Sequence[int],
    dom1k_set: Set[int],
    ext_vocab_set: Set[int],
    n_total: int,
    name_of: Sequence[str],
    kind_of: Sequence[str],
    tn_of: Sequence[int],
    vn_of: Sequence[int],
    et_of: Sequence[int],
    ev_of: Sequence[int],
    sub_sz: Sequence[int],
    mod_of: Sequence[Optional[str]],
    origin_of: Sequence[str],
    tin_by_id: Sequence[int],
    reg_by_dfs: Sequence[str],
    cluster_idx_of: Any,
    raw_clusters: Sequence[Dict[str, Any]],
    lean_kind_by_id: Dict[int, str],
    line_of_id: Dict[int, int],
    *,
    is_lib_arr: Any = None,
    dup_count_of_id: Optional[Sequence[int]] = None,
    lib_match_of_id: Optional[Sequence[int]] = None,
    dk_ids: Optional[Set[int]] = None,
    max_vocab: int = 1024,
    k_svd: int = 24,
    k_nn: int = 15,
    n_steps: int = 180,
    seed: int = 42,
) -> Dict[str, Any]:
    """Build TF-IDF + structural type embedding over landmark declarations."""
    n = len(selected)
    base_fields = [
        "name", "short", "kind_idx", "dom", "pillar_idx", "dir_idx",
        "cluster_idx", "mod_idx", "line", "px", "py", "ux", "uy",
        "top_term_idxs", "nn_idx", "drift", "type_ratio",
        "sim_nn1", "uniq", "lib_sim", "dup_count", "hygiene_flag",
    ]
    if n == 0:
        return {
            "count": 0,
            "svd_explained_variance_ratios": [],
            "svd_explained_variance_sum": 0.0,
            "metrics": {
                "pca2": {"knn_preservation": 1.0, "trustworthiness": 1.0},
                "knn2": {"knn_preservation": 1.0, "trustworthiness": 1.0},
                "drift": {"k_neighbors": 0, "mean_drift_all": 0.0, "mean_drift_dom1k": 0.0, "dom1k_count": 0, "dom1k_nn1_diff_folder_pct": 0.0},
            },
            "tables": {
                "pillars": [],
                "dirs": [],
                "kinds": [],
                "clusters": [],
                "mods": [],
                "vocab_terms": [],
                "hygiene_flags": list(HYGIENE_FLAGS),
            },
            "fields": base_fields,
            "points": [],
            "_decoded": [],
        }

    # Bounded multi-hop outgoing dependency bag per landmark (+ hop-0 library edge ratio)
    bags: List[Dict[int, float]] = []
    df_ctr: collections.Counter[int] = collections.Counter()
    direct_lib_ratios: List[float] = []

    for did in selected:
        bag: Dict[int, float] = collections.defaultdict(float)
        visited_proj: Set[int] = {did}
        frontier = [did]
        weights = (1.0, 0.5, 0.25, 0.125)
        lib_w = 0.0
        tot_w = 0.0
        for hop, w in enumerate(weights):
            if not frontier:
                break
            if hop >= 2 and len(bag) >= 12:
                break
            next_frontier: List[int] = []
            # Query in chunks for speed (uses PRIMARY KEY(src, dst))
            for u in frontier[:160]:
                for dst, ekind in con.execute("SELECT dst, kind FROM edges WHERE src=?", (u,)):
                    d_i = int(dst)
                    if hop == 0 and 0 <= d_i < n_total:
                        ew = 2.0 if int(ekind) in (1, 3) else 1.0
                        tot_w += ew
                        if (is_lib_arr is not None and is_lib_arr[d_i] > 0) or origin_of[d_i] in ("mathlib4", "lean4", "batteries"):
                            lib_w += ew
                    if d_i in ext_vocab_set and d_i != did:
                        bag[d_i] += w
                    elif 0 <= d_i < n_total and origin_of[d_i] == "project" and d_i not in visited_proj:
                        visited_proj.add(d_i)
                        next_frontier.append(d_i)
            frontier = next_frontier

        if (is_lib_arr is not None and is_lib_arr[did] > 0) or origin_of[did] in ("mathlib4", "lean4", "batteries"):
            direct_lib_ratios.append(1.0)
        elif lib_match_of_id is not None and lib_match_of_id[did]:
            edge_r = (lib_w / tot_w) if tot_w > 0.0 else 0.0
            direct_lib_ratios.append(round(max(edge_r, 0.5 + 0.5 * edge_r), 4))
        else:
            direct_lib_ratios.append(round((lib_w / tot_w) if tot_w > 0.0 else 0.0, 4))

        bags.append(bag)
        for tid in bag:
            df_ctr[tid] += 1

    # Select top discriminating vocabulary via smooth TF-IDF energy
    min_df = 3 if n >= 60 else 1
    max_df = int(0.80 * n) if n >= 10 else n
    term_score: Dict[int, float] = {}
    for tid, df in df_ctr.items():
        if df < min_df or df > max_df:
            continue
        idf = math.log((1.0 + n) / (1.0 + df))
        term_score[tid] = idf * df * (1.0 - df / float(max(1, n)))

    if not term_score and df_ctr:
        for tid, df in df_ctr.items():
            term_score[tid] = math.log((1.0 + n) / (1.0 + df)) * df

    vocab_ids = [tid for tid, _ in sorted(term_score.items(), key=lambda x: (-x[1], x[0]))[:max_vocab]]
    v_map = {tid: j for j, tid in enumerate(vocab_ids)}
    V = len(vocab_ids)

    X_tf = np.zeros((n, V), dtype=np.float64)
    if V > 0:
        idf_vec = np.array([math.log((1.0 + n) / (1.0 + df_ctr[tid])) for tid in vocab_ids], dtype=np.float64)
        for i, bag in enumerate(bags):
            for tid, w in bag.items():
                j = v_map.get(tid)
                if j is not None:
                    X_tf[i, j] = math.log1p(w) * idf_vec[j]
        tf_norms = np.linalg.norm(X_tf, axis=1, keepdims=True)
        X_tf_norm = X_tf / np.maximum(tf_norms, 1e-12)
    else:
        X_tf_norm = X_tf

    # Structural type features: kind one-hot, log(dom), type_nodes, value_nodes, type_ratio
    kind_cats = {"thm": 0, "theorem": 0, "lemma": 0, "def": 1, "abbrev": 1, "instance": 1}
    S_feat = np.zeros((n, 7), dtype=np.float64)
    type_ratios: List[float] = []
    display_kinds: List[str] = []
    for i, did in enumerate(selected):
        lk = lean_kind_by_id.get(did) or kind_of[did]
        display_kinds.append(lk)
        k_col = kind_cats.get(lk, 2)
        S_feat[i, k_col] = 1.0
        S_feat[i, 3] = math.log1p(max(1, sub_sz[did]))
        S_feat[i, 4] = math.log1p(max(0, tn_of[did]))
        S_feat[i, 5] = math.log1p(max(0, vn_of[did]))
        et_v, ev_v = et_of[did], ev_of[did]
        tr = et_v / float(max(1, et_v + ev_v))
        S_feat[i, 6] = tr
        type_ratios.append(round(tr, 4))

    for col in range(3, 7):
        mu = float(S_feat[:, col].mean())
        sd = float(S_feat[:, col].std())
        if sd > 1e-9:
            S_feat[:, col] = (S_feat[:, col] - mu) / sd
    S_feat *= 0.12

    X = np.hstack([X_tf_norm, S_feat]) if V > 0 else S_feat
    X = X / np.maximum(np.linalg.norm(X, axis=1, keepdims=True), 1e-12)

    U, S, _Vt = randomized_svd(X, k=k_svd, seed=seed)
    Z_svd = U * S[None, :] if S.size > 0 else np.zeros((n, 2), dtype=np.float64)
    tot_ss = float(np.sum(X * X))
    exp_ratios = [round(float(sv * sv / tot_ss), 5) for sv in S] if tot_ss > 0 else []
    exp_sum = round(float(sum(exp_ratios)), 4)

    pca2 = normalize_2d_isotropic(Z_svd[:, :2] if Z_svd.shape[1] >= 2 else Z_svd)
    knn2, nn_hi, nn_sim = _knn2_umap_with_sim(Z_svd, pca2, k_nn=k_nn, n_steps=n_steps, seed=seed)

    m_pca = evaluate_embedding_quality(Z_svd, pca2, nn_hi)
    m_knn = evaluate_embedding_quality(Z_svd, knn2, nn_hi)

    dir_tops = [dir_top_from_module(name_of[did], mod_of[did]) for did in selected]
    is_dom1k = [did in dom1k_set for did in selected]
    drifts, drift_stats = compute_namespace_drift(nn_hi, dir_tops, is_dom1k, k_drift=10)

    dup_counts = [
        max(1, int(dup_count_of_id[did])) if dup_count_of_id is not None else 1
        for did in selected
    ]
    sim_nn1_list, uniq_list = compute_sim_and_uniq(nn_sim, dup_counts)

    pillars_list: List[str] = []
    for did in selected:
        if origin_of[did] != "project":
            pillars_list.append("BR")
        else:
            tin = tin_by_id[did] if 0 <= did < len(tin_by_id) else -1
            rk = reg_by_dfs[tin] if (0 <= tin < len(reg_by_dfs)) else ""
            pillars_list.append(_pillar_code_for_region(rk, name_of[did]) if rk else "MAIN")

    pillars_tbl = sorted(set(pillars_list))
    dirs_tbl = sorted(set(dir_tops))
    kinds_tbl = sorted(set(display_kinds))
    clusters_tbl = [str(c["cluster_id"]) for c in raw_clusters]
    mods_tbl = sorted({str(mod_of[did]) for did in selected if mod_of[did] is not None})

    pil_map = {v: i for i, v in enumerate(pillars_tbl)}
    dir_map = {v: i for i, v in enumerate(dirs_tbl)}
    knd_map = {v: i for i, v in enumerate(kinds_tbl)}
    mod_map_idx = {v: i for i, v in enumerate(mods_tbl)}
    vocab_terms = [name_of[did] for did in vocab_ids]

    points_compact: List[List[Any]] = []
    decoded: List[Dict[str, Any]] = []
    for i, did in enumerate(selected):
        top_j = (
            [int(j) for j in np.argsort(-X_tf[i])[:4] if X_tf[i, j] > 0.0]
            if V > 0
            else []
        )
        nbr5 = [int(j) for j in nn_hi[i, :5]]
        cl_i = int(cluster_idx_of[did]) if 0 <= did < len(cluster_idx_of) else -1
        cl_id = clusters_tbl[cl_i] if 0 <= cl_i < len(clusters_tbl) else None
        mod_s = mod_of[did]
        mod_i = mod_map_idx[mod_s] if mod_s is not None else -1
        line_no = line_of_id.get(did)
        px, py = round(float(pca2[i, 0]), 4), round(float(pca2[i, 1]), 4)
        ux, uy = round(float(knn2[i, 0]), 4), round(float(knn2[i, 1]), 4)
        short = short_decl_name(name_of[did])
        dom_v = int(sub_sz[did]) if sub_sz[did] > 0 else 1

        if dk_ids and did in dk_ids:
            hyg = 1
        elif vn_of[did] == 1 and kind_of[did] in ("thm", "def"):
            hyg = 2
        elif drifts[i] >= 0.70:
            hyg = 3
        else:
            hyg = 0

        points_compact.append([
            name_of[did],
            short,
            knd_map[display_kinds[i]],
            dom_v,
            pil_map[pillars_list[i]],
            dir_map[dir_tops[i]],
            cl_i,
            mod_i,
            line_no,
            px, py,
            ux, uy,
            top_j,
            nbr5,
            drifts[i],
            type_ratios[i],
            sim_nn1_list[i],
            uniq_list[i],
            direct_lib_ratios[i],
            dup_counts[i],
            hyg,
        ])
        decoded.append({
            "name": name_of[did],
            "short": short,
            "kind": display_kinds[i],
            "dom": dom_v,
            "pillar": pillars_list[i],
            "dir_top": dir_tops[i],
            "cluster_id": cl_id,
            "mod": mod_s,
            "line": line_no,
            "px": px,
            "py": py,
            "ux": ux,
            "uy": uy,
            "top_terms": [vocab_terms[j] for j in top_j],
            "nn_idx": nbr5,
            "drift": drifts[i],
            "type_ratio": type_ratios[i],
            "sim_nn1": sim_nn1_list[i],
            "uniq": uniq_list[i],
            "lib_sim": direct_lib_ratios[i],
            "dup_count": dup_counts[i],
            "hygiene_flag": HYGIENE_FLAGS[hyg],
        })

    return {
        "count": n,
        "svd_explained_variance_ratios": exp_ratios,
        "svd_explained_variance_sum": exp_sum,
        "metrics": {
            "pca2": m_pca,
            "knn2": m_knn,
            "drift": drift_stats,
        },
        "tables": {
            "pillars": pillars_tbl,
            "dirs": dirs_tbl,
            "kinds": kinds_tbl,
            "clusters": clusters_tbl,
            "mods": mods_tbl,
            "vocab_terms": vocab_terms,
            "hygiene_flags": list(HYGIENE_FLAGS),
        },
        "fields": base_fields,
        "points": points_compact,
        "_decoded": decoded,
    }


def decode_layer_points(layer: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Expand compact columnar/indexed rows of a layer into plain dicts."""
    tables = layer.get("tables", {})
    fields = layer.get("fields", [])
    pillars = tables.get("pillars", [])
    dirs = tables.get("dirs", [])
    kinds = tables.get("kinds", [])
    clusters = tables.get("clusters", [])
    mods = tables.get("mods", [])
    vocab = tables.get("vocab_terms", [])
    hyg_tbl = tables.get("hygiene_flags", list(HYGIENE_FLAGS))
    status_tbl = tables.get("statuses", list(SOURCE_STATUSES))

    out: List[Dict[str, Any]] = []
    for row in layer.get("points", []):
        raw = dict(zip(fields, row))
        cl_i = raw.get("cluster_idx", -1)
        mod_i = raw.get("mod_idx", -1)
        item: Dict[str, Any] = {
            "name": raw["name"],
            "short": raw["short"],
            "kind": kinds[raw["kind_idx"]] if 0 <= raw.get("kind_idx", -1) < len(kinds) else "other",
            "dom": raw["dom"],
            "pillar": pillars[raw["pillar_idx"]] if 0 <= raw.get("pillar_idx", -1) < len(pillars) else "MAIN",
            "dir_top": dirs[raw["dir_idx"]] if 0 <= raw.get("dir_idx", -1) < len(dirs) else "<root>",
            "cluster_id": clusters[cl_i] if (0 <= cl_i < len(clusters)) else None,
            "mod": raw["mod"] if "mod" in raw else (mods[mod_i] if 0 <= mod_i < len(mods) else None),
            "line": raw.get("line"),
            "px": raw["px"],
            "py": raw["py"],
            "ux": raw["ux"],
            "uy": raw["uy"],
            "top_terms": [vocab[j] for j in raw.get("top_term_idxs", []) if 0 <= j < len(vocab)],
            "nn_idx": list(raw.get("nn_idx", [])),
            "drift": raw["drift"],
        }
        if "type_ratio" in raw:
            item["type_ratio"] = raw["type_ratio"]
        if "id" in raw:
            item["id"] = raw["id"]
        if "label" in raw:
            item["label"] = raw["label"]
        for opt_k in ("sim_nn1", "uniq", "lib_sim", "dup_count", "clone_count", "fan_in", "loc", "decls", "comment_pct", "sorry_count"):
            if opt_k in raw:
                item[opt_k] = raw[opt_k]
        if "hygiene_flag" in raw:
            hi = int(raw["hygiene_flag"])
            item["hygiene_flag"] = hyg_tbl[hi] if 0 <= hi < len(hyg_tbl) else "clean"
            item["hygiene_flag_idx"] = hi
        if "status_idx" in raw:
            si = int(raw["status_idx"])
            item["status"] = status_tbl[si] if 0 <= si < len(status_tbl) else "clean"
            item["status_idx"] = si
        out.append(item)
    return out


# ---------------------------------------------------------------------------
# Pure-Python 512x512 Preview PNG Renderer
# ---------------------------------------------------------------------------

def _draw_line_aa(
    canvas: List[bytearray],
    width: int,
    height: int,
    x0: float,
    y0: float,
    x1: float,
    y1: float,
    rgb: Tuple[int, int, int],
    alpha: float,
) -> None:
    steps = max(1, int(math.hypot(x1 - x0, y1 - y0)))
    for s in range(steps + 1):
        t = s / float(steps)
        px = int(round(x0 + (x1 - x0) * t))
        py = int(round(y0 + (y1 - y0) * t))
        if 0 <= py < height:
            atlas._blend_pixel(canvas[py], px, width, rgb, alpha)


def _draw_disc(
    canvas: List[bytearray],
    width: int,
    height: int,
    cx: float,
    cy: float,
    radius: float,
    rgb: Tuple[int, int, int],
    alpha: float = 0.90,
) -> None:
    r_ceil = int(math.ceil(radius + 0.5))
    ix, iy = int(round(cx)), int(round(cy))
    for dy in range(-r_ceil, r_ceil + 1):
        py = iy + dy
        if not (0 <= py < height):
            continue
        row = canvas[py]
        for dx in range(-r_ceil, r_ceil + 1):
            px = ix + dx
            if not (0 <= px < width):
                continue
            d = math.hypot((px - cx), (py - cy))
            if d <= radius + 0.4:
                edge_a = alpha * min(1.0, max(0.0, (radius + 0.4 - d) / 0.9))
                atlas._blend_pixel(row, px, width, rgb, edge_a)


def render_embedding_png(
    embedding_doc: Dict[str, Any],
    out_path: str,
    width: int = 512,
    height: int = 512,
) -> Dict[str, Any]:
    """Render a crisp `512x512` `knn2` preview PNG colored by proof pillar."""
    bg = (10, 12, 18)
    canvas: List[bytearray] = [
        bytearray([bg[0], bg[1], bg[2]] * width) for _ in range(height)
    ]

    # Subtle crosshair grid
    mid_x, mid_y = width // 2, height // 2
    for px in range(width):
        if (px % 4) < 2:
            atlas._blend_pixel(canvas[mid_y], px, width, (70, 82, 110), 0.35)
    for py in range(height):
        if (py % 4) < 2:
            atlas._blend_pixel(canvas[py], mid_x, width, (70, 82, 110), 0.35)

    lm_layer = embedding_doc.get("layers", {}).get("landmarks", {})
    pts = decode_layer_points(lm_layer)
    if not pts:
        pts = decode_layer_points(embedding_doc.get("layers", {}).get("clusters_141", {}))

    pad = 24
    span_x = width - 2 * pad
    span_y = height - 2 * pad

    def _to_px(ux: float, uy: float) -> Tuple[float, float]:
        return pad + 0.5 * (ux + 1.0) * span_x, pad + 0.5 * (1.0 - uy) * span_y

    # Faint nearest-neighbor threads for top hubs
    top_hubs = sorted(range(len(pts)), key=lambda i: (-pts[i]["dom"], i))[:60]
    for i in top_hubs:
        x0, y0 = _to_px(pts[i]["ux"], pts[i]["uy"])
        rgb = _PILLAR_RGB.get(pts[i]["pillar"], (160, 180, 210))
        for j in pts[i].get("nn_idx", [])[:2]:
            if 0 <= j < len(pts):
                x1, y1 = _to_px(pts[j]["ux"], pts[j]["uy"])
                _draw_line_aa(canvas, width, height, x0, y0, x1, y1, rgb, 0.14)

    # Scatter dots (smaller background first, larger hubs on top)
    order = sorted(range(len(pts)), key=lambda i: (pts[i]["dom"], i))
    for i in order:
        p = pts[i]
        cx, cy = _to_px(p["ux"], p["uy"])
        rgb = _PILLAR_RGB.get(p["pillar"], (180, 195, 220))
        r = 1.6 if p["dom"] < 1000 else (2.4 if p["dom"] < 10000 else 3.8)
        alpha = 0.78 if p["dom"] < 1000 else 0.92
        _draw_disc(canvas, width, height, cx, cy, r, rgb, alpha=alpha)

    # Top-left compact legend
    legend_tags = ["A", "D", "C", "B", "DM", "LIT", "BR"]
    present_pils = {p["pillar"] for p in pts}
    lx = 10
    for tag in legend_tags:
        if tag in present_pils:
            rgb = _PILLAR_RGB.get(tag, (200, 210, 230))
            _draw_disc(canvas, width, height, lx + 3, 11, 3.0, rgb, 0.95)
            atlas._draw_text_5x7(canvas, width, height, lx + 9, 8, tag, (230, 238, 255))
            lx += 14 + len(tag) * 6

    png_bytes = atlas.encode_png_rgb(width, height, canvas)
    os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
    with open(out_path, "wb") as f:
        f.write(png_bytes)
    return {"width": width, "height": height, "bytes": len(png_bytes)}


# ---------------------------------------------------------------------------
# Unified Orchestrator & CLI
# ---------------------------------------------------------------------------

def _resolve_private_and_fallback_lines(
    ldb: sqlite3.Connection,
    need_ids: Set[int],
    n_total: int,
    name_of: Sequence[str],
    mod_of: Sequence[Optional[str]],
    src_id_of: Sequence[int],
    line_of_id: Dict[int, int],
    lean_kind_by_id: Dict[int, str],
) -> None:
    """Populate `line_of_id` and `lean_kind_by_id` from `leanre.db` (including `_private.` decls)."""
    sid_to_did: Dict[int, List[int]] = collections.defaultdict(list)
    by_mod_need: Dict[str, List[int]] = collections.defaultdict(list)
    fallback_names: Dict[str, List[int]] = collections.defaultdict(list)

    for d_i in need_ids:
        if not (0 <= d_i < n_total):
            continue
        sid = int(src_id_of[d_i])
        if sid >= 0:
            sid_to_did[sid].append(d_i)
        elif mod_of[d_i]:
            by_mod_need[str(mod_of[d_i])].append(d_i)
        else:
            fallback_names[name_of[d_i]].append(d_i)

    sids_list = sorted(sid_to_did.keys())
    for i in range(0, len(sids_list), 400):
        chunk = sids_list[i : i + 400]
        qm = ",".join("?" for _ in chunk)
        for sid_v, kd_v, lno_v in ldb.execute(
            f"SELECT id, kind, line_no FROM declarations WHERE id IN ({qm})", chunk
        ):
            for d_i in sid_to_did[int(sid_v)]:
                line_of_id[d_i] = int(lno_v)
                if str(kd_v) in ("structure", "class"):
                    lean_kind_by_id[d_i] = str(kd_v)

    # Indexed lookup by `module` for `_private.` and `src_decl_id IS NULL` decls
    for mod_s, dids in sorted(by_mod_need.items()):
        mod_rows = ldb.execute(
            "SELECT name, kind, line_no FROM declarations WHERE module = ? ORDER BY line_no ASC",
            (mod_s,),
        ).fetchall()
        if not mod_rows:
            for d_i in dids:
                fallback_names[name_of[d_i]].append(d_i)
            continue
        exact_map: Dict[str, Tuple[str, int]] = {}
        leaf_map: Dict[str, Tuple[str, int]] = {}
        for nm_v, kd_v, lno_v in mod_rows:
            s_nm = str(nm_v)
            exact_map.setdefault(s_nm, (str(kd_v), int(lno_v)))
            leaf_map.setdefault(s_nm.rsplit(".", 1)[-1], (str(kd_v), int(lno_v)))
        for d_i in dids:
            if d_i in line_of_id:
                continue
            raw_nm = name_of[d_i]
            inner = raw_nm.split(".0.", 1)[1] if (raw_nm.startswith("_private.") and ".0." in raw_nm) else raw_nm
            leaf = inner.rsplit(".", 1)[-1]
            hit = exact_map.get(inner) or exact_map.get(raw_nm) or exact_map.get(leaf) or leaf_map.get(leaf)
            if hit is not None:
                kd_v, lno_v = hit
                line_of_id[d_i] = lno_v
                if kd_v in ("structure", "class"):
                    lean_kind_by_id[d_i] = kd_v

    fnames = sorted(fallback_names.keys())
    for i in range(0, len(fnames), 400):
        chunk = fnames[i : i + 400]
        qm = ",".join("?" for _ in chunk)
        for nm_v, kd_v, lno_v in ldb.execute(
            f"SELECT name, kind, line_no FROM declarations WHERE name IN ({qm})", chunk
        ):
            for d_i in fallback_names[str(nm_v)]:
                line_of_id.setdefault(d_i, int(lno_v))
                if str(kd_v) in ("structure", "class"):
                    lean_kind_by_id[d_i] = str(kd_v)


def run_embedding(
    kernel_db_path: str,
    leanre_db_path: Optional[str] = None,
    cluster_labels_path: Optional[str] = None,
    portability_path: Optional[str] = None,
    out_json_path: Optional[str] = None,
    png_path: Optional[str] = None,
    max_landmarks: int = 1800,
    svd_dim: int = 24,
    knn_k: int = 15,
    knn_steps: int = 180,
    seed: int = 42,
    workers: int = 0,
) -> Dict[str, Any]:
    """Compute the 2-layer TF-IDF + SVD(k=24) + `pca2`/`knn2` proof map."""
    t0 = time.perf_counter()

    cluster_labels_map: Dict[str, Dict[str, Any]] = {}
    if cluster_labels_path and os.path.isfile(os.path.realpath(cluster_labels_path)):
        with open(cluster_labels_path, "r", encoding="utf-8") as f:
            c141_doc = json.load(f)
        for item in c141_doc.get("clusters", []):
            cid = item.get("cluster_id")
            if cid:
                cluster_labels_map[str(cid)] = item

    portability_ids: List[int] = []
    if portability_path and os.path.isfile(os.path.realpath(portability_path)):
        with open(portability_path, "r", encoding="utf-8") as f:
            pg_doc = json.load(f)
        for item in pg_doc.get("targets", []):
            if item.get("decl_id") is not None:
                portability_ids.append(int(item["decl_id"]))

    with contextlib.closing(atlas.connect_ro(kernel_db_path, mmap_bytes=8_589_934_592)) as con:
        dom_info = atlas.compute_dom_dfs(con, tree_id=0, n_bins=256)
        max_id = dom_info["max_decl_id"]
        n_total = max_id + 1 if max_id >= 0 else 0

        if n_total == 0:
            empty_doc: Dict[str, Any] = {
                "schema": SCHEMA_VERSION,
                "inputs": {"kernel_db": atlas.safe_display_path(kernel_db_path)},
                "runtime_sec": round(time.perf_counter() - t0, 3),
                "svd_dim": svd_dim,
                "knn_k": knn_k,
                "knn_steps": knn_steps,
                "seed": seed,
                "layers": {
                    "clusters_141": _build_clusters_layer(
                        kernel_db_path, [], np.zeros(0, dtype=np.int32), [], 0, [], [], {},
                    ),
                    "landmarks": _build_landmarks_layer(
                        con, [], set(), set(), 0, [], [], [], [], [], [], [], [], [], [], [], np.zeros(0, dtype=np.int32), [], {}, {},
                    ),
                },
            }
            if out_json_path:
                _write_compact_json(empty_doc, out_json_path)
            return empty_doc

        name_of: List[str] = [""] * n_total
        kind_of: List[str] = [""] * n_total
        tn_of = array.array("I", [0]) * n_total
        vn_of = array.array("I", [0]) * n_total
        fi_of = array.array("I", [0]) * n_total
        et_of = array.array("I", [0]) * n_total
        ev_of = array.array("I", [0]) * n_total
        flags_of = array.array("I", [0]) * n_total
        live_of = bytearray(n_total)
        sighash_of: List[Optional[str]] = [None] * n_total

        for did, nm, kd, tn, vn, fi, fot, fov, flg, lm, sh in con.execute(
            "SELECT id, name, kind, type_nodes, value_nodes, fan_in, fan_out_type, fan_out_value, flags, live_mask, sighash FROM decls"
        ):
            d_i = int(did)
            name_of[d_i] = str(nm)
            kind_of[d_i] = str(kd)
            tn_of[d_i] = int(tn)
            vn_of[d_i] = int(vn)
            fi_of[d_i] = int(fi)
            et_of[d_i] = int(fot)
            ev_of[d_i] = int(fov)
            flags_of[d_i] = int(flg)
            live_of[d_i] = 1 if lm != 0 else 0
            if sh:
                sighash_of[d_i] = str(sh)

        mod_of: List[Optional[str]] = [None] * n_total
        meth_of: List[Optional[str]] = [None] * n_total
        src_id_of = array.array("i", [-1]) * n_total
        if atlas._table_exists(con, "decl_module"):
            for did, mod, meth, sid in con.execute(
                "SELECT decl_id, module, method, src_decl_id FROM decl_module"
            ):
                d_i = int(did)
                if 0 <= d_i < n_total:
                    mod_of[d_i] = mod
                    meth_of[d_i] = meth
                    if sid is not None:
                        src_id_of[d_i] = int(sid)

        has_src_repo = "src_repo" in atlas._table_columns(con, "decls")
        srepo_map: Dict[int, str] = {}
        if has_src_repo:
            for did, sr in con.execute("SELECT id, src_repo FROM decls WHERE src_repo IS NOT NULL"):
                srepo_map[int(did)] = str(sr)

        origin_of: List[str] = ["project"] * n_total
        for d_i in range(n_total):
            nm = name_of[d_i]
            if nm:
                # Infer project module on `_private.<mod>.0.<decl>` if `decl_module` missed it
                if mod_of[d_i] is None and nm.startswith("_private.") and ".0." in nm:
                    cand_mod = nm[len("_private."):].split(".0.", 1)[0]
                    if cand_mod and not cand_mod.startswith(("Init.", "Lean.", "Std.", "Batteries.", "Mathlib.")):
                        mod_of[d_i] = cand_mod
                origin_of[d_i] = atlas.classify_decl_origin(
                    nm, mod_of[d_i], meth_of[d_i], srepo_map.get(d_i)
                )

        # k1n signature duplication counts and library k1n matches
        k1n_counts: collections.Counter[str] = collections.Counter()
        lib_sighashes: Set[str] = set()
        is_lib_arr = np.zeros(n_total, dtype=np.uint8)
        for d_i in range(n_total):
            is_lib = origin_of[d_i] in ("mathlib4", "lean4", "batteries")
            if is_lib:
                is_lib_arr[d_i] = 1
            sh = sighash_of[d_i]
            if sh:
                if is_lib:
                    lib_sighashes.add(sh)
                if live_of[d_i] and name_of[d_i] and not is_compiler_aux(name_of[d_i]):
                    k1n_counts[sh] += 1

        dup_count_of_id = array.array("I", [1]) * n_total
        lib_match_of_id = bytearray(n_total)
        for d_i in range(n_total):
            sh = sighash_of[d_i]
            if sh:
                dup_count_of_id[d_i] = max(1, int(k1n_counts.get(sh, 1)))
                if sh in lib_sighashes:
                    lib_match_of_id[d_i] = 1

        # `decide_kernel` taint IDs from `taint_sources` or `flags` (`F_OF_DECIDE = 2`)
        dk_ids: Set[int] = set()
        if atlas._table_exists(con, "taint_sources"):
            ts_cols = atlas._table_columns(con, "taint_sources")
            if "class" in ts_cols and "decl_id" in ts_cols:
                for (tdid,) in con.execute(
                    "SELECT decl_id FROM taint_sources WHERE class IN ('decide_kernel', 'decide_kernel_pattern')"
                ):
                    if tdid is not None:
                        dk_ids.add(int(tdid))
        for d_i in range(n_total):
            if (flags_of[d_i] & 2) != 0:
                dk_ids.add(d_i)

        # Load dom (tree_id=0)
        children: Dict[int, List[int]] = collections.defaultdict(list)
        sub_sz = array.array("I", [0]) * n_total
        dom_roots_top: List[int] = []
        if atlas._table_exists(con, "dom"):
            dom_rows = con.execute(
                "SELECT decl_id, idom, subtree_size FROM dom WHERE tree_id=0"
            ).fetchall()
        else:
            dom_rows = []

        if dom_rows:
            for did, idom, sz in dom_rows:
                d_i = int(did)
                sub_sz[d_i] = int(sz)
                if idom is None:
                    dom_roots_top.append(d_i)
                else:
                    children[int(idom)].append(d_i)
        else:
            for d_i in range(n_total):
                if live_of[d_i]:
                    sub_sz[d_i] = 1
                    dom_roots_top.append(d_i)

        # Map DFS index -> atlas region key
        reg_by_dfs = [""] * max(0, dom_info["n_live"])
        for reg in dom_info["regions"]:
            rk = str(reg["key"])
            for pos in range(int(reg["dfs_start"]), int(reg["dfs_end"])):
                reg_by_dfs[pos] = rk

        raw_clusters, cluster_idx_of = _build_cluster_partition(
            con=con,
            n_total=n_total,
            name_of=name_of,
            kind_of=kind_of,
            live_of=live_of,
            fan_in_of=fi_of,
            mod_of=mod_of,
            sub_sz=sub_sz,
            children=children,
            dom_roots_top=dom_roots_top,
            tin_by_id=dom_info["tin_by_id"],
            reg_by_dfs=reg_by_dfs,
            cluster_labels_map=cluster_labels_map,
        )

        # Compute per-cluster average type_ratio from member fan_out_type / fan_out_value
        for cl in raw_clusters:
            et_sum = 0
            ev_sum = 0
            for d_i in cl["members"]:
                et_sum += et_of[d_i]
                ev_sum += ev_of[d_i]
            cl["type_ratio"] = et_sum / float(max(1, et_sum + ev_sum))

        # External / library vocabulary pool (filtering typeclass-instance boilerplate!)
        ext_ids = [
            d_i
            for d_i in range(n_total)
            if name_of[d_i]
            and origin_of[d_i] != "project"
            and not is_compiler_aux(name_of[d_i])
            and not name_of[d_i].startswith("_private.")
            and not is_typeclass_boilerplate(name_of[d_i], kind_of[d_i])
        ]
        if len(ext_ids) < 12:
            # Small/synthetic corpus fallback: include all non-aux, non-boilerplate declarations
            ext_ids = [
                d_i
                for d_i in range(n_total)
                if name_of[d_i]
                and not is_compiler_aux(name_of[d_i])
                and not is_typeclass_boilerplate(name_of[d_i], kind_of[d_i])
            ]
        ext_vocab_set = set(ext_ids)

        # Top external candidates for cluster-level matrix (fast O(1) lookup array)
        ext_ranked = sorted(ext_ids, key=lambda d: (-fi_of[d], d))
        cluster_cand_ext = ext_ranked[:3000]

        # Optional `leanre.db` enrichment (structures + line numbers + forensic_hits)
        lean_kind_by_id: Dict[int, str] = {}
        line_of_id: Dict[int, int] = {}
        has_ldb = bool(leanre_db_path and os.path.isfile(os.path.realpath(leanre_db_path)))
        if has_ldb and leanre_db_path:
            with contextlib.closing(atlas.connect_ro(leanre_db_path)) as ldb:
                if atlas._table_exists(ldb, "declarations"):
                    struct_sids = {
                        int(r[0])
                        for r in ldb.execute("SELECT id FROM declarations WHERE kind IN ('structure', 'class')")
                    }
                    struct_names = {
                        str(r[0]): str(r[1])
                        for r in ldb.execute("SELECT name, kind FROM declarations WHERE kind IN ('structure', 'class')")
                    }
                    for d_i in range(n_total):
                        sid = int(src_id_of[d_i])
                        if sid >= 0 and sid in struct_sids:
                            lean_kind_by_id[d_i] = "structure"
                        elif name_of[d_i] in struct_names:
                            lean_kind_by_id[d_i] = struct_names[name_of[d_i]]
                    selected, dom1k_set = _select_landmarks(
                        n_total=n_total,
                        name_of=name_of,
                        kind_of=kind_of,
                        live_of=live_of,
                        fan_in_of=fi_of,
                        tn_of=tn_of,
                        sub_sz=sub_sz,
                        mod_of=mod_of,
                        origin_of=origin_of,
                        raw_clusters=raw_clusters,
                        lean_kind_by_id=lean_kind_by_id,
                        portability_ids=portability_ids,
                        max_landmarks=max_landmarks,
                    )
                    need_ids = set(selected) | {int(c["root_decl_id"]) for c in raw_clusters}
                    _resolve_private_and_fallback_lines(
                        ldb=ldb,
                        need_ids=need_ids,
                        n_total=n_total,
                        name_of=name_of,
                        mod_of=mod_of,
                        src_id_of=src_id_of,
                        line_of_id=line_of_id,
                        lean_kind_by_id=lean_kind_by_id,
                    )
                else:
                    selected, dom1k_set = _select_landmarks(
                        n_total=n_total,
                        name_of=name_of,
                        kind_of=kind_of,
                        live_of=live_of,
                        fan_in_of=fi_of,
                        tn_of=tn_of,
                        sub_sz=sub_sz,
                        mod_of=mod_of,
                        origin_of=origin_of,
                        raw_clusters=raw_clusters,
                        lean_kind_by_id=lean_kind_by_id,
                        portability_ids=portability_ids,
                        max_landmarks=max_landmarks,
                    )
                if atlas._table_exists(ldb, "forensic_hits"):
                    dk_mod_decls: Set[Tuple[str, str]] = set()
                    dk_mod_lines: Set[Tuple[str, int]] = set()
                    for hmod, hline, hdname in ldb.execute(
                        "SELECT module, line_no, decl_name FROM forensic_hits WHERE tag='decide_kernel'"
                    ):
                        if hmod and hdname:
                            dk_mod_decls.add((str(hmod), str(hdname)))
                        if hmod and hline:
                            dk_mod_lines.add((str(hmod), int(hline)))
                    if dk_mod_decls or dk_mod_lines:
                        for d_i in set(selected) | {int(c["root_decl_id"]) for c in raw_clusters}:
                            m_s = mod_of[d_i]
                            if not m_s:
                                continue
                            inner = name_of[d_i].split(".0.", 1)[1] if ".0." in name_of[d_i] else name_of[d_i]
                            l_v = line_of_id.get(d_i)
                            if (m_s, name_of[d_i]) in dk_mod_decls or (m_s, inner) in dk_mod_decls or (l_v is not None and (m_s, l_v) in dk_mod_lines):
                                dk_ids.add(d_i)
        else:
            selected, dom1k_set = _select_landmarks(
                n_total=n_total,
                name_of=name_of,
                kind_of=kind_of,
                live_of=live_of,
                fan_in_of=fi_of,
                tn_of=tn_of,
                sub_sz=sub_sz,
                mod_of=mod_of,
                origin_of=origin_of,
                raw_clusters=raw_clusters,
                lean_kind_by_id=lean_kind_by_id,
                portability_ids=portability_ids,
                max_landmarks=max_landmarks,
            )

        clusters_layer = _build_clusters_layer(
            kernel_db_path=kernel_db_path,
            raw_clusters=raw_clusters,
            cluster_idx_of=cluster_idx_of,
            cand_ext_ids=cluster_cand_ext,
            n_total=n_total,
            name_of=name_of,
            type_ratio_of=[0.0] * n_total,
            line_of_id=line_of_id,
            is_lib_arr=is_lib_arr,
            dup_count_of_id=dup_count_of_id,
            lib_match_of_id=lib_match_of_id,
            dk_ids=dk_ids,
            vn_of=vn_of,
            kind_of=kind_of,
            max_vocab=768,
            k_svd=svd_dim,
            k_nn=knn_k,
            n_steps=knn_steps,
            seed=seed,
            workers=workers,
        )
        landmarks_layer = _build_landmarks_layer(
            con=con,
            selected=selected,
            dom1k_set=dom1k_set,
            ext_vocab_set=ext_vocab_set,
            n_total=n_total,
            name_of=name_of,
            kind_of=kind_of,
            tn_of=tn_of,
            vn_of=vn_of,
            et_of=et_of,
            ev_of=ev_of,
            sub_sz=sub_sz,
            mod_of=mod_of,
            origin_of=origin_of,
            tin_by_id=dom_info["tin_by_id"],
            reg_by_dfs=reg_by_dfs,
            cluster_idx_of=cluster_idx_of,
            raw_clusters=raw_clusters,
            lean_kind_by_id=lean_kind_by_id,
            line_of_id=line_of_id,
            is_lib_arr=is_lib_arr,
            dup_count_of_id=dup_count_of_id,
            lib_match_of_id=lib_match_of_id,
            dk_ids=dk_ids,
            max_vocab=1024,
            k_svd=svd_dim,
            k_nn=knn_k,
            n_steps=knn_steps,
            seed=seed,
        )

    # Pop internal `_decoded` before JSON serialization (keep for optional PNG render)
    cl_decoded = clusters_layer.pop("_decoded", [])
    lm_decoded = landmarks_layer.pop("_decoded", [])

    doc: Dict[str, Any] = {
        "schema": SCHEMA_VERSION,
        "inputs": {
            "kernel_db": atlas.safe_display_path(kernel_db_path),
            "leanre_db": atlas.safe_display_path(leanre_db_path) if has_ldb else None,
            "numpy_version": str(np.__version__) if np is not None else "stdlib",
        },
        "runtime_sec": round(time.perf_counter() - t0, 3),
        "svd_dim": int(svd_dim),
        "knn_k": int(knn_k),
        "knn_steps": int(knn_steps),
        "seed": int(seed),
        "layers": {
            "clusters_141": clusters_layer,
            "landmarks": landmarks_layer,
        },
    }

    if out_json_path:
        _write_compact_json(doc, out_json_path)

    if png_path:
        render_embedding_png(doc, png_path, width=512, height=512)

    # Keep decoded accessible in Python return value only? No, keep return value identical to JSON!
    _ = (cl_decoded, lm_decoded)
    return doc


# ---------------------------------------------------------------------------
# Source-Only Module Embedding (`build_source_embedding`)
# ---------------------------------------------------------------------------

_SRC_IMPORT_RE = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z_][^\s]*)"
)
_SRC_OPEN_RE = re.compile(r"^\s*open\s+(.+)$")
_SRC_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
_SRC_CAMEL_RE = re.compile(r"[A-Z]+(?=[A-Z][a-z]|\b)|[A-Z]?[a-z]+|\d+")

_EXT_IMPORT_PREFIXES = (
    "Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq", "ProofWidgets",
)

_SRC_STOP_WORDS = frozenset({
    "theorem", "lemma", "def", "abbrev", "structure", "class", "instance", "inductive",
    "opaque", "axiom", "noncomputable", "private", "protected", "unsafe", "partial",
    "nonrec", "scoped", "local", "where", "extends", "deriving", "fun", "let", "have",
    "show", "from", "with", "that", "this", "some", "none", "true", "false", "prop",
    "type", "sort", "nat", "int", "bool", "char", "string", "unit", "punit", "empty",
    "option", "list", "set", "fin", "and", "not", "iff", "exists", "forall", "for",
    "main", "basic", "defs", "lemmas", "helper", "helpers", "aux", "proof", "spec",
    "statement", "step", "part", "case", "cases", "thm", "lem", "hyp", "hyps", "data",
    "eq", "ne", "le", "lt", "ge", "gt", "add", "mul", "sub", "div", "neg", "inv",
    "zero", "one", "two", "of", "by", "in", "at", "to", "on", "is", "as", "if",
    "then", "else", "match", "do", "return", "pure", "classical", "decidable",
})

_FORBIDDEN_HOST_PATH_RE = re.compile(
    r"(?:"
    + "/" + "usr" + "/" + "local" + "/" + r"[^/\s]+/home/"
    + "|" + "/" + "usr" + "/" + "local" + "/" + "google"
    + "|" + "/" + "ho" + r"me/[A-Za-z0-9_.-]+"
    + "|" + "/" + "Us" + r"ers/[A-Za-z0-9_.-]+"
    + ")"
)


def _safe_input_label(path: Optional[str]) -> Optional[str]:
    if not path:
        return None
    disp = atlas.safe_display_path(path)
    if disp and _FORBIDDEN_HOST_PATH_RE.search(disp):
        return os.path.basename(disp)
    return disp


def _is_challenge_module(file_path: str, module_name: str) -> bool:
    fp = str(file_path or "").replace("\\", "/").lower()
    base = os.path.basename(fp)
    mod_low = str(module_name or "").lower()
    if "comparatorchallenges/" in fp or "comparatorchallenges." in mod_low:
        return True
    if "challenge" in base or "challenge" in mod_low.rsplit(".", 1)[-1]:
        return True
    if base == "celllayertheorems.lean" or mod_low == "celllayertheorems":
        return True
    return False


def _short_module_name(mod_name: str) -> str:
    parts = mod_name.split(".")
    if len(parts) <= 1:
        return mod_name
    if len(parts) >= 2 and parts[-1] in ("Basic", "Defs", "Lemmas", "Aux", "Core", "Main", "Statement", "Proof"):
        return f"{parts[-2]}.{parts[-1]}"
    return parts[-1]


def _scan_lean_file_meta(full_path: str) -> Tuple[int, int, List[str], List[str]]:
    """Fast single-pass Lean 4 reader returning `(lines_wc, comment_lines, imports, opens)`."""
    try:
        with open(full_path, "rb") as f:
            raw = f.read()
    except OSError:
        return 0, 0, [], []

    if not raw:
        return 0, 0, [], []

    lines_wc = raw.count(b"\n")
    if lines_wc == 0 and raw:
        lines_wc = 1

    has_comments = (b"--" in raw) or (b"/-" in raw)
    text = raw.decode("utf-8", errors="replace")

    comment_lines = 0
    if has_comments:
        n = len(text)
        i = 0
        in_str = False
        depth = 0
        line_has_comment = False
        code_chars: List[str] = []
        while i < n:
            ch = text[i]
            if ch == "\n":
                if line_has_comment or depth > 0:
                    comment_lines += 1
                line_has_comment = depth > 0
                code_chars.append("\n")
                i += 1
                continue
            if depth > 0:
                if ch == "/" and i + 1 < n and text[i + 1] == "-":
                    depth += 1
                    i += 2
                elif ch == "-" and i + 1 < n and text[i + 1] == "/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            elif in_str:
                code_chars.append(ch)
                if ch == "\\" and i + 1 < n:
                    code_chars.append(text[i + 1])
                    i += 2
                elif ch == '"':
                    in_str = False
                    i += 1
                else:
                    i += 1
            else:
                if ch == '"':
                    in_str = True
                    code_chars.append(ch)
                    i += 1
                elif ch == "/" and i + 1 < n and text[i + 1] == "-":
                    depth = 1
                    line_has_comment = True
                    i += 2
                elif ch == "-" and i + 1 < n and text[i + 1] == "-":
                    line_has_comment = True
                    j = text.find("\n", i)
                    if j == -1:
                        break
                    i = j
                else:
                    code_chars.append(ch)
                    i += 1
        if not text.endswith("\n") and (line_has_comment or depth > 0):
            comment_lines += 1
        clean_text = "".join(code_chars)
    else:
        clean_text = text

    imports: List[str] = []
    opens: List[str] = []
    # Imports and top-level opens sit near the top; scan lines fast
    for line in clean_text.splitlines():
        s = line.lstrip()
        if not s:
            continue
        if "import " in s:
            m = _SRC_IMPORT_RE.match(s)
            if m:
                imports.append(m.group(1))
                continue
        if s.startswith("open "):
            m = _SRC_OPEN_RE.match(s)
            if m:
                body = m.group(1).split("--", 1)[0].strip()
                if body.startswith("scoped "):
                    body = body[7:].strip()
                for part in body.split():
                    if part in ("in", "hiding", "renaming", "only") or part.startswith(("(", "{", "[")):
                        break
                    if re.match(r"^[A-Za-z_][\w.']*$", part):
                        opens.append(part)
    return lines_wc, comment_lines, imports, opens


def _tokenize_source_ident(ident: str) -> List[str]:
    """Extract clean math/domain tokens from a Lean identifier without boilerplate."""
    out: List[str] = []
    for seg in ident.split("."):
        if not seg or seg.startswith("_"):
            continue
        if seg[0].isupper() and len(seg) >= 3 and seg.lower() not in _SRC_STOP_WORDS:
            if not _TC_BOILERPLATE_RE.search(seg):
                out.append(seg)
        for part in seg.split("_"):
            for w in _SRC_CAMEL_RE.findall(part):
                wl = w.lower()
                if len(wl) >= 3 and not wl.isdigit() and wl not in _SRC_STOP_WORDS:
                    out.append(wl)
    return out


def _build_tfidf_svd_umap_generic(
    bags: Sequence[Dict[str, float]],
    dir_tops: Sequence[str],
    is_core_or_hub: Sequence[bool],
    dup_counts: Sequence[int],
    *,
    max_vocab: int = 512,
    svd_dim: int = 24,
    knn_k: int = 10,
    n_steps: int = 180,
    seed: int = 42,
    extra_feats: Optional[Sequence[Sequence[float]]] = None,
) -> Dict[str, Any]:
    """Vectorized (or pure-stdlib fallback) TF-IDF + SVD + pca2 + knn2 + metrics."""
    n = len(bags)
    if n == 0:
        return {
            "pca2": [[0.0, 0.0]] * 0,
            "knn2": [[0.0, 0.0]] * 0,
            "nn_hi": [],
            "vocab_terms": [],
            "top_term_idxs": [],
            "exp_ratios": [],
            "exp_sum": 0.0,
            "m_pca": {"knn_preservation": 1.0, "trustworthiness": 1.0},
            "m_knn": {"knn_preservation": 1.0, "trustworthiness": 1.0},
            "drifts": [],
            "drift_stats": {"k_neighbors": 0, "mean_drift_all": 0.0, "mean_drift_dom1k": 0.0, "dom1k_count": 0, "dom1k_nn1_diff_folder_pct": 0.0},
            "sim_nn1": [],
            "uniq": [],
        }

    df_ctr: collections.Counter[str] = collections.Counter()
    for bag in bags:
        for tok in bag:
            df_ctr[tok] += 1

    min_df = 2 if n >= 20 else 1
    max_df = int(0.85 * n) if n >= 8 else n
    term_score: Dict[str, float] = {}
    for tok, df in df_ctr.items():
        if df < min_df or df > max_df:
            continue
        idf = math.log((1.0 + n) / (1.0 + df))
        term_score[tok] = idf * df * (1.0 - df / float(max(1, n)))
    if not term_score and df_ctr:
        for tok, df in df_ctr.items():
            term_score[tok] = math.log((1.0 + n) / (1.0 + df)) * df

    vocab_terms = [tok for tok, _ in sorted(term_score.items(), key=lambda x: (-x[1], x[0]))[:max_vocab]]
    v_map = {tok: j for j, tok in enumerate(vocab_terms)}
    V = len(vocab_terms)

    if np is not None:
        X_tf = np.zeros((n, V), dtype=np.float64)
        if V > 0:
            idf_vec = np.array([math.log((1.0 + n) / (1.0 + df_ctr[tok])) for tok in vocab_terms], dtype=np.float64)
            for i, bag in enumerate(bags):
                for tok, w in bag.items():
                    j = v_map.get(tok)
                    if j is not None:
                        X_tf[i, j] = math.log1p(max(0.0, w)) * idf_vec[j]
            tf_norms = np.linalg.norm(X_tf, axis=1, keepdims=True)
            X_norm = X_tf / np.maximum(tf_norms, 1e-12)
        else:
            tf_norms = np.zeros((n, 1), dtype=np.float64)
            X_norm = np.ones((n, 2), dtype=np.float64) / math.sqrt(2.0)

        if extra_feats is not None and len(extra_feats) == n and len(extra_feats[0]) > 0:
            S_arr = np.asarray(extra_feats, dtype=np.float64).copy()
            for col in range(S_arr.shape[1]):
                mu = float(S_arr[:, col].mean())
                sd = float(S_arr[:, col].std())
                if sd > 1e-9:
                    S_arr[:, col] = (S_arr[:, col] - mu) / sd
            S_arr *= 0.12
            X = np.hstack([X_norm, S_arr])
        else:
            X = X_norm
        X = X / np.maximum(np.linalg.norm(X, axis=1, keepdims=True), 1e-12)

        U, S, _Vt = randomized_svd(X, k=svd_dim, seed=seed)
        Z_svd = U * S[None, :] if S.size > 0 else np.zeros((n, 2), dtype=np.float64)
        tot_ss = float(np.sum(X * X))
        exp_ratios = [round(float(sv * sv / tot_ss), 5) for sv in S] if tot_ss > 0 else []
        exp_sum = round(float(sum(exp_ratios)), 4)

        pca2 = normalize_2d_isotropic(Z_svd[:, :2] if Z_svd.shape[1] >= 2 else Z_svd)
        knn2, nn_hi, nn_sim = _knn2_umap_with_sim(Z_svd, pca2, k_nn=knn_k, n_steps=n_steps, seed=seed)
        m_pca = evaluate_embedding_quality(Z_svd, pca2, nn_hi)
        m_knn = evaluate_embedding_quality(Z_svd, knn2, nn_hi)
        top_term_idxs: List[List[int]] = [
            ([int(j) for j in np.argsort(-X_tf[i])[:4] if X_tf[i, j] > 0.0] if V > 0 and float(tf_norms[i, 0]) > 1e-12 else [])
            for i in range(n)
        ]
        pca2_py = [[round(float(pca2[i, 0]), 4), round(float(pca2[i, 1]), 4)] for i in range(n)]
        knn2_py = [[round(float(knn2[i, 0]), 4), round(float(knn2[i, 1]), 4)] for i in range(n)]
        nn5_py = [[int(j) for j in nn_hi[i, :5]] for i in range(n)]
    else:
        X_tf_py: List[List[float]] = [[0.0] * V for _ in range(n)]
        idf_py = [math.log((1.0 + n) / (1.0 + df_ctr[tok])) for tok in vocab_terms]
        X_rows: List[List[float]] = []
        for i, bag in enumerate(bags):
            row = X_tf_py[i]
            for tok, w in bag.items():
                j = v_map.get(tok)
                if j is not None:
                    row[j] = math.log1p(max(0.0, w)) * idf_py[j]
            nr = math.sqrt(sum(v * v for v in row))
            if V > 0:
                norm_row = [v / max(nr, 1e-12) for v in row]
            else:
                norm_row = [1.0 / math.sqrt(2.0), 1.0 / math.sqrt(2.0)]
            X_rows.append(norm_row)
        if extra_feats is not None and len(extra_feats) == n and len(extra_feats[0]) > 0:
            ncols = len(extra_feats[0])
            cols_norm: List[List[float]] = []
            for c_i in range(ncols):
                vals = [float(extra_feats[r_i][c_i]) for r_i in range(n)]
                mu = sum(vals) / n
                sd = math.sqrt(sum((v - mu) ** 2 for v in vals) / n)
                cols_norm.append([((v - mu) / sd if sd > 1e-9 else 0.0) * 0.12 for v in vals])
            for r_i in range(n):
                X_rows[r_i].extend(cols_norm[c_i][r_i] for c_i in range(ncols))
        for r_i in range(n):
            nr = max(1e-12, math.sqrt(sum(v * v for v in X_rows[r_i])))
            X_rows[r_i] = [v / nr for v in X_rows[r_i]]

        U_py, S_py, _Vt_py = randomized_svd(X_rows, k=svd_dim, seed=seed)
        Z_py = [[U_py[i][j] * S_py[j] for j in range(len(S_py))] for i in range(n)] if S_py else [[0.0, 0.0] for _ in range(n)]
        tot_ss = sum(sum(v * v for v in r) for r in X_rows)
        exp_ratios = [round(sv * sv / tot_ss, 5) for sv in S_py] if tot_ss > 0 else []
        exp_sum = round(sum(exp_ratios), 4)
        pca2_raw = normalize_2d_isotropic([r[:2] for r in Z_py])
        knn2_raw, nn_hi, nn_sim = _knn2_umap_with_sim(Z_py, pca2_raw, k_nn=knn_k, n_steps=n_steps, seed=seed)
        m_pca = evaluate_embedding_quality(Z_py, pca2_raw, nn_hi)
        m_knn = evaluate_embedding_quality(Z_py, knn2_raw, nn_hi)
        top_term_idxs = [
            [j for j, v in sorted(((j, X_tf_py[i][j]) for j in range(V) if X_tf_py[i][j] > 0.0), key=lambda x: (-x[1], x[0]))[:4]]
            for i in range(n)
        ]
        pca2_py = [[round(r[0], 4), round(r[1], 4)] for r in pca2_raw]
        knn2_py = [[round(r[0], 4), round(r[1], 4)] for r in knn2_raw]
        nn5_py = [list(nn_hi[i][:5]) for i in range(n)]

    drifts, drift_stats = compute_namespace_drift(nn_hi, dir_tops, is_core_or_hub, k_drift=10)
    sim_nn1_list, uniq_list = compute_sim_and_uniq(nn_sim, dup_counts)
    return {
        "pca2": pca2_py,
        "knn2": knn2_py,
        "nn5": nn5_py,
        "vocab_terms": vocab_terms,
        "top_term_idxs": top_term_idxs,
        "exp_ratios": exp_ratios,
        "exp_sum": exp_sum,
        "m_pca": m_pca,
        "m_knn": m_knn,
        "drifts": drifts,
        "drift_stats": drift_stats,
        "sim_nn1": sim_nn1_list,
        "uniq": uniq_list,
    }


def _select_source_modules(
    records: Sequence[Dict[str, Any]],
    max_points: int,
) -> List[int]:
    """Select up to `max_points` representative modules prioritizing entry, sorry, hubs, and diversity."""
    n = len(records)
    if n <= max_points:
        return list(range(n))

    selected: List[int] = []
    seen: Set[int] = set()

    def _add(idx: int) -> None:
        if idx not in seen and len(selected) < max_points:
            seen.add(idx)
            selected.append(idx)

    # 1. Entry roots and forensic-flagged modules (sorry, axiom, decide_kernel, etc.)
    for idx, r in enumerate(records):
        if r["bfs_depth"] == 0 or r["forensic_flags"] or r["sorry_count"] > 0 or r["is_challenge"]:
            _add(idx)

    # 2. Stratified top representative per directory (`dir_top`) so every subfolder appears
    by_dir: Dict[str, List[int]] = collections.defaultdict(list)
    for idx, r in enumerate(records):
        by_dir[r["dir_top"]].append(idx)
    for dt in sorted(by_dir.keys()):
        cands = sorted(
            by_dir[dt],
            key=lambda i: (-records[i]["fan_in"], -records[i]["dom"], -records[i]["loc"], records[i]["name"]),
        )
        _add(cands[0])

    # 3. Representative orphans up to 1/6 of budget
    orphan_cap = max(10, max_points // 6)
    orphans = [
        i for i, r in enumerate(records)
        if i not in seen and r["bfs_depth"] < 0
    ]
    orphans.sort(key=lambda i: (-records[i]["fan_in"], -records[i]["decls"], -records[i]["loc"], records[i]["name"]))
    for i in orphans[:orphan_cap]:
        if len(selected) >= max_points:
            break
        _add(i)

    # 4. Remaining slots by structural centrality + vocabulary uniqueness/richness
    rest = [i for i in range(n) if i not in seen]
    rest.sort(
        key=lambda i: (
            -(records[i]["fan_in"] * 4 + records[i]["dom"] * 2 + records[i]["rev_reach"] + records[i]["uniq_hint"] * 25.0 + min(20, records[i]["decls"])),
            -records[i]["loc"],
            records[i]["name"],
        )
    )
    for i in rest:
        if len(selected) >= max_points:
            break
        _add(i)

    selected.sort()
    return selected


def build_source_embedding(
    scanner_db: str,
    src_dir: str,
    *,
    flirt_db: Optional[str] = None,
    out_path: Optional[str] = None,
    max_points: int = 1800,
    svd_dim: int = 24,
    knn_k: int = 10,
    seed: int = 42,
    roots: Optional[List[str]] = None,
) -> Dict[str, Any]:
    """Build interactive `leanre.embedding_2d/1` map from source scanner DB (+ optional `flirt_db`)."""
    t0 = time.perf_counter()
    n_steps = 180

    with contextlib.closing(atlas.connect_ro(scanner_db)) as con:
        cs_row = con.execute("SELECT value_json FROM meta WHERE key='corpus_stats'").fetchone()
        corpus_stats = json.loads(cs_row[0]) if cs_row else {}
        mod_rows = con.execute(
            """SELECT name, file_path, namespace_top, namespace_l2, lines_wc,
                      decl_count, fan_in, fan_out, bfs_depth, dom_subtree_size,
                      rev_reach, clone_cluster_size, forensic_flags_json
               FROM modules ORDER BY id ASC"""
        ).fetchall()
        edge_rows = [
            (str(r[0]), str(r[1]))
            for r in con.execute("SELECT src, dst FROM module_edges")
        ]
        decl_rows = con.execute(
            "SELECT module, name, kind, signature_snippet, line_no FROM declarations ORDER BY id ASC"
        ).fetchall()
        sorry_counts_by_mod: Dict[str, int] = collections.Counter()
        if atlas._table_exists(con, "forensic_hits"):
            for (hmod,) in con.execute("SELECT module FROM forensic_hits WHERE tag='sorry'"):
                sorry_counts_by_mod[str(hmod)] += 1

    flirt_meta: Dict[str, Dict[str, Any]] = {}
    alpha_cluster_sizes: Dict[str, int] = collections.Counter()
    has_fdb = bool(flirt_db and os.path.isfile(os.path.realpath(flirt_db)))
    if has_fdb and flirt_db:
        with contextlib.closing(atlas.connect_ro(flirt_db)) as fcon:
            if atlas._table_exists(fcon, "module_fingerprints"):
                for mod, subimps_j, opens_j, toks_j, asig in fcon.execute(
                    "SELECT module, mathlib_subimports_json, opens_json, type_tokens_top_json, alpha_clone_sig FROM module_fingerprints"
                ):
                    as_s = str(asig or "")
                    if as_s and as_s not in ("shim_empty", "empty"):
                        alpha_cluster_sizes[as_s] += 1
                    flirt_meta[str(mod)] = {
                        "subimps": json.loads(subimps_j) if subimps_j else [],
                        "opens": json.loads(opens_j) if opens_j else [],
                        "toks": json.loads(toks_j) if toks_j else [],
                        "alpha_sig": as_s,
                    }

    mod_fields = [
        "name", "short", "kind_idx", "dom", "fan_in", "loc", "decls",
        "comment_pct", "sorry_count", "pillar_idx", "dir_idx", "line",
        "px", "py", "ux", "uy", "top_term_idxs", "nn_idx", "drift",
        "sim_nn1", "uniq", "lib_sim", "clone_count", "status_idx",
    ]

    n_total_mods = len(mod_rows)
    if n_total_mods == 0:
        empty_layer = {
            "count": 0,
            "svd_explained_variance_ratios": [],
            "svd_explained_variance_sum": 0.0,
            "metrics": {
                "pca2": {"knn_preservation": 1.0, "trustworthiness": 1.0},
                "knn2": {"knn_preservation": 1.0, "trustworthiness": 1.0},
                "drift": {"k_neighbors": 0, "mean_drift_all": 0.0, "mean_drift_dom1k": 0.0, "dom1k_count": 0, "dom1k_nn1_diff_folder_pct": 0.0},
            },
            "tables": {
                "pillars": [],
                "dirs": [],
                "kinds": list(SOURCE_KINDS),
                "statuses": list(SOURCE_STATUSES),
                "vocab_terms": [],
            },
            "fields": mod_fields,
            "points": [],
        }
        empty_doc: Dict[str, Any] = {
            "schema": SCHEMA_VERSION,
            "inputs": {
                "scanner_db": _safe_input_label(scanner_db),
                "src_dir": _safe_input_label(src_dir),
                "flirt_db": _safe_input_label(flirt_db) if has_fdb else None,
                "mode": "source",
                "numpy_version": str(np.__version__) if np is not None else "stdlib",
            },
            "runtime_sec": round(time.perf_counter() - t0, 3),
            "svd_dim": int(svd_dim),
            "knn_k": int(knn_k),
            "knn_steps": n_steps,
            "seed": int(seed),
            "layers": {"modules": empty_layer},
        }
        if out_path:
            _write_compact_json(empty_doc, out_path)
        return empty_doc

    mod_names = [str(r[0]) for r in mod_rows]
    name_to_idx = {nm: i for i, nm in enumerate(mod_names)}

    # Build adjacency graph for reachability + 1-hop neighborhoods
    adj: List[List[int]] = [[] for _ in range(n_total_mods)]
    radj: List[List[int]] = [[] for _ in range(n_total_mods)]
    for src_m, dst_m in edge_rows:
        u = name_to_idx.get(src_m)
        v = name_to_idx.get(dst_m)
        if u is not None and v is not None and u != v:
            adj[u].append(v)
            radj[v].append(u)

    eff_roots: List[str] = []
    if roots:
        eff_roots = [r for r in roots if r in name_to_idx]
    if not eff_roots:
        cs_roots = corpus_stats.get("root_modules") or (
            [corpus_stats["root_module"]] if corpus_stats.get("root_module") else []
        )
        eff_roots = [str(r) for r in cs_roots if str(r) in name_to_idx]

    # Recompute BFS/dominators if `roots` explicitly passed (or DB has no reachable nodes despite roots)
    bfs_depths = [int(r[8]) for r in mod_rows]
    dom_sizes = [int(r[9]) for r in mod_rows]
    if roots and eff_roots:
        root_ids = [name_to_idx[r] for r in eff_roots]
        bfs_depths, _ = _graph.bfs_shortest_paths(root_ids, adj, n_total_mods)
        if len(root_ids) == 1:
            _, _, dom_sizes, _, _ = _graph.dominators_chk(root_ids[0], adj, radj, n_total_mods)
        else:
            v_idx = n_total_mods
            adj_v = [list(x) for x in adj] + [list(root_ids)]
            radj_v = [list(x) for x in radj] + [[]]
            for rid in root_ids:
                radj_v[rid].append(v_idx)
            _, _, dom_v, _, _ = _graph.dominators_chk(v_idx, adj_v, radj_v, n_total_mods + 1)
            dom_sizes = dom_v[:n_total_mods]

    # Per-root reachability sets when >= 2 roots (e.g. NavierStokes + Euler)
    reach_by_root: Dict[str, Set[int]] = {}
    if len(eff_roots) >= 2:
        for rname in eff_roots:
            rid = name_to_idx[rname]
            dist_r, _ = _graph.bfs_shortest_paths([rid], adj, n_total_mods)
            reach_by_root[rname] = {i for i, d in enumerate(dist_r) if d >= 0}

    # Group declarations by module
    decls_by_mod: Dict[str, List[Tuple[str, str, str, int]]] = collections.defaultdict(list)
    for m_s, d_name, d_kind, d_sig, d_line in decl_rows:
        decls_by_mod[str(m_s)].append((str(d_name), str(d_kind), str(d_sig or ""), int(d_line)))

    # Choose pillar scheme for reachable modules
    reach_top_ctr: collections.Counter[str] = collections.Counter()
    reach_l2_ctr: collections.Counter[str] = collections.Counter()
    for i, r in enumerate(mod_rows):
        if bfs_depths[i] >= 0:
            reach_top_ctr[str(r[2])] += 1
            reach_l2_ctr[str(r[3])] += 1
    multi_top_ns = sum(1 for _, c in reach_top_ctr.items() if c >= 2) >= 2
    keep_top_pillars = {k for k, _ in reach_top_ctr.most_common(7)}
    keep_l2_pillars = {k for k, _ in reach_l2_ctr.most_common(7)}

    # Extract per-module metadata, comment_pct, imports, opens, and raw token bags
    records: List[Dict[str, Any]] = []
    direct_bags: List[Dict[str, float]] = []
    abs_src = os.path.abspath(src_dir)

    for i, r in enumerate(mod_rows):
        mod_nm = str(r[0])
        fpath = str(r[1])
        ns_top = str(r[2])
        ns_l2 = str(r[3])
        lines_wc = int(r[4])
        decl_cnt = int(r[5])
        fan_in = int(r[6])
        fan_out = int(r[7])
        bfs_d = int(bfs_depths[i])
        dom_sz = int(dom_sizes[i])
        rev_r = int(r[10])
        clone_sz = max(1, int(r[11]))
        fflags = set(json.loads(r[12]) if r[12] else [])

        fm = flirt_meta.get(mod_nm)
        if fm and fm["alpha_sig"]:
            clone_sz = max(clone_sz, alpha_cluster_sizes.get(fm["alpha_sig"], 1))

        full_lean = os.path.join(abs_src, fpath)
        l_wc_disk, c_lines, imports, opens = _scan_lean_file_meta(full_lean)
        eff_loc = l_wc_disk if l_wc_disk > 0 else lines_wc
        comment_pct = round(100.0 * c_lines / float(max(1, eff_loc)), 1)

        bag: Dict[str, float] = collections.defaultdict(float)
        ext_imp_cnt = 0
        proj_imp_cnt = 0
        for imp in imports:
            if imp.startswith(_EXT_IMPORT_PREFIXES):
                ext_imp_cnt += 1
                iparts = imp.split(".")
                pref = ".".join(iparts[: min(3, len(iparts))])
                bag[pref] += 1.4
                for tok in _tokenize_source_ident(".".join(iparts[1:])):
                    bag[tok] += 0.6
            else:
                proj_imp_cnt += 1
                if "." in imp:
                    bag[".".join(imp.split(".")[:2])] += 0.5

        for op in opens:
            for tok in _tokenize_source_ident(op):
                bag[tok] += 0.8

        hdr_lib_hits = 0
        hdr_tot_toks = 0
        m_decls = decls_by_mod.get(mod_nm, [])
        has_axiom_decl = False
        for d_name, d_kind, d_sig, _ in m_decls:
            if d_kind == "axiom":
                has_axiom_decl = True
            # Strip module prefix from decl name if present
            short_d = d_name[len(mod_nm) + 1:] if d_name.startswith(mod_nm + ".") else d_name
            for tok in _tokenize_source_ident(short_d):
                bag[tok] += 1.0
            # Extract identifiers from signature snippet
            sig_body = d_sig.split(":", 1)[1] if ":" in d_sig else d_sig
            for ident in _SRC_IDENT_RE.findall(sig_body):
                if ident in _SRC_STOP_WORDS:
                    continue
                if ident.startswith(_EXT_IMPORT_PREFIXES) or ident in atlas._EXTERNAL_TOP_PREFIXES:
                    hdr_lib_hits += 1
                hdr_tot_toks += 1
                for tok in _tokenize_source_ident(ident):
                    bag[tok] += 0.9

        if fm:
            for sub in fm["subimps"]:
                bag[str(sub)] += 1.0
                ext_imp_cnt += 1
            for op in fm["opens"]:
                for tok in _tokenize_source_ident(str(op)):
                    bag[tok] += 0.6
            for tk in fm["toks"]:
                tk_s = str(tk)
                if tk_s in atlas._EXTERNAL_TOP_PREFIXES:
                    hdr_lib_hits += 1
                hdr_tot_toks += 1
                for tok in _tokenize_source_ident(tk_s):
                    bag[tok] += 0.8

        imp_tot = ext_imp_cnt + proj_imp_cnt
        imp_lib_frac = (ext_imp_cnt / float(imp_tot)) if imp_tot > 0 else 0.0
        hdr_lib_frac = (hdr_lib_hits / float(hdr_tot_toks)) if hdr_tot_toks > 0 else imp_lib_frac
        lib_sim = round(max(0.0, min(1.0, 0.5 * imp_lib_frac + 0.5 * hdr_lib_frac)), 4)

        is_chal = _is_challenge_module(fpath, mod_nm)
        sorry_cnt = sorry_counts_by_mod.get(mod_nm, 0)
        if "sorry" in fflags and sorry_cnt == 0:
            sorry_cnt = 1

        if is_chal:
            kind_str = "challenge"
        elif bfs_d < 0:
            kind_str = "orphan"
        elif bfs_d == 0:
            kind_str = "root"
        elif fan_in >= 2 or dom_sz >= 3 or rev_r >= 3 or (n_total_mods < 10 and fan_in >= 1 and fan_out >= 1):
            kind_str = "core"
        else:
            kind_str = "leaf"

        if bfs_d < 0:
            pillar_str = "Challenge" if is_chal else "Unreached"
        elif len(eff_roots) >= 2:
            hitting = [rn for rn in eff_roots if i in reach_by_root.get(rn, ())]
            if len(hitting) == 1:
                pillar_str = hitting[0].split(".")[0]
            elif mod_nm.split(".")[0] in {rn.split(".")[0] for rn in hitting}:
                pillar_str = mod_nm.split(".")[0]
            else:
                pillar_str = "Shared"
        else:
            if multi_top_ns:
                pillar_str = ns_top if ns_top in keep_top_pillars else "Other"
            else:
                pillar_str = ns_l2 if ns_l2 in keep_l2_pillars else "Other"

        if sorry_cnt > 0 and is_chal:
            status_str = "challenge_sorry"
        elif sorry_cnt > 0:
            status_str = "proof_sorry"
        elif "axiom" in fflags or has_axiom_decl:
            status_str = "axiom"
        elif "decide_kernel" in fflags:
            status_str = "decide_kernel"
        elif bfs_d < 0:
            status_str = "unreached"
        else:
            status_str = "clean"

        fdir = os.path.dirname(fpath.replace("\\", "/"))
        if fdir:
            dparts = [p for p in fdir.split("/") if p and p != "."]
            dir_top = ".".join(dparts[:2]) if len(dparts) >= 2 else (dparts[0] if dparts else (ns_top or "<root>"))
        else:
            dir_top = ns_top or "<root>"

        direct_bags.append(bag)
        records.append({
            "idx": i,
            "name": mod_nm,
            "short": _short_module_name(mod_nm),
            "file_path": fpath,
            "dir_top": dir_top,
            "kind": kind_str,
            "pillar": pillar_str,
            "status": status_str,
            "dom": dom_sz if dom_sz > 0 else rev_r,
            "fan_in": fan_in,
            "fan_out": fan_out,
            "loc": eff_loc,
            "decls": decl_cnt,
            "comment_pct": comment_pct,
            "sorry_count": sorry_cnt,
            "bfs_depth": bfs_d,
            "rev_reach": rev_r,
            "clone_count": clone_sz,
            "lib_sim": lib_sim,
            "forensic_flags": fflags,
            "is_challenge": is_chal,
            "uniq_hint": 0.0,
        })

    # 1-hop import neighborhood bags across ALL modules
    tok_df: collections.Counter[str] = collections.Counter()
    for b in direct_bags:
        for t in b:
            tok_df[t] += 1

    hop_bags: List[Dict[str, float]] = []
    for i in range(n_total_mods):
        hb: Dict[str, float] = dict(direct_bags[i])
        for v in adj[i]:
            for t, w in direct_bags[v].items():
                hb[t] = hb.get(t, 0.0) + 0.35 * w
        if len(hb) < 4:
            for u in radj[i]:
                for t, w in direct_bags[u].items():
                    hb[t] = hb.get(t, 0.0) + 0.15 * w
        hop_bags.append(hb)
        # Lightweight pre-sampling uniqueness hint (rare token density)
        if hb:
            rarity = sum(1.0 / math.log1p(tok_df[t]) for t in hb if tok_df[t] > 0) / float(len(hb))
            records[i]["uniq_hint"] = rarity / float(1.0 + math.log2(records[i]["clone_count"]))

    keep_indices = _select_source_modules(records, max_points=max_points)
    kept_recs = [records[i] for i in keep_indices]
    kept_bags = [hop_bags[i] for i in keep_indices]
    m_cnt = len(kept_recs)

    dir_tops = [r["dir_top"] for r in kept_recs]
    is_core_hub = [r["kind"] in ("root", "core") for r in kept_recs]
    dup_counts = [r["clone_count"] for r in kept_recs]
    extra_feats = [
        [
            math.log1p(max(0, r["loc"])),
            math.log1p(max(0, r["decls"])),
            math.log1p(max(0, r["fan_in"])),
            math.log1p(max(0, r["dom"])),
        ]
        for r in kept_recs
    ]

    emb = _build_tfidf_svd_umap_generic(
        kept_bags,
        dir_tops,
        is_core_hub,
        dup_counts,
        max_vocab=512,
        svd_dim=svd_dim,
        knn_k=knn_k,
        n_steps=n_steps,
        seed=seed,
        extra_feats=extra_feats,
    )

    pillars_tbl = sorted({r["pillar"] for r in kept_recs})
    dirs_tbl = sorted(set(dir_tops))
    kinds_tbl = list(SOURCE_KINDS)
    statuses_tbl = list(SOURCE_STATUSES)
    pil_map = {v: idx for idx, v in enumerate(pillars_tbl)}
    dir_map = {v: idx for idx, v in enumerate(dirs_tbl)}
    knd_map = {v: idx for idx, v in enumerate(kinds_tbl)}
    sts_map = {v: idx for idx, v in enumerate(statuses_tbl)}

    mod_points: List[List[Any]] = []
    for i, r in enumerate(kept_recs):
        mod_points.append([
            r["name"],
            r["short"],
            knd_map[r["kind"]],
            r["dom"],
            r["fan_in"],
            r["loc"],
            r["decls"],
            r["comment_pct"],
            r["sorry_count"],
            pil_map[r["pillar"]],
            dir_map[r["dir_top"]],
            1,
            emb["pca2"][i][0],
            emb["pca2"][i][1],
            emb["knn2"][i][0],
            emb["knn2"][i][1],
            emb["top_term_idxs"][i],
            emb["nn5"][i],
            emb["drifts"][i],
            emb["sim_nn1"][i],
            emb["uniq"][i],
            r["lib_sim"],
            r["clone_count"],
            sts_map[r["status"]],
        ])

    modules_layer: Dict[str, Any] = {
        "count": m_cnt,
        "svd_explained_variance_ratios": emb["exp_ratios"],
        "svd_explained_variance_sum": emb["exp_sum"],
        "metrics": {
            "pca2": emb["m_pca"],
            "knn2": emb["m_knn"],
            "drift": emb["drift_stats"],
        },
        "tables": {
            "pillars": pillars_tbl,
            "dirs": dirs_tbl,
            "kinds": kinds_tbl,
            "statuses": statuses_tbl,
            "vocab_terms": emb["vocab_terms"],
        },
        "fields": mod_fields,
        "points": mod_points,
    }

    layers: Dict[str, Any] = {"modules": modules_layer}

    # Optional `folders` rollup layer when >= 40 modules and >= 2 folders
    if n_total_mods >= 40:
        f_groups: Dict[str, List[int]] = collections.defaultdict(list)
        for i, r in enumerate(records):
            f_groups[r["dir_top"]].append(i)
        if 2 <= len(f_groups) <= max(250, n_total_mods // 3):
            f_names = sorted(f_groups.keys())
            f_bags: List[Dict[str, float]] = []
            f_recs: List[Dict[str, Any]] = []
            sts_prio = {s: idx for idx, s in enumerate(SOURCE_STATUSES)}
            # Worst status priority: proof_sorry > axiom > decide_kernel > challenge_sorry > unreached > clean
            worst_rank = {"clean": 0, "unreached": 1, "challenge_sorry": 2, "decide_kernel": 3, "axiom": 4, "proof_sorry": 5}
            for fnm in f_names:
                idxs = f_groups[fnm]
                agg_bag: Dict[str, float] = collections.defaultdict(float)
                loc_sum = 0
                decls_sum = 0
                fan_in_sum = 0
                dom_max = 0
                sorry_sum = 0
                c_num = 0.0
                lib_num = 0.0
                clone_max = 1
                pil_ctr: collections.Counter[str] = collections.Counter()
                knd_ctr: collections.Counter[str] = collections.Counter()
                best_sts = "clean"
                for idx in idxs:
                    rr = records[idx]
                    loc_sum += rr["loc"]
                    decls_sum += rr["decls"]
                    fan_in_sum += rr["fan_in"]
                    if rr["dom"] > dom_max:
                        dom_max = rr["dom"]
                    sorry_sum += rr["sorry_count"]
                    w_loc = max(1, rr["loc"])
                    c_num += rr["comment_pct"] * w_loc
                    lib_num += rr["lib_sim"] * w_loc
                    if rr["clone_count"] > clone_max:
                        clone_max = rr["clone_count"]
                    pil_ctr[rr["pillar"]] += w_loc
                    knd_ctr[rr["kind"]] += 1
                    if worst_rank.get(rr["status"], 0) > worst_rank.get(best_sts, 0):
                        best_sts = rr["status"]
                    for tok, tw in hop_bags[idx].items():
                        agg_bag[tok] += tw
                tot_w_loc = max(1, sum(max(1, records[idx]["loc"]) for idx in idxs))
                f_bags.append(agg_bag)
                f_recs.append({
                    "name": fnm,
                    "short": fnm.rsplit(".", 1)[-1] if "." in fnm else fnm,
                    "dir_top": fnm.split(".")[0],
                    "kind": knd_ctr.most_common(1)[0][0],
                    "pillar": pil_ctr.most_common(1)[0][0],
                    "status": best_sts,
                    "dom": max(dom_max, len(idxs)),
                    "fan_in": fan_in_sum,
                    "loc": loc_sum,
                    "decls": decls_sum,
                    "comment_pct": round(c_num / float(tot_w_loc), 1),
                    "sorry_count": sorry_sum,
                    "lib_sim": round(lib_num / float(tot_w_loc), 4),
                    "clone_count": clone_max,
                })

            f_emb = _build_tfidf_svd_umap_generic(
                f_bags,
                [r["dir_top"] for r in f_recs],
                [True] * len(f_recs),
                [r["clone_count"] for r in f_recs],
                max_vocab=384,
                svd_dim=svd_dim,
                knn_k=knn_k,
                n_steps=n_steps,
                seed=seed,
                extra_feats=[
                    [math.log1p(r["loc"]), math.log1p(r["decls"]), math.log1p(r["fan_in"]), math.log1p(r["dom"])]
                    for r in f_recs
                ],
            )
            f_pillars = sorted({r["pillar"] for r in f_recs})
            f_dirs = sorted({r["dir_top"] for r in f_recs})
            fp_map = {v: idx for idx, v in enumerate(f_pillars)}
            fd_map = {v: idx for idx, v in enumerate(f_dirs)}
            f_pts: List[List[Any]] = []
            for i, r in enumerate(f_recs):
                f_pts.append([
                    r["name"],
                    r["short"],
                    knd_map[r["kind"]],
                    r["dom"],
                    r["fan_in"],
                    r["loc"],
                    r["decls"],
                    r["comment_pct"],
                    r["sorry_count"],
                    fp_map[r["pillar"]],
                    fd_map[r["dir_top"]],
                    1,
                    f_emb["pca2"][i][0],
                    f_emb["pca2"][i][1],
                    f_emb["knn2"][i][0],
                    f_emb["knn2"][i][1],
                    f_emb["top_term_idxs"][i],
                    f_emb["nn5"][i],
                    f_emb["drifts"][i],
                    f_emb["sim_nn1"][i],
                    f_emb["uniq"][i],
                    r["lib_sim"],
                    r["clone_count"],
                    sts_prio[r["status"]],
                ])
            layers["folders"] = {
                "count": len(f_recs),
                "svd_explained_variance_ratios": f_emb["exp_ratios"],
                "svd_explained_variance_sum": f_emb["exp_sum"],
                "metrics": {
                    "pca2": f_emb["m_pca"],
                    "knn2": f_emb["m_knn"],
                    "drift": f_emb["drift_stats"],
                },
                "tables": {
                    "pillars": f_pillars,
                    "dirs": f_dirs,
                    "kinds": kinds_tbl,
                    "statuses": statuses_tbl,
                    "vocab_terms": f_emb["vocab_terms"],
                },
                "fields": mod_fields,
                "points": f_pts,
            }

    doc: Dict[str, Any] = {
        "schema": SCHEMA_VERSION,
        "inputs": {
            "scanner_db": _safe_input_label(scanner_db),
            "src_dir": _safe_input_label(src_dir),
            "flirt_db": _safe_input_label(flirt_db) if has_fdb else None,
            "mode": "source",
            "total_modules": n_total_mods,
            "roots": eff_roots,
            "numpy_version": str(np.__version__) if np is not None else "stdlib",
        },
        "runtime_sec": round(time.perf_counter() - t0, 3),
        "svd_dim": int(svd_dim),
        "knn_k": int(knn_k),
        "knn_steps": n_steps,
        "seed": int(seed),
        "layers": layers,
    }

    if out_path:
        _write_compact_json(doc, out_path)
    return doc


def _write_compact_json(doc: Dict[str, Any], out_path: str) -> None:
    if os.path.islink(out_path):
        raise ValueError(f"Refusing to write through symlink: {out_path}")
    os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
    payload = json.dumps(doc, separators=(",", ":"), ensure_ascii=False)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(payload)
        f.write("\n")


def build_arg_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(
        prog="python3 leanre/embedding.py",
        description="Build 2D TF-IDF + SVD(k=24) + pca2/knn2 embedding map over kernel.db or Lean source tree.",
    )
    ap.add_argument("--kernel-db", default=DEFAULT_KERNEL_DB, help="Path to read-only kernel.db")
    ap.add_argument("--leanre-db", default=DEFAULT_LEANRE_DB, help="Optional path to leanre.db")
    ap.add_argument("--cluster-labels", default=DEFAULT_CLUSTER_LABELS, help="Optional cluster_labels_141.json")
    ap.add_argument("--portability", default=DEFAULT_PORTABILITY, help="Optional portability_gems.json")
    ap.add_argument("--src", default=None, help="Source-only mode: path to Lean source directory")
    ap.add_argument("--scanner-db", default=None, help="Source-only mode: path to scanner leanre.db")
    ap.add_argument("--flirt-db", default=None, help="Source-only mode: optional path to flirt tier1.db")
    ap.add_argument("--roots", action="append", default=None, help="Source-only mode: root module(s) (comma-separated or repeated)")
    ap.add_argument("--out", default=DEFAULT_OUT_JSON, help="Output JSON path (<= 650 KB)")
    ap.add_argument("--png", default=None, help="Optional path to write 512x512 preview PNG")
    ap.add_argument("--max-landmarks", type=int, default=1800, help="Target landmark/module point cap")
    ap.add_argument("--svd-dim", type=int, default=24, help="Truncated SVD rank")
    ap.add_argument("--knn-k", type=int, default=None, help="k-NN neighbors in SVD space (15 kernel, 10 source)")
    ap.add_argument("--knn-steps", type=int, default=180, help="Gradient steps for knn2")
    ap.add_argument("--seed", type=int, default=42, help="Deterministic RNG seed")
    ap.add_argument("--workers", type=int, default=0, help="Worker processes (0 = auto)")
    return ap


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_arg_parser().parse_args(argv)
    if args.src or args.scanner_db:
        roots_list: Optional[List[str]] = None
        if args.roots:
            roots_list = [p.strip() for item in args.roots for p in item.split(",") if p.strip()]
        knn_k_src = 10 if args.knn_k is None else int(args.knn_k)
        if args.scanner_db and os.path.isfile(args.scanner_db):
            src_dir = args.src or os.path.dirname(os.path.abspath(args.scanner_db))
            doc = build_source_embedding(
                scanner_db=args.scanner_db,
                src_dir=src_dir,
                flirt_db=args.flirt_db,
                out_path=args.out,
                max_points=args.max_landmarks,
                svd_dim=args.svd_dim,
                knn_k=knn_k_src,
                seed=args.seed,
                roots=roots_list,
            )
        else:
            if not args.src or not os.path.isdir(args.src):
                raise FileNotFoundError(f"Missing --src directory: {args.src}")
            try:
                from leanre import scanner as _scanner  # type: ignore[import-not-found]
            except ImportError:  # pragma: no cover
                import scanner as _scanner  # type: ignore[no-redef]
            with tempfile.TemporaryDirectory(prefix="leanre_emb_scan_") as td:
                tmp_db = os.path.join(td, "leanre.db")
                root_arg = roots_list[0] if (roots_list and len(roots_list) == 1) else "auto"
                _scanner.run_scan(args.src, tmp_db, root_module=root_arg, verbose=False, max_hits_per_tag=0)
                doc = build_source_embedding(
                    scanner_db=tmp_db,
                    src_dir=args.src,
                    flirt_db=args.flirt_db,
                    out_path=args.out,
                    max_points=args.max_landmarks,
                    svd_dim=args.svd_dim,
                    knn_k=knn_k_src,
                    seed=args.seed,
                    roots=roots_list,
                )
        ml = doc["layers"]["modules"]
        out_bytes = os.path.getsize(args.out) if (args.out and os.path.isfile(args.out)) else 0
        print(
            f"[embedding-source] done in {doc['runtime_sec']:.2f}s | "
            f"modules={ml['count']} (knn{knn_k_src}={ml['metrics']['knn2']['knn_preservation']:.4f}, "
            f"trust={ml['metrics']['knn2']['trustworthiness']:.4f}) | "
            f"json={out_bytes:,} B"
        )
        return 0

    knn_k_kern = 15 if args.knn_k is None else int(args.knn_k)
    doc = run_embedding(
        kernel_db_path=args.kernel_db,
        leanre_db_path=args.leanre_db,
        cluster_labels_path=args.cluster_labels,
        portability_path=args.portability,
        out_json_path=args.out,
        png_path=args.png,
        max_landmarks=args.max_landmarks,
        svd_dim=args.svd_dim,
        knn_k=knn_k_kern,
        knn_steps=args.knn_steps,
        seed=args.seed,
        workers=args.workers,
    )
    cl = doc["layers"]["clusters_141"]
    lm = doc["layers"]["landmarks"]
    out_bytes = os.path.getsize(args.out) if (args.out and os.path.isfile(args.out)) else 0
    print(
        f"[embedding] done in {doc['runtime_sec']:.2f}s | "
        f"clusters={cl['count']} (knn15={cl['metrics']['knn2']['knn_preservation']:.4f}, "
        f"trust={cl['metrics']['knn2']['trustworthiness']:.4f}) | "
        f"landmarks={lm['count']} (pca15={lm['metrics']['pca2']['knn_preservation']:.4f}, "
        f"knn15={lm['metrics']['knn2']['knn_preservation']:.4f}, "
        f"trust={lm['metrics']['knn2']['trustworthiness']:.4f}, "
        f"dom1k_nn1_diff={lm['metrics']['drift']['dom1k_nn1_diff_folder_pct']:.2f}%) | "
        f"json={out_bytes:,} B"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
