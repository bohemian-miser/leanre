#!/usr/bin/env python3
"""leanre.circuit — 2swap/Tromp-inspired 3-level Proof-Circuit engine, SVG & HTML exporter.

Generates a canonical ``leanre.circuit/1`` JSON payload, publication-grade dark/light
vector SVG diagrams, and standalone zero-CDN interactive pan/zoom HTML visualizers
for any Lean 4 project across three zoom levels:

  * Zoom 0 (``macro``)   — Macro repo circuit: headline roots, top dominator pillars,
                          shared diamonds (between >= 2 pillars), repeated signature-hash
                          (``k1n`` / ``k1a``) motif clusters, standalone portable islands,
                          and dead/unreachable mass (``live=0``).
  * Zoom 1 (``bundle``)  — Record / Prop-def IC pin-board: producer bank (root,
                          local_witness, via_extends, self->S), center field/conjunct
                          port spine (projected / unread / conditional_prop / True stub),
                          and consumer bank with red dangling wires for dropped inputs.
  * Zoom 2 (``theorem``) — Theorem step-wiring circuit: horizontal Tromp binder bar
                          with unplugged dropped binders, topological lanes for
                          ``obtain``/``rcases``/``have``/``let`` steps (plus term-mode
                          application fallback), FLIRT/``k1n`` callee multiplicity badges,
                          and semantic/``true_slot``/``le_refl``/``else 0`` pin overlays.

Guardrails:
  - Python 3.11+ standard library + sibling ``leanre`` modules only (zero external deps).
  - Strictly read-only SQLite access (``file:<real>?mode=ro`` + ``PRAGMA query_only=1``).
  - Strictly zero external CDNs, zero raw multi-line ``.lean`` dumps, strict XML/HTML
    escaping, and symlink refusal on output targets.
"""
from __future__ import annotations

import argparse
import collections
import html
import json
import math
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

import bundles as _bundles  # noqa: E402
import config as _config  # noqa: E402
import kernel as _kernel  # noqa: E402

SCHEMA_VERSION = "leanre.circuit/1"

DEFAULT_KERNEL_DB = os.path.join(_REPO_ROOT, "outputs", "kernel", "kernel.db")
DEFAULT_SRC_ROOT = os.path.join(_REPO_ROOT, "data", "rh_mirror", "src")

MOTIF_PALETTE: Tuple[str, ...] = (
    "#22d3ee",
    "#a78bfa",
    "#f59e0b",
    "#34d399",
    "#f472b6",
    "#38bdf8",
    "#fb923c",
    "#818cf8",
    "#2dd4bf",
    "#eab308",
)

BINDER_PALETTE: Tuple[str, ...] = (
    "#34d399",
    "#22d3ee",
    "#38bdf8",
    "#a78bfa",
    "#2dd4bf",
    "#60a5fa",
    "#818cf8",
    "#4ade80",
)

THEMES: Dict[str, Dict[str, str]] = {
    "dark": {
        "name": "dark",
        "bg": "#0b1020",
        "grid": "#131b33",
        "panel": "#11182c",
        "panel_alt": "#162039",
        "chip": "#0f172a",
        "border": "#273557",
        "border_hi": "#3b5080",
        "text": "#e2e8f0",
        "sub": "#94a3b8",
        "muted": "#64748b",
        "emerald": "#34d399",
        "cyan": "#22d3ee",
        "violet": "#a78bfa",
        "amber": "#f59e0b",
        "crimson": "#ef4444",
        "slate": "#64748b",
        "blue": "#60a5fa",
        "rail": "#17233f",
    },
    "light": {
        "name": "light",
        "bg": "#f8fafc",
        "grid": "#e2e8f0",
        "panel": "#ffffff",
        "panel_alt": "#f1f5f9",
        "chip": "#f8fafc",
        "border": "#cbd5e1",
        "border_hi": "#94a3b8",
        "text": "#0f172a",
        "sub": "#475569",
        "muted": "#64748b",
        "emerald": "#059669",
        "cyan": "#0891b2",
        "violet": "#7c3aed",
        "amber": "#d97706",
        "crimson": "#dc2626",
        "slate": "#64748b",
        "blue": "#2563eb",
        "rail": "#e2e8f0",
    },
}

_PIN_STATUS_COLORS = {
    "projected": "emerald",
    "unread": "slate",
    "conditional_prop": "amber",
    "literal_true": "crimson",
    "used": "emerald",
    "dropped": "crimson",
    "dangling": "crimson",
    "instance": "slate",
    "unique": "slate",
    "low_repeat": "cyan",
    "high_repeat": "violet",
    "default_zero": "amber",
    "le_refl": "amber",
    "true_slot": "crimson",
}

_IDENT_START = r"A-Za-z_\u03b1-\u03c9\u0391-\u03a9"
_IDENT_CONT = r"A-Za-z0-9_'\u2070-\u209f\u03b1-\u03c9\u0391-\u03a9"
_RE_IDENT = re.compile(rf"[{_IDENT_START}][{_IDENT_CONT}]*")
_RE_QUAL_IDENT = re.compile(rf"[{_IDENT_START}][{_IDENT_CONT}]*(?:\.[{_IDENT_START}][{_IDENT_CONT}]*)*")
_RE_INVALID_XML = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]")
_RE_TACTIC_LEAD = re.compile(
    r"^(?P<kw>obtain|rcases|haveI|have|letI|let|set|choose|intro|intros|rintro|exact|refine|apply|rw|simp|convert|unfold|cases|induction)\b(.*)$"
)
_RE_NOISE_HEADS = frozenset({
    "by", "fun", "if", "then", "else", "match", "with", "let", "have", "obtain",
    "rcases", "intro", "intros", "rintro", "exact", "refine", "apply", "show",
    "from", "rw", "simp", "only", "at", "using", "in", "do", "return", "where",
    "Type", "Prop", "Sort", "Nat", "Int", "Real", "Complex", "Fin", "Finset",
    "Set", "List", "Option", "Bool", "True", "False", "Eq", "And", "Or", "Not",
    "forall", "Exists", "rfl", "trivial", "sorry", "classical", "linarith",
    "ring", "omega", "norm_num", "abel", "aesop", "decide", "congr", "ext",
})


# ---------------------------------------------------------------------------
# Generic Safe I/O, Escaping & Resolution Helpers
# ---------------------------------------------------------------------------

def _open_ro(kernel_db_path: str) -> sqlite3.Connection:
    real = os.path.realpath(kernel_db_path)
    if not os.path.isfile(real):
        raise FileNotFoundError(f"Missing SQLite database: {kernel_db_path}")
    conn = sqlite3.connect(f"file:{real}?mode=ro", uri=True)
    conn.execute("PRAGMA query_only=1")
    return conn


def _safe_write_text(out_path: str, text: str) -> None:
    if os.path.islink(out_path):
        raise ValueError(f"Refusing to write through symlink: {out_path}")
    parent = os.path.dirname(os.path.abspath(out_path))
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(text)


def _rel_display_path(path: Optional[str]) -> Optional[str]:
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


def _has_table(conn: sqlite3.Connection, name: str) -> bool:
    return (
        conn.execute(
            "SELECT 1 FROM sqlite_master WHERE type IN ('table', 'view') AND name = ?",
            (name,),
        ).fetchone()
        is not None
    )


def _clean_text(value: Any) -> str:
    if value is None:
        return ""
    s = _RE_INVALID_XML.sub("", str(value))
    return " ".join(s.split())


def _xml_esc(value: Any) -> str:
    return html.escape(_RE_INVALID_XML.sub("", str(value or "")), quote=True).replace("--", "&#45;&#45;")


def _escape_json_for_script(obj: Any) -> str:
    raw = json.dumps(obj, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    return raw.replace("<", "\\u003c").replace(">", "\\u003e").replace("&", "\\u0026")


def _short_name(fqn: str, max_chars: int = 32) -> str:
    s = _clean_text(fqn)
    if len(s) <= max_chars:
        return s
    parts = s.split(".")
    tail = parts[-1]
    if len(parts) >= 2 and len(parts[-2]) + 1 + len(tail) <= max_chars:
        return f"{parts[-2]}.{tail}"
    if len(tail) <= max_chars:
        return tail
    return tail[: max(4, max_chars - 1)] + "…"


def _clip_chars(text: str, max_chars: int) -> str:
    s = _clean_text(text)
    if max_chars <= 1:
        return s[:max_chars]
    if len(s) <= max_chars:
        return s
    return s[: max_chars - 1] + "…"


def _clip_px(text: str, max_px: float, font_size: float = 11.0, mono: bool = True) -> str:
    char_w = font_size * (0.62 if mono else 0.56)
    budget = max(3, int(max_px / max(1.0, char_w)))
    return _clip_chars(text, budget)


def _fmt_int(n: Any) -> str:
    try:
        return f"{int(n):,}"
    except (TypeError, ValueError):
        return "0"


def _resolve_default_src_root(kernel_db_path: str, src_root: Optional[str]) -> Optional[str]:
    if src_root is not None:
        real = os.path.realpath(src_root)
        if not os.path.isdir(real):
            raise FileNotFoundError(f"Missing --src-root directory: {src_root}")
        return real
    # Auto-discover nearby leanre.toml src_dir only when matching DB or default repo DB
    kdb_real = os.path.realpath(kernel_db_path)
    def_real = os.path.realpath(DEFAULT_KERNEL_DB)
    if kdb_real == def_real and os.path.isdir(DEFAULT_SRC_ROOT):
        return os.path.realpath(DEFAULT_SRC_ROOT)
    cfg_path = _config.find_config(os.path.dirname(kdb_real))
    if cfg_path is not None and os.path.realpath(str(cfg_path)) != os.path.realpath(os.path.join(_REPO_ROOT, "leanre.toml")):
        try:
            cfg = _config.load_config(str(cfg_path))
            cand = cfg.resolve_src_dir()
            if cand and os.path.isdir(cand):
                return os.path.realpath(cand)
        except Exception:
            pass
    return None


def _is_aux_name(name: str) -> bool:
    return any(
        tok in name
        for tok in ("._proof_", "._simp_", "._cstage", ".match_", "._unary", "._mutual", "._sunfold", ".eq_")
    )


def _resolve_decl_exact_or_fuzzy(
    conn: sqlite3.Connection,
    decl: str,
    *,
    exact_case: bool = False,
) -> Tuple[int, str, Optional[str]]:
    q = decl.strip()
    if not q:
        raise LookupError("Empty declaration query")
    if not exact_case:
        return _kernel._resolve_decl_id(conn, q, allow_suffix=True, allow_const_folding=True)

    # Exact-case lookup: full name, _root_. stripped, or exact-case suffix without NOCASE fallback
    for cand in (q, q[7:] if q.startswith("_root_.") else q):
        row = conn.execute("SELECT id, name FROM decls WHERE name = ?", (cand,)).fetchone()
        if row is not None:
            return int(row[0]), str(row[1]), (None if cand == q else q)
    q_clean = q[7:] if q.startswith("_root_.") else q
    glob_pat = f"*.{_kernel._escape_glob(q_clean)}"
    rows = conn.execute(
        "SELECT id, name FROM decls WHERE name GLOB ? ORDER BY length(name), name LIMIT 50",
        (glob_pat,),
    ).fetchall()
    if len(rows) == 1:
        return int(rows[0][0]), str(rows[0][1]), q
    if len(rows) > 1:
        pub = [r for r in rows if not str(r[1]).startswith("_private.")]
        if len(pub) == 1:
            return int(pub[0][0]), str(pub[0][1]), q
        sample = ", ".join(str(r[1]) for r in (pub or rows)[:6])
        raise LookupError(f"Ambiguous exact-case suffix {q!r} ({len(rows)} matches): {sample}")
    raise LookupError(f"Declaration not found (exact-case): {decl}")


def _k1n_counts_for_hashes(conn: sqlite3.Connection, hashes: Iterable[str]) -> Dict[str, int]:
    uniq = sorted({h for h in hashes if h})
    if not uniq:
        return {}
    use_consts = _has_table(conn, "consts") and (
        conn.execute("SELECT 1 FROM consts WHERE sighash IS NOT NULL LIMIT 1").fetchone() is not None
    )
    out: Dict[str, int] = {}
    for i in range(0, len(uniq), 400):
        chunk = uniq[i : i + 400]
        ph = ",".join("?" for _ in chunk)
        if use_consts:
            rows = conn.execute(
                f"SELECT sighash, COUNT(*) FROM consts WHERE sighash IN ({ph}) GROUP BY sighash",
                chunk,
            ).fetchall()
        else:
            rows = conn.execute(
                f"SELECT sighash, COUNT(*) FROM decls WHERE sighash IN ({ph}) GROUP BY sighash",
                chunk,
            ).fetchall()
        for sh, cnt in rows:
            out[str(sh)] = int(cnt)
    return out


# ---------------------------------------------------------------------------
# Zoom 0 — Macro Repo Circuit (`--mode macro`)
# ---------------------------------------------------------------------------

def _load_matching_portability_islands(
    conn: sqlite3.Connection,
    kernel_db_path: str,
    portability_json: Optional[str],
) -> Optional[Tuple[List[Dict[str, Any]], Dict[str, Any]]]:
    cands: List[str] = []
    if portability_json:
        cands.append(portability_json)
    else:
        kdb_dir = os.path.dirname(os.path.realpath(kernel_db_path))
        cands.append(os.path.join(os.path.dirname(kdb_dir), "portability_gems.json"))
        cands.append(os.path.join(kdb_dir, "portability_gems.json"))
        if os.path.realpath(kernel_db_path) == os.path.realpath(DEFAULT_KERNEL_DB):
            cands.append(os.path.join(_REPO_ROOT, "outputs", "portability_gems.json"))

    chosen: Optional[str] = None
    for p in cands:
        if p and os.path.isfile(p) and not os.path.islink(p):
            chosen = p
            break
    if not chosen:
        return None

    try:
        with open(chosen, "r", encoding="utf-8") as f:
            doc = json.load(f)
    except (OSError, json.JSONDecodeError):
        return None

    raw_targets = [t for t in (doc.get("targets") or []) if isinstance(t, dict) and t.get("name")]
    if not raw_targets:
        return None

    # Ensure portability_gems.json belongs to this kernel.db (avoid mixing RH JSON onto tiny_demo DB)
    probe = str(raw_targets[0]["name"])
    if conn.execute("SELECT 1 FROM decls WHERE name = ? LIMIT 1", (probe,)).fetchone() is None:
        return None

    n = len(raw_targets)
    overlap = doc.get("overlap") if isinstance(doc.get("overlap"), dict) else {}
    proj_mat = overlap.get("project_decls_matrix")
    has_mat = (
        isinstance(proj_mat, list)
        and len(proj_mat) == n
        and all(isinstance(row, list) and len(row) == n for row in proj_mat)
    )

    visited: Set[int] = set()
    components: List[List[int]] = []
    for i in range(n):
        if i in visited:
            continue
        comp: List[int] = []
        q: collections.deque[int] = collections.deque([i])
        visited.add(i)
        while q:
            u = q.popleft()
            comp.append(u)
            if has_mat:
                for v in range(n):
                    if v != u and v not in visited and (proj_mat[u][v] or 0) > 0:
                        visited.add(v)
                        q.append(v)
        comp.sort()
        components.append(comp)

    islands: List[Dict[str, Any]] = []
    for idx, comp in enumerate(components, 1):
        members = [raw_targets[m] for m in comp]
        lead = max(
            members,
            key=lambda t: (int((t.get("cone") or {}).get("project_decls") or 0), str(t.get("name") or "")),
        )
        lead_name = str(lead.get("name") or "")
        inter_max = 0
        if has_mat:
            cset = set(comp)
            for u in comp:
                for v in range(n):
                    if v not in cset:
                        inter_max = max(inter_max, int(proj_mat[u][v] or 0))
        tiers = sorted({str((m.get("contamination") or {}).get("tier") or "unknown") for m in members})
        proj_max = max(int((m.get("cone") or {}).get("project_decls") or 0) for m in members)
        ext_max = max(int((m.get("boundary") or {}).get("direct_external_decls") or 0) for m in members)
        islands.append({
            "id": f"island_{idx}",
            "lead_target": lead_name,
            "short_label": _short_name(lead_name, 26),
            "members_count": len(members),
            "member_names": [str(m.get("name") or "") for m in members],
            "tiers": tiers,
            "standalone_ready": "standalone-ready" in tiers,
            "max_project_decls": proj_max,
            "max_external_decls": ext_max,
            "inter_island_overlap": inter_max,
            "pairwise_disjoint": inter_max == 0,
        })
    islands.sort(key=lambda isl: (-isl["max_project_decls"], isl["lead_target"]))
    meta = {
        "source": _rel_display_path(chosen),
        "targets_count": n,
        "islands_count": len(islands),
        "pairwise_disjoint_count": sum(1 for isl in islands if isl["pairwise_disjoint"]),
    }
    return islands, meta


def _compute_fallback_islands(
    conn: sqlite3.Connection,
    roots: Sequence[Dict[str, Any]],
    pillars: Sequence[Dict[str, Any]],
    tree_id: Optional[int],
    total_decls: int,
) -> Tuple[List[Dict[str, Any]], Dict[str, Any]]:
    """Compute disjoint island summary directly from kernel.db when portability_gems.json is absent."""
    has_reach = _has_table(conn, "reach")
    cands: List[Dict[str, Any]] = []
    seen: Set[int] = set()
    for p in pillars:
        did = int(p["decl_id"])
        if did not in seen and p.get("role") == "pillar":
            seen.add(did)
            cands.append({"decl_id": did, "name": p["name"], "size": int(p["subtree_size"])})
    for r in roots:
        did = int(r["decl_id"])
        if did not in seen:
            seen.add(did)
            sz = 0
            if tree_id is not None:
                row = conn.execute(
                    "SELECT subtree_size FROM dom WHERE tree_id = ? AND decl_id = ?",
                    (tree_id, did),
                ).fetchone()
                if row:
                    sz = int(row[0])
            cands.append({"decl_id": did, "name": r["name"], "size": sz})

    if not cands:
        return [], {"source": "computed", "targets_count": 0, "islands_count": 0, "pairwise_disjoint_count": 0}

    # Keep mutually non-overlapping dominator subtrees (no candidate dominates another)
    kept: List[Dict[str, Any]] = []
    if tree_id is not None:
        id_set = {c["decl_id"] for c in cands}
        ancestor_map: Dict[int, Set[int]] = {}
        for c in cands[:12]:
            did = c["decl_id"]
            anc: Set[int] = set()
            cur = did
            for _ in range(32):
                row = conn.execute(
                    "SELECT idom FROM dom WHERE tree_id = ? AND decl_id = ?",
                    (tree_id, cur),
                ).fetchone()
                if not row or row[0] is None:
                    break
                parent = int(row[0])
                if parent in anc:
                    break
                anc.add(parent)
                cur = parent
            ancestor_map[did] = anc
        for c in cands[:10]:
            did = c["decl_id"]
            ancs = ancestor_map.get(did, set())
            # Skip hubs that strictly dominate multiple kept islands
            dominates_kept = any(did in ancestor_map.get(k["decl_id"], set()) for k in kept)
            dominated_by_kept = any(k["decl_id"] in ancs for k in kept)
            if not dominates_kept and not dominated_by_kept:
                kept.append(c)
            if len(kept) >= 6:
                break
    if not kept:
        kept = cands[: min(4, len(cands))]

    # On small DBs, measure direct/reach pairwise overlap accurately
    islands: List[Dict[str, Any]] = []
    for idx, c in enumerate(kept, 1):
        did = c["decl_id"]
        ext_cnt = int(
            conn.execute(
                "SELECT COUNT(*) FROM edges e JOIN decls d ON d.id = e.dst WHERE e.src = ? AND e.kind IN (1, 2, 3)",
                (did,),
            ).fetchone()[0]
        )
        overlap = 0
        if has_reach and total_decls <= 25_000 and len(kept) > 1:
            others = [k["decl_id"] for k in kept if k["decl_id"] != did]
            # Check edge overlap between direct cones on small graphs
            for od in others:
                ov = conn.execute(
                    "SELECT COUNT(*) FROM edges e1 JOIN edges e2 ON e1.dst = e2.dst WHERE e1.src = ? AND e2.src = ?",
                    (did, od),
                ).fetchone()[0]
                overlap = max(overlap, int(ov))
        islands.append({
            "id": f"island_{idx}",
            "lead_target": c["name"],
            "short_label": _short_name(c["name"], 26),
            "members_count": 1,
            "member_names": [c["name"]],
            "tiers": ["standalone-ready" if overlap == 0 else "scoped"],
            "standalone_ready": overlap == 0,
            "max_project_decls": int(c["size"]),
            "max_external_decls": ext_cnt,
            "inter_island_overlap": overlap,
            "pairwise_disjoint": overlap == 0,
        })
    return islands, {
        "source": "computed",
        "targets_count": len(islands),
        "islands_count": len(islands),
        "pairwise_disjoint_count": sum(1 for isl in islands if isl["pairwise_disjoint"]),
    }


def _query_macro_motifs(
    conn: sqlite3.Connection,
    total_decls: int,
    has_dm: bool,
    max_motifs: int = 10,
) -> List[Dict[str, Any]]:
    """Query top repeated ``k1n`` and ``k1a`` signature-hash motif clusters using indexed scans."""
    min_rep = 2 if total_decls <= 5000 else 10
    has_consts = _has_table(conn, "consts")
    use_consts = has_consts and (
        conn.execute("SELECT 1 FROM consts WHERE sighash IS NOT NULL LIMIT 1").fetchone() is not None
    )

    candidates: List[Tuple[str, str, int]] = []  # (scheme, sighash, raw_count)
    for scheme, col in (("k1n", "sighash"), ("k1a", "sighash_anon")):
        if use_consts:
            rows = conn.execute(
                f"SELECT {col}, COUNT(*) AS cnt FROM consts "
                f"WHERE {col} IS NOT NULL GROUP BY {col} HAVING cnt >= ? "
                f"ORDER BY cnt DESC, {col} ASC LIMIT 24",
                (min_rep,),
            ).fetchall()
        else:
            rows = conn.execute(
                f"SELECT {col}, COUNT(*) AS cnt FROM decls "
                f"WHERE {col} IS NOT NULL GROUP BY {col} HAVING cnt >= ? "
                f"ORDER BY cnt DESC, {col} ASC LIMIT 24",
                (min_rep,),
            ).fetchall()
        for sh, cnt in rows:
            candidates.append((scheme, str(sh), int(cnt)))

    if not candidates:
        return []

    enriched: List[Dict[str, Any]] = []
    seen_rep_count: Set[Tuple[str, int]] = set()
    for scheme, sh, raw_cnt in candidates:
        col = "sighash" if scheme == "k1n" else "sighash_anon"
        if use_consts:
            if has_dm:
                srows = conn.execute(
                    f"SELECT d.name, d.kind, d.live_mask, d.value_nodes, dm.module "
                    f"FROM consts c JOIN decls d ON d.id = c.decl_id "
                    f"LEFT JOIN decl_module dm ON dm.decl_id = d.id "
                    f"WHERE c.{col} = ? LIMIT 30",
                    (sh,),
                ).fetchall()
            else:
                srows = [
                    (r[0], r[1], r[2], r[3], None)
                    for r in conn.execute(
                        f"SELECT d.name, d.kind, d.live_mask, d.value_nodes "
                        f"FROM consts c JOIN decls d ON d.id = c.decl_id "
                        f"WHERE c.{col} = ? LIMIT 30",
                        (sh,),
                    ).fetchall()
                ]
        else:
            srows = [
                (r[0], r[1], r[2], r[3], None)
                for r in conn.execute(
                    f"SELECT name, kind, live_mask, value_nodes FROM decls WHERE {col} = ? LIMIT 30",
                    (sh,),
                ).fetchall()
            ]
        if not srows:
            continue
        live_samples = [r for r in srows if int(r[2]) != 0]
        pool = live_samples or srows
        proj_pool = [r for r in pool if r[4] is not None] or pool
        non_aux = [r for r in proj_pool if not _is_aux_name(str(r[0]))] or proj_pool
        rep = min(non_aux, key=lambda r: (len(str(r[0])), str(r[0])))
        rep_name = str(rep[0])
        rep_kind = str(rep[1])
        rep_mod = rep[4]
        max_vn = max(int(r[3]) for r in srows)
        is_aux_cluster = all(_is_aux_name(str(r[0])) for r in pool)

        # Deduplicate k1a when identical to k1n on the same representative & count
        sig_key = (rep_name, raw_cnt)
        if sig_key in seen_rep_count and scheme == "k1a":
            continue
        seen_rep_count.add(sig_key)

        enriched.append({
            "scheme": scheme,
            "sighash": sh,
            "short_hash": sh.split(":", 1)[-1][:10],
            "count": raw_cnt,
            "sample_name": rep_name,
            "short_label": _short_name(rep_name, 26),
            "sample_kind": rep_kind,
            "sample_module": rep_mod,
            "max_value_nodes": max_vn,
            "is_aux": is_aux_cluster,
            "live_in_sample": len(live_samples),
        })

    # Prioritize live, non-aux, high-repeat clusters (while preserving huge top counts)
    enriched.sort(
        key=lambda m: (
            0 if m["live_in_sample"] > 0 else 1,
            0 if not m["is_aux"] else 1,
            -m["count"],
            m["scheme"],
            m["sighash"],
        )
    )
    selected = enriched[:max_motifs]
    for idx, item in enumerate(selected):
        item["color"] = MOTIF_PALETTE[idx % len(MOTIF_PALETTE)]
        item["bucket"] = f"motif_{idx + 1}"
    return selected


def build_macro_circuit(
    kernel_db_path: str = DEFAULT_KERNEL_DB,
    *,
    src_root: Optional[str] = None,
    portability_json: Optional[str] = None,
    dom_threshold: Optional[int] = None,
    max_nodes: int = 12,
    title: Optional[str] = None,
) -> Dict[str, Any]:
    """Build Zoom 0 (macro repository circuit) JSON payload ``leanre.circuit/1``."""
    t0 = time.time()
    real_src = _resolve_default_src_root(kernel_db_path, src_root)
    conn = _open_ro(kernel_db_path)
    try:
        has_dm = _kernel._has_decl_module_rows(conn)
        has_roots = _has_table(conn, "roots")
        has_dom = _has_table(conn, "dom") and _has_table(conn, "dom_trees")

        # 1. Corpus counts & dead mass
        by_kind: Dict[str, Dict[str, int]] = {}
        total_decls = 0
        live_decls = 0
        for kind, tot, liv in conn.execute(
            "SELECT kind, COUNT(*), COALESCE(SUM(CASE WHEN live_mask != 0 THEN 1 ELSE 0 END), 0) "
            "FROM decls GROUP BY kind ORDER BY kind"
        ):
            t_i, l_i = int(tot), int(liv)
            total_decls += t_i
            live_decls += l_i
            by_kind[str(kind)] = {"total": t_i, "live": l_i, "dead": t_i - l_i}
        dead_decls = max(0, total_decls - live_decls)

        dead_sample: List[Dict[str, Any]] = []
        if dead_decls > 0:
            for r in conn.execute(
                "SELECT name, kind, value_nodes FROM decls WHERE live_mask = 0 "
                "ORDER BY value_nodes DESC, id ASC LIMIT 6"
            ):
                dead_sample.append({"name": str(r[0]), "kind": str(r[1]), "value_nodes": int(r[2])})

        # 2. Roots
        roots: List[Dict[str, Any]] = []
        if has_roots:
            for rid, rname, rdid, rgrp in conn.execute("SELECT id, name, decl_id, grp FROM roots ORDER BY id"):
                drow = conn.execute(
                    "SELECT kind, fan_in, fan_out FROM decls WHERE id = ?",
                    (int(rdid),),
                ).fetchone()
                roots.append({
                    "root_id": int(rid),
                    "decl_id": int(rdid),
                    "name": str(rname),
                    "grp": str(rgrp),
                    "kind": str(drow[0]) if drow else "thm",
                    "fan_in": int(drow[1]) if drow else 0,
                    "fan_out": int(drow[2]) if drow else 0,
                })

        # 3. Dominator pillars + shared diamond detection
        tree_id: Optional[int] = None
        tree_label = "ALL"
        if has_dom:
            trow = conn.execute("SELECT id, label FROM dom_trees WHERE label='ALL'").fetchone()
            if trow is None:
                trow = conn.execute("SELECT id, label FROM dom_trees ORDER BY id LIMIT 1").fetchone()
            if trow is not None:
                tree_id = int(trow[0])
                tree_label = str(trow[1])

        if dom_threshold is None:
            if live_decls <= 120:
                eff_threshold = max(2, live_decls // 6)
            else:
                eff_threshold = max(10, int(live_decls * 0.025))
        else:
            eff_threshold = max(1, int(dom_threshold))

        pillars: List[Dict[str, Any]] = []
        diamond_hubs: List[Dict[str, Any]] = []
        shared_between_pillars_decls = 0
        shared_diamond_roots = 0
        cross_pillar_shared_edges = 0
        multi_root_shared = 0

        if tree_id is not None:
            dom_rows = conn.execute(
                "SELECT d.id, d.name, d.kind, dm.depth, dm.subtree_size, dm.idom, d.fan_in, d.fan_out "
                "FROM dom dm JOIN decls d ON d.id = dm.decl_id "
                "WHERE dm.tree_id = ? AND dm.subtree_size >= ? "
                "ORDER BY dm.subtree_size DESC, d.id ASC LIMIT 60",
                (tree_id, eff_threshold),
            ).fetchall()
            if len(dom_rows) < 4:
                dom_rows = conn.execute(
                    "SELECT d.id, d.name, d.kind, dm.depth, dm.subtree_size, dm.idom, d.fan_in, d.fan_out "
                    "FROM dom dm JOIN decls d ON d.id = dm.decl_id "
                    "WHERE dm.tree_id = ? ORDER BY dm.subtree_size DESC, d.id ASC LIMIT 20",
                    (tree_id,),
                ).fetchall()

            dom_by_id: Dict[int, Dict[str, Any]] = {}
            children_by_idom: Dict[int, List[Dict[str, Any]]] = collections.defaultdict(list)
            for did, dname, dknd, dep, sub_sz, idom, fi, fo in dom_rows:
                item = {
                    "decl_id": int(did),
                    "name": str(dname),
                    "kind": str(dknd),
                    "depth": int(dep),
                    "subtree_size": int(sub_sz),
                    "idom": int(idom) if idom is not None else None,
                    "fan_in": int(fi),
                    "fan_out": int(fo),
                }
                dom_by_id[item["decl_id"]] = item
                if item["idom"] is not None:
                    children_by_idom[item["idom"]].append(item)

            # Annotate spine hubs vs major branch pillars
            for did, item in dom_by_id.items():
                kids = children_by_idom.get(did, [])
                sig_kids = [k for k in kids if k["subtree_size"] >= max(2, int(item["subtree_size"] * 0.04))]
                if len(sig_kids) >= 2:
                    item["role"] = "spine_hub"
                elif len(kids) == 1 and kids[0]["subtree_size"] >= int(item["subtree_size"] * 0.90):
                    item["role"] = "spine_hub"
                else:
                    item["role"] = "pillar"

            pillars = list(dom_by_id.values())[: max(4, min(max_nodes, 14))]
            pillar_ids = {p["decl_id"] for p in pillars}

            # Compute shared diamond children at every multi-branch hub
            for did, item in dom_by_id.items():
                kids = children_by_idom.get(did, [])
                sig_kids = [k for k in kids if k["subtree_size"] >= max(2, int(item["subtree_size"] * 0.04))]
                if len(sig_kids) < 2:
                    continue
                tot_kids, tot_sum = conn.execute(
                    "SELECT COUNT(*), COALESCE(SUM(subtree_size), 0) FROM dom WHERE tree_id = ? AND idom = ?",
                    (tree_id, did),
                ).fetchone()
                sig_sum = sum(k["subtree_size"] for k in sig_kids)
                rem_roots = max(0, int(tot_kids) - len(sig_kids))
                rem_decls = max(0, int(tot_sum) - sig_sum)
                if rem_decls > 0:
                    diamond_hubs.append({
                        "hub_id": did,
                        "hub_name": item["name"],
                        "branch_pillars": [k["name"] for k in sig_kids],
                        "branch_pillar_ids": [k["decl_id"] for k in sig_kids],
                        "diamond_roots": rem_roots,
                        "diamond_decls": rem_decls,
                    })
                    shared_diamond_roots += rem_roots
                    shared_between_pillars_decls += rem_decls

            # Direct shared outgoing targets between top distinct branch pillars
            branch_pids = [p["decl_id"] for p in pillars if p.get("role") == "pillar"][:8]
            if len(branch_pids) >= 2:
                ph = ",".join("?" for _ in branch_pids)
                cross_pillar_shared_edges = int(
                    conn.execute(
                        f"SELECT COUNT(*) FROM (SELECT dst FROM edges WHERE src IN ({ph}) GROUP BY dst HAVING COUNT(*) >= 2)",
                        branch_pids,
                    ).fetchone()[0]
                )
            elif len(roots) >= 2 and total_decls <= 25_000 and _has_table(conn, "reach"):
                multi_root_shared = int(
                    conn.execute(
                        "SELECT COUNT(*) FROM (SELECT decl_id FROM reach GROUP BY decl_id HAVING COUNT(*) >= 2)"
                    ).fetchone()[0]
                )

            if not roots:
                root_rows = [p for p in pillars if p["idom"] is None][:4]
                for idx, rr in enumerate(root_rows):
                    roots.append({
                        "root_id": idx,
                        "decl_id": rr["decl_id"],
                        "name": rr["name"],
                        "grp": "ROOT",
                        "kind": rr["kind"],
                        "fan_in": rr["fan_in"],
                        "fan_out": rr["fan_out"],
                    })

        # Fallback if no dom tree existed
        if not pillars and roots:
            for r in roots:
                pillars.append({
                    "decl_id": r["decl_id"],
                    "name": r["name"],
                    "kind": r["kind"],
                    "depth": 0,
                    "subtree_size": 1,
                    "idom": None,
                    "fan_in": r["fan_in"],
                    "fan_out": r["fan_out"],
                    "role": "pillar",
                })
            pillar_ids = {p["decl_id"] for p in pillars}
        else:
            pillar_ids = {p["decl_id"] for p in pillars}

        # 4. Motif clusters (`k1n` / `k1a`)
        motifs = _query_macro_motifs(conn, total_decls, has_dm, max_motifs=min(max_nodes, 10))

        # 5. Disjoint standalone portable islands
        port_loaded = _load_matching_portability_islands(conn, kernel_db_path, portability_json)
        if port_loaded is not None:
            islands, islands_meta = port_loaded
        else:
            islands, islands_meta = _compute_fallback_islands(conn, roots, pillars, tree_id, total_decls)

        # 6. Assemble canonical leanre.circuit/1 nodes & wires
        nodes: List[Dict[str, Any]] = []
        wires: List[Dict[str, Any]] = []

        for r in roots[:8]:
            nodes.append({
                "id": f"root:{r['decl_id']}",
                "label": _short_name(r["name"], 26),
                "full_name": r["name"],
                "kind": "root",
                "status": "live",
                "lane": 0,
                "badge": r["grp"],
                "metrics": {"fan_in": r["fan_in"], "fan_out": r["fan_out"]},
                "zoom_target": {"mode": "theorem", "target": r["name"]},
                "tooltip": f"Root [{r['grp']}]: {r['name']} (fan_out={r['fan_out']})",
            })

        nodes.append({
            "id": "dead_mass",
            "label": f"Dead Mass ({_fmt_int(dead_decls)})",
            "full_name": "Unreachable declarations (live_mask = 0)",
            "kind": "dead_mass",
            "status": "dead" if dead_decls > 0 else "live",
            "lane": 0,
            "badge": f"{(100.0 * dead_decls / max(1, total_decls)):.2f}%",
            "metrics": {"dead_decls": dead_decls, "total_decls": total_decls, "sample": dead_sample},
            "zoom_target": None,
            "tooltip": f"Unreachable (live=0): {dead_decls:,} / {total_decls:,} decls",
        })

        for p in pillars:
            pct = (100.0 * p["subtree_size"] / max(1, live_decls))
            nodes.append({
                "id": f"dom:{p['decl_id']}",
                "label": _short_name(p["name"], 26),
                "full_name": p["name"],
                "kind": p.get("role", "pillar"),
                "status": "live",
                "lane": 1,
                "badge": f"dom {_fmt_int(p['subtree_size'])} ({pct:.1f}%)",
                "metrics": {
                    "subtree_size": p["subtree_size"],
                    "depth": p["depth"],
                    "fan_in": p["fan_in"],
                    "fan_out": p["fan_out"],
                    "pct_live": round(pct, 2),
                },
                "zoom_target": {"mode": "theorem", "target": p["name"]},
                "tooltip": f"Dominator {p['name']} | subtree={p['subtree_size']:,} ({pct:.1f}%), depth={p['depth']}",
            })
            if p["idom"] is not None and p["idom"] in pillar_ids:
                wires.append({
                    "id": f"w:dom:{p['idom']}->{p['decl_id']}",
                    "src": f"dom:{p['idom']}",
                    "dst": f"dom:{p['decl_id']}",
                    "kind": "dom_spine",
                    "status": "used",
                    "color_key": "cyan" if p.get("role") == "spine_hub" else "emerald",
                    "label": "",
                })

        # Connect roots to top dominator hub if roots aren't already in pillar_ids
        if roots and pillars:
            top_dom_id = f"dom:{pillars[0]['decl_id']}"
            for r in roots[:8]:
                rid_str = f"root:{r['decl_id']}"
                if r["decl_id"] in pillar_ids:
                    wires.append({
                        "id": f"w:r2d:{r['decl_id']}",
                        "src": rid_str,
                        "dst": f"dom:{r['decl_id']}",
                        "kind": "root_entry",
                        "status": "used",
                        "color_key": "emerald",
                        "label": "",
                    })
                else:
                    wires.append({
                        "id": f"w:r2top:{r['decl_id']}",
                        "src": rid_str,
                        "dst": top_dom_id,
                        "kind": "root_entry",
                        "status": "used",
                        "color_key": "blue",
                        "label": "",
                    })

        # Shared diamond hub node
        diamond_summary_decls = shared_between_pillars_decls or cross_pillar_shared_edges or multi_root_shared
        top_dhub = diamond_hubs[0] if diamond_hubs else None
        diamond_node = {
            "id": "shared_diamond",
            "label": f"Shared Diamond ({_fmt_int(diamond_summary_decls)})",
            "full_name": "Shared subgraph reached across >= 2 major pillars",
            "kind": "diamond",
            "status": "live",
            "lane": 1,
            "badge": (
                f"{_fmt_int(shared_diamond_roots)} roots"
                if shared_diamond_roots > 0
                else f"{_fmt_int(cross_pillar_shared_edges or multi_root_shared)} shared"
            ),
            "metrics": {
                "shared_decls": shared_between_pillars_decls,
                "shared_roots": shared_diamond_roots,
                "cross_pillar_direct_edges": cross_pillar_shared_edges,
                "multi_root_shared": multi_root_shared,
                "hubs": diamond_hubs[:4],
            },
            "zoom_target": {"mode": "theorem", "target": top_dhub["hub_name"]} if top_dhub else None,
            "tooltip": (
                f"Shared diamond across >= 2 pillars: {shared_diamond_roots:,} roots / "
                f"{shared_between_pillars_decls:,} decls (cross-pillar edges={cross_pillar_shared_edges:,})"
            ),
        }
        nodes.append(diamond_node)
        if top_dhub:
            for bpid in top_dhub["branch_pillar_ids"][:4]:
                if bpid in pillar_ids:
                    wires.append({
                        "id": f"w:dia:{bpid}",
                        "src": f"dom:{bpid}",
                        "dst": "shared_diamond",
                        "kind": "diamond_share",
                        "status": "used",
                        "color_key": "violet",
                        "label": "",
                    })

        for idx, m in enumerate(motifs):
            nodes.append({
                "id": f"motif:{idx}",
                "label": m["short_label"],
                "full_name": m["sample_name"],
                "kind": "motif_cluster",
                "status": "live" if m["live_in_sample"] > 0 else "dead",
                "lane": 2,
                "color": m["color"],
                "badge": f"{m['scheme']} ×{_fmt_int(m['count'])}",
                "metrics": m,
                "zoom_target": {"mode": "theorem", "target": m["sample_name"]},
                "tooltip": f"{m['sighash']} ({m['count']:,} decls) e.g. {m['sample_name']}",
            })

        for isl in islands[:8]:
            nodes.append({
                "id": isl["id"],
                "label": isl["short_label"],
                "full_name": isl["lead_target"],
                "kind": "island",
                "status": "projected" if isl["standalone_ready"] else "conditional_prop",
                "lane": 3,
                "badge": f"{_fmt_int(isl['max_project_decls'])} proj",
                "metrics": isl,
                "zoom_target": {"mode": "theorem", "target": isl["lead_target"]},
                "tooltip": (
                    f"Island {isl['lead_target']}: {isl['max_project_decls']:,} project decls, "
                    f"disjoint={isl['pairwise_disjoint']}, tiers={','.join(isl['tiers'])}"
                ),
            })

        elapsed = round(time.time() - t0, 3)
        return {
            "schema": SCHEMA_VERSION,
            "mode": "macro",
            "title": title or "Macro Proof-Circuit Map",
            "target": None,
            "pins": {
                "kernel_db": _rel_display_path(kernel_db_path),
                "src_root": _rel_display_path(real_src),
                "source_mode": "source+kernel" if real_src else "kernel_only",
                "dom_tree": tree_label,
                "dom_threshold": eff_threshold,
                "elapsed_seconds": elapsed,
            },
            "stats": {
                "total_decls": total_decls,
                "live_decls": live_decls,
                "dead_decls": dead_decls,
                "roots_count": len(roots),
                "pillars_count": len(pillars),
                "shared_diamond_roots": shared_diamond_roots,
                "shared_diamond_decls": shared_between_pillars_decls,
                "cross_pillar_shared_edges": cross_pillar_shared_edges,
                "motif_clusters_count": len(motifs),
                "islands_count": len(islands),
                "node_count": len(nodes),
                "wire_count": len(wires),
                "by_kind": by_kind,
            },
            "lanes": [
                {"id": 0, "label": "Roots & Dead Mass"},
                {"id": 1, "label": "Dominator Pillars & Shared Diamonds"},
                {"id": 2, "label": "Repeated Motif Clusters (k1n / k1a)"},
                {"id": 3, "label": "Standalone Portable Islands"},
            ],
            "binders": [],
            "nodes": nodes,
            "wires": wires,
            "badges": [
                {"label": f"live {_fmt_int(live_decls)}", "color_key": "emerald"},
                {"label": f"dead {_fmt_int(dead_decls)}", "color_key": "crimson" if dead_decls else "slate"},
                {"label": f"diamond {_fmt_int(diamond_summary_decls)}", "color_key": "violet"},
                {"label": f"{len(motifs)} motif clusters", "color_key": "cyan"},
                {"label": f"{len(islands)} islands", "color_key": "amber"},
            ],
            "legend": [
                {"label": "Root / Pillar (live)", "color_key": "emerald", "style": "solid"},
                {"label": "Dominator Spine Hub", "color_key": "cyan", "style": "solid"},
                {"label": "Shared Diamond (>=2 pillars)", "color_key": "violet", "style": "solid"},
                {"label": "Dead / Unreachable (live=0)", "color_key": "crimson", "style": "dashed"},
                {"label": "Repeated k1n/k1a Motif (×N)", "color_key": "amber", "style": "badge"},
            ],
            "meta": {
                "roots": roots,
                "pillars": pillars,
                "diamond_hubs": diamond_hubs,
                "motifs": motifs,
                "islands": islands,
                "islands_meta": islands_meta,
                "dead_sample": dead_sample,
            },
        }
    finally:
        conn.close()


# ---------------------------------------------------------------------------
# Zoom 1 — Record / Interface Pin-Board (`--mode bundle`)
# ---------------------------------------------------------------------------

def _classify_consumer_drops(
    kernel_db_path: str,
    src_root: Optional[str],
    target_fqn: str,
    consumers: Sequence[Dict[str, Any]],
) -> Tuple[Set[str], Dict[str, Any]]:
    """Run kernel.hygiene_decls on consumers to detect dropped/dangling bundle inputs."""
    if not src_root or not consumers:
        return set(), {"audited": 0, "dropped_target_count": 0, "source_checked": False}

    target_leaf = target_fqn.rsplit(".", 1)[-1]
    check_names = [str(c["name"]) for c in consumers[:220] if c.get("name")]
    if not check_names:
        return set(), {"audited": 0, "dropped_target_count": 0, "source_checked": False}

    try:
        rep = _kernel.hygiene_decls(
            kernel_db_path,
            check_names,
            src_root=src_root,
            only="dropped",
            max_decls=max(250, len(check_names) + 10),
            continue_on_error=True,
        )
    except Exception:
        return set(), {"audited": 0, "dropped_target_count": 0, "source_checked": False}

    dropped_names: Set[str] = set()
    for entry in rep.get("decls") or []:
        cname = str(entry.get("name") or "")
        for f in entry.get("findings") or []:
            pt = str(f.get("param_type") or "")
            det = str(f.get("detail") or "")
            if target_leaf in pt or target_leaf in det or target_fqn in pt or target_fqn in det:
                dropped_names.add(cname)
                break

    audited = int((rep.get("summary") or {}).get("decls_audited") or len(check_names))
    return dropped_names, {
        "audited": audited,
        "dropped_target_count": len(dropped_names),
        "source_checked": True,
    }


def _select_balanced_producers(
    sites: Sequence[Dict[str, Any]],
    via_sites: Sequence[Dict[str, Any]],
    max_nodes: int,
) -> List[Dict[str, Any]]:
    """Select up to `max_nodes` producers balanced across root/local/via_extends/self roles."""
    buckets: Dict[str, List[Dict[str, Any]]] = {
        "root": [],
        "local_witness": [],
        "via_extends": [],
        "self_transform": [],
    }
    for p in sites:
        if p.get("takes_self_param"):
            role = "self_transform"
        elif p.get("is_local_witness"):
            role = "local_witness"
        else:
            role = "root"
        item = dict(p)
        item["producer_role"] = role
        buckets[role].append(item)
    for p in via_sites:
        item = dict(p)
        item["producer_role"] = "via_extends"
        buckets["via_extends"].append(item)

    chosen: List[Dict[str, Any]] = []
    seen: Set[str] = set()
    order = ("root", "local_witness", "via_extends", "self_transform")
    idx = 0
    while len(chosen) < max_nodes:
        progressed = False
        for key in order:
            if idx < len(buckets[key]):
                cand = buckets[key][idx]
                nm = str(cand.get("name") or "")
                if nm not in seen:
                    seen.add(nm)
                    chosen.append(cand)
                    if len(chosen) >= max_nodes:
                        break
                progressed = True
        if not progressed:
            break
        idx += 1
    return chosen


def build_bundle_circuit(
    kernel_db_path: str = DEFAULT_KERNEL_DB,
    target: str = "",
    *,
    src_root: Optional[str] = None,
    max_nodes: int = 16,
    exact_case: bool = False,
    title: Optional[str] = None,
) -> Dict[str, Any]:
    """Build Zoom 1 (record / interface pin-board) JSON payload ``leanre.circuit/1``."""
    t0 = time.time()
    if not target or not target.strip():
        raise ValueError("bundle mode requires a target structure, class, or Prop-def name")
    cap = max(2, int(max_nodes))
    real_src = _resolve_default_src_root(kernel_db_path, src_root)

    inst_rep = _bundles.run_instantiations(
        kernel_db_path=kernel_db_path,
        src_root=real_src,
        instantiations=target,
        live_only=False,
        limit=max(220, cap),
        exact=exact_case,
        continue_on_error=False,
    )
    targets = inst_rep.get("targets") or []
    if not targets:
        raise LookupError(f"No structure or Prop-def matched {target!r}")
    t_obj = targets[0]
    fqn = str(t_obj["name"])
    is_prop_def = bool(t_obj.get("is_prop_def"))

    # Collect field / conjunct pin statuses
    pins: List[Dict[str, Any]] = []
    bundle_rec: Optional[Dict[str, Any]] = None
    if not is_prop_def:
        try:
            brep = _bundles.run_bundles(
                kernel_db_path=kernel_db_path,
                src_root=real_src,
                structure=fqn,
                top=10,
                only="all",
                include_eliminated=True,
                exact=True,
                continue_on_error=True,
            )
            for b in brep.get("bundles") or []:
                if b.get("name") == fqn:
                    bundle_rec = b
                    break
        except Exception:
            bundle_rec = None

    if bundle_rec is not None and bundle_rec.get("fields"):
        for idx, fld in enumerate(bundle_rec["fields"]):
            is_lit_true = bool(fld.get("is_literal_true"))
            is_cond = bool(fld.get("is_conditional_prop"))
            projected = bool(fld.get("projected"))
            if is_lit_true:
                st = "literal_true"
            elif is_cond:
                st = "conditional_prop"
            elif not projected:
                st = "unread"
            else:
                st = "projected"
            pins.append({
                "index": idx,
                "id": f"pin:{idx}",
                "name": str(fld["name"]),
                "status": st,
                "color_key": _PIN_STATUS_COLORS[st],
                "projected": projected,
                "is_conditional_prop": is_cond,
                "is_literal_true": is_lit_true,
                "fan_in": int(fld.get("fan_in") or 0),
                "decl_kind": fld.get("decl_kind"),
                "type": _clip_chars(fld.get("type") or "", 140),
            })
    elif is_prop_def:
        conjs = list(t_obj.get("conjuncts") or [])
        unread_legs: Set[int] = set()
        true_legs: Set[int] = set()
        if real_src:
            try:
                h_self = _kernel.hygiene_decls(
                    kernel_db_path,
                    [fqn],
                    src_root=real_src,
                    only="all",
                    continue_on_error=True,
                )
                d_self = (h_self.get("decls") or [{}])[0]
                tsum = d_self.get("tuple_summary") or {}
                unread_legs = {int(x) for x in (tsum.get("unread_legs") or [])}
                for f in d_self.get("findings") or []:
                    if f.get("kind") == "conjunct_true_slot" and f.get("conjunct_index") is not None:
                        true_legs.add(int(f["conjunct_index"]))
            except Exception:
                pass
        for idx, conj in enumerate(conjs):
            c_clean = _clean_text(conj)
            is_lit_true = (idx in true_legs) or (c_clean in ("True", "_root_.True"))
            is_cond = _bundles._is_conditional_prop_field(conj, True, None)
            projected = idx not in unread_legs
            if is_lit_true:
                st = "literal_true"
            elif is_cond:
                st = "conditional_prop"
            elif not projected:
                st = "unread"
            else:
                st = "projected"
            pins.append({
                "index": idx,
                "id": f"pin:{idx}",
                "name": f"[{idx}] {_clip_chars(c_clean, 30)}",
                "status": st,
                "color_key": _PIN_STATUS_COLORS[st],
                "projected": projected,
                "is_conditional_prop": is_cond,
                "is_literal_true": is_lit_true,
                "fan_in": 0,
                "decl_kind": "conjunct",
                "type": _clip_chars(c_clean, 140),
            })

    # Fallback when kernel-only mode had empty fields
    if not pins:
        proj_names = list((t_obj.get("projections_and_helpers") or {}).get("field_projections") or [])
        for idx, pname in enumerate(proj_names):
            pins.append({
                "index": idx,
                "id": f"pin:{idx}",
                "name": str(pname),
                "status": "projected",
                "color_key": "emerald",
                "projected": True,
                "is_conditional_prop": False,
                "is_literal_true": False,
                "fan_in": 0,
                "decl_kind": None,
                "type": "",
            })

    # Left bank: producers
    prod_obj = t_obj.get("producers") or {}
    shown_prods = _select_balanced_producers(
        prod_obj.get("sites") or [],
        prod_obj.get("via_extends_sites") or [],
        cap,
    )
    total_prods_all = int(prod_obj.get("total_count") or 0) + int(prod_obj.get("via_extends_count") or 0)

    # Right bank: consumers + hygiene dangling input audit
    cons_obj = t_obj.get("consumers") or {}
    all_cons = list(cons_obj.get("top_examples") or [])
    dropped_cons_set, drop_audit_meta = _classify_consumer_drops(
        kernel_db_path, real_src, fqn, all_cons
    )
    shown_cons = all_cons[:cap]
    total_cons_all = int(cons_obj.get("total_count") or len(all_cons))

    nodes: List[Dict[str, Any]] = []
    wires: List[Dict[str, Any]] = []

    chip_id = "chip:target"
    pin_counts = collections.Counter(p["status"] for p in pins)
    nodes.append({
        "id": chip_id,
        "label": _short_name(fqn, 34),
        "full_name": fqn,
        "kind": "chip",
        "status": "live" if t_obj.get("live_mask") else "dead",
        "lane": 1,
        "badge": f"{t_obj.get('source_kind', 'structure')} · {t_obj.get('universe_kind', '?')}",
        "anchor": t_obj.get("anchor"),
        "pins": pins,
        "metrics": {
            "total_fields": len(pins),
            "projected": pin_counts["projected"],
            "unread": pin_counts["unread"],
            "conditional_prop": pin_counts["conditional_prop"],
            "literal_true": pin_counts["literal_true"],
            "fan_in": int(t_obj.get("fan_in") or 0),
        },
        "zoom_target": None,
        "tooltip": f"{fqn} ({t_obj.get('universe_kind')}) | {len(pins)} pins, fan_in={t_obj.get('fan_in')}",
    })

    role_color = {
        "root": "emerald",
        "local_witness": "cyan",
        "via_extends": "violet",
        "self_transform": "amber",
    }
    role_badge = {
        "root": "root",
        "local_witness": "local",
        "via_extends": "extends",
        "self_transform": "self→S",
    }

    for idx, p in enumerate(shown_prods):
        pname = str(p["name"])
        prole = p["producer_role"]
        nid = f"prod:{idx}"
        nodes.append({
            "id": nid,
            "label": _short_name(pname, 28),
            "full_name": pname,
            "kind": "producer",
            "producer_role": prole,
            "status": "live" if p.get("live_mask") else "dead",
            "lane": 0,
            "badge": role_badge.get(prole, prole),
            "anchor": p.get("anchor"),
            "metrics": {
                "dom_subtree_size": int(p.get("dom_subtree_size") or 0),
                "via_extends_child": p.get("via_extends_child"),
            },
            "zoom_target": {"mode": "theorem", "target": pname} if p.get("decl_kind") in ("thm", "def") else None,
            "tooltip": f"Producer [{role_badge.get(prole, prole)}]: {pname}",
        })
        wires.append({
            "id": f"w:prod:{idx}",
            "src": nid,
            "dst": chip_id,
            "kind": "producer_in",
            "status": "used",
            "color_key": role_color.get(prole, "emerald"),
            "label": "",
        })

    if total_prods_all > len(shown_prods):
        nodes.append({
            "id": "prod:overflow",
            "label": f"+{_fmt_int(total_prods_all - len(shown_prods))} more producers",
            "full_name": f"{total_prods_all} total producers",
            "kind": "overflow_pill",
            "lane": 0,
            "status": "projected",
            "badge": f"total {_fmt_int(total_prods_all)}",
            "zoom_target": None,
            "tooltip": (
                f"root={prod_obj.get('root_count', 0)}, local={prod_obj.get('local_witness_count', 0)}, "
                f"via_extends={prod_obj.get('via_extends_count', 0)}, self→S={prod_obj.get('self_transform_count', 0)}"
            ),
        })

    for idx, c in enumerate(shown_cons):
        cname = str(c["name"])
        is_dropped = cname in dropped_cons_set
        nid = f"cons:{idx}"
        nodes.append({
            "id": nid,
            "label": _short_name(cname, 28),
            "full_name": cname,
            "kind": "consumer",
            "status": "dangling" if is_dropped else ("live" if c.get("live_mask") else "dead"),
            "drops_target": is_dropped,
            "lane": 2,
            "badge": "DROPPED ×" if is_dropped else c.get("edge_kind", "consumer"),
            "anchor": c.get("anchor"),
            "metrics": {
                "dom_subtree_size": int(c.get("dom_subtree_size") or 0),
                "root_depth": c.get("root_depth"),
            },
            "zoom_target": {"mode": "theorem", "target": cname} if c.get("decl_kind") in ("thm", "def") else None,
            "tooltip": f"Consumer ({'UNPLUGGED/DROPPED input' if is_dropped else 'uses input'}): {cname}",
        })
        wires.append({
            "id": f"w:cons:{idx}",
            "src": chip_id,
            "dst": nid,
            "kind": "consumer_out",
            "status": "dangling" if is_dropped else "used",
            "color_key": "crimson" if is_dropped else "emerald",
            "dangling": is_dropped,
            "label": "×" if is_dropped else "",
        })

    if total_cons_all > len(shown_cons):
        drop_note = ""
        if drop_audit_meta["source_checked"] and drop_audit_meta["audited"] > 0:
            drop_note = f" ({drop_audit_meta['dropped_target_count']}/{drop_audit_meta['audited']} drop input)"
        nodes.append({
            "id": "cons:overflow",
            "label": f"+{_fmt_int(total_cons_all - len(shown_cons))} more consumers{drop_note}",
            "full_name": f"{total_cons_all} total consumers",
            "kind": "overflow_pill",
            "lane": 2,
            "status": "dangling" if drop_audit_meta["dropped_target_count"] > 0 else "projected",
            "badge": f"total {_fmt_int(total_cons_all)}",
            "zoom_target": None,
            "tooltip": f"{total_cons_all} consumers ({cons_obj.get('live_count', 0)} live){drop_note}",
        })

    badges = [
        {"label": f"root:{prod_obj.get('root_count', 0)} local:{prod_obj.get('local_witness_count', 0)} ext:{prod_obj.get('via_extends_count', 0)} self:{prod_obj.get('self_transform_count', 0)}", "color_key": "cyan"},
        {"label": f"pins: {pin_counts['projected']} read · {pin_counts['unread']} unread", "color_key": "emerald" if pin_counts["unread"] == 0 else "slate"},
    ]
    if pin_counts["conditional_prop"]:
        badges.append({"label": f"{pin_counts['conditional_prop']} cond (P→Q)", "color_key": "amber"})
    if pin_counts["literal_true"]:
        badges.append({"label": f"{pin_counts['literal_true']} True stub", "color_key": "crimson"})
    if drop_audit_meta["source_checked"] and drop_audit_meta["dropped_target_count"] > 0:
        badges.append({
            "label": f"{drop_audit_meta['dropped_target_count']}/{drop_audit_meta['audited']} consumers drop input",
            "color_key": "crimson",
        })

    elapsed = round(time.time() - t0, 3)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "bundle",
        "title": title or f"Bundle Pin-Board — {_short_name(fqn, 40)}",
        "target": fqn,
        "pins": {
            "kernel_db": _rel_display_path(kernel_db_path),
            "src_root": _rel_display_path(real_src),
            "source_mode": "source+kernel" if real_src else "kernel_only",
            "elapsed_seconds": elapsed,
        },
        "stats": {
            "total_fields": len(pins),
            "projected_fields": pin_counts["projected"],
            "unread_fields": pin_counts["unread"],
            "conditional_prop_fields": pin_counts["conditional_prop"],
            "literal_true_fields": pin_counts["literal_true"],
            "producers_total": total_prods_all,
            "producers_shown": len(shown_prods),
            "producers_breakdown": {
                "root": int(prod_obj.get("root_count") or 0),
                "local_witness": int(prod_obj.get("local_witness_count") or 0),
                "via_extends": int(prod_obj.get("via_extends_count") or 0),
                "self_transform": int(prod_obj.get("self_transform_count") or 0),
            },
            "consumers_total": total_cons_all,
            "consumers_live": int(cons_obj.get("live_count") or 0),
            "consumers_shown": len(shown_cons),
            "consumers_audited": drop_audit_meta["audited"],
            "consumers_dropped_input": drop_audit_meta["dropped_target_count"],
            "node_count": len(nodes),
            "wire_count": len(wires),
        },
        "lanes": [
            {"id": 0, "label": "Producers"},
            {"id": 1, "label": "Interface IC Pin-Board"},
            {"id": 2, "label": "Consumers & Dangling Inputs"},
        ],
        "binders": [],
        "nodes": nodes,
        "wires": wires,
        "badges": badges,
        "legend": [
            {"label": "Read / Projected Pin", "color_key": "emerald", "style": "solid"},
            {"label": "Unread / Never Projected (0 callers)", "color_key": "slate", "style": "dashed"},
            {"label": "Conditional Prop (cond → P)", "color_key": "amber", "style": "solid"},
            {"label": "Literal True Stub / Dropped Input Wire", "color_key": "crimson", "style": "dashed"},
        ],
        "meta": {
            "target_info": {
                "decl_id": t_obj.get("decl_id"),
                "name": fqn,
                "module": t_obj.get("module"),
                "anchor": t_obj.get("anchor"),
                "source_kind": t_obj.get("source_kind"),
                "universe_kind": t_obj.get("universe_kind"),
                "is_prop_def": is_prop_def,
            },
            "field_pins": pins,
            "drop_audit": drop_audit_meta,
        },
    }


# ---------------------------------------------------------------------------
# Zoom 2 — Theorem Step-Wiring Circuit (`--mode theorem`)
# ---------------------------------------------------------------------------

def _split_tactic_statements(body_text: str) -> List[Tuple[int, str]]:
    """Split a tactic `by ...` block into indentation-bounded logical statements."""
    stripped = body_text.lstrip()
    if not re.match(r"^by(?:\s|$)", stripped):
        return []
    after_by = body_text[len(body_text) - len(stripped) + 2 :]
    lines = after_by.split("\n")

    # Determine base tactic indentation from first non-empty line
    base_indent: Optional[int] = None
    for ln in lines:
        s = ln.strip()
        if s:
            base_indent = len(ln) - len(ln.lstrip(" \t"))
            break
    if base_indent is None:
        return []

    stmts: List[Tuple[int, str]] = []
    cur_lines: List[str] = []
    cur_start_rel_line = 0
    bracket_depth = 0
    rel_line = 0
    open_chs = "([{⟨"
    close_chs = ")]}⟩"

    for ln in lines:
        s = ln.strip()
        indent = len(ln) - len(ln.lstrip(" \t"))
        starts_new = False
        if s and bracket_depth == 0 and indent <= base_indent:
            # Handle optional bullet `· ` at same indent
            clean_s = s[1:].lstrip() if s.startswith("·") else s
            if _RE_TACTIC_LEAD.match(clean_s) or s.startswith("·"):
                starts_new = True
        if starts_new and cur_lines:
            stmts.append((cur_start_rel_line, " ".join(x.strip() for x in cur_lines if x.strip())))
            cur_lines = []

        if s:
            if not cur_lines:
                cur_start_rel_line = rel_line
            cur_lines.append(s[1:].lstrip() if (not cur_lines and s.startswith("·")) else s)
            for ch in s:
                if ch in open_chs:
                    bracket_depth += 1
                elif ch in close_chs:
                    bracket_depth = max(0, bracket_depth - 1)
        rel_line += 1

    if cur_lines:
        stmts.append((cur_start_rel_line, " ".join(x.strip() for x in cur_lines if x.strip())))
    return stmts


def _extract_vars_from_pattern(pat: str) -> Tuple[List[str], int]:
    """Extract variable identifiers and wildcard `_` count from an obtain/rcases pattern."""
    vars_out: List[str] = []
    wildcards = 0
    for tok in re.findall(rf"_|[{_IDENT_START}][{_IDENT_CONT}]*", pat):
        if tok == "_":
            wildcards += 1
        elif tok not in _RE_NOISE_HEADS:
            vars_out.append(tok)
    return vars_out, wildcards


def _extract_step_record(
    stmt: str,
    line_no: int,
    step_idx: int,
) -> Optional[Dict[str, Any]]:
    """Parse one Lean tactic statement into a structured circuit step node."""
    s = stmt.strip()
    if not s:
        return None
    m = _RE_TACTIC_LEAD.match(s)
    if not m:
        return None
    kw = m.group("kw")
    rest = m.group(2).strip()

    if kw in ("intro", "intros", "rintro"):
        return None  # Handled directly on Tromp binder bar

    if kw == "obtain":
        assign_idx = _kernel._find_depth0_assign(rest)
        if assign_idx >= 0:
            pat = rest[:assign_idx].strip()
            rhs = rest[assign_idx + 2 :].strip()
        else:
            pat, rhs = rest, ""
        # Strip optional `: Type` inside `obtain pat : T := rhs`
        c_idx = _kernel._find_depth0_colon(pat)
        if c_idx >= 0:
            pat = pat[:c_idx].strip()
        out_vars, wcards = _extract_vars_from_pattern(pat)
        return {
            "id": f"step:{step_idx}",
            "kind": "obtain",
            "line_no": line_no,
            "outputs": out_vars,
            "wildcards": wcards,
            "expr": rhs,
            "label": f"obtain ⟨{', '.join(out_vars[:3])}{'…' if len(out_vars) > 3 else ''}⟩",
            "raw_preview": _clip_chars(s, 140),
        }

    if kw == "rcases":
        m_with = re.search(r"\bwith\b", rest)
        if m_with:
            rhs = rest[: m_with.start()].strip()
            pat = rest[m_with.end() :].strip()
        else:
            rhs, pat = rest, ""
        out_vars, wcards = _extract_vars_from_pattern(pat)
        return {
            "id": f"step:{step_idx}",
            "kind": "rcases",
            "line_no": line_no,
            "outputs": out_vars,
            "wildcards": wcards,
            "expr": rhs,
            "label": f"rcases → {', '.join(out_vars[:3]) or '_'}",
            "raw_preview": _clip_chars(s, 140),
        }

    if kw == "choose":
        m_using = re.search(r"\busing\b", rest)
        if m_using:
            pat = rest[: m_using.start()].strip()
            rhs = rest[m_using.end() :].strip()
        else:
            pat, rhs = rest, ""
        out_vars, wcards = _extract_vars_from_pattern(pat)
        return {
            "id": f"step:{step_idx}",
            "kind": "choose",
            "line_no": line_no,
            "outputs": out_vars,
            "wildcards": wcards,
            "expr": rhs,
            "label": f"choose {', '.join(out_vars[:3])}",
            "raw_preview": _clip_chars(s, 140),
        }

    if kw in ("have", "haveI", "let", "letI", "set"):
        assign_idx = _kernel._find_depth0_assign(rest)
        lhs = rest[:assign_idx].strip() if assign_idx >= 0 else rest
        rhs = rest[assign_idx + 2 :].strip() if assign_idx >= 0 else ""
        c_idx = _kernel._find_depth0_colon(lhs)
        vpart = lhs[:c_idx].strip() if c_idx >= 0 else lhs
        out_vars, wcards = _extract_vars_from_pattern(vpart)
        vname = out_vars[0] if out_vars else "_h"
        return {
            "id": f"step:{step_idx}",
            "kind": kw.rstrip("I"),
            "line_no": line_no,
            "outputs": out_vars or [vname],
            "wildcards": wcards,
            "expr": rhs + (" " + lhs[c_idx + 1 :].strip() if c_idx >= 0 else ""),
            "label": f"{kw} {vname}",
            "raw_preview": _clip_chars(s, 140),
        }

    if kw in ("exact", "refine", "apply", "convert"):
        return {
            "id": f"step:{step_idx}",
            "kind": "close" if kw in ("exact", "refine") else kw,
            "line_no": line_no,
            "outputs": [],
            "wildcards": 0,
            "expr": rest,
            "label": f"{kw} {_clip_chars(rest, 22)}",
            "raw_preview": _clip_chars(s, 140),
        }

    # Rewriting / automation step (`rw`, `simp`, `unfold`, etc.)
    return {
        "id": f"step:{step_idx}",
        "kind": kw,
        "line_no": line_no,
        "outputs": [],
        "wildcards": 0,
        "expr": rest,
        "label": f"{kw} {_clip_chars(rest, 22)}",
        "raw_preview": _clip_chars(s, 140),
    }


def _build_binder_bar(
    span: Dict[str, Any],
    telescope: Sequence[Dict[str, Any]],
    exp_telescope: Sequence[Dict[str, Any]],
    hygiene_findings: Sequence[Dict[str, Any]],
    k1n_counts: Dict[str, int],
    out_edges: Sequence[Dict[str, Any]],
) -> Tuple[List[Dict[str, Any]], int]:
    """Construct the top horizontal Tromp binder bar entries."""
    dropped_header_idx: Set[int] = set()
    dropped_slot_idx: Set[int] = set()
    dropped_names: Set[str] = set()
    for f in hygiene_findings:
        if f.get("category") != "dropped":
            continue
        bidx = f.get("binder_index")
        sidx = f.get("slot_index")
        bpos = str(f.get("binder_pos") or "")
        if bpos.startswith("header #") and bidx is not None:
            dropped_header_idx.add(int(bidx))
        elif sidx is not None:
            dropped_slot_idx.add(int(sidx))
        elif f.get("binder") and f.get("binder") != "_":
            dropped_names.add(str(f["binder"]))

    body = span.get("body_text") or ""
    header_binders = span.get("header_binders") or []
    binders: List[Dict[str, Any]] = []
    inst_count = 0

    for idx, hb in enumerate(header_binders):
        bkind = str(hb.get("kind") or "explicit")
        bname = hb.get("name")
        btype = str(hb.get("type") or "")
        if bkind == "instance":
            inst_count += 1
            continue
        is_dropped = (idx in dropped_header_idx) or (bname in dropped_names) or (bname == "_" and bkind == "explicit")
        if not is_dropped and not hygiene_findings and bname and bname != "_":
            # Fallback only when hygiene_decls did not inspect this decl
            has_imp_tac = _kernel._RE_IMPLICIT_CTX_TACTIC.search(body) is not None
            later = " ".join(x.get("type", "") for x in header_binders[idx + 1 :]) + " " + str(span.get("type_expr") or "")
            if bkind == "explicit" and not has_imp_tac and _kernel._count_ident_refs(bname, body) == 0 and _kernel._count_ident_refs(bname, later) == 0:
                is_dropped = True
        disp_name = bname or f"h{idx}"
        binders.append({
            "id": f"binder:{len(binders)}",
            "name": disp_name,
            "var_name": bname if (bname and bname != "_") else None,
            "kind": bkind,
            "type": _clip_chars(btype, 80),
            "status": "dropped" if is_dropped else "used",
            "color": "#ef4444" if is_dropped else BINDER_PALETTE[len(binders) % len(BINDER_PALETTE)],
            "line_no": hb.get("line_no"),
        })

    # Inspect leading `intro`/`intros` or leading `fun ... =>` to name telescope slots
    intro_names: List[str] = []
    body_stripped = body.lstrip()
    if re.match(r"^by(?:\s|$)", body_stripped):
        for ln in body_stripped[2:].split("\n"):
            st = ln.strip()
            if not st or st == "classical":
                continue
            mi = re.match(r"^(?:intro|intros|rintro)\b(.*)$", st)
            if not mi:
                break
            for tok, _is_pat in _kernel._parse_intro_tokens(mi.group(1)):
                intro_names.append(tok)
    else:
        for fitem in _kernel._iter_fun_binders(body_stripped, 0, [0], 1):
            if fitem.get("offset", 99) <= 2:
                for bn, _bk in fitem.get("binders") or ():
                    intro_names.append(bn)
            break

    # Choose best-aligned telescope (expanded if intro_names exceed unexpanded telescope)
    use_tele = list(exp_telescope) if (exp_telescope and len(intro_names) > len(telescope)) else list(telescope)
    edge_by_leaf = {e["name"].rsplit(".", 1)[-1]: e for e in out_edges}

    for sidx, sl in enumerate(use_tele):
        skind = str(sl.get("kind") or "arrow")
        if skind == "instance":
            inst_count += 1
            continue
        iname = intro_names[sidx] if sidx < len(intro_names) else None
        stype = str(sl.get("type") or "")
        head_tok = (_RE_QUAL_IDENT.findall(stype) or [""])[0].rsplit(".", 1)[-1]
        if sl.get("name"):
            sname = str(sl["name"])
        elif iname and iname not in ("_", "rfl"):
            sname = iname
        elif head_tok:
            sname = head_tok
        else:
            sname = f"arg{sidx}"
        is_dropped = (sidx in dropped_slot_idx) or (iname == "_") or (sname in dropped_names)
        k1n_cnt = 1
        if head_tok and head_tok in edge_by_leaf:
            sh = edge_by_leaf[head_tok].get("sighash")
            if sh:
                k1n_cnt = k1n_counts.get(sh, 1)

        var_nm = iname if (iname and iname != "_") else (sl.get("name") if sl.get("name") != "_" else None)
        binders.append({
            "id": f"binder:{len(binders)}",
            "name": sname if iname != "_" else f"_ : {_clip_chars(head_tok or stype, 14)}",
            "var_name": var_nm,
            "kind": skind,
            "type": _clip_chars(stype, 80),
            "status": "dropped" if is_dropped else "used",
            "color": "#ef4444" if is_dropped else BINDER_PALETTE[len(binders) % len(BINDER_PALETTE)],
            "k1n_count": k1n_cnt,
            "line_no": sl.get("line_no"),
        })

    return binders, inst_count


def _parse_term_mode_nodes(
    body_text: str,
    start_line: int,
    out_edges: Sequence[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    """Fallback step extractor for term-mode proofs (`fun ... => ...`, `if h : P ... else 0`, applications)."""
    s = body_text.strip()
    # Peel leading `fun ... =>` / `λ ... ↦`
    while True:
        kw_len = _kernel._at_quantifier_or_lambda(s, 0, include_forall=False, include_exists=False, include_fun=True)
        if kw_len <= 0:
            break
        nxt = _kernel._extract_lambda_body(s)
        if nxt is None:
            break
        s = nxt.strip()

    if not s:
        return []

    # Check if purely a single binder variable pass-through (`fun h _ => h`)
    if _RE_IDENT.fullmatch(s):
        return [{
            "id": "step:0",
            "kind": "term_pass",
            "line_no": start_line,
            "outputs": [],
            "wildcards": 0,
            "expr": s,
            "label": f"pass-through: {s}",
            "raw_preview": _clip_chars(s, 120),
        }]

    # Extract top-level callee and direct argument subexpressions
    edge_names = {e["name"].rsplit(".", 1)[-1]: e["name"] for e in out_edges}
    toks = _kernel._split_top_level_app_args(s)
    steps: List[Dict[str, Any]] = []
    if len(toks) >= 2:
        head = toks[0].lstrip("@")
        arg_exprs = toks[1:]
        sub_out_ids: List[str] = []
        # Create sub-application cards for parenthesized compound arguments that call project/known funcs
        for aidx, arg in enumerate(arg_exprs[:10]):
            inner = _kernel._strip_outer_parens(arg)
            if len(inner) > 20 and (" " in inner):
                sub_toks = _kernel._split_top_level_app_args(inner)
                sub_head = sub_toks[0].lstrip("@") if sub_toks else ""
                sub_leaf = sub_head.rsplit(".", 1)[-1]
                if sub_leaf in edge_names or len(sub_toks) >= 2:
                    sid = f"step:{len(steps)}"
                    sub_out_ids.append(sid)
                    steps.append({
                        "id": sid,
                        "kind": "term_arg",
                        "line_no": start_line,
                        "outputs": [],
                        "wildcards": 0,
                        "expr": inner,
                        "label": f"arg {sub_leaf or _clip_chars(inner, 20)}",
                        "raw_preview": _clip_chars(inner, 120),
                    })
        root_step = {
            "id": f"step:{len(steps)}",
            "kind": "term_app",
            "line_no": start_line,
            "outputs": [],
            "wildcards": 0,
            "expr": s,
            "explicit_dep_steps": sub_out_ids,
            "label": f"apply {_short_name(head, 24)}",
            "raw_preview": _clip_chars(s, 140),
        }
        steps.append(root_step)
    else:
        steps.append({
            "id": "step:0",
            "kind": "term_app",
            "line_no": start_line,
            "outputs": [],
            "wildcards": 0,
            "expr": s,
            "label": _clip_chars(s, 30),
            "raw_preview": _clip_chars(s, 140),
        })
    return steps


def _motif_tier(cnt: int) -> Tuple[str, str]:
    if cnt >= 5:
        return "high_repeat", "violet"
    if cnt >= 2:
        return "low_repeat", "cyan"
    return "unique", "slate"


def build_theorem_circuit(
    kernel_db_path: str = DEFAULT_KERNEL_DB,
    decl: str = "",
    *,
    src_root: Optional[str] = None,
    max_nodes: int = 32,
    exact_case: bool = False,
    title: Optional[str] = None,
) -> Dict[str, Any]:
    """Build Zoom 2 (theorem step-wiring circuit) JSON payload ``leanre.circuit/1``."""
    t0 = time.time()
    if not decl or not decl.strip():
        raise ValueError("theorem mode requires a declaration name")
    cap = max(4, int(max_nodes))
    real_src = _resolve_default_src_root(kernel_db_path, src_root)
    conn = _open_ro(kernel_db_path)
    try:
        did, fqn, _resolved_from = _resolve_decl_exact_or_fuzzy(conn, decl, exact_case=exact_case)
        has_dm = _kernel._has_decl_module_rows(conn)
        if has_dm:
            drow = conn.execute(
                "SELECT d.kind, d.value_nodes, d.type_nodes, d.fan_in, d.fan_out, d.flags, d.live_mask, "
                "       d.sighash, d.sighash_anon, dm.module "
                "FROM decls d LEFT JOIN decl_module dm ON dm.decl_id = d.id WHERE d.id = ?",
                (did,),
            ).fetchone()
        else:
            drow = conn.execute(
                "SELECT kind, value_nodes, type_nodes, fan_in, fan_out, flags, live_mask, "
                "       sighash, sighash_anon, NULL "
                "FROM decls WHERE id = ?",
                (did,),
            ).fetchone()
        if not drow:
            raise LookupError(f"Declaration id={did} disappeared from decls")

        dkind, val_nodes, typ_nodes, fan_in, fan_out, flags, live_mask, sh_k1n, sh_k1a, mod_name = (
            str(drow[0]), int(drow[1]), int(drow[2]), int(drow[3]), int(drow[4]),
            int(drow[5]), int(drow[6]), drow[7], drow[8], drow[9],
        )

        # Outgoing direct kernel dependencies
        out_edges: List[Dict[str, Any]] = []
        for edid, ename, eknd, ek, esh, evn, elm in conn.execute(
            "SELECT d.id, d.name, d.kind, e.kind, d.sighash, d.value_nodes, d.live_mask "
            "FROM edges e JOIN decls d ON d.id = e.dst "
            "WHERE e.src = ? ORDER BY e.kind DESC, d.value_nodes DESC, d.name ASC LIMIT 250",
            (did,),
        ):
            out_edges.append({
                "decl_id": int(edid),
                "name": str(ename),
                "kind": str(eknd),
                "edge_kind": int(ek),
                "sighash": str(esh) if esh else None,
                "value_nodes": int(evn),
                "live_mask": int(elm),
            })

        k1n_counts = _k1n_counts_for_hashes(
            conn, [e["sighash"] for e in out_edges if e["sighash"]] + ([str(sh_k1n)] if sh_k1n else [])
        )

        # Optional .lean source span & hygiene overlay
        span: Optional[Dict[str, Any]] = None
        anchor: Optional[str] = None
        hygiene_findings: List[Dict[str, Any]] = []
        telescope: List[Dict[str, Any]] = []
        exp_telescope: List[Dict[str, Any]] = []
        return_type = ""

        if real_src and mod_name:
            rel = str(mod_name).replace(".", os.sep) + ".lean"
            abs_path, _err = _kernel._safe_resolve_src_path(real_src, rel)
            if abs_path is not None:
                file_cache: Dict[str, Dict[str, Any]] = {}
                span = _kernel._extract_decl_source_span(abs_path, fqn, file_cache)
                if span is not None:
                    disp_base = (
                        os.path.dirname(real_src) if os.path.basename(real_src) == "src" else real_src
                    )
                    anchor = f"{_kernel._rel_display_path(abs_path, disp_base)}:{span['start_line']}"
                    telescope, return_type = _kernel._parse_type_telescope(
                        span["type_expr"], span["type_offset"], span["line_offsets"], span["start_line"]
                    )
                    try:
                        exp_telescope, _exp_ret, _extra = _kernel._expand_def_telescope(
                            conn, did, telescope, return_type,
                            has_dm=has_dm, sroot=real_src, src_fallback={},
                            file_cache=file_cache, def_edge_cache={},
                        )
                    except Exception:
                        exp_telescope = list(telescope)
                    try:
                        hrep = _kernel.hygiene_decls(
                            kernel_db_path, [fqn], src_root=real_src,
                            only="all", include_semantic=True, continue_on_error=True,
                        )
                        hygiene_findings = list(((hrep.get("decls") or [{}])[0]).get("findings") or [])
                    except Exception:
                        hygiene_findings = []
    finally:
        conn.close()

    # Build Tromp binder bar + steps
    binders: List[Dict[str, Any]] = []
    inst_count = 0
    raw_steps: List[Dict[str, Any]] = []

    if span is not None:
        binders, inst_count = _build_binder_bar(
            span, telescope, exp_telescope, hygiene_findings, k1n_counts, out_edges
        )
        body_text = span.get("body_text") or ""
        tactic_stmts = _split_tactic_statements(body_text)
        body_start_line = _kernel._offset_to_line(
            span["line_offsets"], span["body_offset"], span["start_line"]
        )
        if tactic_stmts:
            for rline, stmt in tactic_stmts:
                rec = _extract_step_record(stmt, body_start_line + rline, len(raw_steps))
                if rec is not None:
                    raw_steps.append(rec)
            # If tactic proof had many rewrite/simp steps and exceeds cap, keep structural steps + close
            if len(raw_steps) > cap:
                structural = [
                    st for st in raw_steps
                    if st["kind"] in ("obtain", "rcases", "have", "let", "set", "choose", "close", "apply", "convert")
                ]
                if len(structural) >= 2:
                    raw_steps = structural[:cap]
                else:
                    raw_steps = raw_steps[:cap]
        if not raw_steps:
            raw_steps = _parse_term_mode_nodes(body_text, body_start_line, out_edges)[:cap]
    else:
        # Kernel-only fallback: build binder-like type edges + value callee pills
        type_edges = [e for e in out_edges if e["edge_kind"] in (1, 3)]
        val_edges = [e for e in out_edges if e["edge_kind"] in (2, 3)]
        for idx, te in enumerate(type_edges[:12]):
            binders.append({
                "id": f"binder:{idx}",
                "name": _short_name(te["name"], 24),
                "var_name": None,
                "kind": "kernel_type_dep",
                "type": te["name"],
                "status": "used",
                "color": BINDER_PALETTE[idx % len(BINDER_PALETTE)],
                "k1n_count": k1n_counts.get(te["sighash"] or "", 1),
                "line_no": None,
            })
        for idx, ve in enumerate(val_edges[: min(cap, 12)]):
            raw_steps.append({
                "id": f"step:{idx}",
                "kind": "callee",
                "line_no": None,
                "outputs": [],
                "wildcards": 0,
                "expr": ve["name"],
                "label": _short_name(ve["name"], 26),
                "raw_preview": ve["name"],
            })

    # Map edge leaf -> edge info for callee badge annotation
    edge_by_leaf: Dict[str, Dict[str, Any]] = {}
    for e in out_edges:
        leaf = e["name"].rsplit(".", 1)[-1]
        if leaf not in edge_by_leaf or e["value_nodes"] > edge_by_leaf[leaf]["value_nodes"]:
            edge_by_leaf[leaf] = e

    # Track hygiene overlays (`true_slot`, `default_zero_branch`, `le_refl_closure`)
    semantic_badges: List[Dict[str, Any]] = []
    line_badges: Dict[int, List[Dict[str, Any]]] = collections.defaultdict(list)
    matched_sem_ids: Set[int] = set()
    for f in hygiene_findings:
        cat = f.get("category")
        knd = str(f.get("kind") or "")
        lno = f.get("line_no")
        b_item: Optional[Dict[str, Any]] = None
        if cat == "true_slot" and f.get("suppression_reason") is None:
            b_item = {"label": "true_slot", "color_key": "crimson", "detail": f.get("detail", "")}
        elif knd == "default_zero_branch":
            b_item = {"label": "else 0", "color_key": "amber", "detail": f.get("detail", "")}
        elif knd == "le_refl_closure":
            b_item = {"label": "le_refl", "color_key": "amber", "detail": f.get("detail", "")}
        if b_item:
            semantic_badges.append(b_item)
            if lno is not None:
                line_badges[int(lno)].append(b_item)

    # Wire binders -> steps AND earlier step outputs -> later steps, and assign topological lanes
    nodes: List[Dict[str, Any]] = []
    wires: List[Dict[str, Any]] = []
    var_producer: Dict[str, str] = {}
    binder_consumed_by: Dict[str, List[str]] = collections.defaultdict(list)
    step_layer: Dict[str, int] = {}

    for st in raw_steps:
        sid = st["id"]
        expr = st.get("expr") or ""
        dep_binders: List[str] = []
        dep_steps: List[str] = list(st.get("explicit_dep_steps") or [])

        for b in binders:
            vn = b.get("var_name")
            if vn and _kernel._count_ident_refs(vn, expr) > 0:
                dep_binders.append(b["id"])
                binder_consumed_by[b["id"]].append(sid)

        for vname, prod_sid in var_producer.items():
            if prod_sid != sid and _kernel._count_ident_refs(vname, expr) > 0:
                if prod_sid not in dep_steps:
                    dep_steps.append(prod_sid)

        layer = 1
        for ps in dep_steps:
            layer = max(layer, step_layer.get(ps, 1) + 1)
        step_layer[sid] = layer

        # Detect callee references & FLIRT/k1n repeat counts inside this step
        callees_here: List[Dict[str, Any]] = []
        seen_c: Set[str] = set()
        for tok in _RE_QUAL_IDENT.findall(expr):
            leaf = tok.rsplit(".", 1)[-1]
            if leaf in seen_c or leaf in _RE_NOISE_HEADS or leaf in var_producer:
                continue
            e = edge_by_leaf.get(leaf)
            if e is not None:
                seen_c.add(leaf)
                sh = e.get("sighash")
                cnt = k1n_counts.get(sh, 1) if sh else 1
                tier, ckey = _motif_tier(cnt)
                callees_here.append({
                    "name": e["name"],
                    "short": leaf,
                    "sighash": sh,
                    "k1n_count": cnt,
                    "tier": tier,
                    "color_key": ckey,
                })
                if len(callees_here) >= 4:
                    break

        s_badges = list(line_badges.get(int(st["line_no"]), ())) if st.get("line_no") else []
        if s_badges and st.get("line_no"):
            matched_sem_ids.add(int(st["line_no"]))
        if st.get("wildcards", 0) > 0:
            s_badges.append({"label": f"_{st['wildcards']}x", "color_key": "amber", "detail": "wildcard pattern binding"})

        max_callee_rep = max((c["k1n_count"] for c in callees_here), default=1)
        _tier, c_status = _motif_tier(max_callee_rep)
        nodes.append({
            "id": sid,
            "label": st["label"],
            "full_name": st["raw_preview"],
            "kind": f"step_{st['kind']}",
            "step_kind": st["kind"],
            "status": "true_slot" if any(b["label"] == "true_slot" for b in s_badges) else ("default_zero" if s_badges else "used"),
            "lane": layer,
            "line_no": st.get("line_no"),
            "outputs": st.get("outputs", []),
            "callees": callees_here,
            "badges": s_badges,
            "badge": f"L{st['line_no']}" if st.get("line_no") else st["kind"],
            "zoom_target": (
                {"mode": "theorem", "target": callees_here[0]["name"]}
                if callees_here and callees_here[0]["name"] != fqn
                else None
            ),
            "tooltip": st["raw_preview"],
        })

        for bid in dep_binders:
            b_obj = next(b for b in binders if b["id"] == bid)
            wires.append({
                "id": f"w:b:{bid}->{sid}",
                "src": bid,
                "dst": sid,
                "kind": "binder_drop",
                "status": "used",
                "color": b_obj["color"],
                "color_key": "emerald",
                "label": b_obj.get("var_name") or "",
            })
        for ps in dep_steps:
            wires.append({
                "id": f"w:s:{ps}->{sid}",
                "src": ps,
                "dst": sid,
                "kind": "step_flow",
                "status": "used",
                "color_key": "cyan",
                "label": "",
            })

        for ov in st.get("outputs") or []:
            var_producer[ov] = sid

    # Attach any unmatched semantic/true_slot badges to single term node or Conclusion Gate
    unmatched_sem: List[Dict[str, Any]] = []
    for lno_k, b_list in sorted(line_badges.items()):
        if lno_k not in matched_sem_ids:
            unmatched_sem.extend(b_list)
    if not line_badges and semantic_badges:
        unmatched_sem = list(semantic_badges)
    if unmatched_sem:
        step_nodes_only = [nd for nd in nodes if nd["id"].startswith("step:")]
        if len(step_nodes_only) == 1:
            step_nodes_only[0]["badges"].extend(unmatched_sem[:3])
            step_nodes_only[0]["status"] = "true_slot" if any(b["label"] == "true_slot" for b in step_nodes_only[0]["badges"]) else "default_zero"
            unmatched_sem = []

    # Add Conclusion Output Gate at bottom lane
    max_step_layer = max(step_layer.values(), default=0)
    gate_id = "gate:conclusion"
    ret_lbl = _clip_chars(return_type or _short_name(fqn, 30), 48)
    gate_badges = unmatched_sem[:3]
    nodes.append({
        "id": gate_id,
        "label": f"⊢ {ret_lbl}",
        "full_name": f"{fqn} : {return_type or '?'}",
        "kind": "conclusion_gate",
        "status": "live" if live_mask else "dead",
        "lane": max_step_layer + 1,
        "badge": f"{dkind} · k1n ×{_fmt_int(k1n_counts.get(str(sh_k1n), 1))}",
        "badges": gate_badges,
        "zoom_target": None,
        "tooltip": f"Conclusion of {fqn}: {return_type or '(kernel)'}",
    })

    # Wire unconsumed leaf steps into Conclusion Output Gate
    steps_with_outgoing = {w["src"] for w in wires if w["src"].startswith("step:")}
    for nd in list(nodes):
        if nd["id"].startswith("step:") and nd["id"] not in steps_with_outgoing:
            wires.append({
                "id": f"w:g:{nd['id']}",
                "src": nd["id"],
                "dst": gate_id,
                "kind": "to_conclusion",
                "status": "used",
                "color_key": "emerald",
                "label": "",
            })

    # Any used binder that had 0 intermediate step references wires directly to Conclusion Gate (unless dropped!)
    for b in binders:
        if b["status"] == "used" and not binder_consumed_by.get(b["id"]):
            wires.append({
                "id": f"w:b2g:{b['id']}",
                "src": b["id"],
                "dst": gate_id,
                "kind": "binder_drop",
                "status": "used",
                "color": b["color"],
                "color_key": "emerald",
                "label": b.get("var_name") or "",
            })

    # Add External Callees & FLIRT/k1n Motif Strip (lane = max_step_layer + 2)
    val_callees = [e for e in out_edges if e["edge_kind"] in (2, 3) and not _is_aux_name(e["name"])]
    shown_callees = val_callees[: min(16, cap)]
    callee_nodes: List[Dict[str, Any]] = []
    for idx, ce in enumerate(shown_callees):
        sh = ce.get("sighash")
        cnt = k1n_counts.get(sh, 1) if sh else 1
        tier, ckey = _motif_tier(cnt)
        cid = f"callee:{idx}"
        cn = {
            "id": cid,
            "label": _short_name(ce["name"], 24),
            "full_name": ce["name"],
            "kind": "callee",
            "status": tier,
            "lane": max_step_layer + 2,
            "badge": f"×{_fmt_int(cnt)}",
            "color_key": ckey,
            "metrics": {"k1n_count": cnt, "sighash": sh, "value_nodes": ce["value_nodes"]},
            "zoom_target": (
                {"mode": "bundle", "target": ce["name"]}
                if ce["kind"] == "inductive"
                else {"mode": "theorem", "target": ce["name"]}
            ),
            "tooltip": f"Callee {ce['name']} ({ce['kind']}) | k1n ×{cnt:,}, value_nodes={ce['value_nodes']}",
        }
        nodes.append(cn)
        callee_nodes.append(cn)

    dropped_count = sum(1 for b in binders if b["status"] == "dropped")
    used_count = sum(1 for b in binders if b["status"] == "used")
    badges: List[Dict[str, Any]] = [
        {"label": f"binders: {used_count} used · {dropped_count} dropped", "color_key": "crimson" if dropped_count else "emerald"},
        {"label": f"steps: {len(raw_steps)}", "color_key": "cyan"},
        {"label": f"k1n ×{_fmt_int(k1n_counts.get(str(sh_k1n), 1))}", "color_key": "violet" if k1n_counts.get(str(sh_k1n), 1) >= 5 else "slate"},
    ]
    if inst_count:
        badges.append({"label": f"{inst_count} [inst]", "color_key": "slate"})
    for sb in semantic_badges[:4]:
        badges.append(sb)

    max_lane = max((n["lane"] for n in nodes), default=1)
    lanes = [{"id": 0, "label": "Tromp Binder Bar"}]
    for l_i in range(1, max_step_layer + 1):
        lanes.append({"id": l_i, "label": f"Step Lane {l_i}"})
    lanes.append({"id": max_step_layer + 1, "label": "Conclusion Gate"})
    if callee_nodes:
        lanes.append({"id": max_step_layer + 2, "label": "External Callees (k1n Motif Multiplicity)"})

    elapsed = round(time.time() - t0, 3)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "theorem",
        "title": title or f"Theorem Wiring — {_short_name(fqn, 40)}",
        "target": fqn,
        "pins": {
            "kernel_db": _rel_display_path(kernel_db_path),
            "src_root": _rel_display_path(real_src),
            "source_mode": "source+kernel" if span is not None else "kernel_only",
            "anchor": anchor,
            "elapsed_seconds": elapsed,
        },
        "stats": {
            "decl_kind": dkind,
            "value_nodes": val_nodes,
            "type_nodes": typ_nodes,
            "fan_in": fan_in,
            "fan_out": fan_out,
            "live_mask": live_mask,
            "binders_total": len(binders),
            "binders_used": used_count,
            "binders_dropped": dropped_count,
            "instance_binders_collapsed": inst_count,
            "steps_count": len(raw_steps),
            "callees_shown": len(callee_nodes),
            "callees_total_edges": len(out_edges),
            "semantic_badges_count": len(semantic_badges),
            "node_count": len(nodes),
            "wire_count": len(wires),
        },
        "lanes": lanes,
        "binders": binders,
        "nodes": nodes,
        "wires": wires,
        "badges": badges,
        "legend": [
            {"label": "Used Binder / Proof Wire", "color_key": "emerald", "style": "solid"},
            {"label": "Dropped / Unplugged Binder (0 wires)", "color_key": "crimson", "style": "dashed"},
            {"label": "k1n ×1 Unique Callee", "color_key": "slate", "style": "badge"},
            {"label": "k1n ×2–4 Repeated Motif", "color_key": "cyan", "style": "badge"},
            {"label": "k1n ×5+ High-Repeat Motif", "color_key": "violet", "style": "badge"},
            {"label": "else 0 / le_refl / true_slot Pin", "color_key": "amber", "style": "badge"},
        ],
        "meta": {
            "decl_id": did,
            "name": fqn,
            "module": mod_name,
            "anchor": anchor,
            "sighash": sh_k1n,
            "sighash_anon": sh_k1a,
            "return_type": _clip_chars(return_type, 200),
            "hygiene_findings_count": len(hygiene_findings),
            "semantic_badges": semantic_badges,
        },
    }


# ---------------------------------------------------------------------------
# Vector SVG Renderer (`render_circuit_svg`)
# ---------------------------------------------------------------------------

def _theme_palette(theme: str) -> Dict[str, str]:
    t = str(theme or "dark").strip().lower()
    if t not in THEMES:
        raise ValueError(f"Unsupported theme {theme!r} (expected 'dark' or 'light')")
    return THEMES[t]


def _color_for(pal: Dict[str, str], key: Optional[str], default_key: str = "cyan") -> str:
    if not key:
        return pal[default_key]
    if key.startswith("#"):
        return key
    return pal.get(key, pal[default_key])


def _svg_rect(
    x: float, y: float, w: float, h: float,
    *, rx: float = 8.0, fill: str, stroke: str, sw: float = 1.3,
    dash: Optional[str] = None, cls: str = "", opacity: Optional[float] = None,
) -> str:
    attrs = [
        f'x="{x:.1f}"', f'y="{y:.1f}"', f'width="{max(1.0, w):.1f}"', f'height="{max(1.0, h):.1f}"',
        f'rx="{rx:.1f}"', f'fill="{fill}"', f'stroke="{stroke}"', f'stroke-width="{sw:.1f}"',
    ]
    if dash:
        attrs.append(f'stroke-dasharray="{dash}"')
    if cls:
        attrs.append(f'class="{cls}"')
    if opacity is not None:
        attrs.append(f'fill-opacity="{opacity:.2f}"')
    return f"<rect {' '.join(attrs)}/>"


def _svg_text(
    x: float, y: float, text: str,
    *, fill: str, size: float = 11.5, weight: str = "400",
    anchor: str = "start", mono: bool = False, cls: str = "",
) -> str:
    fam = "ui-monospace,'SF Mono',Menlo,Consolas,monospace" if mono else "-apple-system,BlinkMacSystemFont,'Segoe UI',Inter,sans-serif"
    c_attr = f' class="{cls}"' if cls else ""
    return (
        f'<text x="{x:.1f}" y="{y:.1f}" fill="{fill}" font-size="{size:.1f}" '
        f'font-weight="{weight}" text-anchor="{anchor}" font-family="{fam}"{c_attr}>{_xml_esc(text)}</text>'
    )


def _svg_pill(
    x: float, y: float, text: str,
    *, fill: str, stroke: str, text_color: str, size: float = 10.0, mono: bool = True,
) -> Tuple[str, float]:
    w = max(34.0, len(text) * (size * (0.62 if mono else 0.56)) + 14.0)
    h = size + 9.0
    svg = (
        f'<g>{_svg_rect(x, y, w, h, rx=h / 2.0, fill=fill, stroke=stroke, sw=1.1)}'
        f'{_svg_text(x + w / 2.0, y + h / 2.0 + size * 0.34, text, fill=text_color, size=size, weight="600", anchor="middle", mono=mono)}</g>'
    )
    return svg, w


def _node_open_tag(node: Dict[str, Any]) -> str:
    nid = _xml_esc(node.get("id", ""))
    zt = node.get("zoom_target") or {}
    zmode = _xml_esc(zt.get("mode", "")) if isinstance(zt, dict) else ""
    ztgt = _xml_esc(zt.get("target", "")) if isinstance(zt, dict) else ""
    return (
        f'<g class="circuit-node" data-node-id="{nid}" '
        f'data-zoom-mode="{zmode}" data-zoom-target="{ztgt}">'
        f'<title>{_xml_esc(node.get("tooltip") or node.get("full_name") or node.get("label"))}</title>'
    )


def _cubic_wire(
    x1: float, y1: float, x2: float, y2: float,
    *, color: str, sw: float = 1.8, dashed: bool = False, vertical: bool = True,
) -> str:
    if vertical:
        dy = max(22.0, abs(y2 - y1) * 0.48)
        c1x, c1y = x1, y1 + dy
        c2x, c2y = x2, y2 - dy
    else:
        dx = max(28.0, abs(x2 - x1) * 0.45)
        c1x, c1y = x1 + dx, y1
        c2x, c2y = x2 - dx, y2
    dash_attr = ' stroke-dasharray="5,4"' if dashed else ""
    halo = (
        f'<path d="M{x1:.1f},{y1:.1f} C{c1x:.1f},{c1y:.1f} {c2x:.1f},{c2y:.1f} {x2:.1f},{y2:.1f}" '
        f'fill="none" stroke="{color}" stroke-width="{sw + 2.4:.1f}" stroke-opacity="0.16"{dash_attr}/>'
        if not dashed
        else ""
    )
    main = (
        f'<path d="M{x1:.1f},{y1:.1f} C{c1x:.1f},{c1y:.1f} {c2x:.1f},{c2y:.1f} {x2:.1f},{y2:.1f}" '
        f'fill="none" stroke="{color}" stroke-width="{sw:.1f}" stroke-opacity="0.88"{dash_attr}/>'
    )
    return halo + main


def _render_header_and_legend(
    payload: Dict[str, Any],
    pal: Dict[str, str],
    width: float,
    y_legend: float,
) -> Tuple[str, str, float]:
    """Render shared top banner and bottom legend strip, returning (header_svg, legend_svg, total_height)."""
    # Top-right summary badges (allocate right rail first so title never collides)
    badge_svgs: List[str] = []
    bx = width - 36.0
    for b in reversed((payload.get("badges") or [])[:4]):
        lbl = _clip_chars(str(b.get("label") or ""), 30)
        col = _color_for(pal, b.get("color_key"), "cyan")
        pw = max(44.0, len(lbl) * 6.5 + 16.0)
        if bx - pw - 8.0 < 480.0:
            break
        bx -= pw + 8.0
        p_svg, _ = _svg_pill(bx, 29, lbl, fill=pal["panel_alt"], stroke=col, text_color=col, size=10.2)
        badge_svgs.append(p_svg)

    title_budget = max(220.0, bx - 54.0)
    title = _clip_px(str(payload.get("title") or "Proof Circuit"), title_budget, 15.5, mono=False)
    mode = str(payload.get("mode") or "circuit").upper()
    pins = payload.get("pins") or {}
    sub = f"mode={mode} · db={pins.get('kernel_db') or 'kernel.db'} · {pins.get('source_mode', 'kernel')} · {pins.get('elapsed_seconds', 0)}s"

    hdr_parts = [
        _svg_rect(20, 14, width - 40, 56, rx=10, fill=pal["panel"], stroke=pal["border"], sw=1.2, cls="c-panel"),
        _svg_text(36, 38, title, fill=pal["text"], size=15.5, weight="700", cls="c-text"),
        _svg_text(36, 56, _clip_px(sub, title_budget, 11.0, mono=True), fill=pal["sub"], size=11.0, mono=True, cls="c-sub"),
        *badge_svgs,
    ]

    # Wrap legend items cleanly onto 1 or 2 rows so none are dropped
    leg_items = list(payload.get("legend") or [])
    leg_rows: List[List[Tuple[Dict[str, Any], float]]] = [[]]
    cur_lx = 34.0
    for item in leg_items:
        lbl = str(item.get("label") or "")
        iw = 36.0 + len(lbl) * 6.3 + 16.0
        if leg_rows[-1] and cur_lx + iw > width - 34.0:
            leg_rows.append([])
            cur_lx = 34.0
        leg_rows[-1].append((item, cur_lx))
        cur_lx += iw

    leg_h = 20.0 + len(leg_rows) * 22.0
    leg_parts = [
        _svg_rect(20, y_legend, width - 40, leg_h, rx=8, fill=pal["panel"], stroke=pal["border"], sw=1.1, cls="c-panel"),
    ]
    for r_idx, r_items in enumerate(leg_rows):
        ry = y_legend + 21.0 + r_idx * 22.0
        for item, lx in r_items:
            lbl = str(item.get("label") or "")
            col = _color_for(pal, item.get("color_key"), "cyan")
            st = item.get("style", "solid")
            if st == "dashed":
                leg_parts.append(
                    f'<line x1="{lx:.1f}" y1="{ry - 3:.1f}" x2="{lx + 22:.1f}" y2="{ry - 3:.1f}" '
                    f'stroke="{col}" stroke-width="2.2" stroke-dasharray="4,3"/>'
                )
            elif st == "badge":
                leg_parts.append(_svg_rect(lx + 2, ry - 10, 18, 14, rx=4, fill=pal["panel_alt"], stroke=col, sw=1.4))
            else:
                leg_parts.append(
                    f'<line x1="{lx:.1f}" y1="{ry - 3:.1f}" x2="{lx + 22:.1f}" y2="{ry - 3:.1f}" '
                    f'stroke="{col}" stroke-width="2.4"/>'
                )
            leg_parts.append(_svg_text(lx + 28, ry, lbl, fill=pal["sub"], size=10.8, cls="c-sub"))

    return "\n".join(hdr_parts), "\n".join(leg_parts), y_legend + leg_h + 18.0


def _render_macro_svg(payload: Dict[str, Any], pal: Dict[str, str]) -> str:
    width = 1360.0
    nodes = payload.get("nodes") or []
    wires = payload.get("wires") or []

    roots = [n for n in nodes if n["kind"] == "root"]
    dead_nodes = [n for n in nodes if n["kind"] == "dead_mass"]
    dom_nodes = [n for n in nodes if n["kind"] in ("spine_hub", "pillar")]
    diamond_nodes = [n for n in nodes if n["kind"] == "diamond"]
    motif_nodes = [n for n in nodes if n["kind"] == "motif_cluster"]
    island_nodes = [n for n in nodes if n["kind"] == "island"]

    pos: Dict[str, Tuple[float, float, float, float]] = {}  # id -> (x, y, w, h)
    body_parts: List[str] = []

    # Band 0: Roots + Dead Mass
    y0 = 104.0
    body_parts.append(_svg_text(28, y0 - 10, "LANE 0 · HEADLINE ROOTS & UNREACHABLE MASS", fill=pal["muted"], size=10.5, weight="700", mono=True))
    top_row = roots + dead_nodes
    col_cnt = max(1, len(top_row))
    card_w = min(230.0, (width - 56.0 - 14.0 * (col_cnt - 1)) / col_cnt)
    for idx, n in enumerate(top_row):
        x = 28.0 + idx * (card_w + 14.0)
        pos[n["id"]] = (x, y0, card_w, 60.0)

    # Band 1: Dominator Spine & Pillars + Shared Diamond Hub
    y1 = 204.0
    body_parts.append(_svg_text(28, y1 - 10, "LANE 1 · DOMINATOR PILLARS & SHARED DIAMOND (>=2 PILLARS)", fill=pal["muted"], size=10.5, weight="700", mono=True))
    dom_cols = 4
    dom_w = 246.0
    dom_h = 62.0
    dom_gap_x = 16.0
    dom_gap_y = 18.0
    for idx, n in enumerate(dom_nodes):
        r = idx // dom_cols
        c = idx % dom_cols
        x = 28.0 + c * (dom_w + dom_gap_x)
        y = y1 + r * (dom_h + dom_gap_y)
        pos[n["id"]] = (x, y, dom_w, dom_h)
    dom_rows = max(1, math.ceil(len(dom_nodes) / dom_cols))
    y1_end = y1 + dom_rows * (dom_h + dom_gap_y) - dom_gap_y
    if diamond_nodes:
        dx = 28.0 + dom_cols * (dom_w + dom_gap_x) + 8.0
        dw = width - dx - 28.0
        pos[diamond_nodes[0]["id"]] = (dx, y1, max(220.0, dw), min(132.0, max(84.0, y1_end - y1)))

    # Band 2: Repeated Motif Clusters (`k1n` / `k1a`)
    y2 = max(y1_end, y1 + 100.0) + 46.0
    body_parts.append(_svg_text(28, y2 - 10, "LANE 2 · REPEATED KERNEL SIGNATURE MOTIFS (k1n / k1a)", fill=pal["muted"], size=10.5, weight="700", mono=True))
    m_cols = 5
    m_w = (width - 56.0 - 14.0 * (m_cols - 1)) / m_cols
    m_h = 64.0
    for idx, n in enumerate(motif_nodes):
        r = idx // m_cols
        c = idx % m_cols
        pos[n["id"]] = (28.0 + c * (m_w + 14.0), y2 + r * (m_h + 14.0), m_w, m_h)
    m_rows = max(1, math.ceil(max(1, len(motif_nodes)) / m_cols))
    y2_end = y2 + m_rows * (m_h + 14.0) - 14.0

    # Band 3: Standalone Portable Islands
    y3 = y2_end + 46.0
    body_parts.append(_svg_text(28, y3 - 10, "LANE 3 · STANDALONE PORTABLE ISLANDS", fill=pal["muted"], size=10.5, weight="700", mono=True))
    isl_cols = max(1, min(4, len(island_nodes)))
    isl_w = (width - 56.0 - 16.0 * (isl_cols - 1)) / isl_cols
    isl_h = 62.0
    for idx, n in enumerate(island_nodes):
        r = idx // isl_cols
        c = idx % isl_cols
        pos[n["id"]] = (28.0 + c * (isl_w + 16.0), y3 + r * (isl_h + 14.0), isl_w, isl_h)
    isl_rows = max(1, math.ceil(max(1, len(island_nodes)) / isl_cols))
    y3_end = y3 + isl_rows * (isl_h + 14.0) - 14.0

    # Draw wires first (underneath nodes)
    for w in wires:
        if w["src"] not in pos or w["dst"] not in pos:
            continue
        sx, sy, sw, sh = pos[w["src"]]
        dx, dy, dw, dh = pos[w["dst"]]
        col = _color_for(pal, w.get("color_key"), "emerald")
        if w["kind"] == "diamond_share":
            body_parts.append(_cubic_wire(sx + sw, sy + sh / 2, dx, dy + dh / 2, color=col, sw=1.8, vertical=False))
        else:
            body_parts.append(_cubic_wire(sx + sw / 2, sy + sh, dx + dw / 2, dy, color=col, sw=1.7, vertical=True))

    # Draw nodes
    for n in nodes:
        if n["id"] not in pos:
            continue
        x, y, w, h = pos[n["id"]]
        k = n["kind"]
        if k == "dead_mass":
            stroke = pal["crimson"] if (n.get("metrics") or {}).get("dead_decls", 0) > 0 else pal["slate"]
            dash = "5,4"
        elif k == "diamond":
            stroke = pal["violet"]
            dash = None
        elif k == "spine_hub":
            stroke = pal["cyan"]
            dash = None
        elif k == "motif_cluster":
            stroke = _color_for(pal, n.get("color"), "amber")
            dash = None
        elif k == "island":
            stroke = pal["emerald"] if n.get("status") == "projected" else pal["amber"]
            dash = None
        else:
            stroke = pal["emerald"]
            dash = None

        parts = [_node_open_tag(n)]
        parts.append(_svg_rect(x, y, w, h, rx=8, fill=pal["panel_alt"], stroke=stroke, sw=1.5, dash=dash, cls="c-card"))
        parts.append(_svg_text(x + 12, y + 23, _clip_px(n["label"], w - 24, 12.0, mono=True), fill=pal["text"], size=12.0, weight="700", mono=True, cls="c-text"))
        badge_txt = _clip_px(str(n.get("badge") or ""), w - 24, 10.5, mono=True)
        parts.append(_svg_text(x + 12, y + 43, badge_txt, fill=stroke, size=10.5, weight="600", mono=True))
        if k == "diamond" and h >= 84:
            stats = payload.get("stats") or {}
            sub_txt = f"cross-pillar edges: {_fmt_int(stats.get('cross_pillar_shared_edges', 0))}"
            parts.append(_svg_text(x + 12, y + 63, _clip_px(sub_txt, w - 24, 10.2, mono=True), fill=pal["sub"], size=10.2, mono=True, cls="c-sub"))
        parts.append("</g>")
        body_parts.append("\n".join(parts))

    y_legend = y3_end + 26.0
    hdr_svg, leg_svg, total_h = _render_header_and_legend(payload, pal, width, y_legend)
    return _wrap_svg(width, total_h, pal, hdr_svg + "\n" + "\n".join(body_parts) + "\n" + leg_svg)


def _render_bundle_svg(payload: Dict[str, Any], pal: Dict[str, str]) -> str:
    width = 1340.0
    nodes = payload.get("nodes") or []
    wires = payload.get("wires") or []
    prods = [n for n in nodes if n["kind"] in ("producer", "overflow_pill") and n["lane"] == 0]
    cons = [n for n in nodes if n["kind"] in ("consumer", "overflow_pill") and n["lane"] == 2]
    chip = next(n for n in nodes if n["kind"] == "chip")
    pins = chip.get("pins") or []

    x_left, w_left = 32.0, 326.0
    x_chip, w_chip = 446.0, 448.0
    x_right, w_right = 982.0, 326.0

    y_top = 112.0
    row_h = 38.0
    row_gap = 8.0
    pin_h = 26.0

    left_h = max(1, len(prods)) * (row_h + row_gap)
    right_h = max(1, len(cons)) * (row_h + row_gap)
    chip_h = 68.0 + max(1, len(pins)) * pin_h + 18.0
    y_end = y_top + max(left_h, right_h, chip_h)

    pos: Dict[str, Tuple[float, float, float, float]] = {chip["id"]: (x_chip, y_top, w_chip, chip_h)}
    for idx, n in enumerate(prods):
        pos[n["id"]] = (x_left, y_top + idx * (row_h + row_gap), w_left, row_h)
    for idx, n in enumerate(cons):
        pos[n["id"]] = (x_right, y_top + idx * (row_h + row_gap), w_right, row_h)

    parts: List[str] = [
        _svg_text(x_left, y_top - 12, "PRODUCERS (LEFT BANK)", fill=pal["muted"], size=10.5, weight="700", mono=True),
        _svg_text(x_chip, y_top - 12, "INTERFACE IC SPINE (PINS)", fill=pal["muted"], size=10.5, weight="700", mono=True),
        _svg_text(x_right, y_top - 12, "CONSUMERS & DANGLING AUDIT (RIGHT BANK)", fill=pal["muted"], size=10.5, weight="700", mono=True),
    ]

    # Wires
    for w in wires:
        if w["src"] not in pos or w["dst"] not in pos:
            continue
        sx, sy, sw, sh = pos[w["src"]]
        dx, dy, dw, dh = pos[w["dst"]]
        col = _color_for(pal, w.get("color_key"), "emerald")
        if w["kind"] == "producer_in":
            py_in = y_top + 68.0 + min(max(12.0, sy + sh / 2 - y_top - 68.0), max(24.0, chip_h - 86.0))
            parts.append(_cubic_wire(sx + sw, sy + sh / 2, x_chip, py_in, color=col, sw=1.7, vertical=False))
            parts.append(f'<circle cx="{sx + sw:.1f}" cy="{sy + sh / 2:.1f}" r="3.2" fill="{col}"/>')
            parts.append(f'<circle cx="{x_chip:.1f}" cy="{py_in:.1f}" r="3.2" fill="{col}"/>')
        elif w["kind"] == "consumer_out":
            py_out = y_top + 68.0 + min(max(12.0, dy + dh / 2 - y_top - 68.0), max(24.0, chip_h - 86.0))
            if w.get("dangling"):
                # Broken crimson wire terminating in an unplugged `×` stub before the consumer
                x_mid = x_chip + w_chip + (x_right - (x_chip + w_chip)) * 0.62
                y_mid = (py_out + dy + dh / 2) / 2.0
                parts.append(_cubic_wire(x_chip + w_chip, py_out, x_mid, y_mid, color=pal["crimson"], sw=1.8, dashed=True, vertical=False))
                parts.append(f'<circle cx="{x_chip + w_chip:.1f}" cy="{py_out:.1f}" r="3.2" fill="{pal["crimson"]}"/>')
                parts.append(f'<circle cx="{x_mid:.1f}" cy="{y_mid:.1f}" r="5.5" fill="{pal["bg"]}" stroke="{pal["crimson"]}" stroke-width="1.6"/>')
                parts.append(_svg_text(x_mid, y_mid + 3.5, "×", fill=pal["crimson"], size=10.5, weight="700", anchor="middle", mono=True))
            else:
                parts.append(_cubic_wire(x_chip + w_chip, py_out, dx, dy + dh / 2, color=col, sw=1.7, vertical=False))
                parts.append(f'<circle cx="{x_chip + w_chip:.1f}" cy="{py_out:.1f}" r="3.2" fill="{col}"/>')
                parts.append(f'<circle cx="{dx:.1f}" cy="{dy + dh / 2:.1f}" r="3.2" fill="{col}"/>')

    # Producer & consumer bank cards
    for n in prods + cons:
        x, y, w, h = pos[n["id"]]
        is_ov = n["kind"] == "overflow_pill"
        is_drop = bool(n.get("drops_target"))
        if is_ov:
            stroke = pal["crimson"] if n.get("status") == "dangling" else pal["border_hi"]
            dash = "4,3"
        elif is_drop:
            stroke = pal["crimson"]
            dash = "5,3"
        elif n["kind"] == "producer":
            stroke = _color_for(pal, {"root": "emerald", "local_witness": "cyan", "via_extends": "violet", "self_transform": "amber"}.get(n.get("producer_role", ""), "emerald"))
            dash = None
        else:
            stroke = pal["emerald"]
            dash = None
        parts.append(_node_open_tag(n))
        parts.append(_svg_rect(x, y, w, h, rx=7, fill=pal["panel_alt"], stroke=stroke, sw=1.4, dash=dash, cls="c-card"))
        badge_txt = str(n.get("badge") or "")
        lbl_max_w = w - 24 - (len(badge_txt) * 6.5 + 14 if badge_txt else 0)
        parts.append(_svg_text(x + 12, y + 23, _clip_px(n["label"], max(80.0, lbl_max_w), 11.2, mono=True), fill=pal["text"], size=11.2, weight="600", mono=True, cls="c-text"))
        if badge_txt and not is_ov:
            pw = max(38.0, len(badge_txt) * 6.3 + 12)
            p_svg, _ = _svg_pill(x + w - pw - 8, y + 9, badge_txt, fill=pal["panel"], stroke=stroke, text_color=stroke, size=9.6)
            parts.append(p_svg)
        parts.append("</g>")

    # Central IC chip & field/conjunct pin spine
    cx, cy, cw, ch = pos[chip["id"]]
    parts.append(_node_open_tag(chip))
    parts.append(_svg_rect(cx, cy, cw, ch, rx=11, fill=pal["chip"], stroke=pal["border_hi"], sw=2.0, cls="c-panel"))
    parts.append(_svg_rect(cx + 1, cy + 1, cw - 2, 54, rx=10, fill=pal["panel_alt"], stroke="none"))
    parts.append(_svg_text(cx + 16, cy + 25, _clip_px(chip["label"], cw - 32, 14.0, mono=True), fill=pal["text"], size=14.0, weight="700", mono=True, cls="c-text"))
    parts.append(_svg_text(cx + 16, cy + 43, _clip_px(str(chip.get("badge") or ""), cw - 32, 10.5, mono=True), fill=pal["cyan"], size=10.5, mono=True))
    parts.append("</g>")

    py = cy + 68.0
    status_label = {
        "projected": "READ",
        "unread": "UNREAD",
        "conditional_prop": "COND →",
        "literal_true": "TRUE STUB",
    }
    for p in pins:
        st = p["status"]
        col = _color_for(pal, p.get("color_key"), "emerald")
        dash = "4,3" if st == "unread" else None
        parts.append(
            f'<g class="circuit-pin" data-pin="{_xml_esc(p["name"])}">'
            f'<title>{_xml_esc(p["name"] + ": " + (p.get("type") or st))}</title>'
        )
        parts.append(_svg_rect(cx + 12, py, cw - 24, pin_h - 4, rx=5, fill=pal["panel"], stroke=col, sw=1.1, dash=dash))
        parts.append(f'<circle cx="{cx + 22:.1f}" cy="{py + (pin_h - 4) / 2:.1f}" r="3.4" fill="{col}"/>')
        parts.append(_svg_text(cx + 32, py + 15, _clip_px(p["name"], cw - 150, 10.8, mono=True), fill=pal["text"], size=10.8, mono=True, cls="c-text"))
        st_txt = status_label.get(st, st.upper())
        if st == "projected" and p.get("fan_in"):
            st_txt = f"READ ×{p['fan_in']}"
        parts.append(_svg_text(cx + cw - 20, py + 15, st_txt, fill=col, size=9.8, weight="700", anchor="end", mono=True))
        parts.append("</g>")
        py += pin_h

    hdr_svg, leg_svg, total_h = _render_header_and_legend(payload, pal, width, y_end + 26.0)
    return _wrap_svg(width, total_h, pal, hdr_svg + "\n" + "\n".join(parts) + "\n" + leg_svg)


def _render_theorem_svg(payload: Dict[str, Any], pal: Dict[str, str]) -> str:
    binders = payload.get("binders") or []
    nodes = payload.get("nodes") or []
    wires = payload.get("wires") or []

    step_nodes = [n for n in nodes if n["id"].startswith("step:")]
    gate_nodes = [n for n in nodes if n["kind"] == "conclusion_gate"]
    callee_nodes = [n for n in nodes if n["kind"] == "callee"]

    # Group steps by topological lane
    lanes_map: Dict[int, List[Dict[str, Any]]] = collections.defaultdict(list)
    for sn in step_nodes:
        lanes_map[int(sn.get("lane") or 1)].append(sn)
    max_cols = min(5, max([len(v) for v in lanes_map.values()] + [1]))

    binder_min_w = max(84.0, min(140.0, 1180.0 / max(1, len(binders)))) if binders else 120.0
    needed_w_binders = 56.0 + max(1, len(binders)) * (binder_min_w + 8.0)
    needed_w_steps = 56.0 + max_cols * 255.0
    width = max(1280.0, min(1800.0, max(needed_w_binders, needed_w_steps)))

    parts: List[str] = []
    pos: Dict[str, Tuple[float, float, float, float]] = {}

    # Lane 0: Tromp Horizontal Binder Bar
    y_tromp = 104.0
    parts.append(_svg_text(28, y_tromp - 10, "TROMP BINDER BAR (HORIZONTAL RAIL — UNPLUGGED = DROPPED HYPOTHESIS)", fill=pal["muted"], size=10.5, weight="700", mono=True))
    bar_h = 56.0
    parts.append(_svg_rect(28, y_tromp, width - 56, bar_h, rx=9, fill=pal["rail"], stroke=pal["border_hi"], sw=1.4, cls="c-panel"))
    if binders:
        slot_gap = 8.0
        slot_w = min(160.0, (width - 76.0 - slot_gap * (len(binders) - 1)) / len(binders))
        bx = 38.0
        for b in binders:
            is_drop = b["status"] == "dropped"
            col = pal["crimson"] if is_drop else _color_for(pal, b.get("color"), "emerald")
            dash = "4,3" if is_drop else None
            parts.append(
                f'<g class="circuit-node" data-node-id="{_xml_esc(b["id"])}" data-zoom-mode="" data-zoom-target="">'
                f'<title>{_xml_esc(b["name"] + " : " + (b.get("type") or "") + " [" + b["status"] + "]")}</title>'
            )
            parts.append(_svg_rect(bx, y_tromp + 6, slot_w, bar_h - 12, rx=6, fill=pal["panel"], stroke=col, sw=1.5, dash=dash))
            parts.append(_svg_text(bx + slot_w / 2, y_tromp + 25, _clip_px(b["name"], slot_w - 10, 10.5, mono=True), fill=pal["text"], size=10.5, weight="700", anchor="middle", mono=True, cls="c-text"))
            st_lbl = "× DROP" if is_drop else _clip_px(b.get("type") or "used", slot_w - 10, 8.8, mono=True)
            parts.append(_svg_text(bx + slot_w / 2, y_tromp + 41, st_lbl, fill=col, size=8.8, weight="600", anchor="middle", mono=True))
            if is_drop:
                parts.append(f'<circle cx="{bx + slot_w / 2:.1f}" cy="{y_tromp + bar_h:.1f}" r="4.0" fill="{pal["bg"]}" stroke="{pal["crimson"]}" stroke-width="1.6"/>')
            else:
                parts.append(f'<circle cx="{bx + slot_w / 2:.1f}" cy="{y_tromp + bar_h:.1f}" r="3.5" fill="{col}"/>')
            parts.append("</g>")
            pos[b["id"]] = (bx, y_tromp + 6, slot_w, bar_h - 12)
            bx += slot_w + slot_gap
    else:
        parts.append(_svg_text(width / 2, y_tromp + 33, "(no explicit binders)", fill=pal["muted"], size=11.0, anchor="middle", mono=True))

    # Step Lanes (1 .. K)
    y_cur = y_tromp + bar_h + 44.0
    step_h = 68.0
    for l_idx in sorted(lanes_map.keys()):
        row = lanes_map[l_idx]
        # Wrap very wide lanes into sub-rows of <= 5 cards so nothing gets squished
        chunks = [row[i : i + 5] for i in range(0, len(row), 5)]
        for ch_idx, ch in enumerate(chunks):
            if ch_idx == 0:
                parts.append(_svg_text(28, y_cur - 8, f"LANE {l_idx}", fill=pal["muted"], size=9.8, weight="700", mono=True))
            cnt = len(ch)
            card_w = min(250.0, (width - 56.0 - 18.0 * (cnt - 1)) / cnt)
            total_row_w = cnt * card_w + max(0, cnt - 1) * 18.0
            sx = (width - total_row_w) / 2.0
            for n in ch:
                pos[n["id"]] = (sx, y_cur, card_w, step_h)
                sx += card_w + 18.0
            y_cur += step_h + 40.0

    # Conclusion Gate
    if gate_nodes:
        gn = gate_nodes[0]
        gw = min(560.0, width - 80.0)
        gh = 80.0 if gn.get("badges") else 58.0
        pos[gn["id"]] = ((width - gw) / 2.0, y_cur, gw, gh)
        y_cur += gh + 36.0

    # External Callee / Motif Strip
    if callee_nodes:
        parts.append(_svg_text(28, y_cur - 10, "EXTERNAL CALLEES & FLIRT/k1n MOTIF MULTIPLICITY (×1 GREY · ×2-4 CYAN · ×5+ VIOLET)", fill=pal["muted"], size=10.2, weight="700", mono=True))
        c_cols = 4
        cw = (width - 56.0 - 14.0 * (c_cols - 1)) / c_cols
        ch = 44.0
        for idx, cn in enumerate(callee_nodes):
            r = idx // c_cols
            c = idx % c_cols
            pos[cn["id"]] = (28.0 + c * (cw + 14.0), y_cur + r * (ch + 10.0), cw, ch)
        c_rows = max(1, math.ceil(len(callee_nodes) / c_cols))
        y_cur += c_rows * (ch + 10.0) + 14.0

    # Draw Wires (binder drops & step flows)
    for w in wires:
        if w["src"] not in pos or w["dst"] not in pos:
            continue
        sx, sy, sw, sh = pos[w["src"]]
        dx, dy, dw, dh = pos[w["dst"]]
        col = _color_for(pal, w.get("color") or w.get("color_key"), "emerald")
        y_start = y_tromp + bar_h if w["src"].startswith("binder:") else (sy + sh)
        parts.append(_cubic_wire(sx + sw / 2, y_start, dx + dw / 2, dy, color=col, sw=1.7, vertical=True))
        parts.append(f'<circle cx="{dx + dw / 2:.1f}" cy="{dy:.1f}" r="3.0" fill="{col}"/>')

    # Draw Step, Gate & Callee Nodes
    for n in step_nodes + gate_nodes + callee_nodes:
        if n["id"] not in pos:
            continue
        x, y, w, h = pos[n["id"]]
        if n["kind"] == "conclusion_gate":
            stroke = pal["emerald"] if n["status"] == "live" else pal["crimson"]
            g_badges = n.get("badges") or []
            parts.append(_node_open_tag(n))
            parts.append(_svg_rect(x, y, w, h, rx=10, fill=pal["chip"], stroke=stroke, sw=2.0, cls="c-panel"))
            parts.append(_svg_text(x + w / 2, y + 25, _clip_px(n["label"], w - 28, 12.2, mono=True), fill=pal["text"], size=12.2, weight="700", anchor="middle", mono=True, cls="c-text"))
            parts.append(_svg_text(x + w / 2, y + 44, _clip_px(str(n.get("badge") or ""), w - 28, 10.2, mono=True), fill=stroke, size=10.2, anchor="middle", mono=True))
            if g_badges:
                px = x + 16.0
                for gb in g_badges[:3]:
                    gc = _color_for(pal, gb.get("color_key"), "amber")
                    p_svg, pw = _svg_pill(px, y + 52, gb["label"], fill=pal["panel"], stroke=gc, text_color=gc, size=9.2)
                    if px + pw < x + w - 12:
                        parts.append(p_svg)
                        px += pw + 6.0
            parts.append("</g>")
            continue

        if n["kind"] == "callee":
            col = _color_for(pal, n.get("color_key"), "slate")
            parts.append(_node_open_tag(n))
            parts.append(_svg_rect(x, y, w, h, rx=7, fill=pal["panel_alt"], stroke=col, sw=1.4, cls="c-card"))
            btxt = str(n.get("badge") or "×1")
            p_svg, pw = _svg_pill(x + w - max(42.0, len(btxt) * 6.5 + 14) - 8, y + 12, btxt, fill=pal["panel"], stroke=col, text_color=col, size=9.8)
            parts.append(_svg_text(x + 12, y + 26, _clip_px(n["label"], w - pw - 26, 11.0, mono=True), fill=pal["text"], size=11.0, weight="600", mono=True, cls="c-text"))
            parts.append(p_svg)
            parts.append("</g>")
            continue

        # Step card
        s_badges = n.get("badges") or []
        if any(b["label"] == "true_slot" for b in s_badges):
            stroke = pal["crimson"]
        elif s_badges:
            stroke = pal["amber"]
        elif n.get("step_kind") in ("close", "term_app", "term_pass"):
            stroke = pal["emerald"]
        else:
            stroke = pal["cyan"]

        parts.append(_node_open_tag(n))
        parts.append(_svg_rect(x, y, w, h, rx=8, fill=pal["panel_alt"], stroke=stroke, sw=1.5, cls="c-card"))
        parts.append(_svg_text(x + 11, y + 21, _clip_px(n["label"], w - 64, 11.2, mono=True), fill=pal["text"], size=11.2, weight="700", mono=True, cls="c-text"))
        if n.get("badge"):
            parts.append(_svg_text(x + w - 10, y + 20, str(n["badge"]), fill=pal["muted"], size=9.5, anchor="end", mono=True))

        # Callee/k1n or semantic pills along bottom of step box
        px = x + 10.0
        for sb in s_badges[:2]:
            sc = _color_for(pal, sb.get("color_key"), "amber")
            p_svg, pw = _svg_pill(px, y + 38, sb["label"], fill=pal["panel"], stroke=sc, text_color=sc, size=9.0)
            if px + pw < x + w - 8:
                parts.append(p_svg)
                px += pw + 5.0
        for ce in (n.get("callees") or [])[:2]:
            cc = _color_for(pal, ce.get("color_key"), "slate")
            ct = f"{_clip_chars(ce['short'], 13)} ×{ce['k1n_count']}"
            p_svg, pw = _svg_pill(px, y + 38, ct, fill=pal["panel"], stroke=cc, text_color=cc, size=9.0)
            if px + pw < x + w - 8:
                parts.append(p_svg)
                px += pw + 5.0
        parts.append("</g>")

    hdr_svg, leg_svg, total_h = _render_header_and_legend(payload, pal, width, y_cur + 18.0)
    return _wrap_svg(width, total_h, pal, hdr_svg + "\n" + "\n".join(parts) + "\n" + leg_svg)


def _wrap_svg(width: float, height: float, pal: Dict[str, str], inner: str) -> str:
    w_i = max(320, int(math.ceil(width)))
    h_i = max(240, int(math.ceil(height)))
    return (
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {w_i} {h_i}" '
        f'width="{w_i}" height="{h_i}" role="img" data-theme="{pal["name"]}">\n'
        f'<defs>\n'
        f'  <pattern id="cGrid" width="28" height="28" patternUnits="userSpaceOnUse">\n'
        f'    <path d="M 28 0 L 0 0 0 28" fill="none" stroke="{pal["grid"]}" stroke-width="0.7" opacity="0.65"/>\n'
        f'  </pattern>\n'
        f'</defs>\n'
        f'<rect class="c-bg" x="0" y="0" width="{w_i}" height="{h_i}" fill="{pal["bg"]}"/>\n'
        f'<rect x="0" y="0" width="{w_i}" height="{h_i}" fill="url(#cGrid)"/>\n'
        f'{inner}\n'
        f'</svg>\n'
    )


def render_circuit_svg(payload: Dict[str, Any], theme: str = "dark") -> str:
    """Render a canonical ``leanre.circuit/1`` payload to deterministic well-formed SVG."""
    pal = _theme_palette(theme)
    mode = str(payload.get("mode") or "")
    if mode == "macro":
        return _render_macro_svg(payload, pal)
    if mode == "bundle":
        return _render_bundle_svg(payload, pal)
    if mode == "theorem":
        return _render_theorem_svg(payload, pal)
    raise ValueError(f"Unsupported circuit mode: {mode!r}")


# ---------------------------------------------------------------------------
# Standalone Interactive Pan/Zoom HTML Exporter (`render_circuit_html`)
# ---------------------------------------------------------------------------

_HTML_TEMPLATE = """<!doctype html>
<html lang="en" data-theme="__THEME__">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>__TITLE__</title>
<style>
:root{
  --bg:#0b1020;--bar:#10172b;--panel:#131c34;--border:#273557;--text:#e2e8f0;--sub:#94a3b8;--accent:#22d3ee;
  --mono:ui-monospace,"SF Mono",Menlo,Consolas,monospace;
  --sans:-apple-system,BlinkMacSystemFont,"Segoe UI",Inter,sans-serif;
}
html[data-theme="light"]{
  --bg:#f8fafc;--bar:#ffffff;--panel:#f1f5f9;--border:#cbd5e1;--text:#0f172a;--sub:#475569;--accent:#0891b2;
}
*{box-sizing:border-box}
html,body{margin:0;padding:0;height:100%;overflow:hidden;background:var(--bg);color:var(--text);font-family:var(--sans);font-size:13px}
.app{display:flex;flex-direction:column;height:100%}
header{display:flex;align-items:center;gap:8px;padding:8px 14px;background:var(--bar);border-bottom:1px solid var(--border);flex-wrap:wrap;z-index:10}
.brand{font-family:var(--mono);font-weight:700;font-size:14px;margin-right:8px}.brand span{color:var(--accent)}
input[type=search]{background:var(--panel);color:var(--text);border:1px solid var(--border);border-radius:6px;padding:5px 10px;font-size:12px;min-width:210px}
button{background:var(--panel);color:var(--text);border:1px solid var(--border);border-radius:6px;padding:5px 10px;font-size:12px;cursor:pointer;font-weight:600}
button:hover{border-color:var(--accent)}
.spacer{flex:1}
.meta-pill{font-family:var(--mono);font-size:11px;color:var(--sub);padding:2px 8px;border:1px solid var(--border);border-radius:999px}
.stage-wrap{position:relative;flex:1;overflow:hidden;cursor:grab}
.stage-wrap.dragging{cursor:grabbing}
.stage{position:absolute;top:0;left:0;transform-origin:0 0}
.stage svg{display:block;user-select:none}
.circuit-node{cursor:pointer;transition:opacity .15s}
.circuit-node:hover rect{filter:brightness(1.15)}
.circuit-node.dim{opacity:.18}
.circuit-node.hl rect{stroke-width:2.8 !important}
.tooltip{position:fixed;pointer-events:none;z-index:30;max-width:440px;padding:8px 10px;border-radius:7px;background:var(--bar);border:1px solid var(--accent);color:var(--text);font-family:var(--mono);font-size:11px;line-height:1.4;box-shadow:0 8px 24px rgba(0,0,0,.35);display:none;word-break:break-word}
.drawer{display:flex;align-items:center;gap:12px;padding:7px 14px;background:var(--bar);border-top:1px solid var(--border);font-family:var(--mono);font-size:11.5px;min-height:36px;overflow:hidden}
.drawer .d-main{flex:1;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.drawer .d-cmd{color:var(--accent)}
</style>
</head>
<body>
<div class="app">
  <header>
    <div class="brand">leanre<span>.circuit</span></div>
    <input id="qSearch" type="search" placeholder="Highlight node / decl / k1n…">
    <button id="btnZoomIn" title="Zoom in">+</button>
    <button id="btnZoomOut" title="Zoom out">−</button>
    <button id="btnFit" title="Fit to viewport">Fit</button>
    <button id="btnReset" title="100% scale">1:1</button>
    <button id="btnTheme" title="Toggle dark/light theme">Theme</button>
    <button id="btnDownload" title="Download SVG file">Download SVG</button>
    <div class="spacer"></div>
    <span class="meta-pill" id="metaBadge"></span>
  </header>
  <div class="stage-wrap" id="stageWrap">
    <div class="stage" id="stage"></div>
  </div>
  <div class="drawer" id="drawer">
    <span class="d-main" id="drawerText">Click any node to inspect details &amp; cross-zoom hook; drag to pan, wheel to zoom.</span>
    <span class="d-cmd" id="drawerCmd"></span>
  </div>
</div>
<div class="tooltip" id="tip"></div>
<script id="leanre-circuit-data" type="application/json">__PAYLOAD_JSON__</script>
<script id="leanre-circuit-svg-dark" type="text/plain">__SVG_DARK__</script>
<script id="leanre-circuit-svg-light" type="text/plain">__SVG_LIGHT__</script>
<script>
(function(){
"use strict";
const DATA = JSON.parse(document.getElementById("leanre-circuit-data").textContent || "{}");
const SVG_DARK = document.getElementById("leanre-circuit-svg-dark").textContent;
const SVG_LIGHT = document.getElementById("leanre-circuit-svg-light").textContent;
const stageWrap = document.getElementById("stageWrap");
const stage = document.getElementById("stage");
const tip = document.getElementById("tip");
const qSearch = document.getElementById("qSearch");
const drawerText = document.getElementById("drawerText");
const drawerCmd = document.getElementById("drawerCmd");
const metaBadge = document.getElementById("metaBadge");

let theme = document.documentElement.getAttribute("data-theme") || "dark";
let scale = 1, tx = 16, ty = 16, dragging = false, sx = 0, sy = 0;

const nodeById = new Map();
for(const n of (DATA.nodes || [])) nodeById.set(n.id, n);
for(const b of (DATA.binders || [])) nodeById.set(b.id, b);

metaBadge.textContent = (DATA.mode || "").toUpperCase() + " · " +
  ((DATA.stats && DATA.stats.node_count) || 0) + " nodes · " +
  ((DATA.stats && DATA.stats.wire_count) || 0) + " wires";

function applyTransform(){
  stage.style.transform = "translate(" + tx + "px," + ty + "px) scale(" + scale + ")";
}

function fitToViewport(){
  const svg = stage.querySelector("svg");
  if(!svg) return;
  const vb = svg.viewBox.baseVal;
  const sw = vb.width || Number(svg.getAttribute("width")) || 1200;
  const sh = vb.height || Number(svg.getAttribute("height")) || 800;
  const cw = stageWrap.clientWidth || 1200;
  const ch = stageWrap.clientHeight || 800;
  scale = Math.max(0.25, Math.min(1.25, Math.min((cw - 24) / sw, (ch - 24) / sh)));
  tx = Math.max(8, (cw - sw * scale) / 2);
  ty = Math.max(8, (ch - sh * scale) / 2);
  applyTransform();
}

function applySearch(){
  const q = qSearch.value.trim().toLowerCase();
  const els = stage.querySelectorAll(".circuit-node");
  for(const g of els){
    const nid = g.getAttribute("data-node-id") || "";
    const obj = nodeById.get(nid) || {};
    const hay = ((obj.label || "") + " " + (obj.full_name || "") + " " + (obj.tooltip || "") + " " + (obj.badge || "")).toLowerCase();
    const hit = q ? hay.includes(q) : false;
    g.classList.toggle("dim", Boolean(q && !hit));
    g.classList.toggle("hl", hit);
  }
}

function mountSvg(){
  while(stage.firstChild) stage.removeChild(stage.firstChild);
  const parser = new DOMParser();
  const doc = parser.parseFromString(theme === "light" ? SVG_LIGHT : SVG_DARK, "image/svg+xml");
  const svgEl = doc.documentElement;
  stage.appendChild(document.importNode(svgEl, true));
  for(const g of stage.querySelectorAll(".circuit-node")){
    const nid = g.getAttribute("data-node-id") || "";
    const obj = nodeById.get(nid) || {id: nid};
    g.addEventListener("mouseenter", (ev) => {
      tip.textContent = obj.tooltip || obj.full_name || obj.label || nid;
      tip.style.display = "block";
    });
    g.addEventListener("mousemove", (ev) => {
      tip.style.left = Math.min(window.innerWidth - 460, ev.clientX + 14) + "px";
      tip.style.top = Math.min(window.innerHeight - 120, ev.clientY + 14) + "px";
    });
    g.addEventListener("mouseleave", () => { tip.style.display = "none"; });
    g.addEventListener("click", (ev) => {
      ev.stopPropagation();
      const zmode = g.getAttribute("data-zoom-mode") || "";
      const ztgt = g.getAttribute("data-zoom-target") || "";
      drawerText.textContent = obj.tooltip || obj.full_name || obj.label || nid;
      drawerCmd.textContent = (zmode && ztgt) ? ("leanre circuit " + zmode + " " + ztgt) : "";
      if(typeof window.LEANRE_CIRCUIT_ON_NODE_CLICK === "function"){
        window.LEANRE_CIRCUIT_ON_NODE_CLICK(obj, ev);
      }
      window.dispatchEvent(new CustomEvent("leanre:circuit-zoom", {detail: {mode: zmode, target: ztgt, node: obj}}));
    });
  }
  applySearch();
}

stageWrap.addEventListener("pointerdown", (ev) => {
  if(ev.button !== 0) return;
  dragging = true;
  sx = ev.clientX - tx;
  sy = ev.clientY - ty;
  stageWrap.classList.add("dragging");
});
window.addEventListener("pointermove", (ev) => {
  if(!dragging) return;
  tx = ev.clientX - sx;
  ty = ev.clientY - sy;
  applyTransform();
});
window.addEventListener("pointerup", () => {
  dragging = false;
  stageWrap.classList.remove("dragging");
});
stageWrap.addEventListener("wheel", (ev) => {
  ev.preventDefault();
  const rect = stageWrap.getBoundingClientRect();
  const mx = ev.clientX - rect.left;
  const my = ev.clientY - rect.top;
  const factor = ev.deltaY < 0 ? 1.12 : 0.89;
  const ns = Math.max(0.2, Math.min(4.0, scale * factor));
  tx = mx - (mx - tx) * (ns / scale);
  ty = my - (my - ty) * (ns / scale);
  scale = ns;
  applyTransform();
}, {passive: false});

document.getElementById("btnZoomIn").addEventListener("click", () => { scale = Math.min(4.0, scale * 1.2); applyTransform(); });
document.getElementById("btnZoomOut").addEventListener("click", () => { scale = Math.max(0.2, scale / 1.2); applyTransform(); });
document.getElementById("btnFit").addEventListener("click", fitToViewport);
document.getElementById("btnReset").addEventListener("click", () => { scale = 1; tx = 16; ty = 16; applyTransform(); });
document.getElementById("btnTheme").addEventListener("click", () => {
  theme = (theme === "dark") ? "light" : "dark";
  document.documentElement.setAttribute("data-theme", theme);
  mountSvg();
});
document.getElementById("btnDownload").addEventListener("click", () => {
  const txt = (theme === "light" ? SVG_LIGHT : SVG_DARK);
  const blob = new Blob([txt], {type: "image/svg+xml;charset=utf-8"});
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = "leanre_circuit_" + (DATA.mode || "diagram") + ".svg";
  document.body.appendChild(a);
  a.click();
  a.remove();
  URL.revokeObjectURL(url);
});
qSearch.addEventListener("input", applySearch);

mountSvg();
fitToViewport();
window.addEventListener("resize", fitToViewport);
})();
</script>
</body>
</html>
"""


def render_circuit_html(payload: Dict[str, Any], theme: str = "dark") -> str:
    """Render a standalone, zero-CDN, XSS-safe interactive pan/zoom HTML circuit viewer."""
    _theme_palette(theme)
    svg_dark = render_circuit_svg(payload, theme="dark").replace("</script", "<\\/script")
    svg_light = render_circuit_svg(payload, theme="light").replace("</script", "<\\/script")
    title = _xml_esc(payload.get("title") or "leanre circuit")
    return (
        _HTML_TEMPLATE
        .replace("__THEME__", _xml_esc(theme))
        .replace("__TITLE__", title)
        .replace("__PAYLOAD_JSON__", _escape_json_for_script(payload))
        .replace("__SVG_DARK__", svg_dark)
        .replace("__SVG_LIGHT__", svg_light)
    )


# ---------------------------------------------------------------------------
# CLI Integration (`leanre circuit`)
# ---------------------------------------------------------------------------

def normalize_circuit_argv(argv: Sequence[str]) -> List[str]:
    """Allow both `leanre circuit macro ...` and `leanre circuit --mode macro ...`."""
    raw = list(argv)
    if not raw:
        return raw
    if raw[0] in ("macro", "bundle", "theorem", "-h", "--help"):
        return raw
    out: List[str] = []
    mode_val: Optional[str] = None
    i = 0
    while i < len(raw):
        tok = raw[i]
        if tok == "--mode" and i + 1 < len(raw):
            mode_val = raw[i + 1]
            i += 2
            continue
        if tok.startswith("--mode="):
            mode_val = tok.split("=", 1)[1]
            i += 1
            continue
        out.append(tok)
        i += 1
    if mode_val:
        return [mode_val] + out
    return raw


def _emit_circuit_outputs(args: argparse.Namespace, payload: Dict[str, Any]) -> int:
    wrote = False
    if getattr(args, "svg", None):
        svg_txt = render_circuit_svg(payload, theme=args.theme)
        _safe_write_text(args.svg, svg_txt)
        wrote = True
    if getattr(args, "html", None):
        html_txt = render_circuit_html(payload, theme=args.theme)
        _safe_write_text(args.html, html_txt)
        wrote = True
    if getattr(args, "out", None):
        _safe_write_text(args.out, json.dumps(payload, indent=2, ensure_ascii=False))
        wrote = True
    if getattr(args, "json", False) or not wrote:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        st = payload.get("stats") or {}
        print(
            f"[circuit:{payload['mode']}] nodes={st.get('node_count', 0)} "
            f"wires={st.get('wire_count', 0)} elapsed={payload['pins']['elapsed_seconds']}s"
        )
    return 0


def _cmd_circuit(args: argparse.Namespace) -> int:
    try:
        mode = getattr(args, "circuit_mode", None)
        if mode == "macro":
            payload = build_macro_circuit(
                kernel_db_path=args.kernel_db,
                src_root=args.src_root,
                portability_json=getattr(args, "portability_json", None),
                dom_threshold=getattr(args, "dom_threshold", None),
                max_nodes=args.max_nodes,
                title=args.title,
            )
        elif mode == "bundle":
            payload = build_bundle_circuit(
                kernel_db_path=args.kernel_db,
                target=args.target,
                src_root=args.src_root,
                max_nodes=args.max_nodes,
                exact_case=args.exact_case,
                title=args.title,
            )
        elif mode == "theorem":
            payload = build_theorem_circuit(
                kernel_db_path=args.kernel_db,
                decl=args.decl,
                src_root=args.src_root,
                max_nodes=args.max_nodes,
                exact_case=args.exact_case,
                title=args.title,
            )
        else:
            print("leanre circuit requires subcommand: macro, bundle, or theorem", file=sys.stderr)
            return 2
        return _emit_circuit_outputs(args, payload)
    except (FileNotFoundError, LookupError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


def _add_common_circuit_args(p: argparse.ArgumentParser, default_max_nodes: int) -> None:
    p.add_argument("--kernel-db", default=DEFAULT_KERNEL_DB, help="Path to kernel.db (opened strictly mode=ro)")
    p.add_argument("--src-root", "--src", dest="src_root", default=None, help="Optional Lean src/ directory")
    p.add_argument("--max-nodes", type=int, default=default_max_nodes, help=f"Max displayed nodes per bank/lane (default: {default_max_nodes})")
    p.add_argument("--svg", default=None, help="Write vector SVG diagram to path")
    p.add_argument("--html", default=None, help="Write standalone zero-CDN interactive pan/zoom HTML to path")
    p.add_argument("--out", default=None, help="Optional path to write canonical leanre.circuit/1 JSON")
    p.add_argument("--json", action="store_true", help="Emit canonical leanre.circuit/1 JSON to stdout")
    p.add_argument("--theme", choices=("dark", "light"), default="dark", help="SVG/HTML color theme (default: dark)")
    p.add_argument("--title", default=None, help="Custom diagram title")
    p.add_argument("--exact-case", action="store_true", help="Disable case-insensitive fallback matching")


def register_cli(sub: Any, dest: str = "circuit_func") -> argparse.ArgumentParser:
    """Attach `leanre circuit` subcommand (`macro`, `bundle`, `theorem`) to `leanre/leanre.py`."""
    p = sub.add_parser(
        "circuit",
        help="2swap/Tromp-inspired 3-level Proof-Circuit JSON, SVG & interactive HTML generator",
    )
    csub = p.add_subparsers(dest="circuit_mode", required=True)

    pm = csub.add_parser("macro", help="Zoom 0: Macro repo circuit (pillars, shared diamonds, k1n/k1a motifs, islands)")
    _add_common_circuit_args(pm, default_max_nodes=12)
    pm.add_argument("--portability-json", default=None, help="Optional path to portability_gems.json")
    pm.add_argument("--dom-threshold", type=int, default=None, help="Override auto-scaled dominator subtree threshold")
    pm.set_defaults(**{dest: _cmd_circuit})

    pb = csub.add_parser("bundle", help="Zoom 1: Record / Prop-def IC pin-board & dangling consumer check")
    pb.add_argument("target", help="Structure, class, or Prop-def name")
    _add_common_circuit_args(pb, default_max_nodes=16)
    pb.set_defaults(**{dest: _cmd_circuit})

    pt = csub.add_parser("theorem", help="Zoom 2: Theorem Tromp binder bar, step wiring & k1n callee motifs")
    pt.add_argument("decl", help="Theorem or definition declaration name")
    _add_common_circuit_args(pt, default_max_nodes=32)
    pt.set_defaults(**{dest: _cmd_circuit})

    return p


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(prog="leanre-circuit", description="3-level Proof-Circuit visualizer backend")
    sub = ap.add_subparsers(dest="cmd", required=True)
    register_cli(sub, dest="circuit_func")
    norm = normalize_circuit_argv(sys.argv[1:] if argv is None else argv)
    if norm and norm[0] not in ("circuit", "-h", "--help"):
        norm = ["circuit"] + norm
    elif not norm:
        norm = ["circuit", "-h"]
    args = ap.parse_args(norm)
    return int(args.circuit_func(args))


if __name__ == "__main__":
    sys.exit(main())
