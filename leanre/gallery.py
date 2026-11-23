#!/usr/bin/env python3
"""leanre.gallery — Multi-project static site & registry builder ("Bring Your Own Lean").

Exports any Lean 4 repository (source-only, or enriched with kernel.db / NDJSON)
into `<out_dir>/p/<slug>/` using the canonical `leanre.site_manifest/1` schema,
and generates `<gallery_dir>/projects.json` (`leanre.projects_registry/1`).

Guardrails:
  - Python 3.11+ stdlib + sibling `leanre` modules only.
  - Zero raw `.lean` files or multi-line proof bodies exported.
  - Zero workstation absolute paths, hostnames, or secrets in outputs.
  - Refuses symlinked output paths and enforces GitHub Pages file size limits.
"""
from __future__ import annotations

import argparse
import collections
import datetime
import hashlib
import json
import os
import re
import sqlite3
import subprocess
import sys
import tempfile
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import circuit as _circuit  # noqa: E402
import config as _config  # noqa: E402
import graph as _graph  # noqa: E402
import scanner as _scanner  # noqa: E402

SITE_MANIFEST_SCHEMA = "leanre.site_manifest/1"
PROJECTS_REGISTRY_SCHEMA = "leanre.projects_registry/1"
MODULE_MATRIX_SCHEMA = "leanre.module_matrix/1"

MAX_EXPORT_FILE_BYTES = 25 * 1024 * 1024
MAX_SEARCH_SHARD_BYTES = 145 * 1024
MAX_SEARCH_TOTAL_BYTES = 3_400_000
MAX_SIG_LEN = 160

_FORBIDDEN_HOST_PATH_RE = re.compile(
    r"(?:"
    + "/" + "usr" + "/" + "local" + "/" + r"[^/\s]+/home/"
    + "|" + "/" + "usr" + "/" + "local" + "/" + "google"
    + "|" + "/" + "ho" + r"me/[A-Za-z0-9_.-]+"
    + "|" + "/" + "Us" + r"ers/[A-Za-z0-9_.-]+"
    + ")"
)

_SHOWCASE_ORDER = [
    "riemann-hypothesis",
    "navier-stokes",
    "navier-stokes-euler",
    "prime-number-theorem",
    "carleson",
    "flt",
    "sphere-packing",
    "tiny-demo",
]


def _open_ro(path: str) -> sqlite3.Connection:
    real = os.path.realpath(path)
    if not os.path.isfile(real):
        raise FileNotFoundError(f"Missing SQLite database: {path}")
    conn = sqlite3.connect(f"file:{real}?mode=ro", uri=True)
    conn.execute("PRAGMA query_only=1")
    return conn


def _safe_write_bytes(out_path: str, data: bytes) -> None:
    if os.path.islink(out_path):
        raise ValueError(f"Refusing to write through symlink: {out_path}")
    parent = os.path.dirname(os.path.abspath(out_path))
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(out_path, "wb") as f:
        f.write(data)


def _safe_write_text(out_path: str, text: str) -> int:
    raw = text.encode("utf-8")
    _safe_write_bytes(out_path, raw)
    return len(raw)


def _safe_write_json(out_path: str, obj: Any) -> int:
    raw = json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
    _safe_write_bytes(out_path, raw)
    return len(raw)


def _sanitize_text_paths(val: str) -> str:
    return _FORBIDDEN_HOST_PATH_RE.sub("<path>", val)


def _sanitize_json_value(obj: Any) -> Any:
    if isinstance(obj, str):
        return _sanitize_text_paths(obj) if _FORBIDDEN_HOST_PATH_RE.search(obj) else obj
    if isinstance(obj, list):
        return [_sanitize_json_value(v) for v in obj]
    if isinstance(obj, dict):
        return {k: _sanitize_json_value(v) for k, v in obj.items()}
    return obj


def _clip(text: Any, limit: int = MAX_SIG_LEN) -> str:
    if text is None:
        return ""
    s = " ".join(str(text).split())
    if len(s) <= limit:
        return s
    return s[: max(0, limit - 1)] + "…"


def _short_name(fqn: str, max_chars: int = 30) -> str:
    s = str(fqn or "").strip()
    if len(s) <= max_chars:
        return s
    parts = s.split(".")
    if len(parts) >= 2 and len(parts[-2]) + 1 + len(parts[-1]) <= max_chars:
        return f"{parts[-2]}.{parts[-1]}"
    tail = parts[-1]
    if len(tail) <= max_chars:
        return tail
    return tail[: max(4, max_chars - 1)] + "…"


def _clean_repo_url(repo_url: Optional[str]) -> str:
    s = str(repo_url or "").strip().rstrip("/")
    if s.endswith(".git"):
        s = s[:-4]
    if s and s.startswith(("https://github.com/", "http://github.com/")):
        return s
    return s


def _normalize_src_prefix(src_prefix: str) -> str:
    s = str(src_prefix or "").strip().lstrip("/")
    if not s:
        return ""
    if not s.endswith("/"):
        s += "/"
    return s


def _github_blob_url(repo_url: str, pinned_commit: str, src_prefix: str, file_path: str, line: Optional[int] = None) -> Optional[str]:
    base = _clean_repo_url(repo_url)
    if not base or not base.startswith("https://github.com/"):
        return None
    commit = str(pinned_commit or "main").strip()
    rel = str(file_path or "").replace(os.sep, "/").lstrip("/")
    if not rel or ".." in rel:
        return None
    pref = _normalize_src_prefix(src_prefix)
    if pref and not rel.startswith(pref):
        rel = pref + rel
    frag = f"#L{int(line)}" if line and int(line) > 0 else ""
    return f"{base}/blob/{commit}/{rel}{frag}"


def _search_prefix_bucket(text: str) -> str:
    alnum = re.sub(r"[^a-z0-9]", "", str(text or "").lower())
    if len(alnum) >= 2:
        return alnum[:2]
    return "_"


def _slugify_id(text: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9_-]+", "_", str(text or "")).strip("_")
    return cleaned or "node"


def _infer_category(slug: str, badge: str = "", description: str = "") -> str:
    low = f"{slug} {badge} {description}".lower()
    if "demo" in low or slug == "tiny-demo":
        return "demo"
    if any(k in low for k in ("ai", "llm", "navier-stokes", "riemann-hypothesis")):
        return "ai-assisted"
    return "human-baseline"


def _infer_license(src_dir: str, explicit: str = "") -> str:
    if explicit and explicit.strip():
        return explicit.strip()
    for base in (src_dir, os.path.dirname(os.path.abspath(src_dir))):
        if not base or not os.path.isdir(base):
            continue
        for fn in ("LICENSE", "LICENSE.md", "LICENSE.txt", "COPYING"):
            cand = os.path.join(base, fn)
            if os.path.isfile(cand) and not os.path.islink(cand):
                try:
                    with open(cand, "r", encoding="utf-8", errors="replace") as f:
                        head = f.read(1024)
                    if "Apache License" in head and "2.0" in head:
                        return "Apache-2.0"
                    if "MIT License" in head:
                        return "MIT"
                    if "GNU AFFERO GENERAL PUBLIC LICENSE" in head:
                        return "AGPL-3.0-or-later"
                    if "GNU GENERAL PUBLIC LICENSE" in head:
                        return "GPL-3.0"
                    if "BSD" in head:
                        return "BSD"
                    return "Custom (LICENSE file)"
                except OSError:
                    pass
    return "None (no license)"


def _git_meta(path: str) -> Tuple[str, str]:
    """Return (repo_url, commit_sha) from git if `path` is inside a git repo."""
    for cand in (path, os.path.dirname(os.path.abspath(path))):
        if not cand or not os.path.isdir(cand):
            continue
        r_sha = subprocess.run(
            ["git", "-C", cand, "rev-parse", "HEAD"],
            capture_output=True, text=True, check=False,
        )
        if r_sha.returncode == 0 and r_sha.stdout.strip():
            sha = r_sha.stdout.strip()
            r_url = subprocess.run(
                ["git", "-C", cand, "remote", "get-url", "origin"],
                capture_output=True, text=True, check=False,
            )
            url = _clean_repo_url(r_url.stdout.strip()) if r_url.returncode == 0 else ""
            return url, sha
    return "", ""


def _plural_word(n: int, singular: str, plural: Optional[str] = None) -> str:
    return singular if int(n) == 1 else (plural or (singular + "s"))


def _plural(n: int, singular: str, plural: Optional[str] = None) -> str:
    return f"{int(n):,} {_plural_word(n, singular, plural)}"


def _is_challenge_spec_file(file_path: str, module_name: str = "") -> bool:
    """Identify intentional Comparator/Challenge specification stubs (not incomplete proofs)."""
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


def _split_sorry_hits(
    hits: Sequence[Dict[str, Any]],
    by_name: Dict[str, Dict[str, Any]],
) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    """Partition `sorry` hits into `(proof_sorry_hits, challenge_sorry_hits)`."""
    proof_hits: List[Dict[str, Any]] = []
    challenge_hits: List[Dict[str, Any]] = []
    for h in hits:
        if h.get("tag") != "sorry":
            continue
        mod = str(h.get("module") or "")
        m_obj = by_name.get(mod)
        fpath = m_obj["file_path"] if m_obj else (mod.replace(".", "/") + ".lean")
        if _is_challenge_spec_file(fpath, mod):
            challenge_hits.append(h)
        else:
            proof_hits.append(h)
    return proof_hits, challenge_hits


def _bfs_reach_count(start: str, adj: Dict[str, List[str]]) -> int:
    seen: Set[str] = {start}
    q: collections.deque[str] = collections.deque([start])
    while q:
        u = q.popleft()
        for v in adj.get(u, ()):
            if v not in seen:
                seen.add(v)
                q.append(v)
    return len(seen)


def _apply_multi_root_graph(
    db_path: str,
    root_names: Sequence[str],
    stats: Dict[str, Any],
) -> Dict[str, Any]:
    """Recompute BFS & virtual-root CHK dominators across multiple entry modules."""
    conn = sqlite3.connect(db_path)
    try:
        mod_rows = conn.execute(
            "SELECT id, name, lines FROM modules ORDER BY id ASC"
        ).fetchall()
        n = len(mod_rows)
        if n == 0:
            return stats
        id_to_name = [str(r[1]) for r in mod_rows]
        name_to_idx = {nm: idx for idx, nm in enumerate(id_to_name)}
        lines_arr = [int(r[2]) for r in mod_rows]

        adj: List[List[int]] = [[] for _ in range(n)]
        radj: List[List[int]] = [[] for _ in range(n)]
        adj_str: Dict[str, List[str]] = collections.defaultdict(list)
        for src, dst in conn.execute("SELECT src, dst FROM module_edges"):
            u = name_to_idx.get(str(src))
            v = name_to_idx.get(str(dst))
            if u is not None and v is not None and u != v:
                adj[u].append(v)
                radj[v].append(u)
                adj_str[str(src)].append(str(dst))

        root_ids = [name_to_idx[r] for r in root_names if r in name_to_idx]
        if not root_ids:
            return stats

        bfs_depth, parent_to_main = _graph.bfs_shortest_paths(root_ids, adj, n)
        # Add synthetic super-root at index `n` with edges to every entry root
        v_idx = n
        adj_v = [list(x) for x in adj] + [list(root_ids)]
        radj_v = [list(x) for x in radj] + [[]]
        for rid in root_ids:
            radj_v[rid].append(v_idx)
        lines_v = lines_arr + [0]
        idom_v, rpo_v, dom_size_v, dom_lines_v, _dom_children = _graph.dominators_chk(
            v_idx, adj_v, radj_v, n + 1, weights=lines_v
        )

        mod_updates: List[Tuple[int, Optional[str], Optional[str], int, int, int]] = []
        for idx in range(n):
            p_main = id_to_name[parent_to_main[idx]] if parent_to_main[idx] != -1 else None
            dom_p = id_to_name[idom_v[idx]] if idom_v[idx] not in (-1, v_idx) else None
            mod_updates.append((
                int(bfs_depth[idx]),
                p_main,
                dom_p,
                int(dom_size_v[idx]),
                int(dom_lines_v[idx]),
                idx + 1,
            ))
        conn.executemany(
            """UPDATE modules
               SET bfs_depth = ?, parent_to_main = ?, dom_parent = ?,
                   dom_subtree_size = ?, dom_subtree_lines = ?
               WHERE id = ?""",
            mod_updates,
        )

        # Update forensic_hits shortest paths to nearest root
        hit_updates: List[Tuple[int, str, int]] = []
        for hid, hmod in conn.execute("SELECT id, module FROM forensic_hits"):
            uidx = name_to_idx.get(str(hmod))
            if uidx is None:
                continue
            hops = int(bfs_depth[uidx])
            path_ids = _graph.reconstruct_path_to_root(uidx, parent_to_main)
            path_names = [id_to_name[x] for x in path_ids]
            hit_updates.append((hops, json.dumps(path_names, ensure_ascii=False), int(hid)))
        if hit_updates:
            conn.executemany(
                "UPDATE forensic_hits SET hops_to_main = ?, shortest_path_to_main_json = ? WHERE id = ?",
                hit_updates,
            )

        cs = json.loads(
            conn.execute("SELECT value_json FROM meta WHERE key='corpus_stats'").fetchone()[0]
        )
        reach_union = sum(1 for d in bfs_depth if d >= 0)
        rc_map = {r: _bfs_reach_count(r, adj_str) for r in root_names}
        cs["root_module"] = ", ".join(root_names)
        cs["root_modules"] = list(root_names)
        cs["root_reach_counts"] = rc_map
        cs["reachable_from_main"] = reach_union
        cs["max_bfs_depth"] = max((d for d in bfs_depth if d >= 0), default=0)
        conn.execute(
            "INSERT OR REPLACE INTO meta(key, value_json) VALUES ('corpus_stats', ?)",
            (json.dumps(cs, ensure_ascii=False),),
        )
        conn.commit()
        return cs
    finally:
        conn.close()


def _run_scanner_smart(
    src_dir: str,
    db_path: str,
    *,
    auto_root: bool = True,
    root_module: Optional[str] = None,
    workers: Optional[int] = None,
    cfg: Optional[_config.LeanreConfig] = None,
) -> Dict[str, Any]:
    """Run `scanner.run_scan` with `--max-hits-per-tag 0`, multi-root targets, and leaf-root escape."""
    init_root = "auto" if auto_root else (root_module or "auto")
    stats = _scanner.run_scan(
        src_dir=src_dir,
        db_path=db_path,
        root_module=init_root,
        workers=workers,
        verbose=False,
        config=cfg,
        max_hits_per_tag=0,
    )
    if not auto_root:
        return stats

    n_mods = int(stats.get("modules") or 0)
    reach = int(stats.get("reachable_from_main") or 0)

    conn = _open_ro(db_path)
    try:
        mods = [
            (str(r[0]), int(r[1]), int(r[2]))
            for r in conn.execute("SELECT name, fan_in, fan_out FROM modules")
        ]
        adj: Dict[str, List[str]] = collections.defaultdict(list)
        for src, dst in conn.execute("SELECT src, dst FROM module_edges"):
            adj[str(src)].append(str(dst))
    finally:
        conn.close()

    lake_info = _scanner._load_lake_hints(src_dir)
    default_targets: List[str] = []
    if lake_info:
        default_targets = [str(t).strip().removesuffix(".*") for t in (lake_info.get("defaultTargets") or [])]

    mod_set = {m for m, _, _ in mods}
    non_challenge_targets: List[str] = []
    for dt in default_targets:
        if _is_challenge_spec_file(dt + ".lean", dt):
            continue
        if dt in mod_set and dt not in non_challenge_targets:
            non_challenge_targets.append(dt)

    # Multi-root union when `lakefile.toml` `defaultTargets` names >= 2 co-equal proof targets
    if len(non_challenge_targets) >= 2:
        union_seen: Set[str] = set()
        for tgt in non_challenge_targets:
            q = collections.deque([tgt])
            union_seen.add(tgt)
            while q:
                u = q.popleft()
                for v in adj.get(u, ()):
                    if v not in union_seen:
                        union_seen.add(v)
                        q.append(v)
        single_best = max(_bfs_reach_count(t, adj) for t in non_challenge_targets)
        if len(union_seen) > single_best:
            return _apply_multi_root_graph(db_path, non_challenge_targets, stats)

    if n_mods < 10 or reach > 5:
        return stats

    candidates: List[str] = list(non_challenge_targets)
    for dt in default_targets:
        if dt in mod_set and dt not in candidates:
            candidates.append(dt)
    for nm, fi, fo in sorted(mods, key=lambda x: (-x[2], x[1], x[0])):
        if fo > 0 and ("." not in nm or fi == 0):
            if nm not in candidates:
                candidates.append(nm)
            if len(candidates) >= 24:
                break

    best_root = stats.get("root_module")
    best_reach = reach
    for cand in candidates:
        rc = _bfs_reach_count(cand, adj)
        if rc > best_reach:
            best_reach = rc
            best_root = cand

    if best_root and best_root != stats.get("root_module") and best_reach >= max(10, reach * 3):
        stats = _scanner.run_scan(
            src_dir=src_dir,
            db_path=db_path,
            root_module=str(best_root),
            workers=workers,
            verbose=False,
            config=cfg,
            max_hits_per_tag=0,
        )
    return stats


def _run_flirt_tier1(
    src_dir: str,
    tier1_db_path: str,
    *,
    threads: int = 8,
    cfg: Optional[_config.LeanreConfig] = None,
) -> Dict[str, Any]:
    """Run FLIRT Tier 1 without RH calibration."""
    from flirt import tier1 as _tier1

    return _tier1.run_tier1(
        src_dir=src_dir,
        db_path=tier1_db_path,
        summary_path=None,
        threads=threads,
        kernel_db="",  # explicitly disable RH kernel calibration
        verbose=False,
        config=cfg,
    )


def _query_scanner_snapshot(db_path: str) -> Dict[str, Any]:
    """Read module, declaration, and forensic data from `leanre.db` (read-only)."""
    conn = _open_ro(db_path)
    try:
        corpus_stats = json.loads(
            conn.execute("SELECT value_json FROM meta WHERE key='corpus_stats'").fetchone()[0]
        )
        forensic_summary = json.loads(
            conn.execute("SELECT value_json FROM meta WHERE key='forensic_summary'").fetchone()[0]
        )
        modules = [
            {
                "id": int(r[0]),
                "name": str(r[1]),
                "file_path": str(r[2]),
                "namespace_top": str(r[3]),
                "namespace_l2": str(r[4]),
                "lines": int(r[5]),
                "lines_wc": int(r[6]),
                "decl_count": int(r[7]),
                "thm_count": int(r[8]),
                "def_count": int(r[9]),
                "fan_in": int(r[10]),
                "fan_out": int(r[11]),
                "bfs_depth": int(r[12]),
                "dom_parent": str(r[13]) if r[13] is not None else None,
                "dom_subtree_size": int(r[14]),
                "dom_subtree_lines": int(r[15]),
                "rev_reach": int(r[16]),
                "is_shim": int(r[17]),
                "flags": json.loads(r[18]) if r[18] else [],
            }
            for r in conn.execute(
                """SELECT id, name, file_path, namespace_top, namespace_l2, lines, lines_wc,
                          decl_count, thm_count, def_count, fan_in, fan_out, bfs_depth,
                          dom_parent, dom_subtree_size, dom_subtree_lines, rev_reach,
                          is_shim, forensic_flags_json
                   FROM modules ORDER BY id ASC"""
            )
        ]
        edges = [
            (str(r[0]), str(r[1]))
            for r in conn.execute("SELECT src, dst FROM module_edges ORDER BY src ASC, dst ASC")
        ]
        decls = [
            {
                "id": int(r[0]),
                "name": str(r[1]),
                "kind": str(r[2]),
                "module": str(r[3]),
                "line": int(r[4]),
                "sig": str(r[5] or ""),
                "tags": json.loads(r[6]) if r[6] else [],
            }
            for r in conn.execute(
                "SELECT id, name, kind, module, line_no, signature_snippet, forensic_tags FROM declarations ORDER BY id ASC"
            )
        ]
        hits = [
            {
                "tag": str(r[0]),
                "severity": str(r[1]),
                "module": str(r[2]),
                "line": int(r[3]),
                "decl_name": str(r[4]) if r[4] else None,
                "hops_to_main": int(r[5]),
            }
            for r in conn.execute(
                """SELECT tag, severity, module, line_no, decl_name, hops_to_main
                   FROM forensic_hits
                   ORDER BY CASE severity WHEN 'critical' THEN 0 WHEN 'audit' THEN 1 WHEN 'interesting' THEN 2 ELSE 3 END,
                            hops_to_main ASC, module ASC, line_no ASC"""
            )
        ]
    finally:
        conn.close()

    return {
        "corpus_stats": corpus_stats,
        "forensic_summary": forensic_summary,
        "modules": modules,
        "edges": edges,
        "decls": decls,
        "hits": hits,
    }


def _build_source_overview_pillars(
    modules: Sequence[Dict[str, Any]],
    root_module: str,
    reach_count: int,
    root_modules: Optional[Sequence[str]] = None,
) -> List[Dict[str, Any]]:
    """Top 12 module dominator / import hubs under `root_module`."""
    denom = max(1, reach_count, len(modules))
    by_name = {m["name"]: m for m in modules}
    root_set = set(root_modules or [root_module])
    root_obj = by_name.get(root_module)

    # Sort dominators under root_module(s) by dom_subtree_size, then fan_in
    dom_ranked = sorted(
        (m for m in modules if m["dom_subtree_size"] > 0),
        key=lambda m: (0 if m["name"] in root_set else 1, -m["dom_subtree_size"], -m["fan_in"], m["name"]),
    )
    selected: List[Dict[str, Any]] = []
    seen: Set[str] = set()
    for m in dom_ranked:
        if m["name"] in seen:
            continue
        seen.add(m["name"])
        selected.append(m)
        if len(selected) >= 12:
            break

    # If few modules sit in the dominator tree (e.g. disjoint sub-libraries), fill with top fan-in hubs
    if len(selected) < 12:
        for m in sorted(modules, key=lambda x: (-x["rev_reach"], -x["fan_in"], -x["lines_wc"], x["name"])):
            if m["name"] in seen:
                continue
            seen.add(m["name"])
            selected.append(m)
            if len(selected) >= 12:
                break

    pillars: List[Dict[str, Any]] = []
    for idx, m in enumerate(selected[:12]):
        sub_sz = m["dom_subtree_size"] if m["dom_subtree_size"] > 0 else max(1, m["rev_reach"])
        pct = round(100.0 * sub_sz / denom, 2)
        depth = 0 if m["name"] in root_set else (1 if (m["dom_parent"] in root_set or m["dom_parent"] is None) else min(3, max(1, m["bfs_depth"])))
        role = "root" if m["name"] in root_set else ("spine_hub" if idx == 1 and root_obj and sub_sz > 0.7 * max(1, root_obj["dom_subtree_size"]) else "pillar")
        if m["dom_subtree_size"] > 0:
            tail = "entry module" if m["name"] in root_set else f"{m['fan_in']:,} direct {_plural_word(m['fan_in'], 'importer')}"
            note = f"{sub_sz:,} dominated modules · {m['lines_wc']:,} lines · {tail}"
        else:
            note = f"outside primary root · imported transitively by {m['rev_reach']:,} modules · {m['lines_wc']:,} lines"
        pillars.append({
            "id": _slugify_id(m["name"]),
            "name": m["name"],
            "label": _short_name(m["name"], 32),
            "role": role,
            "decl": None,
            "target": m["name"],
            "subtree_size": sub_sz,
            "pct_live": pct,
            "depth": depth,
            "idom": m["dom_parent"],
            "lines_wc": m["lines_wc"],
            "decl_count": m["decl_count"],
            "fan_in": m["fan_in"],
            "rev_reach": m["rev_reach"],
            "note": note,
            "description": note,
            "circuit_mode": "macro",
            "circuit_target": "",
        })
    return pillars


def _build_source_macro_circuit(
    *,
    slug: str,
    title: str,
    snapshot: Dict[str, Any],
    flirt_summary: Optional[Dict[str, Any]],
) -> Tuple[Dict[str, Any], str, str]:
    """Build a canonical `leanre.circuit/1` macro diagram & dark/light SVGs for source-only repos."""
    cs = snapshot["corpus_stats"]
    modules = snapshot["modules"]
    hits = snapshot["hits"]
    root_mod = str(cs.get("root_module") or "Main")
    root_mods = list(cs.get("root_modules") or [root_mod])
    root_set = set(root_mods)
    root_reach_counts = cs.get("root_reach_counts") or {}
    n_mods = len(modules)
    reach = int(cs.get("reachable_from_main") or 0)
    unreached = max(0, n_mods - reach)
    total_edges = int(cs.get("project_import_edges") or 0)
    total_decls = int(cs.get("declarations") or 0)
    total_lines = int(cs.get("lines_wc") or 0)

    by_name = {m["name"]: m for m in modules}
    nodes: List[Dict[str, Any]] = []
    wires: List[Dict[str, Any]] = []

    # Lane 0: Root module(s) + Unreachable / dead modules
    root_node_ids: Dict[str, str] = {}
    for r_idx, r_name in enumerate(root_mods):
        rnid = f"root:{r_idx}"
        root_node_ids[r_name] = rnid
        root_m = by_name.get(r_name)
        r_reach = int(root_reach_counts.get(r_name, reach))
        r_loc = root_m["lines_wc"] if (root_m and len(root_mods) > 1) else total_lines
        nodes.append({
            "id": rnid,
            "label": _short_name(r_name, 26),
            "full_name": r_name,
            "kind": "root",
            "status": "live",
            "lane": 0,
            "badge": f"{r_reach:,}/{n_mods:,} reach · {r_loc:,} lines",
            "anchor": f"{root_m['file_path']}:1" if root_m else None,
            "metrics": {"fan_in": root_m["fan_in"] if root_m else 0, "fan_out": root_m["fan_out"] if root_m else 0},
            "zoom_target": None,
            "tooltip": f"Entry module {r_name}: reaches {r_reach:,}/{n_mods:,} modules, {total_edges:,} import edges",
        })
    nodes.append({
        "id": "dead_mass",
        "label": f"Unreached ({unreached:,} mods)",
        "full_name": f"Modules unreachable from {root_mod}",
        "kind": "dead_mass",
        "status": "dead" if unreached > 0 else "live",
        "lane": 0,
        "badge": f"{(100.0 * unreached / max(1, n_mods)):.1f}% of files",
        "metrics": {"dead_decls": unreached, "total_decls": n_mods},
        "zoom_target": None,
        "tooltip": f"{unreached:,} of {n_mods:,} modules not imported by {root_mod}",
    })

    # Lane 1: Top dominator submodules (up to 8) + Shared Diamond summary
    dom_cands = [
        m for m in sorted(
            modules,
            key=lambda x: (-x["dom_subtree_size"], -x["rev_reach"], -x["fan_in"], x["name"]),
        )
        if m["name"] not in root_set
    ][:8]
    dom_ids: Dict[str, str] = {}
    for idx, m in enumerate(dom_cands):
        nid = f"dom:{m['id']}"
        dom_ids[m["name"]] = nid
        sub_sz = m["dom_subtree_size"] if m["dom_subtree_size"] > 0 else m["rev_reach"]
        pct = 100.0 * sub_sz / max(1, n_mods)
        is_hub = m["dom_subtree_size"] > 0.65 * max(1, reach)
        nodes.append({
            "id": nid,
            "label": _short_name(m["name"], 24),
            "full_name": m["name"],
            "kind": "spine_hub" if is_hub else "pillar",
            "status": "live" if m["dom_subtree_size"] > 0 else "dead",
            "lane": 1,
            "badge": f"dom {sub_sz:,} ({pct:.1f}%) · {m['lines_wc']:,}L",
            "anchor": f"{m['file_path']}:1",
            "metrics": {
                "subtree_size": sub_sz,
                "pct_live": round(pct, 1),
                "fan_in": m["fan_in"],
                "fan_out": m["fan_out"],
            },
            "zoom_target": None,
            "tooltip": f"{m['name']} | dominated={m['dom_subtree_size']:,}, transitive_importers={m['rev_reach']:,}, direct_importers={m['fan_in']}, lines={m['lines_wc']:,}",
        })

    for m in dom_cands:
        nid = dom_ids[m["name"]]
        parent = m.get("dom_parent")
        if parent and parent in root_node_ids:
            wires.append({
                "id": f"w:r->{m['id']}",
                "src": root_node_ids[parent],
                "dst": nid,
                "kind": "root_entry",
                "status": "used",
                "color_key": "emerald",
                "label": "",
            })
        elif parent and parent in dom_ids:
            wires.append({
                "id": f"w:d:{parent}->{m['id']}",
                "src": dom_ids[parent],
                "dst": nid,
                "kind": "dom_spine",
                "status": "used",
                "color_key": "cyan",
                "label": "",
            })
        elif m["dom_subtree_size"] > 0:
            wires.append({
                "id": f"w:r2:{m['id']}",
                "src": "root:0",
                "dst": nid,
                "kind": "root_entry",
                "status": "used",
                "color_key": "blue",
                "label": "",
            })

    # Shared fan-in diamond node
    shared_mods = [m for m in modules if m["fan_in"] >= 2]
    nodes.append({
        "id": "shared_diamond",
        "label": f"Shared Core ({len(shared_mods):,} mods)",
        "full_name": "Modules imported by >= 2 project files",
        "kind": "diamond",
        "status": "live",
        "lane": 1,
        "badge": f"{total_edges:,} import edges",
        "metrics": {"shared_decls": len(shared_mods), "cross_pillar_direct_edges": total_edges},
        "zoom_target": None,
        "tooltip": f"{len(shared_mods):,} modules have fan-in >= 2 across {total_edges:,} import edges",
    })
    for m in dom_cands[:4]:
        wires.append({
            "id": f"w:dia:{m['id']}",
            "src": dom_ids[m["name"]],
            "dst": "shared_diamond",
            "kind": "diamond_share",
            "status": "used",
            "color_key": "violet",
            "label": "",
        })

    # Lane 2: Top fan-in library modules (up to 10)
    top_fan_in = sorted(
        modules,
        key=lambda x: (-x["fan_in"], -x["rev_reach"], -x["lines_wc"], x["name"]),
    )[:10]
    palette = _circuit.MOTIF_PALETTE
    for idx, m in enumerate(top_fan_in):
        nodes.append({
            "id": f"motif:{idx}",
            "label": _short_name(m["name"], 24),
            "full_name": m["name"],
            "kind": "motif_cluster",
            "status": "live",
            "lane": 2,
            "color": palette[idx % len(palette)],
            "badge": f"{m['fan_in']} importers · {m['lines_wc']:,}L",
            "anchor": f"{m['file_path']}:1",
            "metrics": {"fan_in": m["fan_in"], "rev_reach": m["rev_reach"], "lines": m["lines_wc"]},
            "zoom_target": None,
            "tooltip": f"Top library {m['name']}: imported directly by {_plural(m['fan_in'], 'module')} (transitive importers={m['rev_reach']:,}, {m['lines_wc']:,} lines)",
        })

    # Lane 3: Incomplete / axiomatic hotspots (proof sorry, challenge sorry, axiom, decide_kernel, native_decide, unsafe, implemented_by)
    tag_tot = (snapshot["forensic_summary"].get("total_hit_counts") or {})
    proof_sorry_hits, challenge_sorry_hits = _split_sorry_hits(hits, by_name)
    proof_sorry_cnt = len(proof_sorry_hits)
    challenge_sorry_cnt = len(challenge_sorry_hits)
    hotspot_nodes_added = 0

    if proof_sorry_cnt > 0:
        first_hit = proof_sorry_hits[0]
        first_mod = by_name.get(first_hit["module"])
        n_files = len({h["module"] for h in proof_sorry_hits})
        nodes.append({
            "id": "island:hot:proof_sorry",
            "label": f"proof sorry ({proof_sorry_cnt:,})",
            "full_name": first_hit["decl_name"] or first_hit["module"],
            "kind": "island",
            "status": "conditional_prop",
            "lane": 3,
            "badge": _plural(n_files, "file"),
            "anchor": f"{first_mod['file_path']}:{first_hit['line']}" if first_mod else None,
            "metrics": {"max_project_decls": proof_sorry_cnt},
            "zoom_target": None,
            "tooltip": f"proof sorry / admit: {_plural(proof_sorry_cnt, 'hit')} across {_plural(n_files, 'file')}",
        })
        hotspot_nodes_added += 1

    if challenge_sorry_cnt > 0:
        first_hit = challenge_sorry_hits[0]
        first_mod = by_name.get(first_hit["module"])
        n_files = len({h["module"] for h in challenge_sorry_hits})
        nodes.append({
            "id": "island:hot:challenge_sorry",
            "label": f"challenge specs ({challenge_sorry_cnt:,})",
            "full_name": first_hit["decl_name"] or first_hit["module"],
            "kind": "island",
            "status": "projected",
            "lane": 3,
            "badge": _plural(n_files, "file"),
            "anchor": f"{first_mod['file_path']}:{first_hit['line']}" if first_mod else None,
            "metrics": {"max_project_decls": challenge_sorry_cnt},
            "zoom_target": None,
            "tooltip": f"challenge spec placeholders: {_plural(challenge_sorry_cnt, 'hit')} across {_plural(n_files, 'file')}",
        })
        hotspot_nodes_added += 1

    hotspot_specs = [
        ("axiom", "axiom"),
        ("decide_kernel", "decide +kernel"),
        ("native_decide", "native_decide"),
        ("unsafe", "unsafe"),
        ("implemented_by", "implemented_by / @[extern]"),
    ]
    for tag_key, tag_label in hotspot_specs:
        cnt = int(tag_tot.get(tag_key, 0) or 0)
        if cnt <= 0:
            continue
        tag_hits = [h for h in hits if h["tag"] == tag_key]
        first_hit = tag_hits[0] if tag_hits else None
        first_mod = by_name.get(first_hit["module"]) if first_hit else None
        anchor = f"{first_mod['file_path']}:{first_hit['line']}" if (first_mod and first_hit) else None
        n_files = len({h["module"] for h in tag_hits})
        nodes.append({
            "id": f"island:hot:{tag_key}",
            "label": f"{tag_label} ({cnt:,})",
            "full_name": first_hit["decl_name"] or first_hit["module"] if first_hit else tag_label,
            "kind": "island",
            "status": "conditional_prop",
            "lane": 3,
            "badge": _plural(n_files, "file"),
            "anchor": anchor,
            "metrics": {"max_project_decls": cnt},
            "zoom_target": None,
            "tooltip": f"{tag_label}: {_plural(cnt, 'hit')} across {_plural(n_files, 'file')}",
        })
        hotspot_nodes_added += 1

    if hotspot_nodes_added == 0:
        nodes.append({
            "id": "island:clean",
            "label": "Clean Audit (0 sorry/axiom)",
            "full_name": f"{slug}: zero sorry/axiom/unsafe/decide+kernel hits",
            "kind": "island",
            "status": "projected",
            "lane": 3,
            "badge": f"{total_decls:,} decls",
            "metrics": {"max_project_decls": total_decls},
            "zoom_target": None,
            "tooltip": "Zero sorry, axiom, decide +kernel, native_decide, or unsafe hits detected",
        })

    axiom_cnt = int(tag_tot.get("axiom", 0) or 0)
    dk_cnt = int(tag_tot.get("decide_kernel", 0) or 0)
    flirt_mis = int((flirt_summary or {}).get("misfile_scoring", {}).get("alertable_misfiles_total", 0) or 0)

    if challenge_sorry_cnt > 0:
        sorry_badge = f"proof sorry {proof_sorry_cnt:,} (+{challenge_sorry_cnt:,} challenge)"
    else:
        sorry_badge = f"sorry {proof_sorry_cnt:,}"
    badges = [
        {"label": f"{n_mods:,} files · {total_lines:,} lines", "color_key": "emerald"},
        {"label": f"{total_decls:,} decls", "color_key": "cyan"},
        {"label": f"{sorry_badge} · axiom {axiom_cnt:,}", "color_key": "amber" if (proof_sorry_cnt or axiom_cnt) else "emerald"},
    ]
    if dk_cnt:
        badges.append({"label": f"decide +kernel {dk_cnt:,}", "color_key": "violet"})
    if flirt_summary is not None:
        badges.append({"label": f"dir outliers {flirt_mis:,}", "color_key": "slate"})

    payload: Dict[str, Any] = {
        "schema": _circuit.SCHEMA_VERSION,
        "mode": "macro",
        "source_only": True,
        "title": f"{title} — Module Import Map",
        "target": None,
        "pins": {
            "kernel_db": f"{slug} (source)",
            "src_root": slug,
            "source_mode": "source_only",
            "dom_tree": root_mod,
            "elapsed_seconds": 0,
        },
        "stats": {
            "total_decls": total_decls,
            "live_decls": reach,
            "dead_decls": unreached,
            "roots_count": len(root_mods),
            "pillars_count": len(dom_cands),
            "shared_diamond_roots": len(shared_mods),
            "shared_diamond_decls": len(shared_mods),
            "cross_pillar_shared_edges": total_edges,
            "motif_clusters_count": len(top_fan_in),
            "excluded_prop_shells": 0,
            "excluded_trivial_shells": 0,
            "islands_count": max(1, hotspot_nodes_added),
            "node_count": len(nodes),
            "wire_count": len(wires),
        },
        "lanes": [
            {"id": 0, "label": "Entry Module(s) & Unreached Modules"},
            {"id": 1, "label": "Major Import Subtrees & Shared Hubs"},
            {"id": 2, "label": "Most-Imported Modules (by Direct Importers)"},
            {"id": 3, "label": "Incomplete / Axiomatic Hotspots (sorry / axiom)"},
        ],
        "binders": [],
        "nodes": nodes,
        "wires": wires,
        "badges": badges,
        "legend": [
            {"label": "Entry / Dominator Submodule", "color_key": "emerald", "style": "solid"},
            {"label": "Dominator Spine Hub", "color_key": "cyan", "style": "solid"},
            {"label": "Shared Core (>=2 importers)", "color_key": "violet", "style": "solid"},
            {"label": "Unreached Modules", "color_key": "crimson", "style": "dashed"},
            {"label": "Most-Imported Module / Hotspot", "color_key": "amber", "style": "badge"},
        ],
        "meta": {
            "root_module": root_mod,
            "root_modules": root_mods,
            "source_only": True,
        },
    }
    svg_dark = _circuit.render_circuit_svg(payload, theme="dark")
    svg_light = _circuit.render_circuit_svg(payload, theme="light")
    return payload, svg_dark, svg_light


def _dfs_module_order(
    modules: Sequence[Dict[str, Any]],
    edges: Sequence[Tuple[str, str]],
    root_module: str,
) -> List[Dict[str, Any]]:
    """Order modules by dominator/import DFS from `root_module`, then unreached hubs."""
    by_name = {m["name"]: m for m in modules}
    dom_children: Dict[str, List[str]] = collections.defaultdict(list)
    for m in modules:
        p = m.get("dom_parent")
        if p and p in by_name and p != m["name"]:
            dom_children[p].append(m["name"])
    for p in dom_children:
        dom_children[p].sort(key=lambda nm: (-by_name[nm]["dom_subtree_size"], -by_name[nm]["fan_in"], nm))

    imp_adj: Dict[str, List[str]] = collections.defaultdict(list)
    for src, dst in edges:
        if src in by_name and dst in by_name:
            imp_adj[src].append(dst)
    for src in imp_adj:
        imp_adj[src].sort(key=lambda nm: (-by_name[nm]["dom_subtree_size"], -by_name[nm]["fan_in"], nm))

    ordered: List[Dict[str, Any]] = []
    seen: Set[str] = set()

    def _dfs(start: str) -> None:
        stack = [start]
        while stack:
            cur = stack.pop()
            if cur in seen or cur not in by_name:
                continue
            seen.add(cur)
            ordered.append(by_name[cur])
            kids = list(dom_children.get(cur, ()))
            for nxt in imp_adj.get(cur, ()):
                if nxt not in seen and nxt not in kids:
                    kids.append(nxt)
            for nxt in reversed(kids):
                if nxt not in seen:
                    stack.append(nxt)

    if root_module in by_name:
        _dfs(root_module)
    for m in sorted(modules, key=lambda x: (-x["rev_reach"], -x["fan_in"], -x["lines_wc"], x["name"])):
        if m["name"] not in seen:
            _dfs(m["name"])
    return ordered


def _build_module_matrix(
    *,
    slug: str,
    repo_url: str,
    pinned_commit: str,
    src_prefix: str,
    snapshot: Dict[str, Any],
) -> Dict[str, Any]:
    """Build compact binned module-import adjacency grid (32x32 or 64x64) + clickable samples."""
    cs = snapshot["corpus_stats"]
    modules = snapshot["modules"]
    edges = snapshot["edges"]
    decls = snapshot["decls"]
    root_mod = str(cs.get("root_module") or "Main")

    ordered = _dfs_module_order(modules, edges, root_mod)
    n_mods = len(ordered)
    grid_size = 64 if n_mods >= 128 else 32
    idx_of = {m["name"]: i for i, m in enumerate(ordered)}
    bin_of = {
        m["name"]: min(grid_size - 1, (i * grid_size) // max(1, n_mods))
        for i, m in enumerate(ordered)
    }
    by_name = {m["name"]: m for m in ordered}

    grid: List[List[int]] = [[0] * grid_size for _ in range(grid_size)]
    cell_edge_lists: Dict[Tuple[int, int], List[Tuple[int, str, str]]] = collections.defaultdict(list)
    diag_edges = 0
    for src, dst in edges:
        if src not in bin_of or dst not in bin_of:
            continue
        r = bin_of[src]
        c = bin_of[dst]
        grid[r][c] += 1
        if abs(r - c) <= 2:
            diag_edges += 1
        prio = -(by_name[dst]["fan_in"] + by_name[src]["dom_subtree_size"])
        cell_edge_lists[(r, c)].append((prio, src, dst))

    # Top non-empty cell samples (cap at 500 cells so JSON stays < 250 KB)
    ranked_cells = sorted(
        cell_edge_lists.items(),
        key=lambda kv: (-len(kv[1]), kv[0][0], kv[0][1]),
    )[:500]
    cell_samples: Dict[str, List[Dict[str, Any]]] = {}
    for (r, c), elist in ranked_cells:
        elist.sort(key=lambda t: (t[0], t[1], t[2]))
        samples_rc: List[Dict[str, Any]] = []
        for _, src, dst in elist[:3]:
            sm = by_name[src]
            dm = by_name[dst]
            samples_rc.append({
                "src": src,
                "dst": dst,
                "src_path": sm["file_path"],
                "dst_path": dm["file_path"],
                "src_url": _github_blob_url(repo_url, pinned_commit, src_prefix, sm["file_path"], 1),
                "dst_url": _github_blob_url(repo_url, pinned_commit, src_prefix, dm["file_path"], 1),
            })
        cell_samples[f"{r},{c}"] = samples_rc

    # Bin metadata
    bins_out: List[Dict[str, Any]] = []
    bin_mods: Dict[int, List[Dict[str, Any]]] = collections.defaultdict(list)
    for i, m in enumerate(ordered):
        bin_mods[bin_of[m["name"]]].append(m)
    for b in range(grid_size):
        bms = bin_mods.get(b, [])
        top_ms = sorted(bms, key=lambda x: (-x["fan_in"], -x["dom_subtree_size"], -x["lines_wc"], x["name"]))[:3]
        bins_out.append({
            "bin": b,
            "module_count": len(bms),
            "lines_wc": sum(x["lines_wc"] for x in bms),
            "label": _short_name(top_ms[0]["name"], 28) if top_ms else "",
            "top_modules": [
                {
                    "name": tm["name"],
                    "file_path": tm["file_path"],
                    "lines_wc": tm["lines_wc"],
                    "decl_count": tm["decl_count"],
                    "fan_in": tm["fan_in"],
                    "url": _github_blob_url(repo_url, pinned_commit, src_prefix, tm["file_path"], 1),
                }
                for tm in top_ms
            ],
        })

    # Contiguous depth-2 / top-level regions along DFS order
    regions: List[Dict[str, Any]] = []
    if ordered:
        cur_key = ordered[0]["namespace_l2"]
        start_i = 0
        for i, m in enumerate(ordered):
            k = m["namespace_l2"]
            if k != cur_key:
                seg = ordered[start_i:i]
                regions.append({
                    "key": cur_key,
                    "dfs_start": start_i,
                    "dfs_end": i,
                    "bin_start": bin_of[ordered[start_i]["name"]],
                    "bin_end": bin_of[ordered[i - 1]["name"]] + 1,
                    "module_count": len(seg),
                    "lines_wc": sum(x["lines_wc"] for x in seg),
                })
                cur_key = k
                start_i = i
        seg = ordered[start_i:]
        regions.append({
            "key": cur_key,
            "dfs_start": start_i,
            "dfs_end": n_mods,
            "bin_start": bin_of[ordered[start_i]["name"]],
            "bin_end": bin_of[ordered[-1]["name"]] + 1,
            "module_count": len(seg),
            "lines_wc": sum(x["lines_wc"] for x in seg),
        })
    if len(regions) > 48:
        # Coalesce smallest adjacent regions for compact legend display
        regions = sorted(regions, key=lambda r: -r["module_count"])[:48]
        regions.sort(key=lambda r: r["dfs_start"])

    # Top declarations (1-line signatures <= 160 chars ONLY; ZERO proof bodies)
    kind_prio = {"axiom": 0, "theorem": 1, "inductive": 2, "structure": 3, "class": 4, "def": 5}
    ranked_decls = sorted(
        (d for d in decls if not d["name"].startswith("_anon_")),
        key=lambda d: (
            0 if d["tags"] else 1,
            kind_prio.get(d["kind"], 6),
            -(by_name.get(d["module"], {}).get("fan_in", 0)),
            -(by_name.get(d["module"], {}).get("dom_subtree_size", 0)),
            d["name"],
        ),
    )[:40]
    top_declarations = []
    for d in ranked_decls:
        mod_obj = by_name.get(d["module"])
        top_declarations.append({
            "name": d["name"],
            "kind": d["kind"],
            "module": d["module"],
            "line": d["line"],
            "fan_in": mod_obj["fan_in"] if mod_obj else 0,
            "signature": _clip(d["sig"], MAX_SIG_LEN),
            "tags": d["tags"],
            "url": _github_blob_url(repo_url, pinned_commit, src_prefix, mod_obj["file_path"], d["line"]) if mod_obj else None,
        })

    return {
        "schema": MODULE_MATRIX_SCHEMA,
        "repo": slug,
        "root_module": root_mod,
        "n_modules": n_mods,
        "n_reachable": int(cs.get("reachable_from_main") or 0),
        "n_edges": len(edges),
        "diagonal_near_edges": diag_edges,
        "diagonal_near_pct": round(100.0 * diag_edges / max(1, len(edges)), 2),
        "grid_size": grid_size,
        "grid": grid,
        "cell_samples": cell_samples,
        "bins": bins_out,
        "regions": regions,
        "top_declarations": top_declarations,
        "order_index": {m["name"]: idx_of[m["name"]] for m in ordered[:80]},
    }


def _detect_readme_caveats(src_dir: str, slug: str) -> List[str]:
    """Extract factual repository caveats from README/NOTICE without verbatim source dumps."""
    caveats: List[str] = []
    readme_text = ""
    for base in (src_dir, os.path.dirname(os.path.abspath(src_dir))):
        if not base or not os.path.isdir(base):
            continue
        for fn in ("README.md", "NOTICE"):
            cand = os.path.join(base, fn)
            if os.path.isfile(cand) and not os.path.islink(cand):
                try:
                    with open(cand, "r", encoding="utf-8", errors="replace") as f:
                        readme_text += "\n" + f.read(16_384)
                except OSError:
                    pass
    low = readme_text.lower()
    if "arb" in low and ("certificate" in low or "interval arithmetic" in low):
        caveats.append(
            "External numerical certificate caveat (README.md): the 128-bit Arb/FLINT interval-arithmetic "
            "certificate referenced by the paper is external and not included in this repository."
        )
    if "was not rebuilt" in low or "not rebuilt when this repository was assembled" in low:
        caveats.append(
            "Build caveat (README.md): the patched Lean package was not rebuilt after the final cell-layer patch."
        )
    has_comparator_dir = os.path.isdir(os.path.join(src_dir, "ComparatorChallenges"))
    if has_comparator_dir or ("comparator" in low and "statement" in low and "sorry" in low):
        caveats.append(
            "Comparator layout: challenge/statement files (`ComparatorChallenges/` / `*Challenge*.lean`) "
            "intentionally hold `sorry` placeholders separated from proof modules."
        )
    if "no data" in low and "navier" in slug:
        pass
    return caveats


def _build_summary_md(
    *,
    slug: str,
    title: str,
    repo_url: str,
    pinned_commit: str,
    src_prefix: str,
    license_label: str,
    description: str,
    snapshot: Dict[str, Any],
    flirt_summary: Optional[Dict[str, Any]],
    src_dir: str,
    source_only: bool,
    kernel_stats: Optional[Dict[str, Any]] = None,
) -> str:
    """Build crisp, factual `data/summary.md` with pinned GitHub #L<n> links (ZERO proof bodies)."""
    cs = snapshot["corpus_stats"]
    fs = snapshot["forensic_summary"]
    modules = snapshot["modules"]
    hits = snapshot["hits"]
    by_name = {m["name"]: m for m in modules}

    root_mod = str(cs.get("root_module") or "Main")
    root_mods = list(cs.get("root_modules") or [root_mod])
    root_reach_counts = cs.get("root_reach_counts") or {}
    n_mods = int(cs.get("modules") or 0)
    reach = int(cs.get("reachable_from_main") or 0)
    loc = int(cs.get("lines_wc") or 0)
    n_edges = int(cs.get("project_import_edges") or 0)
    n_decls = int(cs.get("declarations") or 0)
    kinds = cs.get("decl_counts_by_kind") or {}
    thms = int(kinds.get("theorem", 0)) + int(kinds.get("lemma", 0))
    defs = int(kinds.get("def", 0)) + int(kinds.get("abbrev", 0)) + int(kinds.get("instance", 0)) + int(kinds.get("opaque", 0))
    inds = int(kinds.get("inductive", 0)) + int(kinds.get("structure", 0)) + int(kinds.get("class", 0))
    axioms = int(kinds.get("axiom", 0))

    tot_hits = fs.get("total_hit_counts") or {}
    mod_hits = fs.get("module_counts") or {}
    proof_sorry_hits, challenge_sorry_hits = _split_sorry_hits(hits, by_name)
    proof_sorry = len(proof_sorry_hits)
    proof_sorry_files = len({h["module"] for h in proof_sorry_hits})
    challenge_sorry = len(challenge_sorry_hits)
    challenge_sorry_files = len({h["module"] for h in challenge_sorry_hits})
    axiom_hits = int(tot_hits.get("axiom", 0))
    dk_cnt = int(tot_hits.get("decide_kernel", 0))
    nd_cnt = int(tot_hits.get("native_decide", 0))
    unsafe_cnt = int(tot_hits.get("unsafe", 0))
    impl_cnt = int(tot_hits.get("implemented_by", 0))

    clean_url = _clean_repo_url(repo_url)
    short_sha = pinned_commit[:12] if pinned_commit else "HEAD"
    if len(root_mods) >= 2:
        root_breakdown = ", ".join(
            f"{r} {int(root_reach_counts.get(r, 0)):,}" for r in root_mods
        )
        entry_line = (
            f"- **Entry modules:** {', '.join(f'`{r}`' for r in root_mods)} "
            f"(combined reach: **{reach:,} / {n_mods:,}** modules, "
            f"**{100.0 * reach / max(1, n_mods):.1f}%**; {root_breakdown})"
        )
    else:
        entry_line = (
            f"- **Entry module:** `{root_mod}` (reaches **{reach:,} / {n_mods:,}** modules, "
            f"**{100.0 * reach / max(1, n_mods):.1f}%**)"
        )

    lines: List[str] = [
        f"# {title}",
        "",
        description if description else f"Automated static structural scan of `{slug}`.",
        "",
        "## Provenance & Scope",
        "",
        f"- **Repository:** [{clean_url or slug}]({clean_url})" if clean_url else f"- **Repository:** `{slug}`",
        f"- **Pinned commit:** `{short_sha}` (`{pinned_commit}`)" if pinned_commit else "- **Pinned commit:** unpinned",
        f"- **License:** {license_label}",
        f"- **Analysis mode:** {'Source + Kernel (`kernel.db`)' if not source_only else 'Source-level import and declaration scan (no compiled kernel export)'}",
        entry_line,
        "",
        "## Scale & Composition",
        "",
        "| Metric | Value |",
        "| --- | ---: |",
        f"| Lean modules | {n_mods:,} |",
        f"| Lines of code | {loc:,} |",
        f"| Project import edges | {n_edges:,} |",
        f"| Declarations (source) | {n_decls:,} |",
        f"| Theorems / lemmas | {thms:,} |",
        f"| Defs / abbrevs / instances | {defs:,} |",
        f"| Inductives / structures / classes | {inds:,} |",
        f"| Custom `axiom` declarations | {axioms:,} |",
    ]
    if challenge_sorry > 0:
        lines.append(f"| Proof `sorry` / `admit` hits | {proof_sorry:,} ({_plural(proof_sorry_files, 'file')}) |")
        lines.append(f"| Challenge-spec `sorry` hits | {challenge_sorry:,} ({_plural(challenge_sorry_files, 'file')}) |")
    else:
        lines.append(f"| `sorry` / `admit` hits | {proof_sorry:,} ({_plural(proof_sorry_files, 'file')}) |")
    lines.append(f"| `decide +kernel` hits | {dk_cnt:,} |")
    if kernel_stats:
        lines.extend([
            f"| Kernel live / total decls | {int(kernel_stats.get('live_decls', 0)):,} / {int(kernel_stats.get('total_decls', 0)):,} |",
            f"| Kernel edges | {int(kernel_stats.get('edges', 0)):,} |",
        ])

    caveats = _detect_readme_caveats(src_dir, slug)
    if caveats:
        lines.extend(["", "## Repository Notes & Caveats", ""])
        for c in caveats:
            lines.append(f"- {c}")

    lines.extend(["", "## Axioms, Incomplete Proofs, and Kernel Directives", ""])
    if not any((proof_sorry, challenge_sorry, axiom_hits, dk_cnt, nd_cnt, unsafe_cnt, impl_cnt)):
        lines.extend([
            "- No `sorry`, custom `axiom`, `decide +kernel`, `native_decide`, `unsafe`, or `implemented_by` hits were found.",
            "",
        ])
    else:
        def _append_hit_section(label: str, sec_hits: Sequence[Dict[str, Any]], n_t: int, n_f: int) -> None:
            lines.append(f"### {label}: {_plural(n_t, 'hit')} in {_plural(n_f, 'file')}")
            lines.append("")
            for h in sec_hits[:15]:
                m_obj = by_name.get(h["module"])
                fpath = m_obj["file_path"] if m_obj else (h["module"].replace(".", "/") + ".lean")
                url = _github_blob_url(repo_url, pinned_commit, src_prefix, fpath, h["line"])
                loc_str = f"[{h['module']}:L{h['line']}]({url})" if url else f"`{h['module']}:L{h['line']}`"
                decl_str = f" — `{h['decl_name']}`" if h.get("decl_name") else ""
                lines.append(f"- {loc_str}{decl_str}")
            if len(sec_hits) > 15:
                lines.append(f"- … and {len(sec_hits) - 15:,} more")
            lines.append("")

        if challenge_sorry > 0:
            if proof_sorry_hits:
                _append_hit_section("Proof `sorry` / `admit`", proof_sorry_hits, proof_sorry, proof_sorry_files)
            _append_hit_section("Challenge-spec `sorry`", challenge_sorry_hits, challenge_sorry, challenge_sorry_files)
        elif proof_sorry_hits:
            _append_hit_section("`sorry` / `admit`", proof_sorry_hits, proof_sorry, proof_sorry_files)

        for tag, label in (
            ("axiom", "`axiom`"),
            ("decide_kernel", "`decide +kernel`"),
            ("native_decide", "`native_decide`"),
            ("unsafe", "`unsafe`"),
            ("implemented_by", "`implemented_by` / `@[extern]`"),
        ):
            t_hits = [h for h in hits if h["tag"] == tag]
            if not t_hits:
                continue
            n_t = int(tot_hits.get(tag, len(t_hits)))
            n_f = int(mod_hits.get(tag, len({h["module"] for h in t_hits})))
            _append_hit_section(label, t_hits, n_t, n_f)

    if flirt_summary:
        ms = flirt_summary.get("misfile_scoring") or {}
        bs = flirt_summary.get("boilerplate_stats") or {}
        alert_n = int(ms.get("alertable_misfiles_total", 0))
        alert_pct = float(ms.get("alertable_pct_of_corpus", 0.0))
        high_n = int(ms.get("high_tier_count", 0))
        med_n = int(ms.get("medium_tier_count", 0))
        abc = bs.get("alpha_body_clone") or {}
        abc_c = int(abc.get("clusters", 0))
        abc_r = int(abc.get("redundant_modules", 0))
        sig = bs.get("sigset_clone") or {}
        sig_c = int(sig.get("clusters", 0))
        sig_r = int(sig.get("redundant_modules", 0))
        shim_n = int((bs.get("import_shim") or {}).get("modules", 0))
        lines.extend([
            "## Duplication & Directory Alignment",
            "",
            f"- **Directory-vs-namespace outliers:** {_plural(alert_n, 'file')} ({alert_pct:.1f}%; {high_n:,} high, {med_n:,} medium)",
            f"- **Identical-body file clones:** {_plural(abc_c, 'cluster')}"
            + (f" ({_plural(abc_r, 'redundant file')})" if abc_r else ""),
            f"- **Identical-signature file clusters:** {_plural(sig_c, 'cluster')}"
            + (f" ({_plural(sig_r, 'redundant file')})" if sig_r else ""),
            f"- **Import-only shims:** {shim_n:,}",
        ])

    top_imp = sorted(modules, key=lambda x: (-x["fan_in"], -x["lines_wc"], x["name"]))[:10]
    if top_imp:
        lines.extend([
            "",
            "## Most-Imported Modules (Top 10)",
            "",
            "| Module | Direct Importers | Transitive Importers | Lines | Declarations |",
            "| --- | ---: | ---: | ---: | ---: |",
        ])
        for m in top_imp:
            url = _github_blob_url(repo_url, pinned_commit, src_prefix, m["file_path"], 1)
            m_lbl = f"[{m['name']}]({url})" if url else f"`{m['name']}`"
            lines.append(f"| {m_lbl} | {m['fan_in']:,} | {m['rev_reach']:,} | {m['lines_wc']:,} | {m['decl_count']:,} |")

    return "\n".join(lines) + "\n"


def _build_source_search_shards(
    out_project_dir: str,
    *,
    snapshot: Dict[str, Any],
    summary_title: str,
    extra_findings: Optional[Sequence[Dict[str, Any]]] = None,
    extra_dossiers: Optional[Sequence[Dict[str, Any]]] = None,
    search_limit: int = 30_000,
    circuit_by_name: Optional[Dict[str, str]] = None,
    kernel_dom_by_name: Optional[Dict[str, int]] = None,
    max_shard_bytes: int = MAX_SEARCH_SHARD_BYTES,
    max_total_bytes: int = MAX_SEARCH_TOTAL_BYTES,
) -> Dict[str, Any]:
    """Build leaf-prefix sharded `data/search/<pfx>.json` (<=150 KB/shard, zero proof bodies)."""
    modules = snapshot["modules"]
    decls = snapshot["decls"]
    by_name = {m["name"]: m for m in modules}
    cir_map = circuit_by_name or {}
    kdom = kernel_dom_by_name or {}

    # Priority pool: (is_pinned, sort_score, bucket, entry_dict)
    raw_shards: Dict[str, List[Tuple[bool, Tuple[int, int, str], Dict[str, Any]]]] = collections.defaultdict(list)
    seen_keys: Set[Tuple[str, str]] = set()

    # 1. Summary finding entry + any separately authored findings/dossiers
    sum_entry = {
        "name": summary_title,
        "kind": "finding",
        "mod": "data/summary.md",
        "line": 1,
        "fan_in": 0,
        "dom": 0,
        "live": 1,
        "bp_id": "summary",
    }
    raw_shards[_search_prefix_bucket("summary")].append((True, (-10**9, 0, "summary"), sum_entry))

    for f_doc in (extra_findings or ()):
        fslug = str(f_doc.get("slug") or "")
        if not fslug or fslug == "summary":
            continue
        fentry = {
            "name": str(f_doc.get("title") or fslug),
            "kind": "finding",
            "mod": str(f_doc.get("path") or ""),
            "line": 1,
            "fan_in": 0,
            "dom": 0,
            "live": 1,
            "bp_id": fslug,
        }
        raw_shards[_search_prefix_bucket(fslug)].append((True, (-10**9 + 1, 0, fslug), fentry))

    for d_doc in (extra_dossiers or ()):
        dslug = str(d_doc.get("slug") or "")
        if not dslug:
            continue
        dentry = {
            "name": str(d_doc.get("title") or dslug),
            "kind": "dossier",
            "mod": str(d_doc.get("path") or ""),
            "line": 1,
            "fan_in": 0,
            "dom": 0,
            "live": 1,
            "bp_id": dslug,
        }
        raw_shards[_search_prefix_bucket(dslug)].append((True, (-10**9 + 2, 0, dslug), dentry))

    # 2. All modules (pinned up to cap)
    for m in sorted(modules, key=lambda x: (-x["dom_subtree_size"], -x["fan_in"], x["name"])):
        key = ("module", m["name"])
        if key in seen_keys:
            continue
        seen_keys.add(key)
        short = m["name"].rsplit(".", 1)[-1]
        bucket = _search_prefix_bucket(short)
        dom_v = m["dom_subtree_size"] if m["dom_subtree_size"] > 0 else m["rev_reach"]
        entry = {
            "name": m["name"],
            "kind": "module",
            "mod": m["name"],
            "line": 1,
            "fan_in": m["fan_in"],
            "dom": dom_v,
            "live": 1 if m["dom_subtree_size"] > 0 else 0,
        }
        raw_shards[bucket].append((True, (0, -dom_v, m["name"]), entry))

    # 3. Named declarations
    kind_prio = {"axiom": 0, "theorem": 1, "lemma": 1, "inductive": 2, "structure": 2, "class": 2, "def": 3}
    ranked_decls = sorted(
        (d for d in decls if not d["name"].startswith("_anon_")),
        key=lambda d: (
            0 if (d["tags"] or d["name"] in cir_map) else 1,
            kind_prio.get(d["kind"], 4),
            -(kdom.get(d["name"], 0)),
            -(by_name.get(d["module"], {}).get("fan_in", 0)),
            -(by_name.get(d["module"], {}).get("dom_subtree_size", 0)),
            d["name"],
        ),
    )
    if search_limit > 0:
        ranked_decls = ranked_decls[:search_limit]

    for d in ranked_decls:
        key = (d["kind"], d["name"])
        if key in seen_keys:
            continue
        seen_keys.add(key)
        m_obj = by_name.get(d["module"])
        fan_in = m_obj["fan_in"] if m_obj else 0
        dom_v = kdom.get(d["name"])
        if dom_v is None:
            dom_v = m_obj["dom_subtree_size"] if m_obj else 0
        live_v = 1 if (m_obj and m_obj["dom_subtree_size"] > 0) or d["name"] in kdom else 0
        short = d["name"].rsplit(".", 1)[-1]
        bucket = _search_prefix_bucket(short)
        is_pin = bool(d["tags"] or d["name"] in cir_map or d["kind"] == "axiom")
        entry: Dict[str, Any] = {
            "name": d["name"],
            "kind": d["kind"],
            "mod": d["module"],
            "line": d["line"],
            "fan_in": fan_in,
            "dom": dom_v,
            "live": live_v,
        }
        if d["name"] in cir_map:
            entry["circuit_path"] = cir_map[d["name"]]
        raw_shards[bucket].append((is_pin, (1, -fan_in, d["name"]), entry))

    def _pack_shard(entries: List[Dict[str, Any]]) -> Any:
        if len(entries) < 8:
            return entries
        pref_counts: collections.Counter[str] = collections.Counter()
        for e in entries:
            ms = str(e.get("mod") or "")
            if "." in ms and not ms.startswith("data/"):
                parts = ms.split(".")
                p = ".".join(parts[:3]) if len(parts) >= 3 else parts[0]
                pref_counts[p] += 1
        common = sorted(p for p, c in pref_counts.items() if c >= 2)
        if not common:
            return entries
        pref_idx = {p: i for i, p in enumerate(common)}
        packed: List[Dict[str, Any]] = []
        for e in entries:
            ms = str(e.get("mod") or "")
            new_mod: Any = ms
            if "." in ms and not ms.startswith("data/"):
                parts = ms.split(".")
                p = ".".join(parts[:3]) if len(parts) >= 3 else parts[0]
                if p in pref_idx:
                    rest = ".".join(parts[3:]) if len(parts) >= 3 else ".".join(parts[1:])
                    new_mod = f"{pref_idx[p]}:{rest}" if rest else pref_idx[p]
            ne = dict(e)
            ne["mod"] = new_mod
            packed.append(ne)
        obj = {"mod_prefixes": common, "entries": packed}
        raw_sz = len(json.dumps(entries, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))
        pak_sz = len(json.dumps(obj, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))
        return obj if pak_sz + 64 < raw_sz else entries

    shard_keys = sorted(raw_shards.keys())
    final_shards: List[str] = []
    actual_total_bytes = 0
    actual_total_entries = 0

    # Sort each shard deterministically and enforce per-shard and total byte budgets
    shard_items: List[Tuple[str, List[Dict[str, Any]]]] = []
    for sk in shard_keys:
        items_sk = sorted(raw_shards[sk], key=lambda x: (0 if x[0] else 1, x[1]))
        shard_items.append((sk, [x[2] for x in items_sk]))

    for sk, rows_sk in shard_items:
        if not rows_sk:
            continue
        # Trim tail entries if shard exceeds max_shard_bytes or global budget
        while rows_sk:
            packed_obj = _pack_shard(rows_sk)
            raw_b = json.dumps(packed_obj, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
            if len(raw_b) <= max_shard_bytes and (actual_total_bytes + len(raw_b) <= max_total_bytes or len(rows_sk) == 1):
                break
            if len(rows_sk) == 1:
                break
            # Drop last 20% or 1 item for fast convergence
            drop_n = max(1, len(rows_sk) // 5) if len(raw_b) > max_shard_bytes * 1.4 else 1
            rows_sk = rows_sk[:-drop_n]

        if actual_total_bytes >= max_total_bytes:
            break
        packed_obj = _pack_shard(rows_sk)
        nbytes = _safe_write_json(os.path.join(out_project_dir, "data", "search", f"{sk}.json"), packed_obj)
        actual_total_bytes += nbytes
        actual_total_entries += len(rows_sk)
        final_shards.append(sk)

    return {
        "shard_prefix_len": 2,
        "shard_template": "data/search/{prefix}.json",
        "bucket_mode": "leaf_prefix2",
        "bucket_key": "leaf",
        "total_entries": actual_total_entries,
        "total_bytes": actual_total_bytes,
        "shards": final_shards,
    }


def _verify_export_safety(root_dir: str) -> Dict[str, Any]:
    total_bytes = 0
    file_count = 0
    max_file_bytes = 0
    max_file_rel = ""
    for root, dirs, files in os.walk(root_dir, followlinks=False):
        dirs.sort()
        files.sort()
        for fn in files:
            full = os.path.join(root, fn)
            if os.path.islink(full):
                raise ValueError(f"Unexpected symlink inside export dir: {full}")
            rel = os.path.relpath(full, root_dir).replace(os.sep, "/")
            if fn.endswith(".lean"):
                raise ValueError(f"Refusing exported .lean file inside export dir: {rel}")
            sz = os.path.getsize(full)
            if sz > MAX_EXPORT_FILE_BYTES:
                raise ValueError(f"File exceeds 25 MB limit ({sz:,} bytes): {rel}")
            total_bytes += sz
            file_count += 1
            if sz > max_file_bytes:
                max_file_bytes = sz
                max_file_rel = rel
            if fn.endswith((".json", ".md", ".html", ".js", ".css", ".svg")):
                with open(full, "r", encoding="utf-8", errors="replace") as f:
                    txt = f.read()
                m = _FORBIDDEN_HOST_PATH_RE.search(txt)
                if m:
                    raise ValueError(f"Workstation path {m.group(0)!r} leaked into exported file: {rel}")
    return {
        "total_bytes": total_bytes,
        "file_count": file_count,
        "max_file_bytes": max_file_bytes,
        "max_file_rel": max_file_rel,
    }


def _maybe_build_kernel_assets(
    *,
    src_dir: str,
    out_project_dir: str,
    kernel_db: Optional[str],
    ndjson_path: Optional[str],
    cfg: Optional[_config.LeanreConfig],
    tmp_dir: str,
) -> Optional[Dict[str, Any]]:
    """If kernel.db or NDJSON exists, build kernel circuits & extract kernel stats."""
    import kernel as _kernel

    eff_kdb = kernel_db
    eff_ndjson = ndjson_path
    if eff_kdb is None and eff_ndjson is None and cfg is not None and cfg.export_path:
        base_dir = os.path.dirname(os.path.abspath(cfg.source_path)) if cfg.source_path else os.path.abspath(src_dir)
        cand_nd = os.path.join(base_dir, cfg.export_path)
        if os.path.isfile(cand_nd) and not os.path.islink(cand_nd):
            eff_ndjson = cand_nd

    if eff_kdb is None and eff_ndjson is not None:
        if not os.path.isfile(_kernel.default_binary_path()):
            return None
        roots = cfg.kernel_root_specs() if (cfg and cfg.kernel_root_specs()) else ["Main:ROOT"]
        kout = os.path.join(tmp_dir, "kernel_out")
        _kernel.run_pipeline(
            input_path=eff_ndjson,
            out_dir=kout,
            src_dir=src_dir,
            roots=roots,
            threads=2,
            workers=1,
            auto_build=False,
            verbose=False,
        )
        eff_kdb = os.path.join(kout, "kernel.db")

    if not eff_kdb or not os.path.isfile(eff_kdb):
        return None

    kconn = _open_ro(eff_kdb)
    try:
        total_decls = int(kconn.execute("SELECT COUNT(*) FROM decls").fetchone()[0])
        live_decls = int(kconn.execute("SELECT COUNT(*) FROM decls WHERE live_mask != 0").fetchone()[0])
        dead_decls = max(0, total_decls - live_decls)
        total_edges = int(kconn.execute("SELECT COUNT(*) FROM edges").fetchone()[0])

        kdom_by_name: Dict[str, int] = {}
        has_dom = kconn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='dom'").fetchone() is not None
        if has_dom:
            for nm, sub in kconn.execute(
                "SELECT d.name, dm.subtree_size FROM dom dm JOIN decls d ON d.id = dm.decl_id WHERE dm.tree_id = 0"
            ):
                kdom_by_name[str(nm)] = int(sub)

        ind_rows = [
            str(r[0]) for r in kconn.execute(
                "SELECT name FROM decls WHERE kind = 'inductive' AND live_mask != 0 ORDER BY fan_in DESC, id ASC LIMIT 24"
            )
        ]
        thm_rows = [
            (str(r[0]), int(kdom_by_name.get(str(r[0]), 0)))
            for r in kconn.execute(
                "SELECT name FROM decls WHERE kind IN ('thm', 'def') AND live_mask != 0 ORDER BY fan_in DESC, id ASC LIMIT 36"
            )
            if not _circuit._is_aux_name(str(r[0]))
        ]
    finally:
        kconn.close()

    # Macro kernel circuit + bundles + theorems (when small/clean)
    macro_raw = _circuit.build_macro_circuit(
        kernel_db_path=eff_kdb,
        src_root=src_dir,
    )
    macro_clean = _sanitize_json_value(macro_raw)
    if isinstance(macro_clean.get("pins"), dict):
        macro_clean["pins"]["kernel_db"] = os.path.basename(str(macro_clean["pins"].get("kernel_db") or "kernel.db"))
        macro_clean["pins"]["src_root"] = os.path.basename(os.path.abspath(src_dir))
        macro_clean["pins"]["elapsed_seconds"] = 0
    macro_svg_d = _circuit.render_circuit_svg(macro_clean, theme="dark")
    macro_svg_l = _circuit.render_circuit_svg(macro_clean, theme="light")

    bundles_out: List[Dict[str, Any]] = []
    theorems_out: List[Dict[str, Any]] = []
    circuit_by_name: Dict[str, str] = {}
    used_slugs: Set[str] = set()

    for fqn in ind_rows:
        try:
            raw_b = _circuit.build_bundle_circuit(kernel_db_path=eff_kdb, target=fqn, src_root=src_dir, max_nodes=16, exact_case=True)
        except Exception:
            continue
        clean_b = _sanitize_json_value(raw_b)
        if isinstance(clean_b.get("pins"), dict):
            clean_b["pins"]["kernel_db"] = "kernel.db"
            clean_b["pins"]["src_root"] = os.path.basename(os.path.abspath(src_dir))
        cslug = _slugify_id(fqn.replace(".", "_"))
        while cslug in used_slugs:
            cslug += "_" + hashlib.sha1(fqn.encode("utf-8")).hexdigest()[:4]
        used_slugs.add(cslug)
        rel_b = f"data/circuits/bundle/{cslug}.json"
        _safe_write_json(
            os.path.join(out_project_dir, rel_b),
            {
                "schema": clean_b.get("schema", _circuit.SCHEMA_VERSION),
                "mode": "bundle",
                "name": fqn,
                "payload": clean_b,
                "svg_dark": _circuit.render_circuit_svg(clean_b, theme="dark"),
                "svg_light": _circuit.render_circuit_svg(clean_b, theme="light"),
            },
        )
        st = clean_b.get("stats") or {}
        bundles_out.append({
            "name": fqn,
            "short": _short_name(fqn),
            "badge": f"{int(st.get('total_fields') or 0)} fields",
            "path": rel_b,
            "producers": int(st.get("producers_total") or 0),
            "consumers": int(st.get("consumers_total") or 0),
            "dropped_consumers": int(st.get("consumers_dropped_input") or 0),
            "fields": int(st.get("total_fields") or 0),
            "cond_fields": int(st.get("conditional_prop_fields") or 0),
            "true_fields": int(st.get("literal_true_fields") or 0),
        })
        circuit_by_name[fqn] = rel_b

    for fqn, dom_sz in thm_rows:
        try:
            raw_t = _circuit.build_theorem_circuit(kernel_db_path=eff_kdb, decl=fqn, src_root=src_dir, max_nodes=28, exact_case=True)
        except Exception:
            continue
        clean_t = _sanitize_json_value(raw_t)
        if isinstance(clean_t.get("pins"), dict):
            clean_t["pins"]["kernel_db"] = "kernel.db"
            clean_t["pins"]["src_root"] = os.path.basename(os.path.abspath(src_dir))
        cslug = _slugify_id(fqn.replace(".", "_"))
        while cslug in used_slugs:
            cslug += "_" + hashlib.sha1(fqn.encode("utf-8")).hexdigest()[:4]
        used_slugs.add(cslug)
        rel_t = f"data/circuits/theorem/{cslug}.json"
        _safe_write_json(
            os.path.join(out_project_dir, rel_t),
            {
                "schema": clean_t.get("schema", _circuit.SCHEMA_VERSION),
                "mode": "theorem",
                "name": fqn,
                "payload": clean_t,
                "svg_dark": _circuit.render_circuit_svg(clean_t, theme="dark"),
                "svg_light": _circuit.render_circuit_svg(clean_t, theme="light"),
            },
        )
        st = clean_t.get("stats") or {}
        theorems_out.append({
            "name": fqn,
            "short": _short_name(fqn),
            "badge": f"dom {dom_sz:,}" if dom_sz else f"{int(st.get('steps_count') or 0)} steps",
            "path": rel_t,
            "dom": dom_sz,
            "steps": int(st.get("steps_count") or 0),
            "binders_used": int(st.get("binders_used") or 0),
            "binders_dropped": int(st.get("binders_dropped") or 0),
            "kind": str(st.get("decl_kind") or "thm"),
        })
        circuit_by_name.setdefault(fqn, rel_t)

    return {
        "total_decls": total_decls,
        "live_decls": live_decls,
        "dead_decls": dead_decls,
        "edges": total_edges,
        "kdom_by_name": kdom_by_name,
        "macro_payload": macro_clean,
        "macro_svg_dark": macro_svg_d,
        "macro_svg_light": macro_svg_l,
        "bundles": bundles_out,
        "theorems": theorems_out,
        "circuit_by_name": circuit_by_name,
    }


def export_source_project(
    src_dir: str,
    out_dir: str,
    *,
    slug: str,
    title: str,
    repo_url: str,
    pinned_commit: str,
    src_prefix: str = "",
    description: str = "",
    badge: str = "",
    license_label: str = "",
    auto_root: bool = True,
    root_module: Optional[str] = None,
    kernel_db: Optional[str] = None,
    ndjson_path: Optional[str] = None,
    category: Optional[str] = None,
    tagline: Optional[str] = None,
    notes_dir: Optional[str] = None,
    extra_dossiers: Optional[Sequence[str]] = None,
    run_flirt: bool = True,
    run_embedding: bool = True,
    workers: Optional[int] = None,
    search_limit: int = 30_000,
    demo_mode: Optional[bool] = None,
) -> Dict[str, Any]:
    """Scan a Lean 4 repository and export `<out_dir>/p/<slug>/` in `leanre.site_manifest/1` shape."""
    import export_site as _export_site
    import stylometry as _stylometry

    if not slug or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", slug):
        raise ValueError(f"Invalid project slug: {slug!r}")
    if os.path.islink(out_dir):
        raise ValueError(f"Refusing symlinked out_dir: {out_dir}")
    if notes_dir and os.path.islink(notes_dir):
        raise ValueError(f"Refusing symlinked notes_dir: {notes_dir}")
    abs_src = os.path.abspath(src_dir)
    if not os.path.isdir(abs_src):
        raise FileNotFoundError(f"Missing src_dir: {src_dir}")

    os.makedirs(out_dir, exist_ok=True)
    _safe_write_bytes(os.path.join(out_dir, ".nojekyll"), b"")

    proj_dir = os.path.join(out_dir, "p", slug)
    if os.path.islink(proj_dir):
        raise ValueError(f"Refusing symlinked project output dir: {proj_dir}")
    os.makedirs(proj_dir, exist_ok=True)

    local_cfg_path = _config.find_local_config(abs_src)
    cfg = _config.load_config(str(local_cfg_path)) if local_cfg_path is not None else None

    eff_repo_url = _clean_repo_url(repo_url) or (cfg.repo_url.rstrip("/") if cfg and cfg.repo_url else "")
    eff_commit = str(pinned_commit or "").strip() or (cfg.pinned_commit if cfg and cfg.pinned_commit else "")
    if not eff_repo_url or not eff_commit:
        git_url, git_sha = _git_meta(abs_src)
        eff_repo_url = eff_repo_url or git_url
        eff_commit = eff_commit or git_sha

    eff_prefix = _normalize_src_prefix(src_prefix)
    eff_license = _infer_license(abs_src, license_label)
    eff_category = category or _infer_category(slug, badge, description)
    eff_demo = bool(demo_mode) if demo_mode is not None else (eff_category == "demo" or slug == "tiny-demo")
    eff_tagline = tagline or description or f"Lean 4 formalization ({eff_category})"

    embedding_rel: Optional[str] = None
    stylo_row: Optional[Dict[str, Any]] = None
    with tempfile.TemporaryDirectory(prefix=f"leanre_gal_{slug}_") as td:
        scan_db = os.path.join(td, "leanre.db")
        _run_scanner_smart(
            abs_src,
            scan_db,
            auto_root=auto_root,
            root_module=root_module,
            workers=workers,
            cfg=cfg,
        )
        snapshot = _query_scanner_snapshot(scan_db)

        flirt_summary: Optional[Dict[str, Any]] = None
        t1_db: Optional[str] = None
        if run_flirt:
            t1_db = os.path.join(td, "tier1.db")
            flirt_summary = _run_flirt_tier1(
                abs_src,
                t1_db,
                threads=workers or min(8, os.cpu_count() or 4),
                cfg=cfg,
            )

        kernel_res = _maybe_build_kernel_assets(
            src_dir=abs_src,
            out_project_dir=proj_dir,
            kernel_db=kernel_db,
            ndjson_path=ndjson_path,
            cfg=cfg,
            tmp_dir=td,
        )

        # Auto-generate source-level 2D embedding map (`data/embedding_2d.json`)
        cs_tmp = snapshot["corpus_stats"]
        root_mods_tmp = list(cs_tmp.get("root_modules") or [str(cs_tmp.get("root_module") or "Main")])
        if run_embedding and len(snapshot["modules"]) >= 4:
            try:
                import embedding as _embedding
                build_fn = getattr(_embedding, "build_source_embedding", None)
                if callable(build_fn):
                    emb_out = os.path.join(proj_dir, "data", "embedding_2d.json")
                    os.makedirs(os.path.dirname(emb_out), exist_ok=True)
                    emb_doc = build_fn(
                        scanner_db=scan_db,
                        src_dir=abs_src,
                        flirt_db=t1_db if (t1_db and os.path.isfile(t1_db)) else None,
                        out_path=emb_out,
                        roots=root_mods_tmp,
                    )
                    if isinstance(emb_doc, dict):
                        _safe_write_json(emb_out, _sanitize_json_value(emb_doc))
                    if os.path.isfile(emb_out):
                        embedding_rel = "data/embedding_2d.json"
            except ValueError:
                embedding_rel = None

        stylo_row = _stylometry.compute_project_stylometry(
            src_dir=abs_src,
            scan_db=scan_db,
            flirt_summary=flirt_summary,
            snapshot=snapshot,
            slug=slug,
            title=title,
            path=f"p/{slug}",
            license_label=eff_license,
            category=eff_category,
            has_kernel_export=(kernel_res is not None),
            has_embedding_2d=bool(embedding_rel),
            workers=workers,
        )

    source_only = kernel_res is None
    cs = snapshot["corpus_stats"]
    fs = snapshot["forensic_summary"]
    modules = snapshot["modules"]
    by_mod = {m["name"]: m for m in modules}
    root_mod = str(cs.get("root_module") or "Main")
    root_mods = list(cs.get("root_modules") or [root_mod])
    reach_cnt = int(cs.get("reachable_from_main") or 0)
    total_files = int(cs.get("modules") or 0)
    total_lines = int(cs.get("lines_wc") or 0)
    total_edges = int(cs.get("project_import_edges") or 0)
    total_decls = int(cs.get("declarations") or 0)
    kinds = cs.get("decl_counts_by_kind") or {}
    thms = int(kinds.get("theorem", 0)) + int(kinds.get("lemma", 0))
    defs = (
        int(kinds.get("def", 0))
        + int(kinds.get("abbrev", 0))
        + int(kinds.get("instance", 0))
        + int(kinds.get("opaque", 0))
    )
    inds = int(kinds.get("inductive", 0)) + int(kinds.get("structure", 0)) + int(kinds.get("class", 0))
    axioms = int(kinds.get("axiom", 0))

    tot_hits = fs.get("total_hit_counts") or {}
    mod_hits = fs.get("module_counts") or {}
    sorry_cnt = int(tot_hits.get("sorry", 0))
    sorry_files = int(mod_hits.get("sorry", 0))
    proof_sorry_hits, challenge_sorry_hits = _split_sorry_hits(snapshot["hits"], by_mod)
    proof_sorry = len(proof_sorry_hits)
    proof_sorry_files = len({h["module"] for h in proof_sorry_hits})
    challenge_sorry = len(challenge_sorry_hits)
    challenge_sorry_files = len({h["module"] for h in challenge_sorry_hits})
    dk_cnt = int(tot_hits.get("decide_kernel", 0))
    flirt_misfiles = int((flirt_summary or {}).get("misfile_scoring", {}).get("alertable_misfiles_total", 0) or 0)

    overview_pillars = _build_source_overview_pillars(modules, root_mod, reach_cnt, root_modules=root_mods)
    top_modules = [
        {
            "module": m["name"],
            "file_path": m["file_path"],
            "fan_in": m["fan_in"],
            "fan_out": m["fan_out"],
            "rev_reach": m["rev_reach"],
            "lines": m["lines_wc"],
            "lines_wc": m["lines_wc"],
            "decl_count": m["decl_count"],
            "dom_subtree_size": m["dom_subtree_size"],
            "url": _github_blob_url(eff_repo_url, eff_commit, eff_prefix, m["file_path"], 1),
        }
        for m in sorted(modules, key=lambda x: (-x["fan_in"], -x["lines_wc"], x["name"]))[:25]
    ]

    # 1. Macro SVG diagram (`data/circuits/macro.json`)
    if kernel_res is not None:
        macro_payload = kernel_res["macro_payload"]
        svg_dark = kernel_res["macro_svg_dark"]
        svg_light = kernel_res["macro_svg_light"]
    else:
        macro_payload, svg_dark, svg_light = _build_source_macro_circuit(
            slug=slug,
            title=title,
            snapshot=snapshot,
            flirt_summary=flirt_summary,
        )
    macro_rel = "data/circuits/macro.json"
    _safe_write_json(
        os.path.join(proj_dir, macro_rel),
        {
            "schema": macro_payload.get("schema", _circuit.SCHEMA_VERSION),
            "mode": "macro",
            "name": None,
            "payload": _sanitize_json_value(macro_payload),
            "svg_dark": svg_dark,
            "svg_light": svg_light,
        },
    )

    # 2. Module matrix (`data/module_matrix.json`)
    matrix_obj = _build_module_matrix(
        slug=slug,
        repo_url=eff_repo_url,
        pinned_commit=eff_commit,
        src_prefix=eff_prefix,
        snapshot=snapshot,
    )
    matrix_rel = "data/module_matrix.json"
    _safe_write_json(os.path.join(proj_dir, matrix_rel), _sanitize_json_value(matrix_obj))

    # 3. Summary markdown (`data/summary.md`)
    summary_md = _build_summary_md(
        slug=slug,
        title=title,
        repo_url=eff_repo_url,
        pinned_commit=eff_commit,
        src_prefix=eff_prefix,
        license_label=eff_license,
        description=description or eff_tagline,
        snapshot=snapshot,
        flirt_summary=flirt_summary,
        src_dir=abs_src,
        source_only=source_only,
        kernel_stats=kernel_res,
    )
    if _FORBIDDEN_HOST_PATH_RE.search(summary_md):
        summary_md = _sanitize_text_paths(summary_md)
    summary_rel = "data/summary.md"
    summary_bytes = _safe_write_text(os.path.join(proj_dir, summary_rel), summary_md)

    # 4. Compact FLIRT summary asset (`data/flirt_tier1.json`)
    flirt_rel: Optional[str] = None
    if flirt_summary is not None:
        flirt_clean = {
            "schema": flirt_summary.get("schema"),
            "file_count": flirt_summary.get("file_count"),
            "total_lines_wc": flirt_summary.get("total_lines_wc"),
            "total_decls_lean_scoped": flirt_summary.get("total_decls_lean_scoped"),
            "mathlib_import_stats": flirt_summary.get("mathlib_import_stats"),
            "misfile_scoring": {
                k: v for k, v in (flirt_summary.get("misfile_scoring") or {}).items()
                if k != "kernel_precision_calibration"
            },
            "boilerplate_stats": flirt_summary.get("boilerplate_stats"),
            "top_misfiles": (flirt_summary.get("top_misfiles") or [])[:40],
        }
        flirt_rel = "data/flirt_tier1.json"
        _safe_write_json(os.path.join(proj_dir, flirt_rel), _sanitize_json_value(flirt_clean))

    # 5. Optional separately authored notes layer (`notes/<slug>/` + `extra_dossiers`)
    notes_res = _export_site.collect_notes_layer(
        notes_dir,
        proj_dir,
        slug=slug,
        extra_dossiers=extra_dossiers,
        existing_finding_slugs={"summary"},
        existing_dossier_slugs=set(),
    )

    # 6. Sharded search (`data/search/<pfx>.json`)
    search_meta = _build_source_search_shards(
        proj_dir,
        snapshot=snapshot,
        summary_title=f"{title} — Summary",
        extra_findings=notes_res["findings"],
        extra_dossiers=notes_res["dossiers"],
        search_limit=search_limit,
        circuit_by_name=kernel_res["circuit_by_name"] if kernel_res else None,
        kernel_dom_by_name=kernel_res["kdom_by_name"] if kernel_res else None,
    )

    sorry_phrase = (
        f"{proof_sorry:,} proof sorry (+{challenge_sorry:,} challenge)"
        if challenge_sorry > 0
        else f"{proof_sorry:,} sorry"
    )
    findings_list = [
        {
            "slug": "summary",
            "title": f"{title} — Audit Summary",
            "path": summary_rel,
            "bytes": summary_bytes,
            "provenance": "tool_generated",
            "summary": _clip(
                f"{total_files:,} files, {total_lines:,} lines, {total_decls:,} decls, "
                f"{sorry_phrase}, {axioms:,} axioms, {dk_cnt:,} decide+kernel.",
                220,
            ),
        }
    ]
    findings_list.extend(notes_res["findings"])
    dossiers_list = list(notes_res["dossiers"])

    bundles_list = kernel_res["bundles"] if kernel_res else []
    theorems_list = kernel_res["theorems"] if kernel_res else []
    live_decls_val = kernel_res["live_decls"] if kernel_res else sum(
        m["decl_count"] for m in modules if m["dom_subtree_size"] > 0
    )
    dead_decls_val = kernel_res["dead_decls"] if kernel_res else max(0, total_decls - live_decls_val)

    tool_generated_files: List[str] = ["manifest.json", summary_rel, macro_rel, matrix_rel]
    if flirt_rel:
        tool_generated_files.append(flirt_rel)
    if embedding_rel:
        tool_generated_files.append(embedding_rel)
    if search_meta["shards"]:
        tool_generated_files.append("data/search/*.json")

    notes_enabled = bool(
        notes_res["loaded_findings"] or notes_res["loaded_dossiers"] or notes_res["loaded_annotations"]
    )
    provenance_obj: Dict[str, Any] = {
        "tool_generated": tool_generated_files,
        "notes_layer": {
            "enabled": notes_enabled,
            "source_dir": notes_res["source_dir"] if notes_enabled else None,
            "findings_count": notes_res["loaded_findings"],
            "dossiers_count": notes_res["loaded_dossiers"],
            "annotations_count": notes_res["loaded_annotations"],
            "note": _export_site.NOTES_LAYER_NOTE,
        },
    }

    assets_obj: Dict[str, Any] = {
        "summary": summary_rel,
        "module_matrix": matrix_rel,
        "flirt_tier1": flirt_rel,
        "embedding_2d": embedding_rel,
    }
    if notes_res["annotations"]:
        assets_obj["annotations"] = notes_res["annotations"]

    generated_at = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    manifest: Dict[str, Any] = {
        "schema": SITE_MANIFEST_SCHEMA,
        "slug": slug,
        "title": title,
        "repo_name": slug,
        "repo_url": eff_repo_url or None,
        "pinned_commit": eff_commit or None,
        "src_prefix": eff_prefix,
        "registry": "../../projects.json",
        "generated_at": generated_at,
        "demo_mode": eff_demo,
        "source_only": source_only,
        "description": description or eff_tagline,
        "tagline": eff_tagline,
        "badge": badge or ("Kernel + Source" if not source_only else "Source Scan"),
        "license": eff_license,
        "category": eff_category,
        "provenance": provenance_obj,
        "stats": {
            "total_files": total_files,
            "total_lines": total_lines,
            "total_edges": total_edges,
            "edges": kernel_res["edges"] if kernel_res else total_edges,
            "total_decls": total_decls,
            "live_decls": live_decls_val,
            "dead_decls": dead_decls_val,
            "thms": thms,
            "defs": defs,
            "inds": inds,
            "axioms": axioms,
            "sorry_count": sorry_cnt,
            "sorry_files": sorry_files,
            "proof_sorry": proof_sorry,
            "proof_sorry_files": proof_sorry_files,
            "challenge_sorry": challenge_sorry,
            "challenge_sorry_files": challenge_sorry_files,
            "decide_kernel_count": dk_cnt,
            "native_decide_count": int(tot_hits.get("native_decide", 0)),
            "unsafe_count": int(tot_hits.get("unsafe", 0)),
            "implemented_by_count": int(tot_hits.get("implemented_by", 0)),
            "root_module": root_mod,
            "reach_count": reach_cnt,
            "flirt_misfiles": flirt_misfiles,
            "kernel_total_decls": kernel_res["total_decls"] if kernel_res else 0,
            "kernel_live_decls": kernel_res["live_decls"] if kernel_res else 0,
            "blueprints_count": 0,
            "dossiers_count": len(dossiers_list),
            "findings_count": len(findings_list),
            "circuits_bundle_count": len(bundles_list),
            "circuits_theorem_count": len(theorems_list),
            "search_entries": search_meta["total_entries"],
            "search_shards": len(search_meta["shards"]),
        },
        "overview_pillars": overview_pillars,
        "top_modules": top_modules,
        "findings": findings_list,
        "dossiers": dossiers_list,
        "research": [],
        "blueprints": [],
        "circuits": {
            "macro": macro_rel,
            "bundles": bundles_list,
            "theorems": theorems_list,
        },
        "assets": assets_obj,
        "search": {
            "shard_prefix_len": search_meta["shard_prefix_len"],
            "shard_template": search_meta["shard_template"],
            "bucket_mode": search_meta["bucket_mode"],
            "bucket_key": search_meta["bucket_key"],
            "total_entries": search_meta["total_entries"],
            "shards": search_meta["shards"],
        },
    }
    if stylo_row is not None:
        manifest["stylometry"] = stylo_row
    manifest = _sanitize_json_value(manifest)
    manifest_bytes = _safe_write_json(os.path.join(proj_dir, "manifest.json"), manifest)
    safety = _verify_export_safety(proj_dir)

    return {
        "schema": SITE_MANIFEST_SCHEMA,
        "slug": slug,
        "title": title,
        "source_only": source_only,
        "has_embedding_2d": bool(embedding_rel),
        "notes_enabled": notes_enabled,
        "manifest_bytes": manifest_bytes,
        "total_bytes": safety["total_bytes"],
        "file_count": safety["file_count"],
        "max_file_bytes": safety["max_file_bytes"],
        "max_file_rel": safety["max_file_rel"],
        "search_bytes": search_meta["total_bytes"],
        "stats": manifest["stats"],
    }


def default_rh_root_entry() -> Dict[str, Any]:
    """Canonical `riemann-hypothesis` root entry for `projects.json`."""
    return {
        "slug": "riemann-hypothesis",
        "title": "Riemann Hypothesis (Alpöge–Claude)",
        "path": ".",
        "manifest_path": "manifest.json",
        "files": 175187,
        "lines": 17374215,
        "edges": 753261,
        "decls": 1468418,
        "thms": 818755,
        "defs": 242670,
        "inds": 0,
        "axioms": 0,
        "sorry": 0,
        "sorry_files": 0,
        "proof_sorry": 0,
        "proof_sorry_files": 0,
        "challenge_sorry": 0,
        "challenge_sorry_files": 0,
        "decide_kernel": 14,
        "root_module": "allChi",
        "reach_count": 175187,
        "flirt_misfiles": 0,
        "has_kernel_export": True,
        "has_embedding_2d": True,
        "notes_enabled": True,
        "source_only": False,
        "category": "kernel",
        "license": "None (no license)",
        "badge": "Kernel + Source",
        "repo_url": "https://github.com/leanprover-community/riemann-hypothesis",
        "pinned_commit": "40e56bab026552e089d7afcfeff08d2defb9c005",
        "src_prefix": "src/",
        "tagline": (
            "Kernel declaration graph and source analysis of Levent Alpöge and Claude's "
            "17.4M-line RH & Dirichlet GRH archive."
        ),
    }


def _entry_from_manifest(
    man: Dict[str, Any],
    *,
    slug: str,
    rel_path: str,
    manifest_rel: str,
) -> Dict[str, Any]:
    st = man.get("stats") or {}
    source_only = bool(man.get("source_only", not bool(st.get("kernel_total_decls"))))
    has_kernel = not source_only
    cat = str(man.get("category") or (
        "kernel" if (has_kernel and not man.get("demo_mode") and slug == "riemann-hypothesis")
        else _infer_category(slug, str(man.get("badge") or ""), str(man.get("description") or ""))
    ))
    sorry_total = int(st.get("sorry_count") or 0)
    sorry_files = int(st.get("sorry_files") or 0)
    proof_sorry = int(st["proof_sorry"]) if "proof_sorry" in st else sorry_total
    proof_sorry_files = int(st["proof_sorry_files"]) if "proof_sorry_files" in st else sorry_files
    challenge_sorry = int(st.get("challenge_sorry") or 0)
    challenge_sorry_files = int(st.get("challenge_sorry_files") or 0)
    tagline = str(man.get("tagline") or man.get("description") or "")
    if slug == "riemann-hypothesis" and not tagline:
        tagline = default_rh_root_entry()["tagline"]
    assets = man.get("assets") or {}
    prov_notes = ((man.get("provenance") or {}).get("notes_layer") or {})
    has_embedding_2d = bool(assets.get("embedding_2d"))
    notes_enabled = bool(prov_notes.get("enabled", False))
    return {
        "slug": slug,
        "title": str(man.get("title") or slug),
        "path": rel_path,
        "manifest_path": manifest_rel,
        "files": int(st.get("total_files") or 0),
        "lines": int(st.get("total_lines") or 0),
        "edges": int(st.get("total_edges") or st.get("edges") or 0),
        "decls": int(st.get("total_decls") or 0),
        "thms": int(st.get("thms") or 0),
        "defs": int(st.get("defs") or 0),
        "inds": int(st.get("inds") or 0),
        "axioms": int(st.get("axioms") or 0),
        "sorry": sorry_total,
        "sorry_files": sorry_files,
        "proof_sorry": proof_sorry,
        "proof_sorry_files": proof_sorry_files,
        "challenge_sorry": challenge_sorry,
        "challenge_sorry_files": challenge_sorry_files,
        "decide_kernel": int(st.get("decide_kernel_count") or 0),
        "root_module": str(st.get("root_module") or ""),
        "reach_count": int(st.get("reach_count") or 0),
        "flirt_misfiles": int(st.get("flirt_misfiles") or 0),
        "has_kernel_export": has_kernel,
        "has_embedding_2d": has_embedding_2d,
        "notes_enabled": notes_enabled,
        "source_only": source_only,
        "category": cat,
        "license": str(man.get("license") or ("None (no license)" if slug == "riemann-hypothesis" else "Unknown")),
        "badge": str(man.get("badge") or ("Kernel + Source" if has_kernel else "Source Scan")),
        "repo_url": str(man.get("repo_url") or ""),
        "pinned_commit": str(man.get("pinned_commit") or ""),
        "src_prefix": str(man.get("src_prefix") or ""),
        "tagline": tagline,
    }


def register_rh_root(gallery_dir: str) -> Dict[str, Any]:
    """Rebuild `<gallery_dir>/projects.json` with the root `riemann-hypothesis` entry included."""
    return build_projects_registry(gallery_dir, include_rh_root=True)


def build_projects_registry(gallery_dir: str, *, include_rh_root: bool = False) -> Dict[str, Any]:
    """Scan `<gallery_dir>/p/*/manifest.json` (plus optional root) and write `<gallery_dir>/projects.json`."""
    if os.path.islink(gallery_dir):
        raise ValueError(f"Refusing symlinked gallery_dir: {gallery_dir}")
    os.makedirs(gallery_dir, exist_ok=True)
    _safe_write_bytes(os.path.join(gallery_dir, ".nojekyll"), b"")

    p_root = os.path.join(gallery_dir, "p")
    entries: List[Dict[str, Any]] = []
    seen_slugs: Set[str] = set()
    order_rank = {s: i for i, s in enumerate(_SHOWCASE_ORDER)}

    root_mpath = os.path.join(gallery_dir, "manifest.json")
    if os.path.isfile(root_mpath) and not os.path.islink(root_mpath):
        with open(root_mpath, "r", encoding="utf-8") as f:
            rman = json.load(f)
        if isinstance(rman, dict) and not rman.get("demo_mode"):
            rslug = str(rman.get("slug") or rman.get("repo_name") or "riemann-hypothesis")
            entries.append(_entry_from_manifest(rman, slug=rslug, rel_path=".", manifest_rel="manifest.json"))
            seen_slugs.add(rslug)
            if rman.get("registry") != "projects.json":
                rman["registry"] = "projects.json"
                _safe_write_json(root_mpath, _sanitize_json_value(rman))

    if os.path.isdir(p_root) and not os.path.islink(p_root):
        for slug in sorted(os.listdir(p_root)):
            pdir = os.path.join(p_root, slug)
            mpath = os.path.join(pdir, "manifest.json")
            if os.path.islink(pdir) or os.path.islink(mpath) or not os.path.isfile(mpath):
                continue
            with open(mpath, "r", encoding="utf-8") as f:
                man = json.load(f)
            if not isinstance(man, dict):
                continue
            entries.append(_entry_from_manifest(man, slug=slug, rel_path=f"p/{slug}", manifest_rel=f"p/{slug}/manifest.json"))
            seen_slugs.add(slug)

    if include_rh_root and "riemann-hypothesis" not in seen_slugs:
        entries.append(default_rh_root_entry())
        seen_slugs.add("riemann-hypothesis")

    entries.sort(key=lambda e: (order_rank.get(e["slug"], len(order_rank) + 1), e["slug"]))

    # Auto-generate cross-proof stylometry comparison (`data/corpus_comparison.json`)
    import stylometry as _stylometry
    comp_rel: Optional[str] = None
    try:
        comp_doc = _stylometry.build_corpus_comparison(gallery_dir)
        if comp_doc.get("count", 0) > 0:
            comp_rel = "data/corpus_comparison.json"
    except Exception:
        comp_rel = None

    registry: Dict[str, Any] = {
        "schema": PROJECTS_REGISTRY_SCHEMA,
        "generated_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "count": len(entries),
        "projects": entries,
    }
    if comp_rel:
        registry["comparison"] = comp_rel
    registry = _sanitize_json_value(registry)
    _safe_write_json(os.path.join(gallery_dir, "projects.json"), registry)
    return registry


def default_smoke_specs(repo_root: str = _REPO_ROOT) -> List[Dict[str, Any]]:
    """Return the 7 non-RH project export specs resolved against `repo_root`."""
    _, leanre_sha = _git_meta(repo_root)
    specs = [
        {
            "slug": "navier-stokes",
            "title": "Navier–Stokes Blow-up (Alpöge–Buckmaster)",
            "src_dir": os.path.join(repo_root, "data", "corpora", "navier-stokes", "lean"),
            "repo_url": "https://github.com/tristanbuckmaster/navier-stokes",
            "src_prefix": "lean/",
            "license_label": "None (no license)",
            "category": "ai-assisted",
            "badge": "AI-Assisted · No License",
            "description": "Finite-time blow-up for Navier–Stokes (Alpöge–Buckmaster); Arb 128-bit certificate external.",
        },
        {
            "slug": "navier-stokes-euler",
            "title": "Navier–Stokes & Euler Blow-up (OpenAI)",
            "src_dir": os.path.join(repo_root, "data", "corpora", "NavierStokesAndEuler"),
            "repo_url": "https://github.com/openai/NavierStokesAndEuler",
            "src_prefix": "",
            "license_label": "Apache-2.0",
            "category": "ai-assisted",
            "badge": "AI-Assisted · Apache-2.0",
            "description": "Lean 4 formalizations of Navier–Stokes and Euler finite-time blow-up.",
        },
        {
            "slug": "prime-number-theorem",
            "title": "PrimeNumberTheoremAnd",
            "src_dir": os.path.join(repo_root, "data", "corpora", "PrimeNumberTheoremAnd"),
            "repo_url": "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd",
            "src_prefix": "",
            "license_label": "Apache-2.0",
            "category": "human-baseline",
            "badge": "Community Formalization",
            "description": "Community formalization of the Prime Number Theorem and analytic number theory.",
        },
        {
            "slug": "carleson",
            "title": "Carleson",
            "src_dir": os.path.join(repo_root, "data", "corpora", "carleson"),
            "repo_url": "https://github.com/fpvandoorn/carleson",
            "src_prefix": "",
            "license_label": "Apache-2.0",
            "category": "human-baseline",
            "badge": "Community Formalization",
            "description": "Formalization of generalized Carleson's theorem on doubling metric measure spaces.",
        },
        {
            "slug": "flt",
            "title": "Fermat's Last Theorem (FLT)",
            "src_dir": os.path.join(repo_root, "data", "corpora", "FLT"),
            "repo_url": "https://github.com/ImperialCollegeLondon/FLT",
            "src_prefix": "",
            "license_label": "Apache-2.0",
            "category": "human-baseline",
            "badge": "Community Formalization",
            "description": "Imperial College London formalization of Fermat's Last Theorem in Lean 4.",
        },
        {
            "slug": "sphere-packing",
            "title": "Sphere Packing (Viazovska E8)",
            "src_dir": os.path.join(repo_root, "data", "corpora", "SpherePacking"),
            "repo_url": "https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean",
            "src_prefix": "",
            "license_label": "Apache-2.0",
            "category": "human-baseline",
            "badge": "Community Formalization",
            "description": "Lean 4 formalization of Maryna Viazovska's 8-dimensional sphere packing theorem.",
        },
        {
            "slug": "tiny-demo",
            "title": "Tiny Demo (Kernel + Source)",
            "src_dir": os.path.join(repo_root, "examples", "tiny_demo"),
            "repo_url": "https://github.com/bohemian-miser/leanre",
            "pinned_commit": leanre_sha or "main",
            "src_prefix": "examples/tiny_demo/",
            "license_label": "AGPL-3.0-or-later OR MIT-0",
            "category": "demo",
            "badge": "Demo · Kernel + Source",
            "description": "Bundled 5-file Lean 4 fixture with full kernel NDJSON export.",
            "ndjson_path": os.path.join(repo_root, "examples", "tiny_demo", "demo.ndjson"),
        },
    ]
    for sp in specs:
        if "pinned_commit" not in sp:
            r_url, r_sha = _git_meta(sp["src_dir"])
            if r_url:
                sp["repo_url"] = r_url
            sp["pinned_commit"] = r_sha or "main"
    return specs


def _resolve_cfg_path(base_dir: str, val: Optional[str]) -> Optional[str]:
    if not val:
        return None
    s = str(val).strip()
    if not s:
        return None
    return s if os.path.isabs(s) else os.path.join(base_dir, s)


def publish_gallery(
    config_path: str,
    out_dir: str,
    *,
    workers: Optional[int] = None,
    only_slugs: Optional[Sequence[str]] = None,
    max_bundles: int = 60,
    max_theorems: int = 80,
    max_circuits: Optional[int] = None,
    search_limit: int = 30_000,
    run_flirt: bool = True,
    run_embedding: bool = True,
) -> Dict[str, Any]:
    """Build ONE unified static site across all projects configured in `leanre_gallery.toml`."""
    import tomllib
    import export_site as _export_site

    if os.path.islink(out_dir):
        raise ValueError(f"Refusing symlinked out_dir: {out_dir}")
    abs_cfg = os.path.abspath(config_path)
    if not os.path.isfile(abs_cfg):
        raise FileNotFoundError(f"Missing gallery config: {config_path}")
    base_dir = os.path.dirname(abs_cfg)

    with open(abs_cfg, "rb") as f:
        cfg_doc = tomllib.load(f)

    os.makedirs(out_dir, exist_ok=True)
    _export_site._copy_or_fallback_assets(out_dir, "leanre — Proof Explorer")

    only_set: Optional[Set[str]] = {s.strip() for s in only_slugs if s.strip()} if only_slugs else None
    built: List[Dict[str, Any]] = []
    skipped: List[Dict[str, str]] = []

    for proj in cfg_doc.get("projects") or []:
        slug = str(proj.get("slug") or "").strip()
        if not slug:
            continue
        if only_set is not None and slug not in only_set:
            continue

        title = str(proj.get("title") or slug)
        is_root = bool(proj.get("root", False)) or str(proj.get("mode") or "") == "kernel_site"
        src_rel = str(proj.get("src_dir") or "").strip()
        src_abs = _resolve_cfg_path(base_dir, src_rel)

        notes_rel = proj.get("notes_dir")
        notes_abs = _resolve_cfg_path(base_dir, str(notes_rel)) if notes_rel else None
        if notes_abs and not os.path.isdir(notes_abs):
            notes_abs = None

        extra_dossiers_abs: List[str] = []
        for ed in (proj.get("extra_dossiers") or ()):
            ed_abs = _resolve_cfg_path(base_dir, str(ed))
            if ed_abs and os.path.isfile(ed_abs):
                extra_dossiers_abs.append(ed_abs)

        if is_root:
            kdb_abs = _resolve_cfg_path(base_dir, proj.get("kernel_db"))
            has_kdb = bool(kdb_abs and os.path.isfile(kdb_abs))
            has_src = bool(src_abs and os.path.isdir(src_abs))
            if not has_kdb and not has_src:
                reason = f"missing local kernel_db ({proj.get('kernel_db')}) and src_dir ({src_rel})"
                print(f"[publish] skipping {slug!r}: {reason}", file=sys.stderr)
                skipped.append({"slug": slug, "reason": reason})
                continue

            def _opt_file(key: str) -> Optional[str]:
                p = _resolve_cfg_path(base_dir, proj.get(key))
                return p if (p and os.path.isfile(p)) else None

            def _opt_dir(key: str) -> Optional[str]:
                p = _resolve_cfg_path(base_dir, proj.get(key))
                return p if (p and os.path.isdir(p)) else None

            res = _export_site.export_split_site(
                out_dir,
                decomp_dir=_opt_dir("decomp_dir"),
                trim_report=_opt_file("trim_report"),
                cluster_labels=_opt_file("cluster_labels"),
                portability=_opt_file("portability"),
                benchmark=_opt_file("benchmark"),
                atlas_summary=_opt_file("atlas_summary"),
                embedding_2d=_opt_file("embedding_2d"),
                kernel_db=kdb_abs if has_kdb else None,
                leanre_db=_opt_file("leanre_db"),
                src_root=src_abs if has_src else None,
                findings_dir=_opt_dir("findings_dir"),
                analysis_dir=_opt_dir("analysis_dir"),
                research_dir=_opt_dir("research_dir"),
                notes_dir=notes_abs,
                extra_dossiers=extra_dossiers_abs or None,
                flirt_dir=_opt_dir("flirt_dir"),
                config_path=_opt_file("config"),
                title=title,
                repo_url=proj.get("repo_url"),
                pinned_commit=proj.get("pinned_commit"),
                src_prefix=proj.get("src_prefix"),
                slug=slug,
                category=proj.get("category"),
                license_label=proj.get("license"),
                badge=proj.get("badge"),
                tagline=proj.get("tagline") or proj.get("description"),
                max_bundles=max_bundles,
                max_theorems=max_theorems,
                max_circuits=max_circuits,
                search_limit=search_limit,
                demo_mode=False,
                registry_rel="projects.json",
            )
            built.append({"slug": slug, "mode": "root", "total_bytes": res["total_bytes"]})
            continue

        if not src_abs or not os.path.isdir(src_abs):
            reason = f"missing local corpus {src_rel!r}"
            print(f"[publish] skipping {slug!r}: {reason}", file=sys.stderr)
            skipped.append({"slug": slug, "reason": reason})
            continue

        pinned = str(proj.get("pinned_commit") or "").strip()
        if not pinned or pinned == "main":
            _, git_sha = _git_meta(src_abs)
            if git_sha:
                pinned = git_sha
        ndj_abs = _resolve_cfg_path(base_dir, proj.get("ndjson_path"))
        if ndj_abs and not os.path.isfile(ndj_abs):
            ndj_abs = None
        kdb_abs = _resolve_cfg_path(base_dir, proj.get("kernel_db"))
        if kdb_abs and not os.path.isfile(kdb_abs):
            kdb_abs = None

        res = export_source_project(
            src_abs,
            out_dir,
            slug=slug,
            title=title,
            repo_url=str(proj.get("repo_url") or ""),
            pinned_commit=pinned,
            src_prefix=str(proj.get("src_prefix") or ""),
            description=str(proj.get("description") or ""),
            badge=str(proj.get("badge") or ""),
            license_label=str(proj.get("license") or ""),
            category=proj.get("category"),
            tagline=proj.get("tagline"),
            kernel_db=kdb_abs,
            ndjson_path=ndj_abs,
            notes_dir=notes_abs,
            extra_dossiers=extra_dossiers_abs or None,
            run_flirt=run_flirt,
            run_embedding=run_embedding,
            workers=workers,
            search_limit=search_limit,
        )
        built.append({
            "slug": slug,
            "mode": "gallery_project",
            "total_bytes": res["total_bytes"],
            "has_embedding_2d": res["has_embedding_2d"],
            "notes_enabled": res["notes_enabled"],
        })

    reg = build_projects_registry(out_dir)
    safety = _verify_export_safety(out_dir)
    return {
        "schema": PROJECTS_REGISTRY_SCHEMA,
        "out_dir": os.path.basename(os.path.abspath(out_dir)),
        "built_count": len(built),
        "skipped_count": len(skipped),
        "built": built,
        "skipped": skipped,
        "registry_count": reg["count"],
        "comparison": reg.get("comparison"),
        "total_bytes": safety["total_bytes"],
        "file_count": safety["file_count"],
        "max_file_bytes": safety["max_file_bytes"],
        "max_file_rel": safety["max_file_rel"],
    }


def publish_main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        prog="leanre publish",
        description="Build ONE unified static site across all projects in leanre_gallery.toml.",
    )
    ap.add_argument(
        "--config",
        default=os.path.join(_REPO_ROOT, "leanre_gallery.toml"),
        help="Path to leanre_gallery.toml (default: repo root leanre_gallery.toml)",
    )
    ap.add_argument("--out-dir", required=True, help="Output static site directory")
    ap.add_argument("--workers", type=int, default=None, help="Parallel worker count")
    ap.add_argument("--only", default=None, help="Optional comma-separated list of project slugs to build")
    ap.add_argument("--max-bundles", type=int, default=60, help="Max pre-rendered bundle circuits for root project")
    ap.add_argument("--max-theorems", type=int, default=80, help="Max pre-rendered theorem circuits for root project")
    ap.add_argument("--max-circuits", type=int, default=None, help="Optional total circuit cap for root project")
    ap.add_argument("--search-limit", type=int, default=30_000, help="Max declarations indexed per project")
    ap.add_argument("--no-flirt", action="store_true", help="Skip FLIRT Tier 1 pass for source projects")
    ap.add_argument("--no-embedding", action="store_true", help="Skip 2D embedding map generation")
    args = ap.parse_args(argv)

    only_list = [s.strip() for s in args.only.split(",") if s.strip()] if args.only else None
    rep = publish_gallery(
        args.config,
        args.out_dir,
        workers=args.workers,
        only_slugs=only_list,
        max_bundles=args.max_bundles,
        max_theorems=args.max_theorems,
        max_circuits=args.max_circuits,
        search_limit=args.search_limit,
        run_flirt=not args.no_flirt,
        run_embedding=not args.no_embedding,
    )
    print(json.dumps(rep, indent=2, sort_keys=True))
    return 0


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        prog="leanre-gallery",
        description="Build multi-project Lean 4 static gallery (`p/<slug>/` + `projects.json`).",
    )
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_add = sub.add_parser("add", help="Scan a Lean 4 repo and add it to the gallery")
    p_add.add_argument("src_dir", help="Path to Lean 4 source directory")
    p_add.add_argument("--out-dir", required=True, help="Gallery output root directory")
    p_add.add_argument("--slug", required=True, help="URL-safe project slug")
    p_add.add_argument("--title", required=True, help="Display title")
    p_add.add_argument("--repo-url", default="", help="GitHub repository URL")
    p_add.add_argument("--pinned-commit", default="", help="Pinned commit SHA")
    p_add.add_argument("--src-prefix", default="", help="Repo path prefix to src_dir (e.g. 'lean/')")
    p_add.add_argument("--description", default="", help="Short description")
    p_add.add_argument("--badge", default="", help="Badge label")
    p_add.add_argument("--license", dest="license_label", default="", help="SPDX / license label")
    p_add.add_argument("--category", default=None, help="ai-assisted | human-baseline | demo")
    p_add.add_argument("--root", default=None, help="Explicit root module (disables --auto-root)")
    p_add.add_argument("--kernel-db", default=None, help="Optional kernel.db path")
    p_add.add_argument("--ndjson", default=None, help="Optional .ndjson(.zst) export path")
    p_add.add_argument("--notes-dir", default=None, help="Optional separately authored notes/<slug>/ directory")
    p_add.add_argument("--extra-dossier", action="append", default=None, help="Optional extra dossier .md file to attach")
    p_add.add_argument("--no-flirt", action="store_true", help="Skip FLIRT Tier 1 pass")
    p_add.add_argument("--no-embedding", action="store_true", help="Skip 2D embedding map generation")
    p_add.add_argument("--workers", type=int, default=None, help="Worker count")

    p_reg = sub.add_parser("registry", help="Rebuild projects.json from <out-dir>/p/*/manifest.json")
    p_reg.add_argument("gallery_dir", help="Gallery root directory")
    p_reg.add_argument("--include-rh-root", action="store_true", help="Include root riemann-hypothesis entry even without root manifest.json")

    p_smoke = sub.add_parser("build-default", help="Build all 7 bundled non-RH gallery projects")
    p_smoke.add_argument("--out-dir", default="/tmp/leanre_gallery_test", help="Gallery output root")
    p_smoke.add_argument("--workers", type=int, default=None, help="Worker count")
    p_smoke.add_argument("--no-rh-root", action="store_true", help="Do not include root riemann-hypothesis entry in projects.json")

    args = ap.parse_args(argv)
    if args.cmd == "add":
        res = export_source_project(
            args.src_dir,
            args.out_dir,
            slug=args.slug,
            title=args.title,
            repo_url=args.repo_url,
            pinned_commit=args.pinned_commit,
            src_prefix=args.src_prefix,
            description=args.description,
            badge=args.badge,
            license_label=args.license_label,
            auto_root=(args.root is None),
            root_module=args.root,
            kernel_db=args.kernel_db,
            ndjson_path=args.ndjson,
            category=args.category,
            notes_dir=args.notes_dir,
            extra_dossiers=args.extra_dossier,
            run_flirt=not args.no_flirt,
            run_embedding=not args.no_embedding,
            workers=args.workers,
        )
        reg = build_projects_registry(args.out_dir)
        print(json.dumps({"project": res, "registry_count": reg["count"]}, indent=2, sort_keys=True))
        return 0

    if args.cmd == "registry":
        reg = build_projects_registry(args.gallery_dir, include_rh_root=bool(args.include_rh_root))
        print(json.dumps(reg, indent=2, sort_keys=True))
        return 0

    if args.cmd == "build-default":
        results = []
        for sp in default_smoke_specs():
            res = export_source_project(
                sp["src_dir"],
                args.out_dir,
                slug=sp["slug"],
                title=sp["title"],
                repo_url=sp["repo_url"],
                pinned_commit=sp["pinned_commit"],
                src_prefix=sp["src_prefix"],
                description=sp["description"],
                badge=sp["badge"],
                license_label=sp["license_label"],
                category=sp["category"],
                ndjson_path=sp.get("ndjson_path"),
                workers=args.workers,
            )
            results.append(res)
        reg = build_projects_registry(args.out_dir, include_rh_root=not bool(args.no_rh_root))
        print(json.dumps({"exports": results, "registry": reg}, indent=2, sort_keys=True))
        return 0

    return 2


if __name__ == "__main__":
    sys.exit(main())
