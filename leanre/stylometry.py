#!/usr/bin/env python3
"""leanre.stylometry — Deterministic cross-proof structural & stylometric comparison.

Computes pure tool-generated metrics (ZERO LLM prose) across one or more Lean 4
proof repositories or an exported leanre gallery directory, emitting:
  - `schema`: `"leanre.corpus_comparison/1"`
  - default gallery output: `<gallery_dir>/data/corpus_comparison.json`

Guardrails:
  - Python 3.11+ stdlib + sibling `leanre` modules only.
  - Strictly read-only on source trees and SQLite databases (`mode=ro`).
  - Refuses symlinked output targets; never leaks workstation host paths.
  - Zero raw `.lean` source bodies stored in outputs.
"""
from __future__ import annotations

import argparse
import collections
import datetime
import json
import multiprocessing
import os
import re
import sqlite3
import statistics
import sys
import tempfile
import zlib
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import config as _config  # noqa: E402
import scanner as _scanner  # noqa: E402

CORPUS_COMPARISON_SCHEMA = "leanre.corpus_comparison/1"

_RE_MAX_HEARTBEATS = re.compile(r"\bset_option\s+maxHeartbeats\b")

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

METRIC_DEFINITIONS: List[Dict[str, str]] = [
    {"key": "files", "label": "Files", "kind": "int"},
    {"key": "lines", "label": "Lines", "kind": "int"},
    {"key": "decls", "label": "Decls", "kind": "int"},
    {"key": "defs", "label": "Defs", "kind": "int"},
    {"key": "thms", "label": "Theorems", "kind": "int"},
    {"key": "inds", "label": "Inductives", "kind": "int"},
    {"key": "comment_lines", "label": "Comment lines", "kind": "int"},
    {"key": "comment_pct", "label": "Comments %", "kind": "pct"},
    {"key": "max_heartbeats_overrides", "label": "maxHeartbeats", "kind": "int"},
    {"key": "name_compress_ratio", "label": "Name compressibility", "kind": "ratio"},
    {"key": "avg_decl_lines", "label": "Avg lines/decl", "kind": "float"},
    {"key": "median_file_lines", "label": "Median file lines", "kind": "float"},
    {"key": "reach_modules", "label": "Reachable files", "kind": "int"},
    {"key": "reach_pct", "label": "Reachable %", "kind": "pct"},
    {"key": "orphan_modules", "label": "Orphan files", "kind": "int"},
    {"key": "orphan_pct", "label": "Orphan %", "kind": "pct"},
    {"key": "exact_clone_clusters", "label": "Exact clones", "kind": "int"},
    {"key": "sig_clone_clusters", "label": "Sig clones", "kind": "int"},
    {"key": "misfile_count", "label": "Dir outliers", "kind": "int"},
    {"key": "misfile_pct", "label": "Dir outliers %", "kind": "pct"},
    {"key": "proof_sorry", "label": "Proof sorry", "kind": "int"},
    {"key": "challenge_sorry", "label": "Challenge sorry", "kind": "int"},
    {"key": "axioms", "label": "Axioms", "kind": "int"},
    {"key": "decide_kernel", "label": "decide +kernel", "kind": "int"},
]


def _open_ro(path: str) -> sqlite3.Connection:
    real = os.path.realpath(path)
    if not os.path.isfile(real):
        raise FileNotFoundError(f"Missing SQLite database: {path}")
    conn = sqlite3.connect(f"file:{real}?mode=ro", uri=True)
    conn.execute("PRAGMA query_only=1")
    return conn


def _sanitize_json_value(obj: Any) -> Any:
    if isinstance(obj, str):
        return _FORBIDDEN_HOST_PATH_RE.sub("<path>", obj) if _FORBIDDEN_HOST_PATH_RE.search(obj) else obj
    if isinstance(obj, list):
        return [_sanitize_json_value(v) for v in obj]
    if isinstance(obj, dict):
        return {k: _sanitize_json_value(v) for k, v in obj.items()}
    return obj


def _safe_write_json(out_path: str, obj: Any) -> int:
    if os.path.islink(out_path):
        raise ValueError(f"Refusing to write through symlink: {out_path}")
    parent = os.path.dirname(os.path.abspath(out_path))
    if parent:
        os.makedirs(parent, exist_ok=True)
    raw = json.dumps(_sanitize_json_value(obj), ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
    with open(out_path, "wb") as f:
        f.write(raw)
    return len(raw)


def count_lean_comment_lines_and_heartbeats(raw_bytes: bytes) -> Tuple[int, int, int]:
    """Count `(lines_wc, comment_lines, max_heartbeats_overrides)` for one Lean 4 file.

    Fast-paths commentless files in C-speed byte checks. Handles `--` line comments,
    nested `/- ... -/` block comments, and double-quoted strings accurately.
    """
    if not raw_bytes:
        return 0, 0, 0
    lines_wc = raw_bytes.count(b"\n")
    if lines_wc == 0 and raw_bytes:
        lines_wc = 1

    has_comment_marker = (b"--" in raw_bytes) or (b"/-" in raw_bytes)
    has_hb_marker = b"maxHeartbeats" in raw_bytes
    if not has_comment_marker:
        hb = len(_RE_MAX_HEARTBEATS.findall(raw_bytes.decode("utf-8", errors="replace"))) if has_hb_marker else 0
        return lines_wc, 0, hb

    text = raw_bytes.decode("utf-8", errors="replace")
    n = len(text)
    i = 0
    in_str = False
    depth = 0
    comment_lines = 0
    line_has_comment = False
    code_chars: List[str] = [] if has_hb_marker else []

    while i < n:
        ch = text[i]
        if ch == "\n":
            if line_has_comment or depth > 0:
                comment_lines += 1
            line_has_comment = depth > 0
            if has_hb_marker:
                code_chars.append("\n")
            i += 1
            continue

        if depth > 0:
            line_has_comment = True
            if ch == "/" and i + 1 < n and text[i + 1] == "-":
                depth += 1
                i += 2
            elif ch == "-" and i + 1 < n and text[i + 1] == "/":
                depth -= 1
                i += 2
            else:
                i += 1
            continue

        if in_str:
            if has_hb_marker:
                code_chars.append(ch)
            if ch == "\\" and i + 1 < n:
                if has_hb_marker:
                    code_chars.append(text[i + 1])
                i += 2
            elif ch == '"':
                in_str = False
                i += 1
            else:
                i += 1
            continue

        if ch == '"':
            in_str = True
            if has_hb_marker:
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
                i = n
            else:
                i = j
        else:
            if has_hb_marker:
                code_chars.append(ch)
            i += 1

    # Final line without trailing newline
    if text and text[-1] != "\n" and (line_has_comment or depth > 0):
        comment_lines += 1

    hb = len(_RE_MAX_HEARTBEATS.findall("".join(code_chars))) if has_hb_marker else 0
    return lines_wc, comment_lines, hb


def _scan_batch_worker(args: Tuple[str, List[str]]) -> Tuple[int, int, int, List[int]]:
    src_dir, rel_paths = args
    tot_lines = 0
    tot_comments = 0
    tot_hb = 0
    per_file_lines: List[int] = []
    for rel in rel_paths:
        full = os.path.join(src_dir, rel)
        try:
            with open(full, "rb") as f:
                raw = f.read()
        except OSError:
            continue
        lwc, cln, hb = count_lean_comment_lines_and_heartbeats(raw)
        tot_lines += lwc
        tot_comments += cln
        tot_hb += hb
        per_file_lines.append(lwc)
    return tot_lines, tot_comments, tot_hb, per_file_lines


def scan_source_stylometry(
    src_dir: str,
    *,
    workers: Optional[int] = None,
) -> Dict[str, Any]:
    """Scan `.lean` files under `src_dir` for comment lines, `maxHeartbeats`, and median file size."""
    abs_src = os.path.abspath(src_dir)
    if not os.path.isdir(abs_src):
        raise FileNotFoundError(f"Missing src_dir: {src_dir}")

    files = _scanner.discover_lean_files(abs_src)
    rel_paths = [rel for _mid, _mname, rel in files]
    if not rel_paths:
        return {
            "files_scanned": 0,
            "lines_scanned": 0,
            "comment_lines": 0,
            "comment_pct": 0.0,
            "max_heartbeats_overrides": 0,
            "median_file_lines": 0.0,
        }

    eff_workers = workers if workers is not None else min(8, os.cpu_count() or 1)
    eff_workers = max(1, int(eff_workers))

    tot_lines = 0
    tot_comments = 0
    tot_hb = 0
    file_lines: List[int] = []

    if eff_workers > 1 and len(rel_paths) >= 200:
        chunk_sz = max(64, (len(rel_paths) + eff_workers * 4 - 1) // (eff_workers * 4))
        batches = [
            (abs_src, rel_paths[i : i + chunk_sz])
            for i in range(0, len(rel_paths), chunk_sz)
        ]
        with multiprocessing.Pool(processes=eff_workers) as pool:
            for l_sum, c_sum, h_sum, flist in pool.imap_unordered(_scan_batch_worker, batches):
                tot_lines += l_sum
                tot_comments += c_sum
                tot_hb += h_sum
                file_lines.extend(flist)
    else:
        tot_lines, tot_comments, tot_hb, file_lines = _scan_batch_worker((abs_src, rel_paths))

    med = round(float(statistics.median(file_lines)), 1) if file_lines else 0.0
    comment_pct = round(100.0 * tot_comments / max(1, tot_lines), 2) if tot_lines > 0 else 0.0
    return {
        "files_scanned": len(file_lines),
        "lines_scanned": tot_lines,
        "comment_lines": tot_comments,
        "comment_pct": comment_pct,
        "max_heartbeats_overrides": tot_hb,
        "median_file_lines": med,
    }


def compute_name_compress_ratio(decl_names: Sequence[str]) -> float:
    """Compute `len(zlib.compress(names_bytes)) / len(names_bytes)` over sorted declaration names.

    Lower ratios indicate more repetitive / templated naming conventions.
    """
    cleaned = sorted(
        str(nm).strip()
        for nm in decl_names
        if nm and not str(nm).startswith("_anon_")
    )
    if not cleaned:
        return 0.0
    names_bytes = "\n".join(cleaned).encode("utf-8")
    if not names_bytes:
        return 0.0
    comp = zlib.compress(names_bytes, level=6)
    return round(len(comp) / len(names_bytes), 4)


def _is_challenge_spec_file(file_path: str, module_name: str = "") -> bool:
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


def _read_scanner_db_for_stylometry(scan_db: str) -> Dict[str, Any]:
    """Extract stylometric aggregates directly from a populated `leanre.db` (read-only)."""
    conn = _open_ro(scan_db)
    try:
        cs_row = conn.execute("SELECT value_json FROM meta WHERE key='corpus_stats'").fetchone()
        fs_row = conn.execute("SELECT value_json FROM meta WHERE key='forensic_summary'").fetchone()
        cs = json.loads(cs_row[0]) if cs_row else {}
        fs = json.loads(fs_row[0]) if fs_row else {}

        mod_rows = conn.execute(
            "SELECT name, file_path, lines_wc, clone_sig, clone_cluster_size FROM modules"
        ).fetchall()
        file_lines = [int(r[2]) for r in mod_rows]
        by_mod_path = {str(r[0]): str(r[1]) for r in mod_rows}
        clone_sigs: Set[str] = {
            str(r[3])
            for r in mod_rows
            if r[3] and str(r[3]) != "shim_empty" and int(r[4] or 0) > 1
        }

        decl_names = [
            str(r[0])
            for r in conn.execute("SELECT name FROM declarations")
            if r[0] and not str(r[0]).startswith("_anon_")
        ]

        sorry_rows = conn.execute(
            "SELECT module FROM forensic_hits WHERE tag = 'sorry'"
        ).fetchall()
        proof_sorry = 0
        challenge_sorry = 0
        for (mod_nm,) in sorry_rows:
            s_mod = str(mod_nm or "")
            fp = by_mod_path.get(s_mod, s_mod.replace(".", "/") + ".lean")
            if _is_challenge_spec_file(fp, s_mod):
                challenge_sorry += 1
            else:
                proof_sorry += 1
    finally:
        conn.close()

    return {
        "corpus_stats": cs,
        "forensic_summary": fs,
        "file_lines": file_lines,
        "decl_names": decl_names,
        "scanner_clone_clusters": len(clone_sigs),
        "proof_sorry": proof_sorry,
        "challenge_sorry": challenge_sorry,
    }


def _extract_flirt_counts(flirt_summary: Optional[Dict[str, Any]]) -> Tuple[Optional[int], int, int]:
    """Return `(exact_clone_clusters, sig_clone_clusters, misfile_count)` from a FLIRT Tier 1 summary."""
    if not isinstance(flirt_summary, dict):
        return None, 0, 0
    bs = flirt_summary.get("boilerplate_stats") or {}
    ms = flirt_summary.get("misfile_scoring") or {}
    exact_c = int((bs.get("alpha_body_clone") or {}).get("clusters") or 0)
    sig_c = int((bs.get("sigset_clone") or {}).get("clusters") or 0)
    mis_c = int(ms.get("alertable_misfiles_total") or 0)
    return exact_c, sig_c, mis_c


def compute_project_stylometry(
    *,
    src_dir: Optional[str] = None,
    scan_db: Optional[str] = None,
    flirt_summary: Optional[Dict[str, Any]] = None,
    snapshot: Optional[Dict[str, Any]] = None,
    slug: str = "",
    title: str = "",
    path: str = ".",
    license_label: str = "",
    category: str = "",
    has_kernel_export: bool = False,
    has_embedding_2d: bool = False,
    workers: Optional[int] = None,
) -> Dict[str, Any]:
    """Compute a complete deterministic stylometry record for a single Lean 4 project."""
    db_info: Optional[Dict[str, Any]] = None
    if snapshot is not None:
        cs = snapshot.get("corpus_stats") or {}
        fs = snapshot.get("forensic_summary") or {}
        modules = snapshot.get("modules") or []
        decls = snapshot.get("decls") or []
        hits = snapshot.get("hits") or []
        by_mod_path = {str(m.get("name") or ""): str(m.get("file_path") or "") for m in modules}
        file_lines = [int(m.get("lines_wc") or 0) for m in modules]
        decl_names = [
            str(d.get("name") or "")
            for d in decls
            if d.get("name") and not str(d.get("name")).startswith("_anon_")
        ]
        proof_sorry = 0
        challenge_sorry = 0
        for h in hits:
            if h.get("tag") != "sorry":
                continue
            mod_nm = str(h.get("module") or "")
            fp = by_mod_path.get(mod_nm, mod_nm.replace(".", "/") + ".lean")
            if _is_challenge_spec_file(fp, mod_nm):
                challenge_sorry += 1
            else:
                proof_sorry += 1
        scanner_clones = 0
        if scan_db and os.path.isfile(scan_db):
            conn = _open_ro(scan_db)
            try:
                scanner_clones = int(
                    conn.execute(
                        "SELECT COUNT(DISTINCT clone_sig) FROM modules "
                        "WHERE clone_cluster_size > 1 AND clone_sig IS NOT NULL AND clone_sig != 'shim_empty'"
                    ).fetchone()[0]
                )
            finally:
                conn.close()
    elif scan_db and os.path.isfile(scan_db):
        db_info = _read_scanner_db_for_stylometry(scan_db)
        cs = db_info["corpus_stats"]
        fs = db_info["forensic_summary"]
        file_lines = db_info["file_lines"]
        decl_names = db_info["decl_names"]
        proof_sorry = db_info["proof_sorry"]
        challenge_sorry = db_info["challenge_sorry"]
        scanner_clones = db_info["scanner_clone_clusters"]
    elif src_dir and os.path.isdir(src_dir):
        with tempfile.TemporaryDirectory(prefix="leanre_stylo_") as td:
            tmp_db = os.path.join(td, "leanre.db")
            local_cfg = _config.find_local_config(src_dir)
            cfg = _config.load_config(str(local_cfg)) if local_cfg is not None else None
            _scanner.run_scan(
                src_dir=os.path.abspath(src_dir),
                db_path=tmp_db,
                root_module="auto",
                workers=workers,
                verbose=False,
                config=cfg,
                max_hits_per_tag=0,
            )
            db_info = _read_scanner_db_for_stylometry(tmp_db)
            cs = db_info["corpus_stats"]
            fs = db_info["forensic_summary"]
            file_lines = db_info["file_lines"]
            decl_names = db_info["decl_names"]
            proof_sorry = db_info["proof_sorry"]
            challenge_sorry = db_info["challenge_sorry"]
            scanner_clones = db_info["scanner_clone_clusters"]
            if flirt_summary is None:
                try:
                    from flirt import tier1 as _tier1
                    t1_db = os.path.join(td, "tier1.db")
                    flirt_summary = _tier1.run_tier1(
                        src_dir=os.path.abspath(src_dir),
                        db_path=t1_db,
                        summary_path=None,
                        threads=workers or min(8, os.cpu_count() or 4),
                        kernel_db="",
                        verbose=False,
                        config=cfg,
                    )
                except Exception:
                    flirt_summary = None
    else:
        cs = {}
        fs = {}
        file_lines = []
        decl_names = []
        proof_sorry = 0
        challenge_sorry = 0
        scanner_clones = 0

    src_stylo = (
        scan_source_stylometry(src_dir, workers=workers)
        if (src_dir and os.path.isdir(src_dir))
        else None
    )

    files = int(cs.get("modules") or (src_stylo["files_scanned"] if src_stylo else len(file_lines)))
    lines = int(cs.get("lines_wc") or (src_stylo["lines_scanned"] if src_stylo else sum(file_lines)))
    decls = int(cs.get("declarations") or len(decl_names))

    kinds = cs.get("decl_counts_by_kind") or {}
    thms = int(kinds.get("theorem", 0)) + int(kinds.get("lemma", 0))
    if thms == 0 and cs.get("theorems"):
        thms = int(cs.get("theorems") or 0)
    defs = (
        int(kinds.get("def", 0))
        + int(kinds.get("abbrev", 0))
        + int(kinds.get("instance", 0))
        + int(kinds.get("opaque", 0))
    )
    if defs == 0 and cs.get("definitions"):
        defs = int(cs.get("definitions") or 0)
    inds = int(kinds.get("inductive", 0)) + int(kinds.get("structure", 0)) + int(kinds.get("class", 0))

    tot_hits = fs.get("total_hit_counts") or fs.get("hit_counts") or {}
    axioms = int(kinds.get("axiom", 0)) or int(tot_hits.get("axiom", 0) or 0)
    decide_kernel = int(tot_hits.get("decide_kernel", 0) or 0)

    # Reconcile total sorry if forensic_hits table was truncated in a legacy DB
    tot_sorry_meta = int(tot_hits.get("sorry", 0) or 0)
    if tot_sorry_meta > proof_sorry + challenge_sorry:
        proof_sorry += tot_sorry_meta - (proof_sorry + challenge_sorry)

    comment_lines = int(src_stylo["comment_lines"]) if src_stylo else 0
    comment_pct = round(100.0 * comment_lines / max(1, lines), 2) if lines > 0 else 0.0
    max_hb = int(src_stylo["max_heartbeats_overrides"]) if src_stylo else 0

    if file_lines:
        median_file_lines = round(float(statistics.median(file_lines)), 1)
    elif src_stylo:
        median_file_lines = float(src_stylo["median_file_lines"])
    else:
        median_file_lines = 0.0

    name_compress_ratio = compute_name_compress_ratio(decl_names)
    avg_decl_lines = round(lines / max(1, decls), 2) if lines > 0 else 0.0

    reach_modules = int(cs.get("reachable_from_main") or 0)
    if reach_modules > files and files > 0:
        reach_modules = files
    reach_pct = round(100.0 * reach_modules / max(1, files), 2) if files > 0 else 0.0
    orphan_modules = max(0, files - reach_modules)
    orphan_pct = round(100.0 * orphan_modules / max(1, files), 2) if files > 0 else 0.0

    exact_c, sig_c, mis_c = _extract_flirt_counts(flirt_summary)
    exact_clone_clusters = exact_c if exact_c is not None else scanner_clones
    sig_clone_clusters = sig_c
    misfile_count = mis_c
    misfile_pct = round(100.0 * misfile_count / max(1, files), 2) if files > 0 else 0.0

    return {
        "slug": slug,
        "title": title or slug,
        "path": path,
        "files": files,
        "lines": lines,
        "decls": decls,
        "defs": defs,
        "thms": thms,
        "inds": inds,
        "comment_lines": comment_lines,
        "comment_pct": comment_pct,
        "max_heartbeats_overrides": max_hb,
        "name_compress_ratio": name_compress_ratio,
        "avg_decl_lines": avg_decl_lines,
        "median_file_lines": median_file_lines,
        "reach_modules": reach_modules,
        "reach_pct": reach_pct,
        "orphan_modules": orphan_modules,
        "orphan_pct": orphan_pct,
        "exact_clone_clusters": exact_clone_clusters,
        "sig_clone_clusters": sig_clone_clusters,
        "misfile_count": misfile_count,
        "misfile_pct": misfile_pct,
        "proof_sorry": proof_sorry,
        "challenge_sorry": challenge_sorry,
        "axioms": axioms,
        "decide_kernel": decide_kernel,
        "license": license_label or "Unknown",
        "has_kernel_export": bool(has_kernel_export),
        "has_embedding_2d": bool(has_embedding_2d),
        "category": category or "unknown",
    }


def _stylometry_row_from_manifest(
    man: Dict[str, Any],
    proj_dir: str,
    *,
    slug: str,
    rel_path: str,
) -> Dict[str, Any]:
    """Assemble a canonical comparison row from an exported project's `manifest.json`."""
    st = man.get("stats") or {}
    assets = man.get("assets") or {}
    emb = man.get("stylometry") if isinstance(man.get("stylometry"), dict) else {}

    has_kernel = not bool(man.get("source_only", not bool(st.get("kernel_total_decls"))))
    has_emb = bool(assets.get("embedding_2d"))

    # Optional fallback read of exported FLIRT JSON inside proj_dir
    flirt_doc: Optional[Dict[str, Any]] = None
    for cand_rel in (assets.get("flirt_tier1"), assets.get("tier1_summary"), "data/flirt_tier1.json", "data/flirt/tier1_summary.json"):
        if not cand_rel:
            continue
        cand_full = os.path.join(proj_dir, str(cand_rel))
        if os.path.isfile(cand_full) and not os.path.islink(cand_full):
            try:
                with open(cand_full, "r", encoding="utf-8") as f:
                    flirt_doc = json.load(f)
                break
            except (OSError, json.JSONDecodeError):
                pass
    fl_exact, fl_sig, fl_mis = _extract_flirt_counts(flirt_doc)

    files = int(emb.get("files", st.get("total_files") or 0))
    lines = int(emb.get("lines", st.get("total_lines") or 0))
    decls = int(emb.get("decls", st.get("total_decls") or 0))
    defs = int(emb.get("defs", st.get("defs") or 0))
    thms = int(emb.get("thms", st.get("thms") or 0))
    inds = int(emb.get("inds", st.get("inds") or 0))

    comment_lines = int(emb.get("comment_lines") or 0)
    comment_pct = float(emb["comment_pct"]) if "comment_pct" in emb else (
        round(100.0 * comment_lines / max(1, lines), 2) if lines > 0 else 0.0
    )
    max_hb = int(emb.get("max_heartbeats_overrides") or 0)
    name_compress = float(emb.get("name_compress_ratio") or 0.0)
    avg_decl_lines = float(emb["avg_decl_lines"]) if "avg_decl_lines" in emb else (
        round(lines / max(1, decls), 2) if lines > 0 else 0.0
    )
    median_file_lines = float(emb.get("median_file_lines") or 0.0)

    reach_modules = int(emb.get("reach_modules", st.get("reach_count") or 0))
    if reach_modules > files and files > 0:
        reach_modules = files
    reach_pct = float(emb["reach_pct"]) if "reach_pct" in emb else (
        round(100.0 * reach_modules / max(1, files), 2) if files > 0 else 0.0
    )
    orphan_modules = int(emb["orphan_modules"]) if "orphan_modules" in emb else max(0, files - reach_modules)
    orphan_pct = float(emb["orphan_pct"]) if "orphan_pct" in emb else (
        round(100.0 * orphan_modules / max(1, files), 2) if files > 0 else 0.0
    )

    exact_clones = int(emb["exact_clone_clusters"]) if "exact_clone_clusters" in emb else int(fl_exact or 0)
    sig_clones = int(emb["sig_clone_clusters"]) if "sig_clone_clusters" in emb else int(fl_sig or 0)
    mis_cnt = int(emb["misfile_count"]) if "misfile_count" in emb else int(st.get("flirt_misfiles") or fl_mis or 0)
    mis_pct = float(emb["misfile_pct"]) if "misfile_pct" in emb else (
        round(100.0 * mis_cnt / max(1, files), 2) if files > 0 else 0.0
    )

    sorry_tot = int(st.get("sorry_count") or 0)
    proof_sorry = int(emb["proof_sorry"]) if "proof_sorry" in emb else (
        int(st["proof_sorry"]) if "proof_sorry" in st else sorry_tot
    )
    challenge_sorry = int(emb["challenge_sorry"]) if "challenge_sorry" in emb else int(st.get("challenge_sorry") or 0)
    axioms = int(emb["axioms"]) if "axioms" in emb else int(st.get("axioms") or 0)
    decide_kernel = int(emb["decide_kernel"]) if "decide_kernel" in emb else int(st.get("decide_kernel_count") or 0)

    cat = str(man.get("category") or emb.get("category") or ("kernel" if (has_kernel and slug == "riemann-hypothesis") else "unknown"))
    lic = str(man.get("license") or emb.get("license") or "Unknown")

    return {
        "slug": slug,
        "title": str(man.get("title") or emb.get("title") or slug),
        "path": rel_path,
        "files": files,
        "lines": lines,
        "decls": decls,
        "defs": defs,
        "thms": thms,
        "inds": inds,
        "comment_lines": comment_lines,
        "comment_pct": comment_pct,
        "max_heartbeats_overrides": max_hb,
        "name_compress_ratio": name_compress,
        "avg_decl_lines": avg_decl_lines,
        "median_file_lines": median_file_lines,
        "reach_modules": reach_modules,
        "reach_pct": reach_pct,
        "orphan_modules": orphan_modules,
        "orphan_pct": orphan_pct,
        "exact_clone_clusters": exact_clones,
        "sig_clone_clusters": sig_clones,
        "misfile_count": mis_cnt,
        "misfile_pct": mis_pct,
        "proof_sorry": proof_sorry,
        "challenge_sorry": challenge_sorry,
        "axioms": axioms,
        "decide_kernel": decide_kernel,
        "license": lic,
        "has_kernel_export": has_kernel,
        "has_embedding_2d": has_emb,
        "category": cat,
    }


def build_corpus_comparison(
    gallery_dir: str,
    *,
    out_path: Optional[str] = None,
) -> Dict[str, Any]:
    """Build `<gallery_dir>/data/corpus_comparison.json` (`leanre.corpus_comparison/1`) from manifests."""
    if os.path.islink(gallery_dir):
        raise ValueError(f"Refusing symlinked gallery_dir: {gallery_dir}")

    rows: List[Dict[str, Any]] = []
    seen_slugs: Set[str] = set()
    order_rank = {s: i for i, s in enumerate(_SHOWCASE_ORDER)}

    root_mpath = os.path.join(gallery_dir, "manifest.json")
    if os.path.isfile(root_mpath) and not os.path.islink(root_mpath):
        with open(root_mpath, "r", encoding="utf-8") as f:
            rman = json.load(f)
        if isinstance(rman, dict) and not rman.get("demo_mode"):
            rslug = str(rman.get("slug") or rman.get("repo_name") or "riemann-hypothesis")
            rows.append(_stylometry_row_from_manifest(rman, gallery_dir, slug=rslug, rel_path="."))
            seen_slugs.add(rslug)

    p_root = os.path.join(gallery_dir, "p")
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
            if slug in seen_slugs:
                continue
            rows.append(_stylometry_row_from_manifest(man, pdir, slug=slug, rel_path=f"p/{slug}"))
            seen_slugs.add(slug)

    rows.sort(key=lambda r: (order_rank.get(r["slug"], len(order_rank) + 1), r["slug"]))
    doc: Dict[str, Any] = {
        "schema": CORPUS_COMPARISON_SCHEMA,
        "generated_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "provenance": "tool_generated",
        "count": len(rows),
        "metrics": METRIC_DEFINITIONS,
        "projects": rows,
    }
    doc = _sanitize_json_value(doc)

    target = out_path if out_path is not None else os.path.join(gallery_dir, "data", "corpus_comparison.json")
    if target:
        _safe_write_json(target, doc)
    return doc


def compute_from_gallery_config(
    config_path: str,
    *,
    out_path: Optional[str] = None,
    workers: Optional[int] = None,
) -> Dict[str, Any]:
    """Compute `leanre.corpus_comparison/1` directly from a `leanre_gallery.toml` config."""
    import tomllib

    abs_cfg = os.path.abspath(config_path)
    base_dir = os.path.dirname(abs_cfg)
    with open(abs_cfg, "rb") as f:
        cfg_doc = tomllib.load(f)

    rows: List[Dict[str, Any]] = []
    order_rank = {s: i for i, s in enumerate(_SHOWCASE_ORDER)}
    for proj in cfg_doc.get("projects") or []:
        slug = str(proj.get("slug") or "").strip()
        src_rel = str(proj.get("src_dir") or "").strip()
        if not slug or not src_rel:
            continue
        src_abs = os.path.join(base_dir, src_rel) if not os.path.isabs(src_rel) else src_rel
        if not os.path.isdir(src_abs):
            print(f"[stylometry] skipping {slug!r}: missing local corpus {src_rel!r}", file=sys.stderr)
            continue

        scan_db_rel = proj.get("leanre_db")
        scan_db_abs = (
            os.path.join(base_dir, str(scan_db_rel))
            if (scan_db_rel and not os.path.isabs(str(scan_db_rel)))
            else scan_db_rel
        )
        if scan_db_abs and not os.path.isfile(str(scan_db_abs)):
            scan_db_abs = None

        flirt_doc = None
        flirt_dir_rel = proj.get("flirt_dir")
        if flirt_dir_rel:
            fdir = os.path.join(base_dir, str(flirt_dir_rel)) if not os.path.isabs(str(flirt_dir_rel)) else str(flirt_dir_rel)
            t1_sum = os.path.join(fdir, "tier1_summary.json")
            if os.path.isfile(t1_sum) and not os.path.islink(t1_sum):
                try:
                    with open(t1_sum, "r", encoding="utf-8") as f:
                        flirt_doc = json.load(f)
                except (OSError, json.JSONDecodeError):
                    pass

        is_root = bool(proj.get("root", False))
        rel_path = "." if is_root else f"p/{slug}"
        has_kernel = bool(proj.get("kernel_db") or proj.get("ndjson_path"))
        has_emb = bool(proj.get("embedding_2d")) or True
        row = compute_project_stylometry(
            src_dir=src_abs,
            scan_db=str(scan_db_abs) if scan_db_abs else None,
            flirt_summary=flirt_doc,
            slug=slug,
            title=str(proj.get("title") or slug),
            path=rel_path,
            license_label=str(proj.get("license") or "Unknown"),
            category=str(proj.get("category") or "unknown"),
            has_kernel_export=has_kernel,
            has_embedding_2d=has_emb,
            workers=workers,
        )
        rows.append(row)

    rows.sort(key=lambda r: (order_rank.get(r["slug"], len(order_rank) + 1), r["slug"]))
    doc: Dict[str, Any] = {
        "schema": CORPUS_COMPARISON_SCHEMA,
        "generated_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "provenance": "tool_generated",
        "count": len(rows),
        "metrics": METRIC_DEFINITIONS,
        "projects": rows,
    }
    doc = _sanitize_json_value(doc)
    if out_path:
        _safe_write_json(out_path, doc)
    return doc


def _add_cli_args(ap: argparse.ArgumentParser) -> None:
    ap.add_argument("src_dirs", nargs="*", help="Optional Lean source director(ies) to measure directly")
    ap.add_argument("--gallery-dir", default=None, help="Read manifests from a built gallery directory")
    ap.add_argument("--config", default=None, help="Read project definitions from leanre_gallery.toml")
    ap.add_argument("--out", default=None, help="Output JSON path (default: <gallery-dir>/data/corpus_comparison.json or stdout)")
    ap.add_argument("--workers", type=int, default=None, help="Parallel worker count")


def _cmd_stylometry(args: argparse.Namespace) -> int:
    if args.gallery_dir:
        doc = build_corpus_comparison(args.gallery_dir, out_path=args.out)
    elif args.config:
        doc = compute_from_gallery_config(args.config, out_path=args.out, workers=args.workers)
    elif args.src_dirs:
        rows: List[Dict[str, Any]] = []
        for sdir in args.src_dirs:
            slug = re.sub(r"[^a-z0-9-]+", "-", os.path.basename(os.path.abspath(sdir)).lower()).strip("-") or "project"
            rows.append(
                compute_project_stylometry(
                    src_dir=sdir,
                    slug=slug,
                    title=os.path.basename(os.path.abspath(sdir)),
                    path=f"p/{slug}",
                    workers=args.workers,
                )
            )
        doc = _sanitize_json_value({
            "schema": CORPUS_COMPARISON_SCHEMA,
            "generated_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "provenance": "tool_generated",
            "count": len(rows),
            "metrics": METRIC_DEFINITIONS,
            "projects": rows,
        })
        if args.out:
            _safe_write_json(args.out, doc)
    else:
        print("error: stylometry requires --gallery-dir, --config, or at least one <src_dir>", file=sys.stderr)
        return 2

    if not args.out:
        print(json.dumps(doc, indent=2, sort_keys=True, ensure_ascii=False))
    else:
        print(json.dumps({"schema": doc["schema"], "count": doc["count"], "out": os.path.basename(args.out)}, indent=2, sort_keys=True))
    return 0


def register_cli(sub: Any, dest: str = "stylometry_func") -> argparse.ArgumentParser:
    p = sub.add_parser("stylometry", help="Deterministic cross-proof stylometry & corpus comparison JSON")
    _add_cli_args(p)
    p.set_defaults(**{dest: _cmd_stylometry})
    return p


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        prog="leanre-stylometry",
        description="Deterministic cross-proof stylometry (`leanre.corpus_comparison/1`).",
    )
    _add_cli_args(ap)
    args = ap.parse_args(argv)
    return _cmd_stylometry(args)


if __name__ == "__main__":
    sys.exit(main())
