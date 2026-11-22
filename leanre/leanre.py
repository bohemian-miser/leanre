#!/usr/bin/env python3
"""leanre — "Ghidra for Lean": reverse-engineering & forensics CLI for large Lean 4 proof trees.

Python 3.9+ stdlib only (multiprocessing + sqlite3 + sanctioned 7zz for .zst streaming).

Subcommands:
  scan       Parallel scan of all .lean files -> SQLite modules/edges/decls/horn/forensics
  ndjson     Streaming parse of Lean 4 export NDJSON v3.1.0 (.ndjson / .zst / .gz) -> SQLite TCB
  forensics  Deep hotspot analysis, BinDiff v1 snapshot, workbench_bundle.json & forensics_dossier.md
  all        Run scan + ndjson + forensics end-to-end into an output directory
  diff       Compare two forensics_report.json / bindiff_v1 snapshots
  kernel     Native Rust kernel-exact graph extractor (solution.ndjson.zst -> kernel.db)
  sighash    Normalized signature hashes (kernel k1n/k1a & source s1n/s1t/s1a)
  flirt      FLIRT-for-Lean 3-tier fingerprinting (tier1 / tier2 / tier3)
  annot      Portable JSONL annotation packs (validate/export/import/merge/diff/layers/reanchor)
  decompile  Proof decompiler: contracts, unfolding, Horn graph, dominator spine & schema validation
  trim       Read-only virtual proof stripper & disjoint bloat waterfall
"""
from __future__ import annotations

import argparse
import json
import os
import sys

# Ensure sibling modules resolve cleanly regardless of cwd
_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import annot
import decompile.cli as decompile_cli
import kernel
import sighash
import trim
from forensics import diff_snapshots, run_forensics
from ndjson import run_ndjson_to_db
from scanner import run_scan


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        prog="leanre",
        description="Ghidra for Lean: static reverse-engineering & TCB forensics CLI",
    )
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_scan = sub.add_parser("scan", help="Parallel scan of a Lean 4 source tree")
    p_scan.add_argument("src_dir", help="Path to Lean src/ directory")
    p_scan.add_argument("--out-db", required=True, help="Path to output SQLite DB (e.g. outputs/leanre.db)")
    p_scan.add_argument("--out-json", default=None, help="Optional path to write scan JSON summary")
    p_scan.add_argument("--root", default="Main", help="Root module name (default: Main)")
    p_scan.add_argument("--workers", type=int, default=None, help="Worker process count")

    p_nd = sub.add_parser("ndjson", help="Stream-parse Lean 4 NDJSON v3.1.0 export (.zst/.gz/.ndjson)")
    p_nd.add_argument("ndjson_path", help="Path to challenge.ndjson.zst or solution.ndjson.zst")
    p_nd.add_argument("--out-db", required=True, help="Path to SQLite DB (e.g. outputs/leanre.db)")
    p_nd.add_argument("--out-json", default=None, help="Optional path to write TCB stats JSON")

    p_for = sub.add_parser("forensics", help="Generate deep forensics report, workbench bundle & dossier")
    p_for.add_argument("--db", required=True, help="Path to populated outputs/leanre.db")
    p_for.add_argument("--out-report", required=True, help="Output forensics_report.json")
    p_for.add_argument("--out-bundle", required=True, help="Output workbench_bundle.json")
    p_for.add_argument("--out-dossier", required=True, help="Output forensics_dossier.md")

    p_all = sub.add_parser("all", help="Run full pipeline: scan + ndjson + forensics")
    p_all.add_argument("--src", required=True, help="Path to Lean src/ directory")
    p_all.add_argument("--ndjson", required=True, help="Path to challenge.ndjson.zst")
    p_all.add_argument("--out-dir", required=True, help="Output directory (e.g. outputs/)")
    p_all.add_argument("--root", default="Main", help="Root module name (default: Main)")
    p_all.add_argument("--workers", type=int, default=None, help="Worker process count")

    p_diff = sub.add_parser("diff", help="Compare two BinDiff v1 snapshots / forensics_report.json files")
    p_diff.add_argument("snap_a", help="Baseline snapshot JSON")
    p_diff.add_argument("snap_b", help="Target snapshot JSON")
    p_diff.add_argument("--out-json", default=None, help="Optional output path for diff JSON")

    annot.register_cli(sub)
    kernel.register_cli(sub)
    decompile_cli.register_cli(sub)
    trim.register_cli(sub, dest="trim_func")
    sub.add_parser("sighash", help="Normalized signature hashes (kernel/build-lexicon/source)")
    sub.add_parser("flirt", help="FLIRT-for-Lean fingerprinting (tier1/tier2/tier3/cluster)")

    raw_argv = list(sys.argv[1:] if argv is None else argv)
    if raw_argv and raw_argv[0] == "sighash":
        return int(sighash._main(raw_argv[1:]))
    if raw_argv and raw_argv[0] == "flirt":
        rest = raw_argv[1:]
        if not rest or rest[0] in ("-h", "--help"):
            print("usage: leanre flirt {tier1,tier2,tier3,cluster} ...")
            return 0
        flirt_dir = os.path.join(_HERE, "flirt")
        if flirt_dir not in sys.path:
            sys.path.insert(0, flirt_dir)
        tier, tier_args = rest[0], rest[1:]
        if tier == "tier1":
            from flirt import tier1 as _t1
            return int(_t1.main(tier_args))
        if tier == "tier2":
            from flirt import tier2 as _t2
            return int(_t2.main(tier_args))
        if tier == "tier3":
            from flirt import tier3 as _t3
            return int(_t3.main(tier_args))
        if tier == "cluster":
            from flirt import cluster as _cl
            return int(_cl.main(tier_args))
        print(f"leanre flirt: unknown tier {tier!r} (expected tier1, tier2, tier3, or cluster)", file=sys.stderr)
        return 2

    args = ap.parse_args(argv)

    if args.cmd == "kernel":
        return int(args.kernel_func(args))

    if args.cmd == "decompile":
        return int(args.decompile_func(args))

    if args.cmd == "trim":
        return int(args.trim_func(args))

    if args.cmd == "annot":
        try:
            return args.annot_func(args)
        except annot.PackError as e:
            for issue in e.issues:
                print(issue, file=sys.stderr)
            return 1

    if args.cmd == "scan":
        os.makedirs(os.path.dirname(os.path.abspath(args.out_db)), exist_ok=True)
        stats = run_scan(args.src_dir, args.out_db, root_module=args.root, workers=args.workers)
        if args.out_json:
            os.makedirs(os.path.dirname(os.path.abspath(args.out_json)), exist_ok=True)
            with open(args.out_json, "w", encoding="utf-8") as f:
                json.dump(stats, f, indent=2, ensure_ascii=False)
        return 0

    if args.cmd == "ndjson":
        os.makedirs(os.path.dirname(os.path.abspath(args.out_db)), exist_ok=True)
        stats = run_ndjson_to_db(args.ndjson_path, args.out_db)
        if args.out_json:
            os.makedirs(os.path.dirname(os.path.abspath(args.out_json)), exist_ok=True)
            with open(args.out_json, "w", encoding="utf-8") as f:
                json.dump(stats, f, indent=2, ensure_ascii=False)
        return 0

    if args.cmd == "forensics":
        rep = run_forensics(args.db, args.out_report, args.out_bundle, args.out_dossier)
        if not rep["meta"]["acceptance_gates"]["all_passed"]:
            print("WARNING: one or more acceptance gates did not pass!", file=sys.stderr)
            return 2
        return 0

    if args.cmd == "all":
        os.makedirs(args.out_dir, exist_ok=True)
        db_path = os.path.join(args.out_dir, "leanre.db")
        report_path = os.path.join(args.out_dir, "forensics_report.json")
        bundle_path = os.path.join(args.out_dir, "workbench_bundle.json")
        dossier_path = os.path.join(args.out_dir, "forensics_dossier.md")
        run_scan(args.src, db_path, root_module=args.root, workers=args.workers)
        run_ndjson_to_db(args.ndjson, db_path)
        rep = run_forensics(db_path, report_path, bundle_path, dossier_path)
        if not rep["meta"]["acceptance_gates"]["all_passed"]:
            print("WARNING: acceptance gate failure:", json.dumps(rep["meta"]["acceptance_gates"], indent=2), file=sys.stderr)
            return 2
        return 0

    if args.cmd == "diff":
        with open(args.snap_a, "r", encoding="utf-8") as f:
            a = json.load(f)
        with open(args.snap_b, "r", encoding="utf-8") as f:
            b = json.load(f)
        res = diff_snapshots(a, b)
        txt = json.dumps(res, indent=2, ensure_ascii=False)
        if args.out_json:
            with open(args.out_json, "w", encoding="utf-8") as f:
                f.write(txt)
        else:
            print(txt)
        return 0

    return 1


if __name__ == "__main__":
    sys.exit(main())
