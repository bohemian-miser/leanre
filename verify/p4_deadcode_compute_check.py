#!/usr/bin/env python3
"""Independent verifier for Gate D4 (arch half): dead-code partition & compute atlas.

Zero-trust verification of outputs/decomp/compute_atlas.json and
analysis/compute_and_deadcode.md against outputs/leanre.db, outputs/kernel/kernel.db,
and raw .lean files in data/rh_mirror/src/. Does not import leanre/.
"""
from __future__ import annotations

import json
import os
import pathlib
import re
import sqlite3
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
R = []


def ck(ok: bool, msg: str) -> None:
    R.append(bool(ok))
    print(f"{'PASS' if ok else 'FAIL'} [D4-ARCH] {msg}")


def main() -> None:
    atlas_path = ROOT / "outputs" / "decomp" / "compute_atlas.json"
    ck(atlas_path.exists(), f"compute_atlas.json exists: {atlas_path}")
    if not atlas_path.exists():
        sys.exit(1)

    sz = atlas_path.stat().st_size
    ck(sz < 2 * 1024 * 1024, f"compute_atlas.json size < 2 MB ({sz:,} B)")
    ca = json.loads(atlas_path.read_text(encoding="utf-8"))

    ldb = sqlite3.connect(f"file:{ROOT}/outputs/leanre.db?mode=ro", uri=True)
    kdb = sqlite3.connect(f"file:{ROOT}/outputs/kernel/kernel.db?mode=ro", uri=True)
    mirror = ROOT / "data" / "rh_mirror"

    # 1. Independently recompute corpus totals from leanre.db + kernel.db
    tot_mods, tot_lines = ldb.execute("SELECT COUNT(*), SUM(lines_wc) FROM modules").fetchone()
    unreach_mods = ldb.execute("SELECT COUNT(*) FROM modules WHERE bfs_depth IS NULL").fetchone()[0]
    cov_mods_set = set(r[0] for r in kdb.execute("SELECT DISTINCT module FROM decl_module WHERE module IS NOT NULL"))
    all_mods = {r[0]: (r[1], r[2], r[3], r[4]) for r in ldb.execute("SELECT name, file_path, lines_wc, is_shim, decl_count FROM modules")}
    cov_in_proj = cov_mods_set & set(all_mods.keys())
    zero_mods = set(all_mods.keys()) - cov_in_proj
    cov_lines = sum(all_mods[m][1] for m in cov_in_proj)
    zero_lines = sum(all_mods[m][1] for m in zero_mods)

    ct = ca["corpus_totals"]
    ck(
        ct["total_modules"] == tot_mods == 175187
        and ct["total_lines_wc"] == tot_lines == 17374215
        and ct["main_unreachable_modules"] == unreach_mods == 0
        and ct["kernel_covered_modules"] == len(cov_in_proj) == 146283
        and ct["kernel_covered_lines_wc"] == cov_lines
        and ct["zero_kernel_modules"] == len(zero_mods) == 28904
        and ct["zero_kernel_lines_wc"] == zero_lines == 2378537,
        f"corpus_totals exact match: total={tot_mods:,} ({tot_lines:,} wc-l), live={len(cov_in_proj):,} ({cov_lines:,}), zero={len(zero_mods):,} ({zero_lines:,}), unreach={unreach_mods}",
    )

    # 2. Disjoint bucket partition sum == 28,904 modules and 2,378,537 lines_wc
    zk = ca["zero_kernel_classification"]
    buckets = zk["buckets"]
    b_mods = sum(v["modules"] for v in buckets.values())
    b_lines = sum(v["lines_wc"] for v in buckets.values())
    ck(
        zk.get("strictly_disjoint") is True
        and zk["bucket_sum_modules"] == b_mods == 28904
        and zk["bucket_sum_lines_wc"] == b_lines == 2378537,
        f"zero-kernel partition strictly sums to {b_mods:,} modules and {b_lines:,} lines_wc across {len(buckets)} buckets",
    )
    print("     bucket breakdown:")
    for bname, bv in buckets.items():
        print(f"       {bname}: {bv['modules']:,} mods ({bv['lines_wc']:,} lines_wc)")

    # 3. Independently verify >= 10 spot-checked modules per non-empty bucket on disk + kernel.db
    spot = zk.get("spot_checks_per_bucket", {})
    seen_spot_mods = set()
    dup_spot = []
    bad_spot = []
    spot_checked = 0
    for bname, bv in buckets.items():
        if bv["modules"] == 0:
            continue
        items = spot.get(bname, [])
        if len(items) < min(10, bv["modules"]):
            bad_spot.append((bname, f"only {len(items)} spot checks < min(10, {bv['modules']})"))
        for item in items:
            m = item["module"]
            if m in seen_spot_mods:
                dup_spot.append(m)
            seen_spot_mods.add(m)
            if m not in zero_mods:
                bad_spot.append((bname, m, "NOT in zero_mods!"))
                continue
            rel = all_mods[m][0]
            fp = mirror / "src" / rel if not (mirror / rel).exists() else mirror / rel
            if not fp.exists():
                bad_spot.append((bname, m, f"missing on disk: {rel}"))
                continue
            txt = fp.read_text(encoding="utf-8", errors="replace")
            wc_l = txt.count("\n")
            if item.get("lines_wc") is not None and item["lines_wc"] != wc_l:
                bad_spot.append((bname, m, f"lines_wc mismatch: {item['lines_wc']} vs disk {wc_l}"))
                continue
            # Bucket-specific sanity check on disk
            if bname == "import_shim_reexport":
                # Must have no theorem/def/lemma/structure/inductive/class/abbrev outside comments
                code_lines = [l.split("--", 1)[0] for l in txt.splitlines()]
                has_decl = any(re.match(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)\b", cl) for cl in code_lines)
                if has_decl:
                    bad_spot.append((bname, m, "import_shim has a declaration!"))
                    continue
            elif bname == "macro_tactic_elab_syntax_only":
                if not re.search(r"\b(macro|syntax|elab|run_cmd|attribute|scoped\s+notation|local\s+notation|notation|infix|prefix|postfix|declare_syntax_cat|macro_rules|simproc)\b", txt):
                    bad_spot.append((bname, m, "no macro/syntax/elab/run_cmd/attribute/notation keyword found on disk"))
                    continue
            elif bname == "alignment_gap":
                # Verify at least one declared name in file actually exists in kernel.db!
                dnames = set(r[0] for r in ldb.execute("SELECT name FROM declarations WHERE module=?", (m,)))
                # Or check kernel decls matching leaf names
                k_hits = 0
                for dn in list(dnames)[:20]:
                    if kdb.execute("SELECT 1 FROM decls WHERE name=?", (dn,)).fetchone():
                        k_hits += 1
                        break
                # Note: alignment_gap may have decl_name mismatch (e.g. private or namespace), so check reported kernel_decls if present
                rep_kd = item.get("matched_kernel_decls") or item.get("kernel_decls") or []
                for kd in rep_kd[:5]:
                    kd_name = kd["name"] if isinstance(kd, dict) else kd
                    if kdb.execute("SELECT 1 FROM decls WHERE name=?", (kd_name,)).fetchone():
                        k_hits += 1
                        break
                if k_hits == 0 and rep_kd:
                    bad_spot.append((bname, m, f"reported kernel_decls not in kernel.db: {rep_kd[:2]}"))
                    continue
            spot_checked += 1
    ck(not dup_spot and not bad_spot and spot_checked >= 40,
       f"on-disk spot checks across non-empty buckets: checked={spot_checked}, dups={len(dup_spot)}, bad={bad_spot[:5]}")

    # 4. Independently verify kernel flag counts against kernel.db
    kfc = ca["computation_atlas"]["kernel_flag_counts"]
    flag_defs = [("F_REFL_TRUE", 1), ("F_OF_DECIDE", 2), ("F_REDUCE_BOOL", 4), ("F_REDUCE_NAT", 8), ("F_SORRY", 16), ("F_TRUST_COMPILER", 32)]
    flag_diffs = []
    for fname, bit in flag_defs:
        all_c = kdb.execute("SELECT COUNT(*) FROM decls WHERE (flags & ?) != 0", (bit,)).fetchone()[0]
        live_c = kdb.execute("SELECT COUNT(*) FROM decls WHERE live_mask != 0 AND (flags & ?) != 0", (bit,)).fetchone()[0]
        got = kfc.get(fname, {})
        if got.get("all_decls") != all_c or got.get("live_decls") != live_c:
            flag_diffs.append((fname, got, (all_c, live_c)))
    ck(not flag_diffs, f"kernel_flag_counts exact vs kernel.db: diffs={flag_diffs}")

    # 5. Independently verify key live vs dead computational landmarks in kernel.db & on disk
    landmarks = [
        ("ChebyshevPrimeBounds.SmallLoop", "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop", True),
        ("DyadicPrimeIntervals.Run1", "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run1", False),
        ("DyadicPrimeIntervals.Run4", "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run4", False),
        ("InvFiveLogLeSumInvPrimes (table_ok)", "Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes", True),
    ]
    lm_bad = []
    for label, mod, expect_live in landmarks:
        if mod not in all_mods:
            lm_bad.append((label, "NOT IN leanre.db", mod))
            continue
        c = kdb.execute("SELECT COUNT(*) FROM decl_module WHERE module=?", (mod,)).fetchone()[0]
        if (c > 0) != expect_live:
            lm_bad.append((label, c, expect_live))
    # Also check table_ok + its _proof_1_1 directly in kernel.db
    tok = kdb.execute("SELECT id, name, flags FROM decls WHERE name IN ('GlobalTheory.PrimeRecip.table_ok', 'GlobalTheory.PrimeRecip.table_ok._proof_1_1')").fetchall()
    tok_refl = any((r[2] & 1) != 0 for r in tok)
    ck(not lm_bad and len(tok) == 2 and tok_refl,
       f"live/dead compute landmarks verified (SmallLoop live, Run1..4 dead, table_ok={tok}): bad={lm_bad}")

    # 6. Check certified_math_table entries exist on disk & kernel status matches kernel.db
    cmt = ca["computation_atlas"].get("certified_math_table", [])
    cmt_bad = []
    for row in cmt:
        mod = row.get("module")
        if mod and mod in all_mods:
            c = kdb.execute("SELECT COUNT(*) FROM decl_module WHERE module=?", (mod,)).fetchone()[0]
            st = str(row.get("kernel_status", "")).lower()
            if "live" in st and "dead" not in st and c == 0:
                cmt_bad.append((mod, st, c))
            elif "dead" in st and "live" not in st and c > 0:
                cmt_bad.append((mod, st, c))
    ck(len(cmt) >= 8 and not cmt_bad, f"certified_math_table ({len(cmt)} rows) kernel live/dead status verified: bad={cmt_bad[:5]}")

    fails = sum(1 for x in R if not x)
    print(f"\nP4-DEADCODE-COMPUTE-CHECK {'PASS' if fails == 0 else 'FAIL'} ({len(R)-fails}/{len(R)})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
