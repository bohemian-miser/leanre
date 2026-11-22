#!/usr/bin/env python3
"""F2 independent verification script (verifier-owned).

Verifies outputs/flirt/tier2.db, outputs/flirt/tier2_corpora.json,
outputs/flirt/tier2_summary.json, and data/corpora/ without importing leanre/flirt/.
"""
from __future__ import annotations

import collections
import json
import os
import random
import sqlite3
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = []


def ck(ok, msg):
    R.append(bool(ok))
    print(f"{'PASS' if ok else 'FAIL'} [F2] {msg}")


def main():
    db = sqlite3.connect(f"file:{ROOT}/outputs/flirt/tier2.db?mode=ro", uri=True)
    corp_json = json.load(open(os.path.join(ROOT, "outputs", "flirt", "tier2_corpora.json")))
    summ = json.load(open(os.path.join(ROOT, "outputs", "flirt", "tier2_summary.json")))

    # 1. Verify pinned commits, mathlib pin vs rh_mirror/lake-manifest.json, and LICENSE files
    lm = json.load(open(os.path.join(ROOT, "data", "rh_mirror", "lake-manifest.json")))
    lt = open(os.path.join(ROOT, "data", "rh_mirror", "lean-toolchain")).read().strip()
    pinned_pkgs = {p["name"]: p.get("rev") for p in lm.get("packages", [])}
    print(f"     rh_mirror lean-toolchain={lt!r}, lake-manifest mathlib={pinned_pkgs.get('mathlib')}, batteries={pinned_pkgs.get('batteries')}")

    corpora_rows = db.execute("SELECT repo, url, commit_sha, license, lean_toolchain, lexicon_id, lean_files, decls FROM corpora ORDER BY repo").fetchall()
    req_repos = {"mathlib4", "PrimeNumberTheoremAnd", "FLT", "carleson"}
    found_repos = {r[0] for r in corpora_rows}
    ck(req_repos.issubset(found_repos), f"required corpora present: {sorted(found_repos)}")

    sha_bad = []
    lic_bad = []
    for repo, url, sha, lic, tc, lex_id, lf, nd in corpora_rows:
        rdir = os.path.join(ROOT, "data", "corpora", repo)
        if not os.path.isdir(rdir):
            sha_bad.append((repo, "missing dir"))
            continue
        actual_sha = subprocess.run(["git", "-C", rdir, "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
        if actual_sha != sha:
            sha_bad.append((repo, sha, actual_sha))
        # Check LICENSE file on disk
        lic_files = [f for f in os.listdir(rdir) if f.upper().startswith(("LICENSE", "LICENCE", "COPYING"))]
        if not lic_files or not lic:
            lic_bad.append((repo, lic, lic_files))
        if repo == "mathlib4" and pinned_pkgs.get("mathlib"):
            ck(actual_sha == pinned_pkgs["mathlib"], f"mathlib4 commit {actual_sha[:12]} matches rh_mirror/lake-manifest.json {pinned_pkgs['mathlib'][:12]}")
    ck(not sha_bad, f"all {len(corpora_rows)} corpora commit SHAs match `git rev-parse HEAD` on disk; mismatches={sha_bad}")
    ck(not lic_bad, f"all {len(corpora_rows)} corpora have recorded licenses + LICENSE file on disk; missing={lic_bad}")

    # Check tier2_corpora.json agrees with corpora table
    cj_map = {c.get("name", c.get("repo")): c.get("commit", c.get("commit_sha")) for c in (corp_json["corpora"] if isinstance(corp_json, dict) and "corpora" in corp_json else corp_json)}
    db_map = {r[0]: r[2] for r in corpora_rows}
    ck(cj_map == db_map, f"tier2_corpora.json SHAs match tier2.db corpora table ({len(db_map)} repos)")

    # 2. Independently recompute precision/recall/FPR from control_restate (joined to original corpus_sigs.n_tokens) and control_sigs!
    restate_rows = db.execute(
        "SELECT r.corpus_id, s.n_tokens, r.extracted, r.outcome_s1n, r.outcome_s1t, r.outcome_s1a "
        "FROM control_restate r JOIN corpus_sigs s ON s.id = r.corpus_id"
    ).fetchall()
    ck(len(restate_rows) >= 1000, f"control_restate has {len(restate_rows):,} synthetic held-out restatement trials")
    ctrl_rows = db.execute("SELECT control, variant, min_tokens, n, tp, fp, fn, precision, recall, fpr FROM controls").fetchall()
    ctrl_bad = []
    for ctrl, var, mt, n_rep, tp_rep, fp_rep, fn_rep, prec_rep, rec_rep, fpr_rep in ctrl_rows:
        if ctrl == "restate_selfmatch":
            col = {"s1n": 3, "s1t": 4, "s1a": 5}[var]
            sub = [r for r in restate_rows if r[1] >= mt]
            n_m = len(sub)
            tp_m = sum(1 for r in sub if r[col] == "tp")
            fp_m = sum(1 for r in sub if r[col] == "fp")
            fn_m = sum(1 for r in sub if r[col] in ("fn", "miss", "extract_fail"))
            # Check exact counts & rates
            if n_m != n_rep or tp_m != tp_rep or fp_m != fp_rep:
                ctrl_bad.append((ctrl, var, mt, (n_rep, tp_rep, fp_rep), (n_m, tp_m, fp_m)))
            else:
                exp_rec = tp_m / n_m if n_m else 0.0
                exp_prec = tp_m / (tp_m + fp_m) if (tp_m + fp_m) else 0.0
                if abs(exp_rec - (rec_rep or 0)) > 1e-6 or (prec_rep is not None and abs(exp_prec - prec_rep) > 1e-6):
                    ctrl_bad.append((ctrl, var, mt, "rate mismatch", (prec_rep, rec_rep), (exp_prec, exp_rec)))
        elif ctrl in ("neg_swap", "neg_perm"):
            cs_name = ctrl[4:] if db.execute("SELECT COUNT(*) FROM control_sigs WHERE control=?", (ctrl,)).fetchone()[0] == 0 else ctrl
            hcol = f"hit_{var}"
            n_m, fp_m = db.execute(
                f"SELECT COUNT(*), COALESCE(SUM({hcol}), 0) FROM control_sigs WHERE control=? AND n_tokens >= ?",
                (cs_name, mt),
            ).fetchone()
            exp_fpr = fp_m / n_m if n_m else 0.0
            if n_m != n_rep or fp_m != fp_rep or abs(exp_fpr - (fpr_rep or 0)) > 1e-9:
                ctrl_bad.append((ctrl, var, mt, (n_rep, fp_rep, fpr_rep), (n_m, fp_m, exp_fpr)))
    ck(not ctrl_bad, f"recomputed all {len(ctrl_rows)} rows in controls table from raw control_restate/control_sigs; mismatches={ctrl_bad[:5]}")

    # 3. Evidence completeness on EVERY row of matches and kernel_matches
    bad_ev = db.execute(
        "SELECT COUNT(*) FROM matches WHERE sighash='' OR repo='' OR commit_sha='' OR license='' OR corpus_name='' OR provenance!='L'"
    ).fetchone()[0]
    n_matches = db.execute("SELECT COUNT(*) FROM matches").fetchone()[0]
    ck(n_matches > 0 and bad_ev == 0, f"all {n_matches:,} source matches carry sighash/repo/commit_sha/license/corpus_name/provenance='L' (bad={bad_ev})")

    # Check grade/variant breakdown
    grade_br = db.execute("SELECT variant, grade, COUNT(*) FROM matches GROUP BY variant, grade ORDER BY 1, 2").fetchall()
    print("     matches by (variant, grade):", grade_br)

    # 4. Spot-check 30 random strong source matches directly against data/rh_mirror + data/corpora + sighash
    rnd = random.Random(20261122)
    strong = db.execute(
        "SELECT proof_id, proof_module, proof_line, proof_name, variant, sighash, repo, commit_sha, corpus_name, corpus_module, corpus_line, corpus_sig_text "
        "FROM matches_view WHERE grade='strong'"
    ).fetchall()
    ck(len(strong) > 0, f"strong theorem source matches count = {len(strong):,}")
    spot = rnd.sample(strong, min(30, len(strong)))
    spot_bad = []
    for row in spot:
        pid, pmod, pln, pname, var, sh, repo, sha, cname, cmod, cln, csig = row
        # Verify proof_sigs and corpus_sigs actually have that exact sighash
        p_sh = db.execute(f"SELECT {var} FROM proof_sigs WHERE id=?", (pid,)).fetchone()[0]
        c_sh = db.execute(f"SELECT {var} FROM corpus_sigs WHERE repo=? AND module=? AND name=? AND line_no=?", (repo, cmod, cname, cln)).fetchone()
        # Verify proof file exists on disk and contains leaf name near line
        pfile = os.path.join(ROOT, "data", "rh_mirror", "src", pmod.replace(".", "/") + ".lean")
        if not os.path.exists(pfile):
            spot_bad.append((pmod, "missing proof file"))
            continue
        plines = open(pfile, encoding="utf-8", errors="replace").readlines()
        win = "".join(plines[max(0, pln - 3):min(len(plines), pln + 5)])
        leaf = pname.split(".")[-1]
        if p_sh != sh or c_sh is None or c_sh[0] != sh or leaf not in win:
            spot_bad.append((pmod, pln, pname, var, p_sh == sh, c_sh, leaf in win))
    ck(not spot_bad, f"on-disk spot check of {len(spot)} strong source matches (sighash equality + proof file:line): mismatches={spot_bad[:3]}")

    # 5. Kernel-exact matches check against outputs/kernel/kernel.db
    n_km = db.execute("SELECT COUNT(*) FROM kernel_matches").fetchone()[0]
    kdb_path = os.path.join(ROOT, "outputs", "kernel", "kernel.db")
    if n_km > 0 and os.path.exists(kdb_path):
        kdb = sqlite3.connect(f"file:{kdb_path}?mode=ro", uri=True)
        km_bad_ev = db.execute(
            "SELECT COUNT(*) FROM kernel_matches WHERE sighash='' OR lib_const_name='' OR provenance!='L' OR (lib_origin LIKE 'library_corpus%' AND (lib_repo IS NULL OR lib_commit_sha IS NULL))"
        ).fetchone()[0]
        ck(km_bad_ev == 0, f"all {n_km:,} kernel_matches carry full evidence + provenance='L' (bad={km_bad_ev})")
        km_rows = db.execute("SELECT const_name, variant, sighash, lib_const_name FROM kernel_matches").fetchall()
        km_spot = rnd.sample(km_rows, min(50, len(km_rows)))
        km_mism = []
        for cname, var, sh, lname in km_spot:
            col = "sighash" if var == "k1n" else "sighash_anon"
            r1 = kdb.execute(f"SELECT {col} FROM consts WHERE name=?", (cname,)).fetchone()
            r2 = kdb.execute(f"SELECT {col} FROM consts WHERE name=?", (lname,)).fetchone()
            if r1 is None or r2 is None or r1[0] != sh or r2[0] != sh:
                km_mism.append((cname, lname, var, sh, r1, r2))
        ck(not km_mism, f"cross-checked {len(km_spot)} sampled kernel_matches directly against outputs/kernel/kernel.db consts: mismatches={km_mism[:3]}")
        km_br = db.execute("SELECT variant, is_aux, COUNT(*) FROM kernel_matches GROUP BY variant, is_aux ORDER BY 1,2").fetchall()
        print("     kernel_matches by (variant, is_aux):", km_br)
    else:
        print(f"     note: kernel_matches rows={n_km}, kernel.db exists={os.path.exists(kdb_path)}")

    # 6. No raw proof_sigs sig_text column (Guardrail 3)
    pcols = [r[1] for r in db.execute("PRAGMA table_info(proof_sigs)")]
    ck("sig_text" not in pcols and "body" not in pcols, f"proof_sigs stores no raw proof source text (cols={pcols})")

    fails = sum(1 for x in R if not x)
    print(f"\nF2-CHECK {'PASS' if fails == 0 else 'FAIL'} ({len(R)-fails}/{len(R)})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
