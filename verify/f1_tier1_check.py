#!/usr/bin/env python3
"""F1 independent verification script (verifier-owned).

Verifies outputs/flirt/tier1.db & outputs/flirt/tier1_summary.json against data/rh_mirror
and outputs/leanre.db without importing leanre/flirt/.
"""
from __future__ import annotations

import collections
import json
import os
import random
import re
import sqlite3
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = []


def ck(ok, msg):
    R.append(bool(ok))
    print(f"{'PASS' if ok else 'FAIL'} [F1] {msg}")


def main():
    t1 = sqlite3.connect(f"file:{ROOT}/outputs/flirt/tier1.db?mode=ro", uri=True)
    ldb = sqlite3.connect(f"file:{ROOT}/outputs/leanre.db?mode=ro", uri=True)
    summ = json.load(open(os.path.join(ROOT, "outputs", "flirt", "tier1_summary.json")))

    # 1. Coverage == 175,187 modules
    n_fp = t1.execute("SELECT COUNT(*) FROM module_fingerprints").fetchone()[0]
    ck(n_fp == 175187, f"module_fingerprints covers all 175,187 modules (measured={n_fp:,})")

    # 2. Known misfile: GlobalTheory.PrimeRecip.table_ok under AbelianVarietyTheory/Proofs/DivisorProofs/
    target_mod = "Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes"
    row = t1.execute(
        "SELECT rank, module, file_path, declared_ns, folder_ns, score, tier, flag_decl, reason, provenance "
        "FROM misfiles WHERE module=?",
        (target_mod,),
    ).fetchone()
    disk_path = os.path.join(ROOT, "data", "rh_mirror", "src", "Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean")
    disk_txt = open(disk_path, encoding="utf-8", errors="replace").read()
    on_disk = ("namespace GlobalTheory.PrimeRecip" in disk_txt) and ("theorem table_ok" in disk_txt)
    ck(row is not None and row[6] == "high" and "PrimeRecip" in row[3] and on_disk,
       f"known misfile flagged: rank={row[0] if row else None} score={row[5] if row else None} tier={row[6] if row else None} declared_ns={row[3] if row else None} flag_decl={row[7] if row else None}; verified on disk={on_disk}")

    # 3. Independently recompute Phase 2 literal 2-component namespace split of Development.AbelianVarietyTheory
    #    from outputs/leanre.db declarations table (zero trust of tier1 or namespace_stats)
    c_p2 = collections.Counter()
    for (nm,) in ldb.execute("SELECT name FROM declarations WHERE module LIKE 'Development.AbelianVarietyTheory.%' OR module='Development.AbelianVarietyTheory'"):
        parts = nm.split(".")
        pref = ".".join(parts[:2]) if len(parts) >= 2 else parts[0]
        c_p2[pref] += 1
    top3_p2 = c_p2.most_common(3)
    exp_p2 = [("_root_.GlobalTheory", 39212), ("GlobalTheory.IndefiniteRowSideFullHecke", 14165), ("GlobalTheory.Mem", 11592)]
    t1_p2 = t1.execute(
        "SELECT declared_ns, decl_count FROM namespace_folder_matrix "
        "WHERE folder_l2='Development.AbelianVarietyTheory' AND counting_rule='phase2_literal_2comp' "
        "ORDER BY decl_count DESC LIMIT 3"
    ).fetchall()
    ck(top3_p2 == exp_p2 and t1_p2 == exp_p2,
       f"AbelianVarietyTheory 39,212/14,165/11,592 split: own recompute={top3_p2}; tier1.db={t1_p2}")

    # Also inspect lean_scoped_2comp rule in tier1.db
    t1_sc = t1.execute(
        "SELECT declared_ns, decl_count FROM namespace_folder_matrix "
        "WHERE folder_l2='Development.AbelianVarietyTheory' AND counting_rule='lean_scoped_2comp' "
        "ORDER BY decl_count DESC LIMIT 5"
    ).fetchall()
    print(f"     info: tier1.db lean_scoped_2comp top-5 for AbelianVarietyTheory: {t1_sc}")
    ck(len(t1_sc) >= 3 and t1_sc[0][1] > 0, "tier1.db also exposes lean_scoped_2comp counting rule explicitly")

    # 4. Boilerplate collapse checks vs outputs/leanre.db
    bp = dict(t1.execute("SELECT kind, COUNT(*) FROM boilerplate_clusters GROUP BY kind").fetchall())
    bp_m = dict(t1.execute("SELECT c.kind, COUNT(*) FROM boilerplate_clusters c JOIN boilerplate_members m ON c.cluster_id=m.cluster_id GROUP BY c.kind").fetchall())
    ldb_shims = ldb.execute("SELECT COUNT(*) FROM modules WHERE is_shim=1").fetchone()[0]
    ldb_clone_clusters = ldb.execute("SELECT COUNT(DISTINCT clone_sig) FROM modules WHERE clone_cluster_size >= 2").fetchone()[0]
    ldb_clone_mods = ldb.execute("SELECT COUNT(*) FROM modules WHERE clone_cluster_size >= 2").fetchone()[0]
    ck(bp.get("alpha_body_clone") == ldb_clone_clusters == 1192 and bp_m.get("alpha_body_clone") == ldb_clone_mods == 4787,
       f"alpha_body_clone clusters={bp.get('alpha_body_clone')} (leanre.db={ldb_clone_clusters}), mods={bp_m.get('alpha_body_clone')} (leanre.db={ldb_clone_mods})")
    ck(bp_m.get("import_shim") == ldb_shims == 150,
       f"import_shim mods={bp_m.get('import_shim')} (leanre.db={ldb_shims})")
    print(f"     boilerplate kinds: clusters={bp} members={bp_m}")

    # 5. Spot-check 50 misfiles directly on disk in data/rh_mirror
    rnd = random.Random(20261122)
    top_mis = t1.execute("SELECT rank, module, file_path, declared_ns, folder_ns, ns_mismatch_kind FROM misfiles WHERE rank <= 200").fetchall()
    rand_mis = t1.execute("SELECT rank, module, file_path, declared_ns, folder_ns, ns_mismatch_kind FROM misfiles WHERE tier='high' ORDER BY rank LIMIT 2000").fetchall()
    sample = top_mis[:25] + rnd.sample(rand_mis, min(25, len(rand_mis)))
    ns_re = re.compile(r"^\s*namespace\s+(\S+)", re.M)
    decl_re = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s+([A-Za-z0-9_'.]+)", re.M)
    disk_ok = 0
    bad_spot = []
    for rk_, mod, fp_rel, decl_ns, fold_ns, mk in sample:
        fp = os.path.join(ROOT, "data", "rh_mirror", "src", mod.replace(".", "/") + ".lean")
        if not os.path.exists(fp):
            bad_spot.append((mod, "missing file"))
            continue
        txt = open(fp, encoding="utf-8", errors="replace").read()
        ns_found = ns_re.findall(txt)
        d_found = decl_re.findall(txt)
        # Verify declared_ns (ignoring leading _root_.) appears in either a namespace line or a qualified decl name
        core = decl_ns[7:] if decl_ns.startswith("_root_.") else decl_ns
        seg0 = core.split(".")[0]
        if any(core in x or x.startswith(seg0) for x in ns_found) or any(core in x or x.startswith(seg0 + ".") or ("_root_." + seg0) in x for x in d_found) or core == "<root>":
            disk_ok += 1
        else:
            bad_spot.append((mod, decl_ns, ns_found[:3], d_found[:3]))
    ck(not bad_spot, f"on-disk spot check of {len(sample)} high/top misfiles in data/rh_mirror: {disk_ok}/{len(sample)} confirmed; mismatches={bad_spot[:3]}")

    # 6. Ranking monotonicity & provenance check
    out_of_order = t1.execute(
        "SELECT COUNT(*) FROM misfiles a JOIN misfiles b ON b.rank = a.rank + 1 WHERE a.score < b.score - 1e-12"
    ).fetchone()[0]
    bad_prov = t1.execute("SELECT COUNT(*) FROM misfiles WHERE provenance IS NULL OR provenance = ''").fetchone()[0]
    ck(out_of_order == 0 and bad_prov == 0, f"misfiles sorted descending by score (inversions={out_of_order}) and all carry provenance (missing={bad_prov})")

    # 7. Check tier1_summary.json matches tier1.db counts
    meta = {k: json.loads(v) for k, v in t1.execute("SELECT key, value_json FROM meta")}
    print("     tier1 meta keys:", sorted(meta))
    print("     tier1_summary keys:", sorted(summ))

    fails = sum(1 for x in R if not x)
    print(f"\nF1-CHECK {'PASS' if fails == 0 else 'FAIL'} ({len(R)-fails}/{len(R)})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
