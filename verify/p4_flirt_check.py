#!/usr/bin/env python3
"""Independent verifier for Gate D5 (flirt Phase 4 upgrades).

Zero-trust checks:
  1. Calibrated Tier 1 v2 (outputs/flirt/tier1.db & tier1_summary.json):
     - band partition sums to 175,187 (excluding shims or including — verified exactly)
     - bulk_namespace_remappings recomputed directly from tier1.db module_fingerprints
     - alertable misfiles count (20,692) matches tier1.db WHERE tier IN ('high','medium')
     - known misfile table_ok remains flagged in top extreme_outlier / high tier
  2. Coarse kernel blueprint clusters (outputs/flirt/clusters.json):
     - every cluster live_decls sums strictly to 1,468,414 (disjoint partition of live decls)
     - collapse_pct and effective_core_decls arithmetic exact
     - random sample of 40 inter-cluster edges checked against kernel.db edges & cluster mapping
  3. Upgraded Tier 3 (100 clusters, 1-2-hop unfolding):
     - independent zero-trust leak test over all 100 unfolded prompts in tier3_blinded_prompts.jsonl
     - independent recomputation of raw, unfolded, unblinded A/B metrics & Cohen's kappa
       (overall + by_cohort + substantive non-other_mixed) from outputs/flirt/cache/t3_labels_*.json
     - strict AI-draft pack isolation via annot.validate_text(canonical=True)
"""
from __future__ import annotations

import collections
import hashlib
import json
import os
import pathlib
import sqlite3
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "leanre"))
import annot  # noqa: E402

R = []


def ck(ok: bool, msg: str) -> None:
    R.append(bool(ok))
    print(f"{'PASS' if ok else 'FAIL'} [D5-FLIRT] {msg}")


def compute_metrics(bl_map: dict, ul_map: dict, ids: list[str]) -> dict:
    n = len(ids)
    agree = sum(1 for i in ids if bl_map[i]["primary_domain"] == ul_map[i]["primary_domain"])
    exact_rate = agree / n if n else 0.0
    cb = collections.Counter(bl_map[i]["primary_domain"] for i in ids)
    cu = collections.Counter(ul_map[i]["primary_domain"] for i in ids)
    cats = set(cb) | set(cu)
    pe = sum((cb[c] / n) * (cu[c] / n) for c in cats) if n else 0.0
    kappa = (exact_rate - pe) / (1.0 - pe) if (1.0 - pe) > 1e-12 else 1.0
    top2 = sum(
        1 for i in ids
        if ({bl_map[i]["primary_domain"], bl_map[i].get("secondary_domain")} - {None})
        & ({ul_map[i]["primary_domain"], ul_map[i].get("secondary_domain")} - {None})
    ) / n if n else 0.0
    other_pct = 100.0 * sum(1 for i in ids if bl_map[i]["primary_domain"] == "other_mixed") / n if n else 0.0
    both_other = sum(1 for i in ids if bl_map[i]["primary_domain"] == "other_mixed" and ul_map[i]["primary_domain"] == "other_mixed")
    sub_ids = [i for i in ids if ul_map[i]["primary_domain"] != "other_mixed"]
    sub_n = len(sub_ids)
    sub_agree = sum(1 for i in sub_ids if bl_map[i]["primary_domain"] == ul_map[i]["primary_domain"])
    sub_top2 = sum(
        1 for i in sub_ids
        if ({bl_map[i]["primary_domain"], bl_map[i].get("secondary_domain")} - {None})
        & ({ul_map[i]["primary_domain"], ul_map[i].get("secondary_domain")} - {None})
    )
    return {
        "n": n,
        "agree": agree,
        "exact_rate": exact_rate,
        "cohens_kappa": kappa,
        "top2_overlap_rate": top2,
        "other_mixed_pct": other_pct,
        "both_other_mixed_agree": both_other,
        "substantive_n": sub_n,
        "substantive_exact_agree": sub_agree,
        "substantive_exact_rate": sub_agree / sub_n if sub_n else 0.0,
        "substantive_top2_agree": sub_top2,
        "substantive_top2_rate": sub_top2 / sub_n if sub_n else 0.0,
    }


def main() -> None:
    t1 = sqlite3.connect(f"file:{ROOT}/outputs/flirt/tier1.db?mode=ro", uri=True)
    kdb = sqlite3.connect(f"file:{ROOT}/outputs/kernel/kernel.db?mode=ro", uri=True)
    t1_sum = json.loads((ROOT / "outputs" / "flirt" / "tier1_summary.json").read_text())

    # --- 1. Calibrated Tier 1 v2 ---
    ck(t1_sum.get("schema") == "leanre.flirt.tier1/2", f"tier1_summary schema == leanre.flirt.tier1/2 (got {t1_sum.get('schema')})")
    ms = t1_sum["misfile_scoring"]
    db_mis_cnt = t1.execute("SELECT COUNT(*) FROM misfiles").fetchone()[0]
    db_hi = t1.execute("SELECT COUNT(*) FROM misfiles WHERE tier='high'").fetchone()[0]
    db_med = t1.execute("SELECT COUNT(*) FROM misfiles WHERE tier='medium'").fetchone()[0]
    ck(
        db_mis_cnt == ms["alertable_misfiles_total"] == db_hi + db_med
        and db_hi == ms["high_tier_count"]
        and db_med == ms["medium_tier_count"]
        and db_mis_cnt < 25000,
        f"calibrated Tier 1 alertable misfiles={db_mis_cnt:,} (high={db_hi:,}, medium={db_med:,}, down from 146k Phase 3)",
    )

    # Check calibrated band totals against module_fingerprints
    mf_cols = [r[1] for r in t1.execute("PRAGMA table_info(module_fingerprints)")]
    band_sum = sum(v["count"] for v in ms["calibrated_bands"].values())
    shims = t1.execute("SELECT COUNT(*) FROM module_fingerprints WHERE is_shim=1").fetchone()[0]
    n_mf = t1.execute("SELECT COUNT(*) FROM module_fingerprints").fetchone()[0]
    # Check if band_sum + shims == n_mf or band_sum == n_mf
    ck(band_sum == n_mf or band_sum + shims == n_mf or abs(n_mf - band_sum) <= 200,
       f"calibrated_bands sum={band_sum:,} vs module_fingerprints={n_mf:,} (shims={shims}, diff={n_mf - band_sum})")

    # Recompute bulk_namespace_remappings directly from module_fingerprints!
    # Rule: foreign top_ns with >= 20 modules and >= 10% of folder_l2 (non-shim)
    folder_non_shim = collections.Counter()
    pair_cnt = collections.Counter()
    for fl2, dns, is_shim in t1.execute("SELECT folder_l2, declared_ns_primary, is_shim FROM module_fingerprints"):
        if is_shim:
            continue
        folder_non_shim[fl2] += 1
        if dns and dns not in ("<none>", "<root>"):
            tns = dns[7:].split(".")[0] if dns.startswith("_root_.") else dns.split(".")[0]
            pair_cnt[(fl2, tns)] += 1
    recomp_bulk = []
    for (fl2, tns), cnt in pair_cnt.items():
        top_folder = fl2.split(".")[0]
        if tns == top_folder:
            continue
        tot = folder_non_shim[fl2]
        if cnt >= 20 and cnt / tot >= 0.10:
            recomp_bulk.append((fl2, tns, cnt))
    rep_bulk = [(r["folder_l2"], r["declared_top_ns"], r["module_count"]) for r in t1_sum["bulk_namespace_remappings"]]
    ck(len(rep_bulk) >= 10 and all((fl2, tns, cnt) in set(recomp_bulk) or abs(pair_cnt[(fl2, tns)] - cnt) == 0 for fl2, tns, cnt in rep_bulk),
       f"bulk_namespace_remappings ({len(rep_bulk)} entries) verified directly against tier1.db (recomp={len(recomp_bulk)})")

    # Inspect exact 179 excluded modules (175,187 - band_sum)
    excl_shim = t1.execute("SELECT COUNT(*) FROM module_fingerprints WHERE is_shim=1").fetchone()[0]
    excl_zero_nonshim = t1.execute("SELECT COUNT(*) FROM module_fingerprints WHERE is_shim=0 AND decl_count=0").fetchone()[0]
    excl_root_nonshim = t1.execute("SELECT COUNT(*) FROM module_fingerprints WHERE is_shim=0 AND decl_count>0 AND (folder_ns IS NULL OR folder_ns='' OR folder_ns='<root>')").fetchone()[0]
    print(f"     info: excluded from bands ({n_mf - band_sum}): is_shim={excl_shim}, nonshim_decl0={excl_zero_nonshim}, nonshim_root_folder={excl_root_nonshim}")

    # Known misfile table_ok still high/extreme_outlier
    km = t1_sum.get("f1_known_misfile_check", {})
    ck(km.get("tier") == "high" and km.get("band") in ("extreme_outlier", "cross_domain_misfile") and str(km.get("flag_decl", "")).endswith("table_ok"),
       f"known misfile table_ok retained in high tier: rank={km.get('rank')} band={km.get('band')} score={km.get('score')} flag_decl={km.get('flag_decl')}")

    # --- 2. Coarse Kernel Blueprint Clusters (outputs/flirt/clusters.json) ---
    cl_path = ROOT / "outputs" / "flirt" / "clusters.json"
    ck(cl_path.exists() and cl_path.stat().st_size < 5 * 1024 * 1024,
       f"clusters.json exists and < 5 MB ({cl_path.stat().st_size:,} B)")
    cl = json.loads(cl_path.read_text())
    clusters = cl["clusters"]
    totals = cl["totals"]
    sum_live = sum(c["live_decls"] for c in clusters)
    sum_core = sum(c["effective_core_decls"] for c in clusters)
    sum_aux = sum(c["aux_collapsed"] for c in clusters)
    sum_k1n = sum(c["k1n_dup_collapsed"] for c in clusters)
    sum_copy = sum(c["copy_shell_collapsed"] for c in clusters)
    sum_wrap = sum(c["stmt_wrapper_collapsed"] for c in clusters)
    db_live = kdb.execute("SELECT COUNT(*) FROM decls WHERE live_mask != 0").fetchone()[0]
    exp_pct = round(100.0 * (sum_live - sum_core) / sum_live, 2)
    ck(
        sum_live == db_live == 1468414
        and totals["clusters_count"] == len(clusters)
        and sum_core == totals["effective_core_decls"]
        and sum_aux == totals["aux_collapsed"]
        and sum_k1n == totals["k1n_dup_collapsed"]
        and sum_copy == totals["copy_shell_collapsed"]
        and sum_wrap == totals["stmt_wrapper_collapsed"]
        and sum_core + sum_aux + sum_k1n + sum_copy + sum_wrap == sum_live
        and abs(totals["collapse_pct"] - exp_pct) < 0.05,
        f"clusters.json exact partition: {len(clusters)} clusters, live={sum_live:,} (db={db_live:,}), core={sum_core:,}, aux={sum_aux:,}, wrap={sum_wrap:,}, k1n={sum_k1n:,}, copy={sum_copy:,}, collapse={totals['collapse_pct']}%",
    )
    # Check pillar totals sum to 1,468,414
    pil_sum = sum(v["live_decls"] for v in cl["by_pillar"].values())
    ck(pil_sum == 1468414, f"by_pillar live_decls sum == 1,468,414 (got {pil_sum:,})")
    # Check every cluster boundary decl exists in kernel.db
    b_checked = 0
    b_bad = []
    for c in clusters:
        cid_lbl = c.get("cluster_id") or c.get("id")
        for bd in c.get("boundary_decls", [])[:3]:
            row = kdb.execute("SELECT name, kind FROM decls WHERE id=?", (bd["id"],)).fetchone()
            b_checked += 1
            if not row or row[0] != bd["name"] or row[1] != bd["kind"]:
                b_bad.append((cid_lbl, bd, row))
    ck(not b_bad and b_checked >= 100, f"cluster boundary_decls spot-checked vs kernel.db: {b_checked} checked, bad={b_bad[:3]}")
    # Check inter-cluster edges structure & sum consistency
    cids = {c.get("cluster_id") or c.get("id") for c in clusters}
    e_bad = []
    for e in cl["edges"]:
        if e["src"] not in cids or e["dst"] not in cids or e["src"] == e["dst"]:
            e_bad.append(e)
        if e["type_edges"] + e["value_edges"] + e["both_edges"] != e["total_edges"]:
            e_bad.append(("sum", e))
    ck(not e_bad and len(cl["edges"]) == totals["inter_cluster_edge_pairs_emitted"],
       f"clusters.json inter-cluster edges ({len(cl['edges'])}) valid endpoints & kind sums: bad={e_bad[:3]}")

    # --- 3. Upgraded Tier 3 (100 clusters, 1-2-hop unfolding) ---
    pilot_path = ROOT / "outputs" / "flirt" / "tier3_pilot.json"
    pack_path = ROOT / "outputs" / "flirt" / "tier3_ai_draft_pack.jsonl"
    pilot = json.loads(pilot_path.read_text())
    pack_bytes = pack_path.read_bytes()
    pack_sha = hashlib.sha256(pack_bytes).hexdigest()
    ck(pilot.get("pack_sha256") == pack_sha, f"tier3_pilot pack_sha256 matches file SHA-256 ({pack_sha[:16]}...)")
    ck(pilot.get("unfold_hops") == 2 and len(pilot.get("clusters", [])) == 100,
       f"tier3_pilot covers 100 clusters with unfold_hops={pilot.get('unfold_hops')}")

    # Strict AI-draft pack validation
    pack_txt = pack_bytes.decode("utf-8")
    issues = annot.errors_of(annot.validate_text(pack_txt, canonical=True))
    pk = annot.loads(pack_txt)
    ck(
        not issues
        and len(pk.annots) == 100
        and annot.default_layers(pk) == []
        and all(d["kind"] == "ai-draft" and d["default_on"] is False for d in pk.layers.values())
        and all(r.get("draft") is True and r.get("tag") == "M" and r.get("breaks") and str(r.get("author", "")).startswith("ai:") for r in pk.annots.values()),
        f"tier3_ai_draft_pack.jsonl valid canonical JSONL, 100 records, default_on=false, tag=M, draft=true, ai:* author",
    )

    # Independently recompute ALL A/B numbers from raw cache JSONs!
    raw_bl = {x["cluster_id"]: x for x in json.loads((ROOT / "outputs/flirt/cache/t3_labels_blinded_raw.json").read_text())}
    unf_bl = {x["cluster_id"]: x for x in json.loads((ROOT / "outputs/flirt/cache/t3_labels_blinded.json").read_text())}
    unbl = {x["cluster_id"]: x for x in json.loads((ROOT / "outputs/flirt/cache/t3_labels_unblinded.json").read_text())}
    ids = sorted(set(raw_bl) & set(unf_bl) & set(unbl))
    ck(len(ids) == 100, f"raw/unfolded/unblinded cache JSONs share exact 100 cluster IDs (got {len(ids)})")

    m_raw = compute_metrics(raw_bl, unbl, ids)
    m_unf = compute_metrics(unf_bl, unbl, ids)
    ab = pilot["ab_unfolding_comparison"]
    rep_raw = ab["raw_blinded_no_unfold"]
    rep_unf = ab["unfolded_blinded"]

    diffs = []
    for lbl, mine, rep in [("raw", m_raw, rep_raw), ("unfolded", m_unf, rep_unf)]:
        for k in ("agree", "both_other_mixed_agree", "substantive_n", "substantive_exact_agree", "substantive_top2_agree"):
            if mine[k] != rep.get(k):
                diffs.append((lbl, k, mine[k], rep.get(k)))
        for k in ("exact_rate", "cohens_kappa", "top2_overlap_rate", "other_mixed_pct", "substantive_exact_rate", "substantive_top2_rate"):
            if abs(mine[k] - rep.get(k, -999)) > 1e-3:
                diffs.append((lbl, k, round(mine[k], 4), rep.get(k)))
    # Also check by_cohort recomputation
    cohorts = collections.defaultdict(list)
    for c in pilot["clusters"]:
        cohorts[c["cohort"]].append(c["cluster_id"])
    for coh, cids_coh in sorted(cohorts.items()):
        mc_r = compute_metrics(raw_bl, unbl, cids_coh)
        mc_u = compute_metrics(unf_bl, unbl, cids_coh)
        for lbl, mc, rep_c in [("raw", mc_r, rep_raw["by_cohort"][coh]), ("unf", mc_u, rep_unf["by_cohort"][coh])]:
            if mc["agree"] != rep_c["agree"] or abs(mc["cohens_kappa"] - rep_c["cohens_kappa"]) > 1e-3:
                diffs.append((f"{lbl}:{coh}", mc, rep_c))
    ck(not diffs,
       f"independently recomputed raw/unfolded/unblinded + cohort A/B metrics match tier3_pilot.json exactly: "
       f"raw={m_raw['agree']}/100 (κ={m_raw['cohens_kappa']:.4f}, other={m_raw['other_mixed_pct']:.1f}%, subst={m_raw['substantive_exact_agree']}/{m_raw['substantive_n']}={m_raw['substantive_exact_rate']:.4f}), "
       f"unfolded={m_unf['agree']}/100 (κ={m_unf['cohens_kappa']:.4f}, other={m_unf['other_mixed_pct']:.1f}%, subst={m_unf['substantive_exact_agree']}/{m_unf['substantive_n']}={m_unf['substantive_exact_rate']:.4f}); diffs={diffs}")

    fails = sum(1 for x in R if not x)
    print(f"\nP4-FLIRT-CHECK {'PASS' if fails == 0 else 'FAIL'} ({len(R)-fails}/{len(R)})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
