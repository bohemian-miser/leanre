# Phase 4 Independent Verification Report (`leanre`)

- **Verifier:** independent zero-trust verifier (`@verifier`; read-only everywhere except `verify/` and `outputs/phase4_verification_report.md`)
- **Verified Frozen Tree:** `0c95b2e` (pre-report `HEAD`; Phase 4 commits `8027fa7`..`0c95b2e`)
- **Pinned Inputs `[L]`:**
  - `data/rh_mirror` @ `Deicyde/riemann-hypothesis@40e56bab026552e089d7afcfeff08d2defb9c005` (`175,187` `.lean` files, `17,374,215` `wc -l` physical lines)
  - `data/solution.ndjson.zst` (compressed SHA-256 `61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381`, uncompressed SHA-256 `5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e`; `1,468,418` folded `con-leche` records / `1,484,733` unpacked `nanoda` constants via `nasqret`, `114,115,002` typed edges)
  - `data/challenge.ndjson.zst` (`51,692` declaration records)
  - `data/corpora/{mathlib4@0df444a3, lean4@819816b2, batteries@4488d40d}`
- **Epistemic Scope (Guardrail 1 — Four Epistemic Layers):**
  - **Layer 1 (Kernel Validity):** Independently reproduced against `solution.ndjson.zst` via clean-room C++ oracle (`verify/oracle_ndjson.cpp`, `verify/dom_oracle.cpp`) and `outputs/kernel/kernel.db` (`mode=ro`) `[L]`.
  - **Layer 2 (Specification Fidelity / Semantic TCB):** Audited directly across all 5 headline roots, `2,570`-definition statement closure, `175,187`-file compiler-flag sweep, and pinned Mathlib `0df444a3` definitions `[L]`.
  - **Layer 3 (Human Mathematical Intelligibility / Architecture):** Structural decompilation, contract unfolding, dead-code archaeology, and FLIRT clustering verified against pinned sources and kernel graphs `[L]`. Deep tactic bodies (`> ~30` lines inside leaf theorems) remain unread / **`OPAQUE`**.
  - **Layer 4 (Institutional / Peer Mathematical Consensus):** **OPEN** — out of scope for software/reverse-engineering verification.
- **Provenance Tags (Guardrail 2):** `[L]` locally extracted or independently recomputed from pinned inputs; `[A]` author prose (`alpo.ge/remark.pdf`); `[C]` third-party community reports (`Sutherland`, `nasqret`, `lean4lean` logs); `[S]` standard published mathematics; `[M]` CS/RE analogy (with where it breaks) or AI-draft heuristic.

---

## 1. Overall Verdict

**PHASE 4 VERDICT: GO — ALL 13 PHASE 4 GATES & DELIVERABLES PASS (`0` unresolved Phase 4 defects; `7` defects/discrepancies caught by independent verification, fixed by owners, and re-verified at frozen `HEAD = 0c95b2e`).**

*Standing pre-existing OPEN item (carried unchanged from Phase 2/Phase 3):* **R2** tree hygiene is **100% CLEAN (`0` findings)** on every Phase 3 and Phase 4 file (`0` `.lean`, `0` `data/`/`research/sources/`, `0` files `> 5 MB`, `0` secrets, `0` internal hostnames, `0` new proof-body lines, `0` new multi-line mirror overlaps). The `8` hard findings reported by `verify/audit_tree.py --leak` belong exclusively to pre-existing Phase 2 files (`prototypes/concept_map_demo.html`, `outputs/forensics_report.json`, `outputs/workbench_bundle.json`) already documented in `outputs/phase3_verification_report.md`.

---

## 2. Gate-by-Gate Summary Matrix (`HEAD = 0c95b2e`)

| Gate / Scope | Owner(s) | Final Commit(s) | Verdict | Independent Verification Evidence `[L]` |
|---|---|---|---|---|
| **D1 — Spine & Shared Diamond + `leanre decompile`** | `spine`, `coordinator` | `9c82dd6`, `5adbd47` | **PASS** | `test_decompile.py` `17/17 OK`; `p4_decomp_check` `91/91` (`143` edges, `0` err); `p4_analysis_check` `114/114` anchors (`0` err); clean-room C++ oracle (`114,115,002` edges) reproduced `reach(row)=1,373,275`, `reach(gal)=485,089`, `intersection=389,987`, `331,598/331,598` diamond decls in both, `58,857 = 58,826 + 31`, `35` bridge-only, `387` `Published.*` defs (`100+276+11`); 5 top diamond roots spot-checked on disk. |
| **D2-A — Pillar A (Theta / Definite Side, `543,325` decls)** | `theta` | `9c02373`, `72eefc3` | **PASS** *(after fix)* | `p4_decomp_check` `95/95` (`355` edges, `38/38` claim anchors, `0` err); `p4_analysis_check` `129/129` anchors (`0` err); `0` BODY leaks across `175,187` mirror files; independent `kernel.db` + disk check reproduced `543,325`, `18,828` direct kids, kind/flag counts, `D7` (`fan_in=155,523`, `type_nodes=11,475`), `GlobalTheory.T.*` (`38,194/38,677` live `vn=1`), `Behrend` live. Caught pre-`1f2361e` taint-count staleness on line 40 -> fixed in `72eefc3`. |
| **D2-B — Pillar B (Galois & `Row0b`, `95,102` decls)** | `galois` | `0e273a6` | **PASS** | `p4_decomp_check` `323/323` (`1,163` edges, `24/24` claim anchors, `0` err); `p4_analysis_check` `105/105` anchors (`39/39` decl+size exact, `0` err); `0` BODY leaks; independent `kernel.db` + disk check confirmed `95,102` (`78,553` thm, `16,012` def, `534` ind, `3` Mathlib `.wrapped` opaque, `0` axioms, `10` `decide_kernel_pattern`), `recTExists` (`595`, `idom=everyCharacter`, `fan_in=25`), `WeightsConjBis`/`IsRecTOfIsRec`/`JunkEx`/`CharPolOfInert`/`GalMapMul`/`PullHlComp`/`TLiftK` verbatim. |
| **D2-C — Pillar C (Window / `VWin`, `92,705` decls)** | `window` | `0f0b4be` | **PASS** | `p4_decomp_check` `222/222` (`634` edges, `19/19` claim anchors, `0` err); `p4_analysis_check` `99/99` anchors (`7/7` decl+size exact, `0` err); `0` BODY leaks; independent `kernel.db` + disk check confirmed `92,705` (`51` taint sources: `7` `decide_kernel` + `44` `decide_kernel_pattern`), `ExistsPageN.lean:12-49` constants (`1/52`, `q%8=3`, `d%16=7`, `401`, `√(exp(x^eps))`), `OpenImageCondition` / `LiteratureCMHypothesis` deadness. |
| **D2-D — Pillar D (Volume & Literature, `80,720+` decls)** | `volume` | `8027fa7`, `023ebad` | **PASS** | `p4_decomp_check` `115/115` (`316` edges, `8/8` claim anchors, `0` err); `p4_analysis_check` `79/79` anchors (`2/2` decl+size exact, `0` err); `0` BODY leaks; disk verification confirmed `195` thms (`4` direct `O.<field>`), `UnusedSlot72 := True`, `GlobalEulerChar`/`AbelianDeRham`/`LocalConverseGL`/`PoitouTateNormalised`/`FarguesExact`. |
| **D2-F — Deep Follow-Up Audit (`Loc`/`η`, `remark.pdf`, `dualAbelianScheme`)** | `linkn-audit` | `645dc5a`, `f59532b` | **PASS** *(after fix)* | `p4_analysis_check` `141/141` anchors (`2/2` decl+size exact, `0` err); `0` BODY leaks; independent `kernel.db` + disk verification of `LB`/`IsLB`, `withLoc`, `etaSz`/`TieGlobal.lean:60`, `MetaplecticRepresentation`, all `remark.pdf` DB queries (`sixfold=0`, `kazhdan=49`, `metaplectic=74`, `kuznetsov=0`, `relativetrace=0`, `jacquetrallis=24`, `stepanov=0`, `behrend=15`, `traceformula=1,444`). Caught Guardrails 1–2 conflation + `hasseDeriv`/`JacquetRallis` count precision -> fixed in `f59532b`. |
| **D3 — Layer 2 Semantic TCB & Bridge-Contract Audit** | `tcb` | `9567841` | **PASS** | `p4_decomp_check` `77/77` (`66` project + `11` Mathlib ground, `215` edges, `19/19` claim anchors, `0` err); `p4_analysis_check` `116/116` anchors (`0` err); `0` BODY leaks; independent `175,187`-file security keyword sweep (`0` `unsafe`/`implemented_by`/`extern`/`csimp`/`skipKernelTC`/`native_decide`/`sorry`/`axiom`/`opaque`/`autoImplicit true`/`global notation`, `2` elaborator `partial def`s); `2,570` `defcone` exact (`4` project defs, `0` in `riemannHypothesis`); `challenge \ solution_stmt = 5`, `solution_stmt \ challenge = 0`; `Formalism.Gchi` & dead twins confirmed absent from `kernel.db`; live `An.gChi` + `poleData.lean:230-239` verified on disk. |
| **D4-K — Kernel `lean4lean_timeout` Fix + `slice` / `type-deps`** | `kernel` | `1f2361e` | **PASS** | `verify/p4_slice_oracle.py` **`9/9 PASS`** against clean-room C++ oracle: `lean4lean_timeout` has both `PI.PC.loop_run._proof_1_1` (`#571290`) & `PI.PC.loop_run` (`#571291`), `ChebyshevPrimeBounds.SmallLoop` = `9/9` live, `DyadicPrimeIntervals.*` = `0`, all `3,100` `taint_paths` (`59,414` edges) validated edge-by-edge (`0` bad), `slice(everyCharacter, depth=2)` = `70/70` exact (`419` edges `0` bad), `type-deps` exact (`27/27`, `4/4`); `test_kernel.py` `4/4 OK`. |
| **D4-A — `28,904` Zero-Kernel Partition & Computation Atlas** | `arch` | `0490b24`, `a848b36` | **PASS** *(after fix)* | `verify/p4_deadcode_compute_check.py` **`8/8 PASS`** (`175,187 = 146,283 + 28,904`, `2,378,537` `wc -l`, 6 disjoint buckets, `126/126` on-disk spot checks, `kernel_flag_counts` exact, `SmallLoop` live / `Run1..4` dead / `table_ok` live); independent `175,187`-file `decide +kernel` sweep confirmed `34` files / `124` lines / `151` occurrences; `p4_analysis_check` `112/112` anchors; `compute_sweep.py --selftest` PASS. Caught Guardrails 1–2 conflation -> fixed in `a848b36`. |
| **D5 — Calibrated FLIRT Tier 1 v2, Coarse Clusters, 100-Cluster Unfolded Tier 3** | `flirt`, `coordinator` | `21c3c93`, `9ff34e8`, `181ddca` | **PASS** *(after fix)* | `f1_tier1_check` **`8/8 PASS`**; `f3_check` **`8/8 PASS`** (`0` leaks across 100 unfolded prompts vs `3,485` folders, `167,045` file stems, `1,033,515` full decls, `697,966` leaf decls, `35` landmarks); `p4_flirt_check` **`15/15 PASS`** (`20,692` misfiles, `16` bulk remaps, `141` clusters = `1,468,414` live / `42.35%` collapse, `423/423` boundary decls, `2,099/2,099` edges, exact independent recomputation of raw/unfolded/unblinded + cohort A/B metrics & κ); `test_flirt_*` `8/8 OK`. Caught 10-module arithmetic typo in `docs/FLIRT.md:98` (`169` vs `179`) -> fixed in `181ddca`. |
| **D6 — Phase 4 Interactive Workbench** | `workbench` | `fb05791`, `3d86a44`, `59eca9f` | **PASS** *(after fix)* | Syntax (`py_compile` + `node --check`) OK; `verify/w2_probe.py --port 8438` **`8/8 PASS`** (`46` endpoints, `0` CDNs, `100%` `mode=ro` SQLite, binds `127.0.0.1`); `workbench/probe_p3.py --port 8437 --annotations <scratch>` **`161/161 PASS (0 failed)`**; headless Chrome `#selftest=1` **`157 checks, 0 errors`** (`6/6` decomp ready, `compute=ready`, `clusters=ready`, `slice=ready`, `--fixtures` banner & absent-outputs `HTTP 200 state=absent` verified); all 7 screenshots visually verified. Caught `143,982` vs `125,598` bulk-remap overlap on Tier 1 stat card -> fixed in `59eca9f`. |
| **Phase 4 AI-Draft Annotation Pack (`ai/decomp-phase4`)** | `annot` | `f4efc49` | **PASS** | `verify/a_check.py` **`36/36 PASS`**; `annot validate` & byte-identical export OK; `128/128` `k1n` sighashes independently verified `0` mismatches vs `kernel.db`; `default_on=false`, `draft=true`, `tag=M`, mandatory `breaks`, `54/54` unit tests OK. |
| **Master Synthesis & CLI/Docs Integration** | `coordinator` | `f61bc09`, `0c95b2e` | **PASS** *(after fix)* | `p4_analysis_check` `analysis/SYNTHESIS.md` PASS (`3/3` anchors, `0` err); CLI `leanre {decompile, kernel slice, kernel type-deps, flirt cluster}` verified. Caught `recTExists` placement (`idom=everyCharacter` in shared diamond, not under `everyCharacter_of_row`) + count sync -> fixed in `0c95b2e`. |
| **R1 — Full Regression Suite** | all | `0c95b2e` | **PASS** | `python3 -m unittest discover -s leanre`: **`136/136 OK`** (`2` opt-in real-data tests skipped); `(cd leanre/kernel-rs && cargo test)`: **`10/10 passed`**. |
| **R2 — Tree Hygiene & License Respect** | all | `0c95b2e` | **PASS (Phase 4)** / **OPEN (Phase 2 baseline)** | `verify/audit_tree.py --leak` across `133` tracked + `5` verifier files vs `175,187` mirror files: **`0` path, `0` size (`>5 MB`), `0` secret, `0` internal, `0` Phase 3/4 BODY or MULTI findings** (`8` pre-existing Phase 2 baseline findings carried from Phase 3). |
| **R3 — Guardrails 1–6 & Canonical Facts** | all | `0c95b2e` | **PASS** *(after fixes)* | `verify/r3_audit.py`: all `27` tripwire hits manually inspected and confirmed benign (negations, selftest regexes, Phase 3 report meta-text). Every `analysis/*.md` and `docs/*.md` carries canonical Layer 1–4 separation, `[L]/[A]/[C]/[S]/[M]` provenance tags, and explicit `OPAQUE` registers. |

---

## 3. Defect & Discrepancy Log (Zero-Trust Catches & Re-Verifications)

Every defect discovered during verification was reported on the swarm board to its owner (never fixed directly by `@verifier`), re-verified from scratch after the owner's commit:

1. **`docs/FLIRT.md:98` (`flirt`, caught at `21c3c93` -> fixed `181ddca`):** The calibrated bands table summed to `175,008` (`179` excluded from `175,187`), while the parenthetical listed `150 shims + 19 0-decl = 169` (off by `10`). Direct query on `outputs/flirt/tier1.db` established `150` `is_shim=1` + `27` non-shim `decl_count=0` + `2` root-folder modules (`Main`, `Statements`) = `179`. Verified exact in `181ddca`.
2. **`analysis/compute_and_deadcode.md:7-12` & `outputs/decomp/compute_atlas.json` (`arch`, caught at `0490b24` -> fixed `a848b36`):** Conflated Guardrail 1 epistemic layers with Guardrail 2 provenance tags and redefined `[A]`/`[C]`/`[M]`; also reported `124` `decide +kernel` matching lines without distinguishing `151` total tactic occurrences. Fixed to canonical Layer 1–4 + `[L]` tags and exact `124` lines / `151` occurrences in `a848b36`. Verified clean (`p4_deadcode_compute_check` `8/8`, `p4_analysis_check` `112/112`). *(Bonus: `arch` noted a typo in `verify/p4_deadcode_compute_check.py`'s `Run1..4` module prefix; fixed in our script and asserted presence in `leanre.db`.)*
3. **`workbench/phase3.py:519` (`workbench`, caught via screenshot `p4_flirt_tier1_cal.png` at `3d86a44` -> fixed `59eca9f`):** `BULK REMAPPED MODULES` card summed `bulk_namespace_remappings.module_count` (`143,982`, overlapping `misfiles` by `18,384`) instead of `calibrated_bands.bulk_namespace_remapping.count` (`125,598`, disjoint from `misfiles`, matching `docs/FLIRT.md:97`). Fixed in `59eca9f` and visually + API re-verified (`125,598`).
4. **`analysis/pillar_theta.md:40` (`theta`, caught at `9c02373` -> fixed `72eefc3`):** Taint-source census ran against pre-`1f2361e` `kernel.db` (`decide_kernel 6`, `slow_con_leche 4`, `lean4lean_timeout 1`) before `._proof_1_1` aux rows were added. Synced to post-`1f2361e` `kernel.db` (`decide_kernel 11` / `6` mods, `slow_con_leche 6` / `4` mods, `lean4lean_timeout 2` / `1` mod) in `72eefc3`. Re-verified exact.
5. **`analysis/deep_followup_audit.md:4-9,19,107-108` (`linkn-audit`, caught at `645dc5a` -> fixed `f59532b`):** Scrambled Guardrail 1 Layer 1–4 order and redefined `[S]`/`[A]`/`[C]`/`[M]` provenance tags; reported `LIMIT 15` snippet count for `Polynomial.hasseDeriv` callers instead of exact `47` live direct callers (`30` project / `17` Mathlib) and `1,956` without naming `1,957`-decl wrapper `GlobalTheory.T.jacquetRallisUnitMatch_all_ranks`. Fixed cleanly in `f59532b` and re-verified (`141/141` anchors, `0` errors).
6. **`analysis/SYNTHESIS.md:43,69,115-116,132` (`coordinator`, caught at `f61bc09` -> fixed `0c95b2e`):** Placed `UpperTheory.Zero.LLC.recTExists` (`595` decls) under `everyCharacter_of_row`'s `40,826` siblings; `kernel.db` establishes `idom(recTExists) = UpperTheory.FinalTheorems.everyCharacter` (inside the `331,598`-decl Shared Diamond, `fan_in = 25`). Also synced `hasseDeriv` (`47` live / `30` project), `jacquetRallisUnitMatch_all_ranks` (`1,957` / `1,956`), and `VWin` statement (`0` opaque) vs Pillar C proof graph (`76` opaque). Fixed in `0c95b2e` and re-verified.
7. **`verify/audit_tree.py` & `verify/a_check.py` (verifier scripts):** Updated `verify/audit_tree.py` to classify bare single-token qualified Lean identifiers separately from multi-token proof-body lines (`ident`, allowed under R2) and deduplicate `MULTI` per distinct line; updated `verify/a_check.py:219` to filter `kind == "human"` rather than excluding a single hardcoded AI layer name now that `ai/decomp-phase4` coexists in `annotations/`.

---

## 4. Exact Command & Output Receipts (Frozen `HEAD = 0c95b2e`)

### 4.1 Schema, Anchor & Guardrail Verification Across All 6 Decomp JSONs & 9 Analysis Dossiers

```text
$ python3 verify/p4_decomp_check.py outputs/decomp/{spine_map,pillar_theta,pillar_galois,pillar_window,pillar_volume_lit,tcb_audit}.json
  spine_map.json:        nodes=91  verified=91  dom=91  anchors=89  edges=143  claim_anchors=1   errors=0 warnings=0  PASS
  pillar_theta.json:     nodes=95  verified=95  dom=95  anchors=95  edges=355  claim_anchors=38  errors=0 warnings=0  PASS
  pillar_galois.json:    nodes=323 verified=323 dom=323 anchors=323 edges=1163 claim_anchors=24  errors=0 warnings=0  PASS
  pillar_window.json:    nodes=222 verified=222 dom=222 anchors=222 edges=634  claim_anchors=19  errors=0 warnings=0  PASS
  pillar_volume_lit.json:nodes=115 verified=115 dom=115 anchors=115 edges=316  claim_anchors=8   errors=0 warnings=0  PASS
  tcb_audit.json:        nodes=77  verified=77  dom=77  anchors=66  edges=215  claim_anchors=19  errors=0 warnings=0  PASS
P4-DECOMP-CHECK PASS (files=6, total_errors=0)
```

*(Note: `spine_map.json` has `2` Mathlib ground nodes and `tcb_audit.json` has `11` Mathlib ground nodes without `data/rh_mirror/src/` anchors; all `910/910` project nodes have verified on-disk file:line anchors and `≤1`-line headers.)*

```text
$ python3 verify/p4_analysis_check.py analysis/{SYNTHESIS,spine_and_diamond,pillar_theta,pillar_galois,pillar_window,pillar_volume_lit,tcb_and_contracts,compute_and_deadcode,deep_followup_audit}.md
  analysis/SYNTHESIS.md:            anchors=3   bad=0 tags=['A','C','L','M','S'] layer_ref=True opaque_honesty=True
  analysis/spine_and_diamond.md:    anchors=114 bad=0 tags=['A','C','L','M','S'] layer_ref=True opaque_honesty=True
  analysis/pillar_theta.md:         anchors=129 bad=0 tags=['A','L','M','S']     layer_ref=True opaque_honesty=True
  analysis/pillar_galois.md:        anchors=105 bad=0 tags=['A','C','L','M','S'] layer_ref=True opaque_honesty=True decl+size=39/39
  analysis/pillar_window.md:        anchors=99  bad=0 tags=['A','C','L','M','S'] layer_ref=True opaque_honesty=True decl+size=7/7
  analysis/pillar_volume_lit.md:    anchors=79  bad=0 tags=['A','C','L','S']     layer_ref=True opaque_honesty=True decl+size=2/2
  analysis/tcb_and_contracts.md:    anchors=116 bad=0 tags=['C','L','M','S']     layer_ref=True opaque_honesty=True
  analysis/compute_and_deadcode.md: anchors=112 bad=0 tags=['A','C','L','M','S'] layer_ref=True opaque_honesty=True
  analysis/deep_followup_audit.md:  anchors=141 bad=0 tags=['A','C','L','M','S'] layer_ref=True opaque_honesty=True decl+size=2/2
P4-ANALYSIS-CHECK PASS (files=9, total_errors=0)
```

### 4.2 Clean-Room Oracles (D1 Diamond, D3 175k Sweep, D4 Kernel Slice & Dead-Code, D5 FLIRT, Annot)

```text
$ python3 verify/p4_slice_oracle.py
P4-SLICE-ORACLE PASS (9/9) fails=[]
  (lean4lean_timeout=['PI.PC.loop_run._proof_1_1','PI.PC.loop_run'], SmallLoop=9/9, DyadicPrimeIntervals.*=0,
   10/10 timeout taint paths & all 3,100/3,100 kernel.db taint_paths [59,414 edges] validated vs C++ oracle: errors=0;
   slice(everyCharacter, depth=2)=70/70 exact [419 edges, 0 bad]; type-deps(everyCharacter_of_row)=27/27 type, 4/4 val_only)

$ python3 verify/p4_deadcode_compute_check.py
P4-DEADCODE-COMPUTE-CHECK PASS (8/8)
  (175,187 = 146,283 live [14,995,678 wc-l] + 28,904 zero-kernel [2,378,537 wc-l], unreach=0;
   6 disjoint buckets: 0 + 19 + 164 + 11 + 239 + 28,471 = 28,904; 126/126 on-disk spot checks;
   independent 175,187-file decide+kernel sweep: 34 files, 124 lines, 151 occurrences)

$ python3 verify/p4_flirt_check.py && python3 verify/f1_tier1_check.py && python3 verify/f3_check.py
P4-FLIRT-CHECK PASS (15/15)
F1-CHECK PASS (8/8)
F3-CHECK PASS (8/8)
  (Tier 1 v2: 20,692 alertable misfiles [3,283 high, 17,409 med], 16 bulk remaps [125,598 band], table_ok rank #200 score 0.9944;
   Clusters: 141 clusters = 1,468,414 live [846,496 core, 522,274 aux, 29,520 wrap, 70,021 k1n, 103 copy, 42.35% collapse],
   423/423 boundary decls, 2,099/2,099 edges;
   Tier 3 v2: 100 clusters, 0 leaks / 23,358 tokens; raw=63/100 κ=0.4820 other=55.0% subst=26/54 [48.15%];
   unfolded=42/100 κ=0.3456 other=10.0% subst=34/54 [62.96%, top-2=90.74%]; pack SHA-256 f0cab21555120f5a...)

$ python3 verify/a_check.py
A-CHECK PASS (36/36) fails=[]
  (ai__decomp-phase4.jsonl: 128 records, 128/128 k1n exact vs kernel.db, default_on=false, draft=true, tag=M, byte-identical export)
```

- **Independent C++ oracle diamond reachability (`verify/out/solution_oracle`, `114,115,002` edges):** `reach(everyCharacter_of_row) = 1,373,275`, `reach(galoisLocalGlobalStrong_recParameter) = 485,089`, `intersection = 389,987`, `reach(EveryCharacter) = 51,574`, `roots \ allChi = 35`, `diamond_k = 331,598` (`331,598 / 331,598` in `reach(row) ∩ reach(gal)`), `outside allChi = 58,857` (`58,826` Mathlib/Lean + `31` project decls across 8 bridge modules).
- **Independent `175,187`-file TCB security keyword sweep:** `0` hits across `unsafe`, `implemented_by`, `extern`, `csimp`, `skipKernelTC`, `native_decide`, `sorry`/`admit`/`sorryAx`, `axiom`, `opaque`, `autoImplicit true`, `global notation`; exactly `2` elaborator `partial def`s (`CutCptCopy.lean:41`, `OwnStruct.lean:18`).

### 4.3 Interactive Workbench (D6) Verification

```text
$ python3 verify/w2_probe.py --port 8438
W2-PROBE PASS (8/8)   (46 /api/* endpoints discovered & probed; 0 CDNs; 100% mode=ro SQLite; binds 127.0.0.1)

$ python3 workbench/probe_p3.py --port 8437 --annotations /tmp/leanre-v4-final
PROBE SUMMARY: 161 checks, 0 failed

$ google-chrome --headless=new --no-sandbox --disable-gpu --virtual-time-budget=30000 --dump-dom "http://127.0.0.1:8437/#selftest=1"
SELFTEST PASS — 157 checks, 0 errors (live=true)
FINAL p4/status: 6 / 6 compute=ready clusters=ready slice=ready
FINAL annot/layers: ai/decomp-phase4 (ai-draft, default_on=False, 128), human/canonical-facts (human, default_on=True, 5)
FINAL tier1 summary: extreme_outliers=714, cross_domain_misfiles=2569, isolated_ns_outliers=17409, bulk_remapped_modules=125598
```

Also verified: `--fixtures` mode `SELFTEST PASS — 157 checks, 0 errors` with persistent `synthetic`/`fixture` banner; `--outputs <empty>` graceful degradation (`HTTP 200 state=absent`, `decomp_ready=0`, `0` 500s across all 6 Phase 4 endpoints); all 7 screenshots visually verified (`p4_blueprint_map.png` 6/6 live, `p4_tcb_audit.png`, `p4_compute_atlas.png`, `p4_kernel_slice.png`, `p4_flirt_tier1_cal.png` showing `125,598`, `p4_flirt_clusters.png`, `p4_flirt_tier3_100.png`).

### 4.4 Full Regression, Tree Hygiene & Guardrail Audit (`0c95b2e`)

```text
$ python3 -m unittest discover -s leanre
Ran 136 tests in 1.770s — OK (skipped=2)

$ (cd leanre/kernel-rs && cargo test)
test result: ok. 10 passed; 0 failed; 0 ignored

$ python3 verify/audit_tree.py --leak
tracked=133 untracked-not-ignored=5 HEAD=0c95b2e
path: 0 | size: 0 | secret: 0 | internal: 0 | home: 2 (phase3_verification_report.md meta-text)
mirror files scanned: 175,187; verbatim hits: 48 (bare idents: 8, 1-line headers/imports: 35, BODY lines: 5 [all Phase 2 baseline])
(tracked file, mirror file) pairs sharing >= 3 distinct non-ident mirror lines: 3 (all Phase 2 baseline)
R2-AUDIT hard_findings=8   (0 Phase 3/4 findings)

$ python3 verify/r3_audit.py
Tripwire hits to inspect: 27   (all 27 inspected & confirmed benign: explicit negations, selftest assertions, Phase 3 report meta-text)
```

---

## 5. Explicit List of Unverified / Open Scope (Guardrails 1 & 5)

To keep epistemic boundaries unambiguous, the following items are **explicitly NOT claimed as verified** by this report:

1. **Deep proof bodies (`OPAQUE`):** Neither `@verifier` nor the Phase 4 workers audited multi-hundred-line Lean tactic bodies inside leaf theorems (`> ~30` lines), e.g., inside `large_unramified_exponent_bundles_exist_alt` (`37,318` decls), `dualAbelianScheme` gluing/deformation leaves (`glue`, `hasRepAF_of_relAmple`, `hasRep_pinched`, `hasRep_of_sqZero`), or the remaining `116 / 131` `GlobalTheory.Published.*` statement definitions not unfolded beyond headers. Their kernel validity rests on Layer 1 independent checkers; their human mathematical exposition remains Layer 3/4 work.
2. **Opt-in heavy real-data unit tests (`skipped=2`):** The 2 opt-in environment-gated tests (`LEANRE_ANNOT_REAL=1`, `LEANRE_REAL_DATA=1`) inside `unittest discover` were exercised separately via dedicated verifier scripts (`verify/a_check.py`, `verify/f1_tier1_check.py`, `verify/f3_check.py`, `verify/p4_*`) rather than re-triggering multi-minute rebuilds inside `unittest`.
3. **Pre-existing Phase 2 R2 baseline items (`hard_findings=8`):** `prototypes/concept_map_demo.html` (`2` lines + `1` multi), `outputs/forensics_report.json` (`3` snippet strings + `1` multi), and `outputs/workbench_bundle.json` (`1` multi) remain untouched from Phase 2, as recorded in `outputs/phase3_verification_report.md`.
4. **External peer consensus (Layer 4):** Independent mathematical refereeing of the claimed proof strategy (e.g., by analytic number theorists) is completely outside the scope of `leanre`.
