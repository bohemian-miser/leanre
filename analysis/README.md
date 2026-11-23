# Technical Dossiers

Start with the [summary findings](../findings/) before reading the longer dossiers below.

> **Scope & Tag Legend:** These `79` dossiers document kernel graph structure, statement-closure fidelity, quantitative inequalities, hygiene sweeps, cross-repository comparisons, and literature attribution checks over pinned commit `40e56bab` and `solution.ndjson.zst` (plus source-only comparisons for external corpora). All `999 / 999` live declarations with dominator `subtree_size >= 1,000` are audited across `45` decompilation blueprints (`3,478` unique inspected nodes). Machine-checked kernel soundness and statement fidelity do **not** substitute for human mathematical peer review, and inner tactic bodies beyond inspected headers and wiring remain unread (see [verification scope](../research/04_verification_and_roadmap.md)).
> **Tags:** **`[L]`** verified directly in pinned `.lean` sources or `outputs/kernel/kernel.db` (`[K]` kernel-graph invariant); **`[S]`** standard published mathematics or Lean/Mathlib semantics; **`[C]`** formalization scope limit or caveat (or community report); **`[M]`** structural synthesis or reading; **`[A]`** author prose (`alpo.ge/remark.pdf`); **`OPAQUE`** declaration whose inner body was not unfolded or read line-by-line.

## Mathematical reading guide & deep chain audits

| Dossier | JSON data (`outputs/`) | Scope |
|---|---|---|
| [RH proof mathematical reading guide](rh_proof_exposition.md) | — | End-to-end mathematical reading guide from `Main` through windowed Landau, `meanSqK` (`siegelLower` in `count_a` exp `1`), `ASK − MAIN = De`, and the `11` slope inequalities. |
| [Pillar A / C / D quantitative bridge](pillar_ad_quantitative_bridge.md) | — | Constant propagation from Pillar D `topCovolSlim2_use_alt_alt` → `CovolumeBoundOfX` → `LinkDIV`, Pillar A `StageU` → `HypsAlt` → `ChainTied`, and Pillar C `VWin` → `divinN_of_hypV`. |
| [`LinkG`, rank-$m$ scaling & `DIV`/`Count5`](audit_linkg_slope_error.md) | — | Proves `LinkG` is per-prime bookkeeping (no Chebotarev), checks quantifier-enforced $m$-free errors (`Count5`/`DIV`/`Slopes`), exact `key_identity` main-term match, and `link_of_local_closed` drops. |
| [`ch_balance`, `Places_at` & `LinkDIV_at`](audit_places_div_and_balance.md) | — | Unpacks exact finite Fourier identity `ASK − MAIN = De`, Arakelov degree formula `Places_at`, `DIVinN` handoff, and locates downward force in `JointARam` + `BoundsMu`. |
| [`JointARam`, `BoundsMu` & `L3main` ($\log\Omega$)](audit_jointaram_boundsmu_l3main.md) | — | Audits `JointARam` (`dom=208`, Bost + HN + frame + layer cake, `log|I|` pure slack), `BoundsMu` (`dom=79`, product formula + `DetCS`), trivial `L3main`, and proved Chowla–Selberg + Kronecker limit → `FlatDegree`. |
| [`UAt`, arithmetic Hilbert–Samuel & $c_1$-matching](audit_uat_and_c1_matching.md) | — | Unpacks `atPoint`/`core` (`20` proj decls), corrects `HSAt` vs `HeightAt` (`q9` feeds `volume_line_bundle_le`), verifies `arith_hilbert_samuel_of_literature` ignores `O`, and confirms $c_1 + \frac{p-q}{2}\log\Omega = -q(\log d - \mathrm{lrd}_E)$ normalization. |
| [Pillar D `deep_slim_use` & `MeanAll` bound](audit_deep_slim_use.md) | — | Unpacks `deep_slim_use` (`dom=46,110`) → `deepStR_of_use` (`45,411`), tracing `MeanAll` strength to tower bound `T2` (`ZhangLowerX` via `HSUse.1` + `NineGeoU` → `chain_tower`); Bergman kernel affects only `MultAt`. |
| [Analytic zero-repulsion leaves (`siegelLower`/`count_a`) & `ZhangLowerX`/`T2` constants](audit_siegel_zhang_leaves.md) | — | Audits `siegelLower`, `count_a`, Deuring–Heilbronn / log-free zero density, and closes the remaining `ZhangLowerX` / `T2` cusp and remainder constants beneath `deep_slim_use` (`hsUse_outright`). |
| [`MultEq` & `twisted_multiplicity_eq`](audit_multeq_harish_chandra.md) | — | Traces `9` `MultEq` producers as one chain (`twisted_multiplicity_eq` `5,814`), confirms all `10` `Published.*` adapters close in-repo ignoring `OpenLiteratureStatements`, and corrects `harish_chandra_and_hironaka_core.md`. |
| [`StageU` existence & `RankVal` exponents](audit_stageu_existence_math.md) | — | Traces `RankVal` ($n \asymp x^{2+8\varepsilon}$, $m \asymp x^{1/2-\varepsilon/16}$, $k \asymp x^{9/2+10\varepsilon}$), consumer-side `exists_ranks_rankVal_frame` (`dom=9`), $x^{5\varepsilon}/2$ slack on $k/n^2$, `anyGeometry := True`, `SExt.none := PUnit`, and `FamP.Large`. |
| [Frame order, $m^5$ & bundle witness](audit_frame_order_and_m5.md) | — | Audits explicit 2-power cyclotomic frame (`fieldChi`, `dom=404`), $m^5 = m^2 \cdot m \cdot m^2$ birth in weighted orbital bounds, `bwit_exists_alt` adelic evaluation map, and `memberE_closing_alt_alt`. |
| [Upstream `WBp`, $m^5 = m^2 \cdot m^3$ & `sEEofTT`](audit_wbp_and_seeoftt.md) | — | Discharges upstream `WBp` unconditionally via `ThmBFinal` (`dom=2,368`, `0` `Published.*`), confirms `sEEofTT` uses `dif_pos` only (`5/5` live sites), `RealInAlt`'s `3` conditional-in-form-only fields, and theta-lift adjoint injectivity placement. |
| [Pillar C `vwin_of_row` & continuous $\mathrm{Ш}^1$](audit_vwin_shafarevich.md) | — | Confirms genuine continuous $\mathrm{Ш}^1_{S_\ell}$ (not a proxy), `401 = 1 + 400` rescaling margin, $\frac{1}{2}$ asymptotic slack ($4\varepsilon/5 \to \varepsilon$) dropped in `divinN_of_hypV`, and `7` `dom >= 2,000` sub-engines. |

## Core

| Dossier | JSON data (`outputs/decomp/`) | Scope |
|---|---|---|
| [Whole-proof synthesis](SYNTHESIS.md) | — | Whole-proof map (`1,468,414` live decls), Layer 2 verdict, core discoveries. |
| [Spine & shared diamond](spine_and_diamond.md) | `spine_map.json` | `Main` → `allChi` → `everyCharacter`, `58,857` bridge, `331,598` shared diamond. |
| [Shared diamond & row siblings](diamond_shared_library.md) | `diamond_shared_library.json` | All `18` shared-diamond roots (`dom >= 1,000`, `32,213` decls) & top `10` row-side siblings (`10,915` / `40,826`); `0/28` stubs. |
| [TCB & bridge contracts](tcb_and_contracts.md) | `tcb_audit.json` | Statement-closure audit, `2,570`-def cone, `Formalism.Gchi` dead-code proof. |
| [Compute & dead code](compute_and_deadcode.md) | `compute_atlas.json` | Disjoint taxonomy of all `28,904` zero-kernel files & `34` `decide +kernel` files. |
| [Live 14 `decide +kernel` audit](decide_kernel_live14.md) | `decide_kernel_live14.json` | Line-by-line audit of all `14` live `decide +kernel` files (`18` live decls, `35` auxes, `0` Pillar B) vs `20` dead files. |
| [Placeholders, Pillar A contracts & author-note gaps](deep_followup_audit.md) | *(prose audit)* | `Loc := Empty` / `η`, Pillar A contracts, `remark.pdf` gaps, `dualAbelianScheme`. |
| [Published theorems, stubs & `*junk*` catalogue](published_catalogue.md) | `published_catalogue.json` | All `387` `GlobalTheory.Published.*` defs, `131` bundle `Prop`s, `9` `UnusedSlot*` namespaces, `57` live `*junk*` decls. |
| [Explicit-formula & Landau bridge](explicit_formula_bridge.md) | `explicit_formula_bridge.json` | Windowed `Gm(y) ≤ y^θ` Landau zero-free bridge (`23,523`-decl consumer vs. dead unwindowed draft). |

## Pillar analyses

| Dossier | JSON data (`outputs/decomp/`) | Scope |
|---|---|---|
| [Pillar A — Theta / definite side](pillar_theta.md) | `pillar_theta.json` | `543,325` decls (`37.0%`): `HypsAlt` producer (`StageU`) and consumer (`TopG`). |
| [`StageU` existence engine](stageu_existence.md) | `stageu_existence.json` | `37,318`-decl `large_unramified_exponent_bundles_exist_alt`, `StepW` automaton, `divXFl` stubs. |
| [Pillar A — `StageU` / `AllRows` / `Open0` spine](stageu_hyps_spine.md) | `stageu_hyps_spine.json` | Core `414,292` decls of Pillar A (`allRows_of_open0_alt`, `GalC`, `ontoX`, `open0`, unread fields). |
| [Pillar A — `AllRowsAlt` engines](allrows_engines.md) | `allrows_engines.json` | `54,172`-decl `allRows_of_open0_alt`: `26` fields, `6` engines, `0` `Behrend` hits in its `513,972`-decl cone. |
| [Pillar A — `AllRows` & `stmtE` leaves](allrows_and_stmte_leaves.md) | `allrows_and_stmte_leaves.json` | Inner `AllRows`, `ExportClose`, and `TraceSpectra.stmtE` leaves. |
| [Pillar A — `linkG` consumer bridge](linkg_consumer_bridge.md) | `linkg_consumer_bridge.json` | `19,248`-decl `shape_closed_link_n_of_green` quantitative consumer bridge. |
| [Pillar A — `famAllQ` / `TheoremT` / `NLinkE`](pillar_a_famallq_engines.md) | `pillar_a_famallq_engines.json` | `famAllQ`, `colSide`, `lawsLinks`, `InertStep`, `TheoremT`, `NLinkE`, and dropped `BlochKatoLocal` binders. |
| [Pillar A — `ontoX`, `GalC`, & `open0`](pillar_a_onto_galc_open0.md) | `pillar_a_onto_galc_open0.json` | Sibling mega-subtrees `ontoX_and_lamLow`, `GalC.final_alt_alt`, and `open0`. |
| [Pillar A — inner `2,300..3,400` leaves](pillar_a_inner_leaves.md) | `pillar_a_inner_leaves.json` | Inner `2,300..3,400`-decl leaves (`besselNVG`, etc.). |
| [Pillar A — theta inner engines](theta_inner_engines.md) | `theta_inner_engines.json` | `22,215` dom decls: RSW residue, symmetric forms, Selmer N5, square top, Theorem I, grid frames. |
| [Pillar A — theta deep leaves](theta_leaves_deep.md) | `theta_leaves_deep.json` | `42,414` dom decls: theta, Gram, lattice, Bessel, and Fourier-fit leaves. |
| [Pillar A — `FourierDecay` & `ColRows`](fourier_and_colrows_leaves.md) | `fourier_and_colrows_leaves.json` | `21,592` disjoint decls: `FourierDecay`, `SumSize`, `ColRows`, `Ln17`/`Ln34`. |
| [Counting, prime sums & moments](counting_and_prime_sums.md) | `counting_and_prime_sums.json` | `9` analytic/counting leaves (`sum_over_primes_service`, `dsExhaust`, `refinedSum_weight_of_size_alt` dropping `DeepGoodness`). |
| [Pillar B — Galois / `Row0b`](pillar_galois.md) | `pillar_galois.json` | `95,102` decls (`6.5%`): étale cohomology, `tLiftK`, `recTExists`, `AwayB.tame0`. |
| [Pillar B — `geoOne_holds` odd-rank tower](geo_one_galois.md) | `geo_one_galois.json` | `82,643` decls (`86.9%` of Pillar B): `EtC`, Lefschetz, origin of `AwayB.tame0`. |
| [Pillar B — `AwayB.tame0` upward trace](away_tame0_trace.md) | `away_tame0_trace.json` | Complete upward trace: `0` Pillar C callers, `1` global caller (`away_nice`), `Aw.unr` bypass via `AwayB.tor`. |
| [Galois fixed points, `Et.D2` & antisymmetry](galois_fixedpoints_and_d2.md) | `galois_fixedpoints_and_d2.json` | Galois fixed points, misnamed `Et.D2.intersectionNumber_baseChange`, and Pillar D antisymmetry. |
| [Pillar C — Window / `VWin`](pillar_window.md) | `pillar_window.json` | `92,705` decls (`6.3%`): `VWin` (100% Mathlib), Kato, `Sp(4)`, `U(3)`, patching. |
| [Pillar C — `VWin` internal engines](vwin_engines.md) | `vwin_engines.json` | `vwin_of_row` → `automorphic_window_of_inputs` decomposition. |
| [Kato, étale Gysin/Lefschetz & spectral leaves](kato_and_etale_leaves.md) | `kato_and_etale_leaves.json` | Kato unit law, étale Gysin purity, Lefschetz, misnamed `LeafThom.intersectionNumber_baseChange`, Jacquet–Shalika rigidity. |
| [Pillar C — Kato Euler system & `SymPow`](kato_euler_and_sympow.md) | `kato_euler_and_sympow.json` | Siegel-unit Kato integrality (`Kd.K4`), Shimura reciprocity (`K5.hco`), `specF`/`tFId0`, `seedII_Z_alt`. |
| [Pillar D — Volume & literature](pillar_volume_lit.md) | `pillar_volume_lit.json` | `80,720` decls (`5.5%`): Arakelov/Moriwaki covolume bounds & `195` `*_of_literature` theorems. |
| [Pillar D — covolume & Moriwaki engines](covolume_engines.md) | `covolume_engines.json` | `topCovolSlim2_use_alt_alt` (`deep_slim_use`, `topCovolG_alt_alt`, Bost slope, `CovolumeBoundOfX`). |
| [Pillar D — Arakelov volume & `HodgeModel`](arakelov_volume_engines.md) | `arakelov_volume_engines.json` | `volumeTheoremX_of_inputs` and `HodgeModel` engines. |

## Classical theorems

| Dossier | JSON data (`outputs/decomp/`) | Scope |
|---|---|---|
| [Classical theorems index (`60` milestones)](famous_theorems_index.md) | `famous_theorems_index.json` | `60` classical theorems rated `full`/`narrow`/`conditional`/`wrapper`/`misnamed`/`header-only`, plus `3` misnamed cases. |
| [Literature & algebraic-geometry engines](literature_engines.md) | `literature_engines.json` | Core engines: `toroidalForFanKS`, `canonicalAlgorithmRules_isCorrect`, semi-abelian uniformization, `hsChain`, `theta_integrals_agree`. |
| [Classical & arithmetic geometry leaves](classical_geometry_leaves.md) | `classical_geometry_leaves.json` | `strongResolutionOfSingularitiesCharZero`, `arithHilbertSamuel_of_principalisation`, `good_chern_weil_of_literature`, `zhGeo`, `globalEulerChar_of_lemmaX`. |
| [Harish-Chandra, Hironaka, Mumford & Hodge–de Rham](harish_chandra_and_hironaka_core.md) | `harish_chandra_and_hironaka_core.json` | `twisted_multiplicity_eq`, Hironaka `canonicalAlgorithmRules_isCorrect`, `principalisation_closed`, `semistableReductionSt`, `mumfordProportionality`, `abelianHodgeDeRham'`. |
| [Toroidal compactification, log KS & `closeSph`](compactification_and_sph.md) | `compactification_and_sph.json` | `closeSph`, Siegel & unitary toroidal compactification, Čech-cocycle log Kodaira–Spencer (`hasLogKS`), `theoremHSMBlock`. |
| [Siegel–Weil, $p$-adic monodromy & Wach lattices](siegel_weil_and_padic.md) | `siegel_weil_and_padic.json` | `siegelWeilStd`, `SiegelWeilCoefficients.field`, `Sw47.weilUnitary`, matrix-form $p$-adic monodromy, `wach_lattices` toy `D7` leak. |
| [Convolution, Jacquet–Rallis & profinite cohomology](convolution_and_profinite_leaves.md) | `convolution_and_profinite_leaves.json` | `unitMatch_all` (local JR), `downN`, `gm_of_unit`, `eigInert`, `bijective_gsRealRes` (Poitou–Tate), `multiplicity_formula_holds`, `ssPotB_at_newform`. |

## `dom >= 1,000` closures

| Dossier | JSON data (`outputs/decomp/`) | Scope |
|---|---|---|
| [Upper closure `1,763..3,767`](dom1500_closure_kudla_siegel.md) | `dom1500_closure_kudla_siegel.json` | `26` targets: `closed_of_open_positive`, `join_out_of_literature`, `kudla_splitting_split_unitary_of_literature`, `siegelDeg`, `heckeInt_transform_readTie`, Capelli bounds. |
| [Closure `1,503..1,744`](dom1500_closure_jets_coh.md) | `dom1500_closure_jets_coh.json` | `37` targets: `twisted_jets_assemble` (drops `ThetaLocalInputs`), toroidal charts, `rsPole_of_inputs`, Grothendieck `finiteH_of_isProper`. |
| [Closure `1,354..1,496`](dom1000_closure_s1.md) | `dom1000_closure_s1.json` | `50` targets: `formal_algebraisation_of_literature`, `exists_isArtinK`, `Et.E3.main`, `arcFam_closed`. |
| [Closure `1,185..1,341`](dom1000_closure_s2.md) | `dom1000_closure_s2.json` | `50` targets: Nadel vanishing, Bernstein unitary irreducibility, `chernWeilNumbers_holds`, `LPTied`/`NTiedG` placeholder cones. |
| [Closure `1,077..1,184`](dom1000_closure_s3.md) | `dom1000_closure_s3.json` | `50` targets: `bhatt_scholze_integral_of_literature`, `defect_bound_of_connected_alt`, `localConstants_from_admitted_local_Galois_statements`, Kawamata–Viehweg vanishing. |
| [Closure `1,002..1,077`](dom1000_closure_s4.md) | `dom1000_closure_s4.json` | `51` targets: `coreFiniteGL`, `DualExist.exists_dual`, Kawamata–Viehweg spreading, `torsor_trivial`. |

## Blueprint, semantic audits & portability

| Dossier | JSON data (`outputs/`) | Scope |
|---|---|---|
| [Quantitative inequality blueprint](rh_inequality_blueprint.md) | — | End-to-end parameter chain from `Main` through `VWin`, `RankVal` balancing (`SZ.T1..T4`), `core_gm`, and windowed Landau localization. |
| [Mean-square `1/2`-exponent drill-down](mean_square_half_exponent.md) | — | Traces the analytic $1/2$ exponent in Pillar A: dead `MeanSquareHypW` vs live `QH.meanSqK` (quadratic reciprocity + Landau–Page) and dyadic Gallagher–Sobolev `bad_share`. |
| [Live replacements for `remark.pdf` gaps](remark_replacements_deep.md) | — | Deep trace of 2-fold Weil–Shale `Mp.sub` (`howeDualityReal_holds`), disjoint local `JR.unitMatch_all` vs untwisted simple elliptic `TRCusp'`, and Behrend `thickFrame2`. |
| [Literature attribution check: $p$-adic monodromy](adversarial_monodromy_recheck.md) | — | Second-pass verification of `deRham_potentiallySemistable`: pins **Colmez (2008, *Astérisque* 319)** Robba-free route (Moore determinants + $A_{\mathrm{cris}}$ Gauss-norm substitute), clears earlier caveats. |
| [Literature attribution check: Hironaka resolution](adversarial_hironaka_recheck.md) | — | Second-pass verification of `strongResolutionOfSingularitiesCharZero` & `canonicalAlgorithmRules_isCorrect`: **Kollár (2007) Ch. 3 + Encinas–Villamayor + Bierstone–Milman**, étale descent `BlowupSequenceDescentDatum`, `balancedTunedSheaf` `lcm` exponent. |
| [Literature attribution check: cohomology, Hodge–de Rham, Euler & Kato](adversarial_cohomology_recheck.md) | — | Second-pass verification: Grothendieck EGA III₁ Thm. 3.2.1 (`Spec A`), Oda / Mazur–Messing / BBM char-free abelian Hodge–de Rham (`Hopf F True` benign), Tate (1962) Global Euler–Poincaré, Poitou–Tate real-place iso, Kato (2004) Euler system (`0` Kato log geometry). |
| [Semantic audit: Robba-free $p$-adic monodromy](audit_padic_monodromy_semantic.md) | — | Initial definition audit of `deRham_potentiallySemistable` (see [monodromy attribution check](adversarial_monodromy_recheck.md) for updated attribution & cleared caveats). |
| [Semantic audit: resolution & Kato `Tower`](audit_hironaka_and_kato_semantic.md) | — | Initial definition audit of `strongResolutionOfSingularitiesCharZero` & Kato `Tower` (see [Hironaka attribution check](adversarial_hironaka_recheck.md) & [cohomology/Kato attribution check](adversarial_cohomology_recheck.md)). |
| [Semantic audit: proper cohomology, Hodge–de Rham & Euler char](audit_cohomology_hodge_euler_semantic.md) | — | Initial definition audit of `finiteH_of_isProper`, `abelianHodgeDeRham'`, `globalEulerChar_full`, and `bijective_gsRealRes` (see [cohomology attribution check](adversarial_cohomology_recheck.md)). |
| [Mathlib portability gems (`7` theorems, `4` islands)](mathlib_portability_gems.md) | `../outputs/portability_gems.json` | Cone extraction across `7` classical theorems (`44,858` project decls, `2,978` modules), finding `4` pairwise-disjoint project islands. |

## Corpus sweeps & cross-repo benchmarks

| Dossier | JSON data (`outputs/`) | Scope |
|---|---|---|
| [Top-spine hygiene & toy-witness audit](spine_hygiene_audit.md) | — | `206`-decl critical-path `kernel hygiene` sweep (`0/213` soundness bugs) and `bundles --instantiations` over top `10` interfaces + `DivX` (newly cataloged `llOf_alt`, `exists_baseLattice_of_prime_alt`, `Examples₂.H0`, `6` `*_of_open`, `zL_of_hPA`, `doubling_method`/`ResidueKilled.DM`). |
| [Cross-repository static analysis benchmark (five external corpora)](generic_corpus_trial.md) | `../outputs/xrepo_benchmark.json` | Default-CLI benchmark across `tiny_demo`, `PrimeNumberTheoremAnd`, `carleson`, `FLT`, and `SpherePacking` (`init`/`scan`/`forensics`/`flirt`, plus full `tiny_demo` kernel/trim/bundles/export-site pipeline). |
| [Comparative audit: `navier-stokes` vs. `NavierStokesAndEuler`](navier_stokes_comparison.md) | — | Source-only structural, statement-assumption, and `sorry`/TCB comparison of `tristanbuckmaster/navier-stokes` (unforced, conditional on external certificate) and `openai/NavierStokesAndEuler` (forced NS + unforced Euler, unconditional) against `riemann-hypothesis`. |
| [Unread bundles & placeholders census](unread_bundles_census.md) | `decomp/unread_bundles_census.json` | Source-verified audit of all `5,497` live 1-constructor project inductives, unread fields, and `0`-field placeholders (`leanre bundles`). |
| [Whole-corpus structural anomaly sweep](anomaly_sweep.md) | `decomp/anomaly_sweep.json` | `Empty.elim`, 24-keyword triage, `lam_copy` / `rlΘ₂._proof_1` blowups, `0`-comment verification, headline arithmetic check. |
| [Cross-repo overlap & intra-proof duplication](duplication_and_overlap.md) | `decomp/trim_report.json` | `173` cross-repo `k1n` theorems, `30,055` intra-proof `k1n` clusters (`86.6%` incomparable pairs), `320` `alpha_body_clone` split, directory-vs-signature outliers. |
| [Independent proofs of identical statements & dependency map](alien_proof_twins.md) | `../outputs/atlas_summary.json` | Splits `92,457` non-trivial `k1n` buckets by proof-value Jaccard (`8,107` disjoint-proof pairs / `253` raw cross-repo pairs; see [253-pair audit](alien_twins_mathlib_audit.md) debunking `galois_t2Space` and `instIsDomain`), plus `114M`-edge dominator-DFS dependency matrix and `79,267`-hit Mathlib overlap profile. |
| [Verification of 253 cross-repository duplicate-statement pairs](alien_twins_mathlib_audit.md) | `../outputs/atlas_summary.json` | Audits all `253` cross-repo disjoint-proof pairs (`0/253` novel deep compressions; `galois_t2Space` calls `inferInstance` on Mathlib's own instance; `instIsDomain` is misattributed RH↔RH) and top `5` intra-project ratio illusions. |
| [2D embedding cross-directory drift & bridge audit](embedding_drift_audit.md) | `../outputs/embedding_2d.json` | Audits top `20` highest-drift `dom >= 1,000` landmarks (`15` true misfilings, `1` bridge, `4` artifacts) and all `10` cross-island corridor bridges (`7/7` `dom >= 1,000` genuine AG↔ANT bridges). |
| [141-cluster partition of the live kernel graph](cluster_atlas_141.md) | `flirt/cluster_labels_141.json` | Name-redacted signature topic vs. directory audit of all `141` coarse clusters (`66` misplaced, `30` drift, `45` aligned). |
