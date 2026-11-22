# Technical Dossiers

Start with the [summary findings](../findings/) before reading the longer dossiers below.

> **Scope and limits (Layers 1–3):** These `50` dossiers cover kernel validity, TCB fidelity, and proof architecture over pinned commit `40e56bab` and `solution.ndjson.zst` (using inline provenance tags `[L]`/`[A]`/`[C]`/`[S]`/`[M]`). All `999 / 999` live declarations with dominator `subtree_size >= 1,000` are audited across `45` decompilation blueprints (`3,478` unique inspected nodes). Inner tactic bodies remain unread, and Layer 4 human peer review is outside our scope (see [epistemic scope](../research/04_verification_and_roadmap.md)).

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

## Corpus sweeps

| Dossier | JSON data (`outputs/decomp/` or `flirt/`) | Scope |
|---|---|---|
| [Unread bundles & placeholders census](unread_bundles_census.md) | `unread_bundles_census.json` | Source-verified audit of all `5,497` live 1-ctor project inductives, unread fields, and `0`-field placeholders (`leanre bundles`). |
| [Whole-corpus structural anomaly sweep](anomaly_sweep.md) | `anomaly_sweep.json` | `Empty.elim`, 24-keyword triage, `lam_copy` / `rlΘ₂._proof_1` blowups, `0`-comment verification, headline arithmetic check. |
| [Cross-repo overlap & intra-proof duplication](duplication_and_overlap.md) | `trim_report.json` | `173` cross-repo `k1n` theorems, `30,055` intra-proof `k1n` clusters (`86.6%` incomparable pairs), `320` `alpha_body_clone` split, FLIRT misfiles. |
| [FLIRT `141`-cluster mathematical atlas](cluster_atlas_141.md) | `../outputs/flirt/cluster_labels_141.json` | Fail-closed name-blinded vs. directory audit of all `141` coarse clusters (`66` misplaced, `30` drift, `45` aligned). |
