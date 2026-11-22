# Technical Dossiers

Start with the [summary findings](../findings/) before reading the longer dossiers below.

> **Scope:** These dossiers cover kernel validity, TCB fidelity, and proof structure over pinned commit `40e56bab` and `solution.ndjson.zst` (using inline provenance tags `[L]`/`[A]`/`[C]`/`[S]`/`[M]`). Deep inner proof bodies remain unread (`OPAQUE`), and human peer review is outside our scope (see [epistemic scope](../research/04_verification_and_roadmap.md)).

| Dossier | JSON data (`outputs/decomp/`) | Scope |
|---|---|---|
| [Whole-proof synthesis](SYNTHESIS.md) | — | Whole-proof map (`1,468,414` live decls), Layer 2 verdict, core discoveries. |
| [Spine & shared diamond](spine_and_diamond.md) | `spine_map.json` | `Main` → `allChi` → `everyCharacter`, `58,857` bridge, `331,598` shared diamond. |
| [Pillar A — Theta / definite side](pillar_theta.md) | `pillar_theta.json` | `543,325` decls (`37.0%`): `HypsAlt` producer (`StageU`) and consumer (`TopG`). |
| [Pillar B — Galois / `Row0b`](pillar_galois.md) | `pillar_galois.json` | `95,102` decls (`6.5%`): étale cohomology, `tLiftK`, `recTExists`, `AwayB.tame0`. |
| [Pillar C — Window / `VWin`](pillar_window.md) | `pillar_window.json` | `92,705` decls (`6.3%`): `VWin` (100% Mathlib), Kato, `Sp(4)`, `U(3)`, patching. |
| [Pillar D — Volume & literature](pillar_volume_lit.md) | `pillar_volume_lit.json` | `80,720` decls (`5.5%`): Arakelov/Moriwaki covolume bounds & `195` `*_of_literature` thms. |
| [TCB & bridge contracts](tcb_and_contracts.md) | `tcb_audit.json` | Statement-closure audit, `2,570`-def cone, `Formalism.Gchi` dead-code proof. |
| [Compute & dead code](compute_and_deadcode.md) | `compute_atlas.json` | Disjoint taxonomy of all `28,904` zero-kernel files & `34` `decide +kernel` files. |
| [Placeholders, Pillar A contracts & author-note gaps](deep_followup_audit.md) | *(prose audit)* | `Loc := Empty` / `η`, Pillar A contracts, `remark.pdf` gaps, `dualAbelianScheme`. |
| [Explicit-formula & Landau bridge](explicit_formula_bridge.md) | `explicit_formula_bridge.json` | Windowed `Gm(y) ≤ y^θ` Landau zero-free bridge (`23,523`-decl consumer vs. dead unwindowed draft). |
| [`StageU` existence engine](stageu_existence.md) | `stageu_existence.json` | `37,318`-decl `large_unramified_exponent_bundles_exist_alt`, `StepW` automaton, `divXFl` stubs. |
| [Pillar A — `StageU` / `AllRows` / `Open0` spine](stageu_hyps_spine.md) | `stageu_hyps_spine.json` | Core `414,292` decls of Pillar A (`allRows_of_open0_alt`, `GalC`, `ontoX`, `open0`, unread fields). |
| [Pillar B — `geoOne_holds` odd-rank étale tower](geo_one_galois.md) | `geo_one_galois.json` | `82,643` decls (`86.9%` of Pillar B): `EtC`, Lefschetz, exact origin of `AwayB.tame0`. |
| [Literature & algebraic-geometry engines](literature_engines.md) | `literature_engines.json` | Six named engines (`toroidalForFanKS`, `canonicalAlgorithmRules_isCorrect`, semi-abelian uniformization, `hsChain`, `theta_integrals_agree`). |
| [Published theorems, stubs & `*junk*` catalogue](published_catalogue.md) | `published_catalogue.json` | All `387` `GlobalTheory.Published.*` defs, `131` bundle `Prop`s, `9` `UnusedSlot*` namespaces, and `57` live `*junk*` decls. |
