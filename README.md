# leanre

`leanre` is a reverse-engineering toolkit for large Lean 4 proofs: a Rust streaming extractor and Python CLI/web workbench that turn `lean4export` v3.1.0 archives into a SQLite declaration graph with dominator trees, taint paths, structural signature matching, virtual proof stripping, and portable JSONL annotation packs.

The links below audit Levent Alpöge and Claude's Nov 20, 2026 Lean 4 (`v4.33.1` / Mathlib `v4.33.1`) formalization claiming the **Riemann Hypothesis** and **Dirichlet-only Generalized Riemann Hypothesis** (`175,187` files, `17,374,215` lines `wc -l`, `0` comments, [pinned commit](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005), [companion note](https://alpo.ge/remark.pdf)). Kernel soundness and statement fidelity are not human mathematical refereeing or peer consensus (see [epistemic scope](research/04_verification_and_roadmap.md)).

## What the proof actually does

All numbers come from Andrew Sutherland's exported `solution.ndjson.zst` (`1,468,418` folded `con-leche` records / `1,484,733` unpacked `nanoda` constants / `114,115,002` typed dependency edges; `1,468,414` live, `4` unreferenced primitives). Each count below includes its node plus strict descendants (`subtree_size = self + children`).

```text
Main (5 roots: 2 zeta RH + 3 Dirichlet-only GRH; 1,468,414 live decls)
  bridge outside allChi                       58,857  # Mathlib FE reflection + 31 project decls
  allChi                                   1,409,557  # self (1) + everyCharacter (1,409,556)
    everyCharacter                         1,409,556  # self (1) + 3 branches below (= 96.0% live)
      galoisLocalGlobalStrong_recParameter    95,102  # Pillar B: odd-rank EtC tower + even theta lift
      everyCharacter_of_row                  982,855  # self (1) + 4 blocks below
        vwin_of_row                           92,705  # Pillar C: windowed Sha^1 length bound (VWin)
        every_character_of_theta_integrals   543,325  # Pillar A: HypsAlt producer + Landau consumer
        topCovolSlim2_use_alt_alt             80,720  # Pillar D: Arakelov / Moriwaki covolume bounds
        literature & row-side siblings       266,104  # theta/toroidal/resolution (225,278 incl. 1 self) + siblings (40,826)
      shared diamond                         331,598  # 100% reachable from both main branches
```

## Key findings

- **[Statements and trusted computing base](findings/tcb-and-statements.md)** — Independent checkers accept all five roots in [`Main`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L4) using only `[propext, Classical.choice, Quot.sound]` (`0` `sorryAx`, `0` `unsafe`/`implemented_by`/`extern`/`csimp`/`native_decide`/global `notation`). `riemannHypothesis` pulls `0` project definitions into its `2,448`-definition cone; the `5`-root union adds only the `4` wrapper lines in [`Statements`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Statements.lean#L3). Extended RH is not claimed. The unguarded division in [`Formalism.Gchi`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/StatementOC.lean#L20) is dead code; all three live observables guard `χ = 1`.
- **[Proof map and shared diamond](findings/proof-map.md)** — `everyCharacter` reduces to a single modus ponens splitting `95,102` Galois declarations against `982,855` analytic/automorphic declarations; the `331,598`-declaration diamond between them is `100%` reachable from both sides.
- **[Author note vs Lean code](findings/remark-vs-code.md)** — The exported proof contains `0` hits for a sixfold cover of `GL₅` (only a 2-fold metaplectic cover of `Sp`), `0` for global Kuznetsov / relative trace formula (local `JacquetRallis` unit matching and twisted `TraceFormula` run instead), and `0` for Stepanov's auxiliary polynomial (`Behrend` sets run instead).
- **[Dead code, timeouts, and `decide +kernel`](findings/dead-code-and-timeouts.md)** — Every file is imported by `Main`, yet `28,904` of `175,187` files (`2,378,537` lines) emit zero kernel declarations (`28,471` unused). Four of five `lean4lean` timeout files (`DyadicPrimeIntervals.Run1..4`) are dead; [`ChebyshevPrimeBounds.SmallLoop`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/SmallLoop.lean#L24) is live (`9/9`). Exactly `14` of `34` `decide +kernel` files are live.
- **[Proof size, virtual stripping, and macro blowup](findings/proof-size-and-bloat.md)** — Stripping unused files (`-28,885`), dead intra-file declarations (`115,829`), 1-node renaming aliases (`43,135` theorems), alpha clones (`571`), `k1n` duplicate theorem proofs (`54,510`), and duplicate imports (`13,583 / 19,750` duplicate `import Mathlib` lines sit inside pure-alias files) trims `175,187` files / `17,374,215` lines down to **`105,918` files (`60.46%`) / `12,904,172` lines (`74.27%`) / `1,310,025` decls**. Macro [`copy_cases`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RingSpecNormalisedCharacterEq.lean#L75) inflates 32-line [`lam_copy`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamCopy.lean#L15) to `5,538,373` `value_nodes`.
- **[Renaming shells, `True` stubs, and unread bundles](findings/aliases-and-dummy-slots.md)** — `43,135` live theorem wrappers have `value_nodes = 1` (`38,194` `GlobalTheory.T.*` + `4,941` outside it). Across all `387` `GlobalTheory.Published.*` definitions, only [`UnusedSlot72`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean#L7) is a literal `:= True` stub (plus [`UnusedSlot55`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/TrivialLocalCondition.lean#L89) under `UpperTheory.GalS`). Whole subtrees sit in unread struct fields (`OpenImageCondition` `0/1`, `LiteratureCMHypothesis` `0/11`, `UnitaryGroupThirdPlaceHypotheses` `13/60` unused + `1` `True`, `ThetaLocalInputs` `33/53` unused).
- **[Intentional shortcuts](findings/intentional-shortcuts.md)** — Local Langlands ([`recTExists`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean#L20)) returns a wild placeholder [`junkEx`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/JunkEx.lean#L257) off depth-zero tame inputs; non-toral local–global compatibility checks only inertia via [`AwayB.tame0`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean#L31); inside `StageU`, `23` live `*junk*` decls build a degenerate `DivX` geometry shell because [`anyGeometry`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean#L19) ignores it. None creates a soundness hole because consumers close without the dropped fields.
- **[Core mathematics grounded in Mathlib types](findings/genuine-math.md)** — Load-bearing interfaces unfold straight to Mathlib schemes, adeles, `CyclotomicField`, and `DirichletCharacter.LFunction`: [`VWin`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L49), étale cohomology `EtC`, `dualAbelianScheme`, char-0 embedded resolution of singularities, toroidal compactifications, semi-abelian uniformization, `Linnik`, and a windowed real-variable Laplace localization of Landau's theorem (the classical unwindowed draft is dead).

For deeper dossiers, see [the technical analyses](analysis/README.md); verification logs and scope notes live in [the research notes](research/README.md).

## Running the tool

```bash
# Test Python CLI and Rust kernel extractor
python3 -m unittest discover -s leanre -v
(cd leanre/kernel-rs && cargo test)

# Inspect virtual stripping waterfall and portable annotations
python3 leanre/leanre.py trim --from-report outputs/decomp/trim_report.json
python3 leanre/leanre.py annot validate annotations/

# Launch local interactive workbench (binds 127.0.0.1 only)
python3 workbench/server.py --port 8420
```

Docs: [CLI reference](leanre/README.md), [kernel extractor](docs/KERNEL.md), [signature hashing](docs/SIGHASH.md), [FLIRT header fingerprinting](docs/FLIRT.md), [cross-repo matching](docs/FLIRT_TIER2.md), [annotation packs](docs/ANNOTATION_PACKS.md), and [virtual stripping](docs/TRIM.md).

## License and credits

Tools, web UI, JSON schemas, and original documentation in this repository are licensed under [**GNU AGPL v3.0 or later**](LICENSE). The upstream proof archive ships with **no license**; no `.lean` files or multi-line proof bodies are redistributed here (`data/` and `research/sources/` are gitignored).

Builds alongside public verification work by [Andrew Sutherland](https://math.mit.edu/~drew/grh/), `leanprover-community/riemann-hypothesis` (formerly `Deicyde/riemann-hypothesis`), `nasqret/riemann-rev`, `jae-63`, `drew2apps`, `keithadler/rh-trim`, and `rgrossharv`.
