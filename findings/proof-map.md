# Proof map: from Main to the four pillars and shared diamond

All five headline theorems in [`Main`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L4) reduce to one Mathlib-stated predicate, [`UpperTheory.EveryCharacter`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean#L13) (Dirichlet $L$-functions do not vanish on $\operatorname{Re}(s) > 1/2$ except at $\chi = 1, s = 1$). Its proof [`allChi`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Supplements/Kernels/MainTheorems.lean#L7) dominates `1,409,557` of the `1,468,414` live declarations in the kernel export (`96.0%`; the remaining `4` of `1,468,418` `con-leche` records are unreferenced export primitives).

## Dominator skeleton of the live kernel graph

```text
Main (5 headline theorems; 1,468,414 live decls; counts include each node's self = 1)
  bridge outside allChi                       58,857  # 58,826 Mathlib/Lean + 31 project decls (FE reflection)
  allChi                                   1,409,557  # self (1) + everyCharacter (1,409,556)
    everyCharacter                         1,409,556  # self (1) + 3 direct branch sums below
      galoisLocalGlobalStrong_recParameter    95,102  # Pillar B (6.48%): l-adic Galois reps -> Row0b recT
      everyCharacter_of_row                  982,855  # self (1) + 3 subtrees below (66.93%)
        vwin_of_row                           92,705  # Pillar C (6.31%): windowed Sha^1 length bound (VWin)
        every_character_of_literature_of_vWin 849,323 # self (1) + 3 subtrees below (57.84%)
          every_character_of_theta_integrals  543,325 # Pillar A (37.00%): HypsAlt producer (451,610) + consumer (23,523)
          topCovolSlim2_use_alt_alt            80,720 # Pillar D (5.50%): Arakelov / covering covolume bounds
          literature & classical subtrees     225,277 # theta/toroidal/resolution/published residual (excludes 1 self)
        shared row-side siblings              40,826  # used by both Pillar C and literature side (globalEulerChar, ...)
      shared diamond                         331,598  # 22.58% across 110,898 children; 100% reachable from both sides
```

## Modus ponens at the waist

[`everyCharacter`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L10) applies one implication to one unconditional Galois-representation theorem:

- [`galoisLocalGlobalStrong_recParameter`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean#L6) (`95,102` decls) proves `Row0b recT`, where [`recT`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/Development.lean#L18) is an alias for `IsRecT`. It builds odd-rank representations in étale cohomology of unitary Shimura towers ([`geoOne_holds`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/WeightOneGeometricRealization.lean#L11), `82,643` decls) and handles even ranks via definite-unitary theta lifts ([`tLiftK`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TLiftK.lean#L4), `4,104` decls).
- [`everyCharacter_of_row`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L7) (`982,855` decls) packs `⟨h, recTExists, h⟩` into [`OpenLiteratureStatements`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L215) (nothing is assumed as an axiom), feeds `h` into [`vwin_of_row`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean#L4) to obtain `VWin`, and passes both to [`every_character_of_literature_of_vWin`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L810).
- Inside Pillar A, [`every_character_of_theta_integrals_local_matching`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L69) (`543,325` decls) splits into a `451,610`-decl producer ([`nonempty_hyps_definite_side_of_closed_bound`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L44)) inhabiting the 46-field record `HypsAlt`, and a `23,523`-decl consumer ([`every_character_of_green_v_win`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean#L16)) deriving `ZeroFreeAll` and `EveryCharacter`.
- Pillar D ([`topCovolSlim2_use_alt_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopCovolSlim2Use.lean#L16), `80,720` decls) discharges `CovolumeBoundOfX` via [`deep_slim_use`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/CoreStatements/AutomorphicKernels/MoriwakiBigness/HilbertSamuelApplications/AhSlimU.lean#L9) (`46,110` decls) and covering-geometry height estimates (`20,154` decls).

## Bridge outside allChi

Only `31` project declarations and `58,826` Mathlib/Lean declarations sit outside `allChi`'s dominator subtree (`58,857` total reachable from the five roots without passing through `allChi`, of which `35`—`29` project + `6` library—are reachable exclusively outside `allChi`). Every bridge step uses textbook Mathlib functional-equation reflection:

- [`rh_of_every`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GammaFactorNonvanishing/CritLine.lean#L29) specializes `allChi` to `N = 1` (`LFunction 1 = riemannZeta`), then [`rh_of_right`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GammaFactorNonvanishing/RhOfRight.lean#L5) reflects zeros across $\operatorname{Re}(s) = 1/2$ using `riemannZeta_one_sub` and `riemannZeta_zero`.
- [`critLine`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GammaFactorNonvanishing/CritLine.lean#L11) reflects primitive Dirichlet characters via `completedLFunction_one_sub`, and [`Claim.strip`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L59) strips non-vanishing Euler factors on $\operatorname{Re}(s) > 0$ for imprimitive characters.

## Shared diamond, audit coverage, and coarse FLIRT clustering

Removing the two main branches under `everyCharacter` leaves `110,898` direct dominator children totaling `331,598` declarations (`63.4%` project, `36.0%` Mathlib/Lean; `81,857` are singletons and only `18` roots exceed `1,000` decls). Exact forward reachability over all `114,115,002` kernel edges shows `331,598 / 331,598` (`100%`) are reachable from both `everyCharacter_of_row` and `galoisLocalGlobalStrong_recParameter`—this is a shared library rather than a hidden third argument. It holds `100` of the `387` `GlobalTheory.Published.*` definitions, including [`jacquetRallisUnitMatch_all_ranks`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisUnitMatchAllRanksStatement.lean#L6) (`1,957`), [`dualAbelianScheme`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualAbelianSchemeExistsBiduality.lean#L29) (`1,363`), and [`recTExists`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean#L20) (`595`).

- All `999 / 999` (`100%`) live declarations with dominator `subtree_size >= 1,000` are audited across `45` decompilation blueprints (`3,478` unique inspected nodes out of `4,374` indexed blueprint nodes) and `50` [technical dossiers](../analysis/README.md); deep tactic bodies beneath remain unread.
- Inspecting all `18` shared-diamond roots with `dom >= 1,000` (`32,213` decls) and the `10` largest row-side siblings (`10,915` of `40,826` decls; `0` Pillar B callers) finds `0 / 28` stubs or vacuous goals (`13` Mathlib-grounded [`8` diamond, `5` row], `10` narrow special cases [`6` diamond, `4` row], `4` single-node wrappers over real proofs [`3` diamond, `1` row], `1` concrete-tied abstract record — see [the shared-diamond audit](../analysis/diamond_shared_library.md)).
- Partitioning all `1,468,414` live declarations into `141` coarse FLIRT clusters collapses `42.35%` (`522,274` compiler auxiliaries, `70,021` `k1n` duplicates, `29,520` `*Statement` wrappers, `103` copy shells) to `846,496` core declarations. Comparing fail-closed name-blinded labels against directory paths flags `66` cross-domain misplaced clusters (`27` high-severity), `30` partial/naming-drift clusters, and `45` aligned clusters (see [the 141-cluster atlas](../analysis/cluster_atlas_141.md)).

<details>
<summary>Verify locally</summary>

```bash
python3 -c "
import glob, json, sqlite3
k = sqlite3.connect('file:outputs/kernel/kernel.db?mode=ro', uri=True)
names = (
  'allChi',
  'UpperTheory.FinalTheorems.everyCharacter',
  'UpperTheory.FinalTheorems.everyCharacter_of_row',
  'UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter',
  'UpperTheory.One.vwin_of_row',
  'UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin',
  'UpperTheory.Lit.every_character_of_theta_integrals_local_matching',
  'SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt',
  'UpperTheory.Zero.LLC.recTExists',
)
q = 'SELECT d.name, dm.subtree_size FROM decls d JOIN dom dm ON dm.decl_id=d.id AND dm.tree_id=0 WHERE d.name IN (%s) ORDER BY dm.subtree_size DESC' % ','.join('?'*len(names))
for row in k.execute(q, names): print(row)
non_op = set()
bps = 0
for p in sorted(glob.glob('outputs/decomp/*.json')):
    d = json.load(open(p))
    if isinstance(d, dict) and d.get('schema') == 'leanre.decomp/v1':
        bps += 1
        nodes = d['nodes']
        it = nodes.items() if isinstance(nodes, dict) else [(n.get('fqn') or n.get('id'), n) for n in nodes]
        for fqn, n in it:
            if n.get('status') and n['status'] != 'OPAQUE': non_op.add(fqn)
dom1k = {r[0] for r in k.execute('SELECT d.name FROM dom dm JOIN decls d ON d.id=dm.decl_id WHERE dm.tree_id=0 AND dm.subtree_size>=1000')}
print(f'blueprints={bps} non_opaque={len(non_op)} dom>=1000={len(dom1k & non_op)}/{len(dom1k)}')
"
python3 leanre/decompile dom UpperTheory.FinalTheorems.everyCharacter --depth 1 --min-size 1000
```

</details>
