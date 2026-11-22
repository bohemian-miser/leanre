# Author sketch vs Lean code: what matches and what diverges

Alpöge's [four-page overview](https://alpo.ge/remark.pdf) (whose Footnote 4 warns that parts paraphrase an AI summary) matches the `1,468,414`-declaration kernel graph on its unitary lift chain, mass bookkeeping, seesaw/Bessel bounds, Behrend sets, and a Vandiver-style `Ш¹` bound. Three headline mechanisms in the note—a sixfold cover of $\mathrm{GL}_5$, a global Kuznetsov / relative trace formula, and Stepanov's auxiliary-polynomial method—are absent from the formalized proof.

## Most mechanisms match; three headline claims do not

| Mechanism in `remark.pdf` | Live in kernel? | What the Lean code contains |
|---|---|---|
| Chain of `m` lifts with ranks `k + j(t+1)` | Yes | [`Ranks`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/Params.lean#L6), [`ColumnChain`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/DataKernels.lean#L14), and 135-field [`D7`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean#L76) |
| Mass, Chowla–Selberg, Weyl, Minkowski | Yes | [`minkowski_bound_rat`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/MinkowskiQ.lean#L6), [`chowla_selberg_lattice`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean#L250), [`topCovolSlim2_use_alt_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopCovolSlim2Use.lean#L16) |
| Seesaw and Bessel period bounds | Yes | [`exists_seesaw_pair_of_theta_data`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ExistsSeesawPairOfThetaData.lean#L40) and `besselNVG` (`3,026` decls) |
| Weakening of Vandiver on `H¹` / `Ш¹` | Yes | [`VWin`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L49) bounds weighted $\mathbb{Z}_l$-lengths of $\mathrm{Ш}^1$ (not named Vandiver) |
| Behrend 3-AP-free sets for thick hosts | Yes | Mathlib `Behrend` is live (`15` decls) via [`hostThickExists`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L181) and [`BehrendFree`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/BehrendSets/Statement.lean#L48) |
| Sixfold cover of `GL₅` | No (`0` hits) | Only a 2-fold metaplectic cover of `Sp` is formalized |
| Global Kuznetsov / relative trace formula | Partial (`0` Kuznetsov/RTF) | `24` live local `JacquetRallis` transfer decls + `1,444` twisted `TraceFormula` decls |
| Stepanov auxiliary-polynomial method | No (`0` hits) | `0` Stepanov decls; `hasseDeriv` callers are deformation / Ax–Sen / Frobenius bounds |

## Sixfold cover of GL₅ is absent

Searching all `1,468,418` `con-leche` export records and `175,187` modules finds `0` hits for `sixfold` or `patterson`. The `74` live `metaplectic` declarations formalize a **2-fold** topological cover of the real symplectic group (`Matrix.symplecticGroup ι ℝ`): [`metaplecticRepresentation_holds`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MetaplecticRepresentationHolds.lean#L17) proves `Nat.card pr.ker = 2` with kernel `{1, ε}` ([`sq_scalar_character`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SqScalarCharacterOfDoubleCoverUnitary.lean#L7)). The `GL5/` directory ([`GenusMassVolumes`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/GL5/Statement.lean#L10)) holds Hermitian class-mass identities, and all `49` live `kazhdan` declarations are Gelfand–Kazhdan contragredient duality rather than Kazhdan–Patterson covers.

## Global Kuznetsov and RTF are absent; local Jacquet–Rallis transfer is live

There are `0` live declarations for `kuznetsov` or `relativetrace` (the lone `relative_trace` hit is an algebraic field trace). Instead, the proof combines three different trace mechanisms:

- `24` live `JacquetRallis` declarations sit in the shared diamond, led by [`jacquetRallisUnitMatch_all_ranks`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisUnitMatchAllRanksStatement.lean#L6) (`1,957` dominated decls, wrapping the `1,956`-decl [`unitMatch_all`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisUnitMatchAllRanks.lean#L9)), proving local unitary orbital-integral matching via Weil representations.
- `1,444` live `TraceFormula` declarations implement Arthur / simple twisted trace formulas such as [`trCusp_of_classicalTheorems`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TraceFormulaOfHyp.lean#L45).
- Poincaré-series lower bounds are carried by [`CarrierP`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/TheoremSClosedP.lean#L20) (`8,009` dominated decls, inner proof bodies unread).

## Stepanov auxiliary polynomials are absent; Behrend sets run instead

Neither `stepanov` nor `AuxPoly` appears anywhere in the `175,187`-file corpus (`0` decls, `0` modules). Checking by Mathlib signature rather than name confirms the same absence: `Polynomial.hasseDeriv` has `47` direct live callers (`30` project declarations including `._proof_*` auxiliaries and `17` Mathlib declarations; `68` across all `*hasseDeriv*` constants), all serving unrelated roles—formal deformation in [`formal_deformation`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicDivisibleDedekindFiniteTypeAlgClosed.lean#L61), $p$-adic Hodge theory in [`exists_close_of_hasseDeriv`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/PAdicHodge/AxLemma.lean#L171), and Frobenius-lift bounds. The actual window-separation bottleneck uses Mathlib's `Behrend.exists_large_sphere` through [`hostThickExists`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L181).

<details>
<summary>Verify locally</summary>

```bash
python3 -c "
import sqlite3
k = sqlite3.connect('file:outputs/kernel/kernel.db?mode=ro', uri=True)
for pat in ['sixfold','patterson','metaplectic','kazhdan','kuznetsov','jacquetrallis','traceformula','stepanov','behrend']:
    c = k.execute('SELECT COUNT(*) FROM decls WHERE live_mask>0 AND lower(name) LIKE ?', (f'%{pat}%',)).fetchone()[0]
    print(f'{pat:15s} {c}')
hd = k.execute('''SELECT COUNT(DISTINCT e.src) FROM edges e
    JOIN decls t ON t.id=e.dst JOIN decls s ON s.id=e.src
    WHERE t.name='Polynomial.hasseDeriv' AND s.live_mask>0''').fetchone()[0]
print('hasseDeriv callers:', hd)
"
```

</details>
