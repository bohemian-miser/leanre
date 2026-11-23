# leanre

`leanre` is a generic reverse-engineering toolkit for large Lean 4 proofs (`pyproject.toml` + `leanre.toml`): a Rust streaming extractor and Python 3.11+ CLI, 3-level `circuit` SVG/HTML generator, and web workbench turning `lean4export` v3.1.0 archives into a SQLite declaration graph with dominators, taint, signature hashing, bundle/hygiene audits, `kdiff`, portability cones, virtual stripping, offline HTML export, and annotation packs. Verified on five external Lean 4 corpora ([generic corpus benchmark](analysis/generic_corpus_trial.md)), it is applied below to Levent Alpöge and Claude's Nov 20, 2026 Lean 4 (`v4.33.1` / Mathlib `v4.33.1`) formalization claiming **RH** and **Dirichlet-only GRH** ([pinned commit](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005), [companion note](https://alpo.ge/remark.pdf)).

## Quickstart

```bash
# Zero-toolchain quickstart on the bundled 5-file fixture (<1s)
python3 leanre/leanre.py init --dry-run examples/tiny_demo
python3 leanre/leanre.py all --src examples/tiny_demo --ndjson examples/tiny_demo/demo.ndjson --out-dir /tmp/leanre_demo

# Run Python and Rust test suites (or install CLI with: pip install -e .)
python3 -m unittest discover -s leanre -v
(cd leanre/kernel-rs && cargo test)

# 3-level circuit diagrams (JSON / SVG / interactive HTML), audits, and workbench
python3 leanre/leanre.py circuit macro --svg /tmp/macro.svg --html /tmp/macro.html
python3 leanre/leanre.py circuit bundle HypsAlt --html /tmp/hyps.html
python3 leanre/leanre.py circuit theorem UpperTheory.FinalTheorems.everyCharacter --html /tmp/ec.html
python3 leanre/leanre.py bundles --top 20
python3 leanre/leanre.py kernel hygiene UpperTheory.Top.VWin --cone-depth 1 --semantic
python3 leanre/leanre.py trim --from-report outputs/decomp/trim_report.json
python3 leanre/leanre.py portability finiteH_of_isProper --no-src
python3 leanre/leanre.py export-site --demo --out /tmp/leanre_demo.html
python3 leanre/leanre.py kdiff a_kernel.db b_kernel.db --fail-on-regression
python3 workbench/server.py --port 8420
```

Docs: [CLI reference](leanre/README.md), [kernel extractor](docs/KERNEL.md), [signature hashing](docs/SIGHASH.md), [FLIRT fingerprinting](docs/FLIRT.md), [cross-repo matching](docs/FLIRT_TIER2.md), [annotation packs](docs/ANNOTATION_PACKS.md), [virtual stripping](docs/TRIM.md).

## Riemann Hypothesis formalization audit

All counts come from Andrew Sutherland's exported `solution.ndjson.zst` (`175,187` files, `17,374,215` lines, `0` comments; `1,468,418` folded `con-leche` records / `1,484,733` unpacked `nanoda` constants / `114,115,002` edges; `1,468,414` live). All `999 / 999` live declarations with dominator `subtree_size >= 1,000` are audited across `45` decompilation blueprints (`3,478` inspected nodes) and `75` [technical dossiers](analysis/README.md). Kernel soundness and statement fidelity are not human mathematical peer review (see [epistemic scope](research/04_verification_and_roadmap.md)).

```text
Main (5 roots: 2 zeta RH + 3 Dirichlet-only GRH; 1,468,414 live decls)
  bridge outside allChi                       58,857  # Mathlib FE reflection + 31 project decls
  allChi                                   1,409,557  # self (1) + everyCharacter (1,409,556)
    everyCharacter                         1,409,556  # self (1) + 3 branches (= 96.0% live)
      galoisLocalGlobalStrong_recParameter    95,102  # Pillar B: odd-rank EtC tower + even theta lift
      everyCharacter_of_row                  982,855  # self (1) + 4 blocks below
        vwin_of_row                           92,705  # Pillar C: windowed continuous Sha^1 bound (VWin)
        every_character_of_theta_integrals   543,325  # Pillar A: HypsAlt producer + Landau consumer
        topCovolSlim2_use_alt_alt             80,720  # Pillar D: Arakelov / Moriwaki covolume bounds
        literature & row-side siblings       266,104  # theta/toroidal/resolution (225,278) + siblings (40,826)
      shared diamond                         331,598  # 100% reachable from both main branches
```

| Finding | Summary & deep dossiers |
|---|---|
| [Statements & TCB](findings/tcb-and-statements.md) | All `5` roots in [the entry module](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L4) check under `[propext, Classical.choice, Quot.sound]` (`0` `sorryAx`/`unsafe`/`native_decide`/project `Nat.sub` in statement cone); `riemannHypothesis` pulls `0` project defs (`4` wrapper lines for the `5`-root union); Dedekind/Hecke $L$-functions unclaimed; `Formalism.Gchi` is dead. |
| [Proof map & analytic chain](findings/proof-map.md) | Exact chain: `ch_balance` (`ASK − MAIN = De`) → `LinkG` (per-prime bookkeeping) → `Places_at` → proved global bounds `JointARam` (`208`) & `BoundsMu` (`79`) → `L3main` / Chowla–Selberg (`CMCurve` → Kronecker limit → `FlatDegree`) → `VWin` (genuine `Ш¹`, `401 = 1+400`, `½` slack) → `StageU` (`RankVal`, `m⁵ = m²·m³`, `WBp`, `sEEofTT` `dif_pos` only) → `siegelLower` in `count_a` exp `1`. See [reading guide](analysis/rh_proof_exposition.md) & [quantitative bridge](analysis/pillar_ad_quantitative_bridge.md). |
| [Author note vs Lean code](findings/remark-vs-code.md) | `0` hits for sixfold cover of `GL₅` (only 2-fold Weil–Shale `Mp.sub`), `0` global Kuznetsov/RTF (local `unitMatch_all` + untwisted `TRCusp'`), `0` Stepanov auxiliary polynomial (Behrend `hostThickExists` instead); frame order is an explicit 2-power cyclotomic tower (`fieldChi`), not a density theorem. |
| [Dead code & `decide +kernel`](findings/dead-code-and-timeouts.md) | `28,904 / 175,187` files (`2,378,537` lines) emit `0` kernel decls; `4 / 5` `lean4lean` timeout files are dead (`ChebyshevPrimeBounds.SmallLoop` is live); `14 / 34` `decide +kernel` files are live (`18` decls, `0` in Pillar B). |
| [Proof size & stripping](findings/proof-size-and-bloat.md) | Virtual stripping trims `175,187` files / `17,374,215` lines to `105,918` files (`60.46%`) / `12,904,172` lines (`74.27%`) / `1,310,025` decls; `lam_copy` hits `5,538,373` `value_nodes`. |
| [Aliases, stubs & bundles](findings/aliases-and-dummy-slots.md) | `43,135` `value_nodes = 1` theorem aliases (`38,194` `GlobalTheory.T.*`), `0 / 5,497` literal `: True` struct fields, `2` `0`-field placeholders, `UnusedSlot72 := True`, `anyGeometry := True`, `SExt.none := PUnit`, `llOf_alt` (`11/12` dropped), `exists_baseLattice_of_prime_alt` (`.1` drops `ExBL`), `RealInAlt` (`3` conditional-in-form-only fields), `6` `*_of_open` adapters, unread bundles (`ThetaLocalInputs` `33/53`, `LiteratureCMHypothesis` `11/11`). See [spine hygiene audit](analysis/spine_hygiene_audit.md). |
| [Intentional shortcuts](findings/intentional-shortcuts.md) | `recTExists` falls back to `junkEx` off depth-zero tame inputs; `AwayB.tame0` has `0` Pillar C callers; `wach_lattices` reads `3/192` fields of toy `D7` `exampleRecordOfData`. None creates a soundness hole. |
| [Grounded mathematics](findings/genuine-math.md) | Adversarial rechecks ([monodromy](analysis/adversarial_monodromy_recheck.md), [resolution](analysis/adversarial_hironaka_recheck.md), [cohomology/Kato](analysis/adversarial_cohomology_recheck.md)) pin exact textbook attributions: Colmez (2008) Robba-free $p$-adic monodromy, Kollár Ch. 3 / Encinas–Villamayor / Bierstone–Milman char-0 resolution, Grothendieck EGA III₁ Thm. 3.2.1 (affine base), Oda / Mazur–Messing / BBM char-free abelian Hodge–de Rham (`deg ≤ 2`), Tate (1962) global Euler–Poincaré, Poitou–Tate real-place iso, and Kato (2004) Euler system (`0` Kato log geometry); `7` portability candidates (`44,858` project decls) split into `4` disjoint islands. |

For all `75` technical dossiers see [the analysis index](analysis/README.md); verification logs and scope notes live in [the research notes](research/README.md). Interactive proof explorer: https://leanre.review/

## Reproducing the audit

The `findings/*.md` summaries and several `analysis/*.md` dossiers end with collapsible **Verify locally** command blocks (`leanre` CLI queries and inline `python3` / `sqlite3` checks). Those scripts are omitted from the public website (`leanre.review`) because they require a local checkout containing the untracked upstream proof files and extracted kernel database (`data/` and `outputs/kernel/kernel.db`, both gitignored because the upstream proof archive has no license):

1. Obtain `data/rh_mirror` (`leanprover-community/riemann-hypothesis` at commit `40e56bab026552e089d7afcfeff08d2defb9c005`) and Andrew Sutherland's `solution.ndjson.zst` (`lean4export` v3.1.0).
2. Build the Rust extractor (`python3 leanre/leanre.py kernel build`) and extract `outputs/kernel/kernel.db`:
   `python3 leanre/leanre.py kernel extract --input data/solution.ndjson.zst --out-dir outputs/kernel --src-dir data/rh_mirror/src`
3. Run the `python3 leanre/leanre.py ...` and `sqlite3` checks shown in each Markdown file's **Verify locally** section.

For zero-setup testing without downloading multi-gigabyte archives, run the bundled `examples/tiny_demo` commands in [Quickstart](#quickstart) above.

## License and credits

**Independent project** — `leanre` is not affiliated with or endorsed by `leanprover-community` or any upstream proof author.

Tools, web UI, JSON schemas, and original documentation are licensed under [**GNU AGPL v3.0 or later**](LICENSE). The upstream proof archive ships with **no license**; no `.lean` proof bodies are redistributed here (`data/` and `research/sources/` are gitignored).

Builds alongside public verification work by [Andrew Sutherland](https://math.mit.edu/~drew/grh/), `leanprover-community/riemann-hypothesis` (formerly `Deicyde/riemann-hypothesis`), `nasqret/riemann-rev`, `jae-63`, `drew2apps`, `keithadler/rh-trim`, and `rgrossharv`.
