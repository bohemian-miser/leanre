# Generic Cross-Repo Stress Test (`leanre` at `b97dcfc`)

> **Scope:** Layer 1–3 static instrumentation (`leanre` `b97dcfc`) over five non-RH Lean 4 repositories on disk (`examples/tiny_demo` plus four external Mathlib-4 projects under `data/corpora/`), with all temporary SQLite/JSON outputs isolated outside the repository. Only `tiny_demo` ships an NDJSON kernel export (`demo.ndjson`), so kernel-DAG / `bundles` / `kdiff` / `portability` / `hygiene` / `trim` / `export-site` coverage on the four large corpora remains `UNREAD` (`OPAQUE` until compiled NDJSON is supplied); all source metrics come from `leanre` `scan`, `forensics`, `init`, and `flirt tier1` `[L]`. Tags: `[L]` tool/source-verified, `[S]` Lean/Mathlib convention, `[M]` cross-repo synthesis. Companion JSON: [`outputs/xrepo_benchmark.json`](../outputs/xrepo_benchmark.json).

## 1. Five-Repo Corpus Benchmark (`leanre init`, `scan`, `forensics`, `flirt tier1`) `[L]`

| Repo (Toolchain) | Mods | `wc -l` | Edges | `decls` (`thm` / `def` / `ind` / `ax`) | `sorry` (Mods) | Hub (`dom` / `reach`) | Top Fan-In Module (`fan_in`) | Runtime (s) | Default CLI / Workaround Exit |
|---|---:|---:|---:|---|---:|---|---|---:|---|
| `tiny_demo` (`v4.33.1` export) | `5` | `88` | `6` | `11` (`6` / `4` / `1` / `0`) | `0` (`0`) | `Main` (`4` / `4`) | `Arithmetic` (`3`) | `2.23` | **PASS** (`0` across 14 cmds; `--root` needed for kernel) |
| `PrimeNumberTheoremAnd` (`v4.35.0`) | `235` | `172,342` | `518` | `9,054` (`8,293` / `740` / `21` / `0`) | `>=205` (`20`) | `PrimeNumberTheoremAnd` (`104` / `104`) | `...IEANTN.BKLNW.BKLNW_table10_rows_core` (`17`) | `7.39` | `scan` **FAIL** (`ec=1` def); **PASS** w/ `--root auto` (`0`) |
| `carleson` (`v4.36.0-rc1`) | `128` | `50,197` | `332` | `3,103` (`2,599` / `468` / `36` / `0`) | `6` (`2`) | `Carleson` (`125` / `125`) | `Carleson.TileStructure`, `...LpSeminorm.Basic` (`7`) | `3.78` | `scan` **FAIL** (`ec=1` def); **PASS** w/ `--root auto` (`0`) |
| `FLT` (`v4.35.0`) | `271` | `58,809` | `669` | `3,733` (`2,241` / `1,441` / `48` / `3`) | `60` (`20`) | `FLT` (`261` / `261` via `config`) | `FLT.Mathlib...AdicValuation` (`9`) | `2.98` | `scan` **FAIL** (`ec=1` def); `--root auto` wrong hub (`34/271`) |
| `SpherePacking` (`v4.36.0`) | `73` | `15,446` | `197` | `1,212` (`947` / `261` / `2` / `2`) | `61` (`19`) | `SpherePacking` (`73` / `73`) | `SpherePacking.MagicFunction.a.Basic` (`8`) | `1.74` | `scan` **FAIL** (`ec=1` def); **PASS** w/ `--root auto` (`0`) |

Notes on source counts `[L]`: `thm` = `theorem + lemma`, `def` = `def + abbrev + instance`, `ind` = `inductive + structure + class`, `ax` = `axiom`. In `PrimeNumberTheoremAnd`, `...IEANTN.TMEEMT` hit the scanner's `50`-hit per-module-per-tag cap, so `205` `sorry` hits is a lower bound; `PNT+` also logged `83` `native_decide` hits (`38` mods) and `1` `unsafe`, `SpherePacking` logged `2` `decide +kernel` hits (`SpherePacking.Basic.E8`), and `FLT` logged `3` axioms (`knownin1980s`, `Mazur_statement`, `Odlyzko_statement`).

## 2. `tiny_demo` Full Pipeline Coverage (`14 / 14` Exit `0`, With Caveats) `[L]`

- **Source + NDJSON (`init`, `scan`, `ndjson`, `forensics`):** `0.53s` combined (`17` kernel records, `27` unpacked constants, `39` edges, `0` oracle failures, structural sanity gates `3/3 PASS`) `[L]`.
- **Kernel & downstream tools (`kernel extract --root TinyDemo.main_theorem:DEMO`, `bundles`, `kdiff`, `portability`, `kernel hygiene`, `export-site`, `trim`, `flirt tier1`):**
  - `kernel extract` (`0.19s`): `10` live / `7` dead declarations, `76.47%` module alignment (`13/17`), `0` oracle failures `[L]`.
  - `bundles` (`0.13s`): finds `1` live 1-ctor structure (`TinyDemo.ProofBundle`, `2` fields, `1` unread `unusedNote`) when rooted, vs `0` when `kernel extract` ran unrooted `[L]`.
  - `kdiff` self-diff (`0.14s`): `17` unchanged, `0` regressions, `dom(tree_id=0)` `10 -> 10` `[L]`.
  - `portability` (`0.13s`): `TinyDemo.main_theorem` cone = `8` project + `2` external (`Nat`, `Eq`), `spec_proj=4`, rated `scoped` (because `4` top-level `.lean` files count as `4` "root dirs") `[L]`.
  - `kernel hygiene --cone-depth 2` (`0.13s`): audits `7` decls (`0` findings, `0` errors) `[L]`.
  - `export-site --with-bundles` (`0.13s`): emits self-contained `33,042 B` HTML with zero RH prose leaks (retains `1` `"rh_depth"` JSON key) `[L]`.
  - `flirt tier1` (`0.39s`) + `trim` (`0.13s` explicit flags): `5 -> 2` modules (`88 -> 36` lines, `10 -> 7` live decls, `39 -> 29` value nodes) `[L]`.

## 3. Generic-Lean Portability Bugs & RH Hardcodings Caught `[L]`/`[M]`

1. **`XREPO-01` [HIGH] `leanre/leanre.py` `scan`/`all` default `--root Main`:** Unlike `scanner.py` (`--root auto`), top-level `leanre scan` defaults `--root Main`, failing (`exit 1`) on all 4 external repos (`ValueError: Root module 'Main' not found`); `leanre.py` also omits `--config` on `scan` and `forensics` `[L]`.
2. **`XREPO-02` [HIGH] `scanner.py` `--root auto` & directory filtering (`FLT`, `carleson`, `PNT+`):** `discover_lean_files` only skips `.lake`, `.git`, `build`, so it indexes `blueprint-verso/`, `scripts/SideSkimmer/lakefile.lean`, and `examples/`. On `FLT`, `FLT.lean` has `fan_in > 0`, so `--root auto` picks `blueprint-verso.FLTBlueprint.Chapters.Level02ReductionToPrimeCase` (`reach=34/271`, `hub=FLT.Proof`) instead of `FLT` (`reach=261/271` via `scanner.py --config`) `[L]`.
3. **`XREPO-03` [HIGH] `kernel.py` `extract` ignores `leanre.toml`:** Running `kernel extract` on `tiny_demo` without manual `--root` logs `"RH defaults absent; proceeding with 0 roots"` (`0` live / `17` dead), silently zeroing `bundles` (`0` structures) and nulling `portability` `dom` metrics `[L]`.
4. **`XREPO-04` [HIGH] `trim.py` defaults to RH workspace files & hardcodes commit pin:** Calling `leanre trim --kernel-db <tiny_demo>` without `--src`, `--leanre-db`, `--tier1-db` mixes `10` tiny_demo decls with `175,187` RH modules (`17,374,215` lines), and always prints `pinned to 40e56bab` `[L]`.
5. **`XREPO-05` [MED] `flirt/tier1.py` cross-contaminates via RH `kernel.db`:** Default `--kernel-db` opens RH `outputs/kernel/kernel.db` (`0/N` live calibration), prints RH `F1 AbelianVarietyTheory` stdout lines, and flags `48.1%` (`113/235`) of `PNT+` and `39.1%` (`106/271`) of `FLT` due to Mathlib-extension namespaces (`AddSubgroup`, `riemannZeta`) `[L]`.
6. **`XREPO-06` [MED] Hardcoded `"src/"` anchor prefix & `"rh_depth"` key:** `bundles` and `decompile contract` emit `"src/Bundles.lean"` (line `10`) / `"src/Main.lean"` (line `12`) even when `src_dir = "."`; `bundles` and `export-site` still emit `"rh_depth"` `[L]`.
7. **`XREPO-07` [LOW] `config.py` `init` headline discovery:** Emits unqualified `"main_theorem"` on `tiny_demo` and `headline = []` on `PNT+` and `SpherePacking` because root `.lean` files only re-export submodules `[L]`.
8. **`XREPO-08` [LOW] RH metadata leaks & scanner limits:** `forensics_report.json` emits `kexactB_summary`, `slowest_con_leche`, `drew2apps_split_lines_equiv`; `forensics_dossier.md` skips `## 3.` when TCB is absent; `kernel_report.json` compares `17` records against RH `con_leche` (`1,468,418`) / `nanoda` (`1,484,733`) counts; `scanner.py` caps hits at `50`/module/tag and folds `structure`/`class`/`inductive`/`axiom` into `definitions` `[L]`.

## 4. Recommended Round 5 Patch Priority `[M]`

1. Default `leanre scan`/`all` `--root` to `auto` and wire `--config` across `scan`, `forensics`, `kernel extract`, `bundles`, `portability`, `trim`, `flirt tier1` `[M]`.
2. Align `scanner.py` `discover_lean_files` skip list with `config.py` (`blueprint*`, `scripts`, `examples`, `docs`) and prefer `lakefile.toml` `defaultTargets` in `--root auto` `[M]`.
3. Guard RH-specific defaults (`DEFAULT_KERNEL_DB` in `flirt/tier1.py`, `DEFAULT_SRC`/`DEFAULT_LEANRE_DB` in `trim.py`, `con_leche`/`nanoda` reconciliation in `kernel.py`, `src/` prefix and `rh_depth` in `bundles.py`/`decompile`/`export_site.py`) behind explicit config or RH-only flags `[M]`.
