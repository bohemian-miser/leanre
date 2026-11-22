# Kernel-Exact Declaration Graph (`leanre/kernel-rs` + `leanre/kernel.py`)

> **Epistemic Scope (Guardrail 1):** Everything in `outputs/kernel/kernel.db` and `outputs/kernel_report.json` is **Layer 1 / Layer 2 / Layer 3 instrumentation** extracted deterministically from Sutherland's `lean4export` v3.1.0 NDJSON streams (`[L]`). Kernel validity (`propext`, `Quot.sound`, `Classical.choice`, zero `sorryAx`) is **not** a claim of mathematical peer consensus (Layer 4) or complete human intelligibility (Layer 3).

## 1. Overview & Architecture

The kernel-exact extractor replaces Phase 2's Python NDJSON parser (`leanre/ndjson.py`, ~51k decls) with a native multi-threaded Rust streaming extractor (`leanre/kernel-rs/`, compiled binary `leanre-kernel`) plus a thin stdlib-only Python orchestrator and enrichment layer (`leanre/kernel.py`).

Pipeline stages:
1. **Streaming zstd + SHA-256 + parallel parse (`src/reader.rs`, `src/parse.rs`, `src/store.rs`):** Streams `.ndjson.zst` (`window_log_max = 31` for `--long=30`), computes compressed and uncompressed SHA-256 in parallel, splits 4 MiB newline-aligned blocks across worker threads with a zero-allocation JSON cursor for hot `ie`/`in`/`il` lines (and strict `serde_json` for declaration records, `meta`, and fallback), and stores the expression DAG in a 9-byte/node struct-of-arrays (`tag: u8`, `a: u32`, `b: u32`) plus compact side tables for `letE`, `const.us`, `proj`, and literals.
2. **Exact typed dependency walk (`src/walk.rs`, `src/graph.rs`):** Parallel per-declaration DAG walks keep **type-dependency** and **value-dependency** references strictly separate (`kind`: `1 = type-only`, `2 = value-only`, `3 = both`), count visited DAG nodes, detect kernel-level computation patterns (`flags`), and construct forward/reverse CSR adjacency tables.
3. **Kernel signature hashes (`src/sighash.rs`):** Bit-for-bit Rust implementation of `docs/SIGHASH.md` v1 (`k1n` named and `k1a` lexicon-abstracted Merkle hashes over the hash-consed expression DAG, plus `sig_size` and `n_local`). Immediately after sighash finishes, the ~9.5 GiB expression/name/level tables are dropped before SQLite serialization, capping peak RSS at ~12.3 GiB.
4. **Reachability, dominator trees & brute-force oracle (`src/graph.rs`):** Computes per-root BFS shortest-path trees in both **proof view** (all edges) and **statement view** (root value-only edges omitted, matching Phase 2 TCB semantics), plus the pure definition-only cone (`defcone_mask`). Builds 7 Cooper–Harvey–Kennedy RPO fixpoint dominator trees (`ALL`, 5 single-root trees, and `STMT_ALL`) and cross-checks **every tree** against an independent brute-force node-removal reachability oracle (`oracle_top = 50` largest dominators + `oracle_random = 1,000` fixed-seed sampled reachable nodes per tree).
5. **SQLite emission & Python enrichment (`src/main.rs`, `leanre/kernel.py`):** Atomically stages and populates `outputs/kernel/kernel.db` with `decl_module` (K6 alignment against `outputs/leanre.db` + clean namespace rescan via `sighash.iter_source_decls`) and `taint_sources` / `taint_paths` (K5 taint extraction with an independent post-insert edge-by-edge validator against `edges`).

## 2. Counting Rules & K2 Reconciliation `[L]`

Two numbers circulate in community reports for the same `61,570,595,788`-byte Sutherland export (`solution.ndjson`, SHA-256 `5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e`):

| Counting rule | Definition | Measured (`solution.ndjson.zst`) | External reference | Delta |
|---|---|---:|---:|---:|
| **Declaration records** (`decls` table) | 1 per top-level declaration JSON object (`thm` + `def` + `opaque` + `axiom` + `quot` + `inductive`, where each `inductive` record folds its types, constructors, and recursors) | **1,468,418** | `1,468,418` (`con-leche` fold records `[C]`) | **0** |
| **Unpacked kernel constants** (`consts` table) | 1 per constant added to the Lean environment: `thm` (`1,246,110`) + `def` (`214,241`) + `opaque` (`91`) + `axiom` (`3`) + `quot` (`4`) + `inductive.types` (`7,970`, 1 mutual block of 2 types) + `inductive.ctors` (`8,342`) + `inductive.recs` (`7,972`) | **1,484,733** | `1,484,733` (`nanoda` via `nasqret` `[C]`) | **0** |

The exact difference `1,484,733 - 1,468,418 = 16,315` equals `(7,970 + 8,342 + 7,972) - 7,969 = 16,315` — the extra constants unfolded out of the `7,969` `inductive` records (`+1` mutual type, `+8,342` constructors, `+7,972` recursors). Furthermore, our 0-based `decls.id` export indices match `con-leche-master.log` record indices identically (e.g., `lam_copy` `#829554`, `sigSpan_copy` `#829660`, `PI.PC.loop_run._proof_1_1` `#571290`, `factorial_ladder_one_forty_one._proof_1_1` `#226690`, `GlobalTheory.PrimeRecip.table_ok._proof_1_1` `#570391`).

## 3. SQLite Schema (`outputs/kernel/kernel.db`, Schema v1)

Consumers open `outputs/kernel/kernel.db` **read-only** (`mode=ro`). Nodes in `decls` are 0-based export declaration records (`0 .. N-1`); in both `challenge.ndjson.zst` and `solution.ndjson.zst`, `edges_not_in_export_order = 0`, so every dependency has `dst < src` (the declaration graph is strictly topological in export order).

Note on headline root names: `Main.lean` declares the five headline theorems at root scope (no `namespace Main`), so their kernel constant names are `riemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, and `LFunction_eq_zero_re_of_isPrimitive` (aligned to module `Main` in `decl_module`).

```sql
-- Compact JSON metadata (input bytes/SHA-256, export_meta, counts, sighash lexicon_id,
-- content_hashes, alignment_summary, taint_summary). Every row <= 4 KiB.
CREATE TABLE meta(
    key TEXT PRIMARY KEY,
    value_json TEXT NOT NULL
);

-- One row per export declaration record (id = 0-based export order).
CREATE TABLE decls(
    id INTEGER PRIMARY KEY,
    name TEXT NOT NULL,            -- primary constant name (UNIQUE via decls_name)
    kind TEXT NOT NULL,            -- thm | def | opaque | axiom | quot | inductive
    n_consts INTEGER NOT NULL,     -- 1 for non-inductives; types+ctors+recs for inductives
    type_nodes INTEGER NOT NULL,   -- DAG nodes visited walking type root(s)
    value_nodes INTEGER NOT NULL,  -- DAG nodes visited walking value/rec-rule root(s)
    fan_in INTEGER NOT NULL,       -- in-degree in `edges` (number of dependents)
    fan_out INTEGER NOT NULL,      -- out-degree in `edges` (distinct dependencies)
    fan_out_type INTEGER NOT NULL, -- dependencies occurring in type
    fan_out_value INTEGER NOT NULL,-- dependencies occurring in value
    flags INTEGER NOT NULL,        -- bitmask of kernel expression patterns (see below)
    live_mask INTEGER NOT NULL,    -- bit r set <=> reachable from roots.id=r (proof view)
    stmt_mask INTEGER NOT NULL,    -- bit r set <=> reachable in statement cone of root r
    defcone_mask INTEGER NOT NULL, -- bit r set <=> in pure definition-only cone of root r
    attrs INTEGER NOT NULL,        -- bit 1 = unsafe, bit 2 = partial
    sighash TEXT,                  -- k1n:<32 hex> of primary constant (docs/SIGHASH.md)
    sighash_anon TEXT              -- k1a:<32 hex> of primary constant (lexicon in meta)
);
CREATE UNIQUE INDEX decls_name ON decls(name);

-- One row per unpacked kernel constant (includes every inductive type, ctor, recursor).
CREATE TABLE consts(
    id INTEGER PRIMARY KEY,
    name TEXT NOT NULL,            -- UNIQUE via consts_name
    decl_id INTEGER NOT NULL,      -- FK -> decls.id
    ckind TEXT NOT NULL,           -- thm | def | opaque | axiom | quot | induct | ctor | rec
    ord INTEGER NOT NULL,          -- 0-based order within its decl record
    sighash TEXT,                  -- k1n:<32 hex>
    sighash_anon TEXT,             -- k1a:<32 hex>
    sig_size INTEGER,              -- tree node count (saturating u32, docs/SIGHASH.md §2)
    n_local INTEGER                -- distinct project-local constants abstracted in k1a
);
CREATE UNIQUE INDEX consts_name ON consts(name);
CREATE INDEX consts_decl ON consts(decl_id);
CREATE INDEX consts_sighash ON consts(sighash);
CREATE INDEX consts_sighash_anon ON consts(sighash_anon);

-- Directed dependency edges: `src` depends on `dst`.
-- kind: 1 = type-only, 2 = value-only, 3 = both type and value.
CREATE TABLE edges(
    src INTEGER NOT NULL,
    dst INTEGER NOT NULL,
    kind INTEGER NOT NULL,
    PRIMARY KEY(src, dst)
) WITHOUT ROWID;
CREATE INDEX edges_dst ON edges(dst, src);

-- The 5 headline theorem roots (bit r = 1 << id in live_mask / stmt_mask / defcone_mask).
CREATE TABLE roots(
    id INTEGER PRIMARY KEY,        -- 0..4
    name TEXT NOT NULL,
    decl_id INTEGER NOT NULL,
    grp TEXT NOT NULL              -- RH (ids 0,1) | GRH (ids 2,3,4)
);

-- Shortest-path BFS trees from each root (proof view: all edges; stmt_reach: statement view).
-- Walking `parent` from any live decl_id to root.decl_id yields an exact shortest dependency path.
CREATE TABLE reach(
    root_id INTEGER NOT NULL,
    decl_id INTEGER NOT NULL,
    depth INTEGER NOT NULL,
    parent INTEGER,                -- NULL at root
    PRIMARY KEY(root_id, decl_id)
) WITHOUT ROWID;

CREATE TABLE stmt_reach(
    root_id INTEGER NOT NULL,
    decl_id INTEGER NOT NULL,
    depth INTEGER NOT NULL,
    parent INTEGER,
    PRIMARY KEY(root_id, decl_id)
) WITHOUT ROWID;

-- Dominator trees (Cooper-Harvey-Kennedy from a virtual root over `root_ids`).
-- Labels: ALL (proof, 0..4), ROOT:<name> (proof, single root), STMT_ALL (stmt, 0..4).
CREATE TABLE dom_trees(
    id INTEGER PRIMARY KEY,
    label TEXT NOT NULL,
    view TEXT NOT NULL,            -- proof | stmt
    root_ids TEXT NOT NULL,        -- comma-separated roots.id list
    n_nodes INTEGER NOT NULL
);

CREATE TABLE dom(
    tree_id INTEGER NOT NULL,
    decl_id INTEGER NOT NULL,
    idom INTEGER,                  -- NULL = direct child of the virtual root
    depth INTEGER NOT NULL,        -- 0 for children of the virtual root
    subtree_size INTEGER NOT NULL, -- includes self
    PRIMARY KEY(tree_id, decl_id)
) WITHOUT ROWID;
CREATE INDEX dom_idom ON dom(tree_id, idom, subtree_size DESC, decl_id);
CREATE INDEX dom_top ON dom(tree_id, subtree_size DESC, decl_id);

-- K6 declaration -> .lean module alignment (1 row per decl, no silent drops).
CREATE TABLE decl_module(
    decl_id INTEGER PRIMARY KEY,
    module TEXT,                   -- outputs/leanre.db modules.name, or NULL if unmatched
    method TEXT NOT NULL,          -- matched method or explicit `unmatched:<bucket>`
    src_decl_id INTEGER            -- outputs/leanre.db declarations.id when matched via leanre.db
);
CREATE INDEX decl_module_mod ON decl_module(module);
CREATE INDEX decl_module_method ON decl_module(method);

-- K5 taint sources and edge-validated shortest dependency paths from each live root.
CREATE TABLE taint_sources(
    id INTEGER PRIMARY KEY,
    class TEXT NOT NULL,           -- kexactB | kcopy | CutCptCopy | decide_kernel | decide_kernel_pattern | lean4lean_timeout | slow_con_leche | ofReduceBool | ofReduceNat | trustCompiler | sorryAx
    decl_id INTEGER NOT NULL,
    origin TEXT NOT NULL,          -- source-hit:leanre.db | generated-copy | kernel-pattern:*
    module TEXT,
    line_no INTEGER,
    detail TEXT NOT NULL           -- metadata only (never raw .lean body text)
);
CREATE INDEX taint_sources_class ON taint_sources(class, decl_id);
CREATE INDEX taint_sources_decl ON taint_sources(decl_id);

CREATE TABLE taint_paths(
    source_id INTEGER NOT NULL,
    root_id INTEGER NOT NULL,
    hop INTEGER NOT NULL,          -- 0 = root ... L = taint_sources.decl_id
    decl_id INTEGER NOT NULL,
    edge_kind INTEGER,             -- NULL at hop 0; edges.kind (1|2|3) for (hop-1 -> hop)
    PRIMARY KEY(source_id, root_id, hop)
) WITHOUT ROWID;
CREATE INDEX taint_paths_hop0 ON taint_paths(hop, root_id, source_id);

CREATE VIEW axioms AS SELECT * FROM decls WHERE kind = 'axiom';
```

### `decls.flags` Bitmask (Kernel Expression Patterns)

| Bit | Constant | Meaning in kernel value term |
|---:|---|---|
| `1` | `F_REFL_TRUE` | Value contains `Eq.refl Bool Bool.true` (kernel definitional reduction of a `Bool` equality, including `by decide +kernel` on `f ... = true` such as `PI.PC.loop_run._proof_1_1`, `table_ok._proof_1_1`, `factorial_ladder_one_forty_one._proof_1_1`) |
| `2` | `F_OF_DECIDE` | Value contains `of_decide_eq_true _ _ (Eq.refl Bool true)` (kernel reduction of a `Prop` via `Decidable`, e.g. `by decide +kernel` on inequalities/propositions) |
| `4` | `F_REDUCE_BOOL` | References `Lean.ofReduceBool` or `Lean.reduceBool` (`native_decide`-style compiler-trusted bool reduction) |
| `8` | `F_REDUCE_NAT` | References `Lean.ofReduceNat` or `Lean.reduceNat` |
| `16` | `F_SORRY` | References `sorryAx` |
| `32` | `F_TRUST_COMPILER` | References `Lean.trustCompiler` |

## 4. Measured Findings on `solution.ndjson.zst` `[L]`

Source artifact: `data/solution.ndjson.zst` (`7,699,933,588` B, SHA-256 `61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381`; uncompressed `61,570,595,788` B, SHA-256 `5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e`; Lean `v4.33.1`, `lean4export` `3.1.0`). Local lexicon: `outputs/flirt/cache/lexicon_rh.txt` (`1,051,704` names, `lexicon_id = 294e04cd1ef65e37`).

- **Stream & graph integrity:** `1,080,769,508` NDJSON lines, `1,065,214,335` expr IDs, `14,065,151` name IDs, `21,605` level IDs, `114,115,002` declaration edges (`6,759,347` type-only, `64,738,654` value-only, `42,617,001` both). Zero undefined/duplicate IDs, zero dangling constant references, zero forward references, zero `unsafe` or `partial` records, zero `mdata` nodes.
- **K4 live/dead & axioms:**
  - Union live across the 5 roots: **`1,468,414`**; dead: **`4`** (`Nat.lor`, `Nat.xor`, `String.mk`, `String.mk._proof_1` — present only because `export-targets.txt` explicitly requests primitive `Nat`/`String` constants).
  - Per-root proof live / statement cone / def-cone:
    - `riemannHypothesis` (`RH`): `1,468,390` live (`1` exclusive) / `51,215` stmt / `2,448` defcone
    - `riemannZeta_eq_zero_re` (`RH`): `1,468,392` live (`2` exclusive) / `51,215` stmt / `2,448` defcone
    - `LFunction_ne_zero_of_half_lt_re` (`GRH`): `1,468,382` live (`2` exclusive) / `51,575` stmt / `2,527` defcone
    - `LFunction_eq_zero_re` (`GRH`): `1,468,395` live (`14` exclusive) / `51,555` stmt / `2,524` defcone
    - `LFunction_eq_zero_re_of_isPrimitive` (`GRH`): `1,468,385` live (`5` exclusive) / `51,677` stmt / `2,565` defcone
  - Group splits: `RH` union = `1,468,393` (`12` RH-exclusive), `GRH` union = `1,468,402` (`21` GRH-exclusive), common intersection of all 5 roots = `1,468,379` (`99.997%`). Statement-cone union = `51,687` (`2,570` def-cone), matching `challenge.ndjson.zst` identically.
  - Reachable axioms (all 5 roots, both proof and statement cones): **`propext`** (fan-in `162,696`), **`Quot.sound`** (`245`), **`Classical.choice`** (`279`). **`sorryAx` is completely absent** from the export (`0` decls). **`Lean.ofReduceBool` / `Lean.reduceBool` / `Lean.ofReduceNat` / `Lean.reduceNat` / `Lean.trustCompiler` are all absent** (`0` decls).
- **K5 dominators & taint:**
  - Brute-force node-removal oracle checked `1,050` nodes (top-50 + 1,000 random) on each of the 6 proof trees and `1,049` on `STMT_ALL` (`7,349` total checks): **0 failures**.
  - Top proof-view dominator spine (`ALL` tree): `allChi` (`1,409,557`, 96.0%) → `UpperTheory.FinalTheorems.everyCharacter` (`1,409,556`) → `everyCharacter_of_row` (`982,855`) → `every_character_of_literature_of_vWin` (`849,323`) → `every_character_of_theta_integrals_local_matching` (`543,325`) → `nonempty_hyps_definite_side_of_closed_bound` (`451,610`) → `GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt` (`153,377`); main sibling branches under `everyCharacter` / `everyCharacter_of_row` are `galoisLocalGlobalStrong_recParameter` (`95,102`) and `UpperTheory.One.vwin_of_row` (`92,705`).
  - Taint classes (`620` sources → `3,100` shortest paths, `59,414` edge hops validated against `edges`, **0 failures**):
    - `kexactB`: `94` live decls (`470` paths, min `9` hops from `LFunction_ne_zero_of_half_lt_re`, `10` from `riemannHypothesis`)
    - `kcopy`: `3` live decls (`15` paths, min `13` hops)
    - `CutCptCopy`: `5` live `addDecl`-generated `*Cpt` decls (`low_level_gramCpt`, `glFibreCpt`, `low_level_fibreCpt`, `germ_data_low_levelsCpt`, `block_growth_bound_of_compact_coefCpt`; `25` paths, min `19` hops)
    - `decide_kernel` (source-tagged + live `._proof_1*` reduction auxiliaries): `36` live decls (`180` paths, min `10` hops); `decide_kernel_pattern` (`of_decide_eq_true _ _ (Eq.refl Bool true)`): `472` live decls (`2,360` paths, min `8` hops); `Eq.refl Bool true` (`flags & 1`): `129,492` live decls
    - `lean4lean_timeout` (**5-module audit** `[L]`):
      - **`1` of `5` timeout modules LIVE — `Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop`**: **all `9/9`** kernel declarations aligned to this module are LIVE (`live_mask = 31`): `PI.PC.tst` (`571271`), `PI.PC.loop.match_1` (`571272`), `PI.PC.force.match_1` (`571273`), `PI.PC.force` (`571274`), `PI.PC.loop._f` (`571275`), `PI.PC.loop` (`571276`), `PI.PC.force_eq` (`571278`), **`PI.PC.loop_run._proof_1_1`** (`571290`, `flags = 1` `Eq.refl Bool true` — the exact declaration named in `lean4lean-default-fuel-timeouts.log` & `con-leche-master.log` at 35.1s, min `21` hops from `LFunction_ne_zero_of_half_lt_re` / `22` from `riemannHypothesis`), and **`PI.PC.loop_run`** (`571291`, min `20`/`21` hops, depends on `._proof_1_1` via a `value` edge). Both `PI.PC.loop_run` and `PI.PC.loop_run._proof_1_1` are emitted in `taint_sources` (`10` validated paths).
      - **`4` of `5` timeout modules DEAD — `Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run1`–`Run4`**: **`0`** declarations in `solution.ndjson.zst` (`PI.PrimesDyadicRS.K.run1..4` and their `._proof_1_1` terms are completely absent, along with all 6 sibling files under `DyadicPrimeIntervals/` including `DyadicPrimeIntervals.SmallLoop` — distinct from `ChebyshevPrimeBounds.SmallLoop`). Exact verified dead-code cut-point `[L]`: `Run1..4` → `SmallNaturalNumbersBound` (`0` live) → `OrbitalBoundsConclusion.PrimesDyadicRS` (`primes_dyadic_range`, `0` live) → `ExplicitFormulaCounts.SqfCounts` (`counts_closed`, `0` live) → referenced only by dead theorems `CylinderCountFamily.family_bound_all` (`:324`) and `JCount.family_count_all` (`:204`). `Main` transitively imports `Run1..4` solely because `CylinderCountFamily` also defines live data structures (`AllRowsAt`, `TieCountAt`, `AllRows.toAt`, `AllRowsAt.dimT`, `9` live decls) and `JCount` defines live `CountCylAt`.
    - `slow_con_leche`: all `5` outer theorems + `3` `._proof_1_1` reduction auxiliaries (`8` live sources, `40` paths, min `18` hops; exact `con-leche-master.log` record IDs `#829554`, `#829660`, `#571290`, `#226690`, `#570391`).
    - `ofReduceBool`, `ofReduceNat`, `trustCompiler`, `sorryAx`: `0` sources / `0` paths.
- **K6 `decl -> .lean` module alignment:**
  - When `--src-dir` is provided, the authoritative Lean-scoped source map (`sighash.iter_source_decls`, which respects `namespace`/`section`/`end`/`_root_`) is queried first and cross-linked to `outputs/leanre.db` (`modules` and `declarations.id`) when module names agree — avoiding **`247`** false alignments of Lean core / Mathlib constants (`159` in `challenge_library` such as `Std.*`, `PLift.*`, `Inter`, `Inv`, plus `88` in `library_or_external` such as `Height.*`, `Ext`) caused by Phase 2's anonymous-`end` namespace-popping bug.
  - **`1,250,660 / 1,468,418`** (`85.17%`) aligned to project modules in `outputs/leanre.db`: `693,392` `leanre_db:exact`, `38,813` `leanre_db:strip_root`, `82,799` `private_module`, `415,904` `aux_prefix:leanre_db`, `12,313` `source_rescan:exact`, `7,434` `aux_prefix:source_rescan`, and `5` `generated:CutCptCopy` (`1,232,143` using `outputs/leanre.db` alone, which includes the `247` bogus Phase-2 collisions).
  - Explicit unmatched buckets (`217,758` total, `14.83%`, zero silent drops): `unmatched:library_or_external` (`135,160`), `unmatched:challenge_library` (`44,941`, with **0** challenge library constants falsely matched), `unmatched:external_private` (`29,511`), `unmatched:project_auto_instance` (`7,905`), `unmatched:project_reassoc_attr` (`133`), `unmatched:project_namespace_other` (`108`).
  - Reverse source-tree coverage: **`146,283 / 175,187`** (`83.50%`) `.lean` modules contain at least one live kernel declaration; **`28,904`** (`16.50%`) modules in `data/rh_mirror/src` contribute zero live kernel declarations despite being transitively imported by `Main`.

- **K7 Performance & Determinism `[L]`:**
  - Two independent full runs over `data/solution.ndjson.zst` (48 Rust threads + 24 Python workers, well inside the 64-thread / 100 GiB budget):
    - **Run 1:** Rust extract `503.93s` (parse `107.38s`, edges `5.91s`, sighash `3.95s`, dominators `7.73s`, 7,349 oracle checks `66.30s`, SQLite `306.11s`, DB hash `3.15s`) + enrichment `39.30s`; peak RSS **`12.32 GiB`** (`12,918,772 KiB`).
    - **Run 2:** Rust extract `484.56s` (parse `92.6s`, edges `5.2s`, sighash `4.4s`, oracle `65.2s`) + enrichment `39.42s`; peak RSS **`12.43 GiB`** (`13,031,328 KiB`).
  - **Determinism:** Pre-enrichment 4.1 GiB SQLite DB SHA-256 is **byte-for-byte identical** across both runs (`0c34f4d3c9841a87dd004d720d6ebcb342d3cd3e98c1d2fdbc2ae3898a4c13f8`). All **9** post-enrichment table content hashes (`decls`, `consts`, `edges`, `reach`, `stmt_reach`, `dom`, `decl_module`, `taint_sources`, `taint_paths`) are **identical** across both runs (recorded in `outputs/kernel_report.json` and `meta['content_hashes']`).

## 5. Reproduction Commands

```bash
# 1. Build native Rust extractor & run Rust unit tests
cd leanre/kernel-rs && cargo build --release && cargo test && cd ../..

# 2. K3 challenge regression against Phase 2 outputs/leanre.db + SIGHASH v1 vectors
python3 leanre/kernel.py extract \
  --input data/challenge.ndjson.zst \
  --out-dir /tmp/leanre_k3 \
  --leanre-db outputs/leanre.db \
  --lexicon outputs/flirt/cache/lexicon_rh.txt \
  --threads 32 \
  --expect-sha256 c24ef99dab3556a52c7fb886e03cf22a242f3b96f82ae4cc40539e5d2f678ac6 \
  --expect-uncompressed-sha256 bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9
python3 leanre/kernel.py verify-k3 \
  --challenge-db /tmp/leanre_k3/kernel.db \
  --leanre-db outputs/leanre.db \
  --challenge-stats /tmp/leanre_k3/run_stats.json \
  --ref-sighash-lex-sha 720e1df87e3e300d4437ec294b966d655fa14ebc7935ff9eca43186781f6deb1

# 3. Full solution.ndjson.zst extraction (~9 min, ~12.3 GiB peak RSS on 48 threads)
python3 leanre/kernel.py extract \
  --input data/solution.ndjson.zst \
  --out-dir outputs/kernel \
  --leanre-db outputs/leanre.db \
  --src-dir data/rh_mirror/src \
  --lexicon outputs/flirt/cache/lexicon_rh.txt \
  --threads 48 \
  --workers 24 \
  --oracle-random 1000 \
  --oracle-top 50 \
  --expect-sha256 61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381 \
  --expect-uncompressed-sha256 5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e \
  --report outputs/kernel_report.json

# 4. Standalone taint edge validation + unit tests
python3 leanre/kernel.py validate-taint --kernel-db outputs/kernel/kernel.db
python3 -m unittest leanre/test_kernel.py -v

# 5. Kernel-exact cone slicer & type-deps inspector (read-only parameterized SQL)
python3 leanre/leanre.py kernel slice PI.PC.loop_run --direction backward --depth 2 --edge-kind both --max-nodes 50
python3 leanre/leanre.py kernel slice allChi --direction backward --depth 2 --edge-kind type --stop-at Mathlib --dot
python3 leanre/leanre.py kernel slice PI.PC.loop_run._proof_1_1 --direction forward --depth 3 --json
python3 leanre/leanre.py kernel type-deps PI.PC.loop_run._proof_1_1 --limit 25
python3 leanre/leanre.py kernel type-deps UpperTheory.FinalTheorems.everyCharacter --json
```

## 6. Slicer & Inspector API (`leanre/kernel.py`, Phase 4 D4)

Both tools open `outputs/kernel/kernel.db` strictly read-only (`mode=ro`) with parameterized SQL only:

- **`kernel.slice_decl(kernel_db_path, decl, direction="backward", depth=3, max_nodes=200, edge_kind="both", stop_at=(), tree="ALL")`** (`schema: "leanre.kernel.slice/1"`):
  - `direction`: `backward` (dependencies `src -> dst`), `forward` (dependents `dst -> src`), or `both`.
  - `edge_kind`: `both` / `all` (kinds `1,2,3`), `type` (`1,3`), `value` (`2,3`), `type-only` (`1`), `value-only` (`2`), `type+value` (`3`).
  - `stop_at`: repeatable declaration names, namespace/module prefixes, or `@external` (stops at `decl_module.module IS NULL`); matching boundary nodes are emitted with `"stopped": true` and not expanded further.
  - Exporters: `kernel.format_slice_text(res)`, `kernel.format_slice_dot(res)` (Graphviz DOT), or JSON (`--json`).
- **`kernel.inspect_type_deps(kernel_db_path, decl, tree="ALL", limit=50)`** (`schema: "leanre.kernel.type_deps/1"`):
  - Emits full declaration metadata + `consts`, direct `type` references (`kind IN (1,3)`), direct `value`-only references (`kind = 2`), direct dependents, dominator `idom`/chain/children in `tree`, and exact edge-verified shortest paths to every live headline root (`reach` + `edges`).
  - Both functions resolve `consts.name` (e.g., constructors/recursors) to their parent `decls.id` cleanly when not a primary record name.
