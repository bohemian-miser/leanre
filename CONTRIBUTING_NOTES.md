# Contributing Proof Notes & Annotations

Human reviewers and automated analysis bots can submit chunk-by-chunk proof annotations via pull request without merge conflicts or local multi-gigabyte databases.

## 1. Conflict-Free File Path

Place every new pack in its own file under `annotations/contrib/`:

```text
annotations/contrib/<project_slug>/<author_slug>__<pack_slug>.jsonl
```

- `<project_slug>` must match `leanre_gallery.toml` (e.g., `riemann-hypothesis`, `navier-stokes`, `navier-stokes-euler`, `carleson`, `flt`, `prime-number-theorem`, `sphere-packing`, `tiny-demo`).
- `<author_slug>` must match your record `author` (`@alice` → `alice__...`, `ai:claude-sonnet` → `ai-claude-sonnet__...`, `bot:lean4checker` → `bot-lean4checker__...`).
- Do not edit another contributor's file or top-level `annotations/*.jsonl` in chunk PRs. Keep each pack `<= 2 MiB`.

## 2. Mandatory Trust Separation (Humans vs. Bots)

| Contributor type | Layer `kind` | `default_on` | Record `draft` | `author` format | Allowed `tag` / `status` |
|---|---|---|---|---|---|
| Human reviewer | `human-review` (or `human`) | `true` or `false` | _omitted_ | `@handle` | `L/A/C/S/M`; `verified`, `read`, `summary`, `flagged` |
| LLM / AI agent | `ai-draft` | **`false`** | **`true`** | `ai:<model>` | `M` only (requires `breaks`); `summary`, `read`, `flagged` |
| Automated tool / checker | `bot-check` | **`false`** | **`true`** | `bot:<tool>` | `L/C/M`; `summary`, `read`, `flagged` |

AI and bot packs are **off by default** in the UI so unreviewed machine summaries never appear inside the human-verified coverage layer.

## 3. Quickstart & 5-Line Format

Generate a canonical starter file with one command (or export directly from the Treemap **Annotate / Draft PR** panel):

```bash
python3 leanre/leanre.py annot template \
  --project riemann-hypothesis \
  --name Deduction.landau_window \
  --sighash k1n:b990d259a71ca66f1de10fefe3210325 \
  --author @alice \
  --kind human-review
```

Format (`leanre.annot/1`, UTF-8, sorted keys, no spaces after `:` or `,`, LF newline):

```json
{"schema":"leanre.annot/1","type":"pack"}
{"default_on":true,"kind":"human-review","layer":"human/alice-landau-window","title":"Landau oscillation check","type":"layer"}
{"author":"@alice","created":"2026-11-24T00:00:00Z","layer":"human/alice-landau-window","name":"Deduction.landau_window","note":"Checked Cauchy derivative bound on [U, (1+delta)*U]; hypotheses match lemmaL call site.","sighash":"k1n:b990d259a71ca66f1de10fefe3210325","source":"https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83","status":"verified","tag":"L","target":"decl","type":"annot","updated":"2026-11-24T00:00:00Z"}
```

## 4. Zero-Slop & Licensing Checklist

1. **No raw `.lean` proof bodies:** `riemann-hypothesis` and `navier-stokes` have **no license**. Never commit `.lean` files or paste multi-line Lean code, `import` blocks, or `:= by` tactic proofs into `note`, `breaks`, or PR text.
2. **Pinned commit SHAs only:** Every GitHub `source` / `url` link must use the full 40-character commit SHA from `leanre_gallery.toml` (e.g., `/blob/40e56bab026552e089d7afcfeff08d2defb9c005/...#L83`), never floating `/blob/main/`.
3. **Kernel anchors:** `decl` records on kernel-indexed projects (`riemann-hypothesis`, `tiny-demo`) require a normalized `sighash` (`k1n:<32 hex>`).
4. **Precise scope, zero overclaims:** State specifically which definition, hypothesis, or proof step was checked. Automated CI rejects unqualified completion claims (such as claiming RH or GRH is proved outright).
5. **Verify locally before opening a PR:**
   ```bash
   python3 leanre/leanre.py annot validate annotations
   python3 leanre/leanre.py annot check-pr --all-contrib --strict --markdown-report /tmp/pr_check.md
   python3 verify/audit_tree.py
   ```
