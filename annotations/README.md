# Annotations (`leanre.annot/1`)

Git-backed JSONL overlays attaching audited notes, status tags, and symbol renames to declarations, modules, and folders without touching deterministic tool outputs.

## Directory Layout

```text
annotations/
  human__canonical-facts.jsonl              # Seed human-reviewed facts (default_on: true)
  ai__decomp-phase4.jsonl                   # Phase 4 AI-draft landmarks (default_on: false, draft: true)
  ai__decomp-phase6.jsonl                   # Phase 5-6 AI-draft landmarks (default_on: false, draft: true)
  contrib/
    <project_slug>/                         # Slug from leanre_gallery.toml (e.g. riemann-hypothesis)
      <author_slug>__<pack_slug>.jsonl      # One file per contributor + topic -> zero merge conflicts
  tools/                                    # Seed/landmark pack generators
```

Each contributor or automated bot writes **only** its own `<author_slug>__<pack_slug>.jsonl` file under `annotations/contrib/<project_slug>/` (max `2 MiB`).

## Minimal 5-Line Pack Example

Every file is canonical UTF-8 JSONL (`sort_keys=True`, `separators=(",", ":")`, LF endings):

```json
{"schema":"leanre.annot/1","type":"pack"}
{"default_on":false,"kind":"ai-draft","layer":"ai/bot-demo-scan","title":"Bot structural scan","type":"layer"}
{"default_on":true,"kind":"human-review","layer":"human/alice-demo","title":"Alice review notes","type":"layer"}
{"author":"ai:bot-demo","breaks":"Header-only check; proof body unread.","created":"2026-11-24T00:00:00Z","draft":true,"layer":"ai/bot-demo-scan","name":"TinyDemo.ProofBundle","note":"1-constructor structure with 1 unread field in DeadCode.lean.","sighash":"k1n:b0d73eadd3306c7d128f0df3845a5c49","source":"examples/tiny_demo/Bundles.lean#L9","status":"summary","tag":"M","target":"decl","type":"annot","updated":"2026-11-24T00:00:00Z"}
{"author":"@alice","created":"2026-11-24T00:00:00Z","layer":"human/alice-demo","name":"TinyDemo.main_theorem","note":"Forwards directly to bundle_weight_refl via alias_bundle_weight.","sighash":"k1n:d881d9bce631f1d640f5c9be764f5014","source":"examples/tiny_demo/Main.lean#L11","status":"verified","tag":"L","target":"decl","type":"annot","updated":"2026-11-24T00:00:00Z"}
```

## Trust Tiers & Contested Declarations

- **Human review (`human` / `human-review`):** `default_on: true` allowed; author `@handle`; `status` in `verified | read | summary | flagged`.
- **AI / bot layers (`ai-draft` / `bot-check`):** **must** set `default_on: false` on the layer and `"draft": true` on every record, with author `ai:<model>` or `bot:<tool>`. `ai-draft` records must use `tag: "M"` with a `breaks` caveat and cannot claim `status: "verified"`.
- **Contested targets (`contested: true`):** `leanre annot overlay` compiles all packs into `leanre.treemap.overlay/1` JSON and automatically marks `contested: true` whenever two layers disagree on the same target (e.g., `verified` vs. `flagged`/`suspect`).

## CLI Quick Reference

```bash
# 1. Generate a canonical starter pack in annotations/contrib/<project>/
python3 leanre/leanre.py annot template --project riemann-hypothesis \
  --name UpperTheory.FinalTheorems.everyCharacter --author @alice --kind human-review

# 2. Validate canonical bytes, PR rules, and pinned SHAs (works offline without kernel.db)
python3 leanre/leanre.py annot validate annotations
python3 leanre/leanre.py annot check-pr --all-contrib --strict --markdown-report /tmp/summary.md

# 3. Compile treemap overlay JSON
python3 leanre/leanre.py annot overlay annotations --project riemann-hypothesis -o /tmp/overlay.json
```

See [CONTRIBUTING_NOTES.md](../CONTRIBUTING_NOTES.md) for the PR checklist and [docs/ANNOTATION_PACKS.md](../docs/ANNOTATION_PACKS.md) for the full `leanre.annot/1` specification.
