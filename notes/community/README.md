# Community Analyses & Verification Registry (`notes/community/`)

This directory tracks independent public verification receipts, kernel-checker runs, blueprints, proof visualizers, build-time logs, mathematical critiques, and source mirrors relevant to proofs hosted in `leanre`.

## Policy
- **Original, neutral summaries only.** Do **not** paste copyrighted or unlicensed third-party prose or verbatim Lean proof bodies.
- **Explicit scope and caveats.** Every entry must state *what* it checks or shows, and *what* it does **not** prove (e.g., kernel check ≠ mathematical peer review; text-scan visualizer ≠ kernel replay).
- **HTTPS URLs verified live** (`http_status = 200`). Never include host paths, emails, or HTML/script tags.
- **Zero-conflict PR contributions:** Drop a new file into `notes/community/contrib/<author>__<slug>.json` so parallel PRs never collide on `sources.json`.

## Adding a new analysis via PR

Create `notes/community/contrib/<author>__<slug>.json`:

```json
{
  "id": "unique-lowercase-id",
  "project": "riemann-hypothesis",
  "title": "Short descriptive title",
  "author": "Author name or @handle",
  "category": "kernel-check",
  "url": "https://example.org/verified-page",
  "repo_url": "https://github.com/owner/repo",
  "updated": "2026-11-25",
  "license": "MIT",
  "scope_summary": "1-2 concise neutral sentences describing what this resource checks or provides.",
  "caveat": "Explicit limitation / what it does not establish.",
  "key_numbers": ["175,187 modules built", "exit 0"],
  "anchors": [{"label": "TCB & axioms", "route": "#findings/tcb-and-statements"}]
}
```

Supported `category` values:
`official-statement`, `kernel-check`, `blueprint`, `visualizer`, `build-log`, `math-review`, `source-mirror`, `commentary`.

Validate locally before submitting a PR:

```bash
python3 -m leanre community --dir notes/community
```
