# Background Research & Scope

Reference notes compiled from primary verification logs, Levent Alpöge's [announcement note](https://alpo.ge/remark.pdf), and the pinned [Lean 4 archive](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005). For machine-extracted findings from `solution.ndjson.zst`, start with [the summary findings](../findings/) or [the whole-proof synthesis](../analysis/SYNTHESIS.md).

| File | Contents |
|---|---|
| [Landscape & artifacts](01_landscape_and_artifacts.md) | Primary sources, SHA-256 pins, scale, independent checker matrix, `remark.pdf` summary, and community repos. |
| [Proof-graph analysis methods](02_re_and_tooling_strategy.md) | Proof-graph framing, `leanre` static-analysis passes, 10-layer TCB threat model, and synthetic graph validation. |
| [Mathematical background](03_cs_explainer_and_viz_ideas.md) | Mental models of RH, `Gz(x)` explicit formula, Dirichlet-GRH cryptography table, and cross-links to live views. |
| [Reference counts & verification scope](04_verification_and_roadmap.md) | Reference counts, the four verification layers, provenance tags, and scope limits. |

Local copies of primary logs and the announcement note live in gitignored `research/sources/` (zero `.lean` files or proof bodies are tracked in git).
