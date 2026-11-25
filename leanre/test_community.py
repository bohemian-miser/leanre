#!/usr/bin/env python3
"""Unit tests for `leanre.community` (`leanre.community/1`)."""
from __future__ import annotations

import json
import os
import sys
import tempfile
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import community  # noqa: E402


class TestCommunity(unittest.TestCase):
    def test_load_and_validate_good_and_bad(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            good = {
                "schema": community.COMMUNITY_SCHEMA,
                "as_of": "2026-11-25",
                "entries": [
                    {
                        "id": "lean-check-demo",
                        "project": "riemann-hypothesis",
                        "title": "Independent checker log",
                        "author": "Verifier",
                        "category": "kernel-check",
                        "url": "https://example.org/check",
                        "updated": "2026-11-24",
                        "license": "MIT",
                        "scope_summary": "Checks axiom usage against pinned export.",
                        "caveat": "Does not constitute peer review.",
                        "key_numbers": ["0 sorryAx"],
                        "anchors": [{"label": "TCB finding", "route": "#findings/tcb-and-statements"}],
                    }
                ],
            }
            with open(os.path.join(td, "sources.json"), "w", encoding="utf-8") as fh:
                json.dump(good, fh)
            os.makedirs(os.path.join(td, "contrib"), exist_ok=True)
            with open(os.path.join(td, "contrib", "alice__note.json"), "w", encoding="utf-8") as fh:
                json.dump({
                    "id": "alice-note",
                    "project": "navier-stokes",
                    "title": "Alice review note",
                    "author": "@alice",
                    "category": "math-review",
                    "url": "https://example.org/alice",
                    "updated": "2026-11-25",
                    "license": "CC-BY-4.0",
                    "scope_summary": "Audits periodic boundary setup.",
                    "caveat": "Covers statement only.",
                }, fh)
            bundle, errs = community.load_community_dir(td)
            self.assertEqual(errs, [])
            self.assertEqual(len(bundle["entries"]), 2)
            # Newest-first sort
            self.assertEqual(bundle["entries"][0]["id"], "alice-note")
            filtered = community.filter_for_project(bundle, "riemann-hypothesis")
            self.assertEqual(filtered["project_count"], 1)
            self.assertEqual(filtered["total_count"], 2)

            bad = dict(good["entries"][0])
            bad["url"] = "javascript:alert(1)"
            bad["scope_summary"] = "Check <script>alert(1)</script>"
            self.assertTrue(len(community.validate_entry(bad)) >= 2)

            bad_cat = dict(good["entries"][0])
            bad_cat["category"] = "invalid-kind"
            self.assertTrue(any("category" in e for e in community.validate_entry(bad_cat)))


if __name__ == "__main__":
    unittest.main()
