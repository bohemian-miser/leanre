#!/usr/bin/env python3
"""Module entry point for `python3 -m leanre`."""
from __future__ import annotations

import sys

try:
    from .leanre import main
except ImportError:  # pragma: no cover
    from leanre import main  # type: ignore[no-redef]


if __name__ == "__main__":
    raise SystemExit(main())
