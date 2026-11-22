"""Allow `python3 -m decompile ...` (cwd=leanre/) and `python3 leanre/decompile ...`."""
import os
import sys

if __package__ in (None, ""):
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from decompile.cli import main  # type: ignore
else:
    from .cli import main

if __name__ == "__main__":
    sys.exit(main())
