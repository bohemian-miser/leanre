"""leanre.decompile — Phase 4 proof decompiler (gate D1).

    kdb.KernelDB      read-only kernel.db / leanre.db facade (decls, edges, dominators, anchors)
    source            exact header / fields / def-body reader over data/rh_mirror/src
    graph.Decompiler  contract unfolder, Horn clauses, dominator spine, cones
    schema            leanre.decomp/v1 validator for outputs/decomp/*.json
    cli               `leanre decompile ...` (register_cli hook)
"""
from .kdb import KernelDB, Decl  # noqa: F401
from .graph import Decompiler  # noqa: F401
from .schema import SCHEMA_ID, validate  # noqa: F401
