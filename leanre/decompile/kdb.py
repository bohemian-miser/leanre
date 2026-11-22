"""Read-only access to the kernel-exact graph (`outputs/kernel/kernel.db`, schema in docs/KERNEL.md)
and the Phase 2 source index (`outputs/leanre.db`).

Every connection is opened with `mode=ro` (Phase 4 CPU/RAM hygiene rule). stdlib only.
"""
from __future__ import annotations

import os
import sqlite3
from dataclasses import dataclass
from typing import Iterable, Iterator, Optional

_HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(_HERE))
DEFAULT_KERNEL_DB = os.path.join(REPO, "outputs", "kernel", "kernel.db")
DEFAULT_LEANRE_DB = os.path.join(REPO, "outputs", "leanre.db")
DEFAULT_SRC = os.path.join(REPO, "data", "rh_mirror", "src")

# edges.kind
TYPE, VALUE, BOTH = 1, 2, 3
EDGE_REL = {TYPE: "type", VALUE: "value", BOTH: "both"}

# decl_module.method values that mean "not part of the RH project" (Mathlib / Lean core / Batteries).
GROUND_METHODS = (
    "unmatched:challenge_library",
    "unmatched:library_or_external",
    "unmatched:external_private",
)


def open_ro(path: str) -> sqlite3.Connection:
    if not os.path.exists(path):
        raise FileNotFoundError(path)
    con = sqlite3.connect(f"file:{os.path.abspath(path)}?mode=ro", uri=True, check_same_thread=False)
    con.execute("PRAGMA query_only=1")
    return con


@dataclass(frozen=True)
class Decl:
    id: int
    name: str
    kind: str
    module: Optional[str]
    method: str
    src_decl_id: Optional[int]

    @property
    def ground(self) -> bool:
        """True for Mathlib/Lean/external decls (not authored in the RH project)."""
        return self.method in GROUND_METHODS

    @property
    def is_aux(self) -> bool:
        last = self.name.rsplit(".", 1)[-1]
        return last.startswith("_") or last.startswith("match_") or last.startswith("proof_")


@dataclass(frozen=True)
class DomNode:
    decl_id: int
    idom: Optional[int]
    depth: int
    subtree_size: int


class KernelDB:
    """Thin read-only facade over kernel.db (+ optional leanre.db for file:line anchors)."""

    def __init__(self, kernel_db: str = DEFAULT_KERNEL_DB, leanre_db: Optional[str] = DEFAULT_LEANRE_DB,
                 tree: str = "ALL") -> None:
        self.kpath = kernel_db
        self.k = open_ro(kernel_db)
        self.l = open_ro(leanre_db) if leanre_db and os.path.exists(leanre_db) else None
        row = self.k.execute("SELECT id FROM dom_trees WHERE label=?", (tree,)).fetchone()
        if row is None:
            raise KeyError(f"dom tree {tree!r} not found")
        self.tree_id = int(row[0])
        self.tree_label = tree
        self._decl_cache: dict[int, Decl] = {}

    # ---- declarations -------------------------------------------------
    _DECL_SQL = ("SELECT d.id, d.name, d.kind, m.module, COALESCE(m.method,'unmatched:none'), m.src_decl_id "
                 "FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id ")

    def _mk(self, r) -> Decl:
        d = Decl(int(r[0]), r[1], r[2], r[3], r[4], r[5])
        self._decl_cache[d.id] = d
        return d

    def decl(self, key: int | str) -> Decl:
        if isinstance(key, int):
            if key in self._decl_cache:
                return self._decl_cache[key]
            r = self.k.execute(self._DECL_SQL + "WHERE d.id=?", (key,)).fetchone()
        else:
            r = self.k.execute(self._DECL_SQL + "WHERE d.name=?", (key,)).fetchone()
            if r is None:  # constants (ctors/recs/projections) belong to a parent decl record
                c = self.k.execute("SELECT decl_id FROM consts WHERE name=?", (key,)).fetchone()
                if c is not None:
                    r = self.k.execute(self._DECL_SQL + "WHERE d.id=?", (int(c[0]),)).fetchone()
        if r is None:
            raise KeyError(f"declaration not in kernel.db: {key!r}")
        return self._mk(r)

    def maybe(self, key: int | str) -> Optional[Decl]:
        try:
            return self.decl(key)
        except KeyError:
            return None

    def decls(self, ids: Iterable[int]) -> list[Decl]:
        ids = list(ids)
        out: dict[int, Decl] = {i: self._decl_cache[i] for i in ids if i in self._decl_cache}
        miss = [i for i in ids if i not in out]
        for chunk in _chunks(miss, 900):
            q = self._DECL_SQL + f"WHERE d.id IN ({','.join('?' * len(chunk))})"
            for r in self.k.execute(q, chunk):
                out[int(r[0])] = self._mk(r)
        return [out[i] for i in ids if i in out]

    def search(self, pattern: str, limit: int = 50) -> list[Decl]:
        q = self._DECL_SQL + "WHERE d.name LIKE ? ORDER BY length(d.name) LIMIT ?"
        return [self._mk(r) for r in self.k.execute(q, (pattern, limit))]

    # ---- edges --------------------------------------------------------
    def deps(self, d: int | str | Decl, kinds: tuple[int, ...] = (TYPE, VALUE, BOTH)) -> list[tuple[Decl, int]]:
        i = d.id if isinstance(d, Decl) else self.decl(d).id
        rows = self.k.execute("SELECT dst, kind FROM edges WHERE src=?", (i,)).fetchall()
        rows = [(int(a), int(b)) for a, b in rows if int(b) in kinds]
        ds = {x.id: x for x in self.decls([a for a, _ in rows])}
        return [(ds[a], b) for a, b in rows if a in ds]

    def users(self, d: int | str | Decl, limit: int = 1000) -> list[tuple[Decl, int]]:
        i = d.id if isinstance(d, Decl) else self.decl(d).id
        rows = self.k.execute("SELECT src, kind FROM edges WHERE dst=? LIMIT ?", (i, limit)).fetchall()
        ds = {x.id: x for x in self.decls([int(a) for a, _ in rows])}
        return [(ds[int(a)], int(b)) for a, b in rows if int(a) in ds]

    def edge_kind(self, src: int, dst: int) -> Optional[int]:
        r = self.k.execute("SELECT kind FROM edges WHERE src=? AND dst=?", (src, dst)).fetchone()
        return int(r[0]) if r else None

    def iter_out_batch(self, ids: list[int]) -> Iterator[tuple[int, int, int]]:
        for chunk in _chunks(ids, 900):
            q = f"SELECT src, dst, kind FROM edges WHERE src IN ({','.join('?' * len(chunk))})"
            yield from self.k.execute(q, chunk)

    # ---- dominator tree -----------------------------------------------
    def dom(self, d: int | str | Decl) -> Optional[DomNode]:
        i = d.id if isinstance(d, Decl) else self.decl(d).id
        r = self.k.execute("SELECT decl_id, idom, depth, subtree_size FROM dom WHERE tree_id=? AND decl_id=?",
                           (self.tree_id, i)).fetchone()
        return DomNode(int(r[0]), r[1], int(r[2]), int(r[3])) if r else None

    def dom_children(self, d: int | str | Decl | None, limit: int = 50, min_size: int = 1) -> list[DomNode]:
        if d is None:
            q = ("SELECT decl_id, idom, depth, subtree_size FROM dom WHERE tree_id=? AND idom IS NULL "
                 "AND subtree_size>=? ORDER BY subtree_size DESC, decl_id LIMIT ?")
            args: tuple = (self.tree_id, min_size, limit)
        else:
            i = d.id if isinstance(d, Decl) else self.decl(d).id
            q = ("SELECT decl_id, idom, depth, subtree_size FROM dom WHERE tree_id=? AND idom=? "
                 "AND subtree_size>=? ORDER BY subtree_size DESC, decl_id LIMIT ?")
            args = (self.tree_id, i, min_size, limit)
        return [DomNode(int(a), b, int(c), int(e)) for a, b, c, e in self.k.execute(q, args)]

    def dom_child_stats(self, d: int | str | Decl) -> dict:
        i = d.id if isinstance(d, Decl) else self.decl(d).id
        n, s, singles = self.k.execute(
            "SELECT count(*), COALESCE(sum(subtree_size),0), COALESCE(sum(subtree_size=1),0) FROM dom "
            "WHERE tree_id=? AND idom=?", (self.tree_id, i)).fetchone()
        return {"children": int(n), "children_subtree_total": int(s), "leaf_children": int(singles)}

    def dom_path(self, d: int | str | Decl) -> list[DomNode]:
        """idom chain from `d` up to the virtual root (d first)."""
        out: list[DomNode] = []
        node = self.dom(d)
        while node is not None:
            out.append(node)
            node = self.dom(int(node.idom)) if node.idom is not None else None
        return out

    def roots(self) -> list[tuple[int, str, int, str]]:
        return [(int(a), b, int(c), e) for a, b, c, e in self.k.execute("SELECT id,name,decl_id,grp FROM roots ORDER BY id")]

    # ---- source anchors -----------------------------------------------
    def src_row(self, d: Decl) -> Optional[dict]:
        """Phase 2 leanre.db row (module file + line + 1-line signature snippet) for a kernel decl."""
        if self.l is None or d.src_decl_id is None or not d.method.startswith(("leanre_db", "aux_prefix:leanre_db")):
            return None
        r = self.l.execute(
            "SELECT d.name, d.kind, d.module, d.line_no, d.signature_snippet, d.horn_requires_json, d.horn_proves, m.file_path "
            "FROM declarations d JOIN modules m ON m.name = d.module WHERE d.id=?", (d.src_decl_id,)).fetchone()
        if r is None:
            return None
        return {"name": r[0], "kind": r[1], "module": r[2], "line": int(r[3]), "snippet": r[4],
                "horn_requires": r[5], "horn_proves": r[6], "file": r[7]}

    def module_file(self, module: str) -> Optional[str]:
        if self.l is not None:
            r = self.l.execute("SELECT file_path FROM modules WHERE name=?", (module,)).fetchone()
            if r:
                return r[0]
        return module.replace(".", "/") + ".lean"


def _chunks(xs: list, n: int) -> Iterator[list]:
    for i in range(0, len(xs), n):
        yield xs[i:i + n]
