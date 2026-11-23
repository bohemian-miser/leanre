"""Read-only access to the kernel-exact graph (`outputs/kernel/kernel.db`, schema in docs/KERNEL.md)
and the Phase 2 source index (`outputs/leanre.db`).

Every connection is opened with `mode=ro` (Phase 4 CPU/RAM hygiene rule). stdlib only.
"""
from __future__ import annotations

import difflib
import os
import re
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

_AUX_LAST_PREFIXES = ("_", "match_", "proof_")


def is_aux_name(name: str) -> bool:
    """True for compiler/tactic auxiliary declarations (._proof_*, ._simp_*, _rarg, etc.)."""
    last = name.rsplit(".", 1)[-1]
    return (
        last.startswith(_AUX_LAST_PREFIXES)
        or "._" in name
        or last.endswith("_rarg")
    )


def _escape_like(s: str) -> str:
    return s.replace("!", "!!").replace("%", "!%").replace("_", "!_")


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
        return is_aux_name(self.name)


@dataclass(frozen=True)
class DomNode:
    decl_id: int
    idom: Optional[int]
    depth: int
    subtree_size: int


@dataclass(frozen=True)
class ResolveHit:
    decl: Decl
    all_dom: int
    match: str


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
        if tree == "ALL":
            self._all_tree_id = self.tree_id
        else:
            arow = self.k.execute("SELECT id FROM dom_trees WHERE label='ALL'").fetchone()
            self._all_tree_id = int(arow[0]) if arow else self.tree_id
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

    def search(
        self,
        pattern: str,
        limit: int = 50,
        *,
        project_only: bool = False,
        no_aux: bool = False,
        case_sensitive: bool = False,
        kind: Optional[str] = None,
        module_regex: Optional[str] = None,
        sort_by: str = "name",
    ) -> list[Decl]:
        return [
            r[0]
            for r in self.search_rows(
                pattern,
                limit,
                project_only=project_only,
                no_aux=no_aux,
                case_sensitive=case_sensitive,
                kind=kind,
                module_regex=module_regex,
                sort_by=sort_by,
            )
        ]

    def search_rows(
        self,
        pattern: str,
        limit: int = 50,
        *,
        project_only: bool = False,
        no_aux: bool = False,
        case_sensitive: bool = False,
        kind: Optional[str] = None,
        module_regex: Optional[str] = None,
        sort_by: str = "name",
    ) -> list[tuple[Decl, Optional[int], int, int]]:
        """Search decls returning `(Decl, dom_subtree, fan_in, value_nodes)`."""
        if sort_by not in ("name", "dom", "fan_in", "vn"):
            raise ValueError(f"invalid sort_by {sort_by!r} (expected name|dom|fan_in|vn)")
        has_wild = "%" in pattern
        like_pat = pattern if has_wild else f"%{_escape_like(pattern)}%"
        where = ["d.name LIKE ? ESCAPE '!'"] if not has_wild else ["d.name LIKE ?"]
        params: list = [self._all_tree_id, like_pat]
        if project_only:
            ph = ",".join("?" * len(GROUND_METHODS))
            where.append(f"COALESCE(m.method, 'unmatched:none') NOT IN ({ph})")
            params.extend(GROUND_METHODS)
        if kind:
            kinds = [k.strip() for k in kind.split(",") if k.strip()]
            if kinds:
                ph = ",".join("?" * len(kinds))
                where.append(f"d.kind IN ({ph})")
                params.extend(kinds)
        if no_aux:
            where.append("d.name NOT LIKE '%.!_%' ESCAPE '!' AND d.name NOT LIKE '%!_rarg' ESCAPE '!'")
        order_map = {
            "name": "length(d.name) ASC, d.name ASC",
            "dom": "COALESCE(dom.subtree_size, 0) DESC, length(d.name) ASC, d.name ASC",
            "fan_in": "d.fan_in DESC, length(d.name) ASC, d.name ASC",
            "vn": "d.value_nodes DESC, length(d.name) ASC, d.name ASC",
        }
        sql_limit = "" if (limit <= 0 or case_sensitive or module_regex or no_aux) else f" LIMIT {int(limit)}"
        q = (
            "SELECT d.id, d.name, d.kind, m.module, COALESCE(m.method,'unmatched:none'), m.src_decl_id, "
            "dom.subtree_size, d.fan_in, d.value_nodes "
            "FROM decls d "
            "LEFT JOIN decl_module m ON m.decl_id = d.id "
            "LEFT JOIN dom ON dom.tree_id = ? AND dom.decl_id = d.id "
            f"WHERE {' AND '.join(where)} "
            f"ORDER BY {order_map[sort_by]}{sql_limit}"
        )
        mod_rx = re.compile(module_regex) if module_regex else None
        if case_sensitive:
            if has_wild:
                rx_parts = [re.escape(p) for p in pattern.split("%")]
                name_rx = re.compile("^" + ".*".join(rx_parts) + "$")
            else:
                name_rx = None
        else:
            name_rx = None

        out: list[tuple[Decl, Optional[int], int, int]] = []
        for r in self.k.execute(q, params):
            d = self._mk(r[:6])
            if no_aux and d.is_aux:
                continue
            if case_sensitive:
                if name_rx is not None:
                    if not name_rx.match(d.name):
                        continue
                elif pattern not in d.name:
                    continue
            if mod_rx is not None and not mod_rx.search(d.module or ""):
                continue
            dom_sz = int(r[6]) if r[6] is not None else None
            out.append((d, dom_sz, int(r[7]), int(r[8])))
            if limit > 0 and len(out) >= limit:
                break
        return out

    def all_dom_subtree(self, decl_id: int) -> int:
        r = self.k.execute(
            "SELECT subtree_size FROM dom WHERE tree_id=? AND decl_id=?",
            (self._all_tree_id, decl_id),
        ).fetchone()
        return int(r[0]) if r else 0

    def decl_stats(self, d: int | str | Decl) -> dict:
        decl_obj = d if isinstance(d, Decl) else self.decl(d)
        r = self.k.execute(
            "SELECT kind, n_consts, type_nodes, value_nodes, fan_in, fan_out, "
            "fan_out_type, fan_out_value, flags, live_mask, stmt_mask, defcone_mask, attrs "
            "FROM decls WHERE id=?",
            (decl_obj.id,),
        ).fetchone()
        if r is None:
            raise KeyError(f"declaration not in kernel.db: {decl_obj.id}")
        return {
            "id": decl_obj.id,
            "name": decl_obj.name,
            "kind": r[0],
            "n_consts": int(r[1]),
            "type_nodes": int(r[2]),
            "value_nodes": int(r[3]),
            "fan_in": int(r[4]),
            "fan_out": int(r[5]),
            "fan_out_type": int(r[6]),
            "fan_out_value": int(r[7]),
            "flags": int(r[8]),
            "live_mask": int(r[9]),
            "stmt_mask": int(r[10]),
            "defcone_mask": int(r[11]),
            "attrs": int(r[12]),
            "module": decl_obj.module,
            "method": decl_obj.method,
            "all_dom_subtree": self.all_dom_subtree(decl_obj.id),
        }

    def resolve(self, query: str, limit: int = 10) -> list[ResolveHit]:
        """Resolve an exact name, module-qualified root, suffix, or near-miss namespace.

        Returns candidates sorted by `ALL dom` subtree size descending.
        """
        exact = self.maybe(query)
        if exact is not None:
            return [ResolveHit(exact, self.all_dom_subtree(exact.id), "exact")]

        parts = [p for p in query.split(".") if p]
        stem = parts[-1] if parts else query
        seen: dict[int, tuple[Decl, int, str]] = {}

        def add_row(d: Decl, sz: int, tag: str) -> None:
            prev = seen.get(d.id)
            rank = {"suffix": 0, "substring": 1, "fuzzy": 2}
            if prev is None or rank[tag] < rank[prev[2]]:
                seen[d.id] = (d, sz, tag)

        # 1. Exact suffix matches via dot-stripping (fast PK/index lookup)
        for i in range(1, len(parts)):
            sub = ".".join(parts[i:])
            d = self.maybe(sub)
            if d is not None:
                add_row(d, self.all_dom_subtree(d.id), "suffix")

        # 2. Suffix LIKE matches (`%.<stem>` or `=<stem>`)
        sql_cap = max(limit * 10, 200)
        q_suf = (
            "SELECT d.id, d.name, d.kind, m.module, COALESCE(m.method,'unmatched:none'), m.src_decl_id, "
            "COALESCE(dom.subtree_size, 0) AS sz "
            "FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id "
            "LEFT JOIN dom ON dom.tree_id = ? AND dom.decl_id = d.id "
            "WHERE d.name LIKE ? ESCAPE '!' OR d.name = ? "
            "ORDER BY sz DESC, length(d.name) ASC LIMIT ?"
        )
        for r in self.k.execute(q_suf, (self._all_tree_id, f"%.{_escape_like(stem)}", stem, sql_cap)):
            add_row(self._mk(r[:6]), int(r[6]), "suffix")

        # 3. Substring LIKE matches (`%<stem>%`) if needed
        if len(seen) < limit and len(stem) >= 3:
            q_sub = (
                "SELECT d.id, d.name, d.kind, m.module, COALESCE(m.method,'unmatched:none'), m.src_decl_id, "
                "COALESCE(dom.subtree_size, 0) AS sz "
                "FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id "
                "LEFT JOIN dom ON dom.tree_id = ? AND dom.decl_id = d.id "
                "WHERE d.name LIKE ? ESCAPE '!' "
                "ORDER BY sz DESC, length(d.name) ASC LIMIT ?"
            )
            for r in self.k.execute(q_sub, (self._all_tree_id, f"%{_escape_like(stem)}%", sql_cap)):
                add_row(self._mk(r[:6]), int(r[6]), "substring")

        # 4. Fuzzy fallback (typos / near-miss stems) if still scarce
        if not seen and len(stem) >= 4:
            mid = len(stem) // 2
            chunks = [stem[:mid], stem[mid:]]
            like_clauses = ["d.name LIKE ? ESCAPE '!'"] * len(chunks)
            params_fz: list = [self._all_tree_id] + [f"%{_escape_like(c)}%" for c in chunks]
            if len(parts) > 1:
                like_clauses.append("d.name LIKE ? ESCAPE '!'")
                params_fz.append(f"{_escape_like(parts[0])}.%")
            params_fz.append(500)
            q_fz = (
                "SELECT d.id, d.name, d.kind, m.module, COALESCE(m.method,'unmatched:none'), m.src_decl_id, "
                "COALESCE(dom.subtree_size, 0) AS sz "
                "FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id "
                "LEFT JOIN dom ON dom.tree_id = ? AND dom.decl_id = d.id "
                f"WHERE {' OR '.join(like_clauses)} "
                "ORDER BY sz DESC, length(d.name) ASC LIMIT ?"
            )
            stem_lo = stem.lower()
            for r in self.k.execute(q_fz, params_fz):
                d = self._mk(r[:6])
                d_stem = d.name.rsplit(".", 1)[-1].lower()
                if difflib.SequenceMatcher(None, stem_lo, d_stem).ratio() >= 0.55:
                    add_row(d, int(r[6]), "fuzzy")

        q_lo = query.lower()
        stem_lo = stem.lower()

        def sort_key(item: tuple[Decl, int, str]) -> tuple:
            d, sz, tag = item
            tier = 0 if tag == "suffix" else (1 if tag == "substring" else 2)
            exact_case_suf = d.name == stem or d.name.endswith("." + stem) or d.name.endswith("." + query)
            d_stem_lo = d.name.rsplit(".", 1)[-1].lower()
            sim = difflib.SequenceMatcher(None, stem_lo, d_stem_lo).ratio() if tier == 2 else 0.0
            common_pref = 0
            for a_seg, b_seg in zip(parts[:-1], d.name.split(".")[:-1]):
                if a_seg.lower() == b_seg.lower():
                    common_pref += 1
                else:
                    break
            return (
                tier,
                1 if d.is_aux else 0,
                -sz,
                0 if exact_case_suf else 1,
                -common_pref,
                -round(sim, 3),
                0 if q_lo in d.name.lower() else 1,
                len(d.name),
                d.name,
            )

        ranked = sorted(seen.values(), key=sort_key)
        return [ResolveHit(d, sz, tag) for d, sz, tag in ranked[:limit]]

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

    def dom_below_count(self, d: int | str | Decl, min_size: int) -> int:
        i = d.id if isinstance(d, Decl) else self.decl(d).id
        r = self.k.execute(
            "SELECT count(*) FROM dom WHERE tree_id=? AND idom=? AND subtree_size<?",
            (self.tree_id, i, min_size),
        ).fetchone()
        return int(r[0]) if r else 0

    def ground_id_set(self, ids: Iterable[int]) -> set[int]:
        """Return the subset of `ids` whose `decl_module.method` is in `GROUND_METHODS`."""
        id_list = list(ids)
        if not id_list:
            return set()
        ph = ",".join("?" * len(GROUND_METHODS))
        if len(id_list) > 10_000:
            id_set = set(id_list)
            q = f"SELECT decl_id FROM decl_module WHERE method IN ({ph})"
            return {int(did) for (did,) in self.k.execute(q, GROUND_METHODS) if int(did) in id_set}
        out: set[int] = set()
        for chunk in _chunks(id_list, 900):
            iph = ",".join("?" * len(chunk))
            q = f"SELECT decl_id FROM decl_module WHERE decl_id IN ({iph}) AND method IN ({ph})"
            for (did,) in self.k.execute(q, [*chunk, *GROUND_METHODS]):
                out.add(int(did))
        return out

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
