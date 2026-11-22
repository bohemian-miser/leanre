#!/usr/bin/env python3
"""Verifier-owned, dependency-free graph oracles (deliberately naive / brute force).

Nothing here imports from leanre/. Graphs are dict[int, list[int]] or list[list[int]]
adjacency ("u depends on v" = edge u -> v), roots are ints.
"""
from __future__ import annotations

from collections import deque
from typing import Dict, Iterable, List, Optional, Sequence, Set


def reach(adj, roots: Iterable[int], removed: int = -1, target: int = -1) -> Set[int]:
    """Plain BFS. `removed` is treated as deleted. Early exit if `target` is reached."""
    seen: Set[int] = set()
    dq = deque()
    for r in roots:
        if r != removed and r not in seen:
            seen.add(r)
            dq.append(r)
    while dq:
        u = dq.popleft()
        if u == target:
            return seen
        for w in adj[u]:
            if w != removed and w not in seen:
                seen.add(w)
                dq.append(w)
    return seen


def bfs_path(adj, root: int, target: int) -> Optional[List[int]]:
    par: Dict[int, int] = {root: -1}
    dq = deque([root])
    while dq:
        u = dq.popleft()
        if u == target:
            out = []
            while u != -1:
                out.append(u)
                u = par[u]
            return out[::-1]
        for w in adj[u]:
            if w not in par:
                par[w] = u
                dq.append(w)
    return None


def idom_bruteforce(adj, root: int, v: int) -> Optional[int]:
    """Immediate dominator of v by node-removal reachability.

    Every dominator of v lies on every root->v path, so it suffices to test the nodes of
    one path: d dominates v iff v is unreachable from root once d is deleted. The
    dominators form a chain; the immediate one is the dominator nearest v on the path.
    Returns None if v is unreachable or v == root.
    """
    if v == root:
        return None
    path = bfs_path(adj, root, v)
    if path is None:
        return None
    for d in reversed(path[1:-1]):
        if v not in reach(adj, [root], removed=d, target=v):
            return d
    return root


def dominated_set_bruteforce(adj, root: int, d: int, base: Optional[Set[int]] = None) -> Set[int]:
    """All nodes dominated by d (including d): reachable normally, unreachable w/o d."""
    if base is None:
        base = reach(adj, [root])
    if d not in base:
        return set()
    if d == root:
        return set(base)
    return base - reach(adj, [root], removed=d)


def validate_path(path: Sequence[int], has_edge) -> List[str]:
    """Edge-by-edge validation of a claimed path. has_edge(u, v) -> bool."""
    errs = []
    if len(path) < 1:
        errs.append("empty path")
    for a, b in zip(path, path[1:]):
        if not has_edge(a, b):
            errs.append(f"missing edge {a}->{b}")
    if len(set(path)) != len(path):
        errs.append("path repeats a node")
    return errs


def _selftest() -> None:
    import random

    rnd = random.Random(7)
    for trial in range(300):
        n = rnd.randint(2, 40)
        adj = [[] for _ in range(n)]
        for _ in range(rnd.randint(1, 4 * n)):
            a, b = rnd.randrange(n), rnd.randrange(n)
            if a != b:
                adj[a].append(b)
        base = reach(adj, [0])
        # reference: full dominator sets by definition
        dom = {v: {d for d in base if d == v or v not in reach(adj, [0], removed=d)} for v in base}
        for v in base:
            if v == 0:
                continue
            strict = dom[v] - {v}
            # idom = the strict dominator that is dominated by all other strict dominators
            ref = [d for d in strict if all(x in dom[d] for x in strict)]
            assert len(ref) == 1, (trial, v, ref)
            assert idom_bruteforce(adj, 0, v) == ref[0], (trial, v)
        for d in base:
            assert dominated_set_bruteforce(adj, 0, d, base) == {v for v in base if d in dom[v]}
    print("graph_oracle selftest OK (300 random digraphs, idom + dominated sets vs definition)")


if __name__ == "__main__":
    _selftest()
