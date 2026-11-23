#!/usr/bin/env python3
"""Profile configuration loader and repository auto-discovery (`leanre.toml`).

Uses Python 3.11+ standard-library ``tomllib`` with zero external dependencies.
Supports loading a ``leanre.toml`` profile and auto-discovering Lean 4 / Lake
project metadata (``lakefile.toml``, ``lakefile.lean``, ``lake-manifest.json``,
``lean-toolchain``, source roots, and candidate headline roots) via ``cmd_init``.
"""
from __future__ import annotations

import argparse
import dataclasses
import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

DEFAULT_CONFIG_FILENAME = "leanre.toml"

_SKIP_DIRS: Set[str] = {
    ".git",
    ".github",
    ".lake",
    ".vscode",
    ".docker",
    ".devcontainer",
    "build",
    "blueprint",
    "blueprint-verso",
    "docs",
    "errata",
    "examples",
    "home_page",
    "node_modules",
    "outputs",
    "paper",
    "scripts",
    "target",
    "test",
    "tests",
    "__pycache__",
}

_RE_LAKE_PKG = re.compile(r"^\s*package\s+«?([A-Za-z0-9_.-]+)»?", re.MULTILINE)
_RE_LAKE_LIB = re.compile(r"^\s*lean_lib\s+«?([A-Za-z0-9_.-]+)»?", re.MULTILINE)
_RE_LAKE_EXE = re.compile(r"^\s*lean_exe\s+«?([A-Za-z0-9_.-]+)»?", re.MULTILINE)
_RE_LAKE_REQ = re.compile(r"^\s*require\s+«?([A-Za-z0-9_.-]+)»?", re.MULTILINE)
_RE_LAKE_SRCDIR = re.compile(r'\bsrcDir\s*:=\s*"([^"]+)"')
_RE_LAKE_DEFAULT = re.compile(r"@\[default_target\]\s*(?:lean_lib|lean_exe)\s+«?([A-Za-z0-9_.-]+)»?", re.MULTILINE)
_RE_NS_OPEN = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.'₀-₉]*)")
_RE_SEC_OPEN = re.compile(r"^\s*section(?:\s+([A-Za-z_][A-Za-z0-9_.'₀-₉]*))?\b")
_RE_NS_END = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_.'₀-₉]*))?\s*$")
_RE_TOP_THEOREM = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?P<mods>(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)\s+)*)"
    r"(?:theorem|lemma)\s+(?P<name>[A-Za-z_][A-Za-z0-9_.'₀-₉]*)\b"
)
_RE_IMPORT_LINE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z_][^\s]*)")
_RE_GITHUB_REMOTE = re.compile(
    r"(?:https?://github\.com/|git@github\.com:)([^/\s]+)/([^/\s]+?)(?:\.git)?$"
)


@dataclasses.dataclass
class ForensicRegexSpec:
    tag: str
    pattern: str
    severity: str = "info"

    def compile(self) -> Tuple[str, re.Pattern[str]]:
        return (self.tag, re.compile(self.pattern))


@dataclasses.dataclass
class LeanreConfig:
    schema_version: int = 1
    project_name: str = ""
    root_module: str = "Main"
    src_dir: str = "src"
    export_path: str = ""
    source_roots: List[str] = dataclasses.field(default_factory=list)
    lean_toolchain: str = ""
    pinned_commit: str = ""
    repo_url: str = ""
    upstream_url_template: str = ""
    lakefile: str = ""
    dependencies: List[str] = dataclasses.field(default_factory=list)
    headline_roots: List[str] = dataclasses.field(default_factory=list)
    statement_wrappers: List[str] = dataclasses.field(default_factory=list)
    root_groups: Dict[str, List[str]] = dataclasses.field(default_factory=dict)
    candidate_root_modules: List[str] = dataclasses.field(default_factory=list)
    rh_gates: bool = False
    timeout_modules: Set[str] = dataclasses.field(default_factory=set)
    slow_targets: Dict[str, Dict[str, Any]] = dataclasses.field(default_factory=dict)
    extra_regexes: List[ForensicRegexSpec] = dataclasses.field(default_factory=list)
    source_path: Optional[str] = None

    @classmethod
    def empty(cls) -> "LeanreConfig":
        """Return a neutral generic-repository configuration (no RH assumptions)."""
        return cls()

    @classmethod
    def from_dict(cls, data: Dict[str, Any], source_path: Optional[str] = None) -> "LeanreConfig":
        proj = data.get("project", {}) or {}
        roots = data.get("roots", {}) or {}
        forensics = data.get("forensics", {}) or {}

        groups_raw = roots.get("groups", {}) or {}
        root_groups: Dict[str, List[str]] = {
            str(k): [str(x) for x in (v or [])] for k, v in groups_raw.items()
        }

        headline_raw = roots.get("headline", []) or proj.get("headline_roots", []) or []
        headline_roots = [str(x) for x in headline_raw]

        # Also support compact `project.roots = ["Name:Group", ...]` notation
        for spec in proj.get("roots", []) or []:
            s = str(spec)
            if ":" in s:
                nm, grp = s.split(":", 1)
                nm, grp = nm.strip(), grp.strip() or "ROOT"
                root_groups.setdefault(grp, [])
                if nm and nm not in root_groups[grp]:
                    root_groups[grp].append(nm)
                if nm and nm not in headline_roots:
                    headline_roots.append(nm)
            elif s.strip() and s.strip() not in headline_roots:
                headline_roots.append(s.strip())

        if not headline_roots and root_groups:
            seen: Set[str] = set()
            for vals in root_groups.values():
                for v in vals:
                    if v not in seen:
                        seen.add(v)
                        headline_roots.append(v)

        slow_targets: Dict[str, Dict[str, Any]] = {}
        raw_slow = forensics.get("slow_targets", []) or []
        if isinstance(raw_slow, dict):
            for mod, info in raw_slow.items():
                if isinstance(info, dict):
                    slow_targets[str(mod)] = dict(info)
        else:
            for item in raw_slow:
                if isinstance(item, dict) and item.get("module"):
                    mod = str(item["module"])
                    slow_targets[mod] = {
                        "decl": str(item.get("decl", "")),
                        "full_decl": str(item.get("full_decl", item.get("decl", ""))),
                        "seconds": float(item.get("seconds", 0.0)),
                    }

        extra_regexes: List[ForensicRegexSpec] = []
        raw_rx = forensics.get("extra_regexes", []) or []
        if isinstance(raw_rx, dict):
            for tag, pat in raw_rx.items():
                if isinstance(pat, str):
                    extra_regexes.append(ForensicRegexSpec(tag=str(tag), pattern=pat))
                elif isinstance(pat, dict) and pat.get("pattern"):
                    extra_regexes.append(
                        ForensicRegexSpec(
                            tag=str(tag),
                            pattern=str(pat["pattern"]),
                            severity=str(pat.get("severity", "info")),
                        )
                    )
        else:
            for item in raw_rx:
                if isinstance(item, dict) and item.get("tag") and item.get("pattern"):
                    extra_regexes.append(
                        ForensicRegexSpec(
                            tag=str(item["tag"]),
                            pattern=str(item["pattern"]),
                            severity=str(item.get("severity", "info")),
                        )
                    )

        return cls(
            schema_version=int(data.get("schema_version", 1)),
            project_name=str(proj.get("name", "")),
            root_module=str(proj.get("root_module") or proj.get("main_module") or "Main"),
            src_dir=str(proj.get("src_dir", "src")),
            export_path=str(proj.get("export_path", "")),
            source_roots=[str(x) for x in (proj.get("source_roots", []) or [])],
            lean_toolchain=str(proj.get("lean_toolchain", "")),
            pinned_commit=str(proj.get("pinned_commit", "")),
            repo_url=str(proj.get("repo_url", "")),
            upstream_url_template=str(proj.get("upstream_url_template", "")),
            lakefile=str(proj.get("lakefile", "")),
            dependencies=[str(x) for x in (proj.get("dependencies", []) or [])],
            headline_roots=headline_roots,
            statement_wrappers=[str(x) for x in (roots.get("statement_wrappers", []) or [])],
            root_groups=root_groups,
            candidate_root_modules=[str(x) for x in (roots.get("candidate_modules", []) or [])],
            rh_gates=bool(forensics.get("rh_gates", False)),
            timeout_modules={str(x) for x in (forensics.get("timeout_modules", []) or [])},
            slow_targets=slow_targets,
            extra_regexes=extra_regexes,
            source_path=source_path,
        )

    @classmethod
    def from_toml(cls, path: str | os.PathLike[str]) -> "LeanreConfig":
        p = Path(path)
        with p.open("rb") as f:
            data = tomllib.load(f)
        return cls.from_dict(data, source_path=str(p))

    def kernel_root_specs(self) -> List[str]:
        """Format headline roots as ``NAME:GROUP`` specs for ``leanre-kernel --root``."""
        root_to_group: Dict[str, str] = {}
        for grp, names in self.root_groups.items():
            for nm in names:
                root_to_group.setdefault(nm, grp)
        specs: List[str] = []
        for nm in self.headline_roots:
            grp = root_to_group.get(nm, "ROOT")
            specs.append(f"{nm}:{grp}")
        return specs

    def compiled_extra_regexes(self) -> List[Tuple[str, re.Pattern[str]]]:
        return [spec.compile() for spec in self.extra_regexes]

    def resolve_src_dir(self, base_dir: Optional[str | os.PathLike[str]] = None) -> str:
        """Resolve ``src_dir`` relative to ``base_dir`` or the config file's parent."""
        if os.path.isabs(self.src_dir):
            return self.src_dir
        if base_dir is not None:
            return str(Path(base_dir) / self.src_dir)
        if self.source_path:
            return str(Path(self.source_path).resolve().parent / self.src_dir)
        return self.src_dir


def find_config(start_dir: Optional[str | os.PathLike[str]] = None) -> Optional[Path]:
    """Walk upward from ``start_dir`` (default: cwd) to locate ``leanre.toml``."""
    cur = Path(start_dir or os.getcwd()).resolve()
    if cur.is_file():
        cur = cur.parent
    for directory in (cur, *cur.parents):
        cand = directory / DEFAULT_CONFIG_FILENAME
        if cand.is_file():
            return cand
    return None


def find_local_config(target_path: str | os.PathLike[str]) -> Optional[Path]:
    """Find a ``leanre.toml`` belonging specifically to ``target_path`` without
    walking up into an unrelated parent repository's config.

    Checks ``<target>/leanre.toml`` first, then ``<target.parent>/leanre.toml``
    only if that parent config's resolved ``src_dir`` matches ``target``.
    """
    cur = Path(target_path).resolve()
    if cur.is_file():
        cur = cur.parent
    direct = cur / DEFAULT_CONFIG_FILENAME
    if direct.is_file():
        return direct
    parent_cand = cur.parent / DEFAULT_CONFIG_FILENAME
    if parent_cand.is_file():
        try:
            pcfg = LeanreConfig.from_toml(parent_cand)
            if Path(pcfg.resolve_src_dir()).resolve() == cur:
                return parent_cand
        except (OSError, tomllib.TOMLDecodeError, ValueError):
            pass
    return None


def load_config(
    path: Optional[str | os.PathLike[str]] = None,
    *,
    start_dir: Optional[str | os.PathLike[str]] = None,
    auto_discover: bool = False,
) -> LeanreConfig:
    """Load a ``LeanreConfig`` from ``path`` or return ``LeanreConfig.empty()``.

    If ``path`` is given, it must exist (raises ``FileNotFoundError`` otherwise).
    If ``path`` is ``None`` and ``auto_discover=True``, searches upward for
    ``leanre.toml`` and falls back to ``LeanreConfig.empty()`` when absent.
    """
    if path is not None:
        return LeanreConfig.from_toml(path)
    if auto_discover:
        found = find_config(start_dir=start_dir)
        if found is not None:
            return LeanreConfig.from_toml(found)
    return LeanreConfig.empty()


def coerce_config(config: Optional[LeanreConfig | str | os.PathLike[str]]) -> LeanreConfig:
    """Accept a ``LeanreConfig``, path to ``leanre.toml``, or ``None``."""
    if config is None:
        return LeanreConfig.empty()
    if isinstance(config, LeanreConfig):
        return config
    return LeanreConfig.from_toml(config)


def _toml_quote(val: str) -> str:
    escaped = val.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\r", "\\r").replace("\t", "\\t")
    return f'"{escaped}"'


def _toml_list(items: Sequence[str], indent: str = "") -> str:
    if not items:
        return "[]"
    if len(items) <= 3 and all(len(x) < 32 for x in items):
        return "[" + ", ".join(_toml_quote(x) for x in items) + "]"
    lines = ["["]
    for item in items:
        lines.append(f"{indent}  {_toml_quote(item)},")
    lines.append(f"{indent}]")
    return "\n".join(lines)


def render_toml(cfg: LeanreConfig) -> str:
    """Serialize a ``LeanreConfig`` to clean, deterministic TOML (round-trips via ``tomllib``)."""
    out: List[str] = [
        "# Generated by `leanre init` (leanre.config)",
        f"schema_version = {int(cfg.schema_version)}",
        "",
        "[project]",
        f"name = {_toml_quote(cfg.project_name)}",
        f"root_module = {_toml_quote(cfg.root_module)}",
        f"src_dir = {_toml_quote(cfg.src_dir)}",
        f"source_roots = {_toml_list(cfg.source_roots)}",
    ]
    if cfg.lean_toolchain:
        out.append(f"lean_toolchain = {_toml_quote(cfg.lean_toolchain)}")
    if cfg.pinned_commit:
        out.append(f"pinned_commit = {_toml_quote(cfg.pinned_commit)}")
    if cfg.repo_url:
        out.append(f"repo_url = {_toml_quote(cfg.repo_url)}")
    if cfg.upstream_url_template:
        out.append(f"upstream_url_template = {_toml_quote(cfg.upstream_url_template)}")
    if cfg.lakefile:
        out.append(f"lakefile = {_toml_quote(cfg.lakefile)}")
    if cfg.dependencies:
        out.append(f"dependencies = {_toml_list(cfg.dependencies)}")

    out.append("")
    out.append("[roots]")
    out.append(f"headline = {_toml_list(cfg.headline_roots)}")
    if cfg.candidate_root_modules:
        out.append(f"candidate_modules = {_toml_list(cfg.candidate_root_modules)}")
    if cfg.statement_wrappers:
        out.append(f"statement_wrappers = {_toml_list(cfg.statement_wrappers)}")

    if cfg.root_groups:
        out.append("")
        out.append("[roots.groups]")
        for grp, names in cfg.root_groups.items():
            out.append(f"{grp} = {_toml_list(names)}")

    out.append("")
    out.append("[forensics]")
    out.append(f"rh_gates = {'true' if cfg.rh_gates else 'false'}")
    if cfg.timeout_modules:
        out.append(f"timeout_modules = {_toml_list(sorted(cfg.timeout_modules))}")

    for mod in sorted(cfg.slow_targets):
        info = cfg.slow_targets[mod]
        out.append("")
        out.append("[[forensics.slow_targets]]")
        out.append(f"module = {_toml_quote(mod)}")
        out.append(f"decl = {_toml_quote(str(info.get('decl', '')))}")
        out.append(f"full_decl = {_toml_quote(str(info.get('full_decl', info.get('decl', ''))))}")
        out.append(f"seconds = {float(info.get('seconds', 0.0))}")

    for spec in cfg.extra_regexes:
        out.append("")
        out.append("[[forensics.extra_regexes]]")
        out.append(f"tag = {_toml_quote(spec.tag)}")
        out.append(f"pattern = {_toml_quote(spec.pattern)}")
        out.append(f"severity = {_toml_quote(spec.severity)}")

    return "\n".join(out) + "\n"


def _parse_lakefile_toml(path: Path) -> Dict[str, Any]:
    with path.open("rb") as f:
        data = tomllib.load(f)
    libs: List[Dict[str, Any]] = []
    for lib in data.get("lean_lib", []) or []:
        if isinstance(lib, dict) and lib.get("name"):
            libs.append({
                "name": str(lib["name"]),
                "srcDir": str(lib["srcDir"]) if lib.get("srcDir") else "",
                "globs": [str(g) for g in (lib.get("globs") or [])],
                "roots": [str(r) for r in (lib.get("roots") or [])],
            })
    exes: List[Dict[str, Any]] = []
    for exe in data.get("lean_exe", []) or []:
        if isinstance(exe, dict) and exe.get("name"):
            exes.append({
                "name": str(exe["name"]),
                "root": str(exe.get("root", exe["name"])),
                "srcDir": str(exe["srcDir"]) if exe.get("srcDir") else "",
            })
    reqs: List[str] = []
    for req in data.get("require", []) or []:
        if isinstance(req, dict) and req.get("name"):
            reqs.append(str(req["name"]))
    default_targets = [str(t) for t in (data.get("defaultTargets") or [])]
    return {
        "name": str(data.get("name", "")),
        "srcDir": str(data.get("srcDir", "")),
        "defaultTargets": default_targets,
        "lean_libs": libs,
        "lean_exes": exes,
        "requires": reqs,
    }


def _parse_lakefile_lean(path: Path) -> Dict[str, Any]:
    text = path.read_text(encoding="utf-8", errors="replace")
    m_pkg = _RE_LAKE_PKG.search(text)
    m_src = _RE_LAKE_SRCDIR.search(text)
    libs = [{"name": nm, "srcDir": "", "globs": [], "roots": []} for nm in _RE_LAKE_LIB.findall(text)]
    exes = [{"name": nm, "root": nm, "srcDir": ""} for nm in _RE_LAKE_EXE.findall(text)]
    reqs = list(dict.fromkeys(_RE_LAKE_REQ.findall(text)))
    defaults = list(dict.fromkeys(_RE_LAKE_DEFAULT.findall(text)))
    return {
        "name": m_pkg.group(1) if m_pkg else "",
        "srcDir": m_src.group(1) if m_src else "",
        "defaultTargets": defaults,
        "lean_libs": libs,
        "lean_exes": exes,
        "requires": reqs,
    }


def parse_lakefile(repo_dir: str | os.PathLike[str]) -> Optional[Dict[str, Any]]:
    """Parse ``lakefile.toml`` or ``lakefile.lean`` in ``repo_dir`` if present."""
    root = Path(repo_dir)
    lake_toml = root / "lakefile.toml"
    lake_lean = root / "lakefile.lean"
    try:
        if lake_toml.is_file():
            info = _parse_lakefile_toml(lake_toml)
            info["lakefile"] = "lakefile.toml"
            return info
        if lake_lean.is_file():
            info = _parse_lakefile_lean(lake_lean)
            info["lakefile"] = "lakefile.lean"
            return info
    except (OSError, tomllib.TOMLDecodeError):
        return None
    return None


def _parse_lake_manifest(path: Path) -> List[str]:
    try:
        data = json.loads(path.read_text(encoding="utf-8", errors="replace"))
    except (OSError, json.JSONDecodeError):
        return []
    pkgs = data.get("packages", []) or []
    names: List[str] = []
    for pkg in pkgs:
        if isinstance(pkg, dict) and pkg.get("name") and not pkg.get("inherited", False):
            names.append(str(pkg["name"]))
    if not names:
        for pkg in pkgs:
            if isinstance(pkg, dict) and pkg.get("name"):
                names.append(str(pkg["name"]))
    return list(dict.fromkeys(names))


def _dir_has_lean_files(directory: Path) -> bool:
    if not directory.is_dir():
        return False
    for dirpath, dirnames, filenames in os.walk(directory):
        dirnames[:] = [d for d in dirnames if d not in _SKIP_DIRS]
        for fn in filenames:
            if fn.endswith(".lean"):
                return True
    return False


def _git_metadata(repo_dir: Path, src_dir_rel: str) -> Tuple[str, str]:
    """Read optional commit hash & GitHub blob URL template from git metadata."""
    commit = ""
    url_tpl = ""
    try:
        res = subprocess.run(
            ["git", "-C", str(repo_dir), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            timeout=5,
            check=False,
        )
        if res.returncode == 0:
            commit = res.stdout.strip()
    except OSError:
        return "", ""

    try:
        res_u = subprocess.run(
            ["git", "-C", str(repo_dir), "remote", "get-url", "origin"],
            capture_output=True,
            text=True,
            timeout=5,
            check=False,
        )
        if res_u.returncode == 0:
            remote = res_u.stdout.strip()
            m = _RE_GITHUB_REMOTE.match(remote)
            if m:
                owner, repo = m.group(1), m.group(2)
                prefix = f"{src_dir_rel.strip('/')}/" if src_dir_rel not in ("", ".") else ""
                url_tpl = f"https://github.com/{owner}/{repo}/blob/{{commit}}/{prefix}{{path}}#L{{line}}"
    except OSError:
        pass
    return commit, url_tpl


def _strip_comments_simple(text: str) -> str:
    """Strip Lean 4 `--` line comments and nested `/- ... -/` block comments."""
    if "--" not in text and "/-" not in text:
        return text
    out: List[str] = []
    i = 0
    n = len(text)
    in_str = False
    depth = 0
    while i < n:
        ch = text[i]
        if depth > 0:
            if ch == "/" and i + 1 < n and text[i + 1] == "-":
                depth += 1
                i += 2
            elif ch == "-" and i + 1 < n and text[i + 1] == "/":
                depth -= 1
                i += 2
            else:
                if ch == "\n":
                    out.append("\n")
                i += 1
        elif in_str:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
            elif ch == '"':
                in_str = False
                i += 1
            else:
                i += 1
        else:
            if ch == '"':
                in_str = True
                out.append(ch)
                i += 1
            elif ch == "/" and i + 1 < n and text[i + 1] == "-":
                depth = 1
                i += 2
            elif ch == "-" and i + 1 < n and text[i + 1] == "-":
                j = text.find("\n", i)
                if j == -1:
                    break
                out.append("\n")
                i = j + 1
            else:
                out.append(ch)
                i += 1
    return "".join(out)


def _pop_scope(scope_stack: List[Tuple[str, List[str]]], end_arg: Optional[str]) -> None:
    if not scope_stack:
        return
    if not end_arg:
        scope_stack.pop()
        return
    rem = end_arg.split(".")
    while rem and scope_stack:
        kind, parts = scope_stack[-1]
        if not parts:
            scope_stack.pop()
            continue
        if len(parts) >= len(rem) and parts[-len(rem) :] == rem:
            if len(parts) == len(rem):
                scope_stack.pop()
            else:
                scope_stack[-1] = (kind, parts[: -len(rem)])
            return
        if len(rem) > len(parts) and rem[-len(parts) :] == parts:
            rem = rem[: -len(parts)]
            scope_stack.pop()
            continue
        scope_stack.pop()
        return


def _extract_theorems_from_file(fpath: Path, limit: int = 16) -> Tuple[List[str], List[str]]:
    """Return ``(qualified_theorems, direct_imports)`` from a single ``.lean`` file.

    Tracks ``namespace``/``section``/``end`` blocks so declarations inside a
    namespace emit their qualified Lean kernel name (e.g. ``TinyDemo.main_theorem``).
    Prefers non-private theorems; falls back to private only if none are public.
    """
    if not fpath.is_file():
        return [], []
    try:
        raw = fpath.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return [], []
    clean = _strip_comments_simple(raw)

    scope_stack: List[Tuple[str, List[str]]] = []
    public_found: List[str] = []
    private_found: List[str] = []
    seen_pub: Set[str] = set()
    seen_priv: Set[str] = set()
    imports: List[str] = []

    for line in clean.splitlines():
        m_imp = _RE_IMPORT_LINE.match(line)
        if m_imp:
            imp = m_imp.group(1)
            if imp not in imports:
                imports.append(imp)
            continue
        if not line or line[0] in (" ", "\t"):
            continue
        m_ns = _RE_NS_OPEN.match(line)
        if m_ns:
            scope_stack.append(("ns", m_ns.group(1).split(".")))
            continue
        m_sec = _RE_SEC_OPEN.match(line)
        if m_sec:
            sec_parts = m_sec.group(1).split(".") if m_sec.group(1) else []
            scope_stack.append(("sec", sec_parts))
            continue
        m_end = _RE_NS_END.match(line)
        if m_end:
            _pop_scope(scope_stack, m_end.group(1))
            continue
        m_thm = _RE_TOP_THEOREM.match(line)
        if m_thm:
            mods = m_thm.group("mods") or ""
            raw_name = m_thm.group("name")
            if raw_name.startswith("_root_."):
                fqn = raw_name[len("_root_.") :]
            else:
                ns_parts: List[str] = []
                for kind, parts in scope_stack:
                    if kind == "ns":
                        ns_parts.extend(parts)
                if ns_parts:
                    fqn = ".".join(ns_parts) + "." + raw_name
                else:
                    fqn = raw_name
            is_priv = "private" in mods.split()
            if is_priv:
                if fqn not in seen_priv and len(private_found) < limit:
                    seen_priv.add(fqn)
                    private_found.append(fqn)
            else:
                if fqn not in seen_pub and len(public_found) < limit:
                    seen_pub.add(fqn)
                    public_found.append(fqn)

    return (public_found if public_found else private_found), imports


_HEADLINE_MODULE_HINTS = (
    "main",
    "theorem",
    "proof",
    "consequence",
    "result",
    "statement",
    "final",
    "basic",
)


def _extract_candidate_theorems(
    lean_files: Sequence[Path],
    limit: int = 16,
    *,
    scan_base: Optional[Path] = None,
    project_name: str = "",
) -> List[str]:
    """Scan qualified top-level theorem/lemma names from candidate root `.lean` files.

    When candidate root files are pure re-export hubs (containing only ``import``
    lines, as in Mathlib-style repos), gracefully inspects directly imported
    project modules (prioritizing headline-named modules like ``Main`` / ``Proof`` /
    ``Consequences`` / ``<ProjectName>``) to surface candidate theorem names.
    """
    found: List[str] = []
    seen: Set[str] = set()
    direct_imports: List[str] = []
    seen_imps: Set[str] = set()

    for fpath in lean_files:
        thms, imps = _extract_theorems_from_file(fpath, limit=limit)
        for nm in thms:
            if nm not in seen:
                seen.add(nm)
                found.append(nm)
                if len(found) >= limit:
                    return found
        for imp in imps:
            if imp not in seen_imps:
                seen_imps.add(imp)
                direct_imports.append(imp)

    if found or scan_base is None or not direct_imports:
        return found

    # Graceful fallback for re-export hubs: rank directly imported local modules
    proj_low = project_name.lower()
    local_cands: List[Tuple[int, int, str, Path]] = []
    for imp in direct_imports:
        rel_file = Path(*imp.split(".")).with_suffix(".lean")
        full = scan_base / rel_file
        if not full.is_file():
            continue
        # Skip Mathlib-extension helper folders during headline fallback
        segs = imp.split(".")
        if any(s in ("Mathlib", "ToMathlib", "ForMathlib", "FromMathlib") for s in segs):
            continue
        leaf = segs[-1].lower()
        prio = 2
        if proj_low and leaf == proj_low:
            prio = 0
        elif any(h in leaf for h in _HEADLINE_MODULE_HINTS):
            prio = 1
        local_cands.append((prio, len(segs), imp, full))

    local_cands.sort(key=lambda x: (x[0], x[1], x[2]))
    for _prio, _depth, _imp, fpath in local_cands[:32]:
        thms, _ = _extract_theorems_from_file(fpath, limit=max(4, limit - len(found)))
        for nm in thms:
            if nm not in seen:
                seen.add(nm)
                found.append(nm)
                if len(found) >= limit:
                    return found
    return found


def discover_project(repo_dir: str | os.PathLike[str]) -> Tuple[LeanreConfig, Dict[str, Any]]:
    """Auto-discover Lake metadata, source roots, and candidate roots for a Lean 4 repo."""
    root = Path(repo_dir).resolve()
    if not root.is_dir():
        raise FileNotFoundError(f"Repository directory not found: {repo_dir}")

    lake_info: Dict[str, Any] = {
        "name": "",
        "srcDir": "",
        "defaultTargets": [],
        "lean_libs": [],
        "lean_exes": [],
        "requires": [],
    }
    lakefile_rel = ""
    lake_toml = root / "lakefile.toml"
    lake_lean = root / "lakefile.lean"
    if lake_toml.is_file():
        lakefile_rel = "lakefile.toml"
        lake_info = _parse_lakefile_toml(lake_toml)
    elif lake_lean.is_file():
        lakefile_rel = "lakefile.lean"
        lake_info = _parse_lakefile_lean(lake_lean)

    manifest_deps: List[str] = []
    manifest_path = root / "lake-manifest.json"
    if manifest_path.is_file():
        manifest_deps = _parse_lake_manifest(manifest_path)

    deps = list(dict.fromkeys([*lake_info["requires"], *manifest_deps]))

    toolchain = ""
    tc_path = root / "lean-toolchain"
    if tc_path.is_file():
        toolchain = tc_path.read_text(encoding="utf-8", errors="replace").strip().splitlines()[0].strip()

    project_name = lake_info["name"] or root.name

    # Discover source root layout (`src/` vs repo root with `<Lib>/` folders)
    declared_src_dir = lake_info["srcDir"].strip("/") if lake_info["srcDir"] else ""
    top_lean_files = sorted(p for p in root.iterdir() if p.is_file() and p.suffix == ".lean")
    lib_names = [lib["name"] for lib in lake_info["lean_libs"]]
    exe_roots = [exe["root"] for exe in lake_info["lean_exes"]]

    src_dir_rel = "."
    source_roots: List[str] = []

    if declared_src_dir and (root / declared_src_dir).is_dir():
        src_dir_rel = declared_src_dir
        source_roots.append(declared_src_dir)
    elif (root / "src").is_dir() and _dir_has_lean_files(root / "src") and not top_lean_files:
        src_dir_rel = "src"
        source_roots.append("src")
    else:
        src_dir_rel = "."
        # Prefer directories matching declared lean_lib names first
        for lib in lake_info["lean_libs"]:
            sub = lib["srcDir"].strip("/") or lib["name"]
            if (root / sub).is_dir() and _dir_has_lean_files(root / sub):
                if sub not in source_roots:
                    source_roots.append(sub)
        # Also include any other top-level directories with `.lean` files matching a root `.lean` module
        if not source_roots:
            for entry in sorted(root.iterdir()):
                if entry.is_dir() and entry.name not in _SKIP_DIRS and not entry.name.startswith("."):
                    if _dir_has_lean_files(entry):
                        source_roots.append(entry.name)
        if not source_roots and top_lean_files:
            source_roots.append(".")

    scan_base = root if src_dir_rel == "." else (root / src_dir_rel)

    # Collect candidate root modules (ordered by preference)
    candidate_modules: List[str] = []
    seen_mods: Set[str] = set()

    def _add_mod(mod_name: str) -> None:
        clean = mod_name.strip().removesuffix(".*")
        if not clean or clean in seen_mods:
            return
        rel_file = Path(*clean.split(".")).with_suffix(".lean")
        if (scan_base / rel_file).is_file():
            seen_mods.add(clean)
            candidate_modules.append(clean)

    for t in lake_info["defaultTargets"]:
        _add_mod(t)
    for lib in lake_info["lean_libs"]:
        _add_mod(lib["name"])
        for g in lib.get("globs", []):
            _add_mod(g)
        for r in lib.get("roots", []):
            _add_mod(r)
    for er in exe_roots:
        _add_mod(er)
    for common in ("Main", project_name, "Solution", "Challenge"):
        _add_mod(common)

    # Also check any other top-level `.lean` files in scan_base sorted by import count descending
    extra_top: List[Tuple[int, str]] = []
    if scan_base.is_dir():
        for p in sorted(scan_base.iterdir()):
            if p.is_file() and p.suffix == ".lean":
                mod = p.stem
                if mod not in seen_mods:
                    try:
                        imp_cnt = sum(
                            1 for ln in p.read_text(encoding="utf-8", errors="replace").splitlines()
                            if _RE_IMPORT_LINE.match(ln)
                        )
                    except OSError:
                        imp_cnt = 0
                    extra_top.append((imp_cnt, mod))
    for _cnt, mod in sorted(extra_top, key=lambda x: (-x[0], x[1])):
        _add_mod(mod)

    root_module = candidate_modules[0] if candidate_modules else "Main"

    # Extract candidate headline theorem declarations from candidate root module files
    cand_files = [
        scan_base / Path(*m.split(".")).with_suffix(".lean")
        for m in candidate_modules[:6]
    ]
    headline_roots = _extract_candidate_theorems(
        cand_files,
        limit=16,
        scan_base=scan_base,
        project_name=project_name,
    )

    pinned_commit, upstream_tpl = _git_metadata(root, src_dir_rel)

    cfg = LeanreConfig(
        schema_version=1,
        project_name=project_name,
        root_module=root_module,
        src_dir=src_dir_rel,
        source_roots=source_roots,
        lean_toolchain=toolchain,
        pinned_commit=pinned_commit,
        upstream_url_template=upstream_tpl,
        lakefile=lakefile_rel,
        dependencies=deps,
        headline_roots=headline_roots,
        candidate_root_modules=candidate_modules,
        rh_gates=False,
    )
    meta = {
        "lakefile": lakefile_rel or None,
        "has_manifest": manifest_path.is_file(),
        "default_targets": lake_info["defaultTargets"],
        "lean_libs": lib_names,
        "lean_exes": exe_roots,
        "source_roots": source_roots,
        "src_dir": src_dir_rel,
        "root_module": root_module,
        "candidate_root_modules": candidate_modules,
        "headline_roots": headline_roots,
        "dependencies": deps,
        "lean_toolchain": toolchain,
    }
    return cfg, meta


def cmd_init(args: argparse.Namespace) -> int:
    """Discover Lean 4 / Lake repository layout and write a clean ``leanre.toml``."""
    repo_dir = getattr(args, "repo_dir", None) or getattr(args, "path", None) or "."
    out_arg = getattr(args, "out", None)
    force = bool(getattr(args, "force", False))
    dry_run = bool(getattr(args, "dry_run", False))
    as_json = bool(getattr(args, "json", False))

    cfg, meta = discover_project(repo_dir)
    toml_text = render_toml(cfg)
    # Sanity round-trip check before writing
    tomllib.loads(toml_text)

    out_path = Path(out_arg) if out_arg else (Path(repo_dir).resolve() / DEFAULT_CONFIG_FILENAME)

    if not dry_run:
        if out_path.exists() and not force:
            print(
                f"error: {out_path} already exists (pass --force to overwrite)",
                file=sys.stderr,
            )
            return 1
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(toml_text, encoding="utf-8")

    if as_json:
        payload = {
            "out_path": str(out_path),
            "dry_run": dry_run,
            "discovered": meta,
        }
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    elif dry_run:
        print(toml_text, end="")
    else:
        print(
            f"[init] wrote {out_path} (project={cfg.project_name!r}, "
            f"src_dir={cfg.src_dir!r}, root_module={cfg.root_module!r}, "
            f"source_roots={cfg.source_roots}, candidate_theorems={len(cfg.headline_roots)})"
        )
    return 0


def register_cli(subparsers: argparse._SubParsersAction, dest: str = "config_func") -> None:
    p = subparsers.add_parser(
        "init",
        help="Auto-discover a Lean 4 / Lake repository and generate leanre.toml",
    )
    p.add_argument("repo_dir", nargs="?", default=".", help="Path to Lean 4 repository (default: .)")
    p.add_argument("--out", default=None, help="Output path for leanre.toml (default: <repo_dir>/leanre.toml)")
    p.add_argument("--force", action="store_true", help="Overwrite existing leanre.toml")
    p.add_argument("--dry-run", action="store_true", help="Print generated TOML without writing")
    p.add_argument("--json", action="store_true", help="Print discovery summary as JSON")
    p.set_defaults(**{dest: cmd_init})


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        prog="leanre-config",
        description="Inspect or initialize leanre.toml project profiles",
    )
    sub = ap.add_subparsers(dest="cmd", required=True)
    register_cli(sub, dest="func")

    p_show = sub.add_parser("show", help="Load and print a leanre.toml profile as JSON")
    p_show.add_argument("config_path", nargs="?", default=None, help="Path to leanre.toml")
    p_show.set_defaults(
        func=lambda a: (
            print(
                json.dumps(
                    dataclasses.asdict(load_config(a.config_path, auto_discover=a.config_path is None)),
                    indent=2,
                    default=sorted,
                    ensure_ascii=False,
                )
            )
            or 0
        )
    )

    args = ap.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    sys.exit(main())
