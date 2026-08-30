#!/usr/bin/env python3
"""Reject global declaration collisions in a local Lean import closure.

This is the indexed equivalent of the original Bash/AWK preflight. Deep
Max-11 routes contain hundreds of scratch modules; reading the graph once and
querying the Git index once avoids an O(n^2) shell membership scan and one Git
process per module while preserving the fail-closed output contract.
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path


IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$")
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.]+)\s*$")
END_RE = re.compile(r"^\s*end\s+([A-Za-z0-9_.]+)\s*$")
QUALIFIER_RE = re.compile(r"^(?:noncomputable|protected)\s+")
DECL_RE = re.compile(
    r"^(?:theorem|lemma|def|abbrev|axiom|opaque|structure|class|inductive)"
    r"\s+(\S+)"
)
TARGET_RE = re.compile(r"^[A-Za-z0-9_.-]+[.]lean$")


def usage() -> None:
    print("usage: max11_import_collision_lint.sh FILE.lean", file=sys.stderr)
    raise SystemExit(2)


def strip_comments(line: str, block_depth: int) -> tuple[str, int]:
    """Match the former AWK scanner, including nested Lean block comments."""
    output: list[str] = []
    index = 0
    while index < len(line):
        pair = line[index : index + 2]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                index += 2
            elif pair == "-/":
                block_depth -= 1
                index += 2
            else:
                index += 1
            continue
        if pair == "/-":
            block_depth += 1
            index += 2
        elif pair == "--":
            break
        else:
            output.append(line[index])
            index += 1
    return "".join(output), block_depth


def local_imports(project_dir: Path, source: str) -> list[str]:
    dependencies: list[str] = []
    with (project_dir / source).open(encoding="utf-8") as stream:
        for line in stream:
            match = IMPORT_RE.fullmatch(line.rstrip("\n"))
            if not match:
                continue
            dependency = match.group(1).replace(".", "/") + ".lean"
            if (project_dir / dependency).is_file():
                dependencies.append(dependency)
    return dependencies


def import_closure(project_dir: Path, target: str) -> list[str]:
    closure: list[str] = []
    seen: set[str] = set()
    pending = [target]
    while pending:
        source = pending.pop()
        if source in seen:
            continue
        seen.add(source)
        closure.append(source)
        pending.extend(local_imports(project_dir, source))
    return closure


def tracked_sources(project_dir: Path) -> set[str]:
    result = subprocess.run(
        ["git", "-C", str(project_dir), "ls-files", "-z"],
        check=True,
        stdout=subprocess.PIPE,
    )
    return {entry.decode("utf-8") for entry in result.stdout.split(b"\0") if entry}


def declarations(source_path: Path) -> list[tuple[str, int]]:
    found: list[tuple[str, int]] = []
    namespace_name = ""
    block_depth = 0
    with source_path.open(encoding="utf-8") as stream:
        for line_number, raw_line in enumerate(stream, 1):
            line, block_depth = strip_comments(raw_line, block_depth)
            match = NAMESPACE_RE.fullmatch(line)
            if match:
                name = match.group(1)
                namespace_name = (
                    name if not namespace_name else f"{namespace_name}.{name}"
                )
                continue
            match = END_RE.fullmatch(line)
            if match:
                name = match.group(1)
                if namespace_name == name:
                    namespace_name = ""
                elif namespace_name.endswith("." + name):
                    namespace_name = namespace_name[: -(len(name) + 1)]
                continue

            text = line.lstrip()
            if text.startswith("private "):
                continue
            while True:
                stripped = QUALIFIER_RE.sub("", text, count=1)
                if stripped == text:
                    break
                text = stripped
            match = DECL_RE.match(text)
            if not match:
                continue
            name = re.split(r"[({:]", match.group(1), maxsplit=1)[0]
            if not name:
                continue
            full_name = (
                f"{namespace_name}.{name}"
                if namespace_name and "." not in name
                else name
            )
            found.append((full_name, line_number))
    return found


def main() -> int:
    if len(sys.argv) != 2:
        usage()
    target = sys.argv[1]
    project_dir = Path(__file__).resolve().parent.parent
    if (
        not TARGET_RE.fullmatch(target)
        or Path(target).name != target
        or not (project_dir / target).is_file()
    ):
        usage()

    closure = import_closure(project_dir, target)
    tracked = tracked_sources(project_dir)
    by_name: dict[str, list[tuple[str, int, str]]] = defaultdict(list)
    for source in closure:
        origin = "tracked" if source in tracked else "scratch"
        for name, line_number in declarations(project_dir / source):
            by_name[name].append((source, line_number, origin))

    collision = False
    for name in sorted(by_name):
        locations = by_name[name]
        if len(locations) <= 1 or not any(item[2] == "scratch" for item in locations):
            continue
        collision = True
        rendered = ",".join(f"{source}:{line}" for source, line, _ in locations)
        print(
            f"PREFLIGHT_ERROR file={target} kind=import_declaration_collision "
            f"declaration={name} locations={rendered}",
            file=sys.stderr,
        )
    if collision:
        return 1

    print(f"IMPORT_COLLISION_LINT_OK file={target} closure_files={len(closure)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
