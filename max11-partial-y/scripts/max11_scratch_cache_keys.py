#!/usr/bin/env python3
"""Compute exact scratch `.olean` cache keys in one dependency-graph pass.

`box_lean_verify.sh` historically recomputed every transitive source and
tracked-environment closure with recursive Bash walks.  That is harmless for a
short lane but becomes quadratic (and subprocess-heavy) for 100+ theorem
towers.  This helper preserves the byte-for-byte cache-key format while
memoizing parsed imports and hashes inside one process.

Scratch files are keyed by content, not by whether Git happens to track them.
In particular, a committed `*Scratch.lean` remains in the recursive scratch
closure and is excluded from the tracked-environment component.  This avoids
invalidating a multi-hour `.olean` merely because its byte-identical source
was committed after verification.

Output is one tab-separated record per requested source, in argument order:

    MODULE  source.lean  source_sha256  closure_cache_key  legacy_cache_key

The final field is the pre-fix key that counted tracked scratch sources twice.
The verifier uses it only to atomically promote an already-audited historical
artifact into the content-stable namespace.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
from functools import lru_cache
from pathlib import Path


IMPORT_RE = re.compile(
    r"^import[ \t]+([A-Za-z0-9_.]+)[ \t]*$", re.MULTILINE
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project-dir", required=True, type=Path)
    parser.add_argument("sources", nargs="+")
    args = parser.parse_args()
    project_dir = args.project_dir.resolve()

    tracked_output = subprocess.run(
        ["git", "-C", str(project_dir), "ls-files", "-z"],
        check=True,
        stdout=subprocess.PIPE,
    ).stdout
    tracked = {
        name.decode("utf-8")
        for name in tracked_output.split(b"\0")
        if name
    }

    @lru_cache(maxsize=None)
    def file_sha(source: str) -> str:
        return sha256_bytes((project_dir / source).read_bytes())

    @lru_cache(maxsize=None)
    def local_imports(source: str) -> tuple[str, ...]:
        text = (project_dir / source).read_text(encoding="utf-8")
        dependencies: list[str] = []
        for module in IMPORT_RE.findall(text):
            dependency = module.replace(".", "/") + ".lean"
            if (project_dir / dependency).is_file():
                dependencies.append(dependency)
        return tuple(dependencies)

    @lru_cache(maxsize=None)
    def scratch_closure(source: str) -> tuple[str, ...]:
        seen: set[str] = set()
        ordered: list[str] = []

        def visit(current: str) -> None:
            if current in seen:
                return
            seen.add(current)
            for dependency in local_imports(current):
                if dependency.endswith("Scratch.lean") or dependency not in tracked:
                    visit(dependency)
            ordered.append(current)

        visit(source)
        return tuple(ordered)

    def tracked_environment(
        source: str, excluded: frozenset[str] = frozenset()
    ) -> tuple[str, ...]:
        seen: set[str] = set()
        ordered: list[str] = []

        def visit(current: str) -> None:
            if current in seen:
                return
            seen.add(current)
            if current in tracked and current not in excluded:
                ordered.append(current)
            for dependency in local_imports(current):
                visit(dependency)

        visit(source)
        return tuple(ordered)

    def tracked_environment_hash(
        source: str, excluded: frozenset[str] = frozenset()
    ) -> str:
        payload = bytearray()
        for fixed in ("lean-toolchain", "lake-manifest.json"):
            if (project_dir / fixed).is_file():
                payload.extend(fixed.encode())
                payload.append(0)
                payload.extend(f"{file_sha(fixed)}  {fixed}\n".encode())
        for dependency in tracked_environment(source, excluded):
            payload.extend(dependency.encode())
            payload.append(0)
            payload.extend(
                f"{file_sha(dependency)}  {dependency}\n".encode()
            )
        return sha256_bytes(bytes(payload))

    def closure_cache_key(source: str, *, legacy: bool) -> str:
        closure = scratch_closure(source)
        excluded = frozenset() if legacy else frozenset(closure)
        payload = bytearray(
            f"tracked_environment={tracked_environment_hash(source, excluded)}\n".encode()
        )
        for dependency in closure:
            payload.extend(
                f"file={dependency} sha256={file_sha(dependency)}\n".encode()
            )
        return sha256_bytes(bytes(payload))

    for source in args.sources:
        source_path = project_dir / source
        if not source_path.is_file():
            parser.error(f"missing source: {source}")
        print(
            "\t".join(
                (
                    "MODULE",
                    source,
                    file_sha(source),
                    closure_cache_key(source, legacy=False),
                    closure_cache_key(source, legacy=True),
                )
            )
        )


if __name__ == "__main__":
    main()
