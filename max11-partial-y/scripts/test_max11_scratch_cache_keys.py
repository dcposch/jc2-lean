#!/usr/bin/env python3
"""Regression tests for content-stable scratch `.olean` cache keys."""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path


HELPER = Path(__file__).with_name("max11_scratch_cache_keys.py")


class ScratchCacheKeyTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.repo = Path(self.temp.name)
        subprocess.run(["git", "init", "-q", str(self.repo)], check=True)
        subprocess.run(
            ["git", "-C", str(self.repo), "config", "user.email", "test@example.invalid"],
            check=True,
        )
        subprocess.run(
            ["git", "-C", str(self.repo), "config", "user.name", "Cache Test"],
            check=True,
        )
        (self.repo / "lean-toolchain").write_text("leanprover/lean4:test\n")
        (self.repo / "lake-manifest.json").write_text("{}\n")
        (self.repo / "Base.lean").write_text("def base : Nat := 1\n")
        (self.repo / "LeafScratch.lean").write_text(
            "import Base\n\ndef leaf : Nat := base\n"
        )
        (self.repo / "ChildScratch.lean").write_text(
            "import LeafScratch\n\ndef child : Nat := leaf\n"
        )
        subprocess.run(
            [
                "git",
                "-C",
                str(self.repo),
                "add",
                "lean-toolchain",
                "lake-manifest.json",
                "Base.lean",
            ],
            check=True,
        )
        subprocess.run(
            ["git", "-C", str(self.repo), "commit", "-qm", "base"], check=True
        )

    def tearDown(self) -> None:
        self.temp.cleanup()

    def keys(self, source: str) -> tuple[str, str]:
        output = subprocess.run(
            [
                "python3",
                str(HELPER),
                "--project-dir",
                str(self.repo),
                source,
            ],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout.strip()
        tag, returned_source, _source_hash, key, legacy_key = output.split("\t")
        self.assertEqual(tag, "MODULE")
        self.assertEqual(returned_source, source)
        return key, legacy_key

    def test_committing_byte_identical_scratch_source_keeps_key(self) -> None:
        leaf_before = self.keys("LeafScratch.lean")
        child_before = self.keys("ChildScratch.lean")
        subprocess.run(
            ["git", "-C", str(self.repo), "add", "LeafScratch.lean"], check=True
        )
        subprocess.run(
            ["git", "-C", str(self.repo), "commit", "-qm", "track leaf"], check=True
        )
        leaf_after = self.keys("LeafScratch.lean")
        child_after = self.keys("ChildScratch.lean")
        self.assertEqual(leaf_before[0], leaf_after[0])
        self.assertEqual(child_before[0], child_after[0])
        self.assertNotEqual(leaf_before[1], leaf_after[1])
        self.assertNotEqual(child_before[1], child_after[1])

    def test_source_and_tracked_dependency_changes_still_invalidate(self) -> None:
        initial = self.keys("ChildScratch.lean")[0]
        (self.repo / "LeafScratch.lean").write_text(
            "import Base\n\ndef leaf : Nat := base + 1\n"
        )
        source_changed = self.keys("ChildScratch.lean")[0]
        self.assertNotEqual(initial, source_changed)
        (self.repo / "Base.lean").write_text("def base : Nat := 2\n")
        dependency_changed = self.keys("ChildScratch.lean")[0]
        self.assertNotEqual(source_changed, dependency_changed)


if __name__ == "__main__":
    unittest.main()
