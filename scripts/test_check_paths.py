#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_paths as checker


class CheckPathsTests(unittest.TestCase):
    def test_detects_top_level_case_conflict(self) -> None:
        paths = ["Compiler/Main.lean", "compiler/yul/Foo.yul"]
        conflicts = checker._find_case_conflicts(paths)
        self.assertIn(["Compiler", "compiler"], conflicts)

    def test_detects_nested_case_conflict(self) -> None:
        paths = ["Compiler/Proofs/A.lean", "compiler/proofs/B.lean"]
        conflicts = checker._find_case_conflicts(paths)
        self.assertIn(["Compiler", "compiler"], conflicts)
        self.assertIn(["Compiler/Proofs", "compiler/proofs"], conflicts)

    def test_collects_semantic_bridge_headers(self) -> None:
        headers = checker._collect_semantic_bridge_headers(
            [
                "theorem counter_semantic_bridge",
                "    (state : ContractState)",
                "    (sender : Address)",
                "    : True := by",
            ]
        )
        self.assertEqual(headers[0][0], "counter_semantic_bridge")
        self.assertEqual(headers[0][1], 1)

    def test_finds_missing_state_quantification(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tempdir:
            target = Path(tempdir) / "SemanticBridge.lean"
            target.write_text(
                """
theorem counter_semantic_bridge
    (sender : Address)
    : True := by
  trivial
""".strip()
                + "\n",
                encoding="utf-8",
            )
            issues, theorem_count = checker._find_layer2_universality_issues(target)
        self.assertEqual(theorem_count, 1)
        self.assertTrue(any("missing `(state : ContractState)`" in issue for issue in issues))

    def test_finds_legacy_antipattern(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tempdir:
            target = Path(tempdir) / "SemanticBridge.lean"
            target.write_text(
                """
theorem counter_semantic_bridge
    (state : ContractState)
    (sender : Address)
    : True := by
  let initialStorage := SpecStorage.empty
  trivial
""".strip()
                + "\n",
                encoding="utf-8",
            )
            issues, _ = checker._find_layer2_universality_issues(target)
        self.assertTrue(any("SpecStorage.empty" in issue for issue in issues))
        self.assertTrue(any("let initialStorage :=" in issue for issue in issues))

    def test_ignores_antipattern_in_comments(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tempdir:
            target = Path(tempdir) / "SemanticBridge.lean"
            target.write_text(
                """
/-
SpecStorage.empty
let initialStorage :=
-/
theorem counter_semantic_bridge
    (state : ContractState)
    (sender : Address)
    : True := by
  trivial
""".strip()
                + "\n",
                encoding="utf-8",
            )
            issues, theorem_count = checker._find_layer2_universality_issues(target)
        self.assertEqual(theorem_count, 1)
        self.assertEqual(issues, [])

    def test_check_paths_passes_when_both_checks_are_clean(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tempdir:
            target = Path(tempdir) / "SemanticBridge.lean"
            target.write_text(
                """
theorem counter_semantic_bridge
    (state : ContractState)
    (sender : Address)
    : True := by
  trivial
""".strip()
                + "\n",
                encoding="utf-8",
            )
            stdout = io.StringIO()
            with redirect_stdout(stdout):
                rc = checker.check_paths(
                    tracked_paths=["Compiler/Main.lean", "scripts/check_paths.py"],
                    semantic_bridge=target,
                )
        self.assertEqual(rc, 0)
        self.assertIn("path checks passed", stdout.getvalue())

    def test_check_paths_reports_case_conflicts_and_layer2_failures(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tempdir:
            target = Path(tempdir) / "SemanticBridge.lean"
            target.write_text(
                """
theorem counter_semantic_bridge
    (state : ContractState)
    : True := by
  trivial
""".strip()
                + "\n",
                encoding="utf-8",
            )
            stderr = io.StringIO()
            with redirect_stderr(stderr):
                rc = checker.check_paths(
                    tracked_paths=["Compiler/Main.lean", "compiler/yul/Foo.yul"],
                    semantic_bridge=target,
                )
        self.assertEqual(rc, 1)
        out = stderr.getvalue()
        self.assertIn("path validation failed", out)
        self.assertIn("Compiler  <->  compiler", out)
        self.assertIn("missing `(sender : Address)`", out)

    def test_main_uses_git_paths_by_default(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tempdir:
            target = Path(tempdir) / "SemanticBridge.lean"
            target.write_text(
                """
theorem counter_semantic_bridge
    (state : ContractState)
    (sender : Address)
    : True := by
  trivial
""".strip()
                + "\n",
                encoding="utf-8",
            )
            with patch.object(checker, "TARGET", target):
                with patch.object(checker, "_git_tracked_paths", return_value=["Compiler/Main.lean"]):
                    self.assertEqual(checker.main(), 0)


if __name__ == "__main__":
    unittest.main()
