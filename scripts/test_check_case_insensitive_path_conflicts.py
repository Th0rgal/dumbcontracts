#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import unittest
from contextlib import redirect_stderr
from pathlib import Path
from unittest.mock import patch

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_case_insensitive_path_conflicts as checker


class CaseInsensitivePathConflictTests(unittest.TestCase):
    def test_detects_top_level_conflict(self) -> None:
        paths = ["Compiler/Main.lean", "compiler/yul/Foo.yul"]
        conflicts = checker._find_conflicts(paths)
        self.assertIn(["Compiler", "compiler"], conflicts)

    def test_detects_nested_conflict(self) -> None:
        paths = ["Compiler/Proofs/A.lean", "compiler/proofs/B.lean"]
        conflicts = checker._find_conflicts(paths)
        self.assertIn(["Compiler", "compiler"], conflicts)
        self.assertIn(["Compiler/Proofs", "compiler/proofs"], conflicts)

    def test_main_returns_zero_without_conflicts(self) -> None:
        with patch.object(checker, "_git_tracked_paths", return_value=["Compiler/Main.lean", "scripts/x.py"]):
            self.assertEqual(checker.main(), 0)

    def test_main_returns_one_with_conflicts_and_reports_details(self) -> None:
        with patch.object(checker, "_git_tracked_paths", return_value=["Compiler/Main.lean", "compiler/yul/Foo.yul"]):
            stderr = io.StringIO()
            with redirect_stderr(stderr):
                rc = checker.main()
        self.assertEqual(rc, 1)
        out = stderr.getvalue()
        self.assertIn("case-insensitive path conflicts", out)
        self.assertIn("Compiler  <->  compiler", out)


if __name__ == "__main__":
    unittest.main()
