#!/usr/bin/env python3
from __future__ import annotations

import re
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_doc_counts import apply_fixes, check_file


class CheckDocCountsMultiMatchTests(unittest.TestCase):
    def test_check_file_reports_stale_non_first_occurrence(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "README.md"
            path.write_text(
                "Theorems: 431 across categories.\n"
                "Theorems: 401 across categories.\n",
                encoding="utf-8",
            )
            checks = [
                ("theorem count", re.compile(r"Theorems: (\d+) across"), "431"),
            ]
            errors = check_file(path, checks)
            self.assertEqual(
                errors,
                [
                    "README.md: theorem count occurrence 2 says '401' but expected '431'",
                ],
            )

    def test_apply_fixes_updates_all_stale_occurrences(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "README.md"
            path.write_text(
                "Foundry tests: 403/403 tests pass.\n"
                "Foundry tests: 375/403 tests pass.\n"
                "Foundry tests: 375/403 tests pass.\n",
                encoding="utf-8",
            )
            checks = [
                (
                    "test count",
                    re.compile(r"Foundry tests: (\d+)/403 tests pass"),
                    "403",
                ),
            ]
            changed = apply_fixes(path, checks)
            self.assertTrue(changed)
            self.assertEqual(
                path.read_text(encoding="utf-8"),
                "Foundry tests: 403/403 tests pass.\n"
                "Foundry tests: 403/403 tests pass.\n"
                "Foundry tests: 403/403 tests pass.\n",
            )

    def test_contract_name_regex_does_not_overlap(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "README.md"
            path.write_text(
                "| `Counter.sol` | `Verity/Examples/Counter.lean` | 28 theorems |\n"
                "| `SafeCounter.sol` | `Verity/Examples/SafeCounter.lean` | 25 theorems |\n"
                "| `OwnedCounter.sol` | `Verity/Examples/OwnedCounter.lean` | 48 theorems |\n",
                encoding="utf-8",
            )
            checks = [
                (
                    "counter",
                    re.compile(r"`Verity/Examples/Counter\.lean`\s*\|\s*(\d+) theorems"),
                    "28",
                ),
                (
                    "safe counter",
                    re.compile(
                        r"`Verity/Examples/SafeCounter\.lean`\s*\|\s*(\d+) theorems"
                    ),
                    "25",
                ),
                (
                    "owned counter",
                    re.compile(
                        r"`Verity/Examples/OwnedCounter\.lean`\s*\|\s*(\d+) theorems"
                    ),
                    "48",
                ),
            ]
            self.assertEqual(check_file(path, checks), [])

    def test_check_file_reports_stale_ratio_denominator(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "README.md"
            path.write_text(
                "Property tests (197 functions, covering 250/401 theorems)\n",
                encoding="utf-8",
            )
            checks = [
                (
                    "theorem total in tree coverage",
                    re.compile(r"covering \d+/(\d+) theorems"),
                    "431",
                ),
            ]
            errors = check_file(path, checks)
            self.assertEqual(
                errors,
                [
                    "README.md: theorem total in tree coverage occurrence 1 says '401' but expected '431'",
                ],
            )


if __name__ == "__main__":
    unittest.main()
