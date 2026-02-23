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

import check_doc_counts
import property_utils
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

    def test_get_axiom_and_sorry_counts_ignore_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Verity").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "Commented.lean").write_text(
                "\n".join(
                    [
                        "-- axiom fakeAxiom",
                        "/-",
                        "axiom fakeInBlock",
                        "sorry",
                        "-/",
                        "def quoted := \"axiom fakeInString\"",
                        "def quoted2 := \"sorry\"",
                        "axiom realAxiom : True",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            (root / "Verity" / "Proof.lean").write_text(
                "\n".join(
                    [
                        "-- sorry",
                        "theorem realSorry : True := by",
                        "  sorry",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            old_root = check_doc_counts.ROOT
            try:
                check_doc_counts.ROOT = root
                self.assertEqual(check_doc_counts.get_axiom_count(), 1)
                self.assertEqual(check_doc_counts.get_sorry_count(), 1)
            finally:
                check_doc_counts.ROOT = old_root

    def test_get_manifest_counts_rejects_duplicate_json_keys(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            manifest = Path(tmpdir) / "property_manifest.json"
            manifest.write_text(
                '{\n  "Counter": ["ok"],\n  "Counter": ["dup"]\n}\n',
                encoding="utf-8",
            )
            old_manifest = property_utils.MANIFEST
            try:
                property_utils.MANIFEST = manifest
                with self.assertRaises(SystemExit) as ctx:
                    check_doc_counts.get_manifest_counts()
                self.assertIn("duplicate object key", str(ctx.exception))
            finally:
                property_utils.MANIFEST = old_manifest


if __name__ == "__main__":
    unittest.main()
