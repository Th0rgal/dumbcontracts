#!/usr/bin/env python3
from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import check_contract_structure


class CheckContractStructureDifferentialTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tempdir.name)
        self.old_root = check_contract_structure.ROOT
        check_contract_structure.ROOT = self.root

        (self.root / "test").mkdir(parents=True, exist_ok=True)

    def tearDown(self) -> None:
        check_contract_structure.ROOT = self.old_root
        self.tempdir.cleanup()

    def test_missing_non_excluded_differential_is_reported(self) -> None:
        issues = check_contract_structure.check_differential_tests(["Counter"])
        self.assertEqual(issues, ["Counter: missing test/DifferentialCounter.t.sol"])

    def test_excluded_contract_missing_differential_is_not_reported(self) -> None:
        issues = check_contract_structure.check_differential_tests(["ReentrancyExample", "CryptoHash"])
        self.assertEqual(issues, [])

    def test_existing_differential_file_clears_issue(self) -> None:
        path = self.root / "test" / "DifferentialCounter.t.sol"
        path.write_text("// placeholder", encoding="utf-8")
        issues = check_contract_structure.check_differential_tests(["Counter"])
        self.assertEqual(issues, [])


if __name__ == "__main__":
    unittest.main()
