#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stderr
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_axiom_locations


class CheckAxiomLocationsTests(unittest.TestCase):
    def test_parse_axiom_entries(self) -> None:
        text = (
            "### 1. `a1`\n\n"
            "**Location**: `Compiler/Foo.lean:12`\n\n"
            "### 2. `a2` (private)\n\n"
            "**Location**: `Verity/Bar.lean:34`\n"
        )
        self.assertEqual(
            check_axiom_locations.parse_axiom_entries(text),
            [("a1", "Compiler/Foo.lean", 12), ("a2", "Verity/Bar.lean", 34)],
        )

    def test_parse_active_axiom_count(self) -> None:
        self.assertEqual(
            check_axiom_locations.parse_active_axiom_count("- Active axioms: 3\n"),
            3,
        )
        self.assertIsNone(check_axiom_locations.parse_active_axiom_count("no summary line"))

    def test_discover_repo_axioms_ignores_comments_and_strings(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Verity").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "A.lean").write_text(
                "\n".join(
                    [
                        "-- axiom commented_out : True",
                        "/- axiom in_block_comment : True -/",
                        "def s := \"axiom in_string\"",
                        "axiom real_axiom : True",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )

            old_root = check_axiom_locations.ROOT
            try:
                check_axiom_locations.ROOT = root
                discovered = check_axiom_locations.discover_repo_axioms()
            finally:
                check_axiom_locations.ROOT = old_root

        self.assertEqual(discovered, {"real_axiom": ("Compiler/A.lean", 4)})

    def test_main_reports_missing_registry_entries_and_count_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Verity").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "A.lean").write_text(
                "axiom documented_axiom : True\naxiom missing_axiom : True\n",
                encoding="utf-8",
            )
            (root / "AXIOMS.md").write_text(
                "\n".join(
                    [
                        "### 1. `documented_axiom`",
                        "",
                        "**Location**: `Compiler/A.lean:1`",
                        "",
                        "## Trust Summary",
                        "",
                        "- Active axioms: 1",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )

            stderr = io.StringIO()
            old_root = check_axiom_locations.ROOT
            try:
                check_axiom_locations.ROOT = root
                with redirect_stderr(stderr), self.assertRaises(SystemExit):
                    check_axiom_locations.main()
            finally:
                check_axiom_locations.ROOT = old_root

            err = stderr.getvalue()
            self.assertIn("missing_axiom: declared in Compiler/A.lean:2 but missing from AXIOMS.md", err)
            self.assertIn("AXIOMS.md trust summary says Active axioms: 1, but source has 2", err)


if __name__ == "__main__":
    unittest.main()
