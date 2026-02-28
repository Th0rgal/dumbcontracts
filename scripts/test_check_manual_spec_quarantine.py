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

import check_manual_spec_quarantine


class ManualSpecQuarantineTests(unittest.TestCase):
    def _run_check(self, file_contents: dict[str, str]) -> tuple[int, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tmpdir:
            root = Path(tmpdir)
            canonical_files: list[Path] = []
            for rel in check_manual_spec_quarantine.CANONICAL_FILES:
                rel_path = rel.relative_to(check_manual_spec_quarantine.ROOT)
                path = root / rel_path
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(file_contents.get(str(rel_path), "-- empty\n"), encoding="utf-8")
                canonical_files.append(path)

            old_root = check_manual_spec_quarantine.ROOT
            old_files = check_manual_spec_quarantine.CANONICAL_FILES
            check_manual_spec_quarantine.ROOT = root
            check_manual_spec_quarantine.CANONICAL_FILES = canonical_files
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    rc = check_manual_spec_quarantine.main()
                return rc, stderr.getvalue()
            finally:
                check_manual_spec_quarantine.ROOT = old_root
                check_manual_spec_quarantine.CANONICAL_FILES = old_files

    def test_fails_on_manual_spec_reference(self) -> None:
        rc, stderr = self._run_check(
            {
                "Compiler/MainTest.lean": "def bad := Compiler.Specs.simpleStorageSpec\n",
            }
        )
        self.assertEqual(rc, 1)
        self.assertIn("Compiler.Specs.simpleStorageSpec", stderr)

    def test_allows_allowlisted_crypto_hash_compat_reference(self) -> None:
        rc, stderr = self._run_check(
            {
                "Compiler/CompileDriver.lean": "def ok := Specs.cryptoHashSpec\n",
            }
        )
        self.assertEqual(rc, 0, stderr)

    def test_ignores_comment_and_string_decoys(self) -> None:
        rc, stderr = self._run_check(
            {
                "Compiler/Main.lean": (
                    "-- Compiler.Specs.simpleStorageSpec\n"
                    "def msg := \"Compiler.Specs.counterSpec\"\n"
                ),
            }
        )
        self.assertEqual(rc, 0, stderr)


if __name__ == "__main__":
    unittest.main()
