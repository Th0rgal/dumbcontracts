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

import check_spec_proof_migration_boundary as guard


class SpecProofMigrationBoundaryTests(unittest.TestCase):
    def _run_check(self, files: dict[str, str], allowlist: set[str]) -> tuple[int, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tmpdir:
            root = Path(tmpdir)
            compiler_proofs = root / "Compiler" / "Proofs"
            verity_proofs = root / "Verity" / "Proofs"
            compiler_proofs.mkdir(parents=True, exist_ok=True)
            verity_proofs.mkdir(parents=True, exist_ok=True)

            for rel, content in files.items():
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content, encoding="utf-8")

            old_root = guard.ROOT
            old_roots = guard.PROOF_ROOTS
            old_allowlist = guard.ALLOWLIST
            guard.ROOT = root
            guard.PROOF_ROOTS = [compiler_proofs, verity_proofs]
            guard.ALLOWLIST = {Path(p) for p in allowlist}
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    rc = guard.main()
                return rc, stderr.getvalue()
            finally:
                guard.ROOT = old_root
                guard.PROOF_ROOTS = old_roots
                guard.ALLOWLIST = old_allowlist

    def test_rejects_non_allowlisted_legacy_reference(self) -> None:
        rc, stderr = self._run_check(
            {
                "Verity/Proofs/NewContract/Basic.lean": (
                    "import Verity.Examples.Counter\n"
                    "def x := 1\n"
                )
            },
            allowlist=set(),
        )
        self.assertEqual(rc, 1)
        self.assertIn("unexpected legacy proof reference", stderr)

    def test_accepts_allowlisted_legacy_reference(self) -> None:
        rc, stderr = self._run_check(
            {
                "Compiler/Proofs/SpecCorrectness/Counter.lean": (
                    "def x := Compiler.Specs.counterSpec\n"
                )
            },
            allowlist={"Compiler/Proofs/SpecCorrectness/Counter.lean"},
        )
        self.assertEqual(rc, 0, stderr)

    def test_fails_on_stale_allowlist_entry(self) -> None:
        rc, stderr = self._run_check(
            {"Verity/Proofs/Counter/Basic.lean": "def ok := 42\n"},
            allowlist={"Verity/Proofs/Counter/Basic.lean"},
        )
        self.assertEqual(rc, 1)
        self.assertIn("stale allowlist entry", stderr)

    def test_ignores_comment_and_string_decoys(self) -> None:
        rc, stderr = self._run_check(
            {
                "Verity/Proofs/Counter/Basic.lean": (
                    "-- Verity.Examples.Counter\n"
                    "def msg := \"Compiler.Specs.counterSpec\"\n"
                )
            },
            allowlist=set(),
        )
        self.assertEqual(rc, 0, stderr)


if __name__ == "__main__":
    unittest.main()
