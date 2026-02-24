#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_interop_matrix_sync
import property_utils


class InteropMatrixSyncTests(unittest.TestCase):
    def _run_check(self, roadmap_body: str, status_body: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory(dir=property_utils.ROOT) as tmpdir:
            root = Path(tmpdir)
            roadmap = root / "docs" / "ROADMAP.md"
            status = root / "docs" / "VERIFICATION_STATUS.md"
            roadmap.parent.mkdir(parents=True, exist_ok=True)
            status.parent.mkdir(parents=True, exist_ok=True)
            roadmap.write_text(roadmap_body, encoding="utf-8")
            status.write_text(status_body, encoding="utf-8")

            old_roadmap = check_interop_matrix_sync.ROADMAP
            old_status = check_interop_matrix_sync.VERIFICATION_STATUS
            check_interop_matrix_sync.ROADMAP = roadmap
            check_interop_matrix_sync.VERIFICATION_STATUS = status
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    try:
                        check_interop_matrix_sync.main()
                        return 0, stderr.getvalue()
                    except SystemExit as exc:
                        return int(exc.code), stderr.getvalue()
            finally:
                check_interop_matrix_sync.ROADMAP = old_roadmap
                check_interop_matrix_sync.VERIFICATION_STATUS = old_status

    def test_duplicate_normalized_feature_in_roadmap_fails(self) -> None:
        roadmap = textwrap.dedent(
            """
            ### Solidity Interop Profile (Issue #586)

            | Priority | Feature | Spec support | Codegen support | Proof status | Test status | Current status |
            |---|---|---|---|---|---|---|
            | P1 | Event ABI parity for indexed dynamic tuple payloads | yes | yes | done | done | green |
            | P2 | Full event ABI parity (indexed dynamic + tuple hashing) | yes | yes | done | done | green |
            """
        )
        status = textwrap.dedent(
            """
            ## Solidity Interop Support Matrix (Issue #586)

            | Feature | Spec support | Codegen support | Proof status | Test status | Current status |
            |---|---|---|---|---|---|
            | Event ABI parity indexed dynamic tuple payloads | yes | yes | done | done | green |
            """
        )
        rc, stderr = self._run_check(roadmap, status)
        self.assertEqual(rc, 1)
        self.assertIn("duplicate normalized feature key", stderr)
        self.assertIn("roadmap rows 1 and 2", stderr)

    def test_duplicate_normalized_feature_in_verification_fails(self) -> None:
        roadmap = textwrap.dedent(
            """
            ### Solidity Interop Profile (Issue #586)

            | Priority | Feature | Spec support | Codegen support | Proof status | Test status | Current status |
            |---|---|---|---|---|---|---|
            | P1 | Event ABI parity indexed dynamic tuple payloads | yes | yes | done | done | green |
            """
        )
        status = textwrap.dedent(
            """
            ## Solidity Interop Support Matrix (Issue #586)

            | Feature | Spec support | Codegen support | Proof status | Test status | Current status |
            |---|---|---|---|---|---|
            | Event ABI parity indexed dynamic tuple payloads | yes | yes | done | done | green |
            | Event ABI parity for indexed dynamic tuple payloads | yes | yes | done | done | green |
            """
        )
        rc, stderr = self._run_check(roadmap, status)
        self.assertEqual(rc, 1)
        self.assertIn("duplicate normalized feature key", stderr)
        self.assertIn("verification rows 1 and 2", stderr)

    def test_matching_single_rows_pass(self) -> None:
        roadmap = textwrap.dedent(
            """
            ### Solidity Interop Profile (Issue #586)

            | Priority | Feature | Spec support | Codegen support | Proof status | Test status | Current status |
            |---|---|---|---|---|---|---|
            | P1 | Event ABI parity indexed dynamic tuple payloads | yes | yes | done | done | green |
            """
        )
        status = textwrap.dedent(
            """
            ## Solidity Interop Support Matrix (Issue #586)

            | Feature | Spec support | Codegen support | Proof status | Test status | Current status |
            |---|---|---|---|---|---|
            | Event ABI parity for indexed dynamic tuple payloads | yes | yes | done | done | green |
            """
        )
        rc, stderr = self._run_check(roadmap, status)
        self.assertEqual(rc, 0, stderr)


if __name__ == "__main__":
    unittest.main()
