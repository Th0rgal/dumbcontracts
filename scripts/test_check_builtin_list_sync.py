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

import check_builtin_list_sync
import property_utils


class BuiltinListSyncTests(unittest.TestCase):
    def _run_check(self, linker_body: str, spec_body: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory(dir=property_utils.ROOT) as tmpdir:
            root = Path(tmpdir)
            linker = root / "Compiler" / "Linker.lean"
            spec = root / "Compiler" / "CompilationModel.lean"
            linker.parent.mkdir(parents=True, exist_ok=True)
            spec.parent.mkdir(parents=True, exist_ok=True)
            linker.write_text(linker_body, encoding="utf-8")
            spec.write_text(spec_body, encoding="utf-8")

            old_root = check_builtin_list_sync.ROOT
            old_linker = check_builtin_list_sync.LINKER
            old_spec = check_builtin_list_sync.CONTRACT_SPEC
            check_builtin_list_sync.ROOT = root
            check_builtin_list_sync.LINKER = linker
            check_builtin_list_sync.CONTRACT_SPEC = spec
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    rc = check_builtin_list_sync.main()
                return rc, stderr.getvalue()
            finally:
                check_builtin_list_sync.ROOT = old_root
                check_builtin_list_sync.LINKER = old_linker
                check_builtin_list_sync.CONTRACT_SPEC = old_spec

    def test_comment_decoy_definitions_do_not_mask_real_mismatch(self) -> None:
        rc, stderr = self._run_check(
            linker_body="""-- def yulBuiltins
-- ["mload"]
private def yulBuiltins : List String :=
  ["sstore"]
""",
            spec_body="""-- def interopBuiltinCallNames
-- ["mload"]
private def isLowLevelCallName (name : String) : Bool :=
  ["call"].contains name

private def interopBuiltinCallNames : List String :=
  ["add"]
""",
        )
        self.assertEqual(rc, 1)
        self.assertIn("In Linker.yulBuiltins but not in CompilationModel", stderr)
        self.assertIn("sstore", stderr)

    def test_checker_passes_for_matching_lists_with_expected_linker_only(self) -> None:
        rc, stderr = self._run_check(
            linker_body="""private def yulBuiltins : List String :=
  ["add", "call", "datasize"]
""",
            spec_body="""private def isLowLevelCallName (name : String) : Bool :=
  ["call"].contains name

private def interopBuiltinCallNames : List String :=
  ["add"]
""",
        )
        self.assertEqual(rc, 0, stderr)


if __name__ == "__main__":
    unittest.main()
