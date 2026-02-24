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

import check_yul_builtin_boundary
import property_utils


class YulBuiltinBoundaryTests(unittest.TestCase):
    def _run_check(self, ir_body: str, sem_body: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory(dir=property_utils.ROOT) as tmpdir:
            root = Path(tmpdir)
            proofs = root / "Compiler" / "Proofs"
            builtins = proofs / "YulGeneration" / "Builtins.lean"
            ir = proofs / "IRGeneration" / "IRInterpreter.lean"
            sem = proofs / "YulGeneration" / "Semantics.lean"
            builtins.parent.mkdir(parents=True, exist_ok=True)
            ir.parent.mkdir(parents=True, exist_ok=True)
            sem.parent.mkdir(parents=True, exist_ok=True)

            builtins.write_text("-- builtin boundary module\n", encoding="utf-8")
            ir.write_text(ir_body, encoding="utf-8")
            sem.write_text(sem_body, encoding="utf-8")

            old_root = check_yul_builtin_boundary.ROOT
            old_proofs = check_yul_builtin_boundary.PROOFS_DIR
            old_builtins = check_yul_builtin_boundary.BUILTINS_FILE
            old_runtime = check_yul_builtin_boundary.RUNTIME_INTERPRETERS
            check_yul_builtin_boundary.ROOT = root
            check_yul_builtin_boundary.PROOFS_DIR = proofs
            check_yul_builtin_boundary.BUILTINS_FILE = builtins
            check_yul_builtin_boundary.RUNTIME_INTERPRETERS = [ir, sem]
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    rc = check_yul_builtin_boundary.main()
                return rc, stderr.getvalue()
            finally:
                check_yul_builtin_boundary.ROOT = old_root
                check_yul_builtin_boundary.PROOFS_DIR = old_proofs
                check_yul_builtin_boundary.BUILTINS_FILE = old_builtins
                check_yul_builtin_boundary.RUNTIME_INTERPRETERS = old_runtime

    def test_comment_only_decoy_does_not_satisfy_boundary(self) -> None:
        body = """import Compiler.Proofs.YulGeneration.Builtins
-- decoy only: Compiler.Proofs.YulGeneration.evalBuiltinCall
def evalExpr := 0
"""
        rc, stderr = self._run_check(body, body)
        self.assertEqual(rc, 1)
        self.assertIn("missing call", stderr)

    def test_string_literal_decoy_does_not_satisfy_boundary(self) -> None:
        body = """import Compiler.Proofs.YulGeneration.Builtins
def evalExpr := "Compiler.Proofs.YulGeneration.evalBuiltinCall"
"""
        rc, stderr = self._run_check(body, body)
        self.assertEqual(rc, 1)
        self.assertIn("missing call", stderr)

    def test_eval_builtin_call_with_backend_satisfies_boundary(self) -> None:
        body = """import Compiler.Proofs.YulGeneration.Builtins
def evalExpr :=
  Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackend
"""
        rc, _stderr = self._run_check(body, body)
        self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()
