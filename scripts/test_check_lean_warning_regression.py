#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parent / "check_lean_warning_regression.py"


class CheckLeanWarningRegressionScriptTests(unittest.TestCase):
    def test_accepts_valid_baseline(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            log_path = root / "lake-build.log"
            baseline_path = root / "lean_warning_baseline.json"
            log_path.write_text(
                "warning: Compiler/Main.lean:1:1: declaration uses 'sorry'\n",
                encoding="utf-8",
            )
            baseline_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "total_warnings": 1,
                        "by_file": {"Compiler/Main.lean": 1},
                        "by_message": {"declaration uses 'sorry'": 1},
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            proc = subprocess.run(
                [sys.executable, str(SCRIPT), "--log", str(log_path), "--baseline", str(baseline_path)],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertIn("Lean warning non-regression check passed", proc.stdout)

    def test_rejects_invalid_baseline_counter_shape(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            log_path = root / "lake-build.log"
            baseline_path = root / "lean_warning_baseline.json"
            log_path.write_text("", encoding="utf-8")
            baseline_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "total_warnings": 0,
                        "by_file": [],
                        "by_message": {},
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            proc = subprocess.run(
                [sys.executable, str(SCRIPT), "--log", str(log_path), "--baseline", str(baseline_path)],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("'by_file' must be an object", proc.stderr)

    def test_rejects_invariant_mismatch_in_baseline(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            log_path = root / "lake-build.log"
            baseline_path = root / "lean_warning_baseline.json"
            log_path.write_text("", encoding="utf-8")
            baseline_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "total_warnings": 2,
                        "by_file": {"Compiler/Main.lean": 1},
                        "by_message": {"m": 2},
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            proc = subprocess.run(
                [sys.executable, str(SCRIPT), "--log", str(log_path), "--baseline", str(baseline_path)],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("sum(by_file)=1 must equal total_warnings=2", proc.stderr)


if __name__ == "__main__":
    unittest.main()
