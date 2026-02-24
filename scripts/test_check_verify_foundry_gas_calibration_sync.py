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

import check_verify_foundry_gas_calibration_sync as check


class VerifyFoundryGasCalibrationSyncTests(unittest.TestCase):
    def _run_check(self, verify_text: str, readme_text: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            root = Path(td)
            verify_path = root / "verify.yml"
            readme_path = root / "README.md"
            verify_path.write_text(verify_text, encoding="utf-8")
            readme_path.write_text(readme_text, encoding="utf-8")

            old_verify = check.VERIFY_YML
            old_readme = check.SCRIPTS_README
            check.VERIFY_YML = verify_path
            check.SCRIPTS_README = readme_path
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    try:
                        rc = check.main()
                    except Exception as exc:
                        print(str(exc), file=sys.stderr)
                        rc = 1
                return rc, stderr.getvalue()
            finally:
                check.VERIFY_YML = old_verify
                check.SCRIPTS_README = old_readme

    def test_decoy_values_outside_target_steps_fail(self) -> None:
        verify = textwrap.dedent(
            """
            name: Verify proofs
            jobs:
              foundry-gas-calibration:
                runs-on: ubuntu-latest
                steps:
                  - name: Unrelated step with misleading with.name
                    uses: actions/upload-artifact@v4
                    with:
                      name: static-gas-report
                      path: dummy.txt

                  - name: Download static gas report
                    uses: actions/download-artifact@v4
                    with:
                      name: WRONG-ARTIFACT

                  - name: Setup Foundry environment
                    uses: ./.github/actions/setup-foundry

                  - name: Unrelated env source
                    env:
                      FOUNDRY_PROFILE: difftest
                    run: echo not calibration

                  - name: Check static-vs-foundry gas calibration
                    env:
                      FOUNDRY_PROFILE: wrongprofile
                    run: python3 scripts/check_gas_calibration.py --static-report gas-report-static.tsv
            """
        )
        readme = (
            "**`foundry-gas-calibration`** Runs `check_gas_calibration.py` "
            "using Foundry gas report against static report baseline.\n"
        )
        rc, stderr = self._run_check(verify, readme)
        self.assertEqual(rc, 1)
        self.assertIn("FOUNDRY_PROFILE=difftest", stderr)
        self.assertIn("static-gas-report artifact", stderr)

    def test_target_steps_with_expected_values_pass(self) -> None:
        verify = textwrap.dedent(
            """
            name: Verify proofs
            jobs:
              foundry-gas-calibration:
                runs-on: ubuntu-latest
                steps:
                  - name: Unrelated step with misleading with.name
                    uses: actions/upload-artifact@v4
                    with:
                      name: WRONG-DECOY
                      path: dummy.txt

                  - name: Download static gas report
                    uses: actions/download-artifact@v4
                    with:
                      name: static-gas-report

                  - name: Check static-vs-foundry gas calibration
                    env:
                      FOUNDRY_PROFILE: difftest
                    run: |
                      echo calibration
                      python3 scripts/check_gas_calibration.py --static-report gas-report-static.tsv
            """
        )
        readme = (
            "**`foundry-gas-calibration`** — Static-vs-Foundry gas calibration "
            "check (`check_gas_calibration.py`) using static report + Foundry gas report.\n"
        )
        rc, stderr = self._run_check(verify, readme)
        self.assertEqual(rc, 0, stderr)

    def test_step_names_allow_inline_comments(self) -> None:
        verify = textwrap.dedent(
            """
            name: Verify proofs
            jobs:
              foundry-gas-calibration:
                runs-on: ubuntu-latest
                steps:
                  - name: Download static gas report # keep
                    uses: actions/download-artifact@v4
                    with:
                      name: static-gas-report

                  - name: Check static-vs-foundry gas calibration # keep
                    env:
                      FOUNDRY_PROFILE: difftest
                    run: python3 scripts/check_gas_calibration.py --static-report gas-report-static.tsv
            """
        )
        readme = (
            "**`foundry-gas-calibration`** Runs `check_gas_calibration.py` "
            "using Foundry gas report against static report baseline.\n"
        )
        rc, stderr = self._run_check(verify, readme)
        self.assertEqual(rc, 0, stderr)

    def test_download_artifact_allows_non_v4_ref(self) -> None:
        verify = textwrap.dedent(
            """
            name: Verify proofs
            jobs:
              foundry-gas-calibration:
                runs-on: ubuntu-latest
                steps:
                  - name: Download static gas report
                    uses: "actions/download-artifact@v4.1.0"
                    with:
                      name: static-gas-report

                  - name: Check static-vs-foundry gas calibration
                    env:
                      FOUNDRY_PROFILE: difftest
                    run: python3 scripts/check_gas_calibration.py --static-report gas-report-static.tsv
            """
        )
        readme = (
            "**`foundry-gas-calibration`** Runs `check_gas_calibration.py` "
            "using Foundry gas report against static report baseline.\n"
        )
        rc, stderr = self._run_check(verify, readme)
        self.assertEqual(rc, 0, stderr)


if __name__ == "__main__":
    unittest.main()
