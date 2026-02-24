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

import check_verify_multiseed_sync
import property_utils


class VerifyMultiseedSyncTests(unittest.TestCase):
    def _run_check(self, verify_body: str, script_body: str, readme_body: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory(dir=property_utils.ROOT) as tmpdir:
            root = Path(tmpdir)
            verify = root / "verify.yml"
            script = root / "test_multiple_seeds.sh"
            readme = root / "README.md"
            verify.write_text(verify_body, encoding="utf-8")
            script.write_text(script_body, encoding="utf-8")
            readme.write_text(readme_body, encoding="utf-8")

            old_verify = check_verify_multiseed_sync.VERIFY_YML
            old_script = check_verify_multiseed_sync.MULTISEED_SCRIPT
            old_readme = check_verify_multiseed_sync.SCRIPTS_README
            check_verify_multiseed_sync.VERIFY_YML = verify
            check_verify_multiseed_sync.MULTISEED_SCRIPT = script
            check_verify_multiseed_sync.SCRIPTS_README = readme
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    rc = check_verify_multiseed_sync.main()
                return rc, stderr.getvalue()
            finally:
                check_verify_multiseed_sync.VERIFY_YML = old_verify
                check_verify_multiseed_sync.MULTISEED_SCRIPT = old_script
                check_verify_multiseed_sync.SCRIPTS_README = old_readme

    def test_rejects_seed_defined_outside_strategy_matrix(self) -> None:
        verify = textwrap.dedent(
            """\
            jobs:
              foundry-multi-seed:
                runs-on: ubuntu-latest
                steps:
                  - name: unrelated
                    with:
                      seed: [101, 202, 303]
            """
        )
        script = "DEFAULT_SEEDS=(101 202 303)\n"
        readme = "**`foundry-multi-seed`** smoke (seeds: 101, 202, 303)\n"
        rc, stderr = self._run_check(verify, script, readme)
        self.assertEqual(rc, 1)
        self.assertIn("Could not locate 'strategy'", stderr)

    def test_accepts_inline_matrix_seed_list(self) -> None:
        verify = textwrap.dedent(
            """\
            jobs:
              foundry-multi-seed:
                runs-on: ubuntu-latest
                strategy:
                  matrix:
                    seed: [7, 11, 13]
                steps: []
            """
        )
        script = "DEFAULT_SEEDS=(7 11 13)\n"
        readme = "**`foundry-multi-seed`** smoke (seeds: 7, 11, 13)\n"
        rc, stderr = self._run_check(verify, script, readme)
        self.assertEqual(rc, 0, stderr)

    def test_accepts_block_matrix_seed_list(self) -> None:
        verify = textwrap.dedent(
            """\
            jobs:
              foundry-multi-seed:
                runs-on: ubuntu-latest
                strategy:
                  matrix:
                    seed:
                      - 2
                      - 3
                      - 5
                steps: []
            """
        )
        script = "DEFAULT_SEEDS=(2 3 5)\n"
        readme = "**`foundry-multi-seed`** smoke (seeds: 2, 3, 5)\n"
        rc, stderr = self._run_check(verify, script, readme)
        self.assertEqual(rc, 0, stderr)


if __name__ == "__main__":
    unittest.main()
