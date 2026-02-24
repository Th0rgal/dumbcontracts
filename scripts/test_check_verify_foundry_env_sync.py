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

import check_verify_foundry_job_sync
import check_verify_foundry_patched_sync
import check_verify_foundry_shard_sync


class FoundryEnvSyncTests(unittest.TestCase):
    def _run_job_sync(self, workflow_body: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as d:
            wf = Path(d) / "verify.yml"
            wf.write_text(workflow_body, encoding="utf-8")
            old_verify = check_verify_foundry_job_sync.VERIFY_YML
            check_verify_foundry_job_sync.VERIFY_YML = wf
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    try:
                        rc = check_verify_foundry_job_sync.main()
                        return rc, stderr.getvalue()
                    except Exception as exc:
                        print(str(exc), file=sys.stderr)
                        return 1, stderr.getvalue()
            finally:
                check_verify_foundry_job_sync.VERIFY_YML = old_verify

    def _run_patched_sync(self, workflow_body: str, readme_body: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as d:
            wf = Path(d) / "verify.yml"
            rd = Path(d) / "README.md"
            wf.write_text(workflow_body, encoding="utf-8")
            rd.write_text(readme_body, encoding="utf-8")
            old_verify = check_verify_foundry_patched_sync.VERIFY_YML
            old_readme = check_verify_foundry_patched_sync.SCRIPTS_README
            check_verify_foundry_patched_sync.VERIFY_YML = wf
            check_verify_foundry_patched_sync.SCRIPTS_README = rd
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    try:
                        rc = check_verify_foundry_patched_sync.main()
                        return rc, stderr.getvalue()
                    except Exception as exc:
                        print(str(exc), file=sys.stderr)
                        return 1, stderr.getvalue()
            finally:
                check_verify_foundry_patched_sync.VERIFY_YML = old_verify
                check_verify_foundry_patched_sync.SCRIPTS_README = old_readme

    def _run_shard_sync(self, workflow_body: str, readme_body: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as d:
            wf = Path(d) / "verify.yml"
            rd = Path(d) / "README.md"
            wf.write_text(workflow_body, encoding="utf-8")
            rd.write_text(readme_body, encoding="utf-8")
            old_verify = check_verify_foundry_shard_sync.VERIFY_YML
            old_readme = check_verify_foundry_shard_sync.SCRIPTS_README
            check_verify_foundry_shard_sync.VERIFY_YML = wf
            check_verify_foundry_shard_sync.SCRIPTS_README = rd
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    try:
                        rc = check_verify_foundry_shard_sync.main()
                        return rc, stderr.getvalue()
                    except Exception as exc:
                        print(str(exc), file=sys.stderr)
                        return 1, stderr.getvalue()
            finally:
                check_verify_foundry_shard_sync.VERIFY_YML = old_verify
                check_verify_foundry_shard_sync.SCRIPTS_README = old_readme

    def test_job_sync_rejects_with_block_decoys_when_env_missing(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on: {}
            jobs:
              foundry:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/upload-artifact@v4
                    with:
                      FOUNDRY_PROFILE: "difftest"
                      DIFFTEST_RANDOM_SMALL: "100"
                      DIFFTEST_RANDOM_LARGE: "10000"
                      DIFFTEST_YUL_DIR: "compiler/yul"
                  - name: Download generated Yul
                    uses: actions/download-artifact@v4
                    with:
                      name: generated-yul
                      path: compiler/yul
                  - run: forge test

              foundry-patched:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/upload-artifact@v4
                    with:
                      FOUNDRY_PROFILE: "difftest"
                      DIFFTEST_RANDOM_SMALL: "100"
                      DIFFTEST_RANDOM_LARGE: "10000"
                      DIFFTEST_YUL_DIR: "compiler/yul-patched"
                  - name: Download patched Yul
                    uses: actions/download-artifact@v4
                    with:
                      name: generated-yul-patched
                      path: compiler/yul-patched
                  - run: forge test --no-match-test "Random10000"

              foundry-multi-seed:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/upload-artifact@v4
                    with:
                      FOUNDRY_PROFILE: "difftest"
                      DIFFTEST_RANDOM_SMALL: "100"
                      DIFFTEST_RANDOM_LARGE: "10000"
                      DIFFTEST_YUL_DIR: "compiler/yul"
                  - name: Download generated Yul
                    uses: actions/download-artifact@v4
                    with:
                      name: generated-yul
                      path: compiler/yul
                  - run: forge test --no-match-test "Random10000"
            """
        )
        rc, stderr = self._run_job_sync(workflow)
        self.assertEqual(rc, 1)
        self.assertIn("FOUNDRY_PROFILE", stderr)

    def test_foundry_patched_sync_rejects_with_block_decoys_when_env_missing(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on: {}
            jobs:
              foundry-patched:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/upload-artifact@v4
                    with:
                      DIFFTEST_RANDOM_SEED: "42"
                      DIFFTEST_SHARD_COUNT: "1"
                      DIFFTEST_SHARD_INDEX: "0"
                  - run: forge test --no-match-test "Random10000"
            """
        )
        readme = "**`foundry-patched`** (seed 42, single shard, no `Random10000`)\n"
        rc, stderr = self._run_patched_sync(workflow, readme)
        self.assertEqual(rc, 1)
        self.assertIn("DIFFTEST_RANDOM_SEED", stderr)

    def test_foundry_shard_sync_rejects_with_block_decoys_when_env_missing(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on: {}
            jobs:
              foundry:
                runs-on: ubuntu-latest
                strategy:
                  matrix:
                    shard_index: [0, 1, 2]
                steps:
                  - uses: actions/upload-artifact@v4
                    with:
                      DIFFTEST_SHARD_COUNT: "3"
                      DIFFTEST_RANDOM_SEED: "42"
                  - run: forge test
            """
        )
        readme = "**`foundry`** — 3-shard parallel Foundry tests with seed 42\n"
        rc, stderr = self._run_shard_sync(workflow, readme)
        self.assertEqual(rc, 1)
        self.assertIn("DIFFTEST_SHARD_COUNT", stderr)

    def test_job_sync_ignores_forge_decoy_in_step_name(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on: {}
            jobs:
              foundry:
                runs-on: ubuntu-latest
                steps:
                  - name: Download generated Yul
                    uses: actions/download-artifact@v4
                    with:
                      name: generated-yul
                      path: compiler/yul
                  - name: forge test
                    run: echo "not running tests"
                env:
                  FOUNDRY_PROFILE: "difftest"
                  DIFFTEST_RANDOM_SMALL: "100"
                  DIFFTEST_RANDOM_LARGE: "10000"
                  DIFFTEST_YUL_DIR: "compiler/yul"

              foundry-patched:
                runs-on: ubuntu-latest
                steps:
                  - name: Download patched Yul
                    uses: actions/download-artifact@v4
                    with:
                      name: generated-yul-patched
                      path: compiler/yul-patched
                  - run: forge test --no-match-test "Random10000"
                env:
                  FOUNDRY_PROFILE: "difftest"
                  DIFFTEST_RANDOM_SMALL: "100"
                  DIFFTEST_RANDOM_LARGE: "10000"
                  DIFFTEST_YUL_DIR: "compiler/yul-patched"

              foundry-multi-seed:
                runs-on: ubuntu-latest
                steps:
                  - name: Download generated Yul
                    uses: actions/download-artifact@v4
                    with:
                      name: generated-yul
                      path: compiler/yul
                  - run: forge test --no-match-test "Random10000"
                env:
                  FOUNDRY_PROFILE: "difftest"
                  DIFFTEST_RANDOM_SMALL: "100"
                  DIFFTEST_RANDOM_LARGE: "10000"
                  DIFFTEST_YUL_DIR: "compiler/yul"
            """
        )
        rc, stderr = self._run_job_sync(workflow)
        self.assertEqual(rc, 1)
        self.assertIn("Could not locate 'forge test' command", stderr)

    def test_foundry_patched_sync_ignores_forge_decoy_in_name(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on: {}
            jobs:
              foundry-patched:
                runs-on: ubuntu-latest
                steps:
                  - name: forge test --no-match-test "Random10000"
                    run: echo "placeholder"
                env:
                  DIFFTEST_RANDOM_SEED: "42"
                  DIFFTEST_SHARD_COUNT: "1"
                  DIFFTEST_SHARD_INDEX: "0"
            """
        )
        readme = "**`foundry-patched`** (seed 42, single shard, no `Random10000`)\n"
        rc, stderr = self._run_patched_sync(workflow, readme)
        self.assertEqual(rc, 1)
        self.assertIn("Could not locate 'forge test --no-match-test", stderr)

    def test_job_sync_accepts_env_prefixed_forge_commands(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on: {}
            jobs:
              foundry:
                runs-on: ubuntu-latest
                env:
                  FOUNDRY_PROFILE: "difftest"
                  DIFFTEST_RANDOM_SMALL: "100"
                  DIFFTEST_RANDOM_LARGE: "10000"
                  DIFFTEST_YUL_DIR: "compiler/yul"
                steps:
                  - name: Download generated Yul
                    uses: actions/download-artifact@v4
                    with:
                      name: generated-yul
                      path: compiler/yul
                  - run: FOUNDRY_PROFILE=difftest forge test

              foundry-patched:
                runs-on: ubuntu-latest
                env:
                  FOUNDRY_PROFILE: "difftest"
                  DIFFTEST_RANDOM_SMALL: "100"
                  DIFFTEST_RANDOM_LARGE: "10000"
                  DIFFTEST_YUL_DIR: "compiler/yul-patched"
                steps:
                  - name: Download patched Yul
                    uses: actions/download-artifact@v4
                    with:
                      name: generated-yul-patched
                      path: compiler/yul-patched
                  - run: env FOUNDRY_PROFILE=difftest forge test --no-match-test "Random10000"

              foundry-multi-seed:
                runs-on: ubuntu-latest
                env:
                  FOUNDRY_PROFILE: "difftest"
                  DIFFTEST_RANDOM_SMALL: "100"
                  DIFFTEST_RANDOM_LARGE: "10000"
                  DIFFTEST_YUL_DIR: "compiler/yul"
                steps:
                  - name: Download generated Yul
                    uses: actions/download-artifact@v4
                    with:
                      name: generated-yul
                      path: compiler/yul
                  - run: DIFFTEST_RANDOM_SEED=7 forge test --no-match-test "Random10000"
            """
        )
        rc, stderr = self._run_job_sync(workflow)
        self.assertEqual(rc, 0, stderr)

    def test_foundry_patched_sync_accepts_env_prefix_and_extra_flags(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on: {}
            jobs:
              foundry-patched:
                runs-on: ubuntu-latest
                env:
                  DIFFTEST_RANDOM_SEED: "42"
                  DIFFTEST_SHARD_COUNT: "1"
                  DIFFTEST_SHARD_INDEX: "0"
                steps:
                  - run: FOUNDRY_PROFILE=difftest forge test -vv --no-match-test "Random10000"
            """
        )
        readme = "**`foundry-patched`** (seed 42, single shard, no `Random10000`)\n"
        rc, stderr = self._run_patched_sync(workflow, readme)
        self.assertEqual(rc, 0, stderr)


if __name__ == "__main__":
    unittest.main()
