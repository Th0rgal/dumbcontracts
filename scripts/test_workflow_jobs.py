#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from workflow_jobs import (
    extract_job_body,
    extract_literal_from_mapping_blocks,
    extract_run_commands_from_job_body,
    extract_top_level_jobs,
    match_shell_command,
)


class WorkflowJobsTests(unittest.TestCase):
    def test_extract_top_level_jobs_supports_quoted_and_plain_keys(self) -> None:
        workflow = "\n".join(
            [
                "name: Verify",
                "jobs:",
                "  build:",
                "    runs-on: ubuntu-latest",
                '  "quoted-job":',
                "    runs-on: ubuntu-latest",
                "  checks_2:",
                "    runs-on: ubuntu-latest",
                "",
            ]
        )
        with tempfile.TemporaryDirectory() as tmpdir:
            source = Path(tmpdir) / "verify.yml"
            source.write_text(workflow, encoding="utf-8")
            self.assertEqual(
                extract_top_level_jobs(workflow, source),
                ["build", "quoted-job", "checks_2"],
            )

    def test_extract_job_body_stops_at_next_quoted_job_key(self) -> None:
        workflow = "\n".join(
            [
                "name: Verify",
                "jobs:",
                "  foundry:",
                "    env:",
                '      DIFFTEST_RANDOM_SEED: "7"',
                '  "decoy-job":',
                "    env:",
                '      DIFFTEST_RANDOM_SEED: "999"',
                "",
            ]
        )
        with tempfile.TemporaryDirectory() as tmpdir:
            source = Path(tmpdir) / "verify.yml"
            source.write_text(workflow, encoding="utf-8")
            body = extract_job_body(workflow, "foundry", source)
            self.assertIn('DIFFTEST_RANDOM_SEED: "7"', body)
            self.assertNotIn('DIFFTEST_RANDOM_SEED: "999"', body)

    def test_extract_literal_from_env_ignores_with_block_decoys(self) -> None:
        body = "\n".join(
            [
                "    steps:",
                "      - uses: actions/upload-artifact@v4",
                "        with:",
                '          DIFFTEST_RANDOM_SEED: "999"',
                "      - name: run tests",
                "        env:",
                '          DIFFTEST_RANDOM_SEED: "42"',
                "",
            ]
        )
        with tempfile.TemporaryDirectory() as tmpdir:
            source = Path(tmpdir) / "verify.yml"
            source.write_text(body, encoding="utf-8")
            value = extract_literal_from_mapping_blocks(
                body,
                "env",
                "DIFFTEST_RANDOM_SEED",
                source=source,
                context="foundry",
            )
            self.assertEqual(value, "42")

    def test_extract_run_commands_from_job_body_ignores_name_decoys(self) -> None:
        body = "\n".join(
            [
                "    steps:",
                '      - name: forge test --no-match-test "Random10000"',
                "        run: echo not the real command",
                "      - name: run tests",
                "        run: |",
                "          echo starting",
                "          # forge test --no-match-test \"Random10000\"",
                "          forge test --no-match-test \"Random10000\"",
                "",
            ]
        )
        with tempfile.TemporaryDirectory() as tmpdir:
            source = Path(tmpdir) / "verify.yml"
            source.write_text(body, encoding="utf-8")
            commands = extract_run_commands_from_job_body(
                body,
                source=source,
                context="foundry-patched",
            )
            self.assertIn('forge test --no-match-test "Random10000"', commands)
            self.assertNotIn('name: forge test --no-match-test "Random10000"', commands)

    def test_match_shell_command_accepts_path_env_wrapper(self) -> None:
        matched, forge_tokens = match_shell_command(
            '/usr/bin/env FOUNDRY_PROFILE=difftest forge test --no-match-test "Random10000"',
            program="forge",
            args_prefix=("test",),
        )
        self.assertTrue(matched)
        self.assertEqual(forge_tokens[:2], ["forge", "test"])

    def test_match_shell_command_accepts_command_wrapper(self) -> None:
        matched, forge_tokens = match_shell_command(
            "command -- env FOUNDRY_PROFILE=difftest forge test",
            program="forge",
            args_prefix=("test",),
        )
        self.assertTrue(matched)
        self.assertEqual(forge_tokens[:2], ["forge", "test"])

    def test_match_shell_command_accepts_time_wrapper(self) -> None:
        matched, forge_tokens = match_shell_command(
            'time -f "%E" env FOUNDRY_PROFILE=difftest forge test -vv',
            program="forge",
            args_prefix=("test",),
        )
        self.assertTrue(matched)
        self.assertEqual(forge_tokens[:2], ["forge", "test"])

    def test_match_shell_command_accepts_timeout_and_nice_wrappers(self) -> None:
        matched, forge_tokens = match_shell_command(
            "timeout -k 5s 10m nice -n 10 forge test --no-match-test Random10000",
            program="forge",
            args_prefix=("test",),
        )
        self.assertTrue(matched)
        self.assertEqual(forge_tokens[:2], ["forge", "test"])


if __name__ == "__main__":
    unittest.main()
