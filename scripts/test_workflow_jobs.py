#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from workflow_jobs import extract_job_body, extract_top_level_jobs


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


if __name__ == "__main__":
    unittest.main()
