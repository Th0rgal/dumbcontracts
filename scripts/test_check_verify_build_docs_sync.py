#!/usr/bin/env python3
from __future__ import annotations

import sys
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_verify_build_docs_sync import _extract_workflow_job_commands


class VerifyBuildDocsSyncTests(unittest.TestCase):
    def test_extracts_inline_dash_run_style(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              build:
                runs-on: ubuntu-latest
                steps:
                  - run: python3 scripts/check_a.py
                  - run: echo done
              other:
                runs-on: ubuntu-latest
                steps: []
            """
        )

        self.assertEqual(_extract_workflow_job_commands(workflow, "build"), ["check_a.py"])

    def test_extracts_folded_block_run_commands(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              build:
                runs-on: ubuntu-latest
                steps:
                  - name: folded
                    run: >-
                      python3 scripts/check_b.py
                      python3 scripts/check_c.py --strict
                      echo done
              other:
                runs-on: ubuntu-latest
                steps: []
            """
        )

        self.assertEqual(
            _extract_workflow_job_commands(workflow, "build"),
            ["check_b.py", "check_c.py"],
        )

    def test_extracts_line_continuation_commands(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              build:
                runs-on: ubuntu-latest
                steps:
                  - name: continuation
                    run: |
                      python3 scripts/check_d.py \\
                        --strict
                      echo done
              other:
                runs-on: ubuntu-latest
                steps: []
            """
        )

        self.assertEqual(_extract_workflow_job_commands(workflow, "build"), ["check_d.py"])

    def test_extracts_with_inline_comments(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              build:
                runs-on: ubuntu-latest
                steps:
                  - name: comments
                    run: |
                      # decoy
                      python3 scripts/check_e.py --strict  # keep strict in workflow only
                      echo done
              other:
                runs-on: ubuntu-latest
                steps: []
            """
        )

        self.assertEqual(_extract_workflow_job_commands(workflow, "build"), ["check_e.py"])

    def test_extracts_build_compiler_job(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              build-compiler:
                runs-on: ubuntu-latest
                steps:
                  - run: python3 scripts/check_gas.py
                  - run: python3 scripts/check_yul.py
              other:
                runs-on: ubuntu-latest
                steps: []
            """
        )

        self.assertEqual(
            _extract_workflow_job_commands(workflow, "build-compiler"),
            ["check_gas.py", "check_yul.py"],
        )


if __name__ == "__main__":
    unittest.main()
