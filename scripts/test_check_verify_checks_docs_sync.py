#!/usr/bin/env python3
from __future__ import annotations

import sys
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_verify_checks_docs_sync import _extract_workflow_checks_commands


class VerifyChecksDocsSyncTests(unittest.TestCase):
    def test_extracts_inline_dash_run_style(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              checks:
                runs-on: ubuntu-latest
                steps:
                  - run: python3 scripts/check_inline.py --strict
                  - run: echo done
              other:
                runs-on: ubuntu-latest
                steps: []
            """
        )

        self.assertEqual(
            _extract_workflow_checks_commands(workflow),
            ["check_inline.py --strict"],
        )

    def test_extracts_single_line_and_block_run_commands(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              checks:
                runs-on: ubuntu-latest
                steps:
                  - name: single-line
                    run: python3 scripts/check_a.py
                  - name: block
                    run: |
                      python3 scripts/check_b.py
                      echo done
              other:
                runs-on: ubuntu-latest
                steps: []
            """
        )

        self.assertEqual(
            _extract_workflow_checks_commands(workflow),
            ["check_a.py", "check_b.py"],
        )

    def test_extracts_folded_block_run_commands(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              checks:
                runs-on: ubuntu-latest
                steps:
                  - name: folded
                    run: >-
                      python3 scripts/check_c.py
                      python3 scripts/check_d.py --strict
                      echo done
              other:
                runs-on: ubuntu-latest
                steps: []
            """
        )

        self.assertEqual(
            _extract_workflow_checks_commands(workflow),
            ["check_c.py", "check_d.py --strict"],
        )

    def test_extracts_line_continuation_commands(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              checks:
                runs-on: ubuntu-latest
                steps:
                  - name: continuation
                    run: |
                      python3 scripts/check_e.py \\
                        --strict
                      echo done
              other:
                runs-on: ubuntu-latest
                steps: []
            """
        )

        self.assertEqual(
            _extract_workflow_checks_commands(workflow),
            ["check_e.py --strict"],
        )

    def test_extracts_with_inline_comments(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              checks:
                runs-on: ubuntu-latest
                steps:
                  - name: comments
                    run: |
                      # decoy comment
                      python3 scripts/check_f.py --strict  # enforce strict mode
                      echo done
              other:
                runs-on: ubuntu-latest
                steps: []
            """
        )

        self.assertEqual(
            _extract_workflow_checks_commands(workflow),
            ["check_f.py --strict"],
        )


if __name__ == "__main__":
    unittest.main()
