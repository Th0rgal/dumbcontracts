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

import check_verify_paths_sync


class VerifyPathsSyncTests(unittest.TestCase):
    def _run_check(self, workflow_body: str) -> tuple[int, str]:
        with tempfile.NamedTemporaryFile(
            "w", encoding="utf-8", delete=False, dir=SCRIPT_DIR.parent
        ) as tmp:
            tmp.write(workflow_body)
            workflow_path = Path(tmp.name)

        old_verify = check_verify_paths_sync.VERIFY_YML
        check_verify_paths_sync.VERIFY_YML = workflow_path
        try:
            stderr = io.StringIO()
            with redirect_stderr(stderr):
                try:
                    rc = check_verify_paths_sync.main()
                    return rc, stderr.getvalue()
                except Exception as exc:  # main currently surfaces parse errors directly
                    print(str(exc), file=sys.stderr)
                    return 1, stderr.getvalue()
        finally:
            check_verify_paths_sync.VERIFY_YML = old_verify
            workflow_path.unlink(missing_ok=True)

    def test_decoy_filters_outside_changes_job_fails(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - src/**
                  - docs/**
                  - docs-site/**
                  - AXIOMS.md
                  - README.md
                  - TRUST_ASSUMPTIONS.md
              pull_request:
                paths:
                  - src/**
                  - docs/**
                  - docs-site/**
                  - AXIOMS.md
                  - README.md
                  - TRUST_ASSUMPTIONS.md
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - run: echo no real filters block here
              decoy:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - src/**
            """
        )
        rc, stderr = self._run_check(workflow)
        self.assertEqual(rc, 1)
        self.assertIn("changes.filter.code", stderr)

    def test_changes_job_filters_are_used_even_with_decoy(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - src/**
                  - docs/**
                  - docs-site/**
                  - AXIOMS.md
                  - README.md
                  - TRUST_ASSUMPTIONS.md
              pull_request:
                paths:
                  - src/**
                  - docs/**
                  - docs-site/**
                  - AXIOMS.md
                  - README.md
                  - TRUST_ASSUMPTIONS.md
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - src/**
              decoy:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - not/real/**
            """
        )
        rc, stderr = self._run_check(workflow)
        self.assertEqual(rc, 0, stderr)


if __name__ == "__main__":
    unittest.main()
