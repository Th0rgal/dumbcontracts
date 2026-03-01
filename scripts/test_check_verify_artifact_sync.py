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

import check_verify_artifact_sync


class VerifyArtifactSyncTests(unittest.TestCase):
    def _run_main(self, workflow_body: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as d:
            wf = Path(d) / "verify.yml"
            wf.write_text(workflow_body, encoding="utf-8")
            old_verify = check_verify_artifact_sync.VERIFY_YML
            check_verify_artifact_sync.VERIFY_YML = wf
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    try:
                        rc = check_verify_artifact_sync.main()
                        return rc, stderr.getvalue()
                    except Exception as exc:
                        print(str(exc), file=sys.stderr)
                        return 1, stderr.getvalue()
            finally:
                check_verify_artifact_sync.VERIFY_YML = old_verify

    def test_extract_names_supports_non_first_name_key(self) -> None:
        body = textwrap.dedent(
            """
                  - name: Upload generated Yul
                    uses: actions/upload-artifact@v4
                    with:
                      path: artifacts/out.txt
                      name: generated-yul
                  - name: Download generated Yul
                    uses: actions/download-artifact@v4
                    with:
                      path: artifacts
                      name: generated-yul
            """
        )
        self.assertEqual(
            check_verify_artifact_sync._extract_upload_names(body),
            ["generated-yul"],
        )
        self.assertEqual(
            check_verify_artifact_sync._extract_download_names(body),
            ["generated-yul"],
        )

    def test_rejects_download_step_without_name(self) -> None:
        body = textwrap.dedent(
            """
                  - uses: actions/download-artifact@v4
                    with:
                      path: artifacts
            """
        )
        with self.assertRaisesRegex(ValueError, "download-artifact step"):
            check_verify_artifact_sync._extract_download_names(body)

    def test_main_supports_non_first_name_key(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on: {}
            jobs:
              build:
                runs-on: ubuntu-latest
                steps:
                  - name: Upload generated Yul
                    uses: actions/upload-artifact@v4
                    with:
                      path: artifacts/generated
                      name: generated-yul
              foundry:
                runs-on: ubuntu-latest
                steps:
                  - name: Download generated Yul
                    uses: actions/download-artifact@v4
                    with:
                      path: artifacts/generated
                      name: generated-yul
            """
        )
        rc, stderr = self._run_main(workflow)
        self.assertEqual(rc, 0, stderr)

    def test_main_supports_split_producer_jobs(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on: {}
            jobs:
              build:
                runs-on: ubuntu-latest
                steps:
                  - name: Upload axiom report
                    uses: actions/upload-artifact@v4
                    with:
                      name: axiom-report
                      path: axiom-report.md
              build-compiler:
                runs-on: ubuntu-latest
                steps:
                  - name: Upload generated Yul
                    uses: actions/upload-artifact@v4
                    with:
                      name: generated-yul
                      path: compiler/yul
              foundry:
                runs-on: ubuntu-latest
                steps:
                  - name: Download generated Yul
                    uses: actions/download-artifact@v4
                    with:
                      name: generated-yul
                      path: compiler/yul
            """
        )
        rc, stderr = self._run_main(workflow)
        self.assertEqual(rc, 0, stderr)

    def test_main_rejects_missing_artifact_in_split(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on: {}
            jobs:
              build:
                runs-on: ubuntu-latest
                steps:
                  - name: Upload axiom report
                    uses: actions/upload-artifact@v4
                    with:
                      name: axiom-report
                      path: axiom-report.md
              build-compiler:
                runs-on: ubuntu-latest
                steps:
                  - name: Upload generated Yul
                    uses: actions/upload-artifact@v4
                    with:
                      name: generated-yul
                      path: compiler/yul
              foundry:
                runs-on: ubuntu-latest
                steps:
                  - name: Download missing artifact
                    uses: actions/download-artifact@v4
                    with:
                      name: no-such-artifact
                      path: missing
            """
        )
        rc, stderr = self._run_main(workflow)
        self.assertEqual(rc, 1)
        self.assertIn("no-such-artifact", stderr)


if __name__ == "__main__":
    unittest.main()
