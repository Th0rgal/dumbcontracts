#!/usr/bin/env python3

from __future__ import annotations

import tempfile
import unittest
from unittest import mock
from pathlib import Path

import check_macro_property_test_generation as check


class MacroPropertyGenerationCheckTests(unittest.TestCase):
    def test_check_fails_when_artifacts_missing(self) -> None:
        with tempfile.TemporaryDirectory(dir=check.ROOT) as tmpdir:
            root = Path(tmpdir)
            source = root / "MacroContracts.lean"
            out_dir = root / "artifacts"
            source.write_text(
                "verity_contract Counter where\n"
                "  function ping () : Unit := do\n"
                "    pure ()\n",
                encoding="utf-8",
            )

            expected = check._expected_rendered([source], None)
            rc = check._check(out_dir, expected)
            self.assertEqual(rc, 1)

    def test_write_then_check_passes(self) -> None:
        with tempfile.TemporaryDirectory(dir=check.ROOT) as tmpdir:
            root = Path(tmpdir)
            source = root / "MacroContracts.lean"
            out_dir = root / "artifacts"
            source.write_text(
                "verity_contract Counter where\n"
                "  function ping () : Unit := do\n"
                "    pure ()\n",
                encoding="utf-8",
            )

            expected = check._expected_rendered([source], None)
            self.assertEqual(check._write(out_dir, expected), 0)
            self.assertEqual(check._check(out_dir, expected), 0)

    def test_check_detects_stale_content(self) -> None:
        with tempfile.TemporaryDirectory(dir=check.ROOT) as tmpdir:
            root = Path(tmpdir)
            source = root / "MacroContracts.lean"
            out_dir = root / "artifacts"
            source.write_text(
                "verity_contract Counter where\n"
                "  function ping () : Unit := do\n"
                "    pure ()\n",
                encoding="utf-8",
            )
            expected = check._expected_rendered([source], None)
            self.assertEqual(check._write(out_dir, expected), 0)

            artifact = out_dir / "PropertyCounter.t.sol"
            artifact.write_text(artifact.read_text(encoding="utf-8") + "\n// stale\n", encoding="utf-8")

            self.assertEqual(check._check(out_dir, expected), 1)

    def test_main_discovers_nested_macro_contract_sources(self) -> None:
        with tempfile.TemporaryDirectory(dir=check.ROOT) as tmpdir:
            root = Path(tmpdir)
            macro_dir = root / "Contracts" / "MacroContracts"
            (macro_dir / "Compat").mkdir(parents=True, exist_ok=True)
            (macro_dir / "Compat" / "Nested.lean").write_text(
                "verity_contract NestedCounter where\n"
                "  function ping () : Unit := do\n"
                "    pure ()\n",
                encoding="utf-8",
            )

            out_dir = root / "artifacts"
            old_source = check.DEFAULT_SOURCE
            old_source_dir = check.DEFAULT_SOURCE_DIR
            old_output_dir = check.DEFAULT_OUTPUT_DIR
            check.DEFAULT_SOURCE = macro_dir / "Core.lean"
            check.DEFAULT_SOURCE_DIR = macro_dir
            check.DEFAULT_OUTPUT_DIR = out_dir
            try:
                out_rel = out_dir.relative_to(check.ROOT)
                with mock.patch(
                    "sys.argv",
                    [
                        "check_macro_property_test_generation.py",
                        "--output-dir",
                        str(out_rel),
                    ],
                ):
                    self.assertEqual(check.main(), 0)
            finally:
                check.DEFAULT_SOURCE = old_source
                check.DEFAULT_SOURCE_DIR = old_source_dir
                check.DEFAULT_OUTPUT_DIR = old_output_dir

            self.assertTrue((out_dir / "PropertyNestedCounter.t.sol").exists())


if __name__ == "__main__":
    unittest.main()
