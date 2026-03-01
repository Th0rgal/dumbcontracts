#!/usr/bin/env python3

from __future__ import annotations

import tempfile
import unittest
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


if __name__ == "__main__":
    unittest.main()
