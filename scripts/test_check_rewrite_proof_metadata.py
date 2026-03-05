#!/usr/bin/env python3
from __future__ import annotations

import tempfile
import unittest
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_rewrite_proof_metadata as guard


class RewriteProofMetadataTests(unittest.TestCase):
    def _write_patch_rules(self, text: str) -> Path:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        path = Path(tmp.name) / "PatchRules.lean"
        path.write_text(text, encoding="utf-8")
        return path

    def test_accepts_non_empty_literal_and_alias_proof_refs(self) -> None:
        path = self._write_patch_rules(
            """
            def proofAlias : String := "Proofs.alias"

            def ruleA : ObjectPatchRule := {
              patchName := "a"
              proofId := "Proofs.a"
            }

            def ruleB : ObjectPatchRule := {
              patchName := "b"
              proofId := proofAlias
            }

            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              objectRules := [ruleA]
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              objectRules := [ruleB]
            }
            """
        )
        self.assertEqual(guard.check_active_object_rule_proofs(path), [])

    def test_rejects_empty_proof_id_literal(self) -> None:
        path = self._write_patch_rules(
            """
            def badRule : ObjectPatchRule := {
              patchName := "bad"
              proofId := ""
            }

            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              objectRules := []
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              objectRules := [badRule]
            }
            """
        )
        errors = guard.check_active_object_rule_proofs(path)
        self.assertTrue(any("unresolved or empty proofId token" in err for err in errors))

    def test_rejects_missing_object_rule_definition(self) -> None:
        path = self._write_patch_rules(
            """
            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              objectRules := []
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              objectRules := [missingRule]
            }
            """
        )
        errors = guard.check_active_object_rule_proofs(path)
        self.assertTrue(any("not defined as ObjectPatchRule" in err for err in errors))

    def test_rejects_unresolved_alias(self) -> None:
        path = self._write_patch_rules(
            """
            def badRule : ObjectPatchRule := {
              patchName := "bad"
              proofId := unknownAlias
            }

            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              objectRules := []
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              objectRules := [badRule]
            }
            """
        )
        errors = guard.check_active_object_rule_proofs(path)
        self.assertTrue(any("unresolved or empty proofId token" in err for err in errors))


if __name__ == "__main__":
    unittest.main()
