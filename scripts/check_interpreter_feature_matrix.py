#!/usr/bin/env python3
"""Validate interpreter_feature_matrix.json structure and cross-check builtins.

Checks:
  1. Schema version and required top-level keys.
  2. Every expr/stmt feature has valid status values.
  3. Builtin bridge entries are consistent with evmyullean_capability_report.json:
     all builtins listed as 'supported' in the bridge must appear in the
     capability report's allowed_overlap_builtins list.
  4. Proof status values are from the documented legend.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MATRIX = ROOT / "artifacts" / "interpreter_feature_matrix.json"
CAPABILITY = ROOT / "artifacts" / "evmyullean_capability_report.json"

VALID_STATUSES = {"supported", "unsupported", "fallback_zero", "no_op", "delegated", "n/a"}
VALID_PROOF_STATUSES = {"proved", "assumed", "partial", "not_modeled"}


def main() -> int:
    errors: list[str] = []

    # Load matrix
    if not MATRIX.exists():
        print(f"FAIL: {MATRIX} not found", file=sys.stderr)
        return 1
    with open(MATRIX) as f:
        matrix = json.load(f)

    # 1. Schema check
    if matrix.get("schema_version") != 1:
        errors.append(f"Expected schema_version 1, got {matrix.get('schema_version')}")

    for key in ("interpreters", "expr_features", "stmt_features", "builtin_features",
                "status_legend", "proof_status_legend", "default_execution_path"):
        if key not in matrix:
            errors.append(f"Missing top-level key: {key}")

    # 2. Validate feature statuses
    interpreter_keys = [
        "SpecInterpreter_basic", "SpecInterpreter_fuel", "IRInterpreter", "EVMYulLean_bridge"
    ]
    for feat in matrix.get("expr_features", []):
        name = feat.get("feature", "?")
        for ik in interpreter_keys:
            val = feat.get(ik)
            if val is not None and val not in VALID_STATUSES:
                errors.append(f"expr_features[{name}].{ik}: invalid status '{val}'")
        ps = feat.get("proof_status")
        if ps and ps not in VALID_PROOF_STATUSES:
            errors.append(f"expr_features[{name}].proof_status: invalid '{ps}'")

    stmt_interpreter_keys = ["SpecInterpreter_basic", "SpecInterpreter_fuel", "IRInterpreter"]
    for feat in matrix.get("stmt_features", []):
        name = feat.get("feature", "?")
        for ik in stmt_interpreter_keys:
            val = feat.get(ik)
            if val is not None and val not in VALID_STATUSES:
                errors.append(f"stmt_features[{name}].{ik}: invalid status '{val}'")
        ps = feat.get("proof_status")
        if ps and ps not in VALID_PROOF_STATUSES:
            errors.append(f"stmt_features[{name}].proof_status: invalid '{ps}'")

    # 3. Cross-check builtin bridge against capability report
    if CAPABILITY.exists():
        with open(CAPABILITY) as f:
            cap = json.load(f)
        allowed = set(cap.get("allowed_overlap_builtins", []))
        helpers = set(cap.get("allowed_verity_helpers", []))

        for bf in matrix.get("builtin_features", []):
            name = bf.get("feature", "?")
            bridge = bf.get("evmyullean_bridge")
            verity = bf.get("verity_path")

            if bridge == "supported" and name not in allowed:
                errors.append(
                    f"builtin_features[{name}]: bridge='supported' but "
                    f"not in capability_report.allowed_overlap_builtins"
                )
            if bridge == "delegated" and name not in allowed and name not in helpers:
                # Delegated builtins should be either in allowed list or helpers list
                errors.append(
                    f"builtin_features[{name}]: bridge='delegated' but "
                    f"not in allowed_overlap or allowed_verity_helpers"
                )
    else:
        print(f"  WARNING: {CAPABILITY} not found, skipping cross-check", file=sys.stderr)

    # 4. Check counts are reasonable
    expr_count = len(matrix.get("expr_features", []))
    stmt_count = len(matrix.get("stmt_features", []))
    builtin_count = len(matrix.get("builtin_features", []))

    if expr_count < 10:
        errors.append(f"Only {expr_count} expr features — expected >= 10")
    if stmt_count < 10:
        errors.append(f"Only {stmt_count} stmt features — expected >= 10")
    if builtin_count < 15:
        errors.append(f"Only {builtin_count} builtin features — expected >= 15")

    # Report
    if errors:
        print(f"FAIL: {len(errors)} error(s) in interpreter_feature_matrix.json:",
              file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 1

    print(f"ok: interpreter_feature_matrix.json "
          f"({expr_count} expr, {stmt_count} stmt, {builtin_count} builtin features)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
