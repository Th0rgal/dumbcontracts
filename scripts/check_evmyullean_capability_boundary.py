#!/usr/bin/env python3
"""Enforce EVMYulLean capability boundary for centralized Yul builtins.

Issue #294 tracks replacing hand-rolled semantics with EVMYulLean. This check
keeps `Compiler/Proofs/YulGeneration/Builtins.lean` within an explicitly
supported builtin surface so migration cannot silently expand into unsupported
operations.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BUILTINS_FILE = ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Builtins.lean"

BUILTIN_NAME_RE = re.compile(r'func\s*=\s*"([^"]+)"')

# Builtins currently modeled as part of the overlap subset for planned
# EVMYulLean-backed semantics.
EVMYULLEAN_OVERLAP_BUILTINS = {
    "add",
    "and",
    "calldataload",
    "caller",
    "div",
    "eq",
    "gt",
    "iszero",
    "lt",
    "mod",
    "mul",
    "not",
    "or",
    "shl",
    "shr",
    "sload",
    "sub",
    "xor",
}

# Verity-level helper kept outside upstream Yul builtin set.
VERITY_HELPER_BUILTINS = {"mappingSlot"}

# Explicitly unsupported in the planned EVMYulLean-backed path (per #294
# research notes). Presence here in Builtins.lean should block CI.
EVMYULLEAN_UNSUPPORTED_BUILTINS = {
    "create",
    "create2",
    "extcodecopy",
    "extcodehash",
    "extcodesize",
}


def main() -> int:
    if not BUILTINS_FILE.exists():
        print(
            f"EVMYulLean capability boundary check failed: missing {BUILTINS_FILE.relative_to(ROOT)}",
            file=sys.stderr,
        )
        return 1

    text = BUILTINS_FILE.read_text(encoding="utf-8")
    found = set(BUILTIN_NAME_RE.findall(text))

    allowed = EVMYULLEAN_OVERLAP_BUILTINS | VERITY_HELPER_BUILTINS

    errors: list[str] = []

    unsupported_present = sorted(found & EVMYULLEAN_UNSUPPORTED_BUILTINS)
    if unsupported_present:
        errors.append(
            "contains EVMYulLean-unsupported builtins: " + ", ".join(unsupported_present)
        )

    unknown = sorted(found - allowed)
    if unknown:
        errors.append(
            "introduces builtins outside capability boundary: " + ", ".join(unknown)
        )

    if errors:
        print("EVMYulLean capability boundary check failed:", file=sys.stderr)
        print(f"  - file: {BUILTINS_FILE.relative_to(ROOT)}", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        print(
            "  - action: keep unsupported builtins in legacy fallback semantics, "
            "or update #294 capability matrix with proof/test justification",
            file=sys.stderr,
        )
        return 1

    print("✓ EVMYulLean capability boundary is enforced")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
