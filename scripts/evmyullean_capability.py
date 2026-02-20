"""Shared EVMYulLean capability boundary definitions for CI checks/artifacts."""

from __future__ import annotations

import re
from pathlib import Path

from property_utils import ROOT

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


def extract_found_builtins(builtins_file: Path = BUILTINS_FILE) -> set[str]:
    """Extract builtin names from Builtins.lean."""
    text = builtins_file.read_text(encoding="utf-8")
    return set(BUILTIN_NAME_RE.findall(text))

