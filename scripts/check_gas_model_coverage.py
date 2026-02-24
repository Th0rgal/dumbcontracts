#!/usr/bin/env python3
"""Ensure static gas builtin coverage matches generated Yul call sites."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from property_utils import ROOT

STATIC_ANALYSIS = ROOT / "Compiler" / "Gas" / "StaticAnalysis.lean"
DEFAULT_YUL_DIR = ROOT / "generated" / "yul"

FUNCTION_DEF_RE = re.compile(r"\bfunction\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(")
CALL_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")
MODELED_CALL_RE = re.compile(r'name\s*=\s*"([A-Za-z_][A-Za-z0-9_]*)"')

NON_CALL_KEYWORDS = {"function", "if", "switch", "object", "code"}


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--dir",
        dest="dirs",
        action="append",
        default=[],
        help="Yul directory to scan (repeatable). Default: generated/yul",
    )
    return parser.parse_args(argv)


def load_modeled_calls() -> set[str]:
    text = STATIC_ANALYSIS.read_text(encoding="utf-8")
    return set(MODELED_CALL_RE.findall(text))


def strip_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    text = re.sub(r"//.*", "", text)
    return text


def normalize_scan_dirs(raw_dirs: list[str]) -> list[Path]:
    if not raw_dirs:
        return [DEFAULT_YUL_DIR]
    scan_dirs: list[Path] = []
    for raw in raw_dirs:
        path = Path(raw)
        if not path.is_absolute():
            path = ROOT / path
        scan_dirs.append(path)
    return scan_dirs


def collect_yul_calls(scan_dirs: list[Path]) -> set[str]:
    calls: set[str] = set()
    for scan_dir in scan_dirs:
        for yul_path in sorted(scan_dir.glob("*.yul")):
            source = strip_comments(yul_path.read_text(encoding="utf-8"))
            function_names = set(FUNCTION_DEF_RE.findall(source))
            for line in source.splitlines():
                clean = line.strip()
                for match in CALL_RE.finditer(clean):
                    name = match.group(1)
                    if name in NON_CALL_KEYWORDS or name in function_names:
                        continue
                    calls.add(name)
    return calls


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    scan_dirs = normalize_scan_dirs(args.dirs)

    if not STATIC_ANALYSIS.exists():
        print(f"ERROR: missing {STATIC_ANALYSIS}", file=sys.stderr)
        return 1
    for scan_dir in scan_dirs:
        if not scan_dir.exists():
            print(f"ERROR: missing {scan_dir}", file=sys.stderr)
            return 1

    modeled = load_modeled_calls()
    emitted = collect_yul_calls(scan_dirs)

    missing = sorted(emitted - modeled)
    if missing:
        print("ERROR: Static gas model is missing emitted Yul calls:", file=sys.stderr)
        for name in missing:
            print(f"  - {name}", file=sys.stderr)
        return 1

    scanned = ", ".join(str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p) for p in scan_dirs)
    print(f"OK: static gas model covers all emitted Yul calls ({len(emitted)} names) across: {scanned}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
