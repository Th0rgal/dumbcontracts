#!/usr/bin/env python3
"""Generate/check deterministic EVMYulLean adapter coverage report artifact.

Usage:
    python3 scripts/generate_evmyullean_adapter_report.py
    python3 scripts/generate_evmyullean_adapter_report.py --check
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from property_utils import ROOT

ADAPTER_FILE = (
    ROOT
    / "Compiler"
    / "Proofs"
    / "YulGeneration"
    / "Backends"
    / "EvmYulLeanAdapter.lean"
)
DEFAULT_OUTPUT = ROOT / "artifacts" / "evmyullean_adapter_report.json"

EXPECTED_EXPR_CASES = ["lit", "hex", "str", "ident", "call"]
EXPECTED_STMT_CASES = ["comment", "let_", "assign", "expr", "if_", "for_", "switch", "block", "funcDef"]

CASE_RE = re.compile(r"^\s*\|\s*\.([A-Za-z0-9_']+)")
GAP_RE = re.compile(r'\.error\s+"([^"]+)"')
EVAL_STUB_RE = re.compile(r"def\s+evalBuiltinCallViaEvmYulLean[\s\S]*?:\s*Option\s+Nat\s*:=\s*none")


def _extract_block(text: str, start_marker: str, end_marker: str) -> list[str]:
    start = text.find(start_marker)
    if start < 0:
        raise ValueError(f"Could not find block start marker: {start_marker}")
    end = text.find(end_marker, start)
    if end < 0:
        raise ValueError(f"Could not find block end marker: {end_marker}")
    return text[start:end].splitlines()


def _parse_cases(lines: list[str]) -> dict[str, str]:
    clauses: dict[str, list[str]] = {}
    current: str | None = None
    for line in lines:
        m = CASE_RE.match(line)
        if m:
            current = m.group(1)
            clauses.setdefault(current, [])
        if current is not None:
            clauses[current].append(line)

    result: dict[str, str] = {}
    for name, body_lines in clauses.items():
        body = "\n".join(body_lines)
        gaps = GAP_RE.findall(body)
        if not gaps:
            result[name] = "supported"
            continue
        if "pure (" in body and (".error" in body):
            result[name] = "partial"
            continue
        result[name] = "gap"
    return result


def _parse_gap_messages(lines: list[str]) -> dict[str, list[str]]:
    clauses: dict[str, list[str]] = {}
    current: str | None = None
    for line in lines:
        m = CASE_RE.match(line)
        if m:
            current = m.group(1)
            clauses.setdefault(current, [])
        if current is not None:
            clauses[current].append(line)

    messages: dict[str, list[str]] = {}
    for name, body_lines in clauses.items():
        body = "\n".join(body_lines)
        gaps = sorted(set(GAP_RE.findall(body)))
        if gaps:
            messages[name] = gaps
    return messages


def build_report() -> dict[str, object]:
    if not ADAPTER_FILE.exists():
        raise FileNotFoundError(f"Missing adapter file: {ADAPTER_FILE.relative_to(ROOT)}")

    text = ADAPTER_FILE.read_text(encoding="utf-8")
    expr_lines = _extract_block(text, "def lowerExpr", "partial def lowerStmts")
    stmt_lines = _extract_block(text, "partial def lowerStmt", "def lowerProgram")

    expr_status = _parse_cases(expr_lines)
    stmt_status = _parse_cases(stmt_lines)
    stmt_gap_messages = _parse_gap_messages(stmt_lines)

    missing_expr = sorted(set(EXPECTED_EXPR_CASES) - set(expr_status))
    missing_stmt = sorted(set(EXPECTED_STMT_CASES) - set(stmt_status))

    expr_supported = sorted(k for k, v in expr_status.items() if v == "supported")
    stmt_supported = sorted(k for k, v in stmt_status.items() if v == "supported")
    stmt_partial = sorted(k for k, v in stmt_status.items() if v == "partial")
    stmt_gaps = sorted(k for k, v in stmt_status.items() if v == "gap")

    eval_stub = EVAL_STUB_RE.search(text) is not None

    status = "ok"
    if missing_expr or missing_stmt or stmt_partial or stmt_gaps or eval_stub:
        status = "partial"

    return {
        "schema_version": 1,
        "adapter_file": str(ADAPTER_FILE.relative_to(ROOT)),
        "status": status,
        "expr_supported": expr_supported,
        "stmt_supported": stmt_supported,
        "stmt_partial": stmt_partial,
        "stmt_gaps": stmt_gaps,
        "stmt_gap_messages": stmt_gap_messages,
        "missing_expr_cases": missing_expr,
        "missing_stmt_cases": missing_stmt,
        "eval_builtin_via_evmyullean": "stub-none" if eval_stub else "implemented",
    }


def write_report(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Output artifact path (default: artifacts/evmyullean_adapter_report.json)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail if output artifact is missing or stale",
    )
    args = parser.parse_args()

    payload = build_report()
    rendered = json.dumps(payload, sort_keys=True, indent=2) + "\n"

    if args.check:
        if not args.output.exists():
            print(f"Missing adapter artifact: {args.output}", file=sys.stderr)
            return 1
        existing = args.output.read_text(encoding="utf-8")
        if existing != rendered:
            print(
                "EVMYulLean adapter report is stale. Regenerate with:\n"
                "  python3 scripts/generate_evmyullean_adapter_report.py",
                file=sys.stderr,
            )
            return 1
        print(f"EVMYulLean adapter report is up to date: {args.output}")
        return 0

    write_report(args.output, payload)
    print(f"Wrote EVMYulLean adapter report: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
