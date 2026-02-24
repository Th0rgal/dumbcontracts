#!/usr/bin/env python3
"""Ensure multi-seed lists stay synchronized across workflow, script, and docs."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from workflow_jobs import extract_job_body

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"
MULTISEED_SCRIPT = ROOT / "scripts" / "test_multiple_seeds.sh"
SCRIPTS_README = ROOT / "scripts" / "README.md"


def _parse_seed_csv(raw: str, source: Path) -> list[int]:
    items = [part.strip() for part in raw.split(",")]
    if not items or any(not item for item in items):
        raise ValueError(f"Malformed seed list in {source}: {raw!r}")
    try:
        return [int(item) for item in items]
    except ValueError as exc:
        raise ValueError(f"Non-integer seed in {source}: {raw!r}") from exc


def _line_indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def _is_substantive_line(line: str) -> bool:
    stripped = line.strip()
    return bool(stripped) and not stripped.startswith("#")


def _find_block_end(lines: list[str], start_idx: int, parent_indent: int) -> int:
    for idx in range(start_idx + 1, len(lines)):
        line = lines[idx]
        if not _is_substantive_line(line):
            continue
        if _line_indent(line) <= parent_indent:
            return idx
    return len(lines)


def _find_key_line(
    lines: list[str],
    key: str,
    *,
    start_idx: int,
    end_idx: int,
    required_indent: int,
    source: Path,
) -> tuple[int, str]:
    key_prefix = f"{key}:"
    for idx in range(start_idx, end_idx):
        line = lines[idx]
        if not _is_substantive_line(line):
            continue
        if _line_indent(line) != required_indent:
            continue
        stripped = line.strip()
        if stripped.startswith(key_prefix):
            return idx, stripped[len(key_prefix) :].strip()
    raise ValueError(f"Could not locate '{key}' in {source}")


def _parse_seed_block_list(lines: list[str], source: Path, *, seed_idx: int, seed_indent: int) -> list[int]:
    end_idx = _find_block_end(lines, seed_idx, seed_indent)
    expected_item_indent = seed_indent + 2
    values: list[int] = []
    for idx in range(seed_idx + 1, end_idx):
        line = lines[idx]
        if not _is_substantive_line(line):
            continue
        if _line_indent(line) != expected_item_indent:
            raise ValueError(f"Malformed seed list indentation in {source}")
        stripped = line.strip()
        if not stripped.startswith("- "):
            raise ValueError(f"Malformed seed list item in {source}: {stripped!r}")
        token = stripped[2:].strip()
        if not token:
            raise ValueError(f"Empty seed list item in {source}")
        try:
            values.append(int(token))
        except ValueError as exc:
            raise ValueError(f"Non-integer seed in {source}: {token!r}") from exc
    if not values:
        raise ValueError(f"Empty seed list in {source}")
    return values


def _extract_verify_seeds(text: str) -> list[int]:
    job_body = extract_job_body(text, "foundry-multi-seed", VERIFY_YML)
    lines = job_body.splitlines()
    root_indents = [_line_indent(line) for line in lines if _is_substantive_line(line)]
    if not root_indents:
        raise ValueError(f"Could not parse foundry-multi-seed job body in {VERIFY_YML}")
    root_indent = min(root_indents)

    strategy_idx, _ = _find_key_line(
        lines,
        "strategy",
        start_idx=0,
        end_idx=len(lines),
        required_indent=root_indent,
        source=VERIFY_YML,
    )
    strategy_end = _find_block_end(lines, strategy_idx, root_indent)

    matrix_idx, _ = _find_key_line(
        lines,
        "matrix",
        start_idx=strategy_idx + 1,
        end_idx=strategy_end,
        required_indent=root_indent + 2,
        source=VERIFY_YML,
    )
    matrix_end = _find_block_end(lines, matrix_idx, root_indent + 2)

    seed_idx, seed_rest = _find_key_line(
        lines,
        "seed",
        start_idx=matrix_idx + 1,
        end_idx=matrix_end,
        required_indent=root_indent + 4,
        source=VERIFY_YML,
    )
    if seed_rest:
        m = re.fullmatch(r"\[(?P<csv>[^\]]+)\]", seed_rest)
        if not m:
            raise ValueError(f"Malformed matrix seed list in {VERIFY_YML}: {seed_rest!r}")
        return _parse_seed_csv(m.group("csv"), VERIFY_YML)
    return _parse_seed_block_list(lines, VERIFY_YML, seed_idx=seed_idx, seed_indent=root_indent + 4)


def _extract_script_seeds(text: str) -> list[int]:
    m = re.search(r"^DEFAULT_SEEDS=\((?P<vals>[^)]+)\)\s*$", text, re.MULTILINE)
    if not m:
        raise ValueError(f"Could not locate DEFAULT_SEEDS in {MULTISEED_SCRIPT}")
    raw_tokens = m.group("vals").split()
    if not raw_tokens:
        raise ValueError(f"DEFAULT_SEEDS is empty in {MULTISEED_SCRIPT}")
    try:
        return [int(token) for token in raw_tokens]
    except ValueError as exc:
        raise ValueError(f"Non-integer DEFAULT_SEEDS value in {MULTISEED_SCRIPT}") from exc


def _extract_readme_seeds(text: str) -> list[int]:
    line = re.search(
        r"^\*\*`foundry-multi-seed`\*\*.*\(seeds:\s*(?P<csv>[^)]+)\)\s*$",
        text,
        flags=re.MULTILINE,
    )
    if not line:
        raise ValueError(
            "Could not locate foundry-multi-seed seeds summary in "
            f"{SCRIPTS_README}"
        )
    return _parse_seed_csv(line.group("csv"), SCRIPTS_README)


def _fmt(seeds: list[int]) -> str:
    return ", ".join(str(seed) for seed in seeds)


def main() -> int:
    try:
        verify_text = VERIFY_YML.read_text(encoding="utf-8")
        script_text = MULTISEED_SCRIPT.read_text(encoding="utf-8")
        readme_text = SCRIPTS_README.read_text(encoding="utf-8")

        verify_seeds = _extract_verify_seeds(verify_text)
        script_seeds = _extract_script_seeds(script_text)
        readme_seeds = _extract_readme_seeds(readme_text)
    except ValueError as exc:
        print(f"verify multi-seed sync check failed: {exc}", file=sys.stderr)
        return 1

    errors: list[str] = []
    if script_seeds != verify_seeds:
        errors.append(
            "scripts/test_multiple_seeds.sh DEFAULT_SEEDS differs from "
            "verify.yml foundry-multi-seed matrix."
        )
    if readme_seeds != verify_seeds:
        errors.append(
            "scripts/README.md foundry-multi-seed seeds summary differs from "
            "verify.yml foundry-multi-seed matrix."
        )

    if errors:
        print("verify multi-seed sync check failed:", file=sys.stderr)
        for err in errors:
            print(f"- {err}", file=sys.stderr)
        print(f"  verify.yml seeds: {_fmt(verify_seeds)}", file=sys.stderr)
        print(f"  script seeds:     {_fmt(script_seeds)}", file=sys.stderr)
        print(f"  README seeds:     {_fmt(readme_seeds)}", file=sys.stderr)
        return 1

    print(
        "verify multi-seed lists are synchronized across workflow/script/docs "
        f"({len(verify_seeds)} seeds)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
