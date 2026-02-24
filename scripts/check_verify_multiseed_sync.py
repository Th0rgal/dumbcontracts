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


def _extract_verify_seeds(text: str) -> list[int]:
    job_body = extract_job_body(text, "foundry-multi-seed", VERIFY_YML)
    seed_line = re.search(r"^\s*seed:\s*\[(?P<csv>[^\]]+)\]\s*$", job_body, re.MULTILINE)
    if not seed_line:
        raise ValueError(f"Could not locate matrix seed list in {VERIFY_YML}")
    return _parse_seed_csv(seed_line.group("csv"), VERIFY_YML)


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
    verify_text = VERIFY_YML.read_text(encoding="utf-8")
    script_text = MULTISEED_SCRIPT.read_text(encoding="utf-8")
    readme_text = SCRIPTS_README.read_text(encoding="utf-8")

    verify_seeds = _extract_verify_seeds(verify_text)
    script_seeds = _extract_script_seeds(script_text)
    readme_seeds = _extract_readme_seeds(readme_text)

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
