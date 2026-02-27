#!/usr/bin/env python3
"""Ensure foundry shard configuration stays synchronized across workflow and docs."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from workflow_jobs import extract_job_body, extract_literal_from_mapping_blocks, parse_csv_ints

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"
SCRIPTS_README = ROOT / "scripts" / "README.md"


def _extract_foundry_job_body(text: str) -> str:
    return extract_job_body(text, "foundry", VERIFY_YML)


def _extract_verify_shard_indices(body: str) -> list[int]:
    m = re.search(r"^\s*shard_index:\s*\[(?P<csv>[^\]]+)\]\s*$", body, flags=re.MULTILINE)
    if not m:
        raise ValueError(f"Could not locate foundry matrix shard_index list in {VERIFY_YML}")
    return parse_csv_ints(m.group("csv"), VERIFY_YML)


def _extract_verify_shard_count(body: str) -> int:
    return int(
        extract_literal_from_mapping_blocks(
            body, "env", "DIFFTEST_SHARD_COUNT", source=VERIFY_YML, context="foundry"
        )
    )


def _extract_readme_foundry_summary(text: str) -> tuple[int, int]:
    m = re.search(
        r"^\*\*`foundry`\*\*\s+—\s+(?P<shards>\d+)-shard parallel Foundry tests with seed (?P<seed>\d+)\s*$",
        text,
        flags=re.MULTILINE,
    )
    if not m:
        raise ValueError(
            "Could not locate foundry CI summary line in "
            f"{SCRIPTS_README}"
        )
    return int(m.group("shards")), int(m.group("seed"))


def _extract_verify_seed(body: str) -> int:
    return int(
        extract_literal_from_mapping_blocks(
            body, "env", "DIFFTEST_RANDOM_SEED", source=VERIFY_YML, context="foundry"
        )
    )


def _fmt_indices(values: list[int]) -> str:
    return ", ".join(str(v) for v in values)


def main() -> int:
    verify_text = VERIFY_YML.read_text(encoding="utf-8")
    readme_text = SCRIPTS_README.read_text(encoding="utf-8")

    foundry_body = _extract_foundry_job_body(verify_text)
    shard_indices = _extract_verify_shard_indices(foundry_body)
    shard_count = _extract_verify_shard_count(foundry_body)
    verify_seed = _extract_verify_seed(foundry_body)
    readme_shards, readme_seed = _extract_readme_foundry_summary(readme_text)

    errors: list[str] = []
    if not shard_indices:
        errors.append("verify.yml foundry matrix shard_index list is empty.")
    if len(set(shard_indices)) != len(shard_indices):
        errors.append("verify.yml foundry matrix shard_index list has duplicates.")

    expected_indices = list(range(len(shard_indices)))
    if shard_indices != expected_indices:
        errors.append(
            "verify.yml foundry matrix shard_index list must be contiguous "
            f"0..N-1. got: [{_fmt_indices(shard_indices)}]"
        )

    if shard_count != len(shard_indices):
        errors.append(
            "verify.yml DIFFTEST_SHARD_COUNT differs from foundry matrix size. "
            f"count={shard_count}, matrix-size={len(shard_indices)}"
        )

    if readme_shards != len(shard_indices):
        errors.append(
            "scripts/README.md foundry shard summary differs from verify.yml foundry matrix size. "
            f"README={readme_shards}, matrix-size={len(shard_indices)}"
        )

    if readme_seed != verify_seed:
        errors.append(
            "scripts/README.md foundry seed summary differs from verify.yml DIFFTEST_RANDOM_SEED. "
            f"README={readme_seed}, verify.yml={verify_seed}"
        )

    if errors:
        print("verify foundry shard sync check failed:", file=sys.stderr)
        for err in errors:
            print(f"- {err}", file=sys.stderr)
        return 1

    print(
        "verify foundry shard config is synchronized across workflow/docs "
        f"({len(shard_indices)} shards, seed {verify_seed})."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
