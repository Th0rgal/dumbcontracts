#!/usr/bin/env python3
"""Ensure foundry-patched workflow settings stay synchronized with docs."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from workflow_jobs import (
    extract_job_body,
    extract_literal_from_mapping_blocks,
    extract_run_commands_from_job_body,
)

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"
SCRIPTS_README = ROOT / "scripts" / "README.md"


def _extract_foundry_patched_job(text: str) -> str:
    return extract_job_body(text, "foundry-patched", VERIFY_YML)


def _extract_env_literal(job_body: str, name: str) -> str:
    return extract_literal_from_mapping_blocks(
        job_body, "env", name, source=VERIFY_YML, context="foundry-patched"
    )


def _extract_no_match_test_target(job_body: str) -> str:
    run_commands = extract_run_commands_from_job_body(
        job_body, source=VERIFY_YML, context="foundry-patched"
    )
    forge_lines = [cmd for cmd in run_commands if cmd.startswith("forge test")]
    if not forge_lines:
        raise ValueError(
            "Could not locate 'forge test --no-match-test \"...\"' in "
            f"foundry-patched job in {VERIFY_YML}"
        )
    if len(forge_lines) > 1:
        raise ValueError(
            "Found multiple forge test commands in foundry-patched job in "
            f"{VERIFY_YML}; keep a single command for deterministic checks"
        )
    m = re.match(r'^forge test --no-match-test "([^"]+)"\s*$', forge_lines[0])
    if not m:
        raise ValueError(
            "Could not parse '--no-match-test \"...\"' from foundry-patched "
            f"forge test command in {VERIFY_YML}: {forge_lines[0]!r}"
        )
    return m.group(1)


def _extract_readme_foundry_patched_line(text: str) -> str:
    m = re.search(r"^\*\*`foundry-patched`\*\*.*$", text, re.MULTILINE)
    if not m:
        raise ValueError(f"Could not locate foundry-patched summary line in {SCRIPTS_README}")
    return m.group(0)


def _extract_readme_seed(line: str) -> str:
    m = re.search(r"\(seed\s+(\d+),", line)
    if not m:
        raise ValueError(
            "Could not parse seed from scripts/README.md foundry-patched summary. "
            "Expected format containing '(seed <n>, ...)'"
        )
    return m.group(1)


def main() -> int:
    verify_text = VERIFY_YML.read_text(encoding="utf-8")
    readme_text = SCRIPTS_README.read_text(encoding="utf-8")

    job_body = _extract_foundry_patched_job(verify_text)
    workflow_seed = _extract_env_literal(job_body, "DIFFTEST_RANDOM_SEED")
    workflow_shard_count = _extract_env_literal(job_body, "DIFFTEST_SHARD_COUNT")
    workflow_shard_index = _extract_env_literal(job_body, "DIFFTEST_SHARD_INDEX")
    workflow_no_match = _extract_no_match_test_target(job_body)

    readme_line = _extract_readme_foundry_patched_line(readme_text)
    readme_seed = _extract_readme_seed(readme_line)
    readme_mentions_single_shard = "single shard" in readme_line
    readme_no_match = "`Random10000`" in readme_line

    errors: list[str] = []
    if workflow_seed != readme_seed:
        errors.append(
            "README foundry-patched seed differs from verify.yml DIFFTEST_RANDOM_SEED."
        )
    if workflow_shard_count != "1" or workflow_shard_index != "0":
        errors.append(
            "verify.yml foundry-patched must stay single-shard "
            "(DIFFTEST_SHARD_COUNT=1, DIFFTEST_SHARD_INDEX=0)."
        )
    if not readme_mentions_single_shard:
        errors.append(
            "README foundry-patched summary must mention single-shard mode."
        )
    if workflow_no_match != "Random10000":
        errors.append(
            "verify.yml foundry-patched must keep --no-match-test target as Random10000."
        )
    if not readme_no_match:
        errors.append(
            "README foundry-patched summary must mention no `Random10000`."
        )

    if errors:
        print("verify foundry-patched sync check failed:", file=sys.stderr)
        for err in errors:
            print(f"- {err}", file=sys.stderr)
        print(f"  verify.yml seed:             {workflow_seed}", file=sys.stderr)
        print(f"  README seed:                 {readme_seed}", file=sys.stderr)
        print(f"  verify.yml shard count/index {workflow_shard_count}/{workflow_shard_index}", file=sys.stderr)
        print(f"  verify.yml --no-match-test:  {workflow_no_match}", file=sys.stderr)
        print(f"  README mentions single shard: {readme_mentions_single_shard}", file=sys.stderr)
        print(f"  README mentions Random10000:  {readme_no_match}", file=sys.stderr)
        return 1

    print(
        "verify foundry-patched settings are synchronized across workflow/docs "
        f"(seed {workflow_seed}, single shard, no {workflow_no_match})."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
