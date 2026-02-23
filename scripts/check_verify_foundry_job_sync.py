#!/usr/bin/env python3
"""Ensure foundry workflow jobs keep critical shared settings synchronized."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"


def _extract_job_body(text: str, job: str) -> str:
    section = re.search(
        rf"^  {re.escape(job)}:\n(?P<body>.*?)(?:^  [A-Za-z0-9_-]+:|\Z)",
        text,
        flags=re.MULTILINE | re.DOTALL,
    )
    if not section:
        raise ValueError(f"Could not locate {job} job in {VERIFY_YML}")
    return section.group("body")


def _extract_env_literal(job_body: str, name: str, job: str) -> str:
    m = re.search(rf"^\s*{re.escape(name)}:\s*([^\n#]+?)\s*$", job_body, re.MULTILINE)
    if not m:
        raise ValueError(f"Could not locate {name} in {job} env block in {VERIFY_YML}")
    raw = m.group(1).strip()
    if len(raw) >= 2 and raw[0] == raw[-1] and raw[0] in {'"', "'"}:
        return raw[1:-1]
    return raw


def _extract_download(job_body: str, artifact_name: str, job: str) -> tuple[str, str]:
    step = re.search(
        rf"^\s*- name:\s+Download\s+{re.escape(artifact_name)}\n"
        r"(?P<body>.*?)(?:^\s*- name:|\Z)",
        job_body,
        flags=re.MULTILINE | re.DOTALL,
    )
    if not step:
        raise ValueError(
            f"Could not locate '{artifact_name}' download step in {job} job in {VERIFY_YML}"
        )

    name = re.search(r"^\s*name:\s*([^\s][^\n]*)\s*$", step.group("body"), re.MULTILINE)
    if not name:
        raise ValueError(
            f"Could not locate download artifact name in {job} job for {artifact_name} in {VERIFY_YML}"
        )

    path = re.search(r"^\s*path:\s*([^\s][^\n]*)\s*$", step.group("body"), re.MULTILINE)
    if not path:
        raise ValueError(
            f"Could not locate download artifact path in {job} job for {artifact_name} in {VERIFY_YML}"
        )

    return name.group(1).strip(), path.group(1).strip()


def _extract_forge_line(job_body: str, job: str) -> str:
    m = re.search(r"^\s*forge test[^\n]*$", job_body, flags=re.MULTILINE)
    if not m:
        raise ValueError(f"Could not locate 'forge test' command in {job} job in {VERIFY_YML}")
    return m.group(0).strip()


def main() -> int:
    verify_text = VERIFY_YML.read_text(encoding="utf-8")

    foundry_body = _extract_job_body(verify_text, "foundry")
    patched_body = _extract_job_body(verify_text, "foundry-patched")
    multiseed_body = _extract_job_body(verify_text, "foundry-multi-seed")

    foundry_profile = _extract_env_literal(foundry_body, "FOUNDRY_PROFILE", "foundry")
    patched_profile = _extract_env_literal(patched_body, "FOUNDRY_PROFILE", "foundry-patched")
    multiseed_profile = _extract_env_literal(multiseed_body, "FOUNDRY_PROFILE", "foundry-multi-seed")

    foundry_small = _extract_env_literal(foundry_body, "DIFFTEST_RANDOM_SMALL", "foundry")
    patched_small = _extract_env_literal(patched_body, "DIFFTEST_RANDOM_SMALL", "foundry-patched")
    multiseed_small = _extract_env_literal(multiseed_body, "DIFFTEST_RANDOM_SMALL", "foundry-multi-seed")

    foundry_large = _extract_env_literal(foundry_body, "DIFFTEST_RANDOM_LARGE", "foundry")
    patched_large = _extract_env_literal(patched_body, "DIFFTEST_RANDOM_LARGE", "foundry-patched")
    multiseed_large = _extract_env_literal(multiseed_body, "DIFFTEST_RANDOM_LARGE", "foundry-multi-seed")

    foundry_yul_dir = _extract_env_literal(foundry_body, "DIFFTEST_YUL_DIR", "foundry")
    patched_yul_dir = _extract_env_literal(patched_body, "DIFFTEST_YUL_DIR", "foundry-patched")
    multiseed_yul_dir = _extract_env_literal(multiseed_body, "DIFFTEST_YUL_DIR", "foundry-multi-seed")

    foundry_artifact_name, foundry_artifact_path = _extract_download(foundry_body, "generated Yul", "foundry")
    patched_artifact_name, patched_artifact_path = _extract_download(
        patched_body, "patched Yul", "foundry-patched"
    )
    multiseed_artifact_name, multiseed_artifact_path = _extract_download(
        multiseed_body, "generated Yul", "foundry-multi-seed"
    )

    foundry_cmd = _extract_forge_line(foundry_body, "foundry")
    patched_cmd = _extract_forge_line(patched_body, "foundry-patched")
    multiseed_cmd = _extract_forge_line(multiseed_body, "foundry-multi-seed")

    errors: list[str] = []

    profiles = {foundry_profile, patched_profile, multiseed_profile}
    if profiles != {"difftest"}:
        errors.append(
            "foundry job FOUNDRY_PROFILE must be synchronized to 'difftest' across foundry/foundry-patched/foundry-multi-seed."
        )

    if not (foundry_small == patched_small == multiseed_small):
        errors.append(
            "DIFFTEST_RANDOM_SMALL must match across foundry/foundry-patched/foundry-multi-seed."
        )

    if not (foundry_large == patched_large == multiseed_large):
        errors.append(
            "DIFFTEST_RANDOM_LARGE must match across foundry/foundry-patched/foundry-multi-seed."
        )

    if foundry_artifact_name != "generated-yul" or multiseed_artifact_name != "generated-yul":
        errors.append(
            "foundry and foundry-multi-seed must download the 'generated-yul' artifact."
        )

    if patched_artifact_name != "generated-yul-patched":
        errors.append("foundry-patched must download the 'generated-yul-patched' artifact.")

    if foundry_artifact_path != foundry_yul_dir:
        errors.append(
            "foundry DIFFTEST_YUL_DIR must equal its generated Yul download path."
        )

    if multiseed_artifact_path != multiseed_yul_dir:
        errors.append(
            "foundry-multi-seed DIFFTEST_YUL_DIR must equal its generated Yul download path."
        )

    if patched_artifact_path != patched_yul_dir:
        errors.append(
            "foundry-patched DIFFTEST_YUL_DIR must equal its patched Yul download path."
        )

    if foundry_yul_dir != multiseed_yul_dir:
        errors.append(
            "foundry and foundry-multi-seed must use the same DIFFTEST_YUL_DIR for baseline comparisons."
        )

    if "--no-match-test" in foundry_cmd:
        errors.append("foundry baseline job must not use --no-match-test filtering.")

    if '--no-match-test "Random10000"' not in patched_cmd:
        errors.append(
            "foundry-patched job must keep '--no-match-test \"Random10000\"'."
        )

    if '--no-match-test "Random10000"' not in multiseed_cmd:
        errors.append(
            "foundry-multi-seed job must keep '--no-match-test \"Random10000\"'."
        )

    if errors:
        print("verify foundry job sync check failed:", file=sys.stderr)
        for err in errors:
            print(f"- {err}", file=sys.stderr)
        return 1

    print(
        "verify foundry job settings are synchronized "
        f"(profile={foundry_profile}, random_small={foundry_small}, random_large={foundry_large})."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
