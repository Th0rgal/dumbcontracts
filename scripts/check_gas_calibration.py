#!/usr/bin/env python3
"""Cross-check static runtime gas bounds against Foundry gas measurements."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_FOUNDRY_PATH_GLOB = "test/yul/*.t.sol"
# Slightly above intrinsic transaction base to absorb calldata overhead in Foundry calls.
TX_BASE_GAS = 22000

STATIC_HEADER = "contract\tdeploy_upper_bound\truntime_upper_bound\ttotal_upper_bound"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--static-report",
        type=Path,
        default=None,
        help="Path to precomputed `lake exe gas-report` output. If omitted, runs `lake exe gas-report`.",
    )
    parser.add_argument(
        "--match-path",
        default=DEFAULT_FOUNDRY_PATH_GLOB,
        help="Foundry --match-path pattern used when collecting gas report.",
    )
    parser.add_argument(
        "--tx-base-gas",
        type=int,
        default=TX_BASE_GAS,
        help="Fixed call overhead added when comparing static runtime upper bound to Foundry call gas.",
    )
    return parser.parse_args()


def run_command(cmd: list[str], env: dict[str, str] | None = None) -> str:
    proc = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
        env=env,
    )
    if proc.returncode != 0:
        if proc.stdout:
            sys.stderr.write(proc.stdout)
        if proc.stderr:
            sys.stderr.write(proc.stderr)
        raise RuntimeError(f"`{' '.join(cmd)}` failed with exit code {proc.returncode}")
    return proc.stdout


def load_static_runtime_bounds(path: Path | None) -> dict[str, int]:
    if path is None:
        stdout = run_command(["lake", "exe", "gas-report"])
    else:
        stdout = path.read_text(encoding="utf-8")

    lines = [line.strip() for line in stdout.splitlines() if line.strip()]
    if len(lines) < 4:
        raise ValueError("Static gas report is too short")
    if lines[1] != STATIC_HEADER:
        raise ValueError(f"Unexpected static report header: {lines[1]}")

    bounds: dict[str, int] = {}
    for raw in lines[2:]:
        parts = raw.split("\t")
        if len(parts) != 4:
            raise ValueError(f"Malformed static gas row: {raw}")
        contract, deploy, runtime, total = parts
        if contract == "TOTAL":
            continue
        runtime_n = int(runtime)
        if int(total) != int(deploy) + runtime_n:
            raise ValueError(f"Invalid static total arithmetic for {contract}")
        bounds[contract] = runtime_n

    if not bounds:
        raise ValueError("No contract rows found in static gas report")
    return bounds


def run_foundry_gas_report(match_path: str) -> str:
    env = dict(os.environ)
    env.setdefault("FOUNDRY_PROFILE", "difftest")
    cmd = ["forge", "test", "--gas-report", "--match-path", match_path]
    return run_command(cmd, env=env)


def parse_foundry_runtime_max(stdout: str) -> dict[str, int]:
    contract_header = re.compile(r"\|\s+[^|]*:(?P<name>[A-Za-z0-9_]+)\s+Contract\s*\|")
    observed: dict[str, int] = {}
    current: str | None = None

    for raw in stdout.splitlines():
        m = contract_header.search(raw)
        if m:
            current = m.group("name")
            observed.setdefault(current, 0)
            continue

        if current is None or "|" not in raw:
            continue
        stripped = raw.strip()
        if stripped.startswith("| Function Name") or stripped.startswith("| Deployment Cost"):
            continue
        if set(stripped) <= {"|", "-", "+", "=", "╭", "╰", "╮", "╯"}:
            continue

        cols = [part.strip() for part in raw.split("|")]
        if len(cols) < 7:
            continue
        fn_name = cols[1]
        if not fn_name or fn_name in {"Function Name", "Deployment Cost"}:
            continue

        max_col = cols[5]
        if not max_col.isdigit():
            continue

        max_gas = int(max_col)
        if max_gas > observed[current]:
            observed[current] = max_gas

    observed = {k: v for k, v in observed.items() if v > 0}
    if not observed:
        raise ValueError("No Foundry function gas rows parsed from gas report output")
    return observed


def validate_bounds(static_runtime: dict[str, int], foundry_max: dict[str, int], tx_base_gas: int) -> list[str]:
    failures: list[str] = []
    for contract, observed in sorted(foundry_max.items()):
        static = static_runtime.get(contract)
        if static is None:
            failures.append(f"{contract}: missing in static gas report")
            continue
        bound = static + tx_base_gas
        if observed > bound:
            failures.append(
                f"{contract}: foundry max {observed} exceeds static+txBase {bound} (static={static}, txBase={tx_base_gas})"
            )
    return failures


def main() -> int:
    args = parse_args()
    try:
        static_runtime = load_static_runtime_bounds(args.static_report)
        foundry_stdout = run_foundry_gas_report(args.match_path)
        foundry_max = parse_foundry_runtime_max(foundry_stdout)
        failures = validate_bounds(static_runtime, foundry_max, args.tx_base_gas)
    except Exception as exc:  # pragma: no cover - CI entrypoint
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    if failures:
        print("ERROR: static-vs-foundry gas calibration check failed:", file=sys.stderr)
        for line in failures:
            print(f"  - {line}", file=sys.stderr)
        return 1

    overlap = sorted(set(static_runtime).intersection(foundry_max))
    print(
        "OK: static runtime bounds dominate Foundry max function gas "
        f"for {len(overlap)} contracts (using tx_base_gas={args.tx_base_gas})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
