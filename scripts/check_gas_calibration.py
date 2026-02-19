#!/usr/bin/env python3
"""Cross-check static gas bounds against Foundry gas measurements."""

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
CREATE_TX_BASE_GAS = 53000
CODE_DEPOSIT_GAS_PER_BYTE = 200

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
    parser.add_argument(
        "--create-tx-base-gas",
        type=int,
        default=CREATE_TX_BASE_GAS,
        help="Fixed deployment transaction overhead (tx base + create surcharge).",
    )
    parser.add_argument(
        "--code-deposit-gas-per-byte",
        type=int,
        default=CODE_DEPOSIT_GAS_PER_BYTE,
        help="Gas charged per deployed runtime bytecode byte.",
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


def load_static_bounds(path: Path | None) -> dict[str, tuple[int, int]]:
    if path is None:
        stdout = run_command(["lake", "exe", "gas-report"])
    else:
        stdout = path.read_text(encoding="utf-8")

    lines = [line.strip() for line in stdout.splitlines() if line.strip()]
    if len(lines) < 4:
        raise ValueError("Static gas report is too short")
    if lines[1] != STATIC_HEADER:
        raise ValueError(f"Unexpected static report header: {lines[1]}")

    bounds: dict[str, tuple[int, int]] = {}
    for raw in lines[2:]:
        parts = raw.split("\t")
        if len(parts) != 4:
            raise ValueError(f"Malformed static gas row: {raw}")
        contract, deploy, runtime, total = parts
        if contract == "TOTAL":
            continue
        deploy_n = int(deploy)
        runtime_n = int(runtime)
        if int(total) != deploy_n + runtime_n:
            raise ValueError(f"Invalid static total arithmetic for {contract}")
        bounds[contract] = (deploy_n, runtime_n)

    if not bounds:
        raise ValueError("No contract rows found in static gas report")
    return bounds


def run_foundry_gas_report(match_path: str) -> str:
    env = dict(os.environ)
    env.setdefault("FOUNDRY_PROFILE", "difftest")
    cmd = ["forge", "test", "--gas-report", "--match-path", match_path]
    return run_command(cmd, env=env)


def parse_foundry_report(stdout: str) -> tuple[dict[str, int], dict[str, tuple[int, int]]]:
    contract_header = re.compile(r"\|\s+[^|]*:(?P<name>[A-Za-z0-9_]+)\s+Contract\s*\|")
    observed_runtime: dict[str, int] = {}
    observed_deploy: dict[str, tuple[int, int]] = {}
    current: str | None = None
    expect_deploy_row = False

    for raw in stdout.splitlines():
        m = contract_header.search(raw)
        if m:
            current = m.group("name")
            observed_runtime.setdefault(current, 0)
            expect_deploy_row = False
            continue

        if current is None or "|" not in raw:
            continue
        stripped = raw.strip()
        if stripped.startswith("| Deployment Cost"):
            expect_deploy_row = True
            continue
        if stripped.startswith("| Function Name"):
            expect_deploy_row = False
            continue
        if set(stripped) <= {"|", "-", "+", "=", "╭", "╰", "╮", "╯"}:
            continue

        cols = [part.strip() for part in raw.split("|")]
        if len(cols) < 7:
            continue

        if expect_deploy_row and cols[1].isdigit() and cols[2].isdigit():
            observed_deploy[current] = (int(cols[1]), int(cols[2]))
            expect_deploy_row = False
            continue

        fn_name = cols[1]
        if not fn_name or fn_name in {"Function Name", "Deployment Cost"}:
            continue

        max_col = cols[5]
        if not max_col.isdigit():
            continue

        max_gas = int(max_col)
        if max_gas > observed_runtime[current]:
            observed_runtime[current] = max_gas

    observed_runtime = {k: v for k, v in observed_runtime.items() if v > 0}
    if not observed_runtime:
        raise ValueError("No Foundry function gas rows parsed from gas report output")
    if not observed_deploy:
        raise ValueError("No Foundry deployment rows parsed from gas report output")
    return observed_runtime, observed_deploy


def validate_runtime_bounds(
    static_bounds: dict[str, tuple[int, int]],
    foundry_runtime: dict[str, int],
    tx_base_gas: int,
) -> list[str]:
    failures: list[str] = []
    for contract, observed in sorted(foundry_runtime.items()):
        static = static_bounds.get(contract)
        if static is None:
            failures.append(f"{contract}: missing in static gas report")
            continue
        _, static_runtime = static
        bound = static_runtime + tx_base_gas
        if observed > bound:
            failures.append(
                f"{contract}: foundry max {observed} exceeds static+txBase {bound} (static={static_runtime}, txBase={tx_base_gas})"
            )
    return failures


def validate_deploy_bounds(
    static_bounds: dict[str, tuple[int, int]],
    foundry_deploy: dict[str, tuple[int, int]],
    create_tx_base_gas: int,
    code_deposit_gas_per_byte: int,
) -> list[str]:
    failures: list[str] = []
    for contract, (observed_deploy, deploy_size) in sorted(foundry_deploy.items()):
        static = static_bounds.get(contract)
        if static is None:
            failures.append(f"{contract}: missing in static gas report")
            continue
        static_deploy, _ = static
        bound = static_deploy + create_tx_base_gas + code_deposit_gas_per_byte * deploy_size
        if observed_deploy > bound:
            failures.append(
                f"{contract}: deployment {observed_deploy} exceeds static+createOverhead {bound} "
                f"(staticDeploy={static_deploy}, createTxBase={create_tx_base_gas}, "
                f"depositPerByte={code_deposit_gas_per_byte}, deploySize={deploy_size})"
            )
    return failures


def main() -> int:
    args = parse_args()
    try:
        static_bounds = load_static_bounds(args.static_report)
        foundry_stdout = run_foundry_gas_report(args.match_path)
        foundry_runtime, foundry_deploy = parse_foundry_report(foundry_stdout)
        failures = validate_runtime_bounds(static_bounds, foundry_runtime, args.tx_base_gas)
        failures.extend(
            validate_deploy_bounds(
                static_bounds,
                foundry_deploy,
                args.create_tx_base_gas,
                args.code_deposit_gas_per_byte,
            )
        )
    except Exception as exc:  # pragma: no cover - CI entrypoint
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    if failures:
        print("ERROR: static-vs-foundry gas calibration check failed:", file=sys.stderr)
        for line in failures:
            print(f"  - {line}", file=sys.stderr)
        return 1

    runtime_overlap = sorted(set(static_bounds).intersection(foundry_runtime))
    deploy_overlap = sorted(set(static_bounds).intersection(foundry_deploy))
    print(
        "OK: static bounds dominate Foundry gas "
        f"(runtime contracts={len(runtime_overlap)}, deploy contracts={len(deploy_overlap)}, "
        f"tx_base_gas={args.tx_base_gas}, create_tx_base_gas={args.create_tx_base_gas}, "
        f"code_deposit_gas_per_byte={args.code_deposit_gas_per_byte})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
