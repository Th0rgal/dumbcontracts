#!/usr/bin/env python3
"""Validate selector hashing against solc fixtures.

Runs `solc --hashes` on a small Solidity fixture and compares the
reported selectors to the keccak implementation used by our tools.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "scripts" / "fixtures" / "SelectorFixtures.sol"
KECCAK = ROOT / "scripts" / "keccak256.py"

SIG_RE = re.compile(r"^([A-Za-z0-9_]+\([^\)]*\))\s*:\s*(0x)?([0-9a-fA-F]{8})$")


def die(msg: str) -> None:
    print(f"error: {msg}", file=sys.stderr)
    raise SystemExit(1)


def load_fixture_signatures() -> list[str]:
    if not FIXTURE.exists():
        die(f"Missing fixture file: {FIXTURE}")
    text = FIXTURE.read_text(encoding="utf-8")
    sigs: list[str] = []
    for line in text.splitlines():
        line = line.strip()
        if not line.startswith("function "):
            continue
        line = line[len("function ") :]
        name = line.split("(", 1)[0].strip()
        params = line.split("(", 1)[1].split(")", 1)[0].strip()
        sigs.append(f"{name}({params})")
    if not sigs:
        die("No function signatures found in fixture")
    return sigs


def run_solc_hashes() -> dict[str, str]:
    result = subprocess.run(
        ["solc", "--hashes", str(FIXTURE)],
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        die(f"solc --hashes failed: {result.stderr.strip()}")
    hashes: dict[str, str] = {}
    for line in result.stdout.splitlines():
        line = line.strip()
        match = SIG_RE.match(line)
        if not match:
            continue
        signature = match.group(1)
        selector = match.group(3).lower()
        hashes[signature] = selector
    if not hashes:
        die("No selector hashes parsed from solc output")
    return hashes


def run_keccak(signatures: list[str]) -> dict[str, str]:
    result = subprocess.run(
        ["python3", str(KECCAK), *signatures],
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        die(f"keccak256.py failed: {result.stderr.strip()}")
    selectors = [line.strip().lower().replace("0x", "") for line in result.stdout.splitlines() if line.strip()]
    if len(selectors) != len(signatures):
        die("keccak256.py returned unexpected number of selectors")
    return dict(zip(signatures, selectors, strict=True))


def main() -> None:
    signatures = load_fixture_signatures()
    solc_hashes = run_solc_hashes()
    keccak_hashes = run_keccak(signatures)

    errors: list[str] = []
    for signature in signatures:
        solc_selector = solc_hashes.get(signature)
        if solc_selector is None:
            errors.append(f"Missing solc selector for {signature}")
            continue
        keccak_selector = keccak_hashes[signature]
        if solc_selector != keccak_selector:
            errors.append(
                f"Selector mismatch for {signature}: solc={solc_selector} keccak={keccak_selector}"
            )

    if errors:
        print("Selector fixture check failed:", file=sys.stderr)
        for item in errors:
            print(f"  - {item}", file=sys.stderr)
        raise SystemExit(1)

    print("Selector fixture check passed.")


if __name__ == "__main__":
    main()
