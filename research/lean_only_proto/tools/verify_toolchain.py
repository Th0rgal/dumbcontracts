#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
from pathlib import Path


def read_lock(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def run(cmd: list[str]) -> str:
    return subprocess.check_output(cmd, text=True).strip()


def extract_version(pattern: str, text: str) -> str | None:
    match = re.search(pattern, text)
    return match.group(1) if match else None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lock", default=None)
    parser.add_argument("--require-foundry", action="store_true")
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    lock_path = Path(args.lock) if args.lock else root / "toolchain.lock.json"
    data = read_lock(lock_path)

    errors: list[str] = []

    # Lean
    lean_path = shutil.which("lean")
    if not lean_path and Path("/opt/lean-4.27.0/bin/lean").exists():
        lean_path = "/opt/lean-4.27.0/bin/lean"
    if lean_path:
        lean_out = run([lean_path, "--version"])
        lean_version = extract_version(r"version ([0-9]+\.[0-9]+\.[0-9]+)", lean_out)
        expected_lean = data["lean"]["toolchain"].split(":")[-1]
        if lean_version != expected_lean:
            errors.append(f"lean version mismatch: expected {expected_lean}, got {lean_version}")
    else:
        errors.append("lean not found in PATH")

    # solc
    solc_path = shutil.which("solc")
    if solc_path:
        solc_out = run([solc_path, "--version"])
        solc_version = extract_version(r"Version: ([0-9]+\.[0-9]+\.[0-9]+)", solc_out)
        expected_solc = data["solc"]["version"]
        if solc_version != expected_solc:
            errors.append(f"solc version mismatch: expected {expected_solc}, got {solc_version}")
    else:
        errors.append("solc not found in PATH")

    # foundry
    forge_path = shutil.which("forge")
    if forge_path:
        forge_out = run([forge_path, "--version"])
        expected_foundry = data["foundry"]["version"]
        if expected_foundry not in forge_out:
            errors.append(f"forge version mismatch: expected {expected_foundry} in '{forge_out}'")
    elif args.require_foundry:
        errors.append("forge not found in PATH")

    if errors:
        for err in errors:
            print(err)
        return 1

    print("toolchain OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
