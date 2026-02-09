#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import shutil
import subprocess
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
from typing import Any


def run(cmd: list[str], cwd: Path | None = None) -> str | None:
    try:
        return subprocess.check_output(cmd, text=True, cwd=str(cwd) if cwd else None).strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None


def file_hash(path: Path) -> dict[str, Any]:
    h = sha256()
    size = 0
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
            size += len(chunk)
    return {"path": str(path), "sha256": h.hexdigest(), "bytes": size}


def main() -> int:
    if len(os.sys.argv) < 2:
        print("usage: gen_provenance.py <output.json> [artifact ...]", file=os.sys.stderr)
        return 2

    out_path = Path(os.sys.argv[1])
    artifacts = [Path(p) for p in os.sys.argv[2:]]

    root = Path(__file__).resolve().parents[1]
    repo_root = Path(run(["git", "rev-parse", "--show-toplevel"]) or root)

    lock_path = root / "toolchain.lock.json"
    lock_info = None
    if lock_path.exists():
        lock_info = file_hash(lock_path)
        lock_info["toolchain"] = json.loads(lock_path.read_text(encoding="utf-8"))

    def tool_info(name: str, exe: str) -> dict[str, Any]:
        path = shutil.which(exe)
        info: dict[str, Any] = {"path": path}
        if path:
            info["sha256"] = file_hash(Path(path))["sha256"]
            info["version"] = run([exe, "--version"]) or ""
        return info

    provenance = {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "git": {
            "commit": run(["git", "rev-parse", "HEAD"], cwd=repo_root),
            "dirty": bool(run(["git", "status", "--porcelain"], cwd=repo_root)),
        },
        "toolchain_lock": lock_info,
        "tools": {
            "lean": tool_info("lean", "lean"),
            "lake": tool_info("lake", "lake"),
            "solc": tool_info("solc", "solc"),
            "forge": tool_info("forge", "forge"),
            "cast": tool_info("cast", "cast"),
            "anvil": tool_info("anvil", "anvil"),
        },
        "artifacts": [file_hash(p) for p in artifacts if p.exists()],
    }

    out_path.write_text(json.dumps(provenance, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
