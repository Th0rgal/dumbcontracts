#!/usr/bin/env python3
"""Fail when tracked paths conflict under case-insensitive filesystems."""

from __future__ import annotations

import subprocess
import sys
from collections import defaultdict
from pathlib import PurePosixPath


def _git_tracked_paths() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files"],
        check=True,
        capture_output=True,
        text=True,
    )
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def _collect_case_keys(paths: list[str]) -> dict[str, set[str]]:
    keys: dict[str, set[str]] = defaultdict(set)
    for path_str in paths:
        path = PurePosixPath(path_str)
        parts = path.parts
        for i in range(1, len(parts) + 1):
            orig = "/".join(parts[:i])
            keys[orig.lower()].add(orig)
    return keys


def _find_conflicts(paths: list[str]) -> list[list[str]]:
    conflicts: list[list[str]] = []
    for originals in _collect_case_keys(paths).values():
        if len(originals) > 1:
            conflicts.append(sorted(originals))
    conflicts.sort()
    return conflicts


def main() -> int:
    paths = _git_tracked_paths()
    conflicts = _find_conflicts(paths)
    if not conflicts:
        return 0

    print(
        "ERROR: case-insensitive path conflicts detected in tracked files/directories.",
        file=sys.stderr,
    )
    print(
        "These collide on macOS/Windows and can cause checkout/build failures:",
        file=sys.stderr,
    )
    for group in conflicts:
        print("- " + "  <->  ".join(group), file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
