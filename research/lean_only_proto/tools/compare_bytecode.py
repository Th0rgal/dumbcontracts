#!/usr/bin/env python3
from __future__ import annotations

import sys
from pathlib import Path


def read_hex(path: Path) -> str:
    return "".join(path.read_text(encoding="utf-8").split()).lower()


def main(argv: list[str]) -> int:
    if len(argv) != 4:
        print("usage: compare_bytecode.py <direct.hex> <solc.hex> <output.md>", file=sys.stderr)
        return 2

    direct_path = Path(argv[1])
    solc_path = Path(argv[2])
    out_path = Path(argv[3])

    direct_hex = read_hex(direct_path)
    solc_hex = read_hex(solc_path)

    lines: list[str] = []
    lines.append("# Bytecode Comparison")
    lines.append("")
    lines.append(f"Direct hex: `{direct_path.name}`")
    lines.append(f"Solc hex: `{solc_path.name}`")
    lines.append("")
    lines.append(f"Direct length: {len(direct_hex)} hex chars")
    lines.append(f"Solc length: {len(solc_hex)} hex chars")

    if direct_hex == solc_hex:
        lines.append("")
        lines.append("Match: yes")
        out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        return 0

    lines.append("")
    lines.append("Match: no")
    min_len = min(len(direct_hex), len(solc_hex))
    diff_index = None
    for i in range(min_len):
        if direct_hex[i] != solc_hex[i]:
            diff_index = i
            break
    if diff_index is None:
        diff_index = min_len
    byte_index = diff_index // 2
    lines.append(f"First diff nibble index: {diff_index}")
    lines.append(f"First diff byte index: {byte_index}")
    lines.append("")
    lines.append(f"Direct slice: `{direct_hex[diff_index:diff_index+32]}`")
    lines.append(f"Solc slice: `{solc_hex[diff_index:diff_index+32]}`")

    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
