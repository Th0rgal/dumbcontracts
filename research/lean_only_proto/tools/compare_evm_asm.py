#!/usr/bin/env python3
"""Compare direct EVM-assembly blocks against solc --asm blocks.

The direct assembly is expected to use explicit labels (name:), while solc's
asm output uses tag_ labels. We match by exact opcode+immediate sequences.
"""

from __future__ import annotations

import pathlib
import sys
from typing import Dict, List


def normalize_hex(token: str) -> str:
    h = token[2:]
    if len(h) % 2 == 1:
        h = "0" + h
    return "0x" + h.lower()


def parse_direct(text: str) -> Dict[str, List[str]]:
    blocks: Dict[str, List[str]] = {}
    current = None
    def is_literal(arg: str) -> bool:
        return arg.startswith("0x") or arg.isdigit()
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.endswith(":"):
            current = line[:-1]
            blocks[current] = []
            continue
        if current is None:
            continue
        parts = line.split()
        op = parts[0].upper()
        arg = parts[1] if len(parts) > 1 else None
        if op.startswith("PUSH") and arg is not None:
            if not is_literal(arg):
                # Symbolic label push (e.g., PUSH2 tag_label) - ignore for matching.
                continue
            if arg.startswith("0x"):
                arg = normalize_hex(arg)
            blocks[current].append(f"{op} {arg}")
        else:
            blocks[current].append(op)
    return blocks


def parse_solc_asm(text: str) -> Dict[str, List[str]]:
    blocks: Dict[str, List[str]] = {}
    current = "entry"
    blocks[current] = []

    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.startswith("======="):
            continue
        if line.startswith("Text representation"):
            continue
        if line.startswith("EVM assembly"):
            continue
        if line.startswith("/*"):
            continue

        if line.startswith("tag_") and line.endswith(":"):
            current = line[:-1]
            blocks[current] = []
            continue

        if current is None:
            continue

        token = line.split()[0]
        if token.startswith("tag_"):
            # label target emitted as literal in the asm stream
            continue
        if token.startswith("0x"):
            hex_token = normalize_hex(token)
            size = max(1, (len(hex_token) - 2) // 2)
            blocks[current].append(f"PUSH{size} {hex_token}")
            continue
        if "(" in token:
            token = token.split("(", 1)[0]
        blocks[current].append(token.upper())

    return blocks


def match_blocks(direct: Dict[str, List[str]], solc: Dict[str, List[str]]):
    matches = {}
    for dlabel, dops in direct.items():
        candidates = []
        for slabel, sops in solc.items():
            if dops == sops:
                candidates.append(slabel)
        matches[dlabel] = candidates
    return matches


def render_report(direct: Dict[str, List[str]], solc: Dict[str, List[str]], matches) -> str:
    lines = []
    lines.append("# EVM ASM Comparison")
    lines.append("")
    lines.append(f"Direct blocks: {len(direct)}")
    lines.append(f"solc blocks: {len(solc)}")
    lines.append("")

    lines.append("Matches (direct label -> solc tag_ labels):")
    for dlabel, slabels in matches.items():
        if slabels:
            joined = ", ".join(slabels)
            lines.append(f"- {dlabel}: {joined}")
        else:
            lines.append(f"- {dlabel}: (no exact match)")
    lines.append("")

    unmatched = [d for d, sl in matches.items() if not sl]
    if unmatched:
        lines.append("Notes:")
        lines.append("- Unmatched blocks may differ in immediates or emitted helpers.")
        lines.append("")

    lines.append("Direct op sequences:")
    for dlabel, dops in direct.items():
        lines.append(f"- {dlabel} ({len(dops)} ops):")
        lines.append("  " + ", ".join(dops))
    lines.append("")

    return "\n".join(lines) + "\n"


def main(argv: List[str]) -> int:
    if len(argv) != 4:
        print("usage: compare_evm_asm.py <direct.evm> <solc.asm> <output.md>", file=sys.stderr)
        return 2

    direct_path = pathlib.Path(argv[1])
    solc_path = pathlib.Path(argv[2])
    out_path = pathlib.Path(argv[3])

    direct_text = direct_path.read_text(encoding="utf-8")
    solc_text = solc_path.read_text(encoding="utf-8")

    direct_blocks = parse_direct(direct_text)
    solc_blocks = parse_solc_asm(solc_text)
    matches = match_blocks(direct_blocks, solc_blocks)

    out_path.write_text(render_report(direct_blocks, solc_blocks, matches), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
