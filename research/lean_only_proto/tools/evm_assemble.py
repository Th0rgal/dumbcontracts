#!/usr/bin/env python3
"""Tiny EVM assembler for a minimal assembly subset.

Supports:
- Labels as `name:` lines (emits JUMPDEST for all labels except `entry`)
- Instructions as `OP` or `OP ARG`
- PUSH1..PUSH32 with hex, decimal, or label arguments
- PUSH (auto width) with hex, decimal, or label arguments

Outputs hex string (no 0x prefix).
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import Dict, List, Tuple

OPCODES: Dict[str, int] = {
    "STOP": 0x00,
    "ADD": 0x01,
    "MUL": 0x02,
    "SUB": 0x03,
    "DIV": 0x04,
    "LT": 0x10,
    "GT": 0x11,
    "EQ": 0x14,
    "ISZERO": 0x15,
    "AND": 0x16,
    "OR": 0x17,
    "XOR": 0x18,
    "NOT": 0x19,
    "BYTE": 0x1a,
    "SHL": 0x1b,
    "SHR": 0x1c,
    "SAR": 0x1d,
    "SHA3": 0x20,
    "CALLDATALOAD": 0x35,
    "CALLDATASIZE": 0x36,
    "CALLDATACOPY": 0x37,
    "POP": 0x50,
    "MLOAD": 0x51,
    "MSTORE": 0x52,
    "MSTORE8": 0x53,
    "SLOAD": 0x54,
    "SSTORE": 0x55,
    "JUMP": 0x56,
    "JUMPI": 0x57,
    "PC": 0x58,
    "MSIZE": 0x59,
    "GAS": 0x5a,
    "JUMPDEST": 0x5b,
    "RETURN": 0xf3,
    "REVERT": 0xfd,
}

NO_JUMPDEST_LABELS = {"entry"}


@dataclass
class Instr:
    op: str
    arg: str | None
    line: int


def parse_lines(text: str) -> List[Instr]:
    instrs: List[Instr] = []
    for lineno, raw in enumerate(text.splitlines(), start=1):
        line = raw.strip()
        if not line:
            continue
        if line.endswith(":"):
            label = line[:-1]
            instrs.append(Instr(op="LABEL", arg=label, line=lineno))
            continue
        parts = line.split()
        op = parts[0].upper()
        arg = parts[1] if len(parts) > 1 else None
        instrs.append(Instr(op=op, arg=arg, line=lineno))
    return instrs


def parse_int(value: str) -> int:
    if value.startswith("0x"):
        return int(value[2:], 16)
    return int(value, 10)


def size_for_value(value: int) -> int:
    if value < 0:
        raise ValueError("negative immediate not supported")
    return max(1, (value.bit_length() + 7) // 8)


def instr_size(instr: Instr, auto_widths: Dict[int, int], index: int) -> int:
    op = instr.op
    if op == "LABEL":
        label = instr.arg or ""
        return 0 if label in NO_JUMPDEST_LABELS else 1
    if op == "PUSH0":
        return 1
    if op == "PUSH":
        width = auto_widths.get(index, 1)
        return 1 + width
    if op.startswith("PUSH"):
        n = int(op[4:])
        return 1 + n
    return 1


def resolve_layout(instrs: List[Instr]) -> Tuple[Dict[str, int], Dict[int, int]]:
    auto_widths: Dict[int, int] = {}

    for _ in range(20):
        offset = 0
        label_offsets: Dict[str, int] = {}
        for idx, instr in enumerate(instrs):
            if instr.op == "LABEL":
                label = instr.arg or ""
                label_offsets[label] = offset
                if label not in NO_JUMPDEST_LABELS:
                    offset += 1
                continue
            offset += instr_size(instr, auto_widths, idx)

        new_widths: Dict[int, int] = {}
        for idx, instr in enumerate(instrs):
            if instr.op != "PUSH":
                continue
            if instr.arg is None:
                raise ValueError(f"missing argument for PUSH on line {instr.line}")
            if instr.arg in label_offsets:
                value = label_offsets[instr.arg]
            else:
                value = parse_int(instr.arg)
            width = size_for_value(value)
            if width > 32:
                raise ValueError(f"immediate {value} does not fit in 32 bytes on line {instr.line}")
            new_widths[idx] = width

        if new_widths == auto_widths:
            return label_offsets, auto_widths
        auto_widths = new_widths

    raise ValueError("could not resolve PUSH widths within iteration limit")


def encode(instrs: List[Instr], label_offsets: Dict[str, int], auto_widths: Dict[int, int]) -> bytes:
    out = bytearray()
    for idx, instr in enumerate(instrs):
        op = instr.op
        if op == "LABEL":
            label = instr.arg or ""
            if label not in NO_JUMPDEST_LABELS:
                out.append(OPCODES["JUMPDEST"])
            continue

        if op.startswith("DUP"):
            try:
                n = int(op[3:])
            except ValueError as exc:
                raise ValueError(f"invalid DUP opcode '{op}' on line {instr.line}") from exc
            if not (1 <= n <= 16):
                raise ValueError(f"invalid DUP width '{op}' on line {instr.line}")
            if instr.arg is not None:
                raise ValueError(f"unexpected argument for {op} on line {instr.line}")
            out.append(0x7F + n)
            continue

        if op.startswith("SWAP"):
            try:
                n = int(op[4:])
            except ValueError as exc:
                raise ValueError(f"invalid SWAP opcode '{op}' on line {instr.line}") from exc
            if not (1 <= n <= 16):
                raise ValueError(f"invalid SWAP width '{op}' on line {instr.line}")
            if instr.arg is not None:
                raise ValueError(f"unexpected argument for {op} on line {instr.line}")
            out.append(0x8F + n)
            continue

        if op == "PUSH0":
            if instr.arg is not None:
                raise ValueError(f"unexpected argument for PUSH0 on line {instr.line}")
            out.append(0x5F)
            continue

        if op == "PUSH":
            if instr.arg is None:
                raise ValueError(f"missing argument for PUSH on line {instr.line}")
            if instr.arg in label_offsets:
                value = label_offsets[instr.arg]
            else:
                value = parse_int(instr.arg)
            width = auto_widths.get(idx)
            if width is None:
                width = size_for_value(value)
            if width > 32:
                raise ValueError(f"immediate {value} does not fit in 32 bytes on line {instr.line}")
            out.append(0x5F + width)
            out.extend(value.to_bytes(width, byteorder="big"))
            continue

        if op.startswith("PUSH"):
            try:
                n = int(op[4:])
            except ValueError as exc:
                raise ValueError(f"invalid PUSH opcode '{op}' on line {instr.line}") from exc
            if not (1 <= n <= 32):
                raise ValueError(f"invalid PUSH width '{op}' on line {instr.line}")
            if instr.arg is None:
                raise ValueError(f"missing argument for {op} on line {instr.line}")
            if instr.arg in label_offsets:
                value = label_offsets[instr.arg]
            else:
                value = parse_int(instr.arg)
            if value < 0 or value >= (1 << (8 * n)):
                raise ValueError(
                    f"immediate {value} does not fit in {n} bytes for {op} on line {instr.line}"
                )
            out.append(0x5F + n)
            out.extend(value.to_bytes(n, byteorder="big"))
            continue

        opcode = OPCODES.get(op)
        if opcode is None:
            raise ValueError(f"unknown opcode '{op}' on line {instr.line}")
        if instr.arg is not None:
            raise ValueError(f"unexpected argument for {op} on line {instr.line}")
        out.append(opcode)

    return bytes(out)


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: evm_assemble.py <input.evm> <output.hex>", file=sys.stderr)
        return 2

    src_path = sys.argv[1]
    out_path = sys.argv[2]

    with open(src_path, "r", encoding="utf-8") as f:
        text = f.read()

    instrs = parse_lines(text)
    label_offsets, auto_widths = resolve_layout(instrs)
    bytecode = encode(instrs, label_offsets, auto_widths)

    with open(out_path, "w", encoding="utf-8") as f:
        f.write(bytecode.hex())
        f.write("\n")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
