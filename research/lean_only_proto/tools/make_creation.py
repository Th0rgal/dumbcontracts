#!/usr/bin/env python3
import sys
import re


def usage() -> None:
    print("Usage: make_creation.py <runtime_hex_file> <creation_hex_out>")


def read_hex(path: str) -> str:
    data = open(path, "r", encoding="utf-8").read()
    data = data.strip()
    if data.startswith("0x"):
        data = data[2:]
    data = re.sub(r"\s+", "", data)
    if not data:
        raise SystemExit(f"empty hex input: {path}")
    if len(data) % 2 != 0:
        raise SystemExit(f"odd-length hex input: {path}")
    return data.lower()


def size_for(val: int) -> int:
    if val < 0:
        raise ValueError("negative value")
    bits = val.bit_length()
    return max(1, (bits + 7) // 8)


def push_bytes(val: int, size: int) -> bytes:
    if size < 1 or size > 32:
        raise ValueError("invalid PUSH size")
    opcode = 0x5F + size  # PUSH1 = 0x60
    return bytes([opcode]) + val.to_bytes(size, "big")


def build_creation(runtime_hex: str) -> bytes:
    runtime = bytes.fromhex(runtime_hex)
    length = len(runtime)
    size_len = size_for(length)

    offset = 0
    while True:
        size_off = size_for(offset)
        prefix_len = 9 + 2 * size_len + size_off
        if prefix_len == offset:
            break
        offset = prefix_len

    prefix = b"".join(
        [
            push_bytes(length, size_len),
            push_bytes(offset, size_off),
            b"\x60\x00",  # PUSH1 0x00
            b"\x39",  # CODECOPY
            push_bytes(length, size_len),
            b"\x60\x00",  # PUSH1 0x00
            b"\xF3",  # RETURN
        ]
    )

    return prefix + runtime


def main() -> int:
    if len(sys.argv) != 3:
        usage()
        return 1
    runtime_hex_path = sys.argv[1]
    out_path = sys.argv[2]
    runtime_hex = read_hex(runtime_hex_path)
    creation = build_creation(runtime_hex)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(creation.hex())
        f.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
