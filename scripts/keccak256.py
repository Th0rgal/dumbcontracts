#!/usr/bin/env python3
"""Compute Solidity-style function selectors (keccak256, first 4 bytes).

Usage:
  keccak256.py "transfer(address,uint256)" "balanceOf(address)"

Outputs one selector per line as 0xXXXXXXXX.
"""

import sys
from typing import List

# Keccak-f[1600] parameters
RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]

R = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
]

MASK64 = (1 << 64) - 1


def _rotl(x: int, n: int) -> int:
    return ((x << n) & MASK64) | (x >> (64 - n))


def keccak_f(state: List[int]) -> None:
    for rc in RC:
        # Theta
        c = [state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rotl(c[(x + 1) % 5], 1) for x in range(5)]
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] ^= d[x]

        # Rho + Pi
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = _rotl(state[x + 5 * y], R[x][y])

        # Chi
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] = b[x + 5 * y] ^ ((~b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y])

        # Iota
        state[0] ^= rc


def keccak_256(data: bytes) -> bytes:
    rate = 1088 // 8  # 136 bytes
    state = [0] * 25

    # Absorb full blocks
    offset = 0
    while offset + rate <= len(data):
        block = data[offset:offset + rate]
        offset += rate
        for i in range(0, rate, 8):
            word = int.from_bytes(block[i:i + 8], byteorder="little")
            state[i // 8] ^= word
        keccak_f(state)

    # Final block with padding (always applied, even for empty or exact blocks)
    remaining = data[offset:]
    block = bytearray(rate)
    block[:len(remaining)] = remaining
    block[len(remaining)] ^= 0x01
    block[rate - 1] ^= 0x80
    for i in range(0, rate, 8):
        word = int.from_bytes(block[i:i + 8], byteorder="little")
        state[i // 8] ^= word
    keccak_f(state)

    # Squeeze
    out = bytearray()
    while len(out) < 32:
        for i in range(0, rate, 8):
            out += state[i // 8].to_bytes(8, byteorder="little")
            if len(out) >= 32:
                return bytes(out[:32])
        keccak_f(state)

    return bytes(out[:32])


def selector(sig: str) -> str:
    digest = keccak_256(sig.encode("utf-8"))
    return "0x" + digest[:4].hex()


def self_test() -> bool:
    """Validate keccak_256 against known Keccak-256 test vectors.

    Vectors sourced from the Keccak team reference implementation and
    Ethereum's use of keccak256 (which differs from NIST SHA3-256 in
    padding: Keccak uses 0x01, SHA3 uses 0x06).
    """
    # Full 32-byte digest vectors (independently verifiable)
    full_vectors = [
        # Empty string — canonical Ethereum keccak256("")
        # Source: Ethereum Yellow Paper, every Ethereum client
        (b"",
         "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),

        # keccak256("testing") — verified via ethers.js / web3.js
        (b"testing",
         "5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02"),

        # keccak256("transfer(address,uint256)") — full hash
        # Verified: first 4 bytes = 0xa9059cbb (ERC-20 transfer selector)
        (b"transfer(address,uint256)",
         "a9059cbb2ab09eb219583f4a59a5d0623ade346d962bcd4e46b11da047c9049b"),

        # keccak256("balanceOf(address)") — full hash
        # Verified: first 4 bytes = 0x70a08231 (ERC-20 balanceOf selector)
        (b"balanceOf(address)",
         "70a08231b98ef4ca268c9cc3f6b4590e4bfec28280db06bb5d45e689f2a360be"),
    ]

    # Selector-only vectors (first 4 bytes, verified against solc --hashes)
    selector_vectors = [
        (b"totalSupply()",          "18160ddd"),
        (b"approve(address,uint256)", "095ea7b3"),
        (b"allowance(address,address)", "dd62ed3e"),
        (b"transferFrom(address,address,uint256)", "23b872dd"),
        (b"mint(address,uint256)",  "40c10f19"),
        (b"store(uint256)",         "6057361d"),
        (b"retrieve()",             "2e64cec1"),
        (b"increment()",            "d09de08a"),
        (b"decrement()",            "2baeceb7"),
        (b"transferOwnership(address)", "f2fde38b"),
    ]
    passed = 0
    failed = 0

    # Check full 32-byte digests
    for data, expected in full_vectors:
        actual = keccak_256(data).hex()
        if actual == expected:
            passed += 1
        else:
            label = data.decode("utf-8", errors="replace")
            print(f"FAIL: keccak256(\"{label}\")", file=sys.stderr)
            print(f"  expected: {expected}", file=sys.stderr)
            print(f"  actual:   {actual}", file=sys.stderr)
            failed += 1

    # Check first-4-byte selectors (verified against solc --hashes)
    for data, expected_sel in selector_vectors:
        actual_sel = keccak_256(data).hex()[:8]
        if actual_sel == expected_sel:
            passed += 1
        else:
            sig = data.decode("utf-8")
            print(f"FAIL: selector(\"{sig}\")", file=sys.stderr)
            print(f"  expected: 0x{expected_sel}", file=sys.stderr)
            print(f"  actual:   0x{actual_sel}", file=sys.stderr)
            failed += 1

    total = passed + failed
    if failed:
        print(f"Self-test: {passed}/{total} passed, {failed} FAILED", file=sys.stderr)
        return False
    print(f"Self-test: {total}/{total} passed")
    return True


def main() -> int:
    args = sys.argv[1:]
    if args == ["--self-test"]:
        return 0 if self_test() else 1
    if not args:
        print("Usage: keccak256.py [--self-test | <signature> ...]", file=sys.stderr)
        return 2
    for sig in args:
        print(selector(sig))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
