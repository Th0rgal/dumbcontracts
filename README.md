# Dumb Contracts Research

This repo explores a spec-first model for Ethereum smart contracts where state transitions are validated against simple rules (“dumb contracts”). The focus is on minimal, auditable constraints and testable POCs.

## What’s Here

- `docs/idea-draft.md` captures the original framing and goals.
- `docs/landscape.md` tracks the current tooling landscape.
- `src/` and `test/` contain small Solidity POCs with unit tests.

## Quick Start

```bash
forge build
forge test
```

## Foundry Notes

Foundry is used for unit testing the POCs. If you don’t have it installed, see https://book.getfoundry.sh/.
