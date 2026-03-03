# Agent Guide for Verity

This file is the operator quickstart. Keep it short and enforceable.

## Non-Negotiables

1. Keep `AUDIT.md`, `TRUST_ASSUMPTIONS.md`, and `AXIOMS.md` synchronized with any semantic/trust/CI boundary change.
2. Never claim completion without evidence and passing checks.

## Core Commands

```bash
lake build          # Verify all Lean proofs
make check          # Run local CI-equivalent validation (no Lean build)
make test-python    # Run Python unit tests
make test-foundry   # Run Foundry differential tests
```

## Reference Docs

- Project overview: [README.md](README.md)
- Contribution conventions: [CONTRIBUTING.md](CONTRIBUTING.md)
- Roadmap: [docs/ROADMAP.md](docs/ROADMAP.md)
- Script reference: [scripts/REFERENCE.md](scripts/REFERENCE.md)
