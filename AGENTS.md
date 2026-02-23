# Agent Guide for Verity

Quick operational guide for AI agents. Human overview: [README.md](README.md).

## Critical Documentation Rule

These files are safety-critical and must stay synchronized with source code:

- `AUDIT.md`
- `TRUST_ASSUMPTIONS.md`
- `AXIOMS.md`

If code changes and these files are not updated in the same change set, trust analysis becomes stale and security assessment is unsafe.

Mandatory requirements:

1. Any change affecting architecture, semantics, trust boundaries, assumptions, axioms, CI safety checks, or compilation paths must update these files immediately.
2. Do not defer these updates to a later PR.
3. Treat documentation drift in these files as a security issue.

## Workflow

### Before starting

1. Read [docs/ROADMAP.md](docs/ROADMAP.md).
2. Read [CONTRIBUTING.md](CONTRIBUTING.md).
3. Read the local README for the area you are modifying.

### While coding

Do:

- Read files before editing.
- Run `lake build`.
- Use `[Category]` prefixes.
- Update `docs/ROADMAP.md` for architecture changes.
- Keep `AUDIT.md`, `TRUST_ASSUMPTIONS.md`, and `AXIOMS.md` in sync.

Do not:

- Add files without need.
- Add undocumented `sorry`.
- Skip builds.
- Force-push without approval.

## Issues and PRs

- Title format: `[Category] Brief description`
- Use templates in `.github/ISSUE_TEMPLATE/`
- Categories: `[Trust Reduction]`, `[Property Coverage]`, `[Compiler Enhancement]`, `[Documentation]`, `[Infrastructure]`

## Approval Boundaries

Ask before:

- Force-push
- Merge
- Delete branches
- Change compiler semantics
- Add axioms
- Run destructive operations

Proceed without approval:

- Read files
- Create local branches/commits
- Run builds/tests
- Create issues
- Update docs

## Navigation

| Need | File |
|------|------|
| Project overview | README.md |
| Conventions | CONTRIBUTING.md |
| Current progress | docs/ROADMAP.md |
| Verification status | docs/VERIFICATION_STATUS.md |
| Proof guide | Compiler/Proofs/README.md |
| EDSL semantics | Verity/Core.lean |
| Compiler specs | Compiler/Specs.lean |
| IR semantics | Compiler/Proofs/IRGeneration/IRInterpreter.lean |
| Yul semantics | Compiler/Proofs/YulGeneration/Semantics.lean |

## Standard Commands

```bash
lake build
FOUNDRY_PROFILE=difftest forge test
```

## Notes

- Layer 3 proofs are complete.
- For new contracts, scaffold with `python3 scripts/generate_contract.py <Name>` and follow `/add-contract`.
- For compiler changes, read `Compiler/Specs.lean` and verify proofs still build.
