# Agent Guide for Verity

Quick reference for AI agents. Humans: see [README.md](README.md).

## Documentation Safety (Critical)

The following files are safety-critical and MUST stay synchronized with source code:

- `AUDIT.md`
- `TRUST_ASSUMPTIONS.md`
- `AXIOMS.md`

If code changes and these files are not updated in the same change set, trust boundaries become stale and the system is unsafe to assess correctly.

Mandatory rule:

1. Every source-code change that affects architecture, semantics, trust boundaries, assumptions, axioms, CI safety checks, or compilation paths MUST update these files immediately.
2. Never defer these updates to a later PR.
3. Treat stale trust/audit documentation as a security issue.

## Agent Workflow

### Before Starting
1. Check [docs/ROADMAP.md](docs/ROADMAP.md) for current status
2. Read [CONTRIBUTING.md](CONTRIBUTING.md) for conventions
3. Read relevant README in working directory

### When Writing Code

**DO**: Read before editing · Run `lake build` · Follow `[Category]` prefixes · Update docs/ROADMAP.md for arch changes · Keep `AUDIT.md`, `TRUST_ASSUMPTIONS.md`, and `AXIOMS.md` in sync with code

**DON'T**: Create files unnecessarily · Add `sorry` without docs · Skip builds · Force-push without approval · Create docs proactively

### Creating Issues/PRs

**Format**: `[Category] Brief description` - use templates in `.github/ISSUE_TEMPLATE/`

**Categories**: `[Trust Reduction]` `[Property Coverage]` `[Compiler Enhancement]` `[Documentation]` `[Infrastructure]`

See [CONTRIBUTING.md](CONTRIBUTING.md) for full conventions.

### Human Approval Required

**Ask before**: Force-push, merge, delete branches, change compiler semantics, add axioms, any destructive operations

**Proceed freely**: Read files, create local branches/commits, run builds/tests, create issues, update docs

## Navigation

| Need | Read |
|------|------|
| Project overview | README.md |
| Conventions | CONTRIBUTING.md |
| Current progress | docs/ROADMAP.md |
| Verification details | docs/VERIFICATION_STATUS.md |
| Proof guide | Compiler/Proofs/README.md |
| EDSL semantics | Verity/Core.lean |
| Compiler specs | Compiler/Specs.lean |
| IR semantics | Compiler/Proofs/IRGeneration/IRInterpreter.lean |
| Yul semantics | Compiler/Proofs/YulGeneration/Semantics.lean |

## Task Workflows

**Layer 3 Proofs**: ✅ Complete (all 8 statement proofs + universal dispatcher). No further work needed.

**New Contracts**:
1. Run `python3 scripts/generate_contract.py <Name>` to create scaffold
2. Read [add-contract.mdx](/add-contract) for the full checklist
3. Follow SimpleStorage pattern: Spec → EDSL → Proofs → Compiler → Tests

**Compiler Changes**:
1. Read Compiler/Specs.lean
2. Ensure proofs still build
3. Use template: `.github/ISSUE_TEMPLATE/compiler-enhancement.md`

## Architecture

```
Layer 1 ✅ EDSL ≡ ContractSpec
Layer 2 ✅ ContractSpec → IR
Layer 3 ✅ IR → Yul
```

See [docs/ROADMAP.md](docs/ROADMAP.md) for detailed status.

**Directories**:
- `Verity/` - EDSL, specs, Layer 1 proofs
- `Compiler/` - IR, Yul, codegen
- `Compiler/Proofs/` - Layer 2 & 3 proofs
- `docs/` - Roadmap, verification status
- `test/` - Foundry tests
- `.github/ISSUE_TEMPLATE/` - Issue templates

## Common Pitfalls

❌ Generic titles | ✅ `[Layer 3] Prove conditional statement equivalence`
❌ Edit without reading | ✅ Read tool before Edit tool
❌ Undocumented `sorry` | ✅ Document blockers, create issues
❌ Force-push without approval | ✅ Ask first
❌ Create files proactively | ✅ Edit existing when possible
❌ Docs drift from code | ✅ Update docs with code changes

## Agent Patterns

**Systematic Proof Work**: Prove first completely → Document approach → Apply to rest → Update ROADMAP.md → Close issues

**Safe Exploration**: Read ROADMAP → Use Grep/Glob for definitions → Read specific files → Build mental model → Verify with `lake build`

**Documentation Updates**: Code + verify → Update docs → Check consistency → Commit together

## Commands

```bash
lake build                           # Required before commits
FOUNDRY_PROFILE=difftest forge test  # All tests (FFI needed for property/differential tests)
```

## Resources

- Lean 4: [docs](https://lean-lang.org/documentation/) | [theorem proving](https://lean-lang.org/theorem_proving_in_lean4/)
- Tactics: [Mathlib reference](https://leanprover-community.github.io/mathlib4_docs/tactics.html)
- Start here: `Verity/Proofs/SimpleStorage/Basic.lean` (Layer 1 proofs)

---

**Status**: [docs/ROADMAP.md](docs/ROADMAP.md) · **Humans**: [README.md](README.md) · **Conventions**: [CONTRIBUTING.md](CONTRIBUTING.md)
