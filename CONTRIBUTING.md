# Contributing to DumbContracts

Thank you for your interest in contributing to DumbContracts! This guide will help you understand our development workflow and conventions.

## Quick Links

- **[README.md](README.md)**: Project overview and getting started
- **[AGENTS.md](AGENTS.md)**: Project structure and key concepts
- **[docs/ROADMAP.md](docs/ROADMAP.md)**: Current progress and priorities
- **[Compiler/Proofs/README.md](Compiler/Proofs/README.md)**: Proof development guide

## Issue Conventions

We use structured issue formatting to keep work organized and scannable. When creating or updating issues, please follow these conventions:

### Issue Title Format

Use semantic prefixes to indicate the architectural area:

- `[Layer 3]` - IR ↔ Yul compilation correctness proofs
- `[Trust Reduction]` - Yul ↔ EVM trust assumptions and bridges
- `[Property Coverage]` - Contract property verification completeness
- `[Compiler Enhancement]` - Compiler features and improvements
- `[Documentation]` - Documentation updates and improvements
- `[Infrastructure]` - Build system, CI/CD, tooling

**Examples:**
- ✅ `[Layer 3] Prove conditional (if) statement equivalence`
- ✅ `[Trust Reduction] Add keccak256 axiom for function selector verification`
- ✅ `[Property Coverage] Add finite address set modeling for sum properties`
- ✅ `[Compiler Enhancement] External function linking for production cryptographic libraries`

### Labels

Apply relevant labels to help with filtering and organization:

**By architectural area:**
- `layer-3` - Layer 3 verification work (IR ↔ Yul proofs)
- `lean` - Lean code, proofs, or type system work

**By work type:**
- `proof` - Theorem proving work
- `enhancement` - New features or improvements
- `bug` - Something isn't working
- `documentation` - Documentation improvements

**By status/difficulty:**
- `help-wanted` - Good issues for community contributions
- `good-first-issue` - Suitable for newcomers to the project

### Issue Structure

A well-structured issue should include:

1. **Goal/Summary** - What needs to be accomplished (2-3 sentences)
2. **Effort Estimate** - Realistic time estimate (e.g., "2-4 hours", "1-2 weeks")
3. **Implementation Strategy** - Specific approach with code examples when relevant
4. **Acceptance Criteria** - Clear checkboxes for when the issue is complete
5. **Impact** - Why this matters for the project
6. **References** - Links to relevant files, line numbers, or documentation

**See examples:**
- [Issue #37](https://github.com/Th0rgal/dumbcontracts/issues/37) - Layer 3 work with code examples
- [Issue #38](https://github.com/Th0rgal/dumbcontracts/issues/38) - Trust reduction with multiple approaches
- [Issue #39](https://github.com/Th0rgal/dumbcontracts/issues/39) - Property coverage with type definitions

### Using Issue Templates

We provide issue templates in `.github/ISSUE_TEMPLATE/` for common work types:

- **layer3-statement-proof.md** - For Layer 3 statement equivalence proofs

When creating issues through GitHub's UI, select the appropriate template and fill in the placeholders.

## Pull Request Conventions

### PR Title Format

Use the same semantic prefix convention as issues:

```
[Layer 3] Implement execIRStmtFuel for statement proofs
[Trust Reduction] Add keccak256 axiom with CI validation
[Documentation] Update ROADMAP with completion status
```

### PR Description

Include:
1. **Summary** - What changes are included (bullet points)
2. **Motivation** - Why these changes are needed
3. **Test Plan** - How the changes were validated
4. **Related Issues** - Links to issues this closes/addresses

### Before Submitting

- [ ] Run `lake build` to ensure the project compiles
- [ ] Verify no new `sorry` placeholders were added (unless documented)
- [ ] Update `docs/ROADMAP.md` if architectural changes were made
- [ ] Add/update tests where appropriate
- [ ] Update documentation for new features

### Review Process

1. **Bugbot Review** - Automated checks will run on your PR
2. **Human Review** - Maintainers will review the code and proofs
3. **CI Validation** - All builds and tests must pass
4. **Merge** - PRs are typically squash-merged to keep history clean

## Development Workflow

### Setting Up

```bash
# Clone the repository
git clone https://github.com/Th0rgal/dumbcontracts.git
cd dumbcontracts

# Build the project
lake build

# Run tests (if applicable)
lake test
```

### Working on Layer 3 Proofs

See the dedicated guide: [Compiler/Proofs/README.md](Compiler/Proofs/README.md)

**Quick tips:**
- Start by reading the theorem stub and understanding the statement semantics
- Look at completed proofs (e.g., `assign_equiv`, `storageLoad_equiv`) for patterns
- Use `unfold` to expand definitions and `rw` to rewrite with lemmas
- The `evalIRExpr_eq_evalYulExpr` axiom bridges IR and Yul expression evaluation
- Always verify your proof builds with `lake build`

### Working on Compiler Features

1. **Read the specs** in `Compiler/Specs.lean` to understand the declarative compilation semantics
2. **Check the IR** in `Compiler/IR.lean` and Yul types in `Compiler/Yul.lean`
3. **Update proofs** if you change semantics - all proofs must remain valid
4. **Add tests** in the `test/` directory using Foundry for integration tests

## Code Style

### Lean Code

- Use 2-space indentation
- Keep line length under 100 characters when possible
- Use meaningful variable names (prefer `irState` over `s`)
- Document complex proofs with comments explaining the strategy
- Group related definitions together

### Commit Messages

Follow conventional commit style:

```
<type>: <description>

[optional body]

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
```

**Types:**
- `feat:` - New feature
- `fix:` - Bug fix
- `proof:` - Theorem proving work
- `docs:` - Documentation changes
- `refactor:` - Code restructuring without behavior change
- `test:` - Adding or updating tests
- `chore:` - Build system, dependencies, etc.

**Examples:**
```
proof: complete 7 statement equivalence theorems

Implemented execIRStmtFuel with mutual recursion and proved:
- assign_equiv, storageLoad_equiv, storageStore_equiv
- mappingLoad_equiv, mappingStore_equiv
- return_equiv, revert_equiv

All proofs use evalIRExpr_eq_evalYulExpr axiom and follow
the same pattern: unfold definitions, rewrite with axiom,
case split on results, prove state alignment.

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
```

## Project Architecture

DumbContracts is organized into three verification layers:

1. **Layer 1** (✅ Complete) - EDSL → IR compilation correctness
2. **Layer 2** (✅ Complete) - IR → Yul compilation correctness (expressions)
3. **Layer 3** (🟡 97% Complete) - IR → Yul compilation correctness (statements)

See [docs/ROADMAP.md](docs/ROADMAP.md) for detailed status and priorities.

### Key Directories

- `DumbContracts/` - Contract EDSL, semantics, and user-facing specs
- `Compiler/` - IR/Yul compiler implementation
- `Compiler/Proofs/` - Machine-checked compiler correctness proofs
- `Compiler/Proofs/YulGeneration/` - Layer 2 & 3 proofs
- `docs/` - Project documentation and roadmap
- `test/` - Foundry integration tests
- `scripts/` - Automation scripts for issue management, etc.

## Getting Help

- **Questions about proofs?** Open a GitHub Discussion or ask in a PR
- **Found a bug?** Open an issue with the `bug` label
- **Want to contribute but not sure where to start?** Look for issues labeled `good-first-issue`
- **Need architectural guidance?** Read [AGENTS.md](AGENTS.md) and [Compiler/Proofs/README.md](Compiler/Proofs/README.md)

## Scripts and Automation

### Issue Management

The `scripts/create_layer3_issues.sh` script creates GitHub issues for Layer 3 work:

```bash
./scripts/create_layer3_issues.sh
```

This script is idempotent - it checks for existing issues before creating new ones.

### Bugbot Review

To trigger Bugbot review on a PR, use the `/bugbot-review` skill or comment on the PR.

## Recognition

Contributors will be acknowledged in:
- Git commit co-authorship
- PR descriptions
- Release notes for significant contributions

Thank you for helping make verified smart contract compilation a reality! 🎯
