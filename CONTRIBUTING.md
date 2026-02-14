# Contributing to DumbContracts

Quick conventions for contributing. See [README.md](README.md) for project overview, [docs/ROADMAP.md](docs/ROADMAP.md) for status.

## Issue Format

**Title**: `[Category] Brief description`

**Categories**: `[Layer 3]` `[Trust Reduction]` `[Property Coverage]` `[Compiler Enhancement]` `[Documentation]` `[Infrastructure]`

**Labels**: Use `layer-3` `lean` `proof` `enhancement` `bug` `documentation` `help-wanted` `good-first-issue`

**Structure**: Use issue templates in `.github/ISSUE_TEMPLATE/`
- Goal (what needs doing)
- Effort estimate (hours/weeks)
- Implementation approach
- Acceptance criteria
- References (file paths, issues)

## PR Format

**Title**: Same `[Category]` prefix as issues

**Body**:
```markdown
## Summary
- Bullet points of changes

## Test Plan
How you verified it works

## Related Issues
Closes #X, addresses #Y
```

**Before submitting**:
```bash
lake build  # Must pass
# No new `sorry` without documentation
# No new `axiom` without documenting in AXIOMS.md
# Update docs/ROADMAP.md if architectural changes
```

## Code Style

**Lean**:
- 2-space indentation
- Meaningful names (`irState` not `s`)
- Proofs under 20 lines when possible
- Document complex proof strategies

**Commits**:
```
type: description

[optional body]

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
```

Types: `feat` `fix` `proof` `docs` `refactor` `test` `chore`

## Development

**Layer 3 proofs**: Read [Compiler/Proofs/README.md](Compiler/Proofs/README.md), study completed proofs (`assign_equiv`, `storageLoad_equiv`), use templates

**New contracts**: Follow `SimpleStorage` pattern: Spec → Invariants → Implementation → Proofs → Tests

**Compiler changes**: Check [Compiler/Specs.lean](Compiler/Specs.lean), ensure proofs still build

## Adding Axioms

Axioms should be **avoided whenever possible** as they introduce trust assumptions. If you must add an axiom:

1. **Exhaust all alternatives first**:
   - Can you prove it? (even if difficult)
   - Can you use a weaker lemma?
   - Can you refactor to avoid the need?

2. **Document in AXIOMS.md**:
   - State the axiom clearly
   - Provide soundness justification
   - Explain why a proof isn't feasible
   - Note future work to eliminate axiom
   - Assess risk level

3. **Add inline comment in source**:
   ```lean
   /--
   AXIOM: Brief explanation
   See AXIOMS.md for full soundness justification
   -/
   axiom my_axiom : ...
   ```

4. **CI will validate**: The CI workflow automatically detects axioms and ensures they're documented in AXIOMS.md. Undocumented axioms will fail the build.

See [AXIOMS.md](AXIOMS.md) for current axioms and detailed guidelines.

## Key Files

- `DumbContracts/` - EDSL, specs, Layer 1 proofs
- `Compiler/` - IR, Yul, codegen
- `Compiler/Proofs/` - Layer 2 & 3 proofs
- `docs/ROADMAP.md` - Progress tracking
- `test/` - Foundry tests

Full details: [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md)
