---
name: Layer 3 Statement Equivalence Proof
about: Track progress on proving IR ↔ Yul statement equivalence
title: '[Layer 3] Prove <STATEMENT_TYPE> equivalence'
labels: layer-3, proof, lean, help-wanted
assignees: ''
---

## Statement Type

**Statement**: `<STATEMENT_SYNTAX>`
**Theorem**: `<THEOREM_NAME>_equiv`
**File**: `Compiler/Proofs/YulGeneration/StatementEquivalence.lean`

## Description

Prove that executing this statement type in IR matches executing it in Yul when states are aligned.

**IR Semantics**: <DESCRIPTION>
**Yul Semantics**: <DESCRIPTION>

## Proof Strategy

<STRATEGY_DESCRIPTION>

## Difficulty & Effort

- **Difficulty**: <LOW|MEDIUM|HIGH>
- **Estimated Effort**: <TIME_ESTIMATE>
- **Dependencies**: <DEPENDENCIES>

## Acceptance Criteria

- [ ] Replace `sorry` in theorem stub with complete proof
- [ ] Add tests in `Compiler/Proofs/YulGeneration/SmokeTests.lean` demonstrating equivalence
- [ ] Update roadmap if approach differs from plan
- [ ] CI passes (all proofs check, no new sorries)

## References

- **Roadmap**: `docs/ROADMAP.md` - Layer 3 section
- **IR Semantics**: `Compiler/Proofs/IRGeneration/IRInterpreter.lean`
- **Yul Semantics**: `Compiler/Proofs/YulGeneration/Semantics.lean`
- **Equivalence Definitions**: `Compiler/Proofs/YulGeneration/Equivalence.lean`
- **Theorem Stub**: `Compiler/Proofs/YulGeneration/StatementEquivalence.lean:<LINE_NUMBER>`

## Getting Started

1. Read the roadmap context in `docs/ROADMAP.md`
2. Review the theorem stub in `StatementEquivalence.lean`
3. Study the IR and Yul semantics for this statement type
4. Look at the worked example (variable assignment) for proof patterns
5. Replace `sorry` with your proof
6. Add smoke tests to verify your proof works

## Questions?

Ask in the PR or open a discussion. See `Compiler/Proofs/README.md` for proof development guide.
