---
name: Compiler Enhancement
about: Track new compiler features or improvements
title: '[Compiler Enhancement] <DESCRIPTION>'
labels: enhancement, lean
assignees: ''
---

## Goal

<Brief description of the compiler feature or improvement>

## Motivation

**Current Limitation**: <What the compiler cannot do today>
**Use Case**: <Real-world scenario this enables>
**Impact**: <Who benefits and how>

## Proposed Solution

<High-level description of the approach>

### Design

<Describe the technical design - new IR nodes, compiler passes, etc.>

### Example

**Input (EDSL)**:
```lean
<Example contract code>
```

**Output (Yul)**:
```yul
<Expected generated Yul code>
```

## Implementation Plan

### 1. <Component Name> (e.g., IR Extension)
**File**: `Compiler/IR.lean`
**Changes**: <Description>

```lean
<Code example if relevant>
```

### 2. <Component Name> (e.g., Codegen)
**File**: `Compiler/Codegen.lean`
**Changes**: <Description>

### 3. <Component Name> (e.g., Proof Updates)
**File**: `Compiler/Proofs/`
**Changes**: <Description>

## Testing Strategy

- [ ] Unit tests for new IR nodes/expressions
- [ ] Integration tests in `test/` using Foundry
- [ ] Proof updates to maintain verification guarantees
- [ ] Example contract demonstrating the feature

## Alternatives Considered

### Alternative A: <APPROACH_NAME>
**Why not chosen**: <Reasoning>

### Alternative B: <APPROACH_NAME>
**Why not chosen**: <Reasoning>

## Acceptance Criteria

- [ ] Feature implemented and builds successfully
- [ ] All existing proofs still valid (no broken theorems)
- [ ] Tests added and passing
- [ ] Documentation updated (`README.md`, `Compiler/Specs.lean`)
- [ ] Example added to `DumbContracts/Examples/` if user-facing
- [ ] CI passes

## Effort Estimate

**Estimated Time**: <TIME_ESTIMATE>
**Difficulty**: <LOW|MEDIUM|HIGH>
**Risk Level**: <LOW|MEDIUM|HIGH>

## References

- **Compiler Specs**: `Compiler/Specs.lean`
- **IR Types**: `Compiler/IR.lean`
- **Yul Types**: `Compiler/Yul.lean`
- **Codegen**: `Compiler/Codegen.lean`
- **Related Issues**: <Links>

## Questions?

Ask in the PR or open a discussion. See `CONTRIBUTING.md` for development guide.
