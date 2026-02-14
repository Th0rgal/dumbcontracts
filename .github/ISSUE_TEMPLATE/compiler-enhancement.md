---
name: Compiler Enhancement
about: New compiler features or improvements
title: '[Compiler Enhancement] '
labels: enhancement, lean
---

## Goal
<What compiler feature or improvement>

## Motivation
- **Limitation**: <what compiler cannot do today>
- **Use case**: <real scenario this enables>

## Solution
<High-level approach>

**Example**:
```lean
// EDSL input
<example>
```
```yul
// Yul output
<expected>
```

## Implementation
1. <Component 1> - `File.lean` - <changes>
2. <Component 2> - `File.lean` - <changes>
3. Tests + proof updates

## Acceptance Criteria
- [ ] Feature builds successfully
- [ ] Existing proofs still valid
- [ ] Tests added
- [ ] Documentation updated
- [ ] CI passes

**Effort**: <hours/weeks> | **Risk**: LOW | MEDIUM | HIGH

## References
- Specs: `Compiler/Specs.lean`
- IR: `Compiler/IR.lean`
- Codegen: `Compiler/Codegen.lean`
