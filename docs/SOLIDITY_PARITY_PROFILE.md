# Solidity-Parity Backend Profile

Issue: [#802](https://github.com/Th0rgal/verity/issues/802)

This document defines the opt-in backend profile used for deterministic output-shape alignment with Solidity-style workflows.

## Profile Levels (v1)

`v1` exposes three explicit levels:

1. `semantic` (default)
2. `solidity-parity-ordering`
3. `solidity-parity`

All levels preserve Verity's semantic guarantees. Parity levels only normalize output shape.

## Normalization Rules (v1)

| Rule ID | Description | `semantic` | `solidity-parity-ordering` | `solidity-parity` |
|---|---|---|---|---|
| `dispatch.selector.sort.asc` | Sort runtime dispatch `case` blocks by selector (ascending) | no | yes | yes |
| `helpers.funcdef.sort.lex` | Sort compiler-generated/internal helper function declarations lexicographically by name | no | yes | yes |
| `patch.pass.enable` | Enable deterministic expression patch pass | no (opt-in only) | no (opt-in only) | yes (forced on) |

## Reproducibility Contract

For a fixed source, fixed profile, fixed tool version, and fixed CLI options:

- emitted Yul output is deterministic;
- profile-normalized ordering is stable across repeated runs;
- profile behavior is fully opt-in (`semantic` remains default).

## Non-Goals (v1)

`v1` does not attempt full byte-for-byte `solc` output identity. In particular:

- it does not rewrite all helper naming patterns to mirror `solc` internals;
- it does not force ABI/content layout rewrites beyond documented deterministic normalizations;
- it does not weaken verification constraints to chase shape parity.

Future versions can add additional rules with explicit IDs and migration notes.
