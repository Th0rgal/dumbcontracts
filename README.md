# Dumb Contracts

Lean specs + Lean proofs -> Yul/EVM.

**Start**
```bash
cd /workspaces/mission-a7986e44/dumbcontracts/research/lean_only_proto
PATH=/opt/lean-4.27.0/bin:$PATH lake build
./scripts/end_to_end.sh
```

**Make A Contract (Lean)**
1. Write spec + function in `dumbcontracts/research/lean_only_proto/DumbContracts/Examples.lean`.
2. Add selector + dispatcher in `dumbcontracts/research/lean_only_proto/DumbContracts/Compiler.lean`.
3. Emit Yul in `dumbcontracts/research/lean_only_proto/Main.lean`.
4. Rebuild with `./scripts/end_to_end.sh`.

**Spec Pattern**
```
def mySpecR : SpecR Store := { requires := ..., ensures := ..., reverts := ... }
theorem mySpec_ok : mySpecR.requires s -> ... := by ...
theorem mySpec_reverts : mySpecR.reverts s -> ... := by ...
```

**Docs**
- Docs site (Next.js): `dumbcontracts/docs-site`
- Status: `dumbcontracts/STATUS.md`
- Roadmap: `dumbcontracts/docs/roadmap.md`
- Research log: `dumbcontracts/docs/research-log.md`

**Deploy Docs (Vercel)**
1. Create a new Vercel project from this repo.
2. Set the Root Directory to `docs-site`.
3. Deploy (defaults are fine for Next.js).
