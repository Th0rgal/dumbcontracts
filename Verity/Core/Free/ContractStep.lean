import Verity.Core.Free.IRStepAttr

namespace Verity.Core.Free

/--
`contract_step` performs one controlled simplification step using only the
`ir_step` simp set.
-/
syntax (name := contractStepTac) "contract_step" : tactic

macro_rules
  | `(tactic| contract_step) =>
      `(tactic| simp only [ir_step])

end Verity.Core.Free
