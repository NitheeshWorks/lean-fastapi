import LeanPydantic

/-!
# APIs: `α ∣ c` under `open LeanFastapi`

Constraints are refinement types: `q : Option (String ∣ maxLength 50)`,
`price : Decimal ∣ gt 0`. The notation is lean-pydantic's (Keel's
constraint language), made available by `open LeanFastapi` so that a
FastAPI module needs no second `open`.
-/

namespace LeanFastapi

/-- `α ∣ c`: the values of `α` satisfying the constraint `c`. -/
scoped syntax:50 (priority := high) term:51 " ∣ " refinement : term

macro_rules
  | `($a ∣ $r:refinement) => `(Keel.Refined $a (refinement% $r))

end LeanFastapi
