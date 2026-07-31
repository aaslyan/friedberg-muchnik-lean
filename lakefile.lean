import Lake
open Lake DSL

package «SacksSplitting» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

/-
This project depends on the Friedberg–Muchnik development *as a package*,
not by copying: the oracle-program syntax and numbering, the step-indexed
evaluator with use recording, the use principle, the monotone-stage
approximation layer, `≤ᵀ`/`CE`/`ComputableSet`, and the Mathlib bridge are
all imported from `FriedbergMuchnik`.  Mathlib arrives transitively through
that dependency, at the same revision, so the two developments share one
`≤ᵀ`.
-/
require FriedbergMuchnik from "../friedberg-muchnik-lean"

@[default_target]
lean_lib «SacksSplitting» where
