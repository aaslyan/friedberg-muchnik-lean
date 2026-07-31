/-
# Two finite-injury priority arguments over one oracle model

The root module, and the one place where the two theorems meet.

```
OracleComputability     the machine model, the use principle, ≤ᵀ / CE,
        │               the Mathlib bridge, the restraint mechanism
        ├──────────────┐
        ▼              ▼
FriedbergMuchnik   SacksSplitting
        └──────┬───────┘
               ▼
      PriorityArguments      (this file)
```

`FriedbergMuchnik` and `SacksSplitting` are **siblings**: neither imports
the other, and Lake enforces that.  This is not a tidiness point — it is
the development's main structural claim.  The second theorem was built on
the first's foundation and needed nothing from the first's *proof*, and
the import graph is the evidence.

There is exactly one thing the two have to say to each other, and it is
below: Friedberg–Muchnik produces a set that is c.e. and non-computable,
which is precisely the hypothesis Sacks splitting consumes.  So the first
theorem supplies a witness that the second is not vacuous.
-/
import OracleComputability
import FriedbergMuchnik
import SacksSplitting

namespace PriorityArguments

open OracleComputability
open FriedbergMuchnik

/-- **The two theorems, composed.**  `Aset` — one of the incomparable c.e.
sets built by the Friedberg–Muchnik construction — is c.e. (`ce_Aset`) and
not computable (`Aset_not_computable`), so it satisfies the hypotheses of
the Sacks Splitting Theorem and splits into two c.e. halves, neither of
which computes it.

This is the only declaration in the repository that depends on both
priority arguments, and it is why non-vacuity of `sacks_splitting` is
proved here rather than asserted. -/
theorem friedbergMuchnik_set_splits :
    ∃ A₀ A₁ : Set ℕ, CE A₀ ∧ CE A₁ ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = Aset ∧
      ¬ (Aset ≤ᵀ A₀) ∧ ¬ (Aset ≤ᵀ A₁) :=
  SacksSplitting.sacks_splitting Aset ce_Aset Aset_not_computable

/-- The mirror statement for the other half of the Friedberg–Muchnik
pair. -/
theorem friedbergMuchnik_set_splits' :
    ∃ B₀ B₁ : Set ℕ, CE B₀ ∧ CE B₁ ∧ Disjoint B₀ B₁ ∧ B₀ ∪ B₁ = Bset ∧
      ¬ (Bset ≤ᵀ B₀) ∧ ¬ (Bset ≤ᵀ B₁) :=
  SacksSplitting.sacks_splitting Bset ce_Bset Bset_not_computable

end PriorityArguments
