/-
# The Friedberg–Muchnik theorem

Final assembly.  Everything below is stated in the project's ordinary
computability vocabulary from `Foundation/Reducibility.lean`:

* `CE A` — `A` is the halting domain of an oracle-free program
  (`A = W_e`);
* `A ≤ᵀ B` — some oracle program computes the characteristic function of
  `A` from an oracle for `B`.

The witnesses are the two sets enumerated by the finite-injury priority
construction: `Aset` and `Bset` from `Construction.lean`.  Their
c.e.-ness is `CE.lean` (the construction is computable); the two
non-reducibilities are `Requirements.lean` (every requirement of the
priority argument is satisfied).
-/
import FriedbergMuchnik.Requirements
import FriedbergMuchnik.CE

namespace FriedbergMuchnik

/-- **The Friedberg–Muchnik theorem** (Friedberg 1957, Muchnik 1956;
Soare VII.2), solving Post's problem: there exist computably enumerable
sets `A, B ⊆ ℕ` with `¬(A ≤ᵀ B)` and `¬(B ≤ᵀ A)` — two incomparable
c.e. Turing degrees. -/
theorem friedberg_muchnik :
    ∃ A B : Set ℕ, CE A ∧ CE B ∧ ¬ (A ≤ᵀ B) ∧ ¬ (B ≤ᵀ A) :=
  ⟨Aset, Bset, ce_Aset, ce_Bset, not_A_le_B, not_B_le_A⟩

end FriedbergMuchnik
