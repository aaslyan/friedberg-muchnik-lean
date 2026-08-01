import FriedbergMuchnik.Requirements
import FriedbergMuchnik.CE

/-!
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

namespace FriedbergMuchnik

open OracleComputability

/-- **The Friedberg–Muchnik theorem** (Friedberg 1957, Muchnik 1956;
Soare VII.2), solving Post's problem: there exist computably enumerable
sets `A, B ⊆ ℕ` with `¬(A ≤ᵀ B)` and `¬(B ≤ᵀ A)` — two incomparable
c.e. Turing degrees. -/
theorem friedberg_muchnik :
    ∃ A B : Set ℕ, CE A ∧ CE B ∧ ¬ (A ≤ᵀ B) ∧ ¬ (B ≤ᵀ A) :=
  ⟨Aset, Bset, ce_Aset, ce_Bset, not_A_le_B, not_B_le_A⟩

/-- Neither constructed set is computable (a computable set would reduce
to everything, contradicting the incomparability) — so the theorem also
certifies, inside the model, that c.e. strictly exceeds computable. -/
theorem Aset_not_computable : ¬ ComputableSet Aset :=
  fun h ↦ not_A_le_B (h.turingReducible Bset)

theorem Bset_not_computable : ¬ ComputableSet Bset :=
  fun h ↦ not_B_le_A (h.turingReducible Aset)

end FriedbergMuchnik
