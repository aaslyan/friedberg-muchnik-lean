/-
# The Sacks Splitting Theorem

Final assembly.  Everything is stated in `FriedbergMuchnik`'s own
computability vocabulary — `CE`, `ComputableSet`, `≤ᵀ` — imported from
`Foundation/Reducibility.lean`, not re-defined, so the two theorems live in
the same language and `≤ᵀ` means here exactly what it means there.

The witnesses are the two halves the routing construction enumerates.
Their computable enumerability is `CE.lean`; their disjointness and union
are `Construction.lean`; the two non-reducibilities are `FiniteInjury.lean`,
where every requirement is shown satisfied.

The last step is FM's own: a candidate reduction is *some* oracle program,
and every oracle program is `ofNatCode e` for its own number `e`
(`OracleCode.ofNatCode_encodeCode`, enumeration adequacy) — so requirement
`2e + i` kills it.  This is `not_A_le_B`'s two-line argument, reused in
shape.

Scope note: this is the splitting-with-non-reducibility core.  The full
Sacks Splitting Theorem also makes the halves *low*, which needs the
infinite-injury machinery and is deliberately out of scope here.
-/
import SacksSplitting.FiniteInjury

namespace SacksSplitting

open FriedbergMuchnik
open scoped FriedbergMuchnik

/-- Neither half computes the set it splits.  A candidate reduction is an
oracle program `c`; requirement `2 * encodeCode c + i` is the one that
refutes it. -/
theorem not_reducible_half {ec i : ℕ} (hA : ¬ ComputableSet (enumSet ec))
    (hi : i < 2) : ¬ (enumSet ec ≤ᵀ halfSet ec i) := by
  rintro ⟨c, hc⟩
  have hdiv : (2 * OracleCode.encodeCode c + i) / 2 = OracleCode.encodeCode c := by omega
  have hhalf : halfSet ec (2 * OracleCode.encodeCode c + i) = halfSet ec i := by
    rw [← halfSet_mod_two ec (2 * OracleCode.encodeCode c + i),
      show (2 * OracleCode.encodeCode c + i) % 2 = i by omega]
  refine requirement_satisfied hA (2 * OracleCode.encodeCode c + i) fun y => ?_
  rw [hdiv, hhalf, OracleCode.ofNatCode_encodeCode]
  exact hc y

/-- The theorem for the canonical enumeration `enumSet ec`. -/
theorem sacks_splitting_core (ec : ℕ) (hA : ¬ ComputableSet (enumSet ec)) :
    ∃ A₀ A₁ : Set ℕ, CE A₀ ∧ CE A₁ ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = enumSet ec ∧
      ¬ (enumSet ec ≤ᵀ A₀) ∧ ¬ (enumSet ec ≤ᵀ A₁) :=
  ⟨halfSet ec 0, halfSet ec 1, ce_halfSet ec 0, ce_halfSet ec 1,
    disjoint_halfSet ec, union_halfSet ec,
    not_reducible_half hA (by omega), not_reducible_half hA (by omega)⟩

/-- **The Sacks Splitting Theorem** (Sacks 1963; Soare VII.3), in the
splitting-with-non-reducibility form: every non-computable c.e. set splits
into two c.e. halves, neither of which computes it. -/
theorem sacks_splitting :
    ∀ A : Set ℕ, CE A → ¬ ComputableSet A →
      ∃ A₀ A₁ : Set ℕ, CE A₀ ∧ CE A₁ ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = A ∧
        ¬ (A ≤ᵀ A₀) ∧ ¬ (A ≤ᵀ A₁) := by
  intro A hce hnc
  obtain ⟨ec, rfl⟩ := ce_eq_enumSet hce
  exact sacks_splitting_core ec hnc

/-- **Non-vacuity**, and a direct consumer of Friedberg–Muchnik: the set
`Aset` built by FM's priority construction is c.e. (`ce_Aset`) and not
computable (`Aset_not_computable`), so it satisfies the hypotheses and
splits.  Both facts are imported from the FM package unchanged. -/
theorem sacks_splitting_friedbergMuchnik :
    ∃ A₀ A₁ : Set ℕ, CE A₀ ∧ CE A₁ ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = Aset ∧
      ¬ (Aset ≤ᵀ A₀) ∧ ¬ (Aset ≤ᵀ A₁) :=
  sacks_splitting Aset ce_Aset Aset_not_computable

/-- The split is non-trivial: neither half is all of `A`.  (If it were,
reflexivity of `≤ᵀ` would hand back the reduction the requirements just
ruled out — the same sanity check FM makes with
`ComputableSet.turingReducible`.) -/
theorem halfSet_ne {ec i : ℕ} (hA : ¬ ComputableSet (enumSet ec)) (hi : i < 2) :
    halfSet ec i ≠ enumSet ec := by
  intro h
  refine not_reducible_half hA hi ?_
  rw [h]
  exact TuringReducible.refl _

end SacksSplitting
