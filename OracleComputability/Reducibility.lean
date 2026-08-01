import Mathlib.Data.Set.Basic
import OracleComputability.InfiniteEval

/-!
# Turing reducibility and computable enumerability, project vocabulary

This file fixes the computability-theoretic vocabulary in which the final
Friedberg–Muchnik theorem is stated:

* `A ≤ᵀ B` — some oracle program, run with (the characteristic function of)
  `B` as its oracle, computes the characteristic function of `A`;
* `CE A` — `A` is the halting domain of some program run with *no* oracle
  information (the classical "A = W_e");
* `ComputableSet A` — some oracle-free run computes the characteristic
  function of `A` everywhere.

These definitions are deliberately project-local (see README).  The
foundational hygiene results making `≤ᵀ` recognizably *Turing* reducibility
— reflexivity here, computable sets reduce to every oracle here, adequacy of
the program enumeration in `Numbering.lean`, the Mathlib correspondence in
`MathlibBridge.lean`, and closure under composition in a later file — are
part of the project's foundation obligations, not afterthoughts.
-/

namespace OracleComputability

open Classical in
/-- The characteristic function of a set of naturals (classical: sets are
arbitrary `Set ℕ`, no decidability assumed). -/
noncomputable def charFun (A : Set ℕ) : ℕ → Bool :=
  fun n ↦ decide (n ∈ A)

open Classical in
@[simp] theorem charFun_eq_true {A : Set ℕ} {n : ℕ} :
    charFun A n = true ↔ n ∈ A := by
  simp [charFun]

open Classical in
@[simp] theorem charFun_eq_false {A : Set ℕ} {n : ℕ} :
    charFun A n = false ↔ n ∉ A := by
  simp [charFun]

/-- The output an oracle program must produce to correctly report the
membership bit `b`: `1` for `true`, `0` for `false`. -/
def natOfBool (b : Bool) : ℕ := cond b 1 0

/-- **Turing reducibility** (project vocabulary).  `A ≤ᵀ B` iff some oracle
program, with `B`'s characteristic function as its oracle, halts on every
input `x` and outputs the membership bit of `x` in `A`. -/
def TuringReducible (A B : Set ℕ) : Prop :=
  ∃ c : OracleCode, ∀ x : ℕ, Computes c (charFun B) x (natOfBool (charFun A x))

@[inherit_doc] scoped infix:50 " ≤ᵀ " => TuringReducible

/-- **Computably enumerable** (project vocabulary): `A` is the halting
domain of some program run with the empty oracle — the classical `A = W_e`.
The construction will discharge this for its two sets via the Mathlib
bridge, by exhibiting their monotone stage enumerations as computable. -/
def CE (A : Set ℕ) : Prop :=
  ∃ c : OracleCode, ∀ x : ℕ, x ∈ A ↔ ∃ k d, run k PartOracle.empty c x = .halt d

/-- **Computable set** (project vocabulary): some program with the empty
oracle computes the characteristic function of `A` everywhere. -/
def ComputableSet (A : Set ℕ) : Prop :=
  ∃ c : OracleCode, ∀ x : ℕ,
    ∃ k d, run k PartOracle.empty c x = .halt d ∧ d.output = natOfBool (charFun A x)

/-- `≤ᵀ` is reflexive: the single `query` instruction reduces `A` to `A`.
(Sanity: the reduction relation is about oracle access, not a triviality of
the encoding.) -/
theorem TuringReducible.refl (A : Set ℕ) : A ≤ᵀ A := by
  refine ⟨.query, fun x ↦ ⟨x + 2, ⟨natOfBool (charFun A x), x + 1⟩, ?_, rfl⟩⟩
  exact run_query_some (by omega) rfl

/-- A computable set is Turing reducible to *every* oracle: the reduction
simply never queries.  (This is the sanity theorem that killed the
prefix-monotone-string design: had the construction's limit sets been
computable, they would in particular have been reducible to each other.) -/
theorem ComputableSet.turingReducible {A : Set ℕ} (h : ComputableSet A)
    (B : Set ℕ) : A ≤ᵀ B := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun x ↦ ?_⟩
  obtain ⟨k, d, hr, hout⟩ := hc x
  refine ⟨k, d, ?_, hout⟩
  refine run_halt_mono le_rfl (fun i _ b hb ↦ ?_) hr
  rw [PartOracle.empty_apply] at hb
  exact absurd hb (by simp)

/- `ComputableSet A → CE A` (compose the decider with a search that diverges
on membership bit `0`) belongs to the code-building toolkit of the bridge /
composition layer and is deferred there.  It is not needed for the
Friedberg–Muchnik theorem: the constructed sets are proved c.e. directly
from their monotone stage enumerations. -/

end OracleComputability
