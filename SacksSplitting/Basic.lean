/-
# The given c.e. set, as a computable stage enumeration

Sacks splitting starts from a *given* c.e. set `A` and partitions it; the
Friedberg–Muchnik construction started from nothing.  That difference shows
up immediately, and this file is where it is paid for.

`FriedbergMuchnik`'s `CE A` says `A` is the halting domain of some
oracle-free program.  Everything downstream, though, needs `A` as a
`⊆`-monotone sequence of finite stages that the construction can *watch*:
the splitting machine reacts to `A`'s enumeration, so it needs to know, at
stage `s`, exactly which numbers have shown up.  So this file turns the
existential `CE` statement into an explicit stage function

```
enumStage ec s = { x < s | the program numbered ec halts on x within fuel s }
```

and proves it monotone with the right limit.  Nothing here needs a new
foundational idea — `run_halt_fuel_mono` (FM's use principle, fuel form)
is the whole content — but it is a step FM never had to take, because FM
only ever *produced* `CE` facts and never *consumed* one.

Everything in this file is deliberately built from `nrun`, the numbered-code
form of the evaluator, so that `CE.lean` can show it primitive recursive.
-/
import FriedbergMuchnik

namespace SacksSplitting

open FriedbergMuchnik

/-! ### A Boolean filter written as a `foldr`

`List.filter` has no `Primrec` lemma in Mathlib, but `List.foldr` does, so
every filtering step of the construction goes through this. -/

/-- Keep the elements of `l` satisfying the Boolean predicate `p`.
Written with `cond`, which is exactly the shape `Primrec.cond` consumes. -/
def filterB (p : ℕ → Bool) (l : List ℕ) : List ℕ :=
  l.foldr (fun a acc => cond (p a) (a :: acc) acc) []

@[simp] theorem filterB_nil (p : ℕ → Bool) : filterB p [] = [] := rfl

theorem mem_filterB {p : ℕ → Bool} {l : List ℕ} {x : ℕ} :
    x ∈ filterB p l ↔ x ∈ l ∧ p x = true := by
  induction l with
  | nil => simp [filterB]
  | cons a l ih =>
    have hcons : filterB p (a :: l) =
        cond (p a) (a :: filterB p l) (filterB p l) := rfl
    by_cases hp : p a
    · rw [hcons, hp, Bool.cond_true, List.mem_cons, ih, List.mem_cons]
      constructor
      · rintro (rfl | ⟨h, hx⟩)
        · exact ⟨Or.inl rfl, hp⟩
        · exact ⟨Or.inr h, hx⟩
      · rintro ⟨rfl | h, hx⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h, hx⟩
    · rw [hcons, show p a = false by simpa using hp, Bool.cond_false, ih, List.mem_cons]
      constructor
      · rintro ⟨h, hx⟩; exact ⟨Or.inr h, hx⟩
      · rintro ⟨rfl | h, hx⟩
        · exact absurd hx (by simp [hp])
        · exact ⟨h, hx⟩

/-! ### The stage enumeration of the set with code number `ec` -/

/-- The oracle-free evaluator on numbered codes: `haltsBy s ec x` is true
when program number `ec`, run with no oracle information, halts on `x`
within fuel `s`.  (`2 ≤ ·` is `encodeResult`'s "halt" test.) -/
def haltsBy (ec s x : ℕ) : Bool := decide (2 ≤ nrun s [] ec x)

/-- The empty snapshot is the empty oracle. -/
theorem ofSnapshot_nil : PartOracle.ofSnapshot [] = PartOracle.empty := by
  funext n
  simp [PartOracle.ofSnapshot, PartOracle.empty]

theorem haltsBy_iff {ec s x : ℕ} :
    haltsBy ec s x = true ↔
      ∃ d, run s PartOracle.empty (OracleCode.ofNatCode ec) x = .halt d := by
  rw [haltsBy, decide_eq_true_iff, nrun, ofSnapshot_nil]
  exact two_le_encodeResult_iff

theorem haltsBy_mono {ec s s' x : ℕ} (h : s ≤ s') (hx : haltsBy ec s x = true) :
    haltsBy ec s' x = true := by
  obtain ⟨d, hd⟩ := haltsBy_iff.mp hx
  exact haltsBy_iff.mpr ⟨d, run_halt_fuel_mono h hd⟩

/-- **Stage `s` of the enumeration of `W_ec`**: the numbers below `s` on
which program number `ec` has already halted with fuel `s`.  This is the
`⊆`-monotone finite-stage approximation the splitting construction watches. -/
def enumStage (ec s : ℕ) : List ℕ :=
  filterB (fun x => haltsBy ec s x) (List.range s)

theorem mem_enumStage {ec s x : ℕ} :
    x ∈ enumStage ec s ↔ x < s ∧ haltsBy ec s x = true := by
  rw [enumStage, mem_filterB, List.mem_range]

/-- Stages grow: enumeration without removal. -/
theorem enumStage_subset {ec s s' x : ℕ} (h : s ≤ s') (hx : x ∈ enumStage ec s) :
    x ∈ enumStage ec s' := by
  rw [mem_enumStage] at hx ⊢
  exact ⟨lt_of_lt_of_le hx.1 h, haltsBy_mono h hx.2⟩

/-- The finite stage as a `Finset`, in the shape FM's approximation layer
consumes. -/
def enumStageF (ec s : ℕ) : Finset ℕ := (enumStage ec s).toFinset

theorem mem_enumStageF {ec s x : ℕ} : x ∈ enumStageF ec s ↔ x ∈ enumStage ec s :=
  List.mem_toFinset

theorem enumStageF_mono (ec : ℕ) : StageMono (enumStageF ec) := by
  intro s x hx
  rw [mem_enumStageF] at hx ⊢
  exact enumStage_subset (Nat.le_succ s) hx

/-- The set enumerated by program number `ec`. -/
def enumSet (ec : ℕ) : Set ℕ := limitSet (enumStageF ec)

theorem mem_enumSet {ec x : ℕ} :
    x ∈ enumSet ec ↔
      ∃ k d, run k PartOracle.empty (OracleCode.ofNatCode ec) x = .halt d := by
  rw [enumSet, mem_limitSet]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨d, hd⟩ := haltsBy_iff.mp (mem_enumStage.mp (mem_enumStageF.mp hs)).2
    exact ⟨s, d, hd⟩
  · rintro ⟨k, d, hd⟩
    refine ⟨max k (x + 1), mem_enumStageF.mpr (mem_enumStage.mpr ⟨by omega, ?_⟩)⟩
    exact haltsBy_iff.mpr ⟨d, run_halt_fuel_mono (by omega) hd⟩

/-- **Every c.e. set is one of the `enumSet`s.**  This is the bridge from
FM's `CE` (an existential over programs) to the explicit stage enumeration
the construction reacts to. -/
theorem ce_eq_enumSet {A : Set ℕ} (h : CE A) : ∃ ec, A = enumSet ec := by
  obtain ⟨c, hc⟩ := h
  refine ⟨OracleCode.encodeCode c, ?_⟩
  ext x
  rw [hc x, mem_enumSet, OracleCode.ofNatCode_encodeCode]

/-! ### The numbers entering at a stage

The construction reacts to `A`'s enumeration one stage at a time, so it
needs the numbers that appear at stage `s + 1` and not before. -/

/-- The numbers entering the enumeration at stage `s + 1`. -/
def newAt (ec s : ℕ) : List ℕ :=
  filterB (fun x => !decide (x ∈ enumStage ec s)) (enumStage ec (s + 1))

theorem mem_newAt {ec s x : ℕ} :
    x ∈ newAt ec s ↔ x ∈ enumStage ec (s + 1) ∧ x ∉ enumStage ec s := by
  rw [newAt, mem_filterB]
  simp

/-- Stage `s + 1` is stage `s` together with the new numbers. -/
theorem mem_enumStage_succ {ec s x : ℕ} :
    x ∈ enumStage ec (s + 1) ↔ x ∈ newAt ec s ∨ x ∈ enumStage ec s := by
  rw [mem_newAt]
  constructor
  · intro h
    by_cases hs : x ∈ enumStage ec s
    · exact Or.inr hs
    · exact Or.inl ⟨h, hs⟩
  · rintro (⟨h, -⟩ | h)
    · exact h
    · exact enumStage_subset (Nat.le_succ s) h

end SacksSplitting
