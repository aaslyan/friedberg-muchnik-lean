/-
# The splitting construction

Classical source: Soare, *Recursively Enumerable Sets and Degrees*, VII.3
(the Sacks Splitting Theorem).

The machine is much smaller than Friedberg–Muchnik's, and for a structural
reason: **it makes no positive moves.**  FM's stage picks a requirement,
appoints witnesses, enumerates them and initialises everything below.  A
splitting stage does exactly one thing: for each number that `A`'s own
enumeration produces, decide which half it goes into.

The routing rule (Soare VII.3): a new number `x` is kept out of the half
protected by the **highest-priority requirement that restrains it**.  If
requirement `j` is the least index with `x < R(j, s)`, then `x` is put into
half `1 - j % 2` — the half `N_j` is *not* using as an oracle.  If no
requirement restrains `x`, it goes into `A₀`.  So the highest-priority
requirement demanding protection from `x` always gets it; lower-priority
ones may be injured, and that is the whole injury mechanism.

Two design points worth naming, both forced by the mathematics:

* **The restraint is cumulative.**  `R(j, s+1) = max (R(j, s))
  (restraintAt … s j)`, kept in the state.  The raw stage restraint is not
  monotone — the length of agreement drops whenever a number below it
  enters `A` — and a restraint that can drop protects nothing: a
  computation frozen at stage `s` could be destroyed at stage `t > s`
  merely because the requirement had temporarily stopped asking.  Taking
  the running maximum is what makes `restraint_respected` (in
  `FiniteInjury.lean`) provable at all.  FM needed no such device because
  its restraint is written once, when the requirement acts.
* **The state is a plain tuple.**  `Primcodable` is then automatic, which
  is what lets `CE.lean` skip FM's shadow-implementation layer entirely.

The two invariants of the construction — the halves stay disjoint, and
their union is the current stage of `A` — replace FM's ten-field
`ConsInv`.  There is nothing here to keep fresh, distinct or unrestrained:
the elements are not ours to choose.
-/
import SacksSplitting.Requirements

namespace SacksSplitting

open FriedbergMuchnik

/-! ### Indexing a list of per-requirement data -/

theorem getD_map_range {f : ℕ → ℕ} {n j : ℕ} :
    ((List.range n).map f).getD j 0 = if j < n then f j else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : j < n
  · rw [List.getElem?_range h, if_pos h]; rfl
  · rw [List.getElem?_eq_none (by simp; omega), if_neg h]; rfl

/-! ### The stage step -/

/-- The cumulative restraints after stage `s`: requirement `j ≤ s` keeps
the larger of what it had and what its current agreement demands.  (The
running maximum is essential; see the file docstring.) -/
def newRestraints (ec : ℕ) (st : State) (s : ℕ) : List ℕ :=
  (List.range (s + 1)).map fun j => max (st.2.2.getD j 0) (restraintAt ec st s j)

/-- **The routing rule.**  A new element `x` is sent to the half *not*
used as an oracle by the highest-priority requirement that restrains it;
if nothing restrains it, to `A₀`. -/
def routeTo (rs : List ℕ) (s x : ℕ) : ℕ :=
  match (List.range (s + 1)).find? fun j => decide (x < rs.getD j 0) with
  | none => 0
  | some j => if j % 2 = 0 then 1 else 0

theorem routeTo_lt_two (rs : List ℕ) (s x : ℕ) : routeTo rs s x < 2 := by
  unfold routeTo
  split
  · omega
  · split <;> omega

/-- The routing itself, with the restraint list `rs` and the arriving
numbers `new` already computed.  Splitting the step this way keeps the
`Primrec` derivation in `CE.lean` shallow: the expensive `newRestraints`
is evaluated once, outside the per-element predicate. -/
def stepWith (rs new : List ℕ) (st : State) (s : ℕ) : State :=
  (filterB (fun x => decide (routeTo rs s x = 0)) new ++ st.1,
   filterB (fun x => decide (routeTo rs s x = 1)) new ++ st.2.1,
   rs)

/-- One stage: route each number that `A` enumerates at this stage, and
update the cumulative restraints. -/
def step (ec : ℕ) (st : State) (s : ℕ) : State :=
  stepWith (newRestraints ec st s) (newAt ec s) st s

/-- The construction: state after stage `s`. -/
def stageState (ec : ℕ) : ℕ → State
  | 0 => ([], [], [])
  | s + 1 => step ec (stageState ec s) s

/-- The half of `A` that requirement `j` uses as its oracle, after stage
`s`. -/
def halfList (ec : ℕ) (j s : ℕ) : List ℕ := oracleOf (stageState ec s) j

/-- The same, as a `Finset`, in the shape FM's approximation layer
consumes. -/
def halfF (ec : ℕ) (j s : ℕ) : Finset ℕ := (halfList ec j s).toFinset

/-- The limit half. -/
def halfSet (ec : ℕ) (j : ℕ) : Set ℕ := limitSet (halfF ec j)

/-- **The cumulative restraint** of requirement `j` after stage `s`. -/
def Rest (ec : ℕ) (s j : ℕ) : ℕ := (stageState ec s).2.2.getD j 0

/-! ### The restraint list -/

theorem restraints_length (ec s : ℕ) : (stageState ec s).2.2.length = s := by
  induction s with
  | zero => rfl
  | succ s _ => simp [stageState, step, stepWith, newRestraints]

theorem Rest_zero_of_le {ec s j : ℕ} (h : s ≤ j) : Rest ec s j = 0 := by
  rw [Rest, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [restraints_length]; omega)]
  rfl

theorem Rest_succ_of_le {ec s j : ℕ} (h : j ≤ s) :
    Rest ec (s + 1) j = max (Rest ec s j) (restraintAt ec (stageState ec s) s j) := by
  show (newRestraints ec (stageState ec s) s).getD j 0 = _
  rw [newRestraints, getD_map_range, if_pos (by omega)]
  rfl

theorem restraintAt_le_Rest {ec s j : ℕ} (h : j ≤ s) :
    restraintAt ec (stageState ec s) s j ≤ Rest ec (s + 1) j := by
  rw [Rest_succ_of_le h]; exact le_max_right _ _

theorem Rest_step (ec s j : ℕ) : Rest ec s j ≤ Rest ec (s + 1) j := by
  rcases Nat.lt_or_ge s j with h | h
  swap
  · rw [Rest_succ_of_le h]; exact le_max_left _ _
  · rw [Rest_zero_of_le (by omega)]; exact Nat.zero_le _

theorem Rest_mono {ec j s t : ℕ} (h : s ≤ t) : Rest ec s j ≤ Rest ec t j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (Rest_step _ _ _)

/-! ### How the halves change -/

/-- The step, seen from requirement `j`'s half: the numbers routed to
`j % 2` are prepended, nothing is ever removed. -/
theorem halfList_succ (ec j s : ℕ) :
    halfList ec j (s + 1) =
      filterB (fun x => decide
          (routeTo (newRestraints ec (stageState ec s) s) s x = j % 2))
        (newAt ec s) ++ halfList ec j s := by
  unfold halfList oracleOf
  by_cases h : j % 2 = 0
  · rw [if_pos h, if_pos h, h]; rfl
  · rw [if_neg h, if_neg h, show j % 2 = 1 by omega]; rfl

theorem mem_halfList_succ {ec j s x : ℕ} :
    x ∈ halfList ec j (s + 1) ↔
      (x ∈ newAt ec s ∧
        routeTo (newRestraints ec (stageState ec s) s) s x = j % 2) ∨
      x ∈ halfList ec j s := by
  rw [halfList_succ, List.mem_append, mem_filterB, decide_eq_true_iff]

theorem halfList_subset {ec j s x : ℕ} (h : x ∈ halfList ec j s) :
    x ∈ halfList ec j (s + 1) :=
  mem_halfList_succ.mpr (Or.inr h)

theorem halfF_mono (ec j : ℕ) : StageMono (halfF ec j) := by
  intro s x hx
  rw [halfF, List.mem_toFinset] at hx ⊢
  exact halfList_subset hx

theorem mem_halfF {ec j s x : ℕ} : x ∈ halfF ec j s ↔ x ∈ halfList ec j s :=
  List.mem_toFinset

theorem mem_halfSet {ec j x : ℕ} : x ∈ halfSet ec j ↔ ∃ s, x ∈ halfList ec j s := by
  rw [halfSet, mem_limitSet]
  exact exists_congr fun _ => mem_halfF

/-- The halves depend on the requirement index only through its parity. -/
theorem halfSet_mod_two (ec j : ℕ) : halfSet ec (j % 2) = halfSet ec j := by
  unfold halfSet halfF halfList
  simp only [oracleOf_mod_two]

/-! ### The two invariants

These replace FM's ten-field `ConsInv`: there are no witnesses to keep
fresh or distinct, so all that is left to maintain is that the halves
partition the current stage of `A`. -/

/-- **The union invariant**: after every stage the two halves together are
exactly the current stage of `A`. -/
theorem stage_union (ec s x : ℕ) :
    (x ∈ halfList ec 0 s ∨ x ∈ halfList ec 1 s) ↔ x ∈ enumStage ec s := by
  induction s with
  | zero =>
    constructor
    · rintro (h | h) <;> exact absurd h (by simp [halfList, oracleOf, stageState])
    · intro h
      exact absurd h (by simp [enumStage, filterB])
  | succ s ih =>
    rw [mem_halfList_succ, mem_halfList_succ, mem_enumStage_succ, ← ih]
    have h0 : (0 : ℕ) % 2 = 0 := rfl
    have h1 : (1 : ℕ) % 2 = 1 := rfl
    rw [h0, h1]
    constructor
    · rintro ((⟨hn, -⟩ | h) | (⟨hn, -⟩ | h))
      · exact Or.inl hn
      · exact Or.inr (Or.inl h)
      · exact Or.inl hn
      · exact Or.inr (Or.inr h)
    · rintro (hn | (h | h))
      · have h2 := routeTo_lt_two (newRestraints ec (stageState ec s) s) s x
        by_cases hr : routeTo (newRestraints ec (stageState ec s) s) s x = 0
        · exact Or.inl (Or.inl ⟨hn, hr⟩)
        · exact Or.inr (Or.inl ⟨hn, by omega⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

/-- **The disjointness invariant**: a number is routed to one half only. -/
theorem stage_disjoint (ec s x : ℕ) (h0 : x ∈ halfList ec 0 s) :
    x ∉ halfList ec 1 s := by
  induction s with
  | zero => exact absurd h0 (by simp [halfList, oracleOf, stageState])
  | succ s ih =>
    intro h1
    rw [mem_halfList_succ] at h0 h1
    have e0 : (0 : ℕ) % 2 = 0 := rfl
    have e1 : (1 : ℕ) % 2 = 1 := rfl
    rw [e0] at h0
    rw [e1] at h1
    rcases h0 with ⟨hn0, hr0⟩ | hold0
    · rcases h1 with ⟨-, hr1⟩ | hold1
      · omega
      · exact (mem_newAt.mp hn0).2 ((stage_union ec s x).mp (Or.inr hold1))
    · rcases h1 with ⟨hn1, -⟩ | hold1
      · exact (mem_newAt.mp hn1).2 ((stage_union ec s x).mp (Or.inl hold0))
      · exact ih hold0 hold1

/-! ### The two invariants, in the limit -/

theorem union_halfSet (ec : ℕ) : halfSet ec 0 ∪ halfSet ec 1 = enumSet ec := by
  ext x
  constructor
  · rintro (h | h) <;> obtain ⟨s, hs⟩ := mem_halfSet.mp h
    · exact mem_enumStageF.mpr ((stage_union ec s x).mp (Or.inl hs)) |> fun h' =>
        mem_limitSet.mpr ⟨s, h'⟩
    · exact mem_enumStageF.mpr ((stage_union ec s x).mp (Or.inr hs)) |> fun h' =>
        mem_limitSet.mpr ⟨s, h'⟩
  · intro h
    obtain ⟨s, hs⟩ := mem_limitSet.mp h
    rcases (stage_union ec s x).mpr (mem_enumStageF.mp hs) with h' | h'
    · exact Or.inl (mem_halfSet.mpr ⟨s, h'⟩)
    · exact Or.inr (mem_halfSet.mpr ⟨s, h'⟩)

theorem disjoint_halfSet (ec : ℕ) : Disjoint (halfSet ec 0) (halfSet ec 1) := by
  rw [Set.disjoint_left]
  intro x hx0 hx1
  obtain ⟨s, hs⟩ := mem_halfSet.mp hx0
  obtain ⟨t, ht⟩ := mem_halfSet.mp hx1
  have hs' : x ∈ halfList ec 0 (max s t) :=
    mem_halfF.mp ((halfF_mono ec 0).subset_of_le (le_max_left s t) (mem_halfF.mpr hs))
  have ht' : x ∈ halfList ec 1 (max s t) :=
    mem_halfF.mp ((halfF_mono ec 1).subset_of_le (le_max_right s t) (mem_halfF.mpr ht))
  exact stage_disjoint ec (max s t) x hs' ht'

end SacksSplitting
