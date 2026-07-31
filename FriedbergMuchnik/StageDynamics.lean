/-
# Stage dynamics of the construction

The specification layer over `Construction.lean`: which requirement
receives attention at a stage (`attended`), that it is the *least* one
requiring attention (the priority discipline), and exactly how the state
changes (`step_cases` — the workhorse case split every verification lemma
runs on), together with the derived dynamics:

* records of requirements of higher priority than the attended one are
  untouched (`reqs_getElem?_succ_of_lt`);
* the enumeration lists change only when a requirement acts, and then by
  exactly its witness (`Alist_succ`, `Blist_succ`);
* the freshness counter never decreases (`fresh_mono`).

In textbook terms this file is the "construction" half of Soare VII.2's
bookkeeping: everything here is about single stages; the induction over
stages (finite injury) lives in `FiniteInjury.lean`.
-/
import OracleComputability.Priority
import FriedbergMuchnik.Construction

namespace FriedbergMuchnik

/-! ### The attended requirement -/

/-- The stage-`(s+1)` pre-state: the stage-`s` state with the blank record
of the newest requirement appended (requirement `s` is born at stage
`s + 1`). -/
def preState (s : ℕ) : ConsState :=
  { stageState s with reqs := (stageState s).reqs ++ [ReqState.init] }

/-- The requirement that receives attention at stage `s + 1`, if any:
the least index requiring attention. -/
def attended (s : ℕ) : Option ℕ :=
  (List.range (preState s).reqs.length).find? fun i =>
    (preState s).requiresAttention s i

/-- The stage step, phrased through `attended`. -/
theorem stageState_succ (s : ℕ) :
    stageState (s + 1) =
      match attended s with
      | none => preState s
      | some i => (preState s).stepAt s i := rfl

@[simp] theorem preState_Alist (s : ℕ) : (preState s).Alist = (stageState s).Alist := rfl

@[simp] theorem preState_Blist (s : ℕ) : (preState s).Blist = (stageState s).Blist := rfl

@[simp] theorem preState_fresh (s : ℕ) : (preState s).fresh = (stageState s).fresh := rfl

@[simp] theorem preState_reqs_length (s : ℕ) : (preState s).reqs.length = s + 1 := by
  simp [preState, reqs_length]

/-- Below the newborn record, the pre-state's records are the stage-`s`
records. -/
theorem preState_reqs_getElem?_lt {s j : ℕ} (hj : j < s) :
    (preState s).reqs[j]? = (stageState s).reqs[j]? := by
  show ((stageState s).reqs ++ [ReqState.init])[j]? = (stageState s).reqs[j]?
  rw [List.getElem?_append_left (by rw [reqs_length]; exact hj)]

/-- The newborn record is blank. -/
theorem preState_reqs_getElem?_self (s : ℕ) :
    (preState s).reqs[s]? = some ReqState.init := by
  show ((stageState s).reqs ++ [ReqState.init])[s]? = some ReqState.init
  rw [List.getElem?_append_right (by rw [reqs_length])]
  simp [reqs_length]

/-! ### Leastness of the attended index -/

theorem attended_lt {s i : ℕ} (h : attended s = some i) : i < s + 1 := by
  have := (range_find?_least h).2.1
  rwa [preState_reqs_length] at this

theorem attended_requires {s i : ℕ} (h : attended s = some i) :
    (preState s).requiresAttention s i = true :=
  (range_find?_least h).1

/-- Priority: nothing of higher priority than the attended requirement
required attention. -/
theorem attended_least {s i : ℕ} (h : attended s = some i) :
    ∀ j, j < i → (preState s).requiresAttention s j = false :=
  (range_find?_least h).2.2

/-- Conversely, if requirement `i` requires attention then some
requirement of its priority or higher receives it. -/
theorem attended_le_of_requires {s i : ℕ} (hi : i < s + 1)
    (h : (preState s).requiresAttention s i = true) :
    ∃ j, j ≤ i ∧ attended s = some j := by
  cases hatt : attended s with
  | none =>
    rw [attended, List.find?_eq_none] at hatt
    exact absurd h (by simpa using hatt i (by simpa [preState_reqs_length] using hi))
  | some j =>
    refine ⟨j, ?_, rfl⟩
    by_contra hji
    exact absurd h (by simp [attended_least hatt i (by omega)])

/-! ### The step characterization -/

/-- **The workhorse case split.**  At stage `s + 1` exactly one of the
following happens: nobody requires attention and the state is just the
pre-state; the attended requirement appoints the counter as its witness;
or the attended requirement acts — its witness goes into its target set,
its restraint becomes the recorded use, everything of lower priority is
initialized, and the counter jumps above the new restraint. -/
theorem step_cases (s : ℕ) :
    (attended s = none ∧ stageState (s + 1) = preState s) ∨
    (∃ i r, attended s = some i ∧ (preState s).reqs[i]? = some r ∧
      r.witness = none ∧
      stageState (s + 1) =
        { preState s with
          reqs := (preState s).reqs.set i { r with witness := some (preState s).fresh }
          fresh := (preState s).fresh + 1 }) ∨
    (∃ i r x u, attended s = some i ∧ (preState s).reqs[i]? = some r ∧
      r.witness = some x ∧ r.acted = false ∧
      (preState s).convCheck s i x = some u ∧
      stageState (s + 1) =
        { Alist := if i % 2 = 0 then x :: (preState s).Alist else (preState s).Alist
          Blist := if i % 2 = 0 then (preState s).Blist else x :: (preState s).Blist
          reqs := (preState s).reqs.take i ++ (⟨some x, true, u⟩ : ReqState) ::
            List.replicate ((preState s).reqs.length - (i + 1)) ReqState.init
          fresh := max (preState s).fresh (u + 1) }) := by
  rw [stageState_succ]
  cases hatt : attended s with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some i =>
    have hreq := attended_requires hatt
    cases hri : (preState s).reqs[i]? with
    | none => simp [ConsState.requiresAttention, hri] at hreq
    | some r =>
      cases hw : r.witness with
      | none =>
        refine Or.inr (Or.inl ⟨i, r, rfl, hri, hw, ?_⟩)
        simp only [ConsState.stepAt, List.getD_eq_getElem?_getD, hri,
          Option.getD_some, hw]
      | some x =>
        rw [ConsState.requiresAttention, hri] at hreq
        simp only [hw, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          Option.isSome_iff_exists] at hreq
        obtain ⟨hact, u, hu⟩ := hreq
        refine Or.inr (Or.inr ⟨i, r, x, u, rfl, hri, hw, hact, hu, ?_⟩)
        simp only [ConsState.stepAt, List.getD_eq_getElem?_getD, hri,
          Option.getD_some, hw, hu]

/-! ### Derived dynamics -/

/-- Records of strictly higher priority than anything attended are
untouched by the step (in particular all records when nobody is
attended).  This is the *no upward injury* property of the priority
method. -/
theorem reqs_getElem?_succ_of_lt {s j : ℕ}
    (h : ∀ i, attended s = some i → j < i) :
    (stageState (s + 1)).reqs[j]? = (preState s).reqs[j]? := by
  rcases step_cases s with ⟨hn, hst⟩ | ⟨i, r, ha, hri, hw, hst⟩ |
      ⟨i, r, x, u, ha, hri, hw, hact, hu, hst⟩
  · rw [hst]
  · rw [hst]
    exact List.getElem?_set_ne (by have := h i ha; omega)
  · rw [hst]
    have hj := h i ha
    have hi : i < s + 1 := attended_lt ha
    show ((preState s).reqs.take i ++ _)[j]? = _
    rw [List.getElem?_append_left (by simp [List.length_take]; omega)]
    rw [List.getElem?_take_of_lt hj]

/-- `A` changes only by an even requirement acting, and then by exactly
its witness. -/
theorem Alist_succ (s : ℕ) :
    (stageState (s + 1)).Alist = (stageState s).Alist ∨
    ∃ i r x u, attended s = some i ∧ i % 2 = 0 ∧
      (preState s).reqs[i]? = some r ∧ r.witness = some x ∧ r.acted = false ∧
      (preState s).convCheck s i x = some u ∧
      (stageState (s + 1)).Alist = x :: (stageState s).Alist := by
  rcases step_cases s with ⟨hn, hst⟩ | ⟨i, r, ha, hri, hw, hst⟩ |
      ⟨i, r, x, u, ha, hri, hw, hact, hu, hst⟩
  · exact Or.inl (by rw [hst, preState_Alist])
  · exact Or.inl (by rw [hst]; rfl)
  · by_cases hp : i % 2 = 0
    · exact Or.inr ⟨i, r, x, u, ha, hp, hri, hw, hact, hu, by rw [hst]; simp [hp]⟩
    · exact Or.inl (by rw [hst]; simp [hp])

/-- `B` changes only by an odd requirement acting, and then by exactly
its witness. -/
theorem Blist_succ (s : ℕ) :
    (stageState (s + 1)).Blist = (stageState s).Blist ∨
    ∃ i r x u, attended s = some i ∧ i % 2 = 1 ∧
      (preState s).reqs[i]? = some r ∧ r.witness = some x ∧ r.acted = false ∧
      (preState s).convCheck s i x = some u ∧
      (stageState (s + 1)).Blist = x :: (stageState s).Blist := by
  rcases step_cases s with ⟨hn, hst⟩ | ⟨i, r, ha, hri, hw, hst⟩ |
      ⟨i, r, x, u, ha, hri, hw, hact, hu, hst⟩
  · exact Or.inl (by rw [hst, preState_Blist])
  · exact Or.inl (by rw [hst]; rfl)
  · by_cases hp : i % 2 = 0
    · exact Or.inl (by rw [hst]; simp [hp])
    · exact Or.inr ⟨i, r, x, u, ha, by omega, hri, hw, hact, hu,
        by rw [hst]; simp [hp]⟩

/-- The freshness counter never decreases. -/
theorem fresh_mono (s : ℕ) :
    (stageState s).fresh ≤ (stageState (s + 1)).fresh := by
  rcases step_cases s with ⟨hn, hst⟩ | ⟨i, r, ha, hri, hw, hst⟩ |
      ⟨i, r, x, u, ha, hri, hw, hact, hu, hst⟩
  · rw [hst]; exact le_rfl
  · rw [hst]; exact Nat.le_succ _
  · rw [hst]; exact le_max_left _ _

theorem fresh_mono_le {s t : ℕ} (h : s ≤ t) :
    (stageState s).fresh ≤ (stageState t).fresh := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (fresh_mono _)

end FriedbergMuchnik
