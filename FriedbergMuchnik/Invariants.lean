/-
# State invariants of the construction

The ten facts that hold of every reachable construction state, proved by
induction over the three transitions (record birth, appointment, action).
In textbook terms these are the routine observations Soare makes inline
("witnesses are fresh", "distinct requirements have distinct witnesses",
"an acted requirement's computation is preserved as long as its restraint
is respected") — here they are one structure, `ConsInv`, so that the
satisfaction proofs can cite them by name:

* freshness: the counter strictly dominates all enumerated numbers and
  witnesses, and weakly dominates all restraints — so appointed witnesses
  are new, and are `≥` every live restraint (no requirement ever injures
  a *higher*-priority one by acting);
* `coh` — a record without a witness is fully blank;
* `distinct` — live witnesses are pairwise distinct;
* `wit_ge` — a live witness respects every higher-priority restraint;
* `unacted_out` / `acted_in` — an unacted witness is in neither set; an
  acted witness is in its target set;
* `acted_comp` — **the preserved computation**: an acted requirement's
  diagonalizing run (output `0`, use = its restraint) still halts against
  a snapshot of the *current* oracle list.  Maintenance under enumeration
  is exactly the use principle: anything enumerated later is `≥` the
  restraint, hence below the use nothing changed.
-/
import FriedbergMuchnik.StageDynamics

namespace FriedbergMuchnik

/-! ### Snapshot helpers for list oracles -/

theorem snapshotOf_getElem? {l : List ℕ} {u p : ℕ} (h : p < u) :
    (snapshotOf l u)[p]? = some (decide (p ∈ l)) := by
  have hlen : p < (snapshotOf l u).length := by simpa using h
  rw [List.getElem?_eq_getElem hlen]
  simp [snapshotOf]

theorem ofSnapshot_snapshotOf_some {l : List ℕ} {u p : ℕ} {b : Bool}
    (h : PartOracle.ofSnapshot (snapshotOf l u) p = some b) :
    p < u ∧ b = decide (p ∈ l) := by
  rw [PartOracle.ofSnapshot_apply] at h
  by_cases hp : p < u
  · rw [snapshotOf_getElem? hp] at h
    exact ⟨hp, (Option.some.inj h).symm⟩
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hp)] at h
    exact absurd h (by simp)

/-- Enumerating a number `≥` the use of a halting computation into the
oracle list does not disturb the computation (the use principle in the
form the invariant maintenance needs). -/
theorem run_halt_cons_snapshot {l : List ℕ} {x k len w : ℕ} {c : OracleCode}
    {d : HaltData} (hx : d.use ≤ x)
    (h : run k (PartOracle.ofSnapshot (snapshotOf l len)) c w = .halt d) :
    run k (PartOracle.ofSnapshot (snapshotOf (x :: l) len)) c w = .halt d := by
  refine run_halt_mono le_rfl (fun p hp b hb => ?_) h
  obtain ⟨hpl, hb'⟩ := ofSnapshot_snapshotOf_some hb
  subst hb'
  rw [PartOracle.ofSnapshot_apply, snapshotOf_getElem? hpl]
  have hpx : p ≠ x := by omega
  simp [List.mem_cons, hpx]

/-! ### Record access in the three transition shapes -/

theorem append_singleton_getElem?_cases {α : Type _} {l : List α} {b : α}
    {j : ℕ} {a : α} (h : (l ++ [b])[j]? = some a) :
    l[j]? = some a ∨ (j = l.length ∧ a = b) := by
  rcases Nat.lt_or_ge j l.length with hj | hj
  · rw [List.getElem?_append_left hj] at h
    exact Or.inl h
  · rw [List.getElem?_append_right hj] at h
    rcases Nat.eq_or_lt_of_le hj with he | hl
    · rw [← he, Nat.sub_self] at h
      exact Or.inr ⟨he.symm, (Option.some.inj h).symm⟩
    · rw [List.getElem?_eq_none (by simp; omega)] at h
      exact absurd h (by simp)

theorem set_getElem?_cases {α : Type _} {l : List α} {i j : ℕ} {b a : α}
    (h : (l.set i b)[j]? = some a) :
    (j = i ∧ i < l.length ∧ a = b) ∨ (j ≠ i ∧ l[j]? = some a) := by
  by_cases hj : j = i
  · subst hj
    have hlen : j < l.length := by
      have := (List.getElem?_eq_some_iff.mp h).1
      simpa using this
    rw [List.getElem?_set_self hlen] at h
    exact Or.inl ⟨rfl, hlen, (Option.some.inj h).symm⟩
  · rw [List.getElem?_set_ne (by omega)] at h
    exact Or.inr ⟨hj, h⟩

theorem act_reqs_getElem?_cases {l : List ReqState} {i : ℕ} {rec : ReqState}
    {j : ℕ} {a : ReqState} (hi : i < l.length)
    (h : (l.take i ++ rec ::
      List.replicate (l.length - (i + 1)) ReqState.init)[j]? = some a) :
    (j < i ∧ l[j]? = some a) ∨ (j = i ∧ a = rec) ∨ (i < j ∧ a = ReqState.init) := by
  have hlen : (l.take i).length = i := by
    simp [List.length_take]
    omega
  rcases Nat.lt_trichotomy j i with hj | rfl | hj
  · left
    refine ⟨hj, ?_⟩
    rw [List.getElem?_append_left (by rw [hlen]; omega),
      List.getElem?_take_of_lt hj] at h
    exact h
  · right; left
    rw [List.getElem?_append_right hlen.le, hlen, Nat.sub_self,
      List.getElem?_cons_zero] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩
  · right; right
    refine ⟨hj, ?_⟩
    rw [List.getElem?_append_right (by rw [hlen]; omega), hlen] at h
    have hji : j - i = (j - i - 1) + 1 := by omega
    rw [hji, List.getElem?_cons_succ, List.getElem?_replicate] at h
    split at h
    · exact (Option.some.inj h).symm
    · exact absurd h (by simp)

/-! ### The invariant -/

/-- The ten invariants of reachable construction states; see the file
docstring. -/
structure ConsInv (st : ConsState) : Prop where
  freshA : ∀ a ∈ st.Alist, a < st.fresh
  freshB : ∀ b ∈ st.Blist, b < st.fresh
  freshW : ∀ (i : ℕ) (r : ReqState) (x : ℕ), st.reqs[i]? = some r →
    r.witness = some x → x < st.fresh
  freshR : ∀ (i : ℕ) (r : ReqState), st.reqs[i]? = some r →
    r.restraint ≤ st.fresh
  coh : ∀ (i : ℕ) (r : ReqState), st.reqs[i]? = some r → r.witness = none →
    r.acted = false ∧ r.restraint = 0
  distinct : ∀ (i j : ℕ) (ri rj : ReqState) (xi xj : ℕ), i ≠ j →
    st.reqs[i]? = some ri → st.reqs[j]? = some rj → ri.witness = some xi →
    rj.witness = some xj → xi ≠ xj
  wit_ge : ∀ (i j : ℕ) (ri rj : ReqState) (xi : ℕ), j < i →
    st.reqs[i]? = some ri → st.reqs[j]? = some rj → ri.witness = some xi →
    rj.restraint ≤ xi
  unacted_out : ∀ (i : ℕ) (r : ReqState) (x : ℕ), st.reqs[i]? = some r →
    r.witness = some x → r.acted = false → x ∉ st.Alist ∧ x ∉ st.Blist
  acted_in : ∀ (i : ℕ) (r : ReqState) (x : ℕ), st.reqs[i]? = some r →
    r.witness = some x → r.acted = true → x ∈ st.targetOf i
  acted_comp : ∀ (i : ℕ) (r : ReqState) (x : ℕ), st.reqs[i]? = some r →
    r.witness = some x → r.acted = true →
    ∃ k len, run k (PartOracle.ofSnapshot (snapshotOf (st.oracleOf i) len))
      (OracleCode.ofNatCode (i / 2)) x = .halt ⟨0, r.restraint⟩

/-! ### The three transitions -/

/-- Record birth preserves the invariant: the newborn record is blank. -/
theorem consInv_ext {st : ConsState} (h : ConsInv st) :
    ConsInv { st with reqs := st.reqs ++ [ReqState.init] } := by
  obtain ⟨fA, fB, fW, fR, coh, dis, wge, uo, ai, ac⟩ := h
  refine ⟨fA, fB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i r x hri hx
    rcases append_singleton_getElem?_cases hri with hold | ⟨_, rfl⟩
    · exact fW i r x hold hx
    · simp [ReqState.init] at hx
  · intro i r hri
    rcases append_singleton_getElem?_cases hri with hold | ⟨_, rfl⟩
    · exact fR i r hold
    · simp [ReqState.init]
  · intro i r hri hw
    rcases append_singleton_getElem?_cases hri with hold | ⟨_, rfl⟩
    · exact coh i r hold hw
    · simp [ReqState.init]
  · intro i j ri rj xi xj hne hri hrj hxi hxj
    rcases append_singleton_getElem?_cases hri with hi | ⟨_, rfl⟩
    · rcases append_singleton_getElem?_cases hrj with hj | ⟨_, rfl⟩
      · exact dis i j ri rj xi xj hne hi hj hxi hxj
      · simp [ReqState.init] at hxj
    · simp [ReqState.init] at hxi
  · intro i j ri rj xi hji hri hrj hxi
    rcases append_singleton_getElem?_cases hri with hi | ⟨_, rfl⟩
    · rcases append_singleton_getElem?_cases hrj with hj | ⟨_, rfl⟩
      · exact wge i j ri rj xi hji hi hj hxi
      · simp [ReqState.init]
    · simp [ReqState.init] at hxi
  · intro i r x hri hx hact
    rcases append_singleton_getElem?_cases hri with hold | ⟨_, rfl⟩
    · exact uo i r x hold hx hact
    · simp [ReqState.init] at hx
  · intro i r x hri hx hact
    rcases append_singleton_getElem?_cases hri with hold | ⟨_, rfl⟩
    · exact ai i r x hold hx hact
    · simp [ReqState.init] at hx
  · intro i r x hri hx hact
    rcases append_singleton_getElem?_cases hri with hold | ⟨_, rfl⟩
    · exact ac i r x hold hx hact
    · simp [ReqState.init] at hx

/-- Appointment preserves the invariant: the counter value is fresh
(bigger than every enumerated number and witness, `≥` every restraint),
and the counter then moves past it. -/
theorem consInv_appoint {st : ConsState} {i : ℕ} {r : ReqState}
    (h : ConsInv st) (hri : st.reqs[i]? = some r) (hw : r.witness = none) :
    ConsInv { st with
      reqs := st.reqs.set i { r with witness := some st.fresh }
      fresh := st.fresh + 1 } := by
  obtain ⟨fA, fB, fW, fR, coh, dis, wge, uo, ai, ac⟩ := h
  obtain ⟨hact0, hres0⟩ := coh i r hri hw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact Nat.lt_succ_of_lt (fA a ha)
  · intro b hb
    exact Nat.lt_succ_of_lt (fB b hb)
  · intro j rj x hrj hx
    rcases set_getElem?_cases hrj with ⟨heq, _, rfl⟩ | ⟨hne, hold⟩
    · simp at hx ⊢
      omega
    · exact Nat.lt_succ_of_lt (fW j rj x hold hx)
  · intro j rj hrj
    rcases set_getElem?_cases hrj with ⟨heq, _, rfl⟩ | ⟨hne, hold⟩
    · simp [hres0]
    · exact (fR j rj hold).trans (Nat.le_succ _)
  · intro j rj hrj hwj
    rcases set_getElem?_cases hrj with ⟨heq, _, rfl⟩ | ⟨hne, hold⟩
    · simp at hwj
    · exact coh j rj hold hwj
  · intro a b ra rb xa xb hne hra hrb hxa hxb
    rcases set_getElem?_cases hra with ⟨heqa, _, rfl⟩ | ⟨hnea, holda⟩
    · rcases set_getElem?_cases hrb with ⟨heqb, _, _⟩ | ⟨hneb, holdb⟩
      · omega
      · simp at hxa
        have := fW b rb xb holdb hxb
        omega
    · rcases set_getElem?_cases hrb with ⟨heqb, _, rfl⟩ | ⟨hneb, holdb⟩
      · simp at hxb
        have := fW a ra xa holda hxa
        omega
      · exact dis a b ra rb xa xb hne holda holdb hxa hxb
  · intro a b ra rb xa hba hra hrb hxa
    rcases set_getElem?_cases hra with ⟨heqa, _, rfl⟩ | ⟨hnea, holda⟩
    · simp at hxa
      rcases set_getElem?_cases hrb with ⟨heqb, _, _⟩ | ⟨hneb, holdb⟩
      · omega
      · have := fR b rb holdb
        omega
    · rcases set_getElem?_cases hrb with ⟨heqb, _, rfl⟩ | ⟨hneb, holdb⟩
      · simp [hres0]
      · exact wge a b ra rb xa hba holda holdb hxa
  · intro j rj x hrj hx hactj
    rcases set_getElem?_cases hrj with ⟨heq, _, rfl⟩ | ⟨hne, hold⟩
    · simp at hx
      subst hx
      constructor
      · intro hmem
        exact absurd (fA _ hmem) (by omega)
      · intro hmem
        exact absurd (fB _ hmem) (by omega)
    · exact uo j rj x hold hx hactj
  · intro j rj x hrj hx hactj
    rcases set_getElem?_cases hrj with ⟨heq, _, rfl⟩ | ⟨hne, hold⟩
    · simp [hact0] at hactj
    · exact ai j rj x hold hx hactj
  · intro j rj x hrj hx hactj
    rcases set_getElem?_cases hrj with ⟨heq, _, rfl⟩ | ⟨hne, hold⟩
    · simp [hact0] at hactj
    · exact ac j rj x hold hx hactj

/-- Action preserves the invariant.  The enumerated witness is `≥` every
higher-priority restraint (`wit_ge`), so no preserved computation of
higher priority is disturbed (use principle); everything of lower
priority is initialized to blank. -/
theorem consInv_act {st : ConsState} {i x u : ℕ} {r : ReqState}
    (h : ConsInv st) (hri : st.reqs[i]? = some r) (hw : r.witness = some x)
    (_hact : r.acted = false)
    (hrun : ∃ k len,
      run k (PartOracle.ofSnapshot (snapshotOf (st.oracleOf i) len))
        (OracleCode.ofNatCode (i / 2)) x = .halt ⟨0, u⟩) :
    ConsInv { Alist := if i % 2 = 0 then x :: st.Alist else st.Alist
              Blist := if i % 2 = 0 then st.Blist else x :: st.Blist
              reqs := st.reqs.take i ++ (⟨some x, true, u⟩ : ReqState) ::
                List.replicate (st.reqs.length - (i + 1)) ReqState.init
              fresh := max st.fresh (u + 1) } := by
  obtain ⟨fA, fB, fW, fR, coh, dis, wge, uo, ai, ac⟩ := h
  have hi : i < st.reqs.length := (List.getElem?_eq_some_iff.mp hri).1
  have hxf : x < st.fresh := fW i r x hri hw
  have hAmem : ∀ a, a ∈ (if i % 2 = 0 then x :: st.Alist else st.Alist) →
      a = x ∨ a ∈ st.Alist := by
    intro a ha
    by_cases hp : i % 2 = 0
    · rw [if_pos hp] at ha
      exact List.mem_cons.mp ha
    · rw [if_neg hp] at ha
      exact Or.inr ha
  have hBmem : ∀ b, b ∈ (if i % 2 = 0 then st.Blist else x :: st.Blist) →
      b = x ∨ b ∈ st.Blist := by
    intro b hb
    by_cases hp : i % 2 = 0
    · rw [if_pos hp] at hb
      exact Or.inr hb
    · rw [if_neg hp] at hb
      exact List.mem_cons.mp hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases hAmem a ha with rfl | hold
    · exact lt_of_lt_of_le hxf (le_max_left _ _)
    · exact lt_of_lt_of_le (fA a hold) (le_max_left _ _)
  · intro b hb
    rcases hBmem b hb with rfl | hold
    · exact lt_of_lt_of_le hxf (le_max_left _ _)
    · exact lt_of_lt_of_le (fB b hold) (le_max_left _ _)
  · intro j rj y hrj hy
    rcases act_reqs_getElem?_cases hi hrj with ⟨hj, hold⟩ | ⟨heq, rfl⟩ | ⟨hj, rfl⟩
    · exact lt_of_lt_of_le (fW j rj y hold hy) (le_max_left _ _)
    · simp at hy
      subst hy
      exact lt_of_lt_of_le hxf (le_max_left _ _)
    · simp [ReqState.init] at hy
  · intro j rj hrj
    rcases act_reqs_getElem?_cases hi hrj with ⟨hj, hold⟩ | ⟨heq, rfl⟩ | ⟨hj, rfl⟩
    · exact (fR j rj hold).trans (le_max_left _ _)
    · exact le_trans (Nat.le_succ u) (le_max_right _ _)
    · simp [ReqState.init]
  · intro j rj hrj hwj
    rcases act_reqs_getElem?_cases hi hrj with ⟨hj, hold⟩ | ⟨heq, rfl⟩ | ⟨hj, rfl⟩
    · exact coh j rj hold hwj
    · simp at hwj
    · simp [ReqState.init]
  · intro a b ra rb xa xb hne hra hrb hxa hxb
    rcases act_reqs_getElem?_cases hi hra with ⟨ha, holda⟩ | ⟨heqa, rfl⟩ | ⟨ha, rfl⟩
    · rcases act_reqs_getElem?_cases hi hrb with ⟨hb, holdb⟩ | ⟨heqb, rfl⟩ | ⟨hb, rfl⟩
      · exact dis a b ra rb xa xb hne holda holdb hxa hxb
      · simp at hxb
        subst hxb
        have hrb' : st.reqs[b]? = some r := by rw [heqb]; exact hri
        exact dis a b ra r xa x hne holda hrb' hxa hw
      · simp [ReqState.init] at hxb
    · simp at hxa
      subst hxa
      have hra' : st.reqs[a]? = some r := by rw [heqa]; exact hri
      rcases act_reqs_getElem?_cases hi hrb with ⟨hb, holdb⟩ | ⟨heqb, _⟩ | ⟨hb, rfl⟩
      · exact dis a b r rb x xb hne hra' holdb hw hxb
      · omega
      · simp [ReqState.init] at hxb
    · simp [ReqState.init] at hxa
  · intro a b ra rb xa hba hra hrb hxa
    rcases act_reqs_getElem?_cases hi hra with ⟨ha, holda⟩ | ⟨heqa, rfl⟩ | ⟨ha, rfl⟩
    · rcases act_reqs_getElem?_cases hi hrb with ⟨hb, holdb⟩ | ⟨heqb, rfl⟩ | ⟨hb, rfl⟩
      · exact wge a b ra rb xa hba holda holdb hxa
      · omega
      · omega
    · simp at hxa
      subst hxa
      have hra' : st.reqs[a]? = some r := by rw [heqa]; exact hri
      rcases act_reqs_getElem?_cases hi hrb with ⟨hb, holdb⟩ | ⟨heqb, rfl⟩ | ⟨hb, rfl⟩
      · exact wge a b r rb x hba hra' holdb hw
      · omega
      · omega
    · simp [ReqState.init] at hxa
  · intro j rj y hrj hy hactj
    rcases act_reqs_getElem?_cases hi hrj with ⟨hj, hold⟩ | ⟨heq, rfl⟩ | ⟨hj, rfl⟩
    · obtain ⟨hoA, hoB⟩ := uo j rj y hold hy hactj
      have hyx : y ≠ x := dis j i rj r y x (by omega) hold hri hy hw
      constructor
      · intro hmem
        rcases hAmem y hmem with h' | h'
        · exact hyx h'
        · exact hoA h'
      · intro hmem
        rcases hBmem y hmem with h' | h'
        · exact hyx h'
        · exact hoB h'
    · simp at hactj
    · simp [ReqState.init] at hy
  · intro j rj y hrj hy hactj
    rcases act_reqs_getElem?_cases hi hrj with ⟨hj, hold⟩ | ⟨heq, rfl⟩ | ⟨hj, rfl⟩
    · have hold' := ai j rj y hold hy hactj
      unfold ConsState.targetOf at hold' ⊢
      by_cases hp' : j % 2 = 0 <;> by_cases hp : i % 2 = 0 <;>
        simp only [hp', hp, if_pos, if_false] at hold' ⊢ <;>
        simp [hold']
    · simp at hy
      subst hy
      rw [heq]
      unfold ConsState.targetOf
      by_cases hp : i % 2 = 0 <;> simp [hp]
    · simp [ReqState.init] at hy
  · intro j rj y hrj hy hactj
    rcases act_reqs_getElem?_cases hi hrj with ⟨hj, hold⟩ | ⟨heq, rfl⟩ | ⟨hj, rfl⟩
    · have hxr : rj.restraint ≤ x := wge i j r rj x hj hri hold hw
      obtain ⟨k, len, hk⟩ := ac j rj y hold hy hactj
      unfold ConsState.oracleOf at hk ⊢
      by_cases hp' : j % 2 = 0 <;> by_cases hp : i % 2 = 0 <;>
        simp only [hp', hp, if_true, if_false] at hk ⊢
      · exact ⟨k, len, hk⟩
      · exact ⟨k, len, run_halt_cons_snapshot hxr hk⟩
      · exact ⟨k, len, run_halt_cons_snapshot hxr hk⟩
      · exact ⟨k, len, hk⟩
    · simp at hy
      subst hy
      rw [heq]
      obtain ⟨k, len, hk⟩ := hrun
      unfold ConsState.oracleOf at hk ⊢
      by_cases hp : i % 2 = 0 <;> simp only [hp, if_true, if_false] at hk ⊢
      · exact ⟨k, len, hk⟩
      · exact ⟨k, len, hk⟩
    · simp [ReqState.init] at hy

/-! ### The invariant holds at every stage -/

/-- Every reachable construction state satisfies `ConsInv`. -/
theorem consInv_stage : ∀ s, ConsInv (stageState s)
  | 0 => by
    constructor <;> intros <;> simp_all [stageState]
  | s + 1 => by
    rcases step_cases s with ⟨hn, hst⟩ | ⟨i, r, ha, hri, hw, hst⟩ |
        ⟨i, r, x, u, ha, hri, hw, hact, hu, hst⟩
    · rw [hst]
      exact consInv_ext (consInv_stage s)
    · rw [hst]
      exact consInv_appoint (consInv_ext (consInv_stage s)) hri hw
    · rw [hst]
      exact consInv_act (consInv_ext (consInv_stage s)) hri hw hact
        ⟨s, s, ConsState.convCheck_eq_some.mp hu⟩

end FriedbergMuchnik
