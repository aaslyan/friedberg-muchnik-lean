import SacksSplitting.Construction

/-!
# The construction is computable

Two obligations are discharged here, and it is worth saying why they are
the *same* obligation:

* the halves `A₀`, `A₁` are computably enumerable;
* the "search for a stage of long agreement" procedure of
  `FiniteInjury.lean` really is an algorithm, so that an unsatisfiable
  requirement would make the *given* set `A` computable.

Both reduce to "the stage function is primitive recursive", which is why
they live in one file.  The second is what makes the non-computability
hypothesis on `A` usable at all; FM had no analogue of it.

Compared with FM's `CE.lean` this file is much shorter, for one concrete
reason.  FM's construction state is a pair of custom structures
(`ConsState`, `ReqState`) with no `Primcodable` instance, so FM had to
build a **shadow implementation** on plain tuples (`St`, `RS`, `encSt`),
prove a simulation theorem (`encSt_stage`), and re-express its two list
surgeries as maps over `List.range` (`map_range_set`, `map_range_act`)
before any `Primrec` work could start.  Here `State` is a plain tuple from
the outset, so `Primcodable` is automatic and the shadow layer, the
simulation theorem and the surgeries all disappear.  The `Primrec`
derivation and the `Partrec.rfind` + `ce_of_partrec_dom` ending are FM's,
in shape and in tactic.

Three generic helpers — `primrec_find?`, `primrec_memDecide`,
`primrec_snapshotOf` — come from `OracleComputability.PrimrecTools`.  They
began life `private` inside Friedberg–Muchnik's own `CE.lean`, invisible to
anything downstream; that they are now shared foundation is the whole
point of the split.
-/

namespace SacksSplitting

open OracleComputability

/-! ### Filtering -/

theorem primrec_filterB {α : Type _} [Primcodable α] {p : α → ℕ → Bool} {l : α → List ℕ}
    (hp : Primrec₂ p) (hl : Primrec l) : Primrec fun a ↦ filterB (p a) (l a) :=
  Primrec.list_foldr hl (Primrec.const [])
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

/-! ### The stage enumeration of `A` -/

theorem primrec_haltsBy :
    Primrec fun q : (ℕ × ℕ) × ℕ ↦ haltsBy q.1.1 q.1.2 q.2 := by
  have hv : Primrec fun q : (ℕ × ℕ) × ℕ ↦ nrun q.1.2 [] q.1.1 q.2 :=
    nrun_primrec.comp
      ((((Primrec.snd.comp Primrec.fst).pair (Primrec.const [])).pair
        (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)
  exact (PrimrecRel.comp Primrec.nat_le (Primrec.const 2) hv).decide

theorem primrec_enumStage : Primrec₂ enumStage :=
  primrec_filterB (p := fun q : ℕ × ℕ ↦ fun x ↦ haltsBy q.1 q.2 x)
    primrec_haltsBy.to₂ (Primrec.list_range.comp Primrec.snd)

theorem primrec_memEnum :
    Primrec fun q : (ℕ × ℕ) × ℕ ↦ decide (q.2 ∈ enumStage q.1.1 q.1.2) :=
  primrec_memDecide.comp Primrec.snd (primrec_enumStage.comp
    (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))

theorem primrec_newAt : Primrec₂ newAt :=
  primrec_filterB
    (p := fun q : ℕ × ℕ ↦ fun x ↦ !decide (x ∈ enumStage q.1 q.2))
    ((Primrec.dom_bool (!·)).comp
      (primrec_memDecide.comp Primrec.snd
        (primrec_enumStage.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.fst)))).to₂
    (primrec_enumStage.comp Primrec.fst (Primrec.succ.comp Primrec.snd))

/-! ### The agreement test -/

theorem primrec_oracleOf : Primrec₂ oracleOf :=
  (Primrec.ite
    (PrimrecRel.comp Primrec.eq
      (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0))
    (Primrec.fst.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).of_eq fun q ↦ by
      simp only [oracleOf]

/-- Argument bundle of the agreement test: `(ec, st, s, j, y)`. -/
abbrev AgArgs : Type := ((ℕ × State) × ℕ × ℕ) × ℕ

private theorem ag_ec : Primrec fun w : AgArgs ↦ w.1.1.1 :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.fst)

private theorem ag_st : Primrec fun w : AgArgs ↦ w.1.1.2 :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.fst)

private theorem ag_s : Primrec fun w : AgArgs ↦ w.1.2.1 :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.fst)

private theorem ag_j : Primrec fun w : AgArgs ↦ w.1.2.2 :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.fst)

private theorem ag_y : Primrec fun w : AgArgs ↦ w.2 := Primrec.snd

set_option maxHeartbeats 1600000 in
theorem primrec_agreeAt :
    Primrec fun w : AgArgs ↦ agreeAt w.1.1.1 w.1.1.2 w.1.2.1 w.1.2.2 w.2 := by
  have hv : Primrec fun w : AgArgs ↦
      nrun w.1.2.1 (snapshotOf (oracleOf w.1.1.2 w.1.2.2) w.1.2.1)
        (w.1.2.2 / 2) w.2 :=
    nrun_primrec.comp
      (((ag_s.pair (primrec_snapshotOf.comp (primrec_oracleOf.comp ag_st ag_j) ag_s)).pair
        (Primrec.nat_div.comp ag_j (Primrec.const 2))).pair ag_y)
  have htgt : Primrec fun w : AgArgs ↦
      natOfBool (decide (w.2 ∈ enumStage w.1.1.1 w.1.2.1)) :=
    Primrec.cond
      (primrec_memEnum.comp ((ag_ec.pair ag_s).pair ag_y))
      (Primrec.const 1) (Primrec.const 0)
  exact (Primrec.ite
    (PrimrecPred.and
      (PrimrecRel.comp Primrec.nat_le (Primrec.const 2) hv)
      (PrimrecRel.comp Primrec.eq
        (Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.nat_sub.comp hv (Primrec.const 2))))
        htgt))
    (Primrec.option_some.comp
      (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.nat_sub.comp hv (Primrec.const 2)))))
    (Primrec.const none)).of_eq fun w ↦ by simp only [agreeAt, natOfBool]

/-! ### Agreement length and restraint

Both are defined by structural recursion on a bound, so both are handed to
`Primrec.nat_rec'` after being put in explicit `Nat.rec` form. -/

theorem lenAux_rec (ec : ℕ) (st : State) (s j n : ℕ) :
    lenAux ec st s j n =
      Nat.rec (motive := fun _ ↦ ℕ) 0
        (fun n m ↦ if m = n ∧ (agreeAt ec st s j n).isSome = true then n + 1 else m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (if lenAux ec st s j n = n ∧ _ then n + 1 else lenAux ec st s j n) = _
    rw [ih]

theorem restAux_rec (ec : ℕ) (st : State) (s j n : ℕ) :
    restAux ec st s j n =
      Nat.rec (motive := fun _ ↦ ℕ) 0
        (fun n m ↦ max ((agreeAt ec st s j n).getD 0) m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show max ((agreeAt ec st s j n).getD 0) (restAux ec st s j n) = _
    rw [ih]

set_option maxHeartbeats 1600000 in
theorem primrec_lenAux :
    Primrec fun w : AgArgs ↦ lenAux w.1.1.1 w.1.1.2 w.1.2.1 w.1.2.2 w.2 := by
  have hstep : Primrec₂ fun (w : AgArgs) (q : ℕ × ℕ) ↦
      if q.2 = q.1 ∧ (agreeAt w.1.1.1 w.1.1.2 w.1.2.1 w.1.2.2 q.1).isSome = true
      then q.1 + 1 else q.2 :=
    (Primrec.ite
      (PrimrecPred.and
        (PrimrecRel.comp Primrec.eq (Primrec.snd.comp Primrec.snd)
          (Primrec.fst.comp Primrec.snd))
        (PrimrecRel.comp Primrec.eq
          (Primrec.option_isSome.comp
            (primrec_agreeAt.comp
              ((((ag_ec.comp Primrec.fst).pair (ag_st.comp Primrec.fst)).pair
                ((ag_s.comp Primrec.fst).pair (ag_j.comp Primrec.fst))).pair
                (Primrec.fst.comp Primrec.snd))))
          (Primrec.const true)))
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.nat_rec' ag_y (Primrec.const 0) hstep).of_eq fun w ↦
    (lenAux_rec _ _ _ _ _).symm

theorem primrec_restAux :
    Primrec fun w : AgArgs ↦ restAux w.1.1.1 w.1.1.2 w.1.2.1 w.1.2.2 w.2 := by
  have hstep : Primrec₂ fun (w : AgArgs) (q : ℕ × ℕ) ↦
      max ((agreeAt w.1.1.1 w.1.1.2 w.1.2.1 w.1.2.2 q.1).getD 0) q.2 :=
    (Primrec.nat_max.comp
      (Primrec.option_getD.comp
        (primrec_agreeAt.comp
          ((((ag_ec.comp Primrec.fst).pair (ag_st.comp Primrec.fst)).pair
            ((ag_s.comp Primrec.fst).pair (ag_j.comp Primrec.fst))).pair
            (Primrec.fst.comp Primrec.snd)))
        (Primrec.const 0))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.nat_rec' ag_y (Primrec.const 0) hstep).of_eq fun w ↦
    (restAux_rec _ _ _ _ _).symm

/-- Argument bundle without the recursion bound: `(ec, st, s, j)`. -/
abbrev ReqArgs : Type := (ℕ × State) × ℕ × ℕ

private theorem rq_bundle : Primrec fun v : ReqArgs ↦ ((v.1, v.2), v.2.1) :=
  (Primrec.fst.pair Primrec.snd).pair (Primrec.fst.comp Primrec.snd)

theorem primrec_lenAgree :
    Primrec fun v : ReqArgs ↦ lenAgree v.1.1 v.1.2 v.2.1 v.2.2 :=
  primrec_lenAux.comp rq_bundle

theorem primrec_restraintAt :
    Primrec fun v : ReqArgs ↦ restraintAt v.1.1 v.1.2 v.2.1 v.2.2 :=
  primrec_restAux.comp
    ((Primrec.fst.pair Primrec.snd).pair primrec_lenAgree)

/-! ### The stage step -/

set_option maxHeartbeats 1600000 in
private theorem primrec_newRestraints_map :
    Primrec₂ fun (w : (ℕ × State) × ℕ) (j : ℕ) ↦
      max (w.1.2.2.2.getD j 0) (restraintAt w.1.1 w.1.2 w.2 j) :=
  (Primrec.nat_max.comp
    ((Primrec.list_getD 0).comp
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      Primrec.snd)
    (primrec_restraintAt.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))).to₂

set_option maxHeartbeats 1600000 in
theorem primrec_newRestraints :
    Primrec fun w : (ℕ × State) × ℕ ↦ newRestraints w.1.1 w.1.2 w.2 :=
  Primrec.list_map
    (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)) primrec_newRestraints_map

private theorem primrec_routeFind :
    Primrec fun w : (List ℕ × ℕ) × ℕ ↦
      (List.range (w.1.2 + 1)).find? fun j ↦ decide (w.2 < w.1.1.getD j 0) :=
  primrec_find?
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)))
    (PrimrecRel.comp Primrec.nat_lt (Primrec.snd.comp Primrec.fst)
      ((Primrec.list_getD 0).comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)).decide.to₂

theorem primrec_routeTo :
    Primrec fun w : (List ℕ × ℕ) × ℕ ↦ routeTo w.1.1 w.1.2 w.2 :=
  (Primrec.option_casesOn primrec_routeFind (Primrec.const 0)
    (Primrec.ite
      (PrimrecRel.comp Primrec.eq
        (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0))
      (Primrec.const 1) (Primrec.const 0)).to₂).of_eq fun w ↦ by
        rw [routeTo]
        cases (List.range (w.1.2 + 1)).find? fun j ↦ decide (w.2 < w.1.1.getD j 0) <;>
          rfl

/-- Argument bundle of the routing step: `((rs, new), st, s)`. -/
abbrev StepArgs : Type := (List ℕ × List ℕ) × State × ℕ

private theorem sw_rs : Primrec fun w : StepArgs ↦ w.1.1 :=
  Primrec.fst.comp Primrec.fst

private theorem sw_new : Primrec fun w : StepArgs ↦ w.1.2 :=
  Primrec.snd.comp Primrec.fst

private theorem sw_st : Primrec fun w : StepArgs ↦ w.2.1 :=
  Primrec.fst.comp Primrec.snd

private theorem sw_s : Primrec fun w : StepArgs ↦ w.2.2 :=
  Primrec.snd.comp Primrec.snd

private theorem primrec_stepHalf (b : ℕ) :
    Primrec fun w : StepArgs ↦
      filterB (fun x ↦ decide (routeTo w.1.1 w.2.2 x = b)) w.1.2 :=
  primrec_filterB
    (PrimrecRel.comp Primrec.eq
      (primrec_routeTo.comp
        (((sw_rs.comp Primrec.fst).pair (sw_s.comp Primrec.fst)).pair Primrec.snd))
      (Primrec.const b)).decide.to₂
    sw_new

set_option maxHeartbeats 1600000 in
theorem primrec_stepWith :
    Primrec fun w : StepArgs ↦ stepWith w.1.1 w.1.2 w.2.1 w.2.2 :=
  (Primrec.list_append.comp (primrec_stepHalf 0) (Primrec.fst.comp sw_st)).pair
    ((Primrec.list_append.comp (primrec_stepHalf 1)
        (Primrec.fst.comp (Primrec.snd.comp sw_st))).pair sw_rs)

set_option maxHeartbeats 6400000 in
theorem primrec_step : Primrec fun w : (ℕ × State) × ℕ ↦ step w.1.1 w.1.2 w.2 :=
  (primrec_stepWith.comp
    ((primrec_newRestraints.pair
        (primrec_newAt.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).of_eq fun _ ↦ rfl

theorem stageState_rec (ec s : ℕ) :
    stageState ec s =
      Nat.rec (motive := fun _ ↦ State) ([], [], [])
        (fun s st ↦ step ec st s) s := by
  induction s with
  | zero => rfl
  | succ s ih => show step ec (stageState ec s) s = _; rw [ih]

theorem primrec_stageState : Primrec₂ stageState := by
  have hstep : Primrec₂ fun (q : ℕ × ℕ) (p : ℕ × State) ↦ step q.1 p.2 p.1 :=
    (primrec_step.comp
      (((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd)).pair
        (Primrec.fst.comp Primrec.snd))).to₂
  exact (Primrec.nat_rec' Primrec.snd (Primrec.const ([], [], [])) hstep).of_eq
    fun q ↦ (stageState_rec q.1 q.2).symm

/-! ### The two halves are computably enumerable -/

theorem primrec_memHalf (ec j : ℕ) :
    Primrec fun p : ℕ × ℕ ↦ decide (p.1 ∈ halfList ec j p.2) :=
  primrec_memDecide.comp Primrec.fst
    (primrec_oracleOf.comp
      (primrec_stageState.comp (Primrec.const ec) Primrec.snd)
      (Primrec.const j))

/-- **Each half is computably enumerable** — via FM's `ce_of_partrec_dom`,
exactly as FM certified its own two sets. -/
theorem ce_halfSet (ec j : ℕ) : CE (halfSet ec j) := by
  have hpart : Partrec₂ fun (x s : ℕ) ↦
      (Part.some (decide (x ∈ halfList ec j s)) : Part Bool) :=
    ((primrec_memHalf ec j).to_comp).partrec
  have hrf : Partrec fun x : ℕ ↦
      Nat.rfind fun s ↦ (Part.some (decide (x ∈ halfList ec j s)) : Part Bool) :=
    Partrec.rfind hpart
  refine ce_of_partrec_dom (Partrec.nat_iff.mp hrf) fun x ↦ ?_
  rw [Nat.rfind_dom]
  constructor
  · intro hmem
    obtain ⟨s, hs⟩ := mem_halfSet.mp hmem
    exact ⟨s, by rw [Part.mem_some_iff, eq_comm, decide_eq_true_iff]; exact hs,
      fun _ ↦ trivial⟩
  · rintro ⟨s, hs, -⟩
    rw [Part.mem_some_iff, eq_comm, decide_eq_true_iff] at hs
    exact mem_halfSet.mpr ⟨s, hs⟩

/-! ### The decision procedure for `A`

This is the computability half of `unsatisfied_requirement_computes`: if a
requirement's agreement length grows without bound and always reports `A`
correctly past some stage, searching for such a stage *decides* `A`.  The
search is a `Nat.rfind` over a primitive recursive predicate, and the
resulting partial recursive function is carried into the local oracle model
by FM's `partrec_realized` — which FM itself never needed to use, having
never had to *produce* a computable set. -/

theorem computableSet_of_agreement {ec j s₀ : ℕ}
    (hex : ∀ y, ∃ s, s₀ ≤ s ∧ y < lenAgree ec (stageState ec s) s j)
    (hcorr : ∀ y s, s₀ ≤ s → y < lenAgree ec (stageState ec s) s j →
      (y ∈ enumStage ec s ↔ y ∈ enumSet ec)) :
    ComputableSet (enumSet ec) := by
  classical
  -- the search predicate: "stage `s` is past `s₀` and its agreement covers `y`"
  set P : ℕ → ℕ → Bool := fun y s ↦
    decide (s₀ ≤ s ∧ y < lenAgree ec (stageState ec s) s j) with hPdef
  have hlen : Primrec fun q : ℕ × ℕ ↦ lenAgree ec (stageState ec q.2) q.2 j :=
    primrec_lenAgree.comp
      (((Primrec.const ec).pair
        (primrec_stageState.comp (Primrec.const ec) Primrec.snd)).pair
        (Primrec.snd.pair (Primrec.const j)))
  have hP : Primrec₂ P :=
    (PrimrecPred.and
      (PrimrecRel.comp Primrec.nat_le (Primrec.const s₀) Primrec.snd)
      (PrimrecRel.comp Primrec.nat_lt Primrec.fst hlen)).decide.to₂
  have hmemE : Primrec fun q : ℕ × ℕ ↦ decide (q.1 ∈ enumStage ec q.2) :=
    primrec_memEnum.comp (((Primrec.const ec).pair Primrec.snd).pair Primrec.fst)
  -- the algorithm: find such a stage, then read off `A`'s approximation there
  have hrf : Partrec fun y : ℕ ↦
      Nat.rfind fun s ↦ (Part.some (P y s) : Part Bool) :=
    Partrec.rfind (hP.to_comp).partrec
  have hf : Partrec fun y : ℕ ↦
      (Nat.rfind fun s ↦ (Part.some (P y s) : Part Bool)).map
        fun s ↦ natOfBool (decide (y ∈ enumStage ec s)) :=
    Partrec.map hrf
      (Primrec.to_comp (Primrec.cond hmemE (Primrec.const 1) (Primrec.const 0))).to₂
  obtain ⟨c, hc⟩ := partrec_realized (Partrec.nat_iff.mp hf)
  refine ⟨c, fun x ↦ ?_⟩
  -- the value it produces is the right one
  have hdom : (Nat.rfind fun s ↦ (Part.some (P x s) : Part Bool)).Dom := by
    rw [Nat.rfind_dom]
    obtain ⟨s, hs₀, hs⟩ := hex x
    exact ⟨s, by rw [Part.mem_some_iff, eq_comm, hPdef]; simp [hs₀, hs],
      fun _ ↦ trivial⟩
  obtain ⟨s, hs⟩ := Part.dom_iff_mem.mp hdom
  have hPs : P x s = true := by
    have := Nat.rfind_spec hs
    rwa [Part.mem_some_iff, eq_comm] at this
  have hxs : (x ∈ enumStage ec s ↔ x ∈ enumSet ec) := by
    rw [hPdef] at hPs
    simp only [decide_eq_true_eq] at hPs
    exact hcorr x s hPs.1 hPs.2
  have hval : natOfBool (charFun (enumSet ec) x) ∈
      (Nat.rfind fun s ↦ (Part.some (P x s) : Part Bool)).map
        fun s ↦ natOfBool (decide (x ∈ enumStage ec s)) := by
    refine (Part.mem_map_iff _).mpr ⟨s, hs, ?_⟩
    congr 1
    by_cases hx : x ∈ enumSet ec
    · rw [decide_eq_true (hxs.mpr hx), charFun_eq_true.mpr hx]
    · rw [decide_eq_false (fun h ↦ hx (hxs.mp h)), charFun_eq_false.mpr hx]
  obtain ⟨k, hk⟩ := (hc PartOracle.empty x _).mp hval
  exact ⟨k, ⟨natOfBool (charFun (enumSet ec) x), 0⟩, hk, rfl⟩

end SacksSplitting
