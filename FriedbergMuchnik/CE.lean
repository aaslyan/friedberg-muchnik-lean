/-
# The constructed sets are computably enumerable

The last obligation of the construction: `Aset` and `Bset` are `CE` in the
project's vocabulary.  By `ce_of_partrec_dom` (the Mathlib bridge) it
suffices to give a Mathlib-partial-recursive semi-decider, i.e. to prove
the stage construction computable in Mathlib's sense.

To avoid custom `Primcodable` instances for the state types, we run a
**parallel implementation** of the step function on plain tuples
(`St := List ℕ × List ℕ × List RS × ℕ` with `RS := Option ℕ × Bool × ℕ`),
prove it simulates the real construction (`encSt_stage`), and prove *it*
primitive recursive with stock combinators.  The two nonstandard list
operations of the construction (`set`, and take-cons-replicate) are
re-expressed as maps over `List.range`, which is what the bridge lemmas
`map_range_set` / `map_range_act` justify.
-/
import FriedbergMuchnik.Foundation.MathlibBridge
import FriedbergMuchnik.StageDynamics

namespace FriedbergMuchnik

/-! ### The encoded state -/

/-- Encoded requirement record: (witness, acted, restraint). -/
abbrev RS : Type := Option ℕ × Bool × ℕ

/-- Encoded construction state: (Alist, Blist, records, counter). -/
abbrev St : Type := List ℕ × List ℕ × List RS × ℕ

def encReq (r : ReqState) : RS := (r.witness, r.acted, r.restraint)

def encSt (st : ConsState) : St :=
  (st.Alist, st.Blist, st.reqs.map encReq, st.fresh)

def initRS : RS := (none, false, 0)

/-- Parallel form of `ConsState.convCheck` (definitionally equal after
projecting the state). -/
def convCheckN (Al Bl : List ℕ) (s i x : ℕ) : Option ℕ :=
  let v := nrun s (snapshotOf (if i % 2 = 0 then Bl else Al) s) (i / 2) x
  if 2 ≤ v ∧ (v - 2).unpair.1 = 0 then some ((v - 2).unpair.2) else none

/-- Parallel form of `ConsState.requiresAttention`. -/
def reqAttN (Al Bl : List ℕ) (rs : List RS) (s i : ℕ) : Bool :=
  (rs[i]?).casesOn false fun r =>
    r.1.casesOn true fun x => !r.2.1 && (convCheckN Al Bl s i x).isSome

/-- The unchanged-state builder (idle stages and failed convergence
checks): the pre-state with the newborn blank record. -/
def idleSt (st : St) : St :=
  (st.1, st.2.1, st.2.2.1 ++ [initRS], st.2.2.2)

/-- The appointment state: requirement `i` takes the counter as witness. -/
def appointSt (st : St) (i : ℕ) : St :=
  (st.1, st.2.1,
    (List.range (st.2.2.1 ++ [initRS]).length).map fun j =>
      if j = i then
        (some st.2.2.2,
         ((st.2.2.1 ++ [initRS]).getD i initRS).2.1,
         ((st.2.2.1 ++ [initRS]).getD i initRS).2.2)
      else (st.2.2.1 ++ [initRS]).getD j initRS,
    st.2.2.2 + 1)

/-- The action state: requirement `i` enumerates witness `x` with use `u`,
initializing everything below it. -/
def actSt (st : St) (i x u : ℕ) : St :=
  ((if i % 2 = 0 then x :: st.1 else st.1),
   (if i % 2 = 0 then st.2.1 else x :: st.2.1),
   (List.range (st.2.2.1 ++ [initRS]).length).map fun j =>
     if j < i then (st.2.2.1 ++ [initRS]).getD j initRS
     else if j = i then (some x, true, u) else initRS,
   max st.2.2.2 (u + 1))

/-- Parallel form of `stepState`; the three outcome states are the named
builders above, so that the computability proof only ever manipulates
small, named heads. -/
def stepN (st : St) (s : ℕ) : St :=
  ((List.range (st.2.2.1 ++ [initRS]).length).find? fun i =>
      reqAttN st.1 st.2.1 (st.2.2.1 ++ [initRS]) s i).casesOn
    (idleSt st)
    fun i =>
      (((st.2.2.1 ++ [initRS]).getD i initRS).1).casesOn
        (appointSt st i)
        fun x =>
          (convCheckN st.1 st.2.1 s i x).casesOn (idleSt st)
            fun u => actSt st i x u

/-- Parallel form of `stageState`. -/
def stageN : ℕ → St
  | 0 => ([], [], [], 0)
  | s + 1 => stepN (stageN s) s

/-! ### Correspondence lemmas -/

theorem convCheckN_eq (st : ConsState) (s i x : ℕ) :
    convCheckN st.Alist st.Blist s i x = st.convCheck s i x := rfl

theorem getD_map_encReq (l : List ReqState) (i : ℕ) :
    (l.map encReq).getD i initRS = encReq (l.getD i ReqState.init) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem reqAttN_eq (st : ConsState) (s i : ℕ) :
    reqAttN st.Alist st.Blist (st.reqs.map encReq) s i =
      st.requiresAttention s i := by
  cases hri : st.reqs[i]? with
  | none =>
    simp [reqAttN, ConsState.requiresAttention, List.getElem?_map, hri]
  | some r =>
    cases hw : r.witness with
    | none =>
      simp [reqAttN, ConsState.requiresAttention, List.getElem?_map, hri,
        encReq, hw]
    | some x =>
      simp [reqAttN, ConsState.requiresAttention, List.getElem?_map, hri,
        encReq, hw, convCheckN_eq]

/-! ### The two list surgeries as maps over `range` -/

theorem encReq_witness (r : ReqState) : (encReq r).1 = r.witness := rfl

theorem encReq_acted (r : ReqState) : (encReq r).2.1 = r.acted := rfl

theorem encReq_restraint (r : ReqState) : (encReq r).2.2 = r.restraint := rfl

/-! ### The two list surgeries as maps over `range` -/

theorem map_range_set {α : Type _} (l : List α) (d v : α) (i n : ℕ)
    (hn : n = l.length) (hi : i < l.length) :
    ((List.range n).map fun j => if j = i then v else l.getD j d) =
      l.set i v := by
  subst hn
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map]
  by_cases hj : j < l.length
  · rw [List.getElem?_range hj]
    by_cases hji : j = i
    · subst hji
      simp [List.getElem?_set_self hj]
    · rw [List.getElem?_set_ne (by omega)]
      simp [hji, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hj),
      List.getElem?_eq_none (by simp; omega)]
    rfl

theorem map_range_act {α : Type _} (l : List α) (rec init' : α) (i n : ℕ)
    (hn : n = l.length) (hi : i < l.length) :
    ((List.range n).map fun j =>
      if j < i then l.getD j init' else if j = i then rec else init') =
      l.take i ++ rec :: List.replicate (l.length - (i + 1)) init' := by
  subst hn
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map]
  by_cases hj : j < l.length
  · rw [List.getElem?_range hj]
    rcases Nat.lt_trichotomy j i with hji | rfl | hji
    · rw [List.getElem?_append_left (by simp [List.length_take]; omega),
        List.getElem?_take_of_lt hji]
      simp [hji, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    · have hlen : (l.take j).length = j := by
        simp [List.length_take]
        omega
      rw [List.getElem?_append_right hlen.le, hlen, Nat.sub_self,
        List.getElem?_cons_zero]
      simp
    · have hlen : (l.take i).length = i := by
        simp [List.length_take]
        omega
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      have hji' : j - i = (j - i - 1) + 1 := by omega
      rw [hji', List.getElem?_cons_succ, List.getElem?_replicate,
        if_pos (by omega)]
      simp [show ¬(j < i) by omega, show ¬(j = i) by omega]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hj),
      List.getElem?_eq_none (by simp [List.length_take]; omega)]
    rfl

/-! ### The simulation -/

theorem encSt_stepState (st : ConsState) (s : ℕ) :
    encSt (stepState st s) = stepN (encSt st) s := by
  have hmap : (encSt st).2.2.1 ++ [initRS] =
      (st.reqs ++ [ReqState.init]).map encReq := by
    simp [encSt, encReq, ReqState.init, initRS]
  simp only [stepState, stepN, idleSt, appointSt, actSt, hmap, List.length_map]
  have hpred : (fun i => reqAttN (encSt st).1 (encSt st).2.1
      ((st.reqs ++ [ReqState.init]).map encReq) s i) =
      fun i => ConsState.requiresAttention
        { st with reqs := st.reqs ++ [ReqState.init] } s i :=
    funext fun i =>
      reqAttN_eq { st with reqs := st.reqs ++ [ReqState.init] } s i
  rw [hpred]
  cases hfind : (List.range (st.reqs ++ [ReqState.init]).length).find?
      (fun i => ConsState.requiresAttention
        { st with reqs := st.reqs ++ [ReqState.init] } s i) with
  | none => simp [encSt]
  | some i =>
    have hi : i < (st.reqs ++ [ReqState.init]).length := by
      have h1 := List.mem_of_find?_eq_some hfind
      simpa [List.mem_range] using h1
    have hi' : i < ((st.reqs ++ [ReqState.init]).map encReq).length := by
      simpa using hi
    simp only [ConsState.stepAt]
    rw [getD_map_encReq]
    simp only [encReq_witness, encReq_acted, encReq_restraint]
    cases hw : ((st.reqs ++ [ReqState.init]).getD i ReqState.init).witness with
    | none =>
      simp only [encSt, List.map_set]
      rw [show encReq { (st.reqs ++ [ReqState.init]).getD i ReqState.init with
          witness := some st.fresh } =
        ((some st.fresh,
          ((st.reqs ++ [ReqState.init]).getD i ReqState.init).acted,
          ((st.reqs ++ [ReqState.init]).getD i ReqState.init).restraint) : RS)
        from rfl]
      rw [map_range_set ((st.reqs ++ [ReqState.init]).map encReq) initRS
        ((some st.fresh,
          ((st.reqs ++ [ReqState.init]).getD i ReqState.init).acted,
          ((st.reqs ++ [ReqState.init]).getD i ReqState.init).restraint) : RS) i
        ((st.reqs ++ [ReqState.init]).length) (by simp) hi']
    | some x =>
      simp only []
      rw [show convCheckN (encSt st).1 (encSt st).2.1 s i x =
        ConsState.convCheck { st with reqs := st.reqs ++ [ReqState.init] }
          s i x from rfl]
      cases hcc : ConsState.convCheck
          { st with reqs := st.reqs ++ [ReqState.init] } s i x with
      | none => simp [encSt]
      | some u =>
        simp only [encSt]
        rw [List.map_append, List.map_cons, List.map_replicate, List.map_take]
        rw [show encReq (⟨some x, true, u⟩ : ReqState) =
            ((some x, true, u) : RS) from rfl,
          show encReq ReqState.init = initRS from rfl]
        rw [map_range_act ((st.reqs ++ [ReqState.init]).map encReq)
          ((some x, true, u) : RS) initRS i
          ((st.reqs ++ [ReqState.init]).length) (by simp) hi']
        simp [List.length_map]

/-- The parallel implementation computes the encoding of the real
construction. -/
theorem encSt_stage (s : ℕ) : encSt (stageState s) = stageN s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    show encSt (stepState (stageState s) s) = stepN (stageN s) s
    rw [encSt_stepState, ih]

theorem mem_Alist_iff_stageN (x s : ℕ) :
    x ∈ (stageState s).Alist ↔ x ∈ (stageN s).1 := by
  rw [← encSt_stage]
  exact Iff.rfl

theorem mem_Blist_iff_stageN (x s : ℕ) :
    x ∈ (stageState s).Blist ↔ x ∈ (stageN s).2.1 := by
  rw [← encSt_stage]
  exact Iff.rfl

/-! ### Primitive recursiveness of the parallel implementation -/


private theorem primrec_find? {α β : Type _} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).find? (p a) := by
  have h : Primrec fun a => (f a).foldr
      (fun b acc => bif p a b then some b else acc) (none : Option β) :=
    Primrec.list_foldr hf (Primrec.const none)
      (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  refine h.of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons b l ih =>
    cases hpb : p a b with
    | true => simp [hpb]
    | false => simp [hpb, ih]

private theorem primrec_memDecide :
    Primrec₂ fun (x : ℕ) (l : List ℕ) => decide (x ∈ l) := by
  have heqd : Primrec fun q : (ℕ × List ℕ) × ℕ × Bool =>
      decide (q.1.1 = q.2.1) :=
    (PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)).decide
  have h : Primrec fun q : ℕ × List ℕ =>
      q.2.foldr (fun b acc => decide (q.1 = b) || acc) false :=
    Primrec.list_foldr Primrec.snd (Primrec.const false)
      ((Primrec.dom_bool₂ (· || ·)).comp heqd
        (Primrec.snd.comp Primrec.snd)).to₂
  refine h.to₂.of_eq fun x l => ?_
  induction l with
  | nil => simp
  | cons b l ih => simp [List.mem_cons, ih]

private theorem primrec_snapshotOf : Primrec₂ snapshotOf := by
  have h : Primrec fun q : List ℕ × ℕ =>
      (List.range q.2).map fun j => decide (j ∈ q.1) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      (primrec_memDecide.comp Primrec.snd (Primrec.fst.comp Primrec.fst))
  exact h


set_option maxHeartbeats 1600000 in
private theorem primrec_convCheckN :
    Primrec fun q : ((List ℕ × List ℕ) × ℕ × ℕ) × ℕ =>
      convCheckN q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2 := by
  have hAl : Primrec fun q : ((List ℕ × List ℕ) × ℕ × ℕ) × ℕ => q.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hBl : Primrec fun q : ((List ℕ × List ℕ) × ℕ × ℕ) × ℕ => q.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hs : Primrec fun q : ((List ℕ × List ℕ) × ℕ × ℕ) × ℕ => q.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hii : Primrec fun q : ((List ℕ × List ℕ) × ℕ × ℕ) × ℕ => q.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hx : Primrec fun q : ((List ℕ × List ℕ) × ℕ × ℕ) × ℕ => q.2 :=
    Primrec.snd
  have horacle : Primrec fun q : ((List ℕ × List ℕ) × ℕ × ℕ) × ℕ =>
      if q.1.2.2 % 2 = 0 then q.1.1.2 else q.1.1.1 :=
    Primrec.ite
      (PrimrecRel.comp Primrec.eq
        (Primrec.nat_mod.comp hii (Primrec.const 2)) (Primrec.const 0))
      hBl hAl
  have hv : Primrec fun q : ((List ℕ × List ℕ) × ℕ × ℕ) × ℕ =>
      nrun q.1.2.1 (snapshotOf (if q.1.2.2 % 2 = 0 then q.1.1.2 else q.1.1.1)
        q.1.2.1) (q.1.2.2 / 2) q.2 :=
    nrun_primrec.comp
      (((hs.pair (primrec_snapshotOf.comp horacle hs)).pair
        (Primrec.nat_div.comp hii (Primrec.const 2))).pair hx)
  exact (Primrec.ite
    (PrimrecPred.and
      (PrimrecRel.comp Primrec.nat_le (Primrec.const 2) hv)
      (PrimrecRel.comp Primrec.eq
        (Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.nat_sub.comp hv (Primrec.const 2))))
        (Primrec.const 0)))
    (Primrec.option_some.comp
      (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.nat_sub.comp hv (Primrec.const 2)))))
    (Primrec.const none)).of_eq fun q => by simp only [convCheckN]


set_option maxHeartbeats 16000000 in
private theorem primrec_reqAttN :
    Primrec fun q : ((List ℕ × List ℕ) × List RS) × ℕ × ℕ =>
      reqAttN q.1.1.1 q.1.1.2 q.1.2 q.2.1 q.2.2 := by
  have hAl : Primrec fun q : ((List ℕ × List ℕ) × List RS) × ℕ × ℕ => q.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hBl : Primrec fun q : ((List ℕ × List ℕ) × List RS) × ℕ × ℕ => q.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hrs : Primrec fun q : ((List ℕ × List ℕ) × List RS) × ℕ × ℕ => q.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hs : Primrec fun q : ((List ℕ × List ℕ) × List RS) × ℕ × ℕ => q.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hii : Primrec fun q : ((List ℕ × List ℕ) × List RS) × ℕ × ℕ => q.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hopt : Primrec fun q : ((List ℕ × List ℕ) × List RS) × ℕ × ℕ =>
      q.1.2[q.2.2]? :=
    Primrec.list_getElem?.comp hrs hii
  have hinner2 : Primrec fun p :
      ((((List ℕ × List ℕ) × List RS) × ℕ × ℕ) × RS) × ℕ =>
      !p.1.2.2.1 && (convCheckN p.1.1.1.1.1 p.1.1.1.1.2 p.1.1.2.1 p.1.1.2.2
        p.2).isSome :=
    (Primrec.dom_bool₂ (· && ·)).comp
      ((Primrec.dom_bool (!·)).comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.option_isSome.comp
        (primrec_convCheckN.comp
          ((((hAl.comp (Primrec.fst.comp Primrec.fst)).pair
              (hBl.comp (Primrec.fst.comp Primrec.fst))).pair
            ((hs.comp (Primrec.fst.comp Primrec.fst)).pair
              (hii.comp (Primrec.fst.comp Primrec.fst)))).pair Primrec.snd)))
  have hinner : Primrec fun p :
      (((List ℕ × List ℕ) × List RS) × ℕ × ℕ) × RS =>
      (p.2.1.casesOn true fun x => !p.2.2.1 &&
        (convCheckN p.1.1.1.1 p.1.1.1.2 p.1.2.1 p.1.2.2 x).isSome : Bool) :=
    Primrec.option_casesOn (Primrec.fst.comp Primrec.snd)
      (Primrec.const true) hinner2.to₂
  exact (Primrec.option_casesOn hopt (Primrec.const false) hinner.to₂).of_eq
    fun q => by simp only [reqAttN]

private theorem primrec_idleSt : Primrec idleSt := by
  have h : Primrec fun st : St =>
      ((st.1, st.2.1, st.2.2.1 ++ [initRS], st.2.2.2) : St) :=
    Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      ((Primrec.list_append.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const [initRS])).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact h.of_eq fun st => by simp only [idleSt]

set_option maxHeartbeats 3200000 in
private theorem primrec_appointSt : Primrec₂ appointSt := by
  have hrs : Primrec fun p : St × ℕ => p.1.2.2.1 ++ [initRS] :=
    Primrec.list_append.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.const [initRS])
  have hfr : Primrec fun p : St × ℕ => p.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hgetD : Primrec fun p : St × ℕ =>
      (p.1.2.2.1 ++ [initRS]).getD p.2 initRS :=
    (Primrec.list_getD initRS).comp hrs Primrec.snd
  have hmapf : Primrec fun pp : (St × ℕ) × ℕ =>
      if pp.2 = pp.1.2 then
        (some pp.1.1.2.2.2,
         ((pp.1.1.2.2.1 ++ [initRS]).getD pp.1.2 initRS).2.1,
         ((pp.1.1.2.2.1 ++ [initRS]).getD pp.1.2 initRS).2.2)
      else (pp.1.1.2.2.1 ++ [initRS]).getD pp.2 initRS :=
    Primrec.ite
      (PrimrecRel.comp Primrec.eq Primrec.snd
        (Primrec.snd.comp Primrec.fst))
      ((Primrec.option_some.comp (hfr.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (hgetD.comp Primrec.fst))).pair
          (Primrec.snd.comp (Primrec.snd.comp (hgetD.comp Primrec.fst)))))
      ((Primrec.list_getD initRS).comp (hrs.comp Primrec.fst) Primrec.snd)
  have h : Primrec fun p : St × ℕ =>
      ((p.1.1, p.1.2.1,
        (List.range (p.1.2.2.1 ++ [initRS]).length).map fun j =>
          if j = p.2 then
            (some p.1.2.2.2,
             ((p.1.2.2.1 ++ [initRS]).getD p.2 initRS).2.1,
             ((p.1.2.2.1 ++ [initRS]).getD p.2 initRS).2.2)
          else (p.1.2.2.1 ++ [initRS]).getD j initRS,
        p.1.2.2.2 + 1) : St) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.list_map
          (Primrec.list_range.comp (Primrec.list_length.comp hrs))
          hmapf.to₂).pair
        (Primrec.succ.comp hfr)))
  exact h.of_eq fun p => by simp only [appointSt]

set_option maxHeartbeats 3200000 in
private theorem primrec_actSt :
    Primrec fun w : ((St × ℕ) × ℕ) × ℕ => actSt w.1.1.1 w.1.1.2 w.1.2 w.2 := by
  have hst : Primrec fun w : ((St × ℕ) × ℕ) × ℕ => w.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hi : Primrec fun w : ((St × ℕ) × ℕ) × ℕ => w.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec fun w : ((St × ℕ) × ℕ) × ℕ => w.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hu : Primrec fun w : ((St × ℕ) × ℕ) × ℕ => w.2 := Primrec.snd
  have hAl : Primrec fun w : ((St × ℕ) × ℕ) × ℕ => w.1.1.1.1 :=
    Primrec.fst.comp hst
  have hBl : Primrec fun w : ((St × ℕ) × ℕ) × ℕ => w.1.1.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp hst)
  have hrs : Primrec fun w : ((St × ℕ) × ℕ) × ℕ =>
      w.1.1.1.2.2.1 ++ [initRS] :=
    Primrec.list_append.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hst)))
      (Primrec.const [initRS])
  have hfr : Primrec fun w : ((St × ℕ) × ℕ) × ℕ => w.1.1.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hst))
  have heven : PrimrecPred fun w : ((St × ℕ) × ℕ) × ℕ => w.1.1.2 % 2 = 0 :=
    PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp hi (Primrec.const 2))
      (Primrec.const 0)
  have hmapf : Primrec fun ww : (((St × ℕ) × ℕ) × ℕ) × ℕ =>
      if ww.2 < ww.1.1.1.2 then
        (ww.1.1.1.1.2.2.1 ++ [initRS]).getD ww.2 initRS
      else if ww.2 = ww.1.1.1.2 then
        (some ww.1.1.2, true, ww.1.2) else initRS := by
    have hi' : Primrec fun ww : (((St × ℕ) × ℕ) × ℕ) × ℕ => ww.1.1.1.2 :=
      hi.comp Primrec.fst
    exact Primrec.ite
      (PrimrecRel.comp Primrec.nat_lt Primrec.snd hi')
      ((Primrec.list_getD initRS).comp (hrs.comp Primrec.fst) Primrec.snd)
      (Primrec.ite
        (PrimrecRel.comp Primrec.eq Primrec.snd hi')
        ((Primrec.option_some.comp (hx.comp Primrec.fst)).pair
          ((Primrec.const true).pair (hu.comp Primrec.fst)))
        (Primrec.const initRS))
  have h : Primrec fun w : ((St × ℕ) × ℕ) × ℕ =>
      (((if w.1.1.2 % 2 = 0 then w.1.2 :: w.1.1.1.1 else w.1.1.1.1),
        (if w.1.1.2 % 2 = 0 then w.1.1.1.2.1 else w.1.2 :: w.1.1.1.2.1),
        (List.range (w.1.1.1.2.2.1 ++ [initRS]).length).map fun j =>
          if j < w.1.1.2 then (w.1.1.1.2.2.1 ++ [initRS]).getD j initRS
          else if j = w.1.1.2 then (some w.1.2, true, w.2) else initRS,
        max w.1.1.1.2.2.2 (w.2 + 1)) : St) :=
    (Primrec.ite heven (Primrec.list_cons.comp hx hAl) hAl).pair
      ((Primrec.ite heven hBl (Primrec.list_cons.comp hx hBl)).pair
        ((Primrec.list_map
          (Primrec.list_range.comp (Primrec.list_length.comp hrs))
          hmapf.to₂).pair
        (Primrec.nat_max.comp hfr (Primrec.succ.comp hu))))
  exact h.of_eq fun w => by simp only [actSt]

set_option maxHeartbeats 3200000 in
private theorem primrec_stepN : Primrec₂ stepN := by
  have hAl : Primrec fun q : St × ℕ => q.1.1 := Primrec.fst.comp Primrec.fst
  have hBl : Primrec fun q : St × ℕ => q.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hrs : Primrec fun q : St × ℕ => q.1.2.2.1 ++ [initRS] :=
    Primrec.list_append.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.const [initRS])
  have hs : Primrec fun q : St × ℕ => q.2 := Primrec.snd
  have hfind : Primrec fun q : St × ℕ =>
      (List.range (q.1.2.2.1 ++ [initRS]).length).find? fun i =>
        reqAttN q.1.1 q.1.2.1 (q.1.2.2.1 ++ [initRS]) q.2 i :=
    primrec_find? (Primrec.list_range.comp (Primrec.list_length.comp hrs))
      (primrec_reqAttN.comp
        ((((hAl.comp Primrec.fst).pair (hBl.comp Primrec.fst)).pair
          (hrs.comp Primrec.fst)).pair
          ((hs.comp Primrec.fst).pair Primrec.snd))).to₂
  have hwit : Primrec fun p : (St × ℕ) × ℕ =>
      ((p.1.1.2.2.1 ++ [initRS]).getD p.2 initRS).1 :=
    Primrec.fst.comp
      ((Primrec.list_getD initRS).comp (hrs.comp Primrec.fst) Primrec.snd)
  have hconv2 : Primrec fun p : ((St × ℕ) × ℕ) × ℕ =>
      convCheckN p.1.1.1.1 p.1.1.1.2.1 p.1.1.2 p.1.2 p.2 :=
    primrec_convCheckN.comp
      ((((hAl.comp (Primrec.fst.comp Primrec.fst)).pair
          (hBl.comp (Primrec.fst.comp Primrec.fst))).pair
        ((hs.comp (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)
  have hactB : Primrec fun p : ((St × ℕ) × ℕ) × ℕ =>
      ((convCheckN p.1.1.1.1 p.1.1.1.2.1 p.1.1.2 p.1.2 p.2).casesOn
        (idleSt p.1.1.1) (fun u => actSt p.1.1.1 p.1.2 p.2 u) : St) :=
    Primrec.option_casesOn hconv2
      (primrec_idleSt.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (primrec_actSt.comp
        ((((Primrec.fst.comp (Primrec.fst.comp
            (Primrec.fst.comp Primrec.fst))).pair
           (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)).to₂
  have hbranch : Primrec fun p : (St × ℕ) × ℕ =>
      ((((p.1.1.2.2.1 ++ [initRS]).getD p.2 initRS).1).casesOn
        (appointSt p.1.1 p.2)
        (fun x =>
          ((convCheckN p.1.1.1 p.1.1.2.1 p.1.2 p.2 x).casesOn
            (idleSt p.1.1) (fun u => actSt p.1.1 p.2 x u) : St)) : St) :=
    Primrec.option_casesOn hwit
      (primrec_appointSt.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      hactB.to₂
  exact (Primrec.option_casesOn hfind
    (primrec_idleSt.comp Primrec.fst) hbranch.to₂).of_eq fun q => by
      simp only [stepN]

private theorem primrec_stageN : Primrec stageN := by
  have h : Primrec (Nat.rec (([], [], [], 0) : St)
      fun s ih => stepN ih s : ℕ → St) :=
    Primrec.nat_rec₁ _ primrec_stepN.swap
  refine h.of_eq fun s => ?_
  induction s with
  | zero => rfl
  | succ s ih =>
    show stepN (Nat.rec (([], [], [], 0) : St) (fun s ih => stepN ih s) s) s =
      stageN (s + 1)
    rw [ih]
    rfl

/-! ### The two sets are computably enumerable -/

private theorem primrec_memA :
    Primrec fun p : ℕ × ℕ => decide (p.1 ∈ (stageN p.2).1) :=
  primrec_memDecide.comp Primrec.fst
    (Primrec.fst.comp (primrec_stageN.comp Primrec.snd))

private theorem primrec_memB :
    Primrec fun p : ℕ × ℕ => decide (p.1 ∈ (stageN p.2).2.1) :=
  primrec_memDecide.comp Primrec.fst
    ((Primrec.fst.comp Primrec.snd).comp (primrec_stageN.comp Primrec.snd))

/-- **`A` is computably enumerable** (project vocabulary, via the Mathlib
bridge): the stage construction is computable, so searching for a stage
containing `x` is a partial recursive semi-decider for `Aset`. -/
theorem ce_Aset : CE Aset := by
  have hpart : Partrec₂ fun (x s : ℕ) =>
      (Part.some (decide (x ∈ (stageN s).1)) : Part Bool) :=
    (primrec_memA.to_comp).partrec
  have hrf : Partrec fun x : ℕ =>
      Nat.rfind fun s => (Part.some (decide (x ∈ (stageN s).1)) : Part Bool) :=
    Partrec.rfind hpart
  refine ce_of_partrec_dom (Partrec.nat_iff.mp hrf) fun x => ?_
  rw [Nat.rfind_dom]
  constructor
  · intro hmem
    obtain ⟨s, hs⟩ := mem_limitSet.mp hmem
    refine ⟨s, ?_, fun _ => trivial⟩
    rw [Part.mem_some_iff, eq_comm, decide_eq_true_iff]
    rw [AstageF, List.mem_toFinset] at hs
    exact (mem_Alist_iff_stageN x s).mp hs
  · rintro ⟨s, hs, _⟩
    rw [Part.mem_some_iff, eq_comm, decide_eq_true_iff] at hs
    exact mem_limitSet.mpr ⟨s, by
      rw [AstageF, List.mem_toFinset]
      exact (mem_Alist_iff_stageN x s).mpr hs⟩

/-- **`B` is computably enumerable**. -/
theorem ce_Bset : CE Bset := by
  have hpart : Partrec₂ fun (x s : ℕ) =>
      (Part.some (decide (x ∈ (stageN s).2.1)) : Part Bool) :=
    (primrec_memB.to_comp).partrec
  have hrf : Partrec fun x : ℕ =>
      Nat.rfind fun s => (Part.some (decide (x ∈ (stageN s).2.1)) : Part Bool) :=
    Partrec.rfind hpart
  refine ce_of_partrec_dom (Partrec.nat_iff.mp hrf) fun x => ?_
  rw [Nat.rfind_dom]
  constructor
  · intro hmem
    obtain ⟨s, hs⟩ := mem_limitSet.mp hmem
    refine ⟨s, ?_, fun _ => trivial⟩
    rw [Part.mem_some_iff, eq_comm, decide_eq_true_iff]
    rw [BstageF, List.mem_toFinset] at hs
    exact (mem_Blist_iff_stageN x s).mp hs
  · rintro ⟨s, hs, _⟩
    rw [Part.mem_some_iff, eq_comm, decide_eq_true_iff] at hs
    exact mem_limitSet.mpr ⟨s, by
      rw [BstageF, List.mem_toFinset]
      exact (mem_Blist_iff_stageN x s).mpr hs⟩

end FriedbergMuchnik
