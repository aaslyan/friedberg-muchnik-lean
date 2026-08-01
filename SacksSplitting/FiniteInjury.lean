import SacksSplitting.CE

/-!
# Finite injury, and why the requirements are satisfiable

This file is where Sacks and Friedberg–Muchnik genuinely part company.

FM's injury induction is a **rank** argument: each requirement's record has
a rank in `{0,1,2}` (has a witness? has acted?), receiving attention raises
it strictly, and only a higher-priority action can reset it — so once the
superiors go quiet a requirement acts at most twice more.  That argument
counts *events*.  A splitting requirement generates no events: it never
acts, and its restraint moves whenever the length of agreement moves.
There is nothing to count.

What replaces it is a three-part simultaneous induction along the priority
order.  Writing `R(j, s)` for the cumulative restraint:

1. **`noInjury_of_bounded`** — if every `j' < j` has a bounded restraint,
   then `N_j` is injured only finitely often.  Reason: by the routing rule
   (`injured_by_higher`), an element can enter `N_j`'s half below `N_j`'s
   restraint only if some *higher-priority* requirement also restrained it,
   hence only if it lies below a fixed bound `B`; and below a fixed bound
   only finitely much of `A` is ever enumerated — which is exactly FM's
   `StageMono.stabilizes_below`, reused verbatim.

2. **`unsatisfied_requirement_computes`** — *the one genuinely new piece of
   mathematics in this development.*  If `N_j` is never injured after some
   stage and `Φ_e^{A_i}` nevertheless computes `χ_A` totally and correctly,
   then `A` is computable.  This is what the non-computability hypothesis
   on `A` is for, and FM has no analogue: FM had no given set to exploit.

3. **`restraint_bounded_of`** — a *satisfied* requirement has a bounded
   restraint.  Once `Φ_e^{A_i}` is wrong at some `y₀`, the agreement length
   is eventually `≤ y₀`, and the use of each protected computation is the
   use of its own limit computation — a number that does not depend on the
   stage, by FM's `run_halt_unique`.  So the restraint is bounded by a
   maximum of finitely many fixed numbers.  This is the step that makes
   *recording the use* (rather than just the output) pay off.

Then `restraint_bounded` runs 1 → 2 → 3 by strong induction on the
priority `j`, and `requirement_satisfied` reads off the conclusion.  As in
FM, no closed-form injury bound is ever stated.
-/

namespace SacksSplitting

open OracleComputability

/-! ### Small bridges between `decide`, `natOfBool` and `charFun` -/

theorem natOfBool_inj {b b' : Bool} (h : natOfBool b = natOfBool b') : b = b' := by
  cases b <;> cases b' <;> simp_all [natOfBool]

theorem decide_enumStage_eq {ec s y : ℕ} (h : y ∈ enumStage ec s ↔ y ∈ enumSet ec) :
    decide (y ∈ enumStage ec s) = charFun (enumSet ec) y := by
  by_cases hy : y ∈ enumSet ec
  · rw [decide_eq_true (h.mpr hy), charFun_eq_true.mpr hy]
  · rw [decide_eq_false (fun hc ↦ hy (h.mp hc)), charFun_eq_false.mpr hy]

theorem enumStage_iff_of_eq {ec s y : ℕ}
    (h : decide (y ∈ enumStage ec s) = charFun (enumSet ec) y) :
    y ∈ enumStage ec s ↔ y ∈ enumSet ec := by
  constructor
  · intro hy
    rw [decide_eq_true hy] at h
    exact charFun_eq_true.mp h.symm
  · intro hy
    rw [charFun_eq_true.mpr hy] at h
    exact of_decide_eq_true h

/-- The stage approximation of `A` settles below any fixed bound — FM's
`StageMono.stabilizes_below`, in the shape used repeatedly below. -/
theorem enumStage_stabilizes (ec u : ℕ) :
    ∃ s₀, ∀ s, s₀ ≤ s → ∀ n, n < u → (n ∈ enumStage ec s ↔ n ∈ enumSet ec) := by
  obtain ⟨s₀, hs₀⟩ := (enumStageF_mono ec).stabilizes_below u
  exact ⟨s₀, fun s hs n hn ↦ by
    rw [← mem_enumStageF]; exact hs₀ s hs n hn⟩

/-! ### Injury -/

/-- Requirement `j` is never injured from stage `s₀` on: no number below
its cumulative restraint ever enters its half again. -/
def NoInjuryFrom (ec j s₀ : ℕ) : Prop :=
  ∀ t, s₀ ≤ t → ∀ x, x < Rest ec (t + 1) j →
    x ∈ halfList ec j (t + 1) → x ∈ halfList ec j t

theorem Rest_succ_eq (ec s k : ℕ) :
    Rest ec (s + 1) k = (newRestraints ec (stageState ec s) s).getD k 0 := rfl

/-- **The routing lemma** — the whole injury mechanism in one statement.
If a number enters requirement `j`'s half below `j`'s restraint, then some
*higher-priority* requirement restrained it too; that higher-priority
requirement is the one the routing rule obeyed, and `j` is the casualty.

This replaces FM's "a higher-priority requirement acted and initialised
me": there, injury is a side effect of someone else's positive move; here
it is a side effect of someone else's restraint winning the tie. -/
theorem injured_by_higher {ec j s x : ℕ} (hj : j ≤ s)
    (hlt : x < Rest ec (s + 1) j)
    (hin : x ∈ halfList ec j (s + 1)) (hout : x ∉ halfList ec j s) :
    ∃ j', j' < j ∧ x < Rest ec (s + 1) j' := by
  set rs := newRestraints ec (stageState ec s) s with hrs
  obtain ⟨-, hroute⟩ : x ∈ newAt ec s ∧ routeTo rs s x = j % 2 := by
    rcases mem_halfList_succ.mp hin with h | h
    · exact h
    · exact absurd h hout
  have hjrs : x < rs.getD j 0 := by rwa [Rest_succ_eq] at hlt
  rw [routeTo] at hroute
  cases hfind : (List.range (s + 1)).find? (fun k ↦ decide (x < rs.getD k 0)) with
  | none =>
    rw [List.find?_eq_none] at hfind
    have := hfind j (List.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq] at this
    exact absurd hjrs this
  | some j' =>
    rw [hfind] at hroute
    obtain ⟨hp, -, hleast⟩ := range_find?_least hfind
    simp only [decide_eq_true_eq] at hp
    refine ⟨j', ?_, by rwa [Rest_succ_eq]⟩
    have hne : j' ≠ j := by
      intro hEq
      subst hEq
      have hroute' : (if j' % 2 = 0 then 1 else 0) = j' % 2 := hroute
      by_cases hpar : j' % 2 = 0
      · rw [if_pos hpar] at hroute'; omega
      · rw [if_neg hpar] at hroute'; omega
    by_contra hge
    have := hleast j (by omega)
    simp only [decide_eq_false_iff_not] at this
    exact this hjrs

/-! ### Step 1: bounded higher restraints ⇒ finitely many injuries -/

/-- Finitely many bounded quantities have a common bound. -/
theorem uniform_bound {ec j : ℕ} (h : ∀ j', j' < j → ∃ B, ∀ s, Rest ec s j' ≤ B) :
    ∃ B, ∀ j', j' < j → ∀ s, Rest ec s j' ≤ B := by
  induction j with
  | zero => exact ⟨0, fun j' hj' ↦ absurd hj' (by omega)⟩
  | succ j ih =>
    obtain ⟨B, hB⟩ := ih fun j' hj' ↦ h j' (by omega)
    obtain ⟨B', hB'⟩ := h j (by omega)
    refine ⟨max B B', fun j' hj' s ↦ ?_⟩
    rcases Nat.lt_or_ge j' j with h1 | h1
    · exact le_trans (hB j' h1 s) (le_max_left _ _)
    · have : j' = j := by omega
      subst this
      exact le_trans (hB' s) (le_max_right _ _)

/-- **Injury finiteness.**  If every higher-priority restraint is bounded
by `B`, then only numbers below `B` can ever injure `j`; and past the stage
at which `A`'s enumeration settles below `B` (FM's `stabilizes_below`), no
such number enters at all. -/
theorem noInjury_of_bounded {ec j B : ℕ}
    (hB : ∀ j', j' < j → ∀ s, Rest ec s j' ≤ B) :
    ∃ s₀, NoInjuryFrom ec j s₀ := by
  obtain ⟨t₀, ht₀⟩ := enumStage_stabilizes ec B
  refine ⟨max t₀ j, fun t ht x hx hin ↦ ?_⟩
  by_contra hout
  obtain ⟨j', hj', hxj'⟩ := injured_by_higher (by omega) hx hin hout
  have hxB : x < B := lt_of_lt_of_le hxj' (hB j' hj' (t + 1))
  obtain ⟨hnew, hold⟩ : x ∈ enumStage ec (t + 1) ∧ x ∉ enumStage ec t := by
    rcases mem_halfList_succ.mp hin with h | h
    · exact mem_newAt.mp h.1
    · exact absurd h hout
  exact hold ((ht₀ t (by omega) x hxB).mpr ((ht₀ (t + 1) (by omega) x hxB).mp hnew))

/-! ### Preservation: an uninjured requirement freezes its computations -/

/-- Past the last injury, nothing below the restraint ever enters the half
again.  This is the hypothesis shape FM's `run_halt_limit_of_restraint`
consumes, and it is the *only* thing that lemma needs — which is why it
transfers to Sacks verbatim. -/
theorem restraint_respected {ec j s₀ : ℕ} (hinj : NoInjuryFrom ec j s₀)
    {s u : ℕ} (hs : s₀ ≤ s) (hu : u ≤ Rest ec (s + 1) j) :
    ∀ t, s ≤ t → ∀ n, n < u → n ∈ halfF ec j t → n ∈ halfF ec j s := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact fun n _ hn ↦ hn
  | succ t ht ih =>
    intro n hn hmem
    refine ih n hn ?_
    rw [mem_halfF] at hmem ⊢
    exact hinj t (by omega) n
      (lt_of_lt_of_le hn (le_trans hu (Rest_mono (by omega)))) hmem

/-- **The frozen computation.**  An agreement seen at a stage past the last
injury is the true limit computation — same output, same use.  Direct
application of FM's `run_halt_limit_of_restraint`. -/
theorem agree_run_limit {ec j s₀ s y u : ℕ} (hinj : NoInjuryFrom ec j s₀)
    (hs : s₀ ≤ s) (hjs : j ≤ s)
    (hy : y < lenAgree ec (stageState ec s) s j)
    (hu : agreeAt ec (stageState ec s) s j y = some u) :
    run s (PartOracle.ofFun (charFun (halfSet ec j)))
        (OracleCode.ofNatCode (j / 2)) y
      = .halt ⟨natOfBool (decide (y ∈ enumStage ec s)), u⟩ := by
  have hrun := agreeAt_eq_some.mp hu
  rw [show oracleOf (stageState ec s) j = halfList ec j s from rfl,
    snapshotOf_eq_snapshot] at hrun
  exact run_halt_limit_of_restraint (F := halfF ec j) (halfF_mono ec j) hrun
    (restraint_respected hinj hs
      (le_trans (use_le_restraintAt hy hu) (restraintAt_le_Rest hjs)))

theorem agree_computes {ec j s₀ s y : ℕ} (hinj : NoInjuryFrom ec j s₀)
    (hs : s₀ ≤ s) (hjs : j ≤ s)
    (hy : y < lenAgree ec (stageState ec s) s j) :
    Computes (OracleCode.ofNatCode (j / 2)) (charFun (halfSet ec j)) y
      (natOfBool (decide (y ∈ enumStage ec s))) := by
  obtain ⟨u, hu⟩ := agreeAt_isSome_iff.mp (agreeAt_isSome_of_lt_lenAgree hy)
  exact ⟨s, _, agree_run_limit hinj hs hjs hy hu, rfl⟩

/-! ### Totality makes the agreement grow -/

/-- If the reduction is total and correct at `y`, then from some stage on
the agreement test at `y` succeeds at *every* later stage.  (FM's
`run_halt_snapshot_of_limit` finds a true stage; FM's
`run_halt_toFinset_snapshot` moves it to full fuel and full snapshot
length.) -/
theorem agree_eventually {ec j y : ℕ}
    (hy : Computes (OracleCode.ofNatCode (j / 2)) (charFun (halfSet ec j)) y
      (natOfBool (charFun (enumSet ec) y))) :
    ∃ S, ∀ s, S ≤ s → (agreeAt ec (stageState ec s) s j y).isSome = true := by
  obtain ⟨k, d, hrun, hout⟩ := hy
  obtain ⟨o, du⟩ := d
  have ho : o = natOfBool (charFun (enumSet ec) y) := hout
  subst ho
  obtain ⟨s₀, hs₀⟩ := run_halt_snapshot_of_limit (F := halfF ec j) (halfF_mono ec j) hrun
  obtain ⟨t₁, ht₁⟩ := enumStage_stabilizes ec (y + 1)
  refine ⟨max (max s₀ t₁) (max k du), fun s hs ↦ ?_⟩
  have h2 := hs₀ s (by omega)
  have h3 : run s (PartOracle.ofSnapshot (snapshotOf (halfList ec j s) s))
      (OracleCode.ofNatCode (j / 2)) y = .halt ⟨_, du⟩ :=
    run_halt_toFinset_snapshot (by omega) (by show du ≤ s; omega) h2
  have hval : natOfBool (charFun (enumSet ec) y)
      = natOfBool (decide (y ∈ enumStage ec s)) := by
    rw [decide_enumStage_eq (ht₁ s (by omega) y (by omega))]
  rw [hval] at h3
  have : agreeAt ec (stageState ec s) s j y = some du :=
    agreeAt_eq_some.mpr (by
      rw [show oracleOf (stageState ec s) j = halfList ec j s from rfl]
      exact h3)
  rw [this]
  rfl

/-- The same, uniformly over an initial segment of arguments. -/
theorem agree_eventually_below {ec j : ℕ}
    (hall : ∀ y, Computes (OracleCode.ofNatCode (j / 2)) (charFun (halfSet ec j)) y
      (natOfBool (charFun (enumSet ec) y))) (n : ℕ) :
    ∃ S, ∀ s, S ≤ s → ∀ z, z < n → (agreeAt ec (stageState ec s) s j z).isSome = true := by
  induction n with
  | zero => exact ⟨0, fun s _ z hz ↦ absurd hz (by omega)⟩
  | succ n ih =>
    obtain ⟨S, hS⟩ := ih
    obtain ⟨S', hS'⟩ := agree_eventually (ec := ec) (j := j) (y := n) (hall n)
    refine ⟨max S S', fun s hs z hz ↦ ?_⟩
    rcases Nat.lt_or_ge z n with h | h
    · exact hS s (by omega) z h
    · have : z = n := by omega
      subst this
      exact hS' s (by omega)

/-! ### Step 2: the genuinely new lemma -/

/-- **The non-computability hypothesis is what makes the requirements
satisfiable.**

If requirement `N_j` is never injured after stage `s₀`, and program
`Φ_{j/2}` with oracle `A_{j%2}` nevertheless computes the characteristic
function of `A` everywhere, then `A` is computable.

The algorithm: to decide `y ∈ A`, search for a stage `s ≥ s₀` whose
agreement length exceeds `y`, and report `y ∈ A_s`.  Such a stage exists
because the reduction is total (`agree_eventually_below`); the answer is
correct because past `s₀` the agreeing computation is frozen
(`agree_run_limit`), so it *is* the true value `Φ_{j/2}^{A_i}(y) = χ_A(y)`;
and the search is effective because the whole construction is primitive
recursive (`computableSet_of_agreement`).

This lemma has no counterpart in Friedberg–Muchnik.  FM's requirements are
satisfiable because their witnesses are fresh — a property of the
construction.  A splitting requirement is satisfiable only because of a
property of the *given* set, and this is where that hypothesis is spent. -/
theorem unsatisfied_requirement_computes {ec j s₀ : ℕ} (hinj : NoInjuryFrom ec j s₀)
    (hall : ∀ y, Computes (OracleCode.ofNatCode (j / 2)) (charFun (halfSet ec j)) y
      (natOfBool (charFun (enumSet ec) y))) :
    ComputableSet (enumSet ec) := by
  refine computableSet_of_agreement (ec := ec) (j := j) (s₀ := max s₀ (j + 1))
    (fun y ↦ ?_) (fun y s hs hy ↦ ?_)
  · obtain ⟨S, hS⟩ := agree_eventually_below hall (y + 1)
    refine ⟨max S (max (max s₀ (j + 1)) (y + 1)), by omega, ?_⟩
    exact lt_lenAgree (by omega) fun z hz ↦ hS _ (by omega) z (by omega)
  · have h1 := agree_computes hinj (le_trans (le_max_left _ _) hs)
      (by have := le_trans (le_max_right s₀ (j + 1)) hs; omega) hy
    exact enumStage_iff_of_eq (natOfBool_inj (Computes.unique h1 (hall y)))

/-! ### Step 3: a satisfied requirement has a bounded restraint -/

open Classical in
/-- The use of the *limit* computation of `Φ_{j/2}^{A_{j%2}}` at `y`, when
there is one.  Well defined by FM's `run_halt_unique`: the recorded use of
a halting run against a fixed total oracle does not depend on the fuel.
This is the number that bounds the restraint, and it exists only because
the evaluator records the use at all. -/
noncomputable def limUse (ec j y : ℕ) : ℕ :=
  if h : ∃ d : HaltData, ∃ k, run k (PartOracle.ofFun (charFun (halfSet ec j)))
      (OracleCode.ofNatCode (j / 2)) y = .halt d
  then (Classical.choose h).use else 0

theorem use_eq_limUse {ec j y k : ℕ} {d : HaltData}
    (h : run k (PartOracle.ofFun (charFun (halfSet ec j)))
      (OracleCode.ofNatCode (j / 2)) y = .halt d) :
    d.use = limUse ec j y := by
  have hex : ∃ d : HaltData, ∃ k, run k (PartOracle.ofFun (charFun (halfSet ec j)))
      (OracleCode.ofNatCode (j / 2)) y = .halt d := ⟨d, k, h⟩
  rw [limUse, dif_pos hex]
  obtain ⟨k', hk'⟩ := Classical.choose_spec hex
  rw [run_halt_unique (X := charFun (halfSet ec j))
    (PartOracle.consistent_ofFun _) (PartOracle.consistent_ofFun _) h hk']

/-- **A satisfied requirement restrains only finitely much.**  Once the
reduction is wrong at some `y₀`, the agreement can never again reach past
`y₀`; and every use it does protect is the use of a *limit* computation at
an argument `≤ y₀`, hence one of finitely many fixed numbers. -/
theorem restraint_bounded_of {ec j s₀ : ℕ} (hinj : NoInjuryFrom ec j s₀)
    (hsat : ¬ ∀ y, Computes (OracleCode.ofNatCode (j / 2)) (charFun (halfSet ec j)) y
      (natOfBool (charFun (enumSet ec) y))) :
    ∃ B, ∀ s, Rest ec s j ≤ B := by
  obtain ⟨y₀, hy₀⟩ := Classical.not_forall.mp hsat
  obtain ⟨t₁, ht₁⟩ := enumStage_stabilizes ec (y₀ + 1)
  obtain ⟨s₁, hs₁₀, hs₁j, hs₁t⟩ : ∃ s₁, s₀ ≤ s₁ ∧ j < s₁ ∧ t₁ ≤ s₁ :=
    ⟨max (max s₀ (j + 1)) t₁, by omega, by omega, by omega⟩
  -- the agreement can never again reach past `y₀`
  have hlen : ∀ s, s₁ ≤ s → lenAgree ec (stageState ec s) s j ≤ y₀ := by
    intro s hs
    by_contra hgt
    refine hy₀ ?_
    have h1 := agree_computes hinj (show s₀ ≤ s by omega) (show j ≤ s by omega)
      (show y₀ < lenAgree ec (stageState ec s) s j by omega)
    rwa [decide_enumStage_eq (ht₁ s (by omega) y₀ (by omega))] at h1
  -- every protected use is a limit use at an argument `≤ y₀`
  set M := (Finset.range (y₀ + 1)).sup (limUse ec j) with hMdef
  have hrest : ∀ s, s₁ ≤ s → restraintAt ec (stageState ec s) s j ≤ M := by
    intro s hs
    have hlens := hlen s hs
    refine restraintAt_le fun y hy ↦ ?_
    obtain ⟨u, hu⟩ := agreeAt_isSome_iff.mp (agreeAt_isSome_of_lt_lenAgree hy)
    have hlim := agree_run_limit hinj (show s₀ ≤ s by omega) (show j ≤ s by omega) hy hu
    have hue : u = limUse ec j y := use_eq_limUse hlim
    rw [hu, Option.getD_some, hue]
    exact Finset.le_sup (Finset.mem_range.mpr (by omega))
  -- hence the cumulative restraint is bounded
  refine ⟨max (Rest ec s₁ j) M, fun s ↦ ?_⟩
  rcases Nat.lt_or_ge s s₁ with h | h
  · exact le_trans (Rest_mono (by omega)) (le_max_left _ _)
  · induction s, h using Nat.le_induction with
    | base => exact le_max_left _ _
    | succ t ht ih =>
      rw [Rest_succ_of_le (by omega)]
      exact max_le ih (le_trans (hrest t ht) (le_max_right _ _))

/-! ### The induction along the priority order -/

section
variable {ec : ℕ}

/-- **Every requirement's restraint is bounded** — by strong induction on
the priority, running steps 1 → 2 → 3.  Step 2 is where the hypothesis
`¬ ComputableSet A` is consumed.  (Compare FM's `quiet_above`: same
induction along the priority order, entirely different content.) -/
theorem restraint_bounded (hA : ¬ ComputableSet (enumSet ec)) (j : ℕ) :
    ∃ B, ∀ s, Rest ec s j ≤ B := by
  induction j using Nat.strong_induction_on with
  | _ j IH =>
    obtain ⟨B, hB⟩ := uniform_bound fun j' hj' ↦ IH j' hj'
    obtain ⟨s₀, hinj⟩ := noInjury_of_bounded hB
    exact restraint_bounded_of hinj fun hall ↦ hA (unsatisfied_requirement_computes hinj hall)

/-- **Every requirement is satisfied**: no program computes `χ_A` from
either half.  (FM's `R_satisfied` / `S_satisfied`.) -/
theorem requirement_satisfied (hA : ¬ ComputableSet (enumSet ec)) (j : ℕ) :
    ¬ ∀ y, Computes (OracleCode.ofNatCode (j / 2)) (charFun (halfSet ec j)) y
      (natOfBool (charFun (enumSet ec) y)) := by
  obtain ⟨B, hB⟩ := uniform_bound fun j' (_ : j' < j) ↦ restraint_bounded hA j'
  obtain ⟨s₀, hinj⟩ := noInjury_of_bounded hB
  exact fun hall ↦ hA (unsatisfied_requirement_computes hinj hall)

end

end SacksSplitting
