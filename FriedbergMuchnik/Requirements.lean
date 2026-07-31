/-
# Satisfaction of the requirements

Soare VII.2, the verification: every requirement is met by its stabilized
state.

For `R_e : A ≠ Φ_e^B` (priority `i = 2e`; `S_e` at `2e + 1` is the mirror
image), consider the stable record from `FiniteInjury.exists_stable`.  It
has a witness `x` (else the requirement would still require attention).

* **Acted**: the invariant `acted_in` puts `x ∈ A`, and `acted_comp`
  holds the frozen computation `Φ_e^{B_{s₁}}(x) ↓ = 0` with use =
  restraint.  The quiet tail plus `wit_ge` show no number below the
  restraint ever enters `B` again (`restraint_respected_B`), so by the
  preservation lemma the computation transfers to the limit:
  `Φ_e^B(x) ↓ = 0 ≠ 1 = χ_A(x)`.

* **Never acted**: `unacted_out` keeps `x ∉ A` forever, so a correct
  reduction would compute `Φ_e^B(x) ↓ = 0`.  By `run_halt_snapshot_of_limit`
  that computation is visible against every late stage's snapshot, so at
  a late enough stage the requirement *requires attention* — contradicting
  `stable_not_requires`.  Hence no reduction computes `χ_A` from `B`.
-/
import FriedbergMuchnik.FiniteInjury
import FriedbergMuchnik.Invariants

namespace FriedbergMuchnik

/-! ### Small helpers -/

theorem requiresAttention_of_no_witness {st : ConsState} {s i : ℕ}
    {r : ReqState} (hr : st.reqs[i]? = some r) (hw : r.witness = none) :
    st.requiresAttention s i = true := by
  simp [ConsState.requiresAttention, hr, hw]

theorem requiresAttention_eq_true {st : ConsState} {s i : ℕ} {r : ReqState}
    {x : ℕ} (hr : st.reqs[i]? = some r) (hw : r.witness = some x)
    (ha : r.acted = false) (hc : (st.convCheck s i x).isSome = true) :
    st.requiresAttention s i = true := by
  simp [ConsState.requiresAttention, hr, hw, ha, hc]

/-- After stabilization, numbers below the stable restraint never enter
`B` again (quiet tail + `wit_ge`: later actors are of lower priority and
use fresh witnesses `≥` the restraint). -/
theorem restraint_respected_B {i s₁ : ℕ} {r : ReqState} (hi₁ : i < s₁)
    (hstab : ∀ s, s₁ ≤ s → (stageState s).reqs[i]? = some r)
    (hquiet : ∀ s, s₁ ≤ s → ∀ j, j ≤ i → attended s ≠ some j) :
    ∀ t, s₁ ≤ t → ∀ n, n < r.restraint → n ∈ BstageF t → n ∈ BstageF s₁ := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact fun n _ hn => hn
  | succ t ht ih =>
    intro n hnu hmem
    rcases Blist_succ t with heq |
        ⟨j, rj, y, u', hatt, _hodd, hrj, hwj, _hactj, _hu', heqB⟩
    · apply ih n hnu
      rw [BstageF, List.mem_toFinset, heq] at hmem
      rw [BstageF, List.mem_toFinset]
      exact hmem
    · have hji : i < j := by
        by_contra hle
        exact hquiet t (by omega) j (by omega) hatt
      have hinv := consInv_ext (consInv_stage t)
      have hri' : (preState t).reqs[i]? = some r := by
        rw [preState_reqs_getElem?_lt (by omega)]
        exact hstab t (by omega)
      have hyu : r.restraint ≤ y := hinv.wit_ge j i rj r y hji hrj hri' hwj
      rw [BstageF, List.mem_toFinset, heqB, List.mem_cons] at hmem
      rcases hmem with rfl | hmem'
      · omega
      · apply ih n hnu
        rw [BstageF, List.mem_toFinset]
        exact hmem'

/-- Mirror image for `A`. -/
theorem restraint_respected_A {i s₁ : ℕ} {r : ReqState} (hi₁ : i < s₁)
    (hstab : ∀ s, s₁ ≤ s → (stageState s).reqs[i]? = some r)
    (hquiet : ∀ s, s₁ ≤ s → ∀ j, j ≤ i → attended s ≠ some j) :
    ∀ t, s₁ ≤ t → ∀ n, n < r.restraint → n ∈ AstageF t → n ∈ AstageF s₁ := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact fun n _ hn => hn
  | succ t ht ih =>
    intro n hnu hmem
    rcases Alist_succ t with heq |
        ⟨j, rj, y, u', hatt, _heven, hrj, hwj, _hactj, _hu', heqA⟩
    · apply ih n hnu
      rw [AstageF, List.mem_toFinset, heq] at hmem
      rw [AstageF, List.mem_toFinset]
      exact hmem
    · have hji : i < j := by
        by_contra hle
        exact hquiet t (by omega) j (by omega) hatt
      have hinv := consInv_ext (consInv_stage t)
      have hri' : (preState t).reqs[i]? = some r := by
        rw [preState_reqs_getElem?_lt (by omega)]
        exact hstab t (by omega)
      have hyu : r.restraint ≤ y := hinv.wit_ge j i rj r y hji hrj hri' hwj
      rw [AstageF, List.mem_toFinset, heqA, List.mem_cons] at hmem
      rcases hmem with rfl | hmem'
      · omega
      · apply ih n hnu
        rw [AstageF, List.mem_toFinset]
        exact hmem'

/-! ### Satisfaction of the `R` requirements (`A ≠ Φ_e^B`) -/

/-- **Requirement `R_e` is satisfied** (Soare VII.2): program `e` with
oracle `B` does not compute the characteristic function of `A`. -/
theorem R_satisfied (e : ℕ) :
    ¬ ∀ x, Computes (OracleCode.ofNatCode e) (charFun Bset) x
      (natOfBool (charFun Aset x)) := by
  intro hall
  have hpar : (2 * e) % 2 = 0 := by omega
  have hdiv : 2 * e / 2 = e := by omega
  obtain ⟨s₁, r, hi₁, hstab, hquiet⟩ := exists_stable (2 * e)
  have hnr := stable_not_requires hquiet hi₁
  have hpre : ∀ s, s₁ ≤ s → (preState s).reqs[2 * e]? = some r := by
    intro s hs
    rw [preState_reqs_getElem?_lt (by omega)]
    exact hstab s hs
  obtain ⟨x, hw⟩ : ∃ x, r.witness = some x := by
    cases hwo : r.witness with
    | some x => exact ⟨x, rfl⟩
    | none =>
      have h1 := hnr s₁ le_rfl
      rw [requiresAttention_of_no_witness (hpre s₁ le_rfl) hwo] at h1
      exact absurd h1 (by simp)
  by_cases hacted : r.acted
  · -- acted: x ∈ A but Φ_e^B(x) = 0, frozen by the restraint
    have inv := consInv_stage s₁
    have hrec := hstab s₁ le_rfl
    have hxA : x ∈ Aset := by
      have hin := inv.acted_in (2 * e) r x hrec hw hacted
      unfold ConsState.targetOf at hin
      rw [if_pos hpar] at hin
      exact mem_limitSet.mpr ⟨s₁, by rw [AstageF, List.mem_toFinset]; exact hin⟩
    have hcomp : Computes (OracleCode.ofNatCode e) (charFun Bset) x 0 := by
      obtain ⟨k, len, hk⟩ := inv.acted_comp (2 * e) r x hrec hw hacted
      unfold ConsState.oracleOf at hk
      rw [if_pos hpar, hdiv, snapshotOf_eq_snapshot] at hk
      have hlim := run_halt_limit_of_restraint (F := BstageF) BstageF_mono hk
        (restraint_respected_B hi₁ hstab hquiet)
      exact ⟨k, ⟨0, r.restraint⟩, hlim, rfl⟩
    have h1 := hall x
    rw [charFun_eq_true.mpr hxA] at h1
    have h10 := Computes.unique h1 hcomp
    simp [natOfBool] at h10
  · -- never acted: x ∉ A, so a correct reduction outputs 0 — but then the
    -- requirement would eventually require attention
    have hfalse : r.acted = false := by simpa using hacted
    have hxA : x ∉ Aset := by
      intro hmem
      obtain ⟨t, ht⟩ := mem_limitSet.mp hmem
      have ht' : x ∈ AstageF (max t s₁) :=
        AstageF_mono.subset_of_le (le_max_left _ _) ht
      have hout := ((consInv_stage (max t s₁)).unacted_out (2 * e) r x
        (hstab _ (le_max_right _ _)) hw hfalse).1
      rw [AstageF, List.mem_toFinset] at ht'
      exact hout ht'
    have h0 : Computes (OracleCode.ofNatCode e) (charFun Bset) x 0 := by
      have h1 := hall x
      rw [charFun_eq_false.mpr hxA] at h1
      exact h1
    obtain ⟨k, d, hrun, hout⟩ := h0
    obtain ⟨o, du⟩ := d
    have ho : o = 0 := hout
    subst ho
    obtain ⟨s₀', hs₀'⟩ := run_halt_snapshot_of_limit (F := BstageF)
      BstageF_mono hrun
    have hs₁' : s₁ ≤ max (max s₀' s₁) (max k du) := by omega
    set s := max (max s₀' s₁) (max k du) with hsdef
    have h2 := hs₀' s (by omega)
    have h3 : run s (PartOracle.ofSnapshot (snapshotOf ((stageState s).Blist) s))
        (OracleCode.ofNatCode e) x = .halt ⟨0, du⟩ :=
      run_halt_toFinset_snapshot (by omega) (by show du ≤ s; omega) h2
    have hcc : (preState s).convCheck s (2 * e) x = some du := by
      rw [ConsState.convCheck_eq_some]
      unfold ConsState.oracleOf
      rw [if_pos hpar, hdiv]
      simpa using h3
    have hreq : (preState s).requiresAttention s (2 * e) = true :=
      requiresAttention_eq_true (hpre s hs₁') hw hfalse (by rw [hcc]; rfl)
    have h4 := hnr s hs₁'
    rw [hreq] at h4
    exact absurd h4 (by simp)

/-! ### Satisfaction of the `S` requirements (`B ≠ Φ_e^A`) -/

/-- **Requirement `S_e` is satisfied**: program `e` with oracle `A` does
not compute the characteristic function of `B`.  Mirror image of
`R_satisfied` at priority `2e + 1`. -/
theorem S_satisfied (e : ℕ) :
    ¬ ∀ x, Computes (OracleCode.ofNatCode e) (charFun Aset) x
      (natOfBool (charFun Bset x)) := by
  intro hall
  have hpar : ¬((2 * e + 1) % 2 = 0) := by omega
  have hdiv : (2 * e + 1) / 2 = e := by omega
  obtain ⟨s₁, r, hi₁, hstab, hquiet⟩ := exists_stable (2 * e + 1)
  have hnr := stable_not_requires hquiet hi₁
  have hpre : ∀ s, s₁ ≤ s → (preState s).reqs[2 * e + 1]? = some r := by
    intro s hs
    rw [preState_reqs_getElem?_lt (by omega)]
    exact hstab s hs
  obtain ⟨x, hw⟩ : ∃ x, r.witness = some x := by
    cases hwo : r.witness with
    | some x => exact ⟨x, rfl⟩
    | none =>
      have h1 := hnr s₁ le_rfl
      rw [requiresAttention_of_no_witness (hpre s₁ le_rfl) hwo] at h1
      exact absurd h1 (by simp)
  by_cases hacted : r.acted
  · have inv := consInv_stage s₁
    have hrec := hstab s₁ le_rfl
    have hxB : x ∈ Bset := by
      have hin := inv.acted_in (2 * e + 1) r x hrec hw hacted
      unfold ConsState.targetOf at hin
      rw [if_neg hpar] at hin
      exact mem_limitSet.mpr ⟨s₁, by rw [BstageF, List.mem_toFinset]; exact hin⟩
    have hcomp : Computes (OracleCode.ofNatCode e) (charFun Aset) x 0 := by
      obtain ⟨k, len, hk⟩ := inv.acted_comp (2 * e + 1) r x hrec hw hacted
      unfold ConsState.oracleOf at hk
      rw [if_neg hpar, hdiv, snapshotOf_eq_snapshot] at hk
      have hlim := run_halt_limit_of_restraint (F := AstageF) AstageF_mono hk
        (restraint_respected_A hi₁ hstab hquiet)
      exact ⟨k, ⟨0, r.restraint⟩, hlim, rfl⟩
    have h1 := hall x
    rw [charFun_eq_true.mpr hxB] at h1
    have h10 := Computes.unique h1 hcomp
    simp [natOfBool] at h10
  · have hfalse : r.acted = false := by simpa using hacted
    have hxB : x ∉ Bset := by
      intro hmem
      obtain ⟨t, ht⟩ := mem_limitSet.mp hmem
      have ht' : x ∈ BstageF (max t s₁) :=
        BstageF_mono.subset_of_le (le_max_left _ _) ht
      have hout := ((consInv_stage (max t s₁)).unacted_out (2 * e + 1) r x
        (hstab _ (le_max_right _ _)) hw hfalse).2
      rw [BstageF, List.mem_toFinset] at ht'
      exact hout ht'
    have h0 : Computes (OracleCode.ofNatCode e) (charFun Aset) x 0 := by
      have h1 := hall x
      rw [charFun_eq_false.mpr hxB] at h1
      exact h1
    obtain ⟨k, d, hrun, hout⟩ := h0
    obtain ⟨o, du⟩ := d
    have ho : o = 0 := hout
    subst ho
    obtain ⟨s₀', hs₀'⟩ := run_halt_snapshot_of_limit (F := AstageF)
      AstageF_mono hrun
    have hs₁' : s₁ ≤ max (max s₀' s₁) (max k du) := by omega
    set s := max (max s₀' s₁) (max k du) with hsdef
    have h2 := hs₀' s (by omega)
    have h3 : run s (PartOracle.ofSnapshot (snapshotOf ((stageState s).Alist) s))
        (OracleCode.ofNatCode e) x = .halt ⟨0, du⟩ :=
      run_halt_toFinset_snapshot (by omega) (by show du ≤ s; omega) h2
    have hcc : (preState s).convCheck s (2 * e + 1) x = some du := by
      rw [ConsState.convCheck_eq_some]
      unfold ConsState.oracleOf
      rw [if_neg hpar, hdiv]
      simpa using h3
    have hreq : (preState s).requiresAttention s (2 * e + 1) = true :=
      requiresAttention_eq_true (hpre s hs₁') hw hfalse (by rw [hcc]; rfl)
    have h4 := hnr s hs₁'
    rw [hreq] at h4
    exact absurd h4 (by simp)

/-! ### The two non-reducibilities -/

open scoped FriedbergMuchnik in
/-- `A` is not Turing reducible to `B`: any candidate reduction is
`ofNatCode e` for its own number `e` (enumeration adequacy), and `R_e`
kills it. -/
theorem not_A_le_B : ¬ TuringReducible Aset Bset := by
  rintro ⟨c, hc⟩
  refine R_satisfied (OracleCode.encodeCode c) (fun x => ?_)
  rw [OracleCode.ofNatCode_encodeCode]
  exact hc x

/-- `B` is not Turing reducible to `A`. -/
theorem not_B_le_A : ¬ TuringReducible Bset Aset := by
  rintro ⟨c, hc⟩
  refine S_satisfied (OracleCode.encodeCode c) (fun x => ?_)
  rw [OracleCode.ofNatCode_encodeCode]
  exact hc x

end FriedbergMuchnik
