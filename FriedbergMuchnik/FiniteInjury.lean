import FriedbergMuchnik.StageDynamics

/-!
# Finite injury

The inductive heart of the priority argument (Soare VII.2, "each
requirement receives attention at most finitely often, and hence is
injured at most finitely often"):

* `record_stable_of` — while nothing of priority `≤ i` receives
  attention, requirement `i`'s record is frozen;
* the **rank argument**: give a record rank `0`–`2` (has a witness? has
  acted?).  While the higher priorities are quiet the rank never drops
  (no initialization), and every attention to `i` raises it strictly
  (appointment sets the witness, action sets the flag).  So `i` receives
  attention at most twice after its superiors go quiet — this replaces
  the informal "at most finitely often" count, with no closed-form bound
  ever stated for the whole construction;
* `quiet_above` — by induction along the priority order: for every `i`
  there is a stage after which no requirement `j ≤ i` ever receives
  attention again;
* `exists_stable` / `stable_not_requires` — the packaged conclusion the
  satisfaction proofs consume: a stage from which `i`'s record is
  constant, nothing `≤ i` is attended, and `i` never again *requires*
  attention (if it did, something `≤ i` would receive it).
-/

namespace FriedbergMuchnik

open OracleComputability

/-! ### Record stability -/

/-- One quiet step: if nothing of priority `≤ i` receives attention at
stage `s + 1` (and `i`'s record already exists), the record is
unchanged. -/
theorem record_step_stable {s i : ℕ} (hi : i < s)
    (h : ∀ j, j ≤ i → attended s ≠ some j) :
    (stageState (s + 1)).reqs[i]? = (stageState s).reqs[i]? := by
  rw [reqs_getElem?_succ_of_lt, preState_reqs_getElem?_lt hi]
  intro i' ha'
  by_contra hle
  exact h i' (by omega) ha'

/-- Quiet interval: the record is frozen across any interval during
which nothing of priority `≤ i` receives attention. -/
theorem record_stable_of {t t' i : ℕ} (hi : i < t) (htt : t ≤ t')
    (h : ∀ s, t ≤ s → s < t' → ∀ j, j ≤ i → attended s ≠ some j) :
    (stageState t').reqs[i]? = (stageState t).reqs[i]? := by
  revert h
  induction t', htt using Nat.le_induction with
  | base => intro _; rfl
  | succ t'' htt ih =>
    intro h
    rw [record_step_stable (by omega) (h t'' htt (by omega)),
      ih (fun s hs hs' ↦ h s hs (by omega))]

/-! ### The rank argument -/

/-- The rank of a requirement record: witness appointed (+1), acted
(+1).  Attention strictly increases it; only initialization (an act of
higher priority) can reset it. -/
def rank (r : ReqState) : ℕ :=
  (if r.witness.isSome then 1 else 0) + (if r.acted then 1 else 0)

theorem rank_le_two (r : ReqState) : rank r ≤ 2 := by
  unfold rank
  split <;> split <;> omega

/-- The rank of requirement `i`'s record at stage `s`. -/
def reqRank (i s : ℕ) : ℕ :=
  rank (((stageState s).reqs[i]?).getD ReqState.init)

theorem reqRank_le_two (i s : ℕ) : reqRank i s ≤ 2 :=
  rank_le_two _

/-- Attention strictly increases the rank (appointment sets the witness
bit, action sets the acted bit). -/
theorem reqRank_incr {s i : ℕ} (hi : i < s) (ha : attended s = some i) :
    reqRank i (s + 1) = reqRank i s + 1 := by
  rcases step_cases s with ⟨hn, _⟩ | ⟨i', r, ha', hri, hw, hst⟩ |
      ⟨i', r, x, u, ha', hri, hw, hact, hu, hst⟩
  · rw [ha] at hn; exact absurd hn (by simp)
  · rw [ha] at ha'
    injection ha' with hii
    subst hii
    have hpre : (stageState s).reqs[i]? = some r :=
      (preState_reqs_getElem?_lt hi).symm.trans hri
    have hpost : (stageState (s + 1)).reqs[i]? =
        some { r with witness := some (preState s).fresh } := by
      rw [hst]
      exact List.getElem?_set_self (by simp; omega)
    rw [reqRank, reqRank, hpre, hpost]
    cases hact : r.acted <;> simp [rank, hw, hact]
  · rw [ha] at ha'
    injection ha' with hii
    subst hii
    have hpre : (stageState s).reqs[i]? = some r :=
      (preState_reqs_getElem?_lt hi).symm.trans hri
    have hlen : ((preState s).reqs.take i).length = i := by
      simp [List.length_take]
      omega
    have hpost : (stageState (s + 1)).reqs[i]? =
        some (⟨some x, true, u⟩ : ReqState) := by
      rw [hst]
      show ((preState s).reqs.take i ++ _ :: _)[i]? = _
      rw [List.getElem?_append_right (by rw [hlen])]
      simp [hlen]
    rw [reqRank, reqRank, hpre, hpost]
    simp [rank, hw, hact]

/-- A quiet-below step never decreases the rank. -/
theorem reqRank_mono {s i : ℕ} (hi : i < s)
    (h : ∀ j, j < i → attended s ≠ some j) :
    reqRank i s ≤ reqRank i (s + 1) := by
  by_cases ha : attended s = some i
  · rw [reqRank_incr hi ha]; omega
  · have hstable : (stageState (s + 1)).reqs[i]? = (stageState s).reqs[i]? :=
      record_step_stable hi (fun j hj hja ↦ by
        rcases Nat.lt_or_ge j i with hlt | hge
        · exact h j hlt hja
        · have : j = i := by omega
          exact ha (this ▸ hja))
    rw [reqRank, reqRank, hstable]

/-- Rank monotonicity across a quiet-below interval. -/
theorem reqRank_mono_le {i a b : ℕ} (hia : i < a) (hab : a ≤ b)
    (h : ∀ s, a ≤ s → s < b → ∀ j, j < i → attended s ≠ some j) :
    reqRank i a ≤ reqRank i b := by
  revert h
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ b hab ih =>
    intro h
    exact (ih (fun s hs hs' ↦ h s hs (by omega))).trans
      (reqRank_mono (by omega) (h b hab (by omega)))

/-! ### Every requirement goes quiet -/

/-- The induction step: once everything of strictly higher priority is
quiet, requirement `i` receives attention at most twice more (rank `0`
to `2`), so eventually everything of priority `≤ i` is quiet. -/
private theorem quiet_step {i : ℕ}
    (h : ∃ s₀, ∀ s, s₀ ≤ s → ∀ j, j < i → attended s ≠ some j) :
    ∃ s₁, ∀ s, s₁ ≤ s → ∀ j, j ≤ i → attended s ≠ some j := by
  obtain ⟨s₀, h₀⟩ := h
  by_cases hinf : ∀ t, ∃ s, t ≤ s ∧ attended s = some i
  · exfalso
    set base := max s₀ (i + 1) with hbase
    obtain ⟨t₁, ht₁, ha₁⟩ := hinf base
    obtain ⟨t₂, ht₂, ha₂⟩ := hinf (t₁ + 1)
    obtain ⟨t₃, ht₃, ha₃⟩ := hinf (t₂ + 1)
    have hquiet : ∀ s, base ≤ s → ∀ j, j < i → attended s ≠ some j :=
      fun s hs ↦ h₀ s (le_trans (le_max_left _ _) hs)
    have hbi : i + 1 ≤ base := le_max_right _ _
    have hr₁ : reqRank i (t₁ + 1) = reqRank i t₁ + 1 :=
      reqRank_incr (by omega) ha₁
    have hm₁ : reqRank i (t₁ + 1) ≤ reqRank i t₂ :=
      reqRank_mono_le (by omega) ht₂
        (fun s hs _ ↦ hquiet s (by omega))
    have hr₂ : reqRank i (t₂ + 1) = reqRank i t₂ + 1 :=
      reqRank_incr (by omega) ha₂
    have hm₂ : reqRank i (t₂ + 1) ≤ reqRank i t₃ :=
      reqRank_mono_le (by omega) ht₃
        (fun s hs _ ↦ hquiet s (by omega))
    have hr₃ : reqRank i (t₃ + 1) = reqRank i t₃ + 1 :=
      reqRank_incr (by omega) ha₃
    have hb := reqRank_le_two i (t₃ + 1)
    omega
  · push_neg at hinf
    obtain ⟨t, ht⟩ := hinf
    refine ⟨max s₀ t, fun s hs j hj ↦ ?_⟩
    rcases Nat.lt_or_ge j i with hlt | hge
    · exact h₀ s (le_trans (le_max_left _ _) hs) j hlt
    · have hji : j = i := by omega
      subst hji
      exact ht s (le_trans (le_max_right _ _) hs)

/-- **Finite injury** (Soare VII.2): for every priority level `i` there
is a stage after which no requirement of priority `≤ i` ever receives
attention again.  Induction along the priority order; no closed-form
injury count is stated or needed. -/
theorem quiet_above (i : ℕ) :
    ∃ s₀, ∀ s, s₀ ≤ s → ∀ j, j ≤ i → attended s ≠ some j := by
  induction i with
  | zero => exact quiet_step ⟨0, fun s _ j hj ↦ absurd hj (by omega)⟩
  | succ i IH =>
    obtain ⟨s₀, h₀⟩ := IH
    exact quiet_step ⟨s₀, fun s hs j hj ↦ h₀ s hs j (by omega)⟩

/-! ### The stabilization package -/

/-- For every requirement there is a stage from which its record is a
fixed value and nothing of its priority or higher is ever attended.
This is the state in which the satisfaction argument examines it. -/
theorem exists_stable (i : ℕ) :
    ∃ s₁ r, i < s₁ ∧
      (∀ s, s₁ ≤ s → (stageState s).reqs[i]? = some r) ∧
      (∀ s, s₁ ≤ s → ∀ j, j ≤ i → attended s ≠ some j) := by
  obtain ⟨s₀, h₀⟩ := quiet_above i
  set s₁ := max s₀ (i + 1) with hs₁
  have hi₁ : i < s₁ := by omega
  have hquiet : ∀ s, s₁ ≤ s → ∀ j, j ≤ i → attended s ≠ some j :=
    fun s hs ↦ h₀ s (le_trans (le_max_left _ _) hs)
  have hex : ∃ r, (stageState s₁).reqs[i]? = some r := by
    have hlen : i < (stageState s₁).reqs.length := by
      rw [reqs_length]; exact hi₁
    exact ⟨_, List.getElem?_eq_getElem hlen⟩
  obtain ⟨r, hr⟩ := hex
  refine ⟨s₁, r, hi₁, fun s hs ↦ ?_, hquiet⟩
  rw [record_stable_of hi₁ hs (fun t hts _ ↦ hquiet t hts), hr]

/-- After its stabilization stage, a requirement never again *requires*
attention — otherwise something of its priority or higher would receive
it. -/
theorem stable_not_requires {i s₁ : ℕ}
    (hquiet : ∀ s, s₁ ≤ s → ∀ j, j ≤ i → attended s ≠ some j)
    (hi₁ : i < s₁) :
    ∀ s, s₁ ≤ s → (preState s).requiresAttention s i = false := by
  intro s hs
  by_contra hreq
  rw [Bool.not_eq_false] at hreq
  obtain ⟨j, hji, hja⟩ := attended_le_of_requires (by omega) hreq
  exact hquiet s hs j hji hja

end FriedbergMuchnik
