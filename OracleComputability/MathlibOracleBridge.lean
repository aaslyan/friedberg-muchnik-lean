import Mathlib.Computability.TuringDegree
import OracleComputability.Composition
import OracleComputability.MathlibBridge

/-!
# Bridge to Mathlib's oracle-computability model

This file is intentionally additive: it does not change the project-local
oracle semantics.  It relates them to Mathlib's semantic oracle model from
`Mathlib.Computability.TuringDegree`, where oracle computability is expressed
by `RecursiveIn`.
-/

namespace OracleComputability

open Nat.Partrec (Code)

/-- The total partial function used by Mathlib to represent a Boolean oracle:
on input `n`, return the project's numeric membership bit. -/
def mathlibOracle (X : ℕ → Bool) : ℕ →. ℕ :=
  fun n ↦ Part.some (natOfBool (X n))

/-- The Mathlib/semantic version of set Turing reducibility, specialized to
characteristic functions of sets of naturals. -/
def MathlibTuringReducible (A B : Set ℕ) : Prop :=
  RecursiveIn {mathlibOracle (charFun B)} (mathlibOracle (charFun A))

/-- A local oracle program realizes a Mathlib partial function relative to
the total Boolean oracle `X` when it computes exactly that partial function's
graph. -/
def LocallyRealizes (X : ℕ → Bool) (c : OracleCode) (f : ℕ →. ℕ) : Prop :=
  ∀ x y, Computes c X x y ↔ y ∈ f x

theorem realizes_zero (X : ℕ → Bool) :
    LocallyRealizes X .zero (fun _ ↦ Part.some 0) := by
  intro x y
  constructor
  · intro h
    have hy0 : y = 0 :=
      Computes.unique h ⟨x + 1, ⟨0, 0⟩, run_zero_step _ (by omega), rfl⟩
    subst hy0
    exact Part.mem_some 0
  · intro hy
    have hy0 : y = 0 := Part.mem_unique hy (Part.mem_some 0)
    subst hy0
    exact ⟨x + 1, ⟨0, 0⟩, run_zero_step _ (by omega), rfl⟩

theorem realizes_succ (X : ℕ → Bool) :
    LocallyRealizes X .succ Nat.succ := by
  intro x y
  constructor
  · intro h
    have hyx : y = x + 1 :=
      Computes.unique h ⟨x + 1, ⟨x + 1, 0⟩, run_succ_step _ (by omega), rfl⟩
    subst hyx
    exact Part.mem_some (x + 1)
  · intro hy
    have hyx : y = x + 1 := Part.mem_unique hy (Part.mem_some (x + 1))
    subst hyx
    exact ⟨x + 1, ⟨x + 1, 0⟩, run_succ_step _ (by omega), rfl⟩

theorem realizes_left (X : ℕ → Bool) :
    LocallyRealizes X .left (fun n ↦ Part.some n.unpair.1) := by
  intro x y
  constructor
  · intro h
    have hyx : y = x.unpair.1 :=
      Computes.unique h ⟨x + 1, ⟨x.unpair.1, 0⟩, run_left_step _ (by omega), rfl⟩
    subst hyx
    exact Part.mem_some x.unpair.1
  · intro hy
    have hyx : y = x.unpair.1 := Part.mem_unique hy (Part.mem_some x.unpair.1)
    subst hyx
    exact ⟨x + 1, ⟨x.unpair.1, 0⟩, run_left_step _ (by omega), rfl⟩

theorem realizes_right (X : ℕ → Bool) :
    LocallyRealizes X .right (fun n ↦ Part.some n.unpair.2) := by
  intro x y
  constructor
  · intro h
    have hyx : y = x.unpair.2 :=
      Computes.unique h ⟨x + 1, ⟨x.unpair.2, 0⟩, run_right_step _ (by omega), rfl⟩
    subst hyx
    exact Part.mem_some x.unpair.2
  · intro hy
    have hyx : y = x.unpair.2 := Part.mem_unique hy (Part.mem_some x.unpair.2)
    subst hyx
    exact ⟨x + 1, ⟨x.unpair.2, 0⟩, run_right_step _ (by omega), rfl⟩

theorem realizes_query (X : ℕ → Bool) :
    LocallyRealizes X .query (mathlibOracle X) := by
  intro x y
  constructor
  · intro h
    have hyx : y = natOfBool (X x) := Computes.unique h
      ⟨x + 1, ⟨natOfBool (X x), x + 1⟩,
        by exact run_query_some (by omega) rfl,
        rfl⟩
    subst hyx
    exact Part.mem_some (natOfBool (X x))
  · intro hy
    have hyx : y = natOfBool (X x) :=
      Part.mem_unique hy (Part.mem_some (natOfBool (X x)))
    subst hyx
    exact ⟨x + 1, ⟨natOfBool (X x), x + 1⟩,
      by exact run_query_some (by omega) rfl,
      rfl⟩


theorem realizes_pair {X : ℕ → Bool} {cf cg : OracleCode} {f g : ℕ →. ℕ}
    (hf : LocallyRealizes X cf f) (hg : LocallyRealizes X cg g) :
    LocallyRealizes X (.pair cf cg) (fun n ↦ Nat.pair <$> f n <*> g n) := by
  intro x y
  constructor
  · rintro ⟨k, d, hr, rfl⟩
    match k with
    | 0 => simp at hr
    | k' + 1 =>
      have hx : x ≤ k' := Nat.lt_succ_iff.mp (run_halt_input_lt hr)
      rw [run_pair_step _ _ _ hx] at hr
      obtain ⟨d₁, dr, hcf, hrest, rfl⟩ := RunResult.bind_eq_halt.mp hr
      obtain ⟨d₂, dp, hcg, hp, hdr⟩ := RunResult.bind_eq_halt.mp hrest
      have hdp : dp = ⟨Nat.pair d₁.output d₂.output, 0⟩ :=
        (RunResult.halt.inj hp).symm
      subst hdp
      have hfmem : d₁.output ∈ f x := (hf x d₁.output).mp ⟨k' + 1, d₁, hcf, rfl⟩
      have hgmem : d₂.output ∈ g x := (hg x d₂.output).mp ⟨k' + 1, d₂, hcg, rfl⟩
      rw [hdr]
      exact Part.mem_bind (Part.mem_map Nat.pair hfmem)
        (Part.mem_map (Nat.pair d₁.output) hgmem)
  · intro hy
    simp only [Seq.seq, Part.map_eq_map] at hy
    obtain ⟨fn, hfn, hyfn⟩ := Part.mem_bind_iff.mp hy
    obtain ⟨a, hfa, hfn_eq⟩ := (Part.mem_map_iff Nat.pair).mp hfn
    subst hfn_eq
    obtain ⟨b, hgb, hyab⟩ := (Part.mem_map_iff (Nat.pair a)).mp hyfn
    subst hyab
    obtain ⟨kf, df, hrf, houtf⟩ := (hf x a).mpr hfa
    obtain ⟨kg, dg, hrg, houtg⟩ := (hg x b).mpr hgb
    refine ⟨max (max kf kg) (x + 1) + 1,
      ⟨Nat.pair df.output dg.output, max df.use (max dg.use 0)⟩, ?_, ?_⟩
    · rw [run_pair_step _ _ _ (by omega : x ≤ max (max kf kg) (x + 1))]
      exact RunResult.bind_halt
        (d₂ := ⟨Nat.pair df.output dg.output, max dg.use 0⟩)
        (run_halt_fuel_mono (by omega) hrf)
        (RunResult.bind_halt
          (d₂ := ⟨Nat.pair df.output dg.output, 0⟩)
          (run_halt_fuel_mono (by omega) hrg) rfl)
    · rw [houtf, houtg]

theorem realizes_comp {X : ℕ → Bool} {cf cg : OracleCode} {f g : ℕ →. ℕ}
    (hf : LocallyRealizes X cf f) (hg : LocallyRealizes X cg g) :
    LocallyRealizes X (.comp cf cg) (fun n ↦ g n >>= f) := by
  intro x y
  constructor
  · rintro ⟨k, d, hr, rfl⟩
    match k with
    | 0 => simp at hr
    | k' + 1 =>
      have hx : x ≤ k' := Nat.lt_succ_iff.mp (run_halt_input_lt hr)
      rw [run_comp_step _ _ _ hx] at hr
      obtain ⟨d₁, d₂, hcg, hcf, rfl⟩ := RunResult.bind_eq_halt.mp hr
      have hgmem : d₁.output ∈ g x := (hg x d₁.output).mp ⟨k' + 1, d₁, hcg, rfl⟩
      have hfmem : d₂.output ∈ f d₁.output :=
        (hf d₁.output d₂.output).mp ⟨k' + 1, d₂, hcf, rfl⟩
      simp only [Part.bind_eq_bind, Part.mem_bind_iff]
      exact ⟨d₁.output, hgmem, hfmem⟩
  · intro hy
    simp only [Part.bind_eq_bind, Part.mem_bind_iff] at hy
    obtain ⟨z, hgz, hfz⟩ := hy
    obtain ⟨kg, dg, hrg, houtg⟩ := (hg x z).mpr hgz
    obtain ⟨kf, df, hrf, houtf⟩ := (hf z y).mpr hfz
    refine ⟨max (max kg kf) (x + 1) + 1, ⟨df.output, max dg.use df.use⟩, ?_, houtf⟩
    rw [run_comp_step _ _ _ (by omega : x ≤ max (max kg kf) (x + 1))]
    refine RunResult.bind_halt (run_halt_fuel_mono (by omega) hrg) ?_
    rw [houtg]
    exact run_halt_fuel_mono (by omega) hrf

/-! ### `Computes`-level step lemmas for `prec`

`Computes` hides the fuel behind an existential, so before any induction we
restate the two `run` step lemmas at the `Computes` level, discharging the
fuel bookkeeping once. -/

theorem computes_prec_zero {X : ℕ → Bool} {cf cg : OracleCode} {a y : ℕ} :
    Computes (.prec cf cg) X (Nat.pair a 0) y ↔ Computes cf X a y := by
  have hun1 : (Nat.pair a 0).unpair.1 = a := by rw [Nat.unpair_pair]
  have hun2 : (Nat.pair a 0).unpair.2 = 0 := by rw [Nat.unpair_pair]
  constructor
  · rintro ⟨k, d, hr, rfl⟩
    match k with
    | 0 => simp at hr
    | k + 1 =>
      have hx : Nat.pair a 0 ≤ k := Nat.lt_succ_iff.mp (run_halt_input_lt hr)
      rw [run_prec_zero_step _ cf cg hx hun2, hun1] at hr
      exact ⟨k + 1, d, hr, rfl⟩
  · rintro ⟨k, d, hr, rfl⟩
    refine ⟨max k (Nat.pair a 0) + 1, d, ?_, rfl⟩
    rw [run_prec_zero_step _ cf cg (by omega) hun2, hun1]
    exact run_halt_fuel_mono (by omega) hr

theorem computes_prec_succ {X : ℕ → Bool} {cf cg : OracleCode} {a n y : ℕ} :
    Computes (.prec cf cg) X (Nat.pair a (n + 1)) y ↔
      ∃ i, Computes (.prec cf cg) X (Nat.pair a n) i ∧
        Computes cg X (Nat.pair a (Nat.pair n i)) y := by
  have hun1 : (Nat.pair a (n + 1)).unpair.1 = a := by rw [Nat.unpair_pair]
  have hun2 : (Nat.pair a (n + 1)).unpair.2 = n + 1 := by rw [Nat.unpair_pair]
  constructor
  · rintro ⟨k, d, hr, rfl⟩
    match k with
    | 0 => simp at hr
    | k + 1 =>
      have hx : Nat.pair a (n + 1) ≤ k := Nat.lt_succ_iff.mp (run_halt_input_lt hr)
      rw [run_prec_succ_step _ cf cg hx hun2, hun1] at hr
      obtain ⟨d₁, d₂, hp, hg, rfl⟩ := RunResult.bind_eq_halt.mp hr
      exact ⟨d₁.output, ⟨k, d₁, hp, rfl⟩, ⟨k + 1, d₂, hg, rfl⟩⟩
  · rintro ⟨i, ⟨k₁, d₁, hp, rfl⟩, ⟨k₂, d₂, hg, rfl⟩⟩
    refine ⟨max (max k₁ k₂) (Nat.pair a (n + 1)) + 1,
      ⟨d₂.output, max d₁.use d₂.use⟩, ?_, rfl⟩
    rw [run_prec_succ_step _ cf cg (by omega) hun2, hun1]
    exact RunResult.bind_halt (run_halt_fuel_mono (by omega) hp)
      (run_halt_fuel_mono (by omega) hg)

/-! ### `prec`

The value `RecursiveIn.prec` asks for, as an explicit recursion. -/

def precPart (f g : ℕ →. ℕ) (a : ℕ) : ℕ → Part ℕ
  | 0 => f a
  | n + 1 => (precPart f g a n) >>= fun i ↦ g (Nat.pair a (Nat.pair n i))

theorem computes_prec_iff {X : ℕ → Bool} {cf cg : OracleCode} {f g : ℕ →. ℕ}
    (hf : LocallyRealizes X cf f) (hg : LocallyRealizes X cg g) :
    ∀ (n a y : ℕ), Computes (.prec cf cg) X (Nat.pair a n) y ↔ y ∈ precPart f g a n := by
  intro n
  induction n with
  | zero =>
    intro a y
    rw [computes_prec_zero, hf a y]
    rfl
  | succ n ih =>
    intro a y
    rw [computes_prec_succ]
    show (∃ i, Computes (.prec cf cg) X (Nat.pair a n) i ∧
      Computes cg X (Nat.pair a (Nat.pair n i)) y) ↔
      y ∈ (precPart f g a n) >>= fun i ↦ g (Nat.pair a (Nat.pair n i))
    simp only [Part.bind_eq_bind, Part.mem_bind_iff]
    constructor
    · rintro ⟨i, hi, hy⟩
      exact ⟨i, (ih a i).mp hi, (hg _ y).mp hy⟩
    · rintro ⟨i, hi, hy⟩
      exact ⟨i, (ih a i).mpr hi, (hg _ y).mpr hy⟩

theorem precPart_eq (f g : ℕ →. ℕ) (a n : ℕ) :
    precPart f g a n =
      n.rec (f a) (fun y IH ↦ IH >>= fun i ↦ g (Nat.pair a (Nat.pair y i))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show precPart f g a n >>= _ = _
    rw [ih]

/-- Realization for `RecursiveIn.prec`. -/
theorem realizes_prec {X : ℕ → Bool} {cf cg : OracleCode} {f g : ℕ →. ℕ}
    (hf : LocallyRealizes X cf f) (hg : LocallyRealizes X cg g) :
    LocallyRealizes X (.prec cf cg)
      (fun p ↦
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH ↦ do
          let i ← IH
          g (Nat.pair a (Nat.pair y i))) := by
  intro x y
  have h := computes_prec_iff hf hg x.unpair.2 x.unpair.1 y
  rw [Nat.pair_unpair, precPart_eq] at h
  exact h

/-! ### `Computes`-level step lemmas for `rfind`

Our `rfind` is the *primed* form: at input `Nat.pair a m` it searches
upward from `m`.  Mathlib's `RecursiveIn.rfind` is the unprimed form,
searching from `0`.  These two lemmas isolate one step of the primed
search, fuel discharged. -/

theorem computes_rfind_found {X : ℕ → Bool} {cf : OracleCode} {a m : ℕ}
    (h : Computes cf X (Nat.pair a m) 0) :
    Computes (.rfind cf) X (Nat.pair a m) m := by
  have hun2 : (Nat.pair a m).unpair.2 = m := by rw [Nat.unpair_pair]
  obtain ⟨k, d, hr, hout⟩ := h
  have hr' : run (max k (Nat.pair a m) + 1) (PartOracle.ofFun X) cf (Nat.pair a m)
      = .halt d := run_halt_fuel_mono (by omega) hr
  refine ⟨max k (Nat.pair a m) + 1, ⟨m, max d.use 0⟩, ?_, rfl⟩
  rw [run_rfind_step _ cf (by omega)]
  refine RunResult.bind_halt (d₂ := ⟨m, 0⟩) hr' ?_
  show (if d.output = 0 then RunResult.halt ⟨(Nat.pair a m).unpair.2, 0⟩
    else run (max k (Nat.pair a m)) (PartOracle.ofFun X) (.rfind cf)
      (Nat.pair (Nat.pair a m).unpair.1 ((Nat.pair a m).unpair.2 + 1))) = _
  rw [if_pos hout, hun2]

theorem computes_rfind_step {X : ℕ → Bool} {cf : OracleCode} {a m v y : ℕ}
    (hv : Computes cf X (Nat.pair a m) v) (hv0 : v ≠ 0)
    (h : Computes (.rfind cf) X (Nat.pair a (m + 1)) y) :
    Computes (.rfind cf) X (Nat.pair a m) y := by
  have hun1 : (Nat.pair a m).unpair.1 = a := by rw [Nat.unpair_pair]
  have hun2 : (Nat.pair a m).unpair.2 = m := by rw [Nat.unpair_pair]
  obtain ⟨k₁, d₁, hr₁, hout₁⟩ := hv
  obtain ⟨k₂, d₂, hr₂, hout₂⟩ := h
  have hr₁' : run (max (max k₁ k₂) (Nat.pair a m) + 1) (PartOracle.ofFun X) cf
      (Nat.pair a m) = .halt d₁ := run_halt_fuel_mono (by omega) hr₁
  refine ⟨max (max k₁ k₂) (Nat.pair a m) + 1, ⟨d₂.output, max d₁.use d₂.use⟩, ?_, hout₂⟩
  rw [run_rfind_step _ cf (by omega)]
  refine RunResult.bind_halt (d₂ := d₂) hr₁' ?_
  show (if d₁.output = 0 then RunResult.halt ⟨(Nat.pair a m).unpair.2, 0⟩
    else run (max (max k₁ k₂) (Nat.pair a m)) (PartOracle.ofFun X) (.rfind cf)
      (Nat.pair (Nat.pair a m).unpair.1 ((Nat.pair a m).unpair.2 + 1))) = _
  rw [if_neg (by rw [hout₁]; exact hv0), hun1, hun2]
  exact run_halt_fuel_mono (by omega) hr₂

/-! ### The primed search, characterized without `Nat.rfind` -/

theorem rfind_forward {X : ℕ → Bool} {cf : OracleCode} {f : ℕ →. ℕ}
    (hf : LocallyRealizes X cf f) :
    ∀ (k a m : ℕ) (d : HaltData),
      run k (PartOracle.ofFun X) (.rfind cf) (Nat.pair a m) = .halt d →
      m ≤ d.output ∧ 0 ∈ f (Nat.pair a d.output) ∧
        ∀ j, m ≤ j → j < d.output → ∃ v, v ∈ f (Nat.pair a j) ∧ v ≠ 0 := by
  intro k
  induction k with
  | zero => intro a m d hr; simp at hr
  | succ k ih =>
    intro a m d hr
    have hx : Nat.pair a m ≤ k := Nat.lt_succ_iff.mp (run_halt_input_lt hr)
    have hun1 : (Nat.pair a m).unpair.1 = a := by rw [Nat.unpair_pair]
    have hun2 : (Nat.pair a m).unpair.2 = m := by rw [Nat.unpair_pair]
    rw [run_rfind_step _ cf hx] at hr
    obtain ⟨d₁, d₂, hcf, hcont, rfl⟩ := RunResult.bind_eq_halt.mp hr
    show m ≤ d₂.output ∧ 0 ∈ f (Nat.pair a d₂.output) ∧
      ∀ j, m ≤ j → j < d₂.output → ∃ v, v ∈ f (Nat.pair a j) ∧ v ≠ 0
    have hv : d₁.output ∈ f (Nat.pair a m) :=
      (hf (Nat.pair a m) d₁.output).mp ⟨k + 1, d₁, hcf, rfl⟩
    by_cases h0 : d₁.output = 0
    · rw [if_pos h0, hun2] at hcont
      have hout : d₂.output = m := by rw [← RunResult.halt.inj hcont]
      rw [hout]
      refine ⟨le_rfl, ?_, fun j h1 h2 ↦ absurd h2 (by omega)⟩
      rw [h0] at hv
      exact hv
    · rw [if_neg h0, hun1, hun2] at hcont
      obtain ⟨hle, hz, hj⟩ := ih a (m + 1) d₂ hcont
      refine ⟨by omega, hz, fun j h1 h2 ↦ ?_⟩
      rcases Nat.lt_or_ge j (m + 1) with hjm | hjm
      · have hjeq : j = m := by omega
        subst hjeq
        exact ⟨d₁.output, hv, h0⟩
      · exact hj j hjm h2

theorem rfind_backward {X : ℕ → Bool} {cf : OracleCode} {f : ℕ →. ℕ}
    (hf : LocallyRealizes X cf f) :
    ∀ (t a m : ℕ), 0 ∈ f (Nat.pair a (m + t)) →
      (∀ j, m ≤ j → j < m + t → ∃ v, v ∈ f (Nat.pair a j) ∧ v ≠ 0) →
      Computes (.rfind cf) X (Nat.pair a m) (m + t) := by
  intro t
  induction t with
  | zero =>
    intro a m hz _
    have h0 : Computes cf X (Nat.pair a m) 0 := (hf _ 0).mpr (by simpa using hz)
    simpa using computes_rfind_found h0
  | succ t ih =>
    intro a m hz hj
    obtain ⟨v, hv, hv0⟩ := hj m le_rfl (by omega)
    have hrec : Computes (.rfind cf) X (Nat.pair a (m + 1)) (m + 1 + t) :=
      ih a (m + 1) (by rw [show m + 1 + t = m + (t + 1) by omega]; exact hz)
        (fun j h1 h2 ↦ hj j (by omega) (by omega))
    rw [show m + (t + 1) = m + 1 + t by omega]
    exact computes_rfind_step ((hf _ v).mpr hv) hv0 hrec

/-! ### From the unfolded characterization to `Nat.rfind` -/

theorem mem_map_true {f : ℕ →. ℕ} {w : ℕ} :
    true ∈ ((fun m ↦ decide (m = 0)) <$> f w : Part Bool) ↔ 0 ∈ f w := by
  show true ∈ Part.map (fun m ↦ decide (m = 0)) (f w) ↔ 0 ∈ f w
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨v, hv, hd⟩
    have hv0 : v = 0 := by simpa using hd
    exact hv0 ▸ hv
  · intro h
    exact ⟨0, h, by simp⟩

theorem mem_map_false {f : ℕ →. ℕ} {w : ℕ} :
    false ∈ ((fun m ↦ decide (m = 0)) <$> f w : Part Bool) ↔ ∃ v, v ∈ f w ∧ v ≠ 0 := by
  show false ∈ Part.map (fun m ↦ decide (m = 0)) (f w) ↔ _
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨v, hv, hd⟩
    exact ⟨v, hv, by simpa using hd⟩
  · rintro ⟨v, hv, hv0⟩
    exact ⟨v, hv, by simpa using hv0⟩

/-- The partial function our *primed* `rfind` computes: search upward from
the second component of the input, and report the absolute index found. -/
def rfindPrimed (f : ℕ →. ℕ) : ℕ →. ℕ := fun x ↦
  (Nat.rfind fun n ↦ (fun m ↦ m = 0) <$> f (Nat.pair x.unpair.1 (x.unpair.2 + n))).map
    (fun n ↦ n + x.unpair.2)

theorem realizes_rfind_primed {X : ℕ → Bool} {cf : OracleCode} {f : ℕ →. ℕ}
    (hf : LocallyRealizes X cf f) :
    LocallyRealizes X (.rfind cf) (rfindPrimed f) := by
  intro x y
  have hx : Nat.pair x.unpair.1 x.unpair.2 = x := Nat.pair_unpair x
  constructor
  · rintro ⟨k, d, hr, rfl⟩
    rw [← hx] at hr
    obtain ⟨hle, hz, hj⟩ := rfind_forward hf k x.unpair.1 x.unpair.2 d hr
    refine (Part.mem_map_iff _).mpr ⟨d.output - x.unpair.2, ?_, by omega⟩
    refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · refine mem_map_true.mpr ?_
      rw [show x.unpair.2 + (d.output - x.unpair.2) = d.output by omega]
      exact hz
    · intro j hjlt
      exact mem_map_false.mpr (hj (x.unpair.2 + j) (by omega) (by omega))
  · intro hy
    obtain ⟨n, hn, hyn⟩ := (Part.mem_map_iff _).mp hy
    obtain ⟨htrue, hfalse⟩ := Nat.mem_rfind.mp hn
    have hcomp : Computes (.rfind cf) X (Nat.pair x.unpair.1 x.unpair.2) (x.unpair.2 + n) := by
      refine rfind_backward hf n x.unpair.1 x.unpair.2 (mem_map_true.mp htrue) ?_
      intro j h1 h2
      have hfj := hfalse (m := j - x.unpair.2) (by omega)
      rw [show x.unpair.2 + (j - x.unpair.2) = j by omega] at hfj
      exact mem_map_false.mp hfj
    rw [hx, show x.unpair.2 + n = y by omega] at hcomp
    exact hcomp

/-! ### Codes for oracle-free plumbing, via the existing Mathlib bridge -/

theorem locallyRealizes_embed (X : ℕ → Bool) (cf : Code) :
    LocallyRealizes X (embed cf) (Code.eval cf) := by
  intro x y
  constructor
  · rintro ⟨k, d, hr, rfl⟩
    rw [run_embed] at hr
    cases hev : Code.evaln k cf x with
    | none => rw [hev] at hr; exact absurd hr (by simp)
    | some z =>
      rw [hev] at hr
      have hd : (⟨z, 0⟩ : HaltData) = d := RunResult.halt.inj hr
      subst hd
      exact Code.evaln_complete.mpr ⟨k, Option.mem_def.mpr hev⟩
  · intro hy
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hy
    exact ⟨k, ⟨y, 0⟩, by rw [run_embed, Option.mem_def.mp hk]; rfl, rfl⟩

theorem exists_locallyRealizes_of_partrec {f : ℕ →. ℕ} (hf : Nat.Partrec f)
    (X : ℕ → Bool) : ∃ c, LocallyRealizes X c f := by
  obtain ⟨cf, rfl⟩ := Code.exists_code.mp hf
  exact ⟨embed cf, locallyRealizes_embed X cf⟩

theorem exists_pairZero_code (X : ℕ → Bool) :
    ∃ c, LocallyRealizes X c (fun a ↦ Part.some (Nat.pair a 0)) := by
  refine exists_locallyRealizes_of_partrec ?_ X
  have hc : Computable fun a : ℕ ↦ Nat.pair a 0 :=
    Primrec.to_comp (Primrec₂.natPair.comp Primrec.id (Primrec.const 0))
  exact Partrec.nat_iff.mp hc.partrec

/-! ### `rfind`: primed search plus an input adapter -/

theorem exists_realizes_rfind {X : ℕ → Bool} {cf : OracleCode} {f : ℕ →. ℕ}
    (hf : LocallyRealizes X cf f) :
    ∃ c, LocallyRealizes X c
      (fun a ↦ Nat.rfind fun n ↦ (fun m ↦ m = 0) <$> f (Nat.pair a n)) := by
  obtain ⟨c0, hc0⟩ := exists_pairZero_code X
  refine ⟨.comp (.rfind cf) c0, ?_⟩
  have h := realizes_comp (realizes_rfind_primed hf) hc0
  have hfun : (fun a ↦ (Part.some (Nat.pair a 0)) >>= rfindPrimed f)
      = (fun a ↦ Nat.rfind fun n ↦ (fun m ↦ m = 0) <$> f (Nat.pair a n)) := by
    funext a
    simp only [Part.bind_eq_bind, Part.bind_some]
    unfold rfindPrimed
    simp only [Nat.unpair_pair, Nat.zero_add, Nat.add_zero]
    exact Part.map_id' (fun _ ↦ rfl) _
  rw [hfun] at h
  exact h

/-! ### The induction, and the transfer theorem -/

theorem exists_code_of_recursiveIn {X : ℕ → Bool} {f : ℕ →. ℕ}
    (h : RecursiveIn {mathlibOracle X} f) : ∃ c, LocallyRealizes X c f := by
  induction h with
  | zero => exact ⟨.zero, realizes_zero X⟩
  | succ => exact ⟨.succ, realizes_succ X⟩
  | left => exact ⟨.left, realizes_left X⟩
  | right => exact ⟨.right, realizes_right X⟩
  | oracle g hg =>
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact ⟨.query, realizes_query X⟩
  | pair _ _ ih₁ ih₂ =>
    obtain ⟨c₁, h₁⟩ := ih₁
    obtain ⟨c₂, h₂⟩ := ih₂
    exact ⟨.pair c₁ c₂, realizes_pair h₁ h₂⟩
  | comp _ _ ih₁ ih₂ =>
    obtain ⟨c₁, h₁⟩ := ih₁
    obtain ⟨c₂, h₂⟩ := ih₂
    exact ⟨.comp c₁ c₂, realizes_comp h₁ h₂⟩
  | prec _ _ ih₁ ih₂ =>
    obtain ⟨c₁, h₁⟩ := ih₁
    obtain ⟨c₂, h₂⟩ := ih₂
    exact ⟨.prec c₁ c₂, realizes_prec h₁ h₂⟩
  | rfind _ ih =>
    obtain ⟨c, hc⟩ := ih
    exact exists_realizes_rfind hc

/-- **The transfer theorem.**  Every reduction in Mathlib's `RecursiveIn`
model is captured by an `OracleCode`, so the project-local `≤ᵀ` is not too
weak: the negative results transfer to the standard notion. -/
theorem turingReducible_of_mathlib {A B : Set ℕ} (h : MathlibTuringReducible A B) :
    TuringReducible A B := by
  obtain ⟨c, hc⟩ := exists_code_of_recursiveIn h
  exact ⟨c, fun x ↦ (hc x (natOfBool (charFun A x))).mpr (Part.mem_some _)⟩

/-- Contrapositive: a local non-reducibility is a genuine one. -/
theorem not_mathlibTuringReducible {A B : Set ℕ} (h : ¬ TuringReducible A B) :
    ¬ MathlibTuringReducible A B := fun hm ↦ h (turingReducible_of_mathlib hm)

end OracleComputability
