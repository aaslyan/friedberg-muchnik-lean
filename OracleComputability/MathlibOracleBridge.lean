/-
# Bridge to Mathlib's oracle-computability model

This file is intentionally additive: it does not change the project-local
oracle semantics.  It relates them to Mathlib's semantic oracle model from
`Mathlib.Computability.TuringDegree`, where oracle computability is expressed
by `RecursiveIn`.
-/
import Mathlib.Computability.TuringDegree
import OracleComputability.Composition

namespace OracleComputability

/-- The total partial function used by Mathlib to represent a Boolean oracle:
on input `n`, return the project's numeric membership bit. -/
def mathlibOracle (X : ℕ → Bool) : ℕ →. ℕ :=
  fun n => Part.some (natOfBool (X n))

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
    LocallyRealizes X .zero (fun _ => Part.some 0) := by
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
    LocallyRealizes X .left (fun n => Part.some n.unpair.1) := by
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
    LocallyRealizes X .right (fun n => Part.some n.unpair.2) := by
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
    LocallyRealizes X (.pair cf cg) (fun n => Nat.pair <$> f n <*> g n) := by
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
    LocallyRealizes X (.comp cf cg) (fun n => g n >>= f) := by
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

end OracleComputability
