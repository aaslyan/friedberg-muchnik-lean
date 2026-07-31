/-
# Closure of `≤ᵀ` under composition: transitivity

The reducibility-hygiene result that makes the project's `≤ᵀ`
recognizably *standard* Turing reducibility: it is transitive (with
reflexivity from `Reducibility.lean`, a preorder).

The mechanism is the classical one.  Given a reduction `c₁` computing
`χ_A` from an oracle for `B`, and a reduction `c₂` computing `χ_B` from
an oracle for `C`, substitute `c₂` for every `query` node of `c₁`
(`subst`).  The output convention lines up exactly: a `query` at `n`
returns `natOfBool (χ_B n)`, which is precisely what `c₂` outputs at `n`
— so the substituted program, run against `C`, simulates `c₁` run
against `B`, step for step, with the same outputs (`subst_run_aux`).
Fuel is re-budgeted at every node (the simulated sub-computations each
need their own fuel), which is why the simulation produces *some* fuel
bound rather than preserving the original one; outputs — the only thing
`Computes` cares about — are preserved on the nose.
-/
import OracleComputability.Reducibility

namespace OracleComputability

/-- Substitute the program `q` for every `query` node of a code:
relativized composition at the syntax level. -/
def subst (q : OracleCode) : OracleCode → OracleCode
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .query => q
  | .pair f g => .pair (subst q f) (subst q g)
  | .comp f g => .comp (subst q f) (subst q g)
  | .prec f g => .prec (subst q f) (subst q g)
  | .rfind f => .rfind (subst q f)

/-- **Substitution simulation.**  If `q`, run against the total oracle
`Y`, computes the membership bit `natOfBool (X n)` on every input `n`,
then every halting run of `c` against `X` is simulated by a halting run
of `subst q c` against `Y` with the same output (for some fuel).  The
recursion mirrors the fuel/code recursion of `run` itself. -/
private theorem subst_run_aux (X Y : ℕ → Bool) (q : OracleCode)
    (hq : ∀ n : ℕ, ∃ kq dq,
      run kq (PartOracle.ofFun Y) q n = .halt dq ∧
        dq.output = natOfBool (X n)) :
    ∀ (k : ℕ) (c : OracleCode) (x : ℕ) (d : HaltData),
      run k (PartOracle.ofFun X) c x = .halt d →
      ∃ k' d', run k' (PartOracle.ofFun Y) (subst q c) x = .halt d' ∧
        d'.output = d.output
  | 0, _, _, _, h => by simp at h
  | k + 1, .zero, x, d, h => by
    have hx : x ≤ k := Nat.lt_succ_iff.mp (run_halt_input_lt h)
    rw [run_zero_step _ hx] at h
    exact ⟨k + 1, d, by
      rw [show subst q .zero = .zero from rfl, run_zero_step _ hx]
      exact h, rfl⟩
  | k + 1, .succ, x, d, h => by
    have hx : x ≤ k := Nat.lt_succ_iff.mp (run_halt_input_lt h)
    rw [run_succ_step _ hx] at h
    exact ⟨k + 1, d, by
      rw [show subst q .succ = .succ from rfl, run_succ_step _ hx]
      exact h, rfl⟩
  | k + 1, .left, x, d, h => by
    have hx : x ≤ k := Nat.lt_succ_iff.mp (run_halt_input_lt h)
    rw [run_left_step _ hx] at h
    exact ⟨k + 1, d, by
      rw [show subst q .left = .left from rfl, run_left_step _ hx]
      exact h, rfl⟩
  | k + 1, .right, x, d, h => by
    have hx : x ≤ k := Nat.lt_succ_iff.mp (run_halt_input_lt h)
    rw [run_right_step _ hx] at h
    exact ⟨k + 1, d, by
      rw [show subst q .right = .right from rfl, run_right_step _ hx]
      exact h, rfl⟩
  | k + 1, .query, x, d, h => by
    have hx : x ≤ k := Nat.lt_succ_iff.mp (run_halt_input_lt h)
    rw [run_query_some hx (PartOracle.ofFun_apply X x)] at h
    have hd : d = ⟨cond (X x) 1 0, x + 1⟩ := (RunResult.halt.inj h).symm
    obtain ⟨kq, dq, hrun, hout⟩ := hq x
    refine ⟨kq, dq, by rw [show subst q .query = q from rfl]; exact hrun, ?_⟩
    rw [hout, hd]
    rfl
  | k + 1, .pair f g, x, d, h => by
    have hx : x ≤ k := Nat.lt_succ_iff.mp (run_halt_input_lt h)
    rw [run_pair_step _ _ _ hx] at h
    obtain ⟨d₁, dr, hf, hrest, rfl⟩ := RunResult.bind_eq_halt.mp h
    obtain ⟨d₂, dp, hg, hp, hdr⟩ := RunResult.bind_eq_halt.mp hrest
    have hdp : dp = ⟨Nat.pair d₁.output d₂.output, 0⟩ :=
      (RunResult.halt.inj hp).symm
    subst hdp
    obtain ⟨k₁, d₁', h₁, ho₁⟩ := subst_run_aux X Y q hq (k + 1) f x d₁ hf
    obtain ⟨k₂, d₂', h₂, ho₂⟩ := subst_run_aux X Y q hq (k + 1) g x d₂ hg
    refine ⟨max (max k₁ k₂) (x + 1) + 1,
      ⟨Nat.pair d₁'.output d₂'.output, max d₁'.use (max d₂'.use 0)⟩, ?_, ?_⟩
    · rw [show subst q (.pair f g) = .pair (subst q f) (subst q g) from rfl,
        run_pair_step _ _ _ (by omega : x ≤ max (max k₁ k₂) (x + 1))]
      exact RunResult.bind_halt
        (d₂ := ⟨Nat.pair d₁'.output d₂'.output, max d₂'.use 0⟩)
        (run_halt_fuel_mono (by omega) h₁)
        (RunResult.bind_halt
          (d₂ := ⟨Nat.pair d₁'.output d₂'.output, 0⟩)
          (run_halt_fuel_mono (by omega) h₂) rfl)
    · show Nat.pair d₁'.output d₂'.output = dr.output
      rw [ho₁, ho₂, hdr]
  | k + 1, .comp f g, x, d, h => by
    have hx : x ≤ k := Nat.lt_succ_iff.mp (run_halt_input_lt h)
    rw [run_comp_step _ _ _ hx] at h
    obtain ⟨d₁, d₂, hg, hf, rfl⟩ := RunResult.bind_eq_halt.mp h
    obtain ⟨k₁, d₁', h₁, ho₁⟩ := subst_run_aux X Y q hq (k + 1) g x d₁ hg
    obtain ⟨k₂, d₂', h₂, ho₂⟩ :=
      subst_run_aux X Y q hq (k + 1) f d₁.output d₂ hf
    refine ⟨max (max k₁ k₂) (x + 1) + 1,
      ⟨d₂'.output, max d₁'.use d₂'.use⟩, ?_, ho₂⟩
    rw [show subst q (.comp f g) = .comp (subst q f) (subst q g) from rfl,
      run_comp_step _ _ _ (by omega : x ≤ max (max k₁ k₂) (x + 1))]
    refine RunResult.bind_halt (run_halt_fuel_mono (by omega) h₁) ?_
    rw [ho₁]
    exact run_halt_fuel_mono (by omega) h₂
  | k + 1, .prec f g, x, d, h => by
    have hx : x ≤ k := Nat.lt_succ_iff.mp (run_halt_input_lt h)
    cases hx2 : x.unpair.2 with
    | zero =>
      rw [run_prec_zero_step _ _ _ hx hx2] at h
      obtain ⟨k₁, d₁', h₁, ho₁⟩ :=
        subst_run_aux X Y q hq (k + 1) f x.unpair.1 d h
      refine ⟨max k₁ (x + 1) + 1, d₁', ?_, ho₁⟩
      rw [show subst q (.prec f g) = .prec (subst q f) (subst q g) from rfl,
        run_prec_zero_step _ _ _ (by omega : x ≤ max k₁ (x + 1)) hx2]
      exact run_halt_fuel_mono (by omega) h₁
    | succ n =>
      rw [run_prec_succ_step _ _ _ hx hx2] at h
      obtain ⟨d₁, d₂, hp, hg2, rfl⟩ := RunResult.bind_eq_halt.mp h
      obtain ⟨k₁, d₁', h₁, ho₁⟩ := subst_run_aux X Y q hq k (.prec f g)
        (Nat.pair x.unpair.1 n) d₁ hp
      obtain ⟨k₂, d₂', h₂, ho₂⟩ := subst_run_aux X Y q hq (k + 1) g
        (Nat.pair x.unpair.1 (Nat.pair n d₁.output)) d₂ hg2
      refine ⟨max (max k₁ k₂) (x + 1) + 1,
        ⟨d₂'.output, max d₁'.use d₂'.use⟩, ?_, ho₂⟩
      rw [show subst q (.prec f g) = .prec (subst q f) (subst q g) from rfl,
        run_prec_succ_step _ _ _ (by omega : x ≤ max (max k₁ k₂) (x + 1)) hx2]
      refine RunResult.bind_halt (run_halt_fuel_mono (by omega) h₁) ?_
      rw [ho₁]
      exact run_halt_fuel_mono (by omega) h₂
  | k + 1, .rfind f, x, d, h => by
    have hx : x ≤ k := Nat.lt_succ_iff.mp (run_halt_input_lt h)
    rw [run_rfind_step _ _ hx] at h
    obtain ⟨d₁, d₂, hf, hcont, rfl⟩ := RunResult.bind_eq_halt.mp h
    obtain ⟨k₁, d₁', h₁, ho₁⟩ := subst_run_aux X Y q hq (k + 1) f x d₁ hf
    have hcont₀ :
        (if d₁.output = 0 then RunResult.halt ⟨x.unpair.2, 0⟩
          else run k (PartOracle.ofFun X) (.rfind f)
            (Nat.pair x.unpair.1 (x.unpair.2 + 1))) = .halt d₂ := hcont
    by_cases hy : d₁.output = 0
    · rw [if_pos hy] at hcont₀
      refine ⟨max k₁ (x + 1) + 1, ⟨d₂.output, max d₁'.use d₂.use⟩, ?_, rfl⟩
      rw [show subst q (.rfind f) = .rfind (subst q f) from rfl,
        run_rfind_step _ _ (by omega : x ≤ max k₁ (x + 1))]
      refine RunResult.bind_halt (run_halt_fuel_mono (by omega) h₁) ?_
      show (if d₁'.output = 0 then RunResult.halt ⟨x.unpair.2, 0⟩
        else run (max k₁ (x + 1)) (PartOracle.ofFun Y) (.rfind (subst q f))
          (Nat.pair x.unpair.1 (x.unpair.2 + 1))) = _
      rw [ho₁, if_pos hy]
      exact hcont₀
    · rw [if_neg hy] at hcont₀
      obtain ⟨k₂, d₂', h₂, ho₂⟩ := subst_run_aux X Y q hq k (.rfind f)
        (Nat.pair x.unpair.1 (x.unpair.2 + 1)) d₂ hcont₀
      refine ⟨max (max k₁ k₂) (x + 1) + 1,
        ⟨d₂'.output, max d₁'.use d₂'.use⟩, ?_, ho₂⟩
      rw [show subst q (.rfind f) = .rfind (subst q f) from rfl,
        run_rfind_step _ _ (by omega : x ≤ max (max k₁ k₂) (x + 1))]
      refine RunResult.bind_halt (run_halt_fuel_mono (by omega) h₁) ?_
      show (if d₁'.output = 0 then RunResult.halt ⟨x.unpair.2, 0⟩
        else run (max (max k₁ k₂) (x + 1)) (PartOracle.ofFun Y)
          (.rfind (subst q f))
          (Nat.pair x.unpair.1 (x.unpair.2 + 1))) = _
      rw [ho₁, if_neg hy]
      exact run_halt_fuel_mono (by omega) h₂
  termination_by k c _ _ _ => (k, sizeOf c)

/-- **Transitivity of Turing reducibility** (closure of the reduction
relation under composition, Soare III.1): substitute the `B`-from-`C`
decider for every oracle query of the `A`-from-`B` decider. -/
theorem TuringReducible.trans {A B C : Set ℕ}
    (hab : TuringReducible A B) (hbc : TuringReducible B C) :
    TuringReducible A C := by
  obtain ⟨c₁, h₁⟩ := hab
  obtain ⟨c₂, h₂⟩ := hbc
  refine ⟨subst c₂ c₁, fun x => ?_⟩
  obtain ⟨k, d, hk, hout⟩ := h₁ x
  obtain ⟨k', d', h', hout'⟩ :=
    subst_run_aux (charFun B) (charFun C) c₂
      (fun n => h₂ n) k c₁ x d hk
  exact ⟨k', d', h', by rw [hout', hout]⟩

/-- With `TuringReducible.refl`, the project's `≤ᵀ` is a preorder. -/
instance : Trans TuringReducible TuringReducible TuringReducible :=
  ⟨TuringReducible.trans⟩

end OracleComputability
