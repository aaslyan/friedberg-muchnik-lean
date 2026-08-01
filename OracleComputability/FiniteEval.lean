import Mathlib.Data.Nat.Pairing
import OracleComputability.OracleCode

/-!
# Step-indexed evaluation with finite oracle information

This file gives `OracleCode` its operational semantics: a fuel-bounded
evaluator `run` that consults a *partial* oracle `ℕ → Option Bool` and
returns one of three explicitly distinguished outcomes:

* `halt ⟨output, use⟩` — the computation converged, produced `output`, and
  every oracle position it queried is `< use` (`use` is a strict upper bound
  on the queried positions; `use = 0` means no query was made);
* `stuck` — the computation reached an oracle query the oracle could not
  answer ("insufficient oracle information", *not* divergence);
* `timeout` — the fuel ran out.

Recording the `use` in the result is what makes the use principle
(`Use.lean`) a statement about data the construction can actually inspect:
a priority requirement freezes a converging computation by restraining the
oracle set below the recorded `use`.

The fuel discipline (the `x ≤ k` guard, and fuel decreasing exactly at the
recursive calls of `prec` and `rfind`) deliberately mirrors Mathlib's
`Nat.Partrec.Code.evaln`, so that `MathlibBridge.lean` can relate the two
semantics by a single structural induction.
-/

namespace OracleComputability

/-- The data recorded by a halting bounded computation: the `output`, and a
strict upper bound `use` on the oracle positions that were queried.  A
computation with `use = u` depends on the oracle only through positions
`< u`; that is the content of the master lemma `run_halt_mono` in
`Use.lean`. -/
structure HaltData where
  output : ℕ
  use : ℕ
  deriving DecidableEq, Repr

/-- Outcome of running an oracle program with bounded fuel and (possibly)
bounded oracle information. -/
inductive RunResult where
  /-- Converged, with recorded output and use. -/
  | halt (d : HaltData)
  /-- Reached an oracle query at a position the oracle does not answer.
  More *oracle information* may turn this into `halt`; more fuel alone
  cannot. -/
  | stuck
  /-- Ran out of fuel.  More fuel may turn this into `halt` or `stuck`. -/
  | timeout
  deriving DecidableEq, Repr

/-- A partial oracle: an answer (`some b`) or absence of information
(`none`) for each membership question.  Total oracles and finite snapshot
strings are both coerced into this one type, so every lemma about `run` is
stated only once. -/
abbrev PartOracle : Type := ℕ → Option Bool

namespace PartOracle

/-- The everywhere-defined oracle of a total membership function. -/
def ofFun (X : ℕ → Bool) : PartOracle := fun n ↦ some (X n)

/-- The finite oracle described by a snapshot string: position `i` is
answered by `σ[i]` when `i < σ.length` and is unanswered otherwise. -/
def ofSnapshot (σ : List Bool) : PartOracle := fun n ↦ σ[n]?

/-- The empty oracle: no information at all.  Used to define *unrelativized*
computation (`CE`, `ComputableSet` in `Reducibility.lean`). -/
def empty : PartOracle := fun _ ↦ none

@[simp] theorem ofFun_apply (X : ℕ → Bool) (n : ℕ) : ofFun X n = some (X n) := rfl

@[simp] theorem ofSnapshot_apply (σ : List Bool) (n : ℕ) : ofSnapshot σ n = σ[n]? := rfl

@[simp] theorem empty_apply (n : ℕ) : empty n = none := rfl

end PartOracle

namespace RunResult

/-- Sequencing of bounded runs.  If `r` halted, feed its output to the
continuation `f`, and record the larger of the two uses; otherwise propagate
the failure of `r` unchanged. -/
def bind (r : RunResult) (f : ℕ → RunResult) : RunResult :=
  match r with
  | .halt d =>
    match f d.output with
    | .halt d' => .halt ⟨d'.output, max d.use d'.use⟩
    | r' => r'
  | .stuck => .stuck
  | .timeout => .timeout

@[simp] theorem stuck_bind (f : ℕ → RunResult) : bind .stuck f = .stuck := rfl

@[simp] theorem timeout_bind (f : ℕ → RunResult) : bind .timeout f = .timeout := rfl

/-- Inversion principle for `bind`: a sequenced run halts exactly if both
components halt, and the recorded use is the larger of the two. -/
theorem bind_eq_halt {r : RunResult} {f : ℕ → RunResult} {d : HaltData} :
    bind r f = .halt d ↔
      ∃ d₁ d₂, r = .halt d₁ ∧ f d₁.output = .halt d₂ ∧
        d = ⟨d₂.output, max d₁.use d₂.use⟩ := by
  constructor
  · intro h
    cases r with
    | halt d₁ =>
      cases hf : f d₁.output with
      | halt d₂ =>
        refine ⟨d₁, d₂, rfl, hf, ?_⟩
        simpa [bind, hf] using h.symm
      | stuck => simp [bind, hf] at h
      | timeout => simp [bind, hf] at h
    | stuck => simp [bind] at h
    | timeout => simp [bind] at h
  · rintro ⟨d₁, d₂, rfl, hf, rfl⟩
    simp [bind, hf]

/-- Forward direction of `bind_eq_halt`, convenient for rebuilding runs. -/
theorem bind_halt {r : RunResult} {f : ℕ → RunResult} {d₁ d₂ : HaltData}
    (hr : r = .halt d₁) (hf : f d₁.output = .halt d₂) :
    bind r f = .halt ⟨d₂.output, max d₁.use d₂.use⟩ := by
  subst hr; simp [bind, hf]

end RunResult

/-- Fuel-bounded evaluation of an oracle program against a partial oracle.

`run k O c x` runs program `c` on input `x` for at most `k` "steps" and
answers oracle queries with `O`.  The guard `x ≤ k` (for fuel `k + 1`) and
the placement of the fuel decrements copy Mathlib's
`Nat.Partrec.Code.evaln` exactly; see the file docstring.

Everything here is a total function on finite data: for a snapshot oracle
`PartOracle.ofSnapshot σ` the value of `run` is computed from `k`, `σ`, `c`,
`x` alone, with no quantification over infinite objects. -/
def run : ℕ → PartOracle → OracleCode → ℕ → RunResult
  | 0, _, _, _ => .timeout
  | k + 1, O, c, x =>
    if x ≤ k then
      match c with
      | .zero => .halt ⟨0, 0⟩
      | .succ => .halt ⟨x + 1, 0⟩
      | .left => .halt ⟨x.unpair.1, 0⟩
      | .right => .halt ⟨x.unpair.2, 0⟩
      | .query =>
        match O x with
        | some b => .halt ⟨cond b 1 0, x + 1⟩
        | none => .stuck
      | .pair f g =>
        (run (k + 1) O f x).bind fun a ↦
          (run (k + 1) O g x).bind fun b ↦ .halt ⟨Nat.pair a b, 0⟩
      | .comp f g =>
        (run (k + 1) O g x).bind fun y ↦ run (k + 1) O f y
      | .prec f g =>
        match x.unpair.2 with
        | 0 => run (k + 1) O f x.unpair.1
        | n + 1 =>
          (run k O (.prec f g) (Nat.pair x.unpair.1 n)).bind fun y ↦
            run (k + 1) O g (Nat.pair x.unpair.1 (Nat.pair n y))
      | .rfind f =>
        (run (k + 1) O f x).bind fun y ↦
          if y = 0 then .halt ⟨x.unpair.2, 0⟩
          else run k O (.rfind f) (Nat.pair x.unpair.1 (x.unpair.2 + 1))
    else .timeout
  termination_by k _ c _ => (k, sizeOf c)

/-! ### Step lemmas

`run` is defined by well-founded recursion, so it does not reduce
definitionally; these named equations (guard hypothesis discharged) are the
interface every later proof rewrites with. -/

@[simp] theorem run_zero_fuel (O : PartOracle) (c : OracleCode) (x : ℕ) :
    run 0 O c x = .timeout := by
  rw [run.eq_def]

/-- With fuel `k + 1`, an input larger than `k` times out immediately (the
`evaln`-style input guard). -/
theorem run_input_guard {k x : ℕ} (O : PartOracle) (c : OracleCode) (h : ¬ x ≤ k) :
    run (k + 1) O c x = .timeout := by
  rw [run.eq_def]; simp [h]

theorem run_zero_step {k x : ℕ} (O : PartOracle) (hx : x ≤ k) :
    run (k + 1) O .zero x = .halt ⟨0, 0⟩ := by
  rw [run.eq_def]; simp [hx]

theorem run_succ_step {k x : ℕ} (O : PartOracle) (hx : x ≤ k) :
    run (k + 1) O .succ x = .halt ⟨x + 1, 0⟩ := by
  rw [run.eq_def]; simp [hx]

theorem run_left_step {k x : ℕ} (O : PartOracle) (hx : x ≤ k) :
    run (k + 1) O .left x = .halt ⟨x.unpair.1, 0⟩ := by
  rw [run.eq_def]; simp [hx]

theorem run_right_step {k x : ℕ} (O : PartOracle) (hx : x ≤ k) :
    run (k + 1) O .right x = .halt ⟨x.unpair.2, 0⟩ := by
  rw [run.eq_def]; simp [hx]

theorem run_query_some {k x : ℕ} {O : PartOracle} {b : Bool} (hx : x ≤ k)
    (hO : O x = some b) :
    run (k + 1) O .query x = .halt ⟨cond b 1 0, x + 1⟩ := by
  rw [run.eq_def]; simp [hx, hO]

theorem run_query_none {k x : ℕ} {O : PartOracle} (hx : x ≤ k)
    (hO : O x = none) :
    run (k + 1) O .query x = .stuck := by
  rw [run.eq_def]; simp [hx, hO]

theorem run_pair_step {k x : ℕ} (O : PartOracle) (f g : OracleCode) (hx : x ≤ k) :
    run (k + 1) O (.pair f g) x =
      (run (k + 1) O f x).bind fun a ↦
        (run (k + 1) O g x).bind fun b ↦ .halt ⟨Nat.pair a b, 0⟩ := by
  rw [run.eq_def]; simp [hx]

theorem run_comp_step {k x : ℕ} (O : PartOracle) (f g : OracleCode) (hx : x ≤ k) :
    run (k + 1) O (.comp f g) x =
      (run (k + 1) O g x).bind fun y ↦ run (k + 1) O f y := by
  rw [run.eq_def]; simp [hx]

theorem run_prec_zero_step {k x : ℕ} (O : PartOracle) (f g : OracleCode)
    (hx : x ≤ k) (hx2 : x.unpair.2 = 0) :
    run (k + 1) O (.prec f g) x = run (k + 1) O f x.unpair.1 := by
  rw [run.eq_def]; simp [hx, hx2]

theorem run_prec_succ_step {k x n : ℕ} (O : PartOracle) (f g : OracleCode)
    (hx : x ≤ k) (hx2 : x.unpair.2 = n + 1) :
    run (k + 1) O (.prec f g) x =
      (run k O (.prec f g) (Nat.pair x.unpair.1 n)).bind fun y ↦
        run (k + 1) O g (Nat.pair x.unpair.1 (Nat.pair n y)) := by
  rw [run.eq_def]; simp [hx, hx2]

theorem run_rfind_step {k x : ℕ} (O : PartOracle) (f : OracleCode) (hx : x ≤ k) :
    run (k + 1) O (.rfind f) x =
      (run (k + 1) O f x).bind fun y ↦
        if y = 0 then .halt ⟨x.unpair.2, 0⟩
        else run k O (.rfind f) (Nat.pair x.unpair.1 (x.unpair.2 + 1)) := by
  rw [run.eq_def]; simp [hx]

/-- A halting run passed the input guard: the input is strictly below the
fuel.  (Mirrors Mathlib's `evaln_bound`.) -/
theorem run_halt_input_lt {k : ℕ} {O : PartOracle} {c : OracleCode} {x : ℕ}
    {d : HaltData} (h : run k O c x = .halt d) : x < k := by
  match k with
  | 0 => simp at h
  | k + 1 =>
    by_cases hx : x ≤ k
    · omega
    · rw [run_input_guard O c hx] at h
      exact absurd h (by simp)

end OracleComputability
