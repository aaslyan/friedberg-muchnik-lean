/-
# The use principle

The master theorem of this file, `run_halt_mono`, is the single lemma that
carries the whole finite-injury argument:

> If `run k O c x = .halt d`, then `run k' O' c x = .halt d` for every
> `k' ≥ k` and every partial oracle `O'` that *extends the answers of `O`
> below the recorded use* — i.e. `O' i = O i` whenever `i < d.use` and
> `O i = some b`.

Note the hypothesis is *not* "`O'` extends `O` everywhere", nor "`O'` agrees
with `O` below the use": positions `≥ d.use` are completely unconstrained,
and positions `< d.use` where `O` had no information are unconstrained too.
This is exactly what the priority construction needs.  A requirement that
sees a converging computation against a snapshot of the current stage of `B`
imposes a restraint: *no number `< use` may be enumerated into `B` from now
on*.  Since stages only ever grow (`Finset` inclusion, never removal), the
restraint makes every later snapshot — and the true oracle in the limit —
extend the frozen snapshot's answers below the use, so the frozen
computation survives verbatim.  In textbook terms (Soare, "Recursively
Enumerable Sets and Degrees", VII.2) this is the Use Principle.

Corollaries proved here:
* `run_halt_fuel_mono` — more fuel never changes a halting run;
* `run_halt_oracle_ext` — more oracle information never changes a halting run;
* `run_halt_of_consistent` — a halting run against any partial oracle
  consistent with a total `X` is also a halting run against `X` itself;
* `run_halt_unique` — determinism across fuels and consistent oracles.
-/
import FriedbergMuchnik.Foundation.FiniteEval

namespace FriedbergMuchnik

/-- Auxiliary, fully-explicit form of the use principle; the recursion
mirrors the recursion defining `run` (fuel first, then code), so the
termination measure is the same `(k, sizeOf c)`.  Use the implicit-argument
wrapper `run_halt_mono` instead of this. -/
private theorem run_halt_mono_aux :
    ∀ (k k' : ℕ) (O O' : PartOracle) (c : OracleCode) (x : ℕ) (d : HaltData),
      k ≤ k' → (∀ i, i < d.use → ∀ b, O i = some b → O' i = some b) →
      run k O c x = .halt d → run k' O' c x = .halt d
  | 0, _, _, _, _, _, _, _, _, h => by simp at h
  | _ + 1, 0, _, _, _, _, _, hk, _, _ => absurd hk (by omega)
  | k + 1, k' + 1, O, O', c, x, d, hk, hO, h => by
    have hk' : k ≤ k' := by omega
    have hxk : x ≤ k := Nat.lt_succ_iff.mp (run_halt_input_lt h)
    have hxk' : x ≤ k' := hxk.trans hk'
    cases c with
    | zero =>
      rw [run_zero_step O hxk] at h
      rw [run_zero_step O' hxk']
      exact h
    | succ =>
      rw [run_succ_step O hxk] at h
      rw [run_succ_step O' hxk']
      exact h
    | left =>
      rw [run_left_step O hxk] at h
      rw [run_left_step O' hxk']
      exact h
    | right =>
      rw [run_right_step O hxk] at h
      rw [run_right_step O' hxk']
      exact h
    | query =>
      cases hOx : O x with
      | none =>
        rw [run_query_none hxk hOx] at h
        exact absurd h (by simp)
      | some b =>
        rw [run_query_some hxk hOx] at h
        have hd : d = ⟨cond b 1 0, x + 1⟩ := (RunResult.halt.inj h).symm
        have hO'x : O' x = some b :=
          hO x (by rw [hd]; exact Nat.lt_succ_self x) b hOx
        rw [run_query_some hxk' hO'x]
        exact h
    | pair f g =>
      rw [run_pair_step O f g hxk] at h
      rw [run_pair_step O' f g hxk']
      obtain ⟨d₁, dr, hf, hrest, rfl⟩ := RunResult.bind_eq_halt.mp h
      obtain ⟨d₂, dp, hg, hp, hdr⟩ := RunResult.bind_eq_halt.mp hrest
      have hdp : dp = ⟨Nat.pair d₁.output d₂.output, 0⟩ := (RunResult.halt.inj hp).symm
      subst hdp
      have hdr' : dr = ⟨Nat.pair d₁.output d₂.output, d₂.use⟩ := by
        rw [hdr]; simp
      subst hdr'
      have hf' : run (k' + 1) O' f x = .halt d₁ :=
        run_halt_mono_aux (k + 1) (k' + 1) O O' f x d₁ (by omega)
          (fun i hi b hb => hO i (lt_of_lt_of_le hi (le_max_left _ _)) b hb) hf
      have hg' : run (k' + 1) O' g x = .halt d₂ :=
        run_halt_mono_aux (k + 1) (k' + 1) O O' g x d₂ (by omega)
          (fun i hi b hb => hO i (lt_of_lt_of_le hi (le_max_right _ _)) b hb) hg
      have h2 :
          RunResult.bind (run (k' + 1) O' f x)
            (fun a => RunResult.bind (run (k' + 1) O' g x)
              (fun b => RunResult.halt ⟨Nat.pair a b, 0⟩)) =
            .halt ⟨Nat.pair d₁.output d₂.output, max d₁.use (max d₂.use 0)⟩ :=
        RunResult.bind_halt (d₂ := ⟨Nat.pair d₁.output d₂.output, max d₂.use 0⟩) hf'
          (RunResult.bind_halt (d₂ := ⟨Nat.pair d₁.output d₂.output, 0⟩) hg' rfl)
      simpa using h2
    | comp f g =>
      rw [run_comp_step O f g hxk] at h
      rw [run_comp_step O' f g hxk']
      obtain ⟨d₁, d₂, hg, hf, rfl⟩ := RunResult.bind_eq_halt.mp h
      have hg' : run (k' + 1) O' g x = .halt d₁ :=
        run_halt_mono_aux (k + 1) (k' + 1) O O' g x d₁ (by omega)
          (fun i hi b hb => hO i (lt_of_lt_of_le hi (le_max_left _ _)) b hb) hg
      have hf' : run (k' + 1) O' f d₁.output = .halt d₂ :=
        run_halt_mono_aux (k + 1) (k' + 1) O O' f d₁.output d₂ (by omega)
          (fun i hi b hb => hO i (lt_of_lt_of_le hi (le_max_right _ _)) b hb) hf
      exact RunResult.bind_halt hg' hf'
    | prec f g =>
      cases hx2 : x.unpair.2 with
      | zero =>
        rw [run_prec_zero_step O f g hxk hx2] at h
        rw [run_prec_zero_step O' f g hxk' hx2]
        exact run_halt_mono_aux (k + 1) (k' + 1) O O' f x.unpair.1 d (by omega) hO h
      | succ n =>
        rw [run_prec_succ_step O f g hxk hx2] at h
        rw [run_prec_succ_step O' f g hxk' hx2]
        obtain ⟨d₁, d₂, hp, hg, rfl⟩ := RunResult.bind_eq_halt.mp h
        have hp' : run k' O' (.prec f g) (Nat.pair x.unpair.1 n) = .halt d₁ :=
          run_halt_mono_aux k k' O O' (.prec f g) (Nat.pair x.unpair.1 n) d₁ hk'
            (fun i hi b hb => hO i (lt_of_lt_of_le hi (le_max_left _ _)) b hb) hp
        have hg' :
            run (k' + 1) O' g (Nat.pair x.unpair.1 (Nat.pair n d₁.output)) =
              .halt d₂ :=
          run_halt_mono_aux (k + 1) (k' + 1) O O' g
            (Nat.pair x.unpair.1 (Nat.pair n d₁.output)) d₂ (by omega)
            (fun i hi b hb => hO i (lt_of_lt_of_le hi (le_max_right _ _)) b hb) hg
        exact RunResult.bind_halt hp' hg'
    | rfind f =>
      rw [run_rfind_step O f hxk] at h
      rw [run_rfind_step O' f hxk']
      obtain ⟨d₁, d₂, hf, hcont, rfl⟩ := RunResult.bind_eq_halt.mp h
      have hf' : run (k' + 1) O' f x = .halt d₁ :=
        run_halt_mono_aux (k + 1) (k' + 1) O O' f x d₁ (by omega)
          (fun i hi b hb => hO i (lt_of_lt_of_le hi (le_max_left _ _)) b hb) hf
      have hcont₀ :
          (if d₁.output = 0 then RunResult.halt ⟨x.unpair.2, 0⟩
            else run k O (.rfind f) (Nat.pair x.unpair.1 (x.unpair.2 + 1))) =
            .halt d₂ := hcont
      by_cases hy : d₁.output = 0
      · rw [if_pos hy] at hcont₀
        refine RunResult.bind_halt hf' ?_
        show (if d₁.output = 0 then RunResult.halt ⟨x.unpair.2, 0⟩
          else run k' O' (.rfind f) (Nat.pair x.unpair.1 (x.unpair.2 + 1))) = _
        rw [if_pos hy]
        exact hcont₀
      · rw [if_neg hy] at hcont₀
        have hcont' :
            run k' O' (.rfind f) (Nat.pair x.unpair.1 (x.unpair.2 + 1)) =
              .halt d₂ :=
          run_halt_mono_aux k k' O O' (.rfind f)
            (Nat.pair x.unpair.1 (x.unpair.2 + 1)) d₂ hk'
            (fun i hi b hb => hO i (lt_of_lt_of_le hi (le_max_right _ _)) b hb) hcont₀
        refine RunResult.bind_halt hf' ?_
        show (if d₁.output = 0 then RunResult.halt ⟨x.unpair.2, 0⟩
          else run k' O' (.rfind f) (Nat.pair x.unpair.1 (x.unpair.2 + 1))) = _
        rw [if_neg hy]
        exact hcont'
  termination_by k _ _ _ c _ _ _ _ _ => (k, sizeOf c)

/-- **The use principle** (master form).  A halting bounded run survives
(1) any increase of fuel and (2) replacement of the oracle by any partial
oracle that gives the same answers at the positions below the recorded use
at which the original oracle gave answers.  The halting data — output *and*
use — is unchanged. -/
theorem run_halt_mono {k k' : ℕ} {O O' : PartOracle} {c : OracleCode} {x : ℕ}
    {d : HaltData} (hk : k ≤ k')
    (hO : ∀ i, i < d.use → ∀ b, O i = some b → O' i = some b)
    (h : run k O c x = .halt d) :
    run k' O' c x = .halt d :=
  run_halt_mono_aux k k' O O' c x d hk hO h

/-- More fuel never changes a halting run (Mathlib's `evaln_mono`, for the
oracle model). -/
theorem run_halt_fuel_mono {k k' : ℕ} {O : PartOracle} {c : OracleCode} {x : ℕ}
    {d : HaltData} (hk : k ≤ k') (h : run k O c x = .halt d) :
    run k' O c x = .halt d :=
  run_halt_mono hk (fun _ _ _ hb => hb) h

/-- More oracle information never changes a halting run: if `O'` answers
every question `O` answers (identically), a run that halted against `O`
halts identically against `O'`. -/
theorem run_halt_oracle_ext {k : ℕ} {O O' : PartOracle} {c : OracleCode} {x : ℕ}
    {d : HaltData} (hO : ∀ i b, O i = some b → O' i = some b)
    (h : run k O c x = .halt d) :
    run k O' c x = .halt d :=
  run_halt_mono le_rfl (fun i _ b hb => hO i b hb) h

namespace PartOracle

/-- `O.Consistent X`: every answer the partial oracle `O` gives agrees with
the total membership function `X`.  Snapshots of an approximation stage that
has already stabilized below their length are consistent with the limit set,
which is how finite-stage computations transfer to the limit. -/
def Consistent (O : PartOracle) (X : ℕ → Bool) : Prop :=
  ∀ i b, O i = some b → X i = b

theorem consistent_ofFun (X : ℕ → Bool) : (ofFun X).Consistent X :=
  fun _ _ h => Option.some.inj h

theorem consistent_empty (X : ℕ → Bool) : empty.Consistent X := by
  intro i b h
  simp [empty] at h

end PartOracle

/-- A halting run against any partial oracle consistent with `X` is also a
halting run against `X` itself, with the same output and use. -/
theorem run_halt_of_consistent {k : ℕ} {O : PartOracle} {X : ℕ → Bool}
    {c : OracleCode} {x : ℕ} {d : HaltData} (hO : O.Consistent X)
    (h : run k O c x = .halt d) :
    run k (PartOracle.ofFun X) c x = .halt d :=
  run_halt_mono le_rfl
    (fun i _ b hb => by rw [PartOracle.ofFun_apply, hO i b hb]) h

/-- **Determinism across consistent oracles.**  Two halting runs of the same
program on the same input, against possibly different fuels and possibly
different partial oracles that are both consistent with the same total `X`,
record identical halting data.  This is what lets the construction speak of
"the" computation `Φ_e^B(x)` even though it only ever inspects finite
snapshots at finite stages. -/
theorem run_halt_unique {k k' : ℕ} {O O' : PartOracle} {X : ℕ → Bool}
    {c : OracleCode} {x : ℕ} {d d' : HaltData}
    (hO : O.Consistent X) (hO' : O'.Consistent X)
    (h : run k O c x = .halt d) (h' : run k' O' c x = .halt d') :
    d = d' := by
  have h₁ : run (max k k') (PartOracle.ofFun X) c x = .halt d :=
    run_halt_fuel_mono (le_max_left k k') (run_halt_of_consistent hO h)
  have h₂ : run (max k k') (PartOracle.ofFun X) c x = .halt d' :=
    run_halt_fuel_mono (le_max_right k k') (run_halt_of_consistent hO' h')
  rw [h₁] at h₂
  exact RunResult.halt.inj h₂

end FriedbergMuchnik
