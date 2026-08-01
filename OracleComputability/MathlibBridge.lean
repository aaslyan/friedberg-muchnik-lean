import Mathlib.Computability.PartrecCode
import OracleComputability.Use
import OracleComputability.Reducibility

/-!
# The Mathlib bridge

Foundation gate items 2–4.  This is the **only** file of the project that
imports Mathlib's computability library, and the dependency points strictly
one way: ordinary (non-oracle) computability results are transferred *into*
the local oracle model here, and nothing in the local semantics or the
priority argument refers back to Mathlib's `Code`, `Partrec`, or
`RecursiveIn`.

Contents:
* `embed : Nat.Partrec.Code → OracleCode` — the query-free image of
  Mathlib's partial recursive codes (gate item 2);
* `run_embed` — semantic preservation: running an embedded code, against
  *any* partial oracle, is exactly Mathlib's step-indexed `evaln` with the
  result lifted into `RunResult`; in particular embedded codes never get
  `stuck` and always record use `0` (gate item 3);
* `partrec_realized` — every Mathlib-partial-recursive `f : ℕ →. ℕ` is
  realized by a local code that ignores its oracle (gate item 4);
* `ce_of_partrec_dom` — a set with a Mathlib-partial-recursive
  semi-decider is `CE` in the project's sense.

The deliberate fuel-discipline match between `run` and `evaln` (same input
guard, same placement of fuel decrements) is what makes `run_embed` a
single structural induction rather than a simulation argument with fuel
translation.
-/

namespace OracleComputability

open Nat.Partrec (Code)

/-- Lift a step-indexed `Option ℕ` result of Mathlib's `evaln` into
`RunResult`: a value becomes a halt with use `0` (no oracle was consulted),
absence of a value becomes a timeout. -/
def ofEvaln : Option ℕ → RunResult
  | some y => .halt ⟨y, 0⟩
  | none => .timeout

@[simp] theorem ofEvaln_some (y : ℕ) : ofEvaln (some y) = .halt ⟨y, 0⟩ := rfl

@[simp] theorem ofEvaln_none : ofEvaln none = .timeout := rfl

/-- Embedding of Mathlib's partial recursive codes into the oracle
language.  The image is query-free: constructors map to their homonymous
counterparts. -/
def embed : Code → OracleCode
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .pair f g => .pair (embed f) (embed g)
  | .comp f g => .comp (embed f) (embed g)
  | .prec f g => .prec (embed f) (embed g)
  | .rfind' f => .rfind (embed f)

/-- Above the input guard, Mathlib's `evaln` has no value (contrapositive
of `evaln_bound`). -/
theorem evaln_eq_none_of_gt {k x : ℕ} {c : Code} (hx : ¬ x ≤ k) :
    Code.evaln (k + 1) c x = none := by
  cases h : Code.evaln (k + 1) c x with
  | none => rfl
  | some y =>
    have hb : x < k + 1 := Code.evaln_bound (Option.mem_def.mpr h)
    omega

private theorem guard_bind_pos {p : Prop} [Decidable p] (hp : p) {α : Type}
    (o : Option α) : (Bind.bind (guard p) fun _ : Unit ↦ o) = o := by
  simp [guard, hp]

/-- Both sides of the embedding correspondence time out above the input
guard. -/
private theorem run_embed_guard_neg (k x : ℕ) (O : PartOracle) (c : Code)
    (hx : ¬ x ≤ k) :
    run (k + 1) O (embed c) x = ofEvaln (Code.evaln (k + 1) c x) := by
  rw [run_input_guard O _ hx, evaln_eq_none_of_gt hx, ofEvaln_none]

/-- **Semantic preservation of the embedding** (gate item 3), fully
explicit form; use the wrapper `run_embed` instead.  The recursion mirrors
the shared fuel discipline of `run` and `evaln`. -/
private theorem run_embed_aux :
    ∀ (k : ℕ) (O : PartOracle) (c : Code) (x : ℕ),
      run k O (embed c) x = ofEvaln (Code.evaln k c x)
  | 0, _, c, x => by
    simp [Code.evaln]
  | k + 1, O, Code.zero, x => by
    by_cases hx : x ≤ k
    · rw [show embed .zero = .zero from rfl, run_zero_step O hx, Code.evaln]
      simp [guard_bind_pos hx]
    · exact run_embed_guard_neg k x O _ hx
  | k + 1, O, Code.succ, x => by
    by_cases hx : x ≤ k
    · rw [show embed .succ = .succ from rfl, run_succ_step O hx, Code.evaln]
      simp [guard_bind_pos hx]
    · exact run_embed_guard_neg k x O _ hx
  | k + 1, O, Code.left, x => by
    by_cases hx : x ≤ k
    · rw [show embed .left = .left from rfl, run_left_step O hx, Code.evaln]
      simp [guard_bind_pos hx]
    · exact run_embed_guard_neg k x O _ hx
  | k + 1, O, Code.right, x => by
    by_cases hx : x ≤ k
    · rw [show embed .right = .right from rfl, run_right_step O hx, Code.evaln]
      simp [guard_bind_pos hx]
    · exact run_embed_guard_neg k x O _ hx
  | k + 1, O, Code.pair cf cg, x => by
    by_cases hx : x ≤ k
    · have IHf : ∀ z, run (k + 1) O (embed cf) z = ofEvaln (Code.evaln (k + 1) cf z) :=
        fun z ↦ run_embed_aux (k + 1) O cf z
      have IHg : ∀ z, run (k + 1) O (embed cg) z = ofEvaln (Code.evaln (k + 1) cg z) :=
        fun z ↦ run_embed_aux (k + 1) O cg z
      rw [show embed (.pair cf cg) = .pair (embed cf) (embed cg) from rfl,
        run_pair_step O _ _ hx, Code.evaln]
      simp only [IHf, IHg, guard_bind_pos hx]
      cases hf : Code.evaln (k + 1) cf x with
      | none => simp [RunResult.bind, Seq.seq]
      | some a =>
        cases hg : Code.evaln (k + 1) cg x with
        | none => simp [RunResult.bind, Seq.seq]
        | some b => simp [RunResult.bind, Seq.seq]
    · exact run_embed_guard_neg k x O _ hx
  | k + 1, O, Code.comp cf cg, x => by
    by_cases hx : x ≤ k
    · have IHf : ∀ z, run (k + 1) O (embed cf) z = ofEvaln (Code.evaln (k + 1) cf z) :=
        fun z ↦ run_embed_aux (k + 1) O cf z
      have IHg : ∀ z, run (k + 1) O (embed cg) z = ofEvaln (Code.evaln (k + 1) cg z) :=
        fun z ↦ run_embed_aux (k + 1) O cg z
      rw [show embed (.comp cf cg) = .comp (embed cf) (embed cg) from rfl,
        run_comp_step O _ _ hx, Code.evaln]
      simp only [IHf, IHg, guard_bind_pos hx]
      cases hg : Code.evaln (k + 1) cg x with
      | none => simp [RunResult.bind]
      | some y =>
        cases hf : Code.evaln (k + 1) cf y with
        | none => simp [RunResult.bind, hf]
        | some z => simp [RunResult.bind, hf]
    · exact run_embed_guard_neg k x O _ hx
  | k + 1, O, Code.prec cf cg, x => by
    by_cases hx : x ≤ k
    · have IHf : ∀ z, run (k + 1) O (embed cf) z = ofEvaln (Code.evaln (k + 1) cf z) :=
        fun z ↦ run_embed_aux (k + 1) O cf z
      have IHg : ∀ z, run (k + 1) O (embed cg) z = ofEvaln (Code.evaln (k + 1) cg z) :=
        fun z ↦ run_embed_aux (k + 1) O cg z
      have IHp : ∀ z, run k O (.prec (embed cf) (embed cg)) z =
          ofEvaln (Code.evaln k (.prec cf cg) z) :=
        fun z ↦ run_embed_aux k O (.prec cf cg) z
      rw [show embed (.prec cf cg) = .prec (embed cf) (embed cg) from rfl]
      cases hx2 : x.unpair.2 with
      | zero =>
        rw [run_prec_zero_step O _ _ hx hx2, Code.evaln]
        simp only [IHf, guard_bind_pos hx]
        simp [Nat.unpaired, hx2]
      | succ n =>
        rw [run_prec_succ_step O _ _ hx hx2, Code.evaln]
        simp only [IHp, IHg, guard_bind_pos hx, Nat.unpaired, hx2]
        cases hi : Code.evaln k (Code.prec cf cg) (Nat.pair x.unpair.1 n) with
        | none => simp [RunResult.bind]
        | some i =>
          cases hg2 : Code.evaln (k + 1) cg (Nat.pair x.unpair.1 (Nat.pair n i)) with
          | none => simp [RunResult.bind, hg2]
          | some z => simp [RunResult.bind, hg2]
    · exact run_embed_guard_neg k x O _ hx
  | k + 1, O, Code.rfind' cf, x => by
    by_cases hx : x ≤ k
    · have IHf : ∀ z, run (k + 1) O (embed cf) z = ofEvaln (Code.evaln (k + 1) cf z) :=
        fun z ↦ run_embed_aux (k + 1) O cf z
      have IHrec : ∀ z, run k O (.rfind (embed cf)) z =
          ofEvaln (Code.evaln k (.rfind' cf) z) :=
        fun z ↦ run_embed_aux k O (.rfind' cf) z
      rw [show embed (.rfind' cf) = .rfind (embed cf) from rfl,
        run_rfind_step O _ hx, Code.evaln]
      simp only [IHf, IHrec, guard_bind_pos hx, Nat.unpaired, Nat.pair_unpair]
      cases hf : Code.evaln (k + 1) cf x with
      | none => simp [RunResult.bind]
      | some y =>
        by_cases hy : y = 0
        · simp [RunResult.bind, hy]
        · cases hrec : Code.evaln k (Code.rfind' cf)
              (Nat.pair x.unpair.1 (x.unpair.2 + 1)) with
          | none => simp [RunResult.bind, hy]
          | some z => simp [RunResult.bind, hy]
    · exact run_embed_guard_neg k x O _ hx
  termination_by k _ c _ => (k, sizeOf c)

/-- **Semantic preservation of the embedding** (gate item 3).  Running an
embedded Mathlib code against *any* partial oracle is Mathlib's `evaln`,
lifted into `RunResult`.  Embedded codes never query: they are never
`stuck`, and a halting run records use `0`. -/
theorem run_embed {k : ℕ} {O : PartOracle} {c : Code} {x : ℕ} :
    run k O (embed c) x = ofEvaln (Code.evaln k c x) :=
  run_embed_aux k O c x

/-- **Transfer of Mathlib computability into the local model** (gate item
4).  Every Mathlib-partial-recursive `f : ℕ →. ℕ` is realized by a local
oracle program that ignores its oracle: against every partial oracle, its
halting runs are exactly the values of `f`. -/
theorem partrec_realized {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    ∃ c : OracleCode, ∀ (O : PartOracle) (x y : ℕ),
      y ∈ f x ↔ ∃ k, run k O c x = .halt ⟨y, 0⟩ := by
  obtain ⟨cf, rfl⟩ := Code.exists_code.mp hf
  refine ⟨embed cf, fun O x y ↦ ?_⟩
  rw [Code.evaln_complete]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [run_embed, Option.mem_def.mp hk, ofEvaln_some]
  · rintro ⟨k, hk⟩
    rw [run_embed] at hk
    cases hev : Code.evaln k cf x with
    | none => rw [hev, ofEvaln_none] at hk; exact absurd hk (by simp)
    | some z =>
      rw [hev, ofEvaln_some] at hk
      have hz : z = y := by simpa using hk
      exact ⟨k, Option.mem_def.mpr (hz ▸ hev)⟩

/-- A set with a Mathlib-partial-recursive semi-decider is computably
enumerable in the project's sense: `A = W_e` for the embedded code.  This
is the lemma the construction will use (via Mathlib's `Partrec` closure
library) to certify that its two limit sets are c.e. -/
theorem ce_of_partrec_dom {f : ℕ →. ℕ} (hf : Nat.Partrec f) {A : Set ℕ}
    (hA : ∀ x, x ∈ A ↔ (f x).Dom) : CE A := by
  obtain ⟨cf, rfl⟩ := Code.exists_code.mp hf
  refine ⟨embed cf, fun x ↦ ?_⟩
  rw [hA x]
  constructor
  · intro hdom
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hy
    exact ⟨k, ⟨y, 0⟩, by rw [run_embed, Option.mem_def.mp hk, ofEvaln_some]⟩
  · rintro ⟨k, d, hd⟩
    rw [run_embed] at hd
    cases hev : Code.evaln k cf x with
    | none => rw [hev, ofEvaln_none] at hd; exact absurd hd (by simp)
    | some y =>
      have hy : y ∈ Code.eval cf x :=
        Code.evaln_complete.mpr ⟨k, Option.mem_def.mpr hev⟩
      exact Part.dom_iff_mem.mpr ⟨y, hy⟩

end OracleComputability
