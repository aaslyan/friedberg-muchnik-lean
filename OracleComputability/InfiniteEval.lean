import OracleComputability.Use

/-!
# Semantics against an infinite oracle

Ordinary (unbounded) oracle computation is defined as the *existential
closure* of the bounded evaluator of `FiniteEval.lean` over fuel — no
heavyweight continuous-functional framework, exactly as prescribed for this
project.  The finite-to-infinite correspondence (`computes_iff_initialSegment`)
says this loses nothing: a computation converges against the total oracle
`X` iff it converges against some finite initial segment of `X`, and the
initial segment of length the recorded use always suffices.  Both directions
are immediate corollaries of the master use theorem `run_halt_mono`.
-/

namespace OracleComputability

/-- `Computes c X x y`: program `c`, run with the total oracle `X`, halts on
input `x` with output `y` (for some — equivalently, all sufficiently large —
fuel bounds). -/
def Computes (c : OracleCode) (X : ℕ → Bool) (x y : ℕ) : Prop :=
  ∃ k d, run k (PartOracle.ofFun X) c x = .halt d ∧ d.output = y

/-- An oracle program computes at most one output on a given input. -/
theorem Computes.unique {c : OracleCode} {X : ℕ → Bool} {x y y' : ℕ}
    (h : Computes c X x y) (h' : Computes c X x y') : y = y' := by
  obtain ⟨k, d, hr, rfl⟩ := h
  obtain ⟨k', d', hr', rfl⟩ := h'
  rw [run_halt_unique (PartOracle.consistent_ofFun X) (PartOracle.consistent_ofFun X) hr hr']

/-- The initial segment of length `u` of a total membership function, as a
snapshot string: position `i < u` holds `X i`. -/
def initialSegment (X : ℕ → Bool) (u : ℕ) : List Bool :=
  List.ofFn fun i : Fin u ↦ X i

@[simp] theorem initialSegment_length (X : ℕ → Bool) (u : ℕ) :
    (initialSegment X u).length = u := by
  simp [initialSegment]

theorem initialSegment_getElem? {X : ℕ → Bool} {u i : ℕ} (h : i < u) :
    (initialSegment X u)[i]? = some (X i) := by
  have hlen : i < (initialSegment X u).length := by simpa using h
  rw [List.getElem?_eq_getElem hlen]
  simp [initialSegment]

/-- Initial segments are consistent with the function they cut off. -/
theorem consistent_initialSegment (X : ℕ → Bool) (u : ℕ) :
    (PartOracle.ofSnapshot (initialSegment X u)).Consistent X := by
  intro i b h
  rw [PartOracle.ofSnapshot_apply] at h
  rcases Nat.lt_or_ge i u with hi | hi
  · rw [initialSegment_getElem? hi] at h
    exact Option.some.inj h
  · rw [List.getElem?_eq_none (by simpa using hi)] at h
    exact absurd h (by simp)

/-- **Finite-to-infinite correspondence** (foundation gate item 6).
A program computes `y` from the total oracle `X` iff it computes `y` from
some finite initial segment of `X`; moreover the initial segment of length
the recorded use suffices.  Left to right is the use principle; right to
left is consistency of snapshots. -/
theorem computes_iff_initialSegment {c : OracleCode} {X : ℕ → Bool} {x y : ℕ} :
    Computes c X x y ↔
      ∃ k u d, run k (PartOracle.ofSnapshot (initialSegment X u)) c x = .halt d ∧
        d.output = y := by
  constructor
  · rintro ⟨k, d, h, rfl⟩
    refine ⟨k, d.use, d, ?_, rfl⟩
    refine run_halt_mono le_rfl (fun i hi b hb ↦ ?_) h
    rw [PartOracle.ofFun_apply] at hb
    rw [PartOracle.ofSnapshot_apply, initialSegment_getElem? hi]
    exact hb
  · rintro ⟨k, u, d, h, rfl⟩
    exact ⟨k, d, run_halt_of_consistent (consistent_initialSegment X u) h, rfl⟩

end OracleComputability
