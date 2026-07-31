/-
# Monotone finite-stage approximations and their limits

The two c.e. sets of the Friedberg–Muchnik construction are built as
`⊆`-monotone sequences of finite sets `F : ℕ → Finset ℕ` — a number may be
*enumerated* (flip `false → true`) at any stage but never removed.  This
file provides everything the priority argument needs to pass between a
stage, its Boolean snapshot, and the limit set:

* `StageMono`, `limitSet` — monotone stage sequences and their union;
* `StageMono.stabilizesBelow` — below any fixed bound, membership agrees
  with the limit from some stage on (proved by induction on the bound, no
  appeal to finiteness of the limit set is needed);
* `snapshot` — the Boolean string of a stage set up to a bound: the *only*
  way `List Bool` enters the construction (stage sequences themselves are
  **not** prefix-monotone strings — that design would force the limits to
  be computable);
* `run_halt_limit_of_restraint` — **the restraint mechanism** (Soare
  VII.2, "preservation of computations"): a computation seen halting
  against a snapshot of stage `s` survives to the limit set, provided no
  number below its recorded use is enumerated after stage `s`;
* `run_halt_snapshot_of_limit` — conversely, a computation halting against
  the limit is visible to the construction from some stage on.

Both preservation lemmas are corollaries of the master use principle
`run_halt_mono`.
-/
import Mathlib.Data.Finset.Basic
import OracleComputability.Use
import OracleComputability.Reducibility

namespace FriedbergMuchnik

/-- A monotone stage sequence: stages only ever grow (enumeration without
removal).  This, and not prefix-monotonicity of strings, is what "c.e.
approximation" means. -/
def StageMono (F : ℕ → Finset ℕ) : Prop :=
  ∀ s, F s ⊆ F (s + 1)

/-- The limit (union) of a stage sequence: the set actually being
enumerated. -/
def limitSet (F : ℕ → Finset ℕ) : Set ℕ :=
  {n | ∃ s, n ∈ F s}

@[simp] theorem mem_limitSet {F : ℕ → Finset ℕ} {n : ℕ} :
    n ∈ limitSet F ↔ ∃ s, n ∈ F s :=
  Iff.rfl

namespace StageMono

theorem subset_of_le {F : ℕ → Finset ℕ} (hF : StageMono F) {s t : ℕ}
    (h : s ≤ t) : F s ⊆ F t := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (hF _)

/-- **Stabilization below a bound.**  For every bound `u` there is a stage
from which membership below `u` agrees with the limit set.  (Each of the
finitely many positions below `u` that ever gets enumerated is enumerated
at some stage; the induction on `u` takes maxima as it goes.)  This is the
"sufficiently late stage" that every requirement-satisfaction argument
appeals to. -/
theorem stabilizesBelow {F : ℕ → Finset ℕ} (hF : StageMono F) (u : ℕ) :
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ n, n < u → (n ∈ F s ↔ n ∈ limitSet F) := by
  induction u with
  | zero => exact ⟨0, fun s _ n hn => absurd hn (Nat.not_lt_zero n)⟩
  | succ u IH =>
    obtain ⟨s₀, hs₀⟩ := IH
    by_cases hu : u ∈ limitSet F
    · obtain ⟨t, ht⟩ := hu
      refine ⟨max s₀ t, fun s hs n hn => ?_⟩
      rcases Nat.lt_or_ge n u with h | h
      · exact hs₀ s (le_trans (le_max_left _ _) hs) n h
      · have hn_eq : n = u := by omega
        subst hn_eq
        constructor
        · intro hmem
          exact ⟨s, hmem⟩
        · intro _
          exact hF.subset_of_le (le_trans (le_max_right _ _) hs) ht
    · refine ⟨s₀, fun s hs n hn => ?_⟩
      rcases Nat.lt_or_ge n u with h | h
      · exact hs₀ s hs n h
      · have hn_eq : n = u := by omega
        subst hn_eq
        constructor
        · intro hmem
          exact absurd ⟨s, hmem⟩ hu
        · intro hmem
          exact absurd hmem hu

end StageMono

/-- The Boolean snapshot of a finite set up to a bound: position `i < u`
holds the membership bit of `i`.  This is the only place `List Bool`
appears in the construction — always derived, never primary. -/
def snapshot (F : Finset ℕ) (u : ℕ) : List Bool :=
  List.ofFn fun i : Fin u => decide (i.val ∈ F)

@[simp] theorem snapshot_length (F : Finset ℕ) (u : ℕ) :
    (snapshot F u).length = u := by
  simp [snapshot]

theorem snapshot_getElem? {F : Finset ℕ} {u i : ℕ} (h : i < u) :
    (snapshot F u)[i]? = some (decide (i ∈ F)) := by
  have hlen : i < (snapshot F u).length := by simpa using h
  rw [List.getElem?_eq_getElem hlen]
  simp [snapshot]

/-- Inversion: any answer of a snapshot oracle is the membership bit of an
in-range position. -/
theorem ofSnapshot_snapshot_some {F : Finset ℕ} {u i : ℕ} {b : Bool}
    (h : PartOracle.ofSnapshot (snapshot F u) i = some b) :
    i < u ∧ b = decide (i ∈ F) := by
  rw [PartOracle.ofSnapshot_apply] at h
  by_cases hi : i < u
  · rw [snapshot_getElem? hi] at h
    exact ⟨hi, (Option.some.inj h).symm⟩
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi)] at h
    exact absurd h (by simp)

/-- **The restraint mechanism** (Soare VII.2, preservation of
computations).  Suppose at stage `s` the construction sees a computation
halt against the snapshot of `F s` (of any length `u`), recording use
`d.use`, and from stage `s` on no number below `d.use` is enumerated into
the sequence ("the restraint is respected").  Then the very same
computation — same output, same use — halts against the limit set.  This
is how an acting requirement freezes `Φ_e^B(x)` forever. -/
theorem run_halt_limit_of_restraint {F : ℕ → Finset ℕ} {k u s x : ℕ}
    {c : OracleCode} {d : HaltData} (hF : StageMono F)
    (h : run k (PartOracle.ofSnapshot (snapshot (F s) u)) c x = .halt d)
    (hres : ∀ t, s ≤ t → ∀ n, n < d.use → n ∈ F t → n ∈ F s) :
    run k (PartOracle.ofFun (charFun (limitSet F))) c x = .halt d := by
  refine run_halt_mono le_rfl (fun i hi b hb => ?_) h
  obtain ⟨hiu, hb'⟩ := ofSnapshot_snapshot_some hb
  subst hb'
  rw [PartOracle.ofFun_apply]
  congr 1
  by_cases hmem : i ∈ F s
  · rw [charFun_eq_true.mpr (mem_limitSet.mpr ⟨s, hmem⟩), decide_eq_true hmem]
  · have hlim : i ∉ limitSet F := by
      rintro ⟨t, ht⟩
      rcases Nat.le_total t s with hts | hst
      · exact hmem (hF.subset_of_le hts ht)
      · exact hmem (hres t hst i hi ht)
    rw [charFun_eq_false.mpr hlim, decide_eq_false hmem]

/-- Conversely: a computation that halts against the limit set is halting
against the snapshot of every sufficiently late stage (of length its use).
This is why a requirement that would be satisfiable "in the limit" is
eventually offered the chance to act — the standard "wait for a true
stage" step of the verification. -/
theorem run_halt_snapshot_of_limit {F : ℕ → Finset ℕ} {k x : ℕ}
    {c : OracleCode} {d : HaltData} (hF : StageMono F)
    (h : run k (PartOracle.ofFun (charFun (limitSet F))) c x = .halt d) :
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s →
      run k (PartOracle.ofSnapshot (snapshot (F s) d.use)) c x = .halt d := by
  obtain ⟨s₀, hs₀⟩ := hF.stabilizesBelow d.use
  refine ⟨s₀, fun s hs => ?_⟩
  refine run_halt_mono le_rfl (fun i hi b hb => ?_) h
  rw [PartOracle.ofFun_apply] at hb
  have hb' : b = charFun (limitSet F) i := (Option.some.inj hb).symm
  subst hb'
  rw [PartOracle.ofSnapshot_apply, snapshot_getElem? hi]
  congr 1
  have hiff := hs₀ s hs i hi
  by_cases hmem : i ∈ F s
  · rw [decide_eq_true hmem]
    exact (charFun_eq_true.mpr (hiff.mp hmem)).symm
  · rw [decide_eq_false hmem]
    exact (charFun_eq_false.mpr (fun hl => hmem (hiff.mpr hl))).symm

/-! ### Snapshots of enumeration *lists*

A construction that enumerates into a `List ℕ` rather than a `Finset` needs
the same snapshot vocabulary, and needs it in a form the computability
layer can digest.  None of this mentions any particular construction. -/

/-- Boolean snapshot of (the set of elements of) a list: position `j < u`
holds the membership bit of `j`. -/
def snapshotOf (l : List ℕ) (u : ℕ) : List Bool :=
  (List.range u).map fun j => decide (j ∈ l)

@[simp] theorem snapshotOf_length (l : List ℕ) (u : ℕ) :
    (snapshotOf l u).length = u := by
  simp [snapshotOf]

/-- The list snapshot agrees with the `Finset` snapshot. -/
theorem snapshotOf_eq_snapshot (l : List ℕ) (u : ℕ) :
    snapshotOf l u = snapshot l.toFinset u := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp [snapshotOf, snapshot]

theorem snapshotOf_getElem? {l : List ℕ} {u p : ℕ} (h : p < u) :
    (snapshotOf l u)[p]? = some (decide (p ∈ l)) := by
  have hlen : p < (snapshotOf l u).length := by simpa using h
  rw [List.getElem?_eq_getElem hlen]
  simp [snapshotOf]

theorem ofSnapshot_snapshotOf_some {l : List ℕ} {u p : ℕ} {b : Bool}
    (h : PartOracle.ofSnapshot (snapshotOf l u) p = some b) :
    p < u ∧ b = decide (p ∈ l) := by
  rw [PartOracle.ofSnapshot_apply] at h
  by_cases hp : p < u
  · rw [snapshotOf_getElem? hp] at h
    exact ⟨hp, (Option.some.inj h).symm⟩
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hp)] at h
    exact absurd h (by simp)

/-- Enumerating a number `≥` the use of a halting computation into the
oracle list does not disturb the computation — the use principle in the
form a stage-by-stage invariant needs. -/
theorem run_halt_cons_snapshot {l : List ℕ} {x k len w : ℕ} {c : OracleCode}
    {d : HaltData} (hx : d.use ≤ x)
    (h : run k (PartOracle.ofSnapshot (snapshotOf l len)) c w = .halt d) :
    run k (PartOracle.ofSnapshot (snapshotOf (x :: l) len)) c w = .halt d := by
  refine run_halt_mono le_rfl (fun p hp b hb => ?_) h
  obtain ⟨hpl, hb'⟩ := ofSnapshot_snapshotOf_some hb
  subst hb'
  rw [PartOracle.ofSnapshot_apply, snapshotOf_getElem? hpl]
  have hpx : p ≠ x := by omega
  simp [List.mem_cons, hpx]

/-- Transfer a halting run from the `Finset` snapshot of length the use to
the full-length list snapshot of the same stage (more fuel, more oracle —
the use principle again). -/
theorem run_halt_toFinset_snapshot {l : List ℕ} {k s : ℕ} {c : OracleCode}
    {x : ℕ} {d : HaltData} (hk : k ≤ s) (hu : d.use ≤ s)
    (h : run k (PartOracle.ofSnapshot (snapshot l.toFinset d.use)) c x = .halt d) :
    run s (PartOracle.ofSnapshot (snapshotOf l s)) c x = .halt d := by
  refine run_halt_mono hk (fun p hp b hb => ?_) h
  obtain ⟨hpu, hb'⟩ := ofSnapshot_snapshot_some hb
  subst hb'
  rw [PartOracle.ofSnapshot_apply, snapshotOf_getElem? (by omega)]
  simp [List.mem_toFinset]

end FriedbergMuchnik
