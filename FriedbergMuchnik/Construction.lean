/-
# The Friedberg–Muchnik stage construction

The machine that enumerates the two sets.  Classical source: Soare,
*Recursively Enumerable Sets and Degrees*, VII.2 (the original
finite-injury solution of Post's problem).

Requirements, in priority order of their index `i`:

* `i = 2e`  : `R_e : A ≠ Φ_e^B` — witness goes into `A`, restraint on `B`;
* `i = 2e+1`: `S_e : B ≠ Φ_e^A` — witness goes into `B`, restraint on `A`.

State after a stage: the two enumeration lists, one record
`⟨witness, acted, restraint⟩` per requirement (requirement `i` gets its
record at stage `i + 1`), and a freshness counter strictly above every
number the construction has mentioned.

At stage `s + 1` the *least* requirement that requires attention receives
it (Soare's "requires attention" discipline, one action per stage):

* no witness yet → appoint the counter value as witness (fresh: bigger
  than all current restraints and all enumerated numbers);
* witness `x`, not yet acted, and the bounded evaluator sees
  `Φ_{i/2}^{oracle_s}(x) ↓ = 0` (fuel `s`, oracle snapshot of length `s`)
  → **act**: enumerate `x` into the requirement's set, record the
  computation's use as restraint, and *initialize* every lower-priority
  requirement (their witnesses, actions and restraints are cancelled —
  this is the injury).

The convergence test consults `run` only through `nrun` (numbered codes,
encoded results), so the whole step function is built from primitive
recursive pieces; that is what will make `A` and `B` computably
enumerable.
-/
import OracleComputability.RunPrimrec
import OracleComputability.Approximation

namespace FriedbergMuchnik

/-! ### Snapshots of enumeration lists -/

/-- Boolean snapshot of (the set of elements of) a list: position `j < u`
holds the membership bit of `j`. -/
def snapshotOf (l : List ℕ) (u : ℕ) : List Bool :=
  (List.range u).map fun j => decide (j ∈ l)

@[simp] theorem snapshotOf_length (l : List ℕ) (u : ℕ) :
    (snapshotOf l u).length = u := by
  simp [snapshotOf]

/-- The list snapshot agrees with the `Finset` snapshot of the
approximation layer. -/
theorem snapshotOf_eq_snapshot (l : List ℕ) (u : ℕ) :
    snapshotOf l u = snapshot l.toFinset u := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp [snapshotOf, snapshot]

/-! ### Construction state -/

/-- The record the construction keeps for one requirement. -/
structure ReqState where
  /-- The current diagonalization witness, if one is appointed. -/
  witness : Option ℕ
  /-- Whether the requirement has acted (enumerated its witness and
  imposed its restraint) since it was last initialized. -/
  acted : Bool
  /-- The restraint imposed on the *other* set: no number below it may be
  enumerated by lower-priority requirements while this record survives. -/
  restraint : ℕ
  deriving DecidableEq, Repr

/-- The blank record: no witness, no action, no restraint. -/
def ReqState.init : ReqState := ⟨none, false, 0⟩

/-- Construction state after a stage. -/
structure ConsState where
  /-- Numbers enumerated into `A` so far. -/
  Alist : List ℕ
  /-- Numbers enumerated into `B` so far. -/
  Blist : List ℕ
  /-- `reqs[i]` is the record of requirement `i`; length = current stage. -/
  reqs : List ReqState
  /-- Strictly above every number mentioned so far (elements, witnesses,
  restraints); appointed witnesses are drawn from here. -/
  fresh : ℕ
  deriving DecidableEq, Repr

namespace ConsState

/-- The oracle of requirement `i`: even requirements attack `A ≠ Φ^B` and
query `B`; odd ones attack `B ≠ Φ^A` and query `A`. -/
def oracleOf (st : ConsState) (i : ℕ) : List ℕ :=
  if i % 2 = 0 then st.Blist else st.Alist

/-- The set the witness of requirement `i` would be enumerated into. -/
def targetOf (st : ConsState) (i : ℕ) : List ℕ :=
  if i % 2 = 0 then st.Alist else st.Blist

/-- Bounded convergence test of stage `s + 1`: does
`Φ_{i/2}^{oracle}(x)` halt with output `0` within fuel `s`, against the
length-`s` snapshot of the current oracle list?  Returns the recorded use
if so.  (Output `0` is the computation claiming "`x` is *not* in the
target set" — exactly the claim the requirement refutes by enumerating
`x`.) -/
def convCheck (st : ConsState) (s i x : ℕ) : Option ℕ :=
  let v := nrun s (snapshotOf (st.oracleOf i) s) (i / 2) x
  if 2 ≤ v ∧ (v - 2).unpair.1 = 0 then some (v - 2).unpair.2 else none

/-- Requirement `i` requires attention at stage `s + 1` (Soare VII.2.1):
it exists and either has no witness, or has an unacted witness whose
diagonalizing computation has shown up. -/
def requiresAttention (st : ConsState) (s i : ℕ) : Bool :=
  match st.reqs[i]? with
  | none => false
  | some r =>
    match r.witness with
    | none => true
    | some x => !r.acted && (st.convCheck s i x).isSome

/-- Give attention to requirement `i` (assumed to require it).
Appointment consumes the freshness counter; action enumerates the
witness, records the use as restraint, initializes everything of lower
priority, and pushes the counter above the new restraint. -/
def stepAt (st : ConsState) (s i : ℕ) : ConsState :=
  let r := st.reqs.getD i ReqState.init
  match r.witness with
  | none =>
    { st with
      reqs := st.reqs.set i { r with witness := some st.fresh }
      fresh := st.fresh + 1 }
  | some x =>
    match st.convCheck s i x with
    | none => st
    | some u =>
      { Alist := if i % 2 = 0 then x :: st.Alist else st.Alist
        Blist := if i % 2 = 0 then st.Blist else x :: st.Blist
        reqs := st.reqs.take i ++ (⟨some x, true, u⟩ : ReqState) ::
          List.replicate (st.reqs.length - (i + 1)) ReqState.init
        fresh := max st.fresh (u + 1) }

end ConsState

/-- One full stage: create the record for the newest requirement, then
give attention to the least requirement requiring it (if any). -/
def stepState (st : ConsState) (s : ℕ) : ConsState :=
  let st' : ConsState := { st with reqs := st.reqs ++ [ReqState.init] }
  match (List.range st'.reqs.length).find? (fun i => st'.requiresAttention s i) with
  | none => st'
  | some i => st'.stepAt s i

/-- The construction: state after stage `s`. -/
def stageState : ℕ → ConsState
  | 0 => ⟨[], [], [], 0⟩
  | s + 1 => stepState (stageState s) s

/-- The finite approximation to `A` after stage `s`. -/
def AstageF (s : ℕ) : Finset ℕ := (stageState s).Alist.toFinset

/-- The finite approximation to `B` after stage `s`. -/
def BstageF (s : ℕ) : Finset ℕ := (stageState s).Blist.toFinset

/-- The first of the two incomparable c.e. sets. -/
def Aset : Set ℕ := limitSet AstageF

/-- The second of the two incomparable c.e. sets. -/
def Bset : Set ℕ := limitSet BstageF

/-! ### Basic stage lemmas -/

theorem ConsState.stepAt_Alist_mono {st : ConsState} {s i : ℕ} {a : ℕ}
    (h : a ∈ st.Alist) : a ∈ (st.stepAt s i).Alist := by
  simp only [ConsState.stepAt]
  split
  · simpa using h
  · split
    · exact h
    · by_cases hp : i % 2 = 0 <;> simp [hp, h]

theorem ConsState.stepAt_Blist_mono {st : ConsState} {s i : ℕ} {b : ℕ}
    (h : b ∈ st.Blist) : b ∈ (st.stepAt s i).Blist := by
  simp only [ConsState.stepAt]
  split
  · simpa using h
  · split
    · exact h
    · by_cases hp : i % 2 = 0 <;> simp [hp, h]

theorem stepState_Alist_mono {st : ConsState} {s : ℕ} {a : ℕ}
    (h : a ∈ st.Alist) : a ∈ (stepState st s).Alist := by
  simp only [stepState]
  split
  · exact h
  · exact ConsState.stepAt_Alist_mono h

theorem stepState_Blist_mono {st : ConsState} {s : ℕ} {b : ℕ}
    (h : b ∈ st.Blist) : b ∈ (stepState st s).Blist := by
  simp only [stepState]
  split
  · exact h
  · exact ConsState.stepAt_Blist_mono h

/-- The `A`-approximations grow (enumeration without removal): the
construction is a c.e. approximation in the corrected sense. -/
theorem AstageF_mono : StageMono AstageF := by
  intro s a ha
  rw [AstageF, List.mem_toFinset] at ha ⊢
  exact stepState_Alist_mono ha

/-- The `B`-approximations grow. -/
theorem BstageF_mono : StageMono BstageF := by
  intro s b hb
  rw [BstageF, List.mem_toFinset] at hb ⊢
  exact stepState_Blist_mono hb

/-- Requirement `i`'s record exists from stage `i + 1` on: the record
list at stage `s` has length exactly `s`. -/
theorem reqs_length (s : ℕ) : (stageState s).reqs.length = s := by
  induction s with
  | zero => rfl
  | succ s IH =>
    show (stepState (stageState s) s).reqs.length = s + 1
    have hlen' : ((stageState s).reqs ++ [ReqState.init]).length = s + 1 := by
      simp [IH]
    simp only [stepState]
    split
    · exact hlen'
    · next i hfind =>
      have hi : i < s + 1 := by
        have hmem := List.mem_of_find?_eq_some hfind
        rw [List.mem_range] at hmem
        simpa [IH] using hmem
      simp only [ConsState.stepAt]
      split
      · simpa using hlen'
      · split
        · exact hlen'
        · simp only [List.length_append, List.length_take, List.length_cons,
            List.length_replicate, hlen']
          omega

/-- Decoding the convergence test: it succeeds with use `u` exactly if
the bounded run halts with output `0` and use `u`. -/
theorem ConsState.convCheck_eq_some {st : ConsState} {s i x u : ℕ} :
    st.convCheck s i x = some u ↔
      run s (PartOracle.ofSnapshot (snapshotOf (st.oracleOf i) s))
        (OracleCode.ofNatCode (i / 2)) x = .halt ⟨0, u⟩ := by
  unfold convCheck nrun
  cases hr : run s (PartOracle.ofSnapshot (snapshotOf (st.oracleOf i) s))
      (OracleCode.ofNatCode (i / 2)) x with
  | timeout => simp
  | stuck => simp
  | halt d =>
    obtain ⟨o, uu⟩ := d
    by_cases ho : o = 0
    · subst ho
      simp [Nat.unpair_pair]
    · simp [Nat.unpair_pair, ho]

end FriedbergMuchnik
