/-
# The splitting requirements: agreement length and restraint

Requirement `N_j`, for `e = j / 2` and `i = j % 2`, is

> `N_j : A ≠ Φ_e^{A_i}`

— exactly the shape of Friedberg–Muchnik's `R_e : A ≠ Φ_e^B` and
`S_e : B ≠ Φ_e^A`, with the same "even attacks one half, odd the other"
indexing (`oracleOf` below is the twin of FM's `ConsState.oracleOf`).

What is *not* the same is how the requirement is met.  FM's requirement
manufactures its disagreement: it appoints a fresh witness `x`, waits for
`Φ_e(x) ↓ = 0`, and then puts `x` into its own set.  A splitting
requirement cannot manufacture anything — the set `A` is given.  It can
only *find* a disagreement and protect it.  So instead of a witness and an
`acted` flag it keeps a **length of agreement** and a **restraint**:

* `agreeAt ec st s j y` — does `Φ_{e,s}^{A_{i,s}}(y)` halt within fuel `s`,
  against the length-`s` snapshot of its half, with the value that stage
  `s` of `A` assigns to `y`?  If so, return the recorded *use*.
* `lenAgree` — how many leading arguments `y` agree at stage `s`;
* `restraintAt` — the largest use among those agreeing computations, i.e.
  the initial segment of `A_i` that must be frozen to keep them alive.

`agreeAt` is FM's `ConsState.convCheck` with one change of comparison
value: FM asks whether the computation says `0` (the value its witness is
about to refute), Sacks asks whether it says what `A_s` currently says.
The decoding lemma `agreeAt_eq_some` is the twin of FM's
`ConsState.convCheck_eq_some`, proved the same way.

`lenAgree` and `restraintAt` are defined by explicit recursion on a bound
rather than with `List.takeWhile`/`List.foldr`, so that the two extraction
facts each needs (`_isSome_of_lt` / `le_restAux`, and their converses) are
short inductions, and so that `CE.lean` can hand them to `Primrec.nat_rec`
unchanged.
-/
import SacksSplitting.Basic

namespace SacksSplitting

open FriedbergMuchnik

/-! ### The construction state

A plain tuple, not a structure: `Primcodable` is then automatic, which is
what lets `CE.lean` skip the entire shadow-implementation layer FM needed
(`St`, `encSt`, `encSt_stage`) to make its custom state types computable. -/

/-- Construction state after a stage: the two half-enumerations `A₀`, `A₁`
so far, and the cumulative restraint of each requirement born so far. -/
abbrev State : Type := List ℕ × List ℕ × List ℕ

/-- Requirement `j` attacks `A ≠ Φ_{j/2}^{A_{j%2}}`, so its oracle is half
`j % 2`.  (The twin of FM's `ConsState.oracleOf`.) -/
def oracleOf (st : State) (j : ℕ) : List ℕ :=
  if j % 2 = 0 then st.1 else st.2.1

theorem oracleOf_mod_two (st : State) (j : ℕ) : oracleOf st (j % 2) = oracleOf st j := by
  unfold oracleOf
  rw [Nat.mod_mod_of_dvd j (dvd_refl 2)]

/-! ### The agreement test -/

/-- **The bounded agreement test.**  Does `Φ_{j/2}` with the length-`s`
snapshot of half `j % 2` as oracle halt on `y` within fuel `s`, with the
value stage `s` of `A` assigns to `y`?  Returns the recorded use if so.

This is FM's `ConsState.convCheck` with the constant comparison value `0`
replaced by "what `A_s` says": FM refutes a computation by enumerating its
witness, Sacks preserves a computation that is already right. -/
def agreeAt (ec : ℕ) (st : State) (s j y : ℕ) : Option ℕ :=
  let v := nrun s (snapshotOf (oracleOf st j) s) (j / 2) y
  if 2 ≤ v ∧ (v - 2).unpair.1 = natOfBool (decide (y ∈ enumStage ec s)) then
    some (v - 2).unpair.2
  else none

/-- Decoding the agreement test, the twin of FM's
`ConsState.convCheck_eq_some`. -/
theorem agreeAt_eq_some {ec : ℕ} {st : State} {s j y u : ℕ} :
    agreeAt ec st s j y = some u ↔
      run s (PartOracle.ofSnapshot (snapshotOf (oracleOf st j) s))
          (OracleCode.ofNatCode (j / 2)) y
        = .halt ⟨natOfBool (decide (y ∈ enumStage ec s)), u⟩ := by
  unfold agreeAt nrun
  cases hr : run s (PartOracle.ofSnapshot (snapshotOf (oracleOf st j) s))
      (OracleCode.ofNatCode (j / 2)) y with
  | timeout => simp
  | stuck => simp
  | halt d =>
    obtain ⟨o, uu⟩ := d
    by_cases ho : o = natOfBool (decide (y ∈ enumStage ec s))
    · subst ho
      simp [Nat.unpair_pair]
    · simp [Nat.unpair_pair, ho]

theorem agreeAt_isSome_iff {ec : ℕ} {st : State} {s j y : ℕ} :
    (agreeAt ec st s j y).isSome = true ↔ ∃ u, agreeAt ec st s j y = some u := by
  cases h : agreeAt ec st s j y <;> simp

/-! ### Length of agreement -/

/-- `lenAux ec st s j n` — the number of leading arguments below `n` at
which requirement `j` agrees at stage `s`. -/
def lenAux (ec : ℕ) (st : State) (s j : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if lenAux ec st s j n = n ∧ (agreeAt ec st s j n).isSome = true then n + 1
    else lenAux ec st s j n

/-- **The length of agreement** of requirement `j` at stage `s`. -/
def lenAgree (ec : ℕ) (st : State) (s j : ℕ) : ℕ := lenAux ec st s j s

theorem lenAux_le (ec : ℕ) (st : State) (s j n : ℕ) : lenAux ec st s j n ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    show (if lenAux ec st s j n = n ∧ _ then n + 1 else lenAux ec st s j n) ≤ n + 1
    split
    · exact le_rfl
    · omega

theorem lenAgree_le (ec : ℕ) (st : State) (s j : ℕ) : lenAgree ec st s j ≤ s :=
  lenAux_le ec st s j s

theorem lenAux_mono (ec : ℕ) (st : State) (s j : ℕ) {m n : ℕ} (h : m ≤ n) :
    lenAux ec st s j m ≤ lenAux ec st s j n := by
  induction h with
  | refl => exact le_rfl
  | @step n _ ih =>
    refine ih.trans ?_
    show lenAux ec st s j n ≤ if lenAux ec st s j n = n ∧ _ then n + 1 else lenAux ec st s j n
    split
    · omega
    · exact le_rfl

/-- Below the agreement length, the test really did succeed. -/
theorem agreeAt_isSome_of_lt {ec : ℕ} {st : State} {s j n y : ℕ}
    (h : y < lenAux ec st s j n) : (agreeAt ec st s j y).isSome = true := by
  induction n with
  | zero => exact absurd h (by simp [lenAux])
  | succ n ih =>
    rw [show lenAux ec st s j (n + 1) =
        if lenAux ec st s j n = n ∧ (agreeAt ec st s j n).isSome = true
        then n + 1 else lenAux ec st s j n from rfl] at h
    split at h
    · next hc =>
      rcases Nat.lt_or_ge y n with hy | hy
      · exact ih (by omega)
      · have : y = n := by omega
        subst this
        exact hc.2
    · exact ih h

theorem agreeAt_isSome_of_lt_lenAgree {ec : ℕ} {st : State} {s j y : ℕ}
    (h : y < lenAgree ec st s j) : (agreeAt ec st s j y).isSome = true :=
  agreeAt_isSome_of_lt h

/-- Conversely: agreement everywhere below `n` makes the counter reach
`n`. -/
theorem lenAux_eq_of_all {ec : ℕ} {st : State} {s j n : ℕ}
    (h : ∀ y, y < n → (agreeAt ec st s j y).isSome = true) :
    lenAux ec st s j n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : lenAux ec st s j n = n := ih fun y hy => h y (by omega)
    show (if lenAux ec st s j n = n ∧ (agreeAt ec st s j n).isSome = true
      then n + 1 else lenAux ec st s j n) = n + 1
    rw [if_pos ⟨hn, h n (by omega)⟩]

/-- The form the verification uses: if everything up to `y` agrees at a
stage past `y`, the agreement length exceeds `y`. -/
theorem lt_lenAgree {ec : ℕ} {st : State} {s j y : ℕ} (hy : y < s)
    (h : ∀ z, z ≤ y → (agreeAt ec st s j z).isSome = true) :
    y < lenAgree ec st s j := by
  have h1 : lenAux ec st s j (y + 1) = y + 1 :=
    lenAux_eq_of_all fun z hz => h z (by omega)
  have h2 : lenAux ec st s j (y + 1) ≤ lenAgree ec st s j :=
    lenAux_mono ec st s j (by omega)
  omega

/-! ### The restraint -/

/-- `restAux ec st s j n` — the largest use recorded by the agreeing
computations at arguments below `n`. -/
def restAux (ec : ℕ) (st : State) (s j : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max ((agreeAt ec st s j n).getD 0) (restAux ec st s j n)

/-- **The restraint** of requirement `j` at stage `s`: the initial segment
of its half that must stay frozen for its current agreement to survive.
This is the direct analogue of FM's `ReqState.restraint`, which likewise
holds the use of the computation the requirement is protecting — except
that FM's is set once, when the requirement acts, and this one is
recomputed at every stage because the agreement keeps moving. -/
def restraintAt (ec : ℕ) (st : State) (s j : ℕ) : ℕ :=
  restAux ec st s j (lenAgree ec st s j)

theorem le_restAux {ec : ℕ} {st : State} {s j n y : ℕ} (hy : y < n) :
    (agreeAt ec st s j y).getD 0 ≤ restAux ec st s j n := by
  induction n with
  | zero => omega
  | succ n ih =>
    show _ ≤ max ((agreeAt ec st s j n).getD 0) (restAux ec st s j n)
    rcases Nat.lt_or_ge y n with h | h
    · exact le_trans (ih h) (le_max_right _ _)
    · have : y = n := by omega
      subst this
      exact le_max_left _ _

theorem restAux_le {ec : ℕ} {st : State} {s j n M : ℕ}
    (h : ∀ y, y < n → (agreeAt ec st s j y).getD 0 ≤ M) :
    restAux ec st s j n ≤ M := by
  induction n with
  | zero => exact Nat.zero_le M
  | succ n ih =>
    show max ((agreeAt ec st s j n).getD 0) (restAux ec st s j n) ≤ M
    exact max_le (h n (by omega)) (ih fun y hy => h y (by omega))

/-- Every use protected at stage `s` is below the restraint. -/
theorem use_le_restraintAt {ec : ℕ} {st : State} {s j y u : ℕ}
    (hy : y < lenAgree ec st s j) (hu : agreeAt ec st s j y = some u) :
    u ≤ restraintAt ec st s j := by
  have := le_restAux (ec := ec) (st := st) (s := s) (j := j) hy
  rwa [hu, Option.getD_some] at this

theorem restraintAt_le {ec : ℕ} {st : State} {s j M : ℕ}
    (h : ∀ y, y < lenAgree ec st s j → (agreeAt ec st s j y).getD 0 ≤ M) :
    restraintAt ec st s j ≤ M :=
  restAux_le h

end SacksSplitting
