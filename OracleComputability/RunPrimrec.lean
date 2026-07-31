/-
# The finite evaluator is primitive recursive (foundation gate item 8)

This file proves the analog of Mathlib's `Nat.Partrec.Code.primrec_evaln`
for the oracle evaluator: `run`, on snapshot oracles, is primitive
recursive in Mathlib's sense.  This is what lets the Mathlib `Primrec`/
`Partrec` closure library certify that the priority construction — which
consults `run` at every stage — is computable, and hence (through
`MathlibBridge`) that the two constructed sets are `CE`.

Strategy (following `primrec_evaln`'s memo-table strong recursion, with
two simplifications made possible by `Numbering.lean`):

* codes are handled as their numbers (`ofNatCode`), so no `Primcodable
  OracleCode` instance and no primrec-recursor lemma for the code type is
  needed — branching on a code is arithmetic on its number;
* results are encoded as naturals (`encodeResult`: `timeout ↦ 0`,
  `stuck ↦ 1`, `halt ⟨o, u⟩ ↦ Nat.pair o u + 2`), so memo tables are plain
  `List ℕ` and all table operations are naturals-and-lists primitives.

The snapshot `σ : List Bool` is threaded through the strong recursion as
its parameter (Mathlib's proof instantiates that parameter with `Unit`).

The recursion is on the index `Nat.pair k c` (fuel, code number): the row
for `(k, c)` lists `run k σ c n` for all `n < k`, and computing it needs
only rows `(k, c')` for subcode numbers `c' < c` and `(k - 1, c)` — both
smaller indices.  Out-of-range lookups default to `0 = timeout`, which is
exactly the input guard's behavior (`run_timeout_of_ge`), so no special
guard handling is needed — the same trick as Mathlib's `evaln_map`.
-/
import Mathlib.Computability.Primrec
import OracleComputability.FiniteEval
import OracleComputability.Numbering

namespace OracleComputability

/-! ### Results as naturals -/

/-- Injective encoding of `RunResult` into `ℕ`: `timeout ↦ 0`, `stuck ↦ 1`,
`halt ⟨o, u⟩ ↦ Nat.pair o u + 2`.  Halting is "value `≥ 2`", and output
and use are recovered by `Nat.unpair` of the value minus `2`. -/
def encodeResult : RunResult → ℕ
  | .timeout => 0
  | .stuck => 1
  | .halt d => Nat.pair d.output d.use + 2

@[simp] theorem encodeResult_timeout : encodeResult .timeout = 0 := rfl

@[simp] theorem encodeResult_stuck : encodeResult .stuck = 1 := rfl

@[simp] theorem encodeResult_halt (d : HaltData) :
    encodeResult (.halt d) = Nat.pair d.output d.use + 2 := rfl

theorem two_le_encodeResult_iff {r : RunResult} :
    2 ≤ encodeResult r ↔ ∃ d, r = .halt d := by
  cases r with
  | halt d => simp
  | stuck => simp
  | timeout => simp

theorem encodeResult_halt_sub_unpair (d : HaltData) :
    (encodeResult (.halt d) - 2).unpair = (d.output, d.use) := by
  simp [Nat.unpair_pair]

/-! ### The evaluator on numbered codes, with encoded results -/

/-- The finite evaluator in the form in which it crosses the Mathlib
bridge: fuel, snapshot oracle, *numbered* code, input — encoded result.
Everything downstream that needs computability of the evaluator (the stage
construction, c.e.-ness of the constructed sets) consumes `run` through
this function. -/
def nrun (k : ℕ) (σ : List Bool) (c : ℕ) (x : ℕ) : ℕ :=
  encodeResult (run k (PartOracle.ofSnapshot σ) (OracleCode.ofNatCode c) x)

/-- Fuel at most the input forces a timeout (the input guard, in the form
needed for out-of-range table lookups). -/
theorem run_timeout_of_ge {k x : ℕ} (O : PartOracle) (c : OracleCode)
    (h : k ≤ x) : run k O c x = .timeout := by
  cases k with
  | zero => exact run_zero_fuel O c x
  | succ k => exact run_input_guard O c (by omega)

/-! ### Memo tables -/

/-- Table lookup with default `0` (= encoded `timeout`).  `L` is a list of
rows; row `i` is meant to hold the encoded results of `run` at index
`i = Nat.pair k c` for inputs `n < k`, so the default agrees with the
input guard for out-of-range `n`. -/
def lookupTab (L : List (List ℕ)) (i n : ℕ) : ℕ :=
  ((L[i]?).bind fun row => row[n]?).getD 0

/-- The row of the memo table at index `p = Nat.pair k c`: the encoded
results of `run k σ c n` for all `n < k`.  This is the function the strong
recursion computes. -/
def tabRow (σ : List Bool) (p : ℕ) : List ℕ :=
  (List.range p.unpair.1).map fun n => nrun p.unpair.1 σ p.unpair.2 n

@[simp] theorem tabRow_length (σ : List Bool) (p : ℕ) :
    (tabRow σ p).length = p.unpair.1 := by
  simp [tabRow]

/-- Correctness of lookups into a table of correct rows: at any index
below the table length, `lookupTab` computes `nrun` — including out of
range of the row, where the default `0` agrees with the input guard.
(The analog of Mathlib's `evaln_map`.) -/
theorem lookupTab_range_map (σ : List Bool) {N k c : ℕ} (n : ℕ)
    (h : Nat.pair k c < N) :
    lookupTab ((List.range N).map (tabRow σ)) (Nat.pair k c) n = nrun k σ c n := by
  have hN : Nat.pair k c < ((List.range N).map (tabRow σ)).length := by
    simpa using h
  rw [lookupTab, List.getElem?_eq_getElem hN]
  simp only [List.getElem_map, List.getElem_range, Option.bind_some]
  by_cases hn : n < k
  · have hn' : n < (tabRow σ (Nat.pair k c)).length := by simpa using hn
    rw [List.getElem?_eq_getElem hn']
    simp [tabRow, Nat.unpair_pair]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hn)]
    have : run k (PartOracle.ofSnapshot σ) (OracleCode.ofNatCode c) n = .timeout :=
      run_timeout_of_ge _ _ (Nat.le_of_not_lt hn)
    simp [nrun, this]

/-! ### The step function of the strong recursion

`stepBody σ L cc k' n` computes (the encoding of) `run (k' + 1)
(ofSnapshot σ) (ofNatCode cc) n` from a memo table `L`, branching on the
*number* `cc` by the same arithmetic that defines `ofNatCode`:
`cc < 5` selects a leaf, and for `cc = m + 5` the tag `m % 4` selects the
combining constructor with payload `m / 4`.  All recursive calls of `run`
become `lookupTab` lookups at smaller indices, and the `RunResult.bind`
use-bookkeeping becomes arithmetic on encoded results ("`< 2`" = did not
halt; output/use = `Nat.unpair` of the value minus 2). -/

/-- One entry of the next memo-table row; see the section docstring. -/
def stepBody (σ : List Bool) (L : List (List ℕ)) (cc k' n : ℕ) : ℕ :=
  if cc = 0 then Nat.pair 0 0 + 2
  else if cc = 1 then Nat.pair (n + 1) 0 + 2
  else if cc = 2 then Nat.pair n.unpair.1 0 + 2
  else if cc = 3 then Nat.pair n.unpair.2 0 + 2
  else if cc = 4 then
    (σ[n]?).casesOn 1 fun b => Nat.pair (cond b 1 0) (n + 1) + 2
  else
    if (cc - 5) % 4 = 0 then
      let r1 := lookupTab L (Nat.pair (k' + 1) ((cc - 5) / 4).unpair.1) n
      let r2 := lookupTab L (Nat.pair (k' + 1) ((cc - 5) / 4).unpair.2) n
      if r1 < 2 then r1
      else if r2 < 2 then r2
      else Nat.pair (Nat.pair (r1 - 2).unpair.1 (r2 - 2).unpair.1)
        (max (r1 - 2).unpair.2 (max (r2 - 2).unpair.2 0)) + 2
    else if (cc - 5) % 4 = 1 then
      let r2 := lookupTab L (Nat.pair (k' + 1) ((cc - 5) / 4).unpair.2) n
      if r2 < 2 then r2
      else
        let r1 := lookupTab L (Nat.pair (k' + 1) ((cc - 5) / 4).unpair.1)
          (r2 - 2).unpair.1
        if r1 < 2 then r1
        else Nat.pair (r1 - 2).unpair.1
          (max (r2 - 2).unpair.2 (r1 - 2).unpair.2) + 2
    else if (cc - 5) % 4 = 2 then
      if n.unpair.2 = 0 then
        lookupTab L (Nat.pair (k' + 1) ((cc - 5) / 4).unpair.1) n.unpair.1
      else
        let ri := lookupTab L (Nat.pair k' cc)
          (Nat.pair n.unpair.1 (n.unpair.2 - 1))
        if ri < 2 then ri
        else
          let rg := lookupTab L (Nat.pair (k' + 1) ((cc - 5) / 4).unpair.2)
            (Nat.pair n.unpair.1 (Nat.pair (n.unpair.2 - 1) (ri - 2).unpair.1))
          if rg < 2 then rg
          else Nat.pair (rg - 2).unpair.1
            (max (ri - 2).unpair.2 (rg - 2).unpair.2) + 2
    else
      let rf := lookupTab L (Nat.pair (k' + 1) ((cc - 5) / 4)) n
      if rf < 2 then rf
      else if (rf - 2).unpair.1 = 0 then
        Nat.pair n.unpair.2 (max (rf - 2).unpair.2 0) + 2
      else
        let rr := lookupTab L (Nat.pair k' cc)
          (Nat.pair n.unpair.1 (n.unpair.2 + 1))
        if rr < 2 then rr
        else Nat.pair (rr - 2).unpair.1
          (max (rf - 2).unpair.2 (rr - 2).unpair.2) + 2

/-- The row-step function of the strong recursion: from the table of all
rows below index `L.length`, compute row `L.length` (fuel
`L.length.unpair.1`, code number `L.length.unpair.2`).  Always succeeds;
the `Option` is the interface `Primrec.nat_strong_rec` expects. -/
def stepRow (σ : List Bool) (L : List (List ℕ)) : Option (List ℕ) :=
  some <|
    (List.range L.length.unpair.1).map fun n =>
      (L.length.unpair.1).casesOn 0 fun k' => stepBody σ L L.length.unpair.2 k' n

/-- Correctness of one entry of the step function, against *abstract*
correct lookups: if the table answers correctly at all indices
`(k' + 1, c')` for subcode numbers `c' < cc` and at `(k', cc)`, then
`stepBody` computes `nrun (k' + 1) σ cc n`.  One case per constructor of
the machine model, each aligned with its `run_*_step` lemma. -/
private theorem stepBody_correct (σ : List Bool) (L : List (List ℕ))
    (cc k' n : ℕ) (hnk : n ≤ k')
    (hsub : ∀ c', c' < cc →
      ∀ x, lookupTab L (Nat.pair (k' + 1) c') x = nrun (k' + 1) σ c' x)
    (hself : ∀ x, lookupTab L (Nat.pair k' cc) x = nrun k' σ cc x) :
    stepBody σ L cc k' n = nrun (k' + 1) σ cc n := by
  rcases cc with _ | _ | _ | _ | _ | m
  -- cc = 0 : zero
  · simp [stepBody, nrun, OracleCode.ofNatCode_zero,
      run_zero_step (PartOracle.ofSnapshot σ) hnk]
  -- cc = 1 : succ
  · simp [stepBody, nrun, OracleCode.ofNatCode_one,
      run_succ_step (PartOracle.ofSnapshot σ) hnk]
  -- cc = 2 : left
  · simp [stepBody, nrun, OracleCode.ofNatCode_two,
      run_left_step (PartOracle.ofSnapshot σ) hnk]
  -- cc = 3 : right
  · simp [stepBody, nrun, OracleCode.ofNatCode_three,
      run_right_step (PartOracle.ofSnapshot σ) hnk]
  -- cc = 4 : query
  · cases hσ : σ[n]? with
    | some b =>
      simp [stepBody, nrun, OracleCode.ofNatCode_four, hσ,
        run_query_some (O := PartOracle.ofSnapshot σ) hnk
          (by rw [PartOracle.ofSnapshot_apply, hσ])]
    | none =>
      simp [stepBody, nrun, OracleCode.ofNatCode_four, hσ,
        run_query_none (O := PartOracle.ofSnapshot σ) hnk
          (by rw [PartOracle.ofSnapshot_apply, hσ])]
  -- cc = m + 5 : combining constructors, tag m % 4
  · have hb1 : (m / 4).unpair.1 < m + 5 := by
      have := Nat.unpair_left_le (m / 4)
      have := Nat.div_le_self m 4
      omega
    have hb2 : (m / 4).unpair.2 < m + 5 := by
      have := Nat.unpair_right_le (m / 4)
      have := Nat.div_le_self m 4
      omega
    have hbp : m / 4 < m + 5 := by
      have := Nat.div_le_self m 4
      omega
    have h5 : ¬(m + 5 = 0) := by omega
    have h6 : ¬(m + 5 = 1) := by omega
    have h7 : ¬(m + 5 = 2) := by omega
    have h8 : ¬(m + 5 = 3) := by omega
    have h9 : ¬(m + 5 = 4) := by omega
    have hm5 : m + 5 - 5 = m := by omega
    simp only [stepBody, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
      if_neg h9, hm5]
    simp only [nrun]
    have hd : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases hd with hm4 | hm4 | hm4 | hm4
    -- tag 0 : pair
    · have hcode : OracleCode.ofNatCode (m + 5) =
          .pair (OracleCode.ofNatCode (m / 4).unpair.1)
            (OracleCode.ofNatCode (m / 4).unpair.2) := by
        rw [OracleCode.ofNatCode, hm4]
      rw [if_pos hm4, hcode, run_pair_step _ _ _ hnk, hsub _ hb1, hsub _ hb2]
      simp only [nrun]
      cases hr1 : run (k' + 1) (PartOracle.ofSnapshot σ)
          (OracleCode.ofNatCode (m / 4).unpair.1) n with
      | timeout => simp [RunResult.bind]
      | stuck => simp [RunResult.bind]
      | halt d₁ =>
        cases hr2 : run (k' + 1) (PartOracle.ofSnapshot σ)
            (OracleCode.ofNatCode (m / 4).unpair.2) n with
        | timeout => simp [RunResult.bind]
        | stuck => simp [RunResult.bind]
        | halt d₂ => simp [RunResult.bind, Nat.unpair_pair]
    -- tag 1 : comp
    · have hcode : OracleCode.ofNatCode (m + 5) =
          .comp (OracleCode.ofNatCode (m / 4).unpair.1)
            (OracleCode.ofNatCode (m / 4).unpair.2) := by
        rw [OracleCode.ofNatCode, hm4]
      rw [if_neg (show ¬(m % 4 = 0) by omega), if_pos hm4, hcode,
        run_comp_step _ _ _ hnk, hsub _ hb2]
      simp only [nrun]
      cases hr2 : run (k' + 1) (PartOracle.ofSnapshot σ)
          (OracleCode.ofNatCode (m / 4).unpair.2) n with
      | timeout => simp [RunResult.bind]
      | stuck => simp [RunResult.bind]
      | halt d₂ =>
        rw [hsub _ hb1]
        simp only [nrun, encodeResult_halt, Nat.add_sub_cancel,
          Nat.unpair_pair]
        cases hr1 : run (k' + 1) (PartOracle.ofSnapshot σ)
            (OracleCode.ofNatCode (m / 4).unpair.1) d₂.output with
        | timeout => simp [hr1, RunResult.bind]
        | stuck => simp [hr1, RunResult.bind]
        | halt d₁ => simp [hr1, RunResult.bind, Nat.unpair_pair]
    -- tag 2 : prec
    · have hcode : OracleCode.ofNatCode (m + 5) =
          .prec (OracleCode.ofNatCode (m / 4).unpair.1)
            (OracleCode.ofNatCode (m / 4).unpair.2) := by
        rw [OracleCode.ofNatCode, hm4]
      rw [if_neg (show ¬(m % 4 = 0) by omega),
        if_neg (show ¬(m % 4 = 1) by omega), if_pos hm4, hcode]
      by_cases hn2 : n.unpair.2 = 0
      · rw [if_pos hn2, run_prec_zero_step _ _ _ hnk hn2, hsub _ hb1]
        simp [nrun]
      · rw [if_neg hn2]
        have hx2 : n.unpair.2 = (n.unpair.2 - 1) + 1 := by omega
        rw [run_prec_succ_step _ _ _ hnk hx2, hself]
        simp only [nrun, hcode]
        cases hri : run k' (PartOracle.ofSnapshot σ)
            ((OracleCode.ofNatCode (m / 4).unpair.1).prec
              (OracleCode.ofNatCode (m / 4).unpair.2))
            (Nat.pair n.unpair.1 (n.unpair.2 - 1)) with
        | timeout => simp [RunResult.bind]
        | stuck => simp [RunResult.bind]
        | halt dᵢ =>
          rw [hsub _ hb2]
          simp only [nrun, encodeResult_halt, Nat.add_sub_cancel,
            Nat.unpair_pair]
          cases hrg : run (k' + 1) (PartOracle.ofSnapshot σ)
              (OracleCode.ofNatCode (m / 4).unpair.2)
              (Nat.pair n.unpair.1 (Nat.pair (n.unpair.2 - 1) dᵢ.output)) with
          | timeout => simp [hrg, RunResult.bind]
          | stuck => simp [hrg, RunResult.bind]
          | halt d₂ => simp [hrg, RunResult.bind, Nat.unpair_pair]
    -- tag 3 : rfind
    · have hcode : OracleCode.ofNatCode (m + 5) =
          .rfind (OracleCode.ofNatCode (m / 4)) := by
        rw [OracleCode.ofNatCode, hm4]
      rw [if_neg (show ¬(m % 4 = 0) by omega),
        if_neg (show ¬(m % 4 = 1) by omega),
        if_neg (show ¬(m % 4 = 2) by omega), hcode,
        run_rfind_step _ _ hnk, hsub _ hbp]
      simp only [nrun]
      cases hrf : run (k' + 1) (PartOracle.ofSnapshot σ)
          (OracleCode.ofNatCode (m / 4)) n with
      | timeout => simp [RunResult.bind]
      | stuck => simp [RunResult.bind]
      | halt df =>
        rw [hself]
        simp only [nrun, hcode, encodeResult_halt, Nat.add_sub_cancel,
          Nat.unpair_pair]
        by_cases hy : df.output = 0
        · simp [hy, RunResult.bind]
        · cases hrr : run k' (PartOracle.ofSnapshot σ)
              ((OracleCode.ofNatCode (m / 4)).rfind)
              (Nat.pair n.unpair.1 (n.unpair.2 + 1)) with
          | timeout => simp [hy, RunResult.bind]
          | stuck => simp [hy, RunResult.bind]
          | halt dr => simp [hy, RunResult.bind, Nat.unpair_pair]

/-- Correctness of the step function (the hypothesis `H` of
`Primrec.nat_strong_rec`): applied to the table of all rows below `p`, it
produces row `p`. -/
theorem stepRow_correct (σ : List Bool) (p : ℕ) :
    stepRow σ ((List.range p).map (tabRow σ)) = some (tabRow σ p) := by
  have hlen : ((List.range p).map (tabRow σ)).length = p := by simp
  rw [stepRow, hlen, tabRow]
  refine congrArg some (List.map_congr_left fun n hn => ?_)
  rw [List.mem_range] at hn
  cases hk : p.unpair.1 with
  | zero => omega
  | succ k' =>
    rw [hk] at hn
    have hp : Nat.pair (k' + 1) p.unpair.2 = p := by
      rw [← hk]; exact Nat.pair_unpair p
    refine stepBody_correct σ _ p.unpair.2 k' n (by omega)
      (fun c' hc' x => ?_) (fun x => ?_)
    · have h1 : Nat.pair (k' + 1) c' < Nat.pair (k' + 1) p.unpair.2 :=
        Nat.pair_lt_pair_right _ hc'
      rw [hp] at h1
      exact lookupTab_range_map σ x h1
    · have h2 : Nat.pair k' p.unpair.2 < Nat.pair (k' + 1) p.unpair.2 :=
        Nat.pair_lt_pair_left _ (Nat.lt_succ_self k')
      rw [hp] at h2
      exact lookupTab_range_map σ x h2

/-! ### Primitive recursiveness of the step function and of `nrun` -/

private theorem lookupTab_primrec :
    Primrec fun q : List (List ℕ) × ℕ × ℕ => lookupTab q.1 q.2.1 q.2.2 := by
  have h1 : Primrec fun q : List (List ℕ) × ℕ × ℕ => q.1[q.2.1]? :=
    Primrec.list_getElem?.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have h2 : Primrec fun q : List (List ℕ) × ℕ × ℕ =>
      (q.1[q.2.1]?).bind fun row => row[q.2.2]? :=
    Primrec.option_bind h1
      (Primrec.list_getElem?.comp Primrec.snd
        ((Primrec.snd.comp Primrec.snd).comp Primrec.fst))
  exact Primrec.option_getD.comp h2 (Primrec.const 0)

/-- Input packaging for `stepBody_primrec`. -/
private abbrev SBIn : Type := (List Bool × List (List ℕ)) × (ℕ × ℕ) × ℕ

private theorem stepBody_primrec :
    Primrec fun p : SBIn => stepBody p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2 := by
  have hσ : Primrec fun p : SBIn => p.1.1 := Primrec.fst.comp Primrec.fst
  have hL : Primrec fun p : SBIn => p.1.2 := Primrec.snd.comp Primrec.fst
  have hcc : Primrec fun p : SBIn => p.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hk' : Primrec fun p : SBIn => p.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hn : Primrec fun p : SBIn => p.2.2 := Primrec.snd.comp Primrec.snd
  have hk : Primrec fun p : SBIn => p.2.1.2 + 1 := Primrec.succ.comp hk'
  have hn1 : Primrec fun p : SBIn => p.2.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hn)
  have hn2 : Primrec fun p : SBIn => p.2.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hn)
  have hpl : Primrec fun p : SBIn => (p.2.1.1 - 5) / 4 :=
    Primrec.nat_div.comp (Primrec.nat_sub.comp hcc (Primrec.const 5))
      (Primrec.const 4)
  have hpl1 : Primrec fun p : SBIn => ((p.2.1.1 - 5) / 4).unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hpl)
  have hpl2 : Primrec fun p : SBIn => ((p.2.1.1 - 5) / 4).unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hpl)
  -- lookups, encoded-halt construction, output/use extraction
  have look : ∀ {i j : SBIn → ℕ}, Primrec i → Primrec j →
      Primrec fun p : SBIn => lookupTab p.1.2 (i p) (j p) := by
    intro i j hi hj
    exact lookupTab_primrec.comp (hL.pair (hi.pair hj))
  have eH : ∀ {o u : SBIn → ℕ}, Primrec o → Primrec u →
      Primrec fun p : SBIn => Nat.pair (o p) (u p) + 2 := by
    intro o u ho hu
    exact Primrec.nat_add.comp (Primrec₂.natPair.comp ho hu) (Primrec.const 2)
  have out : ∀ {r : SBIn → ℕ}, Primrec r →
      Primrec fun p : SBIn => ((r p) - 2).unpair.1 := by
    intro r hr
    exact Primrec.fst.comp
      (Primrec.unpair.comp (Primrec.nat_sub.comp hr (Primrec.const 2)))
  have use_ : ∀ {r : SBIn → ℕ}, Primrec r →
      Primrec fun p : SBIn => ((r p) - 2).unpair.2 := by
    intro r hr
    exact Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.nat_sub.comp hr (Primrec.const 2)))
  have lt2 : ∀ {r : SBIn → ℕ}, Primrec r → PrimrecPred fun p : SBIn => r p < 2 := by
    intro r hr
    exact PrimrecRel.comp Primrec.nat_lt hr (Primrec.const 2)
  have eqC : ∀ {r : SBIn → ℕ} (c : ℕ), Primrec r →
      PrimrecPred fun p : SBIn => r p = c := by
    intro r c hr
    exact PrimrecRel.comp Primrec.eq hr (Primrec.const c)
  -- the four combining cases
  have casePair : Primrec fun p : SBIn =>
      (fun r1 r2 =>
        if r1 < 2 then r1
        else if r2 < 2 then r2
        else Nat.pair (Nat.pair (r1 - 2).unpair.1 (r2 - 2).unpair.1)
          (max (r1 - 2).unpair.2 (max (r2 - 2).unpair.2 0)) + 2)
      (lookupTab p.1.2 (Nat.pair (p.2.1.2 + 1) ((p.2.1.1 - 5) / 4).unpair.1) p.2.2)
      (lookupTab p.1.2 (Nat.pair (p.2.1.2 + 1) ((p.2.1.1 - 5) / 4).unpair.2) p.2.2) := by
    have hr1 := look (Primrec₂.natPair.comp hk hpl1) hn
    have hr2 := look (Primrec₂.natPair.comp hk hpl2) hn
    exact Primrec.ite (lt2 hr1) hr1
      (Primrec.ite (lt2 hr2) hr2
        (eH (Primrec₂.natPair.comp (out hr1) (out hr2))
          (Primrec.nat_max.comp (use_ hr1)
            (Primrec.nat_max.comp (use_ hr2) (Primrec.const 0)))))
  have caseComp : Primrec fun p : SBIn =>
      (fun r2 =>
        if r2 < 2 then r2
        else
          (fun r1 =>
            if r1 < 2 then r1
            else Nat.pair (r1 - 2).unpair.1
              (max (r2 - 2).unpair.2 (r1 - 2).unpair.2) + 2)
          (lookupTab p.1.2 (Nat.pair (p.2.1.2 + 1) ((p.2.1.1 - 5) / 4).unpair.1)
            (r2 - 2).unpair.1))
      (lookupTab p.1.2 (Nat.pair (p.2.1.2 + 1) ((p.2.1.1 - 5) / 4).unpair.2) p.2.2) := by
    have hr2 := look (Primrec₂.natPair.comp hk hpl2) hn
    have hr1 := look (Primrec₂.natPair.comp hk hpl1) (out hr2)
    exact Primrec.ite (lt2 hr2) hr2
      (Primrec.ite (lt2 hr1) hr1
        (eH (out hr1) (Primrec.nat_max.comp (use_ hr2) (use_ hr1))))
  have casePrec : Primrec fun p : SBIn =>
      if p.2.2.unpair.2 = 0 then
        lookupTab p.1.2 (Nat.pair (p.2.1.2 + 1) ((p.2.1.1 - 5) / 4).unpair.1)
          p.2.2.unpair.1
      else
        (fun ri =>
          if ri < 2 then ri
          else
            (fun rg =>
              if rg < 2 then rg
              else Nat.pair (rg - 2).unpair.1
                (max (ri - 2).unpair.2 (rg - 2).unpair.2) + 2)
            (lookupTab p.1.2 (Nat.pair (p.2.1.2 + 1) ((p.2.1.1 - 5) / 4).unpair.2)
              (Nat.pair p.2.2.unpair.1
                (Nat.pair (p.2.2.unpair.2 - 1) (ri - 2).unpair.1))))
        (lookupTab p.1.2 (Nat.pair p.2.1.2 p.2.1.1)
          (Nat.pair p.2.2.unpair.1 (p.2.2.unpair.2 - 1))) := by
    have hsub1 : Primrec fun p : SBIn => p.2.2.unpair.2 - 1 :=
      Primrec.nat_sub.comp hn2 (Primrec.const 1)
    have hri := look (Primrec₂.natPair.comp hk' hcc)
      (Primrec₂.natPair.comp hn1 hsub1)
    have hrg := look (Primrec₂.natPair.comp hk hpl2)
      (Primrec₂.natPair.comp hn1 (Primrec₂.natPair.comp hsub1 (out hri)))
    exact Primrec.ite (eqC 0 hn2) (look (Primrec₂.natPair.comp hk hpl1) hn1)
      (Primrec.ite (lt2 hri) hri
        (Primrec.ite (lt2 hrg) hrg
          (eH (out hrg) (Primrec.nat_max.comp (use_ hri) (use_ hrg)))))
  have caseRfind : Primrec fun p : SBIn =>
      (fun rf =>
        if rf < 2 then rf
        else if (rf - 2).unpair.1 = 0 then
          Nat.pair p.2.2.unpair.2 (max (rf - 2).unpair.2 0) + 2
        else
          (fun rr =>
            if rr < 2 then rr
            else Nat.pair (rr - 2).unpair.1
              (max (rf - 2).unpair.2 (rr - 2).unpair.2) + 2)
          (lookupTab p.1.2 (Nat.pair p.2.1.2 p.2.1.1)
            (Nat.pair p.2.2.unpair.1 (p.2.2.unpair.2 + 1))))
      (lookupTab p.1.2 (Nat.pair (p.2.1.2 + 1) ((p.2.1.1 - 5) / 4)) p.2.2) := by
    have hrf := look (Primrec₂.natPair.comp hk hpl) hn
    have hrr := look (Primrec₂.natPair.comp hk' hcc)
      (Primrec₂.natPair.comp hn1 (Primrec.succ.comp hn2))
    exact Primrec.ite (lt2 hrf) hrf
      (Primrec.ite (eqC 0 (out hrf))
        (eH hn2 (Primrec.nat_max.comp (use_ hrf) (Primrec.const 0)))
        (Primrec.ite (lt2 hrr) hrr
          (eH (out hrr) (Primrec.nat_max.comp (use_ hrf) (use_ hrr)))))
  -- assemble the branch chain
  simp only [stepBody]
  refine Primrec.ite (eqC 0 hcc) (Primrec.const (Nat.pair 0 0 + 2)) ?_
  refine Primrec.ite (eqC 1 hcc)
    (eH (Primrec.succ.comp hn) (Primrec.const 0)) ?_
  refine Primrec.ite (eqC 2 hcc) (eH hn1 (Primrec.const 0)) ?_
  refine Primrec.ite (eqC 3 hcc) (eH hn2 (Primrec.const 0)) ?_
  refine Primrec.ite (eqC 4 hcc) ?_ ?_
  · exact Primrec.option_casesOn (Primrec.list_getElem?.comp hσ hn)
      (Primrec.const 1)
      (Primrec.nat_add.comp
        (Primrec₂.natPair.comp
          (Primrec.cond Primrec.snd (Primrec.const 1) (Primrec.const 0))
          (Primrec.succ.comp (hn.comp Primrec.fst)))
        (Primrec.const 2)).to₂
  refine Primrec.ite ?_ casePair ?_
  · exact PrimrecRel.comp Primrec.eq
      (Primrec.nat_mod.comp (Primrec.nat_sub.comp hcc (Primrec.const 5))
        (Primrec.const 4)) (Primrec.const 0)
  refine Primrec.ite ?_ caseComp ?_
  · exact PrimrecRel.comp Primrec.eq
      (Primrec.nat_mod.comp (Primrec.nat_sub.comp hcc (Primrec.const 5))
        (Primrec.const 4)) (Primrec.const 1)
  refine Primrec.ite ?_ casePrec caseRfind
  exact PrimrecRel.comp Primrec.eq
    (Primrec.nat_mod.comp (Primrec.nat_sub.comp hcc (Primrec.const 5))
      (Primrec.const 4)) (Primrec.const 2)

private theorem stepRow_primrec : Primrec₂ stepRow := by
  have hlen : Primrec fun p : List Bool × List (List ℕ) => p.2.length :=
    Primrec.list_length.comp Primrec.snd
  have hk : Primrec fun p : List Bool × List (List ℕ) => p.2.length.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hlen)
  have hcc : Primrec fun p : List Bool × List (List ℕ) => p.2.length.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hlen)
  refine Primrec.option_some.comp
    (Primrec.list_map (Primrec.list_range.comp hk) ?_)
  refine Primrec.nat_casesOn (hk.comp Primrec.fst) (Primrec.const 0) ?_
  exact (stepBody_primrec.comp
    (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
      (((hcc.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd).pair
        (Primrec.snd.comp Primrec.fst)))).to₂

/-- The memo-table row function is primitive recursive (by strong
recursion on the row index, with the snapshot as parameter). -/
theorem tabRow_primrec : Primrec₂ tabRow :=
  Primrec.nat_strong_rec tabRow stepRow_primrec stepRow_correct

/-- `nrun` reads off the memo table: `run k σ c x` (encoded) is entry `x`
of the row at index `Nat.pair k c`, with out-of-range defaulting to
timeout exactly as the input guard does. -/
theorem nrun_eq_tabRow (k : ℕ) (σ : List Bool) (c x : ℕ) :
    nrun k σ c x = ((tabRow σ (Nat.pair k c))[x]?).getD 0 := by
  by_cases hx : x < k
  · have hx' : x < (tabRow σ (Nat.pair k c)).length := by simpa using hx
    rw [List.getElem?_eq_getElem hx']
    simp [tabRow, Nat.unpair_pair]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hx)]
    have h : run k (PartOracle.ofSnapshot σ) (OracleCode.ofNatCode c) x = .timeout :=
      run_timeout_of_ge _ _ (Nat.le_of_not_lt hx)
    simp [nrun, h]

/-- **Foundation gate item 8**: the finite evaluator, on snapshot oracles
and numbered codes, is primitive recursive in Mathlib's sense (the analog
of Mathlib's `Nat.Partrec.Code.primrec_evaln`).  Everything the priority
construction computes at a stage factors through this function, so its
computability makes the whole construction computable. -/
theorem nrun_primrec :
    Primrec fun p : ((ℕ × List Bool) × ℕ) × ℕ =>
      nrun p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  have hk : Primrec fun p : ((ℕ × List Bool) × ℕ) × ℕ => p.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hσ : Primrec fun p : ((ℕ × List Bool) × ℕ) × ℕ => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hc : Primrec fun p : ((ℕ × List Bool) × ℕ) × ℕ => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hx : Primrec fun p : ((ℕ × List Bool) × ℕ) × ℕ => p.2 := Primrec.snd
  have htab : Primrec fun p : ((ℕ × List Bool) × ℕ) × ℕ =>
      (tabRow p.1.1.2 (Nat.pair p.1.1.1 p.1.2))[p.2]? :=
    Primrec.list_getElem?.comp
      (tabRow_primrec.comp hσ (Primrec₂.natPair.comp hk hc)) hx
  exact (Primrec.option_getD.comp htab (Primrec.const 0)).of_eq
    fun p => (nrun_eq_tabRow _ _ _ _).symm

end OracleComputability
