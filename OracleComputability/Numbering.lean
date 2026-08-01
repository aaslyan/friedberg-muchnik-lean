import Mathlib.Data.Nat.Pairing
import OracleComputability.OracleCode

/-!
# Effective numbering of oracle programs

Foundation gate items 1 and 5: an explicit bijection `ℕ ≃ OracleCode`
(both round-trip equations proved), so that

* requirements `R_e`/`S_e` can be indexed by naturals while provably
  covering *every* oracle program — this is what makes "for every `e`,
  `A ≠ Φ_e^B`" mean "for every possible Turing reduction" *for the
  project's own definition of `≤ᵀ`* (enumeration adequacy), and
* the priority order of requirements is the order of program numbers, fully
  concrete.

The coding is the usual one (cf. Mathlib's `Nat.Partrec.Code.ofNatCode`):
five leaves get the numbers `0`–`4`, and a composite gets `4·payload + tag + 5`
where `tag < 4` selects the constructor and `payload` codes the children via
`Nat.pair`.  Sums of the form `4·p + t + 5` are written exactly that way so
the `n + 5` pattern of the decoder matches syntactically in proofs.
-/

namespace OracleComputability

namespace OracleCode

/-- Gödel number of an oracle program. -/
def encodeCode : OracleCode → ℕ
  | .zero => 0
  | .succ => 1
  | .left => 2
  | .right => 3
  | .query => 4
  | .pair f g => 4 * Nat.pair (encodeCode f) (encodeCode g) + 5
  | .comp f g => 4 * Nat.pair (encodeCode f) (encodeCode g) + 1 + 5
  | .prec f g => 4 * Nat.pair (encodeCode f) (encodeCode g) + 2 + 5
  | .rfind f => 4 * encodeCode f + 3 + 5

/-- The oracle program with Gödel number `n`.  Total: *every* natural number
is the number of a program, so an enumeration of requirements over `ℕ`
misses no program. -/
def ofNatCode : ℕ → OracleCode
  | 0 => .zero
  | 1 => .succ
  | 2 => .left
  | 3 => .right
  | 4 => .query
  | n + 5 =>
    have _h1 : n / 4 ≤ n := Nat.div_le_self n 4
    have _h2 : (n / 4).unpair.1 ≤ n / 4 := Nat.unpair_left_le _
    have _h3 : (n / 4).unpair.2 ≤ n / 4 := Nat.unpair_right_le _
    match n % 4 with
    | 0 => .pair (ofNatCode (n / 4).unpair.1) (ofNatCode (n / 4).unpair.2)
    | 1 => .comp (ofNatCode (n / 4).unpair.1) (ofNatCode (n / 4).unpair.2)
    | 2 => .prec (ofNatCode (n / 4).unpair.1) (ofNatCode (n / 4).unpair.2)
    | _ => .rfind (ofNatCode (n / 4))
  termination_by n => n
  decreasing_by all_goals omega

/-- Decoding is left inverse to encoding on the five leaves (step lemmas;
`ofNatCode` is defined by well-founded recursion, so these are `rw`
equations rather than definitional reductions). -/
@[simp] theorem ofNatCode_zero : ofNatCode 0 = .zero := by rw [ofNatCode]

@[simp] theorem ofNatCode_one : ofNatCode 1 = .succ := by rw [ofNatCode]

@[simp] theorem ofNatCode_two : ofNatCode 2 = .left := by rw [ofNatCode]

@[simp] theorem ofNatCode_three : ofNatCode 3 = .right := by rw [ofNatCode]

@[simp] theorem ofNatCode_four : ofNatCode 4 = .query := by rw [ofNatCode]

/-- First round-trip: decoding the number of a program gives the program
back (injectivity of the numbering). -/
theorem ofNatCode_encodeCode : ∀ c : OracleCode, ofNatCode (encodeCode c) = c
  | .zero => ofNatCode_zero
  | .succ => ofNatCode_one
  | .left => ofNatCode_two
  | .right => ofNatCode_three
  | .query => ofNatCode_four
  | .pair f g => by
    have IHf := ofNatCode_encodeCode f
    have IHg := ofNatCode_encodeCode g
    show ofNatCode (4 * Nat.pair (encodeCode f) (encodeCode g) + 5) = _
    rw [ofNatCode]
    have hmod : (4 * Nat.pair (encodeCode f) (encodeCode g)) % 4 = 0 := by
      omega
    have hdiv : (4 * Nat.pair (encodeCode f) (encodeCode g)) / 4 =
        Nat.pair (encodeCode f) (encodeCode g) := by
      omega
    rw [hmod, hdiv, Nat.unpair_pair, IHf, IHg]
  | .comp f g => by
    have IHf := ofNatCode_encodeCode f
    have IHg := ofNatCode_encodeCode g
    show ofNatCode (4 * Nat.pair (encodeCode f) (encodeCode g) + 1 + 5) = _
    rw [ofNatCode]
    have hmod : (4 * Nat.pair (encodeCode f) (encodeCode g) + 1) % 4 = 1 := by
      omega
    have hdiv : (4 * Nat.pair (encodeCode f) (encodeCode g) + 1) / 4 =
        Nat.pair (encodeCode f) (encodeCode g) := by
      omega
    rw [hmod, hdiv, Nat.unpair_pair, IHf, IHg]
  | .prec f g => by
    have IHf := ofNatCode_encodeCode f
    have IHg := ofNatCode_encodeCode g
    show ofNatCode (4 * Nat.pair (encodeCode f) (encodeCode g) + 2 + 5) = _
    rw [ofNatCode]
    have hmod : (4 * Nat.pair (encodeCode f) (encodeCode g) + 2) % 4 = 2 := by
      omega
    have hdiv : (4 * Nat.pair (encodeCode f) (encodeCode g) + 2) / 4 =
        Nat.pair (encodeCode f) (encodeCode g) := by
      omega
    rw [hmod, hdiv, Nat.unpair_pair, IHf, IHg]
  | .rfind f => by
    have IHf := ofNatCode_encodeCode f
    show ofNatCode (4 * encodeCode f + 3 + 5) = _
    rw [ofNatCode]
    have hmod : (4 * encodeCode f + 3) % 4 = 3 := by omega
    have hdiv : (4 * encodeCode f + 3) / 4 = encodeCode f := by omega
    rw [hmod, hdiv, IHf]

/-- Second round-trip: encoding the program with number `n` gives `n` back
(surjectivity of the numbering onto `ℕ` — every number *is* a program
number, so `ℕ`-indexed requirement lists are gap-free). -/
theorem encodeCode_ofNatCode : ∀ n : ℕ, encodeCode (ofNatCode n) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    match n with
    | 0 => rw [ofNatCode_zero]; rfl
    | 1 => rw [ofNatCode_one]; rfl
    | 2 => rw [ofNatCode_two]; rfl
    | 3 => rw [ofNatCode_three]; rfl
    | 4 => rw [ofNatCode_four]; rfl
    | n + 5 =>
      have h1 : n / 4 ≤ n := Nat.div_le_self n 4
      have h2 : (n / 4).unpair.1 ≤ n / 4 := Nat.unpair_left_le _
      have h3 : (n / 4).unpair.2 ≤ n / 4 := Nat.unpair_right_le _
      have IH1 := IH (n / 4).unpair.1 (by omega)
      have IH2 := IH (n / 4).unpair.2 (by omega)
      have IHp := IH (n / 4) (by omega)
      have hmod : n % 4 < 4 := Nat.mod_lt _ (by omega)
      rw [ofNatCode]
      rcases hm : n % 4 with _ | _ | _ | _ | m
      · simp only [encodeCode, IH1, IH2, Nat.pair_unpair]
        omega
      · simp only [encodeCode, IH1, IH2, Nat.pair_unpair]
        omega
      · simp only [encodeCode, IH1, IH2, Nat.pair_unpair]
        omega
      · simp only [encodeCode, IHp]
        omega
      · omega

/-- The numbering is a bijection; in particular `OracleCode` is countable
and its enumeration by `ofNatCode` is adequate for the project's `≤ᵀ`:
quantifying requirements over all of `ℕ` covers every oracle program. -/
theorem ofNatCode_surjective : Function.Surjective ofNatCode :=
  fun c ↦ ⟨encodeCode c, ofNatCode_encodeCode c⟩

theorem encodeCode_injective : Function.Injective encodeCode :=
  fun c c' h ↦ by
    have := ofNatCode_encodeCode c
    rw [h, ofNatCode_encodeCode c'] at this
    exact this.symm

end OracleCode

end OracleComputability
