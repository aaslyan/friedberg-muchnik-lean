/-
# Syntax of oracle programs

This file defines *syntax only*: the inductive type of programs for a machine
model of partial recursive functions relative to an oracle for a set of
natural numbers.

The step-indexed operational semantics lives in `FiniteEval.lean`; the
translation to and from Mathlib's `Nat.Partrec.Code` lives in
`MathlibBridge.lean` and nothing outside that file depends on Mathlib's
computability library.  In particular, changes to Mathlib's internal coding
decisions cannot contaminate the priority argument.
-/

namespace FriedbergMuchnik

/-- Programs of the oracle machine model.

The first four constructors and the three combining schemata are Kleene's
partial recursive schemata, in the same unary-with-pairing presentation that
Mathlib uses for plain partial recursive functions (`Nat.Partrec.Code`):
every program denotes a partial function `ℕ →. ℕ`, and multi-argument
functions are routed through the pairing function `Nat.pair`.

`query` is the single oracle primitive: on input `n` it asks the oracle
"is `n` a member of your set?" and returns `1` for yes, `0` for no.

An `OracleCode` containing no `query` node is an ordinary partial recursive
program; `MathlibBridge.lean` makes that statement precise in both
directions. -/
inductive OracleCode : Type where
  /-- The constant zero function `fun _ => 0`. -/
  | zero
  /-- The successor function `fun n => n + 1`. -/
  | succ
  /-- First projection of a coded pair: `fun n => (Nat.unpair n).1`. -/
  | left
  /-- Second projection of a coded pair: `fun n => (Nat.unpair n).2`. -/
  | right
  /-- Oracle query: on input `n`, return `1` if `n` is in the oracle set and
  `0` if it is not.  Relative to *finite* oracle information (a snapshot
  string), a query beyond the end of the snapshot does not halt; see
  `FiniteEval.lean`. -/
  | query
  /-- `pair f g` computes `fun n => Nat.pair (f n) (g n)`. -/
  | pair (f g : OracleCode)
  /-- `comp f g` computes `fun n => f (g n)`. -/
  | comp (f g : OracleCode)
  /-- Primitive recursion.  On input `Nat.pair a 0`, `prec f g` computes
  `f a`; on input `Nat.pair a (n + 1)` it computes
  `g (Nat.pair a (Nat.pair n y))` where `y` is the value at
  `Nat.pair a n`. -/
  | prec (f g : OracleCode)
  /-- Unbounded search (in the "primed" form that recurses well with a step
  bound, exactly as in Mathlib's `Nat.Partrec.Code.rfind'`).  On input
  `Nat.pair a m`, `rfind f` returns the least `m' ≥ m` such that
  `f (Nat.pair a m') = 0`, provided `f (Nat.pair a i)` halts for all
  `m ≤ i ≤ m'`. -/
  | rfind (f : OracleCode)
  deriving DecidableEq, Repr

end FriedbergMuchnik
