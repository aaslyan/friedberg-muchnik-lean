/-
Root module of the Friedberg–Muchnik formalization.

Foundation layer (see README.md for the architecture and the milestone
gate):
* `OracleCode` — syntax of oracle programs (no imports);
* `FiniteEval` — fuel-bounded evaluation with output/use recording against
  partial oracles;
* `Use` — the use principle (master monotonicity/agreement theorem) and
  determinism;
* `InfiniteEval` — semantics against a total oracle as existential closure;
  finite-to-infinite correspondence;
* `Numbering` — effective bijection `ℕ ≃ OracleCode` (enumeration
  adequacy);
* `Reducibility` — the project's `≤ᵀ`, `CE`, `ComputableSet` vocabulary and
  hygiene lemmas;
* `MathlibBridge` — embedding of Mathlib's partial recursive codes with
  semantic preservation; transfer of `Nat.Partrec` witnesses and c.e.-ness
  into the local model (the only file importing Mathlib computability).
-/
import FriedbergMuchnik.Foundation.OracleCode
import FriedbergMuchnik.Foundation.FiniteEval
import FriedbergMuchnik.Foundation.Use
import FriedbergMuchnik.Foundation.InfiniteEval
import FriedbergMuchnik.Foundation.Numbering
import FriedbergMuchnik.Foundation.Reducibility
import FriedbergMuchnik.Foundation.MathlibBridge
import FriedbergMuchnik.Foundation.RunPrimrec
import FriedbergMuchnik.Approximation
