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
  hygiene lemmas.
-/
import FriedbergMuchnik.Foundation.OracleCode
import FriedbergMuchnik.Foundation.FiniteEval
import FriedbergMuchnik.Foundation.Use
import FriedbergMuchnik.Foundation.InfiniteEval
import FriedbergMuchnik.Foundation.Numbering
import FriedbergMuchnik.Foundation.Reducibility
