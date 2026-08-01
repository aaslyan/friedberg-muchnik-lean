import SacksSplitting.Basic
import SacksSplitting.Requirements
import SacksSplitting.Construction
import SacksSplitting.CE
import SacksSplitting.FiniteInjury
import SacksSplitting.Main

/-!
Root module of the Sacks Splitting formalization.

The development is a *client* of `FriedbergMuchnik`: the oracle-program
syntax and numbering, the step-indexed evaluator with use recording, the
use principle, the monotone-stage approximation layer with its restraint
lemma, the `≤ᵀ`/`CE`/`ComputableSet` vocabulary, and the Mathlib bridge are
all imported from there.  See `SacksSplitting/STATUS.md` for the
component-by-component reuse inventory.
-/
