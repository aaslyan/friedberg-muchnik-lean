/-
Root module of the Friedberg–Muchnik formalization.

The oracle model, the use principle, `≤ᵀ`/`CE`, the Mathlib bridge and the
monotone-stage approximation layer live in the `OracleComputability`
library, which this one is a client of; see `OracleComputability.lean` for
the dependency direction.  What follows is only the priority argument:

* `Construction` — the stage machine: per-requirement records, one
  attention per stage, freshness counter;
* `StageDynamics` — `attended` and the priority discipline; the
  `step_cases` trichotomy;
* `FiniteInjury` — the rank argument: once superiors are quiet a
  requirement is attended at most twice more;
* `Invariants` — the ten-field `ConsInv` of every reachable state;
* `Requirements` — satisfaction of every `R_e`/`S_e`;
* `CE` — the constructed sets are computably enumerable;
* `Main` — the theorem.
-/
import OracleComputability
import FriedbergMuchnik.Construction
import FriedbergMuchnik.StageDynamics
import FriedbergMuchnik.FiniteInjury
import FriedbergMuchnik.Invariants
import FriedbergMuchnik.Requirements
import FriedbergMuchnik.CE
import FriedbergMuchnik.Main
