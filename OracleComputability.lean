/-
# Oracle computability: the shared foundation

This library is the part of the development that is not about any
particular theorem.  It fixes a machine model of oracle computation and
proves the facts that *every* priority argument over that model needs.
Both `FriedbergMuchnik` and `SacksSplitting` are built on it, and neither
imports the other.

Dependency direction, strictly one way:

```
Mathlib (ordinary, non-oracle computability: Primrec/Partrec closure)
        │
        ▼
OracleComputability/MathlibBridge.lean, RunPrimrec.lean
        │           (the only two files importing Mathlib computability)
        ▼
OracleComputability/…    (project-local oracle semantics)
        │
        ▼
FriedbergMuchnik/ , SacksSplitting/    (the priority arguments)
```

Contents:

* `OracleCode` — syntax of oracle programs (Kleene schemata + `query`);
* `FiniteEval` — the fuel-bounded evaluator against *partial* oracles,
  recording output **and use**;
* `Use` — the use principle (`run_halt_mono`) and its corollaries,
  including `run_halt_unique`;
* `InfiniteEval` — semantics against a total oracle; finite↔infinite
  correspondence;
* `Numbering` — the effective bijection `ℕ ≃ OracleCode` (enumeration
  adequacy);
* `Reducibility` — `≤ᵀ`, `CE`, `ComputableSet` and their hygiene lemmas;
* `Composition` — `≤ᵀ` is transitive, by query substitution;
* `MathlibBridge` — transfer of ordinary computability into the model;
* `RunPrimrec` — the evaluator is primitive recursive (`nrun_primrec`),
  plus the generic `Primrec` helpers a stage function needs;
* `Approximation` — monotone finite stages, snapshots, and **the restraint
  mechanism** (`run_halt_limit_of_restraint`), the lemma both priority
  arguments turn on.
-/
import OracleComputability.OracleCode
import OracleComputability.FiniteEval
import OracleComputability.Use
import OracleComputability.InfiniteEval
import OracleComputability.Numbering
import OracleComputability.Reducibility
import OracleComputability.Composition
import OracleComputability.MathlibBridge
import OracleComputability.RunPrimrec
import OracleComputability.Priority
import OracleComputability.Approximation
import OracleComputability.PrimrecTools
