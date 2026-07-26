# Drafting Notes

## Repository Structure

The Lean development is rooted at `FriedbergMuchnik.lean`, which imports:

- Foundation: `OracleCode`, `FiniteEval`, `Use`, `InfiniteEval`, `Numbering`,
  `Reducibility`, `MathlibBridge`, `RunPrimrec`.
- Priority construction: `Approximation`, `Construction`, `StageDynamics`,
  `FiniteInjury`, `Invariants`, `Requirements`, `CE`, `Main`.

Total Lean source counted locally: 17 Lean files, 4024 lines including
comments and whitespace.

## Verified Artifact Facts

Checked locally on this workspace:

- `lake build` completed successfully: `Build completed successfully (811 jobs).`
- Temporary check file:

  ```lean
  import FriedbergMuchnik.Main

  #check FriedbergMuchnik.friedberg_muchnik
  #print axioms FriedbergMuchnik.friedberg_muchnik
  ```

  Output theorem type:

  ```lean
  ∃ A B,
    FriedbergMuchnik.CE A ∧
      FriedbergMuchnik.CE B ∧
        ¬FriedbergMuchnik.TuringReducible A B ∧
        ¬FriedbergMuchnik.TuringReducible B A
  ```

  Axiom footprint:

  ```text
  [propext, Classical.choice, Quot.sound]
  ```

- `rg -n "sorry|admit|axiom|unsafe|opaque|extern|implemented_by|native_decide"`
  only found documentation mentions of `sorry`/`axiom`, not Lean declarations.
- Lean toolchain: `leanprover/lean4:v4.26.0`.
- Mathlib revision from `lake-manifest.json`:
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- Repository license: no `LICENSE` file found.
- CI: no `.github` workflow files found.

## Exact Theorem Inventory

Final theorem:

- `FriedbergMuchnik.friedberg_muchnik` in `FriedbergMuchnik/Main.lean`.

Nonreducibility:

- `R_satisfied`, `S_satisfied`, `not_A_le_B`, `not_B_le_A` in
  `FriedbergMuchnik/Requirements.lean`.

Computably enumerable sets:

- `ce_Aset`, `ce_Bset` in `FriedbergMuchnik/CE.lean`.

Finite injury:

- `rank`, `reqRank`, `reqRank_incr`, `quiet_above`, `exists_stable`,
  `stable_not_requires` in `FriedbergMuchnik/FiniteInjury.lean`.

Invariants:

- `ConsInv`, `consInv_stage` in `FriedbergMuchnik/Invariants.lean`.

Stage construction:

- `ReqState`, `ConsState`, `convCheck`, `requiresAttention`, `stepAt`,
  `stepState`, `stageState`, `AstageF`, `BstageF`, `Aset`, `Bset` in
  `FriedbergMuchnik/Construction.lean`.

Oracle semantics:

- `OracleCode` in `Foundation/OracleCode.lean`.
- `HaltData`, `RunResult`, `PartOracle`, `run` in `Foundation/FiniteEval.lean`.
- `run_halt_mono` in `Foundation/Use.lean`.
- `Computes`, `computes_iff_initialSegment` in
  `Foundation/InfiniteEval.lean`.
- `TuringReducible`, `CE`, `ComputableSet` in
  `Foundation/Reducibility.lean`.

Computability bridge:

- `embed`, `run_embed`, `partrec_realized`, `ce_of_partrec_dom` in
  `Foundation/MathlibBridge.lean`.
- `nrun`, `nrun_primrec` in `Foundation/RunPrimrec.lean`.
- `stageN`, `encSt_stepState`, `encSt_stage` in `CE.lean`.

## Semantic Model Summary

The project uses a local oracle-program language with ordinary partial
recursive constructors and one oracle query constructor. A bounded evaluator
`run` executes a program against a partial oracle `ℕ → Option Bool`. A query
answered by `some b` returns `1` or `0`; a query answered by `none` produces
`RunResult.stuck`; fuel exhaustion produces `RunResult.timeout`.

A halting result stores `HaltData.output` and `HaltData.use`. The convention
is strict: if query position `p` is used, the recorded use is at least `p + 1`;
query-free computations have use `0`.

`TuringReducible A B` means there is an `OracleCode` computing the
characteristic function of `A` from the total characteristic oracle of `B`.
`CE A` means `A` is the halting domain of a program run with the empty
oracle.

## Open Foundational Issues

- Transitivity/composition of the local `TuringReducible` relation is not
  currently proved in the repository.
- Equivalence with a separate established oracle-machine semantics or
  Mathlib relative computability framework is not currently proved.
- No repository license or CI workflow was found.

These do not affect the stated theorem, but they should be discussed as
limitations before using unqualified "Turing degree" language.

## Proposed Contribution Claims

Defensible claims:

- A Lean 4 formalization of the Friedberg-Muchnik mutual nonreducibility
  theorem in a project-local oracle-machine model.
- A direct formalization of a finite-injury priority construction with
  explicit witnesses, restraints, initialization, attention, finite rank,
  and eventual quietness.
- A finitary oracle semantics with recorded use and a machine-checked
  agreement-below-use theorem.
- A proof that the constructed limit sets are c.e. using a primitive-recursive
  encoded construction and simulation theorem.

Claims to avoid or qualify:

- "First formalization" unless a broader literature search supports it.
- "Incomparable Turing degrees" without a caveat about local reducibility
  transitivity.
- "Standard Turing reducibility is fully developed internally"; it is not.
- "Constructive theorem"; the axiom footprint includes classical choice.

## Candidate Related Work

- Friedberg's 1957 PNAS solution of Post's problem.
- Muchnik's 1956/1958 solution of the reducibility problem.
- Soare's textbook on recursively enumerable sets and degrees.
- Carneiro's Lean/mathlib formalization of computability via partial recursive
  functions.
- Mathlib documentation for `Partrec` and `PartrecCode`.
- Isabelle AFP universal Turing machine and computability entries.
- Coq formalization of Turing categories / abstract computability.

