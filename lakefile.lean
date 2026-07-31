import Lake
open Lake DSL

package «PriorityArguments» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

/-
Mathlib is used ONLY for ordinary (non-oracle) computability infrastructure:
`Primrec`/`Partrec` closure lemmas, `Nat.Partrec.Code`, and basic data
(`Nat.pair`, `Finset`).  The oracle semantics, the use theorem, Turing
reducibility, and the priority argument are project-local; the dependency
direction is documented in README.md.
-/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

/-- The shared foundation: oracle machine model, use principle, `≤ᵀ`/`CE`,
Mathlib bridge, monotone-stage approximation.  Imports nothing from either
priority argument — Lake enforces the layering the README claims. -/
@[default_target]
lean_lib «OracleComputability» where

/-- The finite-injury solution of Post's problem. -/
@[default_target]
lean_lib «FriedbergMuchnik» where

/-- The Sacks Splitting Theorem, built on the same foundation.  Does *not*
depend on `FriedbergMuchnik`; that independence is the point. -/
@[default_target]
lean_lib «SacksSplitting» where

/-- The root: the one place the two priority arguments meet. -/
@[default_target]
lean_lib «PriorityArguments» where
