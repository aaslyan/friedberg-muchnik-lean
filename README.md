# Friedberg–Muchnik in Lean 4

A formalization of the Friedberg–Muchnik theorem: **there exist computably
enumerable sets `A, B ⊆ ℕ` with `¬(A ≤ᵀ B)` and `¬(B ≤ᵀ A)`** — two
incomparable c.e. Turing degrees, solving Post's problem, by the classical
finite-injury priority argument.

Everything is finitary ("Track B"): computations are run by a fuel-bounded
evaluator against *finite* oracle information, the two sets are built as
monotone sequences of finite sets, and the infinite objects appear only at
the very end via the use principle.

## Corrected design decisions

This project deliberately deviates from the original brief in three places
where the brief was wrong or underestimated; these are load-bearing.

1. **Stage approximations are `⊆`-monotone finite sets, not prefix-monotone
   strings.** `Astage : ℕ → Finset ℕ` with `Astage s ⊆ Astage (s+1)`, limit
   `n ∈ A ↔ ∃ s, n ∈ Astage s`. A bit may flip `false → true` (enumeration)
   but never back. Prefix-monotone `List Bool` stages would freeze every bit
   at first write, making the limit sets computable — and computable sets
   reduce to every oracle (`ComputableSet.turingReducible`), contradicting
   the theorem. `List Bool` survives only as a *snapshot* of a stage set up
   to a bound, fed to the finite evaluator.

2. **The evaluator records output *and* use.** `run k O c x` returns
   `halt ⟨output, use⟩`, `stuck` (insufficient oracle information — distinct
   from divergence), or `timeout`. The use principle is stated for *partial*
   oracles once (`run_halt_mono`) and everything else — restraint
   preservation, snapshot adequacy, finite↔infinite transfer, determinism —
   is a corollary.

3. **Injury counts are proved finite inductively** (each requirement acts
   finitely often given that all higher-priority ones do), with no
   closed-form bound baked into any statement.

## Architecture and dependency direction

```
Mathlib (ordinary, non-oracle computability: Primrec/Partrec closure)
        │
        ▼
FriedbergMuchnik/Foundation/MathlibBridge.lean     (the ONLY file importing
        │                                           Mathlib computability)
        ▼
FriedbergMuchnik/Foundation/…  (project-local oracle semantics)
        │
        ▼
priority argument (Approximation / Requirements / Construction /
                   FiniteInjury / Main)
```

The oracle model, `≤ᵀ`, and `CE` are project-local, so the priority proof
cannot be contaminated by Mathlib's internal coding decisions; Mathlib is
used strictly to discharge "this explicit stage function is computable"
obligations, transferred through the bridge.

### Foundation layer

| File | Content | Status |
|---|---|---|
| `OracleCode.lean` | Syntax only: Kleene schemata + `query`. No imports. | ✅ builds |
| `FiniteEval.lean` | `run : fuel → PartOracle → OracleCode → ℕ → RunResult`, mirroring `Nat.Partrec.Code.evaln`'s fuel discipline; named step lemmas. | ✅ builds |
| `Use.lean` | **Use principle** (`run_halt_mono`, master form for partial oracles); fuel monotonicity, oracle extension, consistency transfer, determinism. | ✅ builds |
| `InfiniteEval.lean` | `Computes` as existential closure over fuel; uniqueness; finite↔infinite correspondence (`computes_iff_initialSegment`). | ✅ builds |
| `Numbering.lean` | Explicit bijection `ℕ ≃ OracleCode`, both round-trips proved — enumeration adequacy for requirement indexing. | ✅ builds |
| `Reducibility.lean` | `≤ᵀ`, `CE`, `ComputableSet`; reflexivity; computable ⇒ reducible to everything. | ✅ builds |
| `MathlibBridge.lean` | See gate items 2–4, 8 below. | ⬜ next |

### Foundation milestone gate

The priority construction does not start until all of these compile with
zero `sorry`:

1. ✅ effective encoding/decoding of oracle programs (`Numbering.lean`)
2. ⬜ embedding `Nat.Partrec.Code → OracleCode` (query-free image)
3. ⬜ semantic preservation of that embedding (`run`/`evaln` correspondence)
4. ⬜ transfer: `Nat.Partrec f` ⇒ `f` realized by a local oracle-free code
5. ✅ enumeration adequacy for the project's `≤ᵀ` (`Numbering.lean`)
6. ✅ finite-to-infinite computation correspondence (`InfiniteEval.lean`)
7. ✅ use principle: preservation under oracle agreement below the recorded
   use (`Use.lean`)
8. ⬜ `run` (on snapshot oracles) is computable in Mathlib's sense — the
   analog of Mathlib's `evaln_prim`, needed before "the constructed sets
   are c.e." can be discharged; the largest single bridge item

Off the critical path but part of "done": closure of `≤ᵀ` under
composition/transitivity via a query-substitution operator (what makes the
project-local `≤ᵀ` recognizably *standard* Turing reducibility), and a
non-vacuity certificate (the model's own halting set is `CE` but not
`ComputableSet`).

## Building

```
lake exe cache get   # fetch Mathlib olean cache (first time)
lake build
```

Toolchain: Lean 4.26.0, Mathlib `v4.26.0`. Zero `sorry` policy: every commit
builds with no `sorry`/`admit`/added axioms.

## Textbook correspondence

Soare, *Recursively Enumerable Sets and Degrees* (1987): the use principle
is VII.2; the construction and injury bookkeeping follow VII.2's
Friedberg–Muchnik presentation with requirements
`R_{2e} : A ≠ Φ_e^B`, `R_{2e+1} : B ≠ Φ_e^A` in priority order. Each
requirement/injury lemma cites the classical step it formalizes in its
docstring.
