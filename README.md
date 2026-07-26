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
obligations, transferred through the bridge layer (`MathlibBridge.lean`
and `RunPrimrec.lean` — the only two files importing Mathlib
computability).

### Foundation layer

| File | Content | Status |
|---|---|---|
| `OracleCode.lean` | Syntax only: Kleene schemata + `query`. No imports. | ✅ builds |
| `FiniteEval.lean` | `run : fuel → PartOracle → OracleCode → ℕ → RunResult`, mirroring `Nat.Partrec.Code.evaln`'s fuel discipline; named step lemmas. | ✅ builds |
| `Use.lean` | **Use principle** (`run_halt_mono`, master form for partial oracles); fuel monotonicity, oracle extension, consistency transfer, determinism. | ✅ builds |
| `InfiniteEval.lean` | `Computes` as existential closure over fuel; uniqueness; finite↔infinite correspondence (`computes_iff_initialSegment`). | ✅ builds |
| `Numbering.lean` | Explicit bijection `ℕ ≃ OracleCode`, both round-trips proved — enumeration adequacy for requirement indexing. | ✅ builds |
| `Reducibility.lean` | `≤ᵀ`, `CE`, `ComputableSet`; reflexivity; computable ⇒ reducible to everything. | ✅ builds |
| `Composition.lean` | Query substitution `subst` + simulation ⇒ `≤ᵀ` transitivity (`≤ᵀ` is a preorder). | ✅ builds |
| `MathlibBridge.lean` | `embed` + semantic preservation (`run_embed`); `Partrec` and c.e. transfer. | ✅ builds |
| `RunPrimrec.lean` | `run` is primitive recursive in Mathlib's sense (`nrun_primrec`, the `primrec_evaln` analog), by memo-table strong recursion on ℕ-encoded codes/results. | ✅ builds |
| `../Approximation.lean` | Monotone `Finset` stages, stabilization, snapshots, the restraint mechanism and true-stage lemmas. | ✅ builds |

### Priority argument

| File | Content | Status |
|---|---|---|
| `Construction.lean` | The stage machine: per-requirement records, one attention per stage, freshness counter. | ✅ builds |
| `StageDynamics.lean` | `attended` + leastness (priority discipline), the `step_cases` trichotomy, list-change and no-upward-injury lemmas. | ✅ builds |
| `FiniteInjury.lean` | The rank argument: once superiors are quiet a requirement is attended ≤ 2 more times; `quiet_above`, stabilization package. | ✅ builds |
| `Invariants.lean` | Ten-field `ConsInv` (freshness, distinctness, witness/restraint discipline, the preserved computation), by induction over the three transitions. | ✅ builds |
| `Requirements.lean` | Satisfaction of every `R_e`/`S_e`; `not_A_le_B`, `not_B_le_A`. | ✅ builds |
| `CE.lean` | Parallel tuple-implementation of the construction + simulation + `Primrec` derivation ⇒ `CE Aset`, `CE Bset`. | ✅ builds |
| `Main.lean` | **`friedberg_muchnik : ∃ A B, CE A ∧ CE B ∧ ¬(A ≤ᵀ B) ∧ ¬(B ≤ᵀ A)`** | ✅ builds |

**The theorem is fully proved.** `#print axioms friedberg_muchnik` reports
only `propext`, `Classical.choice`, `Quot.sound` — no `sorry`, no added
axioms.

Build note: two declarations in `CE.lean` (`primrec_reqAttN` and the
builder lemmas) carry raised `maxHeartbeats` — their `Primrec`
unifications walk through the `Primcodable` pairing encodings and take a
couple of minutes; everything else compiles quickly.

### Foundation milestone gate

The priority construction does not start until all of these compile with
zero `sorry`:

1. ✅ effective encoding/decoding of oracle programs (`Numbering.lean`)
2. ✅ embedding `Nat.Partrec.Code → OracleCode` (query-free image)
3. ✅ semantic preservation of that embedding (`run_embed`: running an
   embedded code against *any* oracle is `evaln`, lifted)
4. ✅ transfer: `Nat.Partrec f` ⇒ `f` realized by a local oracle-free code
   (`partrec_realized`, `ce_of_partrec_dom`)
5. ✅ enumeration adequacy for the project's `≤ᵀ` (`Numbering.lean`)
6. ✅ finite-to-infinite computation correspondence (`InfiniteEval.lean`)
7. ✅ use principle: preservation under oracle agreement below the recorded
   use (`Use.lean`)
8. ✅ `run` (on snapshot oracles) is computable in Mathlib's sense
   (`nrun_primrec` — the `evaln_prim` analog; memo-table strong recursion
   with the snapshot as parameter, codes and results as naturals)

**The foundation gate is closed** — the priority construction is unblocked.

Off the critical path but part of "done" — now closed:

* ✅ closure of `≤ᵀ` under composition: **transitivity**
  (`TuringReducible.trans`, `Foundation/Composition.lean`) via the
  query-substitution operator `subst` and its simulation theorem; with
  reflexivity, the project's `≤ᵀ` is a preorder (`Trans` instance);
* ✅ non-vacuity: neither constructed set is computable
  (`Aset_not_computable` / `Bset_not_computable`, `Main.lean`) — so the
  theorem certifies in-model that c.e. strictly exceeds computable.

## Building

```
lake exe cache get   # fetch Mathlib olean cache (first time)
lake build
```

Toolchain: Lean 4.26.0, Mathlib `v4.26.0`. Zero `sorry` policy: every commit
builds with no `sorry`/`admit`/added axioms; the final theorem's axiom
footprint is `propext`, `Classical.choice`, `Quot.sound`.

## Textbook correspondence

Soare, *Recursively Enumerable Sets and Degrees* (1987): the use principle
is VII.2; the construction and injury bookkeeping follow VII.2's
Friedberg–Muchnik presentation with requirements
`R_{2e} : A ≠ Φ_e^B`, `R_{2e+1} : B ≠ Φ_e^A` in priority order. Each
requirement/injury lemma cites the classical step it formalizes in its
docstring.
