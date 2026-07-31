# Finite-injury priority arguments in Lean 4

Two classical theorems of computability theory, formalized over one oracle
machine model:

```lean
theorem FriedbergMuchnik.friedberg_muchnik :
    ∃ A B : Set ℕ, CE A ∧ CE B ∧ ¬ (A ≤ᵀ B) ∧ ¬ (B ≤ᵀ A)

theorem SacksSplitting.sacks_splitting :
    ∀ A : Set ℕ, CE A → ¬ ComputableSet A →
      ∃ A₀ A₁ : Set ℕ, CE A₀ ∧ CE A₁ ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = A ∧
        ¬ (A ≤ᵀ A₀) ∧ ¬ (A ≤ᵀ A₁)
```

**Friedberg–Muchnik** (1956/57), solving Post's problem: two incomparable
c.e. Turing degrees. **Sacks Splitting** (1963), in its
splitting-with-non-reducibility form: every non-computable c.e. set splits
into two c.e. halves, neither of which computes it.

`lake build` succeeds with zero `sorry`. Every headline theorem reports
exactly `[propext, Classical.choice, Quot.sound]`.

Lowness of the Sacks halves — the full theorem's additional conclusion —
needs infinite-injury machinery and is deliberately out of scope.

## Structure

```
OracleComputability/     the machine model, the use principle, ≤ᵀ / CE,
        │                the Mathlib bridge, the restraint mechanism
        ├───────────────┐
        ▼               ▼
FriedbergMuchnik/   SacksSplitting/
        └───────┬───────┘
                ▼
       PriorityArguments.lean
```

Four Lake libraries. `FriedbergMuchnik` and `SacksSplitting` are
**siblings**: neither imports the other, and the build enforces that.

That independence is the development's main structural claim, not a
tidiness point. Sacks splitting was written against this foundation as a
test of whether the foundation *is* one, and it turned out to need nothing
from Friedberg–Muchnik's proof — only from the shared layer. The import
graph is the evidence, and `PriorityArguments.lean` is the single place the
two theorems meet: Friedberg–Muchnik produces a c.e. non-computable set,
which is exactly the hypothesis Sacks splitting consumes, so the first
theorem certifies that the second is not vacuous.

| Library | Content |
|---|---|
| `OracleComputability` | `OracleCode` syntax and its numbering; the fuel-bounded evaluator `run` recording output **and use**; the use principle `run_halt_mono` and `run_halt_unique`; `≤ᵀ`, `CE`, `ComputableSet` with reflexivity and transitivity; the Mathlib bridge; `nrun_primrec`; monotone-stage approximation with `run_halt_limit_of_restraint`; `Priority.lean`; `PrimrecTools.lean`. |
| `FriedbergMuchnik` | The stage machine with per-requirement records; the priority discipline; the **rank** injury argument; the ten-field state invariant; satisfaction of every requirement; `CE` of both sets. |
| `SacksSplitting` | `A`'s enumeration as a watchable stage sequence; agreement length and cumulative restraint; the routing machine; the priority induction; `CE` of both halves. |
| `PriorityArguments` | The two theorems composed. |

## What the second theorem cost

`SacksSplitting/STATUS.md` carries the component-by-component **reuse
inventory**, written before any Sacks construction code existed: for every
foundation component, a verdict of *reused as-is*, *generalized*, or
*rebuilt*, with the reason. Two findings are worth the front page.

**The foundation transferred whole.** In particular
`run_halt_limit_of_restraint` — preservation of a computation whose use is
protected — was already stated generically in the stage sequence, so the
restraint argument at the heart of Sacks reuses it verbatim. And
`run_halt_unique` turned out to matter more for Sacks than for
Friedberg–Muchnik: it is what makes "the use of the limit computation at
`y`" a well-defined number, which is what bounds the restraint. Recording
the use rather than just the output was a design decision made for the
first theorem, and it paid off for a theorem it was not designed for.

**The priority layer did not transfer, and no generalization would have
helped.** Friedberg–Muchnik's injury induction counts *events*: a
requirement's record has a rank in `{0,1,2}`, receiving attention raises
it, so once the superiors go quiet it acts at most twice more. A splitting
requirement generates no events — it never acts, and its restraint moves
continuously with the length of agreement. Its replacement is a three-part
induction along the priority order (bounded restraints below `j` ⇒ finite
injury to `j` ⇒ `j` satisfied ⇒ `j`'s restraint bounded). The two files
share a shape and no content.

The one genuinely new piece of mathematics is
`SacksSplitting.unsatisfied_requirement_computes`: if a requirement is
never injured after some stage and the reduction nevertheless computes
`χ_A` everywhere, then `A` is computable. Friedberg–Muchnik has no
analogue — its requirements are satisfiable because their witnesses are
fresh, which is a property of the construction, whereas a splitting
requirement is satisfiable only because of a property of the *given* set.

## Building

```
lake exe cache get   # fetch Mathlib olean cache (first time)
lake build
```

Toolchain: Lean 4.26.0, Mathlib `v4.26.0`. A handful of declarations in the
two `CE.lean` files carry raised `maxHeartbeats`: their `Primrec`
unifications walk the `Primcodable` pairing encodings.
`FriedbergMuchnik/CE.lean` is the slow one at roughly 100s; everything else
compiles quickly.

## Textbook correspondence

Soare, *Recursively Enumerable Sets and Degrees* (1987). The use principle
is VII.2; Friedberg–Muchnik follows VII.2 with requirements
`R_{2e} : A ≠ Φ_e^B`, `R_{2e+1} : B ≠ Φ_e^A`; Sacks splitting follows
VII.3, with the cumulative (running-maximum) restraint made explicit,
because the raw stage restraint is not monotone and a restraint that can
drop preserves nothing.

## Status documents

* `STATUS.md` — Friedberg–Muchnik's completion report.
* `SacksSplitting/STATUS.md` — the reuse inventory and the honest
  accounting of what transferred.
* `STATUS_ONE.md` — an independent verification report of an earlier
  Friedberg–Muchnik commit, kept as a record of that check.
* `paper/` — a paper drafted when this repository held only
  Friedberg–Muchnik. Its file paths have been updated, but it does not yet
  cover the second theorem or the foundation/clients split; that rewrite is
  the obvious next job.
