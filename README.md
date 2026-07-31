# The Sacks Splitting Theorem in Lean 4, on the Friedberg–Muchnik foundation

**Every non-computable c.e. set splits into two c.e. halves, neither of
which computes it.**

```lean
theorem sacks_splitting :
    ∀ A : Set ℕ, CE A → ¬ ComputableSet A →
      ∃ A₀ A₁ : Set ℕ, CE A₀ ∧ CE A₁ ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = A ∧
        ¬ (A ≤ᵀ A₀) ∧ ¬ (A ≤ᵀ A₁)
```

`lake build` succeeds with zero `sorry`, and
`#print axioms SacksSplitting.sacks_splitting` reports exactly
`[propext, Classical.choice, Quot.sound]` — the same footprint as
Friedberg–Muchnik's own final theorem.

This is the **splitting-with-non-reducibility core** of Sacks's theorem.
Lowness of the halves — the full theorem's additional conclusion — needs
infinite-injury machinery and is deliberately out of scope.

## The point of the exercise

This development is a **client** of
[`friedberg-muchnik-lean`](../friedberg-muchnik-lean), taken as a package
dependency (`require FriedbergMuchnik from "../friedberg-muchnik-lean"`),
never by copying files.  The oracle-program syntax and its numbering, the
step-indexed evaluator with use recording, the use principle, the
monotone-stage approximation layer with its restraint lemma, the
`≤ᵀ`/`CE`/`ComputableSet` vocabulary and the Mathlib bridge are all
imported.

`SacksSplitting/STATUS.md` carries the component-by-component **reuse
inventory**: for every major FM component, a verdict of *reused as-is*,
*generalized*, or *rebuilt*, with the reason.  It is the headline
deliverable, not an appendix.

Two-sentence version: the whole **foundation** transferred unchanged, and
`run_halt_limit_of_restraint` — the restraint/use-protection lemma — is
already stated generically enough to serve Sacks verbatim; the whole
**priority layer** had to be rebuilt, because FM's finite-injury argument
counts discrete events (a requirement receiving attention) and a splitting
requirement never acts.

## Files

| File | Content |
|---|---|
| `Basic.lean` | Turns FM's existential `CE A` into an explicit `⊆`-monotone stage enumeration the construction can watch — a step FM never needed, since it only ever *produced* `CE` facts. |
| `Requirements.lean` | `N_j : A ≠ Φ_{j/2}^{A_{j%2}}`; the agreement test (FM's `convCheck` with a different comparison value), the length of agreement, and the restraint. |
| `Construction.lean` | The routing stage machine and its two invariants (halves disjoint, union = current stage of `A`) — which replace FM's ten-field `ConsInv`. |
| `CE.lean` | The construction is primitive recursive; both halves are `CE`; and the decision procedure that makes the non-computability hypothesis usable. |
| `FiniteInjury.lean` | The priority induction: routing ⇒ injury finiteness ⇒ satisfaction ⇒ restraint boundedness, by strong induction on the priority. |
| `Main.lean` | The theorem, plus non-vacuity: FM's own `Aset` satisfies the hypotheses and splits. |

## The one genuinely new lemma

`unsatisfied_requirement_computes` (`FiniteInjury.lean`):

> If requirement `N_j` is never injured after some stage, and
> `Φ_{j/2}^{A_{j%2}}` nevertheless computes `χ_A` everywhere, then
> `ComputableSet A`.

To decide `y ∈ A`, search for a stage past the last injury whose agreement
length exceeds `y`, and report `y ∈ A_s`.  Such a stage exists because the
reduction is total; the answer is right because past the last injury the
agreeing computation is *frozen* (FM's `run_halt_limit_of_restraint`), so
it is the true value; and the search is effective because the whole
construction is primitive recursive.

FM has no analogue.  Its requirements are satisfiable because their
witnesses are fresh — a property of the construction.  A splitting
requirement is satisfiable only because of a property of the *given* set,
and this lemma is where that hypothesis is spent.

You can watch the hypothesis being needed.  `enumSet 0` is the set
enumerated by program number `0`, which halts everywhere — so it is `ℕ`,
which is computable, and the theorem does not apply.  Evaluating the
construction on it shows requirement `8`'s restraint growing without
bound:

```lean
#eval (List.range 14).map fun s => Rest 0 s 8
-- [0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 9, 10, 11, 12]
```

That divergence is exactly what `restraint_bounded` rules out, and it is
ruled out only by non-computability of `A`.

## Changes made to the FM repo

Two, both committed separately there, both required:

1. **`FriedbergMuchnik.lean` imported a file that does not exist**
   (`Foundation.MathlibOracleBridge`, added by FM's last commit), so
   `lake build` failed outright on a clean checkout and FM could not be
   depended on at all.  Stray import removed.
2. **Three generic `Primrec` helpers were `private`**
   (`primrec_find?`, `primrec_memDecide`, `primrec_snapshotOf` in
   `FriedbergMuchnik/CE.lean`).  Nothing about them mentions the FM
   construction — they are what *any* priority construction needs to
   certify its stage function computable — but `private` made them
   invisible downstream.  De-privatized and docstringed.

No FM lemma needed to be generalized mathematically.

## Building

```
lake build
```

Toolchain: Lean 4.26.0, Mathlib `v4.26.0` (inherited from FM, same
revision).  Four declarations in `CE.lean` carry raised `maxHeartbeats`:
their `Primrec` unifications walk the `Primcodable` pairing encodings, the
same effect FM documents for its own `CE.lean`.

## Textbook correspondence

Soare, *Recursively Enumerable Sets and Degrees* (1987), VII.3: the
routing rule, the length-of-agreement restraint and the three-part
induction follow Soare's presentation, with the cumulative (running
maximum) restraint made explicit because the raw stage restraint is not
monotone and a restraint that can drop preserves nothing.
