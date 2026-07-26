# The Friedberg–Muchnik theorem is fully formalized. ✅

```
theorem friedberg_muchnik :
    ∃ A B : Set ℕ, CE A ∧ CE B ∧ ¬ (A ≤ᵀ B) ∧ ¬ (B ≤ᵀ A)
```

**`lake build` succeeds, zero `sorry`, and `#print axioms friedberg_muchnik`
reports exactly `[propext, Classical.choice, Quot.sound]`** — nothing else.
Nine commits, ending with `5db3ed3`.

The final push (CE) took real engineering: the construction is mirrored by a
parallel implementation on plain tuples with three **named state-builders**
(`idleSt`/`appointSt`/`actSt`) and list surgeries as maps over `List.range`;
a simulation theorem ties it to the real machine, and the `Primrec`
derivation then composes only small named heads. The instructive failure
along the way: assembling it as one large combinator term made failed
`Primrec X =?= Primrec Y` unifications fall back into the `Primcodable`
pairing encodings — the elaborator symbolically evaluating `Nat.sqrt` for
tens of millions of heartbeats. Confining each tuple-sized comparison to its
own lemma fixed it; two declarations still carry raised heartbeat budgets
(~2–3 min of the build), noted in the README.

## Where the project stands against the agreed "done" criteria

- ✅ Foundation gate, all 8 items (own oracle model; use principle;
  numbering; Mathlib bridge both directions; `evaln_prim` analog)
- ✅ Corrected design throughout: ⊆-monotone `Finset` stages, output+use
  recording, inductive injury finiteness (the rank argument — attention
  bumps a 0–2 rank, so ≤ 2 attentions once superiors are quiet)
- ✅ Priority argument: step trichotomy, ten-field invariant, satisfaction
  of every `R_e`/`S_e`, both non-reducibilities
- ✅ `CE` of both sets via the computable construction; final theorem in
  clean vocabulary, every file docstringed with its Soare VII.2
  correspondence
- ⬜ One open item: **`≤ᵀ` composition/transitivity** (query-substitution
  operator) — the off-critical-path hygiene extension making the project's
  `≤ᵀ` recognizably standard, plus the optional halting-set non-vacuity
  certificate. A self-contained follow-up.
