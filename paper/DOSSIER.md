# Fact dossier — Friedberg–Muchnik and Sacks Splitting in Lean 4

Collected 2026-07-31 against repository HEAD `833d0fc` (branch `master`).
This document is **not** a paper. It is the frozen evidence base a paper is
to be written from. No prose, no argument, no promotion of proposals into
results.

**Evidence tags.** Every statement carries exactly one.

| Tag | Meaning |
|---|---|
| `[VERIFIED-LEAN]` | Read from, or executed against, the Lean sources in this repository at `833d0fc`. |
| `[VERIFIED-PRIMARY]` | Verified against original papers, publisher records, or authoritative library sources. |
| `[MEASURED]` | Objectively measured on the machine described in Part 8. |
| `[ENGINEERING]` | An implementation design decision, as recorded in the sources or reconstructible from them. |
| `[RELATED]` | Prior work. |
| `[OPEN]` | Unresolved; needs evidence before use. |

**Verification environment for all `[MEASURED]` items.** Apple M5, 10 cores,
32 GB RAM, macOS (Darwin 25.5.0); Lean `leanprover/lean4:v4.26.0`; Mathlib
`v4.26.0` at revision `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; Mathlib
oleans supplied by `lake exe cache get`.

---

## Part 1 — Mathematical positioning

### 1.1 The two statements, exactly as formalized

`[VERIFIED-LEAN]` `FriedbergMuchnik/Main.lean:29`:

```lean
theorem friedberg_muchnik :
    ∃ A B : Set ℕ, CE A ∧ CE B ∧ ¬ (A ≤ᵀ B) ∧ ¬ (B ≤ᵀ A)
```

`[VERIFIED-LEAN]` `SacksSplitting/Main.lean:56`:

```lean
theorem sacks_splitting :
    ∀ A : Set ℕ, CE A → ¬ ComputableSet A →
      ∃ A₀ A₁ : Set ℕ, CE A₀ ∧ CE A₁ ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = A ∧
        ¬ (A ≤ᵀ A₀) ∧ ¬ (A ≤ᵀ A₁)
```

`[VERIFIED-LEAN]` Elaborated types, printed by `#check` against the built
environment:

```
FriedbergMuchnik.friedberg_muchnik : ∃ A B, CE A ∧ CE B ∧ ¬A ≤ᵀ B ∧ ¬B ≤ᵀ A
SacksSplitting.sacks_splitting : ∀ (A : Set ℕ),
  CE A → ¬ComputableSet A →
  ∃ A₀ A₁, CE A₀ ∧ CE A₁ ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = A ∧ ¬A ≤ᵀ A₀ ∧ ¬A ≤ᵀ A₁
```

`[VERIFIED-LEAN]` The vocabulary is defined in
`OracleComputability/Reducibility.lean`, not imported from Mathlib:

* `TuringReducible A B := ∃ c : OracleCode, ∀ x, Computes c (charFun B) x (natOfBool (charFun A x))` (line 49);
* `CE A := ∃ c : OracleCode, ∀ x, x ∈ A ↔ ∃ k d, run k PartOracle.empty c x = .halt d` (line 58);
* `ComputableSet A := ∃ c, ∀ x, ∃ k d, run k PartOracle.empty c x = .halt d ∧ d.output = natOfBool (charFun A x)` (line 63).

### 1.2 Historical background

`[VERIFIED-PRIMARY]` Post (1944) asked whether every computably enumerable
set is either computable or Turing-complete — i.e. whether there is a c.e.
set of intermediate Turing degree. Post, *Recursively enumerable sets of
positive integers and their decision problems*, Bull. Amer. Math. Soc. 50
(1944), 284–316, DOI `10.1090/S0002-9904-1944-08111-1`.

`[VERIFIED-PRIMARY]` Friedberg (1957) and Muchnik (1956) independently
answered it positively by constructing two c.e. sets of incomparable
degrees, introducing the priority method. Friedberg, *Two recursively
enumerable sets of incomparable degrees of unsolvability (solution of Post's
problem, 1944)*, Proc. Nat. Acad. Sci. USA 43 (1957), 236–238, DOI
`10.1073/pnas.43.2.236`. Muchnik, Dokl. Akad. Nauk SSSR 108 (1956), 194–197
(Russian).

`[VERIFIED-PRIMARY]` Sacks (1963) proved the Splitting Theorem: Sacks, *On
the degrees less than 0′*, Ann. of Math. (2) 77 (1963), 211–231, with a
correction in Ann. of Math. (2) 78 (1963), 204.

`[RELATED]` Standard secondary sources for both constructions: Soare (1987);
Odifreddi (1989); Cooper (2004); Soare (2016). Full data in Part 7.

### 1.3 Why the theorems matter

`[VERIFIED-PRIMARY]` Friedberg–Muchnik settles Post's problem and shows the
c.e. degrees are not linearly ordered; the priority method it introduced is
the basic technique of the subject (Soare 1987; Lerman–Soare and Lachlan
surveys cited in the Zeng–Forster–Kirst bibliography, Part 2).

`[VERIFIED-PRIMARY]` Sacks Splitting shows every non-computable c.e. degree
is the join of two strictly smaller c.e. degrees, so no c.e. degree above
**0** is join-irreducible.

### 1.4 Exact role of finite injury

`[VERIFIED-LEAN]` In this development "finite injury" is not a single shared
lemma. It is discharged twice, by two different arguments:

* Friedberg–Muchnik, `FriedbergMuchnik/FiniteInjury.lean`: a **rank**
  argument. `rank (r : ReqState) := (if r.witness.isSome then 1 else 0) + (if r.acted then 1 else 0)`
  (line 62); `rank_le_two` (line 65); `reqRank_incr` — receiving attention
  strictly raises the rank (line 78); `quiet_above` — for every priority
  level `i` there is a stage after which nothing of priority `≤ i` is ever
  attended again (line 182), by induction along the priority order.
* Sacks Splitting, `SacksSplitting/FiniteInjury.lean`: a three-part
  simultaneous induction, because a splitting requirement never acts and so
  generates no events to count. `noInjury_of_bounded` (line 153),
  `unsatisfied_requirement_computes` (line 282), `restraint_bounded_of`
  (line 323), assembled by `restraint_bounded` (line 369).

`[VERIFIED-LEAN]` Neither argument states a closed-form injury bound; both
are pure existence-of-a-stabilization-stage statements.

### 1.5 Exact role of priority

`[VERIFIED-LEAN]` The priority order is the natural order on requirement
indices, and in both constructions it is realised by the *same* lemma:
`OracleComputability/Priority.lean:22`,
`range_find?_least : (List.range n).find? p = some i → p i = true ∧ i < n ∧ ∀ j < i, p j = false`.

`[VERIFIED-LEAN]` The two uses differ: Friedberg–Muchnik picks the least
requirement that *requires attention* (`FriedbergMuchnik/StageDynamics.lean:37`,
`attended`); Sacks picks the least requirement whose *restraint* covers an
incoming number (`SacksSplitting/Construction.lean:66`, `routeTo`).

### 1.6 Incomparability

`[VERIFIED-LEAN]` Incomparability is stated as the conjunction of two
negations of the project's `≤ᵀ`; there is no degree structure, no quotient,
and no order in the development.

`[VERIFIED-LEAN]` Non-computability of both Friedberg–Muchnik sets is
derived, not assumed: `FriedbergMuchnik/Main.lean:36,39`,
`Aset_not_computable`, `Bset_not_computable`, each one line from
`ComputableSet.turingReducible`.

`[OPEN]` The classical inference "incomparable c.e. sets ⇒ each has
intermediate degree, hence Post's problem is solved" needs `A ≤ᵀ ∅'` for
c.e. `A`. The development contains **no** jump, no halting set and no
completeness notion `[VERIFIED-LEAN]` (grep for `jump`, `halting set`, `0'`
over the project sources returns only unrelated docstring text). What is
formalized is incomparability plus non-computability; the step to
"intermediate degree" is not formalized.

### 1.7 Relationship to the Splitting Theorem

`[VERIFIED-PRIMARY]` The full Sacks Splitting Theorem (Soare's form)
additionally makes the two halves **low** and allows the non-reducibility to
be stated for a separate given non-computable set `C`.

`[VERIFIED-LEAN]` The formalized statement takes `C := A` and drops lowness.
`SacksSplitting/Main.lean:20–22` records this scope decision explicitly:
"this is the splitting-with-non-reducibility core. The full Sacks Splitting
Theorem also makes the halves *low*, which needs the infinite-injury
machinery and is deliberately out of scope here."

`[VERIFIED-LEAN]` The split is proved non-degenerate: `halfSet_ne`
(`SacksSplitting/Main.lean:68`) shows neither half equals `A`, using
reflexivity of `≤ᵀ`.

`[VERIFIED-LEAN]` Non-vacuity is proved, not assumed:
`PriorityArguments.friedbergMuchnik_set_splits` (line 46) applies
`sacks_splitting` to the Friedberg–Muchnik set `Aset` using `ce_Aset` and
`Aset_not_computable`.

### 1.8 What is constructive, what is not

`[VERIFIED-LEAN]` The *constructions* are executable Lean functions
(Part 5.4). The *verifications* are classical: every headline theorem
depends on `Classical.choice` (Part 5.1).

`[VERIFIED-LEAN]` Specific classical steps: `charFun` is a `noncomputable
def` using `Classical` decidability of set membership
(`OracleComputability/Reducibility.lean:26–29`); `SacksSplitting.limUse` is
a `noncomputable def` built with `Classical.choose`
(`SacksSplitting/FiniteInjury.lean:297–306`); `Classical.not_forall` is used
at `SacksSplitting/FiniteInjury.lean:327`. There are exactly two
`noncomputable` declarations in the whole project.

### 1.9 Where oracle computation enters

`[VERIFIED-LEAN]` `OracleCode` (`OracleComputability/OracleCode.lean:31`) is
Kleene's schemata — `zero`, `succ`, `left`, `right`, `pair`, `comp`, `prec`,
`rfind` — plus exactly one oracle primitive, `query`, which returns `1`/`0`
for membership.

`[VERIFIED-LEAN]` `run : ℕ → PartOracle → OracleCode → ℕ → RunResult`
(`OracleComputability/FiniteEval.lean:137`) is a fuel-bounded evaluator
against a *partial* oracle `PartOracle := ℕ → Option Bool`, with three
outcomes: `halt ⟨output, use⟩`, `stuck` (oracle could not answer), `timeout`
(fuel exhausted). `use` is a **strict** upper bound on queried positions;
query-free halting runs record `use = 0`.

`[VERIFIED-LEAN]` The master lemma is `run_halt_mono`
(`OracleComputability/Use.lean:170`), whose elaborated statement is:

```
∀ {k k' O O' c x d}, k ≤ k' →
  (∀ i < d.use, ∀ b, O i = some b → O' i = some b) →
  run k O c x = .halt d → run k' O' c x = .halt d
```

Note the hypothesis is one-sided: positions `≥ d.use` are unconstrained, and
positions `< d.use` where `O` had no information are unconstrained too.

### 1.10 Relationship with Turing reducibility

`[VERIFIED-LEAN]` `≤ᵀ` is reflexive (`TuringReducible.refl`,
`Reducibility.lean:70`) and transitive (`TuringReducible.trans`,
`Composition.lean:183`, by query substitution `subst`), with a `Trans`
instance (line 196); i.e. a preorder.

`[VERIFIED-LEAN]` Computable sets reduce to every oracle
(`ComputableSet.turingReducible`, `Reducibility.lean:78`).

`[VERIFIED-LEAN]` The numbering `ℕ ≃ OracleCode` is a proved bijection
(`ofNatCode_encodeCode`, `encodeCode_ofNatCode`, `Numbering.lean:75,125`), so
quantifying requirements over `ℕ` covers every program — this is what turns
"for every `e`" into "for every reduction".

`[VERIFIED-LEAN]` The relation is connected to Mathlib's oracle model in one
direction: `turingReducible_of_mathlib : MathlibTuringReducible A B → A ≤ᵀ B`
(`MathlibOracleBridge.lean:514`), by induction over `RecursiveIn` with one
`OracleCode` per constructor. Contrapositive: `not_mathlibTuringReducible`
(line 520). The converse inclusion is **not** proved `[VERIFIED-LEAN]`.

### 1.11 Relationship with c.e. degrees

`[VERIFIED-LEAN]` `CE` is the halting-domain definition (`A = W_e`) with the
empty oracle, and c.e.-ness of every constructed set is proved from the
construction's computability, not assumed: `ce_Aset`, `ce_Bset`
(`FriedbergMuchnik/CE.lean:528,551`), `ce_halfSet` (`SacksSplitting/CE.lean:315`).

`[VERIFIED-LEAN]` `ce_eq_enumSet` (`SacksSplitting/Basic.lean:137`) converts
the existential `CE A` into an explicit monotone stage enumeration
`enumSet ec`, which is what the splitting machine watches.

---

## Part 2 — Related work

### 2.1 Coq, synthetic setting (the closest precedent)

`[VERIFIED-PRIMARY]` Haoyi Zeng, Yannick Forster, Dominik Kirst, *Post's
Problem and the Priority Method in CIC*, TYPES 2024 (Copenhagen), extended
abstract, PDF at `https://www.ps.uni-saarland.de/~zeng/bachelor/TYPES_2024_Post.pdf`.
Verified by reading the PDF. Key quotations:

> "We describe our formalisation of a solution to Post's Problem using the
> priority method in synthetic computability theory. … We work in the
> Calculus of Inductive Constructions and mechanise all proofs in the Coq
> proof assistant."

> "Soare's solution to Post's problem [21] constructs a so-called low simple
> predicate directly, **rather than proving the full Friedberg-Muchnik
> theorem constructing two incomparable predicates**." (emphasis added)

> "In 2021, Andrej Bauer has posed the challenge to 'give a synthetic proof
> of Friedberg-Mucnik theorem'."

> "In this work, we consider the simplest form of the priority method, the
> finite injury priority method, as originally developed by Friedberg and
> Muchnik, which is sufficient for constructing low simple predicates."

`[VERIFIED-PRIMARY]` Consequence for positioning: the existing Coq priority
work formalizes a **low simple set**, not the Friedberg–Muchnik
two-incomparable-sets theorem. The Friedberg–Muchnik theorem is named there
as an open challenge.

`[VERIFIED-PRIMARY]` Future work stated in that abstract: "we assume the law
of excluded middle for all proofs, i.e. full classical logic. As a next step,
we plan to weaken this assumption…"

`[VERIFIED-PRIMARY]` Yannick Forster, Dominik Kirst, Niklas Mück, *Oracle
Computability and Turing Reducibility in the Calculus of Inductive
Constructions*, APLAS 2023, LNCS 14405, 155–181, Springer, DOI
`10.1007/978-981-99-8311-7_8`; arXiv `2307.15543`. Synthetic; establishes
that Turing reducibility forms an upper semilattice, transports decidability,
and is strictly more expressive than truth-table reducibility.

`[VERIFIED-PRIMARY]` Yannick Forster, Dominik Kirst, Niklas Mück, *The
Kleene-Post and Post's Theorem in the Calculus of Inductive Constructions*,
CSL 2024, LIPIcs 288, 29:1–29:20, DOI `10.4230/LIPIcs.CSL.2024.29`.
Synthetic; the Kleene–Post construction is a **finite extension** argument,
not a priority argument, and does not build c.e. sets.

`[VERIFIED-PRIMARY]` Repository `uds-psl/coq-synthetic-computability`
contains a `PostsProblem` directory with files `limit_computability.v`,
`low_simple_predicates.v`, `lowness.v`, `simpleness.v`, `step_indexing.v`,
`the_priority_method.v`, plus `TuringReducibility/OracleComputability.v`,
`PostsTheorem/KleenePostTheorem.v`, `Basic/Rice.v`, `Basic/Myhill.v`.

### 2.2 Lean / Mathlib

`[VERIFIED-PRIMARY]` Mario Carneiro, *Formalizing Computability Theory via
Partial Recursive Functions*, ITP 2019, LIPIcs 141, 12:1–12:17, DOI
`10.4230/LIPIcs.ITP.2019.12`; full version arXiv `1810.08380`. This is the
origin of Mathlib's `Primrec`/`Partrec`/`PartrecCode` infrastructure that
this development reuses.

`[VERIFIED-LEAN]` `Mathlib/Computability/TuringDegree.lean` at the pinned
revision: 177 lines; header reads "Copyright (c) 2025 Tanner Duve … Authors:
Tanner Duve, Elan Roth". Contents: `RecursiveIn (O : Set (ℕ →. ℕ))` as an
inductive relation on partial functions; `TuringReducible`,
`TuringEquivalent` as abbreviations; `TuringDegree` as the quotient;
`TuringReducible.refl/.trans`, `IsPreorder`, `TuringDegree.instPartialOrder`,
`recursiveIn_empty_iff_partrec`. Its "References" section cites Odifreddi
1989.

`[VERIFIED-LEAN]` What Mathlib's oracle file does **not** contain, checked by
reading the whole file: no use principle, no step-indexed oracle evaluation,
no oracle-relative c.e., no jump, no priority argument.

`[VERIFIED-LEAN]` Mathlib's unrelativized c.e. material lives elsewhere:
`ComputablePred` and `REPred` in `Mathlib/Computability/Halting.lean`
(lines 141, 169), with the halting problem and Rice's theorem; these are not
connected to `TuringDegree.lean`.

`[VERIFIED-LEAN]` A grep of the entire pinned Mathlib for `friedberg`,
`muchnik`, `priority argument`, `finite injury`, `use principle`, `post's
problem`, `sacks` returns **no** computability-theoretic hits (only
"Henstock–Sacks" in `Analysis/BoxIntegral`). Mathlib contains none of this
material.

`[VERIFIED-LEAN]` Mathlib does contain `Nat.Partrec.Code.primrec_evaln`
(`PartrecCode.lean:935`), `evaln_complete` (704) and `evaln_bound` (621) —
the ordinary-computability analogues this development mirrors for its oracle
evaluator.

`[OPEN]` No Lean formalization of any priority argument was found by web
search (queries covering "Lean 4 priority method / finite injury
computability 2025–2026" and GitHub-targeted searches). Absence of search
results is weak evidence; see Part 10.

### 2.3 Isabelle / AFP

`[VERIFIED-PRIMARY]` Complete list of AFP entries under Logic → Computability,
read from `isa-afp.org`: *The Busy Beaver Function* (Ramos, Hulak, de
Queiroz, 2026); *SAT is Not Solvable in Constant Time* (Shea, 2026); *The
Halting Problem is Soluble in Malament-Hogarth Spacetimes* (Stannett, 2023);
*The Cook-Levin theorem* (Balbach, 2023); *Automation of Boolos' Curious
Inference* (Benzmüller et al., 2022); *A Verified Translation of Multitape
Turing Machines into Singletape Turing Machines* (Dalvit, Thiemann, 2022);
*Diophantine Equations and the DPRM Theorem* (Bayer et al., 2022);
*Ackermann's Function Is Not Primitive Recursive* (Paulson, 2022); *Some
classical results in inductive inference of recursive functions* (Balbach,
2020); *Universal Turing Machine* (Xu, Zhang, Urban, Joosten, Regensburger,
2019); *Minsky Machines* (Felgenhauer, 2018); *Recursion Theory I*
(Nedzelsky, 2008).

`[VERIFIED-PRIMARY]` The *Universal Turing Machine* entry corresponds to Xu,
Zhang, Urban, *Mechanising Turing Machines and Computability Theory in
Isabelle/HOL*, ITP 2013; it covers recursive functions, undecidability of the
halting problem, and a universal machine.

`[OPEN]` The contents of *Recursion Theory I* (Nedzelsky, 2008) were not
verified — the AFP entry page returned 404 on two URL forms. Needed before
claiming it contains no degree theory.

`[OPEN]` No AFP entry title mentions Turing degrees, oracle computation,
priority arguments, or r.e. degrees.

### 2.4 Coq, analytic / categorical

`[VERIFIED-PRIMARY]` Polina Vinogradova, Amy P. Felty, Philip Scott,
*Formalizing Abstract Computability: Turing Categories in Coq*, LSFA 2017,
published in Electron. Notes Theor. Comput. Sci. 338 (2018), 203–218.
Verified by reading the paper's title page: all three authors are at the
University of Ottawa. It formalizes restriction/Turing categories in Coq;
it is about foundational models, not degree theory.

`[VERIFIED-PRIMARY]` **Citation error in the current repository.**
`paper/references.bib` entry `cockett2018` attributes this paper to
"Cockett, J. R. B. and Hofstra, Pieter and Hrubes, Pavel". The correct
authors are Vinogradova, Felty and Scott. Cockett and Hofstra are the
originators of Turing categories, not the authors of this formalization.

`[RELATED]` Yannick Forster, Fabian Kunze, Maximilian Wuttke, *Verified
programming of Turing machines in Coq*, CPP 2020, DOI
`10.1145/3372885.3373816` — cited by Zeng et al. as the reference for how
costly explicit machine models are in formal proofs.

### 2.5 Agda

`[OPEN]` No Agda formalization of computability theory, recursion theory or
Turing degrees was located. The only nearby item found is an Agda
formalization of restriction categories mentioned in secondary sources,
which was not verified. Treat "nothing in Agda" as unverified.

### 2.6 Sacks Splitting

`[OPEN]` No formalization of the Sacks Splitting Theorem in any proof
assistant was found by web search. The search was not exhaustive; see
Part 10.

---

## Part 3 — Repository facts

All items in this Part are `[VERIFIED-LEAN]` unless tagged otherwise.
Line references are to HEAD `833d0fc`.

### 3.1 Build configuration

* `lean-toolchain`: `leanprover/lean4:v4.26.0`.
* `lakefile.lean`: package `PriorityArguments`, `leanOptions := #[⟨autoImplicit, false⟩]`.
* Single dependency: `mathlib` from git at `v4.26.0`; `lake-manifest.json`
  pins revision `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Inherited
  transitive packages: `plausible`, `LeanSearchClient`, `importGraph`,
  `ProofWidgets4` (and their own dependencies).
* Four `lean_lib` targets, all `@[default_target]`: `OracleComputability`,
  `FriedbergMuchnik`, `SacksSplitting`, `PriorityArguments`.
* No `LICENSE` file. No `.github` directory, hence no CI.
* Git remotes: `origin = https://github.com/aaslyan/friedberg-muchnik-lean`;
  a second remote `sacks` pointing at a local path
  `/Users/araaslyan/sacks-splitting-lean`.

### 3.2 Architecture and dependency graph

Four libraries; `FriedbergMuchnik` and `SacksSplitting` are siblings and
neither imports the other. Verified by reading every `import` line in all 30
project `.lean` files.

```
                    Mathlib
                       │
                       ▼
             OracleComputability            (13 modules + root)
                  ├────────────┐
                  ▼            ▼
        FriedbergMuchnik   SacksSplitting   (7 + root, 6 + root)
                  └─────┬──────┘
                        ▼
                PriorityArguments           (1 module)
```

Mathlib import sites (exhaustive):

| File | Mathlib import |
|---|---|
| `OracleComputability/FiniteEval.lean` | `Mathlib.Data.Nat.Pairing` |
| `OracleComputability/Numbering.lean` | `Mathlib.Data.Nat.Pairing` |
| `OracleComputability/Reducibility.lean` | `Mathlib.Data.Set.Basic` |
| `OracleComputability/Approximation.lean` | `Mathlib.Data.Finset.Basic` |
| `OracleComputability/Priority.lean` | `Mathlib.Data.List.Basic` |
| `OracleComputability/RunPrimrec.lean` | `Mathlib.Computability.Primrec` |
| `OracleComputability/MathlibBridge.lean` | `Mathlib.Computability.PartrecCode` |
| `OracleComputability/MathlibOracleBridge.lean` | `Mathlib.Computability.TuringDegree` |

**Three** files import Mathlib's computability library, not one and not two.
This contradicts two in-repo statements; see Part 9.2.

Intra-project import edges:

```
OracleCode ← FiniteEval ← Use ← InfiniteEval ← Reducibility ← Composition
OracleCode ← Numbering
FiniteEval, Numbering ← RunPrimrec ← PrimrecTools
Use, Reducibility ← Approximation ← PrimrecTools
Use, Reducibility ← MathlibBridge
Composition, MathlibBridge ← MathlibOracleBridge
Priority   (leaf; imports only Mathlib.Data.List.Basic)

RunPrimrec, Approximation ← FM.Construction ← FM.StageDynamics
  ← FM.FiniteInjury, FM.Invariants ← FM.Requirements ← FM.Main
  MathlibBridge, PrimrecTools, FM.StageDynamics ← FM.CE ← FM.Main

OracleComputability ← Sacks.Basic ← Sacks.Requirements ← Sacks.Construction
  ← Sacks.CE ← Sacks.FiniteInjury ← Sacks.Main

OracleComputability, FriedbergMuchnik, SacksSplitting ← PriorityArguments
```

### 3.3 Module inventory

| Module | Lines | Role |
|---|---:|---|
| `OracleComputability/OracleCode.lean` | 62 | syntax of oracle programs |
| `OracleComputability/FiniteEval.lean` | 252 | fuel-bounded evaluator `run`, step lemmas |
| `OracleComputability/Use.lean` | 238 | use principle and corollaries |
| `OracleComputability/InfiniteEval.lean` | 75 | total-oracle semantics, finite↔infinite |
| `OracleComputability/Numbering.lean` | 169 | `ℕ ≃ OracleCode` |
| `OracleComputability/Reducibility.lean` | 94 | `≤ᵀ`, `CE`, `ComputableSet` |
| `OracleComputability/Composition.lean` | 199 | transitivity via query substitution |
| `OracleComputability/MathlibBridge.lean` | 242 | ordinary computability into the model |
| `OracleComputability/MathlibOracleBridge.lean` | 523 | Mathlib `RecursiveIn` → `OracleCode` |
| `OracleComputability/RunPrimrec.lean` | 597 | `nrun_primrec` |
| `OracleComputability/Priority.lean` | 50 | least-index selection |
| `OracleComputability/Approximation.lean` | 239 | monotone stages, snapshots, restraint |
| `OracleComputability/PrimrecTools.lean` | 66 | three generic `Primrec` helpers |
| `OracleComputability.lean` | 60 | library root |
| `FriedbergMuchnik/Construction.lean` | 243 | the stage machine |
| `FriedbergMuchnik/StageDynamics.lean` | 217 | attention, leastness, step trichotomy |
| `FriedbergMuchnik/Invariants.lean` | 386 | the ten-field `ConsInv` |
| `FriedbergMuchnik/FiniteInjury.lean` | 225 | rank argument, `quiet_above` |
| `FriedbergMuchnik/Requirements.lean` | 289 | `R_satisfied`, `S_satisfied`, both non-reducibilities |
| `FriedbergMuchnik/CE.lean` | 573 | shadow implementation, `Primrec`, `ce_Aset`/`ce_Bset` |
| `FriedbergMuchnik/Main.lean` | 42 | the theorem |
| `FriedbergMuchnik.lean` | 27 | library root |
| `SacksSplitting/Basic.lean` | 170 | `CE A` → explicit stage enumeration |
| `SacksSplitting/Requirements.lean` | 233 | agreement test, agreement length, restraint |
| `SacksSplitting/Construction.lean` | 267 | routing machine, two invariants |
| `SacksSplitting/CE.lean` | 399 | `Primrec` derivation, `ce_halfSet`, decision procedure |
| `SacksSplitting/FiniteInjury.lean` | 388 | the three-part priority induction |
| `SacksSplitting/Main.lean` | 75 | the theorem |
| `SacksSplitting.lean` | 16 | library root |
| `PriorityArguments.lean` | 83 | the two theorems composed |

### 3.4 Representation of oracles

* `PartOracle := ℕ → Option Bool` (`FiniteEval.lean:57`) — one type for both
  total oracles and finite snapshots.
* `PartOracle.ofFun (X : ℕ → Bool)`, `PartOracle.ofSnapshot (σ : List Bool)`,
  `PartOracle.empty` (lines 62, 66, 70).
* `PartOracle.Consistent O X := ∀ i b, O i = some b → X i = b` (`Use.lean:199`).
* A query the oracle cannot answer yields `RunResult.stuck`, which is
  distinct from `timeout` — insufficient information is *not* divergence
  (`FiniteEval.lean:42–51`).

### 3.5 Representation of reductions

* `Computes c X x y := ∃ k d, run k (PartOracle.ofFun X) c x = .halt d ∧ d.output = y` (`InfiniteEval.lean:20`).
* `Computes.unique` (line 24) — one output per input, via `run_halt_unique`.
* `TuringReducible` quantifies `∀ x` outside the existential over the code,
  so the reduction must be total (`Reducibility.lean:49`).
* `subst (q : OracleCode) : OracleCode → OracleCode` replaces every `query`
  node by `q` (`Composition.lean:26`); `subst_run_aux` (line 42) is the
  simulation; `TuringReducible.trans` (line 183) is the corollary.

### 3.6 Representation of enumerable sets

* `StageMono F := ∀ s, F s ⊆ F (s + 1)` for `F : ℕ → Finset ℕ`
  (`Approximation.lean:37`); `limitSet F := {n | ∃ s, n ∈ F s}` (line 42).
* `StageMono.stabilizesBelow` (line 63) — below any bound, membership agrees
  with the limit from some stage on; proved by induction on the bound, with
  no appeal to finiteness of the limit.
* `snapshot (F : Finset ℕ) (u : ℕ) : List Bool` (line 97) and
  `snapshotOf (l : List ℕ) (u : ℕ)` (line 181) — `List Bool` is always
  derived, never primary.
* Friedberg–Muchnik sets: `Aset := limitSet AstageF`, `Bset := limitSet BstageF`,
  where `AstageF s := (stageState s).Alist.toFinset` (`Construction.lean:141–150`).
* Sacks halves: `halfSet ec j := limitSet (halfF ec j)` (`Construction.lean:105`).
* Given set for Sacks: `enumStage ec s`, `enumStageF`, `enumSet ec`
  (`Basic.lean:94,109,120`), with `ce_eq_enumSet` (line 137).

### 3.7 Representation of requirements

Friedberg–Muchnik (`Construction.lean:8–11`): requirement `2e` is
`R_e : A ≠ Φ_e^B`; requirement `2e+1` is `S_e : B ≠ Φ_e^A`.

```lean
structure ReqState where          -- Construction.lean:45
  witness : Option ℕ
  acted : Bool
  restraint : ℕ

structure ConsState where         -- Construction.lean:60
  Alist : List ℕ
  Blist : List ℕ
  reqs : List ReqState
  fresh : ℕ
```

Sacks (`Requirements.lean:52`): `abbrev State : Type := List ℕ × List ℕ × List ℕ`
— two half-enumerations and one cumulative restraint per requirement.
Requirement `j` is `N_j : A ≠ Φ_{j/2}^{A_{j%2}}`.

### 3.8 Priority ordering and injury mechanism

Friedberg–Muchnik:

* `ConsState.requiresAttention st s i : Bool` (`Construction.lean:96`) — the
  record exists and either has no witness, or has an unacted witness whose
  diagonalizing computation has appeared.
* `attended s : Option ℕ` (`StageDynamics.lean:37`) — the least such index.
* `ConsState.stepAt` (`Construction.lean:108`): appointment consumes the
  freshness counter; **action** enumerates the witness, records the
  computation's use as restraint, and replaces every lower-priority record by
  `ReqState.init` — that replacement *is* the injury.
* `step_cases` (`StageDynamics.lean:109`) — a hypothesis-free trichotomy:
  every stage is idle, appointment, or action.

Sacks:

* `restraintAt` (`Requirements.lean:197`) — the largest use among currently
  agreeing computations.
* `newRestraints` (`Construction.lean:60`) — `R(j, s+1) = max (R(j,s)) (restraintAt … s j)`,
  a **running maximum** kept in the state.
* `routeTo` (`Construction.lean:66`) — a new element `x` goes to half
  `1 - j % 2` for the least `j` with `x < R(j,s)`, else to half `0`. Injury
  to `j` is exactly an element below `R(j,s)` entering `j`'s own half because
  a higher-priority opposite-parity requirement claimed it
  (`injured_by_higher`, `FiniteInjury.lean:98`).

### 3.9 Construction stages

* `stageState : ℕ → ConsState` (`FriedbergMuchnik/Construction.lean:136`),
  `stageState 0 = ⟨[], [], [], 0⟩`, `stageState (s+1) = stepState (stageState s) s`.
  Requirement `i`'s record is born at stage `i + 1`; `reqs_length s : (stageState s).reqs.length = s` (line 201).
* `SacksSplitting.stageState : ℕ → ℕ → State` (`SacksSplitting/Construction.lean:92`).
* One requirement receives attention per Friedberg–Muchnik stage; a Sacks
  stage attends none and routes all newly arrived elements.

### 3.10 Important invariants

`ConsInv` (`Invariants.lean:92`) — ten fields, verbatim field names:
`freshA`, `freshB`, `freshW`, `freshR`, `coh`, `distinct`, `wit_ge`,
`unacted_out`, `acted_in`, `acted_comp`. Established for every reachable
state by `consInv_stage : ∀ s, ConsInv (stageState s)` (line 372), via
`consInv_ext` (119), `consInv_appoint` (163), `consInv_act` (233) — one per
transition of `step_cases`.

`acted_comp` is the load-bearing field: an acted requirement's diagonalizing
run still halts with output `0` and use equal to its restraint against a
snapshot of the *current* oracle list.

Sacks invariants (`Construction.lean:193,221,242,256`): `stage_union`,
`stage_disjoint`, `union_halfSet`, `disjoint_halfSet` — the halves stay
disjoint and their union is the current stage of `A`.

### 3.11 Termination arguments

* `run` — `termination_by k _ c _ => (k, sizeOf c)` (`FiniteEval.lean:166`);
  fuel decreases exactly at the recursive calls of `prec` and `rfind`,
  deliberately mirroring Mathlib's `evaln`.
* `run_halt_mono_aux` — same measure `(k, sizeOf c)` (`Use.lean:163`).
* `subst_run_aux` — same measure (`Composition.lean:178`).
* `run_embed_aux` — same measure (`MathlibBridge.lean:186`).
* `ofNatCode` — `termination_by n => n`, `decreasing_by all_goals omega`
  (`Numbering.lean:57`).
* `lenAux`, `restAux` (Sacks) — structural recursion on an explicit bound,
  chosen so that `Primrec.nat_rec` applies unchanged
  (`Requirements.lean:105,187` and the file docstring).
* No `partial def`, no `unsafe`, no `decreasing_by sorry` anywhere.

### 3.12 Axiom footprint

`[MEASURED]` `#print axioms` run against the built environment on 37
declarations. **Every one** reports exactly
`[propext, Classical.choice, Quot.sound]`:

```
FriedbergMuchnik.friedberg_muchnik            SacksSplitting.sacks_splitting
PriorityArguments.friedbergMuchnik_set_splits PriorityArguments.friedbergMuchnik_set_splits'
PriorityArguments.friedberg_muchnik_mathlib   PriorityArguments.sacks_splitting_mathlib
OracleComputability.turingReducible_of_mathlib
OracleComputability.not_mathlibTuringReducible
OracleComputability.run_halt_mono             OracleComputability.run_halt_unique
OracleComputability.run_halt_limit_of_restraint
OracleComputability.run_halt_snapshot_of_limit
OracleComputability.TuringReducible.trans     OracleComputability.TuringReducible.refl
OracleComputability.OracleCode.ofNatCode_encodeCode
OracleComputability.OracleCode.encodeCode_ofNatCode
OracleComputability.partrec_realized          OracleComputability.ce_of_partrec_dom
OracleComputability.nrun_primrec
FriedbergMuchnik.ce_Aset                      FriedbergMuchnik.ce_Bset
FriedbergMuchnik.not_A_le_B                   FriedbergMuchnik.not_B_le_A
FriedbergMuchnik.R_satisfied                  FriedbergMuchnik.S_satisfied
FriedbergMuchnik.quiet_above
FriedbergMuchnik.Aset_not_computable          FriedbergMuchnik.Bset_not_computable
SacksSplitting.unsatisfied_requirement_computes
SacksSplitting.restraint_bounded              SacksSplitting.requirement_satisfied
SacksSplitting.ce_halfSet                     SacksSplitting.halfSet_ne
SacksSplitting.disjoint_halfSet               SacksSplitting.union_halfSet
SacksSplitting.ce_eq_enumSet                  SacksSplitting.computableSet_of_agreement
```

`[MEASURED]` An environment census over all project modules reports
**`axiom = 0`**: the development declares no axioms of its own.

### 3.13 Build status

`[MEASURED]` `lake build` from a clean project build directory (Mathlib
oleans present): **exit 0**, "Build completed successfully (829 jobs)".
Timings in Part 8.

`[MEASURED]` Grep for `sorry`, `admit`, `native_decide`, `unsafe`,
`^axiom `, `partial def` over all project `.lean` files: **zero matches**.

`[MEASURED]` `set_option maxHeartbeats` occurs 11 times, all in the two
`CE.lean` files: 5 in `FriedbergMuchnik/CE.lean` (lines 264, 303, 352, 393,
447; values 1.6M, 16M, 3.2M, 3.2M, 3.2M) and 6 in `SacksSplitting/CE.lean`
(lines 105, 156, 210, 223, 274, 281; values 1.6M ×5, 6.4M). Lean's default is
200 000. These are elaboration budgets only and cannot affect the axiom
footprint.

### 3.14 Executable examples

`[MEASURED]` The *actual* Friedberg–Muchnik machine (not the shadow
implementation) evaluates. `#eval` output at stage 20:

```
(stageState 20).Alist = [12, 8, 6, 4, 0]
(stageState 20).Blist = [13, 10, 1]
(stageState 20).fresh = 14
(stageState 20).reqs  = [(some 0, true, 0), (some 1, true, 0), (some 2, false, 0),
                         (some 3, false, 0), (some 4, true, 0), (some 5, false, 0),
                         (some 6, true, 0), (some 7, false, 0), (some 8, true, 9),
                         (some 10, true, 11), (some 12, true, 0), (some 13, true, 0),
                         (none, false, 0) × 8]
attended 19 = some 11
```

`[MEASURED]` The Sacks routing machine evaluates. With `ec = 0` (the code
`zero`, which halts on every input, so `enumSet 0 = ℕ`):

```
enumStage 0 8            = [0, 1, 2, 3, 4, 5, 6, 7]
(stageState 0 8).1       = [7, 6, 5, 4, 3, 2, 1, 0]     -- half A₀
(stageState 0 8).2.1     = []                            -- half A₁
(stageState 0 8).2.2     = [0, 0, 0, 0, 0, 0, 0, 0]      -- cumulative restraints
```

`[MEASURED]` The evaluator itself:

```
run 10 (ofSnapshot [true,false,true]) query 0 = halt {output := 1, use := 1}
run 10 (ofSnapshot [true,false,true]) query 5 = stuck
run 10 empty succ 3                           = halt {output := 4, use := 0}
nrun 20 [true,false] 4 1                      = 6
encodeCode (comp succ (pair left right))      = 9614
ofNatCode 42                                  = comp zero right
```

---

## Part 4 — Novelty

Each item states what would have to be true for the claim to hold, and what
evidence exists.

### 4.1 Mathematical

`[OPEN]` No new mathematics is claimed and none was identified. Both
theorems are classical results from 1956/57 and 1963.

`[VERIFIED-LEAN]` The one lemma the repository itself flags as having no
textbook-visible analogue in the Friedberg–Muchnik proof is
`SacksSplitting.unsatisfied_requirement_computes`
(`SacksSplitting/FiniteInjury.lean:282`):

```
NoInjuryFrom ec j s₀ →
(∀ y, Computes (ofNatCode (j/2)) (charFun (halfSet ec j)) y (natOfBool (charFun (enumSet ec) y))) →
ComputableSet (enumSet ec)
```

`[OPEN]` Whether this counts as *new mathematics* or as a formalization of a
step Soare makes inline is not established. It is a routine step of the
classical proof made explicit; the honest framing is "made explicit", not
"new".

### 4.2 Formalization

`[VERIFIED-PRIMARY] + [OPEN]` Candidate: first machine-checked
Friedberg–Muchnik theorem in an *analytic* setting (explicit oracle machine
model). Supporting evidence: the closest precedent, Zeng–Forster–Kirst 2024,
is synthetic **and** formalizes a low simple set rather than
Friedberg–Muchnik, and names Friedberg–Muchnik as an open challenge posed by
Bauer. Remaining risk: the claim rests on a non-exhaustive search.

`[OPEN]` Candidate: first Friedberg–Muchnik theorem in Lean. Supporting
evidence: Mathlib contains no priority material at all (verified by grep over
the pinned Mathlib); no Lean priority formalization was found by search.
Remaining risk: non-exhaustive search; no Zulip/GitHub code search was run.

`[OPEN]` Candidate: first Sacks Splitting Theorem in any proof assistant.
Supporting evidence: web search found none. Remaining risk: same as above,
and this is the weakest-evidenced of the three claims because no negative
authority (a survey, a library index) was consulted.

`[VERIFIED-LEAN]` Verified and not merely claimed: **two** finite-injury
priority arguments formalized over one shared foundation, with the
independence enforced by the build (`FriedbergMuchnik` and `SacksSplitting`
are separate Lake libraries and neither imports the other).

### 4.3 Engineering

`[VERIFIED-LEAN]` The evaluator records the **use** in its result type
(`HaltData.output`, `HaltData.use`), rather than deriving finite use post hoc
by a continuity argument. This makes the use principle a statement about data
the construction can inspect.

`[VERIFIED-LEAN]` The oracle is *partial* (`ℕ → Option Bool`) with a
dedicated `stuck` outcome, so finite snapshots and total oracles are the same
type and every lemma about `run` is stated once.

`[VERIFIED-LEAN]` The fuel discipline of `run` is deliberately identical to
Mathlib's `evaln` (same input guard `x ≤ k`, same placement of decrements),
which is what makes `run_embed` a single structural induction rather than a
simulation with fuel translation.

`[VERIFIED-LEAN]` `RunPrimrec.lean` handles codes *as numbers* via
`ofNatCode`, avoiding any `Primcodable OracleCode` instance, and encodes
`RunResult` into `ℕ` (`encodeResult`, line 42) so memo tables are `List ℕ`.

### 4.4 Verification

`[MEASURED]` Zero `sorry`, zero project axioms, and a uniform three-axiom
footprint across 37 checked declarations including every headline theorem.

`[MEASURED]` The constructions are executable and were executed (Part 3.14).
This is stronger than "no `sorry`": it shows the definitions are not
vacuously satisfiable stubs.

### 4.5 Tooling

`[OPEN]` No new tooling was produced. No tactic, elaborator, or automation
component exists in the repository.

### 4.6 Architecture

`[VERIFIED-LEAN]` The foundation/clients split is real and enforced: 13
foundation modules imported by both clients, and a single meeting point
(`PriorityArguments.lean`) that is the only declaration site depending on
both.

`[VERIFIED-LEAN]` The reuse verdicts recorded in `SacksSplitting/STATUS.md`
were written *before* any Sacks construction code existed (stated in that
document) and can be checked against the final import graph. The negative
finding — the priority layer did not transfer and no generalization was found
— is `[VERIFIED-LEAN]` in the weak sense that the two `FiniteInjury.lean`
files share no declarations; `[OPEN]` in the strong sense that "no useful
common generalization exists" is a judgement, not a proved statement.

---

## Part 5 — Constructivity audit

### 5.1 Where `Classical` is used

`[MEASURED]` Exhaustive grep for `Classical` over project sources — 9 hits,
of which 7 are code sites and 2 are the words "Classical source:" in the
`Construction.lean` docstrings of the two priority arguments:

| Site | Use |
|---|---|
| `OracleComputability/Reducibility.lean:26` | `open Classical in` before `charFun` |
| `OracleComputability/Reducibility.lean:32` | `open Classical in` before `charFun_eq_true` |
| `OracleComputability/Reducibility.lean:37` | `open Classical in` before `charFun_eq_false` |
| `SacksSplitting/FiniteInjury.lean:297` | `open Classical in` before `limUse` |
| `SacksSplitting/FiniteInjury.lean:306` | `Classical.choose h` inside `limUse` |
| `SacksSplitting/FiniteInjury.lean:315` | `Classical.choose_spec` in `use_eq_limUse` |
| `SacksSplitting/FiniteInjury.lean:327` | `Classical.not_forall` in `restraint_bounded_of` |

`[MEASURED]` Tactics that appeal to classical reasoning: `by_cases` 50
occurrences; `by_contra` 8 occurrences (`FriedbergMuchnik/Requirements.lean` 2,
`FriedbergMuchnik/FiniteInjury.lean` 2, `FriedbergMuchnik/StageDynamics.lean` 1,
`SacksSplitting/FiniteInjury.lean` 3); `push_neg` 1 occurrence.

### 5.2 Whether executable definitions depend on it

`[VERIFIED-LEAN]` Exactly two `noncomputable` declarations exist in the whole
project:

* `OracleComputability.charFun` (`Reducibility.lean:29`) — specification-level
  only; it appears in the *statements* of `TuringReducible`, `Computes`,
  `ComputableSet`, never inside a construction.
* `SacksSplitting.limUse` (`FiniteInjury.lean:303`) — proof-level only; it
  appears in the verification (`restraint_bounded_of`), never in the
  construction.

`[MEASURED]` Everything the constructions actually run on is computable, and
was run: `run`, `nrun`, `encodeCode`, `ofNatCode`, `FriedbergMuchnik.stageState`,
`FriedbergMuchnik.stageN`, `FriedbergMuchnik.attended`,
`SacksSplitting.enumStage`, `SacksSplitting.stageState`,
`SacksSplitting.halfList` all evaluate (Part 3.14).

### 5.3 Whether the proofs only depend on it

`[MEASURED]` Every one of the 37 checked theorems depends on
`Classical.choice`. No theorem in the development is constructive in the
kernel-footprint sense.

`[OPEN]` Which theorems *could* be made choice-free was not investigated. The
`charFun`-based statement shape means even `TuringReducible.refl` carries the
classical footprint, so a constructive subset would require restating the
vocabulary (e.g. over `ℕ → Bool` rather than `Set ℕ`).

### 5.4 Trusted base

`[VERIFIED-LEAN]` **Kernel trusted base**: the Lean 4 kernel (v4.26.0), plus
the three standard axioms `propext`, `Classical.choice`, `Quot.sound`. No
`native_decide`, no `implemented_by`, no `extern`, no `opaque`, no `unsafe`,
no project axioms.

`[VERIFIED-LEAN]` **Library trusted base**: Mathlib `v4.26.0` — specifically
`Nat.Pairing`, `Set.Basic`, `Finset.Basic`, `List.Basic`,
`Computability.Primrec`, `Computability.PartrecCode`,
`Computability.TuringDegree`. Nothing in the local oracle semantics or either
priority argument refers back to Mathlib's `Code`/`Partrec`/`RecursiveIn`
outside the three bridge/`Primrec` files.

`[VERIFIED-LEAN]` **Constructive trusted base**: not applicable — the
development is not constructive (5.3).

### 5.5 Full dependency list

`[VERIFIED-LEAN]` Direct: `mathlib` (v4.26.0). Transitive, from
`lake-manifest.json`: `plausible`, `LeanSearchClient`, `importGraph`,
`ProofWidgets4`, and their own dependencies. None of the transitive packages
is used by any project file (no project file imports them).

---

## Part 6 — Proof engineering

All items `[ENGINEERING]` unless otherwise tagged; each is sourced to a
docstring or status document in the repository, or reconstructed from the
sources and marked as such.

### 6.1 Representation choices that were made, and why

**Stages as `⊆`-monotone `Finset`s, not prefix-monotone strings.**
`Approximation.lean:8–12` and `Reducibility.lean:77–79` record the reason:
had stage sequences been prefix-monotone Boolean strings, the limits would be
computable, and `ComputableSet.turingReducible` would then have handed back
exactly the reduction the theorem denies. The comment calls this "the sanity
theorem that killed the prefix-monotone-string design."

**Recording the use in the result type.** `FiniteEval.lean:16–19`: recording
`use` "is what makes the use principle a statement about data the
construction can actually inspect". `SacksSplitting/STATUS.md` Part 3 reports
this decision paying off in a theorem it was not designed for: `run_halt_unique`
is what makes "the use of the limit computation at `y`" a well-defined number
(`limUse`), which is what bounds the Sacks restraint.

**A partial oracle with an explicit `stuck`.** `FiniteEval.lean:44–51`:
insufficient oracle information is distinguished from divergence; "more
oracle information may turn this into `halt`; more fuel alone cannot."

**Matching Mathlib's fuel discipline.** `MathlibBridge.lean:24–27`: the
deliberate match "is what makes `run_embed` a single structural induction
rather than a simulation argument with fuel translation."

**Codes as numbers in the `Primrec` layer.** `RunPrimrec.lean:12–19`: two
simplifications over Mathlib's `primrec_evaln` — no `Primcodable OracleCode`
instance is needed because branching on a code is arithmetic on its number,
and results are encoded as naturals so memo tables are `List ℕ`.

**Cumulative restraint (Sacks).** `SacksSplitting/Construction.lean:22–30`:
the raw stage restraint is *not* monotone, because the agreement length drops
whenever a number below it enters `A`; "a restraint that can drop protects
nothing", so the state keeps a running maximum. This is described as the one
place where the finite-injury pattern had to be adapted rather than
instantiated.

**Plain tuple state (Sacks) vs. custom structures (Friedberg–Muchnik).**
`SacksSplitting/Requirements.lean:47–50`: `State` is `List ℕ × List ℕ × List ℕ`
so `Primcodable` is automatic.

### 6.2 Alternatives that failed

`[ENGINEERING]` **One large `Primrec` combinator term.** `STATUS.md:14–22`
reports the failure mode concretely: assembling the c.e. proof as a single
combinator term made failed `Primrec X =?= Primrec Y` unifications fall back
into the `Primcodable` pairing encodings, with the elaborator symbolically
evaluating `Nat.sqrt` "for tens of millions of heartbeats". The fix was to
confine each tuple-sized comparison to its own lemma.

`[VERIFIED-LEAN]` The residue of that failure is visible in the sources: 11
raised `maxHeartbeats` budgets, the largest being 16 000 000 (80× default) on
`primrec_reqAttN` (`FriedbergMuchnik/CE.lean:303`).

### 6.3 Proof bottlenecks

`[MEASURED]` `FriedbergMuchnik/CE.lean` costs 106 s of the 122 s clean-build
wall clock. `SacksSplitting/CE.lean` costs 12 s. Every other module is
≤ 2.6 s.

`[ENGINEERING]` `FriedbergMuchnik/CE.lean:8–16` states the cause: `ConsState`
and `ReqState` are custom structures with no `Primcodable` instance, so the
file carries a **shadow implementation** on plain tuples (`St`, `RS`, `encSt`,
named builders `idleSt`/`appointSt`/`actSt`), a simulation theorem
`encSt_stage` (line 247), and two list-surgery bridge lemmas
`map_range_set`/`map_range_act` (lines 132, 151) re-expressing `List.set` and
take-cons-replicate as maps over `List.range`.

`[VERIFIED-LEAN]` The Sacks file has no shadow layer at all: its state is a
tuple from the outset (`SacksSplitting/CE.lean:16–26`).
`SacksSplitting/STATUS.md:213–216` records the counterfactual estimate that
rewriting `ConsState` as a tuple today "would delete roughly half of its
`CE.lean`" — that is an estimate, `[OPEN]` as a measured claim.

### 6.4 Automation

`[VERIFIED-LEAN]` The development uses stock Mathlib automation only:
`simp`, `omega`, `simpa`, `by_cases`, `rcases`/`obtain`, and the `Primrec`
combinator library. `omega` carries most of the arithmetic in `Numbering.lean`
(the `4·p + t + 5` coding arithmetic) and in the rank argument.

`[VERIFIED-LEAN]` `Numbering.lean:15–18` notes a syntactic accommodation made
for automation: sums are written exactly as `4·payload + tag + 5` so that the
decoder's `n + 5` pattern matches syntactically in proofs.

`[VERIFIED-LEAN]` `SacksSplitting/Basic.lean:33–40`: `List.filter` has no
`Primrec` lemma in Mathlib but `List.foldr` does, so the development defines
`filterB` as a `foldr` with `cond` — "exactly the shape `Primrec.cond`
consumes" — and every filtering step goes through it.

`[VERIFIED-LEAN]` `SacksSplitting/Requirements.lean:31–36`: `lenAgree` and
`restraintAt` are defined by explicit recursion on a bound rather than with
`List.takeWhile`/`List.foldr`, specifically so that `CE.lean` can hand them to
`Primrec.nat_rec` unchanged.

### 6.5 Unexpected simplifications

`[VERIFIED-LEAN]` `run_halt_limit_of_restraint` was already stated generically
in the stage sequence `F`, so the Sacks restraint argument reuses it verbatim
with no generalization (`SacksSplitting/STATUS.md` Part 1, approximation-layer
table, and `SacksSplitting/FiniteInjury.lean:173` `restraint_respected`).

`[VERIFIED-LEAN]` `partrec_realized` acquired a consumer it never had in
Friedberg–Muchnik: Sacks uses it to turn the "search for a stage of long
agreement" decision procedure into an oracle-free `OracleCode`, i.e. to
*produce* a `ComputableSet` (`SacksSplitting/CE.lean:343`,
`computableSet_of_agreement`).

`[VERIFIED-LEAN]` The Sacks development needed no analogue of the ten-field
`ConsInv`; two invariants (disjointness, union) suffice, because the elements
are not chosen by the construction.

### 6.6 Unexpected complications

`[VERIFIED-LEAN]` `MathlibOracleBridge.lean:112–121` (README) and the file
itself: the `rfind` case of the transfer theorem is the hardest, because the
local `rfind` is the *primed* form (searching upward from the input's second
component, matching `Nat.Partrec.Code.rfind'`) while Mathlib's
`RecursiveIn.rfind` searches from `0`. The primed search is characterized
first without `Nat.rfind` at all — forward by induction on fuel
(`rfind_forward`, line 319), backward by induction on distance to the target
(`rfind_backward`, line 355) — then converted (`realizes_rfind_primed`, 404),
then composed with an input adapter `a ↦ ⟨a, 0⟩` obtained from the ordinary
Mathlib bridge (`exists_pairZero_code`, 456; `exists_realizes_rfind`, 465).

`[VERIFIED-LEAN]` The same file makes Mathlib's root-namespace
`TuringReducible` visible alongside the project's, so the two must be
distinguished explicitly at the sites that name the relation rather than using
`≤ᵀ` notation (README, and `PriorityArguments.lean`'s explicit
`OracleComputability.TuringReducible` qualifications in
`FriedbergMuchnik/Requirements.lean:276,283`).

### 6.7 Where Lean revealed specification bugs

`[VERIFIED-LEAN]` **A stray import broke the package for downstream users.**
`SacksSplitting/STATUS.md:76–85` and commit `d049c14` ("Root module: drop
stray import of a nonexistent file"): the Friedberg–Muchnik root module
imported `FriedbergMuchnik.Foundation.MathlibOracleBridge`, a file that did
not exist, so `lake build` failed outright on a clean checkout and the package
could not be depended on at all. The project's own build never noticed,
because the file was present locally.

`[VERIFIED-LEAN]` **Three generic helpers were `private` and therefore
unreusable.** `primrec_find?`, `primrec_memDecide`, `primrec_snapshotOf` were
private inside Friedberg–Muchnik's `CE.lean`; making them public
(commit `445048d`) was "the only change FM needed" to serve as a foundation.
They now live in `OracleComputability/PrimrecTools.lean`, whose docstring
names the failure mode: "exactly the sort of thing that silently becomes
unreusable if it is left `private` inside one theorem's computability file."

`[OPEN]` No case is documented in which Lean revealed a *mathematical* error
in the informal proof. `STATUS_ONE.md` — an independent review of commit
`b613d62` — probed seven candidate soundness holes and found five to be false
alarms, one an optional strengthening, and one a documented scope limitation.

### 6.8 Where the implementation diverged from the plan

`[VERIFIED-LEAN]` Three items open at the time of `STATUS_ONE.md` /
`paper/NOTES.md` were subsequently closed:

| Then | Now |
|---|---|
| transitivity of `≤ᵀ` not proved | `TuringReducible.trans`, commit `247ecef` |
| no bridge to an external oracle model | `turingReducible_of_mathlib`, commit `3fcfe62` |
| foundation entangled with Friedberg–Muchnik | extracted to `OracleComputability`, commits `01ba6cb`, `bb4edfe`, `f4b0183` |

`[VERIFIED-LEAN]` One item raised in `STATUS_ONE.md` remains open: the review
observed that the "acted" branch of the requirement-satisfaction proof is
provably exercised (requirement 0's stable record must have `acted = true`),
and suggested stating it as a lemma. Grep confirms no such lemma exists;
`acted = true` appears only inside `ConsInv`'s field types.

`[VERIFIED-LEAN]` `ComputableSet A → CE A` is explicitly deferred and never
proved (`Reducibility.lean:88–92`: "it is not needed for the Friedberg–Muchnik
theorem").

---

## Part 7 — Primary references

Publication data verified against publisher records, JSL/BSL review listings,
DOI registries, or the papers themselves. Discrepancies with the current
`paper/references.bib` are flagged.

| # | Reference | Verified data | Status vs. repo bib |
|---|---|---|---|
| 1 | Post, *Recursively enumerable sets of positive integers and their decision problems* | Bull. Amer. Math. Soc. **50** (1944), 284–316; DOI `10.1090/S0002-9904-1944-08111-1` | `[VERIFIED-PRIMARY]` correct; **DOI missing** in repo bib |
| 2 | Friedberg, *Two recursively enumerable sets of incomparable degrees of unsolvability (solution of Post's problem, 1944)* | Proc. Nat. Acad. Sci. USA **43**(2) (1957), 236–238; DOI `10.1073/pnas.43.2.236`; PMID 16590005 | `[VERIFIED-PRIMARY]` correct |
| 3 | Muchnik, on the unsolvability of the reducibility problem | Dokl. Akad. Nauk SSSR **108** (1956), 194–197; in Russian | `[VERIFIED-PRIMARY]` correct. Title translation varies: "On the unsolvability of the problem of reducibility in the theory of algorithms" (used by Zeng et al. and by the repo) vs. "Negative answer to the problem of reducibility of the theory of algorithms" |
| 4 | Muchnik, *Solution of Post's reduction problem and of certain other problems in the theory of algorithms* | Trudy Moskov. Mat. Obshch. **7** (1958), 391–405 | `[VERIFIED-PRIMARY]` correct |
| 5 | Sacks, *On the degrees less than 0′* | Ann. of Math. (2) **77** (1963), 211–231; **correction**: Ann. of Math. (2) **78** (1963), 204 | `[VERIFIED-PRIMARY]` pages/volume/year correct; repo bib **omits** "second series" and the correction |
| 6 | Soare, *Recursively Enumerable Sets and Degrees* | Perspectives in Mathematical Logic, Springer-Verlag, Berlin/Heidelberg/New York, 1987, xviii + 437 pp.; ISBN 3-540-15299-7 | `[VERIFIED-PRIMARY]` correct; page count and ISBN absent from repo bib |
| 7 | Odifreddi, *Classical Recursion Theory* | Studies in Logic and the Foundations of Mathematics **125**, North-Holland, Amsterdam, 1989, xviii + 668 pp.; ISBN 0-444-87295-7 | `[VERIFIED-PRIMARY]`; **not currently cited** by the repo. Note: Mathlib's `TuringDegree.lean` cites this as `[Odifreddi1989]`; the Zeng et al. bibliography dates the same work 1992 (Elsevier reprint) |
| 8 | Cooper, *Computability Theory* | Chapman & Hall/CRC, Boca Raton FL, 2004, x + 409 pp.; ISBN 1-58488-237-9 | `[VERIFIED-PRIMARY]`; **not currently cited** |
| 9 | Soare, *Turing Computability: Theory and Applications* | Theory and Applications of Computability, Springer, Berlin/Heidelberg, 2016, xxxvi + 263 pp.; ISBN 978-3-642-31932-7; DOI `10.1007/978-3-642-31933-4`; Chapter 7 is *The Finite Injury Method* | `[VERIFIED-PRIMARY]`; **not currently cited** |
| 10 | Carneiro, *Formalizing Computability Theory via Partial Recursive Functions* | ITP 2019, LIPIcs **141**, 12:1–12:17, Schloss Dagstuhl; DOI `10.4230/LIPIcs.ITP.2019.12`; full version arXiv `1810.08380` | `[VERIFIED-PRIMARY]` correct |
| 11 | Forster, Kirst, Mück, *Oracle Computability and Turing Reducibility in CIC* | APLAS 2023, LNCS **14405**, 155–181, Springer; DOI `10.1007/978-981-99-8311-7_8`; arXiv `2307.15543` | `[VERIFIED-PRIMARY]`; repo bib cites only the arXiv preprint — **should cite the APLAS version** |
| 12 | Forster, Kirst, Mück, *The Kleene-Post and Post's Theorem in CIC* | CSL 2024, LIPIcs **288**, 29:1–29:20; DOI `10.4230/LIPIcs.CSL.2024.29` | `[VERIFIED-PRIMARY]`; **not currently cited** and directly relevant |
| 13 | Zeng, Forster, Kirst, *Post's Problem and the Priority Method in CIC* | TYPES 2024, Copenhagen; extended abstract | `[VERIFIED-PRIMARY]` venue correct; **the repo's characterization of its content is wrong** — see Part 9.2 |
| 14 | Vinogradova, Felty, Scott, *Formalizing Abstract Computability: Turing Categories in Coq* | LSFA 2017; ENTCS **338** (2018), 203–218; DOI `10.1016/j.entcs.2018.10.013` | `[VERIFIED-PRIMARY]`; **repo bib has the wrong authors** (attributes it to Cockett, Hofstra, Hrubes) |
| 15 | Xu, Zhang, Urban, Joosten, Regensburger, *Universal Turing Machine* | Archive of Formal Proofs, 2019-02-08; corresponds to Xu, Zhang, Urban, ITP 2013 | `[VERIFIED-PRIMARY]` correct |
| 16 | Duve, Roth, `Mathlib.Computability.TuringDegree` | Mathlib4 file, copyright 2025, authors Tanner Duve and Elan Roth; 177 lines at rev `2df2f01` | `[VERIFIED-LEAN]` correct |
| 17 | Nipkow, Paulson, Wenzel, *Isabelle/HOL* | LNCS **2283**, Springer, 2002 | `[RELATED]` not independently re-verified this session |

`[OPEN]` **Soare section numbers not verified.** The repository asserts
specific Soare correspondences in several docstrings — "Soare VII.2" for the
use principle (`Use.lean:22`), "Soare VII.2" for Friedberg–Muchnik
(`Construction.lean:4`, `README.md:143`), "Soare VII.2.1" for the
requires-attention discipline (`Construction.lean:93`), "Soare VII.3" for
Sacks splitting (`SacksSplitting/Construction.lean:4`), "Soare III.1" for
transitivity (`Composition.lean:181`). None of these could be verified
online; the book's table of contents was not obtainable. Note also an internal
tension: the use principle and Friedberg–Muchnik are both cited as VII.2,
whereas the use principle is normally located in Soare's Chapter III
(Turing Reducibility). **Every Soare pointer must be checked against a
physical copy before publication.**

---

## Part 8 — Measurements

Environment as stated at the top. All figures `[MEASURED]` this session.

### 8.1 Source size

| Unit | Value |
|---|---|
| Lean files (project, excluding `lakefile.lean`) | 30 |
| Total lines of Lean | 6 499 |
| Non-blank, non-comment lines (comments stripped by a nested-block-comment-aware parser) | 4 471 |
| Blank lines | 683 |
| Comment/docstring lines | 1 345 (21 % of all lines) |
| `lakefile.lean` | 36 lines |

Per library:

| Library | Files | Lines | Code lines |
|---|---:|---:|---:|
| `OracleComputability` | 14 | 2 866 | 2 000 |
| `FriedbergMuchnik` | 8 | 2 002 | 1 494 |
| `SacksSplitting` | 7 | 1 548 | 948 |
| `PriorityArguments` | 1 | 83 | 29 |

### 8.2 Declaration counts

Hand-written declarations, counted after stripping comments:

| Library | `theorem` | `def` | `abbrev` | `structure` | `inductive` | `instance` |
|---|---:|---:|---:|---:|---:|---:|
| `OracleComputability` | 95 | 33 | 2 | 1 | 2 | 1 |
| `FriedbergMuchnik` | 73 | 26 | 2 | 3 | 0 | 0 |
| `SacksSplitting` | 102 | 23 | 4 | 0 | 0 | 0 |
| `PriorityArguments` | 4 | 0 | 0 | 0 | 0 | 0 |
| **Total** | **274** | **82** | **8** | **4** | **2** | **1** |

The keyword `lemma` is never used; every proof-carrying declaration is a
`theorem`. 33 declarations are `private`.

Environment census (includes auto-generated declarations — projections,
`deriving` instances, `injEq`, `noConfusion`, etc.): 389 theorems, 211
definitions, 28 constructors/recursors, **0 axioms**, across 27 project
modules.

The gap between 274 hand-written and 389 environment theorems is accounted
for by `deriving DecidableEq, Repr` on `OracleCode`, `HaltData`, `RunResult`,
`ReqState`, `ConsState` and by structure/inductive boilerplate — e.g.
`OracleCode.lean` has 1 hand-written declaration (the inductive type) and 58
in the environment (18 theorems, 29 definitions, 11 constructors/recursors).

### 8.3 Largest files

| File | Lines | Hand-written theorems |
|---|---:|---:|
| `OracleComputability/RunPrimrec.lean` | 597 | 12 |
| `FriedbergMuchnik/CE.lean` | 573 | 23 |
| `OracleComputability/MathlibOracleBridge.lean` | 523 | 26 |
| `SacksSplitting/CE.lean` | 399 | 35 |
| `SacksSplitting/FiniteInjury.lean` | 388 | 18 |
| `FriedbergMuchnik/Invariants.lean` | 386 | 7 |

### 8.4 Build time

Clean project build (`rm -rf .lake/build && lake build`) with Mathlib oleans
already present:

```
Build completed successfully (829 jobs).
lake build  146.78s user 20.22s system 137% cpu 2:01.82 total
```

An independent earlier run of the same command: `1:53.74 total`, 134.69 s
user. A no-op `lake build` (everything up to date): 2.8 s.

Per-module elaboration times from the clean build (all 30 project modules):

| Module | Time |
|---|---:|
| `FriedbergMuchnik.CE` | 106 s |
| `SacksSplitting.CE` | 12 s |
| `OracleComputability.FiniteEval` | 2.6 s |
| `OracleComputability.Numbering` | 2.5 s |
| `OracleComputability.Priority` | 2.4 s |
| `OracleComputability.RunPrimrec` | 2.4 s |
| `OracleComputability.Composition` | 2.4 s |
| `OracleComputability.Use` | 2.3 s |
| `FriedbergMuchnik.FiniteInjury` | 2.2 s |
| `FriedbergMuchnik.Invariants` | 2.2 s |
| `OracleComputability.MathlibBridge` | 2.1 s |
| `PriorityArguments` | 1.7 s |
| `FriedbergMuchnik.Construction` | 1.7 s |
| `OracleComputability.MathlibOracleBridge` | 1.6 s |
| `OracleComputability.PrimrecTools` | 1.6 s |
| `FriedbergMuchnik.Requirements` | 1.6 s |
| `OracleComputability` (root) | 1.6 s |
| `SacksSplitting.Basic` | 1.5 s |
| `SacksSplitting.FiniteInjury` | 1.5 s |
| `SacksSplitting.Requirements` | 1.4 s |
| `OracleComputability.Approximation` | 1.3 s |
| `FriedbergMuchnik.StageDynamics` | 1.2 s |
| `SacksSplitting.Construction` | 1.1 s |
| `SacksSplitting.Main` | 1.1 s |
| `SacksSplitting` (root) | 1.0 s |
| `FriedbergMuchnik.Main` | 0.95 s |
| `FriedbergMuchnik` (root) | 0.86 s |
| `OracleComputability.Reducibility` | 0.82 s |
| `OracleComputability.InfiniteEval` | 0.82 s |
| `OracleComputability.OracleCode` | 0.28 s |

`[MEASURED]` A full build *including* Mathlib from source is 7 742 jobs;
this was started accidentally and aborted, so no total time was obtained.
`lake exe cache get` restores 7 727 Mathlib olean files and decompressed them
in 6.07 s from a warm `~/.cache/mathlib`.

### 8.5 Repository history

| Item | Value |
|---|---|
| Commits on `master` | 29 |
| First commit | `d2cd2a5`, 2026-07-25, "Foundation core: oracle machine model, use principle, numbering, reducibility" |
| Last commit | `833d0fc`, 2026-07-31, "Paper: rebuild main.pdf with the two-theorem revision" |
| Elapsed calendar span | 7 days (2026-07-25 → 2026-07-31) |
| Commits up to `5db3ed3` (Friedberg–Muchnik complete) | 10 |
| Sole author | Ara Aslyan |
| Untracked at collection time | `.serena/` |

### 8.6 Axiom reports

See Part 3.12: 37 declarations checked, all `[propext, Classical.choice, Quot.sound]`.

---

## Part 9 — Claims audit

### 9.1 Safe claims (fully supported by evidence in this dossier)

1. `[VERIFIED-LEAN]` Both theorems are formalized in Lean 4 with the exact
   statements in Part 1.1, and the project builds with zero `sorry`.
2. `[MEASURED]` Every headline theorem, and 37 checked declarations in total,
   depend on exactly `propext`, `Classical.choice`, `Quot.sound`; the project
   declares no axioms of its own.
3. `[MEASURED]` No `sorry`, `admit`, `native_decide`, `unsafe`, `opaque`,
   `partial def`, or project `axiom` appears anywhere in the sources.
4. `[VERIFIED-LEAN]` The development is analytic: an explicit oracle program
   language, a step-indexed evaluator over partial oracle information, and a
   use principle that is a proved theorem about that evaluator.
5. `[VERIFIED-LEAN]` The evaluator records the use, and the use principle is
   one-sided (agreement only at answered positions below the recorded use).
6. `[VERIFIED-LEAN]` `≤ᵀ` is a preorder: reflexivity and transitivity are
   proved, the latter by query substitution.
7. `[VERIFIED-LEAN]` The program numbering is a proved bijection `ℕ ≃ OracleCode`,
   which is what makes the requirement list cover every reduction.
8. `[VERIFIED-LEAN]` Every reduction in Mathlib's `RecursiveIn` model is
   realized by an `OracleCode` (`turingReducible_of_mathlib`), and both
   theorems are restated over Mathlib's relation. The converse is not proved
   and is not claimed.
9. `[VERIFIED-LEAN]` The two priority arguments are separate Lake libraries,
   neither importing the other; the build enforces it.
10. `[VERIFIED-LEAN]` The Friedberg–Muchnik injury argument is a rank argument
    on `{0,1,2}`; the Sacks argument is a three-part induction along the
    priority order; the two `FiniteInjury.lean` files share no declarations.
11. `[MEASURED]` Both constructions are executable, and were executed; concrete
    traces are in Part 3.14.
12. `[VERIFIED-LEAN]` Sacks is formalized in its splitting-with-non-reducibility
    form; lowness is out of scope, and the repository says so.
13. `[VERIFIED-LEAN]` Non-vacuity of the Sacks statement is proved by applying
    it to the Friedberg–Muchnik set.
14. `[MEASURED]` 6 499 lines of Lean across 30 files; 274 hand-written
    theorems; clean build 122 s with Mathlib cached, of which
    `FriedbergMuchnik/CE.lean` is 106 s.
15. `[VERIFIED-PRIMARY]` Mathlib contains no priority-argument, finite-injury,
    or use-principle material, and its oracle file
    (`Computability/TuringDegree.lean`, Duve and Roth, 2025) has no use
    principle, step-indexed oracle evaluation, oracle-relative c.e., or jump.
16. `[VERIFIED-PRIMARY]` The closest prior mechanization of Post's problem
    (Zeng–Forster–Kirst, TYPES 2024) is synthetic and formalizes a **low
    simple set**, explicitly *not* Friedberg–Muchnik, which it names as an
    open challenge.

### 9.2 Unsafe claims (need more evidence, or are currently wrong)

**Wrong as currently written in the repository — must be corrected:**

1. `[VERIFIED-LEAN]` `OracleComputability/MathlibBridge.lean:4–5` says it is
   "the **only** file of the project that imports Mathlib's computability
   library." False: `RunPrimrec.lean` imports `Mathlib.Computability.Primrec`
   and `MathlibOracleBridge.lean` imports `Mathlib.Computability.TuringDegree`.
2. `[VERIFIED-LEAN]` `OracleComputability.lean:16–17` names
   "`MathlibBridge.lean, RunPrimrec.lean` (the only two files importing Mathlib
   computability)". Also false, for the same reason — there are three.
3. `[VERIFIED-PRIMARY]` `paper/references.bib` entry `cockett2018` has the
   wrong authors (see Part 7 #14).
4. `[VERIFIED-PRIMARY]` `paper/sections/related-work.tex:13–14` says
   "Zeng, Forster and Kirst formalize a solution by the priority method in
   Coq". Technically true but materially incomplete: what they formalize is
   Soare's *low simple set*, not Friedberg–Muchnik, and their abstract
   explicitly contrasts the two. The paper's own priority claim is *stronger*
   than it currently states, and the correction is in the source's favour.
5. `[VERIFIED-LEAN]` `STATUS.md:21–22` says "two declarations still carry
   raised heartbeat budgets". There are 11 (5 in `FriedbergMuchnik/CE.lean`,
   6 in `SacksSplitting/CE.lean`).
6. `[VERIFIED-LEAN]` `STATUS.md:10` says "Nine commits, ending with `5db3ed3`".
   `git rev-list --count 5db3ed3` = 10.
7. `[VERIFIED-LEAN]` `README.md:156–159` says the paper "does not yet cover the
   second theorem or the foundation/clients split". Stale: commit `23a6da0`
   added `paper/sections/second-theorem.tex` and rewrote the abstract.
7a. `[VERIFIED-LEAN]` `OracleComputability/OracleCode.lean:28–30` says that an
   `OracleCode` with no `query` node is an ordinary partial recursive program
   and that "`MathlibBridge.lean` makes that statement precise in both
   directions." Only one direction exists. `MathlibBridge.lean` provides
   `embed : Code → OracleCode` with `run_embed` and `partrec_realized`
   (Mathlib → local); there is no map from the query-free fragment back to
   `Nat.Partrec.Code` and no theorem characterizing that fragment. Verified by
   reading the file's full declaration list and by grep for a converse
   construction. Do not repeat the "both directions" claim.

**Stale paper text — will be wrong if published as is:**

8. `[VERIFIED-LEAN]` `paper/sections/limitations.tex:4–18` states that
   transitivity of `TuringReducible` "is not currently proved". It is
   (`TuringReducible.trans`, commit `247ecef`), by exactly the query-substitution
   route the section proposes as future work.
9. `[VERIFIED-LEAN]` `paper/sections/limitations.tex:20–27` states that
   equivalence with an established relative-computability framework is not
   proved. One direction now is (`turingReducible_of_mathlib`).
10. `[VERIFIED-LEAN]` `paper/sections/introduction.tex:60–64` repeats the
    transitivity limitation.
11. `[MEASURED]` `paper/sections/evaluation.tex:9,33–35` reports "811 jobs",
    "17 Lean files", "4024 lines", "178 declarations". Current: 829 jobs, 30
    files, 6 499 lines, 274 hand-written theorems + 90 data declarations.
12. `[VERIFIED-LEAN]` `paper/NOTES.md` is entirely pre-split and pre-Sacks;
    it should be marked superseded or deleted rather than used as a source.

**Claims that need evidence before they can be made:**

13. `[OPEN]` "First formalization of Friedberg–Muchnik in an analytic
    setting" / "first in Lean" / "first Sacks Splitting in any prover". The
    supporting evidence is Part 2, which is a targeted rather than exhaustive
    search. State these as "we are not aware of", with the search described,
    exactly as `related-work.tex:73–80` already does.
14. `[OPEN]` "Solves Post's problem." The formalized content is incomparability
    plus non-computability. There is no jump and no completeness notion in the
    development, so the classical inference to *intermediate degree* is not
    formalized. Either add the caveat or add the material.
15. `[OPEN]` "Incomparable Turing **degrees**." No degree structure, quotient,
    or order on degrees exists in the repository. The theorem is about sets and
    a preorder on sets.
16. `[OPEN]` "Constructive." False in the kernel sense: everything depends on
    `Classical.choice`. The safe statement is that the *constructions* are
    executable while the *verifications* are classical.
17. `[OPEN]` "Rewriting `ConsState` as a tuple would delete roughly half of
    `FriedbergMuchnik/CE.lean`" (`SacksSplitting/STATUS.md:213–216`). An
    estimate, never measured.
18. `[OPEN]` "No useful common generalization of the two injury arguments
    exists" (`README.md`, "What the second theorem cost";
    `SacksSplitting/STATUS.md` Part 3). A judgement. What is verified is that
    the two `FiniteInjury.lean` files share no declarations.
19. `[OPEN]` Every "Soare VII.2 / VII.2.1 / VII.3 / III.1" pointer (Part 7).
20. `[OPEN]` **Elapsed-time claims.** The git history spans 7 calendar days
    (2026-07-25 → 2026-07-31) over 29 commits. Any narrative of "several
    months" of work is unsupported by the repository; if wall-clock effort
    predates the first commit, that needs an independent record.

---

## Part 10 — Missing evidence checklist

Before a paper is submitted, each of the following must be obtained or the
corresponding claim dropped.

### Bibliographic
- [ ] Physical copy of Soare (1987): verify the section number of the Use
      Principle, of the Friedberg–Muchnik theorem, of the requires-attention
      definition, and of the Sacks Splitting Theorem; correct every in-source
      docstring pointer accordingly.
- [ ] Verify the exact statement of Soare's Sacks Splitting Theorem (the
      lowness clause and the role of the auxiliary non-computable set `C`) so
      the scope note is precise about what was dropped.
- [ ] Fix `references.bib` entry `cockett2018` (authors: Vinogradova, Felty,
      Scott).
- [ ] Add the APLAS 2023 published version of Forster–Kirst–Mück alongside the
      arXiv entry.
- [ ] Add Forster–Kirst–Mück, CSL 2024 (Kleene–Post) — directly relevant and
      currently uncited.
- [ ] Decide whether to cite Odifreddi (1989), Cooper (2004), Soare (2016).
- [ ] Add DOIs where verified (Post, Vinogradova et al., Carneiro, CSL/APLAS).
- [ ] Add the Sacks (1963) correction note.

### Related work
- [ ] Verify the contents of AFP *Recursion Theory I* (Nedzelsky, 2008) — the
      entry page 404'd twice.
- [ ] Run a GitHub code search and a Lean Zulip search for "Friedberg",
      "Muchnik", "priority", "finite injury" before making any "first in Lean"
      claim; record the queries and the date.
- [ ] Search the Coq/Rocq package index and `coq-community` for priority
      arguments beyond `coq-synthetic-computability`.
- [ ] Establish whether any Agda computability library exists.
- [ ] Check whether Zeng's bachelor thesis or a successor paper (2025–2026)
      has since formalized Friedberg–Muchnik synthetically — the TYPES 2024
      abstract names it as the open challenge, so this is the single most
      likely way the novelty claim breaks.
- [ ] Check for a formalization of the Sacks Splitting Theorem in the
      Isabelle AFP 2025–2026 additions.

### Repository
- [ ] Add a `LICENSE` file (none exists).
- [ ] Add CI running `lake build` plus the axiom-footprint check (none exists).
- [ ] Update `README.md`'s stale paper note, `STATUS.md`'s commit count and
      heartbeat count, and the two "only file(s) importing Mathlib
      computability" claims.
- [ ] Rewrite or retire `paper/NOTES.md` (superseded on every numeric fact).
- [ ] Rewrite `paper/sections/limitations.tex`, `introduction.tex` and
      `evaluation.tex` against the current state.
- [ ] Decide whether to add the `∃ s r, r.acted = true` lemma suggested by
      `STATUS_ONE.md` item 5, which would show the acted branch is not vacuous.
- [ ] Decide whether to add `ComputableSet A → CE A`, currently deferred.
- [ ] Consider adding the jump / halting set if the paper wants to say "Post's
      problem" without a caveat.

### Measurement
- [ ] Re-measure the full build on a cold cache (from-scratch Mathlib) if the
      paper reports total build cost; the 7 742-job figure has no timing.
- [ ] If the "tuple state would halve `CE.lean`" claim is kept, measure it.
- [ ] Record the reviewer-facing reproduction recipe end to end
      (`lake exe cache get`, `lake build`, axiom check) and time it on a clean
      clone.

### Scope
- [ ] Decide and state explicitly whether the paper claims Post's problem, or
      incomparability plus non-computability.
- [ ] Decide whether to use the word "degrees" anywhere given that no degree
      structure is formalized.
- [ ] State the direction of the Mathlib bridge and why the converse is not
      needed, in the theorem statements themselves and not only in prose.
