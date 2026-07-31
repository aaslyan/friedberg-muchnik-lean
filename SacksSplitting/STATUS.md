# Sacks Splitting on the Friedberg–Muchnik foundation — reuse inventory and status

Target theorem:

```lean
theorem sacks_splitting :
    ∀ A : Set ℕ, CE A → ¬ ComputableSet A →
      ∃ A₀ A₁ : Set ℕ, CE A₀ ∧ CE A₁ ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = A ∧
        ¬ (A ≤ᵀ A₀) ∧ ¬ (A ≤ᵀ A₁)
```

stated in `FriedbergMuchnik`'s own vocabulary (`CE`, `ComputableSet`, `≤ᵀ`),
imported, not redefined. `FriedbergMuchnik` is a Lake **path dependency**
(`require FriedbergMuchnik from "../friedberg-muchnik-lean"`); no FM file is
copied into this project.

---

## Part 1 — The reuse inventory (written before any construction code)

Verdicts: **as-is** = imported and used unchanged; **generalized** = FM
lemma changed in place in the FM repo, separately committed; **rebuilt** =
Sacks needs its own version, with the reason stated.

### Foundation layer — `FriedbergMuchnik/Foundation/`

| FM component | Verdict | Notes |
|---|---|---|
| `OracleCode` (syntax) | **as-is** | Sacks diagonalises against the same programs. |
| `encodeCode` / `ofNatCode`, both round-trips, `ofNatCode_surjective` | **as-is** | Requirement `j` decodes to program `ofNatCode (j / 2)` and half `j % 2`. `ofNatCode_encodeCode` is what turns "for every index `j`" into "for every reduction" — identical role to FM's enumeration adequacy. |
| `run`, `RunResult`, `HaltData`, `PartOracle`, step lemmas, `run_halt_input_lt` | **as-is** | The step-indexed evaluator is untouched. |
| `run_halt_mono` (the use principle) and `run_halt_fuel_mono`, `run_halt_oracle_ext`, `run_halt_of_consistent` | **as-is** | |
| `run_halt_unique` | **as-is**, but load-bearing in a new way | In FM this only says a computation has one output. In Sacks it is what makes **the use of a limit computation a well-defined number `U(y)`**, and `U` is exactly what bounds the restraint function. Without *recorded* use plus its uniqueness, the restraint-boundedness lemma has no statement to prove. This is the single most valuable thing inherited from FM. |
| `Computes`, `Computes.unique` | **as-is** | Used at every "the preserved computation contradicts the reduction" step. |
| `initialSegment`, `computes_iff_initialSegment` | not needed | The approximation layer's snapshot lemmas subsume them here. |
| `charFun`, `natOfBool`, `TuringReducible` (`≤ᵀ`), `CE`, `ComputableSet`, `TuringReducible.refl`, `ComputableSet.turingReducible` | **as-is** | Imported, not re-defined, so the theorem is stated in FM's vocabulary. |
| `subst`, `TuringReducible.trans` (`Foundation/Composition.lean`) | available, not needed | The conclusion is a *negation* of reducibility, so nothing is chained. See the correction under "inherited limitations" below. |
| `embed`, `run_embed`, `partrec_realized`, `ce_of_partrec_dom` | **as-is**, one in a new direction | `ce_of_partrec_dom` certifies `CE A₀`/`CE A₁` exactly as in FM. `partrec_realized` is used for something FM never needed: turning the decision procedure "search for a stage of long agreement" into an oracle-free `OracleCode`, i.e. **producing** a `ComputableSet`. The lemma needed no change; it simply had no consumer before. |
| `nrun`, `nrun_primrec`, `encodeResult` lemmas, `run_timeout_of_ge` | **as-is** | Sacks's stage function consults `run` only through `nrun`, exactly as FM's does — which is what keeps the whole construction primitive recursive. |

### Approximation layer — `FriedbergMuchnik/Approximation.lean`

| FM component | Verdict | Notes |
|---|---|---|
| `StageMono`, `limitSet`, `StageMono.subset_of_le` | **as-is** | Instantiated three times: for `A`'s own enumeration and for each half. |
| `StageMono.stabilizesBelow` | **as-is** | The workhorse of injury finiteness: below a fixed bound only finitely much ever happens, so past some stage no injury below that bound can occur. |
| `snapshot`, `snapshot_getElem?`, `ofSnapshot_snapshot_some` | **as-is** | |
| **`run_halt_limit_of_restraint`** | **as-is** | This is the lemma the brief hoped could be reused directly for the restraint argument, and it can be, verbatim: its statement is already generic in the stage sequence `F`, so it applies to the Sacks halves with no generalization. Sacks is a pure preservation argument, so this single lemma carries more of the proof here than it does in FM. |
| `run_halt_snapshot_of_limit` | **as-is** | The "true stage" step: a limit computation is visible from some stage on. |
| `snapshotOf`, `snapshotOf_eq_snapshot`, `snapshotOf_getElem?`, `run_halt_toFinset_snapshot` | **as-is** | All generic in the list; they live in FM's construction files (`Construction.lean`, `Requirements.lean`) but none of them mentions the FM construction. |
| `range_find?_least` (`StageDynamics.lean`) | **as-is** | "`List.find?` over a range finds the least index." FM uses it for the priority discipline (which requirement receives attention); Sacks uses it for the routing rule (which requirement's restraint wins). Same lemma, different priority mechanism. |

### Priority layer — the FM-specific files

| FM component | Verdict | Reason |
|---|---|---|
| `ConsState` / `ReqState`, `stepAt`, `stepState`, `stageState`, `convCheck`, `requiresAttention` | **rebuilt** | These encode the FM *strategy*: appoint a fresh witness, wait for `Φ_e(x)↓ = 0`, enumerate `x`. Sacks has no witnesses and no diagonalisation move — elements arrive from `A`'s enumeration and are only *routed*. The Sacks state is correspondingly smaller: two enumeration lists and one cumulative restraint per requirement. |
| `attended`, `attended_least`, `step_cases`, `Alist_succ` / `Blist_succ`, `fresh_mono` (`StageDynamics.lean`) | **not applicable** | This is the specification layer of FM's step function, built around "exactly one requirement receives attention per stage". A Sacks stage has no attended requirement at all: every requirement's restraint is consulted at every stage, and the only decision is which half each new element goes to. The analogue is one routing lemma. |
| `ConsInv` (ten fields), `consInv_ext` / `consInv_appoint` / `consInv_act`, `consInv_stage` (`Invariants.lean`) | **not applicable** | Freshness counters, witness distinctness and `wit_ge` exist to stop FM's *freely chosen* witnesses from injuring higher priorities. Sacks does not choose its elements, so there is nothing to keep fresh. The Sacks analogue is two invariants — the halves stay disjoint, and their union is the current stage of `A` — proved by one induction. |
| `rank`, `reqRank`, `reqRank_incr`, `quiet_above`, `exists_stable`, `stable_not_requires` (`FiniteInjury.lean`) | **rebuilt** — the sharpest finding | FM's injury induction is a **rank** argument: a requirement's record has rank in `{0,1,2}`, attention strictly raises it, only injury resets it, so once superiors are quiet a requirement acts at most twice more. That argument cannot be restated for Sacks, because **Sacks requirements never act**: their restraint moves continuously with the length of agreement, and there is no discrete event to count. See Part 2 for what replaces it. Same *shape* (induction along the priority order, no closed-form bound), disjoint content. No generalization of FM's file would have helped; the two are siblings, not instances of a common lemma. |
| `R_satisfied` / `S_satisfied`, `restraint_respected_A` / `_B`, `not_A_le_B` / `not_B_le_A` (`Requirements.lean`) | **rebuilt** | Different strategy ⇒ different satisfaction proof. The final two-line step (*any candidate reduction is `ofNatCode e` for its own number `e`, so requirement `e` kills it*) is reused in shape, via `ofNatCode_encodeCode`. |
| `CE.lean`'s parallel-implementation technique (`St`, `RS`, `encSt`, `encSt_stage`, `map_range_set`, `map_range_act`) | **deliberately not needed** | FM had to build a shadow implementation on plain tuples because `ConsState`/`ReqState` are custom structures with no `Primcodable` instance. Sacks defines its state as a plain tuple type from the outset, so the shadow layer and its simulation theorem disappear entirely. The `Primrec` derivation and the `Partrec.rfind` + `ce_of_partrec_dom` ending have the same shape as FM's. |
| `primrec_find?`, `primrec_memDecide`, `primrec_snapshotOf` (in FM's `CE.lean`) | **generalized in FM** | These three are entirely generic — nothing about them mentions the FM construction — but they were `private`, so they were invisible to any downstream package. De-privatising them (plus docstrings) is the **only change FM needed** to serve as a foundation here. Committed separately in the FM repo. |

### One defect found and fixed in FM

FM's root module `FriedbergMuchnik.lean` imported
`FriedbergMuchnik.Foundation.MathlibOracleBridge`, a file that does not
exist (added by the last commit, `83432a8`). `lake build` therefore failed
outright on a clean checkout, so FM could not be depended on at all until
the stray import was removed. Fixed and committed separately. With it
removed, FM builds clean and
`#print axioms FriedbergMuchnik.friedberg_muchnik` reports exactly
`[propext, Classical.choice, Quot.sound]`.

### Inherited limitations — one correction to the brief

The brief asks that FM's "known limitation (transitivity of the local `≤ᵀ`
not yet proved)" be inherited and noted. That limitation no longer exists:
`TuringReducible.trans` is proved in `Foundation/Composition.lean` (FM
commit `247ecef`), by query substitution, and with `TuringReducible.refl`
the project's `≤ᵀ` is a preorder with a `Trans` instance. FM's `STATUS.md`
still lists it as open; its `README.md` records it as closed. Nothing here
assumes transitivity in any case. What *is* still inherited: `≤ᵀ` has not
been proved equivalent to a standard external formulation (e.g. Mathlib's
`RecursiveIn`), so "not reducible" means "not reducible in this model", for
a model whose adequacy rests on FM's foundation gate.

---

## Part 2 — Sacks requirements mapped to their FM analogues

| | Friedberg–Muchnik | Sacks Splitting |
|---|---|---|
| Requirement `j` | `R_e : A ≠ Φ_e^B` (`j = 2e`), `S_e : B ≠ Φ_e^A` (`j = 2e+1`) | `N_j : A ≠ Φ_e^{A_i}` with `e = j / 2`, `i = j % 2` |
| Sets built | `A`, `B`, from nothing | `A₀`, `A₁`, a partition of the *given* `A` |
| How an element enters | requirement `j` chooses a fresh witness `x` and enumerates it | `A`'s own enumeration produces `x`; the construction only chooses **which half** |
| Positive action | enumerate the witness, creating the disagreement | none — the disagreement is found, never made |
| Restraint | protect the frozen `Φ_e(x)↓ = 0` by keeping numbers below its use out of the oracle set | protect the whole current agreement `Φ_e^{A_i} ↾ ℓ = A ↾ ℓ` by keeping numbers below its use out of `A_i` |
| Injury | a higher-priority requirement acts and initialises `j` | a number below `j`'s restraint is routed into `A_i` because a *higher-priority, opposite-parity* requirement also restrains it |
| Why the requirement is satisfiable | the witness is fresh, so enumerating it is always allowed | **`A` is not computable** — if `Φ_e^{A_i}` computed `χ_A`, the preserved agreement would decide `A` |
| Injury finiteness | rank argument: rank in `{0,1,2}`, attention raises it | restraint boundedness: bounded restraints below `j` confine injuring elements to a finite initial segment of `A`, which stabilises |

The one genuinely new piece of mathematical content, flagged as the brief
requires, is the last row's right-hand cell:

> **`unsatisfied_requirement_computes`** (`SacksSplitting/FiniteInjury.lean`):
> if requirement `N_j` is never injured after some stage and
> `Φ_e^{A_i}` totally and correctly computes `χ_A`, then `ComputableSet A`.

Its proof: past the last injury, any agreement seen at a stage is frozen by
`run_halt_limit_of_restraint`, so `A(y)` equals its stage-`s` approximation
at any stage `s` whose agreement length exceeds `y`; totality of the
reduction makes such stages exist; the search for one is computable because
the whole construction is primitive recursive. `ComputableSet A`
contradicts the hypothesis, so every requirement is satisfied. FM has no
analogue of this lemma — it had no hypothesis on any given set to exploit.

---

## Part 3 — Status: done

`lake build` succeeds; zero `sorry`, zero `admit`, zero added axioms.

```
'SacksSplitting.sacks_splitting' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

— the same footprint as `FriedbergMuchnik.friedberg_muchnik`, checked
side by side.  Nothing extra crept in through the dependency.

1,556 lines across six files, against FM's 4,254 across nineteen.  The
ratio is the inventory's verdict in one number: the expensive part —
foundation, evaluator, use principle, Mathlib bridge — was already there.

| File | Lines | |
|---|---:|---|
| `Basic.lean` | 170 | `CE A` → explicit monotone stage enumeration |
| `Requirements.lean` | 233 | agreement test, agreement length, restraint |
| `Construction.lean` | 267 | routing machine, two invariants |
| `CE.lean` | 398 | `Primrec` derivation, `CE` of both halves, the decision procedure |
| `FiniteInjury.lean` | 388 | the priority induction |
| `Main.lean` | 84 | the theorem |

Non-vacuity is proved, not asserted: `sacks_splitting_friedbergMuchnik`
applies the theorem to FM's own `Aset`, using FM's `ce_Aset` and
`Aset_not_computable` unchanged.  And the split is proved non-degenerate:
`halfSet_ne` shows neither half can be all of `A`, since reflexivity of
`≤ᵀ` would then contradict the non-reducibility just proved.

### Honest accounting — what the exercise actually showed

**The foundation is a foundation.** Every item in the first two tables of
Part 1 was imported and used without modification. Two are worth singling
out because they were the load-bearing ones and neither needed a
generalization:

* `run_halt_limit_of_restraint` is already stated generically in the stage
  sequence `F`, so the restraint argument — the heart of Sacks — reused it
  verbatim. This was the brief's central open question and the answer is
  clean.
* `run_halt_unique` turned out to matter more here than in FM. It is what
  makes "the use of the limit computation at `y`" a well-defined number
  (`limUse`), which is what bounds the restraint. A design decision made
  for FM (record the use, not just the output) paid off for a theorem it
  was not designed for. That is the strongest evidence in this exercise
  that the foundation generalizes.

**The priority layer is not, and could not have been.** FM's
`FiniteInjury.lean` counts events: a requirement's record has a rank in
`{0,1,2}`, receiving attention raises it, so once superiors are quiet it
acts at most twice more. A splitting requirement generates no events — it
never acts, and its restraint moves continuously with the length of
agreement. The replacement is a different argument (bounded restraints
below `j` ⇒ finite injury to `j` ⇒ `j` satisfied ⇒ `j`'s restraint
bounded, by strong induction on `j`). We looked for a common
generalization and there is none worth stating: the two files share a
*shape* (induction along the priority order, no closed-form bound) and no
content. Recording this as "rebuilt" is the accurate verdict, not a
failure of FM's design.

**One reusability defect, and it was about access, not about
mathematics.** Three `Primrec` helpers in FM's `CE.lean` are entirely
generic and were `private`. Nothing needed generalizing; they needed
*exporting*. This is worth naming because it is the kind of thing that is
invisible until someone tries to build on the code: FM's own build never
noticed, and its README's claim to be a foundation was untested until now.
The same is true of the stray import in the root module, which meant the
package did not build at all on a clean checkout.

**Where the two developments diverge structurally.** Two places where FM's
own difficulty simply did not arise here, both traceable to FM's design
choices rather than to Sacks being easier:

* FM's `Invariants.lean` (ten-field `ConsInv`) has no counterpart. Its
  fields exist to keep freely chosen witnesses fresh, distinct, and clear
  of higher-priority restraints. Sacks does not choose its elements, so
  the entire bookkeeping evaporates; the two invariants that remain
  (halves disjoint, union = current stage of `A`) are one induction.
* FM's shadow-implementation layer in `CE.lean` (`St`, `RS`, `encSt`,
  `encSt_stage`, `map_range_set`, `map_range_act`) has no counterpart
  either, because this construction's state is a plain tuple and so has a
  `Primcodable` instance for free. If FM were rewritten today, defining
  `ConsState` as a tuple would delete roughly half of its `CE.lean`.

**One design decision forced by the mathematics, worth flagging.** The
restraint is *cumulative* — `R(j, s+1) = max (R(j, s)) (restraintAt … s
j)` — kept in the state. The raw stage restraint is not monotone: the
length of agreement drops whenever a number below it enters `A`, and a
restraint that can drop protects nothing, since a computation frozen at
stage `s` could be destroyed later merely because its requirement had
temporarily stopped asking. FM needed no such device, its restraint being
written once when a requirement acts. This is the one place where the
finite-injury *pattern* had to be adapted rather than instantiated.

### Inherited limitations

* `≤ᵀ` is FM's, imported. Its foundational adequacy (enumeration
  adequacy, the Mathlib bridge, the use principle) is FM's foundation
  gate; it has **not** been proved equivalent to an external formulation
  such as Mathlib's `RecursiveIn`. "Not reducible" therefore means "not
  reducible in this model". Unchanged from FM, and untouched here.
* Transitivity of `≤ᵀ` is *not* an open item — see the correction in Part
  1. Nothing here uses it in any case.
* Lowness of the halves is out of scope by the brief.
