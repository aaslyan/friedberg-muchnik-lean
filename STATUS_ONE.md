# Verification report: `aaslyan/friedberg-muchnik-lean` @ `b613d62`

**Verdict: Yes — the theorem is proved.** A fresh clone builds successfully
(`Build completed successfully (811 jobs)`, 2m17s wall-clock), and
`#print axioms FriedbergMuchnik.friedberg_muchnik` reports exactly
`[propext, Classical.choice, Quot.sound]` — confirmed by running the check
directly on the fresh clone, not inferred from the README; the escape-hatch
grep over all project `.lean` files is genuinely empty.

## Part 1 — Mechanical verification

**Clone**: fresh, into an isolated directory. HEAD =
`b613d624497e6c8a485eafe891d9398a9e177764`. The only commit beyond the
development history is `b613d62` ("Draft paper…"), which touches only
`paper/*` — no Lean sources.

**Cache + build**: `lake exe cache get` succeeded ("No files to download /
Decompressing 7727 file(s) / Completed successfully!" — the host had a warm
`~/.cache/mathlib`, so no network fetch was exercised; on a cold machine
this step downloads several GB). Full `lake build` output (this is the
complete log — Mathlib's 793 jobs came from cache and produce no lines):

```
✔ [794/811] Built FriedbergMuchnik.Foundation.OracleCode (281ms)
✔ [795/811] Built FriedbergMuchnik.Foundation.Numbering (1.1s)
✔ [796/811] Built FriedbergMuchnik.Foundation.FiniteEval (1.2s)
✔ [797/811] Built FriedbergMuchnik.Foundation.RunPrimrec (1.7s)
✔ [798/811] Built FriedbergMuchnik.Foundation.Use (2.2s)
✔ [799/811] Built FriedbergMuchnik.Foundation.InfiniteEval (725ms)
✔ [800/811] Built FriedbergMuchnik.Foundation.Reducibility (787ms)
✔ [801/811] Built FriedbergMuchnik.Approximation (831ms)
✔ [802/811] Built FriedbergMuchnik.Foundation.MathlibBridge (1.4s)
✔ [803/811] Built FriedbergMuchnik.Construction (1.0s)
✔ [804/811] Built FriedbergMuchnik.StageDynamics (1000ms)
✔ [805/811] Built FriedbergMuchnik.Invariants (1.3s)
✔ [806/811] Built FriedbergMuchnik.FiniteInjury (1.5s)
✔ [807/811] Built FriedbergMuchnik.Requirements (1.2s)
✔ [808/811] Built FriedbergMuchnik.CE (126s)
✔ [809/811] Built FriedbergMuchnik.Main (809ms)
✔ [810/811] Built FriedbergMuchnik (718ms)
Build completed successfully (811 jobs).

real	2m17.164s
user	2m28.642s
sys	0m4.389s
```

Succeeded; no warnings, no errors. `CE.lean` at 126s is the documented
hotspot (raised `maxHeartbeats` on two `Primrec` declarations — elaboration
cost only, no logical content).

**Axiom check** (verbatim, complete):

```
FriedbergMuchnik.friedberg_muchnik :
  ∃ A B,
    FriedbergMuchnik.CE A ∧
      FriedbergMuchnik.CE B ∧ ¬FriedbergMuchnik.TuringReducible A B ∧ ¬FriedbergMuchnik.TuringReducible B A
'FriedbergMuchnik.friedberg_muchnik' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Escape-hatch grep**: the exact command from the task, run over every
project `.lean` file (excluding `.lake/`), produced **no output** (exit 1 =
zero matches). No `sorry`, `admit`, `native_decide`, `opaque`, or `unsafe`
anywhere in the build closure of the project's own files.

## Part 2 — Critical review

**1. Is `TuringReducible` genuinely total, oracle-using reduction? — Fine,
with one documented scope caveat.**
`Reducibility.lean`: `TuringReducible A B := ∃ c, ∀ x, Computes c
(charFun B) x (natOfBool (charFun A x))`, with `Computes c X x y :=
∃ k d, run k (PartOracle.ofFun X) c x = .halt d ∧ d.output = y`
(`InfiniteEval.lean`). This requires halting on **every** `x` (the `∀ x` is
outside), with output exactly the membership bit; the oracle is
everywhere-defined (`ofFun`), so no `stuck`-based vacuity;
`Computes.unique` (via `run_halt_unique`, `Use.lean`) pins the output, so a
program can't "compute" two different bits. `charFun` is classical `decide`
— a legitimate specification-level characteristic function; there is no
pathological `A`,`B` for which the relation degenerates. Oracle-ignoring
programs satisfying `A ≤ᵀ B` for computable `A` is *correct* behavior
(proved as `ComputableSet.turingReducible`). The one real caveat: `≤ᵀ`
quantifies over *this project's* `OracleCode` programs, and the repo does
not prove equivalence with an independent formulation (e.g. Mathlib's
`RecursiveIn`). The model is the textbook relativized Kleene presentation
(schemata + `query`), and `MathlibBridge.partrec_realized` proves every
Mathlib-partial-recursive function is realized — so the negative statements
are not vacuous — but "this model = standard relative computability" rests
on reading the 9-constructor definition, not on a formal bridge. The README
states this openly (the deferred composition/transitivity item).
**Verdict: fine; the model-internality is a known, documented limitation,
standard for self-contained formalizations — a human should judge whether
that scope suffices for their purposes.**

**2. Is `CE` the real halting-domain definition? — Fine.**
`CE A := ∃ c, ∀ x, x ∈ A ↔ ∃ k d, run k PartOracle.empty c x = .halt d` —
the classical `A = W_e` (domain, empty oracle; queries yield
`stuck ≠ halt`, so query-touching paths correctly diverge). The fuel
existential can't be gamed: `run` is fuel-monotone and deterministic, so
`∃ k` is genuine halting; and the **iff for all `x`** forces the domain to
equal `A` exactly — it cannot hold "independent of whether `x` is really in
`A`". `ce_Aset`/`ce_Bset` (`CE.lean`) instantiate this for the actual
`Aset := limitSet AstageF` through the simulation theorem `encSt_stage`
(proved by induction, not assumed) and `mem_Alist_iff_stageN`. Note also:
`CE ≠ ComputableSet` is not certified by a standalone lemma, but it follows
in one line from the theorem itself (if `Aset` were `ComputableSet`,
`ComputableSet.turingReducible` would give `Aset ≤ᵀ Bset`, contradicting
`not_A_le_B`). **Verdict: fine.**

**3. Does the rank argument cover all injury? — Fine (and the question's
premise needs one correction).**
`idleSt`/`appointSt`/`actSt` live in `CE.lean` — they are the *parallel
computability implementation* and play no role in the injury argument. The
injury argument runs on the real machine: `stageState`
(`Construction.lean`) is literally the iteration of `stepState`, and
`StageDynamics.step_cases` is a **hypothesis-free theorem** proving that
`stageState (s+1)` is exactly one of three states (idle / appoint / act),
derived from `stageState_succ : … := rfl`. Because it is a proved
trichotomy about the actual definition — not a modeling assumption — any
unmodeled code path in `stepState` would have made `step_cases`
unprovable. (The one syntactic extra path, `stepAt`'s `convCheck = none`
fallback, is dead when the index was attended, and `step_cases`'s proof
extracts `some u` from `requiresAttention` accordingly.)
`reqRank_incr`/`reqRank_mono`/`record_step_stable` (`FiniteInjury.lean`)
all case on `step_cases` or on `reqs_getElem?_succ_of_lt` (itself proved
from `step_cases`), so appointments by other requirements, actions above,
actions below, and idle stages are each covered. **Verdict: fine —
exhaustiveness is machine-checked, not asserted.**

**4. Could `convCheck` systematically miss converged computations? — False
alarm.**
`convCheck` uses fuel `s` *and* snapshot length `s` (`Construction.lean`) —
the growth rates are identical, and more importantly, detection is not left
informal: the never-acted branch of `R_satisfied`
(`Requirements.lean:182–196`) *proves* eventual detection —
`run_halt_snapshot_of_limit` produces a halt at fuel `k`, snapshot length
`d.use`; `run_halt_toFinset_snapshot` lifts it to fuel `s`, length `s` for
`s ≥ max(k, d.use, …)`; `ConsState.convCheck_eq_some` converts it into
`convCheck = some du`; `requiresAttention_eq_true` then contradicts
`stable_not_requires`. A bad fuel/length growth mismatch would have made
this chain unprovable, not silently weakened the theorem. **Verdict:
fine.**

**5. Does the acted case ever actually fire? — Yes, provably (though the
repo doesn't state it as a lemma).**
Both branches of `R_satisfied`/`S_satisfied` carry full machine-checked
proofs, and the case split is on the actual stable record — the prover
doesn't get to choose. Moreover the acted branch is *forced* to occur: take
`e = 0`, so the reduction code is `ofNatCode 0 = .zero`
(`Numbering.lean:63`), which halts with output `0` on every input
(`run_zero_step`, `FiniteEval.lean:184`). If requirement `i = 0`'s stable
record had `acted = false` forever, then at every large stage its
`convCheck` succeeds (the zero code always "claims `x ∉ A`"), so
`requiresAttention` would be true — contradicting `stable_not_requires`.
Hence requirement 0's stable record has `acted = true`, and the acted
branch (restraint preservation via `run_halt_limit_of_restraint`,
`acted_comp`, `wit_ge`) is genuinely exercised by the construction, exactly
as the informal narrative says. This corollary is derivable from lemmas
already in the repo but is not stated; adding it (e.g.
`∃ s r, … r.acted = true`) would be a cheap strengthening. **Verdict:
fine; optional hardening noted.**

**6. Numbering coverage — False alarm.**
`ofNatCode_encodeCode : ∀ c : OracleCode, ofNatCode (encodeCode c) = c`
(`Numbering.lean:75`) is proved by **structural induction over the
inductive type** — one equation per constructor with recursive calls on
subterms, totality checked by Lean — so it covers codes of arbitrary
nesting depth, not "up to some depth". `encodeCode_ofNatCode` gives the
other round-trip by strong induction on `ℕ`, so the numbering is a genuine
bijection, and `not_A_le_B`/`not_B_le_A` use it on an *arbitrary* candidate
`c` (`e := encodeCode c`), so no reduction escapes the requirement list.
**Verdict: fine.**

**7. Anything else formally-true-but-weaker-than-advertised?** Three honest
notes, none affecting the theorem's validity:

- **`≤ᵀ` is not proven to be a preorder** — reflexivity and
  computable-⇒-reducible-to-everything are proved (`Reducibility.lean`),
  but transitivity/closure-under-composition (the query-substitution
  operator) is an acknowledged open task in the README. Irrelevant to
  Friedberg–Muchnik itself, but part of what makes a relation "recognizably
  `≤ᵀ`"; together with item 1's model-internality, this is the main thing a
  referee would ask for.
- **Restraint convention consistency** (checked, fine): `HaltData.use` is a
  *strict* bound on queried positions, restraints protect `n < use`, and
  `wit_ge` allows witnesses `= restraint` — these three line up
  (`Use.lean`, `Invariants.lean`, `restraint_respected_B`), so there is no
  off-by-one soundness hole; I verified the actual inequalities, not the
  docstrings.
- **Elaboration budgets, not logic**: the raised `maxHeartbeats` in
  `CE.lean` affect only elaboration cost; the axiom check above is the
  ground truth that no logical shortcut was taken.

**Overall**: the build claims hold up exactly as stated, and of the seven
probes, five are clean false alarms, one (item 5) suggests a cheap optional
lemma, and the one substantive caveat — `≤ᵀ` and `CE` being definitions
internal to the project's own (textbook-standard, Mathlib-anchored) machine
model, without a formal equivalence to an independent formulation — is
real, pre-existing, and documented in the repo itself rather than hidden.
