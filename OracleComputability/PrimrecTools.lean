import OracleComputability.RunPrimrec
import OracleComputability.Approximation

/-!
# Generic `Primrec` helpers for stage functions

Three facts with nothing in them about any construction: `List.find?` is
primitive recursive, list membership is primitive recursive, and so is the
Boolean snapshot of an enumeration list.

They are separated out because a priority construction cannot be shown
computable without them — a stage function scans a priority list and feeds
the current enumeration to the evaluator as an oracle — and because they
are exactly the sort of thing that silently becomes unreusable if it is
left `private` inside one theorem's computability file, which is where they
started.
-/

namespace OracleComputability

/-- `List.find?` is primitive recursive (as a `foldr` accumulating the
first hit). -/
theorem primrec_find? {α β : Type _} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a ↦ (f a).find? (p a) := by
  have h : Primrec fun a ↦ (f a).foldr
      (fun b acc ↦ bif p a b then some b else acc) (none : Option β) :=
    Primrec.list_foldr hf (Primrec.const none)
      (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  refine h.of_eq fun a ↦ ?_
  induction f a with
  | nil => rfl
  | cons b l ih =>
    cases hpb : p a b with
    | true => simp [hpb]
    | false => simp [hpb, ih]

/-- Membership in a list of naturals is primitive recursive. -/
theorem primrec_memDecide :
    Primrec₂ fun (x : ℕ) (l : List ℕ) ↦ decide (x ∈ l) := by
  have heqd : Primrec fun q : (ℕ × List ℕ) × ℕ × Bool ↦
      decide (q.1.1 = q.2.1) :=
    (PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)).decide
  have h : Primrec fun q : ℕ × List ℕ ↦
      q.2.foldr (fun b acc ↦ decide (q.1 = b) || acc) false :=
    Primrec.list_foldr Primrec.snd (Primrec.const false)
      ((Primrec.dom_bool₂ (· || ·)).comp heqd
        (Primrec.snd.comp Primrec.snd)).to₂
  refine h.to₂.of_eq fun x l ↦ ?_
  induction l with
  | nil => simp
  | cons b l ih => simp [List.mem_cons, ih]

/-- The Boolean snapshot of an enumeration list is primitive recursive in
the list and the bound — so a stage function may feed the current
enumeration to the evaluator as an oracle and stay computable. -/
theorem primrec_snapshotOf : Primrec₂ snapshotOf := by
  have h : Primrec fun q : List ℕ × ℕ ↦
      (List.range q.2).map fun j ↦ decide (j ∈ q.1) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      (primrec_memDecide.comp Primrec.snd (Primrec.fst.comp Primrec.fst))
  exact h

end OracleComputability
