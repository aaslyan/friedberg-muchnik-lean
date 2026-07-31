/-
# Least-index selection

One lemma, but a shared one: `List.find?` over an initial segment of `ℕ`
returns the *least* satisfying index, together with the fact that every
smaller index fails.

Every priority construction needs exactly this, because "priority" always
comes down to picking the least index with some property and knowing that
nothing above it qualified.  The two constructions in this repository use
it for different purposes — Friedberg–Muchnik to pick the highest-priority
requirement that *requires attention*, Sacks splitting to pick the
highest-priority requirement whose *restraint* covers an incoming number —
so it belongs to neither of them.
-/
import Mathlib.Data.List.Basic

namespace FriedbergMuchnik

/-- `List.find?` over a `range` finds the least satisfying index, and every
index below it fails the test. -/
theorem range_find?_least {n : ℕ} {p : ℕ → Bool} {i : ℕ}
    (h : (List.range n).find? p = some i) :
    p i = true ∧ i < n ∧ ∀ j, j < i → p j = false := by
  refine ⟨List.find?_some h, by simpa using List.mem_of_find?_eq_some h, ?_⟩
  rw [List.find?_eq_some_iff_append] at h
  obtain ⟨hp, as, bs, heq, hfail⟩ := h
  have hlen : as.length < n := by
    have := congrArg List.length heq
    simp at this
    omega
  have hidx : as.length = i := by
    have h1 : (List.range n)[as.length]? = some i := by
      rw [heq, List.getElem?_append_right (Nat.le_refl _)]
      simp
    rw [List.getElem?_range hlen] at h1
    exact Option.some.inj h1
  intro j hj
  have hjas : j ∈ as := by
    have has : as = List.range i := by
      have htake := congrArg (List.take as.length) heq
      rw [List.take_left] at htake
      rw [← htake, hidx, List.take_range]
      congr 1
      omega
    rw [has, List.mem_range]
    exact hj
  simpa using hfail j hjas

end FriedbergMuchnik
