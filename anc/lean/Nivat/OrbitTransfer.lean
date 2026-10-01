/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Orbit

/-!
# Transfer of properties along the orbit closure

Auxiliary lemmas for §8 of *The Convex Nivat Conjecture* (Pan).

Several arguments of §8 replace a counterexample `ξ` by a configuration `ξ' ∈ orbitClosure ξ`
with better properties (Theorem 8.7, Corollary 8.10) and then need to re-apply to `ξ'` a
hypothesis that was stated for `ξ` — typically the alphabet bounds `0 < ξ z` and `ξ z < p`
required by `Nivat.isPeriodic_modP_iff`.  This file collects those transfers.

The mechanism is uniform and cheap: applying the defining property of `orbitClosure` to the
one-point window `{z}` shows that **every value of `x` is a value of `θ`**
(`exists_apply_eq_of_mem_orbitClosure`).  Hence any property of the form "all values of `θ`
satisfy `p`" descends to `x` for free (`forall_apply_of_mem_orbitClosure`); the bounds and the
finiteness of the range are the three instances used downstream.

Complexity is different: it is *not* a pointwise property, and it descends only under a
finiteness assumption on the patterns — see `Nivat.P_le_of_mem_orbitClosure` in
`Nivat/Defs/Orbit.lean`, which already proves `P x W ≤ P θ W` from `(patterns θ W).Finite`.
The lemmas here are the two convenient packagings of it: from a finite alphabet, and from a
configuration of finite range (the §8 situation, where the alphabet is a finite subset of `ℤ`).

## Main results

* `Nivat.exists_apply_eq_of_mem_orbitClosure` — every value of `x` is a value of `θ`.
* `Nivat.lt_of_mem_orbitClosure`, `Nivat.pos_of_mem_orbitClosure` — the alphabet bounds of §8.
* `Nivat.range_finite_of_mem_orbitClosure` — finiteness of the alphabet.
* `Nivat.lowConvexComplexity_of_mem_orbitClosure` — low convex complexity, paper (8.1).

## Status

Complete; no `sorry`.
-/

namespace Nivat

variable {α : Type*}

/-! ### Pointwise transfer

Every value taken by a member of the orbit closure is already taken by `θ`; this is the
defining property of `orbitClosure` applied to a one-point window. -/

/-- Every value of a member of the orbit closure is a value of `θ`: for each `z` there is a
`u` with `x z = θ u`.  This is `mem_orbitClosure_iff` for the window `{z}`. -/
theorem exists_apply_eq_of_mem_orbitClosure {θ x : Config α} (hx : x ∈ orbitClosure θ)
    (z : ℤ × ℤ) : ∃ u : ℤ × ℤ, x z = θ u :=
  let ⟨u, hu⟩ := hx {z}
  ⟨u + z, hu z (Finset.mem_singleton_self z)⟩

/-- Any property of `θ` of the form "every value satisfies `p`" passes to the orbit closure.
All the pointwise transfers below are instances of this. -/
theorem forall_apply_of_mem_orbitClosure {θ x : Config α} (hx : x ∈ orbitClosure θ)
    {q : α → Prop} (h : ∀ z, q (θ z)) (z : ℤ × ℤ) : q (x z) := by
  obtain ⟨u, hu⟩ := exists_apply_eq_of_mem_orbitClosure hx z
  rw [hu]
  exact h u

/-- The alphabet does not grow along the orbit closure. -/
theorem range_subset_of_mem_orbitClosure {θ x : Config α} (hx : x ∈ orbitClosure θ) :
    Set.range x ⊆ Set.range θ := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨u, hu⟩ := exists_apply_eq_of_mem_orbitClosure hx z
  exact ⟨u, hu.symm⟩

/-- A member of the orbit closure of a configuration of finite range again has finite range.
Paper §8.2: the alphabet `A` is shared by the whole orbit closure. -/
theorem range_finite_of_mem_orbitClosure {θ x : Config α} (hx : x ∈ orbitClosure θ)
    (h : (Set.range θ).Finite) : (Set.range x).Finite :=
  h.subset (range_subset_of_mem_orbitClosure hx)

/-- The upper alphabet bound `ξ z < p` of §8.2 passes to the orbit closure.  Together with
`pos_of_mem_orbitClosure` this supplies the two hypotheses of `Nivat.isPeriodic_modP_iff`
for a configuration `x ∈ orbitClosure ξ`. -/
theorem lt_of_mem_orbitClosure {ξ x : Config ℤ} (hx : x ∈ orbitClosure ξ) {p : ℕ}
    (h : ∀ z, ξ z < p) : ∀ z, x z < p :=
  forall_apply_of_mem_orbitClosure (q := fun a => a < (p : ℤ)) hx h

/-- Positivity of the alphabet passes to the orbit closure.  Paper §8.2, `A ⊆ ℤ_{>0}`. -/
theorem pos_of_mem_orbitClosure {ξ x : Config ℤ} (hx : x ∈ orbitClosure ξ)
    (h : ∀ z, 0 < ξ z) : ∀ z, 0 < x z :=
  forall_apply_of_mem_orbitClosure (q := fun a => 0 < a) hx h

/-! ### Complexity transfer

`P x W ≤ P θ W` is `Nivat.P_le_of_mem_orbitClosure`, which needs `(patterns θ W).Finite`:
`Set.ncard` of an infinite set is `0`, so without that hypothesis the inequality is false.
The two lemmas here discharge it in the two situations that occur. -/

/-- Complexity does not increase along the orbit closure, over a finite alphabet. -/
theorem P_le_of_mem_orbitClosure_of_finite [Finite α] {θ x : Config α}
    (hx : x ∈ orbitClosure θ) (W : Finset (ℤ × ℤ)) : P x W ≤ P θ W :=
  P_le_of_mem_orbitClosure hx W (patterns_finite θ W)

/-- Complexity does not increase along the orbit closure of a configuration of finite range.
Paper (8.1).  This is the form used in §8, where the alphabet is a finite subset of `ℤ` and so
the ambient type is infinite. -/
theorem P_le_of_mem_orbitClosure_of_range_finite {θ x : Config α} (hx : x ∈ orbitClosure θ)
    (hfin : (Set.range θ).Finite) (W : Finset (ℤ × ℤ)) : P x W ≤ P θ W :=
  P_le_of_mem_orbitClosure hx W (patterns_finite_of_range_finite hfin W)

/-- Low convex complexity passes to the orbit closure: the same window `S` works.  Paper
Remark 8.3 and (8.1); this is the step used in `IsMinimalCounterexample.of_mem_orbitClosure`. -/
theorem lowConvexComplexity_of_mem_orbitClosure {θ x : Config α} (hx : x ∈ orbitClosure θ)
    (hfin : (Set.range θ).Finite) (h : LowConvexComplexity θ) : LowConvexComplexity x := by
  obtain ⟨S, hne, hconv, hle⟩ := h
  exact ⟨S, hne, hconv, (P_le_of_mem_orbitClosure_of_range_finite hx hfin S).trans hle⟩

/-- Low convex complexity passes to the orbit closure, over a finite alphabet. -/
theorem lowConvexComplexity_of_mem_orbitClosure_of_finite [Finite α] {θ x : Config α}
    (hx : x ∈ orbitClosure θ) (h : LowConvexComplexity θ) : LowConvexComplexity x := by
  obtain ⟨S, hne, hconv, hle⟩ := h
  exact ⟨S, hne, hconv, (P_le_of_mem_orbitClosure_of_finite hx S).trans hle⟩

end Nivat
