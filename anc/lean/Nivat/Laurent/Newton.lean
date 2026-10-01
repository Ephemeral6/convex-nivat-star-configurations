/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Laurent.Basic
import Nivat.Defs.Complexity
import Mathlib.Analysis.Convex.Topology

/-!
# Newton polygons of two-variable Laurent polynomials

Formalisation of the Newton polygon `Newt(f) = Conv(supp f)` of §0.3 of *The Convex Nivat
Conjecture* (Pan).

Mathlib has no Newton polygon, so this file and `Nivat.Laurent.Ostrowski` build the small
amount that the paper uses: the definition, its behaviour on monomials, and — in the companion
file — Minkowski additivity.

## Main definitions

* `Nivat.newt` — `Newt(f) = Conv(supp f) ⊆ ℝ²`.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open scoped Pointwise

/-- The Newton polygon `Newt(f) = Conv(supp f)`.  Paper §0.3. -/
def newt {R : Type*} [CommRing R] (f : LaurentTwo R) : Set (ℝ × ℝ) := Conv (supp f)

theorem newt_eq_conv {R : Type*} [CommRing R] (f : LaurentTwo R) : newt f = Conv (supp f) := rfl

/-- `Newt(f)` spelled out as a convex hull in `ℝ²`; the working form of `Nivat.newt`. -/
theorem newt_eq_convexHull {R : Type*} [CommRing R] (f : LaurentTwo R) :
    newt f = convexHull ℝ (toReal '' (supp f : Set (ℤ × ℤ))) := rfl

@[simp] theorem supp_eq_zero_iff {R : Type*} [CommRing R] (f : LaurentTwo R) :
    supp f = ∅ ↔ f = 0 := by
  rw [supp, Finsupp.support_eq_empty, AddMonoidAlgebra.coeff_eq_zero]

/-- The support of a non-zero Laurent polynomial is a non-empty finite set. -/
theorem supp_nonempty {R : Type*} [CommRing R] {f : LaurentTwo R} (hf : f ≠ 0) :
    (supp f).Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr fun h => hf ((supp_eq_zero_iff f).mp h)

theorem mem_newt_of_mem_supp {R : Type*} [CommRing R] {f : LaurentTwo R} {u : ℤ × ℤ}
    (hu : u ∈ supp f) : toReal u ∈ newt f :=
  subset_Conv hu

/-- The support of a monomial is the singleton `{u}`.  Paper §0.3. -/
@[simp] theorem supp_mono {R : Type*} [CommRing R] [Nontrivial R] (u : ℤ × ℤ) :
    supp (mono u : LaurentTwo R) = {u} := by
  rw [supp, coeff_mono]
  exact Finsupp.support_single u one_ne_zero

/-- The Newton polygon of a monomial is a point. -/
theorem newt_mono {R : Type*} [CommRing R] [Nontrivial R] (u : ℤ × ℤ) :
    newt (mono u : LaurentTwo R) = {toReal u} := by
  rw [newt_eq_convexHull, supp_mono, Finset.coe_singleton, Set.image_singleton,
    convexHull_singleton]

/-- The Newton polygon of a non-zero Laurent polynomial is non-empty. -/
theorem newt_nonempty {R : Type*} [CommRing R] {f : LaurentTwo R} (hf : f ≠ 0) :
    (newt f).Nonempty :=
  let ⟨u, hu⟩ := supp_nonempty hf
  ⟨toReal u, mem_newt_of_mem_supp hu⟩

/-- The Newton polygon is convex. -/
theorem newt_convex {R : Type*} [CommRing R] (f : LaurentTwo R) : Convex ℝ (newt f) :=
  convex_convexHull ℝ _

/-- The Newton polygon is closed: it is the convex hull of a finite set. -/
theorem newt_isClosed {R : Type*} [CommRing R] (f : LaurentTwo R) : IsClosed (newt f) := by
  rw [newt_eq_convexHull]
  exact ((supp f).finite_toSet.image toReal).isClosed_convexHull ℝ

end Nivat
