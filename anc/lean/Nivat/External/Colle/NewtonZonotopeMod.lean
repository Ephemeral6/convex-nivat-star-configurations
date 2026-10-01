/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.NewtonZonotope
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

open scoped Pointwise

set_option autoImplicit false

/-!
# Newton polygon mod p

The Newton polygon of `ψ = ∏_{i ∈ s} (X^{h_i} - 1)` is unchanged by coefficient reduction
`ℤ → ZMod p` (for `p` prime).

This bridges `RegionSteps.lean:2488`'s use of `hhull_mod`, which requires that the zonotope
`Conv (supp ψ)` computed over `ℤ` equals the one computed over `ZMod p`.  The paper's
`:786-792` justifies this: "changing the alphabet if necessary, let `p` be a prime number such
that `𝒜 ⊂ ℤ_p`" + Lemma 2.5 uses `φ_ι ∈ ann_{ℤ_p}(η − η̄_{ι₀})`.

## Main result

* `hhull_mod_of_prime` — `Conv (↑Sw) = Conv (supp ψ_ℤ)` implies
  `Conv (↑Sw) = Conv (supp ψ_{ZMod p})`, by transitivity through `Conv (zonoF s h)`.

## Strategy

With `newt` and `newt_prod` (Ostrowski) now generalized to any integral domain, both
`Conv (supp ψ_ℤ)` and `Conv (supp ψ_{ZMod p})` equal `Conv (zonoF s h)` by the same proof.
Transitivity gives the result.

## Status

Complete; no `sorry`, no new `axiom`.
-/

namespace Nivat

open Nivat.LE2

/-- The coefficientwise reduction `ℤ[T₁^±, T₂^±] → (ZMod p)[T₁^±, T₂^±]`. -/
noncomputable def toZMod (p : ℕ) : LaurentTwo ℤ →+* LaurentTwo (ZMod p) :=
  AddMonoidAlgebra.mapRingHom (ℤ × ℤ) (Int.castRingHom (ZMod p))

@[simp] theorem coeff_toZMod (p : ℕ) (f : LaurentTwo ℤ) (u : ℤ × ℤ) :
    (toZMod p f).coeff u = ((f.coeff u : ℤ) : ZMod p) := by
  simp [toZMod]

/-- Ring homomorphisms can only shrink supports, never enlarge them. -/
theorem supp_toZMod_subset (p : ℕ) (f : LaurentTwo ℤ) : supp (toZMod p f) ⊆ supp f := by
  intro u hu
  rw [mem_supp] at hu ⊢
  contrapose! hu
  simp [coeff_toZMod, hu]

theorem toZMod_mono (p : ℕ) (u : ℤ × ℤ) : toZMod p (mono u) = (mono u : LaurentTwo (ZMod p)) := by
  simp [toZMod, mono, AddMonoidAlgebra.mapRingHom_single]

theorem toZMod_mono_sub_one (p : ℕ) (u : ℤ × ℤ) :
    toZMod p (mono u - 1) = (mono u - 1 : LaurentTwo (ZMod p)) := by
  rw [map_sub, map_one, toZMod_mono]

/-- **The `⊆` direction:** coefficient reduction gives `supp ψ_{ZMod p} ⊆ supp ψ_ℤ`. -/
theorem supp_prod_mono_sub_one_mod_subset {p : ℕ} {ι : Type*} (s : Finset ι) (h : ι → ℤ × ℤ) :
    supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo (ZMod p)))
      ⊆ supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo ℤ)) := by
  calc supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo (ZMod p)))
      = supp (toZMod p (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo ℤ))) := by
          rw [map_prod]; simp only [toZMod_mono_sub_one]
    _ ⊆ supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo ℤ)) := supp_toZMod_subset p _

#print axioms supp_prod_mono_sub_one_mod_subset

/-! ## The generalized Ostrowski lemmas -/

/-- **Newton polygon of a single factor, generalized to any nontrivial commutative ring.**

The Newton polygon of `X^u - 1` is the segment `[0, u]`. This is `NewtonZonotope.lean:122`
generalized from ℂ to any nontrivial ring. -/
theorem newt_mono_sub_one_of_ring {R : Type*} [CommRing R] [Nontrivial R] {u : ℤ × ℤ}
    (hu : u ≠ 0) : newt (mono u - 1 : LaurentTwo R) = Conv ({0, u} : Finset (ℤ × ℤ)) := by
  rw [newt_eq_conv, supp_mono_sub_one hu, Finset.pair_comm]

/-- **Newton polygon of `ψ = ∏ (X^{h_i} - 1)` is the zonotope, over any integral domain.**

This is `NewtonZonotope.lean:181` (`Conv_supp_prod_eq_Conv_zonoF`) generalized from ℤ via ℂ
to any integral domain. With `newt_prod` (Ostrowski) now generic, the detour through ℂ is gone. -/
theorem Conv_supp_prod_eq_Conv_zonoF_of_domain {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ) (hne : ∀ i ∈ s, h i ≠ 0) :
    Conv (supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo R))) = Conv (zonoF s h) := by
  have : newt (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo R)) = Conv (zonoF s h) := by
    calc newt (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo R))
        = ∑ i ∈ s, newt (mono (h i) - 1 : LaurentTwo R) :=
          newt_prod s _ (fun i hi => mono_sub_one_ne_zero (hne i hi))
      _ = ∑ i ∈ s, Conv ({0, h i} : Finset (ℤ × ℤ)) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          exact newt_mono_sub_one_of_ring (hne i hi)
      _ = Conv (zonoF s h) := (Conv_zonoF s h).symm
  exact this

/-- **The Newton polygon of `ψ = ∏ (X^{h_i} - 1)` over `ℤ` equals its value over `ZMod p`.**

Target for `RegionSteps.lean:2511`. Given `Conv (↑Sw) = Conv (supp ψ_ℤ)`, we conclude
`Conv (↑Sw) = Conv (supp ψ_{ZMod p})` by transitivity through `Conv (zonoF s h)`:
both sides equal the zonotope by `Conv_supp_prod_eq_Conv_zonoF_of_domain`, since ℤ is an
integral domain and `ZMod p` (for prime `p`) is a field, hence a domain. -/
theorem hhull_mod_of_prime {p : ℕ} [Fact p.Prime] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (h : ι → ℤ × ℤ) (hne : ∀ i ∈ s, h i ≠ 0) (Sw : Finset (ℤ × ℤ))
    (hSw : Conv Sw = Conv (supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo ℤ)))) :
    Conv Sw = Conv (supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo (ZMod p)))) := by
  calc Conv Sw
      = Conv (supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo ℤ))) := hSw
    _ = Conv (zonoF s h) := Conv_supp_prod_eq_Conv_zonoF_of_domain s h hne
    _ = Conv (supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo (ZMod p)))) :=
        (Conv_supp_prod_eq_Conv_zonoF_of_domain s h hne).symm

#print axioms hhull_mod_of_prime

end Nivat
