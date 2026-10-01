/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.MinkowskiEdges
import Nivat.External.Colle.ConvTransport
import Nivat.Laurent.Ostrowski

/-!
# The Newton polygon of `ψ = ∏_{i ∈ s} (X^{h_i} - 1)` is the lattice zonotope `∑_{i ∈ s} [0, h_i]`

This file supplies the last bridge between

* `Nivat.LE2.zono_no_edge_parallel` (`MinkowskiEdges.lean` §4) — "if no generator of a
  lattice zonotope is parallel to `ℓ` then no *edge* of the zonotope is parallel to `ℓ`",
  proved there for the Minkowski sum `∑ i ∈ s, segOf (h i)` — and
* the hypothesis that Claim 3.6 actually carries, namely
  `Conv S_ψ = Conv (supp ψ)` with `ψ = ∏_{i ≠ i_m} (X^{h_i} - 1)` over `ℤ`.

`MinkowskiEdges.lean`'s Status section lists exactly two missing bridges.  Both are
supplied now:

1. **`Conv S = Conv T → E ↑S = E ↑T`** — this is `Nivat.LE2.E_congr_of_Conv_eq`
   (`ConvTransport.lean`), proved after that Status note was written.
2. **`Conv (supp ψ) = Conv (zonotope)`** — proved here as `Conv_supp_prod_eq_Conv_zonoF`.

Bridge 2 is *not* `supp ψ = ∑ supp (X^{h_i} - 1)`: that is false, because coefficients of
`ψ` can cancel (if `h₁ + h₂ = h₃` the coefficient of `ψ` at `h₁ + h₂` may vanish).  It is
the statement at the level of convex hulls, i.e. Ostrowski's theorem, and `supp ψ ⊊ ∑ …`
is perfectly compatible with it.

Ostrowski is already in the tree as `Nivat.newt_prod` (`Laurent/Ostrowski.lean`), but only
over `ℂ`, while Claim 3.6's `ψ` lives in `LaurentTwo ℤ`.  §1 below closes that gap by
pushing `ψ` along the ring map `ℤ →+* ℂ`: the map is injective, so it preserves `supp` **on
the nose** (`supp_toC`), and `Conv (supp ψ_ℤ) = Conv (supp ψ_ℂ) = Newt ψ_ℂ`.  No new
Ostrowski proof is needed.

## Main results

* `Nivat.LE2.supp_toC` — `supp` is unchanged by `ℤ → ℂ` on coefficients.
* `Nivat.LE2.zonoF` — the lattice zonotope `∑_{i ∈ s} {0, h i}` as a `Finset`, with
  `coe_zonoF : ↑(zonoF s h) = ∑ i ∈ s, segOf (h i)`.
* `Nivat.LE2.Conv_supp_prod_eq_Conv_zonoF` — **Ostrowski over `ℤ`, in the form Claim 3.6
  needs**: `Conv (supp ∏_{i ∈ s} (X^{h_i} - 1)) = Conv (zonoF s h)`.
* `Nivat.LE2.no_edge_parallel_of_Conv_eq_supp_prod` — the assembled statement: an edge
  normal `n` of any `S` with `Conv S = Conv (supp ψ)` satisfies `dot n ℓ ≠ 0` whenever no
  surviving generator `h i` is parallel to `ℓ`.  This is what `Claim36.lean`'s
  `generatingSet_no_edge_parallel` is proved from.

## Status

Complete; no `sorry`, no new `axiom`.
-/

namespace Nivat.LE2

open Nivat Pointwise

/-! ## §1. Transporting `supp` from `ℤ` to `ℂ`

`LaurentTwo R = AddMonoidAlgebra R (ℤ × ℤ)` is functorial in `R`, and an *injective* ring
map induces a map that preserves supports exactly (not just up to inclusion).  That is all
that is needed to run the `ℂ`-only `newt_prod` on a `ℤ`-coefficient polynomial. -/

/-- The coefficientwise inclusion `ℤ[T₁^±, T₂^±] → ℂ[T₁^±, T₂^±]`. -/
noncomputable def toC : LaurentTwo ℤ →+* LaurentTwo ℂ :=
  AddMonoidAlgebra.mapRingHom (ℤ × ℤ) (Int.castRingHom ℂ)

@[simp] theorem coeff_toC (f : LaurentTwo ℤ) (u : ℤ × ℤ) :
    (toC f).coeff u = ((f.coeff u : ℤ) : ℂ) := by
  simp [toC]

/-- `ℤ → ℂ` is injective, so it changes no support. -/
theorem supp_toC (f : LaurentTwo ℤ) : supp (toC f) = supp f := by
  ext u
  simp only [mem_supp, coeff_toC, ne_eq, Int.cast_eq_zero]

theorem toC_mono (u : ℤ × ℤ) : toC (mono u) = (mono u : LaurentTwo ℂ) := by
  simp [toC, mono, AddMonoidAlgebra.mapRingHom_single]

theorem toC_mono_sub_one (u : ℤ × ℤ) :
    toC (mono u - 1) = (mono u - 1 : LaurentTwo ℂ) := by
  rw [map_sub, map_one, toC_mono]

/-- The support of `ψ = ∏ (X^{h_i} - 1)` does not depend on whether the coefficients are
read in `ℤ` or in `ℂ`. -/
theorem supp_prod_mono_sub_one_complex {ι : Type*} (s : Finset ι) (h : ι → ℤ × ℤ) :
    supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo ℂ))
      = supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo ℤ)) := by
  rw [← supp_toC (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo ℤ)), map_prod]
  simp only [toC_mono_sub_one]

/-! ## §2. The support and Newton polygon of a single factor -/

/-- `supp (X^u - 1) = {u, 0}`, over any non-trivial commutative ring.  (The `ℤ` instance of
this is `Colle36Fit.supp_mono_sub_one` in `MinkowskiEdges.lean`; the proof is the same and
is repeated here in the generality the `ℂ` side needs.) -/
theorem supp_mono_sub_one {R : Type*} [CommRing R] [Nontrivial R] {u : ℤ × ℤ} (hu : u ≠ 0) :
    supp (mono u - 1 : LaurentTwo R) = {u, 0} := by
  ext v
  simp only [mem_supp, Finset.mem_insert, Finset.mem_singleton]
  rw [show ((mono u - 1 : LaurentTwo R)).coeff
      = (Finsupp.single u 1 - Finsupp.single 0 1) from rfl]
  simp only [Finsupp.sub_apply, Finsupp.single_apply]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [if_neg (fun hh => hc.1 hh.symm), if_neg (fun hh => hc.2 hh.symm)] at h
    simp at h
  · rintro (rfl | rfl)
    · rw [if_pos rfl, if_neg (fun hh => hu hh.symm)]; norm_num
    · rw [if_neg (fun hh => hu hh), if_pos rfl]; norm_num

theorem mono_sub_one_ne_zero {R : Type*} [CommRing R] [Nontrivial R] {u : ℤ × ℤ}
    (hu : u ≠ 0) : (mono u - 1 : LaurentTwo R) ≠ 0 := by
  intro hz
  have hempty : supp (mono u - 1 : LaurentTwo R) = ∅ := by
    rw [hz]; simp [Nivat.supp]
  rw [supp_mono_sub_one hu] at hempty
  exact absurd (hempty ▸ Finset.mem_insert_self u {0}) (Finset.notMem_empty u)

/-- The Newton polygon of `X^u - 1` is the segment `[0, u]`. -/
theorem newt_mono_sub_one {u : ℤ × ℤ} (hu : u ≠ 0) :
    newt (mono u - 1 : LaurentTwo ℂ) = Conv ({0, u} : Finset (ℤ × ℤ)) := by
  rw [newt_eq_conv, supp_mono_sub_one hu, Finset.pair_comm]

/-! ## §3. The lattice zonotope as a `Finset`, and its convex hull

`Nivat.Conv` is defined only on `Finset`s, so the zonotope must be available as one.  `zonoF`
is the `Finset`-level Minkowski sum; `coe_zonoF` identifies its coercion with the `Set`-level
sum `∑ i ∈ s, segOf (h i)` that `MinkowskiEdges.lean` works with. -/

/-- The lattice zonotope `∑_{i ∈ s} {0, h i}`, as a `Finset`. -/
def zonoF {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ) : Finset (ℤ × ℤ) :=
  ∑ i ∈ s, ({0, h i} : Finset (ℤ × ℤ))

theorem coe_zonoF {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ) :
    (↑(zonoF s h) : Set (ℤ × ℤ)) = ∑ i ∈ s, segOf (h i) := by
  classical
  unfold zonoF
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.coe_add, ih]
      congr 1
      simp [segOf]

theorem Conv_add (S T : Finset (ℤ × ℤ)) : Conv (S + T) = Conv S + Conv T := by
  have himg : ∀ A B : Set (ℤ × ℤ), toReal '' (A + B) = toReal '' A + toReal '' B := by
    intro A B
    ext x
    constructor
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨toReal a, ⟨a, ha, rfl⟩, toReal b, ⟨b, hb, rfl⟩, by simp [toReal]⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by simp [toReal]⟩
  show convexHull ℝ (toReal '' (↑(S + T) : Set (ℤ × ℤ)))
      = convexHull ℝ (toReal '' (↑S : Set (ℤ × ℤ))) + convexHull ℝ (toReal '' (↑T : Set (ℤ × ℤ)))
  rw [Finset.coe_add, himg, convexHull_add]

theorem Conv_zero : Conv (0 : Finset (ℤ × ℤ)) = (0 : Set (ℝ × ℝ)) := by
  show convexHull ℝ (toReal '' (↑(0 : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))) = 0
  rw [Finset.coe_zero, ← Set.singleton_zero, Set.image_singleton,
    show toReal (0 : ℤ × ℤ) = 0 from by simp [toReal], convexHull_singleton,
    Set.singleton_zero]

theorem Conv_zonoF {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ) :
    Conv (zonoF s h) = ∑ i ∈ s, Conv ({0, h i} : Finset (ℤ × ℤ)) := by
  classical
  unfold zonoF
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Conv_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Conv_add, ih]

/-! ## §4. Ostrowski over `ℤ`, in the form Claim 3.6 needs -/

/-- **The Newton polygon of `ψ = ∏_{i ∈ s} (X^{h_i} - 1)` over `ℤ` is the zonotope.**

This is the paper's equation (2.3) (`Newt(A) = Z`), obtained from `Nivat.newt_prod`
(Ostrowski, over `ℂ`) by transporting along the injective ring map `ℤ → ℂ`. -/
theorem Conv_supp_prod_eq_Conv_zonoF {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (h : ι → ℤ × ℤ) (hne : ∀ i ∈ s, h i ≠ 0) :
    Conv (supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo ℤ))) = Conv (zonoF s h) := by
  rw [← supp_prod_mono_sub_one_complex s h]
  show newt (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo ℂ)) = _
  rw [newt_prod s _ (fun i hi => mono_sub_one_ne_zero (hne i hi)), Conv_zonoF]
  exact Finset.sum_congr rfl fun i hi => newt_mono_sub_one (hne i hi)

/-- **The corrected Gap 1 of Claim 3.6, at the hypothesis Claim 3.6 actually carries.**

If every surviving generator `h i` (`i ∈ s`) is non-zero and non-parallel to `ℓ`, then no
edge of any `S` whose convex hull is the Newton polygon of `ψ = ∏_{i ∈ s}(X^{h_i} - 1)` is
parallel to `ℓ` — where "the edge with normal `n` is parallel to `ℓ`" is `dot n ℓ = 0`
(`det_dir`), `E` being indexed by primitive outer *normals*.

Assembled from `Conv_supp_prod_eq_Conv_zonoF` (§4), `E_congr_of_Conv_eq`
(`ConvTransport.lean`) and `zono_no_edge_parallel` (`MinkowskiEdges.lean` §4). -/
theorem no_edge_parallel_of_Conv_eq_supp_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (h : ι → ℤ × ℤ) (hne : ∀ i ∈ s, h i ≠ 0) {ℓ : ℤ × ℤ}
    (hpar : ∀ i ∈ s, det (h i) ℓ ≠ 0) {S : Finset (ℤ × ℤ)}
    (hS : Conv S = Conv (supp (∏ i ∈ s, (mono (h i) - 1 : LaurentTwo ℤ))))
    {n : ℤ × ℤ} (hn : n ∈ E (↑S : Set (ℤ × ℤ))) : dot n ℓ ≠ 0 := by
  have h1 : Conv S = Conv (zonoF s h) := by
    rw [hS, Conv_supp_prod_eq_Conv_zonoF s h hne]
  have h2 : n ∈ E (↑(zonoF s h) : Set (ℤ × ℤ)) := (mem_E_congr_of_Conv_eq h1 n).mp hn
  rw [coe_zonoF] at h2
  have h3 := zono_no_edge_parallel s h hne hpar h2
  rw [det_dir] at h3
  omega

/-! ## §5. Non-degeneracy

Two ways this file could be empty talk: `zonoF` could be the empty set (then `coe_zonoF`
says nothing), or `Conv_supp_prod_eq_Conv_zonoF` could be about a polygon with no edges at
all (then §4 would be vacuous).  Both are ruled out. -/

/-- `zonoF` of the two unit generators is the unit square — four points, positive area. -/
theorem zonoF_unit_square :
    zonoF (Finset.univ : Finset (Fin 2))
      (![((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))]) =
      ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (1 : ℤ))} :
        Finset (ℤ × ℤ)) := by
  decide

/-- The conclusion of `no_edge_parallel_of_Conv_eq_supp_prod` is not vacuous: the polygon in
question really does have edges.  Here `ψ = (X^{(1,0)} - 1)(X^{(0,1)} - 1)` and `(0,1)` is an
edge normal of the unit square, with `dot (0,1) (1,0) = 0` — so the hypothesis `hpar` is
doing real work, it is not excluding an empty set of `n`. -/
theorem mem_E_zonoF_unit_square :
    ((0 : ℤ), (1 : ℤ)) ∈ E (↑(zonoF (Finset.univ : Finset (Fin 2))
      (![((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))])) : Set (ℤ × ℤ)) := by
  rw [zonoF_unit_square]
  refine ⟨by decide, ?_⟩
  have hface : ∀ z ∈ (↑({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)),
        ((1 : ℤ), (1 : ℤ))} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)), z.2 = 1 →
      z ∈ face (↑({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)),
        ((1 : ℤ), (1 : ℤ))} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ)) := by
    rintro z hz hz1
    refine ⟨hz, fun y hy => ?_⟩
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    simp only [dot, hz1]
    rcases hy with rfl | rfl | rfl | rfl <;> norm_num
  exact ⟨((0 : ℤ), (1 : ℤ)), hface _ (by decide) rfl,
    ((1 : ℤ), (1 : ℤ)), hface _ (by decide) rfl, by decide⟩

end Nivat.LE2
