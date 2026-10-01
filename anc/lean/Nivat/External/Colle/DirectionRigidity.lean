import Nivat.External.Colle.TransverseUniqueness
import Nivat.External.KSDecomposition
import Nivat.Defs.Orbit

/-!
# Direction rigidity from a supplied product annihilator

The directional consequence of Colle's Lemma 2.6 needed downstream:
if two distinct configurations with the same product annihilator agree
on a half-plane, one factor direction must be tangent to its boundary.

The product annihilator is an explicit hypothesis. Its existence is not
assumed here. Only the proved Kari–Szabados decomposition is used.
-/

namespace Nivat.Colle

/-- Two configurations annihilated by the same product of transverse
differences are equal if they agree on a half-plane. -/
theorem eq_of_agree_halfPlane_of_prod_annihilator
    {n : ℕ} {v : Fin n → ℤ × ℤ}
    (hnp : Pairwise fun i j => det (v i) (v j) ≠ 0)
    {w : ℝ × ℝ} {c : ℝ} (hwv : ∀ i, inner2 w (v i) ≠ 0)
    {x y : Config ℤ}
    (hx : act (∏ i, (mono (v i) - 1) : LaurentTwo ℤ) x = 0)
    (hy : act (∏ i, (mono (v i) - 1) : LaurentTwo ℤ) y = 0)
    (hagree : ∀ z, c ≤ inner2 w z → x z = y z) : x = y := by
  have hv : ∀ i, v i ≠ 0 := by
    intro i hi
    apply hwv i
    simp only [hi, inner2, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, zero_mul, zero_add]
  have hxy : act (∏ i, (mono (v i) - 1) : LaurentTwo ℤ) (x - y) = 0 := by
    rw [act_sub_right, hx, hy, sub_self]
  obtain ⟨f, hfp, hfsum⟩ := kari_szabados_decomp' hv hnp hxy
  have hzero : ∀ z, c ≤ inner2 w z → ∑ i, f i z = 0 := by
    intro z hz
    rw [← hfsum]
    exact sub_eq_zero.mpr (hagree z hz)
  have htotal := sum_eq_zero_of_halfPlane Finset.univ f v
    (fun i _ => hfp i) (fun i _ => hwv i) hzero
  funext z
  have h := (hfsum z).trans (htotal z)
  exact sub_eq_zero.mp h

/-- The directional part of Colle Lemma 2.6: a half-plane ambiguity is
parallel to a factor of a supplied product annihilator. -/
theorem exists_tangent_of_ne_of_agree_halfPlane
    {n : ℕ} {v : Fin n → ℤ × ℤ}
    (hnp : Pairwise fun i j => det (v i) (v j) ≠ 0)
    {w : ℝ × ℝ} {c : ℝ} {x y : Config ℤ} (hne : x ≠ y)
    (hx : act (∏ i, (mono (v i) - 1) : LaurentTwo ℤ) x = 0)
    (hy : act (∏ i, (mono (v i) - 1) : LaurentTwo ℤ) y = 0)
    (hagree : ∀ z, c ≤ inner2 w z → x z = y z) :
    ∃ i, inner2 w (v i) = 0 := by
  by_contra h
  push Not at h
  exact hne (eq_of_agree_halfPlane_of_prod_annihilator hnp h hx hy hagree)

/-- An annihilation identity passes to the orbit closure, over any
commutative ring, because each equation involves a finite window. -/
theorem act_eq_zero_on_orbitClosure {R : Type*} [CommRing R]
    {p : LaurentTwo R} {ξ x : Config R} (hann : act p ξ = 0)
    (hx : x ∈ orbitClosure ξ) : act p x = 0 := by
  classical
  funext z
  obtain ⟨u, hu⟩ := hx ((supp p).image fun a => z + a)
  have heq : act p x z = act p ξ (u + z) := by
    simp only [act_apply]
    apply Finsupp.sum_congr
    intro a ha
    have hza := hu (z + a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    rw [hza]
    congr 2
    abel
  exact heq.trans (congrFun hann (u + z))

/-- Half-plane ambiguity inside an orbit closure forces a tangent factor
of any supplied product annihilator of the original configuration. -/
theorem exists_tangent_of_orbit_halfPlane_ambiguity
    {n : ℕ} {v : Fin n → ℤ × ℤ}
    (hnp : Pairwise fun i j => det (v i) (v j) ≠ 0)
    {ξ x y : Config ℤ}
    (hann : act (∏ i, (mono (v i) - 1) : LaurentTwo ℤ) ξ = 0)
    (hx : x ∈ orbitClosure ξ) (hy : y ∈ orbitClosure ξ) (hne : x ≠ y)
    {w : ℝ × ℝ} {c : ℝ} (hagree : ∀ z, c ≤ inner2 w z → x z = y z) :
    ∃ i, inner2 w (v i) = 0 := by
  exact exists_tangent_of_ne_of_agree_halfPlane hnp hne
    (act_eq_zero_on_orbitClosure hann hx) (act_eq_zero_on_orbitClosure hann hy) hagree

end Nivat.Colle
