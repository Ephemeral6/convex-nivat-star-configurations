/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# A generic CRT spanning-transport lemma

`Nivat.StarConfig.span_quotient` (Lemma 5.2, `Nivat/BiRecursion.lean`) needs more than "each CRT
factor `R/(aᵢ, cⱼ)` is spanned by the monomials `Y^d`, `d ∈ P_{ij}`" (Step 2,
`Nivat.Sublattice.span_quotient_pair`): spanning every factor individually does **not** imply
spanning the product ring `R/(a, c)` as a `K`-vector space.  Counterexample (one-dimensional,
same shape as the real obstruction): `R = K[Y^±]`, `a = Y² - 1 = (Y-1)(Y+1)`; CRT gives
`R/(a) ≅ K × K` via `f ↦ (f(1), f(-1))`.  Take `D = {0}`, i.e. the single monomial `Y⁰ = 1`: its
image is `1` in *both* factors, hence spans each factor (`R/(a₁) ≅ K` and `R/(a₂) ≅ K`), but
`span_K {(1, 1)}` is only the diagonal line in `K × K`, not the whole (2-dimensional) space.

The fix (paper's `E_{ij}`, §5, Step 3) is to multiply each per-factor generator by an
**idempotent-like** element `e k` that is `≡ 1` on its own factor `k` and `≡ 0` on every other
factor `l ≠ k`: then `e k * t` (for `t` a per-factor generator of factor `k`) becomes a genuine
"coordinate-supported" generator, and these jointly span the whole product.  This file proves
that transport fact in full generality (no Newton-polygon or `StarConfig` content at all): given
such a family `e`, a spanning set `T k` for each factor `R/(I k)`, and `J = ⨅ k, I k`, the images
of `⋃ k, (e k * ·) '' T k` span `R/J` as a `K`-module.

The construction of `e` itself (`Nivat.QuotientGlue.exists_partition_of_unity`) and the
Newton-polygon geometry pinning down what `T k` should concretely be
(`Nivat.StarConfig.Pij_subset_zono_sub_zono`) are supplied elsewhere; this file only needs the
three bookkeeping properties of `e` recorded in `he_diag`/`he_off` below, which
`exists_partition_of_unity` already establishes.

## Main results

* `Nivat.CRTSpan.span_of_partition_of_unity` — the transport lemma described above.

## Status

Complete; no `sorry`.
-/

namespace Nivat
namespace CRTSpan

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra K R]

/-- **The CRT spanning-transport lemma.** Let `J = ⨅ k, I k` for a finite family of ideals
`I : ι → Ideal R`, and let `e : ι → R` be a family with `e k ≡ 1 (mod I k)` (`he_diag`) and
`e k ≡ 0 (mod I l)` for `l ≠ k` (`he_off`) — an "idempotent-like partition of unity" for the
`I k`, as produced by `Nivat.QuotientGlue.exists_partition_of_unity`. If, for every `k`, a set
`T k ⊆ R` spans `R/(I k)` as a `K`-vector space, then the images of `⋃ k, (e k * ·) '' T k` span
`R/J` as a `K`-vector space. -/
theorem span_of_partition_of_unity {ι : Type*} [Fintype ι] {I : ι → Ideal R} {J : Ideal R}
    (hJ : J = ⨅ k, I k) {e : ι → R} (he_diag : ∀ k, e k - 1 ∈ I k)
    (he_off : ∀ k l, k ≠ l → e k ∈ I l) {T : ι → Set R}
    (hspan : ∀ k, Submodule.span K ((Ideal.Quotient.mk (I k)) '' T k) = ⊤) :
    Submodule.span K
        ((Ideal.Quotient.mk J) '' (⋃ k, (fun t => e k * t) '' T k)) = ⊤ := by
  classical
  -- `∑ k, e k ≡ 1 (mod I l)` for every `l`, hence `≡ 1 (mod J)`.
  have hsum1 : (∑ k, e k) - 1 ∈ J := by
    rw [hJ, Ideal.mem_iInf]
    intro l
    have hsplit : (∑ k, e k) - 1 = (e l - 1) + ∑ k ∈ Finset.univ.erase l, e k := by
      rw [← Finset.add_sum_erase _ e (Finset.mem_univ l)]; ring
    rw [hsplit]
    exact (I l).add_mem (he_diag l)
      (Submodule.sum_mem _ fun k hk => he_off k l (Finset.ne_of_mem_erase hk))
  -- Each per-factor spanning set, pushed forward along `mk (I k)` as a `K`-linear map, is `⊤`.
  have hmap : ∀ k, Submodule.map (Ideal.Quotient.mkₐ K (I k)).toLinearMap
      (Submodule.span K (T k)) = ⊤ := by
    intro k
    rw [Submodule.map_span]
    have himg : (Ideal.Quotient.mkₐ K (I k)).toLinearMap '' T k
        = (Ideal.Quotient.mk (I k)) '' T k := by
      simp [Ideal.Quotient.mkₐ_eq_mk]
    rw [himg]
    exact hspan k
  rw [eq_top_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  -- For each `k`, pull the class of `x` in `R/(I k)` back to some `s k ∈ span K (T k)`.
  have hx_mem : ∀ k, (Ideal.Quotient.mk (I k)) x
      ∈ Submodule.map (Ideal.Quotient.mkₐ K (I k)).toLinearMap (Submodule.span K (T k)) := by
    intro k; rw [hmap k]; trivial
  choose s hs_mem hs_eq using hx_mem
  have hs_eq' : ∀ k, x - s k ∈ I k := by
    intro k
    have h := hs_eq k
    rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk] at h
    exact Ideal.Quotient.eq.mp h.symm
  -- `e k * x ≡ e k * s k` modulo *every* `I l`, hence modulo `J`.
  have htransport : ∀ k, (Ideal.Quotient.mk J) (e k * x) = (Ideal.Quotient.mk J) (e k * s k) := by
    intro k
    rw [Ideal.Quotient.eq, hJ, Ideal.mem_iInf]
    intro l
    rcases eq_or_ne l k with rfl | hlk
    · have heq : e l * x - e l * s l = e l * (x - s l) := by ring
      rw [heq]
      exact Ideal.mul_mem_left _ _ (hs_eq' l)
    · have hek : e k ∈ I l := he_off k l (Ne.symm hlk)
      exact (I l).sub_mem (Ideal.mul_mem_right _ _ hek) (Ideal.mul_mem_right _ _ hek)
  -- Assemble: `mk J x = ∑ k, mk J (e k * x) = ∑ k, mk J (e k * s k)`.
  have hstep1 : (Ideal.Quotient.mk J) x = (Ideal.Quotient.mk J) ((∑ k, e k) * x) := by
    rw [Ideal.Quotient.eq]
    have heq : x - (∑ k, e k) * x = (1 - ∑ k, e k) * x := by ring
    rw [heq]
    have hmem : (1 - ∑ k, e k) ∈ J := by
      have h := J.neg_mem hsum1
      simpa using h
    exact Ideal.mul_mem_right _ _ hmem
  have hstep2 : (Ideal.Quotient.mk J) ((∑ k, e k) * x)
      = ∑ k, (Ideal.Quotient.mk J) (e k * x) := by
    rw [Finset.sum_mul]
    exact map_sum (Ideal.Quotient.mk J) _ _
  have hstep3 : ∑ k, (Ideal.Quotient.mk J) (e k * x)
      = ∑ k, (Ideal.Quotient.mk J) (e k * s k) :=
    Finset.sum_congr rfl fun k _ => htransport k
  rw [hstep1, hstep2, hstep3]
  -- `z ∈ span K (T k) ⟹ e k * z ∈ span K ((e k * ·) '' T k)`, universally in `z`.
  have hspan_mul : ∀ (k : ι) (z : R), z ∈ Submodule.span K (T k) →
      e k * z ∈ Submodule.span K ((fun t => e k * t) '' T k) := by
    intro k z hz
    induction hz using Submodule.span_induction with
    | mem t ht => exact Submodule.subset_span ⟨t, ht, rfl⟩
    | zero => simp
    | add u v _ _ hu hv =>
        have heq : e k * (u + v) = e k * u + e k * v := by ring
        rw [heq]; exact Submodule.add_mem _ hu hv
    | smul c u _ hu =>
        have heq : e k * (c • u) = c • (e k * u) := by
          rw [Algebra.smul_def, Algebra.smul_def]; ring
        rw [heq]; exact Submodule.smul_mem _ c hu
  -- `w ∈ span K (⋃ ...) ⟹ mk J w ∈ span K (mk J '' (⋃ ...))`, universally in `w`.
  have hpush : ∀ w : R, w ∈ Submodule.span K (⋃ k, (fun t => e k * t) '' T k) →
      (Ideal.Quotient.mk J) w ∈
        Submodule.span K ((Ideal.Quotient.mk J) '' (⋃ k, (fun t => e k * t) '' T k)) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem t ht => exact Submodule.subset_span ⟨t, ht, rfl⟩
    | zero => simp
    | add u v _ _ hu hv =>
        rw [map_add]; exact Submodule.add_mem _ hu hv
    | smul c u _ hu =>
        have heq : (Ideal.Quotient.mk J) (c • u) = c • (Ideal.Quotient.mk J) u := by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul,
            ← Ideal.Quotient.mkₐ_eq_mk K, AlgHom.commutes]
        rw [heq]; exact Submodule.smul_mem _ c hu
  -- Each summand `mk J (e k * s k)` lies in the target span.
  refine Submodule.sum_mem _ fun k _ => ?_
  have hsub : Submodule.span K ((fun t => e k * t) '' T k)
      ≤ Submodule.span K (⋃ k, (fun t => e k * t) '' T k) :=
    Submodule.span_mono (Set.subset_iUnion (fun k => (fun t => e k * t) '' T k) k)
  exact hpush _ (hsub (hspan_mul k (s k) (hs_mem k)))

end CRTSpan
end Nivat
