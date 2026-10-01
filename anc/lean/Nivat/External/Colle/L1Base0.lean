/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.L1Assemble

/-!
# `MaxBResidual.base0`, both halves, and the concrete `lev₀` threshold

Lane Afill's file (exclusive).  Target: the `base0` field of
`Nivat.ColleReg.L1Data.MaxBResidual` (`L1Assemble.lean:962`), which splits into two independent
halves — a nonempty half and a covering half.

**The nonempty half is a restatement, not a new proof.** `nonempty_half_from_leaf_binders`
below repackages `L1Assemble.lean`'s already-landed Lemma 2.3 chain
(`maxB_nonempty_of_two_le_faces` + `two_le_min_faces_of_nel`, both `L1Assemble.lean:1787-1817`)
purely in the leaf's own binder names (`hSgen, hℓ_nel, hℓ_neg, hu, hdet_ℓ, hu', hdet`), so a
reader of `exists_L1MaxBResidual` can see the shape of what discharges this half without
re-deriving it. `MaxBResidual.base0_of_faces` / `MaxBResidual.ofFive` (`L1Assemble.lean:1905-
1933`, lane L1asm) already assemble this half — and the covering half — against an *abstract*
`RegionFamily`, so this file adds no second derivation of the nonempty half; it exists only
because the covering half below needs the concrete `lev₀` threshold, which no abstract argument
can supply (see next paragraph), and it is convenient to keep both halves' leaf-binder-facing
statements in one place.

**The covering half is new content the abstract route cannot give.**
`L1Data.exists_translate_subset_of_isRegion` (`L1Assemble.lean:1841+`) is existential over an
abstract `IsRegion R u u'` and yields *some* translate `b` with no numeric handle on it — it
cannot answer "does a *specific* `lev₀` work" because it never computes one. Against a concrete
`halfPlaneGE m lev₀`, membership of a translated `S₁` is linear in `lev₀`, so there is an exact
threshold, not just a sufficient bound: `forall_mem_halfPlaneGE_iff` states it as an **iff**
against `dot m b + dot m z₀` (`z₀` the `S₁`-point minimizing `dot m`), so whoever picks `lev₀`
for a concrete family (currently: Cprobe, deriving `line0` on the same family from the
`derivedQ` side) gets the exact ceiling, with no slack to lose or gain.
-/

set_option autoImplicit false

namespace Nivat.ColleReg.L1Data

open Nivat Nivat.LE2

theorem nonempty_half_from_leaf_binders {ξ : Config ℤ} {S₁ : Finset (ℤ × ℤ)}
    {ℓ u u' : ℤ × ℤ} {ε : Bool}
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S₁)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ) (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hu : Primitive u) (hdet_ℓ : Nivat.LE2.dot ℓ u = 0)
    (hu' : Primitive u') (hdet : det u u' ≠ 0) :
    (maxB (derivedQ ε u' S₁) u' ((topFace ε u' S₁).card - 1)).Nonempty :=
  maxB_nonempty_of_two_le_faces (latticeConvex_of_isGeneratingSet hSgen) hSgen.1 hu hu' hdet ε
    (two_le_min_faces_of_nel hSgen hℓ_nel hℓ_neg hu hdet_ℓ)

theorem forall_mem_halfPlaneGE_iff {S₁ : Finset (ℤ × ℤ)} {m b : ℤ × ℤ} {lev₀ : ℤ}
    {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ S₁) (hz₀min : ∀ z ∈ S₁, dot m z₀ ≤ dot m z) :
    (∀ z ∈ S₁, b + z ∈ Nivat.LE2.halfPlaneGE m lev₀) ↔
      lev₀ ≤ dot m b + dot m z₀ := by
  constructor
  · intro h
    have hz₀' := h z₀ hz₀
    simp only [Nivat.LE2.halfPlaneGE, Set.mem_ofPred_eq, dot_add] at hz₀'
    omega
  · intro h z hz
    simp only [Nivat.LE2.halfPlaneGE, Set.mem_ofPred_eq, dot_add]
    have := hz₀min z hz
    omega

theorem exists_lev₀_threshold {S₁ : Finset (ℤ × ℤ)} (hS₁ : S₁.Nonempty) (m b : ℤ × ℤ) :
    ∃ lev₀max : ℤ, ∀ lev₀ : ℤ,
      (∀ z ∈ S₁, b + z ∈ Nivat.LE2.halfPlaneGE m lev₀) ↔ lev₀ ≤ lev₀max := by
  obtain ⟨z₀, hz₀, hz₀min⟩ := S₁.exists_min_image (fun z => dot m z) hS₁
  exact ⟨dot m b + dot m z₀, fun lev₀ => forall_mem_halfPlaneGE_iff hz₀ hz₀min⟩

theorem exists_translate_subset_halfPlaneGE_of_le {S₁ : Finset (ℤ × ℤ)} {m b : ℤ × ℤ}
    {lev₀ : ℤ} {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ S₁) (hz₀min : ∀ z ∈ S₁, dot m z₀ ≤ dot m z)
    (h : lev₀ ≤ dot m b + dot m z₀) :
    ∀ z ∈ S₁, b + z ∈ Nivat.LE2.halfPlaneGE m lev₀ :=
  (forall_mem_halfPlaneGE_iff hz₀ hz₀min).mpr h

#print axioms Nivat.ColleReg.L1Data.nonempty_half_from_leaf_binders
#print axioms Nivat.ColleReg.L1Data.forall_mem_halfPlaneGE_iff
#print axioms Nivat.ColleReg.L1Data.exists_lev₀_threshold
#print axioms Nivat.ColleReg.L1Data.exists_translate_subset_halfPlaneGE_of_le

end Nivat.ColleReg.L1Data
