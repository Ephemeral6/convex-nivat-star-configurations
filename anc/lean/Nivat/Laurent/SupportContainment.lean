/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.BiRecursion

/-!
# Lemma 5.2, item (d): the parallelogram `P_{ij}` lies in `Z - Z`

This file supplies the one purely combinatorial input listed as item (d) of the TODO on
`Nivat.StarConfig.span_quotient` (`Nivat/BiRecursion.lean`): the parallelogram
`P_{ij} = [0, dᵢ vᵢ] + [0, -dⱼ vⱼ]` (paper (5.4), `Nivat.StarConfig.Pij`) is contained in
`Z - Z` (`Nivat.StarConfig.Zono - Nivat.StarConfig.Zono`), for every `i, j`.  This is exactly
what lets the monomial spanning set of each nonzero CRT factor `R/Ifac(i,j)`
(`Nivat.Sublattice.span_quotient_pair`, indexed by exponents in `Pij i j`) be replaced by the
common, `(i,j)`-independent spanning set indexed by `S.ZsubZ = latticePts (Z - Z)`.

The proof is immediate from `Nivat.mem_zonotope_iff`: a point of `Pij i j` uses only the
coefficients `i` and `j` of the ambient zonotope `Z`, so it is the difference of two points of
`Z`, each obtained from a full zonotope point by setting every *other* coordinate's coefficient
to `0`.

## Main results

* `Nivat.StarConfig.Pij_subset_zono_sub_zono` — `S.Pij i j ⊆ S.Zono - S.Zono` for every `i, j`.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open scoped Pointwise

namespace StarConfig

variable {p m : ℕ} [Fact p.Prime] (S : StarConfig p m)

/-- Membership in `latSegment d w`, unpacked to the single scaling coefficient (re-derived here
since the corresponding fact in `Nivat/Lattice/Zonotope.lean` is `private`). -/
private theorem mem_latSegment_iff' {d : ℕ} {w : ℤ × ℤ} {x : ℝ × ℝ} :
    x ∈ latSegment d w ↔ ∃ c : ℝ, c ∈ Set.Icc (0 : ℝ) 1 ∧ c • toReal ((d : ℤ) • w) = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, heq⟩
    exact ⟨b, ⟨hb, by linarith⟩, by simpa using heq⟩
  · rintro ⟨c, ⟨hc0, hc1⟩, rfl⟩
    exact ⟨1 - c, c, by linarith, hc0, by ring, by simp⟩

/-- `toReal` sends `-z` to `-toReal z`. -/
private theorem toReal_neg (z : ℤ × ℤ) : toReal (-z) = -toReal z := by
  simp [toReal]

/-- Placing weight `c ∈ [0, 1]` on a single coordinate `k` of the zonotope (and `0` elsewhere)
lands in `S.Zono`. -/
private theorem smul_gen_mem_zono {k : Fin m} {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    c • toReal ((S.specDeg k : ℤ) • S.v k) ∈ S.Zono := by
  classical
  rw [StarConfig.Zono, mem_zonotope_iff]
  refine ⟨fun l => if l = k then c else 0, fun l => ?_, ?_⟩
  · by_cases h : l = k <;> simp [h, hc]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hlk; simp [hlk]
    · intro h; exact absurd (Finset.mem_univ k) h

/-- **Item (d) of Lemma 5.2's assembly**: the parallelogram `P_{ij}` (paper (5.4)) is contained
in `Z - Z`.  Every point of `P_{ij}` uses only the zonotope coordinates `i` and `j`; setting all
other coordinates' coefficients to `0` exhibits it as a difference of two points of `Z`. -/
theorem Pij_subset_zono_sub_zono (i j : Fin m) : S.Pij i j ⊆ S.Zono - S.Zono := by
  rintro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨a, ha, rfl⟩ := mem_latSegment_iff'.mp hu
  obtain ⟨b, hb, rfl⟩ := mem_latSegment_iff'.mp hw
  simp only [smul_neg, toReal_neg]
  refine Set.mem_sub.mpr ⟨_, S.smul_gen_mem_zono (k := i) ha, _, S.smul_gen_mem_zono (k := j) hb, ?_⟩
  abel

end StarConfig

end Nivat
