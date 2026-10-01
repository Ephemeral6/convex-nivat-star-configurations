/-
lane-hole3-cone, round 167 (2026-09-24).  0 sorry.

# `Nivat.LE2.IsRegion` → `Nivat.Colle41.IsRegion`

Target (team-lead, round 167): `Colle41.IsRegion`'s docstring (`Lemma41.lean:686-687`) admits
it dropped the orientation datum (`detPos`/`precedes`) that `LE2.IsRegion`
(`LatticeEdges.lean:2221`) carries.  This file builds the missing bridge, so any chain-side
consumer that only has `LE2.IsRegion R n n'` (the honest Definition 3.1 reading, with
orientation) can still feed `Colle41`'s Lemma 4.1 machinery.

Signature (team-lead's, not a paraphrase):
```
theorem colle41_of_le2 {R n n'} (h : LE2.IsRegion R n n') :
    Colle41.IsRegion R (-(dir n)) (dir n')
```
The asymmetry (`-(dir n)` for the `ℓ`-edge, `+dir n'` for the `ℓ'`-edge) is not a typo: it is
`b3_colle2.txt:388`'s "`w ≺ ⋯ ≺ w'`" positive orientation, cross-checked numerically against
team-lead's `tmp/region_orientation_probe.lean` (ℓ edge: ray = `-(dir n)`; ℓ_J edge: ray =
`+(dir n')`).

## Built on `RegionRayDir.lean` (lane-env-refute, round 167, `Nivat/`, 0 sorry)

`Nivat.RegionRayDir.rays_of_isRegion` supplies, from `LE2.IsRegion R n n'` alone, **the
existence** of a ray out of each semi-infinite edge in the direction `dir n` or `-(dir n)`
(sign undetermined — that file proves *both* signs genuinely occur on different edges of the
same region, `quad_ray_left`/`quad_ray_bot`).  The only work left, exactly the piece that file
explicitly declines to do ("符号留给外面"), is to use `h.detPos : 0 < det n n'` to rule out the
wrong disjunct on each side.  That is `rayIn_false_of_dot_pos` below: if the *wrong*-signed ray
existed, walking along it would send `dot n' ·` (resp. `dot n ·`) to `+∞`, contradicting the
maximizer bound coming from the *other* edge's face.  `precedes` (`LatticeEdges.lean:2240`) is
not needed — `detPos` alone pins both signs (cross-confirmed independently by lane-env-refute's
`not_rayIn_of_dot_pos`, `tmp/wip/lane-env-refute-raysign.lean`, kept there as a receipt only).
-/
import Nivat.External.Colle.RegionRayDir

set_option autoImplicit false

namespace Nivat.RegionOrientBridge

open Nivat Nivat.LE2

/-! ## §1. The numeric core: a ray in a direction with positive `dot m` against a globally
`m`-bounded region is impossible. -/

/-- If `dot m` is bounded above by `c` on `R`, and `dot m d = D > 0`, no ray `z₀ + k • d`
(`k : ℕ`) can stay in `R` forever. -/
theorem rayIn_false_of_dot_pos {R : Set (ℤ × ℤ)} {z₀ m d : ℤ × ℤ} {c D : ℤ}
    (hbound : ∀ z ∈ R, dot m z ≤ c) (hD : dot m d = D) (hDpos : 0 < D)
    (hray : Colle41.RayIn R z₀ d) : False := by
  set k : ℕ := (c + 1 - dot m z₀).toNat with hk
  have hk' : c + 1 - dot m z₀ ≤ (k : ℤ) := Int.self_le_toNat _
  have hmem := hray k
  have hle := hbound _ hmem
  rw [dot_add_zsmul, hD] at hle
  have hknonneg : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have hprod : (0 : ℤ) ≤ (k : ℤ) * (D - 1) := mul_nonneg hknonneg (by omega)
  nlinarith [hle, hk', hprod]

/-! ## §2. Sign identities: `dot n' (dir n) = det n n'` and `dot n (-(dir n')) = det n n'`. -/

theorem dot_dir_n_eq_det {n n' : ℤ × ℤ} : dot n' (dir n) = det n n' := by
  rw [dot_dir_eq_neg_det]; exact (det_skew n n').symm

theorem dot_neg_dir_n'_eq_det {n n' : ℤ × ℤ} : dot n (-(dir n')) = det n n' := by
  rw [dot_neg_right, dot_dir_eq_neg_det]; ring

/-! ## §3. The bridge. -/

/-- **The bridge, team-lead's exact target.**  `latticeConvex` is `h`'s field directly; each
ray comes from `RegionRayDir.rays_of_isRegion`'s disjunction, with the wrong disjunct killed by
`rayIn_false_of_dot_pos` fed `h.detPos`. -/
theorem colle41_of_le2 {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ} (h : Nivat.LE2.IsRegion R n n') :
    Nivat.Colle41.IsRegion R (-(dir n)) (dir n') := by
  obtain ⟨hL, hR⟩ := Nivat.RegionRayDir.rays_of_isRegion h
  obtain ⟨q', hq'⟩ := h.semiInf'.2.nonempty
  obtain ⟨q, hq⟩ := h.semiInf.2.nonempty
  have hboundn' : ∀ z ∈ R, dot n' z ≤ dot n' q' := fun z hz => hq'.2 z hz
  have hboundn : ∀ z ∈ R, dot n z ≤ dot n q := fun z hz => hq.2 z hz
  have hrayL : ∃ z₀ : ℤ × ℤ, Colle41.RayIn R z₀ (-(dir n)) := by
    rcases hL with ⟨z₀, hray⟩ | hgood
    · exact (rayIn_false_of_dot_pos hboundn' dot_dir_n_eq_det h.detPos hray).elim
    · exact hgood
  have hrayR : ∃ z₀ : ℤ × ℤ, Colle41.RayIn R z₀ (dir n') := by
    rcases hR with hgood | ⟨z₀, hray⟩
    · exact hgood
    · exact (rayIn_false_of_dot_pos hboundn dot_neg_dir_n'_eq_det h.detPos hray).elim
  exact ⟨h.latticeConvex, hrayL, hrayR⟩

/-- **Corollary: the bridge packaged with the orientation datum it consumed.**  Downstream
consumers that need both the (lossy) `Colle41.IsRegion` shape *and* the fact that its two
directions come from a positively-oriented `(ℓ,ℓ')`-pair get both at once, instead of
re-deriving `detPos` from `h` by hand. -/
theorem colle41_of_le2_with_detPos {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ}
    (h : Nivat.LE2.IsRegion R n n') :
    Nivat.Colle41.IsRegion R (-(dir n)) (dir n') ∧ 0 < det n n' :=
  ⟨colle41_of_le2 h, h.detPos⟩

end Nivat.RegionOrientBridge

#print axioms Nivat.RegionOrientBridge.rayIn_false_of_dot_pos
#print axioms Nivat.RegionOrientBridge.colle41_of_le2
#print axioms Nivat.RegionOrientBridge.colle41_of_le2_with_detPos
