/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.L1Cut
import Nivat.External.Colle.LowComplexityWindow
import Nivat.External.Colle.RegionSweep
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.HbaseBridge
import Nivat.Lattice.Primitive

/-!
# `hlev` measurement: a genuine level gap in `maxB`'s output (2026-09-19, L1B)

Exclusive file of lane L1B.  `L1Assemble.lean` (L1asm's), `RegionSteps.lean` (team-lead's) and
`RegionSweep.lean` (Rsweep's) are only imported, never edited.

## What this refutes, precisely (`PROTOCOL.md` §27)

`OPEN.md #10` reframed `hlev : Nivat.RegionSweep.LevelInterval B vl` (an `ofWedge` hypothesis,
`L1RegionBuild.lean:351`) as a property of the *specific constructed* set
`B = maxB (derivedQ ε u' S₁) u'` (`RegionSteps.lean`'s `ofMaxB`), not a free binder.  Two prior
rounds measured that the existing coverage lemmas (`maxB_wide_levels`, `maxB_block`,
`L1Assemble.lean:1655,1713`) only ever certify **one bounded window per side** — the anchor
`a` in `exists_parallelogram` is forced to the leftmost point of the extremal `u'`-face
(`faceIsRun`'s `mlo := M.min'`, `L1Fields.lean:597`), not a free/slidable parameter, so no
tiling argument is available from that machinery.

This file settles the arithmetic question those two rounds left open: **is
`LevelInterval (↑(maxB (derivedQ ε u' S₁) u') vl) vl` actually true**, for a genuine
`Nivat.LatticeConvex S₁` (not an ad hoc `Finset`)?  Answer: **no** — `not_levelInterval_maxB`
below exhibits a 9-point lattice-convex `S₁` (`u' = (1,0)`, `vl = (0,1)`, `ε = true`,
`pw = (topFace true u' S₁).card - 1 = 2`, matching what the leaf's construction would compute,
not a hand-picked `pw`) whose `maxB` output has a level attained on both sides of `-2` but not
at `-2` itself.

⚠ **This is not the `{(0,0),(1,2)}` counterexample from `RegionSweep.lean` reused** — that one
refutes "`LatticeConvex` (alone) ⇒ `LevelInterval`"; the `S₁` here is different, and the
refuted closure is "`maxB (derivedQ ε u' S₁) u'` (the leaf's *specific* construction, run
through its own `pw`) ⇒ `LevelInterval`" — a strictly narrower, more informative claim, since
`maxB`'s own run-filter is exactly the leaf's mechanism, not an arbitrary sweep.

**Consequence for `ofWedge`**: since the counterexample instantiates the real construction
(same `derivedQ`/`topFace`/`maxB` definitions the leaf uses, with `pw` computed the same way),
`hlev` genuinely cannot be discharged as stated from `S₁` being `LatticeConvex` alone — no
matter what extra structure `S₁ = 𝒮_φ`-as-a-generating-set carries, discharging `hlev` (if
possible at all) requires using **generating-set-specific** facts beyond bare lattice
convexity, since lattice convexity alone is insufficient (this witness *is* lattice convex).
-/

set_option autoImplicit false

namespace Nivat.ColleReg.L1Data

open Nivat Nivat.LE2

section LevelGapWitness

/-! ### A lattice-convex sheared strip: rows `y = 0, 1, 2`, row `y` at `x ∈ [3y, 3y+2]`. -/

/-- Local copy of `Nivat.Case2WindowProbe.convex_box` (avoiding an import of the heavy
`Case2WindowProbe.lean`, which is not needed for anything else here). -/
private theorem convex_box (x₀ x₁ y₀ y₁ : ℝ) :
    Convex ℝ {q : ℝ × ℝ | x₀ ≤ q.1 ∧ q.1 ≤ x₁ ∧ y₀ ≤ q.2 ∧ q.2 ≤ y₁} := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  have e1 := mul_le_mul_of_nonneg_left hu1 ha
  have e2 := mul_le_mul_of_nonneg_left hv1 hb
  have e3 := mul_le_mul_of_nonneg_left hu2 ha
  have e4 := mul_le_mul_of_nonneg_left hv2 hb
  have e5 := mul_le_mul_of_nonneg_left hu3 ha
  have e6 := mul_le_mul_of_nonneg_left hv3 hb
  have e7 := mul_le_mul_of_nonneg_left hu4 ha
  have e8 := mul_le_mul_of_nonneg_left hv4 hb
  have hx₀ : a * x₀ + b * x₀ = x₀ := by rw [← add_mul, hab, one_mul]
  have hx₁ : a * x₁ + b * x₁ = x₁ := by rw [← add_mul, hab, one_mul]
  have hy₀ : a * y₀ + b * y₀ = y₀ := by rw [← add_mul, hab, one_mul]
  have hy₁ : a * y₁ + b * y₁ = y₁ := by rw [← add_mul, hab, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Local copy of `Nivat.Case2WindowProbe.latticeConvex_of_box`. -/
private theorem latticeConvex_of_box {W : Finset (ℤ × ℤ)} {x₀ x₁ y₀ y₁ : ℤ}
    (hW : ∀ z, z ∈ W ↔ (x₀ ≤ z.1 ∧ z.1 ≤ x₁) ∧ (y₀ ≤ z.2 ∧ z.2 ≤ y₁)) : LatticeConvex W := by
  intro z hz
  have hsub : Conv W ⊆
      {q : ℝ × ℝ | (x₀ : ℝ) ≤ q.1 ∧ q.1 ≤ x₁ ∧ (y₀ : ℝ) ≤ q.2 ∧ q.2 ≤ y₁} := by
    apply convexHull_min _ (convex_box _ _ _ _)
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe, hW] at hw
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hw
    simp only [Set.mem_ofPred_eq, toReal]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3,
      by exact_mod_cast h4⟩
  have hz' := hsub hz
  simp only [Set.mem_ofPred_eq, toReal] at hz'
  obtain ⟨h1, h2, h3, h4⟩ := hz'
  rw [hW]
  exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩,
    by exact_mod_cast h3, by exact_mod_cast h4⟩

/-- The ambient box: `x ∈ [0,8]`, `y ∈ [0,2]`. -/
private noncomputable def bigBox : Finset (ℤ × ℤ) := (Finset.Icc (0 : ℤ) 8) ×ˢ (Finset.Icc (0 : ℤ) 2)

private theorem mem_bigBox_iff (z : ℤ × ℤ) :
    z ∈ bigBox ↔ (0 ≤ z.1 ∧ z.1 ≤ 8) ∧ (0 ≤ z.2 ∧ z.2 ≤ 2) := by
  unfold bigBox
  simp only [Finset.mem_product, Finset.mem_Icc]

private theorem latticeConvex_bigBox : LatticeConvex bigBox :=
  latticeConvex_of_box mem_bigBox_iff

/-- The witness set: the sheared strip `{(x,y) : 0 ≤ y ≤ 2, 3y ≤ x ≤ 3y+2}`, cut out of
`bigBox` by two real half-planes. -/
noncomputable def witnessS1 : Finset (ℤ × ℤ) :=
  (bigBox.filter (fun z => inner2 (toReal ((1 : ℤ), (-3 : ℤ))) z < (3 : ℝ))).filter
    (fun z => inner2 (toReal ((-1 : ℤ), (3 : ℤ))) z < (1 : ℝ))

private theorem inner2_w1 (z : ℤ × ℤ) :
    inner2 (toReal ((1 : ℤ), (-3 : ℤ))) z = (z.1 : ℝ) - 3 * (z.2 : ℝ) := by
  simp only [inner2, toReal]; push_cast; ring

private theorem inner2_w2 (z : ℤ × ℤ) :
    inner2 (toReal ((-1 : ℤ), (3 : ℤ))) z = -(z.1 : ℝ) + 3 * (z.2 : ℝ) := by
  simp only [inner2, toReal]; push_cast; ring

theorem latticeConvex_witnessS1 : LatticeConvex witnessS1 := by
  unfold witnessS1
  exact Nivat.Colle.latticeConvex_filter_inner2_lt
    (Nivat.Colle.latticeConvex_filter_inner2_lt latticeConvex_bigBox _ _) _ _

/-- The pure-integer characterisation of membership: the real cuts collapse to `x ≤ 3y+2` and
`x ≥ 3y` since the thresholds `3` and `1` are exact integers. -/
theorem mem_witnessS1_iff (z : ℤ × ℤ) :
    z ∈ witnessS1 ↔ (0 ≤ z.1 ∧ z.1 ≤ 8) ∧ (0 ≤ z.2 ∧ z.2 ≤ 2) ∧
      z.1 - 3 * z.2 < 3 ∧ -z.1 + 3 * z.2 < 1 := by
  unfold witnessS1
  simp only [Finset.mem_filter, mem_bigBox_iff, inner2_w1, inner2_w2]
  constructor
  · rintro ⟨⟨hbox, h1⟩, h2⟩
    exact ⟨hbox.1, hbox.2, by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨hx, hy, h1, h2⟩
    exact ⟨⟨⟨hx, hy⟩, by exact_mod_cast h1⟩, by exact_mod_cast h2⟩

/-- Pure-integer restatement, dropping the box bounds to the two diagonal constraints
(the box bounds are implied for the row range we use, but keeping them explicit avoids any
`omega` needing to invent them). -/
theorem mem_witnessS1_iff' (z : ℤ × ℤ) :
    z ∈ witnessS1 ↔ (0 ≤ z.1 ∧ z.1 ≤ 8) ∧ (0 ≤ z.2 ∧ z.2 ≤ 2) ∧
      3 * z.2 ≤ z.1 ∧ z.1 ≤ 3 * z.2 + 2 := by
  rw [mem_witnessS1_iff]
  constructor
  · rintro ⟨hx, hy, h1, h2⟩; exact ⟨hx, hy, by omega, by omega⟩
  · rintro ⟨hx, hy, h1, h2⟩; exact ⟨hx, hy, by omega, by omega⟩

/-! ### The leaf's own construction, run on `witnessS1` -/

private theorem cutNormal_eq :
    cutNormal true ((1 : ℤ), (0 : ℤ)) = toReal ((0 : ℤ), (1 : ℤ)) := by
  unfold cutNormal perp
  norm_num

private theorem inner2_cutNormal_eq (z : ℤ × ℤ) :
    inner2 (cutNormal true ((1 : ℤ), (0 : ℤ))) z = (z.2 : ℝ) := by
  rw [cutNormal_eq]; simp only [inner2, toReal]; ring

/-- The top `u'`-level of `witnessS1` (in the sense `topFace`/`levelMax` use) is exactly `2`,
the `y = 2` row. -/
theorem levelMax_witnessS1 :
    levelMax witnessS1 (cutNormal true ((1 : ℤ), (0 : ℤ))) = (2 : ℝ) := by
  have hne : witnessS1.Nonempty := ⟨(0, 0), (mem_witnessS1_iff' _).mpr ⟨by omega, by omega,
    by omega, by omega⟩⟩
  unfold levelMax
  rw [dif_pos hne]
  apply le_antisymm
  · apply Finset.sup'_le
    intro z hz
    rw [inner2_cutNormal_eq]
    have := (mem_witnessS1_iff' z).mp hz
    exact_mod_cast this.2.1.2
  · have h62 : ((6 : ℤ), (2 : ℤ)) ∈ witnessS1 :=
      (mem_witnessS1_iff' _).mpr ⟨by omega, by omega, by omega, by omega⟩
    have := Finset.le_sup' (fun z => inner2 (cutNormal true ((1 : ℤ), (0 : ℤ))) z) h62
    rwa [inner2_cutNormal_eq] at this

/-- The top `u'`-face is exactly the three points of row `y = 2`, so `pw = 3 - 1 = 2` — the
same `pw` the leaf's `L1DataMax.hBmax` would compute from `S₁ := witnessS1`, not a hand-picked
constant. -/
theorem topFace_witnessS1 :
    topFace true ((1 : ℤ), (0 : ℤ)) witnessS1 =
      ({((6 : ℤ), (2 : ℤ)), (7, 2), (8, 2)} : Finset (ℤ × ℤ)) := by
  unfold topFace
  rw [levelMax_witnessS1]
  ext z
  simp only [Nivat.R2.mem_face, inner2_cutNormal_eq, Finset.mem_insert, Finset.mem_singleton,
    Prod.ext_iff]
  constructor
  · rintro ⟨hz, hz2⟩
    have h2 : z.2 = 2 := by exact_mod_cast hz2
    have h := (mem_witnessS1_iff' z).mp hz
    have hx1 : z.1 ≤ 8 := h.1.2
    have hlo : 6 ≤ z.1 := by omega
    omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      refine ⟨(mem_witnessS1_iff' _).mpr ⟨by omega, by omega, by omega, by omega⟩, by
        rw [h2]; norm_num⟩

theorem topFace_card_witnessS1 :
    (topFace true ((1 : ℤ), (0 : ℤ)) witnessS1).card = 3 := by
  rw [topFace_witnessS1]; decide

/-- `derivedQ`, the leaf's own `Q`, is `witnessS1` minus the top row — i.e. exactly rows
`y = 0, 1`. -/
theorem mem_derivedQ_witnessS1_iff (z : ℤ × ℤ) :
    z ∈ derivedQ true ((1 : ℤ), (0 : ℤ)) witnessS1 ↔
      (0 ≤ z.1 ∧ z.1 ≤ 8) ∧ (0 ≤ z.2 ∧ z.2 ≤ 1) ∧ 3 * z.2 ≤ z.1 ∧ z.1 ≤ 3 * z.2 + 2 := by
  unfold derivedQ
  rw [levelMax_witnessS1]
  simp only [Finset.mem_filter, mem_witnessS1_iff', inner2_cutNormal_eq]
  constructor
  · rintro ⟨⟨hx, hy, h1, h2⟩, h3⟩
    have : z.2 < 2 := by exact_mod_cast h3
    exact ⟨hx, ⟨hy.1, by omega⟩, h1, h2⟩
  · rintro ⟨hx, hy, h1, h2⟩
    exact ⟨⟨hx, ⟨hy.1, by omega⟩, h1, h2⟩, by exact_mod_cast (by omega : z.2 < 2)⟩

/-! ### The gap: `maxB`'s output misses level `-2` (i.e. `x = 2`) strictly between two of its
own attained levels. -/

theorem mem_00 : ((0 : ℤ), (0 : ℤ)) ∈
    maxB (derivedQ true ((1 : ℤ), (0 : ℤ)) witnessS1) ((1 : ℤ), (0 : ℤ))
      ((topFace true ((1 : ℤ), (0 : ℤ)) witnessS1).card - 1) := by
  rw [topFace_card_witnessS1, mem_maxB]
  refine ⟨(mem_derivedQ_witnessS1_iff _).mpr ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
  intro i hi
  interval_cases i
  · have he : ((0 : ℤ), (0 : ℤ)) + ((0 : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ)) = ((0 : ℤ), (0 : ℤ)) := by
      norm_num
    rw [he]
    exact (mem_derivedQ_witnessS1_iff _).mpr ⟨by omega, by omega, by omega, by omega⟩
  · have he : ((0 : ℤ), (0 : ℤ)) + ((1 : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (0 : ℤ)) := by
      norm_num
    rw [he]
    exact (mem_derivedQ_witnessS1_iff _).mpr ⟨by omega, by omega, by omega, by omega⟩

theorem mem_31 : ((3 : ℤ), (1 : ℤ)) ∈
    maxB (derivedQ true ((1 : ℤ), (0 : ℤ)) witnessS1) ((1 : ℤ), (0 : ℤ))
      ((topFace true ((1 : ℤ), (0 : ℤ)) witnessS1).card - 1) := by
  rw [topFace_card_witnessS1, mem_maxB]
  refine ⟨(mem_derivedQ_witnessS1_iff _).mpr ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
  intro i hi
  interval_cases i
  · have he : ((3 : ℤ), (1 : ℤ)) + ((0 : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ)) = ((3 : ℤ), (1 : ℤ)) := by
      norm_num
    rw [he]
    exact (mem_derivedQ_witnessS1_iff _).mpr ⟨by omega, by omega, by omega, by omega⟩
  · have he : ((3 : ℤ), (1 : ℤ)) + ((1 : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ)) = ((4 : ℤ), (1 : ℤ)) := by
      norm_num
    rw [he]
    exact (mem_derivedQ_witnessS1_iff _).mpr ⟨by omega, by omega, by omega, by omega⟩

/-- No element of `maxB`'s output has `x`-coordinate `2` — the only candidate in `witnessS1` is
`(2,0)`, and it fails the run condition since `(3,0) ∉ witnessS1` (row `y = 0` stops at `x = 2`). -/
theorem not_mem_level_two {c : ℤ × ℤ} :
    c ∈ maxB (derivedQ true ((1 : ℤ), (0 : ℤ)) witnessS1) ((1 : ℤ), (0 : ℤ))
      ((topFace true ((1 : ℤ), (0 : ℤ)) witnessS1).card - 1) → c.1 ≠ 2 := by
  intro hc hc2
  rw [topFace_card_witnessS1] at hc
  obtain ⟨hcQ, hrun⟩ := mem_maxB.mp hc
  have hcS1 := (mem_derivedQ_witnessS1_iff c).mp hcQ
  have hc0 : c.2 = 0 := by omega
  have h30 : c + ((1 : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ derivedQ true ((1 : ℤ), (0 : ℤ)) witnessS1 :=
    hrun 1 (by omega)
  have he : c + ((1 : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ)) = (c.1 + 1, c.2) := by
    apply Prod.ext <;> simp
  rw [he] at h30
  have h30' := (mem_derivedQ_witnessS1_iff _).mp h30
  simp only at h30'
  omega

/-- **The gap, as a `LevelInterval` failure.**  `vl := (0,1)`; `det vl z = -z.1`.  Levels `-3`
(at `(3,1)`) and `0` (at `(0,0)`) are both attained by `maxB`'s output, but the level `-2`
strictly between them is not — even though the construction is the leaf's own
`maxB (derivedQ ε u' S₁) u'` run on a genuine `Nivat.LatticeConvex S₁`, with `pw` computed by
the same `(topFace ...).card - 1` formula `L1DataMax.hBmax` uses. -/
theorem not_levelInterval_maxB_witnessS1 :
    ¬ Nivat.RegionSweep.LevelInterval
        (↑(maxB (derivedQ true ((1 : ℤ), (0 : ℤ)) witnessS1) ((1 : ℤ), (0 : ℤ))
              ((topFace true ((1 : ℤ), (0 : ℤ)) witnessS1).card - 1)) : Set (ℤ × ℤ))
        ((0 : ℤ), (1 : ℤ)) := by
  intro h
  obtain ⟨c, hc, hceq⟩ := h ((3 : ℤ), (1 : ℤ)) mem_31 ((0 : ℤ), (0 : ℤ)) mem_00 (-2)
    (by simp only [det]; omega) (by simp only [det]; omega)
  have hc2 : c.1 = 2 := by simp only [det] at hceq; omega
  exact not_mem_level_two hc hc2

end LevelGapWitness

/-! ### `OPEN.md #10`, corrected object: does *any* 2-dimensional lattice-convex `Set`, together
with a primitive direction, force `LevelInterval`?  (2026-09-19, L1B)

Cclaim and L1asm independently caught that `hlev`'s `B` in `ofWedge`/`ofWedgeAt`
(`L1RegionBuild.lean:351`) is the `Case1`/`EnvOf` envelope witness `B : Set (ℤ × ℤ)`, not
`maxB`'s `Finset` output above — the section above answers a real but different question.
Via L1asm's `hres_forces_levelInterval_on_Sphi` (`tmp/l1asm_leaf_wire.lean`, `enveloped_refl`),
the corrected question reduces to a pure lattice-geometry proposition:

> `S : Set (ℤ × ℤ)` lattice-convex, non-collinear (2-dimensional), `vl` primitive
> `⟹ LevelInterval S vl`?

The existing 1-dimensional witness `L1CoverWedge.case1_and_not_levelInterval`
(`L1CoverWedge.lean:329`, `{(0,0),(1,2)}`) does not settle this: it is collinear, so the
2-dimensionality hypothesis is untested by it.  Both witnesses below are genuinely
2-dimensional and settle the corrected proposition: **false**, dimensionality does not
rescue `hlev`. -/

section TwoDGapWitness

/-- Witness 1 (L1B, independent construction): a genuine 2-dimensional lattice-convex
quadrilateral (triangle `(0,0),(2,1),(1,2)` plus interior-adjacent point `(1,1)`) whose
level set along `vl = (1,-1)` skips a level strictly between two attained ones. -/
def S2 : Set (ℤ × ℤ) := {((0:ℤ),(0:ℤ)), ((2:ℤ),(1:ℤ)), ((1:ℤ),(2:ℤ)), ((1:ℤ),(1:ℤ))}

private def triangleS2 : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≤ 2*p.2 ∧ p.1 + p.2 ≤ 3 ∧ 2*p.1 ≥ p.2}

private theorem convex_triangleS2 : Convex ℝ triangleS2 := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [triangleS2, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hx1 ha, mul_le_mul_of_nonneg_left hy1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx2 ha, mul_le_mul_of_nonneg_left hy2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx3 ha, mul_le_mul_of_nonneg_left hy3 hb]

private theorem closed_triangleS2 : IsClosed triangleS2 := by
  have e1 : IsClosed {p : ℝ × ℝ | p.1 ≤ 2*p.2} := isClosed_le continuous_fst (by fun_prop)
  have e2 : IsClosed {p : ℝ × ℝ | p.1 + p.2 ≤ 3} := isClosed_le (by fun_prop) continuous_const
  have e3 : IsClosed {p : ℝ × ℝ | 2*p.1 ≥ p.2} := isClosed_le continuous_snd (by fun_prop)
  have : triangleS2 = {p : ℝ × ℝ | p.1 ≤ 2*p.2} ∩ {p : ℝ × ℝ | p.1 + p.2 ≤ 3} ∩
      {p : ℝ × ℝ | 2*p.1 ≥ p.2} := by ext p; simp [triangleS2, and_assoc]
  rw [this]; exact (e1.inter e2).inter e3

theorem mem_S2_iff (z : ℤ × ℤ) : z ∈ S2 ↔ z = (0,0) ∨ z = (2,1) ∨ z = (1,2) ∨ z = (1,1) := by
  simp [S2]

theorem eq_preimage_triangleS2 : S2 = toReal ⁻¹' triangleS2 := by
  ext z
  rw [mem_S2_iff, Set.mem_preimage]
  simp only [triangleS2, Set.mem_ofPred_eq, toReal]
  constructor
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num
  · rintro ⟨h1, h2, h3⟩
    have h1' : z.1 ≤ 2 * z.2 := by exact_mod_cast h1
    have h2' : z.1 + z.2 ≤ 3 := by exact_mod_cast h2
    have h3' : 2 * z.1 ≥ z.2 := by exact_mod_cast h3
    have hb1 : 0 ≤ z.1 := by omega
    have hb2 : z.1 ≤ 2 := by omega
    have hb3 : 0 ≤ z.2 := by omega
    have hb4 : z.2 ≤ 2 := by omega
    have : z.1 = 0 ∧ z.2 = 0 ∨ z.1 = 2 ∧ z.2 = 1 ∨ z.1 = 1 ∧ z.2 = 2 ∨ z.1 = 1 ∧ z.2 = 1 := by
      omega
    rcases this with ⟨e1,e2⟩|⟨e1,e2⟩|⟨e1,e2⟩|⟨e1,e2⟩
    · left; exact Prod.ext e1 e2
    · right; left; exact Prod.ext e1 e2
    · right; right; left; exact Prod.ext e1 e2
    · right; right; right; exact Prod.ext e1 e2

theorem isLatticeConvexRegion_S2 : IsLatticeConvexRegion S2 :=
  ⟨triangleS2, convex_triangleS2, closed_triangleS2, eq_preimage_triangleS2⟩

theorem det_S2_not_collinear :
    det (((2:ℤ),(1:ℤ)) - ((0:ℤ),(0:ℤ))) (((1:ℤ),(2:ℤ)) - ((0:ℤ),(0:ℤ))) = 3 := by
  simp [det]

theorem primitive_one_negone : Primitive ((1:ℤ), (-1:ℤ)) := ⟨1, 0, by ring⟩

theorem not_levelInterval_S2 : ¬ Nivat.RegionSweep.LevelInterval S2 ((1:ℤ), (-1:ℤ)) := by
  intro h
  obtain ⟨c, hc, hcm⟩ := h (0,0) (by rw [mem_S2_iff]; tauto) (1,1) (by rw [mem_S2_iff]; tauto) 1
    (by simp [det]) (by simp [det])
  rw [mem_S2_iff] at hc
  rcases hc with rfl|rfl|rfl|rfl <;> simp [det] at hcm

/-! ### Necessity, not just insufficiency (2026-09-19, team-lead's `ofWedge`-trace request)

`hlev` feeds exactly one conclusion field of `ofWedge`/`ofWedgeAt`: the `isRegion` component of
`Nivat.L1Region.RegionFamily`, via `isRegion_wedgeFull` (`L1RegionBuild.lean:271`) →
`isLatticeConvexRegion_wedgeFull` (`:216`) → `isLatticeConvexRegion_fullSweep` (`:212`) →
`Nivat.RegionSweep.isLatticeConvexRegion_sweep` (`RegionSweep.lean:213`), applied to `B` and to
`sweep B (-vl)` in turn.  Nothing else in `ofWedge`'s body touches `hlev` — `grow` comes from
`Nivat.L1Region.cut_ssubset` (no `hlev`), `base`/`union_not` are the caller's `hbase`/`hinf`.

**The weakened form does not survive.**  `isLatticeConvexRegion_sweep`'s "Case 1" branch
(`RegionSweep.lean:277-284`) is invoked once *per missing level* `det w z` of a candidate point
`z` not yet known to be in the sweep — a single missing level between two attained ones already
forces the contradiction step to fire, with no slack for "gap of length ≥ 2" or any other
weakening: the module's own docstring calls `LevelInterval` "necessary **and** sufficient"
(`RegionSweep.lean:30`), and `not_isLatticeConvexRegion_sweep_pair` (`:428`) already proves the
*conclusion* (not just the proof method) false for `{(0,0),(1,2)}`, whose `(1,0)`-levels
`{0,2}` have a single-level gap at `1` — exactly `witnessS1`/`S2`/`S3`'s failure mode, not a
weaker one.

**This file now proves necessity directly for `S2` itself** (not the 1-dimensional pair):
`fullSweep S2 vl` — the exact set `isLatticeConvexRegion_fullSweep` is asked to certify — is
provably **not** `IsLatticeConvexRegion`, via the same midpoint argument
(`Colle43.latticeConvexRegion_midpoint`) `not_isLatticeConvexRegion_sweep_pair` uses: translate
`a := (0,0)` (level `0`) and `b := (1,1)` (level `2`) by `0` and `1` copies of `vl` respectively
to land at `(0,0)` and `(2,0)`, whose midpoint `(1,0)` sits at the missing level `1` — and
`(1,0)` cannot be in `fullSweep S2 vl` since every point of `fullSweep S2 vl` has a level in
`S2`'s level set `{0,2,3}`, which does not contain `1`.  So **no weakening of `hlev` can work
for this `B`** — the target conclusion itself is false, not merely unproved from a weaker
hypothesis. -/

theorem not_isLatticeConvexRegion_fullSweep_S2 :
    ¬ IsLatticeConvexRegion (Nivat.ColleReg.fullSweep S2 ((1:ℤ), (-1:ℤ))) := by
  intro hK
  have ha : ((0:ℤ), (0:ℤ)) ∈ Nivat.ColleReg.fullSweep S2 ((1:ℤ), (-1:ℤ)) :=
    Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨(0,0), (mem_S2_iff _).mpr (by tauto), 0, by simp⟩
  have hb : ((2:ℤ), (0:ℤ)) ∈ Nivat.ColleReg.fullSweep S2 ((1:ℤ), (-1:ℤ)) :=
    Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨(1,1), (mem_S2_iff _).mpr (by tauto), 1, by
      apply Prod.ext <;> simp⟩
  have hmid := Nivat.Colle43.latticeConvexRegion_midpoint hK ha hb
    (c := ((1:ℤ), (0:ℤ))) (by apply Prod.ext <;> simp)
  obtain ⟨g, hg, k, hgk⟩ := Nivat.ColleReg.mem_fullSweep_iff.mp hmid
  rw [mem_S2_iff] at hg
  have hlvl : det ((1:ℤ), (-1:ℤ)) ((1:ℤ), (0:ℤ)) = det ((1:ℤ), (-1:ℤ)) g := by
    rw [hgk]; exact Nivat.RegionSweep.det_add_zsmul_self _ _ _
  rcases hg with rfl|rfl|rfl|rfl <;> simp only [det] at hlvl <;> omega

/-! ### Self-correction: the refutation above is a *pathway* refutation, not an *instance*
refutation of `ofWedge`'s actual target (2026-09-19, L1B, checking my own previous claim
before it gets used elsewhere — same discipline `PROTOCOL.md` §25 asks of everyone else).

`not_isLatticeConvexRegion_fullSweep_S2` kills `fullSweep S2 vl` — the *intermediate* object
`isLatticeConvexRegion_wedgeFull`'s proof route builds *before* the outer forward `u'`-sweep.
It does **not** by itself say anything about `wedgeFull S2 vl u'`, the actual object `hlev`
needs to be lattice-convex.  Checked directly, by hand, before landing (§15 → then verified in
Lean below): the outer forward-`u'` sweep can *repair* a level gap that the inner two-sided
`vl`-sweep cannot, because sweeping a full `vl`-line forward by `u'` (with `(u',vl)`
unimodular) produces **every** full `vl`-line at every level `≥` the base line's level, not
just a strip — so a single missing level in `fullSweep`'s level set can vanish entirely once
the forward sweep runs.

**Concretely, for `u' := (1,0)`, `vl := (1,-1)` (unimodular: `det u' vl = -1`), `wedgeFull S2 vl
u'` is exactly the half-plane `{z : 0 ≤ det vl z}` — no gap, no repair needed, `latWedge = wedgeFull`
for this witness.**  Proof: `S2` contains `(0,0)` at level `0` (the minimum level attained by
`S2`); `(⊇)` for any `z` with `det vl z = n ≥ 0`, unimodularity gives `z = k • vl + n • u'` for
some `k` (since `det vl u' = 1`, the `u'`-coefficient in the `(vl,u')`-basis expansion of `z` is
exactly its level), so `z - n • u' = k • vl ∈ fullSweep S2 vl` via `(0,0) ∈ S2`, and `z` is that
point forward-swept by `n ≥ 0` copies of `u'`; `(⊆)` levels only increase (by `s ≥ 0`) under the
forward sweep, and `fullSweep S2 vl`'s levels are all `≥ 0`.  So `IsLatticeConvexRegion
(wedgeFull S2 vl u')` holds **unconditionally for this choice of `u'`** — `hlev` was never
needed for this particular instance, contradicting nothing in the general necessity argument
above (that argument is about the *sweep-of-a-single-set* lemma in isolation, not about the
compound `wedgeFull` object), but correcting the reach I claimed for
`not_isLatticeConvexRegion_fullSweep_S2` in the previous round: it does not "kill the `ofWedge`
route for `B := S2`" — only the specific proof route through `fullSweep` as an unconditionally
lattice-convex intermediate. -/

theorem det_vl_u'_eq_one : det ((1:ℤ),(-1:ℤ)) ((1:ℤ),(0:ℤ)) = 1 := by simp [det]

theorem mem_wedgeFull_S2_iff (z : ℤ × ℤ) :
    z ∈ Nivat.ColleReg.wedgeFull S2 ((1:ℤ),(-1:ℤ)) ((1:ℤ),(0:ℤ)) ↔
      0 ≤ det ((1:ℤ),(-1:ℤ)) z := by
  unfold Nivat.ColleReg.wedgeFull
  rw [Nivat.RegionSweep.mem_sweep]
  constructor
  · rintro ⟨g, hg, t, rfl⟩
    obtain ⟨c, hc, k, hck⟩ := Nivat.ColleReg.mem_fullSweep_iff.mp hg
    have hgl : det ((1:ℤ),(-1:ℤ)) g = det ((1:ℤ),(-1:ℤ)) c := by
      rw [hck]; exact Nivat.RegionSweep.det_add_zsmul_self _ _ _
    have hcl : 0 ≤ det ((1:ℤ),(-1:ℤ)) c := by
      rw [mem_S2_iff] at hc; rcases hc with rfl|rfl|rfl|rfl <;> simp [det]
    have hstep : det ((1:ℤ),(-1:ℤ)) (g + (t:ℤ) • ((1:ℤ),(0:ℤ))) =
        det ((1:ℤ),(-1:ℤ)) g + (t:ℤ) * det ((1:ℤ),(-1:ℤ)) ((1:ℤ),(0:ℤ)) := by
      simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [hstep, det_vl_u'_eq_one, hgl]
    have : (0:ℤ) ≤ (t:ℤ) := Int.natCast_nonneg t
    omega
  · intro hz
    set n : ℤ := det ((1:ℤ),(-1:ℤ)) z with hn
    -- Direct construction: z = (z - n•u') + n•u', and (z - n•u') = k•vl for some k.
    have hklem : ∃ k : ℤ, z - n • ((1:ℤ),(0:ℤ)) = k • ((1:ℤ),(-1:ℤ)) := by
      refine ⟨-(z.2), ?_⟩
      apply Prod.ext
      · simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul, hn, det]; ring
      · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul, hn, det]; ring
    obtain ⟨k, hk⟩ := hklem
    refine ⟨(0,0) + k • ((1:ℤ),(-1:ℤ)),
      Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨(0,0), (mem_S2_iff _).mpr (by tauto), k, rfl⟩,
      n.toNat, ?_⟩
    have hnn : (0:ℤ) ≤ n := hz
    have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hnn
    have hk1 : z.1 - n = k := by simpa using congrArg Prod.fst hk
    have hk2 : z.2 = -k := by simpa using congrArg Prod.snd hk
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, zero_add]
      omega
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, zero_add]
      omega

theorem isLatticeConvexRegion_wedgeFull_S2 :
    IsLatticeConvexRegion (Nivat.ColleReg.wedgeFull S2 ((1:ℤ),(-1:ℤ)) ((1:ℤ),(0:ℤ))) := by
  refine ⟨{p : ℝ × ℝ | 0 ≤ Nivat.RegionSweep.rlevel ((1:ℤ),(-1:ℤ)) p},
    convex_halfSpace_ge (Nivat.RegionSweep.isLinearMap_rlevel _) _,
    isClosed_le continuous_const (Nivat.RegionSweep.continuous_rlevel _), ?_⟩
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Nivat.RegionSweep.rlevel_toReal]
  rw [mem_wedgeFull_S2_iff]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-! ### `latWedge`: the repair `ofWedge` would need in general, and its cost

`latWedge` is `wedgeFull`'s lattice-convex hull — the smallest closed-convex-real-set-preimage
containing it, i.e. `IsLatticeConvexRegion` is true of it *unconditionally*, with no hypothesis
on `B` at all (the witness set is the hull itself). -/

/-- `latWedge B vl u'`: the lattice points of the closed convex hull of `wedgeFull B vl u'`.
This is `IsLatticeConvexRegion` **unconditionally** — no `hlev`, no hypothesis on `B` at all. -/
noncomputable def latWedge (B : Set (ℤ × ℤ)) (vl u' : ℤ × ℤ) : Set (ℤ × ℤ) :=
  toReal ⁻¹' (convHullOf (Nivat.ColleReg.wedgeFull B vl u'))

theorem isLatticeConvexRegion_latWedge (B : Set (ℤ × ℤ)) (vl u' : ℤ × ℤ) :
    IsLatticeConvexRegion (latWedge B vl u') :=
  ⟨convHullOf (Nivat.ColleReg.wedgeFull B vl u'), (convex_convexHull ℝ _).closure,
    isClosed_closure, rfl⟩

theorem wedgeFull_subset_latWedge (B : Set (ℤ × ℤ)) (vl u' : ℤ × ℤ) :
    Nivat.ColleReg.wedgeFull B vl u' ⊆ latWedge B vl u' :=
  fun z hz => subset_closure (subset_convexHull ℝ _ ⟨z, hz, rfl⟩)

/-- **Cost, measured on `S2`: zero.**  Since `wedgeFull S2 vl u'` is already exactly the
half-plane `{det vl · ≥ 0}` (`isLatticeConvexRegion_wedgeFull_S2` above), it equals its own
lattice-convex hull — `latWedge S2 vl u' = wedgeFull S2 vl u'` for this choice of `u'`, so
`hbase` does not need to hold on any larger set and `hinf` does not get any easier, for this
particular `B`.  **This does not generalise**: `wedgeFull`'s repair-for-free depended on `(0,0)`
being `S2`'s own minimum-level point and on the specific unimodular pairing `det vl u' = 1`;
a different `u'` (still satisfying `hunimod`) or a `B` whose minimum-level point is not itself
enough to regenerate every higher level via the `(vl,u')`-lattice-basis change could still leave
a genuine, unrepaired gap.  Not evaluated here — flagging rather than extrapolating from one
instance (`PROTOCOL.md` §25 applies to this claim too). -/
theorem latWedge_eq_wedgeFull_S2 :
    latWedge S2 ((1:ℤ),(-1:ℤ)) ((1:ℤ),(0:ℤ)) =
      Nivat.ColleReg.wedgeFull S2 ((1:ℤ),(-1:ℤ)) ((1:ℤ),(0:ℤ)) := by
  apply Set.Subset.antisymm _ (wedgeFull_subset_latWedge _ _ _)
  intro z hz
  rw [mem_wedgeFull_S2_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hCconv, hCclosed, hCeq⟩ := isLatticeConvexRegion_wedgeFull_S2
  have hzC : toReal z ∉ C := by
    intro h
    have : z ∈ Nivat.ColleReg.wedgeFull S2 ((1:ℤ),(-1:ℤ)) ((1:ℤ),(0:ℤ)) := by
      rw [hCeq]; exact h
    rw [mem_wedgeFull_S2_iff] at this
    omega
  have hzhull : toReal z ∈ convHullOf (Nivat.ColleReg.wedgeFull S2 ((1:ℤ),(-1:ℤ)) ((1:ℤ),(0:ℤ))) := by
    have := hz
    unfold latWedge at this
    exact this
  have hsub : convHullOf (Nivat.ColleReg.wedgeFull S2 ((1:ℤ),(-1:ℤ)) ((1:ℤ),(0:ℤ))) ⊆ C := by
    apply closure_minimal _ hCclosed
    apply convexHull_min _ hCconv
    rintro _ ⟨w, hw, rfl⟩
    rw [hCeq] at hw; exact hw
  exact hzC (hsub hzhull)

/-- Witness 2 (team-lead's hand-derived candidate, §15 → verified here as a kernel fact):
the triangle `(0,0),(1,3),(1,4)` (Pick's theorem: area `1/2`, all three edges primitive so
`B = 3`, hence `I = 0` — the only lattice points are the three named vertices) has
`vl = (1,0)`-levels `{0,3,4}`, skipping `1` strictly between `0` and `4`. -/
def S3 : Set (ℤ × ℤ) := {((0:ℤ),(0:ℤ)), ((1:ℤ),(3:ℤ)), ((1:ℤ),(4:ℤ))}

theorem mem_S3_iff (z : ℤ × ℤ) : z ∈ S3 ↔ z = (0,0) ∨ z = (1,3) ∨ z = (1,4) := by simp [S3]

/-- Half-plane region for the triangle `(0,0),(1,3),(1,4)`: inward normals for edges
`(0,0)-(1,3)`, `(1,3)-(1,4)`, `(1,4)-(0,0)`. -/
private def triangleS3 : Set (ℝ × ℝ) := {p : ℝ × ℝ | 3*p.1 ≤ p.2 ∧ p.1 ≤ 1 ∧ p.2 ≤ 4*p.1}

private theorem convex_triangleS3 : Convex ℝ triangleS3 := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [triangleS3, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hx1 ha, mul_le_mul_of_nonneg_left hy1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx2 ha, mul_le_mul_of_nonneg_left hy2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx3 ha, mul_le_mul_of_nonneg_left hy3 hb]

private theorem closed_triangleS3 : IsClosed triangleS3 := by
  have e1 : IsClosed {p : ℝ × ℝ | 3*p.1 ≤ p.2} := isClosed_le (by fun_prop) continuous_snd
  have e2 : IsClosed {p : ℝ × ℝ | p.1 ≤ 1} := isClosed_le continuous_fst continuous_const
  have e3 : IsClosed {p : ℝ × ℝ | p.2 ≤ 4*p.1} := isClosed_le continuous_snd (by fun_prop)
  have : triangleS3 = {p : ℝ × ℝ | 3*p.1 ≤ p.2} ∩ {p : ℝ × ℝ | p.1 ≤ 1} ∩
      {p : ℝ × ℝ | p.2 ≤ 4*p.1} := by
    ext p; simp [triangleS3, and_assoc]
  rw [this]
  exact (e1.inter e2).inter e3

theorem eq_preimage_triangleS3 : S3 = toReal ⁻¹' triangleS3 := by
  ext z
  rw [mem_S3_iff, Set.mem_preimage]
  simp only [triangleS3, Set.mem_ofPred_eq, toReal]
  constructor
  · rintro (rfl | rfl | rfl) <;> norm_num
  · rintro ⟨h1, h2, h3⟩
    have h1' : 3 * z.1 ≤ z.2 := by exact_mod_cast h1
    have h2' : z.1 ≤ 1 := by exact_mod_cast h2
    have h3' : z.2 ≤ 4 * z.1 := by exact_mod_cast h3
    have : z.1 = 0 ∧ z.2 = 0 ∨ z.1 = 1 ∧ z.2 = 3 ∨ z.1 = 1 ∧ z.2 = 4 := by omega
    rcases this with ⟨e1,e2⟩|⟨e1,e2⟩|⟨e1,e2⟩
    · left; exact Prod.ext e1 e2
    · right; left; exact Prod.ext e1 e2
    · right; right; exact Prod.ext e1 e2

/-- Bounded-enumeration confirmation of team-lead's hand Pick's-theorem computation: the
half-plane intersection `triangleS3` contains exactly the three named lattice points, no more
(this is the fact Pick's theorem was used, by hand, to predict — verified here directly by
case split instead of formalising Pick). -/
theorem isLatticeConvexRegion_S3 : IsLatticeConvexRegion S3 :=
  ⟨triangleS3, convex_triangleS3, closed_triangleS3, eq_preimage_triangleS3⟩

theorem det_S3_not_collinear :
    det (((1:ℤ),(3:ℤ)) - ((0:ℤ),(0:ℤ))) (((1:ℤ),(4:ℤ)) - ((0:ℤ),(0:ℤ))) = 1 := by
  simp [det]

theorem primitive_one_zero : Primitive ((1:ℤ), (0:ℤ)) := ⟨1, 0, by ring⟩

theorem not_levelInterval_S3 : ¬ Nivat.RegionSweep.LevelInterval S3 ((1:ℤ), (0:ℤ)) := by
  intro h
  obtain ⟨c, hc, hcm⟩ := h (0,0) (by rw [mem_S3_iff]; tauto) (1,4) (by rw [mem_S3_iff]; tauto) 1
    (by simp [det]) (by simp [det])
  rw [mem_S3_iff] at hc
  rcases hc with rfl|rfl|rfl <;> simp [det] at hcm

end TwoDGapWitness

/-! ### `wedgeFull` on any finite nonempty `B` is unconditionally a half-plane, no `hlev`

Generalises `mem_wedgeFull_S2_iff`/`isLatticeConvexRegion_wedgeFull_S2` above from the specific
witness `S2` to an arbitrary finite nonempty `B`.  This is the direct answer to team-lead's
2026-09-19 question about the `hbase`-wants-finite / `isRegion`-wants-`hlev` tension: whenever
`B` is finite (which `hcase1`'s natural witness `B := ↑d.Sphi` is), `wedgeFull B vl u'` is
*already* a half-plane, unconditionally, with **no `LevelInterval`/`hlev` hypothesis anywhere**
— `hlev` was only ever needed by the codebase's existing `isLatticeConvexRegion_fullSweep` route
through the *intermediate* `fullSweep` object, never by `wedgeFull` itself once the outer
`u'`-sweep is taken into account.

Proof shape is exactly `mem_wedgeFull_S2_iff` with `S2`'s two hand-checked facts (`0 ≤ det vl c`
for `c ∈ S2`, and the explicit `(0,0)` witness) replaced by their general finite-nonempty
analogues: `Set.Finite.exists_min_image` supplies the extremal `b₀ ∈ B` and the level bound
`L := det vl b₀`; `Nivat.eq_zsmul_of_det_eq_zero` (`Lattice/Primitive.lean:83`, needs only
`Primitive vl`) replaces the `Prod.ext`-by-hand parallel-vector argument. -/

section FiniteBHalfPlane

/-- **The general half-plane identity.** For finite nonempty `B`, primitive `vl`, and
`det vl u' = 1`, `wedgeFull B vl u'` is exactly `{z | L ≤ det vl z}` where `L` is the minimum
`vl`-level attained on `B`. No `LevelInterval B vl` hypothesis appears anywhere. -/
theorem wedgeFull_eq_halfPlane_of_det_eq_one {B : Set (ℤ × ℤ)} (hBfin : B.Finite)
    (hBne : B.Nonempty) {vl u' : ℤ × ℤ} (hvl : Primitive vl) (hvu : det vl u' = 1) :
    ∃ L : ℤ, Nivat.ColleReg.wedgeFull B vl u' = {z : ℤ × ℤ | L ≤ det vl z} := by
  obtain ⟨b0, hb0, hmin⟩ := Set.exists_min_image B (det vl) hBfin hBne
  refine ⟨det vl b0, ?_⟩
  ext z
  simp only [Set.mem_ofPred_eq]
  unfold Nivat.ColleReg.wedgeFull
  rw [Nivat.RegionSweep.mem_sweep]
  constructor
  · rintro ⟨g, hg, t, rfl⟩
    obtain ⟨c, hc, k, hck⟩ := Nivat.ColleReg.mem_fullSweep_iff.mp hg
    have hgl : det vl g = det vl c := by
      rw [hck]; exact Nivat.RegionSweep.det_add_zsmul_self _ _ _
    have hcb : det vl b0 ≤ det vl c := hmin c hc
    have hstep : det vl (g + (t : ℤ) • u') = det vl g + (t : ℤ) * det vl u' := by
      simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [hstep, hvu, hgl]
    have ht0 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    omega
  · intro hz
    set n : ℤ := det vl z - det vl b0 with hn
    have hnn : (0 : ℤ) ≤ n := by omega
    have hzero : det vl (z - b0 - n • u') = 0 := by
      have hexp : det vl (z - b0 - n • u') = det vl z - det vl b0 - n * det vl u' := by
        simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      rw [hexp, hvu]; omega
    obtain ⟨c, hc⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl hzero
    refine ⟨b0 + c • vl, Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨b0, hb0, c, rfl⟩, n.toNat, ?_⟩
    have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hnn
    have heq : z = b0 + c • vl + n • u' := by
      calc z = z - b0 - n • u' + (b0 + n • u') := by abel
      _ = c • vl + (b0 + n • u') := by rw [hc]
      _ = b0 + c • vl + n • u' := by abel
    rw [heq, hcast]

/-- **Unconditional lattice-convexity, no `hlev`.** Immediate corollary: for any finite nonempty
`B`, `IsLatticeConvexRegion (wedgeFull B vl u')` holds with only `Primitive vl` and
`det vl u' = 1` — the `LevelInterval B vl` hypothesis `ofWedge` currently carries is never used. -/
theorem isLatticeConvexRegion_wedgeFull_of_finite {B : Set (ℤ × ℤ)} (hBfin : B.Finite)
    (hBne : B.Nonempty) {vl u' : ℤ × ℤ} (hvl : Primitive vl) (hvu : det vl u' = 1) :
    IsLatticeConvexRegion (Nivat.ColleReg.wedgeFull B vl u') := by
  obtain ⟨L, hL⟩ := wedgeFull_eq_halfPlane_of_det_eq_one hBfin hBne hvl hvu
  rw [hL]
  refine ⟨{p : ℝ × ℝ | (L : ℝ) ≤ Nivat.RegionSweep.rlevel vl p},
    convex_halfSpace_ge (Nivat.RegionSweep.isLinearMap_rlevel _) _,
    isClosed_le continuous_const (Nivat.RegionSweep.continuous_rlevel _), ?_⟩
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Nivat.RegionSweep.rlevel_toReal]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- **Cost, in general: zero.** `latWedge`'s hull is a no-op whenever `B` is finite nonempty and
`det vl u' = 1`, because `wedgeFull B vl u'` is *already* closed and convex (a half-plane) by
`isLatticeConvexRegion_wedgeFull_of_finite` — `latWedge B vl u' = wedgeFull B vl u'` on the nose,
not just `⊇`. This is the general form of `latWedge_eq_wedgeFull_S2` above; `S2` was never a
special case, it was the generic behaviour. -/
theorem latWedge_eq_wedgeFull_of_finite {B : Set (ℤ × ℤ)} (hBfin : B.Finite)
    (hBne : B.Nonempty) {vl u' : ℤ × ℤ} (hvl : Primitive vl) (hvu : det vl u' = 1) :
    latWedge B vl u' = Nivat.ColleReg.wedgeFull B vl u' := by
  apply Set.Subset.antisymm _ (wedgeFull_subset_latWedge _ _ _)
  intro z hz
  by_contra hcon
  obtain ⟨C, hCconv, hCclosed, hCeq⟩ := isLatticeConvexRegion_wedgeFull_of_finite hBfin hBne hvl hvu
  have hzC : toReal z ∉ C := fun h => hcon (by rw [hCeq]; exact h)
  have hzhull : toReal z ∈ convHullOf (Nivat.ColleReg.wedgeFull B vl u') := by
    have := hz; unfold latWedge at this; exact this
  have hsub : convHullOf (Nivat.ColleReg.wedgeFull B vl u') ⊆ C := by
    apply closure_minimal _ hCclosed
    apply convexHull_min _ hCconv
    rintro _ ⟨w, hw, rfl⟩
    rw [hCeq] at hw; exact hw
  exact hzC (hsub hzhull)

end FiniteBHalfPlane

/-! ### `wedgeFull` is a half-plane under `hunimod` alone — no `B` hypothesis whatsoever

Team-lead's dispatch (2026-09-19, correcting `OPEN.md #12`): under `hunimod : det u' vl = ±1`,
`{vl, u'}` is a ℤ-basis (`Nivat.HbaseBridge.basis_expansion`), so `z ∈ wedgeFull B vl u'` reduces
to a **single linear inequality** `dot m b ≤ dot m z` for some `b ∈ B`, where `m := expNormal vl
u'` (`dot m u' = 1`, `dot m vl = 0` — `dot_expNormal_vl (det_swap hunimod)` / `dot_expNormal_u'`).
This subsumes `wedgeFull_eq_halfPlane_of_det_eq_one`/`isLatticeConvexRegion_wedgeFull_of_finite`
above (no finiteness of `B` needed at all — only that `{dot m b | b ∈ B}` has *some* structure:
empty, unbounded below, or bounded below with an attained minimum, and integers bounded below
always attain their minimum, finite or not).

We reuse `Nivat.RegionSweep.rlevel`/`isLinearMap_rlevel`/`continuous_rlevel` (already imported
via `RegionSweep`) rather than adding a `ConvTransport` import: `dot m z = det (m.2, -m.1) z`
turns any `dot m`-half-plane into an `rlevel`-half-plane for the auxiliary vector `(m.2, -m.1)`,
so no new convexity/continuity machinery is needed. -/

section UnimodHalfPlane

theorem det_perp_eq_dot (m z : ℤ × ℤ) : det (m.2, -m.1) z = dot m z := by
  simp only [det, dot]; ring

/-- **The general membership characterisation.** No hypothesis on `B` at all beyond the ambient
`hunimod`. -/
theorem mem_wedgeFull_iff_of_unimod {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (z : ℤ × ℤ) :
    z ∈ Nivat.ColleReg.wedgeFull B vl u' ↔
      ∃ b ∈ B, dot (Nivat.ColleReg.expNormal vl u') b ≤ dot (Nivat.ColleReg.expNormal vl u') z := by
  set m : ℤ × ℤ := Nivat.ColleReg.expNormal vl u' with hm
  have hmu' : dot m u' = 1 := Nivat.ColleReg.dot_expNormal_vl (Nivat.HbaseBridge.det_swap hunimod)
  have hmvl : dot m vl = 0 := Nivat.ColleReg.dot_expNormal_u'
  unfold Nivat.ColleReg.wedgeFull
  rw [Nivat.RegionSweep.mem_sweep]
  constructor
  · rintro ⟨g, hg, t, rfl⟩
    obtain ⟨b, hb, k, hgk⟩ := Nivat.ColleReg.mem_fullSweep_iff.mp hg
    refine ⟨b, hb, ?_⟩
    have hstep : dot m (g + (t : ℤ) • u') = dot m g + (t : ℤ) * dot m u' := by
      simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    have hmvl' : m.1 * vl.1 + m.2 * vl.2 = 0 := by simpa [dot] using hmvl
    have hgl : dot m g = dot m b := by
      rw [hgk]
      simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      linear_combination k * hmvl'
    rw [hstep, hmu', hgl, mul_one]
    have : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    omega
  · rintro ⟨b, hb, hble⟩
    set β : ℤ := dot m z - dot m b with hβ
    have hβnn : (0 : ℤ) ≤ β := by omega
    have hbasis := Nivat.HbaseBridge.basis_expansion hunimod (z - b)
    have hmzb : dot m (z - b) = β := by
      rw [hβ]; simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hmzb] at hbasis
    set s : ℤ := dot (Nivat.ColleReg.expNormal u' vl) (z - b) with hs
    refine ⟨b + s • vl, Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨b, hb, s, rfl⟩, β.toNat, ?_⟩
    have hcast : ((β.toNat : ℕ) : ℤ) = β := Int.toNat_of_nonneg hβnn
    have hdecomp : z - b = β • u' + s • vl := hbasis.symm
    rw [hcast]
    calc z = z - b + b := by abel
    _ = β • u' + s • vl + b := by rw [hdecomp]
    _ = b + s • vl + β • u' := by abel

/-- **Unconditional lattice-convexity — no hypothesis on `B` at all**, only `hunimod`.
`wedgeFull B vl u'` is `dot m ⁻¹' U` (`m := expNormal vl u'`) for the up-set
`U := {L | ∃ b ∈ B, dot m b ≤ L}`; the only up-sets of `ℤ` are `∅`, all of `ℤ`, or `[L₀, ∞)` for
an attained minimum `L₀` — the three cases below, none needing `B` finite, nonempty (beyond the
case split itself), or `LevelInterval`. This is the theorem that kills `hlev`: `ofWedge` can
replace it with `hunimod` alone. -/
theorem isLatticeConvexRegion_wedgeFull_of_unimod {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    IsLatticeConvexRegion (Nivat.ColleReg.wedgeFull B vl u') := by
  classical
  set m : ℤ × ℤ := Nivat.ColleReg.expNormal vl u' with hm
  by_cases hBe : B = ∅
  · subst hBe
    refine ⟨∅, convex_empty, isClosed_empty, ?_⟩
    ext z
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    intro hz
    rw [mem_wedgeFull_iff_of_unimod hunimod] at hz
    obtain ⟨b, hb, -⟩ := hz
    exact hb
  · obtain ⟨b0, hb0⟩ := Set.nonempty_iff_ne_empty.mpr hBe
    by_cases hbdd : ∃ L : ℤ, ∀ b ∈ B, L ≤ dot m b
    · obtain ⟨L, hL⟩ := hbdd
      obtain ⟨L0, ⟨b1, hb1, hb1eq⟩, hmin⟩ := Int.exists_least_of_bdd
        (P := fun L => ∃ b ∈ B, dot m b = L)
        ⟨L, fun z ⟨b, hb, hbeq⟩ => hbeq ▸ hL b hb⟩
        ⟨dot m b0, b0, hb0, rfl⟩
      refine ⟨{p : ℝ × ℝ | (L0 : ℝ) ≤ Nivat.RegionSweep.rlevel (m.2, -m.1) p},
        convex_halfSpace_ge (Nivat.RegionSweep.isLinearMap_rlevel _) _,
        isClosed_le continuous_const (Nivat.RegionSweep.continuous_rlevel _), ?_⟩
      ext z
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Nivat.RegionSweep.rlevel_toReal,
        det_perp_eq_dot]
      rw [mem_wedgeFull_iff_of_unimod hunimod]
      constructor
      · rintro ⟨b, hb, hble⟩
        have hL0b : L0 ≤ dot m b := hmin _ ⟨b, hb, rfl⟩
        exact_mod_cast hL0b.trans hble
      · intro hz
        refine ⟨b1, hb1, ?_⟩
        rw [hb1eq]
        exact_mod_cast hz
    · push Not at hbdd
      refine ⟨Set.univ, convex_univ, isClosed_univ, ?_⟩
      rw [Set.preimage_univ]
      ext z
      simp only [Set.mem_univ, iff_true]
      rw [mem_wedgeFull_iff_of_unimod hunimod]
      obtain ⟨b, hb, hblt⟩ := hbdd (dot m z)
      exact ⟨b, hb, le_of_lt hblt⟩

/-- **`latWedge` collapses to `wedgeFull` unconditionally.** Cost zero for every `B`, not just
finite `B`: since `wedgeFull B vl u'` is already closed and convex, its lattice hull is a no-op. -/
theorem latWedge_eq_wedgeFull_of_unimod {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    latWedge B vl u' = Nivat.ColleReg.wedgeFull B vl u' := by
  apply Set.Subset.antisymm _ (wedgeFull_subset_latWedge _ _ _)
  intro z hz
  by_contra hcon
  obtain ⟨C, hCconv, hCclosed, hCeq⟩ := isLatticeConvexRegion_wedgeFull_of_unimod (B := B) hunimod
  have hzC : toReal z ∉ C := fun h => hcon (by rw [hCeq]; exact h)
  have hzhull : toReal z ∈ convHullOf (Nivat.ColleReg.wedgeFull B vl u') := by
    have := hz; unfold latWedge at this; exact this
  have hsub : convHullOf (Nivat.ColleReg.wedgeFull B vl u') ⊆ C := by
    apply closure_minimal _ hCclosed
    apply convexHull_min _ hCconv
    rintro _ ⟨w, hw, rfl⟩
    rw [hCeq] at hw; exact hw
  exact hzC (hsub hzhull)

/-- **`S2`'s theorem is a one-line corollary of the general one**, confirming team-lead's
prediction: nothing about `S2` was special. -/
theorem isLatticeConvexRegion_wedgeFull_S2' :
    IsLatticeConvexRegion (Nivat.ColleReg.wedgeFull S2 ((1:ℤ),(-1:ℤ)) ((1:ℤ),(0:ℤ))) :=
  isLatticeConvexRegion_wedgeFull_of_unimod (Or.inr (by simp [det]))

end UnimodHalfPlane

/-! ### Team-lead's three follow-ups (2026-09-19, post-freeze): the `-1` mirror, a named
`hunimod`-alone wrapper, and the quadrant corollary for `chainFull`.

**(a) The mirror.** Cclaim's `Route A` (`L1Claim.lean`) feeds `hconv : IsLatticeConvexRegion
(wedgeFull B vl u')` directly, sourced from `isLatticeConvexRegion_wedgeFull_of_finite`
(`FiniteBHalfPlane` above), which only handles `det vl u' = 1`. `wedgeFull_eq_halfPlane_of_det_eq_neg_one`
below is the missing `det vl u' = -1` case at that *same* narrow (finite-`B`, `det`-based)
granularity — a max-level half-plane `{z | det vl z ≤ L}` instead of a min-level one.
**Already covered at the general level**: `isLatticeConvexRegion_wedgeFull_of_unimod`
(`UnimodHalfPlane` above) takes the full `hunimod : det u' vl = 1 ∨ det u' vl = -1` disjunct
uniformly with no internal case split and no `B` hypothesis at all, so the mirror closes a real
but narrow gap — the concrete `det`-indexed half-plane identity, not the lattice-convexity
conclusion itself, which was never one-sided.

**(b) The named wrapper.** `isLatticeConvexRegion_wedgeFull_of_unimod'` is requested taking
`hunimod` and "whatever `B` hypothesis you actually need (if none, say so)". **None** — the
already-landed `isLatticeConvexRegion_wedgeFull_of_unimod` needs no hypothesis on `B` whatsoever
(not finiteness, not nonemptiness); this is a byte-for-byte alias under the requested name,
confirming that is already the strongest form.

**(c) The quadrant corollary.** `chainFull B vl u' b₀ 0` unfolds definitionally (`cut`/`expLevel`
at `n = 0`) to `wedgeFull B vl u' ∩ halfPlaneGE (expNormal u' vl) (dot (expNormal u' vl) b₀)`
(`chainFull_zero_eq_inter`, no hypotheses at all). Combined with the half-plane characterisation
of `wedgeFull` itself (`mem_wedgeFull_iff_of_unimod`) under `hunimod` plus `b₀`
`expNormal vl u'`-minimal in `B`, the first factor becomes a second `halfPlaneGE` with normal
`expNormal vl u'` — the dual basis vector to `expNormal u' vl` — so the whole set is an
intersection of two half-planes with dual-basis normals, i.e. a quadrant in `(u', vl)`
coordinates (`chainFull_zero_eq_quadrant_of_unimod`). -/

section ChainQuadrant

/-- **(a) The `det vl u' = -1` mirror** of `wedgeFull_eq_halfPlane_of_det_eq_one`: a max-level
half-plane instead of a min-level one. Same finite-`B` granularity as the theorem it mirrors;
subsumed at the lattice-convexity level by `isLatticeConvexRegion_wedgeFull_of_unimod`. -/
theorem wedgeFull_eq_halfPlane_of_det_eq_neg_one {B : Set (ℤ × ℤ)} (hBfin : B.Finite)
    (hBne : B.Nonempty) {vl u' : ℤ × ℤ} (hvl : Primitive vl) (hvu : det vl u' = -1) :
    ∃ L : ℤ, Nivat.ColleReg.wedgeFull B vl u' = {z : ℤ × ℤ | det vl z ≤ L} := by
  obtain ⟨b0, hb0, hmin⟩ := Set.exists_min_image B (fun z => -det vl z) hBfin hBne
  refine ⟨det vl b0, ?_⟩
  ext z
  simp only [Set.mem_ofPred_eq]
  unfold Nivat.ColleReg.wedgeFull
  rw [Nivat.RegionSweep.mem_sweep]
  constructor
  · rintro ⟨g, hg, t, rfl⟩
    obtain ⟨c, hc, k, hck⟩ := Nivat.ColleReg.mem_fullSweep_iff.mp hg
    have hgl : det vl g = det vl c := by
      rw [hck]; exact Nivat.RegionSweep.det_add_zsmul_self _ _ _
    have hcb : det vl c ≤ det vl b0 := by have := hmin c hc; omega
    have hstep : det vl (g + (t : ℤ) • u') = det vl g + (t : ℤ) * det vl u' := by
      simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [hstep, hvu, hgl]
    have ht0 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    omega
  · intro hz
    set n : ℤ := det vl b0 - det vl z with hn
    have hnn : (0 : ℤ) ≤ n := by omega
    have hzero : det vl (z - b0 - n • u') = 0 := by
      have hexp : det vl (z - b0 - n • u') = det vl z - det vl b0 - n * det vl u' := by
        simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      rw [hexp, hvu]; omega
    obtain ⟨c, hc⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl hzero
    refine ⟨b0 + c • vl, Nivat.ColleReg.mem_fullSweep_iff.mpr ⟨b0, hb0, c, rfl⟩, n.toNat, ?_⟩
    have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hnn
    have heq : z = b0 + c • vl + n • u' := by
      calc z = z - b0 - n • u' + (b0 + n • u') := by abel
      _ = c • vl + (b0 + n • u') := by rw [hc]
      _ = b0 + c • vl + n • u' := by abel
    rw [heq, hcast]

/-- **(b) The requested `hunimod`-alone wrapper, exact name.** No `B` hypothesis of any kind —
alias of `isLatticeConvexRegion_wedgeFull_of_unimod`, which is already the strongest form. -/
theorem isLatticeConvexRegion_wedgeFull_of_unimod' {B : Set (ℤ × ℤ)} {vl u' : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    IsLatticeConvexRegion (Nivat.ColleReg.wedgeFull B vl u') :=
  isLatticeConvexRegion_wedgeFull_of_unimod hunimod

/-- **(c), step 1: the definitional quadrant unfolding**, no hypotheses. -/
theorem chainFull_zero_eq_inter (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) :
    Nivat.ColleReg.chainFull B vl u' b₀ 0 =
      Nivat.ColleReg.wedgeFull B vl u' ∩
        halfPlaneGE (Nivat.ColleReg.expNormal u' vl)
          (dot (Nivat.ColleReg.expNormal u' vl) b₀) := by
  have hlev : Nivat.ColleReg.expLevel u' vl b₀ 0 = dot (Nivat.ColleReg.expNormal u' vl) b₀ := by
    unfold Nivat.ColleReg.expLevel; simp
  unfold Nivat.ColleReg.chainFull Nivat.L1Region.cut
  rw [hlev]

/-- **(c), step 2: the quadrant corollary.** Under `hunimod` and `b₀` chosen
`expNormal vl u'`-minimal in `B`, `chainFull B vl u' b₀ 0` is the intersection of two
half-planes whose normals are the dual basis `expNormal vl u'`, `expNormal u' vl` of `(u', vl)`
— a quadrant in those coordinates. -/
theorem chainFull_zero_eq_quadrant_of_unimod {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hb₀ : b₀ ∈ B)
    (hmin : ∀ b ∈ B, dot (Nivat.ColleReg.expNormal vl u') b₀ ≤
        dot (Nivat.ColleReg.expNormal vl u') b) :
    Nivat.ColleReg.chainFull B vl u' b₀ 0 =
      halfPlaneGE (Nivat.ColleReg.expNormal vl u') (dot (Nivat.ColleReg.expNormal vl u') b₀) ∩
        halfPlaneGE (Nivat.ColleReg.expNormal u' vl)
          (dot (Nivat.ColleReg.expNormal u' vl) b₀) := by
  rw [chainFull_zero_eq_inter]
  congr 1
  ext z
  simp only [halfPlaneGE, Set.mem_ofPred_eq]
  rw [mem_wedgeFull_iff_of_unimod hunimod]
  constructor
  · rintro ⟨b, hb, hble⟩
    exact (hmin b hb).trans hble
  · intro hz
    exact ⟨b₀, hb₀, hz⟩

/-- **`hmin` is unconditionally selectable for finite nonempty `B`** — same mechanism
`HbaseBridge.lean:1626` already uses inside a different proof (`B.exists_min_image (fun b =>
dot (expNormal vl u') b) hBne`), exposed here as a standalone existence fact so
`chainFull_zero_eq_quadrant_of_unimod`'s two side conditions (`hb₀`, `hmin`) are jointly
satisfiable by *some* `b₀ ∈ B` whenever `B` is finite nonempty. -/
theorem exists_expNormal_vl_u'_min {B : Finset (ℤ × ℤ)} (hBne : B.Nonempty) (vl u' : ℤ × ℤ) :
    ∃ b₀ ∈ B, ∀ b ∈ B, dot (Nivat.ColleReg.expNormal vl u') b₀ ≤
      dot (Nivat.ColleReg.expNormal vl u') b :=
  B.exists_min_image (fun b => dot (Nivat.ColleReg.expNormal vl u') b) hBne

end ChainQuadrant

end Nivat.ColleReg.L1Data
