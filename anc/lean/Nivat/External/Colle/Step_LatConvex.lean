/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.ExternalDefs
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.LatticeEdges

/-!
# Edge structure does not imply convexity: the `bad h` witness

`bad h = ([0,2] × [0,h]) \ {(1,1)}` has exactly the edge normals of the unit square,
`E (bad h) = E sq1` (`E_bad`), and is **not** lattice-convex: `(1,1)` is the midpoint of
`(0,0)` and `(2,2)`, both of which it contains (`not_isLatticeConvexRegion_bad`).

That pair is the whole content of this file, and it is kernel-checked.  It says something
worth saying: **convexity is not derivable from edge structure**, which is precisely why
Colle's Definition 3.2 states it separately (`scratch/b3_colle2.txt`; the term "convex set"
is defined in the running text, not in a `Definition` environment — see `CLAUDE.md`).

## History, and a retracted claim

This file was originally written to refute `Nivat.ColleReg.region_latticeConvex`, and its
header asserted that theorem was false.  **That claim is retracted.**  It depended on
`Enveloped` not carrying convexity — a weakening of Definition 3.2 that this project
introduced and later repaired in `ea5bbc5`.  Under the repaired definition `bad h` is not
enveloped at all (`not_enveloped_bad` below), so it never met the hypothesis it was
supposed to refute.  The refutation machinery built on top of it — `enveloped_bad`,
`enveloped_not_latticeConvex`, `badChain`, `not_region_latticeConvex` — was withdrawn on
2026-09-16; see the note at §2-§3.

The header also claimed "No `sorry`, no new axiom" while `enveloped_bad` carried a `sorry`
two hundred lines below.  Both halves of that sentence are now true, but they were not
then, and the status line had been hand-written rather than generated from build output.

## Status

Generated from build output 2026-09-16: this file has no `sorry`.  Its results depend only
on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Nivat.ColleStep

open Nivat Nivat.LE2

/-! ## §1.  The counterexample set `bad h = ([0,2] × [0,h]) \ {(1,1)}` -/

/-- The defining predicate of `bad h`, kept separate so that it is decidable and can be
used in an `if` inside a configuration. -/
def badP (h : ℤ) (z : ℤ × ℤ) : Prop :=
  0 ≤ z.1 ∧ z.1 ≤ 2 ∧ 0 ≤ z.2 ∧ z.2 ≤ h ∧ z ≠ (1, 1)

instance instDecidableBadP (h : ℤ) (z : ℤ × ℤ) : Decidable (badP h z) := by
  unfold badP; infer_instance

/-- `bad h = ([0,2] × [0,h]) \ {(1,1)}`, for `h ≥ 2` a lattice box with an interior point
removed. -/
def bad (h : ℤ) : Set (ℤ × ℤ) := {z | badP h z}

theorem mem_bad {h : ℤ} {z : ℤ × ℤ} :
    z ∈ bad h ↔ 0 ≤ z.1 ∧ z.1 ≤ 2 ∧ 0 ≤ z.2 ∧ z.2 ≤ h ∧ z ≠ (1, 1) := Iff.rfl

/-- In a direction that is not axis-parallel, `bad h` exposes a single corner of the
ambient box: the deleted point `(1,1)` is never a corner, because `h ≥ 2`. -/
theorem face_bad_of_ne_zero {h : ℤ} (hh : 2 ≤ h) {n : ℤ × ℤ} (h1 : n.1 ≠ 0) (h2 : n.2 ≠ 0) :
    face (bad h) n = {(endp n.1 0 2, endp n.2 0 h)} := by
  have hx : endp n.1 0 2 ≠ 1 := by unfold endp; split <;> omega
  have hC : (endp n.1 0 2, endp n.2 0 h) ∈ bad h := by
    rw [mem_bad]
    refine ⟨(endp_mem (by norm_num)).1, (endp_mem (by norm_num)).2,
      (endp_mem (by omega)).1, (endp_mem (by omega)).2, ?_⟩
    intro hEq
    rw [Prod.ext_iff] at hEq
    exact hx hEq.1
  have hmax : ∀ z ∈ bad h, dot n z ≤ dot n (endp n.1 0 2, endp n.2 0 h) := by
    intro z hz
    obtain ⟨a1, a2, a3, a4, -⟩ := mem_bad.mp hz
    simp only [dot]
    exact add_le_add (mul_le_endp n.1 a1 a2) (mul_le_endp n.2 a3 a4)
  ext z
  constructor
  · rintro ⟨hz, hzm⟩
    have hle := hmax z hz
    have hge := hzm _ hC
    obtain ⟨a1, a2, a3, a4, -⟩ := mem_bad.mp hz
    have e1 := mul_le_endp n.1 a1 a2
    have e2 := mul_le_endp n.2 a3 a4
    simp only [dot] at hle hge
    have f1 : n.1 * z.1 = n.1 * endp n.1 0 2 := by linarith
    have f2 : n.2 * z.2 = n.2 * endp n.2 0 h := by linarith
    exact Prod.ext (mul_left_cancel₀ h1 f1) (mul_left_cancel₀ h2 f2)
  · rintro rfl
    exact ⟨hC, hmax⟩

theorem mem_face_bad_right {h : ℤ} {z : ℤ × ℤ} (hz : z ∈ bad h) (hz2 : z.1 = 2) :
    z ∈ face (bad h) (1, 0) := by
  refine ⟨hz, fun y hy => ?_⟩
  have := (mem_bad.mp hy).2.1
  simp only [dot_e1]
  omega

theorem mem_face_bad_left {h : ℤ} {z : ℤ × ℤ} (hz : z ∈ bad h) (hz2 : z.1 = 0) :
    z ∈ face (bad h) (-1, 0) := by
  refine ⟨hz, fun y hy => ?_⟩
  have := (mem_bad.mp hy).1
  simp only [dot_e1']
  omega

theorem mem_face_bad_top {h : ℤ} {z : ℤ × ℤ} (hz : z ∈ bad h) (hz2 : z.2 = h) :
    z ∈ face (bad h) (0, 1) := by
  refine ⟨hz, fun y hy => ?_⟩
  have := (mem_bad.mp hy).2.2.2.1
  simp only [dot_e2]
  omega

theorem mem_face_bad_bot {h : ℤ} {z : ℤ × ℤ} (hz : z ∈ bad h) (hz2 : z.2 = 0) :
    z ∈ face (bad h) (0, -1) := by
  refine ⟨hz, fun y hy => ?_⟩
  have := (mem_bad.mp hy).2.2.1
  simp only [dot_e2']
  omega

theorem mem_bad_20 {h : ℤ} (hh : 2 ≤ h) : ((2 : ℤ), (0 : ℤ)) ∈ bad h := by
  rw [mem_bad]; refine ⟨by norm_num, by norm_num, by norm_num, by omega, by decide⟩

theorem mem_bad_21 {h : ℤ} (hh : 2 ≤ h) : ((2 : ℤ), (1 : ℤ)) ∈ bad h := by
  rw [mem_bad]; refine ⟨by norm_num, by norm_num, by norm_num, by omega, by decide⟩

theorem mem_bad_00 {h : ℤ} (hh : 2 ≤ h) : ((0 : ℤ), (0 : ℤ)) ∈ bad h := by
  rw [mem_bad]; refine ⟨by norm_num, by norm_num, by norm_num, by omega, by decide⟩

theorem mem_bad_01 {h : ℤ} (hh : 2 ≤ h) : ((0 : ℤ), (1 : ℤ)) ∈ bad h := by
  rw [mem_bad]; refine ⟨by norm_num, by norm_num, by norm_num, by omega, by decide⟩

theorem mem_bad_0h {h : ℤ} (hh : 2 ≤ h) : ((0 : ℤ), h) ∈ bad h := by
  rw [mem_bad]
  refine ⟨by norm_num, by norm_num, by omega, le_refl _, ?_⟩
  intro hEq; rw [Prod.ext_iff] at hEq; exact absurd hEq.1 (by norm_num)

theorem mem_bad_2h {h : ℤ} (hh : 2 ≤ h) : ((2 : ℤ), h) ∈ bad h := by
  rw [mem_bad]
  refine ⟨by norm_num, by norm_num, by omega, le_refl _, ?_⟩
  intro hEq; rw [Prod.ext_iff] at hEq; exact absurd hEq.1 (by norm_num)

/-- **`bad h` has exactly the four axis edge normals** — the same edge set as any box. -/
theorem E_bad {h : ℤ} (hh : 2 ≤ h) : E (bad h) = {(1, 0), (-1, 0), (0, 1), (0, -1)} := by
  ext n
  constructor
  · rintro ⟨hprim, hnt⟩
    by_cases h1 : n.1 = 0
    · rcases prim_eq_of_fst_eq_zero hprim h1 with rfl | rfl <;> simp
    · by_cases h2 : n.2 = 0
      · rcases prim_eq_of_snd_eq_zero hprim h2 with rfl | rfl <;> simp
      · exfalso
        rw [face_bad_of_ne_zero hh h1 h2] at hnt
        exact Set.not_nontrivial_singleton hnt
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨by decide, ⟨_, mem_face_bad_right (mem_bad_20 hh) rfl, _,
        mem_face_bad_right (mem_bad_21 hh) rfl, by decide⟩⟩
    · exact ⟨by decide, ⟨_, mem_face_bad_left (mem_bad_00 hh) rfl, _,
        mem_face_bad_left (mem_bad_01 hh) rfl, by decide⟩⟩
    · refine ⟨by decide, ⟨_, mem_face_bad_top (mem_bad_0h hh) rfl, _,
        mem_face_bad_top (mem_bad_2h hh) rfl, ?_⟩⟩
      intro hEq; rw [Prod.ext_iff] at hEq; exact absurd hEq.1 (by norm_num)
    · exact ⟨by decide, ⟨_, mem_face_bad_bot (mem_bad_00 hh) rfl, _,
        mem_face_bad_bot (mem_bad_20 hh) rfl, by decide⟩⟩


theorem mem_bad_22 {h : ℤ} (hh : 2 ≤ h) : ((2 : ℤ), (2 : ℤ)) ∈ bad h := by
  rw [mem_bad]; refine ⟨by norm_num, by norm_num, by norm_num, by omega, by decide⟩

/-- `bad h` is **not** lattice-convex: `(1,1)` is the midpoint of `(0,0)` and `(2,2)`. -/
theorem not_isLatticeConvexRegion_bad {h : ℤ} (hh : 2 ≤ h) :
    ¬ IsLatticeConvexRegion (bad h) := by
  rintro ⟨C, hconv, -, heq⟩
  have h00 : toReal ((0 : ℤ), (0 : ℤ)) ∈ C := by
    have hm := mem_bad_00 hh; rw [heq] at hm; exact hm
  have h22 : toReal ((2 : ℤ), (2 : ℤ)) ∈ C := by
    have hm := mem_bad_22 hh; rw [heq] at hm; exact hm
  have hmid : toReal ((1 : ℤ), (1 : ℤ)) ∈ C := by
    have hA : ((1 : ℝ) / 2) • toReal ((0 : ℤ), (0 : ℤ))
        + ((1 : ℝ) / 2) • toReal ((2 : ℤ), (2 : ℤ)) ∈ C :=
      hconv h00 h22 (by norm_num) (by norm_num) (by norm_num)
    have hAeq : ((1 : ℝ) / 2) • toReal ((0 : ℤ), (0 : ℤ))
        + ((1 : ℝ) / 2) • toReal ((2 : ℤ), (2 : ℤ)) = toReal ((1 : ℤ), (1 : ℤ)) := by
      simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
      norm_num
    rwa [hAeq] at hA
  have hmem : ((1 : ℤ), (1 : ℤ)) ∈ bad h := by rw [heq]; exact hmid
  exact (mem_bad.mp hmem).2.2.2.2 rfl

/-- **`bad h` is not `E(sq1)`-enveloped.**

This is the corrected form of a theorem `enveloped_bad` that stood here until
2026-09-16 and asserted the *opposite*, `Enveloped sq1 (bad h)`, with its convexity
obligation left `sorry`.  That obligation could never have been discharged: `Enveloped`
carries `IsLatticeConvexRegion` through `WeaklyEnveloped` (`LatticeEdges.lean:624-629`,
projection at `:634`), and `not_isLatticeConvexRegion_bad` above refutes exactly that. -/
theorem not_enveloped_bad {h : ℤ} (hh : 2 ≤ h) : ¬ Enveloped sq1 (bad h) :=
  fun e => not_isLatticeConvexRegion_bad hh e.1.1

/-! ## §2-§3.  Withdrawn 2026-09-16

Three further results stood here and were withdrawn together with `enveloped_bad`, on
which all three depended:

* `enveloped_not_latticeConvex : ¬ ∀ T, Enveloped sq1 T → IsLatticeConvexRegion T`.
  **Now false.**  Once `WeaklyEnveloped` carries convexity, that universal statement is
  true by projection (`LatticeEdges.lean:634`), so its negation cannot hold.  `bad 2`
  refutes it only in the convexity-free reading of Definition 3.2 that this project used
  before `ea5bbc5`, and that reading is not Colle's — see `CLAUDE.md`, "定义债".
* `badChain : ChainData badXi badXper badVl lcWin badGen`, whose `envB`, `envA` and
  `shellEnv` fields were supplied by `enveloped_bad`.  With `bad h` non-convex there is
  no envelope certificate to put in their place.
* `not_region_latticeConvex`, which refuted `region_latticeConvex` *in its pre-2026-09-16
  signature*, before `hξ : IsMinimalCounterexample ξ` was restored to it.  It reached that
  conclusion through `badChain`, hence through `enveloped_bad`, so it was never a
  sorry-free result.

What survives here is the part that was always sound and is kernel-checked: `bad h` has
the edge structure `E (bad h) = E sq1` (`E_bad`) and is nevertheless not lattice-convex
(`not_isLatticeConvexRegion_bad`).  That pair is the real content — edge structure alone
does not imply convexity, which is precisely why Definition 3.2 states convexity
separately. -/


end Nivat.ColleStep
