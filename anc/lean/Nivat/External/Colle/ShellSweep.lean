/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellMink
import Nivat.External.Colle.RegionEdges
import Nivat.External.Colle.Lemma41

/-!
# The `:518` double-sweep intersection, in the paper's own geometry

`b3_colle2.txt:518`, verbatim:

> `Â_i^{(ε)} := { g − t·v_{ℓ_{J+1}} ∈ Â_∞^{(ε)} : g ∈ Â_i, t ∈ ℤ_+ }`

and the paper asserts (`:520`) that for `ε` fixed and `i` large this is an
`E(𝒮_φ)`-enveloped set.  `LEAF-A.md` records the object as dead
(`tmp/shell518_symmetry.lean`: the intersection acquires an edge normal `(-1,-1)` whose
opposite `(1,1)` is a one-point corner, so it cannot be enveloped by anything with a
symmetric edge set).  **That refutation is computed on data the paper does not allow**: its
`Â_i = [0,i]²` has the four axis edge directions, while the ambient sweep runs along
`v_{ℓ_{J-1}} = (1,-1)`, which is not an edge direction of the square window.  Collé's
`v_{ℓ_{J-1}}` is by definition parallel to an edge of `𝒮_φ` (`:426`), so the window whose
shell is being swept diagonally must be a hexagon, not a square.

This file redoes the computation on consistent `m = 3` data and finds the opposite verdict:

* `hexShape a b c d e := {0 ≤ x ≤ a, -e ≤ y ≤ b, -c ≤ x - y ≤ d}` is the general shape of
  "hexagon swept along `(-1,-1)` and cut by `x ≥ 0`, `y ≥ -e`".  `E_hexShape` computes its
  edge set: exactly the six normals `±(1,0), ±(0,1), ±(1,-1)`, under six explicit
  nondegeneracy inequalities (one per edge).  `enveloped_hexShape` then gives
  `Enveloped U (hexShape …)` for any `U` with that edge set and at most two lattice points
  per edge — e.g. the unit hexagon `ShellMink.hexA`.
* §2 instantiates: `Ai i := hexShape (2i) (2i) i i 0`, `Â_∞ := quad` (an
  `(ℓ_{J-1}, ℓ_J)`-region for the hexagon fan, `ℓ_{J-1} ∥ (0,-1)`, `ℓ_J ∥ (1,0)`),
  `Â_∞^{(ε)} = MaxEnv.shell quad (0,-1) (0,1) 0 ε`, sweep direction `-v_{ℓ_{J+1}} = (-1,-1)`.
  `shell518_eq_hexShape` unwinds `ShellMink.shellInter` to `hexShape (2i) (2i) i i ε`, and
  `enveloped_shell518_hexA` concludes `Enveloped hexA (shellInter (Ai i) (Â_∞^{(ε)}) (-1,-1))`
  for every `ε` and every `i ≥ ε + 1` — the `shellEnv` shape (`Lemma35.lean:748`), with
  `i₀ := ε + 1`.

## What this does and does not say

* It withdraws the `:518` leg of "all four sweep encodings are dead" (`LEAF-A.md`): the
  literal `:518` object is enveloped in the paper's geometry, at every thickness.
* It says nothing about `Env := EnvOf d.Sphi` for a general `𝒮_φ`, nor about the other
  `ChainData` fields on a real bundle; it is a shape computation at one window.
* Chain: the only `sorry` any of this can reach is `exists_chainData`
  (`RegionSteps.lean`), which is the sole producer of `ChainData.shellEnv`; no producer
  module exists yet, so this file has no consumer on arrival (PROTOCOL §20, stated up front).
-/

set_option autoImplicit false

namespace Nivat.ShellSweep

open Nivat Nivat.LE2 Nivat.MaxEnv

/-! ## §0. Two helpers -/

/-- A primitive vector with `n.1 = -n.2` is `(1,-1)` or `(-1,1)`
(the missing sibling of `prim_eq_of_coord_eq`). -/
theorem prim_eq_of_coord_eq_neg {n : ℤ × ℤ} (hp : Prim n) (h : n.1 = -n.2) :
    n = (1, -1) ∨ n = (-1, 1) := by
  have : n.2.natAbs = 1 := by
    have := hp; rw [Prim, h, Int.neg_gcd] at this; simpa using this
  rcases Int.natAbs_eq_iff.mp this with h1 | h1
  · right; exact Prod.ext (by rw [h, h1]; rfl) (by simpa using h1)
  · left; exact Prod.ext (by rw [h, h1]; rfl) (by simpa using h1)

/-- **A face in the open cone of two adjacent constraint normals is a single vertex.**
If `⟪n,·⟫ = α⟪m₁,·⟫ + β⟪m₂,·⟫` with `α, β > 0`, both constraints `⟪mᵢ,·⟫ ≤ cᵢ` hold on `R`,
and `v ∈ R` is tight for both, then `face R n ⊆ {v}`. -/
theorem face_subset_singleton_of_cone {R : Set (ℤ × ℤ)} {n m₁ m₂ v : ℤ × ℤ} {α β c₁ c₂ : ℤ}
    (hα : 0 < α) (hβ : 0 < β)
    (hn : ∀ z, dot n z = α * dot m₁ z + β * dot m₂ z) (hD : det m₁ m₂ ≠ 0)
    (h₁ : ∀ z ∈ R, dot m₁ z ≤ c₁) (h₂ : ∀ z ∈ R, dot m₂ z ≤ c₂)
    (hv : v ∈ R) (hv₁ : dot m₁ v = c₁) (hv₂ : dot m₂ v = c₂) :
    face R n ⊆ {v} := by
  intro z hz
  have hle : dot n v ≤ dot n z := hz.2 v hv
  have hA : 0 ≤ α * (c₁ - dot m₁ z) := mul_nonneg hα.le (by linarith [h₁ z hz.1])
  have hB : 0 ≤ β * (c₂ - dot m₂ z) := mul_nonneg hβ.le (by linarith [h₂ z hz.1])
  have hsum : α * (c₁ - dot m₁ z) + β * (c₂ - dot m₂ z) ≤ 0 := by
    rw [hn v, hn z, hv₁, hv₂] at hle; linarith
  have e₁ : dot m₁ z = c₁ := by
    have : α * (c₁ - dot m₁ z) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hα.ne'
    · linarith
  have e₂ : dot m₂ z = c₂ := by
    have : β * (c₂ - dot m₂ z) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hβ.ne'
    · linarith
  exact eq_of_dot_eq_dot hD (e₁.trans hv₁.symm) (e₂.trans hv₂.symm)

/-! ## §1. The hexagon `{0 ≤ x ≤ a, -e ≤ y ≤ b, -c ≤ x - y ≤ d}` -/

/-- The shape of "hexagon swept along `(-1,-1)`, cut by `x ≥ 0` and `y ≥ -e`".  Vertices
`(0,-e), (d-e,-e), (a,a-d), (a,b), (b-c,b), (0,c)` in counterclockwise order. -/
def hexShape (a b c d e : ℤ) : Set (ℤ × ℤ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ a ∧ -e ≤ z.2 ∧ z.2 ≤ b ∧ -c ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ d}

/-- The six outer edge normals of a nondegenerate `hexShape`. -/
def hexE : Set (ℤ × ℤ) :=
  {((1 : ℤ), (0 : ℤ)), ((-1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((0 : ℤ), (-1 : ℤ)),
    ((1 : ℤ), (-1 : ℤ)), ((-1 : ℤ), (1 : ℤ))}

theorem mem_hexShape {a b c d e : ℤ} {z : ℤ × ℤ} :
    z ∈ hexShape a b c d e ↔
      0 ≤ z.1 ∧ z.1 ≤ a ∧ -e ≤ z.2 ∧ z.2 ≤ b ∧ -c ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ d := Iff.rfl

/-- **Nondegeneracy**: every edge carries at least two lattice points.  In vertex order:
bottom `d - e ≥ 1`, lower-right `a - d + e ≥ 1`, right `b - a + d ≥ 1`, top `a - b + c ≥ 1`,
upper-left `b - c ≥ 1`, left `c + e ≥ 1`. -/
structure Nondeg (a b c d e : ℤ) : Prop where
  bot : 1 ≤ d - e
  lr : 1 ≤ a - d + e
  right : 1 ≤ b - a + d
  top : 1 ≤ a - b + c
  ul : 1 ≤ b - c
  left : 1 ≤ c + e

section Faces

variable {a b c d e : ℤ} (h : Nondeg a b c d e)
include h

/-- Each of the six normals has two distinct lattice points on its face. -/
theorem face_pair_hexShape (n : ℤ × ℤ) (hn : n ∈ hexE) :
    ∃ z ∈ face (hexShape a b c d e) n, ∃ z' ∈ face (hexShape a b c d e) n, z ≠ z' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [hexE, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨(a, a - d), ⟨?_, ?_⟩, (a, b), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_hexShape]; omega
    · intro y hy; simp only [mem_hexShape] at hy; simp only [dot]; omega
    · simp only [mem_hexShape]; omega
    · intro y hy; simp only [mem_hexShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega
  · refine ⟨(0, -e), ⟨?_, ?_⟩, (0, c), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_hexShape]; omega
    · intro y hy; simp only [mem_hexShape] at hy; simp only [dot]; omega
    · simp only [mem_hexShape]; omega
    · intro y hy; simp only [mem_hexShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega
  · refine ⟨(a, b), ⟨?_, ?_⟩, (b - c, b), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_hexShape]; omega
    · intro y hy; simp only [mem_hexShape] at hy; simp only [dot]; omega
    · simp only [mem_hexShape]; omega
    · intro y hy; simp only [mem_hexShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega
  · refine ⟨(0, -e), ⟨?_, ?_⟩, (d - e, -e), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_hexShape]; omega
    · intro y hy; simp only [mem_hexShape] at hy; simp only [dot]; omega
    · simp only [mem_hexShape]; omega
    · intro y hy; simp only [mem_hexShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega
  · refine ⟨(d - e, -e), ⟨?_, ?_⟩, (a, a - d), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_hexShape]; omega
    · intro y hy; simp only [mem_hexShape] at hy; simp only [dot]; omega
    · simp only [mem_hexShape]; omega
    · intro y hy; simp only [mem_hexShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega
  · refine ⟨(b - c, b), ⟨?_, ?_⟩, (0, c), ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_hexShape]; omega
    · intro y hy; simp only [mem_hexShape] at hy; simp only [dot]; omega
    · simp only [mem_hexShape]; omega
    · intro y hy; simp only [mem_hexShape] at hy; simp only [dot]; omega
    · intro hh; rw [Prod.ext_iff] at hh; omega

/-- **Every primitive normal outside `hexE` has a one-point face.**  Six open cones, each
pinned by the two adjacent constraints via `face_subset_singleton_of_cone`. -/
theorem face_subsingleton_hexShape {n : ℤ × ℤ} (hp : Prim n) (hn : n ∉ hexE) :
    ∃ v, face (hexShape a b c d e) n ⊆ {v} := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hne : n.1 ≠ 0 ∧ n.2 ≠ 0 ∧ n.1 + n.2 ≠ 0 := by
    refine ⟨fun h0 => hn ?_, fun h0 => hn ?_, fun h0 => hn ?_⟩
    · rcases prim_eq_of_fst_eq_zero hp h0 with rfl | rfl <;> simp [hexE]
    · rcases prim_eq_of_snd_eq_zero hp h0 with rfl | rfl <;> simp [hexE]
    · rcases prim_eq_of_coord_eq_neg hp (by omega) with rfl | rfl <;> simp [hexE]
  obtain ⟨hp0, hq0, hpq0⟩ := hne
  -- the six constraints, as `dot m ≤ c` on the shape
  have cR : ∀ z ∈ hexShape a b c d e, dot ((1 : ℤ), (0 : ℤ)) z ≤ a := by
    intro z hz; simp only [mem_hexShape] at hz; simp only [dot]; omega
  have cL : ∀ z ∈ hexShape a b c d e, dot ((-1 : ℤ), (0 : ℤ)) z ≤ 0 := by
    intro z hz; simp only [mem_hexShape] at hz; simp only [dot]; omega
  have cT : ∀ z ∈ hexShape a b c d e, dot ((0 : ℤ), (1 : ℤ)) z ≤ b := by
    intro z hz; simp only [mem_hexShape] at hz; simp only [dot]; omega
  have cB : ∀ z ∈ hexShape a b c d e, dot ((0 : ℤ), (-1 : ℤ)) z ≤ e := by
    intro z hz; simp only [mem_hexShape] at hz; simp only [dot]; omega
  have cLR : ∀ z ∈ hexShape a b c d e, dot ((1 : ℤ), (-1 : ℤ)) z ≤ d := by
    intro z hz; simp only [mem_hexShape] at hz; simp only [dot]; omega
  have cUL : ∀ z ∈ hexShape a b c d e, dot ((-1 : ℤ), (1 : ℤ)) z ≤ c := by
    intro z hz; simp only [mem_hexShape] at hz; simp only [dot]; omega
  rcases lt_or_gt_of_ne hp0 with hp | hp <;> rcases lt_or_gt_of_ne hq0 with hq | hq <;>
    rcases lt_or_gt_of_ne hpq0 with hpq | hpq
  · -- p < 0, q < 0: vertex (0, -e), constraints L and B
    refine ⟨(0, -e), face_subset_singleton_of_cone (α := -n.1) (β := -n.2)
      (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide) cL cB
      (by simp only [mem_hexShape]; omega) (by simp [dot]) (by simp [dot])⟩
  · omega
  · -- p < 0, q > 0, p + q < 0: vertex (0, c), constraints UL and L
    refine ⟨(0, c), face_subset_singleton_of_cone (α := n.2) (β := -n.1 - n.2)
      (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide) cUL cL
      (by simp only [mem_hexShape]; omega) (by simp [dot]) (by simp [dot])⟩
  · -- p < 0, q > 0, p + q > 0: vertex (b - c, b), constraints UL and T
    refine ⟨(b - c, b), face_subset_singleton_of_cone (α := -n.1) (β := n.1 + n.2)
      (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide) cUL cT
      (by simp only [mem_hexShape]; omega) (by simp [dot]) (by simp [dot])⟩
  · -- p > 0, q < 0, p + q < 0: vertex (d - e, -e), constraints B and LR
    refine ⟨(d - e, -e), face_subset_singleton_of_cone (α := -n.1 - n.2) (β := n.1)
      (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide) cB cLR
      (by simp only [mem_hexShape]; omega) (by simp [dot]) (by simp [dot])⟩
  · -- p > 0, q < 0, p + q > 0: vertex (a, a - d), constraints LR and R
    refine ⟨(a, a - d), face_subset_singleton_of_cone (α := -n.2) (β := n.1 + n.2)
      (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide) cLR cR
      (by simp only [mem_hexShape]; omega) (by simp [dot]) (by simp [dot])⟩
  · omega
  · -- p > 0, q > 0: vertex (a, b), constraints R and T
    refine ⟨(a, b), face_subset_singleton_of_cone (α := n.1) (β := n.2)
      (by omega) (by omega) (fun z => by simp only [dot]; ring) (by decide) cR cT
      (by simp only [mem_hexShape]; omega) (by simp [dot]) (by simp [dot])⟩

/-- **The edge set of a nondegenerate `hexShape` is exactly `hexE`.** -/
theorem E_hexShape : E (hexShape a b c d e) = hexE := by
  ext n
  constructor
  · rintro ⟨hp, hnt⟩
    by_contra hn
    obtain ⟨v, hv⟩ := face_subsingleton_hexShape h hp hn
    exact Set.not_nontrivial_singleton (hnt.mono hv)
  · intro hn
    have hprim : Prim n := by
      simp only [hexE, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨z, hz, z', hz', hzz'⟩ := face_pair_hexShape h n hn
    exact ⟨hprim, z, hz, z', hz', hzz'⟩

/-- Every `hexE`-face of a nondegenerate `hexShape` has at least two lattice points. -/
theorem two_le_encard_face_hexShape (n : ℤ × ℤ) (hn : n ∈ hexE) :
    2 ≤ (face (hexShape a b c d e) n).encard := by
  obtain ⟨z, hz, z', hz', hzz'⟩ := face_pair_hexShape h n hn
  exact two_le_encard_of_pair hz hz' hzz'

end Faces

/-- `hexShape` is the intersection of six rational half-planes, hence a lattice-convex
region. -/
theorem isLatticeConvexRegion_hexShape (a b c d e : ℤ) :
    IsLatticeConvexRegion (hexShape a b c d e) := by
  have heq : hexShape a b c d e =
      (((((Set.univ ∩ halfPlaneLE ((1 : ℤ), (0 : ℤ)) a) ∩ halfPlaneLE ((-1 : ℤ), (0 : ℤ)) 0) ∩
        halfPlaneLE ((0 : ℤ), (1 : ℤ)) b) ∩ halfPlaneLE ((0 : ℤ), (-1 : ℤ)) e) ∩
        halfPlaneLE ((1 : ℤ), (-1 : ℤ)) d) ∩ halfPlaneLE ((-1 : ℤ), (1 : ℤ)) c := by
    ext z
    simp only [mem_hexShape, Set.mem_inter_iff, Set.mem_univ, halfPlaneLE, Set.mem_ofPred_eq,
      dot, true_and]
    omega
  rw [heq]
  iterate 6 refine isLatticeConvexRegion_inter_halfPlaneLE _ _ ?_
  exact Nivat.Colle41.isLatticeConvexRegion_univ

/-- **A nondegenerate `hexShape` is `E(U)`-enveloped by any `U` with edge set `hexE` and at
most two lattice points per edge.** -/
theorem enveloped_hexShape {U : Set (ℤ × ℤ)} {a b c d e : ℤ} (h : Nondeg a b c d e)
    (hEU : E U = hexE) (hU2 : ∀ n ∈ hexE, (face U n).encard ≤ 2) :
    Enveloped U (hexShape a b c d e) := by
  refine ⟨⟨isLatticeConvexRegion_hexShape a b c d e, fun n hn => ?_⟩, ?_⟩
  · rw [E_hexShape h] at hn
    exact ⟨by rw [hEU]; exact hn, le_trans (hU2 n hn) (two_le_encard_face_hexShape h n hn)⟩
  · rw [E_hexShape h, hEU]

/-! ## §2. The instance: hexagon window, quadrant `Â_∞`, sweep along `-v_{ℓ_{J+1}}` -/

open Nivat.ShellMink Pointwise in
/-- `ShellMink.hexA` (the unit hexagon `segOf (1,0) + segOf (1,1) + segOf (0,1)`) is the
`hexShape` with `a = b = 2`, `c = d = 1`, `e = 0`. -/
theorem hexA_eq_hexShape : hexA = hexShape 2 2 1 1 0 := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, w, hw, rfl⟩
    rcases mem_segOf_iff.mp hx with rfl | rfl <;> rcases mem_segOf_iff.mp hy with rfl | rfl <;>
      rcases mem_segOf_iff.mp hw with rfl | rfl <;> simp [mem_hexShape]
  · intro hz
    have h7 : z = (0, 0) ∨ z = (1, 0) ∨ z = (1, 1) ∨ z = (2, 1) ∨ z = (0, 1) ∨ z = (1, 2) ∨
        z = (2, 2) := by
      obtain ⟨x, y⟩ := z
      simp only [mem_hexShape] at hz
      simp only [Prod.ext_iff]
      omega
    rcases h7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, ⟨_, mem_segOf_zero _, _, mem_segOf_zero _, rfl⟩, _, mem_segOf_zero _, by decide⟩
    · exact ⟨_, ⟨_, mem_segOf_self _, _, mem_segOf_zero _, rfl⟩, _, mem_segOf_zero _, by decide⟩
    · exact ⟨_, ⟨_, mem_segOf_zero _, _, mem_segOf_self _, rfl⟩, _, mem_segOf_zero _, by decide⟩
    · exact ⟨_, ⟨_, mem_segOf_self _, _, mem_segOf_self _, rfl⟩, _, mem_segOf_zero _, by decide⟩
    · exact ⟨_, ⟨_, mem_segOf_zero _, _, mem_segOf_zero _, rfl⟩, _, mem_segOf_self _, by decide⟩
    · exact ⟨_, ⟨_, mem_segOf_zero _, _, mem_segOf_self _, rfl⟩, _, mem_segOf_self _, by decide⟩
    · exact ⟨_, ⟨_, mem_segOf_self _, _, mem_segOf_self _, rfl⟩, _, mem_segOf_self _, by decide⟩

theorem nondeg_hexA : Nondeg 2 2 1 1 0 := ⟨by norm_num, by norm_num, by norm_num, by norm_num,
  by norm_num, by norm_num⟩

/-- `E hexA = hexE` (cross-checks `ShellMink.E_hexA`, which gives the same set as a union of
three `E (segOf _)`). -/
theorem E_hexA_eq : E ShellMink.hexA = hexE := by
  rw [hexA_eq_hexShape]; exact E_hexShape nondeg_hexA

/-- **Each edge of the unit hexagon carries exactly two lattice points.** -/
theorem encard_face_hexA_le (n : ℤ × ℤ) (hn : n ∈ hexE) :
    (face ShellMink.hexA n).encard ≤ 2 := by
  rw [hexA_eq_hexShape]
  simp only [hexE, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  have key : ∀ (v v' : ℤ × ℤ), face (hexShape 2 2 1 1 0) n ⊆ {v, v'} →
      (face (hexShape 2 2 1 1 0) n).encard ≤ 2 := fun v v' h =>
    le_trans (Set.encard_mono h) (le_trans (Set.encard_insert_le _ _) (by norm_num))
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · refine key (2, 1) (2, 2) fun z hz => ?_
    have := hz.2 (2, 2) (by simp only [mem_hexShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [mem_hexShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega
  · refine key (0, 0) (0, 1) fun z hz => ?_
    have := hz.2 (0, 0) (by simp only [mem_hexShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [mem_hexShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega
  · refine key (1, 2) (2, 2) fun z hz => ?_
    have := hz.2 (2, 2) (by simp only [mem_hexShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [mem_hexShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega
  · refine key (0, 0) (1, 0) fun z hz => ?_
    have := hz.2 (0, 0) (by simp only [mem_hexShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [mem_hexShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega
  · refine key (1, 0) (2, 1) fun z hz => ?_
    have := hz.2 (1, 0) (by simp only [mem_hexShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [mem_hexShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega
  · refine key (0, 1) (1, 2) fun z hz => ?_
    have := hz.2 (0, 1) (by simp only [mem_hexShape]; omega)
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨x, y⟩ := z
    simp only [mem_hexShape] at hz1; simp only [dot] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]; omega

/-- `Â_i`: the hexagon `{0 ≤ x ≤ 2i, 0 ≤ y ≤ 2i, |x - y| ≤ i}`, an `E(hexA)`-enveloped set
sitting in the quadrant with its `ℓ_{J-1}`-edge on `x = 0` and its `ℓ_J`-edge on `y = 0`. -/
def Ai (i : ℕ) : Set (ℤ × ℤ) := hexShape (2 * i) (2 * i) i i 0

/-- `Â_∞^{(ε)}` for `Â_∞ = quad`, `v_{ℓ_{J-1}} = (0,-1)`, `n_J = (0,1)`, `c_J = 0`: the
half-strip `{0 ≤ x, -ε ≤ y}`. -/
theorem shell_quad_eq (ε : ℕ) :
    MaxEnv.shell quad ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε =
      {z | 0 ≤ z.1 ∧ -(ε : ℤ) ≤ z.2} := by
  ext z
  constructor
  · rintro ⟨⟨g1, g2⟩, ⟨hg1, hg2⟩, t, rfl, hd⟩
    simp only [dot, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Set.mem_ofPred_eq] at hd hg1 hg2 ⊢
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    refine ⟨(z.1, z.2 + (ε : ℤ)), ⟨by simpa using h1, by simp; omega⟩, ε, ?_, ?_⟩
    · ext <;> simp
    · simp [dot]; omega

/-- **`:518` unwound.**  Sweeping `Â_i` along `-v_{ℓ_{J+1}} = (-1,-1)` and intersecting
with `Â_∞^{(ε)}` gives the hexagon `{0 ≤ x ≤ 2i, -ε ≤ y ≤ 2i, |x - y| ≤ i}`. -/
theorem shell518_eq_hexShape (i ε : ℕ) :
    ShellMink.shellInter (Ai i)
        (MaxEnv.shell quad ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε) ((-1 : ℤ), (-1 : ℤ)) =
      hexShape (2 * i) (2 * i) i i ε := by
  rw [ShellMink.shellInter, shell_quad_eq]
  ext z
  simp only [Set.mem_inter_iff, mem_reachSet, Ai, mem_hexShape, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨g, hg, t, rfl⟩, h1, h2⟩
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 ⊢
    omega
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨⟨(z.1 + (max 0 (-z.2) : ℤ), z.2 + (max 0 (-z.2) : ℤ)), ?_,
      (max 0 (-z.2)).toNat, ?_⟩, by omega, by omega⟩
    · dsimp only
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · have ht : ((max 0 (-z.2)).toNat : ℤ) = max 0 (-z.2) :=
        Int.toNat_of_nonneg (le_max_left _ _)
      ext <;> simp [ht]

/-- The `:518` shape is nondegenerate as soon as `ε + 1 ≤ i`. -/
theorem nondeg_shell518 {i ε : ℕ} (hi : ε + 1 ≤ i) : Nondeg (2 * i) (2 * i) i i ε := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **The `:518` object is `E(𝒮_φ)`-enveloped, at every `ε`, for all `i ≥ ε + 1`.** -/
theorem enveloped_shell518_hexA {i ε : ℕ} (hi : ε + 1 ≤ i) :
    Enveloped ShellMink.hexA (ShellMink.shellInter (Ai i)
      (MaxEnv.shell quad ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε) ((-1 : ℤ), (-1 : ℤ))) := by
  rw [shell518_eq_hexShape]
  exact enveloped_hexShape (nondeg_shell518 hi) E_hexA_eq encard_face_hexA_le

/-- **The `shellEnv` shape** (`Lemma35.lean:748`) for `Env := EnvOf hexA`, `shell i ε :=`
the `:518` object, with `ε := 1`, `i₀ := 2`. -/
theorem shellEnv_shape_shell518 :
    ∃ ε i₀ : ℕ, 0 < ε ∧ ∀ i, i₀ ≤ i → EnvOf ShellMink.hexA (ShellMink.shellInter (Ai i)
      (MaxEnv.shell quad ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε) ((-1 : ℤ), (-1 : ℤ))) :=
  ⟨1, 2, one_pos, fun _ hi => enveloped_shell518_hexA (by omega)⟩

/-- `subShell` on this shape: `Â_i ⊆ Â_i^{(ε)}`. -/
theorem Ai_subset_shell518 (i ε : ℕ) :
    Ai i ⊆ ShellMink.shellInter (Ai i)
      (MaxEnv.shell quad ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε) ((-1 : ℤ), (-1 : ℤ)) := by
  rw [shell518_eq_hexShape]
  intro z hz
  simp only [Ai, mem_hexShape] at hz ⊢
  omega

/-- `shellProper` on this shape: for `0 < ε` (and `1 ≤ i`, so that `Â_i` has a genuine
`ℓ_J`-edge to push out from) the point `(0, -1)` is new. -/
theorem not_shell518_subset_Ai {i ε : ℕ} (hi : 1 ≤ i) (hε : 0 < ε) :
    ¬ ShellMink.shellInter (Ai i)
      (MaxEnv.shell quad ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε) ((-1 : ℤ), (-1 : ℤ)) ⊆
        Ai i := by
  rw [shell518_eq_hexShape]
  intro h
  have := h (show ((0 : ℤ), (-1 : ℤ)) ∈ hexShape (2 * i) (2 * i) i i ε by
    simp only [mem_hexShape]; omega)
  simp [Ai, mem_hexShape] at this

end Nivat.ShellSweep

#print axioms Nivat.ShellSweep.hexA_eq_hexShape
#print axioms Nivat.ShellSweep.encard_face_hexA_le
#print axioms Nivat.ShellSweep.shell518_eq_hexShape
#print axioms Nivat.ShellSweep.enveloped_shell518_hexA
#print axioms Nivat.ShellSweep.shellEnv_shape_shell518
#print axioms Nivat.ShellSweep.Ai_subset_shell518
#print axioms Nivat.ShellSweep.not_shell518_subset_Ai
#print axioms Nivat.ShellSweep.prim_eq_of_coord_eq_neg
#print axioms Nivat.ShellSweep.face_subset_singleton_of_cone
#print axioms Nivat.ShellSweep.E_hexShape
#print axioms Nivat.ShellSweep.isLatticeConvexRegion_hexShape
#print axioms Nivat.ShellSweep.enveloped_hexShape
