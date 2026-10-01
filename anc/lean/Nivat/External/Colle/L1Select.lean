/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.HalfPlaneFamily
import Nivat.External.Colle.ChainGeom

/-!
# `L1Select`: the `u'` selection behind `MaxBResidual.det'` and `.prim`

Lane Rsweep's file (exclusive).  Consumer: `L1Assemble.lean` (`exists_L1MaxBResidual_of_pieces`
/ `_of_normal`), which feeds `exists_L1MaxBResidual` (`RegionSteps.lean`).  That leaf's
conclusion is `∃ e u u' v c τ ε S₁ F, … ∧ MaxBResidual ε u u' c τ S₁ F` — kernel-checked:
`u` and `u'` are **existentially bound in the conclusion**, not passed in.  Two of
`MaxBResidual`'s fields (`L1Assemble.lean:944`) constrain that choice and nothing else:

* `det' : det u u' ≠ 0`  (conjunct 5),
* `prim : Primitive u'`  (conjunct 6).

## The slot assignment (corrected 2026-09-19)

**`u := vl`.**  `base0` is discharged in `MaxBResidual.ofFive` by
`two_le_min_faces_of_nel hgen hℓ_nel hℓ_neg hu hdet_ℓ` (`L1Assemble.lean:1920-1935`), whose
`hdet_ℓ : dot ℓ u = 0` puts the **period direction** `u` along `ℓ` (`b3_colle2.txt:806`,
`h ∥ ℓ`).  The leaf binds exactly `hvl_prim : Primitive vl` and `hdet_ℓ : dot ℓ vl = 0`, so
`u := vl` and the two binders are the two inputs.  `u'` is then the along-boundary direction of
a cutting normal `m` with `0 < dot m vl` — and `m` is **not** `±ℓ` (`dot ℓ vl = 0`).

1. **Construction** (§1).  For `m ≠ 0`, the primitive vector along the line `dot m · = 0`,
   obtained by dividing `(-m.2, m.1)` by its gcd
   (`Nivat.exists_primitive_nsmul_eq`, `Lattice/Primitive.lean:52` — reused, not re-proved).
2. **Independence** (§2).  `dot m u' = 0`, `u' ≠ 0`, `dot m u ≠ 0` give `det u u' ≠ 0`:
   `u'` spans `m`'s orthogonal line and `u` is off it.  This is already in the tree as
   `Nivat.ColleReg.det_ne_zero_of_dot` (`ChainGeom.lean:296`, on-chain), and is **reused**
   (`PROTOCOL.md` §20) rather than re-stated under a new name.
3. **Packaging** (§3).  `exists_uu'_of_normal : m ≠ 0 → 0 < dot m u → ∃ u', dot m u' = 0 ∧
   Primitive u' ∧ det u u' ≠ 0`, so `det'` and `prim` are two projections of one witness.
   Consumed at `L1Assemble.lean:2239` (`det_ne_zero_of_dot_pos`) and `:2274`
   (`exists_uu'_of_normal`), both with `u := vl`.

## Retracted (2026-09-19, PROTOCOL §14: status changed, reason kept, nothing silently deleted)

The first version of this file carried a §4 `exists_normal_of_binders` with the slots
**inverted**: `u' := vl`, `m := ±ℓ`, and "the only real input is `dot ℓ u ≠ 0`".  Under the
actual assignment `u := vl` its premise `dot ℓ u ≠ 0` **is the negation of the leaf's own
binder** `hdet_ℓ : dot ℓ vl = 0`, and its conclusion `0 < dot (±ℓ) vl` is `0 < 0`.  Premise and
conclusion were both unsatisfiable at the leaf; L1asm found it while wiring the assembly, and
team-lead confirmed.  The lemma and its two non-vacuity witnesses were removed (they had no
consumer and could never acquire one).  One reading from that section survives as a comment
because it is still true and still load-bearing: *`hdet_vl : det p vl = 0` is the negation of
`det'` at `u := p, u' := vl`, so the binder `p` is not `u`; `u := vl` is pinned by `hdet_ℓ`
through `ofFive`.*

## §4  Adjacent edges need not be unimodular (kernel counterexample, 2026-09-19)

Collé's Claim 4.6 (`b3_colle2.txt:780-784`) takes `u' := v_{ℓ_{ι-1}}`, the direction of the
edge *adjacent* to `ℓ` in the chain `ℓ_{i+1} := ℓ_i^{(-)}`.  L1B's `ofWedge`
(`L1RegionBuild.lean:344`) instead asks `hunimod : det u' vl = ±1`.  If `u'` is chosen freely
that is free (`Primitive.exists_dual`, `Defs/Config.lean:164`); if `u'` is pinned to the
adjacent edge it is a geometric claim, and **§4 shows it is false**: the lattice cone spanned
by `(2,1)` and `(-1,2)` is an `IsLatticeConvexRegion` whose only two edge normals `(1,-2)`,
`(-2,-1)` are `IsSuccEdge`-adjacent (in one order or the other) with `det = ∓5`.  Passing to
edge directions via `perp` does not change the determinant.  ⚠ Scope: the witness is an
unbounded cone (the shape of Collé's `(ℓ, ℓ')`-regions), not a bounded polygon; a bounded
witness would need the full `E`-computation of a triangle and is **not** done here.
-/

set_option autoImplicit false

namespace Nivat.L1Select

open Nivat Nivat.LE2

/-! ## §1  The primitive direction of the line `dot m · = 0` -/

theorem dot_perp_self (m : ℤ × ℤ) : dot m (-m.2, m.1) = 0 := by
  simp only [dot]; ring

theorem perp_ne_zero {m : ℤ × ℤ} (hm : m ≠ 0) : ((-m.2, m.1) : ℤ × ℤ) ≠ 0 := by
  intro h
  apply hm
  simp only [Prod.mk_eq_zero, neg_eq_zero] at h
  exact Prod.ext h.2 h.1

/-- **The primitive vector along `m`'s orthogonal line exists.**  Divide `(-m.2, m.1)` by its
gcd; orthogonality survives because `dot m` is linear and the gcd is nonzero. -/
theorem exists_perpPrim {m : ℤ × ℤ} (hm : m ≠ 0) :
    ∃ u' : ℤ × ℤ, dot m u' = 0 ∧ Primitive u' := by
  obtain ⟨v, k, hv, hk, hkv⟩ := exists_primitive_nsmul_eq (perp_ne_zero hm)
  refine ⟨v, ?_, hv⟩
  have h : dot m ((k : ℤ) • v) = 0 := by rw [← hkv]; exact dot_perp_self m
  rw [HalfPlaneFamily.dot_zsmul_right] at h
  have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  exact (mul_eq_zero.mp h).resolve_left hk'

/-! ## §2  Independence from transversality

`Nivat.ColleReg.det_ne_zero_of_dot {n u v} (hv : v ≠ 0) (hnv : dot n v = 0) (hnu : dot n u ≠ 0) :
det u v ≠ 0` (`ChainGeom.lean:296`) is the statement; only the `0 < ⋯` form is added. -/

/-- `det u u' ≠ 0` from `0 < dot m u` and `u'` primitive on `m`'s line. -/
theorem det_ne_zero_of_dot_pos {m u u' : ℤ × ℤ} (hu' : Primitive u') (hmu' : dot m u' = 0)
    (hmu : 0 < dot m u) : det u u' ≠ 0 :=
  Nivat.ColleReg.det_ne_zero_of_dot hu'.ne_zero hmu' hmu.ne'

/-! ## §3  Packaging: `det'` and `prim` as two projections of one witness -/

/-- **The `u'` selection.**  Given the cutting normal `m` and the transversality of `u` that
the assembly already demands, a `u'` along the boundary exists that is primitive and
independent of `u` — conjuncts 5 and 6 together. -/
theorem exists_uu'_of_normal {m u : ℤ × ℤ} (hm : m ≠ 0) (hmu : 0 < dot m u) :
    ∃ u' : ℤ × ℤ, dot m u' = 0 ∧ Primitive u' ∧ det u u' ≠ 0 := by
  obtain ⟨u', hmu', hprim⟩ := exists_perpPrim hm
  exact ⟨u', hmu', hprim, det_ne_zero_of_dot_pos hprim hmu' hmu⟩

-- Reading kept from the retracted §4 (see module docstring): the leaf's `hdet_vl : det p vl = 0`
-- is the negation of `det'` at `u := p, u' := vl`, so the binder `p` is not `u`; `u := vl` is
-- pinned by `hdet_ℓ` through `MaxBResidual.ofFive`.

/-! ### Non-vacuity of §3

`m = (2, 0)` (deliberately imprimitive), `u = (1, 0)`: the selection returns `u' = ±(0, 1)`. -/

theorem two_zero_ne_zero : ((2 : ℤ), (0 : ℤ)) ≠ (0 : ℤ × ℤ) := by
  intro h
  have := congrArg Prod.fst h
  norm_num at this

theorem dot_two_zero_one_zero_pos : (0 : ℤ) < dot ((2 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) := by
  simp [dot]

/-- The selection on a concrete pair: the hypotheses of `exists_uu'_of_normal` are met. -/
theorem exists_uu'_two_zero :
    ∃ u' : ℤ × ℤ, dot ((2 : ℤ), (0 : ℤ)) u' = 0 ∧ Primitive u' ∧
      det ((1 : ℤ), (0 : ℤ)) u' ≠ 0 :=
  exists_uu'_of_normal two_zero_ne_zero dot_two_zero_one_zero_pos

/-- …and an explicit witness, so the existential is not hiding an empty type. -/
theorem uu'_two_zero_explicit :
    dot ((2 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 0 ∧ Primitive ((0 : ℤ), (1 : ℤ)) ∧
      det ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ≠ 0 :=
  ⟨by simp [dot], ⟨0, 1, by norm_num⟩, by simp [det]⟩

/-! ## §4  Adjacent edges need not be unimodular

The lattice cone `cone5 = {s•(2,1) + t•(-1,2) : s, t ≥ 0} ∩ ℤ²`, written as the two
half-planes `0 ≤ det (2,1) z` and `0 ≤ det z (-1,2)`.  Its edges are the two rays; their
outer normals (the tree's convention, `LatticeEdges.lean:160`: the face *maximises* `dot n`)
are `n₁ = (1,-2)` (face = the `(2,1)`-ray) and `n₂ = (-2,-1)` (face = the `(-1,2)`-ray). -/

/-- The cone spanned by `(2,1)` and `(-1,2)`. -/
def cone5 : Set (ℤ × ℤ) := {z | 0 ≤ 2 * z.2 - z.1 ∧ 0 ≤ 2 * z.1 + z.2}

theorem mem_cone5 {z : ℤ × ℤ} : z ∈ cone5 ↔ 0 ≤ 2 * z.2 - z.1 ∧ 0 ≤ 2 * z.1 + z.2 := Iff.rfl

theorem cone5_eq :
    cone5 = (Set.univ ∩ halfPlaneGE ((-1 : ℤ), (2 : ℤ)) 0) ∩ halfPlaneGE ((2 : ℤ), (1 : ℤ)) 0 := by
  ext z
  simp only [cone5, halfPlaneGE, dot, Set.mem_inter_iff, Set.mem_univ, true_and,
    Set.mem_ofPred_eq]
  omega

/-- `cone5` is a lattice-convex region: `univ` cut by two integral half-planes. -/
theorem isLatticeConvexRegion_cone5 : IsLatticeConvexRegion cone5 := by
  rw [cone5_eq]
  exact isLatticeConvexRegion_inter_halfPlaneGE
    (isLatticeConvexRegion_inter_halfPlaneGE Colle41.isLatticeConvexRegion_univ _ _) _ _

theorem prim_n₁ : Prim ((1 : ℤ), (-2 : ℤ)) :=
  prim_iff_primitive.mpr ⟨1, 0, by norm_num⟩

theorem prim_n₂ : Prim ((-2 : ℤ), (-1 : ℤ)) :=
  prim_iff_primitive.mpr ⟨0, -1, by norm_num⟩

theorem n₁_ne_n₂ : ((1 : ℤ), (-2 : ℤ)) ≠ ((-2 : ℤ), (-1 : ℤ)) := by norm_num

/-- `(1,-2)` is an edge normal: `dot (1,-2) ≤ 0` on the cone, with equality at `0` and `(2,1)`. -/
theorem n₁_mem_E : ((1 : ℤ), (-2 : ℤ)) ∈ LE2.E cone5 := by
  rw [mem_E_iff]
  refine ⟨prim_n₁, (0 : ℤ × ℤ), ?_, ((2 : ℤ), (1 : ℤ)), ?_, by
    intro h; have := congrArg Prod.fst h; norm_num at this⟩
  · rw [mem_face_iff]
    refine ⟨by rw [mem_cone5]; norm_num, fun y hy => ?_⟩
    rw [mem_cone5] at hy
    simp only [dot, Prod.fst_zero, Prod.snd_zero]
    omega
  · rw [mem_face_iff]
    refine ⟨by rw [mem_cone5]; norm_num, fun y hy => ?_⟩
    rw [mem_cone5] at hy
    simp only [dot]
    omega

/-- `(-2,-1)` is an edge normal: `dot (-2,-1) ≤ 0` on the cone, with equality at `0` and
`(-1,2)`. -/
theorem n₂_mem_E : ((-2 : ℤ), (-1 : ℤ)) ∈ LE2.E cone5 := by
  rw [mem_E_iff]
  refine ⟨prim_n₂, (0 : ℤ × ℤ), ?_, ((-1 : ℤ), (2 : ℤ)), ?_, by
    intro h; have := congrArg Prod.fst h; norm_num at this⟩
  · rw [mem_face_iff]
    refine ⟨by rw [mem_cone5]; norm_num, fun y hy => ?_⟩
    rw [mem_cone5] at hy
    simp only [dot, Prod.fst_zero, Prod.snd_zero]
    omega
  · rw [mem_face_iff]
    refine ⟨by rw [mem_cone5]; norm_num, fun y hy => ?_⟩
    rw [mem_cone5] at hy
    simp only [dot]
    omega

/-- **The core of the `E`-computation.**  If `dot k ≤ 0` on the cone and `dot k` vanishes at a
nonzero cone point `w`, then `k` is one of the two edge normals.  Proof: `5 w = α•(2,1) +
β•(-1,2)` with `α = 2w.1 + w.2 ≥ 0`, `β = 2w.2 - w.1 ≥ 0`, so `0 = 5 dot k w = α p + β q` with
`p = dot k (2,1) ≤ 0`, `q = dot k (-1,2) ≤ 0`; both products vanish, `w ≠ 0` forces `α > 0` or
`β > 0`, hence `p = 0` or `q = 0`, and primitivity plus the sign of the other pairing pins `k`. -/
theorem eq_n₁_or_n₂_of_key {k : ℤ × ℤ} (hprim : Prim k)
    (hp : dot k ((2 : ℤ), (1 : ℤ)) ≤ 0) (hq : dot k ((-1 : ℤ), (2 : ℤ)) ≤ 0)
    {w : ℤ × ℤ} (hw : w ∈ cone5) (hw0 : w ≠ 0) (hdot : dot k w = 0) :
    k = ((1 : ℤ), (-2 : ℤ)) ∨ k = ((-2 : ℤ), (-1 : ℤ)) := by
  rw [mem_cone5] at hw
  obtain ⟨hβ, hα⟩ := hw
  simp only [dot] at hp hq hdot
  have hid : (2 * w.1 + w.2) * (2 * k.1 + k.2) + (2 * w.2 - w.1) * (-k.1 + 2 * k.2)
      = 5 * (k.1 * w.1 + k.2 * w.2) := by ring
  have hαp : (2 * w.1 + w.2) * (2 * k.1 + k.2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hα (by linarith)
  have hβq : (2 * w.2 - w.1) * (-k.1 + 2 * k.2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hβ (by linarith)
  have hαp0 : (2 * w.1 + w.2) * (2 * k.1 + k.2) = 0 := by linarith
  have hβq0 : (2 * w.2 - w.1) * (-k.1 + 2 * k.2) = 0 := by linarith
  obtain ⟨a, b, hab⟩ := prim_iff_primitive.mp hprim
  rcases mul_eq_zero.mp hαp0 with hα0 | hp0
  · -- `α = 0`, so `β > 0` (else `w = 0`), so `q = 0`, so `k ∥ (2,1)`.
    have hβpos : 0 < 2 * w.2 - w.1 := by
      rcases hβ.lt_or_eq with h | h
      · exact h
      · exfalso
        exact hw0 (Prod.ext (by show w.1 = 0; omega) (by show w.2 = 0; omega))
    rcases mul_eq_zero.mp hβq0 with h | hq0
    · omega
    · right
      have hk1 : k.1 = 2 * k.2 := by linarith
      have hunit : k.2 * (2 * a + b) = 1 := by rw [hk1] at hab; linear_combination hab
      rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hunit) with h | h
      · exfalso; omega
      · exact Prod.ext (by show k.1 = -2; omega) (by show k.2 = -1; omega)
  · -- `p = 0`, so `k ∥ (1,-2)`.
    left
    have hk2 : k.2 = -2 * k.1 := by linarith
    have hunit : k.1 * (a - 2 * b) = 1 := by rw [hk2] at hab; linear_combination hab
    rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hunit) with h | h
    · exact Prod.ext (by show k.1 = 1; omega) (by show k.2 = -2; omega)
    · exfalso; omega

/-- **`E cone5 ⊆ {(1,-2), (-2,-1)}`.**  A nontrivial face has two distinct maximisers; `0 ∈
cone5` and `2•z ∈ cone5` force the maximum to be `0`, so `dot k ≤ 0` on the cone and one of
the two maximisers is a nonzero cone point where `dot k` vanishes — `eq_n₁_or_n₂_of_key`. -/
theorem eq_n₁_or_n₂_of_mem_E {k : ℤ × ℤ} (hk : k ∈ LE2.E cone5) :
    k = ((1 : ℤ), (-2 : ℤ)) ∨ k = ((-2 : ℤ), (-1 : ℤ)) := by
  rw [mem_E_iff] at hk
  obtain ⟨hprim, z₁, hz₁, z₂, hz₂, hne⟩ := hk
  rw [mem_face_iff] at hz₁ hz₂
  obtain ⟨hz₁c, hmax₁⟩ := hz₁
  obtain ⟨hz₂c, hmax₂⟩ := hz₂
  have h0 : dot k 0 ≤ dot k z₁ := hmax₁ 0 (by rw [mem_cone5]; norm_num)
  have h2 : dot k ((2 : ℤ) • z₁) ≤ dot k z₁ := by
    refine hmax₁ _ ?_
    rw [mem_cone5] at hz₁c ⊢
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    omega
  have hM : dot k z₁ = 0 := by
    simp only [dot, Prod.fst_zero, Prod.snd_zero, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at h0 h2 ⊢
    linarith
  have hle : ∀ y ∈ cone5, dot k y ≤ 0 := fun y hy => by rw [← hM]; exact hmax₁ y hy
  have hp : dot k ((2 : ℤ), (1 : ℤ)) ≤ 0 := hle _ (by rw [mem_cone5]; norm_num)
  have hq : dot k ((-1 : ℤ), (2 : ℤ)) ≤ 0 := hle _ (by rw [mem_cone5]; norm_num)
  have hz₂0 : dot k z₂ = 0 :=
    le_antisymm (hle _ hz₂c) (by rw [← hM]; exact hmax₂ z₁ hz₁c)
  by_cases h1 : z₁ = 0
  · subst h1
    exact eq_n₁_or_n₂_of_key hprim hp hq hz₂c hne.symm hz₂0
  · exact eq_n₁_or_n₂_of_key hprim hp hq hz₁c h1 hM

/-- **The two normals are adjacent** (`IsSuccEdge`, `LatticeEdges.lean:515`), in whichever
order the angular key puts them: `E cone5` has no third element to sit between them. -/
theorem isSuccEdge_cone5 :
    IsSuccEdge cone5 ((1 : ℤ), (-2 : ℤ)) ((-2 : ℤ), (-1 : ℤ)) ∨
      IsSuccEdge cone5 ((-2 : ℤ), (-1 : ℤ)) ((1 : ℤ), (-2 : ℤ)) := by
  rcases angLT_trichotomy prim_n₁ prim_n₂ with h | h | h
  · left
    refine ⟨n₁_mem_E, n₂_mem_E, Or.inl ⟨h, fun k hk h1 h2 => ?_⟩⟩
    rcases eq_n₁_or_n₂_of_mem_E hk with rfl | rfl
    · exact angLT_irrefl _ h1
    · exact angLT_irrefl _ h2
  · exact absurd h n₁_ne_n₂
  · right
    refine ⟨n₂_mem_E, n₁_mem_E, Or.inl ⟨h, fun k hk h1 h2 => ?_⟩⟩
    rcases eq_n₁_or_n₂_of_mem_E hk with rfl | rfl
    · exact angLT_irrefl _ h2
    · exact angLT_irrefl _ h1

theorem det_n₁_n₂ : det ((1 : ℤ), (-2 : ℤ)) ((-2 : ℤ), (-1 : ℤ)) = -5 := by
  norm_num [det]

theorem det_n₂_n₁ : det ((-2 : ℤ), (-1 : ℤ)) ((1 : ℤ), (-2 : ℤ)) = 5 := by
  norm_num [det]

/-- **Adjacent edge normals of a lattice-convex region need not be unimodular.**  Witness:
`cone5`, normals `(1,-2)`, `(-2,-1)`, `det = ∓5`. -/
theorem not_forall_isSuccEdge_det_unimod :
    ¬ ∀ (R : Set (ℤ × ℤ)) (n m : ℤ × ℤ), IsLatticeConvexRegion R → IsSuccEdge R n m →
      det n m = 1 ∨ det n m = -1 := by
  intro h
  rcases isSuccEdge_cone5 with hs | hs
  · have := h _ _ _ isLatticeConvexRegion_cone5 hs
    rw [det_n₁_n₂] at this
    omega
  · have := h _ _ _ isLatticeConvexRegion_cone5 hs
    rw [det_n₂_n₁] at this
    omega

/-- Rotating both vectors by a quarter turn preserves `det`, so the statement about edge
**directions** (`perp` of the normals — Collé's `v_ℓ`, `v_{ℓ'}`) is the same statement. -/
theorem det_perp_perp (a b : ℤ × ℤ) :
    det (Nivat.ColleReg.perp a) (Nivat.ColleReg.perp b) = det a b := by
  simp only [det, Nivat.ColleReg.perp]; ring

/-- **Adjacent edge directions of a lattice-convex region need not be unimodular** — the
statement in the form Claim 4.6's `u' := v_{ℓ_{ι-1}}`, `vl := v_ℓ` would need.  The directions
here are `perp (1,-2) = (2,1)` and `perp (-2,-1) = (1,-2)`, `det = -5`. -/
theorem not_forall_isSuccEdge_det_perp_unimod :
    ¬ ∀ (R : Set (ℤ × ℤ)) (n m : ℤ × ℤ), IsLatticeConvexRegion R → IsSuccEdge R n m →
      det (Nivat.ColleReg.perp n) (Nivat.ColleReg.perp m) = 1 ∨
        det (Nivat.ColleReg.perp n) (Nivat.ColleReg.perp m) = -1 := by
  intro h
  apply not_forall_isSuccEdge_det_unimod
  intro R n m hR hs
  rw [← det_perp_perp]
  exact h R n m hR hs

/-- The hand-read number from the dispatch, now compiled: `det (2,1) (-1,2) = 5`. -/
theorem det_two_one_neg_one_two : det ((2 : ℤ), (1 : ℤ)) ((-1 : ℤ), (2 : ℤ)) = 5 := by
  norm_num [det]

end Nivat.L1Select

section Receipts
/-! Standing `#print axioms` receipts.  Deletable as a block. -/

#print axioms Nivat.L1Select.exists_perpPrim
#print axioms Nivat.L1Select.det_ne_zero_of_dot_pos
#print axioms Nivat.L1Select.exists_uu'_of_normal
#print axioms Nivat.L1Select.exists_uu'_two_zero
#print axioms Nivat.L1Select.uu'_two_zero_explicit
#print axioms Nivat.L1Select.isLatticeConvexRegion_cone5
#print axioms Nivat.L1Select.n₁_mem_E
#print axioms Nivat.L1Select.n₂_mem_E
#print axioms Nivat.L1Select.eq_n₁_or_n₂_of_key
#print axioms Nivat.L1Select.eq_n₁_or_n₂_of_mem_E
#print axioms Nivat.L1Select.isSuccEdge_cone5
#print axioms Nivat.L1Select.not_forall_isSuccEdge_det_unimod
#print axioms Nivat.L1Select.det_perp_perp
#print axioms Nivat.L1Select.not_forall_isSuccEdge_det_perp_unimod
#print axioms Nivat.L1Select.det_two_one_neg_one_two

end Receipts
