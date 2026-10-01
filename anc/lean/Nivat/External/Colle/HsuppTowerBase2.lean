/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.HsuppTowerBase
import Nivat.External.Colle.TowerConstruct

/-!
# `hsupp_tower_base2` — the extremality derivation and three sign/orthogonality bridges

Lane `lane-hsupp`, dispatched by team-lead 2026-09-22, continuing `HsuppTowerBase.lean`.

## Part 1: extremality derivation

`b0pt` is defined (upstream, in `TowerConstruct.lean`) as the `-u'`-extreme point among the
`m0`-minimisers of `B`, i.e. `faceStart B negm0` where `negm0 := -m0` and `dir negm0 = u'`
(so `faceStart_min` literally says: `b0pt` minimises `dot u'`, i.e. maximises `dot (-u')`).
`b0pt_face_facts` below shows this point equals the far endpoint of `face B (nuGen w0)` in
direction `w0`, i.e. exactly `HsuppTowerBase.hbase_base_case`'s `hb0pt_mem`/`hb0pt_maxdir`
hypotheses.

Route (team-lead, verbatim): the edge of `B` arriving at `b0pt` is cw-adjacent to `negm0` in
`B`'s fan (`hadjB` forbids any `B`-edge strictly between `u'` and `vl`, which is exactly what
makes `nuGen w0`/`negm0` fan-adjacent with nothing between — the same adjacency argument as
`TowerConstruct.lean`'s Lemma H, applied to `B`'s fan at `b0pt` instead of to the `u'`/`vl`
gap). `PolyChain.adjacent_shared_vertex` turns "fan-adjacent, `0 < det (nuGen w0) negm0`,
nothing strictly between" into the *equality* `faceEnd B (nuGen w0) = faceStart B negm0`
(the shared-vertex fact); `faceEnd_maxdir` (new, general-purpose, proved below) then reads
off the `w0`-maximality for free.

The `0 < det (nuGen w0) negm0` and "nothing strictly between" hypotheses (`hdet_order`,
`hno_between`) are taken as explicit binders here — they are consequences of `hadjB` plus
`sortedCand`'s sortedness (that `wtower 0` is literally the *first* candidate after `u'` in
the fan order), which live in `TowerConstruct.lean` and are not yet importable from `tmp/wip`.

## Part 2: three small bridges

`hnuGen_EB`, `hj_orth`, `h_u'_neg`, `h_vl_le` (the remaining `hbase_base_case` hypotheses)
translate from `det`-based facts (`genPerp'_wgen_mem_E_B`, `det_wgen_h_eq_zero`,
`det_w_u'_sign_eq_of_hadjB`) to the `dot (nuGen w0) ·`-based shape `hbase_base_case` wants,
via the identity `dot (nuGen w) x = - det w x` (`dot_nuGen_eq_neg_det`, unconditional, no
primitivity needed). The `det`-facts themselves are again taken as binders pending
`TowerConstruct.lean` landing.

`w0 = wgen d nl j0` for the `j0` at tower-index `0` needs no Lean content here: `candSet` is
an image of `wgen`, so `mem_candSet_wtower` (`TowerConstruct.lean`) gives `w0 ∈ candSet`,
hence `∃ j0, w0 = wgen d nl j0` immediately from the image structure — nothing to bridge.

## Status

0 sorry, axiom-clean.
-/

set_option autoImplicit false

namespace Nivat.HsuppTowerBase

open Nivat Nivat.LE2 Nivat.PolyChain

/-! ## Part 1: extremality -/

/-- **General-purpose**: the far endpoint of `face T ν` in direction `dir ν` maximises
`dot (dir ν)` over the whole face. Unconditional — no primitivity of `ν` needed (only that
`ν ∈ E T`), since the coefficient `dot (dir ν) (dir ν)` is a sum of squares, hence `≥ 0`. -/
theorem faceEnd_maxdir {T : Set (ℤ × ℤ)} {ν w : ℤ × ℤ} (hlc : Nivat.IsLatticeConvexRegion T) (hfin : T.Finite)
    (hν : ν ∈ E T) (hdirν : dir ν = w) :
    ∀ z ∈ face T ν, dot w z ≤ dot w (faceStart T ν + (faceLen T ν : ℤ) • dir ν) := by
  subst hdirν
  intro z hz
  rw [face_eq_segment hlc hfin hν] at hz
  obtain ⟨t, htle, htz⟩ := hz
  have hexpand : ∀ s : ℤ, dot (dir ν) (faceStart T ν + s • dir ν)
      = dot (dir ν) (faceStart T ν) + s * dot (dir ν) (dir ν) := by
    intro s
    simp only [dot, dir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [htz, hexpand, hexpand]
  have htcast : (t : ℤ) ≤ (faceLen T ν : ℤ) := by exact_mod_cast htle
  have hQnonneg : 0 ≤ dot (dir ν) (dir ν) := by
    simp only [dot]; exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right htcast hQnonneg]

/-- **The extremality derivation.** `faceStart B negm0` (the `-u'`-extreme point among the
`m0`-minimisers of `B`, via `faceStart_min` once `dir negm0 = u'`) is both a member of
`face B (nuGen w0)` and its `w0`-directional maximiser — exactly `hbase_base_case`'s
`hb0pt_mem`/`hb0pt_maxdir`. -/
theorem b0pt_face_facts {B : Set (ℤ × ℤ)} (hBfin : B.Finite)
    (hBconv : Nivat.IsLatticeConvexRegion B)
    {negm₀ w₀ : ℤ × ℤ} (hnegm₀_EB : negm₀ ∈ E B) (hnuGen_EB : nuGen w₀ ∈ E B)
    (hdet_order : 0 < det (nuGen w₀) negm₀)
    (hno_between : ∀ μ ∈ E B, ¬ (0 < det (nuGen w₀) μ ∧ 0 < det μ negm₀)) :
    (faceStart B negm₀ ∈ face B (nuGen w₀)) ∧
    (∀ z ∈ face B (nuGen w₀), dot w₀ z ≤ dot w₀ (faceStart B negm₀)) := by
  have hi := adjacent_shared_vertex hBfin hBconv hnuGen_EB hnegm₀_EB hdet_order hno_between
  refine ⟨hi ▸ faceEnd_mem hBconv hBfin hnuGen_EB, ?_⟩
  rw [← hi]
  exact faceEnd_maxdir hBconv hBfin hnuGen_EB (dir_nuGen w₀)

/-- Documentation corollary (not consumed downstream): `faceStart B negm0` really is the
`-u'`-extreme point among the `m0`-minimisers, i.e. it minimises `dot u'` over `face B negm0`
(= the `m0`-minimisers of `B` once `negm0 = -m0`), given `dir negm0 = u'`. Immediate from
`faceStart_min`. -/
theorem b0pt_is_neg_u'_extreme {B : Set (ℤ × ℤ)} {negm₀ u' : ℤ × ℤ} (hBfin : B.Finite) (hnegm₀_EB : negm₀ ∈ E B)
    (hdiru' : dir negm₀ = u') :
    ∀ z ∈ face B negm₀, dot u' (faceStart B negm₀) ≤ dot u' z :=
  hdiru' ▸ faceStart_min hBfin hnegm₀_EB

/-! ## Part 2: the three bridges -/

/-- Unconditional algebraic identity: `nuGen w = - dir w`. -/
theorem nuGen_eq_neg_dir (w : ℤ × ℤ) : nuGen w = - dir w := by
  simp [nuGen, dir]

/-- For `Prim w`, `genPerp' w = dir w` (the primitivisation is a no-op since `dir w` is
already primitive, `prim_dir_of_prim`). -/
theorem genPerp'_eq_dir_of_prim {w : ℤ × ℤ} (hw : Prim w) :
    Nivat.LE2.genPerp' w = dir w := by
  have hprimdir : Prim (dir w) := Nivat.LE2.prim_dir_of_prim hw
  unfold Nivat.LE2.genPerp' Nivat.LE2.genPerp Nivat.LE2.primPart
  have hg1 : Int.gcd (dir w).1 (dir w).2 = 1 := hprimdir
  simp [hg1]

theorem nuGen_eq_neg_genPerp'_of_prim {w : ℤ × ℤ} (hw : Prim w) :
    nuGen w = - Nivat.LE2.genPerp' w := by
  rw [genPerp'_eq_dir_of_prim hw, nuGen_eq_neg_dir]

/-- **Bridge 1** (`hnuGen_EB`): if `w0` is primitive and lane-tower's
`genPerp'_wgen_mem_E_B`-style fact puts both `± genPerp' w0` in `E B`, then `nuGen w0 ∈ E B`. -/
theorem hnuGen_EB_of_bridge {B : Set (ℤ × ℤ)} {w₀ : ℤ × ℤ} (hw₀_prim : Prim w₀)
    (hboth : Nivat.LE2.genPerp' w₀ ∈ E B ∧ - Nivat.LE2.genPerp' w₀ ∈ E B) :
    nuGen w₀ ∈ E B := by
  rw [nuGen_eq_neg_genPerp'_of_prim hw₀_prim]
  exact hboth.2

/-- Unconditional algebraic identity linking `dot (nuGen w) ·` to `det w ·`. -/
theorem dot_nuGen_eq_neg_det (w x : ℤ × ℤ) : dot (nuGen w) x = - det w x := by
  simp only [dot, det, nuGen]; ring

/-- **Bridge 2** (`hj_orth`): if lane-tower's `det_wgen_h_eq_zero`-style fact gives
`det w0 (h j0) = 0`, then `dot (nuGen w0) (h j0) = 0`. -/
theorem hj_orth_of_det_eq_zero {w x : ℤ × ℤ} (hdet0 : det w x = 0) :
    dot (nuGen w) x = 0 := by
  rw [dot_nuGen_eq_neg_det, hdet0, neg_zero]

/-- **Bridge 3a** (`h_u'_neg`): if lane-tower's `det_w_u'_sign_eq_of_hadjB`-style fact gives
`0 < det w0 u'`, then `dot (nuGen w0) u' < 0`. -/
theorem h_neg_of_det_pos {w x : ℤ × ℤ} (h : 0 < det w x) : dot (nuGen w) x < 0 := by
  rw [dot_nuGen_eq_neg_det]; linarith

/-- **Bridge 3b** (`h_vl_le`): if lane-tower's `det_w_u'_sign_eq_of_hadjB`-style fact gives
`0 ≤ det w0 vl`, then `dot (nuGen w0) vl ≤ 0`. -/
theorem h_le_of_det_nonneg {w x : ℤ × ℤ} (h : 0 ≤ det w x) : dot (nuGen w) x ≤ 0 := by
  rw [dot_nuGen_eq_neg_det]; linarith

/-! ## Part 3: wiring the bridges against `TowerConstruct.lean`'s real lemmas

`hnuGen_EB`/`hj_orth` are now derived directly from `genPerp'_wgen_mem_E_B`/
`det_wgen_h_eq_zero` (both landed) via Bridge 1/2 above. `h_vl_le` is derived from
`det_w_u'_sign_eq_of_hadjB` (landed) plus the single remaining binder `hdet_u'_pos`
(`0 < det w₀ u'`, equivalent to the old `h_u'_neg` binder up to the `dot_nuGen_eq_neg_det`
sign flip) — this genuinely eliminates the separate `h_vl_le` binder, since
`det_w_u'_sign_eq_of_hadjB` is an `iff` linking the signs of `det w₀ vl` and `det w₀ u'`.
`hdet_order`/`hno_between` (the fan-adjacency facts consumed by `b0pt_face_facts`) stay as
explicit binders, per team-lead's instruction, pending lane-tower's `no_between_extChain`. -/

open Nivat.ColleReg in
/-- **Bridges 1+2, wired.** `w₀ := wgen d nℓ j₀` for `j₀ ≠ i`: `nuGen w₀ ∈ E B` and
`dot (nuGen w₀) (d.h j₀) = 0`, both from landed `TowerConstruct.lean` facts. -/
theorem hnuGen_EB_and_hj_orth_wired {ξ : Nivat.Config ℤ} {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    {vl nℓ : ℤ × ℤ} (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) {j₀ : Fin d.m} (hij₀ : j₀ ≠ i) :
    nuGen (Nivat.ColleReg.wgen d nℓ j₀) ∈ E B ∧
    dot (nuGen (Nivat.ColleReg.wgen d nℓ j₀)) (d.h j₀) = 0 := by
  have hwprim : Prim (Nivat.ColleReg.wgen d nℓ j₀) :=
    Nivat.LE2.prim_iff_primitive.mpr (Nivat.ColleReg.wgen_prim d hvl_prim hprim hperp i hdoth hij₀)
  refine ⟨hnuGen_EB_of_bridge hwprim
      (Nivat.ColleReg.genPerp'_wgen_mem_E_B d hvl_prim hprim hperp henv i hdoth hij₀),
    hj_orth_of_det_eq_zero
      (Nivat.ColleReg.det_wgen_h_eq_zero d hvl_prim hprim hperp i hdoth hij₀)⟩

open Nivat.ColleReg in
/-- **Bridge 3, wired.** From the single binder `hdet_u'_pos : 0 < det w₀ u'` (replacing the
old separate `h_u'_neg`/`h_vl_le` pair), `det_w_u'_sign_eq_of_hadjB` extends the sign to `vl`,
giving both `dot (nuGen w₀) u' < 0` and `dot (nuGen w₀) vl ≤ 0`. -/
theorem h_u'_neg_and_h_vl_le_wired {ξ : Nivat.Config ℤ} {B : Set (ℤ × ℤ)} (d : Nivat.Colle35.DecompData ξ)
    {vl nℓ u' : ℤ × ℤ} (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : Nivat.LE2.EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : dot nℓ u' < 0)
    {j₀ : Fin d.m} (hij₀ : j₀ ≠ i) (hwu' : Nivat.ColleReg.wgen d nℓ j₀ ≠ u')
    (hdet_u'_pos : 0 < det (Nivat.ColleReg.wgen d nℓ j₀) u') :
    dot (nuGen (Nivat.ColleReg.wgen d nℓ j₀)) u' < 0 ∧
    dot (nuGen (Nivat.ColleReg.wgen d nℓ j₀)) vl ≤ 0 := by
  have hiff := Nivat.ColleReg.det_w_u'_sign_eq_of_hadjB d hvl_prim hprim hperp henv i hdoth
    hadjB hunimod hnu hij₀ hwu'
  have hdet_vl_pos : 0 < det (Nivat.ColleReg.wgen d nℓ j₀) vl := hiff.mpr hdet_u'_pos
  exact ⟨h_neg_of_det_pos hdet_u'_pos, h_le_of_det_nonneg (le_of_lt hdet_vl_pos)⟩

end Nivat.HsuppTowerBase

#print axioms Nivat.HsuppTowerBase.hnuGen_EB_and_hj_orth_wired
#print axioms Nivat.HsuppTowerBase.h_u'_neg_and_h_vl_le_wired
#print axioms Nivat.HsuppTowerBase.faceEnd_maxdir
#print axioms Nivat.HsuppTowerBase.b0pt_face_facts
#print axioms Nivat.HsuppTowerBase.b0pt_is_neg_u'_extreme
#print axioms Nivat.HsuppTowerBase.nuGen_eq_neg_dir
#print axioms Nivat.HsuppTowerBase.genPerp'_eq_dir_of_prim
#print axioms Nivat.HsuppTowerBase.nuGen_eq_neg_genPerp'_of_prim
#print axioms Nivat.HsuppTowerBase.hnuGen_EB_of_bridge
#print axioms Nivat.HsuppTowerBase.dot_nuGen_eq_neg_det
#print axioms Nivat.HsuppTowerBase.hj_orth_of_det_eq_zero
#print axioms Nivat.HsuppTowerBase.h_neg_of_det_pos
#print axioms Nivat.HsuppTowerBase.h_le_of_det_nonneg
