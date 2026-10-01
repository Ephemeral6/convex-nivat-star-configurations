/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.PolyChain
import Nivat.External.Colle.HsuppLengthBound

/-!
# `hsupp_tower_base` — the `I = 0` base case of `hbase`'s `B`-vertex induction

Lane `lane-hsupp`, dispatched by team-lead 2026-09-22.  Standalone file (per
team-lead's instruction: pasted here, not into `tmp/wip/TowerConstruct.lean`, which
lane-tower owns).

## Role mapping (team-lead's ruling, verbatim)

At `I = 0`, `Nivat.ColleReg.hrec_of_convex`
(`Nivat/External/Colle/CutRecConvex.lean:54`) is instantiated with:
`R := coneRegion B vl u'`, `m := m0` (perp `u'`, `dot m0 vl > 0`), `w := u'` (the base-level
edge direction, `hmw : dot m0 u' = 0`), `w' := wtower 0` (the stepping direction,
`hneg : dot m0 (wtower 0) < 0`), `nprev := nuGen j0` (outer normal of `B`'s edge arriving
at `b0pt`, in direction `wtower 0`).  `hpw' : dot nprev (wtower 0) <= 0` holds with
**equality** (`nprev` perp `wtower 0`), which is why `hrec_of_convex`'s `hpw'` was weakened
to `<=` (2026-09-22).  `vl` plays no role beyond extending `hprev` from `B` to
`B + N*vl + N*u'`.

This file supplies the four facts about `b0pt`/`nuGen j0` that assemble into `hprev`/`hpw`/
`hpw'` (and the `I = 1` corner-propagation export, fact (iii)).  It does **not** attempt the
`u'`-extreme-point derivation from first principles (that characterization lives with
`TowerConstruct`'s `hadjB`/`sortedCand` machinery, `tmp/wip/TowerConstruct.lean`); instead it
takes the geometric content it needs — that `b0pt` is the far endpoint of the
`nuGen w0`-face of `B` in the `w0`-direction, and the two `hadjB`-derived sign facts — as
explicit hypotheses, matching the parallel-lane protocol (`CLAUDE.md` par 并行协议: shared
objects get their properties stated as explicit assumptions traceable upstream).  At
integration, `w0` is `wtower d nl vl u' j0 0`, `nuGen w0` is lane-tower's `nuGen`/`dir_nuGen`
pairing, and `hb0pt_maxdir`/`h_u'_neg`/`h_vl_le` are consequences of `hadjB_of_hadj` +
`det_w_u'_sign_eq_of_hadjB` (`TowerConstruct.lean`).

`nuGen` here is defined directly via `dir` (not `genPerp'`) — `nuGen w := -dir w` satisfies
`dir (nuGen w) = w` unconditionally (`dir . dir = -id`), which is exactly what's needed to
read `wtower 0`'s direction off the face; for primitive `w` it agrees with
`genPerp' (-w) = -genPerp' w` up to the same sign convention lane-tower's `TowerConstruct.lean`
already uses (`genPerp'_eq_dir_of_prim`).

## Status

0 sorry, axiom-clean.
-/

set_option autoImplicit false

namespace Nivat.HsuppTowerBase

open Nivat Nivat.LE2 Nivat.PolyChain Nivat.HsuppLengthBound Nivat.Colle35

/-! ## Section 1. `nuGen`: read a normal off a direction via `dir` -/

/-- The outer normal whose `dir` is exactly `w`.  `dir (a,b) = (-b,a)`, so
`nuGen w := (w.2, -w.1) = -dir w` and `dir (nuGen w) = w` by `dir . dir = -id`. -/
def nuGen (w : ℤ × ℤ) : ℤ × ℤ := (w.2, -w.1)

theorem dir_nuGen (w : ℤ × ℤ) : Nivat.LE2.dir (nuGen w) = w := by
  simp [Nivat.LE2.dir, nuGen]

theorem dot_nuGen_self (w : ℤ × ℤ) : Nivat.LE2.dot (nuGen w) w = 0 := by
  simp only [Nivat.LE2.dot, nuGen]; ring

theorem nuGen_ne_zero {w : ℤ × ℤ} (hw : w ≠ 0) : nuGen w ≠ 0 := by
  intro hz
  apply hw
  have h1 : w.2 = 0 := congrArg Prod.fst hz
  have h2 : (-w.1 : ℤ) = 0 := congrArg Prod.snd hz
  have h2' : w.1 = 0 := by linarith
  exact Prod.ext h2' h1

theorem nuGen_prim {w : ℤ × ℤ} (hw : Nivat.LE2.Prim w) : Nivat.LE2.Prim (nuGen w) := by
  unfold Nivat.LE2.Prim nuGen at *
  simp only [Int.gcd, Int.natAbs_neg] at hw ⊢
  rw [Nat.gcd_comm]
  exact hw

/-! ## Section 2. The four base-case facts -/

/-- **`hbase` at `I = 0`, the four facts `hrec_of_convex` needs.**  See the module
docstring for the exact role mapping.  Read off `b0pt`'s membership in the
`nuGen w0`-face of `B` (`hb0pt_mem`) plus its `w0`-directional maximality
(`hb0pt_maxdir`, the standalone encoding of "`b0pt` is the far endpoint" / "`-u'`-extreme
among the `m0`-minimisers"), and the two `hadjB`-derived sign facts
(`h_u'_neg`, `h_vl_le`). -/
theorem hbase_base_case {ξ : Nivat.Config ℤ} (d : Nivat.Colle35.DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} (hBfin : B.Finite) (_hBne : B.Nonempty)
    (hBconv : Nivat.IsLatticeConvexRegion B)
    (hEeq : Nivat.LE2.E B = Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (hencard : ∀ n ∈ Nivat.LE2.E B,
      (Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤
        (Nivat.LE2.face B n).encard)
    {vl u' w₀ b₀pt : ℤ × ℤ} {j₀ : Fin d.toDecompData.m}
    (hw₀_ne : w₀ ≠ 0)
    (hnuGen_EB : nuGen w₀ ∈ Nivat.LE2.E B)
    (hj_orth : Nivat.LE2.dot (nuGen w₀) (d.toDecompData.h j₀) = 0)
    (hb₀pt_mem : b₀pt ∈ Nivat.LE2.face B (nuGen w₀))
    (hb₀pt_maxdir : ∀ z ∈ Nivat.LE2.face B (nuGen w₀),
      Nivat.LE2.dot w₀ z ≤ Nivat.LE2.dot w₀ b₀pt)
    (h_u'_neg : Nivat.LE2.dot (nuGen w₀) u' < 0)
    (h_vl_le : Nivat.LE2.dot (nuGen w₀) vl ≤ 0) :
    -- (i) `b₀pt` is the far endpoint (`faceEnd`) of `face B (nuGen w₀)` in direction `w₀`.
    (b₀pt = faceStart B (nuGen w₀) + (faceLen B (nuGen w₀) : ℤ) • Nivat.LE2.dir (nuGen w₀)) ∧
    -- (ii) support: `nuGen w₀` is maximized on `B` at `b₀pt`.
    (∀ z ∈ B, Nivat.LE2.dot (nuGen w₀) z ≤ Nivat.LE2.dot (nuGen w₀) b₀pt) ∧
    -- (iii) the other endpoint (`faceStart`) is `b₀pt` walked back `L` steps along `w₀`,
    -- and `L ≥ gcd (h j₀)`.
    (b₀pt - (faceLen B (nuGen w₀) : ℤ) • w₀ ∈ B ∧
      (Int.gcd (d.toDecompData.h j₀).1 (d.toDecompData.h j₀).2 : ℤ) ≤
        (faceLen B (nuGen w₀) : ℤ)) ∧
    -- (iv) the two `hadjB`-derived sign facts.
    (Nivat.LE2.dot (nuGen w₀) u' < 0 ∧ Nivat.LE2.dot (nuGen w₀) vl ≤ 0) := by
  set ν := nuGen w₀ with hνdef
  have hdirν : Nivat.LE2.dir ν = w₀ := dir_nuGen w₀
  -- (i): pin down which endpoint `b₀pt` is.
  obtain ⟨t, htle, hteq⟩ := (face_eq_segment hBconv hBfin hnuGen_EB) ▸ hb₀pt_mem
  have hend_mem : faceStart B ν + (faceLen B ν : ℤ) • Nivat.LE2.dir ν ∈ Nivat.LE2.face B ν :=
    faceEnd_mem hBconv hBfin hnuGen_EB
  have hmax_end := hb₀pt_maxdir _ hend_mem
  have hQpos : 0 < Nivat.LE2.dot w₀ w₀ := by
    have hor : w₀.1 ≠ 0 ∨ w₀.2 ≠ 0 := by
      by_contra hcon; push Not at hcon
      exact hw₀_ne (Prod.ext hcon.1 hcon.2)
    simp only [Nivat.LE2.dot]
    rcases hor with h1 | h2
    · have h1' := mul_self_pos.mpr h1
      nlinarith [mul_self_nonneg w₀.2]
    · have h2' := mul_self_pos.mpr h2
      nlinarith [mul_self_nonneg w₀.1]
  have hb0_val : Nivat.LE2.dot w₀ b₀pt
      = Nivat.LE2.dot w₀ (faceStart B ν) + (t : ℤ) * Nivat.LE2.dot w₀ w₀ := by
    rw [hteq, hdirν]
    simp only [Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  have hend_val : Nivat.LE2.dot w₀ (faceStart B ν + (faceLen B ν : ℤ) • Nivat.LE2.dir ν)
      = Nivat.LE2.dot w₀ (faceStart B ν)
        + (faceLen B ν : ℤ) * Nivat.LE2.dot w₀ w₀ := by
    rw [hdirν]
    simp only [Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  rw [hend_val, hb0_val] at hmax_end
  have htge : (faceLen B ν : ℤ) ≤ (t : ℤ) := by nlinarith
  have hteq' : t = faceLen B ν := by
    have hle2 : (t : ℤ) ≤ (faceLen B ν : ℤ) := by exact_mod_cast htle
    omega
  have hi : b₀pt = faceStart B ν + (faceLen B ν : ℤ) • Nivat.LE2.dir ν := by
    rw [hteq, hteq']
  refine ⟨hi, hb₀pt_mem.2, ?_, h_u'_neg, h_vl_le⟩
  constructor
  · have hshift : b₀pt - (faceLen B ν : ℤ) • w₀ = faceStart B ν := by
      rw [hi, hdirν]; abel
    rw [hshift]
    exact (Nivat.LE2.face_subset B ν) (faceStart_mem hBfin hnuGen_EB)
  · exact Nivat.HsuppLengthBound.faceLen_ge_gcd d hBfin _hBne hBconv hEeq hencard
      (nuGen_ne_zero hw₀_ne) hj_orth hnuGen_EB

end Nivat.HsuppTowerBase

#print axioms Nivat.HsuppTowerBase.hbase_base_case
#print axioms Nivat.HsuppTowerBase.dir_nuGen
#print axioms Nivat.HsuppTowerBase.nuGen_prim
