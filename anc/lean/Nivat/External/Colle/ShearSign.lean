/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1StraddleWedge
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.L1Line0
import Nivat.External.Colle.ConeRegion

/-!
# Shear sign decision for corner condition

Lane Hcorner's file (exclusive, 2026-09-20). Proves that the corner condition with `K ≤ 0`
does not exist universally.

Original text: b3_colle2.txt:790-804 (placement step), :806-818 (sweep induction boundary).

**Why this matters:** `wedgeFull` is shear-invariant but `coneRegion` is not. The inclusion
`chainFull B vl u₂ b₀ 0 ⊆ coneRegion B vl u'` requires `K ≤ 0` when `b₀` is the
`expNormal u₂ vl`-maximizer. This theorem establishes the boundary between the `m = 2`
degenerate case (where `K = 0` corner may exist) and `m ≥ 3` (where b3_colle2.txt:800-806
sweep induction is required).

Consumer: `RegionSteps.exists_stage2_frame_of_claim46` (`RegionSteps.lean:1412`).
-/

set_option autoImplicit false

namespace Nivat.ShearSign

open Nivat.LE2 Nivat.ColleReg Nivat.L1Line0 Nivat.L1StraddleWedge Nivat.ConeRegion

variable {u' vl : ℤ × ℤ}

/-! ## Coordinate computations for the witness

Fix `vl = (1,1)` (a genuine edge direction of `S`) and `u' = (1,0)`. For any `K`,
the sheared basis `u₂ = u' - K•vl = (1-K, -K)` satisfies:
- `det u₂ vl = 1` (unimodular for all `K`)
- `expNormal u₂ vl = (K, 1-K)`
- `uCoord u₂ vl a b = (b - a).1 - (b - a).2` (independent of `K`)

These closed forms make the case analysis mechanical.

Original text: b3_colle2.txt:790-804. -/

private theorem det_witness (K : ℤ) : det ((1, 0) - K • (1, 1)) (1, 1) = 1 := by
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

private theorem expNormal_witness (K : ℤ) :
    expNormal (((1 : ℤ), (0 : ℤ)) - K • ((1 : ℤ), (1 : ℤ))) ((1 : ℤ), (1 : ℤ)) =
      (K, (1 : ℤ) - K) := by
  simp only [expNormal, det_witness, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.fst_sub, Prod.snd_sub]
  ext <;> ring

private theorem uCoord_witness (K : ℤ) (a b : ℤ × ℤ) :
    uCoord (((1 : ℤ), (0 : ℤ)) - K • ((1 : ℤ), (1 : ℤ))) ((1 : ℤ), (1 : ℤ)) a b =
      (b - a).1 - (b - a).2 := by
  simp only [uCoord, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, det]
  ring

/-! ## Main theorem: Non-positive shear corner does not exist universally

Witness: `S = {(0,0), (1,1), (1,-1), (2,0)}` (the zonotope `supp((X^{h₁}-1)(X^{h₂}-1))`
for `h₁ = (1,1)`, `h₂ = (1,-1)`, a genuine `m = 2` case of `𝒮_φ`).
Frame: `vl = (1,1)` is a genuine edge direction of `S`; `u' = (1,0)` with `det u' vl = 1`.

For any `K ≤ 0`, the corner condition fails:
- `uCoord ≥ 0` on `{(1,-1), (2,0)}` forces `a ∈ {(0,0), (1,1)}`
- `a = (1,-1)`: `uCoord` at `b = (0,0)` is `-2 < 0`
- `a = (2,0)`: `uCoord` at `b = (0,0)` is `-2 < 0`
- `a = (0,0)`: `expNormal` inequality at `b = (1,-1)` requires `2K - 1 ≥ 0`, i.e. `K ≥ 1`
- `a = (1,1)`: `expNormal` inequality at `b = (0,0)` requires `-1 ≥ 0`

Original text: b3_colle2.txt:790-804. -/
theorem not_exists_nonpos_shear_corner :
    ∃ (vl u' : ℤ × ℤ) (S : Finset (ℤ × ℤ)),
      S.Nonempty ∧ (det u' vl = 1 ∨ det u' vl = -1) ∧
      ∀ K : ℤ, K ≤ 0 →
        ¬ ∃ a ∈ S, ∀ b ∈ S,
          0 ≤ dot (expNormal (u' - K • vl) vl) (b - a) ∧
            0 ≤ uCoord (u' - K • vl) vl a b := by
  use (1, 1), (1, 0), {(0, 0), (1, 1), (1, -1), (2, 0)}
  refine ⟨?_, ?_, fun K hK => ?_⟩
  · exact ⟨(0, 0), by simp⟩
  · left
    simp only [det]
    ring
  · intro ⟨a, ha, hcorner⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · -- Case a = (0,0): expNormal fails at b = (1,-1) when K ≤ 0
      have hb := hcorner (1, -1) (by simp)
      rw [expNormal_witness] at hb
      simp only [dot, Prod.fst_sub, Prod.snd_sub] at hb
      -- hb: 0 ≤ K*(1-0) + (1-K)*(-1-0) = 2K - 1
      omega
    · -- Case a = (1,1): expNormal fails at b = (0,0)
      have hb := hcorner (0, 0) (by simp)
      rw [expNormal_witness] at hb
      simp only [dot, Prod.fst_sub, Prod.snd_sub] at hb
      -- hb: 0 ≤ K*(0-1) + (1-K)*(0-1) = -1
      omega
    · -- Case a = (1,-1): uCoord fails at b = (0,0)
      have := hcorner (0, 0) (by simp)
      rw [uCoord_witness] at this
      simp at this
    · -- Case a = (2,0): uCoord fails at b = (0,0)
      have := hcorner (0, 0) (by simp)
      rw [uCoord_witness] at this
      simp at this

#print axioms not_exists_nonpos_shear_corner

/-! ## Necessity: the inclusion forces non-positive shear

The inclusion `chainFull B vl u₂ b₀ 0 ⊆ coneRegion B vl u'` forces `K ≤ 0`.

**Proof sketch:**
1. The ray `z t := b₀ + t•u₂` lies entirely in `chainFull ... 0` (by construction of `chainFull`
   as a cut of `wedgeFull`, and `dot (expNormal u₂ vl) u₂ = 0`).
2. The inclusion forces each `z t ∈ coneRegion B vl u'`, so `z t = b + s•vl + r•u'` for some
   `b ∈ B`, `s r : ℕ`.
3. Apply `dot (expNormal u' vl) ·`: LHS is `dot en b₀ - t*K`, RHS is `≥ m` where `m` is the
   lower bound of `dot en` on the finite set `B`.
4. If `K ≥ 1`, pick `t` large enough to make LHS `< m`, contradiction.

Original text: b3_colle2.txt:790-804. -/
theorem nonpos_shear_of_chainFull_subset
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {K : ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hBfin : B.Finite) (hb₀ : b₀ ∈ B)
    (hsub : chainFull B vl (u' - K • vl) b₀ 0 ⊆
      coneRegion B vl u') :
    K ≤ 0 := by
  -- Step 1: construct the ray z t = b₀ + t•u₂ inside chainFull
  set u₂ := u' - K • vl
  set en₂ := expNormal u₂ vl
  set en := expNormal u' vl

  -- Step 2: obtain lower bound m for dot en on B
  obtain ⟨m, hm⟩ : ∃ m : ℤ, ∀ b ∈ B, m ≤ dot en b := by
    have hne : hBfin.toFinset.Nonempty := by
      rw [Set.Finite.toFinset_nonempty]
      exact ⟨b₀, hb₀⟩
    obtain ⟨b_min, hb_min, hmin⟩ := hBfin.toFinset.exists_min_image (dot en) hne
    use dot en b_min
    intro b hb
    have hb' : b ∈ hBfin.toFinset := by simp [hb]
    exact hmin b hb'

  -- Step 3: derive contradiction from K ≥ 1
  by_contra hpos
  push_neg at hpos
  -- hpos: 1 ≤ K

  -- Choose t large enough
  set t := (dot en b₀ - m + 1).natAbs
  have ht_pos : 0 < dot en b₀ - m + 1 := by
    have := hm b₀ hb₀
    omega
  have ht_bound : (t : ℤ) ≥ dot en b₀ - m + 1 := by
    simp only [t]
    rw [Int.natAbs_of_nonneg (Int.le_of_lt ht_pos)]

  -- The point z t
  set z := b₀ + (t : ℤ) • u₂

  -- z t ∈ chainFull (Step 1 detail)
  have hz_wedge : z ∈ wedgeFull B vl u₂ := by
    rw [Nivat.ColleReg.wedgeFull, Nivat.RegionSweep.mem_sweep]
    use b₀ + 0 • vl, ?_, t
    · simp [z]
    · rw [Nivat.ColleReg.mem_fullSweep_iff]
      exact ⟨b₀, hb₀, 0, by simp⟩

  have hz_level : dot en₂ z = dot en₂ b₀ := by
    simp only [z, dot_add, dot_zsmul]
    have : dot en₂ u₂ = 0 := by
      rw [Nivat.ColleReg.dot_expNormal_u']
    rw [this]
    simp [u₂]

  have hz_chain : z ∈ chainFull B vl u₂ b₀ 0 := by
    rw [Nivat.ColleReg.chainFull, Nivat.L1Region.cut]
    refine ⟨hz_wedge, ?_⟩
    simp only [Nivat.ColleReg.expLevel]
    unfold Nivat.LE2.halfPlaneGE
    simp only [Set.mem_ofPred_eq]
    rw [← hz_level]
    simp [en₂]

  -- Push through hsub
  have hz_cone := hsub hz_chain
  rw [mem_coneRegion_iff] at hz_cone
  obtain ⟨b, hb, s, r, hzb⟩ := hz_cone

  -- Apply dot en
  have hdot_vl : dot en vl = 1 := dot_expNormal_vl hunimod
  have hdot_u' : dot en u' = 0 := by
    rw [Nivat.ColleReg.dot_expNormal_u']

  have hRHS : dot en b + (s : ℤ) ≥ m := by
    have := hm b hb
    calc dot en b + (s : ℤ)
        ≥ dot en b := by omega
      _ ≥ m := this

  have hLHS : dot en z = dot en b₀ - (t : ℤ) * K := by
    simp only [z, dot_add, dot_zsmul, u₂]
    rw [dot_sub, dot_zsmul, hdot_u', hdot_vl]
    ring

  rw [hzb] at hLHS
  simp only [dot_add] at hLHS

  -- hLHS: dot en b₀ - t*K = dot en b + s
  have heq : dot en b₀ - (t : ℤ) * K = dot en b + (s : ℤ) := by
    have h1 : dot en ((s : ℤ) • vl) = (s : ℤ) * dot en vl := dot_zsmul _ _ _
    have h2 : dot en ((r : ℤ) • u') = (r : ℤ) * dot en u' := dot_zsmul _ _ _
    rw [h1, h2, hdot_vl, hdot_u'] at hLHS
    linarith

  -- Contradiction: LHS < m but RHS ≥ m
  have hcontra : dot en b₀ - (t : ℤ) * K < m := by
    have h1 : (t : ℤ) * K ≥ (t : ℤ) * 1 := by
      apply Int.mul_le_mul_of_nonneg_left hpos
      omega
    have h2 : (t : ℤ) * 1 = (t : ℤ) := by ring
    calc dot en b₀ - (t : ℤ) * K
        ≤ dot en b₀ - (t : ℤ) := by omega
      _ ≤ dot en b₀ - (dot en b₀ - m + 1) := by omega
      _ = m - 1 := by ring
      _ < m := by omega

  rw [heq] at hcontra
  omega

#print axioms nonpos_shear_of_chainFull_subset

#print axioms not_exists_nonpos_shear_corner

end Nivat.ShearSign
