/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.ConeHbase

/-!
# `chainFull` embeds into `coneRegion` at the `expNormal`-argmax seed

原文：b3_colle2.txt:806-818 (stage 2's `𝓡^n_I` cutting family)

**Why this is not trivial.** `Nivat.ConeHbase.not_chainFull_subset_coneRegion` (`ConeHbase.lean:208`)
proves the **unconditional** version is false: without the argmax hypothesis, `chainFull` can escape
`coneRegion`. The counterexample has `b₀` that is *not* `expNormal`-maximal in `B`, so the cutting
hyperplane at level `0` admits points with negative `vl`-coefficients (in the `fullSweep` expansion).

**What the argmax hypothesis buys.** When `b₀` maximizes `dot (expNormal u' vl) ·` over `B`, the
cutting condition `expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) z` forces the `vl`-coefficient `s`
in `z = b + s•vl + t•u'` to be nonnegative: `dot (expNormal u' vl) b₀ ≤ dot (expNormal u' vl) b + s`
(by unimodularity, `dot (expNormal u' vl) vl = 1` and `dot (expNormal u' vl) u' = 0`), and
`b₀` maximal forces `s ≥ 0`.

**The shear variant** (second theorem) handles the `u' ↦ u' - K•vl` base change (`:792`'s `φ_ι`
construction): the `u₂`-coefficient `t` stays nonnegative, and `K ≤ 0` ensures `-tK ≥ 0`, so
`z = b + (s - tK)•vl + t•u'` with both `s - tK ≥ 0` and `t ≥ 0`.

## Consumer

`RegionSteps.exists_stage2_frame_of_claim46` (`RegionSteps.lean:1412`) — stage 1 gives periodicity
on `coneRegion B vl u'`; stage 2 needs it on `chainFull … 0`. These two theorems bridge them.
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat.LE2 Nivat.ColleReg Nivat.ConeRegion Nivat.RegionSweep

/-- **`chainFull` at level `0` embeds into `coneRegion` when `b₀` is `expNormal`-maximal.**

原文：b3_colle2.txt:806-818

`chainFull B vl u' b₀ 0 = wedgeFull B vl u' ∩ {z | expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) z}`.
Writing `z = b + s•vl + t•u'` (with `b ∈ B`, `s : ℤ`, `t : ℕ` from `wedgeFull`), and using
`dot (expNormal u' vl) vl = 1` and `dot (expNormal u' vl) u' = 0` (by unimodularity), the
cutting condition becomes `dot (expNormal u' vl) b₀ ≤ dot (expNormal u' vl) b + s`.

Since `b₀` maximizes `dot (expNormal u' vl) ·` over `B`, we have
`dot (expNormal u' vl) b₀ ≤ dot (expNormal u' vl) b`, forcing `s ≥ 0`. Combined with `t ≥ 0`
from `wedgeFull`, this gives `z ∈ coneRegion B vl u'`. -/
theorem chainFull_zero_subset_coneRegion_of_argmax
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hb₀ : b₀ ∈ B)
    (hmax : ∀ b ∈ B, dot (expNormal u' vl) b ≤ dot (expNormal u' vl) b₀) :
    chainFull B vl u' b₀ 0 ⊆ coneRegion B vl u' := by
  intro z hz
  -- `z ∈ chainFull B vl u' b₀ 0` means `z ∈ wedgeFull B vl u'` and the cutting condition holds
  obtain ⟨hz_wedge, hz_cut⟩ := hz
  -- From `wedgeFull`, we have `z = b + s•vl + t•u'` for some `b ∈ B`, `s : ℤ`, `t : ℕ`
  obtain ⟨g, hg_full, t, rfl⟩ := hz_wedge
  obtain ⟨b, hb, s, rfl⟩ := mem_fullSweep_iff.mp hg_full
  -- The cutting condition: `expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) (b + s•vl + t•u')`
  have hlev : expLevel u' vl b₀ 0 = dot (expNormal u' vl) b₀ := by simp [expLevel]
  rw [hlev, halfPlaneGE, Set.mem_setOf_eq] at hz_cut
  -- Expand the dot product using linearity
  have hdot_expand : dot (expNormal u' vl) (b + (s : ℤ) • vl + (t : ℤ) • u') =
      dot (expNormal u' vl) b + s * dot (expNormal u' vl) vl + t * dot (expNormal u' vl) u' := by
    simp only [dot, zsmul_prod]
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  rw [hdot_expand] at hz_cut
  -- Use `dot (expNormal u' vl) vl = 1` and `dot (expNormal u' vl) u' = 0`
  have hdot_vl : dot (expNormal u' vl) vl = 1 := dot_expNormal_vl hunimod
  have hdot_u' : dot (expNormal u' vl) u' = 0 := dot_expNormal_u'
  rw [hdot_vl, hdot_u'] at hz_cut
  simp only [mul_one, mul_zero, add_zero] at hz_cut
  -- Now `hz_cut : dot (expNormal u' vl) b₀ ≤ dot (expNormal u' vl) b + s`
  -- Since `b₀` is maximal, `dot (expNormal u' vl) b ≤ dot (expNormal u' vl) b₀`
  have hmax_b : dot (expNormal u' vl) b ≤ dot (expNormal u' vl) b₀ := hmax b hb
  -- Therefore `s ≥ 0`
  have hs_nonneg : 0 ≤ s := by omega
  -- So we can write `s` as a natural number
  have ⟨s', hs'⟩ : ∃ s' : ℕ, s = (s' : ℤ) := ⟨s.toNat, (Int.toNat_of_nonneg hs_nonneg).symm⟩
  -- Now `z = b + s'•vl + t•u'` with `b ∈ B`, `s' : ℕ`, `t : ℕ`
  rw [hs']
  exact mem_coneRegion_iff.mpr ⟨b, hb, s', t, rfl⟩

/-- **Shear-invariant version**: `chainFull` at sheared base `u' - K•vl` embeds into
`coneRegion` at original base `u'` when `b₀` is `(u' - K•vl)`-argmax and `K ≤ 0`.

原文：b3_colle2.txt:792, :806-818

This handles the base change `u' ↦ u₂ := u' - K•vl` in the erased-generator zonotope construction.
Writing `z = b + s•vl + t•u₂` (from `chainFull B vl u₂ b₀ 0`) and rewriting
`u₂ = u' - K•vl`, we get `z = b + (s - tK)•vl + t•u'`.

The argmax condition on `expNormal u₂ vl = expNormal (u' - K•vl) vl` forces `s ≥ 0` (by the
first theorem's argument applied to `u₂`). Since `K ≤ 0` and `t ≥ 0`, we have `-tK ≥ 0`, so
`s - tK ≥ 0`. Combined with `t ≥ 0`, this gives `z ∈ coneRegion B vl u'`. -/
theorem chainFull_zero_subset_coneRegion_of_argmax_shear
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {K : ℤ} (hK : K ≤ 0)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hb₀ : b₀ ∈ B)
    (hmax : ∀ b ∈ B, dot (expNormal (u' - K • vl) vl) b
              ≤ dot (expNormal (u' - K • vl) vl) b₀) :
    chainFull B vl (u' - K • vl) b₀ 0 ⊆ coneRegion B vl u' := by
  intro z hz
  -- Use the first theorem to get `z ∈ coneRegion B vl (u' - K•vl)`
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    have : det (u' - K • vl) vl = det u' vl := by
      simp only [det, zsmul_prod, Prod.fst_sub, Prod.snd_sub]
      ring
    rw [this]
    exact hunimod
  have hz_cone : z ∈ coneRegion B vl (u' - K • vl) :=
    chainFull_zero_subset_coneRegion_of_argmax hunimod' hb₀ hmax hz
  -- Now rewrite to `coneRegion B vl u'`
  obtain ⟨b, hb, s, t, hz_eq⟩ := mem_coneRegion_iff.mp hz_cone
  -- Since `K ≤ 0`, we have `-K ≥ 0`, so `t * (-K) ≥ 0`, thus `s + t*(-K) ≥ 0`
  have h_nK : 0 ≤ -K := by omega
  have ht_nK : 0 ≤ (t : ℤ) * (-K) := Int.mul_nonneg (Int.natCast_nonneg t) h_nK
  have hs' : 0 ≤ (s : ℤ) + (t : ℤ) * (-K) := by
    have : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
    omega
  -- Express as a natural number
  obtain ⟨s', hs'_eq⟩ : ∃ s' : ℕ, (s : ℤ) + (t : ℤ) * (-K) = (s' : ℤ) :=
    ⟨((s : ℤ) + (t : ℤ) * (-K)).toNat, (Int.toNat_of_nonneg hs').symm⟩
  -- Prove `z = b + s'•vl + t•u'` using direct calculation
  have hz_final : z = b + (s' : ℤ) • vl + (t : ℤ) • u' := by
    -- From hz_eq: z = b + s•vl + t•(u' - K•vl)
    -- Expand: z = b + s•vl + t•u' - t•K•vl = b + (s - tK)•vl + t•u'
    have step1 : z = b + (s : ℤ) • vl + (t : ℤ) • u' - (t : ℤ) • (K • vl) := by
      calc z = b + (s : ℤ) • vl + (t : ℤ) • (u' - K • vl) := hz_eq
        _ = b + (s : ℤ) • vl + ((t : ℤ) • u' - (t : ℤ) • (K • vl)) := by rw [smul_sub]
        _ = b + ((s : ℤ) • vl + (t : ℤ) • u') - (t : ℤ) • (K • vl) := by abel
        _ = b + (s : ℤ) • vl + (t : ℤ) • u' - (t : ℤ) • (K • vl) := by abel
    have step2 : (t : ℤ) • (K • vl) = ((t : ℤ) * K) • vl := by simp only [smul_smul]
    rw [step2] at step1
    have step3 : b + (s : ℤ) • vl + (t : ℤ) • u' - ((t : ℤ) * K) • vl
        = b + ((s : ℤ) - (t : ℤ) * K) • vl + (t : ℤ) • u' := by
      rw [sub_smul]; abel
    rw [step3] at step1
    convert step1 using 2
    · congr 1
      have : (s : ℤ) - (t : ℤ) * K = (s : ℤ) + (t : ℤ) * (-K) := by ring
      rw [this, hs'_eq]
  rw [hz_final]
  exact mem_coneRegion_iff.mpr ⟨b, hb, s', t, rfl⟩

#print axioms chainFull_zero_subset_coneRegion_of_argmax
#print axioms chainFull_zero_subset_coneRegion_of_argmax_shear

/-- **T1: `chainFull R` embeds into `R` when `R` is invariant under `+ℤ•vl` and `+ℕ•u₂`.**

原文：b3_colle2.txt:806-820

`chainFull R vl u₂ b₀ 0 = wedgeFull R vl u₂ ∩ halfPlaneGE (expNormal u₂ vl) (expLevel u₂ vl b₀ 0)`.
Since `wedgeFull R vl u₂ = sweep (fullSweep R vl) u₂` and both `fullSweep` and `sweep` preserve
membership under the respective ray directions (`mem_fullSweep_iff` gives `∃ b ∈ R, ∃ k : ℤ, z = b + k•vl`;
`RegionSweep.mem_sweep` gives `∃ g ∈ fullSweep R vl, ∃ t : ℕ, z = g + t•u₂`), the hypotheses
`hRvl` and `hRu₂` force `wedgeFull R vl u₂ ⊆ R`. Intersecting with a half-plane only shrinks,
so `chainFull R vl u₂ b₀ 0 ⊆ R`. -/
theorem chainFull_zero_subset_of_invariant
    {R : Set (ℤ × ℤ)} {vl u₂ b₀ : ℤ × ℤ}
    (hRvl : ∀ z ∈ R, ∀ k : ℤ, z + k • vl ∈ R)
    (hRu₂ : ∀ z ∈ R, ∀ t : ℕ, z + (t : ℤ) • u₂ ∈ R) :
    chainFull R vl u₂ b₀ 0 ⊆ R := by
  intro z hz
  -- `chainFull R vl u₂ b₀ 0 = wedgeFull R vl u₂ ∩ halfPlaneGE ...`
  simp only [chainFull, Nivat.L1Region.cut] at hz
  obtain ⟨hz_wedge, _⟩ := hz
  -- `wedgeFull R vl u₂ = sweep (fullSweep R vl) u₂`
  simp only [wedgeFull] at hz_wedge
  -- From `sweep`, get `z = g + t•u₂` with `g ∈ fullSweep R vl`
  obtain ⟨g, hg_full, t, rfl⟩ := Nivat.RegionSweep.mem_sweep.mp hz_wedge
  -- From `fullSweep`, get `g = b + k•vl` with `b ∈ R`
  rw [mem_fullSweep_iff] at hg_full
  obtain ⟨b, hb, k, rfl⟩ := hg_full
  -- Now `z = b + k•vl + t•u₂ = (b + k•vl) + t•u₂`
  -- Apply `hRvl` to get `b + k•vl ∈ R`, then `hRu₂` to get `z ∈ R`
  have h1 : b + k • vl ∈ R := hRvl b hb k
  exact hRu₂ (b + k • vl) h1 t

#print axioms chainFull_zero_subset_of_invariant

/-- **T2 refutation: `coneRegion` is NOT invariant under `+ℤ•vl` (only `+ℕ•vl`).**

原文：b3_colle2.txt:806-820

Counterexample: `B = {(0,0)}`, `vl = (1,0)`, `u' = (0,1)`. Then `(0,0) ∈ coneRegion B vl u'`
(take `b = (0,0)`, `s = t = 0`). But `(0,0) + (-1)•(1,0) = (-1,0) ∉ coneRegion B vl u'` because
`mem_coneRegion_iff` would require `(-1,0) = (0,0) + s•(1,0) + t•(0,1)` for some `s, t : ℕ`,
which gives `(-1,0) = (s, t)` — impossible since `s : ℕ`.

This means **`R := coneRegion B vl u'` does not satisfy `chainFull_zero_subset_of_invariant`'s
`hRvl` hypothesis**. The honest options are (a) enlarge `R` to `fullSweep`-style `B + ℤ•vl + ℕ•u'`
and verify periodicity survives, or (b) abandon `PeriodOn.mono` on this route. -/
theorem not_coneRegion_zsmul_vl_mem :
    ∃ (B : Set (ℤ × ℤ)) (vl u' z : ℤ × ℤ) (k : ℤ),
      z ∈ coneRegion B vl u' ∧ z + k • vl ∉ coneRegion B vl u' := by
  -- Witness: B = {(0,0)}, vl = (1,0), u' = (0,1), z = (0,0), k = -1
  refine ⟨{(0, 0)}, (1, 0), (0, 1), (0, 0), -1, ?_, ?_⟩
  · -- (0,0) ∈ coneRegion {(0,0)} (1,0) (0,1)
    rw [mem_coneRegion_iff]
    exact ⟨(0, 0), Set.mem_singleton _, 0, 0, rfl⟩
  · -- (0,0) + (-1)•(1,0) = (-1,0) ∉ coneRegion {(0,0)} (1,0) (0,1)
    simp only [zsmul_prod, Int.reduceNeg, Prod.mk_add_mk, zero_add]
    -- Need to show (-1, 0) ∉ coneRegion {(0,0)} (1,0) (0,1)
    intro h
    rw [mem_coneRegion_iff] at h
    obtain ⟨b, hb, s, t, heq⟩ := h
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    -- Now heq : (-1, 0) = (0, 0) + s•(1, 0) + t•(0, 1)
    simp only [zsmul_prod, Prod.mk_add_mk, zero_add] at heq
    -- Expand: (-1, 0) = (s * 1 + t * 0, s * 0 + t * 1) = (s, t)
    simp only [mul_one, mul_zero, add_zero, zero_add] at heq
    -- Extract the first component: -1 = s
    have h1 : (-1 : ℤ) = (s : ℤ) := congr_arg Prod.fst heq
    -- But s : ℕ implies s ≥ 0, contradiction
    omega

#print axioms not_coneRegion_zsmul_vl_mem

end Nivat.ColleReg

