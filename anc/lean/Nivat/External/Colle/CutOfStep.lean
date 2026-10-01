/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ConeRegion

/-!
# Cut interface for stepped regions

**Source**: Team-lead calculation 2026-09-21, correcting tower top interface.

When R is closed under w'-stepping (up to m-level constraint), then
`(R + ℕ•w') ∩ {z | b₀ ≤ dot m z} = R`.

This replaces the incorrect `cut(R_inf, m, lev, 0) = R` assumption and validates
`hbase` in `L1Data` on concrete instances.

## Main results

* `cut_of_step_eq` - abstract set-theoretic characterization (proven)
* `hrec_coneRegion_nat` - the recursion condition for I=0 ℕ-cone case (proven)

-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.LE2 Nivat.ConeRegion

variable {R : Set (ℤ × ℤ)} {w' m : ℤ × ℤ} {b₀ : ℤ}

/-- **Cut interface via stepping recursion.**

If R satisfies:
- (hRlow) every point in R is above the m-level cutoff b₀
- (hrec) w'-stepping from R stays in R as long as above b₀

then `(R + ℕ•w') ∩ {b₀ ≤ dot m ·} = R`.

原文：Team-lead's H-representation argument, 2026-09-21.
-/
theorem cut_of_step_eq
    (hRlow : ∀ z ∈ R, b₀ ≤ dot m z)
    (hrec : ∀ z ∈ R, ∀ t : ℕ, b₀ ≤ dot m (z + t • w') → z + t • w' ∈ R) :
    {z | ∃ r ∈ R, ∃ t : ℕ, z = r + t • w'} ∩ {z | b₀ ≤ dot m z} = R := by
  ext z
  constructor
  · intro ⟨⟨r, hr, t, heq⟩, hz⟩
    rw [heq] at hz
    rw [heq]
    exact hrec r hr t hz
  · intro hz
    constructor
    · exact ⟨z, hz, 0, by simp⟩
    · exact hRlow z hz

/-- **Recursion condition for cone regions (ℕ-cone version, I=0).**

For `R = coneRegion B vl u'` where B lies in the ℕ-cone from base point b₀pt,
if `z ∈ R` and `z + k•w'` stays above the m-level, then `z + k•w' ∈ R`.

原文：Team-lead calculation 2026-09-21, I=0 case (unimodular).

When `(vl, u')` are unimodular and adjacent edge directions, B lies in the ℕ-cone
from their shared vertex b₀pt. The arithmetic:
- Any `z ∈ R` decomposes as `z = b₀pt + (a₀+s)•vl + (c₀+t)•u'` with a₀,c₀,s,t ∈ ℕ
- `w' = -α•vl + β•u'` (α,β > 0)
- `z + k•w' = b₀pt + ((a₀+s) - kα)•vl + ((c₀+t) + kβ)•u'`
- Level constraint: `dot m (z + k•w') ≥ b₀`
- Since `dot m u' = 0` and `dot m b₀pt = b₀`, this gives `((a₀+s) - kα)·(dot m vl) ≥ 0`
- With `dot m vl > 0`, we conclude `(a₀+s) - kα ≥ 0`
- Similarly `(c₀+t) + kβ ≥ 0` is automatic
- Therefore `z + k•w' = b₀pt + n_vl•vl + n_u'•u'` with n_vl, n_u' ∈ ℕ

**Hypotheses**:
- `hB_cone`: B ⊆ b₀pt + ℕ•vl + ℕ•u' (I=0 case)
- `hb0pt_mem`: b₀pt ∈ B (the shared vertex is in B)
- `hw'_neg_pos`: w' = -α•vl + β•u' with α,β > 0
- `hmu'`: dot m u' = 0 (m perpendicular to u'-direction)
- `hmvl_pos`: 0 < dot m vl (m sees vl-steps)
- `hb0pt_base`: dot m b₀pt = b₀ (base point at base level)
-/
theorem hrec_coneRegion_nat {B : Set (ℤ × ℤ)} {vl u' w' m : ℤ × ℤ} {b₀ : ℤ} {b₀pt : ℤ × ℤ}
    (hB_cone : ∀ b ∈ B, ∃ a c : ℕ, b = b₀pt + (a : ℤ) • vl + (c : ℤ) • u')
    (hb0pt_mem : b₀pt ∈ B)
    (hw'_neg_pos : ∃ α β : ℕ, 0 < α ∧ 0 < β ∧ w' = -(α : ℤ) • vl + (β : ℤ) • u')
    (hmu' : dot m u' = 0)
    (hmvl_pos : 0 < dot m vl)
    (hb0pt_base : dot m b₀pt = b₀)
    (z : ℤ × ℤ) (hz : z ∈ coneRegion B vl u')
    (k : ℕ) (hk : b₀ ≤ dot m (z + k • w')) :
    z + k • w' ∈ coneRegion B vl u' := by
  obtain ⟨b, hb, s, t, hz_eq⟩ := mem_coneRegion_iff.mp hz
  obtain ⟨α, β, hα_pos, hβ_pos, hw'⟩ := hw'_neg_pos
  obtain ⟨a₀, c₀, hb_eq⟩ := hB_cone b hb

  have hz_expand : z = b₀pt + ((a₀ + s) : ℤ) • vl + ((c₀ + t) : ℤ) • u' := by
    rw [hz_eq, hb_eq]; push_cast; module

  have target_form : z + (k : ℤ) • w' =
      b₀pt + ((a₀ + s : ℤ) - (k : ℤ) * (α : ℤ)) • vl +
             ((c₀ + t : ℤ) + (k : ℤ) * (β : ℤ)) • u' := by
    rw [hz_expand, hw']; simp only [smul_add, smul_neg, neg_smul, add_smul]; module

  have coeff_u'_nonneg : 0 ≤ (c₀ + t : ℤ) + (k : ℤ) * (β : ℤ) := by
    have hc₀ : 0 ≤ (c₀ : ℤ) := Nat.cast_nonneg _
    have ht : 0 ≤ (t : ℤ) := Nat.cast_nonneg _
    have hkb : 0 ≤ (k : ℤ) * (β : ℤ) := Int.mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    omega

  have level_target : dot m (z + (k : ℤ) • w') =
      b₀ + ((a₀ + s : ℤ) - (k : ℤ) * (α : ℤ)) * dot m vl := by
    rw [target_form]; simp only [dot_add, dot_smul_right, hmu', hb0pt_base]; ring

  have hk_expanded : b₀ ≤ b₀ + ((a₀ + s : ℤ) - (k : ℤ) * (α : ℤ)) * dot m vl := by
    rw [← level_target]; exact hk

  have coeff_vl_nonneg : 0 ≤ (a₀ + s : ℤ) - (k : ℤ) * (α : ℤ) := by
    by_contra h; push_neg at h
    have : ((a₀ + s : ℤ) - (k : ℤ) * (α : ℤ)) * dot m vl < 0 :=
      Int.mul_neg_of_neg_of_pos h hmvl_pos
    omega

  set n_vl := ((a₀ + s : ℤ) - (k : ℤ) * (α : ℤ)).toNat
  set n_u' := ((c₀ + t : ℤ) + (k : ℤ) * (β : ℤ)).toNat

  have hn_vl_eq : (n_vl : ℤ) = (a₀ + s : ℤ) - (k : ℤ) * (α : ℤ) :=
    Int.toNat_of_nonneg coeff_vl_nonneg
  have hn_u'_eq : (n_u' : ℤ) = (c₀ + t : ℤ) + (k : ℤ) * (β : ℤ) :=
    Int.toNat_of_nonneg coeff_u'_nonneg

  have : z + (k : ℤ) • w' = b₀pt + (n_vl : ℤ) • vl + (n_u' : ℤ) • u' := by
    rw [target_form, hn_vl_eq, hn_u'_eq]

  rw [mem_coneRegion_iff]
  exact ⟨b₀pt, hb0pt_mem, n_vl, n_u', this⟩

end Nivat.ColleReg
