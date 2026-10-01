/-
Copyright (c) 2026 Nivat contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nivat contributors
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.ConeRegion

open Nivat.ConeRegion (dot_zsmul)

/-!
# Strip step via corner placement and downward closure

原文：b3_colle2.txt:786-804 + Figure 10.

Consumer: RegionSteps.lean:2590 `hstrip` (hole 6).

## Why it holds (hard rule 10)

Three named premises, each anchored to the paper:
- **`hplace`**: 原文 b3_colle2.txt:798 — Figure 10's placement: when Ŝ_{φ_ι} is
  translated so its extreme vertex sits at B's corner b₀, the translate lands in H_B(ℓ).
- **`hdown`**: 原文 b3_colle2.txt:786 — 𝓡_{ι−1} is a (-ℓ, ℓ_{ι−1})-region with two
  half-infinite edges, hence closed downward along u' (as long as we don't drop below cz).
- **`hBcorner`**: 原文 b3_colle2.txt:798 — B has a left-bottom corner b₀; every point
  of B lies in the first quadrant relative to b₀ in the (vl, -u') coordinates.

The arithmetic: w = b + s•vl + t•u' where b = b₀ + A•vl - C•u' (C ≥ 0). Then
dot nℓ w = cz + C - t < cz forces C < t, so z + (w - a₀) = (b₀ + (z - a₀)) + (A+s)•vl + (t-C)•u'
is reached by: start at b₀ + (z - a₀) ∈ halfStrip (by hplace), add (A+s)•vl (stays in halfStrip),
walk down t - C > 0 steps via hdown.

-/

set_option autoImplicit false

namespace Nivat.StripPlace

open Nivat.LE2 (dot halfStrip)
open Nivat.ConeRegion (coneRegion)

variable {B : Set (ℤ × ℤ)} {Sw : Finset (ℤ × ℤ)} {vl u' nℓ a₀ b₀ : ℤ × ℤ} {cz : ℤ}

/-- Helper: halfStrip is closed under adding ℕ • vl. -/
theorem halfStrip_add_smul_vl {g : ℤ × ℤ} {k : ℤ} (hk : 0 ≤ k) :
    g ∈ halfStrip B vl → g + k • vl ∈ halfStrip B vl := by
  intro ⟨b, hb, t, hg⟩
  obtain ⟨k_nat, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  refine ⟨b, hb, t + k_nat, ?_⟩
  rw [hg]; push_cast; rw [add_smul]; abel

/-- Helper: walking down along u'. -/
theorem halfStrip_iterate_down (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hb₀cz : dot nℓ b₀ = cz)
    (hdown : ∀ g ∈ halfStrip B vl, cz ≤ dot nℓ (g + u') → g + u' ∈ halfStrip B vl)
    (g : ℤ × ℤ) (hg : g ∈ halfStrip B vl) (d : ℕ)
    (hlev : cz ≤ dot nℓ g - d) :
    g + (d : ℤ) • u' ∈ halfStrip B vl := by
  induction d with
  | zero => simp; exact hg
  | succ d' ih =>
    have h_step : g + (d' : ℤ) • u' ∈ halfStrip B vl := ih (by omega)
    have h_next_lev : cz ≤ dot nℓ (g + (d' : ℤ) • u' + u') := by
      have : dot nℓ (g + (d' : ℤ) • u' + u') = dot nℓ g + (d' : ℤ) * dot nℓ u' + dot nℓ u' := by
        unfold dot; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [this, hnu]; omega
    rw [Nat.cast_succ, add_smul, one_smul, ← add_assoc]
    exact hdown _ h_step h_next_lev

/-- **Strip step from corner placement and downward closure.**

原文：b3_colle2.txt:786-804

When a window translate z + (w - a₀) crosses the cut line (from below cz to ≥ cz),
it lands in halfStrip B vl by: decompose w into corner + horizontal + downward steps,
apply hplace at the corner, close under +ℕvl horizontally, walk down via hdown. -/
theorem stripStep_of_corner_of_place
    (hperp : dot nℓ vl = 0)
    (hnu : dot nℓ u' = -1)
    (hcz : ∀ b ∈ B, cz ≤ dot nℓ b)
    (hb₀ : b₀ ∈ B)
    (hb₀cz : dot nℓ b₀ = cz)
    (hBcorner : ∀ b ∈ B, ∃ A C : ℤ, 0 ≤ A ∧ 0 ≤ C ∧ b = b₀ + A • vl - C • u')
    (hplace : ∀ z ∈ Sw, b₀ + (z - a₀) ∈ halfStrip B vl)
    (hdown : ∀ g ∈ halfStrip B vl, cz ≤ dot nℓ (g + u') → g + u' ∈ halfStrip B vl) :
    ∀ w ∈ coneRegion B vl u', dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ halfStrip B vl := by
  intro w hw hwlev z hz hzcross
  -- Decompose w as b + s•vl + t•u'
  rw [Nivat.ConeRegion.mem_coneRegion_iff] at hw
  obtain ⟨b, hb, s, t, rfl⟩ := hw
  -- Decompose b as b₀ + A•vl - C•u'
  obtain ⟨A, C, hA, hC, rfl⟩ := hBcorner b hb
  -- Key: dot nℓ w = cz + C - t < cz forces C < t
  have hwlevel : dot nℓ (b₀ + A • vl - C • u' + (s : ℤ) • vl + (t : ℤ) • u')
      = cz + C - t := by
    have : dot nℓ (b₀ + A • vl - C • u' + (s : ℤ) • vl + (t : ℤ) • u')
        = dot nℓ b₀ + A * dot nℓ vl + (-(C : ℤ)) * dot nℓ u'
          + (s : ℤ) * dot nℓ vl + (t : ℤ) * dot nℓ u' := by
      unfold dot; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
    rw [this, hb₀cz, hperp, hnu]; ring
  rw [hwlevel] at hwlev
  have hClt : C < t := by omega
  have htC_pos : 0 < t - C := Int.sub_pos_of_lt hClt
  -- Target: z + (w - a₀) = (b₀ + (z - a₀)) + (A+s)•vl + (t-C)•u'
  suffices b₀ + (z - a₀) + (A + (s : ℤ)) • vl + ((t : ℤ) - C) • u' ∈ halfStrip B vl by
    convert this using 1
    simp only [sub_smul, add_smul]
    abel
  -- Step 1: b₀ + (z - a₀) ∈ halfStrip
  have h1 : b₀ + (z - a₀) ∈ halfStrip B vl := by
    have : z ∈ Sw := Finset.erase_subset _ _ hz
    exact hplace z this
  -- Step 2: add (A+s)•vl
  have h2 : b₀ + (z - a₀) + (A + (s : ℤ)) • vl ∈ halfStrip B vl :=
    halfStrip_add_smul_vl (by omega) h1
  -- Step 3: walk down (t - C) steps
  have hlev2 : dot nℓ (b₀ + (z - a₀) + (A + (s : ℤ)) • vl) = cz + dot nℓ (z - a₀) := by
    have : dot nℓ (b₀ + (z - a₀) + (A + (s : ℤ)) • vl)
        = dot nℓ b₀ + dot nℓ (z - a₀) + (A + (s : ℤ)) * dot nℓ vl := by
      unfold dot; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
    rw [this, hb₀cz, hperp]; ring
  obtain ⟨d_nat, hd_nat⟩ := Int.eq_ofNat_of_zero_le (le_of_lt htC_pos)
  rw [hd_nat]
  apply halfStrip_iterate_down hperp hnu hb₀cz hdown _ h2 d_nat
  have hzcross' : cz ≤ dot nℓ (z - a₀) + (cz + C - t) := by
    have : dot nℓ (z + (b₀ + A • vl - C • u' + (s : ℤ) • vl + (t : ℤ) • u' - a₀))
        = dot nℓ z + dot nℓ b₀ + A * dot nℓ vl - C * dot nℓ u'
          + (s : ℤ) * dot nℓ vl + (t : ℤ) * dot nℓ u' - dot nℓ a₀ := by
      unfold dot; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
    rw [this, hb₀cz, hperp, hnu] at hzcross
    have : dot nℓ (z - a₀) = dot nℓ z - dot nℓ a₀ := by
      unfold dot; simp only [Prod.fst_sub, Prod.snd_sub]; ring
    rw [this]; omega
  omega

#check stripStep_of_corner_of_place

end Nivat.StripPlace

#print axioms Nivat.StripPlace.stripStep_of_corner_of_place
#print axioms Nivat.StripPlace.halfStrip_add_smul_vl
#print axioms Nivat.StripPlace.halfStrip_iterate_down
