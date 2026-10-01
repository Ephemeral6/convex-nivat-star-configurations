/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Region
import Nivat.External.Colle.L1Cut
import Nivat.External.Colle.Lemma41
import Nivat.External.Colle.RegionTranslate
import Nivat.External.Colle.CutLevels
import Nivat.External.Colle.RecessionCone

/-!
# L1 Line Package (Claim 4.7 window placement)

Lane: lane-place (2026-09-22)

## Target

`RegionSteps.lean:1734-1740`, the second `obtain` in `exists_cutResidualR_of_claim46`.
Named `Nivat.L1LinePackage.exists_line_package`.

## Paper

原文：b3_colle2.txt:822-852 (Claim 4.7, Figure 11(A)).

## Quantifier order (team-lead ruling, 2026-09-22)

`∃ v τ ε, ∀ N` is CORRECT. By PeriodOn.mono (Lemma41.lean:662) and cut antitone,
the breaking index N₀ is UNIQUE (or does not exist). Use Classical.choose to obtain N₀ first,
then select v τ ε for that fixed N₀.

## Geometry (team-lead ruling, 2026-09-22)

`Colle41.IsRegion Rinf vl w` provides IsLatticeConvexRegion + two rays.
With det vl w ≠ 0, `exists_translate_mem` (RegionTranslate.lean:82) gives:
  ∀ finite W, ∃ b, ∀ z ∈ W, b + z ∈ Rinf.

Since dot m vl > 0 and dot m w = 0, translating along vl increases m-height.
Use `recession_of_ray` to push along vl direction: it gives `∀ z ∈ Rinf, z + vl ∈ Rinf`
directly from any one ray `RayIn Rinf z₀ vl` — no need for the ray to start at our point.

`derivedQ ε w S₁ ⊆ S₁` by filter definition (L1Cut.lean:98-99).
-/

set_option autoImplicit false

namespace Nivat.L1LinePackage

open Nivat Nivat.Colle Nivat.Colle35 Nivat.Colle41 Nivat.ColleReg
open Nivat.ColleReg.L1Data Nivat.L1Region Nivat.LE2

variable {ξ : Config ℤ} {vl : ℤ × ℤ}

/-- derivedQ is a subset of the original set. -/
theorem derivedQ_subset (ε : Bool) (w : ℤ × ℤ) (S : Finset (ℤ × ℤ)) :
    L1Data.derivedQ ε w S ⊆ S := by
  unfold L1Data.derivedQ
  exact Finset.filter_subset _ _

/-- `dot m` distributes over `ℤ`-smul in the second argument. -/
theorem dot_zsmul_right (m z : ℤ × ℤ) (k : ℤ) : LE2.dot m (k • z) = k * LE2.dot m z := by
  simp only [LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Claim 4.7: Line package existence for L1 Case 1.

原文：b3_colle2.txt:822-852

Given a region Rinf with descending cuts and non-periodicity on the full region,
we produce v τ ε such that for ANY breaking point N (unique by monotonicity),
the translated window S + v and its derivedQ land in cut N after adding c•vl.

Quantifier order `∃ v τ ε, ∀ N` works because:
1. By PeriodOn.mono and cut antitone, the breaking point N₀ is unique if it exists.
2. Classical.choose obtains N₀ first (or determines no breaking point).
3. We then select v τ ε specifically for that N₀.

Geometry: IsRegion provides lattice-convexity + rays. exists_translate_mem guarantees
Rinf contains translates. recession_of_ray shows lattice-convex + ray ⟹ closed under +vl.
-/
theorem exists_line_package
    {e : ℤ × ℤ} {c : ℤ} {S : Finset (ℤ × ℤ)}
    (Rinf : Set (ℤ × ℤ))
    (w : ℤ × ℤ) (hw_det : det vl w ≠ 0) (hw_prim : Primitive w)
    (m : ℤ × ℤ) (hmw : LE2.dot m w = 0) (hmvl : 0 < LE2.dot m vl)
    (lev : ℕ → ℤ) (b₀ : ℤ)
    (hlev0 : lev 0 = b₀)
    (hlev : Antitone lev)
    (hexh : ∀ b : ℤ, ∃ n : ℕ, lev n ≤ b)
    (hgap : ∀ n : ℕ, ∃ z ∈ Rinf, lev (n + 1) ≤ LE2.dot m z ∧ LE2.dot m z < lev n)
    (hR : Nivat.Colle41.IsRegion Rinf vl w)
    (hc : 0 < c)
    (hvl_prim : Primitive vl)
    (hinf : ¬ PeriodOn (T e ξ) Rinf (c • vl)) :
    ∃ (v : ℤ × ℤ) (τ : ℤ) (ε : Bool), ∀ (N : ℕ),
      PeriodOn (T e ξ) (L1Region.cut Rinf m lev N) (c • vl) →
      ¬ PeriodOn (T e ξ) (L1Region.cut Rinf m lev (N + 1)) (c • vl) →
      ∀ z ∈ L1Data.derivedQ ε w (S.image (· + v)),
        τ • w + z ∈ L1Region.cut Rinf m lev N ∧
        τ • w + z + c • vl ∈ L1Region.cut Rinf m lev N := by

  -- Extract components from IsRegion
  obtain ⟨hRconv, ⟨z₀, hz₀⟩, ⟨z₀', hz₀'⟩⟩ := hR

  -- recession_of_ray: lattice-convex + ray ⟹ ∀ z ∈ R, z + vl ∈ R
  have hstep : ∀ z ∈ Rinf, z + vl ∈ Rinf :=
    Nivat.RecessionCone.recession_of_ray hRconv hz₀

  -- Extend to arbitrary k•vl translations
  have hpush : ∀ z ∈ Rinf, ∀ k : ℕ, z + (k : ℤ) • vl ∈ Rinf := by
    intro z hz k
    induction k with
    | zero => simpa using hz
    | succ k ih =>
        have heq : z + ((k + 1 : ℕ) : ℤ) • vl = z + (k : ℤ) • vl + vl := by
          push_cast
          rw [add_smul, one_smul]
          abel
        rw [heq]
        exact hstep _ ih

  -- Classical choice: breaking point exists or not
  by_cases hexists : ∃ N, PeriodOn (T e ξ) (L1Region.cut Rinf m lev N) (c • vl) ∧
                            ¬ PeriodOn (T e ξ) (L1Region.cut Rinf m lev (N + 1)) (c • vl)

  · -- Case 1: Breaking point exists
    let N₀ := Classical.choose hexists
    have hN₀ := Classical.choose_spec hexists
    obtain ⟨hN₀_per, hN₀_not⟩ := hN₀

    -- exists_translate_mem: Rinf contains a translate of S
    obtain ⟨b₀, hb₀⟩ := Nivat.ColleReg.exists_translate_mem hRconv hz₀ hz₀' hw_det S

    by_cases hS : S.Nonempty
    · -- S nonempty: push b₀ + S high enough along vl

      -- Minimum m-height of S
      obtain ⟨z_min, hz_min, hmin⟩ := Finset.exists_min_image S (LE2.dot m) hS

      -- Choose k: dot m b₀ + dot m z_min + k * dot m vl ≥ lev N₀ + c * dot m vl
      have hk_ex : ∃ k : ℕ,
          lev N₀ + c * LE2.dot m vl ≤
            LE2.dot m b₀ + LE2.dot m z_min + (k : ℤ) * LE2.dot m vl := by
        set target := lev N₀ + c * LE2.dot m vl - (LE2.dot m b₀ + LE2.dot m z_min) with htarget
        refine ⟨target.toNat, ?_⟩
        have h1 : target ≤ (target.toNat : ℤ) := Int.self_le_toNat target
        have h2 : (target.toNat : ℤ) ≤ (target.toNat : ℤ) * LE2.dot m vl := by
          nlinarith [Int.natCast_nonneg target.toNat, hmvl]
        have h3 : target ≤ (target.toNat : ℤ) * LE2.dot m vl := le_trans h1 h2
        omega

      obtain ⟨k, hk⟩ := hk_ex

      -- Define v := b₀ + k•vl, τ := 0, ε := true
      refine ⟨b₀ + (k : ℤ) • vl, 0, true, ?_⟩

      intro N hper_N hnotper_N1 z hz
      simp only [zero_smul, zero_add]

      -- z ∈ derivedQ ⊆ S.image (· + v)
      have hz_image : z ∈ S.image (fun s => s + (b₀ + (k : ℤ) • vl)) :=
        derivedQ_subset true w _ hz
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz_image

      -- Uniqueness: N = N₀
      have hN_eq : N = N₀ := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hsub : cut Rinf m lev (N + 1) ⊆ cut Rinf m lev N₀ :=
            cut_mono hlev (by omega : N + 1 ≤ N₀)
          exact hnotper_N1 (PeriodOn.mono hsub hN₀_per)
        · have hsub : cut Rinf m lev (N₀ + 1) ⊆ cut Rinf m lev N :=
            cut_mono hlev (by omega : N₀ + 1 ≤ N)
          exact hN₀_not (PeriodOn.mono hsub hper_N)

      rw [hN_eq]

      have hmem1 : s + (b₀ + (k : ℤ) • vl) ∈ Rinf := by
        have heq : s + (b₀ + (k : ℤ) • vl) = (b₀ + s) + (k : ℤ) • vl := by abel
        rw [heq]
        exact hpush (b₀ + s) (hb₀ s hs) k

      have hdot1 : LE2.dot m (s + (b₀ + (k : ℤ) • vl))
          = LE2.dot m b₀ + LE2.dot m s + (k : ℤ) * LE2.dot m vl := by
        rw [LE2.dot_add, LE2.dot_add, dot_zsmul_right]
        ring

      have hheight1 : lev N₀ ≤ LE2.dot m (s + (b₀ + (k : ℤ) • vl)) := by
        rw [hdot1]
        have hzmin_le : LE2.dot m z_min ≤ LE2.dot m s := hmin s hs
        have hcpos : 0 < c * LE2.dot m vl := Int.mul_pos hc hmvl
        omega

      have hmem2 : s + (b₀ + (k : ℤ) • vl) + c • vl ∈ Rinf := by
        have heq : s + (b₀ + (k : ℤ) • vl) + c • vl = (b₀ + s) + ((k : ℤ) + c) • vl := by
          rw [add_smul]; abel
        rw [heq]
        have hnn : 0 ≤ (k : ℤ) + c := by
          have : 0 < c := hc
          omega
        rw [← Int.toNat_of_nonneg hnn]
        exact hpush (b₀ + s) (hb₀ s hs) _

      have hdot2 : LE2.dot m (s + (b₀ + (k : ℤ) • vl) + c • vl)
          = LE2.dot m b₀ + LE2.dot m s + (k : ℤ) * LE2.dot m vl + c * LE2.dot m vl := by
        rw [LE2.dot_add, dot_zsmul_right, hdot1]

      have hheight2 : lev N₀ ≤ LE2.dot m (s + (b₀ + (k : ℤ) • vl) + c • vl) := by
        rw [hdot2]
        have hzmin_le : LE2.dot m z_min ≤ LE2.dot m s := hmin s hs
        have hcpos : 0 < c * LE2.dot m vl := Int.mul_pos hc hmvl
        omega

      exact ⟨⟨hmem1, hheight1⟩, ⟨hmem2, hheight2⟩⟩

    · -- S empty: vacuous
      refine ⟨0, 0, true, ?_⟩
      intro N _ _ z hz
      simp only [zero_smul, zero_add]
      exfalso
      have himg : (S.image (· + 0) : Finset (ℤ × ℤ)).Nonempty :=
        ⟨z, derivedQ_subset true w _ hz⟩
      rw [Finset.image_nonempty] at himg
      exact hS himg

  · -- Case 2: No breaking point (vacuous)
    refine ⟨0, 0, true, ?_⟩
    intro N hper_N hnotper_N1
    exfalso
    exact hexists ⟨N, hper_N, hnotper_N1⟩

/-- **Guard (protocol §27)**: apply `exists_line_package` to the literal binder types of the
`obtain` at `RegionSteps.lean:1734-1740`, so the "matches the consumer" claim is a term the
elaborator checks, not a human's visual comparison. -/
example
    {ξ : Config ℤ} {vl : ℤ × ℤ} {e : ℤ × ℤ} {c : ℤ} (S : Finset (ℤ × ℤ))
    (Rinf : Set (ℤ × ℤ))
    (w : ℤ × ℤ) (hw_det : det vl w ≠ 0) (hw_prim : Primitive w)
    (m : ℤ × ℤ) (hmw : LE2.dot m w = 0) (hmvl : 0 < LE2.dot m vl)
    (b₀ : ℤ) (hR : Nivat.Colle41.IsRegion Rinf vl w)
    (hc : 0 < c) (hvl_prim : Primitive vl)
    (hinf : ¬ PeriodOn (T e ξ) Rinf (c • vl))
    (lev : ℕ → ℤ) (hlev0 : lev 0 = b₀) (hlev : Antitone lev)
    (hexh : ∀ b : ℤ, ∃ n : ℕ, lev n ≤ b)
    (hgap : ∀ n : ℕ, ∃ z ∈ Rinf, lev (n + 1) ≤ LE2.dot m z ∧ LE2.dot m z < lev n) :
    ∃ (v : ℤ × ℤ) (τ : ℤ) (ε : Bool), ∀ (N : ℕ),
      Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev N) (c • vl) →
      ¬ Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) →
      ∀ z ∈ L1Data.derivedQ ε w (S.image (· + v)),
        τ • w + z ∈ Nivat.L1Region.cut Rinf m lev N ∧
        τ • w + z + c • vl ∈ Nivat.L1Region.cut Rinf m lev N :=
  Nivat.L1LinePackage.exists_line_package (e := e) (c := c) (S := S) Rinf w hw_det hw_prim
    m hmw hmvl lev b₀ hlev0 hlev hexh hgap hR hc hvl_prim hinf

end Nivat.L1LinePackage

#print axioms Nivat.L1LinePackage.exists_line_package
