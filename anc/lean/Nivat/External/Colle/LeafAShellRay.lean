/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ItemII

/-!
# Backwards `vl`-ray inside `⋃ i, hatOf A kk vl i`

原文：b3_colle2.txt:506（`Â_∞` 的「two semi-infinite edges parallel to ℓ」）。

`ofParts` 的 `rec_p`（`ChainAssemble.lean:217`）经 `RecessionCone.recession_of_ray` 归约到两条子引理：
(1) `⋃ i, hatOf A kk vl i` 格凸；(2) 它含一条方向 `−vl` 的格射线。本文件给 (2)。

机制：给定 `g₁ ∈ hatOf A kk vl i₀` 与 `t : ℕ`，取 `i` 大到盒子 `[−(i−1), i−1]²` 含 `g₁ − t•vl`；
`dot nℓ (g₁ − t•vl) = dot nℓ (g₁ + kk i•vl) ≥ cz`（`hperp` + `hA_hp`），故 `g₁ − t•vl ∈ B i ⊆ A i`
（`ItemII`，`:474`）；而 `g₁ + kk i•vl ∈ A i`（`hkk_mem`），目标点 `g₁ + (kk i − t)•vl` 是两者的凸组合，
由 `A i` 格凸落在 `A i` 内，即 `g₁ − t•vl ∈ hatOf A kk vl i`。
-/

set_option autoImplicit false

namespace Nivat.LeafAShellRay

open Nivat Nivat.LE2 Nivat.Colle35

variable {nℓ vl : ℤ × ℤ} {cz : ℤ}
variable {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}

/-- **Sub-lemma (2) for `rec_p`: the backwards `vl`-ray from any `g₁` with
`∀ i, g₁ + kk i • vl ∈ A i` lies in `⋃ i, hatOf A kk vl i`.**
原文：b3_colle2.txt:506. -/
theorem ray_neg_vl_subset_iUnion_hatOf
    (hperp : dot nℓ vl = 0)
    (hA_conv : ∀ i, IsLatticeConvexRegion (A i))
    (g₁ : ℤ × ℤ)
    (hkk_mem : ∀ i, g₁ + (kk i : ℤ) • vl ∈ A i)
    (itemII : ItemII B nℓ cz)
    (hB_sub_A : ∀ i, B i ⊆ A i)
    (hA_hp : ∀ i z, z ∈ A i → cz ≤ dot nℓ z) :
    ∀ t : ℕ, g₁ - (t : ℤ) • vl ∈ ⋃ i, hatOf A kk vl i := by
  intro t
  -- the box index
  set i : ℕ := (|g₁.1| + |g₁.2| + (t : ℤ) * (|vl.1| + |vl.2|) + 2).toNat with hi_def
  have hi_cast : (i : ℤ) = |g₁.1| + |g₁.2| + (t : ℤ) * (|vl.1| + |vl.2|) + 2 := by
    rw [hi_def, Int.toNat_of_nonneg]
    positivity
  rw [Set.mem_iUnion]
  refine ⟨i, ?_⟩
  show g₁ - (t : ℤ) • vl + (kk i : ℤ) • vl ∈ A i
  -- the left endpoint is in the box, hence in `B i ⊆ A i`
  have hleft : g₁ - (t : ℤ) • vl ∈ A i := by
    apply hB_sub_A i
    apply itemII i
    · simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul, hi_cast]
      have h1 := abs_sub (g₁.1) ((t : ℤ) * vl.1)
      have h2 : |(t : ℤ) * vl.1| = (t : ℤ) * |vl.1| := by
        rw [abs_mul, Nat.abs_cast]
      have h3 : 0 ≤ (t : ℤ) * |vl.2| := by positivity
      nlinarith [abs_nonneg g₁.2, abs_nonneg vl.1, abs_nonneg vl.2]
    · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul, hi_cast]
      have h1 := abs_sub (g₁.2) ((t : ℤ) * vl.2)
      have h2 : |(t : ℤ) * vl.2| = (t : ℤ) * |vl.2| := by
        rw [abs_mul, Nat.abs_cast]
      have h3 : 0 ≤ (t : ℤ) * |vl.1| := by positivity
      nlinarith [abs_nonneg g₁.1, abs_nonneg vl.1, abs_nonneg vl.2]
    · have hz := hA_hp i _ (hkk_mem i)
      have e1 : dot nℓ (g₁ + (kk i : ℤ) • vl) = dot nℓ g₁ := by
        rw [dot_add]; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hperp ⊢
        nlinarith [hperp]
      have e2 : dot nℓ (g₁ - (t : ℤ) • vl) = dot nℓ g₁ := by
        rw [dot_sub]; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hperp ⊢
        nlinarith [hperp]
      rw [e2]; rw [e1] at hz; exact hz
  have hright : g₁ + (kk i : ℤ) • vl ∈ A i := hkk_mem i
  -- convex combination
  obtain ⟨C, hCconv, -, hAC⟩ := hA_conv i
  rw [hAC] at hleft hright ⊢
  simp only [Set.mem_preimage] at hleft hright ⊢
  by_cases ht : t = 0
  · subst ht
    simpa using hright
  have hden : (0 : ℝ) < (kk i : ℝ) + (t : ℝ) := by
    have : (0 : ℝ) < (t : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ht
    positivity
  set θ : ℝ := (kk i : ℝ) / ((kk i : ℝ) + (t : ℝ)) with hθ
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [hθ, div_le_one hden]; linarith
  have key : toReal (g₁ - (t : ℤ) • vl + (kk i : ℤ) • vl) =
      toReal (g₁ - (t : ℤ) • vl) + θ • (toReal (g₁ + (kk i : ℤ) • vl) - toReal (g₁ - (t : ℤ) • vl)) := by
    have hden' : (kk i : ℝ) + (t : ℝ) ≠ 0 := ne_of_gt hden
    ext
    · simp only [toReal, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul, hθ]
      push_cast
      field_simp
      ring
    · simp only [toReal, Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul, hθ]
      push_cast
      field_simp
      ring
  rw [key]
  exact Convex.add_smul_sub_mem hCconv hleft hright hθ_mem

end Nivat.LeafAShellRay
