/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
# Cut recursion via lattice convexity

原文：b3_colle2.txt:818（`𝓡^0_I = 𝓡_I`，`d_0 = 0`）；`:766`（边法向的循环序，给出 `nprev`）。

`cut_of_step_eq`（`CutOfStep.lean:42`）把「沿 `w'` 扫掠后再截回 `b₀` 层得到原区域」归约到
`hrec : ∀ z ∈ R, ∀ t : ℕ, b₀ ≤ dot m (z + t • w') → z + t • w' ∈ R`。
`hrec_coneRegion_nat`（`CutOfStep.lean:83`）只覆盖 `I = 0` 的锥形区域；本文件对**任意**格凸区域
给出 `hrec`，只用四条前提：

* (a) `hR`：`R` 格凸（`R = toReal ⁻¹' C`，`C` 闭凸）；
* (b) `hlow`、`hb₀`：`b₀` 是 `R` 的最低 `m`-层，`b₀pt` 在这一层；
* (c) `hwray`、`hmw`：从 `b₀pt` 出发的 `w`-格射线在 `R` 内，`w` 沿该层（`dot m w = 0`）；
* (d) `hprev`、`hpw`、`hpw'`：`b₀pt` 处另一条支撑边法向 `nprev`，把 `w` 与 `w'` 放在同一侧
  （`w'` 允许与该边平行：`hpw'` 是 `≤ 0`，2026-09-22 放宽）。

机制：令 `K₀ := (dot m z − b₀)/(−dot m w')`，`q := z + K₀ w'` 落在 `b₀` 层；由 (b)(d) `q − b₀pt`
平行于 `w` 且与 `w` 同向，故 `q` 在 `w`-射线的实凸包内；`z + k w'`（`k ≤ K₀`）是 `z` 与 `q` 的凸组合。

## Main result

* `hrec_of_convex` — 递归条件；消费者 `cut_of_step_eq` 的 `hrec` 前提。

## Status

0 sorry；`#print axioms`：`[propext, Classical.choice, Quot.sound]`（集成者复验 2026-09-22）。
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.LE2

variable {R : Set (ℤ × ℤ)} {w w' m nprev : ℤ × ℤ} {b₀pt : ℤ × ℤ} {b₀ : ℤ}

/-- **Recursion for lattice-convex regions via convex combination.**

If R satisfies:
- (a) `hR`: lattice-convex (R = toReal⁻¹ C for closed convex C ⊆ ℝ²)
- (b) `hlow`, `hb₀`: w-edge at base level b₀
- (c) `hwray`, `hmw`: w-ray from b₀pt contained in R
- (d) `hprev`, `hpw`, `hpw'`: supporting edge nprev at b₀pt (separates w and w')

Then w'-stepping respects the level constraint.

原文：b3_colle2.txt:818。Strategy: show z + k•w' is a convex
combination of z (in R) and a point q on the w-ray (also in R).
-/
theorem hrec_of_convex
    (hR : IsLatticeConvexRegion R)
    (hlow : ∀ z ∈ R, b₀ ≤ dot m z)
    (hb₀ : dot m b₀pt = b₀)
    (hwray : ∀ t : ℕ, b₀pt + t • w ∈ R)
    (hmw : dot m w = 0)
    (hneg : dot m w' < 0)
    (hprev : ∀ z ∈ R, dot nprev (z - b₀pt) ≤ 0)
    (hpw : dot nprev w < 0)
    (hpw' : dot nprev w' ≤ 0)
    (z : ℤ × ℤ) (hz : z ∈ R)
    (k : ℕ) (hk : b₀ ≤ dot m (z + k • w')) :
    z + k • w' ∈ R := by
  -- Unpack lattice convexity
  obtain ⟨C, hCconv, hCclosed, hRC⟩ := hR

  -- Step 1: Define K₀ and prove K₀ ≥ k from level constraint
  set K₀ : ℝ := ((dot m z : ℝ) - (b₀ : ℝ)) / (-(dot m w' : ℝ))

  have hK₀_ge_k : (k : ℝ) ≤ K₀ := by
    have hdot_zkw : dot m (z + k • w') = dot m z + (k : ℤ) * dot m w' := by
      rw [dot_add]
      congr 1
      cases m; cases w'; unfold dot; simp [Prod.smul_mk]; ring
    rw [hdot_zkw] at hk
    have h1 : (b₀ : ℝ) ≤ (dot m z : ℝ) + (k : ℝ) * (dot m w' : ℝ) := by
      exact_mod_cast hk
    have h2 : (k : ℝ) * (-(dot m w' : ℝ)) ≤ (dot m z : ℝ) - (b₀ : ℝ) := by linarith
    have h3 : 0 < -(dot m w' : ℝ) := by
      have : (dot m w' : ℝ) < 0 := by exact_mod_cast hneg
      linarith
    rw [le_div_iff₀ h3]; exact h2

  have hK₀_nonneg : 0 ≤ K₀ := by
    apply div_nonneg
    · have : (b₀ : ℝ) ≤ (dot m z : ℝ) := by exact_mod_cast hlow z hz
      linarith
    · have : (dot m w' : ℝ) < 0 := by exact_mod_cast hneg
      linarith

  -- Step 2: Define q on level b₀
  set q : ℝ × ℝ := toReal z + K₀ • toReal w'

  -- Step 3: q lies on the w-ray (level + nprev side condition)
  have hq_on_ray : ∃ c : ℝ, 0 ≤ c ∧ q = toReal b₀pt + c • toReal w := by
    -- real coordinates of `q - b₀pt`
    set u1 : ℝ := (z.1 : ℝ) + K₀ * (w'.1 : ℝ) - (b₀pt.1 : ℝ) with hu1
    set u2 : ℝ := (z.2 : ℝ) + K₀ * (w'.2 : ℝ) - (b₀pt.2 : ℝ) with hu2
    have hq_eq : q = ((b₀pt.1 : ℝ) + u1, (b₀pt.2 : ℝ) + u2) := by
      simp only [q, toReal, hu1, hu2, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul]
      ext <;> simp <;> ring
    have hmw'_ne : (dot m w' : ℝ) ≠ 0 := by
      have : (dot m w' : ℝ) < 0 := by exact_mod_cast hneg
      exact ne_of_lt this
    have hK₀_eq : K₀ * (-(dot m w' : ℝ)) = (dot m z : ℝ) - (b₀ : ℝ) := by
      simp only [K₀]
      field_simp
    clear_value K₀ u1 u2
    -- (i) `q` sits on the level `b₀`
    have hlev : (m.1 : ℝ) * u1 + (m.2 : ℝ) * u2 = 0 := by
      have hb : (m.1 : ℝ) * b₀pt.1 + (m.2 : ℝ) * b₀pt.2 = b₀ := by
        rw [← hb₀]; simp [dot]
      simp only [dot] at hK₀_eq
      push_cast at hK₀_eq
      rw [hu1, hu2]
      linear_combination -hK₀_eq - hb
    -- (ii) the `nprev`-side
    have hprevR : (nprev.1 : ℝ) * u1 + (nprev.2 : ℝ) * u2 ≤ 0 := by
      have h1 : (dot nprev (z - b₀pt) : ℝ) ≤ 0 := by exact_mod_cast hprev z hz
      have h2 : (dot nprev w' : ℝ) ≤ 0 := by exact_mod_cast hpw'
      have h3 : K₀ * (dot nprev w' : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK₀_nonneg h2
      simp only [dot, Prod.fst_sub, Prod.snd_sub] at h1 h3
      push_cast at h1 h3
      rw [hu1, hu2]
      linarith [h1, h3]
    -- (iii) `u` is parallel to `w`
    have hmwR : (m.1 : ℝ) * w.1 + (m.2 : ℝ) * w.2 = 0 := by
      have : (dot m w : ℝ) = 0 := by exact_mod_cast hmw
      simpa [dot] using this
    have hm_ne : (m.1 : ℝ) ≠ 0 ∨ (m.2 : ℝ) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hmw'_ne
      simp only [dot]; push_cast; rw [hcon.1, hcon.2]; ring
    have hdet : u1 * w.2 - u2 * w.1 = 0 := by
      have e1 : (m.1 : ℝ) * (u1 * w.2 - u2 * w.1) = 0 := by
        linear_combination (w.2 : ℝ) * hlev - u2 * hmwR
      have e2 : (m.2 : ℝ) * (u1 * w.2 - u2 * w.1) = 0 := by
        linear_combination (-(w.1 : ℝ)) * hlev + u1 * hmwR
      rcases hm_ne with h | h
      · exact (mul_eq_zero.mp e1).resolve_left h
      · exact (mul_eq_zero.mp e2).resolve_left h
    have hpwR : (nprev.1 : ℝ) * w.1 + (nprev.2 : ℝ) * w.2 < 0 := by
      have : (dot nprev w : ℝ) < 0 := by exact_mod_cast hpw
      simpa [dot] using this
    -- pick `c`
    obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, u1 = c * w.1 ∧ u2 = c * w.2 := by
      by_cases hw1 : (w.1 : ℝ) = 0
      · have hw2 : (w.2 : ℝ) ≠ 0 := by
          intro hw2; rw [hw1, hw2] at hpwR; simp at hpwR
        refine ⟨u2 / w.2, ?_, ?_⟩
        · rw [hw1, mul_zero]
          rw [hw1, mul_zero, sub_zero] at hdet
          exact (mul_eq_zero.mp hdet).resolve_right hw2
        · field_simp
      · refine ⟨u1 / w.1, ?_, ?_⟩
        · field_simp
        · field_simp
          linear_combination -hdet
    refine ⟨c, ?_, ?_⟩
    · by_contra hc
      push_neg at hc
      have : (nprev.1 : ℝ) * u1 + (nprev.2 : ℝ) * u2 = c * ((nprev.1 : ℝ) * w.1 + (nprev.2 : ℝ) * w.2) := by
        rw [hc1, hc2]; ring
      rw [this] at hprevR
      nlinarith [mul_pos (neg_pos.mpr hc) (neg_pos.mpr hpwR)]
    · rw [hq_eq, hc1, hc2]
      simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]

  -- Step 4: Prove q ∈ C using lattice w-ray and Nat.ceil
  have hq_in_C : q ∈ C := by
    obtain ⟨c, hc_nonneg, hqc⟩ := hq_on_ray
    set n : ℕ := Nat.ceil c
    have hn_ge_c : c ≤ n := Nat.le_ceil c
    have hb0_in_C : toReal b₀pt ∈ C := by
      have h1 : b₀pt + 0 • w = b₀pt := by simp
      have h2 : b₀pt + 0 • w ∈ R := hwray 0
      rw [h1] at h2
      rw [hRC] at h2
      exact h2
    have hbn_in_C : toReal (b₀pt + n • w) ∈ C := by
      have h1 : b₀pt + n • w ∈ R := hwray n
      rw [hRC] at h1
      exact h1
    by_cases hn_zero : n = 0
    · have hc_zero : c = 0 := by
        have : c ≤ 0 := by rw [hn_zero] at hn_ge_c; simp at hn_ge_c; exact hn_ge_c
        linarith
      rw [hqc, hc_zero]; simp; exact hb0_in_C
    · have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn_zero)
      have ht_mem : c / n ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg hc_nonneg (Nat.cast_nonneg n)
        · rw [div_le_one hn_pos]; exact hn_ge_c
      rw [hqc]
      have key : toReal b₀pt + c • toReal w =
                 toReal b₀pt + (c / n) • (toReal (b₀pt + n • w) - toReal b₀pt) := by
        ext
        · unfold toReal at *
          show ↑b₀pt.1 + c * ↑w.1 = ↑b₀pt.1 + c / ↑n * (↑(b₀pt.1 + ↑n * w.1) - ↑b₀pt.1)
          push_cast
          field_simp
          ring
        · unfold toReal at *
          show ↑b₀pt.2 + c * ↑w.2 = ↑b₀pt.2 + c / ↑n * (↑(b₀pt.2 + ↑n * w.2) - ↑b₀pt.2)
          push_cast
          field_simp
          ring
      rw [key]
      exact Convex.add_smul_sub_mem hCconv hb0_in_C hbn_in_C ht_mem

  -- Step 5: Express target as convex combination and conclude
  have hz_in_C : toReal z ∈ C := by
    have h1 : z ∈ R := hz
    rw [hRC] at h1
    exact h1

  by_cases hk_zero : k = 0
  · simp [hk_zero]; exact hz

  have hK₀_pos : 0 < K₀ := by
    by_contra h; simp only [not_lt] at h
    have hK₀_eq : K₀ = 0 := le_antisymm h hK₀_nonneg
    rw [hK₀_eq] at hK₀_ge_k
    simp at hK₀_ge_k
    omega

  have htarget : toReal (z + k • w') ∈ C := by
    have ht_mem : k / K₀ ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (Nat.cast_nonneg k) (le_of_lt hK₀_pos)
      · rw [div_le_one hK₀_pos]; exact hK₀_ge_k
    have key : toReal (z + k • w') = toReal z + (k / K₀) • (q - toReal z) := by
      ext
      · unfold toReal q at *
        show ↑(z.1 + ↑k * w'.1) = ↑z.1 + ↑k / K₀ * (↑z.1 + K₀ * ↑w'.1 - ↑z.1)
        push_cast
        field_simp
        ring
      · unfold toReal q at *
        show ↑(z.2 + ↑k * w'.2) = ↑z.2 + ↑k / K₀ * (↑z.2 + K₀ * ↑w'.2 - ↑z.2)
        push_cast
        field_simp
        ring
    rw [key]
    exact Convex.add_smul_sub_mem hCconv hz_in_C hq_in_C ht_mem

  rw [hRC]; exact htarget

end Nivat.ColleReg
