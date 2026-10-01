/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.ConeRegion

/-!
# Obstruction: `chainFull` cannot be contained in `coneRegion` when `K > 0`

原文：b3_colle2.txt:808

This file proves that when `u₂ = u' - K•vl` with `K > 0`, the set `chainFull R vl u₂ b₀ 0`
(the paper's region construction from the sheared direction) **cannot** be a subset of
`coneRegion B vl u'` (the paper's two-ray cone).

**Why it matters (接链，硬规矩 9):**
消费者是 `RegionSteps.lean:1539` `exists_stage2_frame_of_claim46` 的残余 `sorry`：
它的结论要 `PeriodOn … (chainFull R vl (u'-K•vl) b₀ 0) …`，唯一的周期性输入是
`hbase₁ : PeriodOn (T e ξ) (coneRegion B vl u') (c•vl)`，而 `PeriodOn` 是反变的，
所以**只能靠包含关系**接上。本文件证明该包含在 `K > 0` 时**不可能成立**，
这将迫使原文 `:808` 的修正：改用纯 `ℕ` 扫区域，而不是 `chainFull`。

## The argument (完整，硬规矩 10)

记 `u₂ := u' - K • vl`，`m := expNormal u₂ vl`。

Key observation: for points `z t = b₀ + t•u₂` in `chainFull`, we have:
- `det (z t) vl = det b₀ vl + t * det u₂ vl = det b₀ vl + t * det u' vl`
- If `z t ∈ coneRegion B vl u'`, then `z t = b + s•vl + t'•u'` for some `b ∈ B`, `s, t' : ℕ`
- Comparing determinants: `det b₀ vl + t * det u' vl = det b vl + t' * det u' vl`
- So `t' = t + (det b₀ vl - det b vl) / det u' vl` when `det u' vl = ±1`

For the `det u' vl = -1` case with large enough `t`, this forces `t' < 0`, contradicting `t' : ℕ`.

## 数值实例（硬规矩 10：派几何义务前先算一个实例）

取 `vl = (1, 0)`, `u' = (0, 1)`, `K = 1`，则 `u₂ = (-1, 1)`。
`det u' vl = det (0,1) (1,0) = 0*0 - 1*1 = -1`。

取 `b₀ = (0, 0)`, `B = {(1, 0)}`, `R = {(0, 0)}`。
`det b₀ vl = 0`, `det b vl = det (1,0) (1,0) = 0`。

- `t = 10` 时：`z 10 = (0,0) + 10•(-1,1) = (-10, 10)`。
  - `det (z 10) vl = -10`
  - 若在 `coneRegion` 里：`(-10, 10) = (1,0) + s•(1,0) + t'•(0,1)`
    ⟹ `s = -11`, `t' = 10`。但 `s : ℕ` 不能是负数，矛盾。

Actually for `det u' vl = -1`: from `det b₀ vl + t * (-1) = det b vl + t' * (-1)`,
we get `t' = t + det b vl - det b₀ vl`. For large `t` and `det b vl > det b₀ vl`,
the `vl`-coordinate check fails.

-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.LE2 Nivat.ConeRegion Nivat.RegionSweep

/-- `det` is `ℤ`-linear in the first argument. -/
theorem det_zsmul_left (t : ℤ) (v w : ℤ × ℤ) : det (t • v) w = t * det v w := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- `det` distributes over addition in the first argument. -/
theorem det_add_left (u v w : ℤ × ℤ) : det (u + v) w = det u w + det v w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

/-- Shearing by `vl` doesn't change the determinant: `det (u' - K•vl) vl = det u' vl`. -/
theorem det_shear_vl (u' vl : ℤ × ℤ) (K : ℤ) :
    det (u' - K • vl) vl = det u' vl := by
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Core lemma: points along `u₂` direction all satisfy the chainFull level-0 condition. -/
theorem mem_chainFull_of_ray {R : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {K : ℤ}
    (hb₀ : b₀ ∈ R) (hunimod : det u' vl = 1 ∨ det u' vl = -1) (t : ℕ) :
    b₀ + (t : ℤ) • (u' - K • vl) ∈ chainFull R vl (u' - K • vl) b₀ 0 := by
  set u₂ := u' - K • vl
  set m := expNormal u₂ vl
  rw [chainFull, L1Region.cut, Set.mem_inter_iff, halfPlaneGE, Set.mem_setOf, expLevel]
  refine ⟨?_, ?_⟩
  · -- In wedgeFull
    rw [wedgeFull]
    refine ⟨b₀, ?_, t, rfl⟩
    rw [mem_fullSweep_iff]
    exact ⟨b₀, hb₀, 0, by simp⟩
  · -- Level condition: dot m (b₀ + t•u₂) ≥ dot m b₀
    simp only [Nat.cast_zero, sub_zero]
    rw [dot_add, dot_zsmul, dot_expNormal_u', mul_zero, add_zero]

/-- When `K > 0` and `B` is finite and nonempty, `chainFull R vl (u' - K•vl) b₀ 0` **cannot**
be a subset of `coneRegion B vl u'`.

原文：b3_colle2.txt:808 — 这条否定结论迫使结论形状从 `chainFull` 改成原文的纯 `ℕ` 扫。

**Proof (完整, 无分情形).**  记 `u₂ := u' - K • vl`, `m := expNormal u₂ vl`, `ε := det u' vl`。
由 `det_shear_vl` 有 `det u₂ vl = ε`，故 `dot m vl = 1`（`dot_expNormal_vl`）、
`dot m u₂ = 0`（`dot_expNormal_u'`）、`dot m u' = dot m u₂ + K * dot m vl = K`。

设 `z t := b₀ + t • u₂ ∈ chainFull R vl u₂ b₀ 0`（`mem_chainFull_of_ray`）。若
`z t = b + s • vl + t' • u'`（`b ∈ B`, `s t' : ℕ`），两次取坐标：

* `det · vl` 杀掉 `vl` 分量：`det b₀ vl + t * ε = det b vl + t' * ε`，再乘 `ε`（`ε² = 1`）得
  **`t' = t + ε * (det b₀ vl − det b vl)`**；
* `dot m` 杀掉 `u₂` 分量：`dot m b₀ = dot m b + s + t' * K`。

把第一式代入第二式，`ε`-项恰好抵消，得到**单个势函数** `g x := dot m x − K * ε * det x vl` 上的
恒等式 **`g b + t * K = g b₀ − s`**。因 `s ≥ 0` 且 `g` 在有限非空 `B` 上有下界 `M`，
得 `t * K ≤ g b₀ − M` 对**每个** `t : ℕ` 成立；取 `t := (g b₀ − M).toNat + 1` 并用 `K ≥ 1`
即 `t * K ≥ t > g b₀ − M`，矛盾。

⚠ `K > 0` 是本质的：`K = 0` 时 `dot m u' = 0`，`t'` 不再受 `dot m` 约束，论证失效——
这正对应 `u₂ = u'` 时命题变成 `ConeHbase.not_chainFull_subset_coneRegion` 的具体反例形态。 -/
theorem not_chainFull_subset_coneRegion_of_pos_shear
    {B R : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {K : ℤ}
    (hK : 0 < K) (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hb₀ : b₀ ∈ R) :
    ¬ (chainFull R vl (u' - K • vl) b₀ 0 ⊆ coneRegion B vl u') := by
  intro hsub
  -- `dot` is linear in its second argument along `a - k • c`.
  have hlin : ∀ (n a c : ℤ × ℤ) (k : ℤ), dot n (a - k • c) = dot n a - k * dot n c := by
    intro n a c k
    simp only [Nivat.LE2.dot, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  have hunimod₂ : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [det_shear_vl]; exact hunimod
  have hm_vl : dot (expNormal (u' - K • vl) vl) vl = 1 := dot_expNormal_vl hunimod₂
  have hm_u₂ : dot (expNormal (u' - K • vl) vl) (u' - K • vl) = 0 := dot_expNormal_u'
  have hm_u' : dot (expNormal (u' - K • vl) vl) u' = K := by
    have h := hlin (expNormal (u' - K • vl) vl) u' vl K
    rw [hm_u₂, hm_vl] at h
    linarith
  have hεε : det u' vl * det u' vl = 1 := by
    rcases hunimod with h | h <;> rw [h] <;> norm_num
  -- `g` is bounded below on the finite nonempty `B`.
  obtain ⟨M, hM⟩ : ∃ M : ℤ, ∀ x ∈ B,
      M ≤ dot (expNormal (u' - K • vl) vl) x - K * det u' vl * det x vl := by
    obtain ⟨M, hM⟩ := (hBfin.image
      (fun x => dot (expNormal (u' - K • vl) vl) x - K * det u' vl * det x vl)).bddBelow
    exact ⟨M, fun x hx => hM ⟨x, hx, rfl⟩⟩
  set G : ℤ := dot (expNormal (u' - K • vl) vl) b₀ - K * det u' vl * det b₀ vl with hG
  set t : ℕ := (G - M).toNat + 1 with ht
  have htK : G - M < (t : ℤ) * K := by
    have h1 : G - M < (t : ℤ) := by rw [ht]; push_cast; omega
    have hK1 : (1 : ℤ) ≤ K := by omega
    have h2 : (t : ℤ) * 1 ≤ (t : ℤ) * K :=
      mul_le_mul_of_nonneg_left hK1 (Int.natCast_nonneg t)
    rw [mul_one] at h2
    linarith
  -- The ray point at index `t` is in `chainFull`, hence by `hsub` in `coneRegion`.
  have hmem := hsub (mem_chainFull_of_ray (K := K) hb₀ hunimod t)
  rw [mem_coneRegion_iff] at hmem
  obtain ⟨b, hb, s, t', hz⟩ := hmem
  -- `det · vl` kills the `vl` component.
  have hdet : det b₀ vl + (t : ℤ) * det u' vl = det b vl + (t' : ℤ) * det u' vl := by
    calc det b₀ vl + (t : ℤ) * det u' vl
        = det b₀ vl + (t : ℤ) * det (u' - K • vl) vl := by rw [det_shear_vl]
      _ = det (b₀ + (t : ℤ) • (u' - K • vl)) vl := by rw [det_add_left, det_zsmul_left]
      _ = det (b + (s : ℤ) • vl + (t' : ℤ) • u') vl := by rw [hz]
      _ = det b vl + (t' : ℤ) * det u' vl := by
          rw [det_add_left, det_add_left, det_zsmul_left, det_zsmul_left, det_self,
            mul_zero, add_zero]
  -- `dot m` kills the `u₂` component.
  have hmeq : dot (expNormal (u' - K • vl) vl) b₀
      = dot (expNormal (u' - K • vl) vl) b + (s : ℤ) + (t' : ℤ) * K := by
    calc dot (expNormal (u' - K • vl) vl) b₀
        = dot (expNormal (u' - K • vl) vl) (b₀ + (t : ℤ) • (u' - K • vl)) := by
          rw [dot_add, dot_zsmul, hm_u₂, mul_zero, add_zero]
      _ = dot (expNormal (u' - K • vl) vl) (b + (s : ℤ) • vl + (t' : ℤ) • u') := by rw [hz]
      _ = dot (expNormal (u' - K • vl) vl) b + (s : ℤ) + (t' : ℤ) * K := by
          rw [dot_add, dot_add, dot_zsmul, dot_zsmul, hm_vl, hm_u']; ring
  -- Multiplying `hdet` by `ε` pins `t'` to `t` up to a `B`-dependent offset.
  have ht'eq : (t' : ℤ) = (t : ℤ) + det u' vl * (det b₀ vl - det b vl) := by
    linear_combination (-(det u' vl)) * hdet + ((t : ℤ) - (t' : ℤ)) * hεε
  -- The two coordinate identities collapse into one, on the potential `g`.
  have hkey : dot (expNormal (u' - K • vl) vl) b - K * det u' vl * det b vl + (t : ℤ) * K
      = G - (s : ℤ) := by
    rw [hG]
    linear_combination (-1 : ℤ) * hmeq + (-K) * ht'eq
  have hMb := hM b hb
  have hs : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
  linarith

end Nivat.ColleReg

#print axioms Nivat.ColleReg.det_shear_vl
#print axioms Nivat.ColleReg.mem_chainFull_of_ray
#print axioms Nivat.ColleReg.not_chainFull_subset_coneRegion_of_pos_shear
