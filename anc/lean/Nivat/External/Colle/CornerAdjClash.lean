/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1StraddleWedge

/-!
# `hadj` 与 `hcorner` 不能共用同一个 `(vl, u')`

集成者本轮的诊断，写成内核事实而不是读法（硬规矩 3 / `PROTOCOL.md` §15）。

## 结论

`hcorner`（`L1StraddleWedge.cover_line` 的前提，Figure 11(B)，原文 `b3_colle2.txt:848-856`）
说 `a` 同时是 `S` 在 `expNormal u' vl` 与 `uCoord u' vl` 两个坐标上的极小点。本文件证明：
**只要这样的 `a` 存在，`S` 就没有任何边法向落在「两个坐标都严格为负」的那个开象限里**
（`not_mem_E_of_corner_of_neg_neg`）。

`hadj`（`RegionSteps.lean:1394` 的相邻性前提，Claim 4.6，原文 `b3_colle2.txt:764`）
说 `S` 没有任何边法向落在「`vl`-坐标负、`u'`-坐标正」的那个开象限里。

两条合起来：**`vl`-坐标为负的边法向必须 `u'`-坐标为零**
（`dot_u'_eq_zero_of_adj_of_corner`），于是这样的边法向两两平行
（`det_eq_zero_of_adj_of_corner`）。`𝒮_φ` 是 `m` 个两两不平行生成元的 zonotope，
`E` 按 `E_zono` 是各生成元两个法向的并，除去平行 `vl` 的那一个生成元之后，
剩下 `m - 1` 个生成元各自贡献一个 `vl`-坐标为负的法向，它们必须两两平行 ⟹ `m ≤ 2`。

⚠ **本条与 `exists_corner_shear`（`L1StraddleWedge.lean:493`）不矛盾。** 那条说的是
「对任意有限非空 `S`，**某个剪切** `u' - K•vl` 上有 `hcorner`」。`uCoord` 是剪切不变的
（`uCoord_shear`），变的只是 `expNormal`：`K` 往一侧走 `hcorner` 成立而 `hadj` 失效，
往另一侧走反之。本文件说明这不是 `K` 没选好，而是**两条要求清空的是互补的开象限**。

## 为什么这是对齐问题而不是技术问题（硬规矩 10）

两条前提在原文里属于**两个不同的扫掠**：

* `hadj` / `hcone` / `hstrip` / `hstrict` 是 **Claim 4.6**（`:790-804`）：扫的是
  `l₁ := ℓ^(-)_B`、`l₂ := l₁^(-)`、… 这族**平行 `ℓ` 的直线**，逐条往 `ℓ^(-)` 推进；
  窗口 `𝒮_{φ_ι}` 的极点放在新直线上，其余点落在 `H_B(ℓ) ∪ A₁ ∪ …` 里。
  链上对应物：`a₀` 是 `Sw` 的 `nℓ`-严格极小点（`hstrict`），`hcone` / `hstrip` 说其余点
  要么在锥里要么在半带里。**推进方向：`nℓ` 递减。**
* `hcorner` / `cover_line` / `chainFull` 是 **Figure 11(B)**（`:848-856`；
  `L1StraddleWedge.lean` 模块 docstring 末行自己就是这么标的）：那是第二阶段 `𝓡^n_I`
  的扫掠，直线族是 `ℓ' = ℓ_I` 的等距线，推进方向是 `v⃗_{ℓ_{I-1}}`。原文里 `I` 是使
  `(T^u η)|𝓡_I` 仍有周期 `h` 的**最小**指标（`:812`），一般 `I ≠ ι`，所以
  `(ℓ', v⃗_{ℓ_{I-1}})` 与 `(ℓ, v⃗_{ℓ_{ι-1}})` **不是同一对方向**。

链上的装配器（`RegionSteps.wedgeResidualR_of_cone_of_enveloped` 及其五条下游）把两个阶段
**绑在同一个 `(vl, u')` 上**，本文件证明那样绑就把 `𝒮_φ` 逼成了平行四边形。

## 边界

本文件不含 `IsMinimalCounterexample`（所以不是空真），不含 `sorry`，不含任何新 `Prop`
——`hadj` / `hcorner` 两个形状都是从 `RegionSteps.lean:1394` / `:2044` 逐字抄的。
-/

set_option autoImplicit false

namespace Nivat.CornerAdjClash

open Nivat Nivat.LE2 Nivat.ColleReg Nivat.L1Line0 Nivat.L1StraddleWedge

variable {u' vl : ℤ × ℤ}

/-! ## §1  在幺模基 `(vl, u')` 下展开配对 -/

/-- `dot` 在第二个变量上的双线性展开；幺模性用不上。 -/
theorem dot_smul_add_smul (n vl u' : ℤ × ℤ) (A B : ℤ) :
    dot n (A • vl + B • u') = A * dot n vl + B * dot n u' := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- 任意法向 `n` 与任意向量 `w` 的配对，按 `L1StraddleWedge.eq_coords` 拆成两个坐标：
`dot (expNormal u' vl) w` 是 `vl`-系数，`uCoord u' vl 0 w` 是 `u'`-系数。 -/
theorem dot_eq_coords (hunimod : det u' vl = 1 ∨ det u' vl = -1) (n w : ℤ × ℤ) :
    dot n w = dot (expNormal u' vl) w * dot n vl + uCoord u' vl 0 w * dot n u' := by
  have hw := eq_coords (u' := u') (vl := vl) hunimod w
  calc dot n w
      = dot n ((dot (expNormal u' vl) w) • vl + (uCoord u' vl 0 w) • u') := by rw [← hw]
    _ = _ := dot_smul_add_smul _ _ _ _ _

/-! ## §2  `hcorner` 清空「两个坐标皆负」的开象限 -/

/-- **`hcorner` 把这样的 `n` 的暴露面压成单点 `{a}`。**

`hcorner` 给出 `∀ b ∈ S`，`vl`-坐标 `dot en (b - a) ≥ 0` 且 `u'`-坐标 `uCoord u' vl a b ≥ 0`；
配上 `dot n vl < 0`、`dot n u' < 0` 得 `dot n (b - a) ≤ 0`，且取等只能在两个坐标同时为零
（即 `b = a`）时发生。 -/
theorem face_eq_singleton_of_corner_of_neg_neg
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (ha : a ∈ S)
    (hcorner : ∀ b ∈ S, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b)
    {n : ℤ × ℤ} (hp : dot n vl < 0) (hq : dot n u' < 0) :
    face (↑S : Set (ℤ × ℤ)) n = {a} := by
  have key : ∀ b ∈ S, dot n b - dot n a ≤ 0 ∧ (dot n b - dot n a = 0 → b = a) := by
    intro b hb
    obtain ⟨hα, hβ⟩ := hcorner b hb
    have hsub : dot n (b - a) = dot n b - dot n a := dot_sub n b a
    have hexp : dot n (b - a)
        = dot (expNormal u' vl) (b - a) * dot n vl + uCoord u' vl a b * dot n u' := by
      rw [dot_eq_coords hunimod n (b - a), uCoord_sub_eq]
    have h1 : 0 ≤ dot (expNormal u' vl) (b - a) * (-(dot n vl)) :=
      mul_nonneg hα (by linarith)
    have h2 : 0 ≤ uCoord u' vl a b * (-(dot n u')) := mul_nonneg hβ (by linarith)
    have hrw : dot n b - dot n a
        = -(dot (expNormal u' vl) (b - a) * (-(dot n vl)))
          + -(uCoord u' vl a b * (-(dot n u'))) := by
      rw [← hsub, hexp]; ring
    refine ⟨by linarith, fun hzero => ?_⟩
    -- 取等 ⟹ 两个非负项都为零 ⟹ 两个坐标都为零 ⟹ `b = a`
    have hz1 : dot (expNormal u' vl) (b - a) * (-(dot n vl)) = 0 := by linarith
    have hz2 : uCoord u' vl a b * (-(dot n u')) = 0 := by linarith
    have hα0 : dot (expNormal u' vl) (b - a) = 0 := by
      rcases mul_eq_zero.mp hz1 with h | h
      · exact h
      · exact absurd h (by linarith)
    have hβ0 : uCoord u' vl a b = 0 := by
      rcases mul_eq_zero.mp hz2 with h | h
      · exact h
      · exact absurd h (by linarith)
    have hw := eq_coords (u' := u') (vl := vl) hunimod (b - a)
    rw [hα0, uCoord_sub_eq, hβ0, zero_smul, zero_smul, add_zero] at hw
    exact sub_eq_zero.mp hw
  have haS : a ∈ (↑S : Set (ℤ × ℤ)) := Finset.mem_coe.mpr ha
  ext z
  simp only [mem_face_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzS, hz⟩
    have hza := hz a haS
    have hle := (key z (Finset.mem_coe.mp hzS)).1
    exact (key z (Finset.mem_coe.mp hzS)).2 (by linarith)
  · rintro rfl
    exact ⟨haS, fun y hy => by have := (key y (Finset.mem_coe.mp hy)).1; linarith⟩

/-- **`hcorner` 下，两个坐标都严格为负的本原法向不是边法向。** -/
theorem not_mem_E_of_corner_of_neg_neg
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (ha : a ∈ S)
    (hcorner : ∀ b ∈ S, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b)
    {n : ℤ × ℤ} (hp : dot n vl < 0) (hq : dot n u' < 0) :
    n ∉ E (↑S : Set (ℤ × ℤ)) := by
  intro hn
  obtain ⟨-, hnt⟩ := mem_E_iff.mp hn
  rw [face_eq_singleton_of_corner_of_neg_neg hunimod ha hcorner hp hq] at hnt
  exact absurd hnt (by simp [Set.not_nontrivial_singleton])

/-! ## §3  与 `hadj` 合流 -/

/-- **冲突本身**：`hadj` 与 `hcorner` 同时成立时，每条 `vl`-坐标为负的边法向都必须
`u'`-坐标为零。

`hadj` 排掉 `dot n u' > 0`（相邻性，`b3_colle2.txt:764`），本文件 §2 排掉 `dot n u' < 0`
（`hcorner`，`b3_colle2.txt:848-856`），只剩 `= 0`。 -/
theorem dot_u'_eq_zero_of_adj_of_corner
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (ha : a ∈ S)
    (hcorner : ∀ b ∈ S, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b)
    (hadj : ∀ n ∈ E (↑S : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    {n : ℤ × ℤ} (hn : n ∈ E (↑S : Set (ℤ × ℤ))) (hp : dot n vl < 0) :
    dot n u' = 0 := by
  rcases lt_trichotomy (dot n u') 0 with h | h | h
  · exact absurd hn (not_mem_E_of_corner_of_neg_neg hunimod ha hcorner hp h)
  · exact h
  · exact absurd ⟨hp, h⟩ (hadj n hn)

/-- **推论：这样的边法向两两平行。** `𝒮_φ` 的 `m` 个生成元两两不平行，去掉平行 `vl` 的
那一个之后每个都贡献一条 `vl`-坐标为负的边法向（`E_zono`），于是 `m - 1 ≤ 1`。 -/
theorem det_eq_zero_of_adj_of_corner
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (ha : a ∈ S)
    (hcorner : ∀ b ∈ S, 0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b)
    (hadj : ∀ n ∈ E (↑S : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    {n n' : ℤ × ℤ} (hn : n ∈ E (↑S : Set (ℤ × ℤ))) (hn' : n' ∈ E (↑S : Set (ℤ × ℤ)))
    (hp : dot n vl < 0) (hp' : dot n' vl < 0) :
    det n n' = 0 := by
  have hu'ne : u' ≠ 0 := by
    rintro rfl
    rcases hunimod with h | h <;> simp [det] at h
  have h1 : dot u' n = 0 := by
    have := dot_u'_eq_zero_of_adj_of_corner hunimod ha hcorner hadj hn hp
    simp only [dot] at this ⊢; linarith
  have h2 : dot u' n' = 0 := by
    have := dot_u'_eq_zero_of_adj_of_corner hunimod ha hcorner hadj hn' hp'
    simp only [dot] at this ⊢; linarith
  exact det_eq_zero_of_dot_eq_zero hu'ne h1 h2

end Nivat.CornerAdjClash

section Receipts
/-! 常备 `#print axioms` 收据，可整块删除。 -/

#print axioms Nivat.CornerAdjClash.face_eq_singleton_of_corner_of_neg_neg
#print axioms Nivat.CornerAdjClash.not_mem_E_of_corner_of_neg_neg
#print axioms Nivat.CornerAdjClash.dot_u'_eq_zero_of_adj_of_corner
#print axioms Nivat.CornerAdjClash.det_eq_zero_of_adj_of_corner

end Receipts
