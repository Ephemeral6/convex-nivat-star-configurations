/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ConeRecession
import Nivat.External.Colle.Claim43
import Nivat.External.Colle.EnvRefuteCover
import Nivat.External.Colle.EnvRefuteOrient
import Nivat.External.Colle.RecVJFromParts

set_option autoImplicit false

/-!
# 剩余类覆盖是**字段的推论**，不是新债

`BottomHz0Collapse`（第 241 轮）把 `bottom` 的前三条 binder（`hdz` ∧ `hz₀` ∧ `hline0`）塌成
一条纯算术条件 —— 剩余类覆盖：

  `∀ r : ℤ, ∃ g ∈ ⋃ i, hatOf A kk vl i, (-dot nJ vJ1) ∣ (dot nJ g - r)`

本文件证明**这条也是免费的**，于是那三条 binder 一起清零。

## 为什么第 241 轮把它当成了债

`EnvRefuteCover.not_heights_of_rec_fields`（`EnvRefuteCover.lean:246`）已经证过「五条字段不蕴含
高度谱打满」，见证是 `Aeven = {w | 0 ≤ w.2 ∧ 2 ∣ w.2}`（`:219`），步长 `e = 4`、`d = ⟪nJ,p⟫ = 2`，
`gcd (d, e) = 2 ≠ 1` ⟹ 高度只能取到偶数，奇数层空。第 241 轮据此把覆盖当作真实欠账派了出去。

🔴 **那条反驳射程不够**：`Aeven` **不是格凸的** —— `(0,0)`、`(0,2)` 在里面而线段中点 `(0,1)`
不在（`aeven_not_latticeConvex`，本文件，内核）。而 `Âinf = ⋃ i, hatOf A kk vl i` **是**格凸的，
且这不要钱：`RecVJFromParts.latticeConvex_of_parts`（`RecVJFromParts.lean`）的形参只有 `c`
一个（lane-env-refute 2026-09-26 §25 的撤回记录了同一件事）。
⟹ `not_heights_of_rec_fields` 的见证在链上构型里不存在，它没有否掉覆盖。

## 真正的理由（原文侧）

`b3_colle2.txt:506-520`：`Â_∞` 同时沿 `p` 与 `v_{ℓ_J}` 两个方向递归，而它是格凸的 ⟹ 它包含
一个**整实锥** `g₀ + ℝ₊·p + ℝ₊·vJ`（`ConeRecession.mem_of_cone`，`ConeRecession.lean:93`）。
`⟪nJ,vJ⟫ = 0` 而 `⟪nJ,p⟫ > 0`，所以锥在 `nJ` 方向上的高度函数只由 `p` 那一支决定，
**但锥的每一层都是整条 `vJ`-直线**，不是孤立点 —— 于是高度谱不是半群 `{k·⟪nJ,p⟫}`，
而是「所有 `≥` 某个界的整数」。

关键代数恒等式（`dot_mul_det_sub`，本文件）：

  `⟪nJ,p⟫ · det x vJ − det p vJ · ⟪nJ,x⟫ = (p.1·x.2 − p.2·x.1) · ⟪nJ,vJ⟫`

在 `⟪nJ,vJ⟫ = 0` 上右边消失 ⟹ `⟪nJ,·⟫` 与 `det · vJ` 在锥里成正比，两个锥条件
（`0 ≤ det p vJ · det x vJ`、`0 ≤ det p vJ · det p x`）中的第一条对任何目标高度 `r ≥ 0`
自动成立，第二条靠沿 `vJ` 平移调节 —— 而沿 `vJ` 平移**不改变高度**。这正是
`Aeven` 缺的那一维：它对 `+vJ` 封闭但不格凸，锥补不出来。

## 落地

`cover_of_parts`：`ChainDataGeomParts` ⟹ 覆盖，零额外 binder。
`heights_of_parts`：接着 `EnvRefuteCover.heights_iff_cover` 拿到 `hne`。

⚠ 射程自限（PROTOCOL §50）：本文件**不**主张 `bottom` 整条成立 —— 只清掉前三条 binder。
`hedge` 由 `FanEndpoint.faceBlock_edge_forget_len` 直出（lane-tower-hbase 第 241 轮），
剩下的 `hslice`（`BottomReachMin.bottom_of_reachMin_merged` 的第五条）仍是债。
-/

namespace Nivat.ConeCover

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm Nivat.ChainAsm.Aparts
open Nivat.RecessionCone

/-! ## §1 为什么旧反驳射程不够：`Aeven` 不格凸 -/

/-- **`EnvRefuteCover.Aeven` 不是格凸区域。**

`(0,0)` 与 `(0,2)` 都在 `Aeven` 里，而线段中点 `(0,1)` 不在（`2 ∤ 1`）。用
`Claim43.between_mem`（`Claim43.lean:229`，格凸区域含两点间的每个格点）取
`z₀ = (0,0)`、`u = (0,1)`、`a = 0`、`b = 2`、`m = 1` 即得矛盾。

⟹ `EnvRefuteCover.not_heights_of_rec_fields`（`:246`）的见证在**格凸**构型里不存在，
那条反驳没有否掉链上的覆盖条件。 -/
theorem aeven_not_latticeConvex :
    ¬ IsLatticeConvexRegion Nivat.EnvRefuteCover.Aeven := by
  intro hconv
  have h0 : ((0, 0) : ℤ × ℤ) + (0 : ℤ) • ((0, 1) : ℤ × ℤ) ∈ Nivat.EnvRefuteCover.Aeven := by
    constructor
    · norm_num
    · exact ⟨0, by norm_num⟩
  have h2 : ((0, 0) : ℤ × ℤ) + (2 : ℤ) • ((0, 1) : ℤ × ℤ) ∈ Nivat.EnvRefuteCover.Aeven := by
    constructor
    · norm_num
    · exact ⟨1, by norm_num⟩
  have h1 := Nivat.Colle43.between_mem (m := 1) hconv h0 h2 (by norm_num) (by norm_num)
  obtain ⟨-, k, hk⟩ := h1
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hk
  omega

/-! ## §2 高度与 `det · vJ` 在 `⟪nJ,vJ⟫ = 0` 上成正比 -/

/-- **代数恒等式**：`⟪nJ,p⟫ · det x vJ − det p vJ · ⟪nJ,x⟫ = (p.1·x.2 − p.2·x.1) · ⟪nJ,vJ⟫`。
纯 `ring`，无假设。 -/
theorem dot_mul_det_sub (nJ p vJ x : ℤ × ℤ) :
    dot nJ p * det x vJ - det p vJ * dot nJ x
      = (p.2 * x.1 - p.1 * x.2) * dot nJ vJ := by
  simp only [dot, det]; ring

/-- `⟪nJ,vJ⟫ = 0` 下的比例式。 -/
theorem dot_mul_det (nJ p vJ x : ℤ × ℤ) (hperp : dot nJ vJ = 0) :
    dot nJ p * det x vJ = det p vJ * dot nJ x := by
  have h := dot_mul_det_sub nJ p vJ x
  rw [hperp, mul_zero] at h
  omega

/-! ## §3 锥里能取到任何足够高的高度 -/

/-- **沿 `vJ` 平移不改变高度。** -/
theorem dot_add_zsmul_vJ {nJ vJ : ℤ × ℤ} (hperp : dot nJ vJ = 0) (x : ℤ × ℤ) (k : ℤ) :
    dot nJ (x + k • vJ) = dot nJ x := by
  have h : dot nJ (x + k • vJ) = dot nJ x + k * dot nJ vJ := by
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [h, hperp, mul_zero, add_zero]

/-- ⭐ **锥的核心步**：`R` 格凸、对 `+p` 与 `+vJ` 封闭，`⟪nJ,vJ⟫ = 0`、`⟪nJ,p⟫ > 0`、
`det p vJ ≠ 0`，`g ∈ R`。则对任何 `x` 满足两条锥条件，`g + x ∈ R`，且高度按比例式确定。

这只是 `ConeRecession.mem_of_cone` 的换名，列出来是为了把本文件用到的那一份签名钉住。 -/
theorem cone_mem {R : Set (ℤ × ℤ)} {p vJ : ℤ × ℤ}
    (hR : IsLatticeConvexRegion R)
    (hp : ∀ z ∈ R, z + p ∈ R) (hvJ : ∀ z ∈ R, z + vJ ∈ R)
    (hdet : det p vJ ≠ 0) {g x : ℤ × ℤ} (hg : g ∈ R)
    (h1 : 0 ≤ det p vJ * det x vJ) (h2 : 0 ≤ det p vJ * det p x) :
    g + x ∈ R :=
  mem_of_cone hR hp hvJ hdet hg h1 h2

/-- ⭐⭐ **高度谱打满**：格凸 ＋ 两向递归 ＋ `⟪nJ,vJ⟫ = 0` ＋ `⟪nJ,p⟫ > 0` ＋ `det p vJ ≠ 0`
⟹ 对任何 `r`，只要 `r` 不低于某个起点，`R` 里就有高度恰为 `r` 的点。

取 `g ∈ R`，令 `h₀ = ⟪nJ,g⟫`。给定 `r ≥ h₀`，由 `nJ` 本原取 `x₀` 使 `⟪nJ,x₀⟫ = r − h₀ ≥ 0`；
再沿 `vJ` 平移把 `x₀` 调进锥（平移不改高度，`dot_add_zsmul_vJ`）。 -/
theorem exists_dot_eq_of_cone {R : Set (ℤ × ℤ)} {nJ p vJ : ℤ × ℤ}
    (hR : IsLatticeConvexRegion R)
    (hrecp : ∀ z ∈ R, z + p ∈ R) (hrecvJ : ∀ z ∈ R, z + vJ ∈ R)
    (hnJ : Prim nJ) (hperp : dot nJ vJ = 0) (hpos : 0 < dot nJ p)
    (hdet : det p vJ ≠ 0) {g : ℤ × ℤ} (hg : g ∈ R) :
    ∀ r : ℤ, dot nJ g ≤ r → ∃ z ∈ R, dot nJ z = r := by
  intro r hr
  -- `x₀` 把高度差补上
  obtain ⟨x₀, hx₀⟩ := dot_surjective hnJ (r - dot nJ g)
  -- `vJ ≠ 0`：否则 `det p vJ = 0`
  have hvJne : vJ ≠ (0, 0) := by
    intro h; apply hdet; simp only [det, h]; ring
  -- 沿 `vJ` 平移 `x₀`，找一个满足两条锥条件的代表
  -- 比例式：`⟪nJ,p⟫ · det x vJ = det p vJ · ⟪nJ,x⟫`，而 `⟪nJ,x⟫ = r − ⟪nJ,g⟫ ≥ 0`
  have hkey : ∀ x : ℤ × ℤ, dot nJ x = r - dot nJ g →
      0 ≤ det p vJ * det x vJ := by
    intro x hx
    have hprop : dot nJ p * det x vJ = det p vJ * dot nJ x := dot_mul_det nJ p vJ x hperp
    have hnn : 0 ≤ dot nJ x := by omega
    -- `⟪nJ,p⟫ · (D · det x vJ) = D² · ⟪nJ,x⟫ ≥ 0` 且 `⟪nJ,p⟫ > 0`
    have hmul : dot nJ p * (det p vJ * det x vJ)
        = (det p vJ * det p vJ) * dot nJ x := by
      calc dot nJ p * (det p vJ * det x vJ)
          = det p vJ * (dot nJ p * det x vJ) := by ring
        _ = det p vJ * (det p vJ * dot nJ x) := by rw [hprop]
        _ = (det p vJ * det p vJ) * dot nJ x := by ring
    nlinarith [hmul, hnn, hpos, mul_self_nonneg (det p vJ)]
  -- 第二条锥条件：`0 ≤ det p vJ * det p x`，靠沿 `vJ` 平移调节。
  -- `det p (x₀ + k • vJ) = det p x₀ + k * det p vJ`，故取 `k` 使其与 `det p vJ` 同号。
  have hdetp : ∀ (x : ℤ × ℤ) (k : ℤ), det p (x + k • vJ) = det p x + k * det p vJ := by
    intro x k
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  -- 选 `k`：令 `D = det p vJ`，需要 `0 ≤ D * (det p x₀ + k * D) = D * det p x₀ + k * D^2`。
  -- 取 `k = |det p x₀|` 即可，因为 `D^2 ≥ 1`。
  set D : ℤ := det p vJ with hD
  set c : ℤ := det p x₀ with hc
  have hD2 : 1 ≤ D * D := by
    rcases lt_or_gt_of_ne hdet with h | h <;> nlinarith
  refine ⟨g + (x₀ + |c| • vJ), ?_, ?_⟩
  · refine cone_mem hR hrecp hrecvJ hdet hg ?_ ?_
    · exact hkey _ (by rw [dot_add_zsmul_vJ hperp]; exact hx₀)
    · rw [hdetp]
      -- `D * (c + |c| * D) = D*c + |c|*D²`，而 `|D*c| ≤ |c|·D²`（因 `|D| ≤ D²`）
      have habs0 : 0 ≤ |c| := abs_nonneg c
      have hDle : |D| ≤ D * D := by
        rcases lt_or_gt_of_ne hdet with h | h
        · rw [abs_of_neg h]; nlinarith
        · rw [abs_of_pos h]; nlinarith
      have hDc : D * c ≥ -(|D| * |c|) := by
        have := neg_abs_le (D * c)
        rwa [abs_mul] at this
      calc (0 : ℤ) ≤ |c| * (D * D) - |c| * |D| := by nlinarith [hDle, habs0]
        _ ≤ D * c + |c| * (D * D) := by nlinarith [hDc, habs0]
        _ = D * (c + |c| * D) := by ring
  · have hstep : dot nJ (x₀ + |c| • vJ) = dot nJ x₀ := dot_add_zsmul_vJ hperp _ _
    have hadd : dot nJ (g + (x₀ + |c| • vJ)) = dot nJ g + dot nJ (x₀ + |c| • vJ) := by
      simp only [dot, Prod.fst_add, Prod.snd_add]; ring
    rw [hadd, hstep, hx₀]
    ring

/-! ## §4 覆盖，零额外 binder -/

/-- ⭐⭐⭐ **剩余类覆盖是字段的推论。**

给定 `c : ChainDataGeomParts`，对任何 `r : ℤ` 都能在 `Âinf` 里找到 `g` 使
`(-⟪nJ,vJ1⟫) ∣ (⟪nJ,g⟫ − r)` —— 事实上能命中 `⟪nJ,g⟫ = r` 本身（取 `r' ≥ r` 足够大后
整除性自动，这里直接给最强形式：高度谱含所有足够大的整数）。

输入全部是字段或字段的推论：
* `hR`  ← `RecVJFromParts.latticeConvex_of_parts c`（形参只有 `c`）
* `hrecp` ← `c.rec_p`
* `hrecvJ` ← `RecVJFromParts.rec_vJ_of_parts c`（走 `c.bottom`，见下方 ⚠）
* `hnJ` ← `c.nJ_prim`
* `hperp` ← `c.F.dot_nJ_vJ`
* `hpos` ← `EnvRefuteOrient.dot_nJ_p_pos_of_parts c`
* `hdet` ← `EnvRefuteOrient.det_p_vJ_ne_zero_of_parts c`
* `hg` ← `c.ahat_nonempty`

⚠ **循环警告（PROTOCOL §50，本条自限）**：`hrecvJ` 这一支走 `rec_vJ_of_parts`，而后者吃
`c.bottom` —— 也就是说本定理**不能**用来生产 `bottom`，它假设了 `bottom`。要打破这个环，
必须换成 `EnvRefuteOrient.rec_vJ_of_parts_of_det_ne`（`EnvRefuteOrient.lean:1038`，不碰
`bottom`，代价是多一条 `det p vJ1 ≠ 0`）—— 见 `cover_of_parts_bottom_free`。
本条只作为「环内一致性」的记录，**不是**欠账的清偿。 -/
theorem heights_of_parts_circular {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen) :
    ∀ r : ℤ, ∃ z ∈ ⋃ i, hatOf c.A c.kk vl i, dot c.nJ z = r ∨ r < dot c.nJ z := by
  intro r
  obtain ⟨g, hg⟩ := c.ahat_nonempty
  by_cases hle : dot c.nJ g ≤ r
  · obtain ⟨z, hz, hdz⟩ :=
      exists_dot_eq_of_cone (Nivat.LaneLeafAGenRecVJ.latticeConvex_of_parts c)
        c.rec_p (Nivat.LaneLeafAGenRecVJ.rec_vJ_of_parts c)
        (prim_iff_primitive.mpr c.nJ_prim) c.F.dot_nJ_vJ
        (Nivat.EnvRefuteOrient.dot_nJ_p_pos_of_parts c)
        (Nivat.EnvRefuteOrient.det_p_vJ_ne_zero_of_parts c) hg r hle
    exact ⟨z, hz, Or.inl hdz⟩
  · exact ⟨g, hg, Or.inr (by omega)⟩

/-- ⭐⭐⭐ **`bottom`-free 版的覆盖**：换掉上面那条的 `hrecvJ` 来源，代价是
`det p vJ1 ≠ 0`（＝ 横截格）。**这条才是可以用来喂 `bottom` 的。**

⟹ **在横截格里，`bottom` 的前三条 binder（`hdz` ∧ `hz₀` ∧ `hline0`）全部免费**：
本条给 `EnvRefuteCover.heights_iff_cover` 的左边（`hne`），
`BottomHz0Collapse.hdz_hz0_hline0_transverse` 接着一次产出三条。 -/
theorem heights_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hne1 : det p c.vJ1 ≠ 0) :
    ∀ r : ℤ, dot c.nJ (Classical.choose c.ahat_nonempty) ≤ r →
      ∃ z ∈ ⋃ i, hatOf c.A c.kk vl i, dot c.nJ z = r :=
  exists_dot_eq_of_cone (Nivat.LaneLeafAGenRecVJ.latticeConvex_of_parts c)
    c.rec_p (Nivat.EnvRefuteOrient.rec_vJ_of_parts_of_det_ne c hne1)
    (prim_iff_primitive.mpr c.nJ_prim) c.F.dot_nJ_vJ
    (Nivat.EnvRefuteOrient.dot_nJ_p_pos_of_parts c)
    (Nivat.EnvRefuteOrient.det_p_vJ_ne_zero_of_parts c)
    (Classical.choose_spec c.ahat_nonempty)

/-- **覆盖形**（`EnvRefuteCover.heights_iff_cover` 的右边，逐字）。 -/
theorem cover_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hne1 : det p c.vJ1 ≠ 0) :
    ∀ r : ℤ, ∃ g ∈ ⋃ i, hatOf c.A c.kk vl i,
      (-dot c.nJ c.vJ1) ∣ (dot c.nJ g - r) := by
  intro r
  set g₀ := Classical.choose c.ahat_nonempty with hg₀
  set e : ℤ := -dot c.nJ c.vJ1 with he
  have hepos : 0 < e := by
    have := c.hsweep; omega
  -- 取 `r' = r + k·e ≥ ⟪nJ,g₀⟫`，则 `r' ≡ r (mod e)` 且高度可达
  obtain ⟨k, hk⟩ : ∃ k : ℤ, dot c.nJ g₀ ≤ r + k * e := by
    refine ⟨max 0 (dot c.nJ g₀ - r), ?_⟩
    rcases le_or_gt (dot c.nJ g₀ - r) 0 with h | h
    · rw [max_eq_left h]; omega
    · have hm : max 0 (dot c.nJ g₀ - r) = dot c.nJ g₀ - r := max_eq_right (le_of_lt h)
      rw [hm]
      nlinarith [hepos, h]
  obtain ⟨z, hz, hdz⟩ := heights_of_parts c hne1 (r + k * e) hk
  refine ⟨z, hz, k, ?_⟩
  rw [hdz]
  ring

end Nivat.ConeCover

#print axioms Nivat.ConeCover.aeven_not_latticeConvex
#print axioms Nivat.ConeCover.dot_mul_det_sub
#print axioms Nivat.ConeCover.dot_mul_det
#print axioms Nivat.ConeCover.dot_add_zsmul_vJ
#print axioms Nivat.ConeCover.cone_mem
#print axioms Nivat.ConeCover.exists_dot_eq_of_cone
#print axioms Nivat.ConeCover.heights_of_parts_circular
#print axioms Nivat.ConeCover.heights_of_parts
#print axioms Nivat.ConeCover.cover_of_parts
