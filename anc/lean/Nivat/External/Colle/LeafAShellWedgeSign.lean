/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-leafa-shell
-/
import Nivat.External.Colle.BottomFree
import Nivat.External.Colle.RecVJTransverse

set_option autoImplicit false

/-!
# 楔形支撑界 `hsupp` 是字段的推论，两格通用

`BottomHz0Collapse.hdz_hz0_hline0_of_wedge`（集成者）把 `bottom` 的前三条合取
（`hdz` ∧ `hz₀` ∧ `hline0`）归约到一个楔形 `(nprevJ, V)` 的三条前提 ＋ 剩余类覆盖。
`EnvRefuteOrient` 的 §33/§34（lane-env-refute）把这三条前提里的**前两条**（正交 ＋ 定向）
证成免费（`exists_nprevJ`），并把第三条（支撑界 `hsupp`）夹在一条**必要条件**里：

    det_sign_of_supp :  hsupp ⟹ 0 ≤ det vJ1 p * det vJ1 vJ

本文件补上另外两块，于是 `hsupp` 这条债关闭：

* §2 `det_sign_of_parts`：那个符号条件在链上**恒成立**（是字段的推论）；
* §1 `supp_of_two_walls` ＋ §3 `supp_of_parts`：符号条件**反过来也够**。

⟹ `supp_of_parts` ＋ `exists_nprevJ` 给出 `exists_wedge_of_parts`：**整个楔形在链上免费，
与 `det p vJ1` 是否为零无关**。

## §1 为什么两条墙就够（先算的那个几何实例，硬规矩 6）

`⋃ᵢ Âᵢ` 上有两条与 `i` 无关的墙（`CORE-HOLES.md` 的常设纪律 #7 记的就是这一条）：

| 墙 | 字段 | 法向 |
|---|---|---|
| `cJ ≤ ⟪nJ, z⟫` | `hhp`（`ChainPartsFeed.lean` 的 `hhp` 字段） | `nJ` |
| `cL ≤ ⟪det p vJ · rot p, z⟫` | `ahat_halfPlane_L` | `det p vJ · rot p` |

两个法向不平行：`det nJ (rot p) = ⟪nJ, p⟫ ≠ 0`（字段 `dot_nJ_p`）。
⟹ 两个半平面的交是一个**平移后的二维锥**，两条棱的方向恰是 `p` 与 `vJ`：

* `vJ` 是棱：`⟪nJ, vJ⟫ = 0`（`F.dot_nJ_vJ`）且 `⟪det p vJ · rot p, vJ⟫ = (det p vJ)² > 0`；
* `p` 是棱：`⟪det p vJ · rot p, p⟫ = 0` 且 `⟪nJ, p⟫ > 0`。

一个线性泛函在这个锥上有上界 ⟺ 它在两条棱上非正。要的是 `⟪n, vJ⟫ < 0`，
所以只剩 `⟪n, p⟫ ≤ 0` 需要证 —— 那正是 `det_sign_of_supp` 的逆命题。

数值实例（在 Lean 之前手算的）：`nJ = (0,1)`、`vJ = (1,0)`、`vJ1 = (0,-1)`、`p = (0,1)`。
此时 `det p vJ = -1`、`det p vJ1 = 0`，锥是 `{x ≥ cL} ∩ {y ≥ cJ}` 的一个平移，
合法法向 `n = (-1,0)`（`⟪n,vJ1⟫ = 0`、`⟪n,vJ⟫ = -1 < 0`、`⟪n,p⟫ = 0 ≤ 0`），
上界常数 `-cL`。

## §2 符号闸在链上恒成立 —— 附带一条空真判定

`det_sign_of_parts` 的机理：`dot_mul_det_swap` 取 `n := nJ`、`v := vJ`、`a := p`、`b := vJ1`，
用 `⟪nJ,vJ⟫ = 0` 得

    ⟪nJ,p⟫ · det vJ vJ1 = ⟪nJ,vJ1⟫ · det vJ p

两边乘 `det p vJ1` 后，目标 `⟪nJ,p⟫ · (det vJ1 p · det vJ1 vJ)` 正好等于
`−⟪nJ,vJ1⟫ · (det p vJ · det p vJ1)`，其中后一个因子由
`EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg`（字段，不经 `bottom`）非负，
`−⟪nJ,vJ1⟫ > 0` 由字段 `hsweep`。

⚠ **推论（`not_det_sign_neg`）：`EnvRefuteOrient.not_supp_of_det_sign` 的前提在链上不可满足**，
所以那条否结果对链上构型是空真的（PROTOCOL §41）。特别地，`BottomFree.lean` 抬头引的那组
「满足 `hdz_hz0_hline0_free` 每一条前提」的数值（`nJ=(0,1)`、`vJ=(1,0)`、`vJ1=(0,-1)`、
`p=(-1,1)`）**不是链上构型**：它给 `det p vJ = -1`、`det p vJ1 = 1`，积 `= -1 < 0`，
与 `det_p_vJ_mul_det_p_vJ1_nonneg` 直接冲突 —— 和 `EnvRefuteOrient.stock_witness_not_on_chain`
判掉另一组数据是同一个机制。该行的结论（「本文件在该半格上是空真的」）需要改成
「该半格在链上是空的」；那是集成者的文件，由集成者改，本文件只报告。

## §3 与 `EnvRefuteOrient.supp_of_collinear` 的关系（PROTOCOL §91 归属）

* 路线是 lane-env-refute 的：他们本轮报的纸面猜测②「`hsupp` ⟺ `-nprevJ` 落在
  `cone(nJ, det p vJ · rot p)` 里」就是 §1 的锥判据，并明说「未证、不主张，等 team-lead 派」。
  本文件把那条猜测证了，并发现符号那一半（§2）也是字段推论。
* `supp_of_parts` **严格推广** `EnvRefuteOrient.supp_of_collinear`：后者吃 `hpar`
  （共线格），本条不吃，两格通用。按盲区 3 两条都留，不删 `supp_of_collinear`。
* `supp_of_two_walls` 的载体 `T` 是抽象集合，不吃 `ChainDataGeomParts`；
  §1 的两条墙来自字段，但定理本身对任意满足两条墙的 `T` 成立。

## §4 射程自限

1. 本文件**不**碰剩余类覆盖 `hcov`。横截格里它由 `ConeCover.cover_of_parts` 免费
   （集成者第 243 轮），共线格里它仍是硬债（那一侧要 `rec_vJ`，而共线格的 `rec_vJ`
   按 `RecVJTransverse.lean` 的射程自限第 1 条是未结的硬债）。
2. 本文件**不**碰 `hvJ_eq : vJ = dir (-nJ)`（第 179 轮红线，定向位未裁）、
   也不碰 `hnegnJ : -nJ ∈ E ↑𝒮_φ`。
3. 本文件**不**声称 `Âinf` 有界。`supp_of_parts` 给的是在**楔形法向**上的上界；
   `EnvRefuteOrient.not_bddAbove_of_rec` 说 `Âinf` 沿 `+p` 无界，两者不矛盾：
   楔形法向在 `p` 上取值为 `≤ 0`。
-/

namespace Nivat.LeafAShellWedgeSign

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm Nivat.ChainAsm.Aparts

variable {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}

/-! ## §1 抽象：两条墙 ＋ 两个符号 ⟹ 支撑界 -/

/-- 平面恒等式，无前提：`⟪nJ,q⟫·⟪n,z⟫ = ⟪n,q⟫·⟪nJ,z⟫ + det nJ n · det q z`。

Cramer 分解：把任意泛函 `⟪n,·⟫` 写成两条墙的法向（`nJ` 与 `rot q`，后者对应 `det q ·`）
的组合，系数是两个行列式。 -/
theorem dot_split_two_walls (nJ n q z : ℤ × ℤ) :
    dot nJ q * dot n z = dot n q * dot nJ z + det nJ n * det q z := by
  show (nJ.1 * q.1 + nJ.2 * q.2) * (n.1 * z.1 + n.2 * z.2)
      = (n.1 * q.1 + n.2 * q.2) * (nJ.1 * z.1 + nJ.2 * z.2)
        + (nJ.1 * n.2 - nJ.2 * n.1) * (q.1 * z.2 - q.2 * z.1)
  ring

/-- ⭐⭐ **两条 `i`-无关的墙 ＋ 两个符号 ⟹ 支撑界存在。**

`T` 落在 `{⟪nJ,·⟫ ≥ cJ}` 与 `{det q vJ · det q · ≥ cL}` 的交里；两条墙的法向不平行
（由 `0 < ⟪nJ,q⟫` 保证），该交是 `cone(q, vJ)` 的平移。结论的常数显式：
`|⟪n,q⟫·(det q vJ)²·cJ + det nJ n·det q vJ·cL|`。

载体 `T` 抽象，不吃 `ChainDataGeomParts`。逐量词对应见本文件抬头 §1 的表。 -/
theorem supp_of_two_walls {T : Set (ℤ × ℤ)} {nJ n q vJ : ℤ × ℤ} {cJ cL : ℤ}
    (hα : 0 < dot nJ q) (hD : det q vJ ≠ 0) (hnJvJ : dot nJ vJ = 0)
    (hA : dot n q ≤ 0) (hnvJ : dot n vJ < 0) (hnne : n ≠ 0)
    (hwall1 : ∀ z ∈ T, cJ ≤ dot nJ z)
    (hwall2 : ∀ z ∈ T, cL ≤ det q vJ * det q z) :
    ∃ V : ℤ × ℤ, ∀ z ∈ T, dot n z ≤ dot n V := by
  have hα1 : 1 ≤ dot nJ q := by linarith [Int.add_one_le_iff.mpr hα]
  have hEsq : 1 ≤ det q vJ * det q vJ := by
    rcases lt_or_gt_of_ne hD with h | h <;> nlinarith
  -- `det nJ n * det q vJ = ⟪nJ,q⟫ * ⟪n,vJ⟫ < 0`
  have hBE : det nJ n * det q vJ = dot nJ q * dot n vJ := by
    have hid := dot_split_two_walls nJ n q vJ
    rw [hnJvJ, mul_zero, zero_add] at hid
    linarith
  have hBEneg : det nJ n * det q vJ < 0 := by
    rw [hBE]; exact mul_neg_of_pos_of_neg hα hnvJ
  have hAE : dot n q * (det q vJ * det q vJ) ≤ 0 := by
    nlinarith [mul_nonneg (neg_nonneg.mpr hA) (by linarith : (0 : ℤ) ≤ det q vJ * det q vJ)]
  have hαE : 1 ≤ dot nJ q * (det q vJ * det q vJ) := by nlinarith
  obtain ⟨V, hV⟩ := Nivat.EnvRefuteOrient.exists_dot_ge hnne
    |dot n q * (det q vJ * det q vJ) * cJ + det nJ n * det q vJ * cL|
  refine ⟨V, fun z hz => ?_⟩
  have h1 : cJ ≤ dot nJ z := hwall1 z hz
  have h2 : cL ≤ det q vJ * det q z := hwall2 z hz
  have hid : dot nJ q * dot n z = dot n q * dot nJ z + det nJ n * det q z :=
    dot_split_two_walls nJ n q z
  -- 整个恒等式乘上 `(det q vJ)²`，使第二条墙以原样出现
  have hmul : dot nJ q * (det q vJ * det q vJ) * dot n z
      = dot n q * (det q vJ * det q vJ) * dot nJ z
        + det nJ n * det q vJ * (det q vJ * det q z) := by
    linear_combination (det q vJ * det q vJ) * hid
  have hb1 : dot n q * (det q vJ * det q vJ) * dot nJ z
      ≤ dot n q * (det q vJ * det q vJ) * cJ := by
    nlinarith [mul_nonneg (neg_nonneg.mpr hAE) (sub_nonneg.mpr h1)]
  have hb2 : det nJ n * det q vJ * (det q vJ * det q z)
      ≤ det nJ n * det q vJ * cL := by
    nlinarith [mul_nonneg (neg_nonneg.mpr hBEneg.le) (sub_nonneg.mpr h2)]
  have hbound : dot nJ q * (det q vJ * det q vJ) * dot n z
      ≤ dot n q * (det q vJ * det q vJ) * cJ + det nJ n * det q vJ * cL := by
    rw [hmul]; linarith
  have hKle := le_abs_self
    (dot n q * (det q vJ * det q vJ) * cJ + det nJ n * det q vJ * cL)
  have hXle : dot n z
      ≤ |dot n q * (det q vJ * det q vJ) * cJ + det nJ n * det q vJ * cL| := by
    by_contra hcon
    push_neg at hcon
    have hXpos : 0 < dot n z := lt_of_le_of_lt (abs_nonneg _) hcon
    have hprod : 0 ≤ (dot nJ q * (det q vJ * det q vJ) - 1) * dot n z :=
      mul_nonneg (by linarith) (le_of_lt hXpos)
    nlinarith [hbound, hKle, hprod]
  exact le_trans hXle hV

/-! ## §2 链上：符号闸恒成立 -/

/-- ⭐⭐⭐ **`hsupp` 的符号必要条件在链上恒成立。**

`EnvRefuteOrient.det_sign_of_supp` 证 `hsupp ⟹ 0 ≤ det vJ1 p * det vJ1 vJ`；
本条证明右边是字段的推论。机理见本文件抬头 §2。 -/
theorem det_sign_of_parts (c : ChainDataGeomParts η xper vl p S gen) :
    0 ≤ det c.vJ1 p * det c.vJ1 c.vJ := by
  have hα : 0 < dot c.nJ p := Nivat.EnvRefuteOrient.dot_nJ_p_pos_of_parts c
  have hβ : dot c.nJ c.vJ1 < 0 := c.hsweep
  have hknown : 0 ≤ det p c.vJ * det p c.vJ1 :=
    Nivat.EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg c
  have hid : dot c.nJ p * det c.vJ c.vJ1 - dot c.nJ c.vJ1 * det c.vJ p = 0 := by
    have h := Nivat.EnvRefuteOrient.dot_mul_det_swap c.nJ c.vJ p c.vJ1
    rw [c.F.dot_nJ_vJ, zero_mul] at h
    exact h
  have hmain : dot c.nJ p * (det c.vJ1 p * det c.vJ1 c.vJ)
      = -dot c.nJ c.vJ1 * (det p c.vJ * det p c.vJ1) := by
    simp only [det] at hid ⊢
    linear_combination (p.1 * c.vJ1.2 - p.2 * c.vJ1.1) * hid
  have h1 : 0 ≤ -dot c.nJ c.vJ1 * (det p c.vJ * det p c.vJ1) :=
    mul_nonneg (by linarith) hknown
  by_contra hcon
  push_neg at hcon
  nlinarith [hmain, h1, hα, mul_pos hα (neg_pos.mpr hcon)]

/-- ⚠ **`EnvRefuteOrient.not_supp_of_det_sign` 的前提在链上不可满足。**

⟹ 那条否结果对链上构型空真（PROTOCOL §41）；`BottomFree.lean` 抬头引的那组数值
不是链上构型，理由见本文件抬头 §2。 -/
theorem not_det_sign_neg (c : ChainDataGeomParts η xper vl p S gen) :
    ¬ (det c.vJ1 p * det c.vJ1 c.vJ < 0) :=
  not_lt.mpr (det_sign_of_parts c)

/-! ## §3 链上：楔形整条免费 -/

/-- ⭐⭐⭐ **楔形支撑界是字段的推论，两格通用。**

`⟪n,p⟫ ≤ 0` 由 `det_sign_of_parts` ＋ `dot_mul_det_swap` 得（这是
`EnvRefuteOrient.dot_p_nonpos_of_supp` 的逆向）；两条墙分别是字段 `hhp` 与 `ahat_halfPlane_L`。

⟹ **严格推广 `EnvRefuteOrient.supp_of_collinear`：不吃 `hpar`。** 按盲区 3 两条都留。 -/
theorem supp_of_parts (c : ChainDataGeomParts η xper vl p S gen) {n : ℤ × ℤ}
    (hnvJ1 : dot n c.vJ1 = 0) (hnvJ : dot n c.vJ < 0) :
    ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i, dot n z ≤ dot n V := by
  have hvJne : c.vJ ≠ 0 := (prim_iff_primitive.mpr c.vJ_prim).ne_zero
  have hα : 0 < dot c.nJ p := Nivat.EnvRefuteOrient.dot_nJ_p_pos_of_parts c
  have hD : det p c.vJ ≠ 0 :=
    Nivat.EnvRefuteOrient.det_ne_zero_of_perp hvJne c.F.dot_nJ_vJ c.dot_nJ_p
  have hnne : n ≠ 0 := by
    intro h0
    rw [h0] at hnvJ
    simp [dot] at hnvJ
  -- `⟪n,p⟫ ≤ 0`：符号闸由 `det_sign_of_parts` 兑现
  have hA : dot n p ≤ 0 := by
    have hdet : det c.vJ1 c.vJ ≠ 0 :=
      Nivat.EnvRefuteOrient.det_vJ1_vJ_ne_zero (prim_iff_primitive.mpr c.vJ_prim)
        c.F.dot_nJ_vJ c.hsweep
    have hsq : 1 ≤ det c.vJ1 c.vJ * det c.vJ1 c.vJ := by
      rcases lt_or_gt_of_ne hdet with h | h <;> nlinarith
    have hid := Nivat.EnvRefuteOrient.dot_mul_det_swap n c.vJ1 c.vJ p
    rw [hnvJ1, zero_mul] at hid
    have hkey : dot n p * (det c.vJ1 c.vJ * det c.vJ1 c.vJ)
        = dot n c.vJ * (det c.vJ1 p * det c.vJ1 c.vJ) := by
      linear_combination (-(det c.vJ1 c.vJ)) * hid
    have hrhs : dot n c.vJ * (det c.vJ1 p * det c.vJ1 c.vJ) ≤ 0 := by
      nlinarith [mul_nonneg (neg_nonneg.mpr hnvJ.le) (det_sign_of_parts c)]
    by_contra hcon
    push_neg at hcon
    have hp1 : 1 ≤ dot n p := by linarith [Int.add_one_le_iff.mpr hcon]
    nlinarith [hkey, hrhs, hsq,
      mul_le_mul_of_nonneg_right hp1 (by linarith : (0 : ℤ) ≤ det c.vJ1 c.vJ * det c.vJ1 c.vJ)]
  refine supp_of_two_walls (cJ := c.cJ) (cL := c.cL) hα hD c.F.dot_nJ_vJ hA hnvJ hnne ?_ ?_
  · intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact c.hhp i hi
  · intro z hz
    have hLz : c.cL ≤ dot (det p c.vJ • ((-p.2, p.1) : ℤ × ℤ)) z := c.ahat_halfPlane_L z hz
    have hsm : dot (det p c.vJ • ((-p.2, p.1) : ℤ × ℤ)) z = det p c.vJ * det p z := by
      show det p c.vJ * -p.2 * z.1 + det p c.vJ * p.1 * z.2
          = det p c.vJ * (p.1 * z.2 - p.2 * z.1)
      ring
    rw [hsm] at hLz
    exact hLz

/-- **`EnvRefuteOrient.hline0_wedge_cost` 的 `hsupp`（`∀ n0` 量化形）在链上免费。**

那条综合把楔形代价收成「对**任意**合法法向都有支撑界」；`supp_of_parts` 对任意合法法向
都成立，所以直接兑现。 -/
theorem supp_all_of_parts (c : ChainDataGeomParts η xper vl p S gen) :
    ∀ n0 : ℤ × ℤ, dot n0 c.vJ1 = 0 → dot n0 c.vJ < 0 →
      ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i, dot n0 z ≤ dot n0 V :=
  fun _ h1 h2 => supp_of_parts c h1 h2

/-- ⭐⭐⭐ **整个楔形（法向 ＋ 顶点 ＋ 正交 ＋ 定向 ＋ 支撑界）在链上免费，两格通用。**

法向与前两条来自 `EnvRefuteOrient.exists_nprevJ`（lane-env-refute §33），
支撑界来自 `supp_of_parts`。 -/
theorem exists_wedge_of_parts (c : ChainDataGeomParts η xper vl p S gen) :
    ∃ n V : ℤ × ℤ, dot n c.vJ1 = 0 ∧ dot n c.vJ < 0 ∧
      ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i, dot n z ≤ dot n V := by
  obtain ⟨n, _, hnvJ1, hnvJ⟩ :=
    Nivat.EnvRefuteOrient.exists_nprevJ (prim_iff_primitive.mpr c.vJ_prim)
      c.F.dot_nJ_vJ c.hsweep
  obtain ⟨V, hV⟩ := supp_of_parts c hnvJ1 hnvJ
  exact ⟨n, V, hnvJ1, hnvJ, hV⟩

/-! ## §4 后果：`bottom` 的前三条合取 -/

/-- ⭐⭐⭐ **两格通用：`hdz` ∧ `hz₀` ∧ `hline0` 只欠剩余类覆盖 `hcov`，楔形全免。**

与 `BottomHz0Collapse.hdz_hz0_hline0_of_cover_collinear` 比：**不吃 `hpar`**，
也不吃 `ahat_attained_L`。与 `BottomFree.hdz_hz0_hline0_free_wedge` 比：
楔形的三条 binder（`nprevJ`/`V`/`hnpvJ1`/`hnpvJ`/`hsupp`）全部消失。 -/
theorem hdz_hz0_hline0_of_cover (c : ChainDataGeomParts η xper vl p S gen)
    (hcov : ∀ r : ℤ, ∃ g ∈ ⋃ i, hatOf c.A c.kk vl i,
      (-dot c.nJ c.vJ1) ∣ (dot c.nJ g - r))
    (ε : ℕ) :
    ∃ z₀ : ℤ × ℤ, dot c.nJ z₀ = c.cJ - (ε : ℤ) - 1 ∧
      z₀ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1 ∧
      ∀ z ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1,
        dot c.nJ z = c.cJ - (ε : ℤ) - 1 → ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • c.vJ := by
  obtain ⟨n, V, hnvJ1, hnvJ, hsupp⟩ := exists_wedge_of_parts c
  exact Nivat.BottomHz0Collapse.hdz_hz0_hline0_of_wedge c n V hnvJ1 hnvJ hsupp hcov ε

/-- ⭐⭐⭐ **横截格：`hdz` ∧ `hz₀` ∧ `hline0` 全部免费。**

`hcov` 由 `ConeCover.cover_of_parts`（集成者第 243 轮），楔形由 `exists_wedge_of_parts`。
⟹ 横截格里 `bottom` 的前三条合取**一条 binder 都不欠**。

⚠ 共线格不在射程内：那里 `hcov` 仍是硬债（`ConeCover.cover_of_parts` 要 `det p vJ1 ≠ 0`，
退回 `RecVJFromParts.rec_vJ_of_parts` 会经 `c.bottom` 成环，见 `RecVJTransverse.lean`
的射程自限第 1 条）。 -/
theorem hdz_hz0_hline0_of_parts_transverse (c : ChainDataGeomParts η xper vl p S gen)
    (hne1 : det p c.vJ1 ≠ 0) (ε : ℕ) :
    ∃ z₀ : ℤ × ℤ, dot c.nJ z₀ = c.cJ - (ε : ℤ) - 1 ∧
      z₀ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1 ∧
      ∀ z ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1,
        dot c.nJ z = c.cJ - (ε : ℤ) - 1 → ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • c.vJ :=
  hdz_hz0_hline0_of_cover c (Nivat.ConeCover.cover_of_parts c hne1) ε

end Nivat.LeafAShellWedgeSign

#print axioms Nivat.LeafAShellWedgeSign.dot_split_two_walls
#print axioms Nivat.LeafAShellWedgeSign.supp_of_two_walls
#print axioms Nivat.LeafAShellWedgeSign.det_sign_of_parts
#print axioms Nivat.LeafAShellWedgeSign.not_det_sign_neg
#print axioms Nivat.LeafAShellWedgeSign.supp_of_parts
#print axioms Nivat.LeafAShellWedgeSign.supp_all_of_parts
#print axioms Nivat.LeafAShellWedgeSign.exists_wedge_of_parts
#print axioms Nivat.LeafAShellWedgeSign.hdz_hz0_hline0_of_cover
#print axioms Nivat.LeafAShellWedgeSign.hdz_hz0_hline0_of_parts_transverse
