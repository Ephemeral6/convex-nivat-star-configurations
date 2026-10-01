/-
# `hcomb` 的闭式：`vJ` 被 `p`、`vJ1`、`nJ` 钉成一条**有向**射线

**为什么有这个文件。** `RecVJComb.parts_rec_vJ`（`RecVJComb.lean`）是主仓里**唯一不经
`bottom`** 的 `rec_vJ` 产者——展开后只吃 `c.hhp` / `c.hswept` / `c.rec_p` / `c.F.dot_nJ_vJ`
四条字段，外加侧条件

    hcomb : c.vJ = (a : ℤ) • p + (t : ℤ) • c.vJ1     (a t : ℕ)

而 `bottom` 那条路是循环的（`rec_vJ_of_parts` 的最后一个实参就是 `c.bottom`，lane-tower-hbase
2026-09-26 读出，集成者复核）。⟹ 洞 1 的 `rec_vJ` 一格，欠的**不是产者，是 `hcomb`**。
本文件把 `hcomb` 化成闭式，并给出它在链上**不免费**的内核见证。

## 结论一句话

对 `nJ` 取内积，`a` 与 `t` 被**唯一一条射线**锁死，于是（记 `α := ⟪nJ,p⟫`、`β := −⟪nJ,vJ1⟫`）

    α • vJ = t • W₀,        W₀ := β • p + α • vJ1                （`ray_eq`）

⟹ `det vJ W₀ = 0`（`det_vJ_W₀`）。

🔴 **自撤（2026-09-26，集成者，由 lane-env-refute 指出、集成者复算确认）：本文件初稿把
`det vJ W₀ = 0` 宣传成「链上可直接验算的必要条件，`det ≠ 0` ⟹ `hcomb` 当场死」。
那句话作废——该判据在链数据上恒真，永远不会触发。** 理由是两行算术：

    ⟪nJ, W₀⟫ = (−⟪nJ,vJ1⟫)·⟪nJ,p⟫ + ⟪nJ,p⟫·⟪nJ,vJ1⟫ = 0      ← **无条件**恒等式
    ⟪nJ, vJ⟫ = 0                                              ← 字段 `F.dot_nJ_vJ`

平面上两个都垂直于 `nJ ≠ 0`（`nJ_prim` ＋ `Primitive.ne_zero`）的向量必共线 ⟹ `det vJ W₀ = 0`
在链上**一条 `hcomb` 都不用**就成立（内核件见 `EnvRefuteOrient.lean` 的
`dot_nJ_W₀` / `det_of_perp_perp` / `det_vJ_W₀_vacuous`）。
⟹ `det_vJ_W₀` 本身**是真命题，不撤**，但它作为筛子**没有信息量**；`ray_eq` 的全部内容在
**标量**那一半（`t` 存在且落在 ℕ 里），共线那一半只是 `F.dot_nJ_vJ` 的重复。
这与本文件的主结论（死因是**朝向**）同向——恰恰是它把「朝向」之外的内容清空了。

⚠ 注意 `a t : ℕ` 而**不是** `ℤ`：`hcomb` 要的是 ℕ-**锥**，不是格。把它降格成
「`vJ ∈ ⟨p, vJ1⟩` 的格指标问题」只得到必要条件，会漏掉**定向**那一半——而下面的见证表明，
死掉的恰恰就是定向那一半。

## ⛔ 内核见证：链上现有的符号现货**推不出** `hcomb`

`hcomb_fails_on_full_sign_stock` 给出一组数据，它同时满足

* `Primitive nJ` / `vl` / `p` / `vJ1` / `vJ` 五条本原性；
* `p = −(c:ℤ) • vl` 且 `0 < c`（`exists_chainData` 的 `hp_neg`）；
* `0 < ⟪nJ,p⟫`（`parts_stock_lside` 在链上导出的那条）；
* `⟪nJ,vJ1⟫ < 0`（字段 `hsweep`）；
* `⟪nJ,vJ⟫ = 0`（字段 `F.dot_nJ_vJ`）；
* `det vl vJ1 ≠ 0`（**横截格**——共线格另有 `TowerHlevTile.not_hcomb_of_collinear` 直接否掉）；

**而 `hcomb` 对一切 `a t : ℕ` 为假**。数据：`nJ = (0,1)`、`vl = (1,−1)`、`c = 1`、
`p = (−1,1)`、`vJ1 = (1,−2)`、`vJ = (1,0)`。此时 `α = 1`、`β = 2`、`W₀ = (−1,0)`——
与 `vJ = (1,0)` **平行但反向**，而 `a t : ℕ` 补不出负号。

⟹ **欠的是一条「定向」字段**：某句话把 `vJ` 的指向与 `p`、`vJ1` 张成的锥绑定。按
`Primitive vJ1` 的先例，这记成**缺失字段**，不是可证项。它与 lane-env-refute ＋ lane-tower-hbase
两条独立证据查出的「37 条字段里没有任何一条约束 `⟪nJ,vl⟫ 的符号」（`dot _ vl` 命中 0）是
同一类欠账：结构保留了太多符号自由度。

⚠ 射程（勿放大）：本见证说的是「**这组前提**推不出 `hcomb`」。它**不**说 `hcomb` 在链上为假——
链上还有未被本见证兑现的字段。要否掉 `hcomb` 本身，须兑现全部 37 条。

## ⭐⭐ 但残余的可疑字段只剩 L-块：`hcomb` 路线基本是死路

**订正本文件初稿自己的话。** 初稿写「`escapeW` / `shellSubStrip` / `shellEnv` / `fillCover` /
`bottom` 中任何一条都可能钉死定向」——**前四条已排除**。按字段**类型**（剥掉 docstring 后）
逐条做标识符命中（正控 `hsweep` 命中 `vJ1`、负控 `I₀` 两者皆不命中，均通过；⛔ 不可用朴素正则，
须把 `vJ1` 与 `vJ` 分开切词）：

    命中裸 `vJ` 的字段共 6 条：  F   vJ_prim   bottom   ahat_halfPlane_L   ahat_attained_L   nfp_L
    `escapeW` / `shellSubStrip` / `shellEnv` / `fillCover`： **一条都不提 `vJ`**

⟹ 那四条 shell 字段**在语法上就不可能**约束 `vJ` 的定向（它们只谈 `w` / `vJ1` / `nJ` / `cJ`）。

再按 `hcomb` 的形状筛：`hcomb` 把 `vJ` 与 `p`、`vJ1` 张成的 **ℕ-锥**绑定，所以能蕴含它的字段
必须同时提到 `vJ` 与（`vJ1` 或 `p`）。结果：

    同时命中 `vJ` 与 `vJ1` 的字段： **只有 `bottom`**（经 `MaxEnv.reachSet … vJ1`）
    同时命中 `vJ` 与 `p`  的字段： `ahat_halfPlane_L` / `ahat_attained_L` / `nfp_L`（皆经 `det p vJ`）
    只命中 `vJ` 的字段：          `F : FaceBlock S nJ vJ` / `vJ_prim : Primitive vJ`

⛔ **`bottom` 这条出口是自毁的**：有了 `bottom` 就已经能用 `rec_vJ_of_parts` 直接拿到 `rec_vJ`，
根本不需要 `hcomb`。⟹ `hcomb` 路线要活，只能靠 **L-块**。

⟹ **`hcomb` 路线现在收敛成唯一一个问题**：L-块能否排除本见证那组数据的定向？

🔴 **已由内核回答，而且答案与初稿相反（2026-09-26，lane-env-refute §19，集成者读证明体复核）：
L-块**排除得了**，而且排除理由与这组数据的具体数值无关。** 初稿在这里写「法向 `= (1,1)`、
`dot (1,1) vJ = 1 > 0`——**未被 L-块排除**」，并自标为「读法不是内核事实」。那条读法**是错的**：

    EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg (c : ChainDataGeomParts …)
      : 0 ≤ det p c.vJ * det p c.vJ1

只用 `ahat_nonempty` / `rec_p` / `hswept` / `dot_nJ_p` / `ahat_halfPlane_L` 五条字段（不经
`bottom`、不经 `nfp_L`、不经原文）。机制：L-法向 `m := det p vJ • (-p.2, p.1)` 恒有 `dot m p = 0`；
`rec_p` ＋ `0 < dot nJ p` ⟹ `Â` 的 `nJ`-高度无上界；`hswept` ⟹ 高度仍 `≥ cJ` 时可沿 `vJ1`
走任意步，每步 `m`-值降 `dot m vJ1`；故 `det p vJ * det p vJ1 < 0` 会让 `m` 在 `Â` 上无下界，
与 `ahat_halfPlane_L` 冲突。

⟹ `EnvRefuteOrient.stock_witness_not_on_chain`：本文件见证的 `p = (−1,1)`、`vJ = (1,0)`、
`vJ1 = (1,−2)` 有 `det p vJ = −1`、`det p vJ1 = 1`，积 `= −1 < 0`
⟹ **不存在**以它为 `vJ`/`vJ1` 的 `ChainDataGeomParts`（内核 `False`）。

⟹ `hcomb_fails_on_full_sign_stock` 的射程因此**收窄到**「这组**链外**数据推不出 `hcomb`」。
本文件文首那条 ⚠ 射程自限（「不说 `hcomb` 在链上为假」）**成立且必要**，但结论更弱：
这个见证**不构成**「缺一条定向字段」的证据，因为它根本不是链上的点。
🔴 **因此「欠的是一条定向字段」这个标的也已作废**——见 §下。

## ⭐ 现在的真标的（env-refute §19–§22，集成者复核签名与证明体）

定向的**符号**那一半是链上现货（`orient_sign_of_parts`，由上面的同号筛 ＋ `0 < dot nJ p` 给）。
欠账精确地是 `EnvRefuteOrient.hcomb_iff_cramer` 的三条（`det p vJ1 ≠ 0` 下是 `↔`）：

    (1) det p vJ1 ≠ 0                        —— 横截，显式 binder
    (2) ∃ t : ℕ, det p vJ  = det p vJ1 * t   —— 符号免费，只欠整除
    (3) ∃ a : ℕ, det vJ vJ1 = det p vJ1 * a  —— 整除与符号都无产者

⟹ 接链请用 `EnvRefuteOrient.rec_vJ_of_cramer`，**不要**用 `W₀` 路线（`hOrient_of_dvd` /
`rec_vJ_of_dvd_of_prim_p` 保留不删，但它们要 `Primitive p`，而 `p = -(c:ℤ)•vl` 只有 `c = 1` 才本原）。
⟹ 另见 `RecVJPrimDir.lean`（集成者）：把方向从 `p` 换成**本原**的 `-vl` 后 (1)(2) 不变、
**(3) 严格变弱**（少一个因子 `c`），且 `-vl` 上的递归由 `LeafAGenRecP.rec_p_free` 零假设兑现。
-/
import Nivat.External.Colle.RecVJComb

namespace Nivat.HcombOrient

open Nivat Nivat.LE2

/-- `⟪n, a•p + t•q⟫` 展开。 -/
theorem dot_smul_add (n p q : ℤ × ℤ) (a t : ℤ) :
    dot n (a • p + t • q) = a * dot n p + t * dot n q := by
  simp [dot, Prod.smul_def, smul_eq_mul]
  ring

/-- **高度方程**：`hcomb` ＋ `⟪nJ,vJ⟫ = 0` 把 `(a,t)` 锁在一条射线上。 -/
theorem height_eq {nJ p vJ1 vJ : ℤ × ℤ} {a t : ℤ}
    (hc : vJ = a • p + t • vJ1) (h0 : dot nJ vJ = 0) :
    a * dot nJ p = t * (- dot nJ vJ1) := by
  have := dot_smul_add nJ p vJ1 a t
  rw [← hc, h0] at this
  linarith

/-- **`W₀`**：只由 `nJ` / `p` / `vJ1` 算出的方向向量，`hcomb` 下 `vJ` 必与它同向。 -/
def W₀ (nJ p vJ1 : ℤ × ℤ) : ℤ × ℤ := (- dot nJ vJ1) • p + (dot nJ p) • vJ1

/-- ⭐ **闭式**：`⟪nJ,p⟫ • vJ = t • W₀`。没有 gcd、没有整除条件，纯等式。 -/
theorem ray_eq {nJ p vJ1 vJ : ℤ × ℤ} {a t : ℤ}
    (hc : vJ = a • p + t • vJ1) (h0 : dot nJ vJ = 0) :
    (dot nJ p) • vJ = t • W₀ nJ p vJ1 := by
  have hat : a * dot nJ p = t * (- dot nJ vJ1) := height_eq hc h0
  rw [hc, W₀]
  ext
  · simp [Prod.smul_def, smul_eq_mul]
    linear_combination p.1 * hat
  · simp [Prod.smul_def, smul_eq_mul]
    linear_combination p.2 * hat

/-- **链上必要条件：`hcomb` ⟹ `vJ` 与 `W₀` 共线。**

🔴 **作为筛子已作废（见文首自撤）**：链上 `⟪nJ,W₀⟫ = 0` 是无条件恒等式、`⟪nJ,vJ⟫ = 0` 是字段
`F.dot_nJ_vJ`，两者都垂直于 `nJ ≠ 0` ⟹ 结论在链上**不用 `hcomb`** 就恒成立
（`EnvRefuteOrient.det_vJ_W₀_vacuous`）。本命题**为真、不撤**，但**不要**拿它去验算链数据。 -/
theorem det_vJ_W₀ {nJ p vJ1 vJ : ℤ × ℤ} {a t : ℤ}
    (hc : vJ = a • p + t • vJ1) (h0 : dot nJ vJ = 0) (hα : dot nJ p ≠ 0) :
    det vJ (W₀ nJ p vJ1) = 0 := by
  have h := ray_eq hc h0
  have : (dot nJ p) * det vJ (W₀ nJ p vJ1) = 0 := by
    have hd : det ((dot nJ p) • vJ) (W₀ nJ p vJ1) = (dot nJ p) * det vJ (W₀ nJ p vJ1) := by
      simp [det, Prod.smul_def, smul_eq_mul]; ring
    rw [← hd, h]
    simp [det, Prod.smul_def, smul_eq_mul]; ring
  exact (mul_eq_zero.mp this).resolve_left hα

/-- ⛔ **内核见证：链上现有的符号现货推不出 `hcomb`（横截格）。**
全部前提逐条对应 `exists_chainData` 的 binder 或 `ChainDataGeomParts` 的字段（见文首），
而侧条件对一切 `a t : ℕ` 为假。死因是**定向**：`W₀ = (−1,0)` 与 `vJ = (1,0)` 反向，
`a t : ℕ` 补不出负号。 -/
theorem hcomb_fails_on_full_sign_stock :
    ∃ (nJ vl p vJ1 vJ : ℤ × ℤ) (c : ℕ),
      Primitive nJ ∧ Primitive vl ∧ Primitive p ∧ Primitive vJ1 ∧ Primitive vJ ∧
      0 < c ∧ p = -(c : ℤ) • vl ∧
      0 < dot nJ p ∧ dot nJ vJ1 < 0 ∧ dot nJ vJ = 0 ∧ det vl vJ1 ≠ 0 ∧
      (∀ a t : ℕ, vJ ≠ (a : ℤ) • p + (t : ℤ) • vJ1) := by
  refine ⟨(0, 1), (1, -1), (-1, 1), (1, -2), (1, 0), 1, ?_, ?_, ?_, ?_, ?_,
    one_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isCoprime_one_right
  · exact isCoprime_one_left
  · exact isCoprime_one_right
  · exact isCoprime_one_left
  · exact isCoprime_one_left
  · ext <;> simp [Prod.smul_def]
  · norm_num [dot]
  · norm_num [dot]
  · norm_num [dot]
  · norm_num [det]
  · intro a t h
    rw [Prod.ext_iff] at h
    simp [Prod.smul_def, smul_eq_mul] at h
    omega

/-- **同一组数据把 `W₀` 的值也钉出来**，供人手算复核：`W₀ = (−1,0)`，与 `vJ = (1,0)` 反向。 -/
theorem witness_W₀ : W₀ ((0, 1) : ℤ × ℤ) ((-1, 1) : ℤ × ℤ) ((1, -2) : ℤ × ℤ) = (-1, 0) := by
  ext <;> norm_num [W₀, dot, Prod.smul_def]

#print axioms Nivat.HcombOrient.dot_smul_add
#print axioms Nivat.HcombOrient.height_eq
#print axioms Nivat.HcombOrient.ray_eq
#print axioms Nivat.HcombOrient.det_vJ_W₀
#print axioms Nivat.HcombOrient.hcomb_fails_on_full_sign_stock
#print axioms Nivat.HcombOrient.witness_W₀

end Nivat.HcombOrient
