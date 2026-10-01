/-
Copyright (c) 2026 Nivat Formalization Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lane-leafa-gen
-/
import Nivat.External.Colle.TowerConstruct

/-!
# `3 ≤ d.m ⟹ candSet ≠ ∅`（lane-leafa-gen）

`Nivat.ColleReg.candSet`（`Nivat/External/Colle/TowerConstruct.lean:246`）逐字是

    candSet d nℓ u' i = ((Finset.univ.erase i).image (wgen d nℓ)).erase u'

本文件证：只要 `3 ≤ d.m`，它非空。

## 原文对应（硬规矩 5）

⚠ **本文件不引入任何新 `Prop`，因此没有原文锚点可指，这是故意的。** 这里证的是关于
**我们自己的 Lean 构造** `candSet` 的一条基数事实（`.erase i` 去掉一个下标、`wgen` 在剩下的
下标上单射、`.erase u'` 至多再去掉一个），原文里没有对应物，也不该有：`candSet` 是
team-lead 2026-09-22 的候选集配方（见 `TowerConstruct.lean:240-247` 的 docstring），不是
`scratch/b3_colle2.txt` 的转录。

唯一新增的假设 `hm3 : 3 ≤ d.m` **有**原文来路，且不是我们加的量词（硬规矩 5）：
`b3_colle2.txt:230`（Corollary 1.16 的证明内，本轮当轮亲读）逐字是「Since Conjecture 1.11
holds for $m=2$ (see Theorem 1.12), we may assume $m\geq 3$」，依据是 `:180`/`:182` 的
Theorem 1.12（Szabados [20]，无条件外部定理：`m = 2` 的 `ℤ`-minimal 周期分解不具 low convex
complexity）。Lean 侧的生产者是 `Nivat.OrderThree.three_le_m`
（`Nivat/External/Colle/OrderThree.lean:292`，`hξ : IsMinimalCounterexample ξ` ＋
`d : DecompDataZ ξ` ⟹ `3 ≤ d.toDecompData.m`），由消费者一行兑现，本文件照常写成假设。
（来路由 lane-towerpkg 2026-09-24 指出；`:230` / `:180` 两处我本轮自己读过，`three_le_m` 的
`#print axioms` 我**未复核**。）

## 前提表

`hvl_prim` / `hprim` / `hperp` / `i` / `hdoth` 都是 `exists_cutResidualR_of_claim46`
（`Nivat/External/Colle/RegionSteps.lean`）的原生 binder，且原封不动地只用于把
`det_wgen_h_eq_zero` / `dot_wgen_neg`（`TowerConstruct.lean:623` / `:158`）的前提喂饱。
唯一新增的是 `hm3 : 3 ≤ d.m`，即上面那条链上事实。

## 为什么 `wgen` 在 `j ≠ i` 上单射

`wgen d nℓ j = primPart (orientGen d nℓ j)`（`TowerConstruct.lean:144`），而
`orientGen` 只是按 `dot nℓ (d.h j) < 0` 决定是否翻号（`:125`），`primPart` 只是除以
坐标 gcd（`LatticeEdges.lean:794`）——**两步都只在 `d.h j` 张成的直线上移动**，这一点
在主仓里已由 `det_wgen_h_eq_zero`（`TowerConstruct.lean:623`：`det (wgen d nℓ j) (d.h j) = 0`）
记下。于是 `wgen j = wgen k` 会逼出 `det (d.h j) (d.h k) = 0`，正撞 `DecompData.h_dir`
（`DecompData.lean:104`：`∀ i j, i ≠ j → det (h i) (h j) ≠ 0`）。

⚠ 反过来说，`h_dir` 在这里是**紧的**：去掉它单射立刻为假。数值见 `tmp/_leafagen_wgeninj.py`
（非内核）：`nℓ = (1,0)` 下 `(2,4)`、`(-1,-2)`、`(4,8)`、`(-3,-6)` 四个生成元的 `wgen`
全是 `(-1,-2)`，而它们两两的 `det` 全为 `0`。

## 数值实例（硬规矩 6，非内核，`tmp/_leafagen_wgeninj.py`）

两个实例都让「翻号」与「约 gcd」两步**各自真的发生过**，不是空转：

* `m = 3`，`nℓ = (1,0)`，`i = 2`，`h = [(2,4), (-3,1), (0,5)]`（`dot nℓ (h 2) = 0` ✓，
  `h_dir` 的三个 det 是 `14 / 10 / -15`）：
  `j=0`：`dot nℓ h = 2 ≥ 0` ⟹ 翻号 ⟹ `(-2,-4)` ⟹ gcd `2` ⟹ `wgen = (-1,-2)`；
  `j=1`：`dot nℓ h = -3 < 0` ⟹ 不翻 ⟹ `(-3,1)` ⟹ gcd `1` ⟹ `wgen = (-3,1)`。
  两值不同；取 `u' = (-1,-2)`（`dot nℓ u' = -1` ✓，`.erase u'` **真的咬掉一个**），
  `candSet = {(-3,1)}`，非空。
* `m = 4`，`nℓ = (1,0)`，`i = 3`，`h = [(2,4), (-3,1), (6,-3), (0,1)]`（六个 det 是
  `14 / -30 / 2 / 3 / -3 / 6`）：`wgen` 依次 `(-1,-2)`（翻号＋gcd 2）、`(-3,1)`（不翻，gcd 1）、
  `(-2,1)`（翻号＋gcd 3），三值两两不同；`u' = (-1,-2)` 时 `candSet = {(-3,1), (-2,1)}`，非空。

### 穷举（`tmp/_leafagen_wgeninj34.py` / `_leafagen_wgeninj_equiv.py`，非内核）

单个实例不够——鸽子数塌不塌要穷举。台架：`nℓ` 跑遍 `|·| ≤ 2` 的本原向量，`vl = dir nℓ`，
`h i = c • vl`（`c ∈ {±1, ±2}`，保证 `dot nℓ (h i) = 0`），其余 `h j` 跑遍 `[-3,3]²∖{0}`：

| m | 枚举 | 过 `h_ne` ＋ `h_dir` | 其中 `wgen` 在 `erase i` 上单射 | 碰撞 |
|---|---|---|---|---|
| 2 | 3072 | 2816 | 2816（单元素集，**平凡真**） | **0** |
| 3 | 147456 | 113152 | **113152** | **0** |
| 4 | 7077888 | 4134912 | **4134912** | **0** |

`m = 3` 是假设 `3 ≤ d.m` 的下边界、最紧的一格；`m = 4` 确认不是 `m = 3` 的巧合。

**`m = 2` 那格单列（`tmp/_leafagen_wgeninj_m2.py`）：鸽子数塌的方式不是单射性。**
`m = 2` 时 `univ.erase i` 只剩一个下标，单射平凡为真、碰撞 0——但 `.erase u'` 能把那唯一的
候选咬掉。让 `u'` 跑遍 `Prim u' ∧ dot nℓ u' = -1`（链上 binder `hnu`）：2816 个台架里有
**1248** 个 `(nℓ, h, u')` 三元组使 `candSet = ∅`，最小的一个是
`nℓ = (-2,-1)`、`vl = (1,-2)`、`h = [(-2,4), (-3,3)]`、`u' = (1,-1)`，此时 `wgen (h 1) = (1,-1) = u'`。
⟹ **`hm3` 不是可省的**：`candSet_nonempty` 在 `m = 2` 上为假，而下面 `card_candSet_ge`
（`d.m - 2 ≤ card`）在 `m = 2` 上正好退化成 `0 ≤ card`，一眼看得见掉在哪。
**但这不是缺口**：原文 `:230` 根本不走 `m = 2`，那一格由 Theorem 1.12（Szabados）在外部
处理掉了，链上由 `three_le_m` 供给。所以这 1248 个三元组是「配方在 `m = 2` 上不适用」的
证据，不是「配方有 bug」的证据。
（内核见证需要一个 `m = 2` 的 `DecompData ξ` 台架，我手上没有；要就说。）

⚠ 三格数字**只**用来查鸽子数，不作为任何「下标读法 / 角度条件」类命题的证据
（常设纪律第 1 条 / `CORE-HOLES.md` 第 174 轮那条 `m = 4` 纪律管的是鉴别力，与本格无关）。

再一步：把「碰撞 ⟺ 平行」直接穷举对照（`nℓ` 本原 `|·| ≤ 3`，`a b` 跑遍 `[-4,4]²∖{0}`
且 `dot nℓ · ≠ 0`）——91296 个对子里 `wgen a = wgen b` 有 4576 个，`det a b = 0` 也恰好
4576 个，**「相等但不平行」0 个，「平行但不相等」0 个**。这正是下面 Lean 证明的形状：
`wgen` 的纤维就是过原点的直线，`h_dir` 说不同下标不同直线。

其中「定向翻转真的把不同下标打到同一向量」的实例（team-lead 担心的那一步确实会发生，
只是全被 `h_dir` 挡在门外）：`nℓ = (-3,-2)`，`a = (-4,-4)`（`dot = 20 ≥ 0`，翻号）、
`b = (1,1)`（`dot = -5 < 0`，不翻），两者 `wgen` 都是 `(1,1)`，而 `det a b = 0`。
-/

namespace Nivat.LaneLeafAGenCand

open Nivat.LE2 Nivat.Colle35 Nivat.ColleReg

variable {ξ : Nivat.Config ℤ}

/-- 与一个非零向量都「共线」的两个向量彼此共线。纯代数，无几何内容。 -/
private theorem det_trans_of_ne_zero {w a b : ℤ × ℤ} (hw : w ≠ 0)
    (ha : det w a = 0) (hb : det w b = 0) : det a b = 0 := by
  have hw' : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hw (Prod.ext hc.1 hc.2)
  simp only [det] at ha hb ⊢
  rcases hw' with h | h
  · have hx : w.1 * (a.1 * b.2 - a.2 * b.1) = 0 := by linear_combination a.1 * hb - b.1 * ha
    rcases mul_eq_zero.mp hx with h0 | h0
    · exact absurd h0 h
    · linarith
  · have hx : w.2 * (a.1 * b.2 - a.2 * b.1) = 0 := by linear_combination a.2 * hb - b.2 * ha
    rcases mul_eq_zero.mp hx with h0 | h0
    · exact absurd h0 h
    · linarith

/-- **`wgen d nℓ` 在 `j ≠ i` 上单射。** 翻号与约 gcd 都不出 `d.h j` 张成的直线
（`det_wgen_h_eq_zero`），所以两个下标撞在一起就逼出 `det (d.h j) (d.h k) = 0`，
与 `DecompData.h_dir` 矛盾。 -/
theorem wgen_injOn (d : DecompData ξ) {vl nℓ : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) :
    Set.InjOn (wgen d nℓ) ↑(Finset.univ.erase i) := by
  classical
  intro j hj k hk hjk
  by_contra hne
  have hji : j ≠ i := by simpa using hj
  have hki : k ≠ i := by simpa using hk
  have hwj : det (wgen d nℓ j) (d.h j) = 0 :=
    det_wgen_h_eq_zero d hvl_prim hprim hperp i hdoth hji
  have hwk : det (wgen d nℓ k) (d.h k) = 0 :=
    det_wgen_h_eq_zero d hvl_prim hprim hperp i hdoth hki
  rw [hjk] at hwj
  have hw0 : wgen d nℓ k ≠ 0 := by
    intro h0
    have hlt := dot_wgen_neg d hvl_prim hprim hperp i hdoth hki
    rw [h0] at hlt
    simp [dot] at hlt
  exact d.h_dir j k hne (det_trans_of_ne_zero hw0 hwj hwk)

/-- **`3 ≤ d.m ⟹ candSet ≠ ∅`。** `univ.erase i` 有 `m - 1 ≥ 2` 个下标，`wgen` 在上面单射，
`.erase u'` 至多再去掉一个，故至少剩一个候选。 -/
theorem candSet_nonempty (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hm3 : 3 ≤ d.m) :
    (candSet d nℓ u' i).Nonempty := by
  classical
  have hcard_erase : (Finset.univ.erase i).card = d.m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have himg : ((Finset.univ.erase i).image (wgen d nℓ)).card = d.m - 1 := by
    rw [Finset.card_image_of_injOn (wgen_injOn d hvl_prim hprim hperp i hdoth), hcard_erase]
  have hpred :
      ((Finset.univ.erase i).image (wgen d nℓ)).card - 1 ≤
        (((Finset.univ.erase i).image (wgen d nℓ)).erase u').card :=
    Finset.pred_card_le_card_erase
  have hpos : 0 < (candSet d nℓ u' i).card := by
    have hc : (candSet d nℓ u' i).card
        = (((Finset.univ.erase i).image (wgen d nℓ)).erase u').card := rfl
    omega
  exact Finset.card_pos.mp hpos

/-- **塔至少有两格。** `Mtower = (sortedCand).length + 1`（`TowerConstruct.lean:389`），
而 `sortedCand` 是 `candSet.toList` 的 mergeSort（`:263`），长度就是 `candSet.card`。
配 `candSet_nonempty` 得 `2 ≤ Mtower`：除了 `extChain … 0 = u'` 那一格（`:906`）之外，
**至少还有一格**，而 `.erase u'` 保证那些格子都 `≠ u'`（lane-towerpkg 2026-09-24 读
`candSet` 定义所指）。 -/
theorem two_le_Mtower (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hm3 : 3 ≤ d.m) :
    2 ≤ Mtower d nℓ u' i := by
  classical
  have hlen : (sortedCand d nℓ u' i).length = (candSet d nℓ u' i).card := by
    simp [sortedCand, Finset.length_toList]
  have hpos : 0 < (candSet d nℓ u' i).card :=
    Finset.card_pos.mpr (candSet_nonempty d hvl_prim hprim hperp i hdoth hm3)
  simp only [Mtower]
  omega

/-- **精确的鸽子数：`candSet` 至少有 `m - 2` 个元素。** `univ.erase i` 有 `m - 1` 个下标，
`wgen` 在上面单射所以像也是 `m - 1` 个，`.erase u'` 至多再咬掉一个。
这是 `candSet_nonempty` 的定量版本；`m = 3` 时它就退化成「至少 1 个」。 -/
theorem card_candSet_ge (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) :
    d.m - 2 ≤ (candSet d nℓ u' i).card := by
  classical
  have hcard_erase : (Finset.univ.erase i).card = d.m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have himg : ((Finset.univ.erase i).image (wgen d nℓ)).card = d.m - 1 := by
    rw [Finset.card_image_of_injOn (wgen_injOn d hvl_prim hprim hperp i hdoth), hcard_erase]
  have hpred :
      ((Finset.univ.erase i).image (wgen d nℓ)).card - 1 ≤
        (((Finset.univ.erase i).image (wgen d nℓ)).erase u').card :=
    Finset.pred_card_le_card_erase
  have hc : (candSet d nℓ u' i).card
      = (((Finset.univ.erase i).image (wgen d nℓ)).erase u').card := rfl
  have hi : 0 < d.m := Fin.pos i
  omega

/-- **塔长的定量下界 `m - 1 ≤ Mtower`。** 由 `card_candSet_ge` ＋
`Mtower = (sortedCand).length + 1`。`m = 3` 时给 `2 ≤ Mtower`，与 `two_le_Mtower` 一致；
`m` 越大塔越长。 -/
theorem card_le_Mtower (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) :
    d.m - 1 ≤ Mtower d nℓ u' i := by
  classical
  have hlen : (sortedCand d nℓ u' i).length = (candSet d nℓ u' i).card := by
    simp [sortedCand, Finset.length_toList]
  have := card_candSet_ge (u' := u') d hvl_prim hprim hperp i hdoth
  simp only [Mtower]
  omega

/-- **塔长的上界 `Mtower ≤ m`**（team-lead 第 193 轮点名要）。
`candSet` 是 `(univ.erase i).image (wgen d nℓ)` 再 `.erase u'`，两步都不增基数，
而 `univ.erase i` 有 `m - 1` 个元素；配 `Mtower = (sortedCand).length + 1`
（`TowerConstruct.lean:389`）即得。**不需要 `wgen_injOn`**，因此也不需要
`hvl_prim` / `hprim` / `hperp` / `hdoth` ——这条对任意 `nℓ`、任意 `u'` 无条件成立。

与 `card_le_Mtower` 合成夹逼 `m - 1 ≤ Mtower ≤ m`，两端都紧：`u' ∈ wgen` 的像时取
左端，否则取右端（紧性的 `m = 4` 取景由 lane-tower-hbase 给出，我独立按定义重算过，
但他的 Lean 收据我**未复核**，PROTOCOL §55）。 -/
theorem Mtower_le (d : DecompData ξ) (nℓ u' : ℤ × ℤ) (i : Fin d.m) :
    Mtower d nℓ u' i ≤ d.m := by
  classical
  have hcard_erase : (Finset.univ.erase i).card = d.m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have himg : ((Finset.univ.erase i).image (wgen d nℓ)).card ≤ d.m - 1 := by
    calc ((Finset.univ.erase i).image (wgen d nℓ)).card
        ≤ (Finset.univ.erase i).card := Finset.card_image_le
      _ = d.m - 1 := hcard_erase
  have herase :
      (((Finset.univ.erase i).image (wgen d nℓ)).erase u').card
        ≤ ((Finset.univ.erase i).image (wgen d nℓ)).card := Finset.card_erase_le
  have hc : (candSet d nℓ u' i).card
      = (((Finset.univ.erase i).image (wgen d nℓ)).erase u').card := rfl
  have hlen : (sortedCand d nℓ u' i).length = (candSet d nℓ u' i).card := by
    simp [sortedCand, Finset.length_toList]
  have hi : 0 < d.m := Fin.pos i
  simp only [Mtower]
  omega

/-- **鸽笼的落点：塔的第 0 格是一条货真价实的生成元方向，且不是 `u'`。**
`3 ≤ d.m` ⟹ `sortedCand` 非空 ⟹ `wtower … 0` 落在 `candSet` 里（`mem_candSet_wtower`，
`TowerConstruct.lean:401`），于是同时拿到 `≠ u'`（`ne_u'_of_mem_candSet`，`:312`）、
`Primitive`（`prim_of_mem_candSet`，`:298`）、`dot nℓ (·) < 0`（`dot_of_mem_candSet`，`:286`），
以及它确实是某个 `j ≠ i` 的 `wgen d nℓ j`。

这是「塔包交不出候选」那条分支的收口：`extChain … 0 = u'`（`:906`）之外那一格不但存在，
而且写得出它是哪条生成元。 -/
theorem wtower_zero_good (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hm3 : 3 ≤ d.m) :
    wtower d nℓ vl u' i 0 ≠ u' ∧ Primitive (wtower d nℓ vl u' i 0) ∧
      dot nℓ (wtower d nℓ vl u' i 0) < 0 ∧
      ∃ j : Fin d.m, j ≠ i ∧ wtower d nℓ vl u' i 0 = wgen d nℓ j := by
  classical
  have hlen : (sortedCand d nℓ u' i).length = (candSet d nℓ u' i).card := by
    simp [sortedCand, Finset.length_toList]
  have hpos : 0 < (candSet d nℓ u' i).card :=
    Finset.card_pos.mpr (candSet_nonempty d hvl_prim hprim hperp i hdoth hm3)
  have h0 : 0 < (sortedCand d nℓ u' i).length := by omega
  have hmem : wtower d nℓ vl u' i 0 ∈ candSet d nℓ u' i := mem_candSet_wtower h0
  refine ⟨ne_u'_of_mem_candSet hmem,
    prim_of_mem_candSet d hvl_prim hprim hperp i hdoth hmem,
    dot_of_mem_candSet d hvl_prim hprim hperp i hdoth hmem, ?_⟩
  obtain ⟨_, hv_img⟩ := Finset.mem_erase.mp hmem
  obtain ⟨j, hj_mem, hj⟩ := Finset.mem_image.mp hv_img
  exact ⟨j, (Finset.mem_erase.mp hj_mem).1, hj.symm⟩

/-- **链上塔第 0 格就是排序后的第一个候选。** `towerIdx`（`TowerConstruct.lean:373`）是
`if 0 < det u' vl then len - 1 - k else k`；lane-towerpkg 2026-09-24 指出链上
`det u' vl = -1`（`RegionNlDict.det_u'_vl_eq_neg_one_of_normalized`，`RegionNlDict.lean:128`，
由 `hvl_prim` ＋ `hperp` ＋ `hdetpos` ＋ `hnu` 推出），故恒走 `else` 恒等支。
这里把那个化简做成可复用的形状：只假设 `¬ 0 < det u' vl`（比 `= -1` 弱），结论用 `head?`
以免带 `0 < length` 的证明项。⚠ 这条**没有**替代 `det u' vl = -1` 的证明，那是 towerpkg
那条已落地引理的事，我只消费它的结论形状。 -/
theorem head?_sortedCand_eq (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) (hm3 : 3 ≤ d.m)
    (hduv : ¬ 0 < det u' vl) :
    (sortedCand d nℓ u' i).head? = some (wtower d nℓ vl u' i 0) := by
  classical
  have hlen : (sortedCand d nℓ u' i).length = (candSet d nℓ u' i).card := by
    simp [sortedCand, Finset.length_toList]
  have hpos : 0 < (candSet d nℓ u' i).card :=
    Finset.card_pos.mpr (candSet_nonempty d hvl_prim hprim hperp i hdoth hm3)
  have h0 : 0 < (sortedCand d nℓ u' i).length := by omega
  rw [wtower_eq_getElem h0, List.head?_eq_getElem? , List.getElem?_eq_getElem h0]
  simp [towerIdx, hduv]

#print axioms det_trans_of_ne_zero
#print axioms wgen_injOn
#print axioms candSet_nonempty
#print axioms two_le_Mtower
#print axioms card_candSet_ge
#print axioms card_le_Mtower
#print axioms Mtower_le
#print axioms wtower_zero_good
#print axioms head?_sortedCand_eq

end Nivat.LaneLeafAGenCand
