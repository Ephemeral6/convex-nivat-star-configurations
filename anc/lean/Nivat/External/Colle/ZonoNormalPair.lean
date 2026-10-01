/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ZonoWadjCrit
import Nivat.External.Colle.RegionNlDict

/-!
# `hwadj` 判据的**法向侧**形态：从 `(vl, w)` 提到任意正平行的法向对 `(p, q)`（lane-towerpkg，第 187 轮）

**派工**：team-lead 第 187 轮第 (4) 条：
「把 `ZonoWadjCrit.hwadj_iff_det_sep_Sphi`（`ZonoWadjCrit.lean:202`）从写死的 `(vl, w)`
提成任意方向对，然后在 `(-m, nℓ)` 处实例化。」

## 先订正一句：`hwadj_iff_det_sep_Sphi` 的 `(vl, w)` **本来就不是写死的**

`hwadj_iff_det_sep_Sphi`（`ZonoWadjCrit.lean:202`，本轮亲读）的 `vl w : ℤ × ℤ` 已经是自由变量，
对任意一对向量都成立。所以「泛化成任意方向对」这一步是**空的**。

真正缺的那一步是**换边**：`(-m, nℓ)` 不是一对**方向**，是一对**法向**——

* `dot m w = 0`（`RegionSteps.lean:1857` 的 `hmw`，转引自 lane-tower-hbase 第 186 轮报告）
  ⟹ `m ⊥ w` ⟹ `m ∥ dir w`；
* `dot nℓ vl = 0`（`RegionSteps.lean:1842` 的 `hperp`，同上转引）⟹ `nℓ ∥ dir vl`。

而 `hwadj_iff_det_sep_Sphi` 右边的 `det (d.h j) vl * det (d.h j) w` 吃的是**方向** `vl, w`。
本文件补的就是这个换边：把判据重写成只谈 `(p, q)` 的形状，其中 `p` 与 `dir vl`、
`q` 与 `dir w` 各自**正平行**。

## 「正平行」为什么不写成 `p = c • dir vl`

因为链上拿得到的不是整数倍数，而是 lane-tower-hbase `negm_pos_mul_dir_w`
（`tmp/wip/lane-tower-hbase-sortdir.lean:2193`，本轮亲读）的那个形状：

    det (-m) (dir w) = 0 ∧ 0 < dot (-m) (dir w)

即「平行 ∧ 同向」。整数倍数在 `dir w` 非本原时根本不存在，所以本文件全程用这个无倍数写法。
换算靠一条二维恒等式（`dot_par_transfer`）：

    det u p = 0  ⟹  dot x p * dot u u = dot x u * dot p u

于是 `dot u u > 0`、`dot p u > 0` 时 `dot x p` 与 `dot x u` 对每个 `x` 同号。

## 交付

`hwadj_iff_dot_normal_pair`：一般法向对 `(p, q)`；
`hwadj_iff_no_gen_normal_between`：同一条的 `SepsLine` 读法；
`hwadj_iff_no_gen_normal_between_negm_nl`：在 `(-m, nℓ)` 上的实例化，前提逐条对得上链上 binder。

终点形状（逐字）：

    (∀ n ∈ E ↑d.Sphi, ¬ (dot n vl < 0 ∧ dot n w < 0))
      ↔ ∀ j : Fin d.m, ¬ SepsLine (genPerp (d.h j)) (-m) nℓ

右边逐字读作 **「没有生成元法向 `genPerp (h j)` 的直线严格分隔 `-m` 与 `nℓ`」**；由于
`E ↑d.Sphi` 的 `±` 对称（`ZonoWadjCrit.lean:23-26`），这与「没有生成元法向严格落在
`-m` 到 `nℓ` 的开弧里」是同一句话。

## 数值实例（hard rule 6，本轮手算）

`vl = (1,0)`、`w = (0,1)`、`nℓ = (0,-1)`、`m = (1,0)`：四条链上 binder
（`dot m w = 0`、`0 < dot m vl`、`dot nℓ vl = 0`、`dot nℓ w < 0`）全成立。

* `h = (1,1)`：`det h vl * det h w = (-1)·1 = -1 ≤ 0`（`hwadj` 这一支通过）；
  `genPerp h = (-1,1)`，`det (-1,1) (-m) · det (-1,1) nℓ = 1·1 = 1 ≥ 0`（`¬SepsLine` 通过）。✓
* `h = (1,-1)`：`det h vl * det h w = 1·1 = 1 > 0`（`hwadj` 这一支失败）；
  `genPerp h = (1,1)`，`det (1,1) (-m) · det (1,1) nℓ = 1·(-1) = -1 < 0`（`SepsLine` 成立）。✓

两支都对上。

## ⛔ 本文件**不**声称的事

1. **不声称** `hstrict ⟺ hwadj`，也不在任何 docstring 里替它下结论
   （team-lead 2026-09-24：「拿到内核见证前谁都不许对外报 `hstrict ⟺ hwadj`」）。
   本文件只在 `hwadj` 内部换边，两边都是同一个 `hwadj`。
2. **不声称** 已经把「排序意义下的相邻」（`sortedCand` 那一族）与 `¬ SepsLine` 对上；
   那一条在 `ZonoWadjCrit.lean:63` 已记为欠账，本文件没有动它。
3. **不搬带符号的 `det vl w`**：本文件里没有任何「原文侧 ↔ 链上」的转写，
   所有对象都是链上的（team-lead 第 181 轮硬闸）。
4. **不声称 `hwadj` 成立。** 本文件的每条 `↔` 两边都是同一个 `hwadj`，做的只是
   「法向侧 ⟶ 生成元侧」的换边 ＋ 把前提降成全原生。⚠ lane-tower-hbase 第 192 轮在真
   `DecompDataZ` `dGZ` 上把塔链整条算了出来（`tmp/wip/lane-tower-hbase-sortdir.lean` §29，
   他报 EXIT=0、公理全白；本 lane **未复核**）：同一个 `d` / `nℓ` / `u'` 下
   `I = 1` 那格 `hstrict` **假**、`I = 2` 那格真，而角度杠杆
   `hpre : ∀ k ≤ I, 0 ≤ dot m (extChain k)`（即 `TowerPkgMain.lean:280` 的
   `dot_m_extChain_nonneg`，无极小性前提）**两格都成立** ⟹ **角度侧推不出 `hwadj`**。
   ⟹ 判据接好之后，承重仍然落在「塔包为什么不会交出 `I = 1` 那个 `w`」，
   也就是 `hmin`（周期极小性）。**本文件对那一步一无所献**，谁都不许把本文件读成
   「洞 3 已兑现」。

## 本文件不碰

不 import `RegionSteps` / `ColleRegion` / `Case2WindowProbe` / `NfpLPreamble`；
唯一的 import 是 `ZonoWadjCrit`（本 lane 自己的主仓文件）。不改主仓任何签名。

⚠ 本文件第 191 轮由 team-lead 批准从 `tmp/wip/lane-towerpkg-normalpair.lean` 移入主仓
（消费者：lane-tower-hlev 的 `hstrict_iff_sector_empty` 合成路线）。**import 由 team-lead 加**，
`All.lean` 由他跑 `gen_all.py` 重生成。

## §0′ 与 lane-tower-hlev 的 RHS 同形（第 192 轮，本 lane 自撤一条假警报）

本 lane 第 191 轮曾报「我们两条 RHS 符号相反、建议他把对子翻成 `(-nℓ, m)`」。**那是假警报，
本轮撤回**（team-lead 第 192 轮逐定义核过；本 lane 复核同意）。错因：比的是两条 RHS 的**形状**
在**同一个** `(p, q)` 上，而两条定理并不实例化在同一个 `(p, q)`。

内核见证**本文件已经有了**，就是 `not_sepsLine_genPerp_iff`（同文件，无需引 `tmp/wip`）：
取 `(v, a, b) := (d.h j, -mv, nl)`，它逐字给

    ¬ SepsLine (genPerp (d.h j)) (-mv) nl ↔ 0 ≤ dot (d.h j) (-mv) * dot (d.h j) nl

右边正是 hlev 的 `sector_empty_iff_sign_agree` 在 `p = -mv`、`q = nl` 的右边（`dot` 对称，
见 `Nivat.LE2.dot` 的定义 `n.1*z.1 + n.2*z.2`）。两个 `det (genPerp _) _` 各翻一次号、
乘起来**恰好抵消**——这与本 lane 上轮警告过的「两次变号不抵消」是相反的一侧。
⛔ 由此**不得**推出 `hstrict ⟺ hwadj`：本节只说两条 RHS 同形，LHS 那一侧照旧欠账（见上面第 1 条）。-/

namespace Nivat.LaneTowerPkgNormalPair

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.LaneTowerPkgZonoCrit

/-! ## §1. 二维恒等式 -/

private theorem dot_neg_right (a b : ℤ × ℤ) : dot a (-b) = - dot a b := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

/-- `dot x (dir u) = - det x u`。这是「法向侧 ↔ 方向侧」的唯一换边处。 -/
theorem dot_dir_right (x u : ℤ × ℤ) : dot x (dir u) = - det x u := by
  simp only [dot, det, dir]; ring

/-- `det (genPerp v) x = - dot v x`。`genPerp v = dir v`（`ZonoEdgeGen.lean:43`）。 -/
theorem det_genPerp_left (v x : ℤ × ℤ) : det (genPerp v) x = - dot v x := by
  simp only [genPerp, dot, det, dir]; ring

theorem dot_dir_self (u : ℤ × ℤ) : dot (dir u) (dir u) = dot u u := by
  simp only [dot, dir]; ring

theorem dot_self_pos {u : ℤ × ℤ} (hu : u ≠ 0) : 0 < dot u u := by
  obtain ⟨u1, u2⟩ := u
  have hne : ¬ (u1 = 0 ∧ u2 = 0) := by
    rintro ⟨rfl, rfl⟩
    exact hu rfl
  simp only [dot]
  rcases lt_trichotomy (u1 * u1 + u2 * u2) 0 with hlt | heq | hgt
  · nlinarith [mul_self_nonneg u1, mul_self_nonneg u2]
  · exact absurd ⟨by nlinarith [mul_self_nonneg u1, mul_self_nonneg u2],
      by nlinarith [mul_self_nonneg u1, mul_self_nonneg u2]⟩ hne
  · exact hgt

/-- **平行传递**（二维 Lagrange 型恒等式的退化情形）：`u ∥ p` 时，
`dot · p` 与 `dot · u` 只差一个常数 `dot p u / dot u u`。

无倍数写法：`det u p = 0 ⟹ ∀ x, dot x p * dot u u = dot x u * dot p u`。 -/
theorem dot_par_transfer {u p : ℤ × ℤ} (hpar : det u p = 0) (x : ℤ × ℤ) :
    dot x p * dot u u = dot x u * dot p u := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨p1, p2⟩ := p
  obtain ⟨x1, x2⟩ := x
  simp only [det] at hpar
  simp only [dot]
  linear_combination (u1 * x2 - u2 * x1) * hpar

/-! ## §2. 正平行对的符号传递 -/

/-- **核心换边**：`p` 与 `u` 正平行、`q` 与 `v` 正平行 ⟹ 乘积 `dot x p * dot x q` 与
`dot x u * dot x v` 对每个 `x` 同号。

前提里的 `0 < dot u u` / `0 < dot v v` 就是 `u ≠ 0` / `v ≠ 0`（见 `dot_self_pos`），
`det u p = 0` 是平行，`0 < dot p u` 是同向。 -/
theorem dot_prod_nonpos_iff {u v p q : ℤ × ℤ}
    (huu : 0 < dot u u) (hvv : 0 < dot v v)
    (hpu : det u p = 0) (hpp : 0 < dot p u)
    (hqv : det v q = 0) (hqq : 0 < dot q v) (x : ℤ × ℤ) :
    dot x p * dot x q ≤ 0 ↔ dot x u * dot x v ≤ 0 := by
  have e1 := dot_par_transfer hpu x
  have e2 := dot_par_transfer hqv x
  have key : (dot x p * dot x q) * (dot u u * dot v v)
      = (dot x u * dot x v) * (dot p u * dot q v) := by
    linear_combination (dot x q * dot v v) * e1 + (dot x u * dot p u) * e2
  have hposd : 0 < dot u u * dot v v := mul_pos huu hvv
  have hposn : 0 < dot p u * dot q v := mul_pos hpp hqq
  constructor
  · intro hle
    by_contra hc
    push_neg at hc
    nlinarith
  · intro hle
    by_contra hc
    push_neg at hc
    nlinarith

/-! ## §3. 判据的法向侧形态 -/

/-- **`hwadj` 的法向对判据（一般形）**。

左边逐字是链上 `hwadj`（`Nivat.Hole3Room.nlmax_of_wadj` 的 binder 形状，声明行
`Hole3Room.lean:319`，`hwadj` binder 在 `:324-325`；转引自 `ZonoWadjCrit.lean:117-118`）。

右边只谈法向对 `(p, q)`：`p` 与 `dir vl` 正平行，`q` 与 `dir w` 正平行。
`(p, q) := (-nℓ, -m)` 正是链上那一对（见 `hwadj_iff_no_gen_normal_between_negm_nl`）。 -/
theorem hwadj_iff_dot_normal_pair {α : Type*} [AddCommMonoid α] {η : Config α}
    (d : DecompData η) (vl w p q : ℤ × ℤ) (hvl : vl ≠ 0) (hw : w ≠ 0)
    (hp_par : det (dir vl) p = 0) (hp_pos : 0 < dot p (dir vl))
    (hq_par : det (dir w) q = 0) (hq_pos : 0 < dot q (dir w)) :
    (∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ dot n w < 0)) ↔
      ∀ j : Fin d.m, dot (d.h j) p * dot (d.h j) q ≤ 0 := by
  rw [hwadj_iff_det_sep_Sphi d vl w]
  refine forall_congr' fun j => ?_
  have huu : 0 < dot (dir vl) (dir vl) := by rw [dot_dir_self]; exact dot_self_pos hvl
  have hvv : 0 < dot (dir w) (dir w) := by rw [dot_dir_self]; exact dot_self_pos hw
  rw [dot_prod_nonpos_iff huu hvv hp_par hp_pos hq_par hq_pos (d.h j),
    dot_dir_right, dot_dir_right, neg_mul_neg]

/-- `¬ SepsLine (genPerp v) a b` 的展开式：生成元**法向直线** `ℝ (genPerp v)` 不严格分隔
`a` 与 `b`，等价于 `0 ≤ dot v a * dot v b`。 -/
theorem not_sepsLine_genPerp_iff (v a b : ℤ × ℤ) :
    ¬ SepsLine (genPerp v) a b ↔ 0 ≤ dot v a * dot v b := by
  simp only [SepsLine, not_lt]
  rw [det_genPerp_left, det_genPerp_left]
  constructor <;> intro h <;> nlinarith

/-- **法向对判据的 `SepsLine` 读法**：`hwadj` ⟺ 没有生成元法向直线严格分隔 `p` 与 `-q`。 -/
theorem hwadj_iff_no_gen_normal_between {α : Type*} [AddCommMonoid α] {η : Config α}
    (d : DecompData η) (vl w p q : ℤ × ℤ) (hvl : vl ≠ 0) (hw : w ≠ 0)
    (hp_par : det (dir vl) p = 0) (hp_pos : 0 < dot p (dir vl))
    (hq_par : det (dir w) q = 0) (hq_pos : 0 < dot q (dir w)) :
    (∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ dot n w < 0)) ↔
      ∀ j : Fin d.m, ¬ SepsLine (genPerp (d.h j)) p (-q) := by
  rw [hwadj_iff_dot_normal_pair d vl w p q hvl hw hp_par hp_pos hq_par hq_pos]
  refine forall_congr' fun j => ?_
  rw [not_sepsLine_genPerp_iff, dot_neg_right]
  constructor <;> intro h <;> nlinarith

/-! ## §4. 在 `(-m, nℓ)` 上的实例化 -/

/-- **`hnldir` 是白送的**：链上原生 binder `hdetpos : 0 < det nℓ vl`
（`RegionSteps.lean:1928`，本轮亲读；`exists_cutResidualR_of_claim46` 的 binder，
生产者一侧免费归一，见该处 `:1909-1916` 的注释）逐字给出 `dot nℓ (dir vl) < 0`。

换算只有一步：`dot x (dir u) = - det x u`（`dot_dir_right`）。

⟹ 不需要 `0 < det vl w`，也不需要 lane-tower-hbase 的归一化等式 `nℓ = -(dir vl)`。 -/
theorem dot_nl_dir_vl_neg_of_detpos {nl vl : ℤ × ℤ} (hdetpos : 0 < det nl vl) :
    dot nl (dir vl) < 0 := by
  rw [dot_dir_right]; omega

/-- **终点：链上那一对法向。**

前提逐条对链上 binder：

* `hperp : dot nl vl = 0` —— `RegionSteps.lean:1842`（转引，lane-tower-hbase 第 186 轮报告）；
* `hmw : dot mv w = 0` —— `RegionSteps.lean:1857`（同上，转引）；
* `hnldir : dot nl (dir vl) < 0` —— 由链上原生 binder `hdetpos : 0 < det nl vl`
  （`RegionSteps.lean:1928`，本轮亲读）经 `dot_nl_dir_vl_neg_of_detpos` 白送；
  见下方 `hwadj_iff_no_gen_normal_between_chain`，那一条的前提全部是链上原生 binder；
* `hnegm : 0 < dot (-mv) (dir w)` —— **逐字**是 `negm_pos_mul_dir_w` 结论的第二合取
  （`tmp/wip/lane-tower-hbase-sortdir.lean:2196`，本轮亲读）。

结论右边逐字读作：**没有生成元法向 `genPerp (h j)` 的直线严格分隔 `-m` 与 `nℓ`**。

⛔ 这条**只**换边，不谈 `hstrict`。 -/
theorem hwadj_iff_no_gen_normal_between_negm_nl {α : Type*} [AddCommMonoid α] {η : Config α}
    (d : DecompData η) (vl w mv nl : ℤ × ℤ) (hvl : vl ≠ 0) (hw : w ≠ 0)
    (hperp : dot nl vl = 0) (hnldir : dot nl (dir vl) < 0)
    (hmw : dot mv w = 0) (hnegm : 0 < dot (-mv) (dir w)) :
    (∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ dot n w < 0)) ↔
      ∀ j : Fin d.m, ¬ SepsLine (genPerp (d.h j)) (-mv) nl := by
  have hp_par : det (dir vl) (-nl) = 0 := by
    simp only [det, dir, Prod.fst_neg, Prod.snd_neg]
    simp only [dot] at hperp
    linarith
  have hp_pos : 0 < dot (-nl) (dir vl) := by rw [dot_neg_left]; linarith
  have hq_par : det (dir w) (-mv) = 0 := by
    simp only [det, dir, Prod.fst_neg, Prod.snd_neg]
    simp only [dot] at hmw
    linarith
  rw [hwadj_iff_no_gen_normal_between d vl w (-nl) (-mv) hvl hw hp_par hp_pos hq_par hnegm]
  refine forall_congr' fun j => ?_
  rw [not_sepsLine_genPerp_iff, not_sepsLine_genPerp_iff, dot_neg_right, dot_neg_right,
    dot_neg_right]
  constructor <;> intro h <;> nlinarith

/-- **全链上原生 binder 版**：把 `hnldir` 换成 `hdetpos`，四条前提**逐条**是
`exists_cutResidualR_of_claim46` 的 binder 或其自由推论：

* `hperp : dot nl vl = 0` —— `RegionSteps.lean:1908`（当轮亲读）；
* `hdetpos : 0 < det nl vl` —— `RegionSteps.lean:1928`（当轮亲读）；
* `hmw : dot mv w = 0` —— `exists_cutResidualR_of_claim46` 体内 `RegionSteps.lean:1957`
  那条 `obtain` 的第六个分量（当轮亲读）；
* `hnegm : 0 < dot (-mv) (dir w)` —— lane-tower-hbase `negm_pos_mul_dir_w` 结论第二合取。

⟹ 悬空前提只剩 `hnegm` 一条，而它已有内核生产者。

⛔ 这条**只**换边，不谈 `hstrict`。 -/
theorem hwadj_iff_no_gen_normal_between_chain {α : Type*} [AddCommMonoid α] {η : Config α}
    (d : DecompData η) (vl w mv nl : ℤ × ℤ) (hvl : vl ≠ 0) (hw : w ≠ 0)
    (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hmw : dot mv w = 0) (hnegm : 0 < dot (-mv) (dir w)) :
    (∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ dot n w < 0)) ↔
      ∀ j : Fin d.m, ¬ SepsLine (genPerp (d.h j)) (-mv) nl :=
  hwadj_iff_no_gen_normal_between_negm_nl d vl w mv nl hvl hw hperp
    (dot_nl_dir_vl_neg_of_detpos hdetpos) hmw hnegm

/-! ## §4′. `hnegm` 也是原生 binder 的推论（第 192 轮）

上一节把 `hnegm : 0 < dot (-mv) (dir w)` 记成「悬空、已有内核生产者」。**本节把它降成推论**，
`hwadj_iff_no_gen_normal_between_native` 的前提**全部**是 `exists_cutResidualR_of_claim46`
的原生 binder，一条外部依赖都不剩。

关键是 `nℓ = -(dir vl)` **不是待证的归一化假设**：`Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u'`
（`RegionNlDict.lean:87`，第 192 轮亲读，公理全白）已经从
`hvl_prim` / `hperp` / `hdetpos` / `hnu` 四条原生 binder 把它证出来了。
本 lane 第 191 轮曾把带 `hnl : nl = -(dir vl)` 的引理一律记成「循环归一化」——
**那条记法本轮撤回**：循环的只是「用它去证 `hnldir`」那一条特定路径
（因为 `hnl` 自己要过 `hdetpos`，而 `hdetpos` 直接就给 `hnldir`），`hnl` 本身是定理不是债。

⚠ 硬规矩 6 的数值实例（先手算再写 Lean，内核收据见 `negm_numeric_instance`）：
`nℓ = (1,0)`、`vl = (0,1)`、`w = (-1,-1)`、`mv = (-1,1)`。
`dot nℓ vl = 0`、`det nℓ vl = 1 > 0`、`dot nℓ w = -1 < 0`、`dot mv w = 0`、`dot mv vl = 1 > 0`；
`det vl w = 0·(-1) - 1·(-1) = 1 > 0`，`det mv w = (-1)(-1) - 1·(-1) = 2 > 0`，
Binet–Cauchy 两边对上：`(mv·vl)(w·w) = 1·2 = 2 = 2·1 = det(mv,w)·det(vl,w)`；
`-mv = (1,-1)`、`dir w = (1,-1)`，`dot (-mv) (dir w) = 2 > 0`。 -/

/-- **二维 Binet–Cauchy，无前提。** `(a·c)(b·e) − (a·e)(b·c) = det(a,b)·det(c,e)`。 -/
theorem binet_cauchy (a b c e : ℤ × ℤ) :
    dot a c * dot b e - dot a e * dot b c = det a b * det c e := by
  simp only [dot, det]; ring

/-- `hmw : dot mv w = 0` 把 Binet–Cauchy 的第二项打掉，剩下
`(mv·vl)(w·w) = det(mv,w)·det(vl,w)`；左边由 `hmvl` 与 `w ≠ 0` 为正，
于是 `det vl w > 0` 逼出 `det mv w > 0`。⚠ 这一步**不需要** `Primitive w`：
「`mv ⟂ w` ⟹ `mv` 平行于 `dir w`」这件事根本没有被用成整数倍。 -/
theorem det_mv_w_pos {mv w vl : ℤ × ℤ} (hw : w ≠ 0)
    (hmw : dot mv w = 0) (hmvl : 0 < dot mv vl) (hvlw : 0 < det vl w) :
    0 < det mv w := by
  have hww : 0 < dot w w := dot_self_pos hw
  have hkey : dot mv vl * dot w w = det mv w * det vl w := by
    have hbc := binet_cauchy mv w vl w
    rw [hmw] at hbc
    linarith [hbc]
  have hpos : 0 < det mv w * det vl w := by
    rw [← hkey]; exact mul_pos hmvl hww
  by_contra hc
  push_neg at hc
  nlinarith [hpos, hvlw, hc]

/-- `hwneg : dot nℓ w < 0` 逐字就是 `0 < det vl w` 的反号——一旦用上
`nℓ = -(dir vl)`（`RegionNlDict.nl_eq_neg_dir_vl_and_det_u'`）。 -/
theorem det_vl_w_pos_of_chain {nl vl w u' : ℤ × ℤ}
    (hvlp : Primitive vl) (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1) (hwneg : dot nl w < 0) : 0 < det vl w := by
  have hnl := (Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u' hvlp hperp hdetpos hnu).1
  have hkey : dot nl w = - det vl w := by
    rw [hnl]; simp only [dot, det, dir, Prod.fst_neg, Prod.snd_neg]; ring
  rw [hkey] at hwneg
  linarith

/-- **`hpar` 的独立形态。**  `hmw : dot mv w = 0` 逐字就是 `det (-mv) (dir w) = 0`：
`det (-mv) (dir w) = -(dot mv w)`。单列一条是给下游（lane-tower-hlev 的
`hstrict_iff_wadj` 三条形参之一）直接消费用的，`hwadj_iff_no_gen_normal_between_negm_nl`
的证明里本来就有同一步。 -/
theorem det_negm_dir_w_eq_zero {mv w : ℤ × ℤ} (hmw : dot mv w = 0) :
    det (-mv) (dir w) = 0 := by
  simp only [det, dir, Prod.fst_neg, Prod.snd_neg]
  simp only [dot] at hmw
  linarith

/-- **⭐ `hnegm` 降为推论。**  前提全是 `exists_cutResidualR_of_claim46` 的原生 binder。 -/
theorem negm_pos_dot_dir_w_of_chain {nl vl w mv u' : ℤ × ℤ} (hw : w ≠ 0)
    (hvlp : Primitive vl) (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1) (hwneg : dot nl w < 0)
    (hmw : dot mv w = 0) (hmvl : 0 < dot mv vl) :
    0 < dot (-mv) (dir w) := by
  have h1 : 0 < det mv w :=
    det_mv_w_pos hw hmw hmvl (det_vl_w_pos_of_chain hvlp hperp hdetpos hnu hwneg)
  have h2 : dot (-mv) (dir w) = det mv w := by
    rw [dot_dir_right]; simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  rw [h2]; exact h1

/-- 硬规矩 6 的内核收据：上面文字里那组数。 -/
theorem negm_numeric_instance :
    dot ((1, 0) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) = 0 ∧
      0 < det ((1, 0) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) ∧
      dot ((1, 0) : ℤ × ℤ) ((-1, -1) : ℤ × ℤ) < 0 ∧
      dot ((-1, 1) : ℤ × ℤ) ((-1, -1) : ℤ × ℤ) = 0 ∧
      0 < dot ((-1, 1) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) ∧
      0 < det ((0, 1) : ℤ × ℤ) ((-1, -1) : ℤ × ℤ) ∧
      det ((-1, 1) : ℤ × ℤ) ((-1, -1) : ℤ × ℤ) = 2 ∧
      0 < dot (-((-1, 1) : ℤ × ℤ)) (dir ((-1, -1) : ℤ × ℤ)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  simp only [dot, dir, Prod.fst_neg, Prod.snd_neg]
  norm_num

/-- **⭐⭐ 全原生版本。**  与 `hwadj_iff_no_gen_normal_between_chain` 同一条结论，但
前提表里**再没有**任何外部生产者：逐条对应 `exists_cutResidualR_of_claim46`
（`RegionSteps.lean`，第 192 轮亲读；认标识符不认行号）：

* `hvlp : Primitive vl` —— `:1907`；
* `hperp : dot nl vl = 0` —— `:1908`；
* `hdetpos : 0 < det nl vl` —— `:1928`；
* `hnu : dot nl u' = -1` —— `:1928`（与 `hdetpos` 同一行）；
* `hwp : Primitive w`、`hwneg : dot nl w < 0`、`hmw : dot mv w = 0`、`hmvl : 0 < dot mv vl`
  —— 体内那条 `obtain`（`:1959` 起）的分量。

`vl ≠ 0` / `w ≠ 0` 不单列，从 `Primitive` 现推，免得看起来像多要了 binder。

⛔ 与上一节同样的边界：这条**只**在 `hwadj` 内部换边，**不**声称 `hstrict ⟺ hwadj`。 -/
theorem hwadj_iff_no_gen_normal_between_native {α : Type*} [AddCommMonoid α] {η : Config α}
    (d : DecompData η) (vl w mv nl u' : ℤ × ℤ)
    (hvlp : Primitive vl) (hwp : Primitive w)
    (hperp : dot nl vl = 0) (hdetpos : 0 < det nl vl)
    (hnu : dot nl u' = -1) (hwneg : dot nl w < 0)
    (hmw : dot mv w = 0) (hmvl : 0 < dot mv vl) :
    (∀ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)), ¬ (dot n vl < 0 ∧ dot n w < 0)) ↔
      ∀ j : Fin d.m, ¬ SepsLine (genPerp (d.h j)) (-mv) nl :=
  have hvl : vl ≠ 0 := (prim_iff_primitive.mpr hvlp).ne_zero
  have hw : w ≠ 0 := (prim_iff_primitive.mpr hwp).ne_zero
  hwadj_iff_no_gen_normal_between_chain d vl w mv nl hvl hw hperp hdetpos hmw
    (negm_pos_dot_dir_w_of_chain hw hvlp hperp hdetpos hnu hwneg hmw hmvl)

/-! ## §5. 公理收据 -/
#print axioms dot_dir_right
#print axioms det_genPerp_left
#print axioms dot_dir_self
#print axioms dot_self_pos
#print axioms dot_par_transfer
#print axioms dot_prod_nonpos_iff
#print axioms hwadj_iff_dot_normal_pair
#print axioms not_sepsLine_genPerp_iff
#print axioms hwadj_iff_no_gen_normal_between
#print axioms dot_nl_dir_vl_neg_of_detpos
#print axioms hwadj_iff_no_gen_normal_between_negm_nl
#print axioms hwadj_iff_no_gen_normal_between_chain
#print axioms binet_cauchy
#print axioms det_mv_w_pos
#print axioms det_vl_w_pos_of_chain
#print axioms det_negm_dir_w_eq_zero
#print axioms negm_pos_dot_dir_w_of_chain
#print axioms negm_numeric_instance
#print axioms hwadj_iff_no_gen_normal_between_native

end Nivat.LaneTowerPkgNormalPair
