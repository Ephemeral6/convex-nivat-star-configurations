/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-tower-hbase
-/
import Nivat.External.Colle.TowerHbaseUnitSweep
import Nivat.External.Colle.GcdCollapse
import Nivat.External.Colle.TowerHlevTile
import Nivat.External.Colle.CyclicOrderWindow
import Nivat.External.Colle.EnvRefuteCover
import Nivat.External.Colle.ChainPartsFeed
import Nivat.External.Colle.HcombOrient
import Nivat.External.Colle.ConeRecession
import Nivat.Section8.RegionUpgrade

/-!
# `bottom` 合取 1–3 的 `∀ ε` 版，**不**要求单位步长

`bottom_conj123`（`TowerHbaseUnitSweep.lean`，按名引）为了拿到 `∀ ε` 吃了
`hd : dot nJ vJ1 = -1`。那条作为 `ChainDataGeom` 的定理**为假**：`Nivat.ShellConvex.cgc`
是字段齐全的居民，`bottom` 已证而步长是 `-2`。
⚠⚠ **`cgc` 的射程（lane-leafa-shell 2026-09-25 的合并版，照抄）**：引 `cgc` 只能得到
「`ChainDataGeom` ⊭ X」，**永远得不到**「链上 ⊭ X」，理由有二且独立：(i) 窗口零面积；
(ii) `det p vl ≠ 0`（实测 `det (2,1) (1,-2) = -5`，而链上 `hdet_vl : det p vl = 0`）。
(ii) 那个数本 lane 手算复核过，与他们一致；(i) 那半是集成者所报、本处未复核（§55）。
本文件把 `hd` 换成链上真有的两条字段
`rec_p` / `dot_nJ_p` ＋ 一条新残余 `hcop`。

## 原文锚

* 目标是 `ChainDataGeomParts.bottom` 的前三个合取（`ChainPartsFeed.lean:288-294`），
  原文 `scratch/b3_colle2.txt:432` 的 (3.1)，层号量词在 `:432` 是 `∃ ε ∈ ℤ₊`，
  字段取成 `∀ ε`（比原文强，那笔债记在字段那里，不在本文件）。
* `rec_p` / `dot_nJ_p`（`ChainPartsFeed.lean` 的 `ChainDataGeomParts`，按字段名引）
  ＝ 原文 `:271` 的周期 `p`。
* 字段 `hhp` ＝ 原文 `:492` 的半平面。字段 `hsweep` ＝ 原文 `:492` 的扫掠方向。
  ⚠ 2026-09-26 更正（`PROTOCOL §57`／`§124`）：本节原先写的 `ChainPartsFeed.lean:295`/`:296`
  /`:220`/`:218` 四个行号**全部已腐**（实测 `rec_p` 在 `:367`、`dot_nJ_p` 在 `:368`、
  `hhp` 在 `:292`、`hsweep` 在 `:290`），故一律改为按字段名引、不带行号。

## ⛔ `hcop` 的定性（硬规矩 5）

`hcop : IsCoprime (dot nJ p) (dot nJ vJ1)` 在 `b3_colle2.txt` 里**没有对应物**，
它是本路线的代价，与 `hd` 同类。记它比记 `hd` 值钱的理由有两条，都是内核的：

1. `hd` 已被 `cgc` 证伪为定理；`hcop` **没有**——`cgc` 自己就满足它
   （`dot nJv p2 = 1`、`dot nJv vl2 = -2`，见 `tmp/wip/hbase-recp-probe.lean`，
   ⚠ 那是链外收据，按硬规矩 1 对公理闭包贡献为零）。
2. `hcop` 是**尖锐**的，不是随手加强：从单个 `p`-轨道出发，可达层号恰好是
   `dot nJ g₀ + gcd (dot nJ p) (-dot nJ vJ1) · ℤ`，要命中每一层就必须互素。
   与 lane-env-refute 的负控在同一条边界上会合，见 `not_common_residue_of_rec_p`。
-/


set_option autoImplicit false

namespace Nivat.TowerHbase

open Nivat Nivat.LE2

/-- `Âinf` 关于 `+p` 封闭 ＋ 它整个落在 `dot nJ ≥ cJ` 里 ⟹ `dot nJ p ≥ 0`。

⚠ **去重（集成者第 234 轮裁决：三份都不删）**：本条、lane-tower-hlev 的 `dot_p_pos`、
lane-hole3-nlmax 的 `dot_p_pos_of_fields` 是三个独立构造证同一件事。canonical 记
**`NlmaxGcd.dot_p_pos_of_fields`**（纯字段版，按标识符名查）；本条保留，因为 `ANormal`
一线有 18 个下游，为去重触发重放买不到东西。
⚠ 理由的名字按 lane-hole3-nlmax 的订正写 **Archimedes**（`+p` 走 `m` 步把高度推到任意低，
与半平面下界矛盾），**不是** pigeonhole —— 这里没有抽屉，只有阿基米德性。 -/
theorem dot_nJ_p_nonneg {Ah : Set (ℤ × ℤ)} {nJ p g₀ : ℤ × ℤ} {cJ : ℤ}
    (hg₀ : g₀ ∈ Ah) (hrecp : ∀ g ∈ Ah, g + p ∈ Ah)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z) :
    0 ≤ dot nJ p := by
  rcases le_or_gt 0 (dot nJ p) with h | hneg
  · exact h
  exfalso
  have hh0 : cJ ≤ dot nJ g₀ := hhp _ hg₀
  set m : ℕ := (dot nJ g₀ - cJ + 1).toNat with hm
  have hmc : ((m : ℕ) : ℤ) = dot nJ g₀ - cJ + 1 := Int.toNat_of_nonneg (by omega)
  have hmem := mem_of_natCast_smul hrecp hg₀ m
  have hlt := hhp _ hmem
  rw [hbase_dot_add_zsmul, hmc] at hlt
  nlinarith [hlt, hneg, hh0]

/-- **算术核**：`d, e > 0` 互素 ⟹ 任何整数都写成 `m·d − t·e`，`m t : ℕ`。 -/
theorem exists_nat_combo {d e r : ℤ} (hd : 0 < d) (he : 0 < e) (hcop : IsCoprime d e) :
    ∃ m t : ℕ, (m : ℤ) * d - (t : ℤ) * e = r := by
  obtain ⟨x, y, hxy⟩ := hcop
  set k : ℤ := |r * x| + |r * y| with hk
  have hk0 : 0 ≤ k := by positivity
  have hm0 : 0 ≤ r * x + k * e := by
    have h1 : k ≤ k * e := le_mul_of_one_le_right hk0 he
    have h2 : -(r * x) ≤ |r * x| := neg_le_abs _
    have h3 : (0 : ℤ) ≤ |r * y| := abs_nonneg _
    omega
  have ht0 : 0 ≤ -(r * y) + k * d := by
    have h1 : k ≤ k * d := le_mul_of_one_le_right hk0 hd
    have h2 : r * y ≤ |r * y| := le_abs_self _
    have h3 : (0 : ℤ) ≤ |r * x| := abs_nonneg _
    omega
  refine ⟨(r * x + k * e).toNat, (-(r * y) + k * d).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hm0, Int.toNat_of_nonneg ht0]
  have : (r * x + k * e) * d - (-(r * y) + k * d) * e = r * (x * d + y * e) := by ring
  rw [this]
  have hxy' : x * d + y * e = 1 := by linarith [hxy]
  rw [hxy', mul_one]

/-- ⭐ **每一层都被命中，步长任意**：只要 `dot nJ p` 与 `dot nJ vJ1` 互素。

链上对应（按字段名引，不带行号；原先此处的四个行号已腐，见本文件开头的更正）：
`hrecp` = 字段 `rec_p`，`hp` = 字段 `dot_nJ_p`，`hhp` = 字段 `hhp`，`hsweep` = 字段 `hsweep`。
`hcop` **没有**链上对应物，是本路线新记的残余。 -/
theorem exists_seed_level_of_rec {Ah : Set (ℤ × ℤ)} {nJ vJ1 p g₀ : ℤ × ℤ} {cJ : ℤ} (ε : ℕ)
    (hg₀ : g₀ ∈ Ah) (hrecp : ∀ g ∈ Ah, g + p ∈ Ah)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z)
    (hsweep : dot nJ vJ1 < 0) (hp : dot nJ p ≠ 0)
    (hcop : IsCoprime (dot nJ p) (dot nJ vJ1)) :
    ∃ m t : ℕ, dot nJ (g₀ + (m : ℤ) • p + (t : ℤ) • vJ1) = cJ - (ε : ℤ) - 1 := by
  have hd : 0 < dot nJ p := lt_of_le_of_ne (dot_nJ_p_nonneg hg₀ hrecp hhp) (Ne.symm hp)
  have he : 0 < -dot nJ vJ1 := by omega
  have hcop' : IsCoprime (dot nJ p) (-dot nJ vJ1) := hcop.neg_right
  obtain ⟨m, t, hmt⟩ :=
    exists_nat_combo hd he hcop' (r := cJ - (ε : ℤ) - 1 - dot nJ g₀)
  refine ⟨m, t, ?_⟩
  rw [hbase_dot_add_zsmul, hbase_dot_add_zsmul]
  linarith [hmt]

/-- ⭐ **本条与 lane-env-refute 的负控在同一条边界上会合。**

他们的 `not_bottom_conj1_of_common_residue`（`CyclicOrderStepT.lean`，按名引）在
`hres : ∀ g ∈ A, e ∣ (dot nJ g - cJ)` 下否掉合取 1。本条证明：本文件的前提直接**否掉 `hres`**
（只要步长不是单位）。⟹ 两条不冲突，边界恰是 `gcd (dot nJ p) (dot nJ vJ1)`：
互素 ⟹ 高度跑遍模 `e` 的每个剩余类 ⟹ `hres` 假 ⟹ 他们的负控不适用，本文件的正面构造适用。
⚠ 他们那条的 EXIT／公理本处未复跑（§55）。 -/
theorem not_common_residue_of_rec_p {Ah : Set (ℤ × ℤ)} {nJ vJ1 p g₀ : ℤ × ℤ} {cJ : ℤ}
    (hg₀ : g₀ ∈ Ah) (hrecp : ∀ g ∈ Ah, g + p ∈ Ah)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z)
    (hsweep : dot nJ vJ1 < 0) (hp : dot nJ p ≠ 0)
    (hcop : IsCoprime (dot nJ p) (dot nJ vJ1))
    (hne : dot nJ vJ1 ≠ -1) :
    ¬ (∀ g ∈ Ah, (-dot nJ vJ1) ∣ (dot nJ g - cJ)) := by
  intro hres
  obtain ⟨m, t, hlev⟩ :=
    exists_seed_level_of_rec 0 hg₀ hrecp hhp hsweep hp hcop
  have hmem := mem_of_natCast_smul hrecp hg₀ m
  obtain ⟨q, hq⟩ := hres _ hmem
  rw [hbase_dot_add_zsmul] at hlev
  push_cast at hlev hq
  have hdvd : (-dot nJ vJ1) ∣ (1 : ℤ) := ⟨(t : ℤ) - q, by linarith⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
  · omega
  · omega

/-- ⭐⭐ **`bottom` 合取 1–3 的 `∀ ε` 版，步长自由。**

与 `bottom_conj123` 逐字同结论，唯一差别是把 `hd : dot nJ vJ1 = -1`（作为 `ChainDataGeom`
的定理**为假**，见 `cgc`）换成 `hrecp` ＋ `hp` ＋ `hcop`，前两条都是链上字段。 -/
theorem bottom_conj123_of_rec_p {Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 p a wS : ℤ × ℤ} {cJ : ℤ}
    (ha : a ∈ S) (htile : ∀ b ∈ S, b + wS ∈ Ah)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z)
    (hrec : ∀ g ∈ Ah, g + vJ ∈ Ah)
    (hrecp : ∀ g ∈ Ah, g + p ∈ Ah)
    (hperp : dot nJ vJ = 0)
    (hsweep : dot nJ vJ1 < 0) (hp : dot nJ p ≠ 0)
    (hcop : IsCoprime (dot nJ p) (dot nJ vJ1)) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ k : ℤ, L ≤ k → dot nJ (z₀ + k • vJ) = cJ - (ε : ℤ) - 1) := by
  intro ε
  obtain ⟨m, t, hlev⟩ :=
    exists_seed_level_of_rec ε (htile a ha) hrecp hhp hsweep hp hcop
  have htile' : ∀ b ∈ S, b + (wS + (m : ℤ) • p) ∈ Ah := by
    intro b hb
    have := mem_of_natCast_smul hrecp (htile b hb) m
    have he : b + wS + (m : ℤ) • p = b + (wS + (m : ℤ) • p) := by module
    rwa [he] at this
  have hshift : a + (wS + (m : ℤ) • p) + (t : ℤ) • vJ1
      = a + wS + (m : ℤ) • p + (t : ℤ) • vJ1 := by module
  exact bottom_conj123_of_seed (wS := wS + (m : ℤ) • p) (t := t) ha htile' hrec hperp
    (by rw [hshift]; exact hlev)

/-- ⭐⭐⭐ **合取 1–3，`∀ ε`，`htile` 与 `hadj` 同时出局。**

前件 `hexTile` 逐字是 lane-tower-hlev 的 `exists_tile_of_swept` 的**结论**
（`TowerHlevTile.lean`，按名引）。他那条的残余是 `hindep : det p vJ1 ≠ 0`，其余全是
`ChainDataGeomParts` 字段。本条的残余是 `hcop`。合起来：

| 曾经的前提 | 现状 |
|---|---|
| `htile` | hlev 的 `exists_tile_of_swept` 供出，残余 `hindep` |
| `hadj : det vJ vJ1 = ±1` | **不再需要**（链上有反例，且本条不经过它） |
| `dot nJ vJ1 = -1` | **不再需要**（`cgc` 否掉了它作为定理） |
| —— | 新残余：`hcop : IsCoprime (dot nJ p) (dot nJ vJ1)` |

⚠ 此处用 binder 而非 `import`，理由**已经换过一次，现在是第二条**：
1. ~~`TowerHlevTile.lean` 尚未进全绿 build~~ —— **过期**：集成者第六次 build（20:37:45–20:38:16）
   覆盖了它，其 olean 存在（本 lane 实测），硬规矩 1 不再适用。
2. ⛔ **现行理由**：集成者第 233 轮裁定 `hindep : det p vJ1 ≠ 0` **在链上为假**
   （共线裁决 `vJ1 = m • vl` ＋ binder `hdet_vl : det p vl = 0` ⟹ `det p vJ1 = 0`），
   ⟹ `exists_tile_of_swept` 的前件在链上不可满足，import 它接不出东西来。
   ⚠ 但共线裁决本身**无产者**（见下方 `not_conj1_of_dot_nJ_vl` 一节），
   所以按 §119 这是「**不可判**」：共线成立则那条空，共线不成立则那条活。
   binder 形在两种情形下都不会说谎，因此保留。⚠ 他那条的 EXIT／公理本处未复跑（§55）。 -/
theorem bottom_conj123_of_rec_p_of_tile {Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 p a : ℤ × ℤ} {cJ : ℤ}
    (ha : a ∈ S) (hexTile : ∃ wS : ℤ × ℤ, ∀ b ∈ S, b + wS ∈ Ah)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z)
    (hrec : ∀ g ∈ Ah, g + vJ ∈ Ah)
    (hrecp : ∀ g ∈ Ah, g + p ∈ Ah)
    (hperp : dot nJ vJ = 0)
    (hsweep : dot nJ vJ1 < 0) (hp : dot nJ p ≠ 0)
    (hcop : IsCoprime (dot nJ p) (dot nJ vJ1)) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ k : ℤ, L ≤ k → dot nJ (z₀ + k • vJ) = cJ - (ε : ℤ) - 1) := by
  obtain ⟨wS, htile⟩ := hexTile
  exact bottom_conj123_of_rec_p ha htile hhp hrec hrecp hperp hsweep hp hcop

/-! ## `gcd (dot nJ p) (dot nJ vJ1)` 整除 `det p vJ1` —— 把 `hcop` 换成行列式条件

本节把上面那条自造的债 `hcop` 归约到一个**纯行列式**前件：

`det p vJ1 = ±1` ⟹ `hcop`，因为对任意**本原** `n` 有 `gcd (dot n p) (dot n q) ∣ det p q`。

⟹ 与 lane-tower-hlev 的残余 `hindep : det p vJ1 ≠ 0`（`TowerHlevTile.lean` 的
`exists_tile_of_swept`，按标识符名查）对齐后，合取 1–3 的两条残余变成**同一个量的两档强度**：
把 `≠ 0` 升到 `= ±1`，`hcop` 自动消失。

⚠ **纯格论层面** `≠ 0` 不够：`det p q = -2` 时 `gcd` 可以是 2。
⛔ **但这句话在链上讲不通，本 lane 2026-09-25 订正（lane-env-refute 指出）**：链上
`det p vJ1 ≡ 0`（见本节抬头的 `det_p_vJ1_zero`）⟹「`≠ 0`」「`= ±1`」「卡在中间的 `-2`」
**三格全空**，不是「`-2` 落在中间那一格」。⚠ 原来引的 lane-env-refute `gcd = 2` 见证
（`p = (1,2)`、`vJ1 = (0,-2)`）**不平行**，不满足 `hp_neg` ＋ 共线两条链 binder ⟹ 拿它谈链上
`det p vJ1` 的取值是链外读数。他们已自行把这条射程记在自己名下，此处只作订正（§57）。
⛔ **反方向为假，不要读成 iff**：`det = ±1` 充分不必要。
`nJ = (0,1)`、`p = (1,1)`、`vJ1 = (0,-3)`：`gcd = 1` 而 `det = -3`。

⚠⚠ **`hcop` 本身也是充分不必要的**（lane-env-refute 2026-09-25 的内核见证
`cover_without_gcd_one` / `heights_iff_cover`，`EnvRefuteCover.lean`，按名查）：
恰当的充要条件是**覆盖条件** `∀ r : ℤ, ∃ g ∈ A, (-dot nJ vJ1) ∣ (dot nJ g - r)`，
它比 `hcop` 严格更弱（上半平面 `A = {w | 0 ≤ w.2}` 上 `gcd = 2` 而覆盖成立）。
⟹ 本节的两条只是**一条充分链**：`det = ±1` ⟹ `hcop` ⟹ 覆盖 ⟹ 合取 1–3。
⚠ 其 EXIT／公理为 lane-env-refute 所报，我未复核（§55）。

⛔⛔ **本节前件在链上为假 —— 集成者第 234 轮裁决，内核见证已在主仓。**

`GcdCollapse.det_p_vJ1_zero`（按标识符名查）：

```
p = -(c : ℤ) • vl  ∧  vJ1 = m • vl   ⟹   det p vJ1 = 0
```

两条前提都是链上现成的：`hp` 即 `exists_chainData` 的 binder `hp_neg`（产者是 `ColleRegion` 的
`exists_neg_multiple_of_perp`），`hm` 即第 226 轮共线裁决（`LeafAShellAttain`）。`p` 与 `vJ1`
是同一个 `vl` 的两个倍数 ⟹ 行列式**恒为 0**，与居民无关。推论 `GcdCollapse.not_det_unit`
直接写出：`det p vJ1 = ±1` 与 `det p vJ1 ≠ 0` **在链上都不可满足**。

⟹ **本节是空载出口，不减债**，与 lane-tower-hlev 的 `bottom_conj123_of_tile` 同命。
⛔ **不许**再把本节引为「合取 1–3 的链上出口」，也不许去生产前件 `det p vJ1 = ±1`：
不是「算不算撞纪律 23」的问题，是那条**为假**。
⭐ 保留的理由只有一条：上面两条代数（`gcd_dot_dvd_det` / `isCoprime_dot_of_det_unit`）对**任意**
本原 `n`、**任意** `(p, q)` 成立，错的只是把它实例化到 `(p, vJ1)` 这一对。同一台机器换到
`(vJ, vl)` 上确实有非空内容，见本文件最后一节。

⚠ 唯一的记账保留项（不影响上面的裁决）：`det_p_vJ1_zero` 以 `hm : vJ1 = m • vl` 为**假设**，
而共线裁决是一条**裁决**、不是本仓的定理；我按结论型搜产者（`∃ m …, vJ1 = …` 在
`Nivat/**.lean` 里 0 命中，`vJ1 = m • vl` 56 行 / 8 文件全在 binder 位）没找到 —— 按 §51
只报「没找到」。裁决的边界归集成者，本节照裁决执行。

⛔ **与纪律 23 的界限**：本节只证蕴含，前件 `det p vJ1 = ±1` 留作 binder，**不生产它**。
`det p vJ1` 与被禁的 `hadj : det vJ vJ1 = ±1` 是两组不同的向量对；谁要去产前件，
须先向集成者确认是否落在纪律 23 内。本节对 `det vJ vJ1` 一个字没说。

数值控（分母写全）：随机 200000 组坐标 ∈[-9,9] 的 `(n,p,q)`，两条 `ring` 恒等式违例 0；
其中 `n` 本原的 124045 组整除性违例 0；`|det p q| = 1` 的 1703 个子情形 `gcd = 1` 违例 0。
（控不是证明；证明是 `gcd_dot_dvd_det` 本身。） -/

/-- **对本原 `n`，`gcd (dot n p) (dot n q)` 整除 `det p q`。**

两条 `ring` 恒等式把 `n.1 * det p q` 与 `n.2 * det p q` 写成 `dot n p`、`dot n q` 的整系数组合，
再用 `IsCoprime n.1 n.2` 把 `n.1`、`n.2` 消掉。

⚠ 这是纯格论，不含本项目任何几何假设；`n` 的本原性来自字段 `nJ_prim`
（`ChainPartsFeed.lean`，按标识符名查）。 -/
theorem gcd_dot_dvd_det {n p q : ℤ × ℤ} (hn : IsCoprime n.1 n.2) (g : ℤ)
    (hgp : g ∣ dot n p) (hgq : g ∣ dot n q) : g ∣ det p q := by
  obtain ⟨x, y, hxy⟩ := hn
  have h1 : g ∣ n.1 * det p q := by
    have e : n.1 * det p q = q.2 * dot n p - p.2 * dot n q := by
      simp only [dot, det]; ring
    rw [e]
    exact dvd_sub (Dvd.dvd.mul_left hgp _) (Dvd.dvd.mul_left hgq _)
  have h2 : g ∣ n.2 * det p q := by
    have e : n.2 * det p q = p.1 * dot n q - q.1 * dot n p := by
      simp only [dot, det]; ring
    rw [e]
    exact dvd_sub (Dvd.dvd.mul_left hgq _) (Dvd.dvd.mul_left hgp _)
  have e : det p q = x * (n.1 * det p q) + y * (n.2 * det p q) := by
    have : x * n.1 + y * n.2 = 1 := by linarith [hxy]
    calc det p q = (x * n.1 + y * n.2) * det p q := by rw [this]; ring
      _ = x * (n.1 * det p q) + y * (n.2 * det p q) := by ring
  rw [e]
  exact dvd_add (Dvd.dvd.mul_left h1 _) (Dvd.dvd.mul_left h2 _)

/-- **`det p q = ±1` ⟹ `dot n p` 与 `dot n q` 互素**（`n` 本原）。

`gcd_dot_dvd_det` 的直接推论：任何公约数都整除 `det p q = ±1`，故是单位。 -/
theorem isCoprime_dot_of_det_unit {n p q : ℤ × ℤ} (hn : IsCoprime n.1 n.2)
    (hdet : det p q = 1 ∨ det p q = -1) : IsCoprime (dot n p) (dot n q) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  have h := gcd_dot_dvd_det hn (Int.gcd (dot n p) (dot n q) : ℤ)
    (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  have hu : (Int.gcd (dot n p) (dot n q) : ℤ) ∣ 1 := by
    rcases hdet with hd | hd
    · rw [hd] at h; exact h
    · rw [hd] at h; exact (dvd_neg.mp h)
  have hnat : Int.gcd (dot n p) (dot n q) ∣ 1 := by
    have h1 : ((Int.gcd (dot n p) (dot n q) : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ) := by exact_mod_cast hu
    exact_mod_cast h1
  exact Nat.dvd_one.mp hnat

/-- **把 `bottom` 合取 1–3 的残余从 `hcop` 换成 `det p vJ1 = ±1`。**

`bottom_conj123_of_rec_p_of_tile`（`TowerHbaseRecP.lean`）的同一条结论，
`hcop` 由 `isCoprime_dot_of_det_unit` 从行列式条件产出。

⟹ 与 lane-tower-hlev 的 `hindep : det p vJ1 ≠ 0` 只差**把 `≠ 0` 升到 `= ±1`**。
⛔ `≠ 0` 不够：`det = -2` 时 `gcd` 可以是 2（见文件头的数值实例）。 -/
theorem bottom_conj123_of_det_unit {Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 p a : ℤ × ℤ} {cJ : ℤ}
    (ha : a ∈ S) (hexTile : ∃ wS : ℤ × ℤ, ∀ b ∈ S, b + wS ∈ Ah)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z)
    (hrec : ∀ g ∈ Ah, g + vJ ∈ Ah)
    (hrecp : ∀ g ∈ Ah, g + p ∈ Ah)
    (hperp : dot nJ vJ = 0)
    (hsweep : dot nJ vJ1 < 0) (hp : dot nJ p ≠ 0)
    (hnJ : IsCoprime nJ.1 nJ.2)
    (hdet : det p vJ1 = 1 ∨ det p vJ1 = -1) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ k : ℤ, L ≤ k → dot nJ (z₀ + k • vJ) = cJ - (ε : ℤ) - 1) :=
  bottom_conj123_of_rec_p_of_tile ha hexTile hhp hrec hrecp hperp hsweep hp
    (isCoprime_dot_of_det_unit hnJ hdet)
/-! ## ⛔ `dot nJ vl = -1` **不能**替换 `hcop`：替换后合取 1 为假

集成者第 233 轮派工第 1 条是：把 `bottom_conj123_of_rec_p` 的
`hcop : IsCoprime (dot nJ p) (dot nJ vJ1)` 换成「链上单一形式」`dot nJ vl = -1`，
理由是 `GcdCollapse` 证明了两者在链上互相蕴含。

**本文件用内核居民证明该替换不成立。** 派工单的依据只在 `m = 1` 那一格成立：
`GcdCollapse.unit_sweep_of_gcd_one` 与 `GcdCollapse.gcd_one_of_unit` **两条都带
`hvJ1 : vJ1 = vl`**（即 `m = 1`），而一般 `m` 的 `GcdCollapse.collapse` 的结论是
`-dot nJ vJ1 = m`，**不是** `= -1`。⚠ 而 `m = 1` 本身无产者（`GcdCollapse` 文件头也写了这一点）。
⚠ **订正（lane-leafa-shell 2026-09-25 报，本处未复跑，§55）**：`0 < m` **已经有产者**了 ——
`LeafAShellLsideFork.m_pos_of_chain_stock`（按标识符名查），用的是既有字段 ＋ `hp_neg`。
⟹ `GcdCollapse` 文件头与本节上一版写的「`0 < m` 无产者」都已过期；仍然无产者的是
`m = 1`，以及 `|dot nJ vl| = 1`。这**不**影响本节的结论：本节的见证取 `m = 2`，`0 < m` 成立。

## 见证（`c = m = 2`，满足**全部**链上共线 binder）

| 对象 | 取值 | 满足 |
|---|---|---|
| `nJ` | `(0,1)` | `dot nJ z = z.2` |
| `vl` | `(0,-1)` | `Primitive vl`、`dot nJ vl = -1` ✓（派工单要的那条） |
| `p` | `-(2:ℤ) • vl = (0,2)` | `hp_neg` 形，`0 < c`，`dot nJ p = 2 ≠ 0` |
| `vJ1` | `(2:ℤ) • vl = (0,-2)` | 共线裁决形，`0 < m`，`dot nJ vJ1 = -2 < 0` |
| `A` | `{w | 0 ≤ w.2 ∧ 2 ∣ w.2}` | 非空、`rec_p`、`hhp`（`cJ = 0`） |

⟹ `det p vl = 0`（`hdet_vl` 也满足，见 `witness_det_p_vl`）。
但 `d = 2`、`e = 2` ⟹ `gcd = 2` ⟹ `A` 里高度全偶、`vJ1` 步长也偶 ⟹
`reachSet A vJ1` 的高度全偶 ⟹ **层 `cJ - 0 - 1 = -1` 取不到** ⟹ 合取 1 为假。

## 结论（三句，方向不许混）

1. **`hcop` ⟹ `dot nJ vl = -1`**（`GcdCollapse.dot_nJ_vl_isUnit` ＋ 定符号）—— 这个方向真。
2. **反方向假**：`dot nJ vl = -1` ⇏ `hcop`（本文件 `witness_gcd_two`：`gcd = 2`）。
   ⟹ `dot nJ vl = -1` **严格弱于** `hcop`，拿它替换 `hcop` 会让合取 1 变成假命题。
3. `m = 1` 那一格上两者确实等价 —— 但那一格是**另一笔无产者的债**，不是免费的。

⛔ 因此本 lane **不执行**该替换。若集成者坚持单一债 token，正确的单一形式是
**`dot nJ vl = -1` ＋ `IsCoprime (c : ℤ) (m : ℤ)`**（由 `collapse` 的 `d = c`、`e = m`），
或者直接就用 `hcop`：在共线 binder 下 `hcop ⟺ dot nJ vl = ±1 ∧ IsCoprime c m`。

⛔⛔ **三条就地订正（2026-09-25，§103：不重写上文，只在此加块）**

**(i) 上表那个见证需要一句限定，而且这句限定本轮变紧了。** 它取 `vJ1 = (0,-2)`，**不本原**
（`GcdCollapse.witnessA_vJ1_not_prim`，按标识符名查）。所以上表只在
「**`vJ1` 的本原性未进签名**」这个签名下合法——lane-env-refute 2026-09-25 要求补的正是这句。
⚠ 而本文件 §9 把这句限定变紧了一档：`Primitive vJ1` 现在**不必**诉诸原文
`b3_colle2.txt:351`，只要 `vJ1 = ±dir nprevJ` ＋ `nprevJ ∈ E R` 就白送
（`prim_vJ1_of_edge_ccw` / `prim_vJ1_of_edge_cw`）。⟹ 一旦有人把这条接进
`ChainDataGeomParts`，上表的见证**当场出局**（本原 ＋ 共线 ＋ 符号 ⟹ `m = 1`）。
算术没错，是那个居民不在链上。

**(ii) §113：上文「结论」第 2 句的「严格更弱」只对 `hcop` 说，对覆盖条件不成立。**
按 lane-env-refute 的订正与集成者第 235 轮裁决 3，`dot nJ vl = -1` 与**覆盖条件**是
**不可比**，不是一条强度链。逐条打印两个方向（§113）：

* 覆盖 ⇏ `dot nJ vl = -1`：`EnvRefuteCover.cover_without_gcd_one` 一族，`gcd = 2` 而覆盖成立。
* `dot nJ vl = -1` ⇏ 覆盖：本文件上表的见证（层 `-1` 取不到）。

⟹ `det p vJ1 = ±1` ⟹ `hcop` ⟹ 覆盖 仍是一条链；`dot nJ vl = -1` 挂在**旁支**，
与覆盖条件互不蕴含。

**(iii) `hcop` 连合取 1 的必要条件都不是。** lane-env-refute 2026-09-25 落了
`conj1_heights_without_unit_magnitude`（`EnvRefuteFaceNormal.lean`，按标识符名查；
本处未复跑，§55）：一组**共线且 `Primitive vJ1` 全兑现**的数据上 `gcd = 2` 而合取 1 的
高度部分成立。这与本文件 §8.2 的机制读数一致——`p` 与 `vJ1` 都是 `vl` 的倍数 ⟹ 递推
一个剩余类都换不了 ⟹ 剩余类只能由 `A` 自身的高度谱供，与 `c`、`m` 无关。

⚠ 顺带把 `hcop_iff_coprime_c_m` 的前提钉死，免得被过引：记 `s := dot nJ vl`，一般共线
构型下 `gcd(d,e) = |s| · gcd(c,m)`，所以那条 iff 是**代进 `|s| = 1` 之后**的形状，
`|s|` 本身是另一个因子，不能被 `m` 吸收（lane-env-refute 2026-09-25 提示，算术本处自核）。

⚠ 另一条独立的记账（本 lane 自撤，2026-09-25 按集成者第 234 轮裁决定稿）：本文件
`det p vJ1 = ±1` 那一节的前件在链上**为假**，内核见证是 `GcdCollapse.det_p_vJ1_zero`
（按标识符名查）⟹ 那一节是**空载出口**，与 lane-tower-hlev 的 `hindep : det p vJ1 ≠ 0`
同命。⚠ 上一版这里记的是「§119 未定」，依据是「共线裁决无产者」；集成者第 234 轮把共线
裁决定为链上给定，故改为已裁。保留一句记账：`det_p_vJ1_zero` 以 `hm : vJ1 = m • vl` 为
**假设**，其产者本 lane 按结论型搜索未找到（§51），边界归集成者。
-/

/-- 见证集合：非负偶高度的整点。 -/
def Aw : Set (ℤ × ℤ) := {w : ℤ × ℤ | 0 ≤ w.2 ∧ (2 : ℤ) ∣ w.2}

theorem witness_p : -((2 : ℕ) : ℤ) • ((0, -1) : ℤ × ℤ) = ((0, 2) : ℤ × ℤ) := by decide

theorem witness_vJ1 : ((2 : ℕ) : ℤ) • ((0, -1) : ℤ × ℤ) = ((0, -2) : ℤ × ℤ) := by decide

/-- `hdet_vl` 也满足：`det p vl = 0`。 -/
theorem witness_det_p_vl : det ((0, 2) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) = 0 := by decide

/-- 派工单要的那条前件在见证上**成立**。 -/
theorem witness_dot_nJ_vl : dot ((0, 1) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) = -1 := by decide

/-- 而 `gcd (dot nJ p) (-dot nJ vJ1) = 2` ⟹ `hcop` 在见证上**为假**。 -/
theorem witness_gcd_two :
    Int.gcd (dot ((0, 1) : ℤ × ℤ) ((0, 2) : ℤ × ℤ))
      (-dot ((0, 1) : ℤ × ℤ) ((0, -2) : ℤ × ℤ)) = 2 := by decide

theorem witness_nonempty : ((0, 0) : ℤ × ℤ) ∈ Aw := ⟨le_rfl, dvd_zero 2⟩

theorem witness_rec_p : ∀ g ∈ Aw, g + ((0, 2) : ℤ × ℤ) ∈ Aw := by
  rintro ⟨x, y⟩ ⟨hy, k, hk⟩
  exact ⟨by simp; omega, ⟨k + 1, by simp; omega⟩⟩

theorem witness_hhp : ∀ z ∈ Aw, (0 : ℤ) ≤ dot ((0, 1) : ℤ × ℤ) z := by
  rintro ⟨x, y⟩ ⟨hy, -⟩
  simpa [dot] using hy

/-- `reachSet Aw (0,-2)` 里的高度全是偶数。 -/
theorem witness_even_reach :
    ∀ z ∈ MaxEnv.reachSet Aw ((0, -2) : ℤ × ℤ), (2 : ℤ) ∣ dot ((0, 1) : ℤ × ℤ) z := by
  rintro z ⟨g, ⟨-, k, hk⟩, t, rfl⟩
  refine ⟨k - (t : ℤ), ?_⟩
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  omega

/-- ⛔ **主结论：把 `hcop` 换成 `dot nJ vl = -1` 之后，合取 1 为假。**

全称命题的每一条前提都由上面的见证兑现，包括派工单指定的 `dot nJ vl = -1`、
`hp_neg` 形的 `p = -(c:ℤ) • vl`、共线裁决形的 `vJ1 = (m:ℤ) • vl`、`0 < c`、`0 < m`。 -/
theorem not_conj1_of_dot_nJ_vl :
    ¬ ∀ (A : Set (ℤ × ℤ)) (nJ vl p vJ1 : ℤ × ℤ) (c m : ℕ) (cJ : ℤ),
        A.Nonempty →
        (∀ g ∈ A, g + p ∈ A) →
        (∀ z ∈ A, cJ ≤ dot nJ z) →
        p = -(c : ℤ) • vl →
        vJ1 = (m : ℤ) • vl →
        0 < c → 0 < m →
        dot nJ vJ1 < 0 →
        dot nJ p ≠ 0 →
        dot nJ vl = -1 →
        ∀ ε : ℕ, ∃ z ∈ MaxEnv.reachSet A vJ1, dot nJ z = cJ - (ε : ℤ) - 1 := by
  intro h
  obtain ⟨z, hz, hlev⟩ :=
    h Aw (0, 1) (0, -1) (0, 2) (0, -2) 2 2 0
      ⟨_, witness_nonempty⟩ witness_rec_p witness_hhp
      witness_p.symm witness_vJ1.symm (by norm_num) (by norm_num)
      (by decide) (by decide) (by decide) 0
  obtain ⟨k, hk⟩ := witness_even_reach z hz
  omega

/-- ⛔ **`hcop` 严格弱于 `dot nJ vJ1 = -1`，两者不是同一笔债。**

见证 `c = 3`、`m = 2`（同样满足全部共线 binder）：`p = -(3:ℤ) • vl = (0,3)`、
`vJ1 = (2:ℤ) • vl = (0,-2)` ⟹ `d = 3`、`e = 2` ⟹ **`gcd = 1`（`hcop` 真）**，
而 `dot nJ vJ1 = -2 ≠ -1`（`hd` 假）。

⟹ 方向表（§113，两边都打印）：
* `dot nJ vJ1 = -1` ⟹ `hcop`：**真**（`e = 1` 时 `gcd (d) 1 = 1`）。
* `hcop` ⟹ `dot nJ vJ1 = -1`：**假**，本条就是见证。

⟹ 把 `hcop` 说成「`hd` 换了个名字」不成立：**它是严格更弱的前提，替换确实减了债。**
两者只在 `m = 1` 那一格重合，而 `m = 1` 本身无产者。 -/
theorem hcop_strictly_weaker :
    Int.gcd (dot ((0, 1) : ℤ × ℤ) ((0, 3) : ℤ × ℤ))
        (-dot ((0, 1) : ℤ × ℤ) ((0, -2) : ℤ × ℤ)) = 1 ∧
      dot ((0, 1) : ℤ × ℤ) ((0, -2) : ℤ × ℤ) ≠ -1 ∧
      -((3 : ℕ) : ℤ) • ((0, -1) : ℤ × ℤ) = ((0, 3) : ℤ × ℤ) ∧
      ((2 : ℕ) : ℤ) • ((0, -1) : ℤ × ℤ) = ((0, -2) : ℤ × ℤ) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## ⭐ 共线 binder 下 `hcop` 的**逐字分解**：`dot nJ vl = -1` ＋ `IsCoprime (c : ℤ) m`

集成者第 233 轮派工第 1 条要的是「全树只剩**一个**债 token」。上一节已用内核居民
（`not_conj1_of_dot_nJ_vl`）证明他指定的那个 token（单独的 `dot nJ vl = -1`）**太弱**，
换了之后合取 1 为假。本节把正确的分解落成定理。

在两条共线 binder 下（`hp_neg : p = -(c : ℤ) • vl`，`hm : vJ1 = m • vl`，
两条的来历见 `GcdCollapse` 文件头，按名引），及 `hvl : dot nJ vl = -1`：

```
dot nJ p = c        dot nJ vJ1 = -m
IsCoprime (dot nJ p) (dot nJ vJ1)  ⟺  IsCoprime (c : ℤ) m        -- hcop_iff_coprime_c_m
```

⭐ **副产品：两条旧前提变免费。** `bottom_conj123_of_rec_p` 原本要
`hsweep : dot nJ vJ1 < 0` 与 `hp : dot nJ p ≠ 0` 两条独立前提；在本节的形式下
它们分别由 `0 < m` 与 `0 < c` 加 `hvl` 一步推出（见 `bottom_conj123_of_unit_vl` 证明体）
⟹ `bottom_conj123_of_unit_vl` 的非字段残余**恰好两条**：`hvl` 与 `hcm`。

⭐ **2026-09-25 更新（lane-leafa-shell 报，本处未复跑，§55）**：本条另外两个前提也拿到了产者，
两条都在 `LeafAShellLsideFork.lean`（按标识符名查）：

| 前提 | 产者 | 用到的东西 |
|---|---|---|
| `hmpos : 0 < m` | `m_pos_of_chain_stock` | 字段 `hsweep` / `hhp` / `ahat_nonempty` / `rec_p` / `dot_nJ_p` ＋ binder `hp_neg` |
| `dot nJ vl < 0`（`hvl` 的**符号**那一半） | `dot_nJ_vl_neg_of_rec_p` | 同上，**不需要**互素 |

⟹ 本条的净欠项收缩成两条，都零产者：**`|dot nJ vl| = 1`**（大小那一半，等价于
`det vJ vl = ±1`，见本文件最后一节）与 **`IsCoprime (c : ℤ) m`**。

## ⛔ 订正 `GcdCollapse` 文件头那张表：它少了一行

那张表写「本轮四个债券全部塌进**一个**量 `dot nJ vl`，并拆成符号／大小两半」。
**这两半不完备**：`c = m = 2` 的居民（上一节）两半全满足（`dot nJ vl = -1`，
符号与大小都对）而合取 1 仍为假。⟹ 那张表需要第三行：

| 半 | 内容 | 状态 |
|---|---|---|
| 符号 | `dot nJ vl < 0` | lane 报已有（未进主仓，§55） |
| 大小 | `\|dot nJ vl\| = 1` | ⛔ 零产者 |
| **第三条（本节新增）** | **`IsCoprime (c : ℤ) m`** | ⛔ 零产者，**不可由 `dot nJ vl` 推出** |

## §113 两个方向都打印

* `hvl` 单独不够：`not_conj1_of_dot_nJ_vl`（`c = m = 2`）⟹ **合取 1 为假**。
* `hcm` 单独不够：`coprime_c_m_not_enough`（`c = m = 1`，`vl = (1,-3)`、`nJ = (0,1)`
  两条本原性都立，`dot nJ vl = -3 < 0` 符号也对）⟹ `gcd (d, e) = 3` ⟹ **`hcop` 为假**。
  ⚠ **射程：这一条只杀 `hcop`，不杀合取 1。** 尖锐的判据是 lane-env-refute 的覆盖条件
  （`heights_iff_cover`，`EnvRefuteCover.lean`，按名引），`hcop` 比它严格更强
  ⟹ 「`hcop` 假」推不出「合取 1 假」。不准把本条读成反例。其 EXIT／公理本处未复跑（§55）。

## 射程差别：本节与上方 `det p vJ1 = ±1` 那一节正好相反

那一节的前件在共线裁决下恒假（`det p vJ1 = 0`，集成者的 `det_p_vJ1_zero`，按名引）；
本节把共线当**前提在用**，共线越真本节越活。⟹ 合取 1–3 的活路线是本节，不是那一节。

## 原文锚

`vl` 即 `v⃗_ℓ`（`scratch/b3_colle2.txt:351`），目标仍是 `:432` 的 (3.1)。
⛔ `IsCoprime (c : ℤ) m` 在 `b3_colle2.txt` 里**没有对应物**，与 `hvl` 同类，是本路线的代价。
-/

/-- 共线 binder 下两个内积都退化成 `dot nJ vl` 的整数倍。 -/
theorem dot_of_collinear {nJ vl p vJ1 : ℤ × ℤ} {c : ℕ} {m : ℤ}
    (hp : p = -(c : ℤ) • vl) (hm : vJ1 = m • vl) :
    dot nJ p = -(c : ℤ) * dot nJ vl ∧ dot nJ vJ1 = m * dot nJ vl := by
  refine ⟨?_, ?_⟩
  · rw [hp]; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  · rw [hm]; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- ⭐ `hcop` 在共线 ＋ 单位 binder 下**逐字等于** `IsCoprime (c : ℤ) m`。 -/
theorem hcop_iff_coprime_c_m {nJ vl p vJ1 : ℤ × ℤ} {c : ℕ} {m : ℤ}
    (hp : p = -(c : ℤ) • vl) (hm : vJ1 = m • vl) (hvl : dot nJ vl = -1) :
    IsCoprime (dot nJ p) (dot nJ vJ1) ↔ IsCoprime ((c : ℤ)) m := by
  obtain ⟨h1, h2⟩ := dot_of_collinear (nJ := nJ) hp hm
  have hd : dot nJ p = (c : ℤ) := by rw [h1, hvl]; ring
  have he : dot nJ vJ1 = -m := by rw [h2, hvl]; ring
  rw [hd, he]
  constructor
  · intro h; simpa using h.neg_right
  · intro h; exact h.neg_right

/-- ⭐⭐ 合取 1–3，残余只剩 `dot nJ vl = -1` ＋ `IsCoprime (c : ℤ) m`。 -/
theorem bottom_conj123_of_unit_vl {Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 vl p a : ℤ × ℤ} {cJ : ℤ} {c : ℕ} {m : ℤ}
    (ha : a ∈ S) (hexTile : ∃ wS : ℤ × ℤ, ∀ b ∈ S, b + wS ∈ Ah)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z)
    (hrec : ∀ g ∈ Ah, g + vJ ∈ Ah)
    (hrecp : ∀ g ∈ Ah, g + p ∈ Ah)
    (hperp : dot nJ vJ = 0)
    (hp_neg : p = -(c : ℤ) • vl) (hcpos : 0 < c)
    (hm : vJ1 = m • vl) (hmpos : 0 < m)
    (hvl : dot nJ vl = -1) (hcm : IsCoprime ((c : ℤ)) m) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ k : ℤ, L ≤ k → dot nJ (z₀ + k • vJ) = cJ - (ε : ℤ) - 1) := by
  obtain ⟨h1, h2⟩ := dot_of_collinear (nJ := nJ) hp_neg hm
  have hd : dot nJ p = (c : ℤ) := by rw [h1, hvl]; ring
  have he : dot nJ vJ1 = -m := by rw [h2, hvl]; ring
  have hc' : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hcpos
  have hsweep : dot nJ vJ1 < 0 := by rw [he]; omega
  have hpne : dot nJ p ≠ 0 := by rw [hd]; omega
  exact bottom_conj123_of_rec_p_of_tile ha hexTile hhp hrec hrecp hperp hsweep hpne
    ((hcop_iff_coprime_c_m (nJ := nJ) hp_neg hm hvl).mpr hcm)

/-- 见证 B 的两条本原性。 -/
theorem witnessB_nJ_prim : Primitive ((0, 1) : ℤ × ℤ) := isCoprime_one_right

theorem witnessB_vl_prim : Primitive ((1, -3) : ℤ × ℤ) := isCoprime_one_left

/-- ⛔ 反方向：`IsCoprime c m` 单独**不够**，单位性那一半独立。 -/
theorem coprime_c_m_not_enough :
    IsCoprime ((1 : ℕ) : ℤ) (1 : ℤ) ∧
      -((1 : ℕ) : ℤ) • ((1, -3) : ℤ × ℤ) = ((-1, 3) : ℤ × ℤ) ∧
      (1 : ℤ) • ((1, -3) : ℤ × ℤ) = ((1, -3) : ℤ × ℤ) ∧
      dot ((0, 1) : ℤ × ℤ) ((1, -3) : ℤ × ℤ) = -3 ∧
      dot ((0, 1) : ℤ × ℤ) ((1, -3) : ℤ × ℤ) < 0 ∧
      Int.gcd (dot ((0, 1) : ℤ × ℤ) ((-1, 3) : ℤ × ℤ))
        (-dot ((0, 1) : ℤ × ℤ) ((1, -3) : ℤ × ℤ)) = 3 := by
  refine ⟨isCoprime_one_left, by decide, by decide, by decide, by decide, by decide⟩

/-! ## ⭐ 同一台机器换到 `(vJ, vl)` 上：有非空内容，但**产不出**那条债

集成者第 234 轮派工第 2 条问的就是这个：`gcd_dot_dvd_det` 这台机器在 `(vJ, vl)` 上能不能给出
任何非空内容。**答案：能，而且已经被人接走了；但它产不出那条债，理由是结构性的。**

### 能给什么

`dot_dvd_det` / `det_dvd_dot`（`TowerHbaseUnitSweep.lean`，按名引）在 `hperp : dot nJ vJ = 0`
下给出两个方向的整除，`vl` 是**自由**向量（两条证明对第三个向量一无所求）。
lane-hole3-nlmax 已用这两条把 `±1` 那一档接走了：`NlmaxDetVl.unit_vl_iff_unimodular`
（按名引）＝ `(dot nJ vl = ±1) ↔ (det vJ vl = ±1)`。⟹ **机器在这一对上非空，且不重复造。**

本节只补一条 nlmax 没落、而 `det_dvd_dot` 的 docstring 早就用文字断言过的东西（§111
「被谈论 ≠ 在用」）：两个整除合起来是**相伴**，不只在值为 1 时相等 ——
`det_vJ_vl_assoc`：`det vJ vl = dot nJ vl ∨ det vJ vl = -dot nJ vl`。
⟹ `|det vJ vl| = |dot nJ vl|` 对**每个**值成立，`±1` 那条 iff 是它的特例。

### ⛔ 产不出什么，以及为什么这是结构性的

机器的全部输入是 `nJ_prim` / `vJ_prim` / `hperp`，**三条都与 `vl` 无关**。所以它只能在
`dot nJ vl` 与 `det vJ vl` 之间**搬运**，不能钉住任何一侧的值。内核见证
`arith_fields_do_not_pin_magnitude`：同一对 `nJ = (0,1)`、`vJ = (1,0)`（两条本原、`hperp` 立）

| `vl` | `Primitive vl` | `dot nJ vl` | `det vJ vl` |
|---|---|---|---|
| `(0,-1)` | ✓ | `-1` | `-1` |
| `(1,-3)` | ✓ | `-3` | `-3` |

⟹ 两行都满足 `nJ_prim` / `vJ_prim` / `vl_prim` / `hperp`，`|dot nJ vl|` 取到 1 和 3 两个值
⟹ **这组字段不钉住大小那一半**。第二行还额外满足算术／共线 binder 组的其余各条：
`p = -(1 : ℕ) • vl = (-1,3)` 兑现 `hp_neg` 形（`0 < c`）、`det p vl = 0` 兑现 `hdet_vl`、
`dot nJ p = 3 ≠ 0` 兑现 `dot_nJ_p`、`dot nJ vl = -3 < 0` 兑现符号 ⟹ **整个算术 binder 组
都不钉住它**。

⚠⚠ **射程，两句，不许省**（§85.2）：
1. 这**不是**说 `|dot nJ vl| = 1` 在链上为假。本节一条几何字段都没喂 —— `shellEnv`、
   `fillCover`、`bottom`、`escapeW`、`Config` 那一侧全空，`nJ` 作为 `J`-面法向的来历也没用上。
2. 结论只有一句：**产者必须用到几何**，任何只嚼 `nJ_prim` / `vJ_prim` / `vl_prim` / `hperp` /
   `hp_neg` / 共线 / `hsweep` 的路线都到不了。⟹ 这台机器（含 `gcd_dot_dvd_det`）**不是**
   那条债的入口，定性为「能搬运、不能生产」。

### 原文锚

`vl` 即 `v⃗_ℓ`（`scratch/b3_colle2.txt:351`）；`nJ` 为 `J`-面法向，来历见 `ANormal.lean`
的 `FaceBlock`（按名引）。⛔ `|dot nJ vl| = 1` 在 `b3_colle2.txt` 里没有逐字对应物，它是
本路线为了 `∀ ε` 付的代价。
-/

/-- `det vJ vl` 与 `dot nJ vl` **相伴**（不只是同为单位时相等）。 -/
theorem det_vJ_vl_assoc {nJ vJ vl : ℤ × ℤ} (hnJ_prim : Primitive nJ) (hvJ_prim : Primitive vJ)
    (hperp : dot nJ vJ = 0) :
    det vJ vl = dot nJ vl ∨ det vJ vl = -dot nJ vl := by
  have h1 : dot nJ vl ∣ det vJ vl := dot_dvd_det hnJ_prim hperp vl
  have h2 : det vJ vl ∣ dot nJ vl := det_dvd_dot hvJ_prim hperp
  have hn : (dot nJ vl).natAbs = (det vJ vl).natAbs :=
    Nat.dvd_antisymm (Int.natAbs_dvd_natAbs.mpr h1) (Int.natAbs_dvd_natAbs.mpr h2)
  rcases Int.natAbs_eq_natAbs_iff.mp hn with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by omega)

/-- ⛔ 算术 binder 组**不钉住** `|dot nJ vl|`：同一对 `(nJ, vJ)` 上两个 `vl` 给 1 和 3。 -/
theorem arith_fields_do_not_pin_magnitude :
    (Primitive ((0, 1) : ℤ × ℤ) ∧ Primitive ((1, 0) : ℤ × ℤ) ∧
        dot ((0, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) = 0) ∧
      (Primitive ((0, -1) : ℤ × ℤ) ∧
        dot ((0, 1) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) = -1 ∧
        det ((1, 0) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) = -1) ∧
      (Primitive ((1, -3) : ℤ × ℤ) ∧
        dot ((0, 1) : ℤ × ℤ) ((1, -3) : ℤ × ℤ) = -3 ∧
        det ((1, 0) : ℤ × ℤ) ((1, -3) : ℤ × ℤ) = -3 ∧
        det ((-1, 3) : ℤ × ℤ) ((1, -3) : ℤ × ℤ) = 0 ∧
        -((1 : ℕ) : ℤ) • ((1, -3) : ℤ × ℤ) = ((-1, 3) : ℤ × ℤ) ∧
        dot ((0, 1) : ℤ × ℤ) ((-1, 3) : ℤ × ℤ) = 3) := by
  refine ⟨⟨isCoprime_one_right, isCoprime_one_left, by decide⟩,
    ⟨isCoprime_one_right.neg_right, by decide, by decide⟩,
    ⟨isCoprime_one_left, by decide, by decide, by decide, by decide, by decide⟩⟩

/-! ## ⭐ `hexTile` 整条消失：一条无产者 binder 换成三条链上字段

lane-tower-hlev 2026-09-25 把第二方向从 `vJ1` 改成 `vJ` 之后，出了集合层的通用形
`LaneTowerHlevTile.exists_tile_of_rec_vJ`（按标识符名查），前提是
`hlc` / `hne` / `rec_vJ` / `rec_p` / `hperp` / `vJ ≠ 0` / `dot nJ p ≠ 0`，**行列式残余为零**
（独立性由 `LaneTowerHlevEscPos.det_ne_zero_of_perp` 从 `hperp` ＋ `vJ ≠ 0` ＋ `dot nJ p ≠ 0`
白送）。⟹ 本文件的 `hexTile : ∃ wS, ∀ b ∈ S, b + wS ∈ Ah` 不必再当 binder 传：

| 旧 | 新 | 链上来源 |
|---|---|---|
| `hexTile`（无产者 binder） | `hlc : IsLatticeConvexRegion Ah` | `RecVJFromParts.latticeConvex_of_parts` |
| | `hne : Ah.Nonempty` | 字段 `ahat_nonempty` |
| | `hvJne : vJ ≠ 0` | 字段 `vJ_prim`（本原 ⟹ 非零） |

⟹ `bottom_conj123_of_rec_vJ` 的前提**全部**是链上字段，只剩 `hcop` 一条自造残余
（在共线 binder 下等于 `dot nJ vl = -1` ＋ `IsCoprime (c : ℤ) m`，见上一节）。
⚠ hlev 那边的 EXIT／公理本处未复跑（§55）；本条的 EXIT 是本 lane 自己跑的。

## ⛔⛔ 但这条**不**能被读成「合取 1–3 已兑现」：`hrec` 在一个环上

lane-tower-hlev 报：`rec_vJ` 的主仓产者都吃 `bottom`，于是
`bottom` 合取 1 ⟸ `htile` ⟸ `rec_vJ` ⟸ `bottom` 合取 1 成环，而本文件的 `hrec` 正在环上。
按 §110 本 lane **独立按结论型全树搜了一遍**（骨架
`∀ g ∈ ⋃ i, hatOf _ _ _ i, g + vJ ∈ ⋃ i, hatOf _ _ _ i`），结论分两半：

**（a）环确实存在，而且有一条边在本 lane 自己的文件里。**
`RecVJFromParts.rec_vJ_of_parts` 的证明项末位逐字是 `c.bottom`：

```
rec_vJ_of_bottom (latticeConvex_of_parts c) c.hsweep (…c.hhp…) c.hswept c.F.dot_nJ_vJ c.bottom
```

⟹ 拿它当 `hrec` 的产者去兑现合取 1–3，是循环论证。**不许这么接。**

**⭐（b）订正 lane-tower-hlev：环没有封死，至少有两条产者不吃 `bottom`。**
判据是**证明项用了什么**，不是签名收了什么（§111 被谈论 ≠ 在用）：

| 产者 | 用到的东西 | 吃 `bottom`？ |
|---|---|---|
| `RecVJ.rec_vJ_of_halfPlane` | `hperp` / `hlev` / `subBA` / `subAB` / `hbox` / `hkk` / `0 ≤ dot nℓ vJ` | **否** |
| `RecVJComb.parts_rec_vJ` | `c.hhp` / `c.hswept` / `c.rec_p` / `c.F.dot_nJ_vJ` ＋ 侧条件 `hcomb` | **否**（收了整个 `c`，只用四个字段） |

⟹ 正确的记账**不是**「合取 1–3 被环挡死」，而是：**环可以绕开，代价是 `hcomb` 或
`hbox` ＋ `hkk` 这两组侧条件之一**。`hcomb : c.vJ = (a : ℤ) • p + (t : ℤ) • c.vJ1`（`a t : ℕ`）
的产者状态本节未查，留作记账项，不冒充已兑现。

⚠ `RecVJComb` / `RecVJFromParts` 都是本 lane 的文件，上表是本 lane 直接读证明项得到的，
不是转述。`RecVJ.rec_vJ_of_halfPlane` 那一行是读源码得到的，其 EXIT 本处未复跑（§55）。

## 一个测量陷阱，顺手记下

`grep -E "def IsLatticeConvexRegion"` 在 `Nivat/**.lean` 里报 **2 命中 / 2 文件**，看起来像
§97「一名两物」；实际 `AEnv.lean` 那一处是 docstring 里**引用定义的代码块**，真正的 `def`
只有 `Nivat.IsLatticeConvexRegion`（`Section8/HalfPlane.lean`）一个。
⟹ 按 `def` 前缀 grep 会命中文档代码围栏，判「一名两物」前必须看上下文。
-/

/-- ⭐⭐ 合取 1–3，`hexTile` 整条消失，换成三条链上字段。 -/
theorem bottom_conj123_of_rec_vJ {Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 p a : ℤ × ℤ} {cJ : ℤ}
    (ha : a ∈ S)
    (hlc : IsLatticeConvexRegion Ah) (hne : Ah.Nonempty)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z)
    (hrec : ∀ g ∈ Ah, g + vJ ∈ Ah)
    (hrecp : ∀ g ∈ Ah, g + p ∈ Ah)
    (hperp : dot nJ vJ = 0) (hvJne : vJ ≠ 0)
    (hsweep : dot nJ vJ1 < 0) (hp : dot nJ p ≠ 0)
    (hcop : IsCoprime (dot nJ p) (dot nJ vJ1)) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ k : ℤ, L ≤ k → dot nJ (z₀ + k • vJ) = cJ - (ε : ℤ) - 1) :=
  bottom_conj123_of_rec_p_of_tile ha
    (Nivat.LaneTowerHlevTile.exists_tile_of_rec_vJ hlc hne hrec hrecp hperp hvJne hp S)
    hhp hrec hrecp hperp hsweep hp hcop

/-! ## §7  ⭐ `Primitive vJ1` ＋ `∃ m, vJ1 = m • vl`：产者不欠，欠的是**一条**侧条件

集成者 2026-09-25 派工 (a)：「把 `Primitive vJ1` ＋ `∃ m, vJ1 = m • vl` 的生产者做出来」。
量完的结论是：**这不是一笔产者债**，而且它在窗口里只在**一个**位置上真。

### §7.1  一般形的产者已经在仓里三份（§120：按结论型查重，不按名字）

* `Nivat.eq_zsmul_of_det_eq_zero`（`Nivat/Lattice/Primitive.lean`）：`Primitive vl` ＋
  `det vl vJ1 = 0` ⟹ `∃ m : ℤ, vJ1 = m • vl`。**逐字就是要的那条。**
* `Nivat.eq_or_eq_neg_of_det_eq_zero`（同文件）：两条本原 ＋ 共线 ⟹ `vJ1 = vl ∨ vJ1 = -vl`。
* 同形居民另有两条：`L1Assemble.exists_zsmul_ne_zero_of_parallel`（`Primitive vl` ＋
  `det p vl = 0` ＋ `p ≠ 0` ⟹ `∃ c, c ≠ 0 ∧ p = c • vl`）与
  `EnvFit.exists_zsmul_of_dot_eq_zero`（走法向而不走 `det`）。

⟹ 不造第四条。本节只做**它们接不上的那一步**。

### §7.2  真正的侧条件只有一条：`det vl vJ1 = 0`，而它一次付清三件事

`vJ1_eq_vl_of_det_zero`：`Primitive vl` ＋ `Primitive vJ1` ＋ `det vl vJ1 = 0` ＋
`dot nJ vl < 0` ＋ `hsweep` ⟹ **`vJ1 = vl`**。⟹ `m` 这个参数整族是多余的记账：
`∃ m`、`m = 1`、`IsCoprime (c : ℤ) m` 三行全由同一条 `det vl vJ1 = 0` 掉出来。
`prim_vJ1_iff_m_eq_one` 把这件事记成等价：在共线形 ＋ 两个符号下，
**`Primitive vJ1` 就是 `m = 1`**，一个字都不多。
不带 `Primitive vJ1` 时能拿到的最强结论是 `exists_pos_multiple_of_det_zero`（只给 `0 < m`，
与 lane-leafa-shell 报的 `LeafAShellLsideFork.m_pos_of_chain_stock` 同档，走的是 `det` 而不是链货）。

### §7.3  ⛔⛔ 但 `det vl vJ1 = 0` 在窗口里**不是定理**，是 `m−1` 个位置里的**一个**

`b3_colle2.txt:432` 逐字「with `ι+1 ≤ J ≤ ι+m-1`」；本仓约定 `vJ1 = v⃗_{ℓ_{J−1}}`
（记在 `LeafAJSelect.lean`、`NOTATION.md`、`CyclicOrderWindow.lean` §0.1，
⚠ **不是** `v⃗_{ℓ_{J+1}}`，那是 `w`）。

`CyclicOrderWindow.window_bot_of_det_prev_eq_zero` 说共线 ⟹ `t = 0`。本节取它的**逆否**
（`det_prev_ne_zero_of_window_pos`）并搬到方向侧（`not_collinear_of_window_pos`），
再合成等价 `collinear_iff_window_bot`：

| 窗口位置 | `det vl vJ1` | `∃ m, vJ1 = m • vl` |
|---|---|---|
| `t = 0`（`J = ι+1`） | `= 0` | 真，且 `m = 1` |
| `1 ≤ t ≤ m−2`（`J ≥ ι+2`） | `≠ 0` | **假** |

而 `CyclicOrderWindow.three_le_m_of_window_endpoints` 正是从「`vJ1` 共线 ＋ `w` 横截」
推出 `3 ≤ m` ⟹ 在**恰好是本文件用共线的那个构型里**，窗口有 `m−1 ≥ 2` 个位置，
其中 `m−2 ≥ 1` 个位置上共线前提为假。

### §7.4  ⟹ 记账订正：`hm` 是构型，不是待证命题，射程是窗口底端一格

以 `hm : vJ1 = m • vl` 为前提的声明（`GcdCollapse.vJ1_eq_vl_of_prim` /
`GcdCollapse.isCoprime_c_m_of_prim` / `GcdCollapse.gcd_one_iff_of_prim`，以及本文件的
`hcop_iff_coprime_c_m` / `bottom_conj123_of_unit_vl`）全部只管 `J = ι+1` 这**一格**。
⟹ 集成者「净欠项回到一条」在 `J = ι+1` 上对；在 `J ≥ ι+2` 上 `hm` 为假，
`hcop` 必须另走一条路——尖锐条件是 `EnvRefuteCover.heights_iff_cover` 的覆盖条件，
不是 `hcop` 本身（lane-env-refute 报的「`hcop` 严格更强」）。

### §7.5  ⚠ 「哪个几何对象才是 `vJ1` 的来源」

环序模型 `NormalCycle`（`NormalCycle.lean`，namespace `Nivat.LaneTowerHlevNormalCycle`）里的
`dir (C.nu (i + t))`。⛔ **但 `Primitive vJ1` 在那个模型里不免费**：`NormalCycle` 的字段
只有 `hm` / `hsigma` / `nu` / `mem` / `ne_zero` / `anti` 六条，
`grep -c "Primitive\|Prim "` 在该文件上 **0 命中**（分母：该文件全部 779 行 / 6 个字段，
量纲＝匹配行数；回答的是「模型自带不自带本原性」这一个问题）。
⟹ `Primitive vJ1` 只有两条来路：从 `b3_colle2.txt:351`（`v⃗_ℓ` 取模最小）转录；
或在 `t = 0` 一格上由 `vJ1 = vl` ＋ 已有 binder `Primitive vl`（`RegionSteps.lean:653`）白送。
**后者不需要 `:351`** ——这是 §7.2 的副产品。

⚠ **射程（§41）**：§7.3 的负面结论说的是**环序模型里的窗口位置**，不是「链上 `hm` 为假」。
链上的 `J` 由谁选、选在哪一格，本节一个字都没说；本节也没造任何 `NormalCycle` 居民。 -/

section WindowCollinearity

open Nivat.LaneTowerHlevNormalCycle Nivat.CyclicOrderWindow

variable {N : Set (ℤ × ℤ)} {mm : ℕ} {σ : ℤ}

/-- 共线 ＋ 两个符号 ⟹ 倍数为正。**不**要求 `Primitive vJ1`。
`hsign : dot nJ vl < 0` 的产者是 `LeafAShellLsideFork.dot_nJ_vl_neg_of_rec_p`
（lane-leafa-shell 报，2026-09-25；§55 记为「lane 报」，本 lane 未复跑）。 -/
theorem exists_pos_multiple_of_det_zero {nJ vl vJ1 : ℤ × ℤ}
    (hvl : Primitive vl) (hdet : det vl vJ1 = 0)
    (hsign : dot nJ vl < 0) (hsweep : dot nJ vJ1 < 0) :
    ∃ m : ℤ, 0 < m ∧ vJ1 = m • vl := by
  obtain ⟨m, hm⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl hdet
  refine ⟨m, ?_, hm⟩
  have hdotc : dot nJ vJ1 = m * dot nJ vl := by
    rw [hm]; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  by_contra hneg
  push_neg at hneg
  nlinarith [mul_nonneg (neg_nonneg.mpr hneg) (neg_nonneg.mpr (le_of_lt hsign))]

/-- **两条本原 ＋ 共线 ＋ 符号 ⟹ `vJ1 = vl`，`m` 参数整族消失。**
与 `GcdCollapse.vJ1_eq_vl_of_prim` 的区别（§113 双向打印）：那条以 `hm : vJ1 = m • vl` 为前提、
结论同为 `vJ1 = vl`；本条把 `hm` 换成 `det vl vJ1 = 0`，**少一个存在见证、多一条 `Primitive vl`**。
⟹ 两条都不比对方强，接的是不同的上游：`hm` 来自构型裁决，`det vl vJ1 = 0` 来自窗口位置。 -/
theorem vJ1_eq_vl_of_det_zero {nJ vl vJ1 : ℤ × ℤ}
    (hvl : Primitive vl) (hvJ1 : Primitive vJ1) (hdet : det vl vJ1 = 0)
    (hsign : dot nJ vl < 0) (hsweep : dot nJ vJ1 < 0) : vJ1 = vl := by
  rcases Nivat.eq_or_eq_neg_of_det_eq_zero hvl hvJ1 hdet with h | h
  · exact h
  · exfalso
    have : dot nJ vJ1 = -dot nJ vl := by
      rw [h]; simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring
    omega

/-- **`Primitive vJ1` 恰好就是 `m = 1`**：`:351` 的转录在链上买到的东西，一个字不多一个字不少。 -/
theorem prim_vJ1_iff_m_eq_one {nJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hvl : Primitive vl) (hm : vJ1 = m • vl)
    (hsign : dot nJ vl < 0) (hsweep : dot nJ vJ1 < 0) :
    Primitive vJ1 ↔ m = 1 := by
  refine ⟨fun hp => ?_, fun h => by rw [hm, h, one_smul]; exact hvl⟩
  have hmpos : 0 < m := Nivat.GcdCollapse.m_pos_of_sign hm hsweep hsign
  rcases Int.isUnit_iff.mp (Nivat.GcdCollapse.isUnit_m_of_prim hm hp) with h | h
  · exact h
  · omega

/-- **窗口位置决定共线性**：`CyclicOrderWindow.window_bot_of_det_prev_eq_zero` 的逆否。
`t ≠ 0`（即 `J ≥ ι+2`）时 `det ν_ι ν_{J−1} ≠ 0`。 -/
theorem det_prev_ne_zero_of_window_pos (C : NormalCycle N mm σ) (i t : ℕ)
    (ht : t + 1 < mm) (ht0 : t ≠ 0) : det (C.nu i) (C.nu (i + t)) ≠ 0 :=
  fun h => ht0 (window_bot_of_det_prev_eq_zero C i t ht h)

/-- 方向侧逐字形：`J ≥ ι+2` 时**根本不存在** `m` 使 `vJ1 = m • vl`。
⟹ 以 `hm` 为前提的一切声明在这些位置上是空载的（前件假）。 -/
theorem not_collinear_of_window_pos (C : NormalCycle N mm σ) (i t : ℕ)
    (ht : t + 1 < mm) (ht0 : t ≠ 0) :
    ¬ ∃ m : ℤ, dir (C.nu (i + t)) = m • dir (C.nu i) := by
  rintro ⟨m, hm⟩
  refine det_prev_ne_zero_of_window_pos C i t ht ht0 ?_
  rw [← ncy_det_dir_dir, hm]
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- **窗口底端是共线形唯一可用的位置**，等价形。 -/
theorem collinear_iff_window_bot (C : NormalCycle N mm σ) (i t : ℕ) (ht : t + 1 < mm) :
    (∃ m : ℤ, dir (C.nu (i + t)) = m • dir (C.nu i)) ↔ t = 0 := by
  refine ⟨fun h => ?_, fun h => ⟨1, by rw [h, Nat.add_zero, one_smul]⟩⟩
  by_contra ht0
  exact not_collinear_of_window_pos C i t ht ht0 h

end WindowCollinearity

/-! ## §8  任务 (b)：覆盖条件在 `m = 1` 下的尖锐形，以及 `hcop` 到底强多少

集成者 2026-09-25 派工 (b)：「读 `heights_iff_cover`，判它在 `m = 1`、`gcd = g` 下对合取 1
给出的**尖锐**条件是什么；把『严格更强多少』写成内核对象」。

### §8.1  共线下 gcd 根本不看 `c`

`dvd_dot_p_of_collinear`：`p = -(c:ℤ) • vl` ＋ `vJ1 = vl` ⟹ `d = c * e`
（`d := dot nJ p`、`e := -dot nJ vJ1`）。
`gcd_eq_neg_sweep_of_collinear`：⟹ `Int.gcd d e = (dot nJ vJ1).natAbs = |e|`。
⟹ `hcop ⟺ |dot nJ vJ1| = 1`。这与 `GcdCollapse.gcd_one_iff_of_prim` 是同一件事，
但**这里不经过 `Primitive vJ1`**，只用 `vJ1 = vl`（即 §7 的 `m = 1`）。

### §8.2  ⭐ 尖锐条件：`rec_p` 在共线下是**死重**

`rec_p_orbit_one_residue`：沿 `p` 走任意 `k : ℕ` 步，`dot nJ` 的值都同余 mod `e`。
`cover_iff_of_collinear`：⟹ 覆盖条件是 `A` **自己**的性质，加不加 `rec_p` 轨道一模一样。

⟹ `EnvRefuteCover.cover_of_gcd_one` 走的那条路（拿 `rec_p` 的等差轨道 `a + k·d` 打满
mod `e` 的剩余类）在 `m = 1` 上**完全失效**：`e ∣ d` ⟹ 整条轨道锁死在一格里。
它唯一能打满的情形是 `e = 1`，而那时覆盖本来就平凡（`1 ∣` 一切）。

⟹ **合取 1 高度部分的尖锐条件**：`Âinf` **自己**的高度集
`{dot nJ g : g ∈ Âinf}` 必须打满 mod `e` 的全部 `|e|` 个剩余类。
这是一条关于 `Âinf` 的条件——`p` 与 `c` 一个字都不进来。

### §8.3  ⭐ 「强多少」的内核对象，且这次链上忠实

`cover_without_gcd_one_chain_faithful`：`nJ = (0,1)`、`vl = vJ1 = (1,-2)`、`c = 1`、
`p = (-1,2)`、`cJ = 0`、`A = EnvRefuteCover.Aup`（整个上半平面）。
两条向量都本原、`vJ1 = vl`（`m = 1`）、`p = -(1:ℕ) • vl` 逐字、`dot nJ vl = -2 < 0`
⟹ **共线 binder 全部兑现**；而 `Int.gcd d e = 2 ≠ 1`，合取 1 的高度部分**成立**。

⚠ 这一条补掉的是 lane-env-refute 自己标出的射程缺口：他们的 `cover_without_gcd_one`
取 `p = (1,2)`、`vJ1 = (0,-2)`，这两个向量**不平行** ⟹ 不满足 `hp_neg` ＋ 共线两条链 binder。
本条把同一个 `Aup` 搬到平行且双本原的数据上重取，结论保住 ⟹ 「`hcop` 严格更强」
不再只是链外读数。

`aup_rec_p_witness` 在场只是为了兑现 `rec_p` 这条链 binder（`heights_iff_cover` 本身**不要**它），
不参与证明——记在这里免得下一个读者以为它是死代码（§111）。

### §8.4  ⚠ 射程（§41）

本节说的是「`hcop` 严格更强」与「`rec_p` 在共线下不贡献覆盖」，**不**说合取 1 在链上成立
或不成立。`Âinf` 的高度集到底打不打满 mod `e`，本节一个字都没说——那是 `maxA` / `fillCover`
那一侧的事，不在本 lane 手里。
⚠ 又：§8.1–§8.2 全部以 `vJ1 = vl` 为前提 ⟹ 按 §7.3，射程是窗口底端 `J = ι+1` 一格。 -/

/-- 共线（`m = 1`）下 `d = c * e`：`rec_p` 的步长是 sweep 步长的整数倍。 -/
theorem dvd_dot_p_of_collinear {nJ vl p vJ1 : ℤ × ℤ} {c : ℕ}
    (hp : p = -(c : ℤ) • vl) (hvJ1 : vJ1 = vl) :
    dot nJ p = (c : ℤ) * (-dot nJ vJ1) := by
  rw [hp, hvJ1]
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- ⟹ `gcd d e = |e|`：共线下 gcd 根本不看 `c`，只是 sweep 高度的绝对值。 -/
theorem gcd_eq_neg_sweep_of_collinear {nJ vl p vJ1 : ℤ × ℤ} {c : ℕ}
    (hp : p = -(c : ℤ) • vl) (hvJ1 : vJ1 = vl) :
    Int.gcd (dot nJ p) (-dot nJ vJ1) = (dot nJ vJ1).natAbs := by
  have hd := dvd_dot_p_of_collinear (nJ := nJ) (c := c) hp hvJ1
  have hnat : (dot nJ p).natAbs = c * (dot nJ vJ1).natAbs := by
    rw [hd, Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_natCast]
  have hg : Nat.gcd ((dot nJ vJ1).natAbs) (c * (dot nJ vJ1).natAbs)
      = (dot nJ vJ1).natAbs :=
    Nat.gcd_eq_left ⟨c, by ring⟩
  simp only [Int.gcd, Int.natAbs_neg, hnat]
  rw [Nat.gcd_comm]; exact hg

/-- **`rec_p` 的整条轨道锁在同一个剩余类里**：共线下沿 `p` 走多少步都换不了 mod `e` 的格。 -/
theorem rec_p_orbit_one_residue {nJ vl p vJ1 g : ℤ × ℤ} {c : ℕ}
    (hp : p = -(c : ℤ) • vl) (hvJ1 : vJ1 = vl) (k : ℕ) :
    (-dot nJ vJ1) ∣ (dot nJ (g + (k : ℤ) • p) - dot nJ g) := by
  refine ⟨(k : ℤ) * (c : ℤ), ?_⟩
  have hd := dvd_dot_p_of_collinear (nJ := nJ) (c := c) hp hvJ1
  rw [Nivat.EnvRefuteCover.dot_add_loc, Nivat.EnvRefuteCover.dot_zsmul_loc, hd]
  ring

/-- ⟹ 覆盖条件是 `A` **自己**的性质，`rec_p` 一步都帮不上。 -/
theorem cover_iff_of_collinear {A : Set (ℤ × ℤ)} {nJ vl p vJ1 : ℤ × ℤ} {c : ℕ}
    (hp : p = -(c : ℤ) • vl) (hvJ1 : vJ1 = vl) :
    (∀ r : ℤ, ∃ g ∈ A, (-dot nJ vJ1) ∣ (dot nJ g - r)) ↔
      (∀ r : ℤ, ∃ g ∈ A, ∃ k : ℕ, (-dot nJ vJ1) ∣ (dot nJ (g + (k : ℤ) • p) - r)) := by
  constructor
  · intro h r
    obtain ⟨g, hg, hdvd⟩ := h r
    exact ⟨g, hg, 0, by simpa using hdvd⟩
  · intro h r
    obtain ⟨g, hg, k, hdvd⟩ := h r
    refine ⟨g, hg, ?_⟩
    have horb := rec_p_orbit_one_residue (nJ := nJ) (g := g) (c := c) hp hvJ1 k
    have : dot nJ g - r =
        (dot nJ (g + (k : ℤ) • p) - r) - (dot nJ (g + (k : ℤ) • p) - dot nJ g) := by ring
    rw [this]; exact dvd_sub hdvd horb

/-! ### 链上忠实的「覆盖成立而 `hcop` 为假」见证

`nJ = (0,1)`、`vl = vJ1 = (1,-2)`、`c = 1`、`p = (-1,2)`、`cJ = 0`、`A = Aup`。
两条向量都本原，`vJ1 = vl`（`m = 1`），`p = -(1:ℕ) • vl` 逐字成立 ⟹ 全部共线 binder 兑现。 -/

theorem aup_rec_p_witness :
    ∀ g ∈ Nivat.EnvRefuteCover.Aup, g + ((-1, 2) : ℤ × ℤ) ∈ Nivat.EnvRefuteCover.Aup := by
  intro g hg
  have h : (0 : ℤ) ≤ g.2 := hg
  show (0 : ℤ) ≤ (g + ((-1, 2) : ℤ × ℤ)).2
  simp only [Prod.snd_add]
  omega

theorem aup_halfPlane_witness :
    ∀ g ∈ Nivat.EnvRefuteCover.Aup, (0 : ℤ) ≤ dot ((0, 1) : ℤ × ℤ) g := by
  intro g hg
  have h : (0 : ℤ) ≤ g.2 := hg
  simp only [dot]
  linarith

/-- ⭐ **链上忠实版「`hcop` 严格更强」**：全部共线 binder ＋ 两条本原都兑现，
合取 1 的高度部分**成立**，而 `hcop` **为假**（`gcd = 2`）。 -/
theorem cover_without_gcd_one_chain_faithful :
    (Primitive ((0, 1) : ℤ × ℤ) ∧ Primitive ((1, -2) : ℤ × ℤ) ∧
      ((1, -2) : ℤ × ℤ) = ((1, -2) : ℤ × ℤ) ∧
      -((1 : ℕ) : ℤ) • ((1, -2) : ℤ × ℤ) = ((-1, 2) : ℤ × ℤ) ∧
      dot ((0, 1) : ℤ × ℤ) ((1, -2) : ℤ × ℤ) < 0) ∧
    (∀ ε : ℕ, ∃ z ∈ MaxEnv.reachSet Nivat.EnvRefuteCover.Aup ((1, -2) : ℤ × ℤ),
      dot ((0, 1) : ℤ × ℤ) z = 0 - (ε : ℤ) - 1) ∧
    Int.gcd (dot ((0, 1) : ℤ × ℤ) ((-1, 2) : ℤ × ℤ))
      (-dot ((0, 1) : ℤ × ℤ) ((1, -2) : ℤ × ℤ)) = 2 := by
  refine ⟨⟨isCoprime_one_right, isCoprime_one_left, rfl, by decide, by decide⟩, ?_, by decide⟩
  refine (Nivat.EnvRefuteCover.heights_iff_cover (by decide) aup_halfPlane_witness).mpr ?_
  have he : (-dot ((0, 1) : ℤ × ℤ) ((1, -2) : ℤ × ℤ)) = 2 := by decide
  rw [he]
  exact Nivat.EnvRefuteCover.aup_cover

/-! ## §9. `vJ1` 在链上的来源：边法向 `nprevJ`，不是 `:351` 的 minimum norm

本节回答集成者派的那一格（“把 `Primitive vJ1` ⊕ `∃ m, vJ1 = m • vl` 的生产者做出来，
做不出则报哪个几何对象才是 `vJ1` 的来源”）。答案是后者，而且它把前者的一半也顺手付了。

### §9.1 实测：`vJ1` 不是由 `:351` 进来的

`Nivat/**.lean` 全树 `vJ1 :=` 的构造点只有三族（按形状搜，§120）：

* **ccw**：`vJ1 := dir nprevJ`——`exists_nprevJ_vJ1`（`LeafAJSelect.lean`）的输出；
* **cw**：`vJ1 := -(dir nprevJ)`——`LeafACwBranch.lean` 与 `CyclicOrderAdjRefute.lean`；
* **透传**：`ChainAssemble.lean` / `ChainAssembleInter.lean` / `ItemIIChain.lean` 里的 `vJ1 := vJ1`。

而消费者 `RegionSteps.lean` 里 `vJ1` 的命中数是 **0**（分母：整个文件；量纲：匹配行；
回答的是“消费者自己提不提 `vJ1`”）——它是经结构字段进来的，不是消费者的 binder。

⏹ 结论：链上的 `vJ1` **不是**按原文 `b3_colle2.txt:351`（“the non-zero vector parallel to
`ℓ` of minimum norm”）定义的，它是上一条边的**边法向 `nprevJ` 旋转 90°**。
两者在几何上指同一件事，但在 Lean 里是两个不同的入口，可供的东西不一样。

### §9.2 ⭐ 于是 `Primitive vJ1` 有了不吃原文的生产者

`IsEdge R n := Prim n ∧ (face R n).Nontrivial`（`IsEdge`，`LatticeEdges.lean`）——
**本原性写在边集定义里**。所以 `nprevJ ∈ E R` 白送 `Prim nprevJ`，再经 `dir` 保本原
（`hbase_prim_dir`）就得 `Primitive vJ1`，两个符号分支各一条：
`prim_vJ1_of_edge_ccw` / `prim_vJ1_of_edge_cw`。

这正是 `isLatticeConvexRegion_reachSet_of_site_ccw` / `..._cw`（`ShellHreachInf.lean`）
已经在内部做的那一步，只是那里没把它单独取出来当结论。按集成者的记账口径：
`Primitive vJ1` 确实是**缺失的 binder 导出而不是债**，但导出它的 binder 是 `nprevJ ∈ E R`，
**不是** `:351`。区别是实的：前者是链上现货，后者要先把“`vJ1` 就是 `v⃗_{ℓ_{J−1}}`”
这个对应证出来，而那个对应在主仓里没有任何声明。

### §9.3 ⭐ 而共线那一半，换了个形状就看清楚了

`collinear_vJ1_vl_iff_perp_ccw` / `..._cw`：在 `nprevJ ≠ 0`、`Primitive vl` 之下，

  `∃ m, vJ1 = m • vl`  ⟺  `dot nprevJ vl = 0`.

即共线裁决 `hm` 等价于“**上一条边的法向垂直于 `vl`**”，也就是 `nprevJ = ±n_ℓ`，
也就是 `J−1 = ι`，也就是 **`J = ι+1`，窗口底端**。这与 §7.3 从循环序模型那边得到的
结论逐字一致，但推导路径完全独立（那边用 `NormalCycle` 的角序，这边只用 `dot_dir`）。

`vJ1_eq_vl_of_edge_perp_ccw` 把整包合上：边成员 + 垂直 + 两个符号守卫 ⟹ `vJ1 = vl`（即 `m = 1`）。

### §9.4 ⭕ 负控：边成员资格本身给不出共线

`edge_mem_does_not_give_collinear`：取 `R = {(0,0), (1,-1)}`、`nprevJ = (1,1)`，
则 `(1,1) ∈ E R` 真正兑现（`edgeWit_mem_E`，连面非平凡都验了），`Primitive (1,0)` 真，
而 `∃ m, dir (1,1) = m • (1,0)` **假**。⟹ §9.2 的生产者只产 `Primitive vJ1` 那一半，
共线那一半必须另外供 `dot nprevJ vl = 0`，它不是边数据的推论。

### §9.5 ⚠ 射程（§41）

本节说的是“主仓里 `vJ1` 由什么构造”，**不**断言链上 `J` 落在哪一格，也**不**断言
原文的 `v⃗_{ℓ_{J−1}}` 与主仓的 `vJ1` 定义不等价——只断言主仓里没有把这个等价写成声明。
另：`ChainDataGeomParts` 的 `vJ1` 是裸数据（唯一约束 `hsweep`），所以 §9.2 的生产者
**还接不上那个结构**；要接上得先有一条 `∃ nprevJ ∈ E …, vJ1 = ±dir nprevJ` 的字段或引理，
那是集成者侧的事，本 lane 没动 `ChainPartsFeed.lean`。
-/

section VJ1Source

variable {R : Set (ℤ × ℤ)}

theorem hbase_prim_dir {n : ℤ × ℤ} (hn : Prim n) : Primitive (dir n) := by
  rw [← prim_iff_primitive]
  have h1 : Int.gcd (dir n).1 (dir n).2 = Int.gcd n.1 n.2 := by
    simp only [dir, Int.gcd, Int.natAbs_neg]
    exact Nat.gcd_comm _ _
  show Int.gcd (dir n).1 (dir n).2 = 1
  exact h1.trans hn

theorem prim_vJ1_of_edge_ccw {nprevJ vJ1 : ℤ × ℤ}
    (hnpE : nprevJ ∈ E R) (hvJ1 : vJ1 = dir nprevJ) : Primitive vJ1 := by
  rw [hvJ1]
  exact hbase_prim_dir (mem_E_iff.mp hnpE).1

theorem prim_vJ1_of_edge_cw {nprevJ vJ1 : ℤ × ℤ}
    (hnpE : nprevJ ∈ E R) (hvJ1 : vJ1 = -(dir nprevJ)) : Primitive vJ1 := by
  rw [hvJ1, ← prim_iff_primitive]
  exact (prim_iff_primitive.mpr (hbase_prim_dir (mem_E_iff.mp hnpE).1)).neg

theorem collinear_vJ1_vl_iff_perp_ccw {nprevJ vl vJ1 : ℤ × ℤ}
    (hnp_ne : nprevJ ≠ 0) (hvl : Primitive vl) (hvJ1 : vJ1 = dir nprevJ) :
    (∃ m : ℤ, vJ1 = m • vl) ↔ dot nprevJ vl = 0 := by
  constructor
  · rintro ⟨m, hm⟩
    have h0 : dot nprevJ vJ1 = 0 := by rw [hvJ1]; exact dot_dir nprevJ
    have hmul : m * dot nprevJ vl = 0 := by
      rw [hm] at h0
      simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h0 ⊢
      linarith
    rcases mul_eq_zero.mp hmul with h | h
    · exfalso
      apply Nivat.PolyChainSum.dir_ne_zero hnp_ne
      rw [← hvJ1, hm, h, zero_smul]
    · exact h
  · intro hperp
    refine Nivat.eq_zsmul_of_det_eq_zero hvl ?_
    rw [hvJ1]
    exact det_eq_zero_of_dot_eq_zero hnp_ne hperp (dot_dir nprevJ)

theorem collinear_vJ1_vl_iff_perp_cw {nprevJ vl vJ1 : ℤ × ℤ}
    (hnp_ne : nprevJ ≠ 0) (hvl : Primitive vl) (hvJ1 : vJ1 = -(dir nprevJ)) :
    (∃ m : ℤ, vJ1 = m • vl) ↔ dot nprevJ vl = 0 := by
  constructor
  · rintro ⟨m, hm⟩
    have h0 : dot nprevJ vJ1 = 0 := by
      rw [hvJ1]
      simp only [dot, Prod.fst_neg, Prod.snd_neg, dir]
      ring
    have hmul : m * dot nprevJ vl = 0 := by
      rw [hm] at h0
      simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h0 ⊢
      linarith
    rcases mul_eq_zero.mp hmul with h | h
    · exfalso
      apply Nivat.PolyChainSum.dir_ne_zero hnp_ne
      have : -(dir nprevJ) = (0 : ℤ × ℤ) := by rw [← hvJ1, hm, h, zero_smul]
      rw [(neg_neg (dir nprevJ)).symm, this, neg_zero]
    · exact h
  · intro hperp
    refine Nivat.eq_zsmul_of_det_eq_zero hvl ?_
    rw [hvJ1]
    refine det_eq_zero_of_dot_eq_zero hnp_ne hperp ?_
    simp only [dot, Prod.fst_neg, Prod.snd_neg, dir]
    ring

theorem vJ1_eq_vl_of_edge_perp_ccw {nprevJ nJ vl vJ1 : ℤ × ℤ}
    (hnpE : nprevJ ∈ E R) (hnp_ne : nprevJ ≠ 0) (hvl : Primitive vl)
    (hvJ1 : vJ1 = dir nprevJ) (hperp : dot nprevJ vl = 0)
    (hsign : dot nJ vl < 0) (hsweep : dot nJ vJ1 < 0) : vJ1 = vl := by
  obtain ⟨m, hm⟩ := (collinear_vJ1_vl_iff_perp_ccw hnp_ne hvl hvJ1).mpr hperp
  have hp : Primitive vJ1 := prim_vJ1_of_edge_ccw hnpE hvJ1
  have h1 : m = 1 := (prim_vJ1_iff_m_eq_one hvl hm hsign hsweep).mp hp
  rw [hm, h1, one_smul]

/-! ### Negative control: `nprevJ ∈ E R` does **not** by itself give collinearity. -/

def edgeWitR : Set (ℤ × ℤ) := {z | z = ((0 : ℤ), (0 : ℤ)) ∨ z = ((1 : ℤ), (-1 : ℤ))}

theorem edgeWit_mem_E : ((1 : ℤ), (1 : ℤ)) ∈ E edgeWitR := by
  refine ⟨by decide, ?_⟩
  refine ⟨((0 : ℤ), (0 : ℤ)), ⟨Or.inl rfl, ?_⟩, ((1 : ℤ), (-1 : ℤ)), ⟨Or.inr rfl, ?_⟩, by decide⟩
  · intro y hy
    rcases (hy : y = ((0 : ℤ), (0 : ℤ)) ∨ y = ((1 : ℤ), (-1 : ℤ))) with rfl | rfl <;> decide
  · intro y hy
    rcases (hy : y = ((0 : ℤ), (0 : ℤ)) ∨ y = ((1 : ℤ), (-1 : ℤ))) with rfl | rfl <;> decide

theorem edge_mem_does_not_give_collinear :
    ((1 : ℤ), (1 : ℤ)) ∈ E edgeWitR ∧ Primitive ((1 : ℤ), (0 : ℤ)) ∧
      ¬ ∃ m : ℤ, dir ((1 : ℤ), (1 : ℤ)) = m • ((1 : ℤ), (0 : ℤ)) := by
  refine ⟨edgeWit_mem_E, isCoprime_one_left, ?_⟩
  rintro ⟨m, hm⟩
  have h2 : (dir ((1 : ℤ), (1 : ℤ))).2 = (m • ((1 : ℤ), (0 : ℤ)) : ℤ × ℤ).2 := by rw [hm]
  simp only [dir, Prod.smul_snd, smul_eq_mul, mul_zero] at h2
  exact one_ne_zero h2

end VJ1Source

/-! ## §10. 把 §8 从「窗口底端一格」脱出来：侧条件换成纯高度整除

lane-env-refute 2026-09-25 指出 §8.1–§8.2 整段吃 `vJ1 = vl`，并给了脱法：换成
**纯高度**侧条件。本节照办，路径归他，内核对象归本节。

### §10.1 新侧条件

记 `e := -dot nJ vJ1`。§8 的四条里真正做功的只有 `e ∣ dot nJ p` 这一件事，
而共线只是供它的一种方式。于是：

* `gcd_eq_neg_sweep_of_dvd` —— `e ∣ dot nJ p` ⟹ `Int.gcd (dot nJ p) e = |dot nJ vJ1|`。
  **一个字不提 `vl`、`c`、`m`、`det`。**
* `rec_p_orbit_one_residue_of_dvd` / `cover_iff_of_dvd` —— 同样只吃 `e ∣ dot nJ p`。
  ⟹ §8.2 那条机制读数（`rec_p` 换不了剩余类 ⟹ 剩余类只能由 `A` 自身的高度谱供）
  **在窗口每一格都成立**，不再限于底端。
* `dvd_dot_p_of_height_dvd` —— 从 `hp : p = -(c:ℤ) • vl` ＋ `e ∣ dot nJ vl` 供出它。

### §10.2 §113：新侧条件严格弱于共线，两个方向都打印

* **共线 ⟹ 新侧条件**：`height_dvd_of_collinear`（`vJ1 = vl` ⟹ `e ∣ dot nJ vl`）。
* **新侧条件 ⇏ 共线**：`height_dvd_strictly_weaker_than_collinear` ——
  `nJ = (0,1)`、`vl = (1,-1)`、`vJ1 = (1,1)`：整除成立而 `det vl vJ1 = 2 ≠ 0`。

⟹ §8.1–§8.2 的结论在 §10 的形式下**不再继承 §7.3 的一格射程**。§8 的旧形保留不删（§103），
但引用时请引 §10 这一组。

### §10.3 ⛔ 三条就地订正（2026-09-25）

**(i) §8.3 的 `cover_without_gcd_one_chain_faithful` 是重号，不是补缺口。**
lane-env-refute 的 `conj1_heights_without_unit_magnitude`（`EnvRefuteFaceNormal.lean`）
写入于同轮 22:12:06，本文件 §8 写入 22:53。本处**自己读了他那条的 binder 表**（§50）：
它的 ∃ 包含 `Primitive nJ/vJ/vl/vJ1`、`dot nJ vJ = 0`、`0 < c ∧ p = -(c:ℤ)•vl`、
`0 < m ∧ vJ1 = (m:ℤ)•vl`、`det p vl = 0`、`det p vJ1 = 0`、`rec_p`、`rec_vJ`、`hhp`、
`dot nJ p ≠ 0`、`dot nJ vl = -2`、`gcd = 2`、以及合取 1 的高度部分成立。
按 §113 反方向核：**本文件 §8.3 有而他那条没有的，一条也没有**。
⟹ §8.3 docstring 里「补掉 lane-env-refute 自己标出的射程缺口」那句作废——那个缺口是他标的，
也是他自己在 41 分钟前补的；本文件读到的「`p=(1,2)` 与 `vJ1=(0,-2)` 不平行」是**上上轮**的
`EnvRefuteCover.cover_without_gcd_one`。去重取舍归集成者（§110.2）。
⚠ `rec_p_orbit_one_residue` / `cover_iff_of_collinear` 两条不在此列，他明确认了是新的。

**(ii) 本 lane 在跨 lane 消息里说过「链上 `∃ m, vJ1 = m • vl` 在 `J ≥ ι+2` 为假」——
那句比本文件 §7.5 的射程段强，以 §7.5 为准。** §7 证的是环序模型里 `dir (C.nu ·)` 两两之间的
共线只在 `t = 0` 成立；搬到链上的 `vl` / `vJ1` 还缺一条词典（谁证 `vl`、`vJ1` 分别等于
某个 `dir (C.nu ·)`）。该词典本 lane 未找到，也未主张。lane-env-refute 2026-09-25 钉出这处
不一致，本处照收。⚠ 同时他钉出：`GcdCollapse.det_p_vJ1_zero` 的方向是**共线 ⟹ `det p vJ1 = 0`**，
它**不是**共线的产者——这与本文件 §9.4 的负控同向。

**(iii) `hcomb` / (β) 两条绕环路线均已判死（lane-tower-hlev 报，本处未复跑，§55）。**
`TowerHlevTile.not_hcomb_of_chain` 判 `hcomb` 链上为假（对任意 `m`、任意整数系数）；
`TowerHlevHkk.not_hkk_of_chain` 判 (β) 链上为假，因为链上的 `kk` 至少线性增长，
落在 `tmp/wip/hbase_hkk.lean` 的 `not_hkk_of_id` 排除的那一类里。
⟹ 本文件记账里「`hcomb` 是绕开 `rec_vJ` 循环的唯一残项」一句删除；
`rec_vJ_of_halfPlane_kkSqrt` 的辖域是 `kk := Nat.sqrt`，**不是**链上的 `c.kk`，链上用不了。
-/

section DvdDescope

theorem gcd_eq_neg_sweep_of_dvd {nJ p vJ1 : ℤ × ℤ}
    (hdvd : (-dot nJ vJ1) ∣ dot nJ p) :
    Int.gcd (dot nJ p) (-dot nJ vJ1) = (dot nJ vJ1).natAbs := by
  obtain ⟨q, hq⟩ := hdvd
  have hnat : (dot nJ p).natAbs = (dot nJ vJ1).natAbs * q.natAbs := by
    rw [hq, Int.natAbs_mul, Int.natAbs_neg]
  have hg : Nat.gcd ((dot nJ vJ1).natAbs) ((dot nJ vJ1).natAbs * q.natAbs)
      = (dot nJ vJ1).natAbs :=
    Nat.gcd_eq_left ⟨q.natAbs, rfl⟩
  simp only [Int.gcd, Int.natAbs_neg, hnat]
  rw [Nat.gcd_comm]
  exact hg

theorem dvd_dot_p_of_height_dvd {nJ vl p vJ1 : ℤ × ℤ} {c : ℕ}
    (hp : p = -(c : ℤ) • vl) (he : (-dot nJ vJ1) ∣ dot nJ vl) :
    (-dot nJ vJ1) ∣ dot nJ p := by
  obtain ⟨q, hq⟩ := he
  refine ⟨-(c : ℤ) * q, ?_⟩
  have hpv : dot nJ p = -(c : ℤ) * dot nJ vl := by
    rw [hp]
    simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hpv, hq]
  ring

theorem rec_p_orbit_one_residue_of_dvd {nJ p vJ1 g : ℤ × ℤ}
    (hdvd : (-dot nJ vJ1) ∣ dot nJ p) (k : ℕ) :
    (-dot nJ vJ1) ∣ (dot nJ (g + (k : ℤ) • p) - dot nJ g) := by
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨(k : ℤ) * q, ?_⟩
  have hexp : dot nJ (g + (k : ℤ) • p) - dot nJ g = (k : ℤ) * dot nJ p := by
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hexp, hq]
  ring

theorem cover_iff_of_dvd {A : Set (ℤ × ℤ)} {nJ p vJ1 : ℤ × ℤ}
    (hdvd : (-dot nJ vJ1) ∣ dot nJ p) :
    (∀ r : ℤ, ∃ g ∈ A, (-dot nJ vJ1) ∣ (dot nJ g - r)) ↔
      (∀ r : ℤ, ∃ g ∈ A, ∃ k : ℕ, (-dot nJ vJ1) ∣ (dot nJ (g + (k : ℤ) • p) - r)) := by
  constructor
  · intro h r
    obtain ⟨g, hg, hd⟩ := h r
    exact ⟨g, hg, 0, by simpa using hd⟩
  · intro h r
    obtain ⟨g, hg, k, hd⟩ := h r
    refine ⟨g, hg, ?_⟩
    have horb := rec_p_orbit_one_residue_of_dvd (nJ := nJ) (g := g) hdvd k
    have hrw : dot nJ g - r =
        (dot nJ (g + (k : ℤ) • p) - r) - (dot nJ (g + (k : ℤ) • p) - dot nJ g) := by ring
    rw [hrw]
    exact dvd_sub hd horb

/-- 窗口底端一格是新侧条件的**特例**，不是它的前提：`vJ1 = vl` ⟹ `e ∣ dot nJ vl`。 -/
theorem height_dvd_of_collinear {nJ vl vJ1 : ℤ × ℤ} (hvJ1 : vJ1 = vl) :
    (-dot nJ vJ1) ∣ dot nJ vl := by
  refine ⟨-1, ?_⟩
  rw [hvJ1]
  ring

/-- ⭕ 负控：新侧条件**严格弱于**共线（§113 反方向）——存在 `e ∣ dot nJ vl` 而 `vJ1 ≠ vl`
甚至不共线的数据。`nJ = (0,1)`、`vl = (1,-1)`、`vJ1 = (1,1)`：`dot nJ vl = -1`、
`-dot nJ vJ1 = -1`，整除成立，而 `det vl vJ1 = 2 ≠ 0`。 -/
theorem height_dvd_strictly_weaker_than_collinear :
    (-dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (1 : ℤ))) ∣ dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (-1 : ℤ)) ∧
      det ((1 : ℤ), (-1 : ℤ)) ((1 : ℤ), (1 : ℤ)) ≠ 0 := by
  constructor
  · exact ⟨1, by decide⟩
  · decide

end DvdDescope

/-! ## §11. §10 的侧条件到底比 `IsUnit m` 弱多少（§113，两个方向都打印）

lane-env-refute 2026-09-25 落了 `dvd_iff_isUnit_of_collinear`（`EnvRefuteFaceNormal.lean`，
本处未复跑，§55）：共线 ＋ `dot nJ vl ≠ 0` 之下 `(-dot nJ vJ1) ∣ dot nJ vl ⟺ IsUnit m`，
并建议把 §8 的 `vJ1 = vl` 整体换成 `IsUnit m`（理由：“`m = -1` 同样够用，你漏掉了”）。
本节把那条建议的两个方向都变成内核对象，结论是：**不搬**。

### §11.1 他那条管的是 `e ∣ dot nJ vl`，而 §10 用的是 `e ∣ dot nJ p`，后者严格更弱

`dvd_dot_p_iff_dvd_of_collinear`：共线 ＋ `dot nJ vl ≠ 0` 之下

  `(-dot nJ vJ1) ∣ dot nJ p  ⟺  m ∣ (c : ℤ)`.

而 `IsUnit m ⇒ m ∣ c` 恒成立，反之不然。反方向的见证是
`height_dvd_does_not_give_isUnit_m`：`nJ = (0,1)`、`vl = (0,-1)`、`m = 2`、`c = 4`
——`dot nJ vl = -1 < 0` 与 `dot nJ vJ1 = -2 < 0` **两个符号守卫都兑现**，`e = 2 ∣ 4 = dot nJ p`，
而 `¬ IsUnit 2`。⇒ 把 §10 换成 `IsUnit m` 是**往回走一步**，不搬。

### §11.2 ⏹ “`m = -1` 同样够用”在链上是空的

`isUnit_m_iff_m_eq_one_of_sign`：共线 ＋ `dot nJ vl < 0` ＋ `dot nJ vJ1 < 0` 之下
`IsUnit m ⟺ m = 1`。理由是 `GcdCollapse.m_pos_of_sign` 给 `0 < m`，`m = -1` 当场出局。
⇒ 他指出的“漏掉 `m = -1`”在**纯代数上成立**，在**链上为空**：两个符号守卫都是
`ChainDataGeomParts` 的现货。本条与 §7 的 `prim_vJ1_iff_m_eq_one` 互不包含：
那条从 `Primitive vJ1` 进，本条从 `IsUnit m` 进。

### §11.3 ⚠ 未主张

本节不否定他那条等价（我未复跑，且它管的是另一个整除式），只回答“该不该把 §10 搬过去”。
也不主张链上 `m` 等于什么——共线裁决本身的产者仍然没有（见 §9.3）。
-/

section DvdVsIsUnit

theorem dvd_dot_p_iff_dvd_of_collinear {nJ vl p vJ1 : ℤ × ℤ} {c : ℕ} {m : ℤ}
    (hp : p = -(c : ℤ) • vl) (hm : vJ1 = m • vl) (hs : dot nJ vl ≠ 0) :
    (-dot nJ vJ1) ∣ dot nJ p ↔ m ∣ (c : ℤ) := by
  have hvJ1 : dot nJ vJ1 = m * dot nJ vl := by
    rw [hm]; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hpv : dot nJ p = -((c : ℤ) * dot nJ vl) := by
    rw [hp]; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [hvJ1, hpv, neg_dvd, dvd_neg, mul_dvd_mul_iff_right hs]

/-- ⭕ §113 反方向：§10 的侧条件 `e ∣ dot nJ p` **严格弱于** `IsUnit m`。
`nJ = (0,1)`、`vl = (0,-1)`、`m = 2`、`c = 4`——两个符号守卫都兑现，整除成立，而 `m` 非单位。 -/
theorem height_dvd_does_not_give_isUnit_m :
    (-dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-2 : ℤ))) ∣ dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (4 : ℤ)) ∧
      dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) < 0 ∧
      dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-2 : ℤ)) < 0 ∧
      ¬ IsUnit ((2 : ℤ)) := by
  refine ⟨⟨2, by decide⟩, by decide, by decide, fun h => ?_⟩
  rcases Int.isUnit_iff.mp h with h | h <;> omega

/-- ⛔ 链上 `m = -1` 被两个符号守卫排除：`IsUnit m ⟺ m = 1`。 -/
theorem isUnit_m_iff_m_eq_one_of_sign {nJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hm : vJ1 = m • vl) (hsign : dot nJ vl < 0) (hsweep : dot nJ vJ1 < 0) :
    IsUnit m ↔ m = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h]; exact isUnit_one⟩
  have hpos : 0 < m := Nivat.GcdCollapse.m_pos_of_sign hm hsweep hsign
  rcases Int.isUnit_iff.mp h with h | h
  · exact h
  · omega

end DvdVsIsUnit

/-! ## §12. §10.2 那条负控的见证换成非退化的（lane-env-refute 2026-09-25 钉）

### §12.1 旧见证落在两个退化点上（本处自己重算，§50，不取转述）

§10.2 用的是 `nJ = (0,1)`、`vl = (1,-1)`、`vJ1 = (1,1)`。重算：

* `dot nJ vJ1 = 0·1 + 1·1 = 1 > 0` ⟹ 链上的符号 binder `hsweep : dot nJ vJ1 < 0`
  在那组数据上**为假**；
* `e := -dot nJ vJ1 = -1` ⟹ **模数是单位**。

两条本处都确认。

### §12.2 单位模数处这条分离买不到东西

`cover_trivial_of_unit_modulus`：只要 `A` 非空且 `IsUnit (-dot nJ vJ1)`，覆盖条件
`∀ r, ∃ g ∈ A, e ∣ dot nJ g - r` **平凡为真**——`nJ` / `p` / `vJ1` 的几何一个字都不参与。
⟹ 在 `|e| = 1` 处「新侧条件成立而共线不成立」的原因是 `±1` 整除一切，不是新侧条件更松。
`old_separation_witness_is_degenerate` 把「旧见证确实落在那里」钉成内核对象
（`IsUnit (-dot (0,1) (1,1))` ∧ `¬ (dot (0,1) (1,1) < 0)`）。

### §12.3 换成非退化的见证

`height_dvd_strictly_weaker_nondegenerate`：`nJ = (0,1)`、`vl = (1,-4)`、`vJ1 = (1,-2)`、
`c = 1`、`p = -(1:ℤ) • vl = (-1,4)`。一个 ∃ 包里同时兑现：

* `Primitive vl` ∧ `Primitive vJ1`；
* `dot nJ vl = -4 < 0` ∧ `dot nJ vJ1 = -2 < 0` ⟹ **两条链上符号 binder 都兑现**；
* `e = 2` 且 `2 ≤ e` 写进结论 ⟹ **模数非退化，剩余类机器不空转**；
* `e ∣ dot nJ vl`（`-4 = 2·(-2)`）**与** `e ∣ dot nJ p`（`4 = 2·2`）
  ⟹ 同时覆盖 lane-env-refute 的高度形和本文件 §10 的 `dot nJ p` 形；
* `det vl vJ1 = 2 ≠ 0`，且逐字证了 `¬ ∃ m : ℤ, vJ1 = m • vl`。

⟹ §10.2 那句「新侧条件严格弱于共线」在**非退化区域**里成立。

### §12.4 ⚠ 射程与去重

* `height_dvd_strictly_weaker_than_collinear` **不撤、不删**（§105）：它作为陈述是真的。
  作废的只是 §10.2 把它当「§113 反方向的可用见证」这一**用法**。
* lane-env-refute 同日在 `EnvRefuteFaceNormal.lean` 落了 `hdvd_strictly_weaker_nondegenerate`，
  用的是同一组数字（本处未复跑，§55）。本节仍落一条，是因为他那条只带 `e ∣ dot nJ vl`，
  而 §10 的消费者吃的是 `e ∣ dot nJ p`；本节的 ∃ 包两条都带。去重取舍归集成者（§110.2）。
* ⚠ 本节**不主张**链上真有这样的 `(nJ, vl, vJ1, p)`——它是负控，只否掉「新侧条件 ⟹ 共线」。
* lane-env-refute 第三次提「`m = -1` 你漏了」：答案已在 §11 的
  `isUnit_m_iff_m_eq_one_of_sign`（两条符号 binder 之下 `IsUnit m ⟺ m = 1`），本节不重复造对象。
-/

section DvdSeparationNondegenerate

/-- 单位模数处覆盖条件平凡为真：`A` 非空 ＋ `IsUnit (-dot nJ vJ1)` 就够，
`nJ` / `p` / `vJ1` 的几何不参与。§12.2 用它说明旧见证为何买不到东西。 -/
theorem cover_trivial_of_unit_modulus {A : Set (ℤ × ℤ)} {nJ vJ1 g₀ : ℤ × ℤ}
    (hg₀ : g₀ ∈ A) (hunit : IsUnit (-dot nJ vJ1)) :
    ∀ r : ℤ, ∃ g ∈ A, (-dot nJ vJ1) ∣ (dot nJ g - r) :=
  fun _ => ⟨g₀, hg₀, hunit.dvd⟩

/-- ⭕ 旧见证（§10.2）确实落在退化点：`e = -1` 是单位（⟹ `cover_trivial_of_unit_modulus`
适用），且 `hsweep : dot nJ vJ1 < 0` 在那组上为假。 -/
theorem old_separation_witness_is_degenerate :
    IsUnit (-dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (1 : ℤ))) ∧
      ¬ (dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (1 : ℤ)) < 0) := by
  constructor
  · have h : (-dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (1 : ℤ))) = -1 := by decide
    rw [h]
    exact Int.isUnit_iff.mpr (Or.inr rfl)
  · decide

/-- ⭕ 负控（§113 反方向，非退化版）：存在带**全部链上符号 binder**、模数 `2 ≤ e`、
两条整除都成立、而 `vJ1` 与 `vl` 不共线的数据。见 §12.3 的数字表。 -/
theorem height_dvd_strictly_weaker_nondegenerate :
    ∃ nJ vl vJ1 p : ℤ × ℤ, ∃ c : ℕ,
      Primitive vl ∧ Primitive vJ1 ∧
        0 < c ∧ p = -(c : ℤ) • vl ∧
        dot nJ vl < 0 ∧ dot nJ vJ1 < 0 ∧
        2 ≤ -dot nJ vJ1 ∧
        (-dot nJ vJ1) ∣ dot nJ vl ∧
        (-dot nJ vJ1) ∣ dot nJ p ∧
        det vl vJ1 ≠ 0 ∧
        ¬ ∃ m : ℤ, vJ1 = m • vl := by
  refine ⟨((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (-4 : ℤ)), ((1 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (4 : ℤ)), 1, isCoprime_one_left, isCoprime_one_left, Nat.one_pos, ?_,
    by decide, by decide, by decide, ⟨-2, by decide⟩, ⟨2, by decide⟩, by decide, ?_⟩
  · norm_num [Prod.ext_iff]
  · rintro ⟨m, hm⟩
    rw [Prod.ext_iff] at hm
    obtain ⟨h1, h2⟩ := hm
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
    omega

end DvdSeparationNondegenerate


/-! ## §13. lane-env-refute 把 §12 的判据反向打在 §11 的见证上——照收，并给空格子定理

### §13.1 命中确认（本处自己复算并证了，§50）

§11 的 `height_dvd_does_not_give_isUnit_m` 用的是 `vl = (0,-1)`、`m = 2` ⟹ `vJ1 = (0,-2)`、
`p = (0,4)`（即 `c = 4`）。`Primitive (0,-2) = IsCoprime (0:ℤ) (-2)`，而 `Int.gcd 0 (-2) = 2 ≠ 1`
⟹ **`Primitive vJ1` 在那组数据上为假**。`not_prim_sep_witness_vJ1` 把这一条钉成内核对象。

⟹ 这与本文件上一轮对 lane-env-refute「`m = -1`」的判词是**同一条判据的两次应用**：
分离见证必须落在链上字段兑现得到的区域里，否则那个分离买不到东西。照收，不辩。

### §13.2 后果：`IsUnit m` 方向的分离格子在 `Primitive vJ1` 之下是空的

`isUnit_gap_empty_of_prim_vJ1`：共线 ＋ `hsign` ＋ `hsweep` ＋ `Primitive vJ1`
⟹ `IsUnit m` **与** `∀ c : ℕ, m ∣ (c : ℤ)` 同时**无条件**成立。

⟹ §11.1 说「§10 的 `e ∣ dot nJ p` 严格弱于 `IsUnit m`」——**陈述层仍然对**（两条确实是不同的
整除式，`dvd_dot_p_iff_dvd_of_collinear` 把前者钉成 `m ∣ c`），但它主张的那段**实际差距**
（`m ∣ c` 而 `¬ IsUnit m`）在 `Primitive vJ1` 之下**取不到**。§11 的「不搬」结论因此要改口径：
不是「我的更弱所以更好用」，而是「两条在链上合流，搬不搬都一样」。

### §13.3 ⚠ 但 §12 的见证活着，两件事别混

塌掉的是对 **`IsUnit m`** 的分离，**不是**对**共线**的分离：

* `m` 只在共线之下有定义，而共线 ＋ `Primitive vJ1` ＋ 两条符号 binder 已由
  `prim_vJ1_iff_m_eq_one` 钉成 `m = 1`，所以「`m` 非单位」那一格本来就是空的；
* `height_dvd_strictly_weaker_nondegenerate`（§12）的第二个合取项**就是** `Primitive vJ1`
  （`vJ1 = (1,-2)`，`IsCoprime 1 (-2)` 成立），并且它是**不共线**的数据。
  ⟹ 「新侧条件 ⇏ 共线」在 `Primitive vJ1` ＋ 两条符号 binder ＋ `2 ≤ e` 之下**仍然成立**。

### §13.4 去重（归集成者，§110.2）

lane-env-refute 的 `isUnit_m_of_prim_vJ1`（共线 ＋ `Primitive vJ1` ⟹ `IsUnit m`）是主仓
`GcdCollapse.isUnit_m_of_prim` 的重证，而本文件的 `prim_vJ1_iff_m_eq_one` 早已把它与两条符号
binder 合成 `Primitive vJ1 ↔ m = 1`。⟹ 他 §14 的「合流」结论在主仓里**已有现货**，
不是新增能力；本节只落两件他那边没有的：命中确认的内核对象，与空格子定理。

### §13.5 ⚠ 未主张

本节全部形如「若共线则……」。**共线裁决本身的产者仍然没有**，本处不主张有。
`Primitive vJ1` 的产者是 §9 的 `prim_vJ1_of_edge_ccw` / `_cw`（吃 `nprevJ ∈ E R`
＋ `vJ1 = ±dir nprevJ`），它要挂上 `ChainDataGeomParts` 还缺一条字段，那是集成者的文件。

### §13.6 lane-tower-hlev 钉的射程区分（本处照收，未复跑他的对象，§55）

§9.3 的 `collinear_vJ1_vl_iff_perp_ccw` / `_cw` 是**链侧内部**的等价（两边都是链上对象），
**不受**第 179 轮朝向红线约束；受约束的是再往原文指标走的那一步——
「`nprevJ = ±n_ℓ`」是「哪一格是 `ℓ_{ι−1}`」型的指标事实，落在红线禁区里。
⟹ 引 §9.3 时这两步不许并成一笔记账。该指标事实 lane-tower-hlev 已报集成者待裁，本 lane 不碰。
-/

section PrimGap

/-- §11 的分离见证 `vJ1 = (0,-2)` 不是本原的（`Int.gcd 0 (-2) = 2`）
⟹ 那组数据落在 `¬ Primitive vJ1` 上。见 §13.1。 -/
theorem not_prim_sep_witness_vJ1 : ¬ Primitive ((0 : ℤ), (-2 : ℤ)) := by
  rw [← prim_iff_primitive]
  show ¬ (Int.gcd (0 : ℤ) (-2 : ℤ) = 1)
  decide

/-- ⭐ 空格子：共线 ＋ 两条链上符号 binder ＋ `Primitive vJ1` 之下，
`IsUnit m` 与 `∀ c, m ∣ c` 都**无条件**成立 ⟹ §11.1 主张的那段实际差距在链上取不到。
⚠ 这**不**影响 §12 对**共线**的分离（见 §13.3）。 -/
theorem isUnit_gap_empty_of_prim_vJ1 {nJ vl vJ1 : ℤ × ℤ} {m : ℤ}
    (hvl : Primitive vl) (hm : vJ1 = m • vl)
    (hsign : dot nJ vl < 0) (hsweep : dot nJ vJ1 < 0)
    (hprim : Primitive vJ1) :
    IsUnit m ∧ ∀ c : ℕ, m ∣ (c : ℤ) := by
  have h1 : m = 1 := (prim_vJ1_iff_m_eq_one hvl hm hsign hsweep).mp hprim
  exact ⟨by rw [h1]; exact isUnit_one, fun _ => by rw [h1]; exact one_dvd _⟩

end PrimGap


/-! ## §14. `hsign` 不是字段——订正 §11.2／§13 的措辞，并量化代价

### §14.1 订正（lane-env-refute 2026-09-25 钉；本处自己数了字段表，§50）

本文件 §11.2 与 §13 都写过「两条链上符号 binder 都是 `ChainDataGeomParts` 的字段」。**错。**

* `hsweep : dot nJ vJ1 < 0` 是字段 ✓（`ChainPartsFeed.lean` 的 `hsweep`）。
* `dot nJ vl < 0` **不是字段**：整个 `ChainPartsFeed.lean` 里 `dot nJ vl` 只有 **1** 处命中，
  而那一处在某个 docstring 里（分母：该文件全文；量纲：匹配行数；回答的问题：
  「有没有字段约束 `dot nJ vl` 的符号」）。⟹ 命中 0 个字段。

⚠ **字段总数三本账打架，我不采用任何一版**（§82）：该文件自记「共 34 个字段」，
lane-env-refute 报 36，本处按「结构体内缩进两格的 `name :` 行、剔除 docstring 块」数得 **37**。
⟹ 总数这个数字**作废**，等集成者定一个可复算的计数口径。**但结论不依赖分母**：
三版都不含任何约束 `dot nJ vl` 符号的字段。

`dot nJ vl < 0` 的产者是定理 `LeafAShellLsideFork.dot_nJ_vl_neg_of_rec_p`，它另吃
`hc : 0 < c` 与 `hp_neg : p = -(c : ℤ) • vl` 两条**非字段**（lane-env-refute 报，本处未复跑，§55）。

### §14.2 代价量化：去掉 `hsign`，`m = -1` 就活过来

`m_neg_one_survives_without_hsign`：`nJ = (0,1)`、`vl = (1,1)`、`vJ1 = (-1,-1)`、`m = -1`。
`Primitive vl` ✓、`Primitive vJ1` ✓、`vJ1 = m • vl` ✓、`dot nJ vJ1 = -1 < 0`（**`hsweep` 兑现**）、
`0 < dot nJ vl = 1`（`hsign` **不**兑现）、`m ≠ 1`。

⟹ 只有 `hsweep`（字段）＋ `Primitive vl` ＋ `Primitive vJ1`（§9 的边数据现货）时，
`m = 1` **推不出来**。`prim_vJ1_iff_m_eq_one` 的 `hsign` **不可去**，它是这条链上唯一
非现货的一环。

### §14.3 措辞怎么改

§11.2 与 §13 里凡写「两条链上符号 binder（字段）」的，一律改读作
「**一条字段（`hsweep`）＋ 一条带非字段前提的定理（`hsign`）**」。

⚠ `isUnit_gap_empty_of_prim_vJ1`（§13.2）与 `isUnit_m_iff_m_eq_one_of_sign`（§11.2）
**本身不受影响**——它们把 `hsign` 写成显式 binder，从来没声称它是字段。
受影响的只是「所以 `m = -1` 在链上取不到」这句话的**供给强度**：那句仍然对，
但它的成本是 `hp_neg` ＋ `0 < c`，而不是零。

### §14.4 ⛔ 一条循环：`residue_coverage_of_parts_lside` 不能当合取 1 的产者

lane-leafa-shell 报 `heights_covered_of_parts_lside` / `residue_coverage_of_parts_lside`
（`LeafAShellLsideFork.lean`）是「零 binder，只吃一个 `ChainDataGeomParts` 实例」。
配上 `EnvRefuteCover.heights_iff_cover`（`hsweep` ＋ `hhp` 之下，覆盖条件
⟺ `∀ ε, ∃ z ∈ reachSet, dot nJ z = cJ - (ε:ℤ) - 1`），看起来就能产出 `bottom` 的合取 1,
绕过全部已关停的路线（`hcop` / `gcd` / `|dot nJ vl| = 1` / `det p vJ1 = ±1`）。

**但它是循环的，本处读了源码两处确认**：两条都 `obtain … := parts_stock_lside cp`，
而 `parts_stock_lside` 的第三个分量是 `LaneLeafAGenRecVJ.rec_vJ_of_parts cp`，
后者的最后一个实参正是 **`c.bottom`**（`RecVJFromParts.lean`，按标识符名查）。
⟹ 整条是 `bottom ⟹ 覆盖 ⟹ 合取 1`，**不减债**。

⚠ 这**不是**说那两条错或没用：它们对任何**不是** `bottom` 的消费者照旧有效。
说的只是——**它们不能用来免掉造结构时要交的 `bottom`**。

⚠ 本处也按形状全树查了「谁把覆盖条件当**假设**吃」：命中 **0**
（分母：`Nivat/**` 全树；48 行含 `∣ (dot`，其中覆盖条件形状的全部出现在结论位或 `↔` 的一侧）。
⟹ 本节**不**加 `LeafAShellLsideFork` 的 import：那会给本文件闭包加 11 个模块
（106 → 117，已算过，四条禁止模块均不在其中，无环），换来一条零消费者、
且唯一可见用法是循环的定理。不值。

### §14.5 ⚠ 未主张

`rec_vJ` 在链上是否存在**不经 `bottom`** 的产者，本 lane 未查遍。
已知的另一条（`RecVJComb.parts_rec_vJ` 的 `hcomb` 侧条件）被 lane-tower-hlev 判链上为假
（按他报，本处未复跑，§55）。若有人找到不经 `bottom` 的 `rec_vJ` 产者，§14.4 的循环就断了，
届时那条组合值得落——**那时再加 import**。
-/

section HsignNotAField

/-- ⭕ 负控：只有 `hsweep`（字段）＋ `Primitive vl` ＋ `Primitive vJ1`（边数据现货）时，
`m = 1` 推不出来——`m = -1` 连同两条本原性和 `hsweep` 一起可满足。
⟹ `prim_vJ1_iff_m_eq_one` 的 `hsign` 不可去。见 §14.2。 -/
theorem m_neg_one_survives_without_hsign :
    ∃ nJ vl vJ1 : ℤ × ℤ, ∃ m : ℤ,
      Primitive vl ∧ Primitive vJ1 ∧ vJ1 = m • vl ∧
        dot nJ vJ1 < 0 ∧ 0 < dot nJ vl ∧ m ≠ 1 := by
  refine ⟨((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (1 : ℤ)), ((-1 : ℤ), (-1 : ℤ)), -1,
    isCoprime_one_left, ?_, ?_, by decide, by decide, by decide⟩
  · rw [← prim_iff_primitive]
    show Int.gcd (-1 : ℤ) (-1 : ℤ) = 1
    decide
  · norm_num [Prod.ext_iff]

end HsignNotAField


/-! ## §15. `vJ1` 字段的产者：以 `ChainDataGeomParts` 为参数陈述（集成者 2026-09-26 派）

按集成者裁决 4：写在本文件、以 `ChainDataGeomParts` 为参数陈述，**不碰** `ChainPartsFeed.lean`；
要不要把 `VJ1FromEdge` 变成字段由他定。

### §15.1 `vJ1_edge_stock_of_parts` 一次给两件现货

从 `VJ1FromEdge R cp` ＋ `Primitive vl` 同时产出：

* **`Primitive cp.vJ1`** —— 集成者第 234 轮在 `vJ1` 字段 docstring 里标的两条缺失之一。
  它不经原文：`E R` 的成员资格里就含本原性（`IsEdge R n := Prim n ∧ (face R n).Nontrivial`）。
* **共线 ⟺ `dot nprevJ vl = 0`** —— §9.3 的链侧内部等价，同一个 `nprevJ` 见证两件事。

⟹ 若 `VJ1FromEdge` 成为字段，上面两件都**不必**另立字段。

### §15.2 ⚠ `nJ` / `cJ` 那半：这条路线加不了多少，算清楚在此

`nJ_edge_new_content_of_parts`：`cp.nJ ∈ E R` 给出 `(face R cp.nJ).Nontrivial ∧ Primitive cp.nJ`,
而**后者已经是字段 `nJ_prim`** ⟹ 走边集对 `nJ` 真正新增的只有**面非平凡**这一件。

⟹ `nJ` / `cJ` 的缺口**不是本原性**，是「`ℓ_J` 真的是 `Â_∞` 的一条半无限边」
（`b3_colle2.txt:506`：`Â_∞` 有两条半无限边，一条 ∥ `ℓ`、另一条 ∥ `ℓ_J`；`J` 本身由
`:498-502` 的**增长判据**定，纯增长条件、无行列式／角序条件）。那是另一类义务，
本节**没做**，也不假装做了。

### §15.3 ⚠ 未主张

* 本节**不证** `VJ1FromEdge` 可从现有字段导出。lane-leafa-shell 的
  `prim_vJ1_not_from_sweep_obligations` 已证 `hsweep` ＋ `hswept` 推不出 `Primitive vJ1`，
  故也推不出本条（按他报，本处未复跑，§55）；「整个结构推不出」两边都没造反模型。
* 本节**不**碰「`nprevJ = ±n_ℓ`」那一步——那是「哪一格是 `ℓ_{ι−1}`」型指标事实，
  落第 179 轮朝向红线禁区，lane-tower-hlev 已报集成者待裁（见 §13.6）。
* `±` 那个符号**不是** `:351` 定的：`:351` 只给「本原 ＋ 平行」，符号由 cw 约定定
  （lane-leafa-shell 本轮自读原文的结论，本处照收）。

### §15.4 import 变更记录

新增一条 `import Nivat.External.Colle.ChainPartsFeed`（结构类型的来源）。
本文件闭包 **107 → 114**（含自身口径，新版 `tmp/_impclosure.py` 与自算两者一致），
新增 7 个模块：`AbsorbEnv` / `AhatMono` / `ChainPartsFeed` / `EnvTranslate` / `ItemIIRec` /
`LeafAItemII` / `ShellSweep`。四条禁止模块（`RegionSteps` / `ColleRegion` /
`Case2WindowProbe` / `NfpLPreamble`）均不可达，无环（`ChainPartsFeed` 的闭包不含本模块）。
-/

section VJ1Feed

variable {α : Type*}

/-- **候选字段：`vJ1` 是 `Â` 某条边的方向（差一个符号）。**

原文锚 `b3_colle2.txt:440`（Lemma 3.5(i)）把 `vJ1` 定为 `v⃗_{ℓ_{J−1}}`，即 `Â_∞^{(ε)}` 的
扫掠方向；`:506` 说 `Â_∞` 有两条半无限边、一条 ∥ `ℓ`、另一条 ∥ `ℓ_J`，且
「Actually, `Â_∞` is an `(ℓ, ℓ_J)`-region」。逐量词对应：

* `∃ nprevJ` ↦ 原文那条边的**法向**；
* `nprevJ ∈ E R` ↦ 「它确实是 `R` 的一条边」（`E` 的成员资格内含 `Prim`）；
* `cp.vJ1 = dir nprevJ ∨ cp.vJ1 = -(dir nprevJ)` ↦ 「`vJ1` 平行于那条边」。
  **`±` 是符号约定，不是原文给的**：`:351` 只把 `v⃗_ℓ` 定成「∥ `ℓ` 的最小范数非零向量」
  ＝ 本原 ＋ 平行，符号同样不定（lane-leafa-shell 2026-09-26 读原文，本处照收）。 -/
def VJ1FromEdge {η xper : Config α} {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (R : Set (ℤ × ℤ)) (cp : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    Prop :=
  ∃ nprevJ ∈ E R, cp.vJ1 = dir nprevJ ∨ cp.vJ1 = -(dir nprevJ)

/-- ⭐ **候选字段的两件现货**：`VJ1FromEdge` ＋ `Primitive vl` ⟹ `Primitive cp.vJ1`
（第 234 轮标的缺失之一）**与**「共线 ⟺ `dot nprevJ vl = 0`」，且由**同一个** `nprevJ` 见证。
见 §15.1。 -/
theorem vJ1_edge_stock_of_parts {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {R : Set (ℤ × ℤ)}
    (cp : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hvl : Primitive vl) (h : VJ1FromEdge R cp) :
    Primitive cp.vJ1 ∧
      ∃ nprevJ ∈ E R, ((∃ m : ℤ, cp.vJ1 = m • vl) ↔ dot nprevJ vl = 0) := by
  obtain ⟨nprevJ, hnpE, hdir⟩ := h
  have hne : nprevJ ≠ 0 := (mem_E_iff.mp hnpE).1.ne_zero
  rcases hdir with hd | hd
  · exact ⟨prim_vJ1_of_edge_ccw hnpE hd, nprevJ, hnpE,
      collinear_vJ1_vl_iff_perp_ccw hne hvl hd⟩
  · exact ⟨prim_vJ1_of_edge_cw hnpE hd, nprevJ, hnpE,
      collinear_vJ1_vl_iff_perp_cw hne hvl hd⟩

/-- ⚠ **边集路线对 `nJ` 加不了多少，这条把它算清楚**：`cp.nJ ∈ E R` 的两个分量里
`Primitive cp.nJ` 已经是字段 `nJ_prim` ⟹ 真正新增的只有 `(face R cp.nJ).Nontrivial`。
`nJ` / `cJ` 的缺口是「`ℓ_J` 真是 `Â_∞` 的半无限边」（`b3_colle2.txt:506`），不是本原性。
见 §15.2。 -/
theorem nJ_edge_new_content_of_parts {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {R : Set (ℤ × ℤ)}
    (cp : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (h : cp.nJ ∈ E R) :
    (face R cp.nJ).Nontrivial ∧ Primitive cp.nJ :=
  ⟨(mem_E_iff.mp h).2, cp.nJ_prim⟩

end VJ1Feed


/-! ## §16. 裁决 3(b)：`hexTile` 那一格——**没换签名，改成加一个入口**，理由如下

集成者 2026-09-26 批准「把 `bottom_conj123_of_rec_p_of_tile` 的 `hexTile` 换成 hlev 的
`hlc` / `hne` / `hvJne` 三条字段」，条件是「**新版前提严格更弱**」。

### §16.1 ⚠ 按逻辑读，换过去的前提是严格更**强**，不是更弱（§113 两向都打印）

* **新 ⟹ 旧**：三条新前提 ＋ 本已有的 `hrec` / `hrecp` / `hperp` / `hp`，经
  `TowerHlevTile.exists_tile_of_rec_vJ` 直接**推出** `hexTile`。（这就是下面那条的证明体。）
* **旧 ⇏ 新**：`hexTile` 只说「某个平移把 `S` 整个塞进 `Ah`」，与 `Ah` 是否格凸无关，
  也给不出 `vJ ≠ 0`。

⟹ 前提集合的包含方向是 **新 ⊆ 旧的推论**，所以带三条字段的那版作为**定理更不一般**。
把已落地的签名改成它，等于用一条更一般的换一条更不一般的，还要冒工具盲区 3 的风险
（`type_of%` / `rfl` 护栏只有全量 `lake build` 撞得上，而本 lane 不许跑全量 build）。

⟹ **因此没有换，改成加一条入口；旧版一个字没动。** 集成者要的东西（一个从字段进的入口）
拿到了，代价是多一条声明，不是改签名。若他仍要删旧版，那是一次单独的裁决，不在本节里做。

### §16.2 供给面——这才是那条裁决真正的内容，新版的价值在这里

`hexTile` 在链上**没有**产者；三条新前提**全是链上现货**：

* `Ah.Nonempty` ← 字段 `ahat_nonempty`；
* `vJ ≠ 0` ← 字段 `vJ_prim`（`LeafAShellLsideFork.parts_stock_lside` 里就是这么取的）；
* `IsLatticeConvexRegion Ah` ← `LaneLeafAGenRecVJ.latticeConvex_of_parts`，
  由字段 `maxA` / `hfin` / `AhatMono` 产出。

### §16.3 ⚠ 未主张

* **本条仍带 `hcop`。** `hcop` 已判为充分不必要（覆盖条件才是充要），其上游
  `det p vJ1 = ±1` 链上为假 ⟹ **本条不是合取 1–3 的链上产者**，它只把 tile 那一格的供给
  换成了字段。别读成「合取 1–3 有产者了」。
* `IsLatticeConvexRegion` 全仓有**两个**定义（§97；本文件前面已记过这处一名多物）。
  本条用到的是命名空间解析给出的那一个，且**与 `exists_tile_of_rec_vJ` 用的是同一个**——
  证据是这条编得过（内核给的，不是我读出来的）。`latticeConvex_of_parts` 产出的是哪一个，
  本处**未核**。
-/

section TileFields

/-- ⭐ **从字段进的入口**（裁决 3(b)，加而不换）：把 `hexTile` 换成
`hlc` / `hne` / `hvJne` 三条链上现货，经 `TowerHlevTile.exists_tile_of_rec_vJ` 造出 `hexTile`
再委托给 `bottom_conj123_of_rec_p_of_tile`。
⚠ 仍带 `hcop` ⟹ **不是**链上产者，见 §16.3。 -/
theorem bottom_conj123_of_rec_p_of_fields {Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 p a : ℤ × ℤ} {cJ : ℤ}
    (ha : a ∈ S) (hlc : IsLatticeConvexRegion Ah) (hne : Ah.Nonempty)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z)
    (hrec : ∀ g ∈ Ah, g + vJ ∈ Ah)
    (hrecp : ∀ g ∈ Ah, g + p ∈ Ah)
    (hperp : dot nJ vJ = 0) (hvJne : vJ ≠ 0)
    (hsweep : dot nJ vJ1 < 0) (hp : dot nJ p ≠ 0)
    (hcop : IsCoprime (dot nJ p) (dot nJ vJ1)) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ k : ℤ, L ≤ k → dot nJ (z₀ + k • vJ) = cJ - (ε : ℤ) - 1) :=
  bottom_conj123_of_rec_p_of_tile ha
    (Nivat.LaneTowerHlevTile.exists_tile_of_rec_vJ hlc hne hrec hrecp hperp hvJne hp S)
    hhp hrec hrecp hperp hsweep hp hcop

end TileFields


/-! ## §17. 纸面定位：`vJ` 的定向在原文哪一句（集成者 2026-09-26 派；硬规矩 6 第 1 步）

问的是：`b3_colle2.txt:440-520` 里**哪一句**给出「`v_J` 落在 `−v⃗_ℓ` 与 `v⃗_{ℓ_{J−1}}` 之间」
（或任何等价的角序／定向陈述）。

### §17.1 结论：(c) 档，而且比「没找到」硬一层

**我没找到那一句**（§51：这是「我没找到」，**不是**「不存在」）。理由再往下一层：
**原文从头到尾没有写过 `v⃗_{ℓ_J}` 这个对象**，所以那一句没有可陈述的主语。

读数（仪器：定长字面量扫 `\vec{v}_{\boldsymbol{\ell}` 宏并抓其下标；**分母＝该宏全文 78 次出现**；
正控 `_{J-1}` = 4 > 0、负控 `_{ZZZ}` = 0，两控都过，§133／§134）：

    ℓ'  37 ｜ 裸 ℓ  28 ｜ ℓ_{J−1}  4 ｜ ℓ_{ι−1}  3 ｜ ℓ_{I−1}  2
    ℓ_{ι+m−1}  2 ｜ ℓ_{J+1}  1 ｜ ℓ_i  1 ｜ ⭐ ℓ_J  0

另（同一文件，分母＝全文行数）：`cone` 0 行、`recession` 0 行、`between` 1 行（且与
`\vec{v}` 同行 0 次）、`inward` 2 行。

### §17.2 但角序数据确实在原文里——分散在四处，不是一句

* `:255`（约定）：`conv(S)` 的边界**正定向** ⟹ 每条边 `w ∈ E(S)` 从边界继承朝向；
  `|E(S)| < ∞` 时每条边有唯一后继 `w_s` 与前驱 `w_p`，记 `w_p ≺ w`。
* `:424`（Lemma 3.5 的 binder，`:541` / `:764` 逐字重复）：`ℓ_1,…,ℓ_{2m}` 是过原点、
  平行于 `S_φ` 各边的有向直线的一个枚举，其中**平行于 `ℓ_{i+1}` 的边是平行于 `ℓ_i` 的边的后继**，
  下标模 `2m`。
* `:432`（与 `:498` 取到的是同一个 `J`）：`ι+1 ≤ J ≤ ι+m−1`。
* `:880`：`ℓ_{ι−1}` 与 `ℓ_{ι+m−1}` **反平行** ⟹ 枚举里 `ℓ_{k+m} = −ℓ_k`。这是
  「`−v⃗_ℓ` 也是枚举中的一格（第 `ι+m` 格）」的唯一出处。

四条合起来给出：沿正定向转，`v⃗_{ℓ_{J−1}}` 的方向角 ≤ `v⃗_{ℓ_J}` 的 < `−v⃗_{ℓ_ι}` 的，
即 `v⃗_{ℓ_J}` 落在 `−v⃗_ℓ` 与 `v⃗_{ℓ_{J−1}}` 张成的**开锥**内。⟹ 按集成者给的三档，
这是 **(b)：原文给了（以四条合成的形式），但前提比链上多。**

### §17.3 多出来的前提，逐条列（(b) 档要求的清单）

链上 `ChainDataGeomParts` 只有裸向量 `vJ1` / `vJ`（＋ `nJ` / `cJ`）。37 条字段里**没有**：

1. 枚举 `ℓ_1,…,ℓ_{2m}` 本身，以及「`vJ1` 与 `vJ` 是该枚举中**相邻两格**的 `v⃗`」；
2. 指标窗口 `ι+1 ≤ J ≤ ι+m−1`（链上连 `ι`、`J`、`m` 这三个量都没有）；
3. 反平行 `ℓ_{k+m} = −ℓ_k`（`:880`），否则 `−v⃗_ℓ` 不是窗口端点；
4. `E(S_φ)` 的有限性与正定向约定（`:255`），否则「后继」无定义。

⟹ 四条一条都不是字段，也没有任何字段推得出它们。

### §17.4 ⛔ 更要紧的：把 §17.2 那条定向**当字段加进来，`hcomb` 仍然拿不到**

`hcomb_fails_under_full_cone_stock`（本节）给出一组数据，定向（开锥形式，逐字见该条签名）
**为真**，而 `hcomb` 对一切 `a t : ℤ`（不止 `ℕ`）**为假**。

⟹ 集成者三档里的 (a)「找到那一句 ⟹ 加字段 ⟹ `hcomb` 路线活」在本见证上**不成立**。
死因在这组数据上不是符号（那是集成者 `hcomb_fails_on_full_sign_stock` 的死因），是**整性**：
锥系数是 `1/2`，而 `hcomb` 要 `−vl` 方向的系数落在 `c·ℕ` 里、`vJ1` 方向的落在 `ℕ` 里。
⟹ **`hcomb` 比原文的几何强**（硬规矩 5：比原文强 = 债）。

⚠ 射程自限：本见证只说「**这组**前提（含定向）推不出 `hcomb`」，**不**说 `hcomb` 链上为假；
也**不**是在证 `hcomb`（集成者已封该路），它回答的是「要不要为 `hcomb` 加一条定向字段」——答案是
加了也不够。

### §17.5 ⟹ 建议换靶：原文给 `rec_vJ` 的理由根本不是锥分解

`:386`（Definition 3.1）＋ `:506`：`Â_∞` 是**凸**集，有两条半无限边，一条平行于 `ℓ`、
另一条平行于 `ℓ_J`；由 `:255`，那条边沿有向直线 `ℓ_J` 的朝向 ⟹ `Â_∞` 含一条方向为
`+v⃗_{ℓ_J}` 的射线 ⟹ 该方向在其 recession cone 内 ⟹ `Â_∞ + vJ ⊆ Â_∞`，即 `rec_vJ`。
**这条路一步也不经过 `hcomb`。**

而它要的字段，恰好与我上轮为 `nJ` / `cJ` 报的那一条**是同一个东西**：
「`ℓ_J` 真是 `Â_∞` 的半无限边」（`:506`；`J` 由 `:498-502` 的增长判据钉住）
⟹ **两笔欠账并成一笔。**

⚠ 未主张：(i)「凸集含方向 `d` 的射线 ⟹ 对 `+d` 封闭」在 ℝ² 上是标准事实，但链上的对象是
`IsLatticeConvexRegion`（全仓两个定义，§97），**ℤ² 版要自己证，我没证**；
(ii) 该字段我**没有**产者。

### §17.6 ⚠ `inward` 那两处：原文写过这种形状的定向句，但主语不是 `v⃗_{ℓ_J}`

`inward` 全文 2 行，句式都是「`v⃗_{ℓ_?}` points inward to the `(ℓ,ℓ_J)`-region」：

* `:928`（Claim 4.15 的反证）：主语是 `v⃗_{ℓ_{ι+m−1}}`，在假设 `J < ι+m−1` 之下
  ⟹ 说的是**严格在 `J` 之后**那一格朝内，不是 `J` 自己；而 Claim 4.15 的结论正是
  `J = ι+m−1`，此后 `v⃗_{ℓ_J}` 就是区域自己那条边的方向（边界，不是朝内）。
* `:878` 落在 Claim 4.9 的证明里 ⟹ **顺序禁令的禁区**：本处只记命中数，不读内容、不搭建。

⟹ 两处都是「哪一格」型指标事实，撞第 179 轮朝向红线 ⟹ **本 lane 不在其上建东西**，报集成者裁。

### §17.7 未做

* 没有去证 `hcomb`（集成者已封），也没有碰整除／格指标那一侧的产者方向。
* 没有把 §17.2 的四条写成字段——那是集成者的裁决；本节只给「加了也不够」的内核证据。
-/

section HcombCone

/-- ⭐ **纸面定向即便当字段拿到，`hcomb` 仍然拿不到。**

见证数据 `nJ = (0,1)`、`vl = (-3,-2)`、`c = 1`、`p = -(1:ℤ) • vl = (3,2)`、
`vJ1 = (-1,-2)`、`vJ = (1,0)`。它同时兑现：

* 五条本原性、`0 < c`、`p = -(c:ℤ) • vl`；
* `dot nJ vJ = 0`（字段 `F.dot_nJ_vJ`）、`dot nJ vJ1 < 0`（字段 `hsweep`）、
  `0 < dot nJ p`、`dot nJ vl < 0`、`2 ≤ -dot nJ vJ1`（非退化模数）、
  `det vl vJ1 ≠ 0`（**横截格**）；
* ⭐ **定向**：`∃ k a t : ℤ, 0 < k ∧ 0 < a ∧ 0 < t ∧ k • vJ = a • p + t • vJ1`
  （取 `k = 2`、`a = t = 1`）——这正是「`vJ` 落在由 `p` 与 `vJ1` 张成的**开锥**内」，
  即 §17.2 那四条原文合成所能给出的那一条的逐字形式。

而最后一条说：**对一切 `a t : ℤ`（不止 `ℕ`）** `vJ ≠ a • p + t • vJ1`。

⟹ `hcomb`（`RecVJComb.parts_rec_vJ` 的那条 binder，系数取 `ℕ`）在这组数据上为假，
**而定向为真**。死因在这组数据上不是符号，是**整性**：锥系数是 `1/2`。射程见 §17.4。 -/
theorem hcomb_fails_under_full_cone_stock :
    ∃ nJ vl vJ1 p vJ : ℤ × ℤ, ∃ c : ℕ,
      Primitive nJ ∧ Primitive vl ∧ Primitive vJ1 ∧ Primitive p ∧ Primitive vJ ∧
        0 < c ∧ p = -(c : ℤ) • vl ∧
        dot nJ vJ = 0 ∧ dot nJ vJ1 < 0 ∧ 0 < dot nJ p ∧ dot nJ vl < 0 ∧
        2 ≤ -dot nJ vJ1 ∧ det vl vJ1 ≠ 0 ∧
        (∃ k a t : ℤ, 0 < k ∧ 0 < a ∧ 0 < t ∧ k • vJ = a • p + t • vJ1) ∧
        (∀ a t : ℤ, vJ ≠ a • p + t • vJ1) := by
  refine ⟨((0 : ℤ), (1 : ℤ)), ((-3 : ℤ), (-2 : ℤ)), ((-1 : ℤ), (-2 : ℤ)),
    ((3 : ℤ), (2 : ℤ)), ((1 : ℤ), (0 : ℤ)), 1,
    isCoprime_one_right, ?_, ?_, ?_, isCoprime_one_left, Nat.one_pos, ?_,
    by decide, by decide, by decide, by decide, by decide, by decide,
    ⟨2, 1, 1, by decide, by decide, by decide, by decide⟩, ?_⟩
  · rw [← prim_iff_primitive]
    show Int.gcd (-3 : ℤ) (-2 : ℤ) = 1
    decide
  · rw [← prim_iff_primitive]
    show Int.gcd (-1 : ℤ) (-2 : ℤ) = 1
    decide
  · rw [← prim_iff_primitive]
    show Int.gcd (3 : ℤ) (2 : ℤ) = 1
    decide
  · norm_num [Prod.ext_iff]
  · intro a t hEq
    rw [Prod.ext_iff] at hEq
    obtain ⟨h1, h2⟩ := hEq
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at h1 h2
    omega

/-- `hcomb` 的系数是 `ℕ`（`RecVJComb.parts_rec_vJ` 的原样形状）⟹ `ℤ` 版的不可表示性
直接把 `ℕ` 版盖住。这一条只是把射程对齐到消费者那一侧，别当独立内容。 -/
theorem nat_comb_false_of_int_comb_false {vJ p vJ1 : ℤ × ℤ}
    (h : ∀ a t : ℤ, vJ ≠ a • p + t • vJ1) :
    ∀ a t : ℕ, vJ ≠ (a : ℤ) • p + (t : ℤ) • vJ1 :=
  fun a t => h (a : ℤ) (t : ℤ)

end HcombCone


/-! ## §18. `hOrient` 的两半：符号半由 `bottom` 产出（内核），整性半没有产者

### §18.0 先记三条收到的更正

* **lane-tower-hlev 2026-09-26**：我上一封对他说「`parts_rec_vJ` 那条路封了」是**过读**。
  他的 `not_hcomb_of_chain` 把共线当**前提**，而共线在链上没有产者 ⟹ 推不出「链是共线的」。
  **收**。横截分支活着，本节就建在横截分支上。
* **集成者 2026-09-26**：撤回 `det vJ W₀ ≠ 0` 那个筛子（链上恒真、永不触发）。**收**。
  本节不用行列式判据，用的是标量那一半。
* **lane-env-refute 2026-09-26**：更正「整除免费」——`c ≥ 2` 时整除是第二半。**收**，见 §18.4；
  我的见证落在 `c = 1` ＋ `Primitive p` 上，与他的 `c = 2` 见证互不覆盖。
* **记账级别（lane-tower-hlev 2026-09-26 要求写明，`PROTOCOL §50/§51`）**：本节引用的
  lane-env-refute 那四条字段结论（`escapeW` / `shellSubStrip` / `shellEnv` / `fillCover`
  不提 `vJ`）以及他的符号筛，一律是 **②「lane X 报，我未复跑其证明体」**，不是 ③。
  下文 §18.2 那句「按他报、本处未复跑」按 ② 读。

### §18.1 ⭐⭐ `bottom` 的第 4 合取（穷尽）产出定向的**符号半**

`orient_of_bottom_exhaust`（本节）。⟹ 直接回答 env-refute 两次问的那一句：**能。**
`bottom` 推得出 `∃ d : ℤ, 0 < d ∧ W₀ nJ p vJ1 = d • vJ`。

机制：`rec_p` 把 `g₀` 沿 `p` 抬 `β` 步、再沿 `vJ1` 落 `α` 步，净漂移恰是 `W₀`
（`α = ⟪nJ,p⟫`、`β = -⟪nJ,vJ1⟫`，`⟪nJ,W₀⟫ = 0` 无条件）。于是**最底一层**里坐着一整条
`base + s • W₀`（`s : ℕ`）。穷尽合取把它们逐个逼到射线 `z₀ + k • vJ` 上，
得 `s • W₀ = (k_s − k_0) • vJ`；`s = 1` 给出 `d`，而 `L ≤ k` 这条**下界**排掉 `d < 0`。
⟹ **定向就住在 `bottom` 的 `L ≤ k` 里**，不在别处。

### §18.2 ⚠ 但这同时否掉了 `hcomb` 那条路的**独立性**

env-refute 已证四条不提 `vJ` 的字段（`escapeW` / `shellSubStrip` / `shellEnv` / `fillCover`）
碰不到 `vJ` 的定向（按他报、本处未复跑，§55）；37 条里只剩 `bottom`。而 `bottom` 一到手，
`ItemII.rec_vJ_of_bottom` 直接给 `rec_vJ`，根本不必绕 `hcomb`。

⟹ 集成者写的「两条互不依赖，谁先通谁关掉 `rec_vJ`」按本节应改读作：
**`hcomb` 那条要么经 `bottom`（那它是更长的同一条路），要么经一条字段表**外**的新字段。**

⚠ 未主张：我**没有**证「除 `bottom` 外无入口」——那是全称命题，hlev 的普查器自报是下界（§84）。
我证的是「`bottom` 够」，不是「只有 `bottom` 够」。

⛔ **本小节的粒度错，2026-09-26 更正（lane-tower-hlev 指出，收）。**`bottom` 不是原子：
`ItemII.rec_vJ_of_bottom` 的 `obtain ⟨z₀, L, hz₀, hline, -, -⟩` 只吃**合取 1 ∧ 2**（后两条当场
`-` 丢弃；我亲读了该证明体），而本节 `orient_of_bottom_exhaust` 吃的是**合取 4**。
**两者吃的是不相交的切片。**⟹ 只产出合取 4 时本节的定向点得着、`rec_vJ_of_bottom₁₂`
（`TowerHlevRecVJ.lean`，hlev 的）点不着；只产出 1 ∧ 2 时反过来。**两行互不支配**，
所以上面那句「`hcomb` 那条要么经 `bottom`（更长的同一条路）」**在这个粒度上不成立，撤回**。
可保留的收窄只有：「`hcomb` 的定向半，**目前已知**的唯一产者是 `bottom` 的合取 4」（②/③ 登记，
非否定型结论）。⚠ 合取编号请锚到 `ItemII.lean` 里 `rec_vJ_of_bottom` 的 `bottom` binder 本身，
别把序数当约定（§97）。

⛔⛔ **上面那句保留项也错了，2026-09-26 第二次更正（集成者裁决③ ＋ lane-tower-hlev 转达，收）。**
符号那半有**不经 `bottom`** 的内核产者：`EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg`
（按标识符名引），集成者报其实参是 `c.ahat_nonempty` / `c.rec_p` / `c.hswept` /
`dot_nJ_p_pos_of_parts c` / `c.ahat_halfPlane_L`，一条 `bottom` 都没有（② 我未复跑证明体）。
⟹ 「定向半的唯一产者是 `bottom` 合取 4」**撤回**，该格记 `已否`。本文件 §20 用的正是这条符号筛，
所以本文件自己的 `rec_vJ_of_det_sieve` 就是那句话的反例。**剩下真正没有产者的是整除那一侧**
（`hcomb_iff_cramer` 的 (2)(3)，lane-env-refute 的记法），以及 §22 的 `det p vJ1 ≠ 0`。
⟹ 另见 §20：`rec_vJ` 现在有一条**完全不经 `bottom`** 的通路（字段 ＋ 两条非退化 ＋ 符号筛），
所以「谁是 `rec_vJ` 的唯一入口」这个问题本身也已经过期。

### §18.3 射程

`orient_of_bottom_exhaust` **只用 `bottom` 的第 4 合取**，第 1–3 合取一个没用 ⟹ 对 `bottom`
的任何保留穷尽合取的弱化仍成立。⚠ 我用的是**抽象** `Ah`，不是 `⋃ i, hatOf A kk vl i`；
接到字段上要把 `Ah` 实例化成后者（`hhp` / `rec_p` / `ahat_nonempty` 三条字段正好对位）。
**这一步我没做**，等集成者裁要不要在 parts 上陈述。

### §18.4 整性那一半：没有产者，且与 `c = 1` / `Primitive p` 无关

`hOrient_fails_under_full_cone_stock`（本节）：同 §17 那组数据，`Primitive p` ✓、`c = 1` ✓、
开锥 ✓、**符号半 `W₀ = 4 • vJ` 成立** ✓，而 `∃ t : ℕ, α • vJ = t • W₀` 为假——因为
`d = 4` 不整除 `α = 2`。

⟹ 精确的欠账分解：`hOrient ⟺ (∃ d, 0 < d ∧ W₀ = d • vJ) ∧ d ∣ α`。
**符号半 `bottom` 给，`d ∣ α` 无人给。**

⚠ 与 env-refute 的 `orient_not_enough_without_prim_p`（`c = 2`、`p` 非本原）**不是同一格**：
我这条落在 `c = 1` ＋ `Primitive p` 上 ⟹ 两条互补，都不能删（§105）。

### §18.5 纸面：符号半是 (b)，整性半是 (c)

集成者把验收标准收紧成 `∃ t : ℕ, ⟪nJ,p⟫ • vJ = t • W₀`。分两半答：

* **符号半（`vJ` 与 `W₀` 同向）＝ (b)。** 与 §17.2 那四处（`:255` / `:424` / `:432` / `:880`）
  合成出来的开锥**逐字等价**：开锥 `vJ = λ • p + μ • vJ1`（`λ, μ > 0`）配 `⟪nJ,vJ⟫ = 0`
  ⟹ `λα = μβ` ⟹ `vJ = (μ/α) • W₀` 且 `μ/α > 0`。⟹ §17.3 那四条多出来的前提原封适用，
  一条都不是字段。
* **整性半（`d ∣ α`）＝ (c)：我没找到**（§51）。理由比「没找到」硬一层：`α = ⟪n_J,p⟫`
  里的 `p` 是链上造出来的对象（`p = -(c:ℤ) • v⃗_ℓ`，`c` 来自 `kk` 塔），**原文没有它的对应物**
  （§17.1 的 `ec{v}` 下标清单，分母 78，没有任何 `p`）⟹ 整性半不可能有原文对应句，
  它是形式化侧引入的。

⟹ 合起来：`hOrient` 作为字段，**有原文依据的只有符号半**；整性半要加就是比原文强（硬规矩 5）。
或者改走 §17.5 那条 `:506` 的半无限边路线——它一步给 `rec_vJ`，整性根本不进场。

### §18.6 未做

* 没有把 `Ah` 实例化到 `⋃ i, hatOf A kk vl i`（§18.3）。
* 没有证「除 `bottom` 外无入口」。
* 没有 `d ∣ α` 的任何产者，也**不**主张它链上为真或为假。
* ⚠ `hb_dot_nJ_W₀` 与 `EnvRefuteOrient.lean` 的 `dot_nJ_W₀` 是同一条命题的两份
  （我加 `hb_` 前缀避免 §61 撞名）。去重是集成者的（§110.2）。
-/

section BottomOrient

open Nivat.MaxEnv Nivat.HcombOrient

theorem hb_eq_of_smul_eq {vJ : ℤ × ℤ} (hne : vJ ≠ 0) {x y : ℤ}
    (he : x • vJ = y • vJ) : x = y := by
  rw [Prod.ext_iff] at he
  obtain ⟨h1, h2⟩ := he
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  have hor : vJ.1 ≠ 0 ∨ vJ.2 ≠ 0 := by
    rcases eq_or_ne vJ.1 0 with h1 | h1
    · rcases eq_or_ne vJ.2 0 with h2 | h2
      · exact absurd (Prod.ext_iff.mpr ⟨h1, h2⟩) hne
      · exact Or.inr h2
    · exact Or.inl h1
  rcases hor with h | h
  · exact mul_right_cancel₀ h h1
  · exact mul_right_cancel₀ h h2

theorem hb_mem_of_rec_nat {Ah : Set (ℤ × ℤ)} {p g : ℤ × ℤ}
    (hrecp : ∀ g ∈ Ah, g + p ∈ Ah) (hg : g ∈ Ah) : ∀ n : ℕ, g + (n : ℤ) • p ∈ Ah := by
  intro n
  induction n with
  | zero => simpa using hg
  | succ n ih =>
      have h := hrecp _ ih
      have hs : ((n + 1 : ℕ) : ℤ) • p = (n : ℤ) • p + p := by
        push_cast
        rw [add_smul, one_smul]
      rw [hs, ← add_assoc]
      exact h

/-- `⟪nJ, W₀⟫ = 0`，无条件（`W₀` 的两项高度正好抵消）。 -/
theorem hb_dot_nJ_W₀ (nJ p vJ1 : ℤ × ℤ) : dot nJ (W₀ nJ p vJ1) = 0 := by
  simp only [W₀, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **横截 ⟹ `W₀ ≠ 0`**：`det W₀ vJ1 = (-⟪nJ,vJ1⟫) · det p vJ1`。 -/
theorem hb_W₀_ne_zero_of_det {nJ p vJ1 : ℤ × ℤ} (hβ : dot nJ vJ1 < 0)
    (hdet : det p vJ1 ≠ 0) : W₀ nJ p vJ1 ≠ 0 := by
  intro h
  have hd : det (W₀ nJ p vJ1) vJ1 = (- dot nJ vJ1) * det p vJ1 := by
    simp only [W₀, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [h] at hd
  simp only [det] at hd
  have : (- dot nJ vJ1) * det p vJ1 = 0 := by
    simpa [det] using hd.symm
  rcases mul_eq_zero.mp this with h1 | h2
  · omega
  · exact hdet h2

/-- ⭐⭐ **`bottom` 的第 4 合取（穷尽）钉死 `vJ` 的定向。**

前提全是链上现货或 `bottom` 自己的一部分：`g₀ ∈ Ah`、`hhp`、`rec_p`、`0 < ⟪nJ,p⟫`、
`⟪nJ,vJ1⟫ < 0`、`vJ ≠ 0`（字段 `vJ_prim`）、`W₀ ≠ 0`（＝横截，见 `hb_W₀_ne_zero_of_det`），
以及 `bottom` 第 4 合取的 `∀ ε` 形（第 1–3 合取**不用**）。

结论：`∃ d : ℤ, 0 < d ∧ W₀ nJ p vJ1 = d • vJ`，即 **`vJ` 与 `W₀` 同向**。

机制：`rec_p` 把 `g₀` 沿 `p` 抬高、再沿 `vJ1` 落回同一高度，净漂移恰好是 `W₀`
（`β` 步 `p` ＋ `α` 步 `vJ1`，`α = ⟪nJ,p⟫`、`β = -⟪nJ,vJ1⟫`）。于是最底一层里有
一整条 `base + s • W₀`（`s : ℕ`）。穷尽合取把它们全逼到射线 `z₀ + k • vJ` 上，
而 `L ≤ k` 这条下界把 `d` 的符号钉成正——**定向就住在 `bottom` 的 `L ≤ k` 里**。 -/
theorem orient_of_bottom_exhaust {Ah : Set (ℤ × ℤ)} {nJ vJ vJ1 p g₀ : ℤ × ℤ} {cJ : ℤ}
    (hg₀ : g₀ ∈ Ah)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z)
    (hrecp : ∀ g ∈ Ah, g + p ∈ Ah)
    (hα : 0 < dot nJ p) (hβ : dot nJ vJ1 < 0)
    (hvJne : vJ ≠ 0) (hW : W₀ nJ p vJ1 ≠ 0)
    (hbot : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      ∀ z ∈ shell Ah vJ1 nJ cJ (ε + 1),
        z ∈ shell Ah vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ) :
    ∃ d : ℤ, 0 < d ∧ W₀ nJ p vJ1 = d • vJ := by
  obtain ⟨A, hA⟩ : ∃ A : ℕ, (A : ℤ) = dot nJ p := ⟨(dot nJ p).toNat, Int.toNat_of_nonneg hα.le⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ, (B : ℤ) = - dot nJ vJ1 :=
    ⟨(- dot nJ vJ1).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hBpos : 1 ≤ (B : ℤ) := by omega
  -- 选一个落在 `Ah` 之下的目标高度
  have hh₀ : cJ ≤ dot nJ g₀ := hhp _ hg₀
  obtain ⟨T, hT⟩ : ∃ T : ℕ, (T : ℤ) = dot nJ g₀ - cJ + 1 :=
    ⟨(dot nJ g₀ - cJ + 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hTB : dot nJ g₀ - (T : ℤ) * (B : ℤ) ≤ cJ - 1 := by
    have : (T : ℤ) * 1 ≤ (T : ℤ) * (B : ℤ) :=
      mul_le_mul_of_nonneg_left hBpos (by omega)
    omega
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ, (ε : ℤ) = cJ - 1 - dot nJ g₀ + (T : ℤ) * (B : ℤ) :=
    ⟨(cJ - 1 - dot nJ g₀ + (T : ℤ) * (B : ℤ)).toNat, Int.toNat_of_nonneg (by omega)⟩
  -- 最底一层里的一整条 `W₀`-射线
  set W := W₀ nJ p vJ1 with hWdef
  set base := g₀ + ((T : ℕ) : ℤ) • vJ1 with hbase
  have hWeq : W = ((B : ℤ)) • p + ((A : ℤ)) • vJ1 := by
    rw [hWdef, W₀, hA, hB]
  have hbaseDot : dot nJ base = cJ - (ε : ℤ) - 1 := by
    have hb1 : dot nJ base = dot nJ g₀ + (T : ℤ) * dot nJ vJ1 := by
      rw [hbase]
      simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    have hvj1 : dot nJ vJ1 = -(B : ℤ) := by omega
    rw [hb1, hvj1, hε]
    ring
  have hdotW : dot nJ W = 0 := by rw [hWdef]; exact hb_dot_nJ_W₀ _ _ _
  have hrayDot : ∀ s : ℕ, dot nJ (base + (s : ℤ) • W) = cJ - (ε : ℤ) - 1 := by
    intro s
    have : dot nJ (base + (s : ℤ) • W) = dot nJ base + (s : ℤ) * dot nJ W := by
      simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [this, hdotW, hbaseDot]
    ring
  have hrayMem : ∀ s : ℕ, base + (s : ℤ) • W ∈ reachSet Ah vJ1 := by
    intro s
    refine ⟨g₀ + ((B * s : ℕ) : ℤ) • p, hb_mem_of_rec_nat hrecp hg₀ (B * s), A * s + T, ?_⟩
    rw [hbase, hWeq]
    push_cast
    rw [Prod.ext_iff]
    constructor <;>
      · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
  -- `bottom` 的穷尽合取把这条射线逼到 `z₀ + k • vJ` 上
  obtain ⟨z₀, L, hexh⟩ := hbot ε
  have hkey : ∀ s : ℕ, ∃ k : ℤ, L ≤ k ∧ base + (s : ℤ) • W = z₀ + k • vJ := by
    intro s
    have hin : base + (s : ℤ) • W ∈ shell Ah vJ1 nJ cJ (ε + 1) :=
      mem_shell_succ_iff.mpr (Or.inr ⟨hrayMem s, hrayDot s⟩)
    rcases hexh _ hin with hlow | h
    · rw [shell_eq_reach_inter] at hlow
      have h2 : cJ - (ε : ℤ) ≤ dot nJ (base + (s : ℤ) • W) := hlow.2
      rw [hrayDot s] at h2
      omega
    · exact h
  obtain ⟨k0, hk0L, hk0⟩ := hkey 0
  obtain ⟨k1, hk1L, hk1⟩ := hkey 1
  have e0 : base = z₀ + k0 • vJ := by simpa using hk0
  have e1 : base + W = z₀ + k1 • vJ := by simpa using hk1
  rw [e0] at e1
  have hdW : W = (k1 - k0) • vJ := by
    rw [Prod.ext_iff] at e1 ⊢
    obtain ⟨c1, c2⟩ := e1
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      sub_mul] at c1 c2 ⊢
    exact ⟨by linear_combination c1, by linear_combination c2⟩
  have hdne : k1 - k0 ≠ 0 := by
    intro h
    rw [h, zero_smul] at hdW
    exact hW hdW
  refine ⟨k1 - k0, ?_, hdW⟩
  by_contra hd
  have hdneg : k1 - k0 ≤ -1 := by omega
  obtain ⟨S, hS⟩ : ∃ S : ℕ, (S : ℤ) = k0 - L + 1 :=
    ⟨(k0 - L + 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨kS, hkSL, hkS⟩ := hkey S
  rw [e0] at hkS
  have hsW : (S : ℤ) • W = (kS - k0) • vJ := by
    rw [Prod.ext_iff] at hkS ⊢
    obtain ⟨c1, c2⟩ := hkS
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      sub_mul] at c1 c2 ⊢
    exact ⟨by linear_combination c1, by linear_combination c2⟩
  rw [hdW, smul_smul] at hsW
  have hlin : (S : ℤ) * (k1 - k0) = kS - k0 := hb_eq_of_smul_eq hvJne hsW
  have hmul : (S : ℤ) * (k1 - k0) ≤ (S : ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left hdneg (by omega)
  have hmul2 : kS - k0 ≤ -(S : ℤ) := by
    rw [← hlin]
    simpa using hmul
  omega

/-- ⭐ **纸面定向（开锥）＋ `c = 1` ＋ `Primitive p` 都齐，`hOrient` 仍然为假。**

同 §17 的那组数据：`nJ=(0,1)`、`vl=(-3,-2)`、`c=1`、`p=(3,2)`、`vJ1=(-1,-2)`、`vJ=(1,0)`。
此时 `α = ⟪nJ,p⟫ = 2`、`β = 2`、`W₀ = 2•p + 2•vJ1 = (4,0)`，而 `α • vJ = (2,0)`
⟹ `∃ t : ℕ, α • vJ = t • W₀` 要 `t = 1/2`，为假。⟹ 缺的第二半是**整性**
（`W₀ = d • vJ` 的 `d = 4` 不整除 `α = 2`），与 `Primitive p` / `c = 1` 无关。 -/
theorem hOrient_fails_under_full_cone_stock :
    ∃ nJ vl vJ1 p vJ : ℤ × ℤ, ∃ c : ℕ,
      Primitive p ∧ Primitive vJ ∧ c = 1 ∧ p = -(c : ℤ) • vl ∧
        dot nJ vJ = 0 ∧ dot nJ vJ1 < 0 ∧ 0 < dot nJ p ∧
        (∃ k a t : ℤ, 0 < k ∧ 0 < a ∧ 0 < t ∧ k • vJ = a • p + t • vJ1) ∧
        (∃ d : ℤ, 0 < d ∧ W₀ nJ p vJ1 = d • vJ) ∧
        ¬ (∃ t : ℕ, (dot nJ p) • vJ = (t : ℤ) • W₀ nJ p vJ1) := by
  refine ⟨((0 : ℤ), (1 : ℤ)), ((-3 : ℤ), (-2 : ℤ)), ((-1 : ℤ), (-2 : ℤ)),
    ((3 : ℤ), (2 : ℤ)), ((1 : ℤ), (0 : ℤ)), 1, ?_, isCoprime_one_left, rfl, ?_,
    by decide, by decide, by decide,
    ⟨2, 1, 1, by decide, by decide, by decide, by decide⟩,
    ⟨4, by decide, by decide⟩, ?_⟩
  · rw [← prim_iff_primitive]
    show Int.gcd (3 : ℤ) (2 : ℤ) = 1
    decide
  · norm_num [Prod.ext_iff]
  · rintro ⟨t, ht⟩
    rw [Prod.ext_iff] at ht
    obtain ⟨h1, h2⟩ := ht
    simp only [W₀, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at h1 h2
    omega

end BottomOrient



section WRay

open Nivat.MaxEnv Nivat.HcombOrient

/-!
## §19 `W₀` 方向的射线是**字段现货**；`rec_vJ` 只欠「同向」，**不欠整除**

§18 把 `bottom` 的合取 4 压成了 `∃ d, 0 < d ∧ W₀ nJ p vJ1 = d • vJ`（`orient_of_bottom_exhaust`），
并给出分解 `hOrient ⟺ 同向 ∧ d ∣ ⟪nJ,p⟫`。lane-env-refute 据此把验收标准改成「定向 ＋ 整除」
（或「定向 ＋ `c = 1``）。**本节证明整除那一半对 `rec_vJ` 是多余的。**

### §19.1 机制：`W₀` 的射线不用买

`W₀ = β•p + α•vJ1`（`α = ⟪nJ,p⟫`、`β = −⟪nJ,vJ1⟫`）满足无条件恒等式 `⟪nJ,W₀⟫ = 0`
（`hb_dot_nJ_W₀`，§18）。⟹ 沿 `W₀` 走**高度不变**。于是

    g₀ + s•W₀ = (g₀ + (s·β)•p) + (s·α)•vJ1 ,

左括号由 `rec_p` 反复施用留在 `R` 内（`hb_mem_of_rec_nat`），右边那 `s·α` 步 `vJ1` 由
`hswept`（`MaxEnv.SweptClosed`，其侧条件恰是「落点高度 ≥ cJ」）放行——而落点高度就是
`⟪nJ,g₀⟫`，由 `hhp` 本身 `≥ cJ`。⟹ `ray_W₀_of_fields`：**`R` 含整条 `g₀ + ℕ•W₀`**，
输入只有 `ahat_nonempty` / `hhp` / `rec_p` / `hswept` / `dot_nJ_p` / `hsweep` 六个字段，
**不经 `bottom`、不经原文、不选旋向**（`W₀` 是算出来的，不是挑出来的）。

原文对应：`:506`「`Â_∞` 有两条半无限边，一条平行 `ℓ`、另一条平行 `ℓ_J`」的**第一半**就是
`rec_p`（`p = −c·v⃗_ℓ`）。本节是说：第一半 ＋ 扫掠字段已经免费给出**第三条**射线（方向 `W₀`），
它一般既不平行 `ℓ` 也不平行 `ℓ_J`。

### §19.2 ⭐ 关键：recession cone 是**实**锥，所以整除消失

`recCone R = {w : ℝ×ℝ | ∀ x ∈ convHullOf R, x + w ∈ convHullOf R}`
（`Nivat.recCone`，`Section8/HalfPlane.lean:204`）对**非负实数**数乘封闭
（`Nivat.smul_mem_recCone`，`:336`）。⟹ 一旦 `toReal W₀ ∈ recCone R`，任何
`toReal vJ = λ • toReal W₀`（`λ ≥ 0` **实数**）都给出 `toReal vJ ∈ recCone R`，
再由 `Nivat.add_mem_of_mem_recCone`（`Section8/RegionUpgrade.lean:138`）得 `rec_vJ`。
这就是 `rec_vJ_of_real_dir`。

⟹ 两条推论，都**不带整除前提**：
* `rec_vJ_of_W₀_pos_multiple`：`W₀ = d • vJ`、`0 < d`（λ = 1/d）——即 §18 的输出**逐字**。
* `rec_vJ_of_smul_eq`：`⟪nJ,p⟫ • vJ = (t:ℕ) • W₀`、`0 < ⟪nJ,p⟫`（λ = t/α）——即
  lane-env-refute 的 `hOrient` 的**第一个合取**，签名里**没有** `⟪nJ,p⟫ ∣ t·(−⟪nJ,vJ1⟫)`。

⟹ **验收标准回落到「只要定向」**：`EnvRefuteOrient.rec_vJ_of_hOrient` 的第二个合取对 `rec_vJ`
不是必需的。⚠ 我没有说那个合取为假，也没有说它在别处没用；我说的是本条通路不吃它。

### §19.3 §113：反向差额（「B 比 A 多什么」）

A ＝ 本节前提（`∃ λ ≥ 0, toReal vJ = λ • toReal W₀`），B ＝ `hOrient`（ℕ-标量 ＋ 整除）。
* B ⟹ A：`rec_vJ_of_smul_eq` 的签名即是（只用第一合取）。
* A ⇏ B：§18 的 `hOrient_fails_under_full_cone_stock`（同一份数据：`nJ=(0,1)`、`vl=(-3,-2)`、
  `vJ1=(-1,-2)`、`p=(3,2)`、`vJ=(1,0)`、`c=1`）上 `W₀ = 4 • vJ`（`d = 4 > 0`，A 成立）而
  `¬∃ t:ℕ, 2 • vJ = t • W₀`（B 假，因 `4 ∤ 2`）。⟹ 该数据上本节适用、`rec_vJ_of_hOrient` 不适用。

### §19.4 射程（自限，勿放大）

* ⛔ **没有**证出「同向」本身。`∃ d > 0, W₀ = d • vJ` 仍是欠账；§18 只从 `bottom` 的合取 4
  推出它，**不经 `bottom` 的产者我没有**。本节把欠账从「同向 ＋ 整除」减到「同向」，不是减到零。
* 本节对抽象 `R` 陈述，**未**代入 `⋃ i, hatOf A kk vl i`；代入时 `hg₀ = ahat_nonempty`、
  `hhp`、`hrecp = rec_p`、`hswept` 都是字段，`hconv` 链上由 `ColleReg.region_latticeConvex`
  给（我不能 import `RegionSteps`，故留作前提）。
* `hβ` 我写成 `≤ 0` 而非字段的 `< 0`（`hsweep`）：弱化前提，链上照样喂得进。
* ⚠ **撤回 §17.5 的一句**：那里写「`IsLatticeConvexRegion` 有两个定义（§97）」。**错**。
  `declscan.py IsLatticeConvexRegion` 实跑 `RAW=2 REAL=1`：唯一的 `def` 是
  `Nivat.IsLatticeConvexRegion`（`Section8/HalfPlane.lean`，标识符名为准），另一处命中是
  `AEnv.lean` docstring 里的**逐字引文**、不是定义。与 lane-tower-hlev 的内核互换 `example`
  结论一致。集成者问的「`latticeConvex_of_parts` 产的是哪一个」⟹ **只有一个，无歧义**。
-/

/-- `⟪n, x + k•w⟫ = ⟪n,x⟫ + k·⟪n,w⟫`。纯双线性展开，无前提。 -/
theorem hb_dot_add_zsmul (n x w : ℤ × ℤ) (k : ℤ) :
    dot n (x + k • w) = dot n x + k * dot n w := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **§19.1 `W₀` 射线是字段现货。**  `R` 含整条 `g₀ + ℕ•W₀`，输入只有
「非空 ＋ `hhp` ＋ `rec_p` ＋ `hswept` ＋ 两个符号」，**不经 `bottom`**。
原文锚：`b3_colle2.txt:506` 的第一条半无限边（平行 `ℓ`）＝ `hrecp`；`:440` 的 `+t·v⃗_{ℓ_{J−1}}`
＝ `hswept` 的步长。⚠ 方向 `W₀` 是**算出来的**（`HcombOrient.W₀`），不涉及任何旋向判定，
故不碰第 179 轮红线。 -/
theorem ray_W₀_of_fields {R : Set (ℤ × ℤ)} {nJ p vJ1 g₀ : ℤ × ℤ} {cJ : ℤ}
    (hg₀ : g₀ ∈ R)
    (hhp : ∀ z ∈ R, cJ ≤ dot nJ z)
    (hrecp : ∀ g ∈ R, g + p ∈ R)
    (hswept : SweptClosed R vJ1 nJ cJ)
    (hα : 0 ≤ dot nJ p) (hβ : dot nJ vJ1 ≤ 0) :
    ∀ s : ℕ, g₀ + (s : ℤ) • W₀ nJ p vJ1 ∈ R := by
  obtain ⟨A, hA⟩ : ∃ A : ℕ, (A : ℤ) = dot nJ p := ⟨(dot nJ p).toNat, Int.toNat_of_nonneg hα⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ, (B : ℤ) = - dot nJ vJ1 :=
    ⟨(- dot nJ vJ1).toNat, Int.toNat_of_nonneg (by omega)⟩
  intro s
  have hg₁ : g₀ + ((B * s : ℕ) : ℤ) • p ∈ R := hb_mem_of_rec_nat hrecp hg₀ (B * s)
  have hsplit : g₀ + (s : ℤ) • W₀ nJ p vJ1
      = (g₀ + ((B * s : ℕ) : ℤ) • p) + ((A * s : ℕ) : ℤ) • vJ1 := by
    rw [W₀, ← hA, ← hB]
    push_cast
    rw [Prod.ext_iff]
    constructor <;>
      (simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
  rw [hsplit]
  refine hswept _ hg₁ (A * s) ?_
  rw [← hsplit, hb_dot_add_zsmul, hb_dot_nJ_W₀]
  simpa using hhp g₀ hg₀

/-- **§19.2 `toReal W₀ ∈ recCone R`.**  `ray_W₀_of_fields` ＋
`Nivat.toReal_mem_recCone_of_nat_ray`（`Section8/RegionUpgrade.lean`，按标识符名引）。 -/
theorem recCone_W₀_of_fields {R : Set (ℤ × ℤ)} {nJ p vJ1 g₀ : ℤ × ℤ} {cJ : ℤ}
    (hg₀ : g₀ ∈ R)
    (hhp : ∀ z ∈ R, cJ ≤ dot nJ z)
    (hrecp : ∀ g ∈ R, g + p ∈ R)
    (hswept : SweptClosed R vJ1 nJ cJ)
    (hα : 0 ≤ dot nJ p) (hβ : dot nJ vJ1 ≤ 0) :
    toReal (W₀ nJ p vJ1) ∈ recCone R :=
  toReal_mem_recCone_of_nat_ray (ray_W₀_of_fields hg₀ hhp hrecp hswept hα hβ)

/-- **⭐ §19.2 主条：`rec_vJ` 只需 `vJ` 与 `W₀` 的一个非负实数比。**
`recCone` 对非负实数数乘封闭（`Nivat.smul_mem_recCone`），所以「同向」用不着是整数关系，
更用不着整除。⚠ `lam` 是 `ℝ`，这正是整除消失的地方。 -/
theorem rec_vJ_of_real_dir {R : Set (ℤ × ℤ)} {nJ p vJ1 vJ g₀ : ℤ × ℤ} {cJ : ℤ} {lam : ℝ}
    (hconv : IsLatticeConvexRegion R)
    (hg₀ : g₀ ∈ R)
    (hhp : ∀ z ∈ R, cJ ≤ dot nJ z)
    (hrecp : ∀ g ∈ R, g + p ∈ R)
    (hswept : SweptClosed R vJ1 nJ cJ)
    (hα : 0 ≤ dot nJ p) (hβ : dot nJ vJ1 ≤ 0)
    (hlam : 0 ≤ lam) (hdir : toReal vJ = lam • toReal (W₀ nJ p vJ1)) :
    ∀ g ∈ R, g + vJ ∈ R := by
  have hW : toReal (W₀ nJ p vJ1) ∈ recCone R :=
    recCone_W₀_of_fields hg₀ hhp hrecp hswept hα hβ
  have hv : toReal vJ ∈ recCone R := by
    rw [hdir]; exact smul_mem_recCone hlam hW
  exact fun g hg => add_mem_of_mem_recCone hconv hv hg

/-- **§19.2 推论 1：§18 的输出逐字接进来。**  `orient_of_bottom_exhaust` 给的是
`∃ d, 0 < d ∧ W₀ nJ p vJ1 = d • vJ`；这里 `λ = 1/d`。⛔ 注意 `d` **不必**整除 `⟪nJ,p⟫`。 -/
theorem rec_vJ_of_W₀_pos_multiple {R : Set (ℤ × ℤ)} {nJ p vJ1 vJ g₀ : ℤ × ℤ} {cJ d : ℤ}
    (hconv : IsLatticeConvexRegion R)
    (hg₀ : g₀ ∈ R)
    (hhp : ∀ z ∈ R, cJ ≤ dot nJ z)
    (hrecp : ∀ g ∈ R, g + p ∈ R)
    (hswept : SweptClosed R vJ1 nJ cJ)
    (hα : 0 ≤ dot nJ p) (hβ : dot nJ vJ1 ≤ 0)
    (hd : 0 < d) (hW : W₀ nJ p vJ1 = d • vJ) :
    ∀ g ∈ R, g + vJ ∈ R := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine rec_vJ_of_real_dir (lam := ((d : ℝ))⁻¹) hconv hg₀ hhp hrecp hswept hα hβ
    (le_of_lt (inv_pos.mpr hdR)) ?_
  rw [hW, toReal_zsmul, smul_smul, inv_mul_cancel₀ (ne_of_gt hdR), one_smul]

/-- **⭐ §19.2 推论 2：`hOrient` 的第一个合取单独就够。**
前提逐字是 lane-env-refute 的 `hOrient` 的前半（`⟪nJ,p⟫ • vJ = (t:ℕ) • W₀`），
签名里**没有** `⟪nJ,p⟫ ∣ t·(−⟪nJ,vJ1⟫)`。⟹ 纸面那一步只需定到「同向」一句。 -/
theorem rec_vJ_of_smul_eq {R : Set (ℤ × ℤ)} {nJ p vJ1 vJ g₀ : ℤ × ℤ} {cJ : ℤ} {t : ℕ}
    (hconv : IsLatticeConvexRegion R)
    (hg₀ : g₀ ∈ R)
    (hhp : ∀ z ∈ R, cJ ≤ dot nJ z)
    (hrecp : ∀ g ∈ R, g + p ∈ R)
    (hswept : SweptClosed R vJ1 nJ cJ)
    (hα : 0 < dot nJ p) (hβ : dot nJ vJ1 ≤ 0)
    (hray : (dot nJ p) • vJ = (t : ℤ) • W₀ nJ p vJ1) :
    ∀ g ∈ R, g + vJ ∈ R := by
  have hαR : (0 : ℝ) < ((dot nJ p : ℤ) : ℝ) := by exact_mod_cast hα
  have hreal : ((dot nJ p : ℤ) : ℝ) • toReal vJ = ((t : ℤ) : ℝ) • toReal (W₀ nJ p vJ1) := by
    rw [← toReal_zsmul, ← toReal_zsmul, hray]
  refine rec_vJ_of_real_dir (lam := ((dot nJ p : ℤ) : ℝ)⁻¹ * ((t : ℤ) : ℝ)) hconv hg₀ hhp hrecp
    hswept hα.le hβ (by positivity) ?_
  rw [mul_smul, ← hreal, smul_smul, inv_mul_cancel₀ (ne_of_gt hαR), one_smul]

end WRay



section ScaleSieve

open Nivat.MaxEnv Nivat.HcombOrient

/-!
## §20 `rec_vJ` 在**非退化格**上是字段现货：整除不必要，`s > 0` 由符号筛推出

§19 证了 `rec_vJ ⟸ ∃ d>0, W₀ = d•vJ`（整除已消）。本节把这最后一句也接上：
lane-env-refute §19 的链上符号筛 `0 ≤ det p vJ * det p vJ1`（`EnvRefuteOrient`，按标识符名引，
他们报 `ahat_nonempty`/`rec_p`/`hswept`/`ahat_halfPlane_L`/`dot_nJ_p` 五项、不经 `bottom`；
⚠ ② **我未复跑**）＋ 两条非退化 `det p vJ ≠ 0`、`det p vJ1 ≠ 0` 已经蕴含 `0 < s`。

### §20.1 算式（三行，无前提以外的输入）

`W₀ = β•p + α•vJ1` ⟹ **无条件**恒等式 `det p W₀ = α · det p vJ1`（`hb_det_p_W₀`）。
`vJ_prim` ＋ `⟪nJ,vJ⟫ = 0` ＋ `⟪nJ,W₀⟫ = 0` ⟹ `W₀ = s • vJ`（`hb_scale_of_perp`，
经 `LE2.det_eq_zero_of_dot_eq_zero` ＋ `eq_zsmul_of_det_eq_zero`），于是 `det p W₀ = s · det p vJ`。
两式相等再乘 `det p vJ`：

    s · (det p vJ)² = α · (det p vJ · det p vJ1)

右边 `α > 0`、括号 `> 0`（筛子给 `≥ 0`，两条非退化给 `≠ 0`）⟹ **`s > 0`**（`hb_scale_pos`）。

### §20.2 ⟹ `rec_vJ_of_det_sieve`

把 `hb_scale_pos` 喂进 §19 的 `rec_vJ_of_W₀_pos_multiple`，得

    rec_vJ ⟸ 字段 ＋ (det p vJ ≠ 0) ＋ (det p vJ1 ≠ 0) ＋ (0 ≤ det p vJ * det p vJ1)

**签名里没有任何整除。** 逐条对字段：`hg₀ = ahat_nonempty`、`hhp`、`hrecp = rec_p`、
`hswept`、`hnJ ⟸ nJ_prim`、`hvJprim = vJ_prim`、`hvJperp = F.dot_nJ_vJ`、
`hα ⟸ dot_nJ_p_pos_of_parts`、`hβ ⟸ hsweep`；`hconv` 链上由 `ColleReg.region_latticeConvex` 给
（我不能 import `RegionSteps`，留作前提）。⟹ **只剩两条非退化是欠账。**

### §20.3 与 Cramer 形的关系（§113 反向差额）

lane-env-refute `hcomb_iff_cramer` 把 `hcomb` 刻画成两条整除；集成者据此把纸面标的换成
「相邻边 `det` 的整除／单模」。本节说：**那两条整除对 `rec_vJ` 都不必要**，因为
`recCone` 是实锥（§19.2）。内核见证 `hb_stock_passes_sieve`：§17/§18 那组数据上

    det p vJ = -2 ≠ 0,  det p vJ1 = -4 ≠ 0,  乘积 8 ≥ 0（**过**符号筛），  但 -4 ∤ -2

⟹ 该组数据**不被** env-refute §19 的链外判据排除（与集成者那组不同），`hcomb`/`hOrient` 在其上为假，
而 §20 的 `rec_vJ_of_det_sieve` 在其上**全部前提成立**。⟹ 「整除是 `rec_vJ` 的瓶颈」在这组数据上被证伪。
⚠ 我**没有**说 `hcomb_iff_cramer` 错——它刻画的是 `hcomb`，`hcomb` 确实要整除；我说的是
`rec_vJ` 不用经过 `hcomb`。

### §20.4 射程（自限，勿放大）

* ⛔ `det p vJ ≠ 0` / `det p vJ1 ≠ 0` **我没有产者**。后者为 0 即共线格
  （`GcdCollapse.det_p_vJ1_eq_zero`），那一格本节不覆盖。前者为 0 即 `vJ ∥ p`，本节也不覆盖。
  ⟹ 本节的结论是「**非退化格上** `rec_vJ` 已闭」，不是「`rec_vJ` 已闭」。

  ⛔ **2026-09-26 更正：上面那句「两条都没有产者」错了一半。**`det p vJ ≠ 0` 是本条**自己
  已有的 binder 的代数推论**，根本不该出现在签名里（lane-env-refute 2026-09-26 指出，我复核并
  独立重证，见 §23）：`hvJprim` 给 `vJ ≠ 0`、`hvJperp` 给 `⟪nJ,vJ⟫ = 0`、`hα` 给 `⟪nJ,p⟫ ≠ 0`，
  三条一起就逼出 `det p vJ ≠ 0`。⟹ **真正的欠账只有一条：`det p vJ1 ≠ 0`**，而它按 §22
  逐字等价于原文的 `J > ι+1`，原文**不保证**。`rec_vJ_of_det_sieve` 的签名按集成者裁决②
  不动（`hdpv` 留成冗余 binder），去掉它的形是 §23 的 `rec_vJ_of_det_sieve_slim`。
* ⚠ ② 符号筛 `0 ≤ det p vJ * det p vJ1` 是 lane-env-refute 报的链上现货，**我未复跑**其证明体；
  本节把它当**前提**收在签名里，所以即便那条被撤，本节仍是真命题，只是没有产者。
* 本节对抽象 `R` 陈述，未代入 `⋃ i, hatOf A kk vl i`（§21 补上了这一步）。
-/

/-- `⟪nJ,·⟫`-零向量与 `W₀` 平行：`vJ` 本原 ＋ 两者都 ⊥ `nJ` ⟹ `W₀ = s • vJ`。
`LE2.det_eq_zero_of_dot_eq_zero` ＋ `Nivat.eq_zsmul_of_det_eq_zero`（均按标识符名引）。 -/
theorem hb_scale_of_perp {nJ vJ : ℤ × ℤ} (p vJ1 : ℤ × ℤ)
    (hnJ : nJ ≠ 0) (hvJprim : Primitive vJ) (hvJperp : dot nJ vJ = 0) :
    ∃ s : ℤ, W₀ nJ p vJ1 = s • vJ :=
  eq_zsmul_of_det_eq_zero hvJprim
    (det_eq_zero_of_dot_eq_zero hnJ hvJperp (hb_dot_nJ_W₀ nJ p vJ1))

/-- **无条件恒等式** `det p W₀ = ⟪nJ,p⟫ · det p vJ1`（`det p p = 0` 把 `β` 那一项吃掉）。 -/
theorem hb_det_p_W₀ (nJ p vJ1 : ℤ × ℤ) : det p (W₀ nJ p vJ1) = dot nJ p * det p vJ1 := by
  simp only [W₀, det, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **⭐ §20.1：符号筛 ＋ 两条非退化 ⟹ `0 < s`。**  见 §20.1 的三行算式。 -/
theorem hb_scale_pos {nJ p vJ1 vJ : ℤ × ℤ} {s : ℤ}
    (hW : W₀ nJ p vJ1 = s • vJ)
    (hα : 0 < dot nJ p)
    (hdpv : det p vJ ≠ 0) (hdpv1 : det p vJ1 ≠ 0)
    (hsieve : 0 ≤ det p vJ * det p vJ1) :
    0 < s := by
  have h2 : det p (W₀ nJ p vJ1) = s * det p vJ := by
    rw [hW]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have key : s * det p vJ = dot nJ p * det p vJ1 := by
    rw [← h2, hb_det_p_W₀]
  have key2 : s * (det p vJ * det p vJ) = dot nJ p * (det p vJ * det p vJ1) := by
    linear_combination (det p vJ) * key
  have hsq : 0 < det p vJ * det p vJ := mul_self_pos.mpr hdpv
  have hprod : 0 < det p vJ * det p vJ1 :=
    lt_of_le_of_ne hsieve (Ne.symm (mul_ne_zero hdpv hdpv1))
  by_contra hcon
  have hs : s ≤ 0 := not_lt.mp hcon
  nlinarith [key2, hsq, hprod, hα, hs]

/-- **⭐⭐ §20.2 主条：非退化格上 `rec_vJ` 只吃字段 ＋ 符号筛，整除一条不要。**
逐条对字段见 §20.2；欠账只剩 `det p vJ ≠ 0` / `det p vJ1 ≠ 0` 两条非退化（§20.4）。

⚠⚠ **射程：本条的前件只在「横截格」可满足**（lane-tower-hlev 2026-09-26 要求补此句，收）。
`GcdCollapse` 的 `not_det_unit`（按标识符名引）那节散文写「`det p vJ1` 在链上恒为 `0`」，
**但那条定理把共线 `hm : vJ1 = m • vl` 写成假设、不是结论**，射程只到**链上共线格**；
`ChainPartsFeed.lean` 的 `vJ1` 字段 docstring 逐字写着「凡以共线为前提的结论（`GcdCollapse` 全族…）
射程都是『链上共线格』，不是『链上』」。⟹ 本条**没有**被那句散文判死。
共线格里本条前件**不可满足**（lane-leafa-shell `W₀_eq_det_smul_dir_lside`：`W₀ = (det p vJ1) • dir nJ`，
故 `det p vJ1 = 0 ⟹ W₀ = 0`；② 我未复跑），那一格要换产者，见 §22。

⚠ **同族另一条，集成者 2026-09-26 裁决②「两条都留、不许删」**：
`RecVJTransverse.rec_vJ_of_parts_transverse`（按标识符名引）直接代在 `ChainDataGeomParts` 上，
只要一条 `hdet : det p vJ1 ≠ 0`；本条在抽象 `R` 层、要两条横截 ＋ `hsieve`。两条互不替代。 -/
theorem rec_vJ_of_det_sieve {R : Set (ℤ × ℤ)} {nJ p vJ1 vJ g₀ : ℤ × ℤ} {cJ : ℤ}
    (hconv : IsLatticeConvexRegion R)
    (hg₀ : g₀ ∈ R)
    (hhp : ∀ z ∈ R, cJ ≤ dot nJ z)
    (hrecp : ∀ g ∈ R, g + p ∈ R)
    (hswept : SweptClosed R vJ1 nJ cJ)
    (hnJ : nJ ≠ 0) (hvJprim : Primitive vJ) (hvJperp : dot nJ vJ = 0)
    (hα : 0 < dot nJ p) (hβ : dot nJ vJ1 ≤ 0)
    (hdpv : det p vJ ≠ 0) (hdpv1 : det p vJ1 ≠ 0)
    (hsieve : 0 ≤ det p vJ * det p vJ1) :
    ∀ g ∈ R, g + vJ ∈ R := by
  obtain ⟨s, hW⟩ := hb_scale_of_perp p vJ1 hnJ hvJprim hvJperp
  exact rec_vJ_of_W₀_pos_multiple hconv hg₀ hhp hrecp hswept hα.le hβ
    (hb_scale_pos hW hα hdpv hdpv1 hsieve) hW

/-- **§20.3 见证**：§17/§18 那组数据 **过**符号筛（乘积 `8 ≥ 0`、两条非退化都 `≠ 0`）
而**卡**整除（`-4 ∤ -2`）。⟹ `rec_vJ_of_det_sieve` 在其上可用、Cramer 整除形不可用。 -/
theorem hb_stock_passes_sieve :
    (0 : ℤ) ≤ det ((3 : ℤ), (2 : ℤ)) ((1 : ℤ), (0 : ℤ))
        * det ((3 : ℤ), (2 : ℤ)) ((-1 : ℤ), (-2 : ℤ))
      ∧ det ((3 : ℤ), (2 : ℤ)) ((1 : ℤ), (0 : ℤ)) ≠ 0
      ∧ det ((3 : ℤ), (2 : ℤ)) ((-1 : ℤ), (-2 : ℤ)) ≠ 0
      ∧ ¬ (det ((3 : ℤ), (2 : ℤ)) ((-1 : ℤ), (-2 : ℤ))
            ∣ det ((3 : ℤ), (2 : ℤ)) ((1 : ℤ), (0 : ℤ))) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

end ScaleSieve


section PartsInstance

open Nivat.MaxEnv Nivat.HcombOrient Nivat.Colle35 Nivat.ChainAsm Nivat.ChainAsm.Aparts

/-!
## §21 把 §19/§20 代进链上对象：`R := ⋃ i, hatOf A kk vl i`，并把 hlev 的 `hsign` 兑现

§19/§20 都对抽象 `R` 陈述（§20.4 明写「未代入」）。本节补上那一步：`R` 取成
`ChainDataGeomParts` 的帽子并集，八条前提里有六条是字段。同时把 lane-tower-hlev
2026-09-26 那条收窄（「欠的精确地只剩整数不等号 `0 ≤ dot W₀ vJ`」）与本文件 §20 的
`0 < s` 对齐：两者**是同一笔账**，`hb_sign_iff_scale_nonneg` 把等价性钉成内核。

### §21.1 逐条对字段（`ChainPartsFeed.lean` 的 `ChainDataGeomParts`，按标识符名引）

| `rec_vJ_of_det_sieve` 的 binder | 来源 |
|---|---|
| `hg₀ : g₀ ∈ R` | 字段 `ahat_nonempty` |
| `hhp : ∀ z ∈ R, cJ ≤ dot nJ z` | 字段 `hhp`（逐层版）经 `hb_union_halfPlane_of_parts` |
| `hrecp : ∀ g ∈ R, g + p ∈ R` | 字段 `rec_p` |
| `hswept : SweptClosed R vJ1 nJ cJ` | 字段 `hswept` |
| `hnJ : nJ ≠ 0` | 字段 `nJ_prim` 经 `Primitive.ne_zero`（`Defs/Config.lean`，按标识符名引） |
| `hvJprim : Primitive vJ` | 字段 `vJ_prim` |
| `hvJperp : dot nJ vJ = 0` | 字段 `F` 的 `dot_nJ_vJ`（`FaceBlock`，`ANormal.lean`，按标识符名引） |
| `hβ : dot nJ vJ1 ≤ 0` | 字段 `hsweep`（严格 `< 0`）取 `.le` |

留在 binder 里的只有四条，且**四条都不是整除**：

* `hconv : IsLatticeConvexRegion (⋃ i, hatOf A kk vl i)`；
* `hα : 0 < dot nJ p`；
* `hdpv : det p vJ ≠ 0`、`hdpv1 : det p vJ1 ≠ 0`；
* `hsieve : 0 ≤ det p vJ * det p vJ1`。

⚠ **它们的产者状态，逐条、分级（`PROTOCOL §50/§51/§55`）**：

1. `hα`：字段只给 `dot_nJ_p : dot nJ p ≠ 0`（**不等于零**，不是正）。lane-env-refute 报
   `dot_nJ_p_pos_of_parts`（`EnvRefuteOrient.lean`，按标识符名引）把它抬成正。
   **② 我未复跑，也未 import**（`EnvRefuteOrient` 本轮被 hlev 的 `contenthash.py` 报 DRIFT，
   我不在漂移模块上取读数），故此处保留为 binder，不假装已闭。接不接由集成者裁。
2. `hsieve`：lane-env-refute 报 `det_p_vJ_mul_det_p_vJ1_nonneg` 在链上、不经 `bottom`。
   **② 同上，我未复跑。**
3. `hdpv` / `hdpv1`：⛔ **我没有产者，别人也没报过产者。**`hdpv1` 在共线格恰为零
   （`GcdCollapse` 的 `det_p_vJ1_eq_zero`，按标识符名引），故本条结论准确说是
   「**横截格上** `rec_vJ` 已闭」，不是无条件闭。
4. `hconv`：⚠ lane-env-refute 2026-09-26 报「树里没有『帽子并集是 `IsLatticeConvexRegion`』
   的现成实例，`rec_p_free` 的证明体里只有逐个 `A i` 的凸性」。**② 我未复跑**；
   本节把 `hconv` 老实留成 binder。

### §21.2 与 hlev 的 `rec_vJ_of_ray_W` 的关系（`PROTOCOL §113`，两向差额都打印）

hlev 2026-09-26 交付 `HlevPerpSign.rec_vJ_of_ray_W`（`tmp/wip/hlev-perp-sign.lean`，他们报
EXIT=0、五条白名单；**② 我未复跑**），其欠账写成整数不等号 `hsign : 0 ≤ dot W vJ`。

* **他们比我多什么**：`hsign` 是对 `dot` 的直接假设，不需要 `det p vJ ≠ 0`、
  `det p vJ1 ≠ 0`、`0 ≤ det p vJ * det p vJ1` 三条中的任何一条，也不需要 `0 < dot nJ p`。
  他们那条的 binder 里没有 `p` 这个字。
* **我比他们多什么**：§20 的 `hsieve` 是 lane-env-refute 报的**链上现货**，`hsign` 不是；
  换言之我用三条可能已在链上的条件换掉一条目前没有产者的条件。
* **两者是同一笔账**：`hb_sign_iff_scale_nonneg` 证 `vJ ≠ 0` ＋ `W = s • vJ` ⟹
  `0 ≤ dot W vJ ↔ 0 ≤ s`。而 `W₀ = s • vJ` 的存在性是 §20 的 `hb_scale_of_perp`（白送，
  hlev 的「共线是白送的」与此一致，我们用的是同一条 `LE2.det_eq_zero_of_dot_eq_zero`）。
  ⟹ hlev 的 `hsign` 与我 §20 的 `0 < s` 之差只有 `s = 0` 一点，而 `s = 0` 被
  `hb_W₀_ne_zero_of_det`（本文件，`hβ` 严格 ＋ `det p vJ1 ≠ 0`）排除。
* ⟹ `hb_dot_W₀_vJ_nonneg_of_sieve` 就是**用我的筛子兑现他们的 `hsign`**：同一组前提下
  两条路线都通，不是二选一。

### §21.3 hlev 的两条射程声明，我照收不外推

1. 他们的 `hsign_not_implied` 是「限定非空」见证（`PROTOCOL §71`），**不是**反例：
   它只说 `hsign` 不是多余 binder，不说「`0 ≤ dot W₀ vJ` 推不出来」。
2. 他们明写**没有**证 `0 ≤ dot W₀ vJ` 在链上成立或不成立 ⟹ 该格是 `未定`，不是 `已否`
   （`PROTOCOL §119`：三值，`不可判` 不并进绿）。本节不改这个判定：§20/§21 给的是
   **一条充分路径**（横截 ＋ 符号筛），不是「该不等号已在链上成立」。

### §21.4 射程（`PROTOCOL §41`）

* 本节**没有**证 `hconv`、`hα`、`hdpv`、`hdpv1`、`hsieve` 中任何一条。
* 本节**没有**碰 `bottom` 的任何合取；`rec_vJ_of_parts_det_sieve` 的证明体里没有 `bottom`。
* 本节**没有**主张「`rec_vJ` 已在链上闭」。准确说法：**横截格上，`rec_vJ` 归约到
  `hconv` ＋ `hα` ＋ `hsieve` 三条，其中后两条 lane-env-refute 报为链上现货（②）。**
* 本节**没有**碰方向约定（哪条半无限边是 `ℓ_J`、`+vJ` 还是 `−vJ`）：`s` 的符号是**算出来的**，
  不是选出来的 ⟹ 不触 179 号红线。
* ⛔ 未 import `EnvRefuteOrient`（本轮 DRIFT），故上面凡标 ② 者一律不作为本文件的读数。
-/

variable {α : Type*}

/-- **§21.1 桥**：字段 `hhp` 是逐层的集合包含，`rec_vJ_of_det_sieve` 要的是并集上的逐点不等号。
`halfPlaneGE n c = {z | c ≤ dot n z}`（`LatticeEdges.lean`，按标识符名引），故只差一个 `mem_iUnion`。 -/
theorem hb_union_halfPlane_of_parts {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen) :
    ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i, c.cJ ≤ dot c.nJ z := by
  intro z hz
  rw [Set.mem_iUnion] at hz
  obtain ⟨i, hi⟩ := hz
  exact c.hhp i hi

/-- ⭐⭐ **§21 主条：`rec_vJ` 在链上对象的横截格上，只剩四条 binder、零条整除。**
八条前提落到字段的对照表见 §21.1；四条剩余 binder 的产者状态（含 ② 分级）见 §21.1 的注。 -/
theorem rec_vJ_of_parts_det_sieve {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hconv : IsLatticeConvexRegion (⋃ i, hatOf c.A c.kk vl i))
    (hα : 0 < dot c.nJ p)
    (hdpv : det p c.vJ ≠ 0) (hdpv1 : det p c.vJ1 ≠ 0)
    (hsieve : 0 ≤ det p c.vJ * det p c.vJ1) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i := by
  obtain ⟨g₀, hg₀⟩ := c.ahat_nonempty
  exact rec_vJ_of_det_sieve hconv hg₀ (hb_union_halfPlane_of_parts c) c.rec_p c.hswept
    c.nJ_prim.ne_zero c.vJ_prim c.F.dot_nJ_vJ hα c.hsweep.le hdpv hdpv1 hsieve

/-- `dot (s • v) v = s * dot v v`。§21.2 的算式本体。 -/
theorem hb_dot_smul_left {v W : ℤ × ℤ} {s : ℤ} (hW : W = s • v) :
    dot W v = s * dot v v := by
  subst hW
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- `v ≠ 0 ⟹ 0 < ⟪v,v⟫`（整数版）。 -/
theorem hb_dot_self_pos {v : ℤ × ℤ} (hv : v ≠ 0) : 0 < dot v v := by
  rcases eq_or_ne v.1 0 with h1 | h1
  · rcases eq_or_ne v.2 0 with h2 | h2
    · exact absurd (by simp [Prod.ext_iff, h1, h2]) hv
    · simp only [dot]
      nlinarith [mul_self_nonneg v.1, mul_self_pos.mpr h2]
  · simp only [dot]
    nlinarith [mul_self_nonneg v.2, mul_self_pos.mpr h1]

/-- ⭐ **§21.2：hlev 的 `hsign` 与本文件 §20 的 `0 ≤ s` 是同一笔账。**
`vJ ≠ 0` ＋ `W = s • vJ` ⟹ `0 ≤ dot W vJ ↔ 0 ≤ s`。 -/
theorem hb_sign_iff_scale_nonneg {v W : ℤ × ℤ} {s : ℤ} (hv : v ≠ 0) (hW : W = s • v) :
    0 ≤ dot W v ↔ 0 ≤ s := by
  have hpos : 0 < dot v v := hb_dot_self_pos hv
  rw [hb_dot_smul_left hW]
  constructor
  · intro hle
    by_contra hc
    have hs : s < 0 := not_le.mp hc
    nlinarith
  · intro hle
    exact mul_nonneg hle hpos.le

/-- ⭐ **§21.2：用 §20 的符号筛兑现 lane-tower-hlev `rec_vJ_of_ray_W` 的 `hsign` binder。**
前提与 `rec_vJ_of_det_sieve` 的后七条逐字相同，结论正是他们要的整数不等号。 -/
theorem hb_dot_W₀_vJ_nonneg_of_sieve {nJ p vJ1 vJ : ℤ × ℤ}
    (hnJ : nJ ≠ 0) (hvJprim : Primitive vJ) (hvJperp : dot nJ vJ = 0)
    (hα : 0 < dot nJ p)
    (hdpv : det p vJ ≠ 0) (hdpv1 : det p vJ1 ≠ 0)
    (hsieve : 0 ≤ det p vJ * det p vJ1) :
    0 ≤ dot (W₀ nJ p vJ1) vJ := by
  obtain ⟨s, hW⟩ := hb_scale_of_perp p vJ1 hnJ hvJprim hvJperp
  exact (hb_sign_iff_scale_nonneg hvJprim.ne_zero hW).mpr
    (hb_scale_pos hW hα hdpv hdpv1 hsieve).le

/-! ### §21.5 ⛔ **对 §21.1 第 4 条的当场更正（`PROTOCOL §57`／`§110`）**

§21.1 第 4 条采信了 lane-env-refute 2026-09-26 的 ②「树里没有『帽子并集是
`IsLatticeConvexRegion`』的现成实例」。**那条为假，我按结论型独立搜到了产者、并亲读了证明体
（`PROTOCOL §131`）**：`Nivat.Colle35.latticeConvex_iUnion_hatOf`（`ChainAssemble.lean`，
按标识符名引），结论逐字是 `IsLatticeConvexRegion (⋃ i, hatOf A kk vl i)`，前提四条：

| 它的 binder | `ChainDataGeomParts` 侧 |
|---|---|
| `hEnv : Env = EnvOf ↑S` | `rfl` —— 结构里 `maxA` 的 `Env` 已经钉死成 `EnvOf ↑S` |
| `maxA` | 同名字段 |
| `hfin` | 同名字段 |
| `AhatMono` | 同名字段 |

⟹ **`hconv` 在链上不是欠账，是字段的推论。**下面 `rec_vJ_of_parts_nondeg` 把它从 binder 里删掉。
发现路径记在此：lane-tower-hlev 的 `rec_vJ_of_parts_bottom₁₂`（`TowerHlevRecVJ.lean`）
正文里就在调它，我是读那条时撞见的。⟹ 这也是 hlev 的路线与我的路线共享的那一步。

⚠ 我**没有**去核 lane-env-refute 那句里的另一半（`rec_p_free` 的证明体里只有逐个 `A i` 的凸性）——
那句可能对；错的是从它推出的「树里没有」。`PROTOCOL §87`：某个证明体里没出现，不等于树里不存在。 -/

/-- **§21.5：帽子并集的格凸性是字段的推论，不是 binder。**
`latticeConvex_iUnion_hatOf`（`ChainAssemble.lean`，按标识符名引）＋ 三条同名字段 ＋ `hEnv := rfl`。 -/
theorem hb_latticeConvex_ahat_of_parts {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen) :
    IsLatticeConvexRegion (⋃ i, hatOf c.A c.kk vl i) :=
  latticeConvex_iUnion_hatOf η xper vl S (EnvOf (↑S : Set (ℤ × ℤ))) c.B c.A c.u c.kk rfl
    c.maxA c.hfin c.AhatMono

/-- ⭐⭐⭐ **§21.5 收口形：横截格上，`rec_vJ` 只剩三条 binder。**
`hconv` 由 `hb_latticeConvex_ahat_of_parts` 供给，不再出现在签名里。剩下的三条是
`hα : 0 < dot nJ p`、两条非退化 `det p vJ ≠ 0` / `det p vJ1 ≠ 0`、符号筛 `hsieve`；
前者与 `hsieve` 由 lane-env-refute 报为链上现货（② 我未复跑，见 §21.1），
**两条非退化仍无产者**（§21.4）。签名里零条整除，证明体里零个 `bottom`。 -/
theorem rec_vJ_of_parts_nondeg {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hα : 0 < dot c.nJ p)
    (hdpv : det p c.vJ ≠ 0) (hdpv1 : det p c.vJ1 ≠ 0)
    (hsieve : 0 ≤ det p c.vJ * det p c.vJ1) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i :=
  rec_vJ_of_parts_det_sieve c (hb_latticeConvex_ahat_of_parts c) hα hdpv hdpv1 hsieve

end PartsInstance



section TransverseCriterion

open Nivat.MaxEnv Nivat.HcombOrient Nivat.Colle35 Nivat.ChainAsm Nivat.ChainAsm.Aparts

/-!
## §22 `det p vJ1 ≠ 0` 的原文定位：**它等价于 `J > ι+1`，而原文明确允许 `J = ι+1`**

集成者 2026-09-26 派：从 `ChainDataGeomParts` 的字段（或一条能指到 `b3_colle2.txt` 行号的
前提）推出 `det p vJ1 ≠ 0`；消费者是 `RecVJTransverse.rec_vJ_of_parts_transverse` 的 `hdet`。

### §22.1 结论：**(c) —— 推不出来，而且原文明说不能。**（`PROTOCOL §51` 的分档：
这不是「我搜了范围 X 没找到」，是「原文在该处给出的条件式本身预设了反面可能」。）

`b3_colle2.txt:498` 逐字（`J` 的定义句）：

> let $\iota+1\leq J\leq\iota+m-1$ be the smallest integer such that

`:502` 逐字（紧接其后）：

> for infinity many $i$ . By passing to a subsequence, we can assume that this holds for all
> $i$ . **If $J>\iota+1$ , we also may assume that**

`:506` 逐字（那条附加假设的量词范围，以及 `Â_∞` 的结论句）：

> for every $\iota+1\leq j\leq J-1$ and all $i$ . In particular, $\hat{A}_{\infty}:=\bigcup
> _{i=1}^{\infty}\hat{A}_{i}$ is a weakly $E(\mathcal{S}_{\varphi})$ -enveloped set (see Figure 6),
> with two semi-infinite edges, one of which is parallel to $\boldsymbol{\ell}$ and the other one
> is parallel to $\boldsymbol{\ell}_{J}$ .

⟹ **「`If J > ι+1`」是条件式**：原文把那条附加假设显式地挂在 `J > ι+1` 之下，正因为
`J = ι+1` 是允许的一支。三处独立给出下界 `ι+1`（`:432` 的 Lemma 3.5 陈述、`:498` 的定义、
`:890` 的 Claim 4.x 复述），**没有任何一处把它抬到 `ι+2`**。

`ℓ_ι = ℓ` 由同一对象的两处称呼钉死：`:432` 叫它 `(ℓ_ι, ℓ_J)`-region，`:506` 叫它
`(ℓ, ℓ_J)`-region，指的是同一个 `Â_∞`。

⟹ `J = ι+1` 时 `ℓ_{J−1} = ℓ_ι = ℓ`，而 `vJ1 = v⃗_{ℓ_{J−1}}`（`:440` 逐字，`NOTATION.md` 的
2026-09-22 裁决同此）、`p = −c·v⃗_ℓ`，两者共线 ⟹ `det p vJ1 = 0`。
**⟹ `det p vJ1 ≠ 0` 不是链的推论，它是「链落在哪一格」的判据本身。**

### §22.2 本节落地的是那条判据的**逐字翻译**

`hb_det_p_vJ1_eq_zero_iff_collinear`：在链上现货形 `p = −(c:ℤ)•vl`（`c > 0`）＋ `Primitive vl` 下，

    det p vJ1 = 0  ↔  ∃ m : ℤ, vJ1 = m • vl

左边是集成者 `hdet` 的否定、右边是原文 `ℓ_{J−1} ∥ ℓ` 即 `J = ι+1`。⟹ 消费者要的 `hdet`
逐字等价于原文的 `J > ι+1`，**不多不少**。这正是我能交付的最强形式：把一条分析式的非退化
换成原文里真有名字的组合条件，从而让「该不该给 `hdet`」变成「链落在哪一格」这个可判问题
（lane-tower-hlev 2026-09-26 §6 立的那项，与此同一件事）。

⚠ **本节没有证 `J > ι+1`，也没有证 `J = ι+1`。**按 `PROTOCOL §119` 该格记 `不可判`，
不并进绿。我也**没有**主张「原文有漏洞」——`:502` 的条件式恰恰说明作者是知道两支的。

### §22.3 退化格（`det p vJ1 = 0`，即 `J = ι+1`）原文怎么走

原文对这一支**不另起炉灶**：`:506` 的结论句（`Â_∞` 有两条半无限边、一条 ∥ `ℓ`、另一条
∥ `ℓ_J`，且「Actually, `Â_∞` is an `(ℓ, ℓ_J)`-region」）是在 `:502` 的条件式**之后无条件给出**的
（「In particular」领起，不在 `If J > ι+1` 的辖域内——辖域到 `:506` 开头的
「for every ι+1 ≤ j ≤ J−1 and all i」为止）。⟹ 原文给 `rec_vJ` 的理由在两支里是**同一条**：
`ℓ_J` 那条半无限边。**这就是 `:506` 那一格**（集成者 2026-09-26 裁决④已准我开），
也是共线格唯一的产者候选——`W₀` 路在那里已被 lane-leafa-shell 的
`not_W₀_pos_multiple_of_collinear_lside` 打掉（② 我未复跑）。

### §22.4 射程（`PROTOCOL §41`）

* **没有**证 `det p vJ1 ≠ 0`，也没有给它任何新产者。本节结论是「它不是字段的推论」。
* **没有**改任何签名，**没有**碰 `GcdCollapse.lean`（不是我的文件；那节散文与
  `ChainPartsFeed` 的 `vJ1` 字段自相矛盾，hlev 已报集成者订正，我不动）。
* **没有**碰 `bottom`、没有碰定向约定（集成者本轮已裁定向盲那格由
  `latticeConvex_erase_flip` / `generatesAt_flip_gen` 关闭，② 我未复跑，也不需要）。
* 本节的原文读数是**我亲读** `scratch/b3_colle2.txt` 的 `:432` / `:440` / `:498` / `:502` /
  `:506` / `:890` 六行得到的（`PROTOCOL §131`），不是转述。
-/

/-- ⭐⭐⭐ **§22.2：`hdet` 的原文等价形。**
`det p vJ1 = 0` ⟺ `vJ1 ∥ vl` ⟺ 原文的 `J = ι+1`（`b3_colle2.txt:498` / `:502`）。
⟸ 只用 `hp`；⟹ 用 `hcc` 消去标量、再用 `eq_zsmul_of_det_eq_zero`（`Lattice/Primitive.lean`，
按标识符名引）把 `det vl vJ1 = 0` 兑成倍数。 -/
theorem hb_det_p_vJ1_eq_zero_iff_collinear {vl p vJ1 : ℤ × ℤ} {cc : ℕ}
    (hcc : 0 < cc) (hp : p = -(cc : ℤ) • vl) (hvl : Primitive vl) :
    det p vJ1 = 0 ↔ ∃ m : ℤ, vJ1 = m • vl := by
  have hexp : det p vJ1 = -(cc : ℤ) * det vl vJ1 := by
    subst hp
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  constructor
  · intro h
    have hc : (cc : ℤ) ≠ 0 := by exact_mod_cast hcc.ne'
    rw [hexp] at h
    rcases mul_eq_zero.mp h with h3 | h3
    · exact absurd (neg_eq_zero.mp h3) hc
    · exact eq_zsmul_of_det_eq_zero hvl h3
  · rintro ⟨m, rfl⟩
    rw [hexp]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- **§22.2 的否定形**，即消费者 `RecVJTransverse.rec_vJ_of_parts_transverse` 的 `hdet`
逐字等价于原文 `J > ι+1`。 -/
theorem hb_transverse_iff_not_collinear {vl p vJ1 : ℤ × ℤ} {cc : ℕ}
    (hcc : 0 < cc) (hp : p = -(cc : ℤ) • vl) (hvl : Primitive vl) :
    det p vJ1 ≠ 0 ↔ ¬ ∃ m : ℤ, vJ1 = m • vl :=
  not_congr (hb_det_p_vJ1_eq_zero_iff_collinear hcc hp hvl)

end TransverseCriterion



section DetVJFree

open Nivat.MaxEnv Nivat.HcombOrient Nivat.Colle35 Nivat.ChainAsm Nivat.ChainAsm.Aparts

/-!
## §23 `det p vJ ≠ 0` 是冗余 binder：`rec_vJ` 的非退化欠账降到**一条**

lane-env-refute 2026-09-26 指出 `det p vJ ≠ 0` 不必当欠账，并邀请本 lane 直接抄他们的
`det_ne_zero_of_perp`（⛔ **不能 import `EnvRefuteOrient`**：他们本轮已 import 本文件，反向即成环）。
我按邀请重写了一份（九行，自足，只用 `dot` / `det`），并**独立复核了它对本文件的作用**：

### §23.1 它拆掉的是我自己签名里的冗余，不是别人的债

`rec_vJ_of_det_sieve` 的 binder 里本来就有 `hvJprim : Primitive vJ`（⟹ `vJ ≠ 0`）、
`hvJperp : dot nJ vJ = 0`、`hα : 0 < dot nJ p`（⟹ `dot nJ p ≠ 0`）。三条合起来已经蕴含
`hdpv : det p vJ ≠ 0`。⟹ `hdpv` 从一开始就是**冗余 binder**，不是欠账。这是我上两轮
把「欠账 ＝ 两条非退化」写进 §20.4 / §21.1 的错误，已在那两处当场更正（`PROTOCOL §57`）。

机器是两条无前提的恒等式（`hb_dot_mul_fst_eq` / `hb_dot_mul_snd_eq`）：

    ⟪nJ,p⟫ · v.1 = p.1 · ⟪nJ,v⟫ − nJ.2 · det p v
    ⟪nJ,p⟫ · v.2 = p.2 · ⟪nJ,v⟫ + nJ.1 · det p v

`⟪nJ,v⟫ = 0` ＋ `det p v = 0` ⟹ `⟪nJ,p⟫ · v = 0` ⟹（`⟪nJ,p⟫ ≠ 0`）`v = 0`，与 `v ≠ 0` 矛盾。

### §23.2 ⚠ `det_ne_zero_of_perp` 是**一名两物**（`PROTOCOL §97` / `§111`）

`declscan.py det_ne_zero_of_perp` 给 `RAW=2 REAL=2`，两处**结论不同**，不是重复：

* `EnvRefuteOrient` 那份（lane-env-refute 本轮所报）：`det p v ≠ 0`，前提 `dot nJ p ≠ 0`；
* `EscapeW` 那份（`Nivat.LaneTowerHlevEscPos`，我亲读了证明体）：结论是 **`det vJ vJ1 ≠ 0`**，
  前提是 `dot nJ vJ1 ≠ 0` —— 那是 `vJ`/`vJ1` 的 perp-perp 形，**不是**本节要的 `p` 形。

⟹ 抄的时候必须认结论型，不能认名字（`PROTOCOL §114` / `§120`）。本节这份起名
`hb_det_ne_zero_of_perp` 以免第三次撞名；与 `EnvRefuteOrient` 那份的去重挂集成者
（`PROTOCOL §110.2`），我不删任何一份。

### §23.3 射程（`PROTOCOL §41`）

* 本节**只**在抽象 `R` 层落 `rec_vJ_of_det_sieve_slim`。⛔ **没有**落任何 parts 层的新形——
  那一层已有两条（集成者 `RecVJTransverse.rec_vJ_of_parts_transverse` 只要 `hdet`；
  lane-env-refute `rec_vJ_of_parts_of_det_ne` 同样只要一条），本节再加一条是净负
  （`PROTOCOL §91`、硬规矩 22）。我 §21 的 `rec_vJ_of_parts_nondeg` 也**不改签名**（裁决②）。
* 本节**没有**给 `det p vJ1 ≠ 0` 任何产者，也没有改 §22 的结论：它仍逐字等价于原文
  `J > ι+1`，原文不保证（`b3_colle2.txt:502` 的条件式）。
* ⚠ ② lane-env-refute 本轮报的 `det_p_vJ_ne_zero_of_parts` / `det_prod_pos_of_parts` /
  `rec_vJ_of_parts_of_det_ne` / `latticeConvex_of_parts`，以及他们「复跑了我 §19/§20」的陈述，
  **我未复跑**，按「lane 报」记账（`PROTOCOL §55`）。他们同轮自报主仓 `EnvRefuteOrient.lean`
  处于红树、判据「不可判」——⟹ 上述各条按 `PROTOCOL §112` **不计绿**，本节不依赖其中任何一条。
-/

/-- 无前提恒等式：`⟪nJ,p⟫ · v.1 = p.1 · ⟪nJ,v⟫ − nJ.2 · det p v`。 -/
theorem hb_dot_mul_fst_eq (nJ p v : ℤ × ℤ) :
    dot nJ p * v.1 = p.1 * dot nJ v - nJ.2 * det p v := by
  simp only [dot, det]
  ring

/-- 无前提恒等式：`⟪nJ,p⟫ · v.2 = p.2 · ⟪nJ,v⟫ + nJ.1 · det p v`。 -/
theorem hb_dot_mul_snd_eq (nJ p v : ℤ × ℤ) :
    dot nJ p * v.2 = p.2 * dot nJ v + nJ.1 * det p v := by
  simp only [dot, det]
  ring

/-- ⭐ **§23.1：`v ⊥ nJ` ＋ `v ≠ 0` ＋ `⟪nJ,p⟫ ≠ 0` ⟹ `det p v ≠ 0`。**
lane-env-refute 2026-09-26 的 `EnvRefuteOrient.det_ne_zero_of_perp` 同型（他们邀请本 lane 直抄；
⛔ 不能 import，他们已反向 import 本文件）。⚠ 与 `EscapeW` 里同名但**结论不同**的那条
（`det vJ vJ1 ≠ 0`）不是一回事，见 §23.2。去重挂集成者。 -/
theorem hb_det_ne_zero_of_perp {nJ p v : ℤ × ℤ} (hv : v ≠ 0) (hperp : dot nJ v = 0)
    (hα : dot nJ p ≠ 0) : det p v ≠ 0 := by
  intro hdet
  apply hv
  have h1 : dot nJ p * v.1 = 0 := by rw [hb_dot_mul_fst_eq, hperp, hdet]; ring
  have h2 : dot nJ p * v.2 = 0 := by rw [hb_dot_mul_snd_eq, hperp, hdet]; ring
  have hv1 : v.1 = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hα
    · exact h
  have hv2 : v.2 = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hα
    · exact h
  simp [Prod.ext_iff, hv1, hv2]

/-- ⭐⭐ **§23 主条：`rec_vJ_of_det_sieve` 去掉冗余 binder 后的形，非退化欠账只剩一条。**
与 `rec_vJ_of_det_sieve` 逐条相同，**除了 `hdpv : det p vJ ≠ 0` 被删**——它由
`hvJprim` / `hvJperp` / `hα` 经 `hb_det_ne_zero_of_perp` 推出。
⚠ 射程不变：`hdpv1 : det p vJ1 ≠ 0` 仍在，⟹ 仍是**横截格**结论，共线格不覆盖（§22）。 -/
theorem rec_vJ_of_det_sieve_slim {R : Set (ℤ × ℤ)} {nJ p vJ1 vJ g₀ : ℤ × ℤ} {cJ : ℤ}
    (hconv : IsLatticeConvexRegion R)
    (hg₀ : g₀ ∈ R)
    (hhp : ∀ z ∈ R, cJ ≤ dot nJ z)
    (hrecp : ∀ g ∈ R, g + p ∈ R)
    (hswept : SweptClosed R vJ1 nJ cJ)
    (hnJ : nJ ≠ 0) (hvJprim : Primitive vJ) (hvJperp : dot nJ vJ = 0)
    (hα : 0 < dot nJ p) (hβ : dot nJ vJ1 ≤ 0)
    (hdpv1 : det p vJ1 ≠ 0)
    (hsieve : 0 ≤ det p vJ * det p vJ1) :
    ∀ g ∈ R, g + vJ ∈ R :=
  rec_vJ_of_det_sieve hconv hg₀ hhp hrecp hswept hnJ hvJprim hvJperp hα hβ
    (hb_det_ne_zero_of_perp hvJprim.ne_zero hvJperp hα.ne') hdpv1 hsieve

end DetVJFree


/-! ## §24  `:506` 的「`ℓ_J` 半无限边」：几何字段块**推不出**它（内核负控）

**派工**：集成者裁决④，开 `b3_colle2.txt:506` 的半无限边那一格，目标**不分格**的 `rec_vJ`。
本节交的是这一格的**定价**，结论是否定的。

### §24.1  先钉死「已经有的」，免得造第三个

`:506` 逐字（本轮亲读 `scratch/b3_colle2.txt:506`，§131；下同）：

    In particular, $\hat{A}_{\infty}:=\bigcup_{i=1}^{\infty}\hat{A}_{i}$ is a weakly
    $E(\mathcal{S}_{\varphi})$-enveloped set (see Figure 6), with two semi-infinite edges,
    one of which is parallel to $\boldsymbol{\ell}$ and the other one is parallel to
    $\boldsymbol{\ell}_{J}$. Actually, $\hat{A}_{\infty}$ is an
    $(\boldsymbol{\ell},\boldsymbol{\ell}_{J})$-region.

逐量词对应：`Â_∞` ↦ `⋃ i, hatOf A kk vl i`；「the other one is parallel to `ℓ_J`」的那条
半无限边 ↦ 一条 `vJ` 方向的射线；「semi-infinite」↦ `∀ k : ℤ, L ≤ k`（半射线，不是整条线）。

主仓里这条射线**已经是一个字段**：`ChainDataGeomParts.bottom`（`ChainPartsFeed.lean`）的
**第 2 合取**

    ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) vJ1

⟹ 「由半无限边推 `rec_vJ`」这条路**已经通了，两个产者，一条不欠**：
`LaneLeafAGenRecVJ.rec_vJ_of_parts`（`RecVJFromParts.lean`，只吃 `c`）与
`LaneTowerHlevRecVJ.rec_vJ_of_parts_bottom₁₂`（`TowerHlevRecVJ.lean`，只吃前两个合取，
第 3、4 合取一条不用）。⛔ 本节**不**再造第三个：那是零边际（§91）。

真问题因此不是「半无限边 ⟹ `rec_vJ`」，而是**这条射线本身从哪来**。用 `bottom` 换 `rec_vJ`
是自毁出口——`EnvRefuteOrient.lean` 早写下同一判断（「有 `bottom` 就能用 `rec_vJ_of_parts`
直接拿 `rec_vJ`」），本轮亲读其文字后采信（§131）。

### §24.2  本节回答的是哪个问题（§102：分母、量纲、问题）

**问题**：把 `bottom` 拿掉之后，`ChainDataGeomParts` 的**几何字段**能不能推出 `:506` 的射线？

**分母 = 12**，**量纲** = `ChainDataGeomParts` 的字段或其零代价推论（不含 `bottom`）：

| # | 本节 binder | 链上来源 |
|---|---|---|
| 1 | `IsLatticeConvexRegion R` | `latticeConvex_iUnion_hatOf`（吃 `maxA`/`hfin`/`AhatMono`） |
| 2 | `R.Nonempty` | `ahat_nonempty` |
| 3 | `∀ z ∈ R, cJ ≤ dot nJ z` | `hhp`（经 `Set.iUnion_subset`） |
| 4 | `∀ g ∈ R, g + p ∈ R` | `rec_p` |
| 5 | `SweptClosed R vJ1 nJ cJ` | `hswept` |
| 6 | `∀ g ∈ R, cL ≤ dot (det p vJ • (-p.2, p.1)) g` | `ahat_halfPlane_L`（逐字符同形） |
| 7 | `∃ g ∈ R, dot (det p vJ • (-p.2, p.1)) g = cL` | `ahat_attained_L`（逐字符同形） |
| 8 | `Primitive nJ` | `nJ_prim` |
| 9 | `Primitive vJ` | `vJ_prim` |
| 10 | `dot nJ vJ = 0` | `F.dot_nJ_vJ` |
| 11 | `0 < dot nJ p` | `dot_nJ_p` ＋ 定符号 |
| 12 | `dot nJ vJ1 < 0` | `hsweep` |

**答：不能。** `hb_geom_block_not_imply_edge_ray` 是内核反例；连带
`hb_geom_block_not_imply_rec_vJ` 说同一张表也推不出 `rec_vJ` 本身。

### §24.3  反例

`hbQ := {z | z.1 = 0 ∧ 0 ≤ z.2}`（一条竖直半直线），
`p = (0,1)`、`vJ1 = (0,-1)`、`nJ = (0,1)`、`vJ = (1,0)`、`cJ = 0`、`cL = 0`。

为什么这个形状躲不掉：`hswept` 说「在半平面里沿 `vJ1` 往下走不出界」，`rec_p` 说「沿 `p`
往上走不出界」，而这里 `p = -vJ1`，两条合起来只说「沿竖直线双向自由」——一个字也没说横向。
`ahat_halfPlane_L` 在这组数据上是 `0 ≤ z.1`，`ahat_attained_L` 说它取到，两条都被
`z.1 = 0` 兑现。凸性、本原性、两条正交/符号条件全是逐点验算。

而射线不存在：`reachSet hbQ (0,-1)` 的第一坐标恒为 `0`（`hbQ_reachSet_fst`），
`z₀ + k • (1,0)` 的第一坐标随 `k` 严格递增 ⟹ 两个不同的 `k` 直接撞出 `1 = 0`。
`rec_vJ` 也当场假：`(0,0) + (1,0) ∉ hbQ`。

### §24.4  射程（§41 / §51 / §54 / §71），不许放大

1. 本反例**不**否掉链上的 `rec_vJ`，**不**否掉 `:506`，**不**否掉 `bottom`。它只否掉一条
   **蕴含**：上表 12 条 ⟹ 射线。链上还有 `bottom`、`maxA` 的极大性、`nfp_L`、以及 shell 四条
   （`escapeW` / `shellSubStrip` / `shellEnv` / `fillCover`）**没有**进 binder 表，本反例对它们
   一个字都没说（§54：没碰 ≠ 为假）。本节也**没有**构造 `ChainDataGeomParts` 的实例。
2. 本反例落在**共线格**：`det p vJ1 = det (0,1) (0,-1) = 0`（`hbQ_collinear`）。⟹ 它与横截格的
   那批产者（`EnvRefuteOrient.rec_vJ_of_parts_of_det_ne`、
   `RecVJTransverse.rec_vJ_of_parts_transverse`、本文件 §21 的 `rec_vJ_of_parts_nondeg`）
   **不冲突**：把 `det p vJ1 ≠ 0` 加进上表，本反例当场出局。
3. ⟹ 本节把 lane-leafa-shell「共线格里 `W₀ = 0`，`W₀` 那条路死」**加强一格**：
   共线格里死的不是某一条路，是**整个几何字段块**。共线格的 `rec_vJ` 必须动
   `maxA` / `nfp_L` / shell 块里的某一条，或者直接动 `bottom`。
4. 本 lane **不认领**第 3 条点名的那几条字段（rule 19），只交定价。
-/

section SemiInfEdgePricing

open Nivat.MaxEnv Nivat.Colle35

/-- **`:506` 定价反例的区域**：竖直半直线 `{(0, y) : y ≥ 0}`。

它扮演 `b3_colle2.txt:506` 的 `Â_∞`，但**只**兑现 §24.2 那张 12 条的表；`:506` 断言的
「平行于 `ℓ_J` 的半无限边」在它上面为假，见 `hbQ_no_edge_ray`。 -/
def hbQ : Set (ℤ × ℤ) := {z | z.1 = 0 ∧ 0 ≤ z.2}

theorem mem_hbQ {z : ℤ × ℤ} : z ∈ hbQ ↔ z.1 = 0 ∧ 0 ≤ z.2 := Iff.rfl

/-- `nJ = (0,1)` 读的就是第二坐标。 -/
theorem hbQ_dot_nJ (z : ℤ × ℤ) : dot ((0, 1) : ℤ × ℤ) z = z.2 := by simp [dot]

/-- `nL = (1,0)` 读的就是第一坐标。 -/
theorem hbQ_dot_nL (z : ℤ × ℤ) : dot ((1, 0) : ℤ × ℤ) z = z.1 := by simp [dot]

/-- 表的第 1 条。 -/
theorem hbQ_latticeConvex : IsLatticeConvexRegion hbQ := by
  refine ⟨{x : ℝ × ℝ | x.1 ≤ 0 ∧ 0 ≤ x.1 ∧ 0 ≤ x.2}, ?_, ?_, ?_⟩
  · rintro x ⟨hx1, hx2, hx3⟩ y ⟨hy1, hy2, hy3⟩ a b ha hb -
    refine ⟨?_, ?_, ?_⟩
    · show a * x.1 + b * y.1 ≤ (0 : ℝ)
      linarith [mul_nonneg ha (neg_nonneg.mpr hx1), mul_nonneg hb (neg_nonneg.mpr hy1)]
    · show (0 : ℝ) ≤ a * x.1 + b * y.1
      exact add_nonneg (mul_nonneg ha hx2) (mul_nonneg hb hy2)
    · show (0 : ℝ) ≤ a * x.2 + b * y.2
      exact add_nonneg (mul_nonneg ha hx3) (mul_nonneg hb hy3)
  · exact (isClosed_le continuous_fst continuous_const).inter
      ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_const continuous_snd))
  · ext z
    simp only [Set.mem_preimage, toReal]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_, ?_⟩
      · show ((z.1 : ℝ)) ≤ 0
        exact_mod_cast h1.le
      · show (0 : ℝ) ≤ ((z.1 : ℝ))
        exact_mod_cast h1.ge
      · show (0 : ℝ) ≤ ((z.2 : ℝ))
        exact_mod_cast h2
    · rintro ⟨h1, h2, h3⟩
      have g1 : ((z.1 : ℝ)) ≤ 0 := h1
      have g2 : (0 : ℝ) ≤ ((z.1 : ℝ)) := h2
      have g3 : (0 : ℝ) ≤ ((z.2 : ℝ)) := h3
      refine ⟨?_, ?_⟩
      · have hz : ((z.1 : ℝ)) = 0 := le_antisymm g1 g2
        exact_mod_cast hz
      · exact_mod_cast g3

/-- 表的第 2 条。 -/
theorem hbQ_nonempty : hbQ.Nonempty := ⟨(0, 0), mem_hbQ.mpr ⟨rfl, le_rfl⟩⟩

/-- 表的第 3 条（`cJ = 0`，`nJ = (0,1)`）。 -/
theorem hbQ_halfPlane : ∀ z ∈ hbQ, (0 : ℤ) ≤ dot ((0, 1) : ℤ × ℤ) z := by
  intro z hz
  have h := (mem_hbQ.mp hz).2
  rw [hbQ_dot_nJ]
  exact h

/-- 表的第 4 条（`p = (0,1)`）。 -/
theorem hbQ_rec_p : ∀ g ∈ hbQ, g + ((0, 1) : ℤ × ℤ) ∈ hbQ := by
  intro g hg
  obtain ⟨h1, h2⟩ := mem_hbQ.mp hg
  refine mem_hbQ.mpr ⟨?_, ?_⟩
  · have e : (g + ((0, 1) : ℤ × ℤ)).1 = g.1 := by simp
    rw [e, h1]
  · have e : (g + ((0, 1) : ℤ × ℤ)).2 = g.2 + 1 := by simp
    rw [e]
    omega

/-- 表的第 5 条（`vJ1 = (0,-1)`）。 -/
theorem hbQ_swept : SweptClosed hbQ ((0, -1) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) 0 := by
  intro g hg t ht
  obtain ⟨h1, -⟩ := mem_hbQ.mp hg
  have e1 : (g + (t : ℤ) • ((0, -1) : ℤ × ℤ)).1 = g.1 := by simp
  have e2 : (g + (t : ℤ) • ((0, -1) : ℤ × ℤ)).2 = g.2 - (t : ℤ) := by
    simp [sub_eq_add_neg]
  rw [hbQ_dot_nJ, e2] at ht
  refine mem_hbQ.mpr ⟨?_, ?_⟩
  · rw [e1, h1]
  · rw [e2]
    omega

/-- `ℓ_ι` 侧的法向，在这组数据上算出来是 `(1,0)`。写成 `ahat_halfPlane_L` 的**逐字符**形，
免得「实例其实换了个法向」这种偷换（§50）。 -/
theorem hbQ_nL_eq :
    (det ((0, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) •
      ((-((0, 1) : ℤ × ℤ).2, ((0, 1) : ℤ × ℤ).1) : ℤ × ℤ)) = ((1, 0) : ℤ × ℤ) := by
  norm_num [det, Prod.ext_iff]

/-- 表的第 6 条（`cL = 0`）。 -/
theorem hbQ_halfPlane_L :
    ∀ g ∈ hbQ, (0 : ℤ) ≤
      dot (det ((0, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) •
        ((-((0, 1) : ℤ × ℤ).2, ((0, 1) : ℤ × ℤ).1) : ℤ × ℤ)) g := by
  intro g hg
  have h1 := (mem_hbQ.mp hg).1
  rw [hbQ_nL_eq, hbQ_dot_nL, h1]

/-- 表的第 7 条。 -/
theorem hbQ_attained_L :
    ∃ g ∈ hbQ, dot (det ((0, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) •
      ((-((0, 1) : ℤ × ℤ).2, ((0, 1) : ℤ × ℤ).1) : ℤ × ℤ)) g = 0 := by
  refine ⟨(0, 0), mem_hbQ.mpr ⟨rfl, le_rfl⟩, ?_⟩
  rw [hbQ_nL_eq, hbQ_dot_nL]

/-- **本反例落在共线格**：`det p vJ1 = 0`。⟹ 加一条 `det p vJ1 ≠ 0` 它就出局，
与横截格的那批产者不冲突（§24.4 第 2 条）。 -/
theorem hbQ_collinear : det ((0, 1) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) = 0 := by
  simp [det]

/-- `reachSet hbQ (0,-1)` 的第一坐标恒为 `0`：沿 `vJ1` 扫掠一步也不横移。 -/
theorem hbQ_reachSet_fst {z : ℤ × ℤ}
    (hz : z ∈ MaxEnv.reachSet hbQ ((0, -1) : ℤ × ℤ)) : z.1 = 0 := by
  obtain ⟨g, hg, t, rfl⟩ := hz
  have h1 := (mem_hbQ.mp hg).1
  have e : (g + (t : ℤ) • ((0, -1) : ℤ × ℤ)).1 = g.1 := by simp
  rw [e, h1]

/-- ⭐ **`:506` 的半无限边在 `hbQ` 上不存在。**  语句逐字符是
`ChainDataGeomParts.bottom` 在 `ε = 0` 处的第 1、2 合取，也就是
`LaneTowerHlevRecVJ.rec_vJ_of_parts_bottom₁₂` 的 `hbot`。 -/
theorem hbQ_no_edge_ray :
    ¬ ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot ((0, 1) : ℤ × ℤ) z₀ = 0 - 1 ∧
      ∀ k : ℤ, L ≤ k → z₀ + k • ((1, 0) : ℤ × ℤ) ∈ MaxEnv.reachSet hbQ ((0, -1) : ℤ × ℤ) := by
  rintro ⟨z₀, L, -, hline⟩
  have h1 := hbQ_reachSet_fst (hline L le_rfl)
  have h2 := hbQ_reachSet_fst (hline (L + 1) (by linarith))
  have e1 : (z₀ + L • ((1, 0) : ℤ × ℤ)).1 = z₀.1 + L := by simp
  have e2 : (z₀ + (L + 1) • ((1, 0) : ℤ × ℤ)).1 = z₀.1 + L + 1 := by
    simp; ring
  rw [e1] at h1
  rw [e2] at h2
  omega

/-- `rec_vJ` 本身在 `hbQ` 上也假。 -/
theorem hbQ_not_rec_vJ : ¬ ∀ g ∈ hbQ, g + ((1, 0) : ℤ × ℤ) ∈ hbQ := by
  intro h
  have hm := h (0, 0) (mem_hbQ.mpr ⟨rfl, le_rfl⟩)
  have h1 := (mem_hbQ.mp hm).1
  have e : (((0, 0) : ℤ × ℤ) + ((1, 0) : ℤ × ℤ)).1 = 1 := by simp
  rw [e] at h1
  exact one_ne_zero h1

/-- ⭐⭐ **§24 的结论。** §24.2 那张 12 条的表**推不出** `b3_colle2.txt:506` 的半无限边。
射程见 §24.4：这是对**这张表**的否定，不是对链上 `rec_vJ`、不是对 `:506`、不是对 `bottom`。 -/
theorem hb_geom_block_not_imply_edge_ray :
    ¬ ∀ (R : Set (ℤ × ℤ)) (p vJ1 nJ vJ : ℤ × ℤ) (cJ cL : ℤ),
        IsLatticeConvexRegion R → R.Nonempty →
        (∀ z ∈ R, cJ ≤ dot nJ z) →
        (∀ g ∈ R, g + p ∈ R) →
        SweptClosed R vJ1 nJ cJ →
        (∀ g ∈ R, cL ≤ dot (det p vJ • (-p.2, p.1)) g) →
        (∃ g ∈ R, dot (det p vJ • (-p.2, p.1)) g = cL) →
        Primitive nJ → Primitive vJ → dot nJ vJ = 0 →
        0 < dot nJ p → dot nJ vJ1 < 0 →
        ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - 1 ∧
          ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet R vJ1 := by
  intro h
  refine hbQ_no_edge_ray ?_
  refine h hbQ (0, 1) (0, -1) (0, 1) (1, 0) 0 0 hbQ_latticeConvex hbQ_nonempty
    hbQ_halfPlane hbQ_rec_p hbQ_swept hbQ_halfPlane_L hbQ_attained_L
    (prim_iff_primitive.mp (by decide)) (prim_iff_primitive.mp (by decide))
    ?_ ?_ ?_
  · simp [dot]
  · simp [dot]
  · simp [dot]

/-- 同一张表也推不出 `rec_vJ` 本身。 -/
theorem hb_geom_block_not_imply_rec_vJ :
    ¬ ∀ (R : Set (ℤ × ℤ)) (p vJ1 nJ vJ : ℤ × ℤ) (cJ cL : ℤ),
        IsLatticeConvexRegion R → R.Nonempty →
        (∀ z ∈ R, cJ ≤ dot nJ z) →
        (∀ g ∈ R, g + p ∈ R) →
        SweptClosed R vJ1 nJ cJ →
        (∀ g ∈ R, cL ≤ dot (det p vJ • (-p.2, p.1)) g) →
        (∃ g ∈ R, dot (det p vJ • (-p.2, p.1)) g = cL) →
        Primitive nJ → Primitive vJ → dot nJ vJ = 0 →
        0 < dot nJ p → dot nJ vJ1 < 0 →
        ∀ g ∈ R, g + vJ ∈ R := by
  intro h
  refine hbQ_not_rec_vJ ?_
  refine h hbQ (0, 1) (0, -1) (0, 1) (1, 0) 0 0 hbQ_latticeConvex hbQ_nonempty
    hbQ_halfPlane hbQ_rec_p hbQ_swept hbQ_halfPlane_L hbQ_attained_L
    (prim_iff_primitive.mp (by decide)) (prim_iff_primitive.mp (by decide))
    ?_ ?_ ?_
  · simp [dot]
  · simp [dot]
  · simp [dot]

end SemiInfEdgePricing

section UnboundedLine

open Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm Nivat.ChainAsm.Aparts

/-! ## §25a  `hdpv` 是字段推论，链侧实例化版本

集成者 2026-09-26：`det p c.vJ ≠ 0` 在链上免费。本文件不 `import EnvRefuteOrient`（会成环，
lane-env-refute 已把方向钉死），所以用本仓 §23 的 `hb_det_ne_zero_of_perp` 供给同一条前提：
三个配料 `c.vJ_prim.ne_zero` / `c.F.dot_nJ_vJ` / `hα.ne'` 与 env-refute
`det_p_vJ_ne_zero_of_parts` 的三个配料逐字相同（其证明项由 lane-tower-hlev 亲读后转报，
本 lane 未复跑，`PROTOCOL §55`）。

⛔ 按盲区 3 与集成者裁决②：`rec_vJ_of_det_sieve` / `rec_vJ_of_parts_nondeg` 的签名一个字不动，
本条是**新增**的实例化层。
-/

/-- **`rec_vJ_of_parts_nondeg` 减掉 `hdpv`。**  剩下三条：`hα`（`dot_nJ_p` ＋ 定符号）、
`hdpv1`（= 横截格，`det vl c.vJ1 ≠ 0` 的 `p`-形）、`hsieve`（lane-leafa-shell 报为字段推论，
本 lane 未复跑，故仍留作 binder）。 -/
theorem rec_vJ_of_parts_nondeg_slim {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hα : 0 < dot c.nJ p)
    (hdpv1 : det p c.vJ1 ≠ 0)
    (hsieve : 0 ≤ det p c.vJ * det p c.vJ1) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i :=
  rec_vJ_of_parts_nondeg c hα
    (hb_det_ne_zero_of_perp c.vJ_prim.ne_zero c.F.dot_nJ_vJ hα.ne') hdpv1 hsieve

/-! ## §25b（**2026-09-26 撤出后又准予恢复**）

历史（§105 删号留名）：本节的「稀疏远点 ⟹ 半射线 ⟹ `rec_vJ`」四条 04:07 曾落地，
同日按集成者裁决以**零消费者**为由撤出（不是为假），负控留
`tmp/wip/lane-tower-hbase-s25b-negctrl.lean`。撤出理由是：`hunb`（沿 `v` 有任意远的点）
树里唯一的产者是 `hgrow`，而 `hgrow` 到 `rec_vJ` 另有更短的现货路
（`Colle35.ray_of_pinned_growth` → `RecessionCone.recession_of_ray`，按名引），
那条路用不到凸性 —— `hgrow` 给的是**连续初段**，本就强于「稀疏远点」。

⚠ 本 lane 先前用来翻盘「零消费者」的理由（「`hgrow` 路线要 `hne : ∀ i, (Âᵢ).Nonempty`，
本路线不要」）**作废**：`hne` 是 `hgrow` 产者的 binder，两条路线都以 `hgrow` 为 binder
起步 ⟹ 该项对两条路线代价相同，不构成差价。

🔴 **2026-09-26 集成者裁决：下面两条**抽象层**准予恢复**（理由：当初的撤出理由被本节
§26 的合取 2 驳倒，理由不成立则声明该回来）。恢复的**只有抽象两条**；两条链侧接口形
（`rec_vJ_of_parts_unbounded_line` / `'`）**未获批准，仍留在负控文件里**。
`RecVJSubsume.lean` 与 `LeafAShellPinGrow.lean` 的散文引用本轮随之重新有效。

🔴 **2026-09-26 第 243 轮追加裁决（§105 上一段不删，此段接续）：链侧接口形改为**准予**。**
集成者给的升格理由是共线格 `det p vJ1 = 0` 的一条算术：该格里 `vJ1 = λ • p` 且 `λ < 0`
（字段 `0 < ⟪nJ,p⟫` ＋ 字段 `hsweep : ⟪nJ,vJ1⟫ < 0`），于是 `a := ⟪nJ,p⟫` 整除
`e := -⟪nJ,vJ1⟫` **恒成立** ⟹ 只用 `rec_p` 的 `+p` 射线，高度谱模 `e` 只能命中
`e/a` 个剩余类里的 1 个，`+p` 单独永远不够；而链上另外几条 `rec_vJ` 产者的证明体里
都有 `c.bottom`（lane-leafa-shell 亲读 `RecVJFromParts.rec_vJ_of_parts` 的证明体，
最后一个实参逐字是 `c.bottom`；按 §55 记为「lane-leafa-shell 报」，本 lane 未复核证明体）
⟹ `bottom ⟸ 覆盖 ⟸ rec_vJ ⟸ bottom` 成环。本节这条是**唯一不吃 `bottom` 的入口**。
⚠ 上面那条整除算术是集成者的读数，本 lane 未独立核（§55）；它只影响**优先级**，
不进下面任何签名。

下面三条链侧形的**唯一真前提是 `hunb`**：`hconv` 由 `hb_latticeConvex_ahat_of_parts`
（形参只有 `c`）供给，`hz₀` 由字段 `c.ahat_nonempty` 供给。`hunb` 的产者已派 lane-tower-hlev；
本 lane 本轮全树 grep `ahat_unbounded_along_vJ`（`Nivat/` ＋ `tmp/`，`--include=*.lean`）
**命中 0**（§47；同一调用形对 `rec_vJ_of_unbounded_line` 有命中，grep 本身验过，§133）
⟹ 那条**还不在树里**，本节只是把接口备好，不是说它已经接上了。

⛔ **2026-09-26 同日再更正（§57；上段不删，§105）：共线格里这个 `hunb` 槽位喂不上。**
lane-tower-hlev 落 `TowerHlevCover.not_unb_vJ_Rdeg` 与 `not_unbounded_along_vJ_of_geom_bundle`
（②，本 lane 未复跑），内核证**二十条几何前提推不出 `hunb`**；见证
`Rdeg = {(-t,2t) : t ∈ ℕ}`、`nJ=(0,1)`、`vJ=(1,0)`、`vl=vJ1=(1,-2)`、`p=(-1,2)`。
⚠ 他们**没有**主张「`hunb` 为假」，主张的是「那二十条推不出它」。
本 lane 独立复算了该见证（硬规矩 6②）：`⟪nJ,vJ⟫=0`、`⟪nJ,p⟫=2>0`、`⟪nJ,vJ1⟫=-2<0`、
`det p vJ = -2 ≠ 0` ⟹ 它**满足** §27 的全部符号前提（`det p vJ · det vJ vJ1 = 4 > 0` ✓），
`rec_p` 在其上成立而 `rec_vJ` 假、`hunb` 假 —— 与本节结论不冲突（本节要的正是 `hunb`）。

⭐ **射程（要紧）：该见证的分格量 `det p vJ1 · det vJ vJ1 = 0`**（`det p vJ1 = 0`，共线格）
⟹ 它**落在本文件 §27／§28 两个横截半格之外**，对**异号半格的 `hunb` 槽位一个字都没说**
（`PROTOCOL §54`：没碰过 ≠ 为假）。要封异号半格，需要一个 `det p vJ1 · det vJ vJ1 < 0`
的见证，树里目前没有。

⛔ **§57 更正（2026-09-26，原文保留，§105）：上一段的最后两句作废。** 见 §29：链上
`0 ≤ det p vJ · det p vJ1`（lane-env-refute 的 `EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg`，
②）配本文件 `hb_det_vJ_vJ1_mul_pos` ⟹ 分格量在链上恒 `≥ 0` ⟹ **异号半格在链上是空的**，
根本不需要「一个异号见证」去封它。⟹ `hunb` 的适用格**只有共线格**，而共线格那一格的
`hunb` 槽位正是 lane-tower-hlev 这条结果打掉的。原文：「它落在……两个横截半格之外，对异号
半格的 `hunb` 槽位一个字都没说……树里目前没有」——前半句（射程是共线格）仍然成立，作废的是
「异号半格因此还是一条活路」这个推论。 -/

/-- **格凸性：沿一条直线有任意远的点 ⟹ 整条半射线。**

`hunb` 只说「对每个 `N` 存在 `k ≥ N` 使 `z₀ + k • v ∈ R`」（下标可以跳、可以稀疏），
结论是**每一个** `s : ℕ` 都在。机制：`0 ≤ s ≤ k` 时 `z₀ + s • v` 落在实线段
`[toReal z₀, toReal (z₀ + k • v)]` 上，凸包含它，而 `R` 是该凸集的格点原像
（`eq_preimage_convHullOf`）。

⚠ 只用 `Convex`，不用 `IsClosed`（lane-env-refute 2026-09-26 指出的受力点，本 lane
已亲读证明项：本条从不析构 `IsLatticeConvexRegion`，闭性只经 `eq_preimage_convHullOf` 进入）。

前提表里**没有** `nJ` / `cJ` / `vJ1` / 任何 `det`：这是纯凸性事实。 -/
theorem hb_ray_of_unbounded_line {R : Set (ℤ × ℤ)} {v z₀ : ℤ × ℤ}
    (hconv : IsLatticeConvexRegion R) (hz₀ : z₀ ∈ R)
    (hunb : ∀ N : ℤ, ∃ k : ℤ, N ≤ k ∧ z₀ + k • v ∈ R) :
    ∀ s : ℕ, z₀ + (s : ℤ) • v ∈ R := by
  intro s
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · subst hs0
    simpa using hz₀
  obtain ⟨k, hk, hmem⟩ := hunb (s : ℤ)
  have hspos' : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hspos
  have hkpos : (0 : ℤ) < k := lt_of_lt_of_le hspos' hk
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hhull : Convex ℝ (convHullOf R) := convex_convHullOf R
  have hA : toReal z₀ ∈ convHullOf R := mem_convHullOf_of_mem hz₀
  have hB : toReal (z₀ + k • v) ∈ convHullOf R := mem_convHullOf_of_mem hmem
  set lam : ℝ := (s : ℝ) / (k : ℝ) with hlam
  have hlam0 : (0 : ℝ) ≤ lam := by
    rw [hlam]
    positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlam, div_le_one hkR]
    exact_mod_cast hk
  have hks : lam * (k : ℝ) = (s : ℝ) := by
    rw [hlam]
    field_simp
  have hcomb := hhull hA hB (by linarith : (0 : ℝ) ≤ 1 - lam) hlam0 (by ring)
  have heq : (1 - lam) • toReal z₀ + lam • toReal (z₀ + k • v)
      = toReal (z₀ + (s : ℤ) • v) := by
    rw [toReal_add, toReal_zsmul, toReal_add, toReal_zsmul]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      push_cast
      linear_combination (toReal v).1 * hks
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      push_cast
      linear_combination (toReal v).2 * hks
  rw [heq] at hcomb
  rw [eq_preimage_convHullOf hconv]
  exact hcomb

/-- `:506` 的几何那半，抽象形。  格凸 ＋ 沿 `v` 有任意远的点 ⟹ `R + v ⊆ R`。

ray ⟹ rec 那一步**委托**给正本 `Nivat.RecessionCone.recession_of_ray`（按标识符名引），
本条只贡献「任意远 ⟹ 射线」那个量词升级 —— 不产生第 4 份转发。 -/
theorem rec_vJ_of_unbounded_line {R : Set (ℤ × ℤ)} {v z₀ : ℤ × ℤ}
    (hconv : IsLatticeConvexRegion R) (hz₀ : z₀ ∈ R)
    (hunb : ∀ N : ℤ, ∃ k : ℤ, N ≤ k ∧ z₀ + k • v ∈ R) :
    ∀ g ∈ R, g + v ∈ R :=
  Nivat.RecessionCone.recession_of_ray hconv (hb_ray_of_unbounded_line hconv hz₀ hunb)

/-- **`¬BddAbove` ⟹ `hunb`（适配器）。**

产者那侧「沿 `v` 无界」最自然的形是「步数集不上有界」；本条把它翻成 `hb_ray_of_unbounded_line`
吃的 `∀ N, ∃ k ≥ N` 形。纯序论，零几何、零格。 -/
theorem hb_unbounded_line_of_not_bddAbove {R : Set (ℤ × ℤ)} {v z₀ : ℤ × ℤ}
    (hnb : ¬ BddAbove {k : ℤ | z₀ + k • v ∈ R}) :
    ∀ N : ℤ, ∃ k : ℤ, N ≤ k ∧ z₀ + k • v ∈ R := by
  intro N
  by_contra hcon
  refine hnb ⟨N, fun k hk => ?_⟩
  by_contra hlt
  exact hcon ⟨k, (not_le.mp hlt).le, hk⟩

/-- **链侧接口形（第 243 轮准予）：`ChainDataGeomParts` ＋ `hunb` ⟹ `rec_vJ`。**

原文锚 `scratch/b3_colle2.txt:506`：「$\hat{A}_{\infty}:=\bigcup_{i=1}^{\infty}\hat{A}_{i}$ is a
weakly $E(\mathcal{S}_{\varphi})$-enveloped set …, **with two semi-infinite edges**, one of which is
parallel to $\boldsymbol{\ell}$ and the other one is parallel to $\boldsymbol{\ell}_{J}$」。
逐量词：那条「parallel to $\boldsymbol{\ell}_{J}$ 的半无限边」= 本条的 `hunb`（沿 `c.vJ` 有任意远的
格点，∀ N ∃ k ≥ N）；结论 `∀ g ∈ ⋃ i, hatOf …, g + c.vJ ∈ …` = 同句 `(ℓ, ℓ_J)`-region 的
`ℓ_J` 方向封闭性。原文给的理由是「半无限边」，**不是**「连续初段」：从稀疏远点补到整条射线
的那一步正是 `hb_ray_of_unbounded_line` 用格凸性做的。

`hconv` 由 `hb_latticeConvex_ahat_of_parts c`（形参只有 `c`）供给；证明体里零个 `c.bottom`
（本条只把 `c` 用在格凸性与载体上）。 -/
theorem rec_vJ_of_parts_unbounded_line {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen) {z₀ : ℤ × ℤ}
    (hz₀ : z₀ ∈ ⋃ i, hatOf c.A c.kk vl i)
    (hunb : ∀ N : ℤ, ∃ k : ℤ, N ≤ k ∧ z₀ + k • c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i :=
  rec_vJ_of_unbounded_line (hb_latticeConvex_ahat_of_parts c) hz₀ hunb

/-- **无选择点形：起点由字段 `c.ahat_nonempty` 自己选 ⟹ 签名里只剩 `hunb` 一条真前提。**

这是给 `hunb` 产者对接用的形：产者只需交出「**某个** `Âinf` 里的点沿 `c.vJ` 无界」。 -/
theorem rec_vJ_of_parts_unbounded_line' {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hunb : ∃ z₀ ∈ ⋃ i, hatOf c.A c.kk vl i,
      ∀ N : ℤ, ∃ k : ℤ, N ≤ k ∧ z₀ + k • c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i := by
  obtain ⟨z₀, hz₀, hray⟩ := hunb
  exact rec_vJ_of_parts_unbounded_line c hz₀ hray

/-- **`¬BddAbove` 直投形。** 三者合成：适配器 ＋ 格凸性 ＋ `recession_of_ray`。 -/
theorem rec_vJ_of_parts_not_bddAbove {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen) {z₀ : ℤ × ℤ}
    (hz₀ : z₀ ∈ ⋃ i, hatOf c.A c.kk vl i)
    (hnb : ¬ BddAbove {k : ℤ | z₀ + k • c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i}) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i :=
  rec_vJ_of_parts_unbounded_line c hz₀ (hb_unbounded_line_of_not_bddAbove hnb)

/-- **§86 守卫（会失败的检查）：`hb_ray_of_unbounded_line` 的 `hconv` 不可删。**

见证 `R = {z | ∃ t, z.1 = 2t ∧ z.2 = 0}`、`v = (1,0)`、`z₀ = (0,0)`：`hz₀` 与 `hunb` 都成立
（取 `k = 2|N|`），而 `s = 1` 的射线点 `(1,0) ∉ R`。⟹ 「稀疏远点 ⟹ 整条射线」这一步**纯靠格凸性**，
不是量词记账。

⚠ 这不是说 `rec_vJ_of_unbounded_line` 为假（§54）：该见证不格凸，链上构型里不存在
（它连 `ChainDataGeomParts` 的载体形都不是）。本条只钉「哪条 binder 在受力」。

配对读数：另一条 binder `hunb` 的受力由 lane-tower-hlev 的
`TowerHlevCover.not_unbounded_along_vJ_of_geom_bundle` 见证 `{(-t,2t) : t ∈ ℕ}`
（`vJ = (1,0)`，沿 `+vJ` 完全不动，格凸却 `rec_vJ` 假）钉住；其裸见证形
`TowerHlevCover.not_unb_vJ_Rdeg` 与本文件 `rec_vJ_of_parts_unbounded_line'` 的 `hunb` binder
是同一个量词骨架（`∃ z₀ ∈ …, ∀ N, ∃ k, N ≤ k ∧ z₀ + k • v ∈ …`）。
那两条是**他们报的**（§55，本 lane 未复跑、未 import）。两条合起来：`hconv` 与 `hunb`
一条都不能删。

⚠ **§57 更正（2026-09-26，原文保留见下，§105）**：本段此前把 `hunb` 的受力挂在
`not_cover_of_geom_bundle` 名下 —— 那条否的是**剩余类覆盖**，是第三件事，不是 `hunb`。
括号里的几何描述（见证沿 `+vJ` 不动、格凸）本来就对，错的只是标识符（§111「并」形态：
散文对、声明错）。lane-tower-hlev 主动订正，本行已按其给出的替换品改写。
原文：「另一条 binder `hunb` 的受力由 lane-tower-hlev 的 `not_cover_of_geom_bundle` 见证
`{(-t,2t) : t ∈ ℕ}` …… 钉住」。⟹ 三条声明各钉一格（`hconv` / `hunb` / 覆盖），不是两条。

⚠ 射程不变（§54）：该见证的分格量 `det p vJ1 * det vJ vJ1 = 0`（共线格），对本文件
§27／§28 两个横截半格的 `hunb` 槽位仍然一个字都没说；lane-tower-hlev 亦不主张 `hunb` 为假，
只主张那二十条几何前提推不出它。

⛔ **§57 再更正（2026-09-26，第 245 轮，集成者裁决 —— 上一段的射程限定现在收紧）**：
上一段说「对两个横截半格的 `hunb` 槽位一个字都没说」——**那两格里只有同号格是链上活的**
（异号格链上空真，见 §29 与 `LeafAShellWedgeSign.det_sign_of_parts`），而同号格里
`rec_vJ` 由 `EnvRefuteOrient.rec_vJ_of_parts_of_det_ne` **整格免费**（前提只有
`det p c.vJ1 ≠ 0`，同号蕴含之）。⟹ **`hunb` 在链上唯一可能被需要的格就是共线格**，
而那一格正是 hlev 打掉的那格。⟹ **`hunb` 槽位在链上无消费格**，本文件这条 `rec_vJ`
入口不要再记成活路线。

⛔ **共线格的封锁又收紧一档（集成者转 lane-env-refute 落地，第 245 轮，②，本 lane 未复跑）**：
`EnvRefuteMaxA.exists_maxA_for_ray` 在 hlev **同一个**见证上把 `maxA` 连同 union／有限／
单调一起兑现 ⟹ **把 `maxA` 加进那二十条几何前提，hlev 的两条 bundle 依然成立**。
所以准确的记账是：接口不变（无格假设，对任意 `c` 成立），共线格的 `hunb` 产者位空缺，
且已知**不能**由那二十条几何前提产出，**加上 `maxA` 仍不能**。 -/
theorem hb_unbounded_line_needs_latticeConvex :
    ∃ (R : Set (ℤ × ℤ)) (v z₀ : ℤ × ℤ), z₀ ∈ R ∧
      (∀ N : ℤ, ∃ k : ℤ, N ≤ k ∧ z₀ + k • v ∈ R) ∧
      ¬ (∀ s : ℕ, z₀ + (s : ℤ) • v ∈ R) := by
  refine ⟨{z : ℤ × ℤ | ∃ t : ℤ, z.1 = 2 * t ∧ z.2 = 0}, (1, 0), (0, 0), ⟨0, ?_, ?_⟩, ?_, ?_⟩
  · norm_num
  · norm_num
  · -- `hunb`：取 `k = 2|N|`，见证 `t = |N|`
    intro N
    have hle : N ≤ 2 * |N| := by
      have h1 : N ≤ |N| := le_abs_self N
      have h2 : (0 : ℤ) ≤ |N| := abs_nonneg N
      linarith
    refine ⟨2 * |N|, hle, |N|, ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      norm_num
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      norm_num
  · -- 射线在 `s = 1` 处掉出：`1` 不是偶数
    intro hray
    obtain ⟨t, ht, -⟩ := hray 1
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at ht
    have ht' : (1 : ℤ) = 2 * t := by
      norm_num at ht
      exact ht
    omega

end UnboundedLine

section SuppCell

open Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm Nivat.ChainAsm.Aparts

/-! ## §26 横截格的「定向 ＋ 支撑界」：`rec_p` 把两个旋转里的一个当场杀掉

集成者 2026-09-26 派的新靶子（替换早先那张六条残余单）第 2、3 条，横截格：

* **定向** `dot nprevJ c.vJ < 0`
* **支撑界** `∃ V, ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i, dot nprevJ z ≤ dot nprevJ V`

`nprevJ` 的唯一约束是 `dot nprevJ c.vJ1 = 0`（`EnvRefuteOrient` 的 `hline0_of_supp` 的
binder `hnpvJ1`，按名引），集成者取的实例是旋转 `(c.vJ1.2, -c.vJ1.1)`；另一个同样合法的
取法是 `(-c.vJ1.2, c.vJ1.1)`。本节的内容是：**这两个取法里恰好一个被字段当场否掉，
而且被否掉的那个由 `det p c.vJ1` 的符号决定。**

### §26.1 先算数值实例（硬规矩 6）

取 `p = (1,0)`、`vJ = (1,0)`、`vJ1 = (0,-1)`，则 `det p vJ1 = -1 ≠ 0`（横截格），
两个旋转是 `(vJ1.2, -vJ1.1) = (-1,0)` 与 `(-vJ1.2, vJ1.1) = (1,0)`：

* `dot (1,0) p = 1 > 0`：`rec_p` 沿 `p` 把帽子并集无限往 `+x` 推 ⟹ 该旋转**没有**支撑界。
* `dot (-1,0) p = -1 < 0`：不被 `rec_p` 否掉，且 `dot (-1,0) vJ = -1 < 0`，定向也成立。

共线格 `det p vJ1 = 0` 时 `dot (rot vJ1) p = 0`，`rec_p` 的射线与 `nprevJ` 正交 ⟹
两个旋转都不被否。**这就是两格在这两条上的全部差别**，与「塌不塌」无关。

### §26.2 机制：`hsupp` 强制 `dot nprevJ p ≤ 0`

字段 `rec_p` 给出帽子并集沿 `p` 的**整条射线**，字段 `ahat_nonempty` 给出起点；射线上
`dot w (g + t • p) = dot w g + t * dot w p`，`0 < dot w p` 时无上界。⟹ 任何允许
`w`-支撑界的 `w` 必须满足 `dot w p ≤ 0`。**只用这两条字段：不用穷尽性、不用凸性、
不用 `bottom`、不用 `rec_vJ`。**

### §26.3 ⟹ 两条联立是一个**同号条件**

恒等式 `hb_dot_rot_eq_det`（`dot (v.2,-v.1) d = det d v`）把两条翻成
`a := det p c.vJ1`、`b := det c.vJ c.vJ1` 上的符号条件：旋转 `+` 要 `b < 0` ∧ `a ≤ 0`，
旋转 `-` 要 `b > 0` ∧ `a ≥ 0`。⟹ `a * b < 0` 时**两个旋转全灭**
（`hb_no_rot_admissible_of_det_mul_neg`）；`0 < a * b` 时活下来的那个唯一确定。

⚠ **射程自限（硬规矩 5，别放大）**：
1. 本节**没有**证明 `hsupp` 为假，也**没有**证明帽子并集在横截格里无界。证的是蕴含
   「`hsupp` ⟹ `dot w p ≤ 0`」，以及它与定向条件联立后的符号后果。
2. `a * b` 的符号本身是**定向问题**（第 179 轮红线冻结的那一格），本 lane 不裁；
   `hb_det_mul_pos_satisfiable` 是 `PROTOCOL §86` 守卫，说明同号支可满足、本节不是全灭结论。
3. `nprevJ` 只覆盖两个旋转及其正倍数。若 `c.vJ1` 非本原，`{w | dot w c.vJ1 = 0}` 还有别的
   整点，本节不覆盖那些；把它们并进来需要 `Primitive c.vJ1`，而那条不是字段
   （见本文件 `VJ1Source` 一节）。
4. 与 `EnvRefuteOrient` 的 `supp_fails_on_halfPlane`（lane-env-refute 本轮落，按名引）
   **不是别名**：那条把 `T`、`nprevJ` 钉成字面值，本节给的是**分界线**（哪些 `vJ1` 会否掉
   支撑界），理由走字段 `rec_p` 而不是某个具体居民。两条在数值上一致：那条的
   `nprevJ = (-1,0)` 正是本节判据里**活下来**的那个旋转。
-/

/-- **恒等式**：`v` 的旋转与任意 `d` 的内积就是 `det d v`。零前提。
（`BottomHz0Collapse` 的 `dot_rot_self` 是它在 `d := v` 处的特例。） -/
theorem hb_dot_rot_eq_det (d v : ℤ × ℤ) : dot (v.2, -v.1) d = det d v := by
  simp only [dot, det]
  ring

/-- **另一个旋转**：同一内积差一个符号。 -/
theorem hb_dot_rot'_eq_neg_det (d v : ℤ × ℤ) : dot (-v.2, v.1) d = -det d v := by
  simp only [dot, det]
  ring

/-- ⭐ **沿 `p` 的射线否掉 `w`-支撑界**（`0 < dot w p` 时）。抽象形，无链上内容。 -/
theorem hb_not_supp_of_rec_of_dot_pos {R : Set (ℤ × ℤ)} {w p : ℤ × ℤ}
    (hrec : ∀ g ∈ R, g + p ∈ R) (hne : R.Nonempty) (hpos : 0 < dot w p) :
    ¬ ∃ V : ℤ × ℤ, ∀ z ∈ R, dot w z ≤ dot w V := by
  rintro ⟨V, hV⟩
  obtain ⟨g, hg⟩ := hne
  have hray : ∀ t : ℕ, g + (t : ℤ) • p ∈ R := by
    intro t
    induction t with
    | zero => simpa using hg
    | succ t ih =>
        have h := hrec _ ih
        have heq : g + (t : ℤ) • p + p = g + ((t + 1 : ℕ) : ℤ) • p := by
          push_cast
          rw [add_smul, one_smul, ← add_assoc]
        rw [heq] at h
        exact h
  have hexp : ∀ t : ℕ, dot w (g + (t : ℤ) • p) = dot w g + (t : ℤ) * dot w p := by
    intro t
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have h1 : 1 ≤ dot w p := by
    have h := Int.lt_iff_add_one_le.mp hpos
    linarith
  have hle := hV _ (hray ((dot w V - dot w g).toNat + 1))
  rw [hexp] at hle
  have hNge : dot w V - dot w g ≤ ((dot w V - dot w g).toNat : ℤ) :=
    Int.self_le_toNat _
  have hnn : (0 : ℤ) ≤ ((dot w V - dot w g).toNat : ℤ) + 1 := by
    have h := Int.natCast_nonneg ((dot w V - dot w g).toNat)
    linarith
  have hstep : (((dot w V - dot w g).toNat : ℤ) + 1) * 1
      ≤ (((dot w V - dot w g).toNat : ℤ) + 1) * dot w p :=
    mul_le_mul_of_nonneg_left h1 hnn
  push_cast at hle
  linarith

/-- ⭐ **链上：任何有 `w`-支撑界的 `w` 必须满足 `dot w p ≤ 0`。**
配料只有两条字段：`rec_p` 与 `ahat_nonempty`。

⛔ **§91 披露（集成者裁决，2026-09-26，第 245 轮）**：与
`EnvRefuteOrient.dot_p_nonpos_of_supp` **同结论**，**他们更一般**（任意合法 `nprevJ`），
**本条存在的唯一理由是 import 方向** —— 本文件不能 import `EnvRefuteOrient`（真环：
`EnvRefuteOrient` 已 import 本文件），所以链上想在本文件及其上游里用这条结论，
只能用本条。集成者裁决：**留，不撤**。去重归集成者（`PROTOCOL §110.2`）。 -/
theorem hb_supp_forces_dot_p_nonpos {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen) {w : ℤ × ℤ}
    (hsupp : ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i, dot w z ≤ dot w V) :
    dot w p ≤ 0 := by
  by_contra hcon
  exact hb_not_supp_of_rec_of_dot_pos c.rec_p c.ahat_nonempty (not_le.mp hcon) hsupp

/-- **旋转 `+` 的支撑界 ⟹ `det p c.vJ1 ≤ 0`**。 -/
theorem hb_supp_rot_forces_det_nonpos {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hsupp : ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i,
      dot (c.vJ1.2, -c.vJ1.1) z ≤ dot (c.vJ1.2, -c.vJ1.1) V) :
    det p c.vJ1 ≤ 0 := by
  have h := hb_supp_forces_dot_p_nonpos c hsupp
  rwa [hb_dot_rot_eq_det] at h

/-- **旋转 `-` 的支撑界 ⟹ `0 ≤ det p c.vJ1`**。 -/
theorem hb_supp_rot'_forces_det_nonneg {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hsupp : ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i,
      dot (-c.vJ1.2, c.vJ1.1) z ≤ dot (-c.vJ1.2, c.vJ1.1) V) :
    0 ≤ det p c.vJ1 := by
  have h := hb_supp_forces_dot_p_nonpos c hsupp
  rw [hb_dot_rot'_eq_neg_det] at h
  linarith

/-- ⭐⭐ **`det p c.vJ1` 与 `det c.vJ c.vJ1` 异号 ⟹ 两个旋转都不合法**：
定向与支撑界不能同时成立。⚠ 这不是「横截格为假」，是「横截格要求这两个行列式同号」。

⛔ **§91 披露（集成者裁决，2026-09-26，第 245 轮）**：本条经
`hb_supp_forces_dot_p_nonpos` 走，而那条与 `EnvRefuteOrient.dot_p_nonpos_of_supp`
同结论、他们更一般；**本条存在的唯一理由同样是 import 方向**。集成者裁决：**留，不撤**。

⛔ 另注（§57，与 §29 一致）：前提 `hmul` 即「异号格」，在链上不可满足
（`LeafAShellWedgeSign.det_sign_of_parts`；本文件的等价形是 §29 的
`hb_cell_nonneg_of_sieve_nonneg` ⊗ 链侧筛）⟹ **本条对链上构型空真**，
其内容是「若异号则两个旋转都不合法」这条纯符号蕴含，对链外抽象数据仍有效。 -/
theorem hb_no_rot_admissible_of_det_mul_neg {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hmul : det p c.vJ1 * det c.vJ c.vJ1 < 0) :
    (¬ (dot (c.vJ1.2, -c.vJ1.1) c.vJ < 0 ∧
        ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i,
          dot (c.vJ1.2, -c.vJ1.1) z ≤ dot (c.vJ1.2, -c.vJ1.1) V)) ∧
    (¬ (dot (-c.vJ1.2, c.vJ1.1) c.vJ < 0 ∧
        ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i,
          dot (-c.vJ1.2, c.vJ1.1) z ≤ dot (-c.vJ1.2, c.vJ1.1) V)) := by
  constructor
  · rintro ⟨hor, hsupp⟩
    have ha : det p c.vJ1 ≤ 0 := hb_supp_rot_forces_det_nonpos c hsupp
    have hb : det c.vJ c.vJ1 < 0 := by rwa [hb_dot_rot_eq_det] at hor
    have h0 : (0 : ℤ) ≤ (-det p c.vJ1) * (-det c.vJ c.vJ1) :=
      mul_nonneg (by linarith) (by linarith)
    rw [neg_mul_neg] at h0
    linarith
  · rintro ⟨hor, hsupp⟩
    have ha : 0 ≤ det p c.vJ1 := hb_supp_rot'_forces_det_nonneg c hsupp
    have hb : 0 < det c.vJ c.vJ1 := by
      rw [hb_dot_rot'_eq_neg_det] at hor
      linarith
    have h0 : (0 : ℤ) ≤ det p c.vJ1 * det c.vJ c.vJ1 := mul_nonneg ha (by linarith)
    linarith

/-- **守卫（`PROTOCOL §86`）**：`hb_not_supp_of_rec_of_dot_pos` 的前提族可满足，
所以它不是空真的。 -/
theorem hb_not_supp_hypotheses_satisfiable :
    ∃ (R : Set (ℤ × ℤ)) (w p : ℤ × ℤ),
      (∀ g ∈ R, g + p ∈ R) ∧ R.Nonempty ∧ 0 < dot w p := by
  refine ⟨{z : ℤ × ℤ | 0 ≤ z.1}, ((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ?_,
    ⟨((0 : ℤ), (0 : ℤ)), by simp⟩, by norm_num [dot]⟩
  intro g hg
  have h : (0 : ℤ) ≤ g.1 := hg
  show (0 : ℤ) ≤ (g + ((1 : ℤ), (0 : ℤ))).1
  simpa using (by omega : (0 : ℤ) ≤ g.1 + 1)

/-- **守卫（`PROTOCOL §86`）**：`hb_no_rot_admissible_of_det_mul_neg` 不是全灭结论 ——
同号支可满足，且此时活下来的旋转同时满足定向。数值就是 §26.1 手算那组。 -/
theorem hb_det_mul_pos_satisfiable :
    ∃ p vJ vJ1 : ℤ × ℤ, det p vJ1 ≠ 0 ∧ 0 < det p vJ1 * det vJ vJ1 ∧
      dot (vJ1.2, -vJ1.1) vJ < 0 ∧ dot (vJ1.2, -vJ1.1) p < 0 := by
  refine ⟨((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (-1 : ℤ)), ?_, ?_, ?_, ?_⟩
  · norm_num [det]
  · norm_num [det]
  · norm_num [dot]
  · norm_num [dot]

end SuppCell

section SliceCone

open Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm Nivat.ChainAsm.Aparts

/-! ## §27 `hslice`：锥把它归约成窗口上的一条符号条件，异号半格直接免费

⛔ **§57 更正（2026-09-26 晚，标题里「异号半格直接免费」在链上空真，原文按 §105 保留）**：
见 §29 —— 异号半格（`det p vJ1 · det vJ vJ1 < 0`）在链上无构型。本节所有以异号为前提的
条目**语句仍正确、链上无实例**；链上真正在用的是同号那一支。

集成者 2026-09-26 派的新靶子（`bottom` 横截格账上唯一还挂着的那条）：

```
hslice : ∀ b ∈ S, 1 ≤ dot nJ (b - F.a) → z₀ + (b - F.a) ∈ reachSet Âinf vJ1
```

消费者是 `BottomReachMin.bottom_of_reachMin_merged` 的第五条 binder（按标识符名引），
`z₀` 由 `BottomFree.hdz_hz0_hline0_free` 给出。

### §27.1 原文给的理由（硬规矩 6 ①）

`scratch/b3_colle2.txt:520` 逐字：

> $\hat{A}_{i}^{(\epsilon)}:=\{g-t\vec{v}_{\boldsymbol{\ell}_{J+1}}\in\hat{A}^{(\epsilon)}_{\infty}
> :g\in\hat{A}_{i},\ t\in\mathbb{Z}_{+}\}$ **is an** $E(\mathcal{S}_{\varphi})$**-enveloped set**

而 `:519` 给的**理由**逐字是「for an appropriate $\epsilon\in\mathbb{N}$ fixed and **all**
$i\in\mathbb{N}$ **sufficiently large**」——即：原文不是对固定的 `i` 论证包络性，而是
**走到塔的深处**才拿到它。`reachSet` 里那个 `t ∈ ℤ₊` 的自由度（Lean 侧 `mem_reachSet` 的
`∃ t : ℕ`）与 `Âinf` 沿 `p`、`vJ` 的两向递归，正是「深处」在我们编码里的形。
⟹ 本节的机制**就是**原文那句的理由，不是另找的代用理由。

⚠ 符号：原文是 `g − t·v_{ℓ_{J+1}}`（减号），Lean 的 `reachSet T vJ1 = {g + t•vJ1}`；
两者的 `vJ1` 相差一个符号，这一格由上游 `NOTATION.md` 钉，本节不动它。

### §27.2 数值实例（硬规矩 6 ②）

取 `nJ = (0,1)`、`vJ = (1,0)`、`p = (0,1)`（则 `⟪nJ,vJ⟫ = 0`、`⟪nJ,p⟫ = 1 > 0`、
`det p vJ = -1 ≠ 0`，横截格由 `vJ1` 定）。

* `vJ1 = (1,-1)`：`det p vJ1 = -1`、`det vJ vJ1 = -1`，乘积 `= 1 > 0`（**同号半格**）。
  取 `x = (-1,1)`（高度 `⟪nJ,x⟫ = 1 ≥ 1`，落在 `hslice` 的守卫里）：
  `det p vJ * det p x = (-1)·1 = -1 < 0` ⟹ 锥条件二**不成立**，本节的归约到此为止。
* `vJ1 = (-1,-1)`：`det p vJ1 = 1`、`det vJ vJ1 = -1`，乘积 `= -1 < 0`（**异号半格**）。
  同一个 `x = (-1,1)`：沿 `vJ1` 退 `s` 步，`x - s•vJ1 = (-1+s, 1+s)`，
  两个锥条件是 `1+s ≥ 0` 与 `s-1 ≥ 0` ⟹ `s = 1` 就够；本节公式给的 `s = 2` 也合格。

⟹ 两半格的差别不是精度问题，是**机制在不在**。

### §27.3 机制

`z₀ ∈ reachSet T vJ1` 拆出 `z₀ = g₀ + t₀•vJ1`（`g₀ ∈ T`）。于是

* `z₀ + (b-a) = (g₀ + (b-a)) + t₀•vJ1`，只要 `g₀ + (b-a) ∈ T` 就结案；
* `T` 对 `+p`、`+vJ` 封闭且格凸 ⟹ `RecessionCone.mem_of_cone` 给 `g₀ + x ∈ T`，
  代价是两条行列式符号条件 `0 ≤ det p vJ * det x vJ` 与 `0 ≤ det p vJ * det p x`；
* **第一条白送**（`hb_cone_cond1_of_height`）：比例式
  `⟪nJ,p⟫·det x vJ = det p vJ·⟪nJ,x⟫`（在 `⟪nJ,vJ⟫ = 0` 上）＋ `⟪nJ,p⟫ > 0`
  把它化成 `⟪nJ,x⟫ ≥ 0`，而 `hslice` 的守卫 `1 ≤ ⟪nJ,(b−a)⟫` 更强。
* ⟹ **`hslice` 只剩第二条**（`hb_slice_of_cone`）。
* 异号半格里连第二条也免费（`hb_slice_free_of_det_mul_neg`）：此时可以先沿 `vJ1`
  **退** `s` 步再进锥，而 `det p vJ * det vJ1 vJ < 0` 与 `det p vJ * det p vJ1 < 0`
  两条同时成立，`s` 取够大就把两个符号条件一起压住。结论对**任意** `w` 成立，
  连高度守卫都不要。

`det p vJ * det vJ1 vJ < 0` 这一半是**无条件**的（`hb_det_vJ_vJ1_mul_pos`）：三向量恒等式
`det p vJ·⟪nJ,vJ1⟫ + det vJ vJ1·⟪nJ,p⟫ − det p vJ1·⟪nJ,vJ⟫ = 0` 在 `⟪nJ,vJ⟫ = 0` 上给
`det vJ vJ1·⟪nJ,p⟫ = −det p vJ·⟪nJ,vJ1⟫`，两个符号已知 ⟹ `det p vJ` 与 `det vJ vJ1` 同号。

### §27.4 与已有件的关系（`PROTOCOL §91` 披露）

* `ConeCover.dot_mul_det_sub`（集成者）是同一条比例式恒等式；`ConeCover` 传递地 import
  本文件，反向 import 成环 ⟹ 本节**独立重证、未 import**，两处都留。
* 本节的 `hb_det_vJ_vJ1_mul_pos` 与 lane-env-refute 的 `EnvRefuteOrient.dot_mul_det_swap`
  一族是同一批平面恒等式的不同切法；同样因成环不能 import。
* ⭐ **与 §26 / env-refute §34 的关系是互补，不是重复**：`EnvRefuteOrient.det_sign_of_supp`
  （lane-env-refute 报，本 lane 未复跑 ⟹ ②）证 `hsupp ⟹ 0 ≤ det vJ1 p * det vJ1 vJ`，
  即**异号半格里楔形的支撑界为假**；本节证**异号半格里 `hslice` 免费**。两条合起来是
  `hb_transverse_slice_wedge_dichotomy`：横截格的两条残余债
  （`hsupp` 与 `hslice`）在每半格里**恰好一条免费、另一条活着**。

  ⛔ **2026-09-26 当场更正（`PROTOCOL §57`；上段不删，§105）：「恰好一条免费」已腐烂。**
  lane-env-refute 同日又落 `EnvRefuteOrient.supp_of_same_sign`（②，本 lane 未复跑），
  证**同号半格里 `hsupp` 也免费**；再加本文件 §28 的 `rec_vJ_of_parts_same_sign`
  ⟹ 同号半格里免费的是**两条**（`hsupp` ＋ `rec_vJ`），活着的只有 `hslice` 的窗口符号条件。
  `hb_transverse_slice_wedge_dichotomy` 的**语句本身没有问题**（右支只陈述符号条件，
  不主张任何东西）——腐烂的只有这段散文。

  ⚠ **连接词实测（本 lane 亲读自己文件的签名，不是转述）**：`hsupp` **不是**
  `BottomReachMin.bottom_of_reachMin_merged` 的 binder，也不是 `BottomRoom.bottom_of_window` 的。
  两条合并形的 binder 逐字是 `hrecT` / `hdz` / `hz₀` / `hline0` / `hedge` / `hslice`（＝`hwin`），
  六条合取。`hsupp` 只出现在**`hline0` 的产者**那一层（`BottomRoom` 里带 `nprevJ` 的那族，
  以及集成者的 `BottomFree.hdz_hz0_hline0_free`）。
  ⟹ 异号半格里死掉的是**那个 `hline0` 产者**，不是合并形（`PROTOCOL §54`）：谁用不吃支撑界的
  机制产出 `hline0`，异号半格立刻复活，而那里 `hslice` 对任意 `w` 无条件免费、`hedge` 也免费，
  只剩 `hrecT` ＋ `hline0` 两条。异号半格的 `hrecT` 见 §28 的 `hb_not_sieve_of_opp_sign`：
  行列式筛这条路在那里**不可用**（`hsieve` 可证为假），要走 §25b 的 `hunb`。

### §27.5 射程自限（`PROTOCOL §50`）

* **没有证 `hslice` 为真**。同号半格里本节只给归约，剩下的符号条件
  `0 ≤ det p vJ * det p (b−a)` 是真 binder，且 `hb_slice_side_can_fail` 证它可以为假
  （⟹ 归约不是空谈，也不是隐形消债）。
* **没有证 `hslice` 为假**：符号条件失效只说明**锥这条路**不覆盖那个 `b`，
  `z₀ + (b−a)` 仍可能由别的机制落进 `reachSet`（`PROTOCOL §54`）。
* `hrecvJ`（`rec_vJ`）**不是字段**，本节链侧两条都把它写成显式 binder；横截格里它由
  `EnvRefuteOrient.rec_vJ_of_parts_of_det_ne`（按名引，`bottom`-free，②）供给。
* `0 < ⟪nJ,p⟫` 同样是显式 binder：字段 `dot_nJ_p` 只给 `≠ 0`，抬成正号的现货是
  `EnvRefuteOrient.dot_nJ_p_pos_of_parts`（按名引）—— 那个文件 import 本文件，
  本节不能 import 它，故把它留给消费者去合成。
* **不裁符号**：哪半格是"真实"那半格属于第 179 轮红线冻结的定向问题，本节两半都写到，
  不主张哪一半成立。 -/

/-- **比例式恒等式**：`⟪nJ,p⟫ · det x vJ − det p vJ · ⟪nJ,x⟫ = (p.2·x.1 − p.1·x.2) · ⟪nJ,vJ⟫`。

符号已按 50000 组随机整点核过（0 反例，故意写错的变体哨兵触发）。 -/
theorem hb_dot_mul_det_sub (nJ p vJ x : ℤ × ℤ) :
    dot nJ p * det x vJ - det p vJ * dot nJ x
      = (p.2 * x.1 - p.1 * x.2) * dot nJ vJ := by
  simp only [dot, det]
  ring

/-- ⭐ **锥条件一是白送的。**  `hslice` 的守卫 `1 ≤ ⟪nJ,(b−a)⟫` 比这里要的
`0 ≤ ⟪nJ,x⟫` 强，所以两条锥条件里只有第二条要付钱。 -/
theorem hb_cone_cond1_of_height {nJ p vJ x : ℤ × ℤ}
    (hperp : dot nJ vJ = 0) (hppos : 0 < dot nJ p) (hx : 0 ≤ dot nJ x) :
    0 ≤ det p vJ * det x vJ := by
  have hid := hb_dot_mul_det_sub nJ p vJ x
  rw [hperp, mul_zero] at hid
  have hkey : dot nJ p * det x vJ = det p vJ * dot nJ x := by linarith
  have hmul : dot nJ p * (det p vJ * det x vJ) = det p vJ * det p vJ * dot nJ x := by
    calc dot nJ p * (det p vJ * det x vJ)
        = det p vJ * (dot nJ p * det x vJ) := by ring
      _ = det p vJ * (det p vJ * dot nJ x) := by rw [hkey]
      _ = det p vJ * det p vJ * dot nJ x := by ring
  refine le_of_mul_le_mul_left ?_ hppos
  rw [mul_zero, hmul]
  exact mul_nonneg (mul_self_nonneg _) hx

/-- **三向量平面恒等式**（`det(p,vJ)·vJ1 + det(vJ,vJ1)·p + det(vJ1,p)·vJ = 0` 与 `nJ` 配对）。 -/
theorem hb_dot_det_triple (nJ p vJ vJ1 : ℤ × ℤ) :
    det p vJ * dot nJ vJ1 + det vJ vJ1 * dot nJ p - det p vJ1 * dot nJ vJ = 0 := by
  simp only [dot, det]
  ring

/-- ⭐ **`det p vJ` 与 `det vJ vJ1` 必定同号。**  只吃 `⟪nJ,vJ⟫ = 0`、`⟪nJ,p⟫ > 0`、
`⟪nJ,vJ1⟫ < 0`（后两条即字段 `dot_nJ_p` 抬正号后与 `hsweep`）＋ `det p vJ ≠ 0`，
**与格无关**。 -/
theorem hb_det_vJ_vJ1_mul_pos {nJ p vJ vJ1 : ℤ × ℤ}
    (hperp : dot nJ vJ = 0) (hppos : 0 < dot nJ p) (hsweep : dot nJ vJ1 < 0)
    (hdet : det p vJ ≠ 0) :
    0 < det p vJ * det vJ vJ1 := by
  have hid := hb_dot_det_triple nJ p vJ vJ1
  rw [hperp, mul_zero, sub_zero] at hid
  have hkey : det vJ vJ1 * dot nJ p = -(det p vJ * dot nJ vJ1) := by linarith
  have hmul : (det p vJ * det vJ vJ1) * dot nJ p
      = (det p vJ * det p vJ) * (-(dot nJ vJ1)) := by
    calc (det p vJ * det vJ vJ1) * dot nJ p
        = det p vJ * (det vJ vJ1 * dot nJ p) := by ring
      _ = det p vJ * (-(det p vJ * dot nJ vJ1)) := by rw [hkey]
      _ = (det p vJ * det p vJ) * (-(dot nJ vJ1)) := by ring
  have hrhs : 0 < (det p vJ * det p vJ) * (-(dot nJ vJ1)) :=
    mul_pos (mul_self_pos.mpr hdet) (by linarith)
  have hpos : 0 < (det p vJ * det vJ vJ1) * dot nJ p := by
    rw [hmul]
    exact hrhs
  by_contra hcon
  push_neg at hcon
  have hle : (det p vJ * det vJ vJ1) * dot nJ p ≤ 0 * dot nJ p :=
    mul_le_mul_of_nonneg_right hcon (le_of_lt hppos)
  rw [zero_mul] at hle
  linarith

/-- `det` 在右侧对 `w - s • v` 的展开。 -/
theorem hb_det_sub_zsmul_right (p w v : ℤ × ℤ) (s : ℤ) :
    det p (w - s • v) = det p w - s * det p v := by
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- `det` 在左侧对 `w - s • v` 的展开。 -/
theorem hb_det_sub_zsmul_left (w v u : ℤ × ℤ) (s : ℤ) :
    det (w - s • v) u = det w u - s * det v u := by
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- ⭐⭐ **`hslice` 归约成窗口上的一条符号条件。**

给了锥（格凸 ＋ `rec_p` ＋ `rec_vJ` ＋ `det p vJ ≠ 0`）与 `z₀ ∈ reachSet T vJ1`，
`hslice` 只剩 `hside`。注意 `hside` **不吃 `reachSet`、不吃 `T`**，纯粹是窗口 `W`
相对 `a` 的行列式符号 ⟹ 它是一条可以对具体 `S`／`F.a` 当场验算的条件。

⛔⛔ **`hside` 不是 `FaceBlock` 的推论（2026-09-26 内核反例，第 245 轮 ③(i)）。**
取 `W := S`、`a := F.a`，本条的 `hside` 逐字就是 `FaceBlock.gen` 的 `hstab` 前件所需的
那条符号条件。反例见证（`tmp/wip/hbase-window-cex.lean` 的 `not_window_sign_of_faceBlock`，
本 lane 内核验过、公理干净）：`S = {(0,0),(1,0),(-1,1)}`、`nJ = (0,1)`、`vJ = (1,0)`、
`vJ1 = (1,-1)`、`p = (0,1)`、`F.a = (0,0)`、`F.a' = (1,0)`、`F.r = 1`。
`FaceBlock` **十一条字段全真**（格凸性按凸包枚举证出），`a' = a + r • vJ`、`0 < r`、
`nJ`／`vJ` 本原、§27 四条符号前提（`⟪nJ,vJ⟫ = 0`、`0 < ⟪nJ,p⟫`、`⟪nJ,vJ1⟫ < 0`、
`det p vJ ≠ 0`）全真、链侧筛 `0 ≤ det p vJ · det p vJ1 = 1` 全真，
**且分格量 `det p vJ1 · det vJ vJ1 = 1 > 0`（同号活格，不是 §29 里那个链上空的异号格）**。
失效点 `b = (-1,1)`：高度 `⟪nJ, b - a⟫ = 1` 满足前件，而 `det p vJ · det p (b-a) = -1 < 0`。
⟹ **`hside` 的产者必须动用 `F` 之外的结构**（候选：`ahat_halfPlane_L`／`hswept`／`maxA`／
`S = S_φ` 这一层／`a := F.a` 这个配对本身）。
⚠ 射程（§54）：这**不**是「`hslice` 为假」。`ChainDataGeomParts` 的其余字段本条一条都没验，
那组数能否扩成完整的 `c` 也没验。定向不由本条裁定（第 179 轮冻结）：翻 `vJ` 会同时交换
`F.a ↔ F.a'` 并翻 `det p vJ` 的符号，失效的那一侧对称地翻过去。 -/
theorem hb_slice_of_cone {T : Set (ℤ × ℤ)} {W : Finset (ℤ × ℤ)}
    {nJ p vJ vJ1 z₀ a : ℤ × ℤ}
    (hconv : IsLatticeConvexRegion T)
    (hrecp : ∀ g ∈ T, g + p ∈ T) (hrecvJ : ∀ g ∈ T, g + vJ ∈ T)
    (hdet : det p vJ ≠ 0) (hperp : dot nJ vJ = 0) (hppos : 0 < dot nJ p)
    (hz₀ : z₀ ∈ reachSet T vJ1)
    (hside : ∀ b ∈ W, 1 ≤ dot nJ (b - a) → 0 ≤ det p vJ * det p (b - a)) :
    ∀ b ∈ W, 1 ≤ dot nJ (b - a) → z₀ + (b - a) ∈ reachSet T vJ1 := by
  intro b hb h1
  obtain ⟨g₀, hg₀, t₀, rfl⟩ := mem_reachSet.mp hz₀
  refine mem_reachSet.mpr ⟨g₀ + (b - a), ?_, t₀, by abel⟩
  exact Nivat.RecessionCone.mem_of_cone hconv hrecp hrecvJ hdet hg₀
    (hb_cone_cond1_of_height hperp hppos (by linarith)) (hside b hb h1)

/-- `reachSet` 的换基等式：把 `+w` 搬到 `T` 那一侧，代价是 `vJ1` 的步数从 `t` 涨到 `t + s`。 -/
theorem hb_reach_shift (g w v : ℤ × ℤ) (t s : ℤ) :
    g + t • v + w = g + (w - s • v) + (t + s) • v := by
  rw [add_smul, sub_eq_add_neg]
  abel

/-- ⭐⭐⭐ **异号半格：`hslice` 免费，而且对任意 `w` 成立**（连高度守卫都不要）。

机制：先沿 `vJ1` **退** `s` 步再进锥。`det p vJ * det vJ1 vJ < 0` 是无条件的
（`hb_det_vJ_vJ1_mul_pos`），`det p vJ * det p vJ1 < 0` 恰是 `hopp`；两条同时为负 ⟹
`s` 取够大就把两个锥条件一起压住。`s` 的显式取法是
`|det p vJ · det w vJ| + |det p vJ · det p w|`。

⚠ 这半格正是 lane-env-refute `EnvRefuteOrient.det_sign_of_supp` 判**支撑界为假**的那半格
（该条本 lane 未复跑，②）。⟹ 本条不能与那边的楔形产者串起来用，参见
`hb_transverse_slice_wedge_dichotomy`。

⛔ **§57 更正（2026-09-26 晚）：本条在链上空真**（`hopp` 在链侧前提域里无解，见 §29）。
语句不动、不删（§105），但**不要把它记成「异号半格的 `hslice` 债已还」**——那笔债本来就
不存在，因为那半格在链上是空的。链上还欠的是**同号**半格的窗口符号条件。

⛔ **集成者裁决要求的标注（2026-09-26，第 245 轮）**：前提 `det vJ1 p · det vJ1 vJ < 0`
在链上不可满足（`LeafAShellWedgeSign.det_sign_of_parts`）⟹ 本条对链上构型空真，
只对链外抽象数据有内容。详细理由链见 §28 的 `hb_not_sieve_of_opp_sign` 末段。 -/
theorem hb_slice_free_of_det_mul_neg {T : Set (ℤ × ℤ)} {nJ p vJ vJ1 z₀ : ℤ × ℤ}
    (hconv : IsLatticeConvexRegion T)
    (hrecp : ∀ g ∈ T, g + p ∈ T) (hrecvJ : ∀ g ∈ T, g + vJ ∈ T)
    (hdet : det p vJ ≠ 0) (hperp : dot nJ vJ = 0) (hppos : 0 < dot nJ p)
    (hsweep : dot nJ vJ1 < 0)
    (hopp : det p vJ1 * det vJ vJ1 < 0)
    (hz₀ : z₀ ∈ reachSet T vJ1) (w : ℤ × ℤ) :
    z₀ + w ∈ reachSet T vJ1 := by
  have hDG : 0 < det p vJ * det vJ vJ1 := hb_det_vJ_vJ1_mul_pos hperp hppos hsweep hdet
  have hGne : det vJ vJ1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hDG
    exact lt_irrefl 0 hDG
  -- `det p vJ * det p vJ1 < 0`
  have hDF : det p vJ * det p vJ1 < 0 := by
    have hG2 : 0 < det vJ vJ1 * det vJ vJ1 := mul_self_pos.mpr hGne
    have hprod : (det p vJ * det p vJ1) * (det vJ vJ1 * det vJ vJ1)
        = (det p vJ * det vJ vJ1) * (det p vJ1 * det vJ vJ1) := by ring
    by_contra hcon
    push_neg at hcon
    have h1 : 0 ≤ (det p vJ * det p vJ1) * (det vJ vJ1 * det vJ vJ1) :=
      mul_nonneg hcon (le_of_lt hG2)
    have h2 : (det p vJ * det vJ vJ1) * (det p vJ1 * det vJ vJ1) < 0 :=
      mul_neg_of_pos_of_neg hDG hopp
    rw [hprod] at h1
    linarith
  -- `det p vJ * det vJ1 vJ < 0`（无条件那一半）
  have hDE : det p vJ * det vJ1 vJ < 0 := by
    have he : det p vJ * det vJ1 vJ = -(det p vJ * det vJ vJ1) := by
      simp only [det]
      ring
    rw [he]
    linarith
  have hDE1 : det p vJ * det vJ1 vJ ≤ -1 := by
    have h := Int.lt_iff_add_one_le.mp hDE
    linarith
  have hDF1 : det p vJ * det p vJ1 ≤ -1 := by
    have h := Int.lt_iff_add_one_le.mp hDF
    linarith
  obtain ⟨g₀, hg₀, t₀, rfl⟩ := mem_reachSet.mp hz₀
  set s₀ : ℤ := |det p vJ * det w vJ| + |det p vJ * det p w| with hs₀
  have hs₀nn : 0 ≤ s₀ := by
    rw [hs₀]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hb1 : |det p vJ * det w vJ| ≤ s₀ := by
    rw [hs₀]
    have := abs_nonneg (det p vJ * det p w)
    linarith
  have hb2 : |det p vJ * det p w| ≤ s₀ := by
    rw [hs₀]
    have := abs_nonneg (det p vJ * det w vJ)
    linarith
  refine mem_reachSet.mpr ⟨g₀ + (w - s₀ • vJ1), ?_, t₀ + s₀.toNat, ?_⟩
  · refine Nivat.RecessionCone.mem_of_cone hconv hrecp hrecvJ hdet hg₀ ?_ ?_
    · rw [hb_det_sub_zsmul_left]
      have hexp : det p vJ * (det w vJ - s₀ * det vJ1 vJ)
          = det p vJ * det w vJ - s₀ * (det p vJ * det vJ1 vJ) := by ring
      rw [hexp]
      have hstep : s₀ * (det p vJ * det vJ1 vJ) ≤ s₀ * (-1) :=
        mul_le_mul_of_nonneg_left hDE1 hs₀nn
      have hneg : -(det p vJ * det w vJ) ≤ |det p vJ * det w vJ| :=
        neg_le_abs (det p vJ * det w vJ)
      linarith
    · rw [hb_det_sub_zsmul_right]
      have hexp : det p vJ * (det p w - s₀ * det p vJ1)
          = det p vJ * det p w - s₀ * (det p vJ * det p vJ1) := by ring
      rw [hexp]
      have hstep : s₀ * (det p vJ * det p vJ1) ≤ s₀ * (-1) :=
        mul_le_mul_of_nonneg_left hDF1 hs₀nn
      have hneg : -(det p vJ * det p w) ≤ |det p vJ * det p w| :=
        neg_le_abs (det p vJ * det p w)
      linarith
  · have hcast : ((t₀ + s₀.toNat : ℕ) : ℤ) = (t₀ : ℤ) + s₀ := by
      push_cast
      rw [Int.toNat_of_nonneg hs₀nn]
    rw [hcast]
    exact hb_reach_shift g₀ w vJ1 (t₀ : ℤ) s₀

/-- **链侧归约形。**  `hconv` / `rec_p` 由字段免费，`hrecvJ` 与 `hppos` 是显式 binder
（见 §27.5：两者在树里都有 `bottom`-free 的产者，但都在 import 本文件的文件里）。 -/
theorem hb_slice_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hppos : 0 < dot c.nJ p)
    (hrecvJ : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i)
    {W : Finset (ℤ × ℤ)} {z₀ a : ℤ × ℤ}
    (hz₀ : z₀ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1)
    (hside : ∀ b ∈ W, 1 ≤ dot c.nJ (b - a) → 0 ≤ det p c.vJ * det p (b - a)) :
    ∀ b ∈ W, 1 ≤ dot c.nJ (b - a) →
      z₀ + (b - a) ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1 :=
  hb_slice_of_cone (hb_latticeConvex_ahat_of_parts c) c.rec_p hrecvJ
    (hb_det_ne_zero_of_perp c.vJ_prim.ne_zero c.F.dot_nJ_vJ hppos.ne')
    c.F.dot_nJ_vJ hppos hz₀ hside

/-- **链侧异号半格形**：`hsweep` 也由字段免费，结论对任意 `w`。 -/
theorem hb_slice_free_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hppos : 0 < dot c.nJ p)
    (hrecvJ : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i)
    (hopp : det p c.vJ1 * det c.vJ c.vJ1 < 0)
    {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1) (w : ℤ × ℤ) :
    z₀ + w ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1 :=
  hb_slice_free_of_det_mul_neg (hb_latticeConvex_ahat_of_parts c) c.rec_p hrecvJ
    (hb_det_ne_zero_of_perp c.vJ_prim.ne_zero c.F.dot_nJ_vJ hppos.ne')
    c.F.dot_nJ_vJ hppos c.hsweep hopp hz₀ w

/-- ⭐⭐⭐ **横截格二分：两条残余债在每半格里恰好一条免费。**

左支（异号）：`hslice` 对任意 `w` 免费，**而且**两个合法旋转都不同时满足「定向 ＋ 支撑界」
（`hb_no_rot_admissible_of_det_mul_neg`，本文件 §26）⟹ 楔形那条死。
右支（同号）：本条**什么都不主张** —— 那里 `hslice` 的符号条件是真 binder
（`hb_slice_side_can_fail` 证它可以为假），楔形是否成立未知。

⛔ **2026-09-26 当场更正（`PROTOCOL §57`；上两段不删，§105）**：
(i) 抬头「恰好一条免费」与右支「楔形是否成立未知」**都已腐烂**。同号半格的 `hsupp` 由
lane-env-refute `EnvRefuteOrient.supp_of_same_sign` 证为免费（②，本 lane 未复跑），
`rec_vJ` 由本文件 §28 证为免费 ⟹ 右支活着的只剩 `hslice` 的窗口符号条件。
**语句本身不改**：右支只陈述符号条件，不主张任何东西，腐烂的是散文。
(ii) 左支的合取里两个旋转**只有一个有信息**：合法旋转由 `sign (det vJ1 vJ)` 唯一钉住
（lane-env-refute `dot_rotNeg_eq_neg_det` ＋ `exists_nprevJ`，②），另一个的第一项
（定向 `dot nprevJ vJ < 0`）本来就假、那一支空真。不影响正确性，但**别把它记成两份证据**。

三分里的 `= 0` 支被排除：`det p vJ1 ≠ 0`（横截格）且 `det vJ vJ1 ≠ 0`
（`hb_det_vJ_vJ1_mul_pos` 的推论）。

⛔ **§57 再更正（2026-09-26 晚）：本条的左支在链上走不到。** 见 §29 —— 分格量在链上恒
`≥ 0`，异号无构型。⟹ 这个「二分」在链上**退化成一支**：链上永远落在右支（同号），
左支的全部内容（`hslice` 免费 ＋ 楔形死）是空真的。语句正确、不删（§105），但记账上
**它不再是「两半格各有分工」，而是「链上只有同号半格，那里唯一活账是 `hslice`
的窗口符号条件」**。 -/
theorem hb_transverse_slice_wedge_dichotomy {α : Type*} {η xper : Config α}
    {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hppos : 0 < dot c.nJ p)
    (hrecvJ : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i)
    (hne1 : det p c.vJ1 ≠ 0)
    {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1) :
    ((∀ w : ℤ × ℤ, z₀ + w ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1) ∧
      (¬ (dot (c.vJ1.2, -c.vJ1.1) c.vJ < 0 ∧
          ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i,
            dot (c.vJ1.2, -c.vJ1.1) z ≤ dot (c.vJ1.2, -c.vJ1.1) V)) ∧
      (¬ (dot (-c.vJ1.2, c.vJ1.1) c.vJ < 0 ∧
          ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i,
            dot (-c.vJ1.2, c.vJ1.1) z ≤ dot (-c.vJ1.2, c.vJ1.1) V)))
    ∨ 0 < det p c.vJ1 * det c.vJ c.vJ1 := by
  rcases lt_trichotomy (det p c.vJ1 * det c.vJ c.vJ1) 0 with hlt | heq | hgt
  · refine Or.inl ⟨fun w => hb_slice_free_of_parts c hppos hrecvJ hlt hz₀ w, ?_, ?_⟩
    · exact (hb_no_rot_admissible_of_det_mul_neg c hlt).1
    · exact (hb_no_rot_admissible_of_det_mul_neg c hlt).2
  · exfalso
    have hDG : 0 < det p c.vJ * det c.vJ c.vJ1 :=
      hb_det_vJ_vJ1_mul_pos c.F.dot_nJ_vJ hppos c.hsweep
        (hb_det_ne_zero_of_perp c.vJ_prim.ne_zero c.F.dot_nJ_vJ hppos.ne')
    have hGne : det c.vJ c.vJ1 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hDG
      exact lt_irrefl 0 hDG
    exact mul_ne_zero hne1 hGne heq
  · exact Or.inr hgt

/-- **守卫（`PROTOCOL §86`）一**：归约剩下的符号条件**可以为假** ⟹ `hb_slice_of_cone`
不是隐形消债。数值是 §27.2 同号半格那组：`nJ = (0,1)`、`p = (0,1)`、`vJ = (1,0)`、
`x = (-1,1)`。 -/
theorem hb_slice_side_can_fail :
    (1 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (1 : ℤ)) ∧
      ¬ (0 ≤ det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))
            * det ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (1 : ℤ))) := by
  constructor
  · norm_num [dot]
  · norm_num [det]

/-- **守卫（`PROTOCOL §86`）二**：二分的**两半都由整点实现**，同一组 `nJ`/`p`/`vJ`
（`§27.2`）下只换 `vJ1`。⟹ `hb_transverse_slice_wedge_dichotomy` 两支都非空真。 -/
theorem hb_both_halves_realised :
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 ∧
      0 < dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ)) ∧
      (dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (-1 : ℤ)) < 0 ∧
        0 < det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (-1 : ℤ))
              * det ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (-1 : ℤ))) ∧
      (dot ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (-1 : ℤ)) < 0 ∧
        det ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (-1 : ℤ))
              * det ((1 : ℤ), (0 : ℤ)) ((-1 : ℤ), (-1 : ℤ)) < 0) := by
  refine ⟨by norm_num [dot], by norm_num [dot], ⟨by norm_num [dot], by norm_num [det]⟩,
    ⟨by norm_num [dot], by norm_num [det]⟩⟩

/-! ## §28  同号半格里 `hsieve` 免费 ⟹ 该半格的 `rec_vJ` 不经 `bottom`、也不经 `hunb`

来路：lane-env-refute 本轮报 §37「同号半格里 `hsupp` 是字段免费的」，我去核这半格还欠什么，
发现 §27 的 `hb_det_vJ_vJ1_mul_pos` 与同号条件相乘就把 §21.5 的 `hsieve` 平掉了：

`0 < det p vJ · det vJ vJ1`（§27，无条件）  ∧  `0 < det p vJ1 · det vJ vJ1`（同号半格）
⟹ 两式相乘 `= (det p vJ · det p vJ1) · (det vJ vJ1)²`，而 `(det vJ vJ1)² > 0`
⟹ `0 < det p vJ · det p vJ1` ＝ `hsieve`（严格形）。

⟹ **同号半格的 `rec_vJ` 只剩 `hα : 0 < ⟪nJ,p⟫` 一条 binder**（`hdpv1` 也由同号条件白送：
乘积非零 ⟹ 因子非零）。`hα` 由 lane-env-refute 的 `dot_nJ_p_pos_of_parts` 报为字段推论
（§55，本 lane 未复跑、且因成环无法 import）。证明体走 `rec_vJ_of_parts_nondeg_slim`，
链上零个 `c.bottom` ⟹ 这条**不在** `bottom ⟸ 覆盖 ⟸ rec_vJ ⟸ bottom` 那个环里，
也**不需要** §25b 的 `hunb`（`hunb` 仍是共线格的唯一出口，两条互不替代）。

⛔ 本节不主张哪一半为真：`det p vJ1 · det vJ vJ1` 的符号是第 179 轮冻结的定向量，
两半的可满足性见 §27 的 `hb_both_halves_realised`（两半都有整数见证）。本节只给蕴含式。 -/

/-- **同号 ⟹ `hsieve`（严格形）。**  无格、无 `Primitive`、无凸性：四条符号前提 ＋ 两条恒等式。 -/
theorem hb_sieve_of_same_sign {nJ p vJ vJ1 : ℤ × ℤ}
    (hperp : dot nJ vJ = 0) (hppos : 0 < dot nJ p) (hsweep : dot nJ vJ1 < 0)
    (hdet : det p vJ ≠ 0) (hsame : 0 < det p vJ1 * det vJ vJ1) :
    0 < det p vJ * det p vJ1 := by
  have h1 : 0 < det p vJ * det vJ vJ1 :=
    hb_det_vJ_vJ1_mul_pos hperp hppos hsweep hdet
  have hGne : det vJ vJ1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact lt_irrefl 0 h1
  have hG2 : 0 < det vJ vJ1 * det vJ vJ1 := mul_self_pos.mpr hGne
  have hprod : 0 < (det p vJ * det vJ vJ1) * (det p vJ1 * det vJ vJ1) := mul_pos h1 hsame
  have hre : (det p vJ * det vJ vJ1) * (det p vJ1 * det vJ vJ1)
      = (det p vJ * det p vJ1) * (det vJ vJ1 * det vJ vJ1) := by ring
  rw [hre] at hprod
  by_contra hcon
  have hle : det p vJ * det p vJ1 ≤ 0 := not_lt.mp hcon
  have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hG2)
  rw [zero_mul] at hmul
  linarith

/-- ⭐ **链侧收口：同号半格里 `rec_vJ` 只吃 `hα`。**

前提逐条来路：`hperp = c.F.dot_nJ_vJ`（字段）、`hsweep = c.hsweep`（字段，`ChainPartsFeed`
结构里那条 `dot nJ vJ1 < 0`）、`det p c.vJ ≠ 0` 由 §23 `hb_det_ne_zero_of_perp`
（`c.vJ_prim.ne_zero` ＋ 字段 ＋ `hα.ne'`）、`hdpv1` 由 `hsame` 的非零性。
格凸性与载体由 `rec_vJ_of_parts_nondeg` 一路供给。

原文锚：`scratch/b3_colle2.txt:506`「Actually, $\hat{A}_{\infty}$ is an
$(\boldsymbol{\ell},\boldsymbol{\ell}_{J})$-region」——结论量词 `∀ g ∈ ⋃ i, hatOf …,
g + c.vJ ∈ ⋃ i, hatOf …` 就是该句的 `ℓ_J` 方向封闭性；本条给的是其中一格的证明，
`hsame` 没有原文对应物，它是**分格**用的辅助符号条件，不是新加的量词。

⛔ **§57／§91 更正（2026-09-26 晚）：本条是既有声明的特例，不要给它接线。**
lane-env-refute 的 `EnvRefuteOrient.rec_vJ_of_parts_of_det_ne` 结论逐字相同，前提只有
`det p c.vJ1 ≠ 0` —— **不吃 `hα`、不吃同号**。本 lane 亲读了那条的语句与证明体
（`PROTOCOL §131`）：它走 `exists_pos_scale_of_parts` ＋ 本文件
`rec_vJ_of_W₀_pos_multiple`，实参里有 `dot_nJ_p_pos_of_parts c`（所以 `hα` 在那边是字段推论，
不是 binder），直接实参中**没有 `c.bottom`**（`exists_pos_scale_of_parts` 内部本 lane 未追）。
而本条的 `hsame : 0 < det p c.vJ1 · det c.vJ c.vJ1` 蕴含 `det p c.vJ1 ≠ 0`
⟹ **本条严格弱**。结论：此前挂在集成者那儿的「谁来落 `hα` 接线」那个问题**撤销**，
不需要任何接线；本条保留（§105 删号留名）仅作为「同号半格里 det 筛子免费」这条算术事实的
记录，链上请用 env-refute 那条。去重照旧归集成者（`PROTOCOL §110.2`）。

⛔ **集成者补记（2026-09-26，第 245 轮）**：集成者亲读 `rec_vJ_of_parts_of_det_ne`，确认
前提逐字只有 `(c) (hne1 : det p c.vJ1 ≠ 0)`，**且 `hα` 在其证明体内部由
`dot_nJ_p_pos_of_parts` 自产** ⟹ 「谁来落 `hα` 接线」这道题**整条消失**，
lane-env-refute 回绝接线是对的，集成者也不落。本 lane 自曝：漏掉这条现货**不是**射程所限
——按 `PROTOCOL §58` 跑一次结论型 grep（`\+ c\.vJ ∈`，`Nivat` 下 10 个文件命中，
其中 `EnvRefuteOrient.lean` 十处）当场就会撞上它；漏的是一次该跑而没跑的搜索。
import 方向只决定本文件**不能拿它当证据用**（真环），不决定能不能看见。 -/
theorem rec_vJ_of_parts_same_sign {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainDataGeomParts η xper vl p S gen)
    (hα : 0 < dot c.nJ p)
    (hsame : 0 < det p c.vJ1 * det c.vJ c.vJ1) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i := by
  have hdpv : det p c.vJ ≠ 0 :=
    hb_det_ne_zero_of_perp c.vJ_prim.ne_zero c.F.dot_nJ_vJ hα.ne'
  have hdpv1 : det p c.vJ1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hsame
    exact lt_irrefl 0 hsame
  exact rec_vJ_of_parts_nondeg_slim c hα hdpv1
    (le_of_lt (hb_sieve_of_same_sign c.F.dot_nJ_vJ hα c.hsweep hdpv hsame))

/-- ⭐ **镜像：异号半格里 `hsieve` 可证为假 ⟹ 行列式筛这条 `rec_vJ` 路在那里不可用。**

同一个乘法，另一个方向：`0 < det p vJ · det vJ vJ1`（§27，无条件）× `det p vJ1 · det vJ vJ1 < 0`
（异号）⟹ `(det p vJ · det p vJ1)·(det vJ vJ1)² < 0` ⟹ `det p vJ · det p vJ1 < 0`。

⚠ 这**不是**「异号半格 `rec_vJ` 为假」（`PROTOCOL §54`）：`hsieve` 只是
`rec_vJ_of_parts_nondeg_slim` 的一条 binder，证它为假只说明**那条引理在该半格用不上**，
`rec_vJ` 仍可由别的机制得到 —— 树里现成的另一条入口是 §25b 的 `hunb`
（`rec_vJ_of_parts_unbounded_line'`），它不吃任何行列式符号。
⟹ 记账上：`hunb` 的适用格是**共线格 ＋ 异号半格**两格，不是只有共线格。

⛔ 同日补记（§57）：适用格是两格，但**共线格那格的 `hunb` 槽位已被 lane-tower-hlev
内核证「二十条几何前提喂不上」**（`TowerHlevCover.not_unbounded_along_vJ_of_geom_bundle`，②，
详见 §25b 的更正段）。他们的见证是共线的（分格量 `= 0`）⟹ **异号半格未被触及**，
那里 `hunb` 仍是本文件已知的唯一入口。

⛔⛔ **§57 再更正（2026-09-26 晚，上面两段的结论全部作废，原文按 §105 留在上面）：
本条在链上空真。** 见 §29：`hopp`（异号）在链上无解 —— `0 ≤ det p vJ · det p vJ1`
（lane-env-refute 的 `EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg`，只吃 `c`，②）
配本文件 `hb_det_vJ_vJ1_mul_pos` ⟹ 分格量恒 `≥ 0`。⟹ 三件事同时更正：
(1) **语句仍然正确**（纯符号算术，无链假设），但**对链上构型没有实例**；
(2) 「`hunb` 的适用格是两格」**改回「只有共线格」**——本 lane 2026-09-26 早些时候据此给
lane-tower-hlev 发过一次「适用格扩到两格」的更正，那次更正**本 lane 已撤回**，他们原先的
读数（只有共线格）才是对的；
(3) 由 (1)(2) 得：`hunb` 的唯一适用格恰是被 hlev 打掉的那一格 ⟹ **本文件这条 `rec_vJ`
入口在链上已无剩余用武之地**，别再把它记成活路线。
这次是本 lane 自己撞上团队新判据的反面：`PROTOCOL §110.4`／集成者 2026-09-25 裁决
——「核结论形状不够，必须核前提在自己的前提域里可不可满足」。本条的 `hopp`
从未在链侧前提域里核过，所以一路记成了活格。

⛔ **集成者裁决要求的标注（2026-09-26，第 245 轮）**：前提 `det vJ1 p · det vJ1 vJ < 0`
在链上不可满足（`LeafAShellWedgeSign.det_sign_of_parts`）⟹ 本条对链上构型空真，
只对链外抽象数据有内容。理由链（集成者亲读过证明体，只吃 `ChainDataGeomParts` 字段）：
`det_sign_of_parts` = `dot_mul_det_swap` ＋ `EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg`
＋ `hsweep` ⟹ 链上恒有 `0 ≤ det vJ1 p · det vJ1 vJ`；再配 `det vJ1 vJ ≠ 0` ⟹
**链上只有共线格与同号格两种情形**。本 lane 的 `hb_cell_nonneg_of_sieve_nonneg`（§29）
是同一事实的、把链侧不等式留成显式 binder `hchain` 的形式（本文件不能 import
`EnvRefuteOrient`——真环），三方（本 lane／lane-env-refute／lane-tower-hlev）读数一致。
⚠ 语句不删（§105）：对链外抽象数据仍有内容。 -/
theorem hb_not_sieve_of_opp_sign {nJ p vJ vJ1 : ℤ × ℤ}
    (hperp : dot nJ vJ = 0) (hppos : 0 < dot nJ p) (hsweep : dot nJ vJ1 < 0)
    (hdet : det p vJ ≠ 0) (hopp : det p vJ1 * det vJ vJ1 < 0) :
    det p vJ * det p vJ1 < 0 := by
  have h1 : 0 < det p vJ * det vJ vJ1 :=
    hb_det_vJ_vJ1_mul_pos hperp hppos hsweep hdet
  have hGne : det vJ vJ1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact lt_irrefl 0 h1
  have hG2 : 0 < det vJ vJ1 * det vJ vJ1 := mul_self_pos.mpr hGne
  have hprod : (det p vJ * det vJ vJ1) * (det p vJ1 * det vJ vJ1) < 0 :=
    mul_neg_of_pos_of_neg h1 hopp
  have hre : (det p vJ * det vJ vJ1) * (det p vJ1 * det vJ vJ1)
      = (det p vJ * det p vJ1) * (det vJ vJ1 * det vJ vJ1) := by ring
  rw [hre] at hprod
  by_contra hcon
  have hge : 0 ≤ det p vJ * det p vJ1 := not_lt.mp hcon
  have hmul := mul_le_mul_of_nonneg_right hge (le_of_lt hG2)
  rw [zero_mul] at hmul
  linarith

/-- 上条的 `¬ (0 ≤ …)` 形，直接对上 `rec_vJ_of_parts_nondeg_slim` 的 `hsieve` 槽。

⛔ **集成者裁决要求的标注（2026-09-26，第 245 轮）**：前提 `det vJ1 p · det vJ1 vJ < 0`
在链上不可满足（`LeafAShellWedgeSign.det_sign_of_parts`）⟹ 本条对链上构型空真，
只对链外抽象数据有内容。详细理由链见上条 `hb_not_sieve_of_opp_sign` 的末段。
⚠ 语句不删（§105）。 -/
theorem hb_sieve_unusable_of_opp_sign {nJ p vJ vJ1 : ℤ × ℤ}
    (hperp : dot nJ vJ = 0) (hppos : 0 < dot nJ p) (hsweep : dot nJ vJ1 < 0)
    (hdet : det p vJ ≠ 0) (hopp : det p vJ1 * det vJ vJ1 < 0) :
    ¬ (0 ≤ det p vJ * det p vJ1) :=
  not_le.mpr (hb_not_sieve_of_opp_sign hperp hppos hsweep hdet hopp)

/-! ## §29 异号半格在链上是空的：分格量在链上恒 `≥ 0`

⭐⭐⭐ **本节推翻本文件此前把「异号半格」当成活格的全部记账**（`PROTOCOL §57`，原文按 §105
保留在各条 docstring 里）。

算术只有一步。记 `a = det p vJ`、`b = det p vJ1`、`G = det vJ vJ1`，分格量是 `b·G`：

* 本文件 `hb_det_vJ_vJ1_mul_pos` 无链假设地给 `0 < a·G`（前提：`⟪nJ,vJ⟫ = 0`、`0 < ⟪nJ,p⟫`、
  `⟪nJ,vJ1⟫ < 0`、`a ≠ 0`）。
* lane-env-refute 的 `EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg` 只吃 `c`，给 `0 ≤ a·b`。
* 相乘：`a²·(b·G) = (a·G)·(a·b) ≥ 0`，而 `a ≠ 0` ⟹ `a² > 0` ⟹ **`0 ≤ b·G`**。

⟹ `b·G < 0`（异号半格）在链上**不可能**，任何以异号为前提的命题在链上**空真**。

**数值实例（`Nivat.CLAUDE.md` 硬规矩 6，本 lane 自算）**：`nJ=(0,1)`、`vJ=(1,0)`、`vJ1=(0,-1)`、
`p=(-1,1)` 满足本节四条符号前提且 `b·G = -1 < 0`（异号），但 `a·b = -1 < 0`
⟹ 与 `det_p_vJ_mul_det_p_vJ1_nonneg` 冲突 ⟹ 链外。另外在 `|a|,|b|,|G| ≤ 4` 上穷举：
本节结论 0 个反例，故意写错的形（`b·G ≤ 0`）128 个反例 ⟹ 哨兵会响（`PROTOCOL §86`）。

⚠ **归属（`PROTOCOL §55`）**：`det_p_vJ_mul_det_p_vJ1_nonneg` 是 lane-env-refute 报的，本 lane
**亲读了它的语句与证明体**（`PROTOCOL §131`）——形参只有 `c`，证明体走
`no_lower_bound_of_swept`，实参是 `c.ahat_nonempty` / `c.rec_p` / `c.hswept` /
`dot_nJ_p_pos_of_parts c` / `c.ahat_halfPlane_L`，**不经 `c.bottom`**；但本 lane 未复跑其
`check1.sh`、也未 import（`EnvRefuteOrient` 是本文件的下游，import 即成环）。因此下面这条
把 `0 ≤ a·b` 留成显式 binder `hchain`：在本文件里它是假设，在下游才由字段兑现。

⚠ **2026-09-26 受力位置变更（`PROTOCOL §91`，本段不删上文、另起，§105）：本节退为旁证。**
主仓 `LeafAShellWedgeSign.det_sign_of_parts` 只吃 `c : ChainDataGeomParts …`，
直接给 `0 ≤ det c.vJ1 p · det c.vJ1 c.vJ`，而那与本节结论**是同一个不等式**
（翻号相消，内核件 `hb_det_swap_cell_eq`）。⟹ 异号半格为空这件事的**受力件唯一**，
是 `det_sign_of_parts`；本节 `hb_cell_nonneg_of_sieve_nonneg` 此后只当**binder 形旁证**
（链外可用、不收 `ChainDataGeomParts`）。⛔ 但本 lane 亲读其证明体后确认：
那条**不是独立的第二条证明**，它吃的是与本节**同一组四个输入**。逐条对照见 §30。 -/
theorem hb_cell_nonneg_of_sieve_nonneg {nJ p vJ vJ1 : ℤ × ℤ}
    (hperp : dot nJ vJ = 0) (hppos : 0 < dot nJ p) (hsweep : dot nJ vJ1 < 0)
    (hdet : det p vJ ≠ 0) (hchain : 0 ≤ det p vJ * det p vJ1) :
    0 ≤ det p vJ1 * det vJ vJ1 := by
  have h1 : 0 < det p vJ * det vJ vJ1 :=
    hb_det_vJ_vJ1_mul_pos hperp hppos hsweep hdet
  have ha2 : 0 < det p vJ * det p vJ := mul_self_pos.mpr hdet
  have hprod : 0 ≤ (det p vJ * det vJ vJ1) * (det p vJ * det p vJ1) :=
    mul_nonneg (le_of_lt h1) hchain
  have hre : (det p vJ * det vJ vJ1) * (det p vJ * det p vJ1)
      = (det p vJ * det p vJ) * (det p vJ1 * det vJ vJ1) := by ring
  rw [hre] at hprod
  by_contra hcon
  have hneg : det p vJ1 * det vJ vJ1 < 0 := not_le.mp hcon
  have hlt : (det p vJ * det p vJ) * (det p vJ1 * det vJ vJ1) < 0 :=
    mul_neg_of_pos_of_neg ha2 hneg
  linarith

/-- **上条的直接否定形**：链上没有异号半格的构型。
配合 `hb_det_ne_zero_of_perp` 与字段 `F.dot_nJ_vJ` / `hsweep` / `vJ_prim`，下游只要再有
`0 < ⟪nJ,p⟫` 与 `0 ≤ det p vJ · det p vJ1` 两条链侧现货就能把这条实例化成「异号不存在」。 -/
theorem hb_not_opp_sign_of_sieve_nonneg {nJ p vJ vJ1 : ℤ × ℤ}
    (hperp : dot nJ vJ = 0) (hppos : 0 < dot nJ p) (hsweep : dot nJ vJ1 < 0)
    (hdet : det p vJ ≠ 0) (hchain : 0 ≤ det p vJ * det p vJ1) :
    ¬ (det p vJ1 * det vJ vJ1 < 0) :=
  not_lt.mpr (hb_cell_nonneg_of_sieve_nonneg hperp hppos hsweep hdet hchain)

/-- **§29.1 哨兵：`hchain` 不可删。**

去掉 `0 ≤ det p vJ · det p vJ1` 之后结论为假：`nJ=(0,1)`、`vJ=(1,0)`、`vJ1=(0,-1)`、`p=(-1,1)`
满足 `⟪nJ,vJ⟫ = 0`、`0 < ⟪nJ,p⟫`、`⟪nJ,vJ1⟫ < 0`、`det p vJ ≠ 0` 四条，而
`det p vJ1 · det vJ vJ1 = -1 < 0`。⟹ 「异号为空」**纯靠那条链侧不等式**，不是符号记账；
本文件 §27／§28 的符号前提单独推不出它（`PROTOCOL §86`：会失败的检查）。 -/
theorem hb_cell_nonneg_needs_chain_input :
    dot ((0:ℤ),(1:ℤ)) ((1:ℤ),(0:ℤ)) = 0 ∧
      0 < dot ((0:ℤ),(1:ℤ)) ((-1:ℤ),(1:ℤ)) ∧
      dot ((0:ℤ),(1:ℤ)) ((0:ℤ),(-1:ℤ)) < 0 ∧
      det ((-1:ℤ),(1:ℤ)) ((1:ℤ),(0:ℤ)) ≠ 0 ∧
      det ((-1:ℤ),(1:ℤ)) ((0:ℤ),(-1:ℤ)) * det ((1:ℤ),(0:ℤ)) ((0:ℤ),(-1:ℤ)) < 0 ∧
      det ((-1:ℤ),(1:ℤ)) ((1:ℤ),(0:ℤ)) * det ((-1:ℤ),(1:ℤ)) ((0:ℤ),(-1:ℤ)) < 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [dot, det]

/-- **§28.1 子格收据：同号半格的两个子格都落在 §28 的前提域里。**

lane-env-refute 2026-09-26 自行更正：他们的「同号」`0 < det vJ1 p · det vJ1 vJ` 有两个子格
（两个 `det` 同正 / 同负），§37 当时只覆盖同正那个，同负子格由他们 §38
`supp_of_same_sign_neg` 补齐（②，本 lane 未复跑）。

**这次更正不触及本文件 §28**：`hb_sieve_of_same_sign` / `rec_vJ_of_parts_same_sign`
只用**乘积** `0 < det p vJ1 · det vJ vJ1`，从不拆两个因子各自的符号 ⟹ 两个子格自动都在。
本条是那句话的内核收据：两个见证都满足 §27／§28 的全部符号前提，只在
`det vJ1 vJ` 的符号上相反。

见证（本 lane 先用整数算过再写 Lean，硬规矩 6②；乘积恒等式
`det vJ1 p · det vJ1 vJ = det p vJ1 · det vJ vJ1` 在两个见证上都取 `1`，故意写错符号的
对照式取 `-1`，哨兵触发）：
* 同正：`nJ=(0,1)`、`vJ=(1,0)`、`vJ1=(0,-1)`、`p=(1,1)`，`det vJ1 vJ = 1`；
* 同负：`nJ=(0,1)`、`vJ=(-1,0)`、`vJ1=(0,-1)`、`p=(-1,1)`，`det vJ1 vJ = -1`
  （这条是 lane-env-refute 给的见证，本 lane 独立复算后采用）。

⚠ 这是**可满足性**收据，不是链上存在性：见证是裸整数，没有声称某个
`ChainDataGeomParts` 实例取到它们（集成者 2026-09-26 的判据订正：核见证要逐条对字段，
而本条根本不主张字段侧的事）。 -/
theorem hb_same_sign_subcells_realised :
    (dot ((0, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) = 0 ∧
      0 < dot ((0, 1) : ℤ × ℤ) ((1, 1) : ℤ × ℤ) ∧
      dot ((0, 1) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) < 0 ∧
      det ((1, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) ≠ 0 ∧
      0 < det ((1, 1) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) * det ((1, 0) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) ∧
      0 < det ((0, -1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ)) ∧
    (dot ((0, 1) : ℤ × ℤ) ((-1, 0) : ℤ × ℤ) = 0 ∧
      0 < dot ((0, 1) : ℤ × ℤ) ((-1, 1) : ℤ × ℤ) ∧
      dot ((0, 1) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) < 0 ∧
      det ((-1, 1) : ℤ × ℤ) ((-1, 0) : ℤ × ℤ) ≠ 0 ∧
      0 < det ((-1, 1) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) * det ((-1, 0) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) ∧
      det ((0, -1) : ℤ × ℤ) ((-1, 0) : ℤ × ℤ) < 0) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    norm_num [dot, det]

/-! ## §30 `PROTOCOL §91` 披露：异号半格的受力件换成主仓一条，本文件 §29 退为旁证

集成者队列 ③。**本节不改任何已落声明的语句**，只登记受力位置的变更（§105：旧账不删，另起）。

### §30.1 新的受力件

`LeafAShellWedgeSign.det_sign_of_parts`（按标识符引，`PROTOCOL §124`）：形参只有
`c : ChainDataGeomParts η xper vl p S gen`，结论 `0 ≤ det c.vJ1 p · det c.vJ1 c.vJ`。
lane-tower-hlev 2026-09-26 报为「主仓现货、无额外前提」；**本 lane 亲读了它的语句与证明体**
（`PROTOCOL §131`），未 import（`LeafAShellWedgeSign` 传递地 import 本文件，反向即成环）。

### §30.2 ⛔ 它**不是**独立的第二条证明 —— 这正是 §91 要拦的那种记账

亲读的结果：`det_sign_of_parts` 的证明体逐字用了

* `EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg c` ——＝本文件 §29 的 binder `hchain`；
* `EnvRefuteOrient.dot_nJ_p_pos_of_parts c`        ——＝ `hppos`；
* `c.hsweep`                                       ——＝ `hsweep`；
* `c.F.dot_nJ_vJ`                                  ——＝ `hperp`；
* `EnvRefuteOrient.dot_mul_det_swap` 的平面恒等式   ——＝本文件 `hb_dot_det_triple` 的另一切法。

⟹ 两条吃的是**同一组四个输入**，差别只在打包方式（字段形 vs binder 形）。按 §91
「把两个 ③ 包成一个 ③ 是负收益」：**异号半格为空是一件事，不是两件、更不是三件。**
⟹ 记账口径：受力件唯一，是 `det_sign_of_parts`；lane-tower-hlev 的 `opp_sign_cell_empty`
与 lane-env-refute 的同结论件都不落（他们已如此裁），本文件 §29 退为 binder 形旁证。
⚠ 本 lane 未复跑 `det_sign_of_parts` 的 `check1.sh`，按 `PROTOCOL §55` 该条编译状态记作
「lane-tower-hlev 报」；**亲读的是证明体的实参表，那一条是本 lane 自己读的**（§131）。

### §30.3 `PROTOCOL §113`：两个方向各自多什么（不许只报一边弱）

* `det_sign_of_parts` 比 §29 多：不收 `hdet : det p vJ ≠ 0`。
* §29 比 `det_sign_of_parts` 多：**不收 `ChainDataGeomParts`**，四条前提全是裸向量上的
  binder ⟹ 可在链外、在只有符号假设的上下文里用 —— 本文件 §27／§28 正是这样用的。

⚠ 且第一条那个「多」几乎是空的，本 lane 当场算过（硬规矩 6②）：`dot nJ vJ = 0` ＋
`0 < dot nJ p` 下，`vJ ≠ 0` 就必有 `det p vJ ≠ 0`（否则 `p ∥ vJ` ⟹ `dot nJ p = 0`，
与 `0 < dot nJ p` 冲突），而链上 `vJ ≠ 0` 由 `vJ_prim` 免费，本文件亦有
`hb_det_ne_zero_of_perp`。⟹ 去掉 `hdet` 新增的实例**只有 `vJ = 0` 这一个退化格**，
而那一格结论 `det p vJ1 · det vJ vJ1 = det p vJ1 · 0 = 0` 平凡成立。
**⟹ 本 lane 因此不落「去 `hdet` 的加强版」**：净内容为零，正是 §91 要拦的重复件。

### §30.4 唯一真缺的件是**翻译**，不是不等式

树里两种写法并存：主仓 `EnvRefuteOrient` / `LeafAShellWedgeSign` / `LeafAShellBottomParts` /
`BottomFree` 写 `det vJ1 p · det vJ1 vJ`，本文件 §27–§29 写 `det p vJ1 · det vJ vJ1`。
本 lane 按 `PROTOCOL §58` 做了**结论型**全树搜索（`grep -rE` 于 `Nivat/**.lean`，命中 20 行，
分母＝全部两式并存的行）：命中全是散文或单侧语句，**「这两式相等」树里没有内核件**
（本文件 §28.1 的 docstring 也只在两个具体见证上各取了一个数，是实例不是恒等式）。
⟹ 本节补的就是这一条，且只补这一条。
-/

/-- ⭐ **两种写法逐字相等**：`det vJ1 p · det vJ1 vJ = det p vJ1 · det vJ vJ1`。

两个因子各翻一次号，号相消。⟹ 主仓 `LeafAShellWedgeSign.det_sign_of_parts` 的结论与本文件
§29 的结论**是同一个不等式**，下游一次 `rw` 即可互换（§30.4）。

纯恒等式，**不含任何符号判断**：第 179 轮定向冻结管的是「裁 `det p vJ1 · det vJ vJ1` 的号」，
本条只说两个写法相等，不裁号。 -/
theorem hb_det_swap_cell_eq (p vJ vJ1 : ℤ × ℤ) :
    det vJ1 p * det vJ1 vJ = det p vJ1 * det vJ vJ1 := by
  simp only [det]
  ring

/-- **§30.5 哨兵（`PROTOCOL §86`）：上条不是「怎么换序都成立」。**

只翻**一个**因子的那一式为假。见证 `p=(1,0)`、`vJ=(0,1)`、`vJ1=(1,1)`：
`det vJ1 p = -1`、`det p vJ1 = 1`、`det vJ vJ1 = -1`、`det vJ1 vJ = 1`
⟹ 上条两边同为 `-1`（真），而只翻左因子的那式左边 `(-1)·(-1) = 1`、右边 `1·(-1) = -1`
⟹ `1 ≠ -1`，哨兵响。 -/
theorem hb_det_swap_cell_eq_sentinel :
    det ((1, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) * det ((0, 1) : ℤ × ℤ) ((1, 1) : ℤ × ℤ)
      ≠ det ((1, 0) : ℤ × ℤ) ((1, 1) : ℤ × ℤ) * det ((0, 1) : ℤ × ℤ) ((1, 1) : ℤ × ℤ) := by
  norm_num [det]

/-! ## §31 窗口符号条件与支撑条件是**等价**的，不只是被它蕴含

### §31.1 本节回答的问题

`b3_colle2.txt:790` 那一步要的窗口符号条件（本文件 §? 的真 binder 形，
`0 ≤ det p vJ * det p (b − a)`）此前只有**单向**的判据：`tmp/wip/hbase-vl-orient.lean` 的
`window_sign_of_supp`（支撑 ⟹ 窗口）。单向形留下一个定价问题没答：**有没有比支撑条件更弱的
前提也能推出窗口条件？** 若有，本 lane 的残债（「`FaceBlock` 的 `a` 恰是 `n` 的支撑点」）就
可以绕开；若没有，那条残债是**不可约**的，必须由链上供给。

本节把它钉死在**等价**上：只要那个常因子严格负（`det vl vJ < 0`，即非退化支），
窗口条件与支撑条件**逐点互推**。⟹ 绕不开。

### §31.2 为什么只需要 `det`，不需要 `n` / `rot` / `perpVec`

窗口量是两个因子的积，其中**第一个因子与 `b` 无关**。固定符号后，
`0 ≤ c · d ↔ d ≤ 0`（`c < 0`）是纯序环事实，与「`vl` 是谁的垂直方向」无关。
⟹ 本节不引 `rot`（那条在 `tmp/wip/hbase-vl-orient.lean` 里，`tmp` 不进 build）、
也不引 `EnvRefuteOrient` 的 `dot_perpVec_eq_det`（`EnvRefuteOrient.lean` **import 本文件**，
反向引就成环，并行协议第 2 条）。`det vl (b − a) ≤ 0` 本身就是 `vl`-法向形的支撑条件：
在 `vl = t • rot n`、`0 < t` 下它逐字等于 `dot n b ≤ dot n a`，但那条翻译**不是本节的义务**。

### §31.3 `PROTOCOL §113`：两个方向各自多什么

* 正向（支撑 ⟹ 窗口）：`window_sign_of_supp` 只要 `det vl vJ ≤ 0`（非严格），
  退化支 `det vl vJ = 0` 也成立（两边同为 0）。
* 本节（等价）：**多要** `det vl vJ < 0` 严格。少了严格性等价为假 ——
  `hb_window_iff_needs_strict` 是那个反例（`det vl vJ = 0` 时左边恒真、右边可假）。
⟹ 本节不是 `window_sign_of_supp` 的推广，是它在**非退化支上的加强到等价**；
两条都留，各有自己的适用域。

### §31.4 本轮台架读数（`PROTOCOL §54`：台架不是链上）

本 lane 第 251 轮 Python 台架（`tmp/_hb_r251_pinned.py`，脚本打了 `INPUT:` 行与枚举域）：
`n` 按链上约束**钉在 `p` 上**（`p = -c • vl`、`vl = t • rot n` ⟹ `n ∥ (p.2, -p.1)`，两个符号），
分母 129408 个带 `FaceBlock` 的 `(gens, nJ, vJ, p, sign)` 组，其中 `hsupp ∧ hvJ` 同时成立
28072 组、其中 `dot n vJ < 0` **严格**（非退化）20688 组，而这 20688 组里窗口条件
**全部成立、0 例外**。⟹ 两件事：
(a) 判据**不落空真支**（集成者对全员的硬守卫：任何「加了某条件就杀掉见证」的主张都要报见证）——
    非退化实例有 20688 个，不是 0；
(b) 台架与本节等价形一致，未撞到反例。
⚠ 仅台架、仅该枚举域、仅核了 `FaceBlock` 的 11 个字段，**没有**核 `ChainDataGeomParts` 的 36 个字段
⟹ 不主张 `hslice` 为真或为假。

⛔ **同轮自撤一条哨兵（`PROTOCOL §86`）**：本 lane 先跑过一个「翻转判据」负控
（把 `hvJ` 换成 `dot n vJ ≥ 0`，期望它响），实测 0 —— 那个 0 **不是**负控通过，是**恒空**：
`hsupp` ＋ `a' = a + r • vJ ∈ S` ＋ `1 ≤ r` 已经蕴含 `dot n vJ ≤ 0`
（`tmp/wip/hbase-vl-orient.lean` 的 `dot_nonpos_of_step_mem`），所以「`hsupp` 且 `dot n vJ > 0`」
在构造上不可满足，那条负控**不可能响**。⟹ 该读数作废，本节引的是 §31.4 的正控（20688 个非空实例），
不是那个 0。

### §31.5 受力位置更新（`PROTOCOL §55` 升级为 lane-env-refute 亲读）

§30.2 把异号半格的受力件记在 `det_p_vJ_mul_det_p_vJ1_nonneg` 上。lane-env-refute 本轮亲读了
整条依赖锥后订正：那一条只是两条无前提平面恒等式（`dot_perpVec_self` / `dot_perpVec_eq_det`）
加一次 `no_lower_bound_of_swept` 实例化，**真正的单点在上一层**，是
`EnvRefuteOrient.dot_nJ_p_pos_of_parts`，再往下是 `LeafAShellLsideFork.dot_nonneg_of_rec`；
消费点不是 §30.2 说的 3 处而是 **10+ 处**（`EnvRefuteOrient` 内六处、`BottomFree.lean`、
`LeafAShellBottomParts.lean` 各一处、`HcombOrient.lean` 抬头列为输入、
`LeafAShellWedgeSign.det_sign_of_parts`、本文件 §29）。§30.2 的那个名字不删（§105），
改记于此。可复用的一句（本 lane 的失误，两面同一个）：
**报「受力集中在 X」与收到「义务归约为 X」是同一个失误的两面 —— 两边都必须再往 X 的证明体里读一层，
否则钉住的是可见的最上游，不是真的单点。**
-/

/-- **§31 窗口符号条件 ⟺ 支撑条件（逐点，非退化支）。**

`det vl vJ` 与 `b` 无关，严格负时可以整除掉：`0 ≤ c · d ↔ d ≤ 0`。
右边 `det vl x ≤ 0` 就是 `vl`-法向形的支撑条件。

⟹ **没有比支撑条件更弱的前提能推出窗口条件**：两者在非退化支上是同一个命题。 -/
theorem hb_window_iff_det_nonpos {vl vJ x : ℤ × ℤ} (hneg : det vl vJ < 0) :
    0 ≤ det vl vJ * det vl x ↔ det vl x ≤ 0 := by
  constructor
  · intro h
    by_contra hcon
    have hx : 0 < det vl x := not_le.mp hcon
    have hlt : det vl vJ * det vl x < 0 := mul_neg_of_neg_of_pos hneg hx
    linarith
  · intro h
    rw [← neg_mul_neg]
    exact mul_nonneg (by linarith) (by linarith)

/-- **§31 集合形。** 上条对 `S` 的每个点取合取。左边是目标形的窗口符号条件
（去掉高度前提 `1 ≤ dot nJ (b − a)` 的那一版，比目标形强），右边是支撑条件。 -/
theorem hb_window_set_iff_supp_det {S : Finset (ℤ × ℤ)} {vl vJ a : ℤ × ℤ}
    (hneg : det vl vJ < 0) :
    (∀ b ∈ S, 0 ≤ det vl vJ * det vl (b - a)) ↔ (∀ b ∈ S, det vl (b - a) ≤ 0) := by
  constructor
  · intro h b hb
    exact (hb_window_iff_det_nonpos hneg).mp (h b hb)
  · intro h b hb
    exact (hb_window_iff_det_nonpos hneg).mpr (h b hb)

/-- **§31 哨兵（`PROTOCOL §86`）：严格性不可去。**

`det vl vJ = 0` 时左边恒真而右边可假 ⟹ 等价崩。见证 `vl = (1,0)`、`vJ = (2,0)`（平行，
`det vl vJ = 0`）、`x = (0,1)`：左边 `0 * 1 = 0 ≥ 0` 真，右边 `det vl x = 1 > 0` 假。
⟹ `hb_window_iff_det_nonpos` 的 `hneg` 是真 binder，不是装饰。 -/
theorem hb_window_iff_needs_strict :
    (0 ≤ det ((1, 0) : ℤ × ℤ) ((2, 0) : ℤ × ℤ) * det ((1, 0) : ℤ × ℤ) ((0, 1) : ℤ × ℤ))
      ∧ ¬ det ((1, 0) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) ≤ 0 := by
  refine ⟨?_, ?_⟩
  · norm_num [det]
  · norm_num [det]

/-! ### §31.6 从 `det vl vJ ≠ 0` 就够：二分形，**不定任何符号**

`hb_window_iff_det_nonpos` 要 `det vl vJ < 0`，那是一个**符号裁决**，而第 179 轮的定向冻结
明令不许本 lane 定符号。本小节把它改造成只吃 `≠ 0` 的**二分形**：两个符号各给一条等价，
合起来是「窗口条件 ⟺ 支撑条件（侧由 `det vl vJ` 的符号决定）」。⟹ 用它不需要定符号，
只需要非退化。

非退化那一条链上是现货（lane-tower-hlev 本轮报，本 lane 未复跑其证明体 ⟹ 按 §55 记为
「hlev 报」）：`TowerHlevBottomThin` 的 `thin_det_ne_zero_of_dot_eq_zero`
代 `v := vl` 给 `det vl vJ ≠ 0`，三条前提 `vJ ≠ 0` / `dot nJ vJ = 0` / `dot nJ vl ≠ 0`
链上分别由 `vJ_prim.ne_zero` / `F.dot_nJ_vJ` / `hsweep` 供给。 -/

/-- **§31.6 正号侧的等价。** 与 `hb_window_iff_det_nonpos` 对称：常因子严格正时，
窗口条件换成另一侧的支撑条件 `0 ≤ det vl x`。 -/
theorem hb_window_iff_det_nonneg {vl vJ x : ℤ × ℤ} (hpos : 0 < det vl vJ) :
    0 ≤ det vl vJ * det vl x ↔ 0 ≤ det vl x := by
  constructor
  · intro h
    by_contra hcon
    have hx : det vl x < 0 := not_le.mp hcon
    have hlt : det vl vJ * det vl x < 0 := mul_neg_of_pos_of_neg hpos hx
    linarith
  · intro h
    exact mul_nonneg (le_of_lt hpos) h

/-- **§31.6 二分形：只吃 `det vl vJ ≠ 0`，不定符号。**

结论是一个析取：要么常因子负、窗口 ⟺ `det vl x ≤ 0`，要么常因子正、窗口 ⟺ `0 ≤ det vl x`。
⟹ 消费者拿到 `det vl vJ ≠ 0` 就能用，**不需要**知道是哪一侧；
想落到具体一侧时再 `rcases`，那一步的符号由链上别处供给，不由本节裁。 -/
theorem hb_window_dichotomy_of_ne_zero {vl vJ x : ℤ × ℤ} (hne : det vl vJ ≠ 0) :
    (det vl vJ < 0 ∧ (0 ≤ det vl vJ * det vl x ↔ det vl x ≤ 0)) ∨
      (0 < det vl vJ ∧ (0 ≤ det vl vJ * det vl x ↔ 0 ≤ det vl x)) := by
  rcases lt_trichotomy (det vl vJ) 0 with hlt | heq | hgt
  · exact Or.inl ⟨hlt, hb_window_iff_det_nonpos hlt⟩
  · exact absurd heq hne
  · exact Or.inr ⟨hgt, hb_window_iff_det_nonneg hgt⟩

/-! ### §31.7 `hvJ` 自产（集成者裁决 (a) 授权的复制件）

§31.4 引了这条来说明「翻转 `hvJ` 符号」那个负控**恒空**。原件在
`tmp/wip/hbase-vl-orient.lean` 的 `dot_nonpos_of_step_mem`，那个文件按硬规矩 22
（零消费者）**不上提**；集成者裁决 (a) 明确授权把这一条**复制**进本文件
（本文件已有消费者），原处保留原件并标注（§105）。

机制一句话：支撑性作用在**面的另一端** `a' = a + r • vJ ∈ S` 上 ⟹
`dot n a + r · dot n vJ ≤ dot n a` ⟹ `r · dot n vJ ≤ 0` ⟹ `0 < r` 时 `dot n vJ ≤ 0`。
⟹ 在 `FaceBlock` 上判据只剩 `hsupp` 一条，`hvJ` 不是独立前提。

⚠ `a' = a + r • vJ` 与 `0 < r` **都不是** `FaceBlock` 的字段（`ANormal.lean:638` 明写它们
留在 `exists_faceBlock` 的存在量词里），所以本条按 binder 收，与产者供给的形状一致。 -/

/-- **§31.7 `dot n (a + c • v)` 的展开。** 小计算显式重写，不靠 `by simp`（全 lane 纪律）。 -/
theorem hb_dot_add_smul_right (n a v : ℤ × ℤ) (c : ℤ) :
    dot n (a + c • v) = dot n a + c * dot n v := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **§31.7 `hvJ` 自产。** `tmp/wip/hbase-vl-orient.lean` 的 `dot_nonpos_of_step_mem` 的复制件
（集成者裁决 (a) 授权，原处保留原件）。 -/
theorem hb_dot_nonpos_of_step_mem {S : Finset (ℤ × ℤ)} {n a v : ℤ × ℤ} {r : ℕ}
    (hsupp : ∀ b ∈ S, dot n b ≤ dot n a) (hr : 0 < r)
    (hmem : a + (r : ℤ) • v ∈ S) :
    dot n v ≤ 0 := by
  have h := hsupp _ hmem
  rw [hb_dot_add_smul_right] at h
  have hrpos : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr
  by_contra hcon
  have hvpos : 0 < dot n v := not_le.mp hcon
  have : 0 < (r : ℤ) * dot n v := mul_pos hrpos hvpos
  linarith

/-- **§31.7 哨兵（`PROTOCOL §86`）：`0 < r` 不可去。**

`r = 0` 时 `a + 0 • v = a ∈ S` 对任何 `v` 都成立，支撑性给不出 `v` 的任何信息。
见证 `S = {(0,0)}`、`a = (0,0)`、`n = (1,0)`、`v = (1,0)`：`hsupp` 成立（唯一点取等），
而 `dot n v = 1 > 0` ⟹ 结论为假。⟹ `hr` 是真 binder。 -/
theorem hb_dot_nonpos_of_step_mem_needs_r_pos :
    (∀ b ∈ ({(0, 0)} : Finset (ℤ × ℤ)),
        dot ((1, 0) : ℤ × ℤ) b ≤ dot ((1, 0) : ℤ × ℤ) ((0, 0) : ℤ × ℤ))
      ∧ ¬ dot ((1, 0) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) ≤ 0 := by
  refine ⟨?_, by norm_num [dot]⟩
  intro b hb
  rw [Finset.mem_singleton] at hb
  rw [hb]

end SliceCone


end Nivat.TowerHbase

#print axioms Nivat.TowerHbase.dot_nJ_p_nonneg
#print axioms Nivat.TowerHbase.exists_nat_combo
#print axioms Nivat.TowerHbase.exists_seed_level_of_rec
#print axioms Nivat.TowerHbase.not_common_residue_of_rec_p
#print axioms Nivat.TowerHbase.bottom_conj123_of_rec_p
#print axioms Nivat.TowerHbase.bottom_conj123_of_rec_p_of_tile
#print axioms Nivat.TowerHbase.gcd_dot_dvd_det
#print axioms Nivat.TowerHbase.isCoprime_dot_of_det_unit
#print axioms Nivat.TowerHbase.bottom_conj123_of_det_unit
#print axioms Nivat.TowerHbase.witness_dot_nJ_vl
#print axioms Nivat.TowerHbase.witness_gcd_two
#print axioms Nivat.TowerHbase.witness_det_p_vl
#print axioms Nivat.TowerHbase.witness_p
#print axioms Nivat.TowerHbase.witness_vJ1
#print axioms Nivat.TowerHbase.witness_nonempty
#print axioms Nivat.TowerHbase.witness_rec_p
#print axioms Nivat.TowerHbase.witness_hhp
#print axioms Nivat.TowerHbase.witness_even_reach
#print axioms Nivat.TowerHbase.not_conj1_of_dot_nJ_vl
#print axioms Nivat.TowerHbase.hcop_strictly_weaker
#print axioms Nivat.TowerHbase.dot_of_collinear
#print axioms Nivat.TowerHbase.hcop_iff_coprime_c_m
#print axioms Nivat.TowerHbase.bottom_conj123_of_unit_vl
#print axioms Nivat.TowerHbase.witnessB_nJ_prim
#print axioms Nivat.TowerHbase.witnessB_vl_prim
#print axioms Nivat.TowerHbase.coprime_c_m_not_enough
#print axioms Nivat.TowerHbase.det_vJ_vl_assoc
#print axioms Nivat.TowerHbase.arith_fields_do_not_pin_magnitude
#print axioms Nivat.TowerHbase.bottom_conj123_of_rec_vJ
#print axioms Nivat.TowerHbase.exists_pos_multiple_of_det_zero
#print axioms Nivat.TowerHbase.vJ1_eq_vl_of_det_zero
#print axioms Nivat.TowerHbase.prim_vJ1_iff_m_eq_one
#print axioms Nivat.TowerHbase.det_prev_ne_zero_of_window_pos
#print axioms Nivat.TowerHbase.not_collinear_of_window_pos
#print axioms Nivat.TowerHbase.collinear_iff_window_bot
#print axioms Nivat.TowerHbase.dvd_dot_p_of_collinear
#print axioms Nivat.TowerHbase.gcd_eq_neg_sweep_of_collinear
#print axioms Nivat.TowerHbase.rec_p_orbit_one_residue
#print axioms Nivat.TowerHbase.cover_iff_of_collinear
#print axioms Nivat.TowerHbase.aup_rec_p_witness
#print axioms Nivat.TowerHbase.aup_halfPlane_witness
#print axioms Nivat.TowerHbase.cover_without_gcd_one_chain_faithful

#print axioms Nivat.TowerHbase.hbase_prim_dir
#print axioms Nivat.TowerHbase.prim_vJ1_of_edge_ccw
#print axioms Nivat.TowerHbase.prim_vJ1_of_edge_cw
#print axioms Nivat.TowerHbase.collinear_vJ1_vl_iff_perp_ccw
#print axioms Nivat.TowerHbase.collinear_vJ1_vl_iff_perp_cw
#print axioms Nivat.TowerHbase.vJ1_eq_vl_of_edge_perp_ccw
#print axioms Nivat.TowerHbase.edgeWit_mem_E
#print axioms Nivat.TowerHbase.edge_mem_does_not_give_collinear

#print axioms Nivat.TowerHbase.gcd_eq_neg_sweep_of_dvd
#print axioms Nivat.TowerHbase.dvd_dot_p_of_height_dvd
#print axioms Nivat.TowerHbase.rec_p_orbit_one_residue_of_dvd
#print axioms Nivat.TowerHbase.cover_iff_of_dvd
#print axioms Nivat.TowerHbase.height_dvd_of_collinear
#print axioms Nivat.TowerHbase.height_dvd_strictly_weaker_than_collinear

#print axioms Nivat.TowerHbase.dvd_dot_p_iff_dvd_of_collinear
#print axioms Nivat.TowerHbase.height_dvd_does_not_give_isUnit_m
#print axioms Nivat.TowerHbase.isUnit_m_iff_m_eq_one_of_sign
#print axioms Nivat.TowerHbase.cover_trivial_of_unit_modulus
#print axioms Nivat.TowerHbase.old_separation_witness_is_degenerate
#print axioms Nivat.TowerHbase.height_dvd_strictly_weaker_nondegenerate
#print axioms Nivat.TowerHbase.not_prim_sep_witness_vJ1
#print axioms Nivat.TowerHbase.isUnit_gap_empty_of_prim_vJ1
#print axioms Nivat.TowerHbase.m_neg_one_survives_without_hsign
#print axioms Nivat.TowerHbase.VJ1FromEdge
#print axioms Nivat.TowerHbase.vJ1_edge_stock_of_parts
#print axioms Nivat.TowerHbase.nJ_edge_new_content_of_parts
#print axioms Nivat.TowerHbase.bottom_conj123_of_rec_p_of_fields

#print axioms Nivat.TowerHbase.hcomb_fails_under_full_cone_stock
#print axioms Nivat.TowerHbase.nat_comb_false_of_int_comb_false

#print axioms Nivat.TowerHbase.hb_eq_of_smul_eq
#print axioms Nivat.TowerHbase.hb_mem_of_rec_nat
#print axioms Nivat.TowerHbase.hb_dot_nJ_W₀
#print axioms Nivat.TowerHbase.hb_W₀_ne_zero_of_det
#print axioms Nivat.TowerHbase.orient_of_bottom_exhaust
#print axioms Nivat.TowerHbase.hOrient_fails_under_full_cone_stock

#print axioms Nivat.TowerHbase.hb_dot_add_zsmul
#print axioms Nivat.TowerHbase.ray_W₀_of_fields
#print axioms Nivat.TowerHbase.recCone_W₀_of_fields
#print axioms Nivat.TowerHbase.rec_vJ_of_real_dir
#print axioms Nivat.TowerHbase.rec_vJ_of_W₀_pos_multiple
#print axioms Nivat.TowerHbase.rec_vJ_of_smul_eq

#print axioms Nivat.TowerHbase.hb_scale_of_perp
#print axioms Nivat.TowerHbase.hb_det_p_W₀
#print axioms Nivat.TowerHbase.hb_scale_pos
#print axioms Nivat.TowerHbase.rec_vJ_of_det_sieve
#print axioms Nivat.TowerHbase.hb_stock_passes_sieve

#print axioms Nivat.TowerHbase.hb_union_halfPlane_of_parts
#print axioms Nivat.TowerHbase.rec_vJ_of_parts_det_sieve
#print axioms Nivat.TowerHbase.hb_dot_smul_left
#print axioms Nivat.TowerHbase.hb_dot_self_pos
#print axioms Nivat.TowerHbase.hb_sign_iff_scale_nonneg
#print axioms Nivat.TowerHbase.hb_dot_W₀_vJ_nonneg_of_sieve
#print axioms Nivat.TowerHbase.hb_latticeConvex_ahat_of_parts
#print axioms Nivat.TowerHbase.rec_vJ_of_parts_nondeg
#print axioms Nivat.TowerHbase.hb_det_p_vJ1_eq_zero_iff_collinear
#print axioms Nivat.TowerHbase.hb_transverse_iff_not_collinear
#print axioms Nivat.TowerHbase.hb_dot_mul_fst_eq
#print axioms Nivat.TowerHbase.hb_dot_mul_snd_eq
#print axioms Nivat.TowerHbase.hb_det_ne_zero_of_perp
#print axioms Nivat.TowerHbase.rec_vJ_of_det_sieve_slim

#print axioms Nivat.TowerHbase.hbQ
#print axioms Nivat.TowerHbase.mem_hbQ
#print axioms Nivat.TowerHbase.hbQ_dot_nJ
#print axioms Nivat.TowerHbase.hbQ_dot_nL
#print axioms Nivat.TowerHbase.hbQ_latticeConvex
#print axioms Nivat.TowerHbase.hbQ_nonempty
#print axioms Nivat.TowerHbase.hbQ_halfPlane
#print axioms Nivat.TowerHbase.hbQ_rec_p
#print axioms Nivat.TowerHbase.hbQ_swept
#print axioms Nivat.TowerHbase.hbQ_nL_eq
#print axioms Nivat.TowerHbase.hbQ_halfPlane_L
#print axioms Nivat.TowerHbase.hbQ_attained_L
#print axioms Nivat.TowerHbase.hbQ_collinear
#print axioms Nivat.TowerHbase.hbQ_reachSet_fst
#print axioms Nivat.TowerHbase.hbQ_no_edge_ray
#print axioms Nivat.TowerHbase.hbQ_not_rec_vJ
#print axioms Nivat.TowerHbase.hb_geom_block_not_imply_edge_ray
#print axioms Nivat.TowerHbase.hb_geom_block_not_imply_rec_vJ

#print axioms Nivat.TowerHbase.rec_vJ_of_parts_nondeg_slim

#print axioms Nivat.TowerHbase.hb_dot_rot_eq_det
#print axioms Nivat.TowerHbase.hb_dot_rot'_eq_neg_det
#print axioms Nivat.TowerHbase.hb_not_supp_of_rec_of_dot_pos
#print axioms Nivat.TowerHbase.hb_supp_forces_dot_p_nonpos
#print axioms Nivat.TowerHbase.hb_supp_rot_forces_det_nonpos
#print axioms Nivat.TowerHbase.hb_supp_rot'_forces_det_nonneg
#print axioms Nivat.TowerHbase.hb_no_rot_admissible_of_det_mul_neg
#print axioms Nivat.TowerHbase.hb_not_supp_hypotheses_satisfiable
#print axioms Nivat.TowerHbase.hb_det_mul_pos_satisfiable

#print axioms Nivat.TowerHbase.hb_ray_of_unbounded_line
#print axioms Nivat.TowerHbase.rec_vJ_of_unbounded_line

#print axioms Nivat.TowerHbase.hb_dot_mul_det_sub
#print axioms Nivat.TowerHbase.hb_cone_cond1_of_height
#print axioms Nivat.TowerHbase.hb_dot_det_triple
#print axioms Nivat.TowerHbase.hb_det_vJ_vJ1_mul_pos
#print axioms Nivat.TowerHbase.hb_det_sub_zsmul_right
#print axioms Nivat.TowerHbase.hb_det_sub_zsmul_left
#print axioms Nivat.TowerHbase.hb_reach_shift
#print axioms Nivat.TowerHbase.hb_slice_of_cone
#print axioms Nivat.TowerHbase.hb_slice_free_of_det_mul_neg
#print axioms Nivat.TowerHbase.hb_slice_of_parts
#print axioms Nivat.TowerHbase.hb_slice_free_of_parts
#print axioms Nivat.TowerHbase.hb_transverse_slice_wedge_dichotomy
#print axioms Nivat.TowerHbase.hb_slice_side_can_fail
#print axioms Nivat.TowerHbase.hb_both_halves_realised
#print axioms Nivat.TowerHbase.hb_unbounded_line_of_not_bddAbove
#print axioms Nivat.TowerHbase.rec_vJ_of_parts_unbounded_line
#print axioms Nivat.TowerHbase.rec_vJ_of_parts_unbounded_line'
#print axioms Nivat.TowerHbase.rec_vJ_of_parts_not_bddAbove
#print axioms Nivat.TowerHbase.hb_unbounded_line_needs_latticeConvex
#print axioms Nivat.TowerHbase.hb_sieve_of_same_sign
#print axioms Nivat.TowerHbase.rec_vJ_of_parts_same_sign
#print axioms Nivat.TowerHbase.hb_not_sieve_of_opp_sign
#print axioms Nivat.TowerHbase.hb_sieve_unusable_of_opp_sign
#print axioms Nivat.TowerHbase.hb_same_sign_subcells_realised
#print axioms Nivat.TowerHbase.hb_cell_nonneg_of_sieve_nonneg
#print axioms Nivat.TowerHbase.hb_not_opp_sign_of_sieve_nonneg
#print axioms Nivat.TowerHbase.hb_cell_nonneg_needs_chain_input
#print axioms Nivat.TowerHbase.hb_det_swap_cell_eq
#print axioms Nivat.TowerHbase.hb_det_swap_cell_eq_sentinel
#print axioms Nivat.TowerHbase.hb_window_iff_det_nonpos
#print axioms Nivat.TowerHbase.hb_window_set_iff_supp_det
#print axioms Nivat.TowerHbase.hb_window_iff_needs_strict
#print axioms Nivat.TowerHbase.hb_window_iff_det_nonneg
#print axioms Nivat.TowerHbase.hb_window_dichotomy_of_ne_zero
#print axioms Nivat.TowerHbase.hb_dot_add_smul_right
#print axioms Nivat.TowerHbase.hb_dot_nonpos_of_step_mem
#print axioms Nivat.TowerHbase.hb_dot_nonpos_of_step_mem_needs_r_pos
-- §30.6 完整性补齐（`PROTOCOL §84`：报计数必须带分母）：声明头 163 条而收据只有 161 条，
-- 差的两条是 `def Aw` 与 `def edgeWitR`，此前从未出过收据。补上后 163 == 163。
#print axioms Nivat.TowerHbase.Aw
#print axioms Nivat.TowerHbase.edgeWitR
