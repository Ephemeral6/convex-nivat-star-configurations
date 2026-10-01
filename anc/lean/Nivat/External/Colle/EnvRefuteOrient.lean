/-
# `hcomb` 的缺失字段：**定向**（正式缺失字段报告）

**为什么有这个文件。** 集成者在 `HcombOrient.lean` 用内核见证
（`HcombOrient.hcomb_fails_on_full_sign_stock`）证明：链上现有的符号现货推不出
`RecVJComb.parts_rec_vJ` 的侧条件

    hcomb : c.vJ = (a : ℤ) • p + (t : ℤ) • c.vJ1     (a t : ℕ)

并派本 lane 按 `Primitive vJ1` 的先例把它写成一条**正式的缺失字段报告**，要求三项：
(a) 缺的谓词逐字符长什么样；(b) 原文哪一句给了它；(c) 加上它之后 `hcomb` 是否就自由
（用 `ray_eq` 算，不靠读法）。本文件是那份报告，三项逐条在下面，每条都有内核件。

## (a) 缺的谓词，逐字符

    hOrient : ∃ t : ℕ, (dot nJ p) • vJ = (t : ℤ) • HcombOrient.W₀ nJ p vJ1

展开 `W₀` 即 `∃ t : ℕ, ⟪nJ,p⟫ • vJ = t • ((−⟪nJ,vJ1⟫) • p + ⟪nJ,p⟫ • vJ1)`。
它要的**不是**共线（见下），而是「`vJ` 落在 `W₀` 的**非负**射线上」。

## (b) 原文出处：**未查**

`b3_colle2.txt:440-520` 我没有读，也不打算读：本 lane 身上有一条永久禁令「别再往下读原文
`b3_colle2.txt`」，我不自行解除它。⟹ 本报告的 (b) 栏是**空的，不是负的**：按 §51，
「我没找到」与「原文没有」是两件事，此处连「我没找到」都还没发生。这一栏要么由集成者显式解禁后
由我补，要么派给 lane-tower-hbase / lane-leafa-shell 做纸面定位。**在 (b) 补上之前，本条只能算
「链上缺一条谓词」，不能算「原文缺一条谓词」。**

## (c) 加上它之后 `hcomb` 还欠一条整除 —— `c = 1` 时才自由

⚠ **本栏第一版把答案写成「完全自由」，是错的，已改（§102 自曝）。** 错因：我第一版的数值搜索
把 `Primitive p` 当成了现货并直接**过滤掉**了非本原的 `p`，于是搜出 0 个反例。
`Primitive p` **不是链上现货**：`p = −(c:ℤ) • vl` 只有 `c = 1` 时才本原，而全树扫
`Primitive p` 在 `RegionSteps` / `ChainPartsFeed` / `RecVJComb` 三处**命中 0**
（哨兵：同一命令里 `Primitive vl` 在 `RegionSteps` 命中 30）。

一般形（`hcomb_iff_ray_dvd`，**不**假设 `Primitive p`）：

    (∃ a t : ℕ, vJ = a • p + t • vJ1)  ↔  (∃ t : ℕ, ⟪nJ,p⟫ • vJ = t • W₀ ∧ ⟪nJ,p⟫ ∣ t·(−⟪nJ,vJ1⟫))

⟹ **只加定向字段不够**，还欠整除 `⟪nJ,p⟫ ∣ t·(−⟪nJ,vJ1⟫)`。内核见证
`orient_not_enough_without_prim_p`：`nJ = (−4,−3)`、`vl = (−2,3)`、`c = 2`、`p = (4,−6)`、
`vJ1 = (1,−1)`、`vJ = (3,−4)` 同时满足四条本原性（`nJ`/`vl`/`vJ1`/`vJ`——`p` 不在其中，
因为它不是现货）、`p = −2 • vl`、`0 < ⟪nJ,p⟫`、`⟪nJ,vJ1⟫ < 0`、`⟪nJ,vJ⟫ = 0`、
`det vl vJ1 ≠ 0`，**且定向谓词成立**（`t = 1`，`α = 2`、`β = 1`、`W₀ = (6,−8)`），
**而 `hcomb` 对一切 `a t : ℕ` 为假**——死在 `2 ∤ 1`。

`c = 1`（等价于 `Primitive p`）时整除免费：`hcomb_iff_ray` 是干净的 ⟺，
`dvd_of_ray` 用 `Primitive p` 的 Bezout 系数把整除当场证出。
⟹ ⚠ 对集成者「格那一半不是瓶颈」的判断，我上一轮的确认**过头了**：它只在 `c = 1` 成立。
`ray_eq` 里没有整除是因为它是**必要**方向；**充分**方向要整除，且只有 `Primitive p` 才免费。
⟹ 缺失字段实际是**两条**（或一条合写的）：定向 ＋（`c ≥ 2` 时的）整除；
或者先证 `c = 1`——那是另一条欠账，不在本文件。

## ⚠ 对既有读数的一条修正：`det vJ W₀ = 0` 是**恒真**的，不能当判据

`HcombOrient.lean` 把 `det_vJ_W₀` 写成「链上可直接验算的必要条件：`det vJ W₀ ≠ 0` ⟹ `hcomb`
当场死」。这条判据**永远不会触发**：

* `dot_nJ_W₀`：`⟪nJ, W₀ nJ p vJ1⟫ = 0` —— **无条件**，连 `hcomb` 都不用（把定义展开就是
  `(−⟪nJ,vJ1⟫)⟪nJ,p⟫ + ⟪nJ,p⟫⟪nJ,vJ1⟫`）。
* `det_of_perp_perp`：平面上两条都与 `n ≠ 0` 垂直的向量必共线。
* ⟹ `det_vJ_W₀_vacuous`：只用 `nJ ≠ 0`（字段 `nJ_prim` ＋ `Primitive.ne_zero`）和
  `⟪nJ,vJ⟫ = 0`（字段 `F.dot_nJ_vJ`）就得到 `det vJ (W₀ nJ p vJ1) = 0`。

两条字段都是链上无条件成立的 ⟹ `det vJ W₀ ≠ 0` 在链数据上不可能发生。
⟹ `ray_eq` 的全部内容在**标量**里（`t` 的存在与非负），共线那一半是 `F.dot_nJ_vJ` 的重复。
这正好与集成者自己的结论（「崩的是朝向」）同向，但把「可验算的必要条件」这一句作废。
⚠ 本条只否 `det_vJ_W₀` 作为**判据**的用处；`det_vJ_W₀` 本身是真命题，不撤。

## 供给面：37 条字段里哪一条可能钉死定向

集成者点名 `escapeW` / `shellSubStrip` / `shellEnv` / `fillCover` / `bottom` 五条为本见证未兑现、
可能蕴含定向。逐条扫它们的**类型**（`ChainPartsFeed.lean` 五条字段的声明体，`vJ` 按
`vJ(?![0-9])` 匹配以避开 `vJ1`，哨兵取字段声明行 `vJ : ℤ × ℤ`，哨兵命中 1）：

| 字段 | 类型里 `vJ` 命中 |
|---|---|
| `escapeW` | 0 |
| `shellSubStrip` | 0 |
| `shellEnv` | 0 |
| `fillCover` | 0 |
| `bottom` | 3 |

⟹ 五条里**只有 `bottom`** 的类型提到 `vJ`（`z₀ + k • vJ`，`L ≤ k`——一条 `+vJ` 方向的射线，
形状上正是定向）。其余四条只能**间接**经 `S` / `gen` 约束 `vJ`，而那条通道是
`F : FaceBlock S nJ vJ` ＋ `gen_eq : gen = F.a'`（结构体内 `gen` 只在这两处出现，扫 `\bgen\b`
命中 4：参数行、两行注释、`gen_eq`）。这条通道被下面这条定理封住一半：

* `faceBlockFlip`：`FaceBlock S n v → FaceBlock S n (-v)`，把 `a` 与 `a'` 对调即可。
  ⟹ **面数据是定向盲的**：`latticeConvex_S` / `a_mem` / `a'_mem` / `lex` / `lex'` / `edge` /
  `edge'` / `dot_nJ_vJ` 八条对 `vJ ↦ −vJ` 全部成立，`vJ_prim` 与 `F.dot_nJ_vJ` 同样对称。
  ⟹ 翻转唯一付出的代价是 `gen_eq`：翻转后 `gen` 得从 `F.a'` 换成 `F.a`。

⚠ 射程（勿放大）：`faceBlockFlip` 说的是「面数据本身不区分 `±vJ`」。翻转要付的代价在
`gen_eq` 上（`gen` 得从 `F.a'` 换成 `F.a`），**这笔代价付得出，已关闭**：

* `latticeConvex_erase_flip`：`F.lex` 说 `F.a` 在 `(−n, −v)` 序下严格最大，
  `Colle37Geom.latticeConvex_erase_of_lexExtreme`（`ShellGeom.lean`，对 `(n, d)` 完全泛用）
  给出 `LatticeConvex (S.erase F.a)`。现成用法全是 `… F.lex'`（给 `S.erase F.a'`），这里是镜像。
* `generatesAt_flip_gen`：`Colle.IsGeneratingSet ξ S` 的第三项是「每个顶点都被生成」
  （`Generating.lean`：`∀ a ∈ S, LatticeConvex (S.erase a) → GeneratesAt ξ S a`），
  上一条正好兑现顶点条件 ⟹ `GeneratesAt ξ S (faceBlockFlip F).a'`。
* 而 `IsGeneratingSet ξ S` 与 `GeneratesAt ξ S gen` 是消费者**并列输出**的两个合取项
  （`RegionSteps.lean` 的 `exists_preamble` 结论里紧挨着），`S` 同一个 ⟹ 换 `gen` 不需要新前提。

⟹ 「面数据 ＋ `gen`」这条通道**内核侧**的代价付得出。✅ **2026-09-26 集成者裁决：
四条 `vJ`-无关字段出局，已定。** 他独立复核了两件事（不是读本文件的 docstring）：
`Colle37Geom.latticeConvex_erase_of_lexExtreme` 确在 `ShellGeom.lean` 且对 `(n,d)` 泛用
（树里现成用法全喂 `F.lex'`，喂 `F.lex` 合法）；`Colle.IsGeneratingSet ξ S` 确是
`exists_preamble` 结论里的并列合取项、`S` 同一个 ⟹ 换 `gen` 不需要新前提。
消费者那一侧是他读的（禁令不变，我不读消费者）。他同时自撤了他本轮的 `GenSiteBlind.lean`
（更绕且与既有装配重复，已 `rm`，未进 build）与其中「lex⟹顶点的引理树里没找到」那句。

⚠ `bottom` 那条（唯一同时提到 `vJ` 与 `vJ1` 的，集成者第 237 轮按字段类型重算确认）
**不在我格子里**，且它是**自毁出口**：有 `bottom` 就能用 `rec_vJ_of_parts` 直接拿 `rec_vJ`，
不需要 `hcomb`。⟹ 按集成者第 237 轮的收敛，`hcomb` 路线活口只剩 **L-块**
（`ahat_halfPlane_L` / `ahat_attained_L` / `nfp_L`，都经带符号的 `det p vJ`）。

## 定向就是死因，且只是死因

`flip_repairs_hcomb_on_stock_witness`：在集成者那组见证数据上（`nJ=(0,1)`、`p=(−1,1)`、
`vJ1=(1,−2)`、`vJ=(1,0)`），`hcomb` 对一切 `a t : ℕ` 为假，而 `−vJ` 用 `a = 2`、`t = 1` 当场成立。
`orient_separates_stock_witness`：同一组数据上 `hOrient` 对 `vJ` 为假、对 `−vJ` 取 `t = 1` 为真。
⟹ 见证的死因**恰好**是 `hOrient` 的方向选择，不是格指标、不是本原性、不是符号现货的任何其它一条。
-/
import Nivat.External.Colle.HcombOrient
import Nivat.External.Colle.ANormal
import Nivat.External.Colle.ShellGeom
import Nivat.External.Colle.LeafAShellLsideFork
import Nivat.External.Colle.RecVJPrimDir
import Nivat.External.Colle.RecVJFromParts
import Nivat.External.Colle.TowerHbaseRecP
import Nivat.External.Colle.ItemII

namespace Nivat.EnvRefuteOrient

open Nivat Nivat.LE2 Nivat.HcombOrient

/-! ### `W₀` 与 `nJ` 垂直，共线性是白给的 -/

/-- `dot n (-v) = - dot n v`。 -/
theorem dot_neg_right (n v : ℤ × ℤ) : dot n (-v) = - dot n v := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]
  ring

/-- ⭐ **无条件**：`W₀` 总与 `nJ` 垂直。展开定义即
`(−⟪nJ,vJ1⟫)·⟪nJ,p⟫ + ⟪nJ,p⟫·⟪nJ,vJ1⟫ = 0`，不需要 `hcomb`、不需要任何前提。 -/
theorem dot_nJ_W₀ (nJ p vJ1 : ℤ × ℤ) : dot nJ (W₀ nJ p vJ1) = 0 := by
  simp only [W₀, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- 平面上两条都与 `n ≠ 0` 垂直的向量必共线。

⚠ **第 247 轮去重（集成者，§110.2）**：本条与 `Nivat.LE2.det_eq_zero_of_dot_eq_zero`
（`LatticeEdges.lean:110`）**逐字同命题**，证明体已换成一行桥接。规范形在 `LatticeEdges`，
本条只作为本文件内的局部别名保留（**删名会打到 `:176` 与 `HcombOrient.lean:31`**，故按 §105 留名）。
⛔ 新代码请直接用 `Nivat.LE2.det_eq_zero_of_dot_eq_zero`，不要再写第 N 份。 -/
theorem det_of_perp_perp {n u w : ℤ × ℤ} (hn : n ≠ 0)
    (hu : dot n u = 0) (hw : dot n w = 0) : det u w = 0 :=
  Nivat.LE2.det_eq_zero_of_dot_eq_zero hn hu hw

/-- ⛔ **`det vJ W₀ = 0` 在链上恒真**：只用 `nJ ≠ 0`（字段 `nJ_prim`）和 `⟪nJ,vJ⟫ = 0`
（字段 `F.dot_nJ_vJ`），`hcomb` 一条也不用。⟹ `HcombOrient.det_vJ_W₀` 不能当判据，
`det vJ W₀ ≠ 0` 在链数据上不可能发生。 -/
theorem det_vJ_W₀_vacuous {nJ p vJ1 vJ : ℤ × ℤ} (hn : nJ ≠ 0) (h0 : dot nJ vJ = 0) :
    det vJ (W₀ nJ p vJ1) = 0 :=
  det_of_perp_perp hn h0 (dot_nJ_W₀ nJ p vJ1)

/-! ### 闭式：定向谓词 ⟺ `hcomb` -/

/-- **整除是白给的**：射线方程 ＋ `Primitive p` 的 Bezout 系数直接给出
`⟪nJ,p⟫ ∣ t · (−⟪nJ,vJ1⟫)`。⟹ `hcomb` 的充分性方向不欠任何整除侧条件。 -/
theorem dvd_of_ray {nJ p vJ1 vJ : ℤ × ℤ} {t : ℕ} (hp : Primitive p)
    (hray : (dot nJ p) • vJ = (t : ℤ) • W₀ nJ p vJ1) :
    (dot nJ p) ∣ (t : ℤ) * (- dot nJ vJ1) := by
  obtain ⟨x, y, hxy⟩ := hp
  have e1 := congrArg Prod.fst hray
  have e2 := congrArg Prod.snd hray
  simp only [W₀, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
  refine ⟨x * (vJ.1 - (t : ℤ) * vJ1.1) + y * (vJ.2 - (t : ℤ) * vJ1.2), ?_⟩
  linear_combination (-x) * e1 + (-y) * e2 - ((t : ℤ) * (- dot nJ vJ1)) * hxy

/-- ⭐ **定向谓词 ＋ 整除推出 `hcomb`**：`a` 由整除商给出，符号由 `0 < ⟪nJ,p⟫` 与
`⟪nJ,vJ1⟫ < 0` 保证落在 `ℕ` 里。 -/
theorem hcomb_of_ray_of_dvd {nJ p vJ1 vJ : ℤ × ℤ} {t : ℕ}
    (hα : 0 < dot nJ p) (hβ : dot nJ vJ1 < 0)
    (hdvd : (dot nJ p) ∣ (t : ℤ) * (- dot nJ vJ1))
    (hray : (dot nJ p) • vJ = (t : ℤ) • W₀ nJ p vJ1) :
    ∃ a : ℕ, vJ = (a : ℤ) • p + (t : ℤ) • vJ1 := by
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : 0 ≤ k := by
    by_contra h
    have hneg : dot nJ p * k < 0 := mul_neg_of_pos_of_neg hα (not_le.mp h)
    have hpos : 0 ≤ (t : ℤ) * (- dot nJ vJ1) :=
      mul_nonneg (Int.natCast_nonneg t) (by linarith)
    rw [hk] at hpos
    linarith
  have hkt : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
  have e1 := congrArg Prod.fst hray
  have e2 := congrArg Prod.snd hray
  simp only [W₀, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
  refine ⟨k.toNat, ?_⟩
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hkt]
    refine mul_left_cancel₀ (ne_of_gt hα) ?_
    rw [e1]
    linear_combination p.1 * hk
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hkt]
    refine mul_left_cancel₀ (ne_of_gt hα) ?_
    rw [e2]
    linear_combination p.2 * hk

/-- **`Primitive p` 下整除免费**（即 `c = 1` 的特例）：`dvd_of_ray` 把整除当场证出。
⚠ `Primitive p` **不是链上现货**，见 `orient_not_enough_without_prim_p`。 -/
theorem hcomb_of_ray {nJ p vJ1 vJ : ℤ × ℤ} {t : ℕ} (hp : Primitive p)
    (hα : 0 < dot nJ p) (hβ : dot nJ vJ1 < 0)
    (hray : (dot nJ p) • vJ = (t : ℤ) • W₀ nJ p vJ1) :
    ∃ a : ℕ, vJ = (a : ℤ) • p + (t : ℤ) • vJ1 :=
  hcomb_of_ray_of_dvd hα hβ (dvd_of_ray hp hray) hray

/-- ⭐⭐ **`hcomb` 的闭式（一般形，不假设 `Primitive p`）**：侧条件 `hcomb` 与
「定向 ＋ 整除」等价。⟹ 只加定向字段还不够，一般情形还欠 `⟪nJ,p⟫ ∣ t·(−⟪nJ,vJ1⟫)`。 -/
theorem hcomb_iff_ray_dvd {nJ p vJ1 vJ : ℤ × ℤ}
    (hα : 0 < dot nJ p) (hβ : dot nJ vJ1 < 0) (h0 : dot nJ vJ = 0) :
    (∃ a t : ℕ, vJ = (a : ℤ) • p + (t : ℤ) • vJ1) ↔
      (∃ t : ℕ, (dot nJ p) • vJ = (t : ℤ) • W₀ nJ p vJ1 ∧
        (dot nJ p) ∣ (t : ℤ) * (- dot nJ vJ1)) := by
  constructor
  · rintro ⟨a, t, hc⟩
    refine ⟨t, ray_eq hc h0, ?_⟩
    exact ⟨(a : ℤ), by linear_combination - height_eq hc h0⟩
  · rintro ⟨t, hray, hdvd⟩
    obtain ⟨a, ha⟩ := hcomb_of_ray_of_dvd hα hβ hdvd hray
    exact ⟨a, t, ha⟩

/-- ⭐⭐ **`hcomb` 的闭式（`Primitive p`，即 `c = 1`）**：侧条件 `hcomb` 与定向谓词 `hOrient`
**等价**，整除那一半由 `Primitive p` 的 Bezout 系数免费兑现。
⚠ 前提里 `Primitive p` **不是链上现货**（全树 `Primitive p` 在 `RegionSteps` /
`ChainPartsFeed` / `RecVJComb` 三处命中 0，而 `Primitive vl` 在 `RegionSteps` 命中 30）；
`c ≥ 2` 时本条不适用，见 `orient_not_enough_without_prim_p`。 -/
theorem hcomb_iff_ray {nJ p vJ1 vJ : ℤ × ℤ} (hp : Primitive p)
    (hα : 0 < dot nJ p) (hβ : dot nJ vJ1 < 0) (h0 : dot nJ vJ = 0) :
    (∃ a t : ℕ, vJ = (a : ℤ) • p + (t : ℤ) • vJ1) ↔
      (∃ t : ℕ, (dot nJ p) • vJ = (t : ℤ) • W₀ nJ p vJ1) := by
  constructor
  · rintro ⟨a, t, hc⟩
    exact ⟨t, ray_eq hc h0⟩
  · rintro ⟨t, hray⟩
    obtain ⟨a, ha⟩ := hcomb_of_ray hp hα hβ hray
    exact ⟨a, t, ha⟩

/-- ⛔⛔ **内核见证：只加定向字段还不够**（`c ≥ 2` 时）。这组数据满足**全部链上现货**
——四条本原性 `nJ` / `vl` / `vJ1` / `vJ`（`nJ_prim`、`Primitive vl`、`vJ1`、`vJ_prim`）、
`p = −(c:ℤ) • vl` 且 `0 < c`、`0 < ⟪nJ,p⟫`、`⟪nJ,vJ1⟫ < 0`（`hsweep`）、
`⟪nJ,vJ⟫ = 0`（`F.dot_nJ_vJ`）、`det vl vJ1 ≠ 0`（横截）——**并且满足定向谓词 `hOrient`**
（`t = 1`），**而 `hcomb` 对一切 `a t : ℕ` 仍为假**。
数据：`nJ = (−4,−3)`、`vl = (−2,3)`、`c = 2`、`p = (4,−6)`、`vJ1 = (1,−1)`、`vJ = (3,−4)`，
`α = 2`、`β = 1`、`W₀ = (6,−8)`。缺的是 `α ∣ t·β`（这里 `2 ∤ 1`）。
⟹ `Primitive p` 那条前提是本质的，而它**不是链上现货**。 -/
theorem orient_not_enough_without_prim_p :
    ∃ (nJ vl p vJ1 vJ : ℤ × ℤ) (c t : ℕ),
      Primitive nJ ∧ Primitive vl ∧ Primitive vJ1 ∧ Primitive vJ ∧
      0 < c ∧ p = -(c : ℤ) • vl ∧
      0 < dot nJ p ∧ dot nJ vJ1 < 0 ∧ dot nJ vJ = 0 ∧ det vl vJ1 ≠ 0 ∧
      (dot nJ p) • vJ = (t : ℤ) • W₀ nJ p vJ1 ∧
      ¬ Primitive p ∧
      (∀ a t : ℕ, vJ ≠ (a : ℤ) • p + (t : ℤ) • vJ1) := by
  refine ⟨(-4, -3), (-2, 3), (4, -6), (1, -1), (3, -4), 2, 1,
    ⟨-1, 1, by norm_num⟩, ⟨1, 1, by norm_num⟩, ⟨1, 0, by norm_num⟩, ⟨-1, -1, by norm_num⟩,
    two_pos, ?_, by norm_num [dot], by norm_num [dot], by norm_num [dot], by norm_num [det],
    ?_, ?_, ?_⟩
  · rw [Prod.ext_iff]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    omega
  · rw [Prod.ext_iff]
    simp only [W₀, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    omega
  · rintro ⟨u, v, h⟩
    simp only at h
    omega
  · intro a t h
    rw [Prod.ext_iff] at h
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h
    omega

/-! ### 面数据是定向盲的 -/

/-- ⭐ **`FaceBlock` 对 `vJ ↦ −vJ` 封闭**：把两个端点 `a`、`a'` 对调即可，八条义务逐条成立。
⟹ 面数据本身不区分 `±vJ`，不可能是 `hOrient` 的产者。
⚠ 翻转付出的唯一代价在结构体的另一条字段 `gen_eq : gen = F.a'` 上（翻转后是 `gen = F.a`），
见文首「残留问题」。 -/
def faceBlockFlip {S : Finset (ℤ × ℤ)} {n v : ℤ × ℤ}
    (F : Nivat.Colle35.FaceBlock S n v) : Nivat.Colle35.FaceBlock S n (-v) where
  a := F.a'
  a' := F.a
  r := F.r
  latticeConvex_S := F.latticeConvex_S
  a_mem := F.a'_mem
  a'_mem := F.a_mem
  lex := by simpa only [neg_neg] using F.lex'
  lex' := by simpa only [neg_neg] using F.lex
  edge := by simpa only [smul_neg, ← sub_eq_add_neg] using F.edge'
  edge' := by simpa only [smul_neg, sub_neg_eq_add] using F.edge
  dot_nJ_vJ := by rw [dot_neg_right, F.dot_nJ_vJ, neg_zero]

/-- **翻转后的 `gen` 是个顶点**：`F.lex` 说 `F.a` 在 `(−n, −v)` 序下严格最大，
`Colle37Geom.latticeConvex_erase_of_lexExtreme` 对 `(n, d)` 完全泛用，取 `(−n, −v)` 即得。
（现成用法全是 `… F.lex'`，给的是 `S.erase F.a'`；这里是它的镜像。） -/
theorem latticeConvex_erase_flip {S : Finset (ℤ × ℤ)} {n v : ℤ × ℤ}
    (F : Nivat.Colle35.FaceBlock S n v) : LatticeConvex (S.erase F.a) :=
  Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme F.latticeConvex_S F.lex

/-- ⭐ **残留问题关闭：翻转的 `gen` 代价付得出**。翻转后要的是 `GeneratesAt ξ S F.a`
（`gen_eq` 在翻转结构上读作 `gen = (faceBlockFlip F).a' = F.a`），而它由消费者**已经输出**的
`IsGeneratingSet ξ S` 直接给出——`IsGeneratingSet` 的第三项就是「每个顶点都被生成」，
顶点条件由 `latticeConvex_erase_flip` 兑现。
⟹ 「面数据 ＋ `gen`」这条通道**整条**定向盲，四条 `vJ`-无关字段全部出局。 -/
theorem generatesAt_flip_gen {A : Type*} {ξ : Config A} {S : Finset (ℤ × ℤ)} {n v : ℤ × ℤ}
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S) (F : Nivat.Colle35.FaceBlock S n v) :
    Nivat.Colle.GeneratesAt ξ S (faceBlockFlip F).a' :=
  hSgen.2.2 F.a F.a_mem (latticeConvex_erase_flip F)

/-! ### 接链：`hOrient` 一到手，`rec_vJ` 立刻闭合 -/

/-- **`0 < ⟪nJ,p⟫` 是字段给的，不是额外前提，而且不经 `bottom`。**
`LaneLeafAShellLsideFork.dot_nonneg_of_rec` 吃 `ahat_nonempty` ＋ `hhp` ＋ `rec_p` 得
`0 ≤ ⟪nJ,p⟫`，再配字段 `dot_nJ_p`（只给 `≠ 0`）升成严格。
⚠ 出处：`LeafAShellLsideFork.parts_stock_lside` 里同样的两步，但那条是 `private` 且它的
`hrecvJ` 分量走 `rec_vJ_of_parts`（经 `bottom`）——本条**只取符号那一项**，与 `bottom` 无关。
⚠ 对比 `LaneTowerHbaseRecVJ.dot_nJ_p_pos_of_comb`：那条是从 `hcomb` **推出**符号的，
用在这里会成环；本条改从字段取。 -/
theorem dot_nJ_p_pos_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    0 < dot c.nJ p := by
  have hlb : ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i, c.cJ ≤ dot c.nJ g := by
    intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    exact c.hhp i hi
  have h0 : 0 ≤ dot c.nJ p :=
    Nivat.LaneLeafAShellLsideFork.dot_nonneg_of_rec c.ahat_nonempty hlb c.rec_p
  exact lt_of_le_of_ne h0 (Ne.symm c.dot_nJ_p)

/-- ⭐⭐⭐ **`hOrient` ⟹ `rec_vJ`，零额外 binder。** 结论与 `LaneTowerHbaseRecVJ.parts_rec_vJ`
的结论逐字符相同（本证明就是把 `hcomb` 喂给它），而**唯一**的非字段输入是 `hOrient`：
`0 < ⟪nJ,p⟫` 由 `dot_nJ_p_pos_of_parts` 从字段取，`⟪nJ,vJ1⟫ < 0` 是字段 `hsweep`，
`a t : ℕ` 由 `hcomb_of_ray_of_dvd` 同时产出（`a` 是整除商，符号由那两条保证落在 `ℕ`）。
⟹ 洞 1 的 `rec_vJ` 一格从「不知道缺什么」变成「**精确地缺 `hOrient` 这一条谓词，且它一到手
结论就闭合**」。
⚠ 这里的 `hOrient` 是**两项合写**（定向 ＋ 整除），不是只有定向：`c ≥ 2` 时整除不免费，
见 `orient_not_enough_without_prim_p`。只要定向那一项的版本见 `rec_vJ_of_hOrient_of_prim_p`。 -/
theorem rec_vJ_of_hOrient {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hOrient : ∃ t : ℕ, (dot c.nJ p) • c.vJ = (t : ℤ) • W₀ c.nJ p c.vJ1 ∧
      (dot c.nJ p) ∣ (t : ℤ) * (- dot c.nJ c.vJ1)) :
    ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      g + c.vJ ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i := by
  obtain ⟨t, hray, hdvd⟩ := hOrient
  obtain ⟨a, ha⟩ := hcomb_of_ray_of_dvd (dot_nJ_p_pos_of_parts c) c.hsweep hdvd hray
  exact Nivat.LaneTowerHbaseRecVJ.parts_rec_vJ c ha

/-- **`c = 1`（`Primitive p`）时只要定向那一项。** 整除由 `dvd_of_ray` 的 Bezout 免费。
⚠ `Primitive p` 不是链上现货（`p = −(c:ℤ) • vl` 只有 `c = 1` 才本原）。 -/
theorem rec_vJ_of_hOrient_of_prim_p {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) (hp : Primitive p)
    (hOrient : ∃ t : ℕ, (dot c.nJ p) • c.vJ = (t : ℤ) • W₀ c.nJ p c.vJ1) :
    ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      g + c.vJ ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i := by
  obtain ⟨t, hray⟩ := hOrient
  exact rec_vJ_of_hOrient c ⟨t, hray, dvd_of_ray hp hray⟩

/-! ### 定向就是死因 -/

/-- ⛔ **集成者见证的死因恰好是定向**：同一组数据上 `hcomb` 对一切 `a t : ℕ` 为假，
而 `−vJ` 用 `a = 2`、`t = 1` 当场成立，且 `−vJ` 仍然本原、仍然 `⟪nJ,·⟫ = 0`。 -/
theorem flip_repairs_hcomb_on_stock_witness :
    (∀ a t : ℕ, ((1, 0) : ℤ × ℤ) ≠ (a : ℤ) • ((-1, 1) : ℤ × ℤ) + (t : ℤ) • ((1, -2) : ℤ × ℤ)) ∧
      (-((1, 0) : ℤ × ℤ)) = ((2 : ℕ) : ℤ) • ((-1, 1) : ℤ × ℤ) + ((1 : ℕ) : ℤ) • ((1, -2) : ℤ × ℤ) ∧
      Primitive (-((1, 0) : ℤ × ℤ)) ∧
      dot ((0, 1) : ℤ × ℤ) (-((1, 0) : ℤ × ℤ)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a t h
    rw [Prod.ext_iff] at h
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h
    omega
  · rw [Prod.ext_iff]
    simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    omega
  · exact ⟨-1, 0, by norm_num⟩
  · norm_num [dot]

/-- ⛔ **定向谓词在同一组数据上分开 `±vJ`**：对 `vJ = (1,0)` 不存在 `t : ℕ`，
对 `−vJ = (−1,0)` 取 `t = 1` 成立。（`W₀ = (−1,0)`，见 `HcombOrient.witness_W₀`。） -/
theorem orient_separates_stock_witness :
    (∀ t : ℕ, (dot ((0, 1) : ℤ × ℤ) ((-1, 1) : ℤ × ℤ)) • ((1, 0) : ℤ × ℤ)
        ≠ (t : ℤ) • W₀ ((0, 1) : ℤ × ℤ) ((-1, 1) : ℤ × ℤ) ((1, -2) : ℤ × ℤ)) ∧
      (dot ((0, 1) : ℤ × ℤ) ((-1, 1) : ℤ × ℤ)) • (-((1, 0) : ℤ × ℤ))
        = ((1 : ℕ) : ℤ) • W₀ ((0, 1) : ℤ × ℤ) ((-1, 1) : ℤ × ℤ) ((1, -2) : ℤ × ℤ) := by
  constructor
  · intro t h
    rw [Prod.ext_iff] at h
    simp only [W₀, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at h
    omega
  · ext <;> norm_num [W₀, dot]

/-! ## §19 `hswept` ＋ `rec_p` ＋ `ahat_halfPlane_L` 逼出 `det p vJ` 与 `det p vJ1` 同号

**这一节把 §1–§18 的缺失字段报告作废了一半。** 集成者派的任务是「在
`hcomb_fails_on_full_sign_stock` 那组数据上兑现 L-块」。做不成，而且**做不成本身是链上事实**：
那组数据被 L-块排除，排除理由与那组数据无关，是下面这条一般命题。

机制（`no_lower_bound_of_swept`）：记 `m := det p vJ • (-p.2, p.1)`（`ahat_halfPlane_L` 的法向）。

* `dot m p = 0` **恒成立**（`(-p.2, p.1) ⊥ p`，与任何字段无关）；
* `rec_p` ⟹ `Â` 沿 `p` 无限延伸，而 `0 < dot nJ p`（`dot_nJ_p_pos_of_parts`）⟹ `nJ`-高度
  沿 `p` 无上界；
* `hswept` ⟹ 在 `nJ`-高度还 `≥ cJ` 时可沿 `vJ1` 任意步；每走一步 `m`-值降 `dot m vJ1`；
* 于是 `dot m vJ1 < 0` ⟹ `m`-值在 `Â` 上**无下界** ⟹ `ahat_halfPlane_L` 假。

⟹ `0 ≤ det p vJ * det p vJ1`（`det_p_vJ_mul_det_p_vJ1_nonneg`），**只用**
`ahat_nonempty` / `rec_p` / `hswept` / `dot_nJ_p` / `hhp`-侧的 `dot_nonneg_of_rec` /
`ahat_halfPlane_L`，**不经 `bottom`、不经 `nfp_L`、不经原文**。

⚠ 我没有兑现 L-块，所以**没有**「L-块与 `hcomb`-假可以并存」的见证；相反方向的见证有：
`stock_witness_not_on_chain`。按集成者的话，「L-块排除不了这组数据」本来是读法；现在内核给的是
**它排除得了**。 -/

theorem dot_add_orient (n a b : ℤ × ℤ) : dot n (a + b) = dot n a + dot n b := by
  simp only [dot, Prod.fst_add, Prod.snd_add]; ring

theorem dot_smul_orient (n : ℤ × ℤ) (k : ℤ) (v : ℤ × ℤ) : dot n (k • v) = k * dot n v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem dot_smul_left_orient (s : ℤ) (u v : ℤ × ℤ) : dot (s • u) v = s * dot u v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- `(-p.2, p.1) ⊥ p`，无前提。 -/
theorem dot_perpVec_self (p : ℤ × ℤ) : dot ((-p.2, p.1) : ℤ × ℤ) p = 0 := by
  show (-p.2) * p.1 + p.1 * p.2 = 0
  ring

/-- `ahat_halfPlane_L` 的法向作用在任一 `v` 上就是 `det p v`（差一个 `det p vJ` 因子）。 -/
theorem dot_perpVec_eq_det (p v : ℤ × ℤ) : dot ((-p.2, p.1) : ℤ × ℤ) v = det p v := by
  show (-p.2) * v.1 + p.1 * v.2 = p.1 * v.2 - p.2 * v.1
  ring

/-- 平面 Cramer 恒等式：`(det p w) • u - (det p u) • w = (det u w) • p`。 -/
theorem cramer_smul (p u w : ℤ × ℤ) :
    (det p w) • u - (det p u) • w = (det u w) • p := by
  rw [Prod.ext_iff]
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> ring

/-- `det p W₀ = (dot nJ p) * det p vJ1`（`W₀` 的 `p`-分量对 `det p ·` 无贡献）。 -/
theorem det_p_W₀ (nJ p vJ1 : ℤ × ℤ) :
    det p (W₀ nJ p vJ1) = (dot nJ p) * det p vJ1 := by
  simp only [W₀, det, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- `rec_p` 沿 `p` 迭代。 -/
theorem iter_rec_p {U : Set (ℤ × ℤ)} {p : ℤ × ℤ}
    (hrec : ∀ g ∈ U, g + p ∈ U) :
    ∀ (k : ℕ) (g : ℤ × ℤ), g ∈ U → g + (k : ℤ) • p ∈ U := by
  intro k
  induction k with
  | zero => intro g hg; simpa using hg
  | succ n ih =>
      intro g hg
      have h := hrec _ (ih g hg)
      have he : g + (n : ℤ) • p + p = g + ((n + 1 : ℕ) : ℤ) • p := by
        push_cast
        rw [add_smul, one_smul, add_assoc]
      rwa [he] at h

/-- **`rec_p` 把 `hswept` 的守卫顶开**：对任意 `t`，先沿 `p` 走够高再沿 `vJ1` 走 `t` 步，
结果仍在 `U` 内，而任何 `⊥ p` 的泛函在它上面的值恰好降了 `t` 个 `dot m vJ1`。 -/
theorem exists_low_of_swept {U : Set (ℤ × ℤ)} {p vJ1 nJ m : ℤ × ℤ} {cJ : ℤ}
    (hrec : ∀ g ∈ U, g + p ∈ U)
    (hsw : Nivat.MaxEnv.SweptClosed U vJ1 nJ cJ)
    (hα : 0 < dot nJ p) {g₀ : ℤ × ℤ} (hg₀ : g₀ ∈ U)
    (hmp : dot m p = 0) (t : ℕ) :
    ∃ z ∈ U, dot m z = dot m g₀ + (t : ℤ) * dot m vJ1 := by
  have hα' : (1 : ℤ) ≤ dot nJ p := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, cJ - dot nJ g₀ - (t : ℤ) * dot nJ vJ1 ≤ (k : ℤ) :=
    ⟨(cJ - dot nJ g₀ - (t : ℤ) * dot nJ vJ1).toNat, Int.self_le_toNat _⟩
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have hkmul : (k : ℤ) ≤ (k : ℤ) * dot nJ p := le_mul_of_one_le_right hk0 hα'
  have hg1 : g₀ + (k : ℤ) • p ∈ U := iter_rec_p hrec k g₀ hg₀
  have hheight : cJ ≤ dot nJ (g₀ + (k : ℤ) • p + (t : ℤ) • vJ1) := by
    rw [dot_add_orient, dot_add_orient, dot_smul_orient, dot_smul_orient]
    linarith
  refine ⟨g₀ + (k : ℤ) • p + (t : ℤ) • vJ1, hsw _ hg1 t hheight, ?_⟩
  rw [dot_add_orient, dot_add_orient, dot_smul_orient, dot_smul_orient, hmp]
  ring

/-- **`ahat_halfPlane_L` 的方向被 `hswept` 钉死**：若 `⊥ p` 的泛函在 `vJ1` 上取负，
则它在 `Â` 上无下界。 -/
theorem no_lower_bound_of_swept {U : Set (ℤ × ℤ)} {p vJ1 nJ m : ℤ × ℤ} {cJ cL : ℤ}
    (hne : U.Nonempty) (hrec : ∀ g ∈ U, g + p ∈ U)
    (hsw : Nivat.MaxEnv.SweptClosed U vJ1 nJ cJ)
    (hα : 0 < dot nJ p) (hmp : dot m p = 0) (hmv : dot m vJ1 < 0)
    (hL : ∀ g ∈ U, cL ≤ dot m g) : False := by
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨T, hT⟩ : ∃ T : ℕ, dot m g₀ - cL + 1 ≤ (T : ℤ) :=
    ⟨(dot m g₀ - cL + 1).toNat, Int.self_le_toNat _⟩
  obtain ⟨z, hz, hzval⟩ := exists_low_of_swept hrec hsw hα hg₀ hmp T
  have h1 := hL z hz
  rw [hzval] at h1
  have hTnn : (0 : ℤ) ≤ (T : ℤ) := Int.natCast_nonneg T
  have hle : dot m vJ1 ≤ -1 := by omega
  have h3 : (T : ℤ) * dot m vJ1 ≤ (T : ℤ) * (-1) := mul_le_mul_of_nonneg_left hle hTnn
  linarith

/-- ⭐ **链上现货：`det p vJ` 与 `det p vJ1` 同号（弱）。** 不经 `bottom`、不经 `nfp_L`。 -/
theorem det_p_vJ_mul_det_p_vJ1_nonneg {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    0 ≤ det p c.vJ * det p c.vJ1 := by
  by_contra hcon
  have h' : det p c.vJ * det p c.vJ1 < 0 := not_le.mp hcon
  refine no_lower_bound_of_swept (m := (det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ))
    c.ahat_nonempty c.rec_p c.hswept (dot_nJ_p_pos_of_parts c) ?_ ?_ c.ahat_halfPlane_L
  · rw [dot_smul_left_orient, dot_perpVec_self, mul_zero]
  · rw [dot_smul_left_orient, dot_perpVec_eq_det]; exact h'

/-- ⭐ **集成者那组「全符号现货」数据不在链上。** `det p vJ = -1`、`det p vJ1 = 1`，
积 `= -1 < 0`，与 `det_p_vJ_mul_det_p_vJ1_nonneg` 冲突。

⟹ `HcombOrient.hcomb_fails_on_full_sign_stock` 证的是「这组**链外**数据推不出 `hcomb`」，
它**不**证明 `hcomb` 在链上无产者。 -/
theorem stock_witness_not_on_chain {α : Type*} {η xper : Config α} {gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper
      ((1, -1) : ℤ × ℤ) ((-1, 1) : ℤ × ℤ) S gen)
    (hvJ : c.vJ = (1, 0)) (hvJ1 : c.vJ1 = (1, -2)) : False := by
  have h := det_p_vJ_mul_det_p_vJ1_nonneg c
  rw [hvJ, hvJ1] at h
  norm_num [det] at h

/-! ## §20 定向的符号那一半是链上现货；欠账缩成一条整除 `det p vJ1 ∣ det p vJ` -/

/-- **Cramer ＋ `det vJ W₀ = 0`**：`(dot nJ p * det p vJ1) • vJ = (det p vJ) • W₀`。
这是 `ray_eq` 的「共线」那一半的定量形，无前提地把 `vJ` 与 `W₀` 的比值写成两个 `det` 的比。 -/
theorem ray_identity_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    ((dot c.nJ p) * det p c.vJ1) • c.vJ = (det p c.vJ) • W₀ c.nJ p c.vJ1 := by
  have hdet0 : det c.vJ (W₀ c.nJ p c.vJ1) = 0 :=
    det_vJ_W₀_vacuous c.nJ_prim.ne_zero c.F.dot_nJ_vJ
  have h := cramer_smul p c.vJ (W₀ c.nJ p c.vJ1)
  rw [hdet0, zero_smul, sub_eq_zero, det_p_W₀] at h
  exact h

/-- ⭐ **定向（符号）是链上现货**：`0 ≤ det p vJ * det p W₀`。
与 `ray_identity_of_parts` 合起来就是「`vJ` 与 `W₀` 正向平行」。 -/
theorem orient_sign_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    0 ≤ (det p c.vJ) * det p (W₀ c.nJ p c.vJ1) := by
  rw [det_p_W₀]
  have h1 := det_p_vJ_mul_det_p_vJ1_nonneg c
  have h2 : 0 < dot c.nJ p := dot_nJ_p_pos_of_parts c
  have h3 : det p c.vJ * (dot c.nJ p * det p c.vJ1)
      = dot c.nJ p * (det p c.vJ * det p c.vJ1) := by ring
  rw [h3]
  exact mul_nonneg (le_of_lt h2) h1

/-- ⭐ **欠账缩成一条整除。** 有了 `det p vJ1 ∣ det p vJ`（且 `det p vJ1 ≠ 0`），
定向谓词 `hOrient` 的射线那一半**在链上自由**——`t : ℕ` 由 `det p vJ / det p vJ1` 直接给出，
非负性来自 §19。 -/
theorem hOrient_of_dvd {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hne : det p c.vJ1 ≠ 0) (hdvd : det p c.vJ1 ∣ det p c.vJ) :
    ∃ t : ℕ, (dot c.nJ p) • c.vJ = (t : ℤ) • W₀ c.nJ p c.vJ1 := by
  obtain ⟨k, hk⟩ := hdvd
  have hsign := det_p_vJ_mul_det_p_vJ1_nonneg c
  have hsq : 0 < det p c.vJ1 ^ 2 := by
    rcases lt_trichotomy (det p c.vJ1) 0 with h | h | h
    · nlinarith
    · exact absurd h hne
    · nlinarith
  have hk0 : 0 ≤ k := by
    by_contra hkneg
    have hkneg' : k < 0 := not_le.mp hkneg
    have hrw : det p c.vJ * det p c.vJ1 = det p c.vJ1 ^ 2 * k := by rw [hk]; ring
    rw [hrw] at hsign
    have hneg : det p c.vJ1 ^ 2 * k < 0 := mul_neg_of_pos_of_neg hsq hkneg'
    linarith
  refine ⟨k.toNat, ?_⟩
  have hkt : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
  rw [hkt]
  have hray := ray_identity_of_parts c
  rw [hk] at hray
  have e1 := congrArg Prod.fst hray
  have e2 := congrArg Prod.snd hray
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
  rw [Prod.ext_iff]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨mul_left_cancel₀ hne ?_, mul_left_cancel₀ hne ?_⟩
  · linear_combination e1
  · linear_combination e2

/-- ⭐ **接链形**：`Primitive p` ＋ `det p vJ1 ∣ det p vJ` ⟹ `rec_vJ`。
结论逐字符等于 `RecVJComb.parts_rec_vJ` 的结论。 -/
theorem rec_vJ_of_dvd_of_prim_p {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) (hp : Primitive p)
    (hne : det p c.vJ1 ≠ 0) (hdvd : det p c.vJ1 ∣ det p c.vJ) :
    ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      g + c.vJ ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i :=
  rec_vJ_of_hOrient_of_prim_p c hp (hOrient_of_dvd c hne hdvd)

/-! ## §21 hbase 的 `hcomb_fails_under_full_cone_stock` 与 §19/§20 对齐

hbase 2026-09-26 报（我未复跑其证明体，只复跑了下面这两条数值）：`nJ=(0,1)`、`vl=(-3,-2)`、
`c=1`、`p=(3,2)`、`vJ1=(-1,-2)`、`vJ=(1,0)`，`hcomb` 对一切 `a t : ℤ` 假，死因是纯整性。

下面两条是我自己算的：那组数据**通过** §19 的同号筛，**卡在** §20 的整除。
⟹ 两条判据互相独立，§19 不蕴含 §20。 -/

/-- hbase 那组数据上定向谓词也为假（`α • vJ = (2,0)`、`W₀ = (4,0)`，`t = 1/2 ∉ ℤ`），
所以它与 `rec_vJ_of_hOrient` 不冲突：那条的前件在这组数据上就不成立。 -/
theorem hbase_witness_orient_false :
    ∀ t : ℤ, (dot ((0, 1) : ℤ × ℤ) ((3, 2) : ℤ × ℤ)) • ((1, 0) : ℤ × ℤ)
      ≠ t • W₀ ((0, 1) : ℤ × ℤ) ((3, 2) : ℤ × ℤ) ((-1, -2) : ℤ × ℤ) := by
  intro t h
  rw [Prod.ext_iff] at h
  simp only [W₀, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at h
  omega

/-- hbase 那组数据：`det p vJ = -2`、`det p vJ1 = -4`，积 `= 8 ≥ 0`（过 §19），
但 `-4 ∤ -2`（卡 §20）。 -/
theorem hbase_witness_sign_ok_dvd_fails :
    0 ≤ det ((3, 2) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) * det ((3, 2) : ℤ × ℤ) ((-1, -2) : ℤ × ℤ) ∧
      ¬ (det ((3, 2) : ℤ × ℤ) ((-1, -2) : ℤ × ℤ) ∣ det ((3, 2) : ℤ × ℤ) ((1, 0) : ℤ × ℤ)) := by
  constructor
  · norm_num [det]
  · rintro ⟨k, hk⟩
    norm_num [det] at hk
    omega

/-! ## §22 `hcomb` 的**精确**闭形式：`det p vJ1` 上的两条 ℕ-整除（不经 `W₀`、不经 `Primitive p`）

§20 走的是 `W₀` 路线，代价是还要一条 `α ∣ t·β`（`Primitive p` 时才自由，`c ≥ 2` 时不自由）。
直接对 `{p, vJ1}` 用 Cramer 就没有这个代价：`det p vJ1 ≠ 0` 时，`hcomb` 的两个系数由

    a = det vJ vJ1 / det p vJ1 ,      t = det p vJ / det p vJ1

唯一定出，于是 `hcomb` **等价于**这两个商都落在 ℕ 里（`hcomb_iff_cramer`，是 `↔`，两个方向都证）。
⟹ 洞 1 的 `rec_vJ` 欠账精确地是这两条，其中 `t` 那条的**符号**已由 §19 免费（`nat_t_of_dvd`），
`a` 那条的符号还没有产者。 -/

/-- 平面二维展开：`(det p q) • x = (det x q) • p + (det p x) • q`。 -/
theorem cramer_expand (p q x : ℤ × ℤ) :
    (det p q) • x = (det x q) • p + (det p x) • q := by
  rw [Prod.ext_iff]
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> ring

/-- ⭐ **`hcomb` 的精确闭形式**（`det p vJ1 ≠ 0` 下的 `↔`）。 -/
theorem hcomb_iff_cramer {p vJ1 vJ : ℤ × ℤ} (hne : det p vJ1 ≠ 0) :
    (∃ a t : ℕ, vJ = (a : ℤ) • p + (t : ℤ) • vJ1) ↔
      ((∃ a : ℕ, det vJ vJ1 = det p vJ1 * (a : ℤ)) ∧
        (∃ t : ℕ, det p vJ = det p vJ1 * (t : ℤ))) := by
  constructor
  · rintro ⟨a, t, rfl⟩
    refine ⟨⟨a, ?_⟩, ⟨t, ?_⟩⟩ <;>
      · simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
  · rintro ⟨⟨a, ha⟩, ⟨t, ht⟩⟩
    refine ⟨a, t, ?_⟩
    have h := cramer_expand p vJ1 vJ
    rw [ha, ht] at h
    rw [Prod.ext_iff] at h ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h ⊢
    exact ⟨mul_left_cancel₀ hne (by linear_combination h.1),
      mul_left_cancel₀ hne (by linear_combination h.2)⟩

/-- **`t` 的符号由 §19 免费**：有整除就有 ℕ-商，不必另外假设非负。 -/
theorem nat_t_of_dvd {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hne : det p c.vJ1 ≠ 0) (hdvd : det p c.vJ1 ∣ det p c.vJ) :
    ∃ t : ℕ, det p c.vJ = det p c.vJ1 * (t : ℤ) := by
  obtain ⟨k, hk⟩ := hdvd
  have hsign := det_p_vJ_mul_det_p_vJ1_nonneg c
  have hsq : 0 < det p c.vJ1 ^ 2 := by
    rcases lt_trichotomy (det p c.vJ1) 0 with h | h | h
    · nlinarith
    · exact absurd h hne
    · nlinarith
  have hk0 : 0 ≤ k := by
    by_contra hkneg
    have hkneg' : k < 0 := not_le.mp hkneg
    have hrw : det p c.vJ * det p c.vJ1 = det p c.vJ1 ^ 2 * k := by rw [hk]; ring
    rw [hrw] at hsign
    have hneg : det p c.vJ1 ^ 2 * k < 0 := mul_neg_of_pos_of_neg hsq hkneg'
    linarith
  exact ⟨k.toNat, by rw [Int.toNat_of_nonneg hk0]; exact hk⟩

/-- ⭐ **接链形（无 `Primitive p`）**：`det p vJ1 ≠ 0` ＋ 两条 ℕ-整除 ⟹ `rec_vJ`。
结论逐字符等于 `RecVJComb.parts_rec_vJ` 的结论。 -/
theorem rec_vJ_of_cramer {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hne : det p c.vJ1 ≠ 0)
    (ha : ∃ a : ℕ, det c.vJ c.vJ1 = det p c.vJ1 * (a : ℤ))
    (hdvd : det p c.vJ1 ∣ det p c.vJ) :
    ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      g + c.vJ ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i := by
  obtain ⟨a, t, hc⟩ := (hcomb_iff_cramer hne).mpr ⟨ha, nat_t_of_dvd c hne hdvd⟩
  exact Nivat.LaneTowerHbaseRecVJ.parts_rec_vJ c hc

/-! ## §23 欠账的第三种写法：一个整数 `s`，要它同时整除 `dot nJ p` 与 `- dot nJ vJ1`

`vJ_prim` ＋ `det vJ W₀ = 0` ⟹ `W₀ = s • vJ`，`s : ℤ` 唯一（`scale_of_parts`）。
把 `W₀` 的定义代回去，`hcomb` 的两个系数直接读出来：

    - dot nJ vJ1 = s * a ,      dot nJ p = s * t

⟹ `hcomb` 只要 `s ∣ dot nJ p` ＋ `s ∣ (- dot nJ vJ1)` ＋ `0 < s`（`hcomb_of_scale`，
证明只是把 `s` 约掉，不用 Cramer、不用 `Primitive p`）。符号侧 `0 < s` 由 §19 给（`det p vJ ≠ 0` 时）。

⟹ 三种等价写法，供纸面定位挑一个最像原文的标的：
* §20 `W₀` 形：`det p vJ1 ∣ det p vJ` ＋ `α ∣ t·β`；
* §22 Cramer 形：`det p vJ1` 整除 `det p vJ` 与 `det vJ vJ1`（**精确**，`↔`）；
* §23 content 形：`W₀` 沿 `vJ` 的伸缩因子 `s` 整除 `dot nJ p` 与 `- dot nJ vJ1`。

`rec_vJ_of_unimodular` 是 §22 形最好用的特例：`det p vJ1 = ±1` 时两条整除**全免**，只剩一条符号。 -/

/-- 本原向量的共线伴随必是它的整数倍。 -/
theorem exists_scale_of_prim {u w : ℤ × ℤ} (hu : Primitive u) (hdet : det u w = 0) :
    ∃ s : ℤ, w = s • u := by
  obtain ⟨x, y, hxy⟩ := hu
  refine ⟨x * w.1 + y * w.2, ?_⟩
  rw [Prod.ext_iff]
  simp only [det] at hdet
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · linear_combination (-w.1) * hxy + (-y) * hdet
  · linear_combination (-w.2) * hxy + x * hdet

/-- `W₀ = s • vJ`，`s : ℤ`（`vJ_prim` ＋ `det_vJ_W₀_vacuous`）。 -/
theorem scale_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    ∃ s : ℤ, W₀ c.nJ p c.vJ1 = s • c.vJ :=
  exists_scale_of_prim c.vJ_prim (det_vJ_W₀_vacuous c.nJ_prim.ne_zero c.F.dot_nJ_vJ)

/-- ⭐ **把 `s` 约掉就是 `hcomb`**：不用 Cramer、不用 `Primitive p`、不用 `det p vJ1 ≠ 0`。 -/
theorem hcomb_of_scale {nJ p vJ1 vJ : ℤ × ℤ} {s : ℤ} (hs : s ≠ 0)
    (hW : W₀ nJ p vJ1 = s • vJ) {a t : ℕ}
    (ha : - dot nJ vJ1 = s * (a : ℤ)) (ht : dot nJ p = s * (t : ℤ)) :
    vJ = (a : ℤ) • p + (t : ℤ) • vJ1 := by
  have e1 := congrArg Prod.fst hW
  have e2 := congrArg Prod.snd hW
  simp only [W₀, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at e1 e2
  rw [Prod.ext_iff]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · refine mul_left_cancel₀ hs ?_
    linear_combination -e1 + p.1 * ha + vJ1.1 * ht
  · refine mul_left_cancel₀ hs ?_
    linear_combination -e2 + p.2 * ha + vJ1.2 * ht

/-- ⭐ **接链形（content 版）**：`0 < s` ＋ 两条整除 ⟹ `rec_vJ`。
两个 ℕ-商的非负性是免费的——`0 < dot nJ p`（`dot_nJ_p_pos_of_parts`）与
`0 < - dot nJ vJ1`（`hsweep`）自动把商顶到正数。 -/
theorem rec_vJ_of_scale_dvd {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) {s : ℤ} (hs : 0 < s)
    (hW : W₀ c.nJ p c.vJ1 = s • c.vJ)
    (hda : s ∣ (- dot c.nJ c.vJ1)) (hdt : s ∣ dot c.nJ p) :
    ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      g + c.vJ ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i := by
  obtain ⟨a', ha'⟩ := hda
  obtain ⟨t', ht'⟩ := hdt
  have hβ : 0 < - dot c.nJ c.vJ1 := by linarith [c.hsweep]
  have hα : 0 < dot c.nJ p := dot_nJ_p_pos_of_parts c
  have hpa : 0 < s * a' := by rw [← ha']; exact hβ
  have hpt : 0 < s * t' := by rw [← ht']; exact hα
  have ha0 : 0 ≤ a' := by
    by_contra hcon
    linarith [mul_neg_of_pos_of_neg hs (not_le.mp hcon), hpa]
  have ht0 : 0 ≤ t' := by
    by_contra hcon
    linarith [mul_neg_of_pos_of_neg hs (not_le.mp hcon), hpt]
  have hc := hcomb_of_scale (ne_of_gt hs) hW (a := a'.toNat) (t := t'.toNat)
    (by rw [Int.toNat_of_nonneg ha0]; exact ha')
    (by rw [Int.toNat_of_nonneg ht0]; exact ht')
  exact Nivat.LaneTowerHbaseRecVJ.parts_rec_vJ c hc

/-- ⭐ **`det p vJ1 = ±1` 时两条整除全免，只剩一条符号。** -/
theorem rec_vJ_of_unimodular {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hdet : det p c.vJ1 = 1 ∨ det p c.vJ1 = -1)
    (hsign : 0 ≤ det p c.vJ1 * det c.vJ c.vJ1) :
    ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      g + c.vJ ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i := by
  have hne : det p c.vJ1 ≠ 0 := by rcases hdet with h | h <;> rw [h] <;> norm_num
  refine rec_vJ_of_cramer c hne ?_ ?_
  · rcases hdet with h | h
    · have h0 : 0 ≤ det c.vJ c.vJ1 := by rw [h, one_mul] at hsign; exact hsign
      exact ⟨(det c.vJ c.vJ1).toNat, by rw [h, one_mul, Int.toNat_of_nonneg h0]⟩
    · have h0 : 0 ≤ - det c.vJ c.vJ1 := by rw [h] at hsign; linarith
      exact ⟨(- det c.vJ c.vJ1).toNat, by
        rw [h, Int.toNat_of_nonneg h0]; ring⟩
  · rcases hdet with h | h <;> rw [h]
    · exact one_dvd _
    · exact ⟨- det p c.vJ, by ring⟩

/-! ## §24 把 §19／§22 整体改挂到本原方向 `-vl` 上（集成者 2026-09-26 §4 派工）

集成者 `RecVJPrimDir.lean` 的杠杆：`rec_of_comb`（`RecVJComb.lean`）的方向是自由变量，
而帽子并集对 `-vl` 的封闭是更原始的事实（`LaneLeafAGenRecP.rec_p_free`，零链外假设），
`rec_p` 才是它迭代 `c` 次的推论。⟹ 侧条件可以整条搬到 `-vl` 上。

搬过去以后 **`Primitive` 那一格就地兑现**（`Primitive vl` 是 `exists_chainData` 的 binder），
于是我 §1–§18 的 `hcomb_iff_ray` 前提满足，**整除那一半由 Bezout 免费**：

* `rec_vJ_negvl_of_hOrient`：唯一链外输入是**纯定向** `∃ t : ℕ, ⟪nJ,−vl⟫ • vJ = t • W₀ nJ (−vl) vJ1`。
  ⟹ 缺失字段报告的标的回到一条，与集成者 §1 的判断一致，也与 lane-tower-hbase 2026-09-26
  「验收标准退回『只要定向』」同向（他走实锥、我走 Bezout，两条独立）。
* `rec_vJ_negvl_of_cramer`：Cramer 版，第 3 条按集成者 `cramer3_negvl_of_cramer3` 少一个因子 `c`。

⚠ §19 的同号筛**不必**重跑在 `-vl` 上：`det p x = c · det (−vl) x`（`RecVJPrimDir.det_p_eq_smul`）
⟹ 两个乘积只差 `c² > 0`，符号相同，代数转移即可（`det_negvl_mul_nonneg_of_parts`）。
⟹ 我没有用 `rec_p_free` 的那一串 leaf A binder，`hrec` 在下面是显式 binder。

⚠ 射程：本节**不**构造 `hOrient`，也不主张它有产者。 -/

/-- `Primitive v → Primitive (-v)`。 -/
theorem primitive_neg {v : ℤ × ℤ} (h : Primitive v) : Primitive (-v) := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨-x, -y, ?_⟩
  simp only [Prod.fst_neg, Prod.snd_neg]
  linear_combination hxy

/-- `hhp` 的并集形（`RecVJComb` 里的同名 `private` 引理的公开重建）。 -/
theorem union_hhp_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i, c.cJ ≤ dot c.nJ g := by
  intro g hg
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
  exact c.hhp i hi

/-- 整除 ＋ 同号 ⟹ ℕ-商（`nat_t_of_dvd` 的无结构版）。 -/
theorem nat_quotient_of_dvd {D N : ℤ} (hne : D ≠ 0) (hsign : 0 ≤ N * D) (hdvd : D ∣ N) :
    ∃ t : ℕ, N = D * (t : ℤ) := by
  obtain ⟨k, hk⟩ := hdvd
  have hsq : 0 < D ^ 2 := by
    rcases lt_trichotomy D 0 with h | h | h
    · nlinarith
    · exact absurd h hne
    · nlinarith
  have hk0 : 0 ≤ k := by
    by_contra hcon
    have hkneg : k < 0 := not_le.mp hcon
    have hrw : N * D = D ^ 2 * k := by rw [hk]; ring
    rw [hrw] at hsign
    linarith [mul_neg_of_pos_of_neg hsq hkneg]
  exact ⟨k.toNat, by rw [Int.toNat_of_nonneg hk0]; exact hk⟩

/-- §19 的同号筛转移到 `-vl`：两个乘积只差 `c² > 0`。 -/
theorem det_negvl_mul_nonneg_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {cc : ℕ}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hc : 0 < cc) (hp : p = -(cc : ℤ) • vl) :
    0 ≤ det (-vl) c.vJ * det (-vl) c.vJ1 := by
  have h := det_p_vJ_mul_det_p_vJ1_nonneg c
  rw [Nivat.RecVJPrimDir.det_p_eq_smul hp, Nivat.RecVJPrimDir.det_p_eq_smul hp] at h
  have hc' : (0 : ℤ) < (cc : ℤ) := by exact_mod_cast hc
  have hcc2 : (0 : ℤ) < (cc : ℤ) * (cc : ℤ) := mul_pos hc' hc'
  by_contra hcon
  have hX : det (-vl) c.vJ * det (-vl) c.vJ1 < 0 := not_le.mp hcon
  nlinarith [mul_neg_of_pos_of_neg hcc2 hX, h]

/-- ⭐⭐ **本轮最紧的接链形：唯一链外输入是纯定向。**
`Primitive vl` ⟹ `Primitive (-vl)` ⟹ `hcomb_iff_ray` 的 Bezout 前提就地兑现
⟹ 整除那一半免费。`hrec` 由 `LaneLeafAGenRecP.rec_p_free` 兑现（零链外假设，集成者
`RecVJPrimDir.rec_vJ_free_of_comb_negvl` 已把那串 binder 接好）。 -/
theorem rec_vJ_negvl_of_hOrient {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {cc : ℕ}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hc : 0 < cc) (hp : p = -(cc : ℤ) • vl) (hvl : Primitive vl)
    (hrec : ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      g + (-vl) ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i)
    (hOrient : ∃ t : ℕ, (dot c.nJ (-vl)) • c.vJ = (t : ℤ) • W₀ c.nJ (-vl) c.vJ1) :
    ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      g + c.vJ ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i := by
  have hαpos : 0 < dot c.nJ (-vl) :=
    Nivat.RecVJPrimDir.dot_nJ_negvl_pos hc hp (dot_nJ_p_pos_of_parts c)
  obtain ⟨a, t, hcomb⟩ :=
    (hcomb_iff_ray (primitive_neg hvl) hαpos c.hsweep c.F.dot_nJ_vJ).mpr hOrient
  exact Nivat.LaneTowerHbaseRecVJ.rec_of_comb (union_hhp_of_parts c) c.hswept hrec
    c.F.dot_nJ_vJ hcomb

/-- ⭐ **Cramer 版的 `-vl` 形**：第 3 条按 `RecVJPrimDir.cramer3_negvl_of_cramer3`
比 `p`-版少一个因子 `c`；第 2 条的符号仍由 §19 免费。 -/
theorem rec_vJ_negvl_of_cramer {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {cc : ℕ}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hc : 0 < cc) (hp : p = -(cc : ℤ) • vl)
    (hrec : ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      g + (-vl) ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i)
    (hne : det (-vl) c.vJ1 ≠ 0)
    (ha : ∃ a : ℕ, det c.vJ c.vJ1 = det (-vl) c.vJ1 * (a : ℤ))
    (hdvd : det (-vl) c.vJ1 ∣ det (-vl) c.vJ) :
    ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      g + c.vJ ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i := by
  have ht := nat_quotient_of_dvd hne (det_negvl_mul_nonneg_of_parts c hc hp) hdvd
  obtain ⟨a, t, hcomb⟩ := (hcomb_iff_cramer hne).mpr ⟨ha, ht⟩
  exact Nivat.LaneTowerHbaseRecVJ.rec_of_comb (union_hhp_of_parts c) c.hswept hrec
    c.F.dot_nJ_vJ hcomb

/-! ## §25 `det p vJ ≠ 0` 是字段的推论 ⟹ `rec_vJ` 的链外欠账只剩一条

lane-tower-hbase 2026-09-26 §20（`TowerHbaseRecP.lean` 的 `rec_vJ_of_det_sieve`）把 `rec_vJ`
的链外输入收成三条：`det p vJ ≠ 0`、`det p vJ1 ≠ 0`、`0 ≤ det p vJ * det p vJ1`。
第三条是我 §19 的 `det_p_vJ_mul_det_p_vJ1_nonneg`（字段直出）。本节证**第一条也是字段直出**：

`det p vJ = 0` ＋ `vJ ≠ 0` ⟹ `(⟪nJ,p⟫) • vJ = 0`（两个分量各一行 `linear_combination`，
只用 `dot nJ vJ = 0`）⟹ `⟪nJ,p⟫ = 0`，与 `dot_nJ_p_pos_of_parts` 矛盾。
⟹ 「`vJ ∦ p`」不是几何义务，是 `dot_nJ_vJ` ＋ `dot_nJ_p` 的代数推论。

⟹ **链外只剩 `det p vJ1 ≠ 0`（= `vJ1 ∦ p`，在 `p = -c•vl` 下即 `vJ1 ∦ vl`）。**

🔴 **撤回我 2026-09-26 给集成者的 §113 反向差**：我当时写「帽子并集的格凸性在树里没有现成实例，
只有逐个 `A i` 的」。**错**。`RecVJFromParts.lean` 的 `latticeConvex_of_parts` 直接产
`IsLatticeConvexRegion (⋃ i, hatOf c.A c.kk vl i)`，形参只有 `c` 一个，零额外 binder
（我本轮读了它的声明并在下面 `rec_vJ_of_parts_of_det_ne` 里实际喂进去，编译是内核给的证据）。
⟹ hbase 那条实锥路线的 `hconv` **不要钱**，我之前给集成者的「代价未知，请裁」这个前提作废。

⚠ 射程：`det p vJ1 ≠ 0` 我**没有**产者，也不主张它成立；`GcdCollapse` 里有它为 `0` 的那一格。 -/

/-- ⭐ **`vJ ∦ p` 是代数推论，不是几何义务。**
只用「`vJ` 非零」「`vJ ⊥ nJ`」「`⟪nJ,p⟫ ≠ 0`」三条。 -/
theorem det_ne_zero_of_perp {nJ p v : ℤ × ℤ} (hv : v ≠ 0)
    (hperp : dot nJ v = 0) (hα : dot nJ p ≠ 0) : det p v ≠ 0 := by
  intro hdet
  have hd : p.1 * v.2 - p.2 * v.1 = 0 := hdet
  have hq : nJ.1 * v.1 + nJ.2 * v.2 = 0 := hperp
  have h1 : dot nJ p * v.1 = 0 := by
    show (nJ.1 * p.1 + nJ.2 * p.2) * v.1 = 0
    linear_combination p.1 * hq - nJ.2 * hd
  have h2 : dot nJ p * v.2 = 0 := by
    show (nJ.1 * p.1 + nJ.2 * p.2) * v.2 = 0
    linear_combination p.2 * hq + nJ.1 * hd
  have hv1 : v.1 = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hα
    · exact h
  have hv2 : v.2 = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hα
    · exact h
  refine hv ?_
  rw [Prod.ext_iff]
  constructor
  · simpa using hv1
  · simpa using hv2

/-- 链上实例：`vJ_prim.ne_zero` ＋ `F.dot_nJ_vJ` ＋ `dot_nJ_p_pos_of_parts`。 -/
theorem det_p_vJ_ne_zero_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    det p c.vJ ≠ 0 :=
  det_ne_zero_of_perp c.vJ_prim.ne_zero c.F.dot_nJ_vJ (dot_nJ_p_pos_of_parts c).ne'

/-- §19 的 `≥ 0` ＋ 上一条 ⟹ 严格 `> 0`，只欠 `det p vJ1 ≠ 0`。 -/
theorem det_prod_pos_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hne1 : det p c.vJ1 ≠ 0) :
    0 < det p c.vJ * det p c.vJ1 :=
  lt_of_le_of_ne (det_p_vJ_mul_det_p_vJ1_nonneg c)
    (Ne.symm (mul_ne_zero (det_p_vJ_ne_zero_of_parts c) hne1))

/-- `det p (s • v) = s * det p v`。 -/
theorem det_smul_right (p v : ℤ × ℤ) (s : ℤ) : det p (s • v) = s * det p v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- ⭐ §23 那个 `s` 的**符号**由 §19 的同号筛决定，不需要任何整除。
`det p W₀ = α · det p vJ1`（`det_p_W₀`，无条件）＝ `s · det p vJ`（代 `W₀ = s • vJ`），
两边乘 `det p vJ`：`s · (det p vJ)² = α · (det p vJ · det p vJ1)`，右边两因子皆正。
（与 hbase `TowerHbaseRecP.lean` 的 `hb_scale_pos` 同命题，我独立证，未 import 他的；
去重挂集成者，§110.2。） -/
theorem scale_pos_of_sieve {nJ p vJ1 vJ : ℤ × ℤ} {s : ℤ}
    (hW : W₀ nJ p vJ1 = s • vJ) (hα : 0 < dot nJ p)
    (hdpv : det p vJ ≠ 0) (hprod : 0 < det p vJ * det p vJ1) : 0 < s := by
  have h := det_p_W₀ nJ p vJ1
  rw [hW, det_smul_right] at h
  have key : dot nJ p * det p vJ1 = s * det p vJ := h.symm
  have hsq : 0 < det p vJ * det p vJ := mul_self_pos.mpr hdpv
  have hmul : dot nJ p * (det p vJ * det p vJ1) = s * (det p vJ * det p vJ) := by
    linear_combination (det p vJ) * key
  have hpos : 0 < dot nJ p * (det p vJ * det p vJ1) := mul_pos hα hprod
  by_contra hcon
  have hs : s ≤ 0 := not_lt.mp hcon
  nlinarith [hmul, hpos, mul_nonneg (neg_nonneg.mpr hs) hsq.le]

/-- ⭐⭐ **字段 ＋ `det p vJ1 ≠ 0` ⟹ `W₀` 是 `vJ` 的正整数倍。**
这正是 hbase `rec_vJ_of_W₀_pos_multiple` 的输入，且**不经 `bottom`**。 -/
theorem exists_pos_scale_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hne1 : det p c.vJ1 ≠ 0) :
    ∃ s : ℤ, 0 < s ∧ W₀ c.nJ p c.vJ1 = s • c.vJ := by
  obtain ⟨s, hW⟩ := scale_of_parts c
  exact ⟨s, scale_pos_of_sieve hW (dot_nJ_p_pos_of_parts c) (det_p_vJ_ne_zero_of_parts c)
    (det_prod_pos_of_parts c hne1), hW⟩

/-- ⭐⭐⭐ **`rec_vJ` 的 `bottom`-free 版：字段 ＋ 一条非退化 `det p vJ1 ≠ 0`。**

对照 `RecVJFromParts.rec_vJ_of_parts`（已有，走 `c.bottom`）：本条**不碰 `bottom`**，
代价是多一条 `det p vJ1 ≠ 0`。`hconv` 由 `latticeConvex_of_parts` 供给（形参只有 `c`）。
整除一条不要——根源是 `recCone` 是实锥（hbase §19.2）。

⚠ **2026-09-26 自订正（第 245 轮）：上一句原写「免费供给」，过强。**
`latticeConvex_of_parts` 经 `Colle35.latticeConvex_iUnion_hatOf` **吃 `maxA` ＋ `hfin` ＋
`AhatMono`** 三条 A 侧字段。「形参只有 `c`」为真（不需额外 binder），「免费」为假（有字段代价）。
⟹ 本条的准确定价是「**`bottom`-free，但吃 A 侧三条 ＋ 下列八条**」。

⭐ **`bottom`-free 是闭包穷举的结论，不是「本层没看到」（§87）**：
`exists_pos_scale_of_parts` 展开为 `scale_of_parts` ＋ `scale_pos_of_sieve`（不吃 `c`）＋
`dot_nJ_p_pos_of_parts` ＋ `det_p_vJ_ne_zero_of_parts` ＋ `det_prod_pos_of_parts`，字段访问
并集恰为八条：`vJ_prim` / `nJ_prim` / `F.dot_nJ_vJ` / `hhp` / `rec_p` / `ahat_nonempty` /
`hswept` / `ahat_halfPlane_L`。机械证据：**`.bottom` 在本文件全文只命中 1 次且在 docstring
里**（哨兵：同一 grep 在 `RecVJFromParts.lean` 命中 `c.bottom` 2 次，会响）。外层
`TowerHbase.rec_vJ_of_W₀_pos_multiple` 不吃 `c`、九个实参全显式 ⟹ 亦够不到 `bottom`。

⭐ **A 侧三条确实推不出 `rec_vJ`**（故承重前提真在 `hne1` ＋ 上列八条）：
`EnvRefuteMaxA.exists_maxA_for_ray` 在 hlev 的 `Rdeg` 上兑现 `maxA` ＋ `hfin` ＋ `AhatMono`，
而同一居民上 `TowerHlevCover.not_rec_vJ_Rdeg` 证 `rec_vJ` 对 `vJ = (1,0)` 为假。
⛔ 射程：以上全部关于 `det p vJ1 ≠ 0`（横截）支；共线格走
`RecVJFromParts.rec_vJ_of_parts`，那条**确实吃 `c.bottom`**，本条不改善那一支。 -/
theorem rec_vJ_of_parts_of_det_ne {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hne1 : det p c.vJ1 ≠ 0) :
    ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      g + c.vJ ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i := by
  obtain ⟨g₀, hg₀⟩ := c.ahat_nonempty
  obtain ⟨s, hs, hW⟩ := exists_pos_scale_of_parts c hne1
  exact Nivat.TowerHbase.rec_vJ_of_W₀_pos_multiple
    (Nivat.LaneLeafAGenRecVJ.latticeConvex_of_parts c) hg₀ (union_hhp_of_parts c) c.rec_p
    c.hswept (dot_nJ_p_pos_of_parts c).le c.hsweep.le hs hW

/-- **对齐 hbase §20.3**：他那组数据 `p=(3,2)`、`vJ=(1,0)`、`vJ1=(-1,-2)` 上
`s = 4`（`W₀ = 4 • vJ`）而 `α = ⟪nJ,p⟫ = 2` ⟹ `s ∤ α`。
⟹ **同一组数据上：实锥路线可用、我 §23 的 `s ∣ α` 路线不可用。**
这是对我自己 §23／§24 标的的反向见证，不是对他的。 -/
theorem hbase_witness_scale_pos_but_dvd_fails :
    W₀ ((0 : ℤ), (1 : ℤ)) ((3 : ℤ), (2 : ℤ)) ((-1 : ℤ), (-2 : ℤ))
        = (4 : ℤ) • ((1 : ℤ), (0 : ℤ))
      ∧ (0 : ℤ) < 4
      ∧ ¬ ((4 : ℤ) ∣ dot ((0 : ℤ), (1 : ℤ)) ((3 : ℤ), (2 : ℤ))) := by
  refine ⟨?_, by norm_num, ?_⟩
  · simp only [W₀, dot]
    decide
  · decide

/-! ## §26 `det p vJ1 ≠ 0` 的产者：横截格（集成者 2026-09-26 派工）

集成者的定位：`p` 是 `ChainDataGeomParts` 的**参数**，结构内部没有字段把 `p` 和 `vl` 绑起来；
绑定发生在消费者侧（`RegionSteps` 的 `exists_neg_multiple_of_perp`，给 `p = -(c:ℤ)•vl`、
`c : ℕ`、`0 < c`，且 `c = 1` 不被强制）。⟹ 消费者处 `det p vJ1 ≠ 0` ⟺ `det vl vJ1 ≠ 0`，
逐字就是「横截格」。本节把这个 ⟺ 证出来，并接到 §25 上。

⚠ 射程：本节**不**主张 `det vl vJ1 ≠ 0` 成立，只把 `p`-形的欠账换成 `vl`-形的欠账。
共线格上它恰为 `0`（`GcdCollapse` 的 `det_p_vJ1_eq_zero`，lane-tower-hbase 指的那一格）。 -/

/-- `det (-v) x = - det v x`。 -/
theorem det_neg_left (v x : ℤ × ℤ) : det (-v) x = - det v x := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]
  ring

/-- ⭐ **`p = -c•vl`（`0 < c`）下，`det p · ≠ 0` 与 `det vl · ≠ 0` 同真。**
`det p x = (c:ℤ) * det (-vl) x`（`RecVJPrimDir.det_p_eq_smul`）＝ `-(c:ℤ) * det vl x`，
`c ≠ 0` ⟹ 两边同零同非零。 -/
theorem det_p_ne_zero_iff_transverse {vl p x : ℤ × ℤ} {c : ℕ}
    (hc : 0 < c) (hp : p = -(c : ℤ) • vl) :
    det p x ≠ 0 ↔ det vl x ≠ 0 := by
  have hc' : (c : ℤ) ≠ 0 := by
    exact_mod_cast hc.ne'
  have hval : det p x = -((c : ℤ) * det vl x) := by
    rw [Nivat.RecVJPrimDir.det_p_eq_smul hp, det_neg_left]
    ring
  rw [hval, neg_ne_zero]
  exact ⟨fun h => fun h0 => h (by rw [h0, mul_zero]), fun h => mul_ne_zero hc' h⟩

/-- 集成者本轮要的那条（`RecVJTransverse` 的 `hdet` 产者）。 -/
theorem det_p_vJ1_ne_zero_of_transverse {vl p vJ1 : ℤ × ℤ} {c : ℕ}
    (hc : 0 < c) (hp : p = -(c : ℤ) • vl) (htr : det vl vJ1 ≠ 0) :
    det p vJ1 ≠ 0 :=
  (det_p_ne_zero_iff_transverse hc hp).mpr htr

/-- ⭐⭐ §25 ＋ §26：**`rec_vJ` 在横截格上只吃字段 ＋ `p = -c•vl`。**
链外输入只剩 `det vl c.vJ1 ≠ 0` 一条，且**不经 `bottom`**。 -/
theorem rec_vJ_of_parts_of_transverse {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {cc : ℕ}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hc : 0 < cc) (hp : p = -(cc : ℤ) • vl) (htr : det vl c.vJ1 ≠ 0) :
    ∀ g ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      g + c.vJ ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i :=
  rec_vJ_of_parts_of_det_ne c (det_p_vJ1_ne_zero_of_transverse hc hp htr)

/-! ## §27 共线格上 `W₀` 家族整条为空：`det p vJ1 ≠ 0` 是必要条件，不是方便条件

lane-tower-hbase 2026-09-26 §23 报：剩下那条 `det p vJ1 ≠ 0` 逐字等价于原文的 `J > ι+1`，
而 `J = ι+1` 那一支作者显式承认存在 ⟹ §25/§26 以及集成者 `RecVJTransverse`、他 §20–§23，
四条全部只覆盖横截格。**原文那一半我按禁令 42 不核、不引**；本节只把**链上那一半**证成内核事实：

设 `det p vJ1 = 0`。由 `scale_of_parts` 取 `W₀ = s • vJ`，
`det_p_W₀` 给 `s · det p vJ = ⟪nJ,p⟫ · det p vJ1 = 0`，而 §25 的 `det_p_vJ_ne_zero_of_parts`
说 `det p vJ ≠ 0` ⟹ **`s = 0` ⟹ `W₀ = 0`**。

⟹ 共线格上不存在正倍数 `W₀ = s • vJ`（`0 < s`），**即 `exists_pos_scale_of_parts` 的那条
非退化前提是必要的**，删不掉；任何以 `W₀` 的正倍数／ℕ-射线／实锥方向为入口的路线
（我 §20/§25、hbase §18–§23、hlev 的 `rec_vJ_of_ray_W`）在那一格上全部空转。
这与 hbase 报的 `W₀ = (det p vJ1) • dir nJ` 闭式同向，但**不经那条闭式**，只用字段。

⚠ 射程：本节**不**证共线格在链上可达，也**不**证 `rec_vJ` 在那里为假——只证 `W₀` 这个入口在那里为空。 -/

/-- `Primitive vl` 下 `det vl x = 0 ⟺ x` 是 `vl` 的整数倍。 -/
theorem det_vl_eq_zero_iff_multiple {vl x : ℤ × ℤ} (hvl : Primitive vl) :
    det vl x = 0 ↔ ∃ m : ℤ, x = m • vl := by
  constructor
  · exact fun h => exists_scale_of_prim hvl h
  · rintro ⟨m, rfl⟩
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- §26 那条 ⟺ 的零形。 -/
theorem det_p_eq_zero_iff_transverse {vl p x : ℤ × ℤ} {c : ℕ}
    (hc : 0 < c) (hp : p = -(c : ℤ) • vl) :
    det p x = 0 ↔ det vl x = 0 := by
  have h := det_p_ne_zero_iff_transverse (x := x) hc hp
  constructor
  · intro h0
    by_contra hcon
    exact h.mpr hcon h0
  · intro h0
    by_contra hcon
    exact h.mp hcon h0

/-- **共线格的刻画**：`p = -c•vl`（`0 < c`）＋ `Primitive vl` 下，
`det p vJ1 = 0 ↔ ∃ m, vJ1 = m • vl`。（与 lane-tower-hbase 的
`hb_det_p_vJ1_eq_zero_iff_collinear` 同命题，我独立证、未 import 他那条。） -/
theorem det_p_vJ1_eq_zero_iff_collinear {vl p vJ1 : ℤ × ℤ} {c : ℕ}
    (hc : 0 < c) (hp : p = -(c : ℤ) • vl) (hvl : Primitive vl) :
    det p vJ1 = 0 ↔ ∃ m : ℤ, vJ1 = m • vl :=
  (det_p_eq_zero_iff_transverse hc hp).trans (det_vl_eq_zero_iff_multiple hvl)

/-- `s • v = 0` ＋ `v ≠ 0` ⟹ `s = 0`。 -/
theorem smul_eq_zero_left {s : ℤ} {v : ℤ × ℤ} (hv : v ≠ 0) (h : s • v = 0) : s = 0 := by
  by_contra hs
  refine hv ?_
  have h1 : s * v.1 = 0 := by
    have := congrArg Prod.fst h
    simpa using this
  have h2 : s * v.2 = 0 := by
    have := congrArg Prod.snd h
    simpa using this
  rw [Prod.ext_iff]
  constructor
  · simpa using (mul_eq_zero.mp h1).resolve_left hs
  · simpa using (mul_eq_zero.mp h2).resolve_left hs

/-- ⭐ **共线格上 `W₀ = 0`**，只用字段 ＋ §25 的 `det p vJ ≠ 0`。 -/
theorem W₀_eq_zero_of_collinear_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (h0 : det p c.vJ1 = 0) :
    W₀ c.nJ p c.vJ1 = 0 := by
  obtain ⟨s, hW⟩ := scale_of_parts c
  have hd := det_p_W₀ c.nJ p c.vJ1
  rw [hW, det_smul_right, h0, mul_zero] at hd
  have hs : s = 0 := by
    rcases mul_eq_zero.mp hd with h | h
    · exact h
    · exact absurd h (det_p_vJ_ne_zero_of_parts c)
  rw [hW, hs, zero_smul]

/-- ⭐⭐ **共线格上正倍数不存在** ⟹ `exists_pos_scale_of_parts` 的非退化前提是必要的。 -/
theorem no_pos_scale_of_collinear_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (h0 : det p c.vJ1 = 0) :
    ¬ ∃ s : ℤ, 0 < s ∧ W₀ c.nJ p c.vJ1 = s • c.vJ := by
  rintro ⟨s, hs, hW⟩
  rw [W₀_eq_zero_of_collinear_of_parts c h0] at hW
  exact hs.ne' (smul_eq_zero_left c.vJ_prim.ne_zero hW.symm)

/-! ## §28 退化格里 `rec_vJ` 不是「还没接好」，是**这一束前提根本推不出它**

§27 只说 `W₀` 那个入口在退化格为空，lane-tower-hlev 的 `not_hcomb_of_degenerate` 说 `hcomb`
在那里为假。两条都是「某条路走不通」。本节给的是**整束前提的反例**：

取 `nJ = p = (0,1)`、`vl = vJ1 = (0,-1)`（故 `p = -(1:ℤ) • vl`、`det p vJ1 = 0`，退化）、
`vJ = (1,0)`、`cJ = 0`、`cL = -5`，`U := [-5,0] × [0,∞)`。
它把三条免-`bottom` 路线实际用到的前提**全部**兑现：`Nonempty`、`hhp`、`rec_p`、`hswept`、
`hsweep`、`dot nJ vJ = 0`、`0 < dot nJ p`、三条 `Primitive`、`ahat_halfPlane_L`、`ahat_attained_L`、
以及 `IsLatticeConvexRegion`（真造了 `C` 并验了 `Convex` / `IsClosed` / `toReal ⁻¹' C`）。
**而 `rec_vJ` 为假**：`(0,0) ∈ U`，`(0,0) + vJ = (1,0) ∉ U`。

⟹ 退化格必须有**这束之外**的输入。`bottom` 正是这样一条（`RecVJFromParts.rec_vJ_of_parts`
无条件给 `rec_vJ`），所以本见证反过来也说明：**它必然违反 `bottom`**——否则和那条冲突。

⚠ PROTOCOL §11 的申报：我兑现的就是上面列出的那些合取，**没有**构造完整的
`ChainDataGeomParts`（`A`/`B`/`u`/`kk`/`maxA`/`escapeW`/`shellSubStrip`/`fillCover`/`F`/`bottom`/
`nfp_L` 等字段一概未兑现，其中 `bottom` 按上一段必然不成立）。
⟹ 本条否掉的是**「这一束前提蕴含 `rec_vJ`」**，**不是**「链上退化格里 `rec_vJ` 为假」。
后者我没证、也不主张。 -/

/-- §28 的见证区域 `U = [-5,0] × [0,∞)`。 -/
def degenU : Set (ℤ × ℤ) := {g | 0 ≤ g.2 ∧ -5 ≤ g.1 ∧ g.1 ≤ 0}

/-- `degenU` 的实凸包 `C`。 -/
def degenC : Set (ℝ × ℝ) := {q | 0 ≤ q.2 ∧ -5 ≤ q.1 ∧ q.1 ≤ 0}

theorem mem_degenU {g : ℤ × ℤ} : g ∈ degenU ↔ (0 ≤ g.2 ∧ -5 ≤ g.1 ∧ g.1 ≤ 0) := Iff.rfl

theorem mem_degenC {q : ℝ × ℝ} : q ∈ degenC ↔ (0 ≤ q.2 ∧ -5 ≤ q.1 ∧ q.1 ≤ 0) := Iff.rfl

/-- `degenU` 是格凸区域：`C` 是三个闭半平面的交。 -/
theorem degen_latticeConvex : IsLatticeConvexRegion degenU := by
  refine ⟨degenC, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    rw [mem_degenC] at hx hy
    obtain ⟨hx1, hx2, hx3⟩ := hx
    obtain ⟨hy1, hy2, hy3⟩ := hy
    rw [mem_degenC]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · have h1 : IsClosed {q : ℝ × ℝ | 0 ≤ q.2} := isClosed_le continuous_const continuous_snd
    have h2 : IsClosed {q : ℝ × ℝ | (-5 : ℝ) ≤ q.1} := isClosed_le continuous_const continuous_fst
    have h3 : IsClosed {q : ℝ × ℝ | q.1 ≤ (0 : ℝ)} := isClosed_le continuous_fst continuous_const
    have he : degenC =
        {q : ℝ × ℝ | 0 ≤ q.2} ∩ ({q : ℝ × ℝ | (-5 : ℝ) ≤ q.1} ∩ {q : ℝ × ℝ | q.1 ≤ (0 : ℝ)}) := by
      ext q
      rw [mem_degenC]
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [he]
    exact h1.inter (h2.inter h3)
  · ext g
    rw [mem_degenU]
    show _ ↔ toReal g ∈ degenC
    rw [mem_degenC]
    simp only [toReal]
    constructor
    · rintro ⟨ha, hb, hc⟩
      exact ⟨by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hc⟩
    · rintro ⟨ha, hb, hc⟩
      exact ⟨by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hc⟩

/-- `degenU` 沿 `p = (0,1)` 封闭。 -/
theorem degen_rec_p : ∀ g ∈ degenU, g + ((0 : ℤ), (1 : ℤ)) ∈ degenU := by
  intro g hg
  rw [mem_degenU] at hg ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- `degenU` 是 `(vJ1 = (0,-1), nJ = (0,1), cJ = 0)`-swept。 -/
theorem degen_swept :
    Nivat.MaxEnv.SweptClosed degenU ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 := by
  intro g hg t hheight
  rw [mem_degenU] at hg
  have e1 : (g + (t : ℤ) • ((0 : ℤ), (-1 : ℤ))).1 = g.1 := by
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    ring
  have e2 : (g + (t : ℤ) • ((0 : ℤ), (-1 : ℤ))).2 = g.2 - (t : ℤ) := by
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    ring
  have hh : (0 : ℤ) ≤ g.2 - (t : ℤ) := by
    have hv : dot ((0 : ℤ), (1 : ℤ)) (g + (t : ℤ) • ((0 : ℤ), (-1 : ℤ))) = g.2 - (t : ℤ) := by
      simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [hv] at hheight
    exact hheight
  rw [mem_degenU, e1, e2]
  exact ⟨hh, hg.2.1, hg.2.2⟩

/-- ⭐⭐⭐ **退化格的全束反例**：免-`bottom` 路线实际用到的前提全部成立，`rec_vJ` 为假。 -/
theorem degen_bundle_not_enough :
    ((0 : ℤ), (1 : ℤ)) = -((1 : ℕ) : ℤ) • ((0 : ℤ), (-1 : ℤ))
      ∧ Primitive ((0 : ℤ), (-1 : ℤ)) ∧ Primitive ((0 : ℤ), (1 : ℤ))
      ∧ Primitive ((1 : ℤ), (0 : ℤ))
      ∧ det ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) = 0
      ∧ det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) ≠ 0
      ∧ dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0
      ∧ 0 < dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ))
      ∧ dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) < 0
      ∧ degenU.Nonempty
      ∧ IsLatticeConvexRegion degenU
      ∧ (∀ g ∈ degenU, (0 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) g)
      ∧ (∀ g ∈ degenU, g + ((0 : ℤ), (1 : ℤ)) ∈ degenU)
      ∧ Nivat.MaxEnv.SweptClosed degenU ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0
      ∧ (∀ g ∈ degenU,
          (-5 : ℤ) ≤ dot ((det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))) •
            ((-(1 : ℤ)), (0 : ℤ))) g)
      ∧ (∃ g ∈ degenU,
          dot ((det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))) • ((-(1 : ℤ)), (0 : ℤ))) g = -5)
      ∧ ¬ (∀ g ∈ degenU, g + ((1 : ℤ), (0 : ℤ)) ∈ degenU) := by
  refine ⟨by decide, ⟨0, -1, by norm_num⟩, ⟨0, 1, by norm_num⟩, ⟨1, 0, by norm_num⟩,
    by decide, by decide, by decide, by decide, by decide,
    ⟨((0 : ℤ), (0 : ℤ)), by rw [mem_degenU]; norm_num⟩,
    degen_latticeConvex, ?_, degen_rec_p, degen_swept, ?_, ?_, ?_⟩
  · intro g hg
    rw [mem_degenU] at hg
    show (0 : ℤ) ≤ 0 * g.1 + 1 * g.2
    omega
  · intro g hg
    rw [mem_degenU] at hg
    show (-5 : ℤ) ≤ _
    simp only [dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    omega
  · refine ⟨((-5 : ℤ), (0 : ℤ)), by rw [mem_degenU]; norm_num, ?_⟩
    simp only [dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    norm_num
  · intro hcon
    have h0 : ((0 : ℤ), (0 : ℤ)) ∈ degenU := by rw [mem_degenU]; norm_num
    have h1 := hcon _ h0
    rw [mem_degenU] at h1
    simp only [Prod.fst_add, Prod.snd_add] at h1
    omega

/-- ⭐ 新增：`degenU` 是一列**有限**集的**单调**并（＝ leafa-shell 那条前提族里
我 §28 缺的那一样；`hfin` ＋ `AhatMono` 的线性半边）。 -/
theorem degenU_chain :
    ∃ F : ℕ → Set (ℤ × ℤ), (∀ i, (F i).Finite) ∧ (∀ i j, i ≤ j → F i ⊆ F j) ∧
      degenU = ⋃ i, F i := by
  refine ⟨fun i => (fun q : ℤ × ℕ => ((q.1, (q.2 : ℤ)) : ℤ × ℤ)) ''
    (Set.Icc (-5 : ℤ) 0 ×ˢ Set.Iic i), ?_, ?_, ?_⟩
  · intro i
    exact ((Set.finite_Icc (-5 : ℤ) 0).prod (Set.finite_Iic i)).image _
  · intro i j hij
    refine Set.image_mono ?_
    rintro ⟨a, k⟩ ⟨ha, hk⟩
    exact ⟨ha, le_trans hk hij⟩
  · ext z
    rw [mem_degenU]
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_prod, Set.mem_Icc, Set.mem_Iic]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have ht : ((z.2.toNat : ℕ) : ℤ) = z.2 := Int.toNat_of_nonneg h1
      exact ⟨z.2.toNat, ⟨z.1, z.2.toNat⟩, ⟨⟨h2, h3⟩, le_refl _⟩,
        Prod.ext rfl (by simpa using ht)⟩
    · rintro ⟨i, ⟨a, k⟩, ⟨⟨ha1, ha2⟩, _⟩, rfl⟩
      exact ⟨Int.natCast_nonneg k, ha1, ha2⟩

/-- ⭐⭐⭐ **退化格：前提族严格包含 `LeafAShellLsideFork
.rec_vJ_not_from_linear_fields_collinear_lside`**（逐字抄它那 18 条，再多一条
`ahat_attained_L`），`rec_vJ` 仍不是推论。见证 `U = [-5,0] × [0,∞)`。 -/
theorem rec_vJ_not_from_linear_fields_collinear_with_attained :
    ¬ ∀ (U : Set (ℤ × ℤ)) (vl p nJ vJ vJ1 : ℤ × ℤ) (cc : ℕ) (cJ cL : ℤ),
        IsLatticeConvexRegion U →
        U.Nonempty →
        (∃ F : ℕ → Set (ℤ × ℤ), (∀ i, (F i).Finite) ∧ (∀ i j, i ≤ j → F i ⊆ F j) ∧
          U = ⋃ i, F i) →
        Primitive vl → Primitive nJ → Primitive vJ → Primitive vJ1 →
        0 < cc → p = -(cc : ℤ) • vl →
        (∀ z ∈ U, z + p ∈ U) →
        (∀ z ∈ U, cJ ≤ dot nJ z) →
        MaxEnv.SweptClosed U vJ1 nJ cJ →
        (∀ z ∈ U, cL ≤ dot (det p vJ • ((-p.2 : ℤ), p.1)) z) →
        (∃ z ∈ U, dot (det p vJ • ((-p.2 : ℤ), p.1)) z = cL) →
        dot nJ vJ = 0 → 0 < dot nJ p → dot nJ vJ1 < 0 →
        det p vJ ≠ 0 → det p vJ1 = 0 →
        (∀ z ∈ U, z + vJ ∈ U) := by
  intro h
  have h00 : ((0 : ℤ), (0 : ℤ)) ∈ degenU := by rw [mem_degenU]; norm_num
  have hcon := h degenU ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ))
      ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) 1 0 (-5)
      degen_latticeConvex ⟨_, h00⟩ degenU_chain
      ⟨0, -1, by norm_num⟩ ⟨0, 1, by norm_num⟩ ⟨1, 0, by norm_num⟩ ⟨0, -1, by norm_num⟩
      Nat.one_pos (by simp)
      degen_rec_p
      (by
        intro z hz
        rw [mem_degenU] at hz
        show (0 : ℤ) ≤ 0 * z.1 + 1 * z.2
        omega)
      degen_swept
      (by
        intro z hz
        rw [mem_degenU] at hz
        show (-5 : ℤ) ≤ _
        simp only [dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        omega)
      ⟨((-5 : ℤ), (0 : ℤ)), by rw [mem_degenU]; norm_num, by
        simp only [dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        norm_num⟩
      (by norm_num [dot]) (by norm_num [dot]) (by norm_num [dot])
      (by norm_num [det]) (by norm_num [det])
  have h1 := hcon _ h00
  rw [mem_degenU] at h1
  simp only [Prod.fst_add, Prod.snd_add] at h1
  omega

/-! ## §29  `ItemII` 正是杀死 §28 见证的那一格（内核，不是 docstring 阅读）

lane-tower-hlev 报（②，读签名）：增长判据的 Lean 对应物是 `faceLen` 无界，树里已有
sorry-free 生产链，`ChainDataGeomParts` 缺的是 `ItemII`（`ItemII.lean` 的
`Nivat.Colle35.ItemII`）。我自己核了两件事：
(1) `ChainPartsFeed.lean` 里 `ItemII` 的 7 处命中全是 `import` 行与注释，结构**确无**该字段；
(2) `LeafAJSelect.lean` 的 15 处 `sorry` 全在注释/docstring 里，无 tactic 位，`:162`
    那条「§2 …(`sorry`, …)」确是腐烂小节标题。

本节给的是**内核**版的路由确认：`ItemII` ＋ `subBA` 立刻把整个半平面塞进 `⋃ A i`，
⟹ §28 的见证 `degenU = [-5,0] × [0,∞)` 在 `ItemII` 下**当场不可满足**（`(1,0)` 在半平面里、
不在 `degenU` 里）。⟹ 「§28 之外」的候选不再只是一张字段表：`ItemII` 是**已验证**能杀死它的一条。

⚠ 射程：本节**不**主张 `ItemII` 加进 `ChainDataGeomParts` 后 `rec_vJ` 就证出来了
（那要 hlev 报的那条 `faceLen` 链真能合成，他自己标了「没验证」）。本节只说
「§28 的反例在 `ItemII` 下失效」，即那条反例的射程边界**恰好**在这一格。 -/

/-- `ItemII` ＋ `B i ⊆ A i` ⟹ 整个半平面 `{z | cz ≤ ⟪nl,z⟫}` 落进 `⋃ A i`。 -/
theorem halfPlane_sub_iUnion_of_itemII {B A : ℕ → Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (h2 : Nivat.Colle35.ItemII B nl cz) (hsub : ∀ i, B i ⊆ A i) :
    {z : ℤ × ℤ | cz ≤ dot nl z} ⊆ ⋃ i, A i := by
  intro z hz
  have hm0 : (0 : ℤ) ≤ max |z.1| |z.2| := le_trans (abs_nonneg z.1) (le_max_left _ _)
  have hcast : (((max |z.1| |z.2|).toNat + 1 : ℕ) : ℤ) - 1 = max |z.1| |z.2| := by
    push_cast
    rw [Int.toNat_of_nonneg hm0]
    ring
  refine Set.mem_iUnion.mpr ⟨(max |z.1| |z.2|).toNat + 1, hsub _ (h2 _ z ?_ ?_ hz)⟩
  · rw [hcast]; exact le_max_left _ _
  · rw [hcast]; exact le_max_right _ _

/-- ⭐⭐ **§28 的见证在 `ItemII` 下不可满足**：`(1,0)` 在半平面里却不在 `degenU` 里。 -/
theorem degenU_not_itemII {B A : ℕ → Set (ℤ × ℤ)}
    (h2 : Nivat.Colle35.ItemII B ((0 : ℤ), (1 : ℤ)) 0) (hsub : ∀ i, B i ⊆ A i)
    (hU : (⋃ i, A i) ⊆ degenU) : False := by
  have hhalf : ((1 : ℤ), (0 : ℤ)) ∈ {z : ℤ × ℤ | (0 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) z} := by
    show (0 : ℤ) ≤ 0 * 1 + 1 * 0
    norm_num
  have h1 : ((1 : ℤ), (0 : ℤ)) ∈ degenU :=
    hU (halfPlane_sub_iUnion_of_itemII h2 hsub hhalf)
  rw [mem_degenU] at h1
  omega

/-! ## §30  把 §29 从「杀死我这一个见证」升成「杀死整族条状见证」（全称 `nℓ` / `cz`）

§29 的 `degenU_not_itemII` 把 `nl` / `cz` 钉成了字面值 `(0,1)` / `0`。但链上的 `nℓ`、`cz`
由上游给定、不由我选 ⟹ 钉死字面值只证明了「某一组参数下失效」，**不足以**说「这族见证在
`ItemII` 下失效」。本节给全称版：对**任何** `nℓ ≠ 0`、**任何** `cz`，只要见证被一条竖条
（`|z.1| ≤ L`）或横条（`|z.2| ≤ L`）装住，`ItemII` 就与它矛盾。

⚠ `nℓ ≠ 0` 不能省，也不是我加的前提：`LeafAEdgeUnbounded.lean` 头部自己写明，取
`nℓ = 0` / `cz = 1` / `B := fun _ => ∅` 时 `ItemII` **空真**成立 ⟹ 不带 `nℓ ≠ 0` 的「杀」
是假绿。而 `LeafAEdgeUnbounded.exists_edge_unbounded` 的 binder 里 `hnℓ : nℓ ≠ 0` 正排在
`hItemII` 之前（本 lane 2026-09-26 04:05 自读该文件，mtime 2026-09-22 17:28:42），
所以这条前提是链上白送的。

⚠ 射程不变：本节仍**不**主张「`ChainDataGeomParts` 加了 `ItemII` 就证出 `rec_vJ`」。
本节只说：三份同格反例见证（本文件 §28 的 `degenU`、`LaneLeafAShellLsideFork
.collinearStrip_lside`、lane-tower-hbase §24 那个 `{z | z.1 = 0 ∧ 0 ≤ z.2}` 形）
**全都**落在 `not_itemII_of_subset_vstrip` / `_hstrip` 的射程里。 -/

/-- 算术零件：`m ≠ 0` 时可取到 `|k|` 任意大、且把 `m * k` 推过任意下界 `c` 的 `k`。 -/
theorem exists_abs_gt_mul_ge {m : ℤ} (hm : m ≠ 0) (c L : ℤ) :
    ∃ k : ℤ, L < |k| ∧ c ≤ m * k := by
  have hL0 : (0 : ℤ) ≤ |L| := abs_nonneg L
  have hLle : L ≤ |L| := le_abs_self L
  set K : ℤ := max (|L| + 1) c with hKdef
  have hKL : |L| + 1 ≤ K := le_max_left _ _
  have hKc : c ≤ K := le_max_right _ _
  have hK0 : (0 : ℤ) ≤ K := by omega
  rcases lt_or_gt_of_ne hm with h | h
  · refine ⟨-K, ?_, ?_⟩
    · rw [abs_neg, abs_of_nonneg hK0]; omega
    · have h1 : (1 : ℤ) ≤ -m := by omega
      have h2 : K ≤ -m * K := le_mul_of_one_le_left hK0 h1
      have heq : m * -K = -m * K := by ring
      rw [heq]
      exact le_trans hKc h2
  · refine ⟨K, ?_, ?_⟩
    · rw [abs_of_nonneg hK0]; omega
    · have h1 : (1 : ℤ) ≤ m := by omega
      exact le_trans hKc (le_mul_of_one_le_left hK0 h1)

/-- `nl ≠ 0` 的坐标形（避开已弃用的 `push_neg`）。 -/
theorem fst_ne_zero_or_snd_ne_zero {nl : ℤ × ℤ} (hnl : nl ≠ 0) : nl.1 ≠ 0 ∨ nl.2 ≠ 0 := by
  rcases eq_or_ne nl.1 0 with h1 | h1
  · exact Or.inr fun h2 => hnl (Prod.ext h1 h2)
  · exact Or.inl h1

/-- 任何 `nℓ ≠ 0` 的半平面都含 `|z.1|` 任意大的点 ⟹ 逃得出任何竖条。 -/
theorem exists_bigX_in_halfPlane {nl : ℤ × ℤ} (hnl : nl ≠ 0) (cz L : ℤ) :
    ∃ z : ℤ × ℤ, cz ≤ dot nl z ∧ L < |z.1| := by
  have hor : nl.1 ≠ 0 ∨ nl.2 ≠ 0 := fst_ne_zero_or_snd_ne_zero hnl
  rcases eq_or_ne nl.2 0 with h2 | h2
  · have h1 : nl.1 ≠ 0 := by
      rcases hor with h | h
      · exact h
      · exact absurd h2 h
    obtain ⟨k, hk1, hk2⟩ := exists_abs_gt_mul_ge h1 cz L
    refine ⟨(k, 0), ?_, hk1⟩
    show cz ≤ nl.1 * k + nl.2 * 0
    rw [h2]; linarith
  · have hL0 : (0 : ℤ) ≤ |L| := abs_nonneg L
    have hLle : L ≤ |L| := le_abs_self L
    obtain ⟨k, _, hk2⟩ := exists_abs_gt_mul_ge h2 (cz - nl.1 * (|L| + 1)) 0
    refine ⟨(|L| + 1, k), ?_, ?_⟩
    · show cz ≤ nl.1 * (|L| + 1) + nl.2 * k
      linarith
    · show L < |(|L| + 1)|
      rw [abs_of_pos (by omega : (0 : ℤ) < |L| + 1)]
      omega

/-- 横条版：任何 `nℓ ≠ 0` 的半平面都含 `|z.2|` 任意大的点。 -/
theorem exists_bigY_in_halfPlane {nl : ℤ × ℤ} (hnl : nl ≠ 0) (cz L : ℤ) :
    ∃ z : ℤ × ℤ, cz ≤ dot nl z ∧ L < |z.2| := by
  have hor : nl.1 ≠ 0 ∨ nl.2 ≠ 0 := fst_ne_zero_or_snd_ne_zero hnl
  rcases eq_or_ne nl.1 0 with h1 | h1
  · have h2 : nl.2 ≠ 0 := by
      rcases hor with h | h
      · exact absurd h1 h
      · exact h
    obtain ⟨k, hk1, hk2⟩ := exists_abs_gt_mul_ge h2 cz L
    refine ⟨(0, k), ?_, hk1⟩
    show cz ≤ nl.1 * 0 + nl.2 * k
    rw [h1]; linarith
  · have hL0 : (0 : ℤ) ≤ |L| := abs_nonneg L
    have hLle : L ≤ |L| := le_abs_self L
    obtain ⟨k, _, hk2⟩ := exists_abs_gt_mul_ge h1 (cz - nl.2 * (|L| + 1)) 0
    refine ⟨(k, |L| + 1), ?_, ?_⟩
    · show cz ≤ nl.1 * k + nl.2 * (|L| + 1)
      linarith
    · show L < |(|L| + 1)|
      rw [abs_of_pos (by omega : (0 : ℤ) < |L| + 1)]
      omega

/-- ⭐⭐⭐ **整族「竖条」见证在 `ItemII` 下不可满足**，`nℓ`（只要非零）与 `cz` 全称。 -/
theorem not_itemII_of_subset_vstrip {B A : ℕ → Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz L : ℤ}
    {U : Set (ℤ × ℤ)} (hnl : nl ≠ 0)
    (h2 : Nivat.Colle35.ItemII B nl cz) (hsub : ∀ i, B i ⊆ A i)
    (hU : (⋃ i, A i) ⊆ U) (hstrip : ∀ z ∈ U, |z.1| ≤ L) : False := by
  obtain ⟨z, hz, hzL⟩ := exists_bigX_in_halfPlane hnl cz L
  have hzU : z ∈ U := hU (halfPlane_sub_iUnion_of_itemII h2 hsub hz)
  exact absurd (hstrip z hzU) (not_le.mpr hzL)

/-- ⭐⭐⭐ 「横条」版。 -/
theorem not_itemII_of_subset_hstrip {B A : ℕ → Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz L : ℤ}
    {U : Set (ℤ × ℤ)} (hnl : nl ≠ 0)
    (h2 : Nivat.Colle35.ItemII B nl cz) (hsub : ∀ i, B i ⊆ A i)
    (hU : (⋃ i, A i) ⊆ U) (hstrip : ∀ z ∈ U, |z.2| ≤ L) : False := by
  obtain ⟨z, hz, hzL⟩ := exists_bigY_in_halfPlane hnl cz L
  have hzU : z ∈ U := hU (halfPlane_sub_iUnion_of_itemII h2 hsub hz)
  exact absurd (hstrip z hzU) (not_le.mpr hzL)

/-- §28 见证 `degenU` 的全称版（§29 那条是它在 `nl = (0,1)`、`cz = 0` 的特例）。 -/
theorem degenU_not_itemII_forall {B A : ℕ → Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hnl : nl ≠ 0) (h2 : Nivat.Colle35.ItemII B nl cz) (hsub : ∀ i, B i ⊆ A i)
    (hU : (⋃ i, A i) ⊆ degenU) : False :=
  not_itemII_of_subset_vstrip (L := 5) hnl h2 hsub hU (by
    intro z hz
    rw [mem_degenU] at hz
    exact abs_le.mpr ⟨by omega, by omega⟩)

/-- lane-leafa-shell 的共线见证 `collinearStrip_lside = {z | z.1 ≤ 0 ∧ z.2 = 0}` 同样不可满足
（横条，`L = 0`）。这条不是转述他的读数：`collinearStrip_lside` 在本文件的 import 闭包里，
由内核自己检查。 -/
theorem collinearStrip_lside_not_itemII {B A : ℕ → Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    (hnl : nl ≠ 0) (h2 : Nivat.Colle35.ItemII B nl cz) (hsub : ∀ i, B i ⊆ A i)
    (hU : (⋃ i, A i) ⊆ Nivat.LaneLeafAShellLsideFork.collinearStrip_lside) : False :=
  not_itemII_of_subset_hstrip (L := 0) hnl h2 hsub hU (by
    intro z hz
    have : z.2 = 0 := hz.2
    rw [this]
    simp)

/-- lane-tower-hbase §24 的见证形 `{z | z.1 = 0 ∧ 0 ≤ z.2}` 也不可满足（竖条，`L = 0`）。
陈述用**形状**而非他的标识符（他的文件不在我的 import 闭包里，规矩 55：不转述别人的读数）。 -/
theorem vline_witness_not_itemII {B A : ℕ → Set (ℤ × ℤ)} {nl : ℤ × ℤ} {cz : ℤ}
    {U : Set (ℤ × ℤ)} (hnl : nl ≠ 0)
    (h2 : Nivat.Colle35.ItemII B nl cz) (hsub : ∀ i, B i ⊆ A i)
    (hU : (⋃ i, A i) ⊆ U) (hline : ∀ z ∈ U, z.1 = 0) : False :=
  not_itemII_of_subset_vstrip (L := 0) hnl h2 hsub hU (by
    intro z hz
    rw [hline z hz]
    simp)

/-! ## §31  证伪优先：`ItemII` ＋ `hhp` 把 `nℓ` 钉死成 `nJ`

⛔⛔ **第 246 轮自撤：本节带 `hvl : 0 ≤ dot nJ vl` 的五条在链上空真**（`②`，依据是集成者
第 246 轮通报的 `p = -c • vl`，`c > 0`，来自 `exists_chainData` 的 `hp_neg`；该 binder 对
本 lane 封闭，我**无权亲读**，故标 ②）。机制一行：本文件 `dot_nJ_p_pos_of_parts` 给
`0 < ⟪nJ,p⟫`，代入 `p = -c • vl` 得 `⟪nJ,p⟫ = -c · ⟪nJ,vl⟫ > 0` ⟹ **`⟪nJ,vl⟫ < 0` 严格**
⟹ `hvl` 与之对撞，链上恒假。受影响的正是：`halfPlane_le_of_itemII_of_hhp`、
`itemII_hhp_forces_codirectional`、`itemII_hhp_forces_nl_eq_nJ`、
`not_itemII_of_hhp_of_det_ne_zero`、`not_itemII_of_hhp_of_dot_nonpos`。

⚠ **不是翻个号就能修**：`halfPlane_le_of_itemII_of_hhp` 里 `hvl` 撑的是
`0 ≤ kk i * ⟪nJ,vl⟫` 然后 `linarith`；`⟪nJ,vl⟫ < 0` 时那一步方向反了，结论推不出来。
唯一的活路是 `kk i = 0`（平移消失），链上 `kk` 是否强制非零我不知道。

⚠ **射程边界（§66）**：本节**不**受影响的是 `halfPlane_sub_iUnion_of_itemII`（只吃
`ItemII` ＋ `subBA`，**不吃 `hvl`**，见其签名）——它给的是**未钉定向**的 `nℓ` 半平面，仍然活。
§29 / §30 也不吃 `hvl`，不连坐。按 §105 一条不删，只标注。

数值侧（`nJ=(0,1)`、`vJ=(1,0)`、`vl=vJ1=(1,-2)`、`p = -c • vl`，哨兵「`nJ` 翻号」已响）：
`c = 1,2,3` 时 `⟪nJ,vl⟫` 恒 `= -2 < 0`；顺带订正集成者那条 `p`-free 代入——
`|det p vJ| = ⟪nJ,p⟫` 代入后是 **`|det vl vJ| = -⟪nJ,vl⟫`**（左边 `p` 在 `abs` 里出 `+c`，
右边 `p` 在 `dot` 里线性出 `-c`，负号留下），不是他写的 `+⟪nJ,vl⟫`；他 ① 主体那条
`det`⟺`det` 的约化**是对的**（两边各两个 `p`，`c²` 约掉）。

集成者派的是「先看 `itemII_of_parts` 是不是假的」。他给的算式（我复核过，并且他自己订正了
上一版「方向正好相反」那句——`halfPlane_sub_iUnion_of_itemII` 的结论管 `A`，`hhp` 管
`hatOf A kk vl i = {z | z + kk i • vl ∈ A i}`，两者不是一句话能对撞的矛盾）是：
`z` 在 `nℓ`-半平面 ⟹ `z ∈ A i` ⟹ `z - kk i • vl ∈ hatOf A kk vl i` ⟹ 由 `hhp`
`cJ ≤ ⟪nJ,z⟫ - kk i * ⟪nJ,vl⟫`。

**我这里比他的判据多拿到两格**：
1. 他只在 `⟪nJ,vl⟫ = 0` 时消掉 `kk` 项，并把 `⟪nJ,vl⟫ ≠ 0` 整个留作「要算增长率」。其实
   `0 ≤ ⟪nJ,vl⟫` 就够：`kk i ≥ 0` ⟹ 减掉的是非负量 ⟹ `cJ ≤ ⟪nJ,z⟫` 照样成立。⟹ 只有
   `⟪nJ,vl⟫ < 0` 那一侧才真需要增长率，`= 0` 与 `> 0` 两侧都已封闭。
2. 结论不止「强约束」：配上链上白送的 `Primitive nJ`（`ChainPartsFeed` 的 `nJ_prim` 字段）
   与 `Primitive nℓ`，`⋂` 出来的是 **`nℓ = nJ`**（`det = 0` 由半平面比较得出，`nℓ = -nJ`
   被 `0 < ⟪nJ,nℓ⟫` 排除）。

⟹ **`itemII_of_parts` 只可能在 `nℓ := c.nJ` 这一个取法上成立**；任何要求 `nℓ ≠ c.nJ`
（例如 `nℓ` 取 ℓ 侧边法向）的接线当场为假，不必去证。这是给集成者 ④ 的答案，也是给
lane-tower-hbase 主攻 `itemII_of_parts` 的前置约束。

⚠ 数值实例（硬规矩 6，先算再派）：`nℓ = (0,1)`、`cz = 0`、`nJ = (1,0)`、`cJ = 0`、
`vl = (0,1)`（`⟪nJ,vl⟫ = 0`）⟹ 必要条件 `0 ≤ ⟪nJ,z⟫` 在整个上半平面上，死在格点
`z = (-1,0)`（`⟪nℓ,z⟫ = 0 ≥ cz`，`⟪nJ,z⟫ = -1 < 0`）。换成 `nJ = (0,2) = 2•nℓ`、`cJ = -5`
则不死 ⟹ 判据的牙齿恰好长在「非正倍数」上。

⚠ 射程：本节**不**证 `itemII_of_parts` 为假——它只把 `nℓ` 的取法压到唯一一个候选。
`⟪nJ,vl⟫ < 0` 那一侧我没封，别当已封。 -/

/-- 算术零件：`m ≠ 0` ⟹ `m * k` 可以压到任意上界之下。 -/
theorem exists_mul_lt {m : ℤ} (hm : m ≠ 0) (c : ℤ) : ∃ k : ℤ, m * k < c := by
  obtain ⟨k, _, hk⟩ := exists_abs_gt_mul_ge (neg_ne_zero.mpr hm) (1 - c) 0
  refine ⟨k, ?_⟩
  have heq : -m * k = -(m * k) := by ring
  rw [heq] at hk
  linarith

/-- `n ≠ 0` ⟹ `⟪n,n⟫ ≥ 1`（格上没有长度介于 0 与 1 之间的向量）。 -/
theorem one_le_dot_self {n : ℤ × ℤ} (hn : n ≠ 0) : 1 ≤ dot n n := by
  have key : ∀ x : ℤ, x ≠ 0 → 1 ≤ x * x := by
    intro x hx
    have hpos : 0 < x * x := mul_self_pos.mpr hx
    linarith [Int.lt_iff_add_one_le.mp hpos]
  have h1 : 0 ≤ n.1 * n.1 := mul_self_nonneg _
  have h2 : 0 ≤ n.2 * n.2 := mul_self_nonneg _
  show (1 : ℤ) ≤ n.1 * n.1 + n.2 * n.2
  rcases fst_ne_zero_or_snd_ne_zero hn with h | h
  · linarith [key _ h]
  · linarith [key _ h]

/-- 半平面非空：沿 `n` 本身走足够远即可。 -/
theorem exists_base_in_halfPlane {n : ℤ × ℤ} (hn : n ≠ 0) (c : ℤ) :
    ∃ m : ℤ, 0 ≤ m ∧ c ≤ dot n (m • n) := by
  have hQ : 1 ≤ dot n n := one_le_dot_self hn
  have hm0 : (0 : ℤ) ≤ max 0 c := le_max_left _ _
  have hmc : c ≤ max 0 c := le_max_right _ _
  refine ⟨max 0 c, hm0, ?_⟩
  have hstep : max 0 c ≤ max 0 c * dot n n := le_mul_of_one_le_right hm0 hQ
  have heq : dot n ((max 0 c) • n) = max 0 c * dot n n := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [heq]; linarith

/-- **横截时半平面必然逃出 `nJ`-半平面**：`det nℓ nJ ≠ 0` ⟹ 沿 `dir nℓ` 走，
`⟪nℓ,·⟫` 不变而 `⟪nJ,·⟫` 按 `det nℓ nJ` 线性地跑到任意负。 -/
theorem exists_halfPlane_dot_lt_of_det_ne_zero {nl nJ : ℤ × ℤ} (hnl : nl ≠ 0)
    (hD : det nl nJ ≠ 0) (cz cJ : ℤ) :
    ∃ z : ℤ × ℤ, cz ≤ dot nl z ∧ dot nJ z < cJ := by
  obtain ⟨m, _, hm⟩ := exists_base_in_halfPlane hnl cz
  obtain ⟨k, hk⟩ := exists_mul_lt hD (cJ - dot nJ (m • nl))
  refine ⟨m • nl + k • ((-nl.2 : ℤ), nl.1), ?_, ?_⟩
  · have heq : dot nl (m • nl + k • ((-nl.2 : ℤ), nl.1)) = dot nl (m • nl) := by
      simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [heq]; exact hm
  · have heq : dot nJ (m • nl + k • ((-nl.2 : ℤ), nl.1))
        = dot nJ (m • nl) + det nl nJ * k := by
      simp only [dot, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [heq]; linarith

/-- **反向平行时也逃得出**：`⟪nJ,nℓ⟫ < 0` ⟹ 沿 `nℓ` 走远，`⟪nℓ,·⟫` 上升而 `⟪nJ,·⟫` 下降。 -/
theorem exists_halfPlane_dot_lt_of_dot_neg {nl nJ : ℤ × ℤ} (hnl : nl ≠ 0)
    (hP : dot nJ nl < 0) (cz cJ : ℤ) :
    ∃ z : ℤ × ℤ, cz ≤ dot nl z ∧ dot nJ z < cJ := by
  have hQ : 1 ≤ dot nl nl := one_le_dot_self hnl
  have hm0 : (0 : ℤ) ≤ max (max 0 cz) (1 - cJ) :=
    le_trans (le_max_left 0 cz) (le_max_left _ _)
  have hmcz : cz ≤ max (max 0 cz) (1 - cJ) :=
    le_trans (le_max_right 0 cz) (le_max_left _ _)
  have hmcJ : 1 - cJ ≤ max (max 0 cz) (1 - cJ) := le_max_right _ _
  refine ⟨(max (max 0 cz) (1 - cJ)) • nl, ?_, ?_⟩
  · have heq : dot nl ((max (max 0 cz) (1 - cJ)) • nl)
        = max (max 0 cz) (1 - cJ) * dot nl nl := by
      simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have hstep : max (max 0 cz) (1 - cJ) ≤ max (max 0 cz) (1 - cJ) * dot nl nl :=
      le_mul_of_one_le_right hm0 hQ
    rw [heq]; linarith
  · have heq : dot nJ ((max (max 0 cz) (1 - cJ)) • nl)
        = max (max 0 cz) (1 - cJ) * dot nJ nl := by
      simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have hP1 : dot nJ nl ≤ -1 := by linarith
    have hstep : max (max 0 cz) (1 - cJ) * dot nJ nl
        ≤ max (max 0 cz) (1 - cJ) * (-1) := mul_le_mul_of_nonneg_left hP1 hm0
    rw [heq]; linarith

/-- 与某非零向量既正交又平行的向量只能是零。 -/
theorem eq_zero_of_det_eq_zero_of_dot_eq_zero {nl nJ : ℤ × ℤ} (hnl : nl ≠ 0)
    (hD : det nl nJ = 0) (hP : dot nJ nl = 0) : nJ = 0 := by
  have hQ : 1 ≤ dot nl nl := one_le_dot_self hnl
  have hD' : nl.1 * nJ.2 - nl.2 * nJ.1 = 0 := hD
  have hP' : nJ.1 * nl.1 + nJ.2 * nl.2 = 0 := hP
  have hQ' : (1 : ℤ) ≤ nl.1 * nl.1 + nl.2 * nl.2 := hQ
  have h1 : nJ.1 * (nl.1 * nl.1 + nl.2 * nl.2) = 0 := by
    linear_combination nl.1 * hP' - nl.2 * hD'
  have h2 : nJ.2 * (nl.1 * nl.1 + nl.2 * nl.2) = 0 := by
    linear_combination nl.2 * hP' + nl.1 * hD'
  have hz1 : nJ.1 = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h (by omega)
  have hz2 : nJ.2 = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h (by omega)
  exact Prod.ext hz1 hz2

/-- ⭐ **集成者 ② 的必要条件，且把他的 `⟪nJ,vl⟫ = 0` 放宽成 `0 ≤ ⟪nJ,vl⟫`**：
`ItemII` ＋ `subBA` ＋ `hhp` ⟹ 整个 `nℓ`-半平面被 `nJ`-半平面装住。 -/
theorem halfPlane_le_of_itemII_of_hhp {B A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl nl nJ : ℤ × ℤ} {cz cJ : ℤ}
    (h2 : Nivat.Colle35.ItemII B nl cz) (hsub : ∀ i, B i ⊆ A i)
    (hhp : ∀ i, Nivat.Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hvl : 0 ≤ dot nJ vl) :
    ∀ z : ℤ × ℤ, cz ≤ dot nl z → cJ ≤ dot nJ z := by
  intro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (halfPlane_sub_iUnion_of_itemII h2 hsub hz)
  have hmem : z - (kk i : ℤ) • vl ∈ Nivat.Colle35.hatOf A kk vl i := by
    show z - (kk i : ℤ) • vl + (kk i : ℤ) • vl ∈ A i
    simpa using hi
  have hge : cJ ≤ dot nJ (z - (kk i : ℤ) • vl) := hhp i hmem
  have heq : dot nJ (z - (kk i : ℤ) • vl) = dot nJ z - (kk i : ℤ) * dot nJ vl := by
    simp only [dot, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hnn : 0 ≤ (kk i : ℤ) * dot nJ vl := mul_nonneg (Int.natCast_nonneg _) hvl
  rw [heq] at hge
  linarith

/-- ⭐⭐ 二择一：`ItemII` ＋ `hhp` ＋ `0 ≤ ⟪nJ,vl⟫` ⟹ `nℓ` 与 `nJ` 平行且同向。 -/
theorem itemII_hhp_forces_codirectional {B A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl nl nJ : ℤ × ℤ} {cz cJ : ℤ}
    (hnl : nl ≠ 0) (hnJ : nJ ≠ 0) (hvl : 0 ≤ dot nJ vl)
    (h2 : Nivat.Colle35.ItemII B nl cz) (hsub : ∀ i, B i ⊆ A i)
    (hhp : ∀ i, Nivat.Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ) :
    det nl nJ = 0 ∧ 0 < dot nJ nl := by
  have hkey := halfPlane_le_of_itemII_of_hhp h2 hsub hhp hvl
  have hdet : det nl nJ = 0 := by
    by_contra hD
    obtain ⟨z, hz1, hz2⟩ := exists_halfPlane_dot_lt_of_det_ne_zero hnl hD cz cJ
    exact absurd (hkey z hz1) (not_le.mpr hz2)
  refine ⟨hdet, ?_⟩
  rcases lt_trichotomy (dot nJ nl) 0 with h | h | h
  · obtain ⟨z, hz1, hz2⟩ := exists_halfPlane_dot_lt_of_dot_neg hnl h cz cJ
    exact absurd (hkey z hz1) (not_le.mpr hz2)
  · exact absurd (eq_zero_of_det_eq_zero_of_dot_eq_zero hnl hdet h) hnJ
  · exact h

/-- ⭐⭐⭐ **`nℓ` 被钉死**：再加上链上白送的两条 `Primitive`，`ItemII` 的法向只能**就是** `nJ`。
⟹ 任何取 `nℓ ≠ c.nJ` 的 `itemII_of_parts` 接线为假，不必去证。 -/
theorem itemII_hhp_forces_nl_eq_nJ {B A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl nl nJ : ℤ × ℤ} {cz cJ : ℤ}
    (hnlp : Primitive nl) (hnJp : Primitive nJ) (hvl : 0 ≤ dot nJ vl)
    (h2 : Nivat.Colle35.ItemII B nl cz) (hsub : ∀ i, B i ⊆ A i)
    (hhp : ∀ i, Nivat.Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ) :
    nl = nJ := by
  have hnl : nl ≠ 0 := (prim_iff_primitive.mpr hnlp).ne_zero
  have hnJ : nJ ≠ 0 := (prim_iff_primitive.mpr hnJp).ne_zero
  obtain ⟨hdet, hpos⟩ := itemII_hhp_forces_codirectional hnl hnJ hvl h2 hsub hhp
  rcases eq_or_neg_of_prim_of_det_eq_zero (prim_iff_primitive.mpr hnlp)
      (prim_iff_primitive.mpr hnJp) hdet with h | h
  · exact h.symm
  · exfalso
    have hself : dot nJ nl = - dot nl nl := by
      rw [h]
      simp only [dot, Prod.fst_neg, Prod.snd_neg]
      ring
    have hQ : 1 ≤ dot nl nl := one_le_dot_self hnl
    rw [hself] at hpos
    linarith

/-- 证伪形 (i)：横截 ⟹ `ItemII` 不可满足。 -/
theorem not_itemII_of_hhp_of_det_ne_zero {B A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl nl nJ : ℤ × ℤ} {cz cJ : ℤ}
    (hnl : nl ≠ 0) (hnJ : nJ ≠ 0) (hvl : 0 ≤ dot nJ vl)
    (h2 : Nivat.Colle35.ItemII B nl cz) (hsub : ∀ i, B i ⊆ A i)
    (hhp : ∀ i, Nivat.Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hD : det nl nJ ≠ 0) : False :=
  absurd (itemII_hhp_forces_codirectional hnl hnJ hvl h2 hsub hhp).1 hD

/-- 证伪形 (ii)：反向（含正交）⟹ `ItemII` 不可满足。 -/
theorem not_itemII_of_hhp_of_dot_nonpos {B A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl nl nJ : ℤ × ℤ} {cz cJ : ℤ}
    (hnl : nl ≠ 0) (hnJ : nJ ≠ 0) (hvl : 0 ≤ dot nJ vl)
    (h2 : Nivat.Colle35.ItemII B nl cz) (hsub : ∀ i, B i ⊆ A i)
    (hhp : ∀ i, Nivat.Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hP : dot nJ nl ≤ 0) : False :=
  absurd (itemII_hhp_forces_codirectional hnl hnJ hvl h2 hsub hhp).2 (not_lt.mpr hP)

/-! ## §32 `bottom` 的 `hline0`：承重前提是 `nprevJ`-支撑界（lane-env-refute 2026-09-26）

派工：证伪 `BottomReachMin.bottom_of_reachMin` 的 `hline0`（截面能否带洞 / 两段 / 双向无界）。
结论两半：`hline0_of_supp` 排除带洞与两段并**连带给出** `hdz` / `hz₀`；
`not_hline0_without_supp` 证明去掉 `hsupp` 后确实双向无界，`supp_fails_on_halfPlane` 保证
两条不冲突。⟹ `hline0` 现签名不必改，欠的是 `hsupp` 的生产者。
⚠ 本节**不用** `hrecT`（向上封闭只服务 `bottom` 第 2 合取）。
⚠ `bottom` 第 1＋2 合取的证伪已在主仓 `ANormal.not_bottom_of_shell_data`，本节不重复。
-/

/-! ## §1 两块零件 -/

/-- **支撑界沿 `vJ1` 传到 `Nivat.MaxEnv.reachSet`。** 承重的是 `dot nprevJ vJ1 = 0`：扫掠方向落在
`nprevJ` 的层线里，所以扫多远都不改 `nprevJ`-高度。 -/
theorem supp_reachSet {T : Set (ℤ × ℤ)} {vJ1 nprevJ V : ℤ × ℤ}
    (hnpvJ1 : dot nprevJ vJ1 = 0)
    (hsupp : ∀ z ∈ T, dot nprevJ z ≤ dot nprevJ V) :
    ∀ z ∈ Nivat.MaxEnv.reachSet T vJ1, dot nprevJ z ≤ dot nprevJ V := by
  rintro z ⟨g, hg, t, rfl⟩
  have hexp : dot nprevJ (g + (t : ℤ) • vJ1)
      = dot nprevJ g + (t : ℤ) * dot nprevJ vJ1 := by
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hexp, hnpvJ1, mul_zero, add_zero]
  exact hsupp g hg

/-- **同一条 `nJ`-层线上的两点相差 `vJ` 的整数倍。** `dot nJ (z - z') = 0` 与 `dot nJ vJ = 0`
让两者平行（`det_eq_zero_of_dot_eq_zero`），`Prim vJ` 把平行升成整数倍
（`exists_smul_of_det_eq_zero`）。 -/
theorem eq_add_zsmul_of_dot_eq {nJ vJ z z' : ℤ × ℤ} (hnJ : nJ ≠ 0) (hvJ : Prim vJ)
    (hnJvJ : dot nJ vJ = 0) (h : dot nJ z = dot nJ z') :
    ∃ k : ℤ, z = z' + k • vJ := by
  have hw : dot nJ (z - z') = 0 := by
    simp only [dot, Prod.fst_sub, Prod.snd_sub] at *
    linear_combination h
  have hdet : det vJ (z - z') = 0 := det_eq_zero_of_dot_eq_zero hnJ hnJvJ hw
  obtain ⟨a, ha⟩ := exists_smul_of_det_eq_zero hvJ hdet
  have h1 : z.1 - z'.1 = a * vJ.1 := congrArg Prod.fst ha
  have h2 : z.2 - z'.2 = a * vJ.2 := congrArg Prod.snd ha
  refine ⟨a, Prod.ext ?_ ?_⟩
  · show z.1 = z'.1 + (a • vJ).1
    simp only [Prod.smul_fst, smul_eq_mul]
    omega
  · show z.2 = z'.2 + (a • vJ).2
    simp only [Prod.smul_snd, smul_eq_mul]
    omega

/-! ## §2 `hline0` 由 `nprevJ`-支撑界给出，连带 `hdz` / `hz₀` -/

/-- ⭐ **`bottom_of_reachMin` 的 `hdz` ＋ `hz₀` ＋ `hline0` 三条 binder，一次给出。**

`hsupp` / `hnpvJ1` / `hnpvJ` 三条与 `BottomRoom.hband_of_far_corner` 族吃的**同名同型**。
`hne` 只是「该层的截面非空」，即 `bottom` 第 1 合取所断言的那件事。

证法：层线上的 `k`-集合非空（`k = 0`）且下有界（`hsupp` 经 `supp_reachSet` 传到 `Nivat.MaxEnv.reachSet`，
再用 `dot nprevJ vJ < 0` 把 `nprevJ`-上界翻成 `k`-下界），`Int.exists_least_of_bdd` 取最小元。
⚠ 全程**不用** `hrecT`：向上封闭是 `bottom` 第 2 合取的事，与 `hline0` 无关。 -/
theorem hline0_of_supp {T : Set (ℤ × ℤ)} {nJ vJ vJ1 nprevJ V : ℤ × ℤ} {cJ : ℤ} {ε : ℕ}
    (hnJ : nJ ≠ 0) (hvJ : Prim vJ) (hnJvJ : dot nJ vJ = 0)
    (hnpvJ1 : dot nprevJ vJ1 = 0) (hnpvJ : dot nprevJ vJ < 0)
    (hsupp : ∀ z ∈ T, dot nprevJ z ≤ dot nprevJ V)
    (hne : ∃ z ∈ Nivat.MaxEnv.reachSet T vJ1, dot nJ z = cJ - (ε : ℤ) - 1) :
    ∃ z₀ : ℤ × ℤ, dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧ z₀ ∈ Nivat.MaxEnv.reachSet T vJ1 ∧
      ∀ z ∈ Nivat.MaxEnv.reachSet T vJ1, dot nJ z = cJ - (ε : ℤ) - 1 →
        ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • vJ := by
  classical
  obtain ⟨zb, hzb, hlev⟩ := hne
  have hsuppR := supp_reachSet hnpvJ1 hsupp
  -- `zb` 处的层高在平移 `k • vJ` 下不变
  have hlevel : ∀ k : ℤ, dot nJ (zb + k • vJ) = cJ - (ε : ℤ) - 1 := by
    intro k
    have hexp : dot nJ (zb + k • vJ) = dot nJ zb + k * dot nJ vJ := by
      simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [hexp, hnJvJ, mul_zero, add_zero, hlev]
  set Pk : ℤ → Prop := fun k => zb + k • vJ ∈ Nivat.MaxEnv.reachSet T vJ1 with hPk
  have hinh : ∃ k : ℤ, Pk k := ⟨0, by simpa [hPk] using hzb⟩
  have hbdd : ∃ b : ℤ, ∀ k : ℤ, Pk k → b ≤ k := by
    refine ⟨-|dot nprevJ V - dot nprevJ zb| - 1, fun k hk => ?_⟩
    have hle : dot nprevJ (zb + k • vJ) ≤ dot nprevJ V := hsuppR _ hk
    have hexp : dot nprevJ (zb + k • vJ) = dot nprevJ zb + k * dot nprevJ vJ := by
      simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [hexp] at hle
    have hkm : k * dot nprevJ vJ ≤ dot nprevJ V - dot nprevJ zb := by linarith
    have hDabs : dot nprevJ V - dot nprevJ zb ≤ |dot nprevJ V - dot nprevJ zb| :=
      le_abs_self _
    rcases le_or_gt 0 k with h0 | h0
    · have h1 : (0 : ℤ) ≤ |dot nprevJ V - dot nprevJ zb| := abs_nonneg _
      linarith
    · have hm : 1 ≤ -dot nprevJ vJ := by omega
      have hnk : (0 : ℤ) ≤ -k := by omega
      have hge : -k ≤ (-k) * (-dot nprevJ vJ) := le_mul_of_one_le_right hnk hm
      have heq2 : (-k) * (-dot nprevJ vJ) = k * dot nprevJ vJ := by ring
      rw [heq2] at hge
      linarith
  obtain ⟨kmin, hkmin, hleast⟩ := Int.exists_least_of_bdd hbdd hinh
  refine ⟨zb + kmin • vJ, hlevel kmin, hkmin, ?_⟩
  intro z hz hzlev
  have hzb' : dot nJ z = dot nJ zb := by rw [hzlev, hlev]
  obtain ⟨a, ha⟩ := eq_add_zsmul_of_dot_eq hnJ hvJ hnJvJ hzb'
  have hPa : Pk a := by
    show zb + a • vJ ∈ Nivat.MaxEnv.reachSet T vJ1
    rw [← ha]; exact hz
  have hge : kmin ≤ a := hleast a hPa
  refine ⟨a - kmin, by omega, ?_⟩
  rw [ha, sub_smul]
  abel

/-! ## §3 去掉 `hsupp` 就假：上半平面的截面是整条层线

坐标系与 §2 的数值实例同一套（`nJ = (0,1)`、`vJ = (1,0)`、`vJ1 = (0,-1)`、
`nprevJ = (-1,0)`、`cJ = 0`、`ε = 0`），只把象限换成上半平面。 -/

/-- 上半平面沿 `(0,-1)` 扫掠覆盖整个格：任意 `z` 都由 `(z.1, z.2 + |z.2|)` 出发 `|z.2|` 步到达。 -/
theorem mem_reach_upper (z : ℤ × ℤ) :
    z ∈ Nivat.MaxEnv.reachSet {w : ℤ × ℤ | 0 ≤ w.2} ((0 : ℤ), (-1 : ℤ)) := by
  refine ⟨(z.1, z.2 + (z.2.natAbs : ℤ)), by simpa using (by omega : (0:ℤ) ≤ z.2 + z.2.natAbs),
    z.2.natAbs, ?_⟩
  ext <;> simp

/-- ⭐ **`hline0` 在去掉 `hsupp` 之后为假**，且被否掉的是**带全部其它前提**的版本：
`hrecT`、`hhp` 形的 `cJ ≤ dot nJ ·`、`ANormal.lean` 逼出的 `dot nJ vJ1 < 0`、
`dot nprevJ vJ1 = 0`、`dot nprevJ vJ < 0`、`Prim vJ`、`dot nJ vJ = 0`、截面非空 —— 全部兑现。
唯一缺的就是 `hsupp`（§4 证明它在这个 `T` 上对任何 `V` 都不成立）。

失效方式是**双向无界**，不是带洞、不是两段 —— §2 已把后两族一次性排除。 -/
theorem not_hline0_without_supp :
    ∃ (T : Set (ℤ × ℤ)) (nJ vJ vJ1 nprevJ : ℤ × ℤ) (cJ : ℤ),
      nJ ≠ 0 ∧ Prim vJ ∧ dot nJ vJ = 0 ∧
      (∀ g ∈ T, g + vJ ∈ T) ∧
      (∀ g ∈ T, cJ ≤ dot nJ g) ∧
      dot nJ vJ1 < 0 ∧
      dot nprevJ vJ1 = 0 ∧ dot nprevJ vJ < 0 ∧
      (∃ z ∈ Nivat.MaxEnv.reachSet T vJ1, dot nJ z = cJ - 1) ∧
      ¬ ∃ z₀ : ℤ × ℤ, dot nJ z₀ = cJ - 1 ∧ z₀ ∈ Nivat.MaxEnv.reachSet T vJ1 ∧
          ∀ z ∈ Nivat.MaxEnv.reachSet T vJ1, dot nJ z = cJ - 1 →
            ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • vJ := by
  refine ⟨{w : ℤ × ℤ | 0 ≤ w.2}, ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-1 : ℤ)), ((-1 : ℤ), (0 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Prod.ext_iff]
  · simp [Prim, Int.gcd]
  · simp [dot]
  · intro g hg
    show (0 : ℤ) ≤ (g + ((1 : ℤ), (0 : ℤ))).2
    have : (0 : ℤ) ≤ g.2 := hg
    simpa using this
  · intro g hg
    have : (0 : ℤ) ≤ g.2 := hg
    simpa [dot] using this
  · simp [dot]
  · simp [dot]
  · simp [dot]
  · exact ⟨((0 : ℤ), (-1 : ℤ)), mem_reach_upper _, by simp [dot]⟩
  · rintro ⟨z₀, hdz, -, hall⟩
    have hz₀2 : z₀.2 = -1 := by simpa [dot] using hdz
    obtain ⟨k, hk0, hk⟩ := hall (z₀.1 - 1, -1) (mem_reach_upper _) (by simp [dot])
    have h1 : z₀.1 - 1 = z₀.1 + k := by
      have := congrArg Prod.fst hk
      simpa using this
    omega

/-! ## §4 `hsupp` 在上半平面上对任何 `V` 都不成立 —— §2 与 §3 不冲突 -/

/-- **§2 与 §3 的分界线就是 `hsupp`。** 上半平面在 `nprevJ = (-1,0)` 方向向上无界，
所以 §3 的 `T` 不在 §2 的射程内，两条同时成立。 -/
theorem supp_fails_on_halfPlane (V : ℤ × ℤ) :
    ¬ ∀ z ∈ {w : ℤ × ℤ | 0 ≤ w.2},
        dot ((-1 : ℤ), (0 : ℤ)) z ≤ dot ((-1 : ℤ), (0 : ℤ)) V := by
  intro h
  have hmem : ((V.1 - 1 : ℤ), (0 : ℤ)) ∈ {w : ℤ × ℤ | 0 ≤ w.2} := by simp
  have := h _ hmem
  simp only [dot] at this
  omega

/-! ## §5 §2 的前提族可满足（非空真），且机器真的转 -/

/-- **§2 的 binder 在象限上全部兑现。** 守卫：若 `hline0_of_supp` 的前提族不可满足，
它就是空真的。 -/
theorem hline0_supp_hypotheses_satisfiable :
    ∃ (T : Set (ℤ × ℤ)) (nJ vJ vJ1 nprevJ V : ℤ × ℤ) (cJ : ℤ),
      nJ ≠ 0 ∧ Prim vJ ∧ dot nJ vJ = 0 ∧
      dot nprevJ vJ1 = 0 ∧ dot nprevJ vJ < 0 ∧
      (∀ z ∈ T, dot nprevJ z ≤ dot nprevJ V) ∧
      (∀ g ∈ T, g + vJ ∈ T) ∧ (∀ g ∈ T, cJ ≤ dot nJ g) ∧
      dot nJ vJ1 < 0 ∧
      (∃ z ∈ Nivat.MaxEnv.reachSet T vJ1, dot nJ z = cJ - 1) := by
  refine ⟨{w : ℤ × ℤ | 0 ≤ w.1 ∧ 0 ≤ w.2}, ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-1 : ℤ)), ((-1 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ)), 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Prod.ext_iff]
  · simp [Prim, Int.gcd]
  · simp [dot]
  · simp [dot]
  · simp [dot]
  · intro z hz
    have h1 : (0 : ℤ) ≤ z.1 := hz.1
    simpa [dot] using h1
  · intro g hg
    exact ⟨by have := hg.1; simpa using (by omega : (0:ℤ) ≤ g.1 + 1), by simpa using hg.2⟩
  · intro g hg
    have := hg.2
    simpa [dot] using this
  · simp [dot]
  · exact ⟨((0 : ℤ), (-1 : ℤ)), ⟨((0 : ℤ), (0 : ℤ)), ⟨le_rfl, le_rfl⟩, 1, by ext <;> simp⟩,
      by simp [dot]⟩

/-- **机器真的转**：把 §5 的象限实例喂进 §2，得到该层截面确实是一条 `vJ`-半线。 -/
theorem hline0_on_quadrant :
    ∃ z₀ : ℤ × ℤ, dot ((0 : ℤ), (1 : ℤ)) z₀ = (0 : ℤ) - ((0 : ℕ) : ℤ) - 1 ∧
      z₀ ∈ Nivat.MaxEnv.reachSet {w : ℤ × ℤ | 0 ≤ w.1 ∧ 0 ≤ w.2} ((0 : ℤ), (-1 : ℤ)) ∧
      ∀ z ∈ Nivat.MaxEnv.reachSet {w : ℤ × ℤ | 0 ≤ w.1 ∧ 0 ≤ w.2} ((0 : ℤ), (-1 : ℤ)),
        dot ((0 : ℤ), (1 : ℤ)) z = (0 : ℤ) - ((0 : ℕ) : ℤ) - 1 →
          ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • ((1 : ℤ), (0 : ℤ)) := by
  refine hline0_of_supp (nprevJ := ((-1 : ℤ), (0 : ℤ))) (V := ((0 : ℤ), (0 : ℤ)))
    (by simp [Prod.ext_iff]) (by simp [Prim, Int.gcd]) (by simp [dot]) (by simp [dot])
    (by simp [dot]) ?_ ?_
  · intro z hz
    have h1 : (0 : ℤ) ≤ z.1 := hz.1
    simpa [dot] using h1
  · exact ⟨((0 : ℤ), (-1 : ℤ)), ⟨((0 : ℤ), (0 : ℤ)), ⟨le_rfl, le_rfl⟩, 1, by ext <;> simp⟩,
      by simp [dot]⟩


/-! ## §33  楔形法向 `nprevJ`：两条定向前提是自由的，欠账只剩支撑界

消费者 `BottomHz0Collapse.hdz_hz0_hline0_of_wedge` / `..._transverse`（按名引）把 §32 的
`hline0_of_supp` 套在楔形 `(nprevJ, V)` 上，并把 `⟪nprevJ,vJ⟫ < 0`（定向）与 `hsupp`
（支撑界）一并列成残余；`BottomRoom` 的四处也把这两条当 binder 吃。本节证明**只有 `hsupp`
是真欠账**：定向那条由 `det vJ1 vJ ≠ 0`（字段的代数推论）＋ 挑旋转的符号白拿，且在
`Prim vJ1` 下反向唯一 —— 合法的 `nprevJ` 必是规范向量的正倍数，消费者没有自由度可以
用来把 `hsupp` 调容易。

⚠ `Prim vJ1` 不是字段、不免费（`TowerHbase.not_prim_sep_witness_vJ1` 的退化见证
`vJ1 = (0,-2)` 就不本原）。§33.1 / §33.2 不吃它，只有 §33.3 / §33.4 的唯一性吃它。

数值实例（硬规矩 6，先于 Lean 算的）：`nJ = (0,1)`、`vJ = (1,0)`、`vJ1 = (0,-1)` ⟹
`det vJ1 vJ = 1 > 0` ⟹ 走第二支，规范向量 `(vJ1.2, -vJ1.1) = (-1,0)`，与 §32 的
`hline0_on_quadrant` 里手填的 `nprevJ` 逐字相同：§33.2 机械地产出了上一节手挑的那个。 -/

/-! ## §33.1 `vJ1 ∦ vJ` 是字段的推论 -/

/-- `det vJ1 vJ ≠ 0`，只用 `Prim vJ` ＋ `⟪nJ,vJ⟫ = 0` ＋ `⟪nJ,vJ1⟫ < 0`。
（后者是 `ChainDataGeomParts` 逼出来的，见 `ANormal.lean` 的 `Bottom` 一节。） -/
theorem det_vJ1_vJ_ne_zero {nJ vJ vJ1 : ℤ × ℤ} (hvJ : Prim vJ)
    (hnJvJ : dot nJ vJ = 0) (hnJvJ1 : dot nJ vJ1 < 0) : det vJ1 vJ ≠ 0 :=
  det_ne_zero_of_perp hvJ.ne_zero hnJvJ (ne_of_lt hnJvJ1)

/-! ## §33.2 定向前提白拿 -/

/-- ⭐⭐⭐ **`⟪nprevJ,vJ1⟫ = 0` ∧ `⟪nprevJ,vJ⟫ < 0` 可以零额外几何义务地兑现。**

`nprevJ` 在 `vJ1` 的两个旋转里按 `det vJ1 vJ` 的符号挑一个即可。不吃 `Prim vJ1`、
不吃 `det p vJ1` 的任何信息 ⟹ 共线格与横截格通用。 -/
theorem exists_nprevJ {nJ vJ vJ1 : ℤ × ℤ} (hvJ : Prim vJ)
    (hnJvJ : dot nJ vJ = 0) (hnJvJ1 : dot nJ vJ1 < 0) :
    ∃ nprevJ : ℤ × ℤ,
      (nprevJ = ((-vJ1.2, vJ1.1) : ℤ × ℤ) ∨ nprevJ = ((vJ1.2, -vJ1.1) : ℤ × ℤ)) ∧
      dot nprevJ vJ1 = 0 ∧ dot nprevJ vJ < 0 := by
  have hdet : det vJ1 vJ ≠ 0 := det_vJ1_vJ_ne_zero hvJ hnJvJ hnJvJ1
  have hexp : det vJ1 vJ = vJ1.1 * vJ.2 - vJ1.2 * vJ.1 := rfl
  rcases lt_or_gt_of_ne hdet with h | h
  · refine ⟨(-vJ1.2, vJ1.1), Or.inl rfl, dot_perpVec_self vJ1, ?_⟩
    rw [dot_perpVec_eq_det]
    exact h
  · refine ⟨(vJ1.2, -vJ1.1), Or.inr rfl, ?_, ?_⟩
    · show vJ1.2 * vJ1.1 + -vJ1.1 * vJ1.2 = 0
      ring
    · show vJ1.2 * vJ.1 + -vJ1.1 * vJ.2 < 0
      rw [hexp] at h
      linarith

/-! ## §33.3 反向唯一性：`nprevJ` 没有可调的自由度 -/

/-- `Prim vJ1` 下，`⟪w,vJ1⟫ = 0` 的解恰是 `(-vJ1.2, vJ1.1)` 的整数倍。 -/
theorem eq_zsmul_rot_of_perp {vJ1 w : ℤ × ℤ} (hvJ1 : Prim vJ1) (hw : dot w vJ1 = 0) :
    ∃ t : ℤ, w = (t * (-vJ1.2), t * vJ1.1) := by
  have hrot : Prim ((-vJ1.2, vJ1.1) : ℤ × ℤ) :=
    prim_iff_primitive.mpr (Nivat.TowerHbase.hbase_prim_dir hvJ1)
  have hw' : dot vJ1 w = 0 := by
    show vJ1.1 * w.1 + vJ1.2 * w.2 = 0
    have : w.1 * vJ1.1 + w.2 * vJ1.2 = 0 := hw
    linarith
  have hr' : dot vJ1 ((-vJ1.2, vJ1.1) : ℤ × ℤ) = 0 := by
    show vJ1.1 * -vJ1.2 + vJ1.2 * vJ1.1 = 0
    ring
  exact exists_smul_of_det_eq_zero hrot
    (det_eq_zero_of_dot_eq_zero hvJ1.ne_zero hr' hw')

/-- ⭐⭐⭐ **任何合法的 `nprevJ` 都是 §2 那个规范向量的正倍数。**

⟹ 消费者不能靠换 `nprevJ` 把 `hsupp` 调容易：`hsupp` 的方向被 `det vJ1 vJ` 的符号
唯一决定（正倍数不改变「有上界」这件事，见 §4）。 -/
theorem nprevJ_pos_multiple {nJ vJ vJ1 w : ℤ × ℤ} (hvJ1 : Prim vJ1) (hvJ : Prim vJ)
    (hnJvJ : dot nJ vJ = 0) (hnJvJ1 : dot nJ vJ1 < 0)
    (hw1 : dot w vJ1 = 0) (hw2 : dot w vJ < 0) :
    ∃ (t : ℤ) (n0 : ℤ × ℤ), 0 < t ∧ w = (t * n0.1, t * n0.2) ∧
      (n0 = ((-vJ1.2, vJ1.1) : ℤ × ℤ) ∨ n0 = ((vJ1.2, -vJ1.1) : ℤ × ℤ)) ∧
      dot n0 vJ1 = 0 ∧ dot n0 vJ < 0 := by
  obtain ⟨s, hs⟩ := eq_zsmul_rot_of_perp hvJ1 hw1
  have hdet : det vJ1 vJ ≠ 0 := det_vJ1_vJ_ne_zero hvJ hnJvJ hnJvJ1
  have hexp : det vJ1 vJ = vJ1.1 * vJ.2 - vJ1.2 * vJ.1 := rfl
  have hw2' : s * (vJ1.1 * vJ.2 - vJ1.2 * vJ.1) < 0 := by
    have h1 : w.1 = s * (-vJ1.2) := congrArg Prod.fst hs
    have h2 : w.2 = s * vJ1.1 := congrArg Prod.snd hs
    have : w.1 * vJ.1 + w.2 * vJ.2 < 0 := hw2
    rw [h1, h2] at this
    linarith
  rcases lt_or_gt_of_ne hdet with h | h
  · -- `det vJ1 vJ < 0` ⟹ `s > 0`，规范向量是 `(-vJ1.2, vJ1.1)`
    rw [hexp] at h
    have hs0 : 0 < s := by
      rcases lt_trichotomy s 0 with hlt | heq | hgt
      · nlinarith
      · rw [heq] at hw2'; simp at hw2'
      · exact hgt
    exact ⟨s, (-vJ1.2, vJ1.1), hs0, hs, Or.inl rfl, dot_perpVec_self vJ1, by
      rw [dot_perpVec_eq_det, hexp]; linarith⟩
  · -- `det vJ1 vJ > 0` ⟹ `s < 0`，规范向量是 `(vJ1.2, -vJ1.1)`
    rw [hexp] at h
    have hs0 : s < 0 := by
      rcases lt_trichotomy s 0 with hlt | heq | hgt
      · exact hlt
      · rw [heq] at hw2'; simp at hw2'
      · nlinarith
    refine ⟨-s, (vJ1.2, -vJ1.1), by omega, ?_, Or.inr rfl, ?_, ?_⟩
    · have h1 : w.1 = s * (-vJ1.2) := congrArg Prod.fst hs
      have h2 : w.2 = s * vJ1.1 := congrArg Prod.snd hs
      refine Prod.ext ?_ ?_
      · show w.1 = -s * vJ1.2
        rw [h1]; ring
      · show w.2 = -s * -vJ1.1
        rw [h2]; ring
    · show vJ1.2 * vJ1.1 + -vJ1.1 * vJ1.2 = 0
      ring
    · show vJ1.2 * vJ.1 + -vJ1.1 * vJ.2 < 0
      linarith

/-! ## §33.4 正倍数不改变支撑界 -/

/-- `hsupp` 沿正倍数下降：`w = t • n0`（`t > 0`）⟹ `w` 的支撑界给出 `n0` 的支撑界。
⟹ 与 §3 合起来：楔形债只有「`T` 沿规范方向有上界」这**一条**，`V` 仍可自由取。 -/
theorem supp_of_pos_multiple {T : Set (ℤ × ℤ)} {w n0 V : ℤ × ℤ} {t : ℤ} (ht : 0 < t)
    (hw : w = (t * n0.1, t * n0.2))
    (h : ∀ z ∈ T, dot w z ≤ dot w V) : ∀ z ∈ T, dot n0 z ≤ dot n0 V := by
  intro z hz
  have hz' := h z hz
  have hexp : ∀ u : ℤ × ℤ, dot w u = t * dot n0 u := by
    intro u
    rw [hw]
    show t * n0.1 * u.1 + t * n0.2 * u.2 = t * (n0.1 * u.1 + n0.2 * u.2)
    ring
  rw [hexp, hexp] at hz'
  exact le_of_mul_le_mul_left hz' ht

/-- ⭐ **综合：定向前提消掉后，`hline0` 的楔形代价只剩一条支撑界。**

结论逐字给出 `EnvRefuteOrient.hline0_of_supp` 的三条楔形前提（`hnpvJ1` / `hnpvJ` / `hsupp`
里的前两条由本条产出），第三条以 `n0` 上的支撑界为唯一输入。 -/
theorem hline0_wedge_cost {T : Set (ℤ × ℤ)} {nJ vJ vJ1 : ℤ × ℤ} {cJ : ℤ} {ε : ℕ}
    (hnJ : nJ ≠ 0) (hvJ : Prim vJ) (hnJvJ : dot nJ vJ = 0) (hnJvJ1 : dot nJ vJ1 < 0)
    (hsupp : ∀ n0 : ℤ × ℤ, dot n0 vJ1 = 0 → dot n0 vJ < 0 →
      ∃ V : ℤ × ℤ, ∀ z ∈ T, dot n0 z ≤ dot n0 V)
    (hne : ∃ z ∈ Nivat.MaxEnv.reachSet T vJ1, dot nJ z = cJ - (ε : ℤ) - 1) :
    ∃ z₀ : ℤ × ℤ, dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      z₀ ∈ Nivat.MaxEnv.reachSet T vJ1 ∧
      ∀ z ∈ Nivat.MaxEnv.reachSet T vJ1, dot nJ z = cJ - (ε : ℤ) - 1 →
        ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • vJ := by
  obtain ⟨n0, _, h1, h2⟩ := exists_nprevJ hvJ hnJvJ hnJvJ1
  obtain ⟨V, hV⟩ := hsupp n0 h1 h2
  exact hline0_of_supp hnJ hvJ hnJvJ h1 h2 (fun z hz => hV z hz) hne

/-! ## §33.5 非空真守卫：§2 的前提族在 `hline0_on_quadrant` 的实例上可满足 -/

/-- `nJ = (0,1)`、`vJ = (1,0)`、`vJ1 = (0,-1)` 兑现 §2 的三条前提，
且 §2 产出的规范向量就是 `(-1, 0)`。 -/
theorem exists_nprevJ_instance :
    ∃ nprevJ : ℤ × ℤ,
      (nprevJ = ((-1 : ℤ), (0 : ℤ)) ∨ nprevJ = ((-1 : ℤ), (0 : ℤ))) ∧
      dot nprevJ ((0 : ℤ), (-1 : ℤ)) = 0 ∧ dot nprevJ ((1 : ℤ), (0 : ℤ)) < 0 := by
  refine ⟨((-1 : ℤ), (0 : ℤ)), Or.inl rfl, ?_, ?_⟩
  · decide
  · decide

/-- §1 在该实例上非空转：`Prim (1,0)` ＋ `⟪(0,1),(1,0)⟫ = 0` ＋ `⟪(0,1),(0,-1)⟫ = -1 < 0`
全部成立，`det (0,-1) (1,0) = 1 ≠ 0`。 -/
theorem det_vJ1_vJ_ne_zero_instance :
    det ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)) ≠ 0 :=
  det_vJ1_vJ_ne_zero (nJ := ((0 : ℤ), (1 : ℤ)))
    (prim_iff_primitive.mpr isCoprime_one_left) (by decide) (by decide)


/-! ## §34  支撑界 `hsupp` 的二分：横截格一半为假，共线格免费

集成者第 242 轮派工：`Âinf := ⋃ i, hatOf A kk vl i` 在楔形法向上有没有上界？
走「为假」一侧，且必须抬到**真** `Âinf`（抽象集合的反例射程不够，同
`EnvRefuteFaceNormal.lean` 那条的自限）。

**做法不是造居民，是证「对每个居民都成立」的话**：`rec_p`（`ChainPartsFeed.lean`，作用在
**并集**上）与 `ahat_nonempty` 都是字段 ⟹ 无界性可直接在 `c : ChainDataGeomParts …` 上证。
这比造见证强：不是「存在一个居民让路线死」，是「该符号区里**任何**居民都让路线死」。

1. 机制（§34.2/§34.3）：`0 < ⟪nprevJ,p⟫` ⟹ `rec_p` 的 `+p` 射线把 `⟪nprevJ,·⟫` 推到无穷
   ⟹ `hsupp` 对**任何** `V` 为假。
2. 必要条件（§34.4）：`hsupp` ⟹ `0 ≤ det vJ1 p * det vJ1 vJ`。两个行列式**严格异号**时，
   §32 的 `hline0_of_supp` 路线在那半个横截格上**死**（`not_supp_of_det_sign`）。
3. 共线格（§34.5/§34.6）：`det p vJ1 = 0` ⟹ 合法 `nprevJ` 自动 `⟪nprevJ,p⟫ = 0`（机制空转），
   且 `hsupp` 由字段 `ahat_halfPlane_L` **白送**，常数显式 `|⟪nprevJ,vJ⟫ * cL|`。
   ⟹ 共线格的楔形债**关闭**。

⚠ 空真守卫：以 `c` 为前提的结论在该符号区无居民时空真；本节**不主张**该区非空（造 `c`
就是 `RegionSteps` 那条总债）。非空真的部分是 §34.2（抽象 `T`）与 §34.7 的算术实例。

⚠ 派工把方向写死成 `(vJ1.2, -vJ1.1)`；按 §33 合法方向是 `±(-vJ1.2, vJ1.1)` 中由
`det vJ1 vJ` 符号挑出的那个。本节结论按两个行列式的**乘积**陈述，与挑哪支无关，两支都覆盖。

数值实例（硬规矩 6，先于 Lean 算的）：死格 `nJ=(0,1)`、`vJ=(1,0)`、`vJ1=(0,-1)`、
`p=(-1,1)`（`det vJ1 p * det vJ1 vJ = -1 < 0`，合法向量 `(-1,0)`，`⟪(-1,0),p⟫ = 1 > 0`）；
免费格同上但 `p=(0,1)`（`det p vJ1 = 0`，`⟪nprevJ,z⟫ = det p z ≤ -cL`）。 -/

/-! ## §34.1 一条平面恒等式 -/

/-- **核心恒等式，无前提**：`⟪n,a⟫·det v b − ⟪n,b⟫·det v a = ⟪n,v⟫·det a b`。

当 `⟪n,v⟫ = 0`（即 `n ⊥ v`）时它给出 `⟪n,a⟫·det v b = ⟪n,b⟫·det v a`，
即「`n` 在 `v` 的正交线上」把两个方向的配对捆成一个比例。本文件所有符号推理都走这条，
**不需要 `Primitive vJ1`**（那不是字段）。 -/
theorem dot_mul_det_swap (n v a b : ℤ × ℤ) :
    (dot n a) * det v b - (dot n b) * det v a = (dot n v) * det a b := by
  show (n.1 * a.1 + n.2 * a.2) * (v.1 * b.2 - v.2 * b.1)
      - (n.1 * b.1 + n.2 * b.2) * (v.1 * a.2 - v.2 * a.1)
    = (n.1 * v.1 + n.2 * v.2) * (a.1 * b.2 - a.2 * b.1)
  ring

/-- `n ≠ 0` 时 `⟪n,·⟫` 在 `ℤ²` 上取到任意大的值。用来兑现 `hline0_of_supp` 要的那个 `V`。 -/
theorem exists_dot_ge {n : ℤ × ℤ} (hn : n ≠ 0) (M : ℤ) : ∃ V : ℤ × ℤ, M ≤ dot n V := by
  have hor : n.1 ≠ 0 ∨ n.2 ≠ 0 := fst_ne_zero_or_snd_ne_zero hn
  have hMle : M ≤ |M| := le_abs_self M
  have hM0 : (0 : ℤ) ≤ |M| := abs_nonneg M
  rcases hor with h | h
  · refine ⟨(|M| * n.1, 0), ?_⟩
    show M ≤ n.1 * (|M| * n.1) + n.2 * 0
    have hsq : 1 ≤ n.1 * n.1 := by
      rcases lt_or_gt_of_ne h with h' | h' <;> nlinarith
    nlinarith
  · refine ⟨(0, |M| * n.2), ?_⟩
    show M ≤ n.1 * 0 + n.2 * (|M| * n.2)
    have hsq : 1 ≤ n.2 * n.2 := by
      rcases lt_or_gt_of_ne h with h' | h' <;> nlinarith
    nlinarith

/-! ## §34.2 机制：recession 方向抬高 ⟹ 没有上界（抽象，非空真） -/

/-- ⭐⭐⭐ **`rec_p` ＋ `0 < ⟪w,p⟫` ⟹ `T` 在 `w` 方向无界。**

只吃「非空」「沿 `+p` 封闭」两条，`T` 任意。这是把上半平面那个反例的**机制**剥出来：
原来的反例靠 `reachSet` 造无界，这里靠 `rec_p` 造，而 `rec_p` 是字段。 -/
theorem not_bddAbove_of_rec {T : Set (ℤ × ℤ)} {p w : ℤ × ℤ}
    (hne : T.Nonempty) (hrec : ∀ g ∈ T, g + p ∈ T) (hpos : 0 < dot w p) :
    ¬ ∃ V : ℤ × ℤ, ∀ z ∈ T, dot w z ≤ dot w V := by
  rintro ⟨V, hV⟩
  obtain ⟨g, hg⟩ := hne
  -- 沿 `+p` 走 `t` 步仍在 `T` 里
  have hray : ∀ t : ℕ, g + (t : ℤ) • p ∈ T := by
    intro t
    induction t with
    | zero => simpa using hg
    | succ k ih =>
      have := hrec _ ih
      have heq : g + (k : ℤ) • p + p = g + ((k + 1 : ℕ) : ℤ) • p := by
        push_cast
        rw [add_smul, one_smul]
        abel
      rwa [heq] at this
  have hlin : ∀ t : ℕ, dot w (g + (t : ℤ) • p) = dot w g + (t : ℤ) * dot w p := by
    intro t
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  set t : ℕ := (dot w V - dot w g).toNat + 1 with ht
  have hbig : dot w V - dot w g < (t : ℤ) := by
    have : dot w V - dot w g ≤ ((dot w V - dot w g).toNat : ℤ) := Int.self_le_toNat _
    push_cast [ht]
    omega
  have hle := hV _ (hray t)
  rw [hlin] at hle
  nlinarith [hle, hbig, hpos]

/-! ## §34.3 抬到真 `Âinf`：同一条，前提全是字段 -/

/-- ⭐⭐⭐ **`hsupp` 在 `0 < ⟪nprevJ,p⟫` 时为假，对真 `Âinf`。**

前提只有两条字段（`ahat_nonempty` / `rec_p`）＋ 一条符号条件；`Âinf` 是结构里那个真的
`⋃ i, hatOf c.A c.kk vl i`，不是抽象集合。 -/
theorem not_supp_of_dot_p_pos {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    {nprevJ : ℤ × ℤ} (hpos : 0 < dot nprevJ p) :
    ¬ ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      dot nprevJ z ≤ dot nprevJ V :=
  not_bddAbove_of_rec c.ahat_nonempty c.rec_p hpos

/-- 逆否：`hsupp` 成立 ⟹ `⟪nprevJ,p⟫ ≤ 0`。 -/
theorem dot_p_nonpos_of_supp {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    {nprevJ V : ℤ × ℤ}
    (hsupp : ∀ z ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      dot nprevJ z ≤ dot nprevJ V) :
    dot nprevJ p ≤ 0 := by
  by_contra h
  exact not_supp_of_dot_p_pos c (not_le.mp h) ⟨V, hsupp⟩

/-! ## §34.4 必要条件：两个行列式不许异号 -/

/-- ⭐⭐⭐ **`hsupp` ⟹ `0 ≤ det vJ1 p * det vJ1 vJ`。**

⟹ 逆否（`not_supp_of_det_sign`）：两个行列式**严格异号**时，任何合法楔形法向都没有
支撑界，`hline0_of_supp` 这条路线在那半个横截格上**死**。

推理只用 §34.1 的恒等式 ＋ §34.3，**不吃 `Primitive vJ1`**。 -/
theorem det_sign_of_supp {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    {nprevJ V : ℤ × ℤ}
    (hnpvJ1 : dot nprevJ c.vJ1 = 0) (hnpvJ : dot nprevJ c.vJ < 0)
    (hsupp : ∀ z ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      dot nprevJ z ≤ dot nprevJ V) :
    0 ≤ det c.vJ1 p * det c.vJ1 c.vJ := by
  have hq : dot nprevJ p ≤ 0 := dot_p_nonpos_of_supp c hsupp
  -- 恒等式取 `n := nprevJ`、`v := vJ1`、`a := vJ`、`b := p`
  have hid := dot_mul_det_swap nprevJ c.vJ1 c.vJ p
  rw [hnpvJ1, zero_mul] at hid
  -- `⟪nprevJ,vJ⟫ * det vJ1 p = ⟪nprevJ,p⟫ * det vJ1 vJ`
  have hkey : dot nprevJ c.vJ * det c.vJ1 p = dot nprevJ p * det c.vJ1 c.vJ := by linarith
  -- 两边乘 `det vJ1 vJ`
  have hmul : dot nprevJ c.vJ * (det c.vJ1 p * det c.vJ1 c.vJ)
      = dot nprevJ p * (det c.vJ1 c.vJ * det c.vJ1 c.vJ) := by
    calc dot nprevJ c.vJ * (det c.vJ1 p * det c.vJ1 c.vJ)
        = (dot nprevJ c.vJ * det c.vJ1 p) * det c.vJ1 c.vJ := by ring
      _ = (dot nprevJ p * det c.vJ1 c.vJ) * det c.vJ1 c.vJ := by rw [hkey]
      _ = dot nprevJ p * (det c.vJ1 c.vJ * det c.vJ1 c.vJ) := by ring
  have hsq : 0 ≤ det c.vJ1 c.vJ * det c.vJ1 c.vJ := mul_self_nonneg _
  nlinarith [hmul, hsq, hq, hnpvJ]

/-- 逆否形：**符号异号 ⟹ 整个合法楔形族都没有支撑界。**

⚠ **2026-09-26 订正（射程，不改语句）**：本条的前提「严格异号」在**链上不可满足** ——
`0 ≤ det p vJ · det p vJ1` 是字段的推论（本文件 `det_p_vJ_mul_det_p_vJ1_nonneg`），
配 lane-tower-hbase 的 `TowerHbase.hb_det_vJ_vJ1_mul_pos`（`0 < det p vJ · det vJ vJ1`）
即得 `0 ≤ det vJ1 p · det vJ1 vJ`；lane-leafa-shell 已把这一步内核化为
`LeafAShellWedgeSign.det_sign_of_parts` / `not_det_sign_neg`。⟹ 本条对**链上构型空真**，
只对链外构型有内容（与本文件 `stock_witness_not_on_chain` 同一机制）。语句与证明不动。 -/
theorem not_supp_of_det_sign {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hsign : det c.vJ1 p * det c.vJ1 c.vJ < 0) :
    ∀ nprevJ : ℤ × ℤ, dot nprevJ c.vJ1 = 0 → dot nprevJ c.vJ < 0 →
      ¬ ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
        dot nprevJ z ≤ dot nprevJ V := by
  intro nprevJ h1 h2 ⟨V, hV⟩
  exact absurd (det_sign_of_supp c h1 h2 hV) (not_le.mpr hsign)

/-! ## §34.5 共线格：机制空转 -/

/-- 共线格（`det p vJ1 = 0`）里任何合法 `nprevJ` 自动 `⟪nprevJ,p⟫ = 0`
⟹ §34.3 的机制在那里**空转**，不是「碰巧没抓到」。 -/
theorem dot_p_eq_zero_of_collinear {p vJ1 nprevJ : ℤ × ℤ} (hvJ1 : vJ1 ≠ 0)
    (hpar : det p vJ1 = 0) (hnpvJ1 : dot nprevJ vJ1 = 0) : dot nprevJ p = 0 := by
  -- 取 `b := (-vJ1.2, vJ1.1)`，`det vJ1 b = vJ1.1² + vJ1.2² > 0`
  have hid := dot_mul_det_swap nprevJ vJ1 p ((-vJ1.2, vJ1.1) : ℤ × ℤ)
  rw [hnpvJ1, zero_mul] at hid
  have hdb : det vJ1 ((-vJ1.2, vJ1.1) : ℤ × ℤ) = vJ1.1 * vJ1.1 + vJ1.2 * vJ1.2 := by
    show vJ1.1 * vJ1.1 - vJ1.2 * -vJ1.2 = vJ1.1 * vJ1.1 + vJ1.2 * vJ1.2
    ring
  have hdp : det vJ1 p = 0 := by
    have h : p.1 * vJ1.2 - p.2 * vJ1.1 = 0 := hpar
    show vJ1.1 * p.2 - vJ1.2 * p.1 = 0
    linear_combination -h
  have hne : vJ1.1 ≠ 0 ∨ vJ1.2 ≠ 0 := fst_ne_zero_or_snd_ne_zero hvJ1
  have hpos : 0 < vJ1.1 * vJ1.1 + vJ1.2 * vJ1.2 := by
    rcases hne with h | h
    · have : 0 < vJ1.1 * vJ1.1 := mul_self_pos.mpr h
      nlinarith [mul_self_nonneg vJ1.2]
    · have : 0 < vJ1.2 * vJ1.2 := mul_self_pos.mpr h
      nlinarith [mul_self_nonneg vJ1.1]
  rw [hdb, hdp, mul_zero] at hid
  have hfin : dot nprevJ p * (vJ1.1 * vJ1.1 + vJ1.2 * vJ1.2) = 0 := by linarith
  rcases mul_eq_zero.mp hfin with h | h
  · exact h
  · exact absurd h (ne_of_gt hpos)

/-! ## §34.6 共线格：`hsupp` 由字段白送 -/

/-- ⭐⭐⭐ **共线格的支撑界是免费的**，常数显式 `|⟪nprevJ,vJ⟫ * cL|`。

只用字段 `ahat_halfPlane_L`（`cL ≤ ⟪det p vJ • (-p.2,p.1), g⟫`）＋ `dot_nJ_p` ＋
`F.dot_nJ_vJ` ＋ `vJ_prim` ＋ 合法性两条 ＋ `hpar`。⟹ 共线格的楔形债关闭。

⛔ **§105 标注（集成者第 244 轮裁决 ④：整条作废，但按 §105 不删、只改状态）**：
`LeafAShellWedgeSign.supp_of_parts` 已**两格通用**地免费产出 `hsupp`（两条 `i`-无关的墙
`hhp` ＋ `ahat_halfPlane_L`，不吃 `hpar`、不吃 `hdir`、不分格）⟹ 严格推广本条与 §37
`supp_of_same_sign` 两条。裁决是**不接线**进 `BottomHz0Collapse` / `BottomFree`：
`hsupp` 从此不是任何人的债，也不需要分格讨论。
⟹ 本文件 §34 / §36 / §37 / §38 那张 `hsupp` 三分表数学上成立，但链上已被一条无分格的
定理吞掉。
⭐ 非白做：`det_p_vJ_mul_det_p_vJ1_nonneg`（本文件 §19）正是
`LeafAShellWedgeSign.det_sign_of_parts` 的承重前提，`supp_of_parts` 建在它上面。 -/
theorem supp_of_collinear {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    {nprevJ : ℤ × ℤ} (hpar : det p c.vJ1 = 0)
    (hnpvJ1 : dot nprevJ c.vJ1 = 0) (hnpvJ : dot nprevJ c.vJ < 0) :
    ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      dot nprevJ z ≤ dot nprevJ V := by
  have hvJne : c.vJ ≠ 0 := (prim_iff_primitive.mpr c.vJ_prim).ne_zero
  have hD : det p c.vJ ≠ 0 := det_ne_zero_of_perp hvJne c.F.dot_nJ_vJ c.dot_nJ_p
  have hnne : nprevJ ≠ 0 := by
    intro h0
    rw [h0] at hnpvJ
    simp [dot] at hnpvJ
  set D : ℤ := det p c.vJ with hDdef
  set u : ℤ := dot nprevJ c.vJ with hudef
  have hDsq : 1 ≤ D * D := by
    rcases lt_or_gt_of_ne hD with h | h <;> nlinarith
  obtain ⟨V, hV⟩ := exists_dot_ge hnne |u * c.cL|
  refine ⟨V, fun z hz => ?_⟩
  -- 字段给的是 `cL ≤ D * det p z`
  have hLz : c.cL ≤ dot (D • ((-p.2, p.1) : ℤ × ℤ)) z := c.ahat_halfPlane_L z hz
  have hsm : dot (D • ((-p.2, p.1) : ℤ × ℤ)) z = D * det p z := by
    show D * -p.2 * z.1 + D * p.1 * z.2 = D * (p.1 * z.2 - p.2 * z.1)
    ring
  rw [hsm] at hLz
  -- 恒等式：`⟪nprevJ,z⟫ * D = u * det p z`（用到 `⟪nprevJ,p⟫ = 0`）
  have hnp : dot nprevJ p = 0 := by
    refine dot_p_eq_zero_of_collinear ?_ hpar hnpvJ1
    intro h0
    rw [h0] at hnpvJ1
    have : dot c.nJ ((0 : ℤ), (0 : ℤ)) < 0 := by
      have := c.hsweep
      rwa [h0] at this
    simp [dot] at this
  have hid := dot_mul_det_swap nprevJ p z c.vJ
  rw [hnp, zero_mul] at hid
  have hkey : dot nprevJ z * D = u * det p z := by
    rw [hDdef, hudef]; linarith
  -- 乘 `D`：`⟪nprevJ,z⟫ * D² = u * (D * det p z) ≤ u * cL ≤ |u * cL|`
  have hstep : dot nprevJ z * (D * D) = u * (D * det p z) := by
    calc dot nprevJ z * (D * D) = (dot nprevJ z * D) * D := by ring
      _ = (u * det p z) * D := by rw [hkey]
      _ = u * (D * det p z) := by ring
  have hune : u < 0 := hnpvJ
  have hub : u * (D * det p z) ≤ u * c.cL := by
    have := mul_le_mul_of_nonpos_left hLz (le_of_lt hune)
    linarith [this]
  have habs : u * c.cL ≤ |u * c.cL| := le_abs_self _
  have hfin : dot nprevJ z * (D * D) ≤ |u * c.cL| := by linarith [hstep, hub, habs]
  rcases le_or_gt (dot nprevJ z) 0 with hle | hgt
  · calc dot nprevJ z ≤ 0 := hle
      _ ≤ |u * c.cL| := abs_nonneg _
      _ ≤ dot nprevJ V := hV
  · have : dot nprevJ z ≤ dot nprevJ z * (D * D) := by nlinarith
    linarith [hV]

/-! ## §34.7 非空真守卫：§34.2 的前提族可满足，且死格的符号条件可兑现 -/

/-- §34.2 在「死格」数值实例上真的转：`T` = 全平面沿 `p = (-1,1)` 封闭、非空，
`w = (-1,0)`、`⟪w,p⟫ = 1 > 0` ⟹ 无上界。 -/
theorem not_bddAbove_instance :
    ¬ ∃ V : ℤ × ℤ, ∀ z ∈ (Set.univ : Set (ℤ × ℤ)),
      dot ((-1 : ℤ), (0 : ℤ)) z ≤ dot ((-1 : ℤ), (0 : ℤ)) V :=
  not_bddAbove_of_rec (p := ((-1 : ℤ), (1 : ℤ)))
    ⟨(0, 0), Set.mem_univ _⟩ (fun _ _ => Set.mem_univ _) (by decide)

/-- 死格的符号条件在 `nJ = (0,1)`、`vJ = (1,0)`、`vJ1 = (0,-1)`、`p = (-1,1)` 上兑现：
`det vJ1 p * det vJ1 vJ = (-1) * 1 = -1 < 0`，同时 `⟪nJ,vJ⟫ = 0`、`⟪nJ,vJ1⟫ < 0`、
`⟪nJ,p⟫ ≠ 0`（字段不冲突），合法向量 `(-1,0)` 满足 `⟪·,vJ1⟫ = 0` ∧ `⟪·,vJ⟫ < 0`。 -/
theorem dead_cell_instance :
    det ((0 : ℤ), (-1 : ℤ)) ((-1 : ℤ), (1 : ℤ))
        * det ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)) < 0 ∧
      dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 ∧
      dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) < 0 ∧
      dot ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (1 : ℤ)) ≠ 0 ∧
      dot ((-1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) = 0 ∧
      dot ((-1 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) < 0 ∧
      0 < dot ((-1 : ℤ), (0 : ℤ)) ((-1 : ℤ), (1 : ℤ)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- 共线格实例：`p = (0,1)` ⟹ `det p vJ1 = 0`，且合法向量 `(-1,0)` 确实 `⟪nprevJ,p⟫ = 0`
（§34.5 的机制空转是真的，不是靠假设）。 -/
theorem collinear_cell_instance :
    det ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) = 0 ∧
      dot ((-1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) = 0 ∧
      dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ)) ≠ 0 := by
  refine ⟨by decide, by decide, by decide⟩


/-! ## §35 `⟪nJ,vl⟫ = 0` 那一格：`ItemII` 对**任意**本原法向都不可满足
（集成者 2026-09-26 裁决 (2) 准予落地）

两个投入都已在树里、都公理干净：

* `Nivat.Colle35.not_itemII_of_chain`（`ItemII.lean`）——有限种子 ＋ `subStrip` ＋ `hchain`
  的链上，`ItemII B nℓ cz` 对每个 `cz`、每个 `nℓ ⊥ vl` 为假。⚠ 它把 `hperp : ⟪nℓ,vl⟫ = 0`
  当**前提**，所以单独用的时候只封住正交那一族法向。
* §31 的 `itemII_hhp_forces_nl_eq_nJ`——`ItemII` ＋ `hhp` ＋ `0 ≤ ⟪nJ,vl⟫` 把 `ItemII`
  的法向钉死成 `nJ`。

合成的全部内容：在 `⟪nJ,vl⟫ = 0` 这一格里 `hperp` 不必再当前提——它由 `ItemII` 自己连同
`hhp` 推出来（`nℓ = nJ` ⟹ `⟪nℓ,vl⟫ = ⟪nJ,vl⟫ = 0`）。⟹ 那一格里 `ItemII` 对**任意本原
法向、任意 `cz`** 为假，不是只对正交的那一族。

⚠ 射程（PROTOCOL §11，逐条申报）：
1. 本节**不**吃 `ChainDataGeomParts`，`B`/`A`/`kk` 是散装的；对居民用要自己喂字段。
2. `hchain : ∀ i, B (i+1) ⊆ halfStrip (A i) vl` **不是** `ChainData` / `ChainDataGeomParts`
   字段（字段是反向的 `subAB : A i ⊆ B (i+1)`），它是 `ChainRecursion` 的构造选择
   `B (i+1) := A i`。这条限制原样继承自 `not_itemII_of_chain` 的 docstring，没有放宽。
3. `hB0 : (B 0).Finite` 同上，是有限种子假设。
4. 本节不是空真：见 `itemii_close_hypotheses_satisfiable`。

⚠ 一名多物（NOTATION）：`halfStrip` 有两个——`Nivat.LE2.halfStrip`（`LatticeEdges.lean`）
与 `Nivat.Colle35.halfStrip`（`Lemma35.lean`）。`not_itemII_of_chain` 在 `Nivat.Colle35`
里用的是后者；本文件 `open Nivat.LE2`，所以**必须**写全名 `Nivat.Colle35.halfStrip`，
否则会静默接到另一个定义上。

## 原文核对（集成者点名的两行，按禁令只读了这一窗）

`scratch/b3_colle2.txt:464` 是 item (i) 证明的开头：“The assumption on item (i) allows us to
construct a sequence of `E(S_φ)`-enveloped sets `B' ⊂ B₁ ⊂ A₁ ⊂ B₂ ⊂ ⋯`”，`:476` 是那条
构造的条件 (ii)（`B_i` 同时包含 `A_{i-1}` 与 `[-i+1,i-1]² ∩ H(ℓ⁽⁻⁾)`）。⟹ 原文里
item (i)/(ii) 出现在**假设侧**，是用来造链的；lane-leafa-shell 报的「从塔的入口签名去够
`ItemII`」堵死，与这一读法一致。本节走的是**否定**方向（给定链 ⟹ ¬`ItemII`），不经过
那条入口，所以不受它阻碍。⚠ 没有往下读。 -/

/-- ⭐⭐ **`⟪nJ,vl⟫ = 0` 那一格：`ItemII` 对任意本原 `nℓ`、任意 `cz` 为假。**

与 `Nivat.Colle35.not_itemII_of_chain` 的差别只有一条：那条要 `hperp : ⟪nℓ,vl⟫ = 0` 当输入，
本条把它换成格条件 `⟪nJ,vl⟫ = 0` ＋ `hhp`，由 §31 的钉死引理自己推出来。 -/
theorem not_itemII_of_chain_of_dot_nJ_vl_zero {B A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl nl nJ : ℤ × ℤ} {cz cJ : ℤ}
    (hB0 : (B 0).Finite) (hvl0 : vl ≠ 0)
    (hnlp : Primitive nl) (hnJp : Primitive nJ)
    (hperpJ : dot nJ vl = 0)
    (hsub : ∀ i, B i ⊆ A i)
    (hhp : ∀ i, Nivat.Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (subStrip : ∀ i, A i ⊆ Nivat.Colle35.halfStrip (B i) vl)
    (hchain : ∀ i, B (i + 1) ⊆ Nivat.Colle35.halfStrip (A i) vl) :
    ¬ Nivat.Colle35.ItemII B nl cz := by
  intro h2
  have hnl : nl ≠ 0 := (prim_iff_primitive.mpr hnlp).ne_zero
  have heq : nl = nJ :=
    itemII_hhp_forces_nl_eq_nJ hnlp hnJp (le_of_eq hperpJ.symm) h2 hsub hhp
  have hperp : dot nl vl = 0 := by rw [heq]; exact hperpJ
  exact Nivat.Colle35.not_itemII_of_chain hB0 hvl0 hperp hnl subStrip hchain cz h2

/-- **非空真守卫**：上条的几何前提族有居民。`nJ = (0,1)`、`vl = (1,0)` 同时兑现
`⟪nJ,vl⟫ = 0`、`Primitive nJ`、`vl ≠ 0` ⟹ 结论不是靠某条前提为假而空真地成立。 -/
theorem itemii_close_hypotheses_satisfiable :
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0
      ∧ Primitive ((0 : ℤ), (1 : ℤ))
      ∧ ((1 : ℤ), (0 : ℤ)) ≠ (0, 0) := by
  refine ⟨by decide, ?_, by decide⟩
  exact prim_iff_primitive.mp (by decide)


/-!
## §36 楔形朝向 `hdir` 的定价：它**恰好**是一个符号，非退化免费

集成者 2026-09-26 裁决 (6) 列的横截格两条真债之一是朝向
`hdir : ⟪rot vJ1, vJ⟫ < 0`（旋转钉死成 `(vJ1.2, -vJ1.1)`）。本节把它算完：

* 恒等式 `⟪(v.2,-v.1), w⟫ = - det v w`（无前提，`ring`）⟹ `hdir ⟺ 0 < det vJ1 vJ`。
* `det vJ1 vJ ≠ 0` 由 §33 的 `det_vJ1_vJ_ne_zero` 从 `Prim vJ` ＋ `⟪nJ,vJ⟫ = 0` ＋
  `⟪nJ,vJ1⟫ < 0` **免费**得到（三条都是字段或字段推论）。

⟹ `hdir` 不是几何义务，是一个**二选一的符号**：`0 < det vJ1 vJ` 时钉死的那个旋转直接可用；
`det vJ1 vJ < 0` 时另一个旋转 `(-vJ1.2, vJ1.1)` 可用，由 §33 的 `exists_nprevJ` 给出
（那条已证：两个定向前提总能同时兑现，代价为零）。

⚠ 与 §34 的联系（同一个符号，两处露头）：`det_sign_of_supp` 说支撑界 `hsupp` 蕴含
`0 ≤ det vJ1 p * det vJ1 vJ`。所以 `hdir` 与 `hsupp` **不是两笔独立的债**——它们都由
`det vJ1 vJ` 的符号（连同 `det vJ1 p` 的符号）决定。

⚠ 射程：本节**不**主张 `0 < det vJ1 vJ` 成立。它只说：那个不等式是 `hdir` 的**全部**内容，
且它的非退化版本免费。要不要把消费者处钉死的旋转换成 `exists_nprevJ` 选出来的那个，
是消费者侧的裁决，不在本节。
-/

/-- 无前提平面恒等式：`⟪(v.2,-v.1), w⟫ = - det v w`。 -/
theorem dot_rotNeg_eq_neg_det (v w : ℤ × ℤ) :
    dot ((v.2, -v.1) : ℤ × ℤ) w = - det v w := by
  simp only [dot, det]
  ring

/-- ⭐⭐ **`hdir` 的全部内容就是 `0 < det vJ1 vJ`，而非退化免费。**

第一个合取把朝向翻译成符号（无前提）；第二个合取说那个行列式非零是字段推论
（§33 `det_vJ1_vJ_ne_zero`）⟹ 两支必居其一，没有第三种情形。 -/
theorem hdir_iff_det_pos_of_fields {nJ vJ vJ1 : ℤ × ℤ} (hvJ : Prim vJ)
    (hnJvJ : dot nJ vJ = 0) (hnJvJ1 : dot nJ vJ1 < 0) :
    (dot ((vJ1.2, -vJ1.1) : ℤ × ℤ) vJ < 0 ↔ 0 < det vJ1 vJ)
      ∧ det vJ1 vJ ≠ 0 := by
  refine ⟨?_, det_vJ1_vJ_ne_zero hvJ hnJvJ hnJvJ1⟩
  rw [dot_rotNeg_eq_neg_det]
  omega

/-- **另一支也不空**：`det vJ1 vJ < 0` 时钉死的旋转失败，但 `(-vJ1.2, vJ1.1)` 成功。
⟹ 消费者若肯把旋转当成被选出来的量而不是钉死的字面值，`hdir` 的代价是零
（§33 `exists_nprevJ`）。 -/
theorem hdir_flip_of_det_neg {vJ vJ1 : ℤ × ℤ} (h : det vJ1 vJ < 0) :
    dot ((-vJ1.2, vJ1.1) : ℤ × ℤ) vJ < 0 := by
  have hid : dot ((-vJ1.2, vJ1.1) : ℤ × ℤ) vJ = det vJ1 vJ := by
    simp only [dot, det]
    ring
  rw [hid]
  exact h

/-- **非空真守卫**：两支各给一个数值居民，都用钉死的旋转/翻转旋转检验。
`vJ1 = (0,-1)`、`vJ = (1,0)` ⟹ `det vJ1 vJ = 1 > 0`（钉死支）；
`vJ1 = (0,1)`、`vJ = (1,0)` ⟹ `det vJ1 vJ = -1 < 0`（翻转支）。 -/
theorem hdir_both_branches_inhabited :
    (0 : ℤ) < det ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ))
      ∧ det ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) < 0 := by
  constructor <;> decide

/-!
## §37 锥判据：同号半格里 `hsupp` **免费**，锥外区域是**空的**

集成者 2026-09-26 派工：对同号半格做锥判据 `-nprevJ ∈ cone(nJ, det p vJ • rot p)` 的两个方向
（`supp_of_cone` / `not_supp_of_not_cone`）。

**结果：正方向成立，反方向的前提区**为空** ⟹ 不存在「锥外」的横截同号格。**
派工里那个「锥外最小见证」`nJ=(0,1)`、`vJ=(1,0)`、`vJ1=(0,-1)`、`p=(1,-3)` 不满足字段：
`⟪nJ,p⟫ = -3 < 0`，而 `0 < ⟪nJ,p⟫` 是字段推论（`ahat_nonempty` ＋ `hhp` ＋ `rec_p` 给
`0 ≤ ⟪nJ,p⟫`，字段 `dot_nJ_p` 给 `≠ 0`；树里就是 `EnvRefuteOrient.dot_nJ_p_pos_of_parts`）。
见 `out_of_cone_witness_violates_dot_nJ_p`。

## 为什么锥外是空的

无前提平面恒等式（`supp_key_identity`，纯 `ring`）：
```
- ⟪nJ,p⟫ · ⟪rotm vJ1, z⟫ = det vJ1 p · ⟪nJ,z⟫ + (-⟪nJ,vJ1⟫) · ⟪rotm p, z⟫
```
（`rotm v := (v.2, -v.1)`；`nprevJ` 就是 `rotm vJ1` 的正倍数。）三个系数在同号半格里**全正**：

| 系数 | 正性来源 |
|---|---|
| `⟪nJ,p⟫` | 字段推论 `dot_nJ_p_pos_of_parts` |
| `det vJ1 p` | 同号条件 ＋ `0 < det vJ1 vJ` |
| `-⟪nJ,vJ1⟫` | 字段 `hsweep` |

⟹ `-nprevJ` 总是 `nJ` 与 `rotm p` 的正组合，即**恒在锥内**（`neg_rotm_mem_cone`）。而
`rotm p` 与派工里的锥生成元 `det p vJ • rot p` 同向：`det p vJ < 0` 在同号支自动成立
（`det_p_vJ_neg_of_det_vJ1_vJ_pos`，机制是 `vJ = t • dir nJ` 且 `det · vJ = t · ⟪nJ,·⟫`），
所以 `det p vJ • rot p = (-det p vJ) • rotm p` 是 `rotm p` 的正倍数（`wedge_gen_pos_multiple`）。

## 与 §34 / §36 合起来，`hsupp` 这一条整条关掉

* 异号半格：§34 `not_supp_of_det_sign` —— `hsupp` 无解，那半格死。
* 同号半格：本节 `supp_of_same_sign` —— `hsupp` **由字段免费供给**，常数显式。
* 共线格：§34 `supp_of_collinear` —— `hsupp` 免费。
* 而「哪个旋转合法」由 `det vJ1 vJ` 的符号定，§36 `hdir_iff_det_pos_of_fields` 已算完。

⚠ 射程（PROTOCOL §11）：
1. 本节**不**主张同号半格非空 —— 以 `c` 为前提的结论在无居民时空真，那是
   `exists_chainData` 的总债。按集成者要求配了抽象层可满足性实例
   `same_sign_hypotheses_satisfiable`。
2. 本节只处理钉死旋转 `rotm vJ1` 配 `0 < det vJ1 vJ` 这一支；另一支（`det vJ1 vJ < 0`，
   合法旋转是 `-rotm vJ1`）由抽象核心 `supp_of_two_lower_bounds` 同样覆盖，但那一支要把
   `vJ1` 换成 `-vJ1`，而 `vJ1` 是字段、不能代入 ⟹ 留给消费者侧按 §36 的二分挑分支。
3. 本节**不**碰 `hline0` 本身，只产它的 `hsupp` binder。
-/

/-! ## §37.1 零件 -/

/-- `v ≠ 0` ⟹ 旋转 `(v.2, -v.1) ≠ 0`。 -/
theorem rotm_ne_zero {v : ℤ × ℤ} (hv : v ≠ 0) : ((v.2, -v.1) : ℤ × ℤ) ≠ 0 := by
  intro h0
  refine hv (Prod.ext ?_ ?_)
  · have h2 : -v.1 = 0 := by simpa using congrArg Prod.snd h0
    simpa using neg_eq_zero.mp h2
  · simpa using congrArg Prod.fst h0

/-- `⟪n,v⟫ < 0` ⟹ `v ≠ 0`。 -/
theorem ne_zero_of_dot_neg {n v : ℤ × ℤ} (h : dot n v < 0) : v ≠ 0 := by
  intro h0
  rw [h0] at h
  simp [dot] at h

/-- ⭐ **无前提平面恒等式**：把 `⟪rotm vJ1, ·⟫` 写成 `⟪nJ,·⟫` 与 `⟪rotm p, ·⟫` 的组合。
系数分别是 `det vJ1 p` 与 `-⟪nJ,vJ1⟫`，左边的因子是 `⟪nJ,p⟫`。纯 `ring`。 -/
theorem supp_key_identity (nJ p vJ1 z : ℤ × ℤ) :
    - dot nJ p * dot ((vJ1.2, -vJ1.1) : ℤ × ℤ) z
      = det vJ1 p * dot nJ z + (- dot nJ vJ1) * dot ((p.2, -p.1) : ℤ × ℤ) z := by
  simp only [dot, det]
  ring

/-- ⭐⭐ **抽象核心：两条下界 ＋ 一个正组合 ⟹ 支撑界。**

`hcomb` 就是「`t • w` 是两条下界法向的负组合」的标量形（对每个 `z` 成立的恒等式），
把锥内条件以最好用的形式吃进来。⛔ 本条不吃任何几何结构，`T` 是任意集合。 -/
theorem supp_of_two_lower_bounds {T : Set (ℤ × ℤ)} {w : ℤ × ℤ} {t c1 c2 : ℤ}
    (f g : ℤ × ℤ → ℤ) (hw : w ≠ 0) (ht : 0 < t)
    (hcomb : ∀ z : ℤ × ℤ, t * dot w z = - f z - g z)
    (h1 : ∀ z ∈ T, c1 ≤ f z) (h2 : ∀ z ∈ T, c2 ≤ g z) :
    ∃ V : ℤ × ℤ, ∀ z ∈ T, dot w z ≤ dot w V := by
  obtain ⟨V, hV⟩ := exists_dot_ge hw |(- c1 - c2)|
  refine ⟨V, fun z hz => ?_⟩
  have hb : t * dot w z ≤ - c1 - c2 := by
    have hz' := hcomb z
    linarith [h1 z hz, h2 z hz]
  have habs : - c1 - c2 ≤ |(- c1 - c2)| := le_abs_self _
  have ht1 : (1 : ℤ) ≤ t := ht
  rcases le_or_gt (dot w z) 0 with hle | hgt
  · calc dot w z ≤ 0 := hle
      _ ≤ |(- c1 - c2)| := abs_nonneg _
      _ ≤ dot w V := hV
  · have hle1 : dot w z ≤ t * dot w z := by nlinarith
    linarith [hV]

/-! ## §37.2 `det p vJ < 0` 在同号支自动成立 -/

/-- ⭐ **`0 < det vJ1 vJ` ⟹ `det p vJ < 0`**（在字段符号下）。

机制：`vJ ⊥ nJ` ＋ `Prim nJ` ⟹ `vJ = t • dir nJ`；而 `det x (dir nJ) = ⟪nJ,x⟫`（纯 `ring`）
⟹ `det vJ1 vJ = t · ⟪nJ,vJ1⟫` 与 `det p vJ = t · ⟪nJ,p⟫`。前者正 ＋ `⟪nJ,vJ1⟫ < 0` ⟹ `t < 0`
⟹ 后者负（`⟪nJ,p⟫ > 0`）。⟹ 朝向 `hdir` 与楔形生成元的方向是**同一个符号的两种说法**。 -/
theorem det_p_vJ_neg_of_det_vJ1_vJ_pos {nJ p vJ vJ1 : ℤ × ℤ}
    (hnJ : Prim nJ) (hperp : dot nJ vJ = 0) (hα : 0 < dot nJ p)
    (hsweep : dot nJ vJ1 < 0) (hdir : 0 < det vJ1 vJ) : det p vJ < 0 := by
  have hdirprim : Prim (dir nJ) := prim_iff_primitive.mpr (Nivat.TowerHbase.hbase_prim_dir hnJ)
  have hdet0 : det (dir nJ) vJ = 0 :=
    det_eq_zero_of_dot_eq_zero hnJ.ne_zero (dot_dir nJ) hperp
  obtain ⟨t, ht⟩ := exists_smul_of_det_eq_zero hdirprim hdet0
  have h1 : det vJ1 vJ = t * dot nJ vJ1 := by
    rw [ht]
    simp only [det, dot, dir]
    ring
  have h2 : det p vJ = t * dot nJ p := by
    rw [ht]
    simp only [det, dot, dir]
    ring
  have ht0 : t < 0 := by
    rcases lt_trichotomy t 0 with h | h | h
    · exact h
    · rw [h1, h, zero_mul] at hdir; omega
    · exfalso
      rw [h1] at hdir
      nlinarith
  rw [h2]
  nlinarith

/-- **楔形生成元与 `rotm p` 同向**：`det p vJ < 0` 时 `det p vJ • rot p = (-det p vJ) • rotm p`，
系数 `-det p vJ > 0`。⟹ 派工里的锥 `cone(nJ, det p vJ • rot p)` 与本节用的
`cone(nJ, rotm p)` 是**同一个锥**。 -/
theorem wedge_gen_pos_multiple {p vJ : ℤ × ℤ} (h : det p vJ < 0) :
    det p vJ • ((-p.2, p.1) : ℤ × ℤ) = (- det p vJ) • ((p.2, -p.1) : ℤ × ℤ)
      ∧ 0 < - det p vJ := by
  refine ⟨?_, by omega⟩
  refine Prod.ext ?_ ?_ <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-! ## §37.3 锥外区域是空的 -/

/-- ⭐⭐⭐ **同号半格里 `-rotm vJ1` 恒在锥 `cone(nJ, rotm p)` 内**，系数全正、显式给出。

⟹ 派工里那条 `not_supp_of_not_cone` 的前提区（「锥外」）在字段符号下**为空**，
那个方向不是可做的靶子而是空真命题。 -/
theorem neg_rotm_mem_cone {nJ p vJ1 : ℤ × ℤ} (hα : 0 < dot nJ p)
    (hsweep : dot nJ vJ1 < 0) (hsame : 0 < det vJ1 p) :
    ∃ t a b : ℤ, 0 < t ∧ 0 < a ∧ 0 < b ∧
      t • (- ((vJ1.2, -vJ1.1) : ℤ × ℤ)) = a • nJ + b • ((p.2, -p.1) : ℤ × ℤ) := by
  refine ⟨dot nJ p, det vJ1 p, - dot nJ vJ1, hα, hsame, by omega, ?_⟩
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Prod.fst_neg,
      Prod.snd_neg, smul_eq_mul, dot, det] <;>
    ring

/-- **派工里的「锥外最小见证」不满足字段。**
`nJ = (0,1)`、`p = (1,-3)` ⟹ `⟪nJ,p⟫ = -3 < 0`，而 `0 < ⟪nJ,p⟫` 是字段推论
（树里 `EnvRefuteOrient.dot_nJ_p_pos_of_parts`：`ahat_nonempty` 沿 `rec_p` 的射线必须留在
`hhp` 的半平面里 ⟹ `0 ≤ ⟪nJ,p⟫`；字段 `dot_nJ_p` 给 `≠ 0`）。
⟹ 那 8 个「锥外」组合都要重新过一遍 `0 < ⟪nJ,p⟫` 这道闸。 -/
theorem out_of_cone_witness_violates_dot_nJ_p :
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (-3 : ℤ)) < 0 := by
  decide

/-! ## §37.4 主结论：同号半格 `hsupp` 免费 -/

/-- ⭐⭐⭐ **横截同号半格：`hsupp` 由字段免费供给。**

结论逐字是 `hline0_of_supp` / `BottomHz0Collapse.hdz_hz0_hline0_of_wedge` 吃的那条
`hsupp` binder，取 `nprevJ := rotm c.vJ1`。常数显式：
`V` 由 `exists_dot_ge` 在 `|-(det vJ1 p · D · cJ) - ((-⟪nJ,vJ1⟫) · cL)|` 上取，
`D := -det p c.vJ > 0`。

⚠ 前提只有两条符号：`hdir : 0 < det c.vJ1 c.vJ`（＝ §36 的朝向那一支）与
`hsame : 0 < det c.vJ1 p`（＝ §34 `det_sign_of_supp` 必要条件的严格同号支）。
其余全部是字段。

⚠ **§91 重复品标注（集成者第 244 轮裁决 ②：留，不删）**：本条与
`TowerHlevSupp.supp_of_det_nonpos_rot` **同机制**（`supp_key_identity` ＋
`supp_of_two_lower_bounds`），且**他那条更一般**（他的 `hK = 0` 半还覆盖共线格）。
本条继续存在的唯一理由是 **import 方向**：`BottomFree → ConeCover → EnvRefuteOrient`，
而 hlev 那条所在文件 `import BottomFree` ⟹ 他那条在 `ConeCover` / `BottomFree` /
`BottomHz0Collapse` 内部**不可用**，本条可用，且集成者确实要在那一层用。
⟹ 报「A 弱于 B」时按 §113 同时记 B 多出的东西：他多出共线格与抽象 `nprevJ`。

⚠ 另按集成者第 244 轮裁决 ④：`hsupp` 本身已由 `LeafAShellWedgeSign.supp_of_parts`
两格通用地免费产出 ⟹ 本条与 §34.6 `supp_of_collinear` 都不再需要接线，详见那条的 §105 注。 -/
theorem supp_of_same_sign {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hdir : 0 < det c.vJ1 c.vJ) (hsame : 0 < det c.vJ1 p) :
    ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      dot ((c.vJ1.2, -c.vJ1.1) : ℤ × ℤ) z ≤ dot ((c.vJ1.2, -c.vJ1.1) : ℤ × ℤ) V := by
  have hα : 0 < dot c.nJ p := dot_nJ_p_pos_of_parts c
  have hsweep : dot c.nJ c.vJ1 < 0 := c.hsweep
  have hDneg : det p c.vJ < 0 :=
    det_p_vJ_neg_of_det_vJ1_vJ_pos (prim_iff_primitive.mpr c.nJ_prim) c.F.dot_nJ_vJ hα hsweep hdir
  have hwne : ((c.vJ1.2, -c.vJ1.1) : ℤ × ℤ) ≠ 0 := rotm_ne_zero (ne_zero_of_dot_neg hsweep)
  set D : ℤ := - det p c.vJ with hDdef
  have hDpos : 0 < D := by rw [hDdef]; omega
  have hApos : 0 < det c.vJ1 p * D := mul_pos hsame hDpos
  have hBpos : 0 < - dot c.nJ c.vJ1 := by omega
  refine supp_of_two_lower_bounds
    (fun z => (det c.vJ1 p * D) * dot c.nJ z)
    (fun z => (- dot c.nJ c.vJ1) * (D * dot ((p.2, -p.1) : ℤ × ℤ) z))
    (t := dot c.nJ p * D) (c1 := (det c.vJ1 p * D) * c.cJ)
    (c2 := (- dot c.nJ c.vJ1) * c.cL) hwne (mul_pos hα hDpos) ?_ ?_ ?_
  · intro z
    have hid := supp_key_identity c.nJ p c.vJ1 z
    linear_combination (-D) * hid
  · intro z hz
    exact mul_le_mul_of_nonneg_left (union_hhp_of_parts c z hz) (le_of_lt hApos)
  · intro z hz
    have hLz : c.cL ≤ dot ((det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ)) z := c.ahat_halfPlane_L z hz
    have hsm : dot ((det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ)) z
        = D * dot ((p.2, -p.1) : ℤ × ℤ) z := by
      rw [hDdef]
      show det p c.vJ * -p.2 * z.1 + det p c.vJ * p.1 * z.2
        = - det p c.vJ * (p.2 * z.1 + -p.1 * z.2)
      ring
    rw [hsm] at hLz
    exact mul_le_mul_of_nonneg_left hLz (le_of_lt hBpos)

/-- **非空真守卫**（集成者要的抽象层可满足性实例）：同号半格的符号族有居民。
`nJ = (0,1)`、`vJ = (1,0)`、`vJ1 = (0,-1)`、`p = (1,1)` 逐条兑现
`⟪nJ,vJ⟫ = 0`、`0 < ⟪nJ,p⟫`、`⟪nJ,vJ1⟫ < 0`、`0 < det vJ1 vJ`、`0 < det vJ1 p`，
并且 `det p vJ = -1 < 0`（与 `det_p_vJ_neg_of_det_vJ1_vJ_pos` 的结论一致）。 -/
theorem same_sign_hypotheses_satisfiable :
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0
      ∧ 0 < dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (1 : ℤ))
      ∧ dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) < 0
      ∧ 0 < det ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ))
      ∧ 0 < det ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (1 : ℤ))
      ∧ det ((1 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) < 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-!
## §38 楔形 `hsupp` 的分格穷尽性 ＋ 相容性收据（集成者第 243 轮新纪律）

集成者第 243 轮的纪律是：**新 `Prop` / 新 `def` 必须附一条相容性收据**，
核的不是结论形状而是「前提在自己的前提域里可不可满足」。本节把这条纪律
**回溯**用到我自己 §34 / §37 落的三条楔形结论上，结果抓到一个我自己的洞。

## 洞是什么

`supp_of_same_sign`（§37）与 lane-tower-hlev 的 `supp_of_det_nonpos_rot` 都要
`0 < det vJ1 vJ`。而「同号」是 `0 < det vJ1 p * det vJ1 vJ`，它有**两个**子格：

* `0 < det vJ1 p` ∧ `0 < det vJ1 vJ` —— §37 覆盖；
* `det vJ1 p < 0` ∧ `det vJ1 vJ < 0` —— **两条都没覆盖**。

而第二个子格**非空**（本节 §38.3 的第四组数值）：字段约束
`⟪nJ,vJ⟫ = 0`、`0 < ⟪nJ,p⟫`、`⟪nJ,vJ1⟫ < 0` 允许 `det vJ1 vJ < 0`
（Cramer 关系 `det p vJ · ⟪nJ,vJ1⟫ = det vJ1 vJ · ⟪nJ,p⟫` ⟹ 它等价于 `0 < det p vJ`）。
⟹ 我此前对集成者 / hbase / hlev 报的「同号半格 `hsupp` 免费」**只成立一半**。

## 本节补齐

* `supp_of_same_sign_neg`：负同号子格，法向取**另一个**旋转 `(-vJ1.2, vJ1.1)`
  （§36 `hdir_flip_of_det_neg` 说它正是那里合法的那个），机制是同一条
  `supp_key_identity`，两个系数同时翻号、两条下界仍是字段 `hhp`（`cJ`）与
  `ahat_halfPlane_L`（`cL`）。⟹ 「同号 ⟹ `hsupp` 免费」现在两个子格都真。
* `supp_trichotomy_exhaustive_of_parts`：真 `c` 上没有第四格 ——
  `det vJ1 vJ ≠ 0` 由字段免费（§33 `det_vJ1_vJ_ne_zero`），所以乘积为零只能来自
  `det vJ1 p = 0`（＝共线格）。
* `supp_trichotomy_cells_all_inhabited`：四个格的符号约束**都可满足**
  ⟹ 四条结论一条都不空真（符号层；居民层是 `exists_chainData` 的全局债，不在此声明）。

⚠ 射程：本节只在**符号层**声明可满足，不主张存在满足全部 37 条字段的居民。
-/

/-! ## §38.1 真 `c` 上没有第四格 -/

/-- **分格穷尽**：任何 `c` 落在「共线 / 横截·同号 / 横截·异号」三格之一。
`det vJ1 vJ ≠ 0` 由字段 `vJ_prim` ＋ `F.dot_nJ_vJ` ＋ `hsweep` 免费（§33）
⟹ 乘积为零只能来自 `det vJ1 p = 0`。 -/
theorem supp_trichotomy_exhaustive_of_parts {α : Type*} {η xper : Config α}
    {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    det p c.vJ1 = 0
      ∨ 0 < det c.vJ1 p * det c.vJ1 c.vJ
      ∨ det c.vJ1 p * det c.vJ1 c.vJ < 0 := by
  have hG : det c.vJ1 c.vJ ≠ 0 :=
    det_vJ1_vJ_ne_zero (prim_iff_primitive.mpr c.vJ_prim) c.F.dot_nJ_vJ c.hsweep
  rcases lt_trichotomy (det c.vJ1 p * det c.vJ1 c.vJ) 0 with h | h | h
  · exact Or.inr (Or.inr h)
  · refine Or.inl ?_
    have h0 : det c.vJ1 p = 0 := by
      rcases mul_eq_zero.mp h with h1 | h2
      · exact h1
      · exact absurd h2 hG
    have hflip : det p c.vJ1 = - det c.vJ1 p := by simp only [det]; ring
    rw [hflip, h0, neg_zero]
  · exact Or.inr (Or.inl h)

/-! ## §38.2 负同号子格：§37 漏掉的那一半 -/

/-- **`det p vJ` 在负同号子格里为正**。用 lane-tower-hbase 的
`TowerHbase.hb_det_vJ_vJ1_mul_pos`（`det p vJ` 与 `det vJ vJ1` 必同号，不吃 `Primitive`）
而不是我自己 §37 那条（那条只给 `0 < det vJ1 vJ` 的方向）。 -/
theorem det_p_vJ_pos_of_det_vJ1_vJ_neg {α : Type*} {η xper : Config α}
    {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hdir' : det c.vJ1 c.vJ < 0) : 0 < det p c.vJ := by
  have hvJne : c.vJ ≠ 0 := (prim_iff_primitive.mpr c.vJ_prim).ne_zero
  have hEne : det p c.vJ ≠ 0 := det_ne_zero_of_perp hvJne c.F.dot_nJ_vJ c.dot_nJ_p
  have hmul : 0 < det p c.vJ * det c.vJ c.vJ1 :=
    Nivat.TowerHbase.hb_det_vJ_vJ1_mul_pos c.F.dot_nJ_vJ (dot_nJ_p_pos_of_parts c)
      c.hsweep hEne
  have hswapG : det c.vJ c.vJ1 = - det c.vJ1 c.vJ := by simp only [det]; ring
  rw [hswapG] at hmul
  nlinarith [hmul]

/-- ⭐ **负同号子格的 `hsupp`：§37 漏掉的那一半，法向是另一个旋转。**

前提 `det vJ1 p < 0` ∧ `det vJ1 vJ < 0`（即「同号」的负子格），法向取
`(-vJ1.2, vJ1.1)` —— 由 §36 `hdir_flip_of_det_neg`，`det vJ1 vJ < 0` 时正是**这个**
旋转满足 `⟪·,vJ⟫ < 0`，钉死的 `(vJ1.2,-vJ1.1)` 在这里是非法的。

机制与 §37 逐字同源（`supp_key_identity` ＋ `supp_of_two_lower_bounds`），只是
两个系数同时翻号：`det p vJ1 > 0` 配 `⟪nJ,z⟫ ≥ cJ`，`-⟪nJ,vJ1⟫ > 0` 配
`ahat_halfPlane_L` 的 `cL`，而 `det p vJ > 0` 使楔形那条下界的方向恰好对上。

⚠ **§91 / §105 标注（集成者第 244 轮裁决 ②：留，且明确不连坐）**：§37 那条
`supp_of_same_sign` 若将来被删，本条**不跟着删**——它覆盖的是**负负子格**
（`det vJ1 p < 0` ∧ `det vJ1 vJ < 0`），该子格在 hlev `TowerHlevSupp` 侧**无对应物**
（他那条的 `hL : 0 < det vJ1 vJ` 把负子格排除在外），故本条**不是**重复品。

⭐ **负负子格没有被「链上无异号格」删掉**：链上那条是
`LeafAShellWedgeSign.det_sign_of_parts`（字段推论，无额外前提）
`0 ≤ det vJ1 p * det vJ1 vJ`，它杀的是**异号**格；本子格两个因子**同时**翻号 ⟹ 乘积 `> 0`，
与该推论相容，不在其射程内。⟹ 本条仍有内容。 -/
theorem supp_of_same_sign_neg {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hdir' : det c.vJ1 c.vJ < 0) (hsame' : det c.vJ1 p < 0) :
    ∃ V : ℤ × ℤ, ∀ z ∈ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i,
      dot ((-c.vJ1.2, c.vJ1.1) : ℤ × ℤ) z ≤ dot ((-c.vJ1.2, c.vJ1.1) : ℤ × ℤ) V := by
  have hα : 0 < dot c.nJ p := dot_nJ_p_pos_of_parts c
  have hsweep : dot c.nJ c.vJ1 < 0 := c.hsweep
  have hEpos : 0 < det p c.vJ := det_p_vJ_pos_of_det_vJ1_vJ_neg c hdir'
  have hwne : ((-c.vJ1.2, c.vJ1.1) : ℤ × ℤ) ≠ 0 := by
    intro h0
    have hvJ1ne : c.vJ1 ≠ 0 := ne_zero_of_dot_neg hsweep
    refine hvJ1ne (Prod.ext ?_ ?_)
    · have h2 : c.vJ1.1 = 0 := by simpa using congrArg Prod.snd h0
      simpa using h2
    · have h1 : -c.vJ1.2 = 0 := by simpa using congrArg Prod.fst h0
      simpa using neg_eq_zero.mp h1
  set E : ℤ := det p c.vJ with hEdef
  have hKpos : 0 < det p c.vJ1 := by
    have hflip : det p c.vJ1 = - det c.vJ1 p := by simp only [det]; ring
    rw [hflip]; omega
  have hApos : 0 < det p c.vJ1 * E := mul_pos hKpos hEpos
  have hBpos : 0 < - dot c.nJ c.vJ1 := by omega
  refine supp_of_two_lower_bounds
    (fun z => (det p c.vJ1 * E) * dot c.nJ z)
    (fun z => (- dot c.nJ c.vJ1) * (- (E * dot ((p.2, -p.1) : ℤ × ℤ) z)))
    (t := dot c.nJ p * E) (c1 := (det p c.vJ1 * E) * c.cJ)
    (c2 := (- dot c.nJ c.vJ1) * c.cL) hwne (mul_pos hα hEpos) ?_ ?_ ?_
  · intro z
    have hid := supp_key_identity c.nJ p c.vJ1 z
    have hrot : dot ((-c.vJ1.2, c.vJ1.1) : ℤ × ℤ) z
        = - dot ((c.vJ1.2, -c.vJ1.1) : ℤ × ℤ) z := by simp only [dot]; ring
    have hflip2 : det c.vJ1 p = - det p c.vJ1 := by simp only [det]; ring
    linear_combination E * hid + (dot c.nJ p * E) * hrot + (E * dot c.nJ z) * hflip2
  · intro z hz
    exact mul_le_mul_of_nonneg_left (union_hhp_of_parts c z hz) (le_of_lt hApos)
  · intro z hz
    have hLz : c.cL ≤ dot ((det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ)) z := c.ahat_halfPlane_L z hz
    have hsm : dot ((det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ)) z
        = - (E * dot ((p.2, -p.1) : ℤ × ℤ) z) := by
      rw [hEdef]
      show det p c.vJ * -p.2 * z.1 + det p c.vJ * p.1 * z.2
        = - (det p c.vJ * (p.2 * z.1 + -p.1 * z.2))
      ring
    rw [hsm] at hLz
    exact mul_le_mul_of_nonneg_left hLz (le_of_lt hBpos)

/-! ## §38.3 相容性收据：四个格全部非空（符号层） -/

/-- **相容性收据（集成者第 243 轮纪律）**：楔形四个格的符号约束都可满足
⟹ §34 / §37 / §38.2 的四条结论一条都不空真。公共部分
`nJ = (0,1)`、`vJ1 = (0,-1)`；前三组 `vJ = (1,0)`，第四组 `vJ = (-1,0)`
（这一组正是暴露 §37 缺口的那个子格：`det vJ1 vJ < 0` 且 `det vJ1 p < 0`）。

⚠ 只是符号层：不主张存在满足全部 37 条字段的居民（那是 `exists_chainData` 的全局债）。

⚠ **2026-09-26 订正（本条收据不完整，语句不改）**：本条只核了 `⟪nJ,·⟫` 那几条符号约束，
**漏了链上必要条件 `0 ≤ det p vJ · det p vJ1`**（本文件 `det_p_vJ_mul_det_p_vJ1_nonneg`）。
按那条复核：共线 / 正同号 / 负同号三组见证都**通过**（乘积分别为 `0` / `1` / `1`），
但「横截·异号」那组（`p=(-1,1)`、`vJ=(1,0)`）乘积 `= -1 < 0` ⟹ **它是链外见证**，
该格在链上其实是**空的**（lane-leafa-shell 的 `LeafAShellWedgeSign.not_det_sign_neg`）。
⟹ 本条应读作「三个格在链上非空 ＋ 第四格只在符号层非空」。教训写在 §39.3：
相容性收据必须把**已知的字段推论**一起核，只核显式字段约束不够。 -/
theorem supp_trichotomy_cells_all_inhabited :
    -- 公共：nJ 与 vJ1 的字段约束
    (Primitive ((0 : ℤ), (1 : ℤ))
      ∧ dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) < 0)
    -- 共线格：p = (0,1)、vJ = (1,0)
    ∧ (Primitive ((1 : ℤ), (0 : ℤ))
        ∧ dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0
        ∧ 0 < dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ))
        ∧ det ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) = 0)
    -- 横截·正同号：p = (1,1)、vJ = (1,0)
    ∧ (0 < dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (1 : ℤ))
        ∧ 0 < det ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (1 : ℤ))
        ∧ 0 < det ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)))
    -- 横截·异号：p = (-1,1)、vJ = (1,0)
    ∧ (0 < dot ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (1 : ℤ))
        ∧ det ((0 : ℤ), (-1 : ℤ)) ((-1 : ℤ), (1 : ℤ))
            * det ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)) < 0)
    -- 横截·负同号（§37 的缺口）：p = (-1,1)、vJ = (-1,0)
    ∧ (Primitive ((-1 : ℤ), (0 : ℤ))
        ∧ dot ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (0 : ℤ)) = 0
        ∧ 0 < dot ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (1 : ℤ))
        ∧ det ((0 : ℤ), (-1 : ℤ)) ((-1 : ℤ), (1 : ℤ)) < 0
        ∧ det ((0 : ℤ), (-1 : ℤ)) ((-1 : ℤ), (0 : ℤ)) < 0
        ∧ 0 < det ((0 : ℤ), (-1 : ℤ)) ((-1 : ℤ), (1 : ℤ))
            * det ((0 : ℤ), (-1 : ℤ)) ((-1 : ℤ), (0 : ℤ))) := by
  refine ⟨⟨prim_iff_primitive.mp (by decide), by decide⟩,
    ⟨prim_iff_primitive.mp (by decide), by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩,
    ⟨prim_iff_primitive.mp (by decide), by decide, by decide, by decide, by decide,
      by decide⟩⟩

/-!
## §39 `det p vJ = ± ⟪nJ,p⟫`：`vJ` 只差 `dir nJ` 一个单位倍

lane-tower-hbase 两轮点名要的那条。机制全在 §37 已经用过的那台机器上：
字段 `F.dot_nJ_vJ`（`vJ ⊥ nJ`）＋ `nJ_prim` ⟹ `vJ = t • dir nJ`；再配字段
`vJ_prim : Primitive vJ` ⟹ `t` 是单位 ⟹ **`t = ±1`**。于是

* `det p vJ = t · ⟪nJ,p⟫`，`det vJ1 vJ = t · ⟪nJ,vJ1⟫`（**同一个 `t`**）；
* 配 `hsweep : ⟪nJ,vJ1⟫ < 0`，`t` 的符号被 `det vJ1 vJ` 的符号唯一钉死 ⟹
  `0 < det vJ1 vJ` ⟹ `t = -1` ⟹ `det p vJ = -⟪nJ,p⟫`；反之 `det p vJ = ⟪nJ,p⟫`。

⟹ `det p vJ` 不是独立量，它的**模**就是 `⟪nJ,p⟫`。hbase §27 把 `hslice` 归约成的窗口条件
`0 ≤ det p vJ · det p (b − F.a)` 因此塌成单侧的 `det p (b − F.a)` 符号条件。

## §91 交代：`t` 是单位这一步是树里第三份

`EnvRefuteFaceNormal.isUnit_m_of_prim_vJ1` 与 `GcdCollapse.isUnit_m_of_prim` 已有两份，
但 `EnvRefuteOrient` **不 import** `EnvRefuteFaceNormal`，为四行引理新增一条 import 边
在盲区 2 下不划算（谁传递地 import 我，得集成者算）。⟹ 此处内联，并把选择权交出去：
集成者若愿加边，可直接替换成 `isUnit_m_of_prim_vJ1`，本节其余部分不受影响。

## 相容性收据（集成者第 243 轮纪律）

`det_pm_branches_on_chain_compatible` 给两支各一组数值，且**这次把链上必要条件
`0 ≤ det p vJ · det p vJ1`（`det_p_vJ_mul_det_p_vJ1_nonneg`）一起核了** ——
我 §38.3 的收据漏了这一条，导致「异号格非空」那一块实际上给的是**链外**见证
（lane-leafa-shell 本轮的 `det_sign_of_parts` / `not_det_sign_neg` 指出，见 §38 的订正注记）。
-/

/-! ## §39.1 `vJ` 恰是 `± dir nJ` -/

/-- `vJ ⊥ nJ` ＋ `nJ_prim` ⟹ `vJ = t • dir nJ`；再加 `vJ_prim` ⟹ `t = ±1`。 -/
theorem vJ_eq_pm_dir_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    c.vJ = ((1 : ℤ) * (dir c.nJ).1, (1 : ℤ) * (dir c.nJ).2)
      ∨ c.vJ = ((-1 : ℤ) * (dir c.nJ).1, (-1 : ℤ) * (dir c.nJ).2) := by
  have hnJ : Prim c.nJ := prim_iff_primitive.mpr c.nJ_prim
  have hdirp : Prim (dir c.nJ) := prim_iff_primitive.mpr (Nivat.TowerHbase.hbase_prim_dir hnJ)
  have hdet0 : det (dir c.nJ) c.vJ = 0 :=
    det_eq_zero_of_dot_eq_zero hnJ.ne_zero (dot_dir c.nJ) c.F.dot_nJ_vJ
  obtain ⟨t, ht⟩ := exists_smul_of_det_eq_zero hdirp hdet0
  obtain ⟨a, b, hab⟩ := c.vJ_prim
  rw [ht] at hab
  simp only at hab
  have hu : IsUnit t := isUnit_of_dvd_one
    ⟨a * (dir c.nJ).1 + b * (dir c.nJ).2, by linear_combination - hab⟩
  rcases Int.isUnit_iff.mp hu with h | h
  · exact Or.inl (by rw [ht, h])
  · exact Or.inr (by rw [ht, h])

/-! ## §39.2 两个行列式同时塌成内积 -/

/-- ⭐ **`det p vJ` 与 `det vJ1 vJ` 同时是 `± ⟪nJ,·⟫`，而且是同一个符号。** -/
theorem det_pm_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    (det p c.vJ = dot c.nJ p ∧ det c.vJ1 c.vJ = dot c.nJ c.vJ1)
      ∨ (det p c.vJ = - dot c.nJ p ∧ det c.vJ1 c.vJ = - dot c.nJ c.vJ1) := by
  rcases vJ_eq_pm_dir_of_parts c with h | h
  · refine Or.inl ⟨?_, ?_⟩ <;> rw [h] <;> simp only [det, dot, dir] <;> ring
  · refine Or.inr ⟨?_, ?_⟩ <;> rw [h] <;> simp only [det, dot, dir] <;> ring

/-- `0 < det vJ1 vJ`（＝ §36 钉死旋转那支的 `hdir`）⟹ `det p vJ = -⟪nJ,p⟫`。 -/
theorem det_p_vJ_eq_neg_dot_of_hdir {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hdir : 0 < det c.vJ1 c.vJ) : det p c.vJ = - dot c.nJ p := by
  rcases det_pm_of_parts c with ⟨-, h2⟩ | ⟨h1, -⟩
  · exfalso; rw [h2] at hdir; exact absurd c.hsweep (by omega)
  · exact h1

/-- `det vJ1 vJ < 0`（＝ §38.2 那支）⟹ `det p vJ = ⟪nJ,p⟫`。 -/
theorem det_p_vJ_eq_dot_of_hdir_neg {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    (hdir' : det c.vJ1 c.vJ < 0) : det p c.vJ = dot c.nJ p := by
  rcases det_pm_of_parts c with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h1
  · exfalso; rw [h2] at hdir'; exact absurd c.hsweep (by omega)

/-- **`|det p vJ| = ⟪nJ,p⟫`**：两支合起来的无符号形式。 -/
theorem abs_det_p_vJ_of_parts {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    |det p c.vJ| = dot c.nJ p := by
  have hα : 0 < dot c.nJ p := dot_nJ_p_pos_of_parts c
  rcases det_pm_of_parts c with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
  · exact abs_of_pos hα
  · rw [abs_neg]; exact abs_of_pos hα

/-! ## §39.3 相容性收据：两支都在链的必要条件之内 -/

/-- **相容性收据**：`t = -1` 支与 `t = 1` 支各一组数值，且两组都满足链上必要条件
`0 ≤ det p vJ · det p vJ1`（`det_p_vJ_mul_det_p_vJ1_nonneg`）。

公共 `nJ = (0,1)`、`vJ1 = (0,-1)`；`t = -1` 支 `vJ = (1,0)`、`p = (1,1)`，
`t = 1` 支 `vJ = (-1,0)`、`p = (-1,1)`。

⚠ 与我 §38.3 的差别正在这里：那条只核了 `⟪nJ,·⟫` 那几条符号约束，**漏了这条乘积非负**，
于是「异号格非空」用的是链外见证。 -/
theorem det_pm_branches_on_chain_compatible :
    (det ((1 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))
        = - dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (1 : ℤ))
      ∧ 0 ≤ det ((1 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))
          * det ((1 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)))
    ∧ (det ((-1 : ℤ), (1 : ℤ)) ((-1 : ℤ), (0 : ℤ))
        = dot ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (1 : ℤ))
      ∧ 0 ≤ det ((-1 : ℤ), (1 : ℤ)) ((-1 : ℤ), (0 : ℤ))
          * det ((-1 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ))) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

#print axioms Nivat.EnvRefuteOrient.dot_neg_right
#print axioms Nivat.EnvRefuteOrient.dot_nJ_W₀
#print axioms Nivat.EnvRefuteOrient.det_of_perp_perp
#print axioms Nivat.EnvRefuteOrient.det_vJ_W₀_vacuous
#print axioms Nivat.EnvRefuteOrient.dvd_of_ray
#print axioms Nivat.EnvRefuteOrient.hcomb_of_ray_of_dvd
#print axioms Nivat.EnvRefuteOrient.hcomb_of_ray
#print axioms Nivat.EnvRefuteOrient.hcomb_iff_ray_dvd
#print axioms Nivat.EnvRefuteOrient.hcomb_iff_ray
#print axioms Nivat.EnvRefuteOrient.orient_not_enough_without_prim_p
#print axioms Nivat.EnvRefuteOrient.faceBlockFlip
#print axioms Nivat.EnvRefuteOrient.latticeConvex_erase_flip
#print axioms Nivat.EnvRefuteOrient.generatesAt_flip_gen
#print axioms Nivat.EnvRefuteOrient.dot_nJ_p_pos_of_parts
#print axioms Nivat.EnvRefuteOrient.rec_vJ_of_hOrient
#print axioms Nivat.EnvRefuteOrient.rec_vJ_of_hOrient_of_prim_p
#print axioms Nivat.EnvRefuteOrient.flip_repairs_hcomb_on_stock_witness
#print axioms Nivat.EnvRefuteOrient.orient_separates_stock_witness
#print axioms Nivat.EnvRefuteOrient.dot_add_orient
#print axioms Nivat.EnvRefuteOrient.dot_smul_orient
#print axioms Nivat.EnvRefuteOrient.dot_smul_left_orient
#print axioms Nivat.EnvRefuteOrient.dot_perpVec_self
#print axioms Nivat.EnvRefuteOrient.dot_perpVec_eq_det
#print axioms Nivat.EnvRefuteOrient.cramer_smul
#print axioms Nivat.EnvRefuteOrient.det_p_W₀
#print axioms Nivat.EnvRefuteOrient.iter_rec_p
#print axioms Nivat.EnvRefuteOrient.exists_low_of_swept
#print axioms Nivat.EnvRefuteOrient.no_lower_bound_of_swept
#print axioms Nivat.EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg
#print axioms Nivat.EnvRefuteOrient.stock_witness_not_on_chain
#print axioms Nivat.EnvRefuteOrient.ray_identity_of_parts
#print axioms Nivat.EnvRefuteOrient.orient_sign_of_parts
#print axioms Nivat.EnvRefuteOrient.hOrient_of_dvd
#print axioms Nivat.EnvRefuteOrient.rec_vJ_of_dvd_of_prim_p
#print axioms Nivat.EnvRefuteOrient.hbase_witness_orient_false
#print axioms Nivat.EnvRefuteOrient.hbase_witness_sign_ok_dvd_fails
#print axioms Nivat.EnvRefuteOrient.cramer_expand
#print axioms Nivat.EnvRefuteOrient.hcomb_iff_cramer
#print axioms Nivat.EnvRefuteOrient.nat_t_of_dvd
#print axioms Nivat.EnvRefuteOrient.rec_vJ_of_cramer
#print axioms Nivat.EnvRefuteOrient.exists_scale_of_prim
#print axioms Nivat.EnvRefuteOrient.scale_of_parts
#print axioms Nivat.EnvRefuteOrient.hcomb_of_scale
#print axioms Nivat.EnvRefuteOrient.rec_vJ_of_scale_dvd
#print axioms Nivat.EnvRefuteOrient.rec_vJ_of_unimodular
#print axioms Nivat.EnvRefuteOrient.primitive_neg
#print axioms Nivat.EnvRefuteOrient.union_hhp_of_parts
#print axioms Nivat.EnvRefuteOrient.nat_quotient_of_dvd
#print axioms Nivat.EnvRefuteOrient.det_negvl_mul_nonneg_of_parts
#print axioms Nivat.EnvRefuteOrient.rec_vJ_negvl_of_hOrient
#print axioms Nivat.EnvRefuteOrient.rec_vJ_negvl_of_cramer
#print axioms Nivat.EnvRefuteOrient.det_ne_zero_of_perp
#print axioms Nivat.EnvRefuteOrient.det_p_vJ_ne_zero_of_parts
#print axioms Nivat.EnvRefuteOrient.det_prod_pos_of_parts
#print axioms Nivat.EnvRefuteOrient.det_smul_right
#print axioms Nivat.EnvRefuteOrient.scale_pos_of_sieve
#print axioms Nivat.EnvRefuteOrient.exists_pos_scale_of_parts
#print axioms Nivat.EnvRefuteOrient.rec_vJ_of_parts_of_det_ne
#print axioms Nivat.EnvRefuteOrient.hbase_witness_scale_pos_but_dvd_fails
#print axioms Nivat.EnvRefuteOrient.det_neg_left
#print axioms Nivat.EnvRefuteOrient.det_p_ne_zero_iff_transverse
#print axioms Nivat.EnvRefuteOrient.det_p_vJ1_ne_zero_of_transverse
#print axioms Nivat.EnvRefuteOrient.rec_vJ_of_parts_of_transverse
#print axioms Nivat.EnvRefuteOrient.det_vl_eq_zero_iff_multiple
#print axioms Nivat.EnvRefuteOrient.det_p_eq_zero_iff_transverse
#print axioms Nivat.EnvRefuteOrient.det_p_vJ1_eq_zero_iff_collinear
#print axioms Nivat.EnvRefuteOrient.smul_eq_zero_left
#print axioms Nivat.EnvRefuteOrient.W₀_eq_zero_of_collinear_of_parts
#print axioms Nivat.EnvRefuteOrient.no_pos_scale_of_collinear_of_parts
#print axioms Nivat.EnvRefuteOrient.degenU
#print axioms Nivat.EnvRefuteOrient.degenC
#print axioms Nivat.EnvRefuteOrient.mem_degenU
#print axioms Nivat.EnvRefuteOrient.mem_degenC
#print axioms Nivat.EnvRefuteOrient.degen_latticeConvex
#print axioms Nivat.EnvRefuteOrient.degen_rec_p
#print axioms Nivat.EnvRefuteOrient.degen_swept
#print axioms Nivat.EnvRefuteOrient.degen_bundle_not_enough
#print axioms Nivat.EnvRefuteOrient.degenU_chain
#print axioms Nivat.EnvRefuteOrient.rec_vJ_not_from_linear_fields_collinear_with_attained
#print axioms Nivat.EnvRefuteOrient.halfPlane_sub_iUnion_of_itemII
#print axioms Nivat.EnvRefuteOrient.degenU_not_itemII
#print axioms Nivat.EnvRefuteOrient.exists_abs_gt_mul_ge
#print axioms Nivat.EnvRefuteOrient.fst_ne_zero_or_snd_ne_zero
#print axioms Nivat.EnvRefuteOrient.exists_bigX_in_halfPlane
#print axioms Nivat.EnvRefuteOrient.exists_bigY_in_halfPlane
#print axioms Nivat.EnvRefuteOrient.not_itemII_of_subset_vstrip
#print axioms Nivat.EnvRefuteOrient.not_itemII_of_subset_hstrip
#print axioms Nivat.EnvRefuteOrient.degenU_not_itemII_forall
#print axioms Nivat.EnvRefuteOrient.collinearStrip_lside_not_itemII
#print axioms Nivat.EnvRefuteOrient.vline_witness_not_itemII
#print axioms Nivat.EnvRefuteOrient.exists_mul_lt
#print axioms Nivat.EnvRefuteOrient.one_le_dot_self
#print axioms Nivat.EnvRefuteOrient.exists_base_in_halfPlane
#print axioms Nivat.EnvRefuteOrient.exists_halfPlane_dot_lt_of_det_ne_zero
#print axioms Nivat.EnvRefuteOrient.exists_halfPlane_dot_lt_of_dot_neg
#print axioms Nivat.EnvRefuteOrient.eq_zero_of_det_eq_zero_of_dot_eq_zero
#print axioms Nivat.EnvRefuteOrient.halfPlane_le_of_itemII_of_hhp
#print axioms Nivat.EnvRefuteOrient.itemII_hhp_forces_codirectional
#print axioms Nivat.EnvRefuteOrient.itemII_hhp_forces_nl_eq_nJ
#print axioms Nivat.EnvRefuteOrient.not_itemII_of_hhp_of_det_ne_zero
#print axioms Nivat.EnvRefuteOrient.not_itemII_of_hhp_of_dot_nonpos
#print axioms Nivat.EnvRefuteOrient.supp_reachSet
#print axioms Nivat.EnvRefuteOrient.eq_add_zsmul_of_dot_eq
#print axioms Nivat.EnvRefuteOrient.hline0_of_supp
#print axioms Nivat.EnvRefuteOrient.mem_reach_upper
#print axioms Nivat.EnvRefuteOrient.not_hline0_without_supp
#print axioms Nivat.EnvRefuteOrient.supp_fails_on_halfPlane
#print axioms Nivat.EnvRefuteOrient.hline0_supp_hypotheses_satisfiable
#print axioms Nivat.EnvRefuteOrient.hline0_on_quadrant
#print axioms Nivat.EnvRefuteOrient.det_vJ1_vJ_ne_zero
#print axioms Nivat.EnvRefuteOrient.exists_nprevJ
#print axioms Nivat.EnvRefuteOrient.eq_zsmul_rot_of_perp
#print axioms Nivat.EnvRefuteOrient.nprevJ_pos_multiple
#print axioms Nivat.EnvRefuteOrient.supp_of_pos_multiple
#print axioms Nivat.EnvRefuteOrient.hline0_wedge_cost
#print axioms Nivat.EnvRefuteOrient.exists_nprevJ_instance
#print axioms Nivat.EnvRefuteOrient.det_vJ1_vJ_ne_zero_instance
#print axioms Nivat.EnvRefuteOrient.dot_mul_det_swap
#print axioms Nivat.EnvRefuteOrient.exists_dot_ge
#print axioms Nivat.EnvRefuteOrient.not_bddAbove_of_rec
#print axioms Nivat.EnvRefuteOrient.not_supp_of_dot_p_pos
#print axioms Nivat.EnvRefuteOrient.dot_p_nonpos_of_supp
#print axioms Nivat.EnvRefuteOrient.det_sign_of_supp
#print axioms Nivat.EnvRefuteOrient.not_supp_of_det_sign
#print axioms Nivat.EnvRefuteOrient.dot_p_eq_zero_of_collinear
#print axioms Nivat.EnvRefuteOrient.supp_of_collinear
#print axioms Nivat.EnvRefuteOrient.not_bddAbove_instance
#print axioms Nivat.EnvRefuteOrient.dead_cell_instance
#print axioms Nivat.EnvRefuteOrient.collinear_cell_instance
#print axioms Nivat.EnvRefuteOrient.not_itemII_of_chain_of_dot_nJ_vl_zero
#print axioms Nivat.EnvRefuteOrient.itemii_close_hypotheses_satisfiable
#print axioms Nivat.EnvRefuteOrient.dot_rotNeg_eq_neg_det
#print axioms Nivat.EnvRefuteOrient.hdir_iff_det_pos_of_fields
#print axioms Nivat.EnvRefuteOrient.hdir_flip_of_det_neg
#print axioms Nivat.EnvRefuteOrient.hdir_both_branches_inhabited
#print axioms Nivat.EnvRefuteOrient.rotm_ne_zero
#print axioms Nivat.EnvRefuteOrient.ne_zero_of_dot_neg
#print axioms Nivat.EnvRefuteOrient.supp_key_identity
#print axioms Nivat.EnvRefuteOrient.supp_of_two_lower_bounds
#print axioms Nivat.EnvRefuteOrient.det_p_vJ_neg_of_det_vJ1_vJ_pos
#print axioms Nivat.EnvRefuteOrient.wedge_gen_pos_multiple
#print axioms Nivat.EnvRefuteOrient.neg_rotm_mem_cone
#print axioms Nivat.EnvRefuteOrient.out_of_cone_witness_violates_dot_nJ_p
#print axioms Nivat.EnvRefuteOrient.supp_of_same_sign
#print axioms Nivat.EnvRefuteOrient.same_sign_hypotheses_satisfiable
#print axioms Nivat.EnvRefuteOrient.supp_trichotomy_exhaustive_of_parts
#print axioms Nivat.EnvRefuteOrient.det_p_vJ_pos_of_det_vJ1_vJ_neg
#print axioms Nivat.EnvRefuteOrient.supp_of_same_sign_neg
#print axioms Nivat.EnvRefuteOrient.supp_trichotomy_cells_all_inhabited
#print axioms Nivat.EnvRefuteOrient.vJ_eq_pm_dir_of_parts
#print axioms Nivat.EnvRefuteOrient.det_pm_of_parts
#print axioms Nivat.EnvRefuteOrient.det_p_vJ_eq_neg_dot_of_hdir
#print axioms Nivat.EnvRefuteOrient.det_p_vJ_eq_dot_of_hdir_neg
#print axioms Nivat.EnvRefuteOrient.abs_det_p_vJ_of_parts
#print axioms Nivat.EnvRefuteOrient.det_pm_branches_on_chain_compatible

/-! ## §33  ⛔ `ItemII` 的**族**护栏：不许按帽族实例化

### 来历

§29 / §30 的 `halfPlane_sub_iUnion_of_itemII` 结论是 `{z | cz ≤ ⟪nl,z⟫} ⊆ ⋃ i, A i`，其中
`A` 是**抽象**族。链上唯一正确的代入是 `A := c.A`（`subBA : ∀ i, B i ⊆ A i` 说的就是脱帽族）。
lane-leafa-shell 本轮报了 `not_exhHP_of_parts`（`tmp/wip/lane-leafa-shell-exhhp-refute.lean`，
未落主仓），否的是**穷尽型** `¬ ∀ q, cJ ≤ ⟪nJ,q⟫ → ∃ i₀, ∀ i ≥ i₀, q ∈ hatOf A kk vl i`；
他自述其证明体只取了「`q ∈ ⋃ i, hatOf …`」这一个推论，`∃i₀ ∀i≥i₀` 那层量词一步没用上
⟹ 并集型也该成立，但他明说**不会**写那份内核见证（§51）。

本节把**并集型**补上，且**不转抄他的证明体**（§91：形状重复才算重复，机制不同不算）：
他走「两堵墙不平行」（`det nJ n_L ≠ 0`）；本节走「沿 `-vJ` 滑」——`⟪nJ,·⟫` 在 `vJ` 方向上
恒定（字段 `F.dot_nJ_vJ`），而 `⟪n_L,·⟫` 每滑一步降 `(det p vJ)² > 0`
（`det_p_vJ_ne_zero_of_parts`，本文件）。半平面里于是有 `n_L` 高度任意低的点，
被字段 `ahat_halfPlane_L` 当场挡掉。

⛔⛔ **第 247 轮 09:40 自我订正（上面那段「机制不同」的判断是错的，保留原文不删，按 §105）**：
我当时只有他的**口头描述**（「两堵墙不平行」），没读证明体。事后亲读
`tmp/wip/lane-leafa-shell-exhunion.lean` 的 `not_exh_union_halfPlane_of_parts` 证明体，
他实际也是**滑**——沿 `Nivat.LE2.dir c.nJ` 平移，保 `nJ`-高度而把 `ℓ` 墙推到 `-∞`。
因 `F.dot_nJ_vJ` ＋ `vJ_prim` 有 `vJ = ±dir c.nJ`，⟹ **两条是同一个机制**，
「机制不同故不算重复」这个理由**不成立**。

更要紧的是**语句层面**：他那条的结论 `¬ ∀ q, c.cJ ≤ dot c.nJ q → q ∈ ⋃ j, hatOf …` 与本节
`not_halfPlane_sub_iUnion_hatOf` 的 `¬ ({z | …} ⊆ ⋃ i, hatOf …)` **定义等价**——
`tmp/wip/lane-env-refute-bridgeprobe.lean` 内核验过：`fun h => not_halfPlane_sub_iUnion_hatOf c h`
一行直接给出他那条的逐字形状（`EXIT=0`，公理全白）。⟹ 两条是同一命题的两种写法，
他那 45 行证明体按 §91 是**重复品**。两份是同一轮并发写出的（我 09:24 落主仓、他 09:36 落
`tmp/wip/`，消息交叉），不是谁越界。**处置归集成者（§110.2）**；我这边的记法是：
主仓保留本节这一条，他那条换成上面那行桥接即可，他的 `eventually_mem_iff_mem_union`
（`AhatMono` ⟹ 穷尽型 ⟺ 并集型，双向、零额外前提）与 `not_exhHP_of_parts_via_union`
是**新内容**，不受影响。

⭐ 连带简化（他那条带来的）：既然 `AhatMono` 把穷尽型与并集型逐字打平，下面
`not_itemII_of_hat_family` 也**同时**否掉「`ItemII` 按帽族 ＋ 穷尽型」那个变体，
不需要另写一条。

### 数值实例（硬规矩 6，先算后写）

`p` / `vJ` 各取 4 值、`det p vJ ≠ 0` 的 16 组**全部**满足 `⟪n_L,vJ⟫ = (det p vJ)²`
且 `⟪nJ,vJ⟫ = 0`（哨兵「差 1」读 0，已燃）。取 `p = (1,-2)`、`vJ = (2,3)`、`g₀ = (5,7)`：
`D = det p vJ = 7`、`D² = 49`；`t = 0,1,5,20` 时 `nJ` 高度恒 `-1`（`≥ cJ` 恒真），
`n_L` 高度 `119 → 70 → -126 → -861`（`≥ cL` 自 `t = 1` 起假）。

### 射程自限（§84，带分母）

* 只否「`{z | cJ ≤ ⟪nJ,z⟫} ⊆ ⋃ i, hatOf A kk vl i`」这**一个**形状。**不**主张 `Â_∞` 有界，
  **不**给 `Â_∞` 的楔形上界（那是 `LeafAShellWedgeSign.exists_wedge_of_parts` 的活）。
* **与 §29 / §30 不矛盾**：`hatOf i` 比 `A i` 平移了 `-kk i • vl`，脱帽族的半平面包含
  在 `ItemII` 下仍然成立。两者合起来说的是「`kk` 的平移是本质的」，不是「§29 错了」。
* 吃的字段：`ahat_nonempty` / `hhp` / `ahat_halfPlane_L` / `F.dot_nJ_vJ` / `vJ_prim`
  ＋经 `det_p_vJ_ne_zero_of_parts` 的 `rec_p` / `hswept` / `dot_nJ_p` 一线
  ⟹ **不是「几乎无前提」**（我自己那条「`bottom`-free ≠ 字段-free」同款口径）。
* ⚠ 本节**不**回答「`ItemII` 该不该加进 `ChainDataGeomParts`」，只钉死一件事：
  加的话必须按**脱帽族**陈述。`CORE-HOLES.md` 那条硬护栏（报「`ItemII` 杀死某见证」
  必须报所用 `(nℓ, cz)`）在**族**这一维上有同款要求：还必须报**帽族还是脱帽族**。 -/

/-- `⟪n_L, vJ⟫ = (det p vJ)²`，其中 `n_L = det p vJ • (-p.2, p.1)`。
纯计算；与 lane-leafa-shell 的 `dot_nL_vJ1_nonneg` 不是一回事（那条讲 `vJ1` 且只给符号）。 -/
theorem dot_nL_vJ_eq_det_sq (p v : ℤ × ℤ) :
    dot ((det p v) • ((-p.2, p.1) : ℤ × ℤ)) v = det p v * det p v := by
  simp only [dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- ⭐ **并集型反驳**：`nJ` 半平面装不进 `Â_∞ = ⋃ i, hatOf A kk vl i`。 -/
theorem not_halfPlane_sub_iUnion_hatOf {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    ¬ ({z : ℤ × ℤ | c.cJ ≤ dot c.nJ z} ⊆ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i) := by
  intro hsub
  obtain ⟨g₀, hg₀⟩ := c.ahat_nonempty
  have hDne : det p c.vJ ≠ 0 := det_p_vJ_ne_zero_of_parts c
  have hDsq : 1 ≤ det p c.vJ * det p c.vJ := by
    rcases lt_or_gt_of_ne hDne with h | h <;> nlinarith
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp hg₀
  have hgJ : c.cJ ≤ dot c.nJ g₀ := c.hhp i₀ hi₀
  set t : ℤ := max 0 (dot ((det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ)) g₀ - c.cL) + 1 with ht
  have ht0 : 0 ≤ t := by
    have h1 : (0 : ℤ) ≤ max 0 (dot ((det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ)) g₀ - c.cL) :=
      le_max_left _ _
    omega
  have htbig : dot ((det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ)) g₀ - c.cL < t := by
    have h1 : dot ((det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ)) g₀ - c.cL ≤
        max 0 (dot ((det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ)) g₀ - c.cL) := le_max_right _ _
    omega
  set q : ℤ × ℤ := g₀ - t • c.vJ with hq
  have hqJ : dot c.nJ q = dot c.nJ g₀ - t * dot c.nJ c.vJ := by
    simp only [hq, dot, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hqJ' : c.cJ ≤ dot c.nJ q := by
    rw [hqJ, c.F.dot_nJ_vJ]
    omega
  have hqL : dot ((det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ)) q
      = dot ((det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ)) g₀
        - t * dot ((det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ)) c.vJ := by
    simp only [hq, dot, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hqL' : dot ((det p c.vJ) • ((-p.2, p.1) : ℤ × ℤ)) q < c.cL := by
    rw [hqL, dot_nL_vJ_eq_det_sq]
    have hmul : t ≤ t * (det p c.vJ * det p c.vJ) := by nlinarith [ht0, hDsq]
    omega
  exact absurd (c.ahat_halfPlane_L q (hsub hqJ')) (not_le.mpr hqL')

/-- ⛔ `ItemII` ＋「被**帽族**装住」在链上不可满足 ⟹ 那样实例化 §29 / §30，
「`ItemII` 杀见证」就退化成「靠矛盾杀一切」，信息量为零。 -/
theorem not_itemII_of_hat_family {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen)
    {B : ℕ → Set (ℤ × ℤ)}
    (h2 : Nivat.Colle35.ItemII B c.nJ c.cJ)
    (hsub : ∀ i, B i ⊆ Nivat.Colle35.hatOf c.A c.kk vl i) : False :=
  not_halfPlane_sub_iUnion_hatOf c (halfPlane_sub_iUnion_of_itemII h2 hsub)

/-- 正面读法：链上**存在**逃出 `Â_∞` 的半平面点。 -/
theorem exists_halfPlane_not_mem_iUnion_hatOf {α : Type*} {η xper : Config α}
    {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (c : Nivat.ChainAsm.Aparts.ChainDataGeomParts η xper vl p S gen) :
    ∃ z : ℤ × ℤ, c.cJ ≤ dot c.nJ z ∧ z ∉ ⋃ i, Nivat.Colle35.hatOf c.A c.kk vl i := by
  by_contra hcon
  refine not_halfPlane_sub_iUnion_hatOf c ?_
  intro z hz
  by_contra hmem
  exact absurd ⟨z, hz, hmem⟩ hcon

#print axioms Nivat.EnvRefuteOrient.dot_nL_vJ_eq_det_sq
#print axioms Nivat.EnvRefuteOrient.not_halfPlane_sub_iUnion_hatOf
#print axioms Nivat.EnvRefuteOrient.not_itemII_of_hat_family
#print axioms Nivat.EnvRefuteOrient.exists_halfPlane_not_mem_iUnion_hatOf

end Nivat.EnvRefuteOrient
