/-
# `hwit` 与 `hg` 的定价对比 ＋ 钉住 ⟹ `dir J` 方向 `rec_vJ`（lane-leafa-shell §27）

集成者 2026-09-26 点名的问题：「§25 的 `rec_vJ_of_level_witness_collinear_lside` 把共线格
`rec_vJ` 归约到 `hwit`（每条 `vl`-纤维非空）。比一下 `hwit` 和 `LeafAJSelect.hgrow_of_pinned_ccw`
的 `hg`——两者都是「某个东西被钉住／非空」形，如果能互推，或者 `hwit` 比 `hg` 便宜，
那共线格就有路了。」

本文件给出两条内核回答，其中第一条**与「`hwit` 更便宜」的猜测相反**。

## §27a  `hwit` 不比目标便宜 —— 在 §25 的前提下它**就是**目标

`hwit_of_rec_vJ_lside`：`rec_vJ ⟹ hwit`，**零前提**（取 `y := z + vJ`，`det vl 0 = 0`）。
与 `LeafAShellLsideFork.rec_vJ_of_level_witness_collinear_lside`（`hwit ⟹ rec_vJ`）合成得
`hwit_iff_rec_vJ_collinear_lside`：在那六条前提（`0 < cc` / `p = -cc•vl` / `Primitive vl` /
`rec_p` / `SweptClosed` / `hhp` / `hlevel`）之下

    hwit  ⟺  rec_vJ

⟹ **`hwit` 是等价刻画，不是廉价充分条件。**「归约到 `hwit`」买到的全部东西是
「把方向问题换成纤维问题」，**没有降低难度**。§25 那条不撤：它唯一的独特价值是
**不用凸性**（两向差见 §27c 射程自限 1）。

## §27b  `hg` 的产者（⚠ 记账：集成者 2026-09-26 已自行更正，本节不重复立案）

`§47` 扫描（哨兵 `轮` = OPEN 109 / NOTE 56 / LANDING 695，非零）：
`exists_gJ_pinned` = OPEN 0 / NOTE 0 / LANDING 9；`hArcbdd` = OPEN 1 / NOTE 0 / LANDING 5；
`hg₁` = OPEN 12 / NOTE 0 / LANDING 7；`hwit` = OPEN 0 / NOTE 0 / LANDING 1。
按 `§51` 读了命中行：`blueprint/LANDING.md` 已有集成者逐字的「⛔『`hg` 面起点钉死全树
无生产者』——错，我 grep 打偏」，并把债挪到 `hg₁`。⟹ 本节只把已记的账做成可编译形状。

独立复核到的同一事实（读的是签名与证明体，不是报告）：产者是
`LeafAJSelect.exists_gJ_pinned_ccw`，结论逐字是

    ∃ g_J : ℤ × ℤ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ i₀ : ℕ, ∀ i ≥ i₀, Nivat.PolyChain.faceStart (Ahat (σ i)) J = g_J

即 `hgrow_of_pinned_ccw` 的 `hσmono` ＋ `hg` **原样**。按结论形状 grep 漏掉它的原因是
`faceStart` 与 `= g_J` 之间隔着 `∃ σ`、`StrictMono σ`、`∃ i₀`、`∀ i ≥ i₀` 四段且**跨行**；
按**输入形状**（谁消费 `hg`）一搜就到——`PROTOCOL §137` 要求的第二个方向。

`exists_gJ_pinned_ccw` 自己未兑现的 binder：

| binder | 原文对应 |
|---|---|
| `hg₁ : ∀ i, faceStart (Ahat i) ℓ + faceLen (Ahat i) ℓ • dir ℓ = g₁` | `b3_colle2.txt:488` 的 `g_1`／`k_i` 归一化 |
| `hArcbdd : ∀ μ ∈ Arc ℓ J, ∃ L, ∀ i, faceLen (Ahat i) μ ≤ L` | `b3_colle2.txt:502`/`:506` 的「`ι+1 ≤ j ≤ J−1` 截长相等」 |
| `henv` / `hSfin` / `hSarea` / `hℓE` / `hJE` / `hℓJ` | Def 3.2（`b3_colle2.txt:402`）侧 |

⟹ **`hg` 不是断口，`hg₁` 与 `hArcbdd` 才是。**

## §27c  钉住 ⟹ `dir J` 方向的 `rec_vJ`（不分格）

`rec_dirJ_of_pinned_tower_lside`：把 `LeafAJSelect.hgrow_of_pinned_ccw` →
`Colle35.ray_of_pinned_growth` → `Colle35.rec_of_ray` 三段接成一条。三段本来都在主仓、
各自 sorry-free，但**没有任何一处把它们拼起来过**；拼完之后残余 binder 才看得清。
`rec_dirJ_of_gJ_pinned_ccw_lside`：再把 `exists_gJ_pinned_ccw` 前置，于是 `σ` / `i₀` / `g_J`
全部消失，签名里只剩塔侧条件 ＋ 上表那两条原文债。

⭐ **两条签名里都没有 `p`、没有 `vJ1`、没有任何 `det p vJ1`** ⟹ **不分格**，
共线格与横截格共用。这是「原文侧不走 `⟨p,vJ1⟩` 锥」（见 `LeafAShellLsideFork` §26 的
四处原文逐字，集成者第 239 轮裁决四）的可编译版本。

⚠ **射程自限**：
1. 结论方向是 `dir J`，**不是** `ChainDataGeomParts` 的字段 `c.vJ`。把两者等同需要一条
   「`∃ J` 选出来的边 ＝ 字段 `nJ`」的字典（集成者的「断口二」），**本文件没有它**，
   也不声称它成立。
   ⭐ **与 `TowerHbase.rec_vJ_of_parts_unbounded_line` 的两向差（`§52`）**：那条的结论直接
   落在字段 `c.vJ` 上，**整条绕开这条字典**，代价是要一条「沿 `c.vJ` 任意远有点」的
   无界性 `hunb`；本条的输入是原文自己的钉住步骤（`b3_colle2.txt:488` ＋ `:500`），
   代价是欠那条字典。⟹ 两条不互含，都留（`§110.2`，去重挂集成者）。
   ⟹ 若只求最短路径关掉这一格，**那条更短**（少一条字典，且按 lane-tower-hbase 自报
   还同时省掉 `hg` 与 `hne`；**他报，我未复跑**）。
2. `hlcU : IsLatticeConvexRegion (⋃ i, Ahat i)` 是 binder；在链上它由
   `RecVJFromParts.latticeConvex_of_parts` 免费。⚠ **逐层**版 `hlc` 另有产者
   （lane-tower-hlev 报 `LaneHole3ConeHkeyE.isLatticeConvexRegion_hatOf_of_maxA`；
   **他报，我未复核**），两个版本别混用。
3. `hne : ∀ i, (Ahat i).Nonempty` 按 `blueprint/CORE-HOLES.md` 常设纪律 #6
   **不是链上现货**（`ahat_nonempty` 是并集非空），照抄为 binder，不声称可兑现。
4. ccw／cw 那一位（`CORE-HOLES.md` 标 🔴 未裁）本文件不碰：只用了 ccw 那支，且
   **不主张**链上是 ccw；cw 镜像（`hgrow_of_pinned_cw` ＋ `exists_gJ_pinned_cw`）结论是
   `-dir J` 方向，接法逐字对称，谁为真由别的 lane 判。

## §27d  共线格上把 `hArcbdd` 兑掉

`rec_dirJ_of_gJ_pinned_ccw_of_arc_empty_lside`：把 `hArcbdd` 换成一条等式 `Arc ℓ J = ∅`，
于是**整个 `b3_colle2.txt:502`/`:506` 那句假设从签名里消失**，只剩 `hg₁`。这是
lane-tower-hlev 那条读数（`J = ι+1` ⟹ `J` 是 `ℓ` 的紧邻后继 ⟹ `Arc ℓ J = ∅`）的内核版本。
⚠ 「`J = ι+1` ⟹ `Arc ℓ J = ∅`」本身本文件**不证**（那要环序侧的紧邻后继刻画），
收成 binder `hArc0`。
⚠ 这不是 `§41` 的空真陷阱：空的是求和／量词的**指标集**，结论未被削弱
（`exists_gJ_pinned_ccw` 的证明体里那个和式右端变 0 ⟹ 钉住反而对**所有** `k` 成立）。

## ⛔ 本文件不主张的

⛔ 不主张 `hJunb`（`b3_colle2.txt:500` 的截长无界）在链上成立；它是显式 binder。
⛔ 不主张断口二（`∃ J` 选出的边 ＝ 字段 `nJ`）成立。
⛔ 不主张 `ChainDataGeomParts` 能产出 `Colle35.ItemII`（穷尽性）。lane-env-refute 本轮报
   内核见证 `collinearStrip_lside_not_itemII`（`nℓ` / `cz` 全称，只要 `nℓ ≠ 0`）把
   `LeafAShellLsideFork` §24 的见证集合在 `ItemII` 之下判为不可满足 ⟹ 该洞定位到
   `ChainDataGeomParts` 缺 `ItemII`（字段表里最近的 `envB` 是包络性，不是穷尽性）；
   **他报，我未复跑**，本文件不依赖它。
-/
import Nivat.External.Colle.ItemII
import Nivat.External.Colle.LeafAJSelect
import Nivat.External.Colle.LeafAShellLsideFork
import Nivat.External.Colle.NlmaxReachMin
import Nivat.External.Colle.EnvRefuteCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Nivat.LeafAShellPinGrow

open Nivat Nivat.LE2 Nivat.Colle35

/-! ## §27a  `hwit` ⟸ `rec_vJ`（零前提） -/

/-- **`rec_vJ ⟹ hwit`，零前提。** 取 `y := z + vJ`，则 `z + vJ - y = 0` 而 `det vl 0 = 0`。

⟹ 与 `LeafAShellLsideFork.rec_vJ_of_level_witness_collinear_lside` 合起来说明：
`hwit` 在那六条前提下与结论**等价**，不是一个更弱的充分条件。

⚠ 本条与原文无关（纯代数），不对应 `b3_colle2.txt` 任何一行；它是对「`hwit` 这条 binder
值多少钱」的定价，不是一条几何事实。 -/
theorem hwit_of_rec_vJ_lside {U : Set (ℤ × ℤ)} (vl : ℤ × ℤ) {vJ : ℤ × ℤ}
    (hrec : ∀ z ∈ U, z + vJ ∈ U) :
    ∀ z ∈ U, ∃ y ∈ U, det vl (z + vJ - y) = 0 := by
  intro z hz
  refine ⟨z + vJ, hrec z hz, ?_⟩
  have h0 : (z + vJ - (z + vJ) : ℤ × ℤ) = 0 := sub_self _
  rw [h0]
  simp [det]

/-- ⭐ **§27a 的定价结论：共线格里 `hwit ⟺ rec_vJ`。**

`mp` 是 `LeafAShellLsideFork.rec_vJ_of_level_witness_collinear_lside`，
`mpr` 是上面那条（零前提）。⟹ 「归约到 `hwit`」没有降低难度。

前提逐条与 §25 同：`hccpos` / `hp`（`p = -cc•vl`，共线格）/ `hvlprim` / `hrecp`（`rec_p`）/
`hswept`（`MaxEnv.SweptClosed`，守卫只看终点高度）/ `hhp`（半平面下界）/
`hlevel`（`⟪nJ,vJ⟫ = 0`，即 `vJ` 与墙平行）。 -/
theorem hwit_iff_rec_vJ_collinear_lside {U : Set (ℤ × ℤ)} {nJ vl p vJ : ℤ × ℤ}
    {cJ : ℤ} {cc : ℕ}
    (hccpos : 0 < cc) (hp : p = -(cc : ℤ) • vl) (hvlprim : Primitive vl)
    (hrecp : ∀ z ∈ U, z + p ∈ U)
    (hswept : MaxEnv.SweptClosed U vl nJ cJ)
    (hhp : ∀ z ∈ U, cJ ≤ dot nJ z)
    (hlevel : dot nJ vJ = 0) :
    (∀ z ∈ U, ∃ y ∈ U, det vl (z + vJ - y) = 0) ↔ (∀ z ∈ U, z + vJ ∈ U) :=
  ⟨fun hwit => Nivat.LaneLeafAShellLsideFork.rec_vJ_of_level_witness_collinear_lside
      hccpos hp hvlprim hrecp hswept hhp hlevel hwit,
   fun hrec => hwit_of_rec_vJ_lside vl hrec⟩

/-! ## §27c  钉住 ⟹ `dir J` 方向的 `rec_vJ`（不分格） -/

/-- ⭐⭐ **塔侧钉住 ＋ 截长无界 ⟹ `⋃ Âᵢ` 在 `dir J` 方向上递归闭。**

三段接线，无新数学：`LeafAJSelect.hgrow_of_pinned_ccw` → `Colle35.ray_of_pinned_growth`
→ `Colle35.rec_of_ray`。`hgrow_of_pinned_ccw` 的结论是 `… ∈ Ahat (σ i)`，
`ray_of_pinned_growth` 要的是 `… ∈ Ahat i`，取 `i := σ i` 即可（`σ` 只是重标号）。

量词对应（`b3_colle2.txt:500`）：`hJunb` 是「不存在统一上界 `L`」，逐字对应原文
「`|Â_i ∩ w_i(J)| < |Â_{i+1} ∩ w_{i+1}(J)|` for infinitely many `i`」推出的截长无界；
`hg` 是 `:488` 的钉住沿稳定子列 `σ` 传播的形状。

⚠ 签名里没有 `p` / `vJ1` / `det p vJ1` ⟹ **共线格与横截格共用**。
⚠ 结论方向是 `dir J`，不是 `ChainDataGeomParts` 的字段 `c.vJ`；两者的字典本文件没有。
⚠ `hne` 按常设纪律 #6 不是链上现货。 -/
theorem rec_dirJ_of_pinned_tower_lside {Ahat : ℕ → Set (ℤ × ℤ)} {J g_J : ℤ × ℤ}
    (AhatMono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j)
    (hfin : ∀ i, (Ahat i).Finite) (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (hlcU : IsLatticeConvexRegion (⋃ i, Ahat i))
    (hJEall : ∀ i, J ∈ E (Ahat i))
    (hJunb : ¬ ∃ L : ℕ, ∀ i, Nivat.PolyChain.faceLen (Ahat i) J ≤ L)
    {σ : ℕ → ℕ} (hσmono : StrictMono σ) {i₀ : ℕ}
    (hg : ∀ i ≥ i₀, Nivat.PolyChain.faceStart (Ahat (σ i)) J = g_J) :
    ∀ z ∈ ⋃ i, Ahat i, z + dir J ∈ ⋃ i, Ahat i := by
  have hgrow :=
    Nivat.LeafAJSelect.hgrow_of_pinned_ccw AhatMono hfin hne hlc hJEall hJunb hσmono hg
  have hgrow' : ∀ N : ℕ, ∃ i : ℕ, ∀ t : ℕ, t ≤ N → g_J + (t : ℤ) • dir J ∈ Ahat i := by
    intro N
    obtain ⟨i, hi⟩ := hgrow N
    exact ⟨σ i, hi⟩
  exact rec_of_ray hlcU (ray_of_pinned_growth hgrow')

/-- ⭐⭐ **§27b 的正面兑现：`hg` 由 `exists_gJ_pinned_ccw` 供给，于是 `σ` / `i₀` / `g_J` 消失。**

剩下的原文债只有两条：`hg₁`（`b3_colle2.txt:488` 的 `g_1`／`k_i` 归一化）与
`hArcbdd`（`b3_colle2.txt:502`/`:506` 的中间截长有界）。其余 binder 全是塔侧的
（`AhatMono` / `hfin` / `hne` / `hlc` / `hlcU` / `henv` / `hSfin` / `hSarea` /
`hℓE` / `hJE` / `hℓJ` / `hJEall` / `hJunb`）。

⚠ `hne` 按常设纪律 #6 **不是链上现货**；`hlcU` 在链上由 `latticeConvex_of_parts` 免费。 -/
theorem rec_dirJ_of_gJ_pinned_ccw_lside {Ahat : ℕ → Set (ℤ × ℤ)}
    {Sphi : Finset (ℤ × ℤ)} {ℓ J g₁ : ℤ × ℤ}
    (AhatMono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j)
    (hfin : ∀ i, (Ahat i).Finite) (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (hlcU : IsLatticeConvexRegion (⋃ i, Ahat i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J)
    (hg₁ : ∀ i, Nivat.PolyChain.faceStart (Ahat i) ℓ
        + (Nivat.PolyChain.faceLen (Ahat i) ℓ : ℤ) • dir ℓ = g₁)
    (hArcbdd : ∀ μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J,
      ∃ L : ℕ, ∀ i, Nivat.PolyChain.faceLen (Ahat i) μ ≤ L)
    (hJEall : ∀ i, J ∈ E (Ahat i))
    (hJunb : ¬ ∃ L : ℕ, ∀ i, Nivat.PolyChain.faceLen (Ahat i) J ≤ L) :
    ∀ z ∈ ⋃ i, Ahat i, z + dir J ∈ ⋃ i, Ahat i := by
  obtain ⟨g_J, σ, hσmono, i₀, hg⟩ :=
    Nivat.LeafAJSelect.exists_gJ_pinned_ccw hfin hlc henv hSfin hSarea hℓE hJE hℓJ hg₁ hArcbdd
  exact rec_dirJ_of_pinned_tower_lside AhatMono hfin hne hlc hlcU hJEall hJunb hσmono hg

/-! ## §27d  共线格上把 `hArcbdd` 兑掉 -/

/-- ⭐ **共线格（`J = ι+1`）上把 `hArcbdd` 兑掉。**

空指标集上 `hArcbdd` 的 `∀ μ ∈ ∅` 当场为真，故该前提从签名里消失，只剩 `hArc0` 一条**等式**
＋ `hg₁`。这是 lane-tower-hlev 那条读数（`J = ι+1` ⟹ 紧邻后继 ⟹ `Arc ℓ J = ∅`）的内核版本。

⚠ 本文件**不证** `J = ι+1 ⟹ Arc ℓ J = ∅`（那要环序侧的紧邻后继刻画），`hArc0` 收成 binder。
⚠ 这不是 `§41` 的空真陷阱：空的是求和／量词的**指标集**，结论未被削弱
（`exists_gJ_pinned_ccw` 的证明体里那个和式右端变 0 ⟹ 钉住反而对**所有** `k` 成立，
比一般情形强）。 -/
theorem rec_dirJ_of_gJ_pinned_ccw_of_arc_empty_lside {Ahat : ℕ → Set (ℤ × ℤ)}
    {Sphi : Finset (ℤ × ℤ)} {ℓ J g₁ : ℤ × ℤ}
    (AhatMono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j)
    (hfin : ∀ i, (Ahat i).Finite) (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (hlcU : IsLatticeConvexRegion (⋃ i, Ahat i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J)
    (hg₁ : ∀ i, Nivat.PolyChain.faceStart (Ahat i) ℓ
        + (Nivat.PolyChain.faceLen (Ahat i) ℓ : ℤ) • dir ℓ = g₁)
    (hArc0 : Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J = ∅)
    (hJEall : ∀ i, J ∈ E (Ahat i))
    (hJunb : ¬ ∃ L : ℕ, ∀ i, Nivat.PolyChain.faceLen (Ahat i) J ≤ L) :
    ∀ z ∈ ⋃ i, Ahat i, z + dir J ∈ ⋃ i, Ahat i := by
  refine rec_dirJ_of_gJ_pinned_ccw_lside AhatMono hfin hne hlc hlcU henv hSfin hSarea
    hℓE hJE hℓJ hg₁ ?_ hJEall hJunb
  intro μ hμ
  rw [hArc0] at hμ
  simp at hμ

/-! ## §28 剩余类覆盖 ⟸ 格凸性 ＋ `rec_p` ＋ 一条非循环的 `rec_vJ`

集成者第 242 轮派给本 lane 的靶子是 `bottom` 的 `hline0`。**它是别名**：
`BottomHz0Collapse.hdz_hz0_hline0_of_cover_collinear`（主仓，集成者本人同轮落的）已把
共线格的 `hdz` / `hz₀` / `hline0` 三条一次产出，唯一代价是剩余类覆盖

    hcov : ∀ r : ℤ, ∃ g ∈ U, (-dot nJ vJ1) ∣ (dot nJ g - r)

⟹ 真靶子是 `hcov`，不是 `hline0`。本节把 `hcov` 证掉。

## 归属（§91）与一次现货误记（自报）

⚠ **路线不是本 lane 发现的**：`blueprint/LANDING.md` 第 234 轮 §5 已由集成者写下
「缺口是 `hconv`（格凸），而 `hconv` 在链上免费」并派了 `heights_contiguous_of_conv_recVJ`；
同一条还预先堵掉了「格凸 ＋ `nJ` 本原 ⟹ 高度谱连续」的错路（两点集 `{(0,0),(1,2)}`），
指出「缺的是厚度，厚度就是 `rec_vJ`」。本节是那条派工的兑现，不是新路线。

⚠ **本 lane 本轮先写了一份重复品**：高度谱那一条**本 lane 自己上一轮已经证过**——
`LeafAShellLsideFork.heights_covered_of_latticeConvex_lside`（§16b，前提比重写的那份还弱：
只要 `vJ ≠ 0`，不要 `Primitive vJ`）。符号那一条同样已有：
`LeafAShellLsideFork.dot_nonneg_of_rec` ＋ 字段 `dot_nJ_p`。⟹ 重复品**不落地**，
本节只保留真正新的三步，并按集成者本轮的通例把这次「没先数现货」记在这里。

## 本节新增的三步

1. `not_latticeConvex_Aeven` —— **判别性收据（§52，两座台架之差）**。`EnvRefuteCover` §4 的
   `not_heights_of_rec_fields` 用居民 `Aeven = {w | 0 ≤ w.2 ∧ 2 ∣ w.2}` 证明 `hcov` 不从
   `ahat_nonempty` / `rec_p` / `ahat_halfPlane` / `hsweep` / `dot_nJ_p` 五条字段推出。
   本条在内核里指出该居民**不是格凸的**（`(0,0)`、`(0,2)` 在里面、中点 `(0,1)` 不在）。
   ⟹ 两条结论不冲突，差的恰是格凸性。
   ⚠ 另记（`LANDING.md` 第 233 轮，集成者）：`Aeven` 的 `det p vJ1 ≠ 0`，按那条裁决
   它**不是链上共线格的居民**；本条不依赖那一点，只用它做前后两条引理的分界。
2. `cover_of_latticeConvex_rec` —— 高度谱是一整条半直线 ⟹ 每个剩余类都被打到。
3. `hdz_hz0_hline0_of_latticeConvex_collinear` —— 接上 `EnvRefuteCover.heights_iff_cover`
   与 `NlmaxReachMin.exists_reachMin_of_L`，直接给出 `BottomReachMin.bottom_of_reachMin`
   的 `hdz` ∧ `hz₀` ∧ `hline0` 三条 binder。

## 还欠什么（射程，§50）

⚠ 除 `hrecvJ` 外，下面各条前提全是 `ChainDataGeomParts` 的字段：格凸性经
`ChainAssemble.latticeConvex_iUnion_hatOf`（只吃 `maxA` / `hfin` / `AhatMono`，**不吃 `bottom`**），
`hrecp` 是 `rec_p`，`hnJ` 是 `nJ_prim`，`hvJ0` 是 `vJ_ne`，`hnJvJ` 是 `F.dot_nJ_vJ`，
`hne` 是 `ahat_nonempty`，`hhp` 是 `hhp`，`hp0` 是 `dot_nJ_p`，`hsweep` 是 `hsweep`，
`hlowL` / `hattL` 是 `ahat_halfPlane_L` / `ahat_attained_L`，`hpar` 是共线格的定义本身。

⚠ **`hrecvJ` 必须由非循环的产者供**：`RecVJFromParts.rec_vJ_of_parts` 吃 `c.bottom`，
喂回来就成环（`BottomReachMin.lean` 抬头同一警告）。现成的非循环产者：本文件 §27c 的
`rec_dirJ_of_gJ_pinned_ccw_lside`（欠 `hg₁` / `hJunb` ＋ 断口二那条字典）与抽象层的
`TowerHbase.rec_vJ_of_unbounded_line`（欠无界性；集成者本轮明令保留该层）。

⚠ 本节全部在抽象 `U : Set (ℤ × ℤ)` 上，**不吃 `ChainDataGeomParts`**——刻意如此：吃 `c`
就等于同时拿到 `c.bottom`，按 `RecVJSubsume` 那道护栏是零增量，且对**造** `c` 的人无用。 -/

section Hcov

open Nivat.MaxEnv

variable {U : Set (ℤ × ℤ)}

/-- **`EnvRefuteCover.Aeven` 不是格凸区域。**  `(0,0)`、`(0,2)` 在里面而中点 `(0,1)` 不在。

⟹ `EnvRefuteCover` §4（覆盖条件不从五条字段推出）与下面的 `cover_of_latticeConvex_rec`
（覆盖条件从格凸性 ＋ `rec_p` ＋ `rec_vJ` 推出）之间**差的就是格凸性**，两者不冲突。

⚠ **辖域词（第 244 轮补，lane-tower-hlev 指出，lane-env-refute 同轮独立加强）**：
上一句里的「就是」只在 **`Aeven` 这一个见证的范围内**成立，**不许**读成
「格凸性是 `cover_of_latticeConvex_rec` 的唯一承重前提」。两侧各有一条内核收据：

* lane-env-refute 亲算：`Aeven` 配 `nJ=(0,1)`、`vJ=(1,0)`、`vJ1=(0,-4)`、`p=(1,2)`、`cJ=0` 时，
  `cover_of_latticeConvex_rec` 的前提表里**除 `hlc` 外每一条都成立**（`hrecvJ` 因
  `Aeven + (a,0) ⊆ Aeven` 平凡成立），而结论取 `r` 奇即假 ⟹ 在**这个**见证上格凸性确是唯一承重的。
* lane-tower-hlev 的 `TowerHlevCover.not_cover_of_geom_bundle`（`tmp/wip/hlev-cover-recvj.lean`，
  0 sorry、公理全白，**他报的，我未复跑**）：二十条前提**含** `IsLatticeConvexRegion`、
  载体是真 `⋃ i, hatOf A kk vl i`，结论（剩余类覆盖）为假 ⟹ **`hrecvJ` 在本条里不可删，
  同样是承重输入**。

⟹ 正确的记法是：`hlc` 与 `hrecvJ` **两条都承重**，谁都不单独充分。
另记（同轮，hlev）：`rec_vJ_not_from_linear_fields_collinear_lside` 的居民
`{z | z.1 ≤ 0 ∧ z.2 = 0}` 在 `nJ = (-1,0)` 下高度集是全部非负整数，**覆盖在它上面成立**
⟹ 「`rec_vJ` 假」**不蕴含**「覆盖假」，那条补不上这一格；要补得把射线斜率换成 `-2`。 -/
theorem not_latticeConvex_Aeven : ¬ IsLatticeConvexRegion Nivat.EnvRefuteCover.Aeven := by
  rintro ⟨C, hconv, -, hEC⟩
  have h0 : ((0, 0) : ℤ × ℤ) ∈ Nivat.EnvRefuteCover.Aeven := ⟨le_rfl, ⟨0, by norm_num⟩⟩
  have h2 : ((0, 2) : ℤ × ℤ) ∈ Nivat.EnvRefuteCover.Aeven := ⟨by norm_num, ⟨1, by norm_num⟩⟩
  rw [hEC] at h0 h2
  have hmid := hconv h0 h2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  have hmem : ((0, 1) : ℤ × ℤ) ∈ Nivat.EnvRefuteCover.Aeven := by
    rw [hEC]
    have heq : toReal ((0, 1) : ℤ × ℤ)
        = (1/2 : ℝ) • toReal ((0, 0) : ℤ × ℤ) + (1/2 : ℝ) • toReal ((0, 2) : ℤ × ℤ) := by
      refine Prod.ext_iff.mpr ⟨?_, ?_⟩ <;>
        simp only [toReal, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul] <;>
        norm_num
    show toReal ((0, 1) : ℤ × ℤ) ∈ C
    rw [heq]
    exact hmid
  obtain ⟨-, k, hk⟩ := hmem
  change (1 : ℤ) = 2 * k at hk
  omega

/-- ⭐⭐ **剩余类覆盖成立。**

高度谱那一步是本 lane §16b 的 `LeafAShellLsideFork.heights_covered_of_latticeConvex_lside`
（格凸 ＋ `rec_p` ＋ `rec_vJ` ⟹ 从任一点的高度起每个整数高度都被取到）；符号 `0 < ⟪nJ,p⟫`
由 `LeafAShellLsideFork.dot_nonneg_of_rec`（非空 ＋ `hhp` ＋ `rec_p` ⟹ `0 ≤ ⟪nJ,p⟫`）配
字段 `dot_nJ_p`（只给 `≠ 0`）升成严格——两条都不经 `bottom`。

本条新增的只有最后一步算术：要打到剩余类 `r`，取高度 `r + k·e`（`e := -⟪nJ,vJ1⟫ ≥ 1`，
`k := (⟪nJ,g₀⟫ - r).toNat`）即可，因为高度谱向上是满的。 -/
theorem cover_of_latticeConvex_rec {nJ vJ vJ1 p : ℤ × ℤ} {cJ : ℤ}
    (hlc : IsLatticeConvexRegion U)
    (hrecp : ∀ g ∈ U, g + p ∈ U) (hrecvJ : ∀ g ∈ U, g + vJ ∈ U)
    (hnJ : Primitive nJ) (hvJ0 : vJ ≠ 0) (hnJvJ : dot nJ vJ = 0)
    (hne : U.Nonempty) (hhp : ∀ g ∈ U, cJ ≤ dot nJ g) (hp0 : dot nJ p ≠ 0)
    (hsweep : dot nJ vJ1 < 0) :
    ∀ r : ℤ, ∃ y ∈ U, (-dot nJ vJ1) ∣ (dot nJ y - r) := by
  have hδ : 0 < dot nJ p :=
    lt_of_le_of_ne
      (Nivat.LaneLeafAShellLsideFork.dot_nonneg_of_rec hne hhp hrecp) (Ne.symm hp0)
  obtain ⟨g₀, hg₀⟩ := hne
  intro r
  have he1 : (1 : ℤ) ≤ -dot nJ vJ1 := by omega
  set k : ℕ := (dot nJ g₀ - r).toNat with hk
  have hk' : dot nJ g₀ - r ≤ (k : ℤ) := by rw [hk]; exact Int.self_le_toNat _
  have hkn : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have hle : dot nJ g₀ ≤ r + (k : ℤ) * (-dot nJ vJ1) := by
    have h1 : (k : ℤ) * 1 ≤ (k : ℤ) * (-dot nJ vJ1) := mul_le_mul_of_nonneg_left he1 hkn
    linarith
  obtain ⟨y, hy, hyd⟩ :=
    Nivat.LaneLeafAShellLsideFork.heights_covered_of_latticeConvex_lside
      hlc hnJ hg₀ hrecvJ hrecp hnJvJ hvJ0 hδ hle
  exact ⟨y, hy, (k : ℤ), by rw [hyd]; ring⟩

/-- ⭐⭐⭐ **共线格：`bottom` 的 `hdz` ∧ `hz₀` ∧ `hline0` 三条，代价只剩一条非循环的 `rec_vJ`。**

结论形状与 `NlmaxReachMin.exists_reachMin_of_L` 逐字符一致，即
`BottomReachMin.bottom_of_reachMin` 的 `hdz` ∧ `hz₀` ∧ `hline0` 三条 binder。
`det p vJ ≠ 0` 由本 lane §2 的 `LeafAShellLsideFork.det_p_vJ_ne_of_fields` 白拿
（集成者的 `BottomHz0Collapse.det_p_vJ_ne` 是同一事实的吃 `c` 版本，那版对造 `c` 的人不可用）。

⚠ `hrecvJ` 的非循环产者见本节抬头；其余前提全是字段。 -/
theorem hdz_hz0_hline0_of_latticeConvex_collinear {nJ vJ vJ1 p : ℤ × ℤ} {cJ cL : ℤ}
    (hlc : IsLatticeConvexRegion U)
    (hrecp : ∀ g ∈ U, g + p ∈ U) (hrecvJ : ∀ g ∈ U, g + vJ ∈ U)
    (hnJ : Primitive nJ) (hvJ : Primitive vJ) (hnJvJ : dot nJ vJ = 0)
    (hne : U.Nonempty) (hhp : ∀ g ∈ U, cJ ≤ dot nJ g) (hp0 : dot nJ p ≠ 0)
    (hsweep : dot nJ vJ1 < 0) (hpar : det p vJ1 = 0)
    (hlowL : ∀ g ∈ U, cL ≤ dot (det p vJ • (-p.2, p.1)) g)
    (hattL : ∃ g ∈ U, dot (det p vJ • (-p.2, p.1)) g = cL)
    (ε : ℕ) :
    ∃ z₀ : ℤ × ℤ, dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧ z₀ ∈ reachSet U vJ1 ∧
      ∀ z ∈ reachSet U vJ1, dot nJ z = cJ - (ε : ℤ) - 1 →
        ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • vJ := by
  have hvJ0 : vJ ≠ 0 := (prim_iff_primitive.mpr hvJ).ne_zero
  exact Nivat.NlmaxReachMin.exists_reachMin_of_L
    (prim_iff_primitive.mpr hnJ) (prim_iff_primitive.mpr hvJ) hnJvJ hpar
    (Nivat.LaneLeafAShellLsideFork.det_p_vJ_ne_of_fields hnJvJ hp0 hvJ0) hlowL hattL
    ((Nivat.EnvRefuteCover.heights_iff_cover hsweep hhp).mpr
      (cover_of_latticeConvex_rec hlc hrecp hrecvJ hnJ hvJ0 hnJvJ hne hhp hp0 hsweep) ε)

end Hcov

end Nivat.LeafAShellPinGrow

#print axioms Nivat.LeafAShellPinGrow.hwit_of_rec_vJ_lside
#print axioms Nivat.LeafAShellPinGrow.hwit_iff_rec_vJ_collinear_lside
#print axioms Nivat.LeafAShellPinGrow.rec_dirJ_of_pinned_tower_lside
#print axioms Nivat.LeafAShellPinGrow.rec_dirJ_of_gJ_pinned_ccw_lside
#print axioms Nivat.LeafAShellPinGrow.rec_dirJ_of_gJ_pinned_ccw_of_arc_empty_lside
#print axioms Nivat.LeafAShellPinGrow.not_latticeConvex_Aeven
#print axioms Nivat.LeafAShellPinGrow.cover_of_latticeConvex_rec
#print axioms Nivat.LeafAShellPinGrow.hdz_hz0_hline0_of_latticeConvex_collinear
