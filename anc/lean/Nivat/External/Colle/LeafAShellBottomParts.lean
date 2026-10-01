/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-leafa-shell
-/
import Nivat.External.Colle.BottomRoom
import Nivat.External.Colle.BottomFree
import Nivat.External.Colle.FanEndpoint
import Nivat.External.Colle.LeafAShellWedgeSign

set_option autoImplicit false

/-!
# `bottom` 的字段层总装：两格各一条，残项收敛到**一条**壳侧输入

集成者第 242 轮派给 lane-leafa-shell 的靶子是「`hedge` / `hlow` / `hhigh` 在共线格的字段化」，
并要求「先数现货」。数完的结果是：**这三条在主仓里已经各自被处理过，缺的是把它们与
`hdz` / `hz₀` / `hline0` 那一侧拼成 `ChainDataGeomParts.bottom` 逐字的那一步**。本文件就是那一步。

## §1 `hedge` 是字段，零成本（本轮第一件事的答案）

`Nivat.Colle35.FaceBlock` 的 `edge` 字段逐字是

    ∀ b ∈ S.erase a, (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a + (j : ℤ) • v) ∨ 1 ≤ dot n (b - a)

而 `BottomReachMin.bottom_of_reachMin` 要的 `hedge` 与它**逐字符只差 `j ≤ r` 一个合取**。
`FanEndpoint.faceBlock_edge_forget_len` 已经把那个合取忘掉（证明体是
`fun b hb => (F.edge b hb).imp (fun ⟨j, h1, _, h3⟩ => ⟨j, h1, h3⟩) id`，我逐字读过，不是转述）。
⟹ `hedge` **不是债**，`hedge_of_parts` 只是把它挂到 `c.F` 上。

## §2 `hlow` / `hhigh`：合并形是现货，且合并**不产生净收益**

* `BottomReachMin.hslice_of_low_high` ＋ `bottom_of_reachMin_merged`（lane-tower-hbase 第 242 轮）
  把两条合成一条 ε-无关的 `hslice`，并证明两种写法等价。
* `BottomRoom.bottom_of_window` 的 `hwin` 是同一条的带守卫形；
  `BottomRoom.window_of_shell_of_line`（lane-chaindata-lead）把它归约到
  **有限壳 `P` 的 `E(𝒮_φ)`-包络性**，即一条关于 `EnvOf ↑𝒮_φ` 的存在命题
  （`IntegShellFeedEnvOf.lean` 的 `shellFeed_iff_envOf_cover'`），与字段 `shellEnv`
  **同谓词但量词与载体都不同**（详见 §11）。

⚠ 集成者派工信里对 `hhigh_vacuous` 的方向警告（「`bottom` 要对**每个** `ε` 成立，所以
『取大 `ε`』不合法」）**成立**，且已被两处独立记过：`BottomRoom` 抬头那段
（「At `ε = 0` it degenerated completely」）与 `BottomReachMin` 的 `hslice_of_low_high` 一节
（「净收益为零」）。本文件不重复立案。

## §3 本文件的增量：`ShellFeed` ⟹ `bottom` 逐字

`bottom_of_triple_of_shellFeed` 把三段现货接成一条：

    (hdz ∧ hz₀ ∧ hline0)  ＋  ShellFeed  ⟹  ChainDataGeomParts.bottom 的结论逐字

其中 `hedge` / `ha_mem` / `dot_nJ_vJ` / `nJ_prim` 全部由 `c.F` 与 `c` 的字段供，
`hz₀P` 由 `MaxEnv.mem_shell_succ_iff` ＋ `hdz` ＋ `hz₀` 白送（`z₀` 的高度恰是第 `ε+1` 层
新增的那条线），不再是 binder。两条特化：

* `bottom_of_cover_shellFeed_collinear`（共线格，`det p vJ1 = 0`）——三合一走
  `BottomHz0Collapse.hdz_hz0_hline0_of_cover_collinear`，残项是剩余类覆盖 `hcov`。
* `bottom_of_wedge_shellFeed_transverse`（横截格，`det p vJ1 ≠ 0`）——三合一走
  `BottomFree.hdz_hz0_hline0_free`，`hcov` 由 `ConeCover.cover_of_parts` 白送，
  残项换成楔形的定向 `hdir` ＋ 支撑界 `hsupp`。

⟹ **两格的 `bottom` 现在各只欠三件**：`rec_vJ`（非循环的 `hrecT`）、`ShellFeed`、
定向位 `hvJ_eq`；共线格另欠 `hcov`，横截格另欠 `hdir` ＋ `hsupp`。

⚠ **上面这段是第 242 轮的读数，第 244 轮已被 §7 取代**（PROTOCOL §103：旧读数不订正，
现货读数另起一条）。现在的读数见 §7。

## §4 `ShellFeed` 与原文逐量词对应

`ShellFeed d T vJ1 nJ cJ` 的八个合取，对着 `scratch/b3_colle2.txt:518`

    Â_i^{(ε)} := {g - t·v⃗_{ℓ_{J+1}} ∈ Â_∞^{(ε)} : g ∈ Â_i, t ∈ ℤ₊}

与 `:520`「is an $E(\mathcal{S}_{\varphi})$-enveloped set」：

| `ShellFeed` 的合取 | 原文对应物 |
|---|---|
| `P.Finite` / `P.Nonempty` / `PosArea P` / `IsLatticeConvexRegion P` | `Â_i^{(ε)}` 是有限格凸正面积集（`:520` 的「enveloped set」预设） |
| `P ⊆ MaxEnv.shell T vJ1 nJ cJ (ε+1)` | `:518` 的 `∈ Â_∞^{(ε)}`（本文件的层号是 `ε+1`，见下） |
| `E P = E ↑𝒮_φ` ＋ 面长不等式 | `:520` 的 `E(𝒮_φ)`-enveloped |
| `∀ z₀ … , ∃ P, … ∧ z₀ ∈ P` | `:516` 的「for an appropriate $\epsilon$ fixed and **all $i$ sufficiently large**」＋ `:518` 的 `g ∈ Â_i`：`Â_i^{(ε)}` 是**对给定点取充分大的 `i`** ⟹ **`P` 依赖 `z₀`**，故 `∃P` 必须在 `∀z₀` 之内 |

⚠ **三处比原文强。第 1、2 处是消费者强加的，不是本文件新增的债；第 3 处是本文件自己写错、
本轮已改正**（详见 §8）：

1. **`∀ ε`**。原文 `:516` 只说「for an appropriate $\epsilon\in\mathbb{N}$ fixed and all
   $i\in\mathbb{N}$ sufficiently large」，即 `∃ ε`。`ChainDataGeomParts.bottom` 字段自己是
   `∀ ε : ℕ`，`ShellFeed` 只是跟着它。这正是 `blueprint/OPEN.md` 第 9 条已立案的那条
   （「原文『某个合适的 ε』确是存在性，`bottom` 的 `∀ε` 字段很可能是真欠债」）。
2. **层号 `ε+1` 而不是 `ε`**。`bottom` 的第四合取谈的是第 `ε+1` 层，`z₀` 落在它新增的那条线上，
   所以 `P` 必须活在 `ε+1` 层。原文 `:518` 的 `ε` 是同一个自由变量，不构成新量词。
3. 🔴 **量词顺序**（致命，已改正）。第 242 轮的 `ShellFeedLine` 把 `∃ P` 提到了 `∀ z₀` **之前**，
   于是同一个有限 `P` 要含下整条最低线。原文 `:518` 的 `Â_i^{(ε)}` 对**每个** `g ∈ Â_i` 另取
   充分大的 `i`，`P` 本来就依赖 `z₀` ⟹ 提升量词没有原文对应物（硬规矩 5）。
   内核见证 `not_shellFeedLine_quadrant`；改正后的 `ShellFeed` 把 `z₀` 收成参数。
   ⟹ 第 1、2 处只是**范围**上比原文宽，不影响可满足性；第 3 处让前提域**空**，性质不同。

⚠ **`hvJ_eq : vJ = dir (-nJ)` 原样传递、未审**。`BottomRoom` 的 §6 已记：该 binder 对定向敏感，
第 179 轮红线禁止在「链 `vl` ＝ 源 `v⃗_{ℓ_ι}`」裁决前移动它。本文件不碰，只转发。

⚠ **`hnegnJ : -nJ ∈ E ↑𝒮_φ` 不是 `ChainDataGeomParts` 的字段**，是本文件新收的 binder。
调用点（`tmp/wip` 的 leaf A 总装，按文件名 ＋ 标识符引：`LeafAAssemble.lean` 的扇形数据段）
有 `nJ = -J` 且 `J ∈ E ↑𝒮_φ`，所以它在链上有现货；这里不假装它是字段。

## §5 §52 两座台架之间的差

`HwinRefute.not_Hwin_oct8`（lane-leafa-gen）在 oct8 台架上内核否掉一条也叫 `hwin` 的东西。
**那不是这里的 `hwin`**：它否的是 `FillCoverGuarded.fillCover_of_window` 的假设
「窗口整块落在同一个 `collarY i ε` 里」，目标集合是 `collarY`；本文件的 `hwin` 目标集合是
`MaxEnv.reachSet (⋃ i, hatOf …) vJ1`，产者是 `BottomRoom.window_of_shell_of_line`。
两座台架的差就是**目标集合**：一个是 collar，一个是扫出集。同名不同物，已追加进
`blueprint/NOTATION.md`。

`lane-cd-hhigh-refute.lean` / `-refute2.lean` 的两条反例同样不触及本文件：它们否的是
**抽象 `T`** 与 `WeaklyEnveloped ↑S T` 下的 `hhigh`，而 `ShellFeed` 要的是**有限壳 `P` 的
满包络性**（`E P = E ↑𝒮_φ` ＋ 面长不等式），两条反例都不提供这样的 `P`。

## §6 归属（PROTOCOL §91）

本文件不含新数学。三段现货分别是：`BottomRoom` 的 `bottom_of_window` /
`window_of_shell_of_line` / `faceStart_of_edge`（lane-chaindata-lead）、`BottomHz0Collapse` 与
`BottomFree` 的三合一（集成者，`EnvRefuteOrient.hline0_of_supp` 由 lane-env-refute 提供）、
`FanEndpoint.faceBlock_edge_forget_len`（lane-tower-hbase）。本文件的增量是**代入与总装**：
把它们拼成 `ChainDataGeomParts.bottom` 的**逐字结论**，并在这个过程中消掉 `hz₀P` 这条 binder。

## §7 第 244 轮的现货读数（取代 §3 末尾那两行）

本轮两条新料并进来：

* `LeafAShellWedgeSign.exists_wedge_of_parts`（本 lane 本轮，路线归 lane-env-refute 的猜测②）
  ——**楔形整条在链上免费，两格通用**；
* `RecVJTransverse.rec_vJ_of_parts_transverse`（集成者第 243 轮）——**横截格的 `hrecT` 免费**。

于是：

| 格 | `bottom` 现在欠的 binder |
|---|---|
| 横截（`det p vJ1 ≠ 0`） | `ShellFeed` ＋ `hvJ_eq` ＋ `hnegnJ`（见 `bottom_of_shellFeed_transverse`） |
| 共线（`det p vJ1 = 0`） | 上列三条 ＋ `hcov`（剩余类覆盖）＋ `hrecT`（见 `bottom_of_cover_shellFeed_freewedge`） |

`hedge` / `hlow` / `hhigh` / `hdir` / `hsupp` 五条已全部消失。
`hvJ_eq` 与 `hnegnJ` 都不是新债：前者是第 179 轮红线锁住的定向位（本文件只转发、不审），
后者在调用点由 `nJ = -J` ＋ `J ∈ E ↑𝒮_φ` 供。
⟹ **横截格里 `bottom` 的唯一实质欠账是 `ShellFeed`**，而 `ShellFeed` 是一条关于
`EnvOf ↑𝒮_φ` 的存在命题（`IntegShellFeedEnvOf.lean` 的 `shellFeed_iff_envOf_cover'`），
与字段 `shellEnv` **同谓词但量词与载体都不同**（详见 §11）。

⚠ 按盲区 3，第 242 轮的三条（`bottom_of_triple_of_shellFeed` /
`bottom_of_cover_shellFeed_collinear` / `bottom_of_wedge_shellFeed_transverse`）**都不删**：
它们的 binder 更多，但载体相同，是本轮两条的抽象上游。

## §8 自查：第 242 轮的 `ShellFeed` 写强了，本轮内核否掉并改正

§3 / §4 / §6 里说「`hz₀P` 由 `mem_shell_succ_iff` 白送、不再是 binder」的那几句**是错的**，
本轮自查抓到：那一版 `ShellFeed`（现更名 `ShellFeedLine`）要求**有限**的 `P` 含下第 `ε+1` 层
最低线的**全部**点，而那条最低线一般是一整条 `vJ`-射线（`bottom` 第四合取自己就写成
`z₀ + k • vJ`，`L ≤ k`），**无限** ⟹ 定义不可满足，以它为前提的定理空真。

* 内核见证：`not_shellFeedLine_quadrant`（`T := {0 ≤ x ∧ 0 ≤ y}`、`vJ1 := (0,-1)`、
  `nJ := (0,1)`、`cJ := 0`、`ε := 0`；对**任何** `d` 成立，与 `𝒮_φ` 无关）。
* 改正：`ShellFeed` 把 `z₀` 收成参数、`hz₀P` 原样留着 ⟹ 逐字就是
  `BottomRoom.window_of_shell_of_line` 的八条壳侧 binder，**一条都不加强**。
* 因此 §4 的表第 4 行（「最低线整条落在 `P` 里」）描述的是 `ShellFeedLine`，不是 `ShellFeed`；
  `ShellFeed` 对应的那一行应读成「`z₀ ∈ Â_i^{(ε)}` 对充分大的 `i`」，正是 `:518` 的原样。
* §6 末尾「并在这个过程中消掉 `hz₀P` 这条 binder」**撤回**。本文件的增量只剩「代入与总装」。

⟹ 加强的那个量词原文没有对应物（硬规矩 5：当场删）。教训记在这里，不另开 NOTE 条目。

## §9 本文件的三条 `bottom` 产者不吃 `c.bottom`（第 245 轮，机械复核）

🔴 **`bottom` 是 `ChainDataGeomParts` 的字段**（`ChainPartsFeed.lean` 的 `bottom` 字段），
而且是 **Prop 字段**。⟹ 任何形如 `(c : ChainDataGeomParts …) → <bottom 的语句>` 的定理，
都能由 `c.bottom` 一行证出；又因证明无关，**「真造出来的」与「拿字段兑现的」在语义上
根本区分不出来**。`#print axioms` 也看不见（字段投影不是公理）。
⟹ 对本文件这种「结论逐字等于某个字段」的总装，**唯一可能的判据是证明项的语法**：
该投影常量在不在传递依赖闭包里。亲读证明体不是「更严格的做法」，是唯一的做法。

这件事本轮做成了机械判据（`tmp/_depscan245.lean`，一次性收据，走
`env.checked.get.find?` 的传递闭包）。读数（两条正控都响、负控静默，故 `false` 可采信）：

| 声明 | `USES_FIELD` | 闭包 |
|---|---|---|
| 正控 1 `LaneLeafAGenRecVJ.rec_vJ_of_parts` | **true** | 23867 |
| 正控 2 `ConeCover.heights_of_parts_circular` | **true** | 23944 |
| 负控 `BottomHz0Collapse.union_hhp_ge` | false | 10468 |
| `RecVJTransverse.rec_vJ_of_parts_transverse` | false | 23897 |
| `ConeCover.cover_of_parts` | false | 23932 |
| `LeafAShellWedgeSign.hdz_hz0_hline0_of_parts_transverse` | false | 23971 |
| 本文件 `bottom_of_triple_of_shellFeed` | false | 24386 |
| 本文件 `bottom_of_cover_shellFeed_freewedge` | false | 24448 |
| 本文件 `bottom_of_shellFeed_transverse` | false | 25063 |

⚠ PROTOCOL §103：这是第 245 轮那一刻的读数。任一条产者的证明体被改动后必须重跑；
读数不随改动自动作废，也不因后续改动被追认。
⚠ 仪器上的三个坑（都静默假绿，记在这里以免再踩）：
1. `env.find?` 对**定理**返回的 `value?` 在本版 Lean 里**恒为 `none`**（异步实现，连同一
   文件里刚写的 `theorem` 也一样）⟹ 闭包只走类型，正控静默报 `false`。必须用
   `env.checked.get.find?`。**量纲哨兵**：闭包 size 两三百 = 只走了类型，两万多 = 走了证明项。
2. 目标常量名写错时同样全报 `false` ⟹ 必须对 **target 自身**也打 `target_known=`。
3. 正控可以瞄错：`ConeCover.heights_of_parts` 是 **bottom-free 版**，循环的那条叫
   `heights_of_parts_circular`。「正控不响」的第一诊断必须是「我瞄错了」。

## §10 `ShellFeed` 的前提域非空（几何六条）

正文 §10 节的 `shellFeed_geom_quad_bench`：在**否掉 `ShellFeedLine` 的同一座台架**上，
对每个 `ε` 与该层最低线上的每个 `z₀` 正面造出 `P`，兑现八条合取里与 `d` 无关的六条
（`PosArea` 是被证掉的，见证是 `2×2` 方格而非单点）。剩下两条与 `d` 绑定，不兑现，
也**不**主张链上的 `Âinf` 满足 `ShellFeed`。

## §11 `ShellFeed` 与字段 `shellEnv`：同谓词，量词与载体都不同（第 246 轮）

抬头 §2 / §7 与 `bottom_of_shellFeed_transverse` 的 docstring 里原先写「`ShellFeed` 即消费者
自己的 `shellEnv` 那一格」。**那句读数不对**，本轮按 §57 更正为上面的写法。正确的对应关系是
集成者钉进内核的 `IntegShellFeedEnvOf.lean` 的 `shellFeed_iff_envOf_cover'`：`ShellFeed`
逐字等价于「每个壳底点被某个 `E(𝒮_φ)`-包络的有限正面积 `P` 罩住」，零前提。
与字段 `shellEnv` 逐条对比，**同谓词（都是 `EnvOf`），三处不同**：

| | `shellEnv`（字段） | `ShellFeed` |
|---|---|---|
| 量词 | `∃ ε ∃ i₀ ∀ i ≥ i₀` | `∀ ε ∀ z₀`（带守卫）`∃ P` |
| 载体 | 钉死为 `shellInter (hatOf A kk vl i) (shell … ε) w` | 任意有限 `P ⊆ shell … (ε+1)` |
| `w` | 出现（字段 `hsweepW`） | 不出现 |

⟹ 字段只兑现 `ShellFeed` 所需那族包络性在**单个 `ε`** 上的切片（逐字收据：本文件
`stage_envOf_at_field_eps`，证明体就是 `c.shellEnv` 这一个投影）。

**`∀ ε` 不可降**，且理由不在 `bottom` 内部：`ColleRegion.lean` 解开 `Colle35.lemma35` 的
`∃ ε`（首个失配层）后**同时**喂层 `ε` 与层 `ε+1` 两条，经 `Claim411.shellInf_succ_step` 的
升层步接到 `RegionSteps.lean` ⟹ 外部消费结构一次就要相邻两层。结案见 `blueprint/OPEN.md` #26。

## §12 本轮落地的九条：`ShellFeed` 归约到两条输入（第 246 轮）

正文 §12 节把 `ShellFeed` 的**八条**合取全部归约到**两条**输入（`shellFeed_of_stage_family`），
再把链上那一族「阶」的子集性与有限性用字段兑现掉（`stage_subset` / `stage_finite`），
最后给楔形版的穷尽归约（§13）。归属（§91）：判据「`ShellFeed` 是一条 `EnvOf` 命题」是
集成者的（`IntegShellFeedEnvOf.lean`），本节的增量是**代入 ＋ 把 `PosArea` 从 `EnvOf` 里
证出来**（集成者那份把 `PosArea P` 留在等价式两边）。

⛔ 半平面版的两条（`stage_exh_of_halfPlane_exh` / `shellFeed_of_parts_of_envOf_halfPlaneExh`）
**不落主仓**：它们本身为真，但链上空真，见 §13。
-/

namespace Nivat.LeafAShellBottomParts

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm Nivat.ChainAsm.Aparts

variable {η xper : Config ℤ} {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}

/-- **`hedge` 是 `FaceBlock` 字段的直接推论，零成本。**

`BottomReachMin.bottom_of_reachMin` 的 `hedge` 与 `FaceBlock.edge` 只差合取 `j ≤ r`；
`FanEndpoint.faceBlock_edge_forget_len` 把它忘掉。原文对应 `scratch/b3_colle2.txt:380-392`
（Def 3.1 的面沿 `ℓ` 排列）经 `ChainGeom.lean` 的 `edge` 字段转写，量词一一对应：
`∀ b ∈ S.erase a` ↦ 面以外的窗口点，左析取支是面上的 `vJ`-行，右析取支是抬高至少 1。 -/
theorem hedge_of_parts {nJ vJ : ℤ × ℤ} (F : FaceBlock S nJ vJ) :
    ∀ b ∈ S.erase F.a,
      (∃ j : ℕ, 1 ≤ j ∧ b = F.a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - F.a) :=
  Nivat.FanEndpoint.faceBlock_edge_forget_len F

/-- ⛔ **第 242 轮写错的那一版，保留供对照（PROTOCOL §105「删号留名」）。**

它要求有限的 `P` 含下第 `ε+1` 层最低线的**全部**点。但那条最低线一般是一整条 `vJ`-射线
（`bottom` 第四合取自己就把它写成 `z₀ + k • vJ`，`L ≤ k`），**无限**，所以有限的 `P`
装不下 ⟹ 本定义在一般情形**不可满足**，以它为前提的定理是空真的。
内核见证见 `not_shellFeedLine_quadrant`（第一象限台架，`ε = 0` 一层就够）。

这是本 lane 自己的错：第 242 轮为了消掉 `BottomRoom.window_of_shell_of_line` 的 binder
`hz₀P` 而把「一个点在 `P` 里」加强成「整条线在 `P` 里」，加强的那个量词**原文没有对应物**
（硬规矩 5）。修正版是下面的 `ShellFeed`，把 `z₀` 收成参数、`hz₀P` 原样留着。 -/
def ShellFeedLine (d : Nivat.Colle35.DecompDataZ η) (T : Set (ℤ × ℤ))
    (vJ1 nJ : ℤ × ℤ) (cJ : ℤ) : Prop :=
  ∀ ε : ℕ, ∃ P : Set (ℤ × ℤ),
    P.Finite ∧ P.Nonempty ∧ PosArea P ∧ IsLatticeConvexRegion P ∧
    P ⊆ MaxEnv.shell T vJ1 nJ cJ (ε + 1) ∧
    (∀ z ∈ MaxEnv.shell T vJ1 nJ cJ (ε + 1), dot nJ z = cJ - (ε : ℤ) - 1 → z ∈ P) ∧
    E P = E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ∧
    (∀ n ∈ E P, (face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤ (face P n).encard)

/-- ⭐ **`ShellFeedLine` 在第一象限台架上为假**（PROTOCOL §41：守卫正面兑现，不是空真）。

`T := {z | 0 ≤ z.1 ∧ 0 ≤ z.2}`、`vJ1 := (0,-1)`、`nJ := (0,1)`、`cJ := 0`，取 `ε := 0`。
第 1 层的最低线是 `{(x, -1) | 0 ≤ x}`：每个 `(x,-1)` 都由 `g := (x,0) ∈ T` 沿 `vJ1` 走 `t := 1`
步得到，高度 `-1 = cJ - 0 - 1` 恰在截线上 ⟹ 它在 `shell T vJ1 nJ cJ 1` 里。
这条线无限，而 `ShellFeedLine` 要 `P.Finite` 且含下整条线 ⟹ 矛盾。

⚠ 本条对**任何** `d` 成立（`E P = E ↑𝒮_φ` 那两条合取根本没用到），
所以不是「这个 `𝒮_φ` 不好」，是定义本身写强了。 -/
theorem not_shellFeedLine_quadrant (d : Nivat.Colle35.DecompDataZ η) :
    ¬ ShellFeedLine d {z : ℤ × ℤ | 0 ≤ z.1 ∧ 0 ≤ z.2} (0, -1) (0, 1) 0 := by
  intro h
  obtain ⟨P, hPfin, -, -, -, -, hPline, -, -⟩ := h 0
  have hmem : ∀ x : ℕ, ((x : ℤ), (-1 : ℤ)) ∈ P := by
    intro x
    refine hPline ((x : ℤ), (-1 : ℤ)) ?_ (by simp [dot])
    rw [MaxEnv.shell_eq_reach_inter]
    refine ⟨⟨((x : ℤ), (0 : ℤ)), ⟨by positivity, le_refl 0⟩, 1, ?_⟩, by simp [dot]⟩
    show ((x : ℤ), (-1 : ℤ)) = ((x : ℤ), (0 : ℤ)) + ((1 : ℕ) : ℤ) • ((0 : ℤ), (-1 : ℤ))
    ext <;> simp
  exact absurd hPfin (Set.infinite_of_injective_forall_mem
    (f := fun x : ℕ => ((x : ℤ), (-1 : ℤ)))
    (fun a b hab => by simpa using congrArg Prod.fst hab) hmem).not_finite

/-- **壳侧输入的打包形（第 244 轮修正版）**：对每个 `ε` 与该层最低线上的每个点 `z₀`，
存在一个有限、格凸、正面积、`E(𝒮_φ)`-包络的 `P`，落在第 `ε+1` 层里并**含 `z₀`**。

这就是 `BottomRoom.window_of_shell_of_line` 的六条壳侧 binder
（`hPfin` / `hPne` / `hParea` / `hlcP` / `hPsub` / `hz₀P` ＋ `hEeq` / `henv`）原样打包，
**一条都不加强**。与被否掉的 `ShellFeedLine` 之差就是最后那条：「`z₀ ∈ P`」而不是
「整条最低线 ⊆ `P`」。

原文对应 `scratch/b3_colle2.txt:518`（`Â_i^{(ε)}` 的定义式）＋ `:520`
（「is an $E(\mathcal{S}_{\varphi})$-enveloped set」）。逐量词对应与两处「比原文强」的说明
见本文件抬头 §4：`∀ ε` 是消费者 `ChainDataGeomParts.bottom` 强加的（原文 `:516` 只给 `∃ ε`），
层号 `ε+1` 是 `bottom` 第四合取的层号、不是新量词。

⭐ **前提域已被六边形台架正面兑现全八条**（§52 鉴别性收据，见证在
`tmp/wip/lane-leafa-shell-shellfeed-hex.lean` 的 `shellFeed_hex_bench`：`T := LE2.quad`、
`vJ1 := (0,-1)`、`nJ := (0,1)`、`cJ := 0`，`P := sh518 …` 是随 `z₀` 变大的六边形）。
⟹ **`shellEnv` 死于钉死 `P` 是哪个集合（`shellInter (hatOf …) (shell …) w`，`i`-族），
不死于壳里造不出 `E(𝒮_φ)`-包络集**：同一座台架上包络集要多少有多少，只是不长成
`shellInter` 的样子。这与 `not_shellFeedLine_quadrant` 形成对照——那条死于**量词顺序**
（有限 `P` 装不下无穷线），与载体形状无关。 -/
def ShellFeed (d : Nivat.Colle35.DecompDataZ η) (T : Set (ℤ × ℤ))
    (vJ1 nJ : ℤ × ℤ) (cJ : ℤ) : Prop :=
  ∀ (ε : ℕ) (z₀ : ℤ × ℤ), z₀ ∈ MaxEnv.shell T vJ1 nJ cJ (ε + 1) →
    dot nJ z₀ = cJ - (ε : ℤ) - 1 →
    ∃ P : Set (ℤ × ℤ),
      P.Finite ∧ P.Nonempty ∧ PosArea P ∧ IsLatticeConvexRegion P ∧
      P ⊆ MaxEnv.shell T vJ1 nJ cJ (ε + 1) ∧ z₀ ∈ P ∧
      E P = E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ∧
      (∀ n ∈ E P, (face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤ (face P n).encard)

/-- ⭐⭐⭐ **字段层总装：三合一 ＋ `ShellFeed` ⟹ `ChainDataGeomParts.bottom` 的结论逐字。**

结论与 `ChainPartsFeed.lean` 的 `bottom` 字段逐字符相同（`T := ⋃ i, hatOf c.A c.kk vl i`，
`a := c.F.a`）。除 `htriple` / `hshell` 外的每条前提都是字段或字段的白送推论：

* `hedge` ← `c.F.edge`（经 `hedge_of_parts`）；
* `ha_mem` ← `c.F.a_mem`；`dot_nJ_vJ` ← `c.F.dot_nJ_vJ`；`nJ ≠ 0` ← `c.nJ_prim`；
* `hz₀shell`（`z₀` 落在第 `ε+1` 层里）← `MaxEnv.mem_shell_succ_iff` ＋ `hdz` ＋ `hz₀`，白送。

⚠ 第 242 轮这里写的是「`hz₀P` 不再是 binder」，**那是错的**，已由
`not_shellFeedLine_quadrant` 内核否掉；现在 `hz₀P` 由 `ShellFeed` 原样带着。

⚠ `hrecT` 必须来自**非循环**的 `rec_vJ` 产者：`RecVJFromParts.rec_vJ_of_parts` 吃 `c.bottom`，
喂回这里成环。 -/
theorem bottom_of_triple_of_shellFeed
    (d : Nivat.Colle35.DecompDataZ η)
    (c : ChainDataGeomParts η xper vl p S gen)
    (hS : S = d.toDecompData.Sphi)
    (hrecT : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i)
    (hvJ_eq : c.vJ = dir (-c.nJ))
    (hnegnJ : -c.nJ ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (htriple : ∀ ε : ℕ, ∃ z₀ : ℤ × ℤ, dot c.nJ z₀ = c.cJ - (ε : ℤ) - 1 ∧
      z₀ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1 ∧
      ∀ z ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1,
        dot c.nJ z = c.cJ - (ε : ℤ) - 1 → ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • c.vJ)
    (hshell : ShellFeed d (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot c.nJ z₀ = c.cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • c.vJ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • c.vJ + (b - c.F.a) ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1) ∧
      (∀ z ∈ MaxEnv.shell (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ (ε + 1),
        z ∈ MaxEnv.shell (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ ε ∨
          ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • c.vJ) := by
  subst hS
  intro ε
  obtain ⟨z₀, hdz, hz₀, hline0⟩ := htriple ε
  have hedge := hedge_of_parts c.F
  have hz₀shell : z₀ ∈ MaxEnv.shell (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ (ε + 1) :=
    mem_shell_succ_iff.mpr (Or.inr ⟨hz₀, hdz⟩)
  obtain ⟨P, hPfin, hPne, hParea, hlcP, hPshell, hz₀P, hEeq, henv⟩ :=
    hshell ε z₀ hz₀shell hdz
  have hwin := Nivat.BottomRoom.window_of_shell_of_line d hPfin hPne hParea hlcP hPshell
    hvJ_eq (prim_iff_primitive.mpr c.nJ_prim).ne_zero hEeq hnegnJ henv
    (Finset.mem_coe.mpr c.F.a_mem) c.F.dot_nJ_vJ hedge hz₀P hdz hline0
  exact Nivat.BottomRoom.bottom_of_window hrecT hdz hz₀ hline0 hedge
    (fun b hb _ => hwin b hb)

/-- ⭐⭐ **共线格（`det p vJ1 = 0`）的 `bottom`。**

三合一走 `BottomHz0Collapse.hdz_hz0_hline0_of_cover_collinear`，它的六条前提里五条是字段
（`nJ_prim` / `vJ_prim` / `F.dot_nJ_vJ` / `ahat_halfPlane_L` / `ahat_attained_L`），
第六条 `det p vJ ≠ 0` 由 `BottomHz0Collapse.det_p_vJ_ne` 白送 ⟹ 这一侧只剩 `hcov`。

⟹ 共线格的 `bottom` 欠：`hrecT`（非循环 `rec_vJ`）、`hcov`（剩余类覆盖）、`hshell`、
`hvJ_eq`（定向位）、`hnegnJ`。 -/
theorem bottom_of_cover_shellFeed_collinear
    (d : Nivat.Colle35.DecompDataZ η)
    (c : ChainDataGeomParts η xper vl p S gen)
    (hS : S = d.toDecompData.Sphi)
    (hpar : det p c.vJ1 = 0)
    (hrecT : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i)
    (hvJ_eq : c.vJ = dir (-c.nJ))
    (hnegnJ : -c.nJ ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (hcov : ∀ r : ℤ, ∃ g ∈ ⋃ i, hatOf c.A c.kk vl i,
      (-dot c.nJ c.vJ1) ∣ (dot c.nJ g - r))
    (hshell : ShellFeed d (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot c.nJ z₀ = c.cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • c.vJ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • c.vJ + (b - c.F.a) ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1) ∧
      (∀ z ∈ MaxEnv.shell (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ (ε + 1),
        z ∈ MaxEnv.shell (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ ε ∨
          ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • c.vJ) :=
  bottom_of_triple_of_shellFeed d c hS hrecT hvJ_eq hnegnJ
    (fun ε => Nivat.BottomHz0Collapse.hdz_hz0_hline0_of_cover_collinear c hpar hcov ε) hshell

/-- ⭐⭐ **横截格（`det p vJ1 ≠ 0`）的 `bottom`。**

三合一走 `BottomFree.hdz_hz0_hline0_free`：那里 `hcov` 由 `ConeCover.cover_of_parts` 从字段
白送，代价换成楔形的两条（定向 `hdir` ＋ 支撑界 `hsupp`）。

🔴🔴 **射程订正（集成者第 243 轮，本条比上面那行强得多）**：`hsupp` 不只是「可能为假」——
`EnvRefuteOrient.det_sign_of_supp`（`EnvRefuteOrient.lean:2311`，内核）证明
`hsupp` ⟹ `0 ≤ det vJ1 p * det vJ1 vJ`，逆否 `not_supp_of_det_sign`（`:2335`）：
**两行列式严格异号时 `hsupp` 对任何合法 `nprevJ` 与任何 `V` 都无解**（机制：`0 < ⟪nprevJ,p⟫`
时字段 `rec_p` 的 `+p` 射线把 `⟪nprevJ,·⟫` 推到无穷，见 `not_bddAbove_of_rec`，`:2250`）。
集成者复核的数值实例 `nJ=(0,1)`、`vJ=(1,0)`、`vJ1=(0,-1)`、`p=(-1,1)` 满足本条的**每一条**
前提（`hne1 : det p vJ1 = -1 ≠ 0`、`hdir : ⟪rot vJ1,vJ⟫ = -1 < 0`）而乘积 `= -1 < 0`
⟹ 在**抽象**签名下本条对该半格空真。⭐ **再订正（同轮稍后，你自己的
`LeafAShellWedgeSign.det_sign_of_parts`）：那半格在链上不存在**——符号条件
`0 ≤ det vJ1 p * det vJ1 vJ` 是字段的推论，上述数值有
`det p vJ * det p vJ1 = -1 < 0`，与 `EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg`（`:529`）
冲突 ⟹ 不是链上构型 ⟹ 本条在链上全格可用。
⟹ 且 `hsupp` 已整体免费（`LeafAShellWedgeSign.supp_of_parts`，两格通用），
横截格的三合一改走 `LeafAShellWedgeSign.hdz_hz0_hline0_of_parts_transverse` 即**零 binder**。
同一订正已写进上游 `BottomFree.hdz_hz0_hline0_free` 的射程段。
`hdir` 则**已不是债**：`EnvRefuteOrient.exists_nprevJ`（`:2047`）白送。

⟹ 横截格·**同号**半格（`0 ≤ det vJ1 p * det vJ1 vJ`）的 `bottom` 欠：`hrecT`、`hsupp`（唯一真靶子，
锥判据已派 lane-env-refute）、`hshell`、`hvJ_eq`、`hnegnJ`。
⟹ 横截格·**异号**半格：本条无效，需另找 `hline0` 路线。 -/
theorem bottom_of_wedge_shellFeed_transverse
    (d : Nivat.Colle35.DecompDataZ η)
    (c : ChainDataGeomParts η xper vl p S gen)
    (hS : S = d.toDecompData.Sphi)
    (hne1 : det p c.vJ1 ≠ 0)
    (hrecT : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i)
    (hvJ_eq : c.vJ = dir (-c.nJ))
    (hnegnJ : -c.nJ ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (V : ℤ × ℤ) (hdir : dot (c.vJ1.2, -c.vJ1.1) c.vJ < 0)
    (hsupp : ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i,
      dot (c.vJ1.2, -c.vJ1.1) z ≤ dot (c.vJ1.2, -c.vJ1.1) V)
    (hshell : ShellFeed d (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot c.nJ z₀ = c.cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • c.vJ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • c.vJ + (b - c.F.a) ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1) ∧
      (∀ z ∈ MaxEnv.shell (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ (ε + 1),
        z ∈ MaxEnv.shell (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ ε ∨
          ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • c.vJ) :=
  bottom_of_triple_of_shellFeed d c hS hrecT hvJ_eq hnegnJ
    (fun ε => Nivat.BottomFree.hdz_hz0_hline0_free c hne1 V hdir hsupp ε) hshell

/-! ## §7 第 244 轮：楔形消失后的两条 -/

/-- ⭐⭐ **两格通用：`bottom` 欠 `hcov` ＋ `hrecT` ＋ `hshell` ＋ 两条定向/包络位。**

三合一走 `LeafAShellWedgeSign.hdz_hz0_hline0_of_cover`，楔形整条由
`LeafAShellWedgeSign.exists_wedge_of_parts` 从字段兑现 ⟹ 与
`bottom_of_cover_shellFeed_collinear` 比，`hpar` 这条 binder 也消失，本条在**两格**都能用。 -/
theorem bottom_of_cover_shellFeed_freewedge
    (d : Nivat.Colle35.DecompDataZ η)
    (c : ChainDataGeomParts η xper vl p S gen)
    (hS : S = d.toDecompData.Sphi)
    (hrecT : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i)
    (hvJ_eq : c.vJ = dir (-c.nJ))
    (hnegnJ : -c.nJ ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (hcov : ∀ r : ℤ, ∃ g ∈ ⋃ i, hatOf c.A c.kk vl i,
      (-dot c.nJ c.vJ1) ∣ (dot c.nJ g - r))
    (hshell : ShellFeed d (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot c.nJ z₀ = c.cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • c.vJ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • c.vJ + (b - c.F.a) ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1) ∧
      (∀ z ∈ MaxEnv.shell (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ (ε + 1),
        z ∈ MaxEnv.shell (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ ε ∨
          ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • c.vJ) :=
  bottom_of_triple_of_shellFeed d c hS hrecT hvJ_eq hnegnJ
    (fun ε => Nivat.LeafAShellWedgeSign.hdz_hz0_hline0_of_cover c hcov ε) hshell

/-- ⭐⭐⭐ **横截格（`det p vJ1 ≠ 0`）：`bottom` 只欠 `ShellFeed` ＋ `hvJ_eq` ＋ `hnegnJ`。**

三条 binder 同时消失：

* `hcov` ← `ConeCover.cover_of_parts`（集成者第 243 轮，经
  `LeafAShellWedgeSign.hdz_hz0_hline0_of_parts_transverse`）；
* 楔形（`nprevJ`/`V`/`hdir`/`hsupp`）← `LeafAShellWedgeSign.exists_wedge_of_parts`（本轮）；
* `hrecT` ← `RecVJTransverse.rec_vJ_of_parts_transverse`（集成者第 243 轮，**不经 `c.bottom`**）。

⟹ 横截格里 `bottom` 的唯一实质欠账是 `ShellFeed`，即一条关于 `EnvOf ↑𝒮_φ` 的存在命题
（`IntegShellFeedEnvOf.lean` 的 `shellFeed_iff_envOf_cover'`），与字段 `shellEnv` 同谓词但
量词与载体都不同（§11）；
`hvJ_eq`（第 179 轮红线锁住的定向位）与 `hnegnJ`（调用点由 `nJ = -J` 供）都不是新债。 -/
theorem bottom_of_shellFeed_transverse
    (d : Nivat.Colle35.DecompDataZ η)
    (c : ChainDataGeomParts η xper vl p S gen)
    (hS : S = d.toDecompData.Sphi)
    (hne1 : det p c.vJ1 ≠ 0)
    (hvJ_eq : c.vJ = dir (-c.nJ))
    (hnegnJ : -c.nJ ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (hshell : ShellFeed d (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot c.nJ z₀ = c.cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • c.vJ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • c.vJ + (b - c.F.a) ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1) ∧
      (∀ z ∈ MaxEnv.shell (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ (ε + 1),
        z ∈ MaxEnv.shell (⋃ i, hatOf c.A c.kk vl i) c.vJ1 c.nJ c.cJ ε ∨
          ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • c.vJ) :=
  bottom_of_triple_of_shellFeed d c hS
    (Nivat.RecVJTransverse.rec_vJ_of_parts_transverse c hne1) hvJ_eq hnegnJ
    (fun ε => Nivat.LeafAShellWedgeSign.hdz_hz0_hline0_of_parts_transverse c hne1 ε) hshell

/-! ## §10 第 245 轮：`ShellFeed` 的前提域非空（几何六条**正面**兑现）

集成者第 243 轮的判据：「落新 `Prop` / 新 `def` 时顺手问一句『有没有一个居民同时满足我这些合取』」。
本节在**否掉 `ShellFeedLine` 的同一座台架**（第一象限，`vJ1 = (0,-1)`、`nJ = (0,1)`、`cJ = 0`）
上正面造出 `P`，兑现 `ShellFeed` 八条合取里与 `d` 无关的**六条**：
`P.Finite` / `P.Nonempty` / `PosArea P` / `IsLatticeConvexRegion P` / `P ⊆ shell …` / `z₀ ∈ P`。

⚠ 射程（PROTOCOL §50）：剩下两条（`E P = E ↑𝒮_φ` ＋ 面长不等式）与 `d` 绑定，本节**不**兑现，
也**不**主张链上的 `Âinf` 满足 `ShellFeed`。本节只回答一个问题：**杀死 `ShellFeedLine` 的那个
机制（有限集装不下无穷线）在 `ShellFeed` 上已经不存在。** 见证是 `2×2` 方格，不是单点 ⟹
`PosArea` 是被**证掉**的，不是被转发的（与集成者 `tmp/wip` 的 `shellFeedPt_consistent`
取 `P := {z₀}` 之差就在这里：单点没有正面积）。
-/

/-- 第一象限台架上壳的**闭式**：`shell {0 ≤ x ∧ 0 ≤ y} (0,-1) (0,1) 0 (ε+1)`
恰是右半带 `{0 ≤ z.1 ∧ -(ε)-1 ≤ z.2}`。

⟸ 方向用到 `reachSet` 只朝 `vJ1 = (0,-1)` 一个方向扫：高度为负的点由 `(z.1, 0)` 走
`(-z.2).toNat` 步得到，高度非负的点取 `t := 0`。 -/
theorem mem_shell_quad_bench (ε : ℕ) (z : ℤ × ℤ) :
    z ∈ MaxEnv.shell {w : ℤ × ℤ | 0 ≤ w.1 ∧ 0 ≤ w.2} (0, -1) (0, 1) 0 (ε + 1) ↔
      0 ≤ z.1 ∧ -(ε : ℤ) - 1 ≤ z.2 := by
  rw [MaxEnv.shell_eq_reach_inter]
  constructor
  · rintro ⟨⟨g, hg, t, hz⟩, hh⟩
    have h1 : z.1 = g.1 := by rw [hz]; simp
    simp only [Set.mem_ofPred_eq, dot] at hh
    push_cast at hh
    exact ⟨h1 ▸ hg.1, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · by_cases h : 0 ≤ z.2
      · exact ⟨z, ⟨h1, h⟩, 0, by simp⟩
      · push Not at h
        refine ⟨(z.1, 0), ⟨h1, le_refl 0⟩, (-z.2).toNat, ?_⟩
        have ht : ((-z.2).toNat : ℤ) = -z.2 := Int.toNat_of_nonneg (by linarith)
        ext <;> simp [ht]
    · simp only [Set.mem_ofPred_eq, dot]
      push_cast
      linarith

/-- ⭐ **`ShellFeed` 的几何六条在第一象限台架上可满足**（对**每个** `ε` 与该层最低线上的
**每个** `z₀`）。见证是以 `z₀` 为左下角的 `2×2` 方格 `box z₀ (z₀ + (1,1))`。

与 `not_shellFeedLine_quadrant` 是同一座台架、同一个 `ε`、同一条最低线：
那边有限的 `P` 要装下整条线故为假，这边 `P` 只要含 `z₀` 一点故为真。
**这就是两座台架之间的差**（PROTOCOL §52），也是量词顺序那一处订正的全部内容。 -/
theorem shellFeed_geom_quad_bench (ε : ℕ) (z₀ : ℤ × ℤ)
    (hz₀ : z₀ ∈ MaxEnv.shell {w : ℤ × ℤ | 0 ≤ w.1 ∧ 0 ≤ w.2} (0, -1) (0, 1) 0 (ε + 1))
    (hline : dot ((0 : ℤ), (1 : ℤ)) z₀ = 0 - (ε : ℤ) - 1) :
    ∃ P : Set (ℤ × ℤ),
      P.Finite ∧ P.Nonempty ∧ PosArea P ∧ IsLatticeConvexRegion P ∧
      P ⊆ MaxEnv.shell {w : ℤ × ℤ | 0 ≤ w.1 ∧ 0 ≤ w.2} (0, -1) (0, 1) 0 (ε + 1) ∧
      z₀ ∈ P := by
  have h0 : 0 ≤ z₀.1 := ((mem_shell_quad_bench ε z₀).mp hz₀).1
  have hy : z₀.2 = -(ε : ℤ) - 1 := by simp only [dot] at hline; linarith
  have hz₀mem : z₀ ∈ box z₀ (z₀ + (1, 1)) := ⟨le_refl _, by simp, le_refl _, by simp⟩
  refine ⟨box z₀ (z₀ + (1, 1)), ?_, ⟨z₀, hz₀mem⟩, ?_, isLatticeConvexRegion_box _ _,
    ?_, hz₀mem⟩
  · refine (Set.finite_Icc z₀ (z₀ + (1, 1))).subset ?_
    rintro z ⟨ha, hb, hc, hd⟩
    exact Set.mem_Icc.mpr ⟨⟨ha, hc⟩, ⟨hb, hd⟩⟩
  · refine ⟨z₀, hz₀mem, z₀ + (1, 0), ⟨by simp, by simp, by simp, by simp⟩,
      z₀ + (0, 1), ⟨by simp, by simp, by simp, by simp⟩, ?_⟩
    simp [det]
  · rintro z ⟨ha, -, hc, -⟩
    exact (mem_shell_quad_bench ε z).mpr ⟨le_trans h0 ha, by rw [← hy]; exact hc⟩

/-- 修正是一次**削弱**：被否掉的 `ShellFeedLine` 蕴含改正后的 `ShellFeed`。

（`ShellFeedLine` 在一般情形为假，所以这条不给出 `ShellFeed` 的任何居民；它只把
「第 242 轮那一版确实严格更强」这句话变成内核事实。） -/
theorem shellFeed_of_shellFeedLine {d : Nivat.Colle35.DecompDataZ η} {T : Set (ℤ × ℤ)}
    {vJ1 nJ : ℤ × ℤ} {cJ : ℤ} (h : ShellFeedLine d T vJ1 nJ cJ) :
    ShellFeed d T vJ1 nJ cJ := by
  intro ε z₀ hz₀shell hz₀line
  obtain ⟨P, hfin, hne, harea, hlc, hsub, hPline, hE, henv⟩ := h ε
  exact ⟨P, hfin, hne, harea, hlc, hsub, hPline z₀ hz₀shell hz₀line, hE, henv⟩

/-! ## §12 第 246 轮：`ShellFeed` 的八条合取归约到两条输入

`Q ε i` 读作 `Â_i^{(ε)}`。归约后真正的债只有两条：`hQenv`（每个 `ε` 都要有包络阶）与
`hQexh`（穷尽）。其余六条合取的来源：

| 合取 | 来源 |
|---|---|
| `IsLatticeConvexRegion P` | `EnvOf` 的 `.1.1`（`WeaklyEnveloped` 的第一合取） |
| `E P = E ↑𝒮_φ` | `LE2.Enveloped.E_eq` ＋ `LE2.finite_E_of_finite`（`𝒮_φ` 是 `Finset`） |
| 面长不等式 | `EnvOf` 的 `.1.2 n hn` 的第二分量，量词逐字就跑在 `E P` 上 |
| `PosArea P` | `AhatMono.posArea_of_enveloped` ＋ `AhatMono.posArea_Sphi` |
| `P.Nonempty` | `z₀ ∈ P`，即 `hQexh` |
| `P.Finite` / `P ⊆ shell` | `hQfin` / `hQsub` |

⚠ 射程自限（§50）：本节**不**主张 `hQenv` 或 `hQexh` 在链上成立，也**不**主张字段 `shellEnv`
蕴含 `ShellFeed`（三处差别见 §11）。
-/

/-- ⭐⭐⭐ **`ShellFeed` 归约到两条输入。**

原文：`scratch/b3_colle2.txt:516`（「for an appropriate $\epsilon$ fixed and all $i$
sufficiently large」＝ `hQenv` 的单 `ε` 切片）、`:518`（`Â_i^{(ε)}` 的定义与 `g ∈ Â_i`，
即 `hQexh`）。逐量词：`∀ ε` ↦ 消费者 `bottom` 强加（§11，原文只给 `∃ ε`）；
`∃ i₀ ∀ i ≥ i₀` ↦ `:516` 的「all $i$ sufficiently large」；`∀ z ∈ shell` ↦ `:518` 的
「for each `g`」。 -/
theorem shellFeed_of_stage_family (d : Nivat.Colle35.DecompDataZ η)
    {T : Set (ℤ × ℤ)} {vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    {Q : ℕ → ℕ → Set (ℤ × ℤ)}
    (hQsub : ∀ ε i, Q ε i ⊆ MaxEnv.shell T vJ1 nJ cJ ε)
    (hQfin : ∀ ε i, (Q ε i).Finite)
    (hQenv : ∀ ε : ℕ, ∃ i₀ : ℕ, ∀ i, i₀ ≤ i →
      EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) (Q ε i))
    (hQexh : ∀ ε : ℕ, ∀ z ∈ MaxEnv.shell T vJ1 nJ cJ ε, ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → z ∈ Q ε i) :
    ShellFeed d T vJ1 nJ cJ := by
  intro ε z₀ hz₀ _hline
  obtain ⟨i₀, hi₀⟩ := hQenv (ε + 1)
  obtain ⟨i₁, hi₁⟩ := hQexh (ε + 1) z₀ hz₀
  have henv : EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) (Q (ε + 1) (max i₀ i₁)) :=
    hi₀ _ (le_max_left _ _)
  have hmem : z₀ ∈ Q (ε + 1) (max i₀ i₁) := hi₁ _ (le_max_right _ _)
  have hE : E (Q (ε + 1) (max i₀ i₁)) = E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) :=
    Nivat.LE2.Enveloped.E_eq
      (Nivat.LE2.finite_E_of_finite d.toDecompData.Sphi.finite_toSet) henv
  refine ⟨Q (ε + 1) (max i₀ i₁), hQfin _ _, ⟨z₀, hmem⟩, ?_, henv.1.1, hQsub _ _, hmem, hE, ?_⟩
  · exact Nivat.AhatMono.posArea_of_enveloped d.toDecompData.Sphi.finite_toSet
      (Nivat.AhatMono.posArea_Sphi d.toDecompData) henv
  · intro n hn
    exact (henv.1.2 n hn).2

/-- **链上的阶落在壳里**：`ShellMink.shellInter_subset_right`，与 `w` 无关。 -/
theorem stage_subset (c : ChainDataGeomParts η xper vl p S gen) (ε i : ℕ) :
    ShellMink.shellInter (hatOf c.A c.kk vl i)
        (MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε) c.w ⊆
      MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε :=
  ShellMink.shellInter_subset_right _ _ _

/-- ⭐ **链上的阶是有限的，只用两个字段：`hfin` ＋ `hsweepW`。**

`shellInter A Ainf w = reachSet A w ∩ Ainf`。取 `Ainf := shell (⋃ j, Â_j) vJ1 nJ cJ ε`，
由 `MaxEnv.shell_eq_reach_inter` 它含在截半平面 `{z | cJ - ε ≤ dot nJ z}` 里，于是该交集
含在 `shell (Â_i) w nJ cJ ε` 里；而 `MaxEnv.shell_finite` 只要 `(Â_i).Finite`（字段 `hfin`）
＋ `dot nJ w < 0`（字段 `hsweepW`）。⟹ 与形状收敛无关。 -/
theorem stage_finite (c : ChainDataGeomParts η xper vl p S gen) (ε i : ℕ) :
    (ShellMink.shellInter (hatOf c.A c.kk vl i)
      (MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε) c.w).Finite := by
  refine (MaxEnv.shell_finite (v := c.w) (n := c.nJ) (c := c.cJ) (ε := ε)
    (c.hfin i) c.hsweepW).subset ?_
  rintro z ⟨hreach, hcut⟩
  rw [MaxEnv.shell_eq_reach_inter] at hcut ⊢
  exact ⟨hreach, hcut.2⟩

/-- **逐字收据：字段 `shellEnv` 就是 `hQenv` 在单个 `ε` 上的切片。**

证明体是 `c.shellEnv` 这一个投影 ⟹ 语句与字段逐字同形。§11 那句「字段只兑现一个 `ε`」
以本条为准，不以散文为准。 -/
theorem stage_envOf_at_field_eps (c : ChainDataGeomParts η xper vl p S gen) :
    ∃ ε i₀ : ℕ, 0 < ε ∧ ∀ i, i₀ ≤ i →
      EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf c.A c.kk vl i)
        (MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε) c.w) :=
  c.shellEnv

/-- ⭐⭐⭐ **链上形：`ShellFeed` ⟸ 「每个 `ε` 有包络阶」＋「穷尽」，其余全由字段白送。**

`hQsub` / `hQfin` 已被 `stage_subset` / `stage_finite` 吃掉，所以这条的前提表里**只剩**
`henv` 与 `hexh` 两条，外加把 `↑S` 与 `↑𝒮_φ` 对上的 `hS`。 -/
theorem shellFeed_of_parts_of_envOf_exh (c : ChainDataGeomParts η xper vl p S gen)
    (d : Nivat.Colle35.DecompDataZ η)
    (hS : (↑S : Set (ℤ × ℤ)) = (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (henv : ∀ ε : ℕ, ∃ i₀ : ℕ, ∀ i, i₀ ≤ i →
      EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf c.A c.kk vl i)
        (MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε) c.w))
    (hexh : ∀ ε : ℕ, ∀ z ∈ MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε,
      ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → z ∈ ShellMink.shellInter (hatOf c.A c.kk vl i)
        (MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε) c.w) :
    ShellFeed d (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ := by
  refine shellFeed_of_stage_family d
    (Q := fun ε i => ShellMink.shellInter (hatOf c.A c.kk vl i)
      (MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε) c.w)
    (stage_subset c) (stage_finite c) ?_ hexh
  intro ε
  obtain ⟨i₀, hi₀⟩ := henv ε
  exact ⟨i₀, fun i hi => hS ▸ hi₀ i hi⟩

/-! ## §13 穷尽那一半：半平面形为假，楔形才是正确形状

⛔ **半平面形已被本 lane 内核否掉，故不落主仓。** `tmp/wip/lane-leafa-shell-exhhp-refute.lean`
的 `not_exhHP_of_parts`（0 sorry、公理全白、无额外前提、无格分情形）逐字结论是

    ¬ (∀ q, cJ ≤ ⟪nJ,q⟫ → ∃ i₀, ∀ i ≥ i₀, q ∈ hatOf A kk vl i)

理由一句话：该假设 ＋ 字段 `hhp` 合起来说 `⋃_i Â_i` **就是**半平面 `halfPlaneGE nJ cJ`，
而字段 `ahat_halfPlane_L` 还有第二堵墙 `cL ≤ ⟪n_L,·⟫`（`n_L := det p vJ • dir p`），且
`det nJ n_L = det p vJ · ⟪nJ,p⟫ ≠ 0`（两个因子分别由 `EnvRefuteOrient.abs_det_p_vJ_of_parts`
与字段 `dot_nJ_p` 给）⟹ 两堵不平行的墙夹出**楔形**，不是半平面。

⟹ 正确形状是下面的楔形版 `hexhW`：穷尽假设**两堵墙都要**。而 `z` 侧那堵墙由
`lwall_of_shell` 白送（关键一步是 `⟪n_L,v_{J+1}⟫ = det p vJ · det p vJ1 ≥ 0`，
即 `EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg`，lane-env-refute 的现货；⚠ 那条不经
`bottom`，但吃 `ahat_nonempty` / `rec_p` / `hswept` / `dot_nJ_p` / `ahat_halfPlane_L`
五个字段，本节继承的就是这五条）⟹ 与半平面版相比只多出**一条**符号 binder
`hwL : ⟪n_L,w⟫ ≤ 0`（回退方向不穿出 `ℓ` 墙）。

⚠ 本节**不**主张 `hwL` 在链上成立，也**不**主张它为假：它压在第 179 轮定向冻结上
（`det p w` 的符号），归 `w` 的持有者裁。
-/

/-- **`⟪n_L, v_{J+1}⟫ = det p v_J · det p v_{J+1} ≥ 0`**，链上白送。 -/
theorem dot_nL_vJ1_nonneg (c : ChainDataGeomParts η xper vl p S gen) :
    0 ≤ dot (det p c.vJ • ((-p.2), p.1)) c.vJ1 := by
  have h := Nivat.EnvRefuteOrient.det_p_vJ_mul_det_p_vJ1_nonneg c
  have he : dot (det p c.vJ • ((-p.2), p.1)) c.vJ1 = det p c.vJ * det p c.vJ1 := by
    simp only [dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [he]
  exact h

/-- ⭐ **`ℓ` 墙从 `⋃ Â_i` 自动延到整个壳。**

壳的点是 `g + t • v_{J+1}`（`g ∈ ⋃ Â_i`，`t : ℕ`），字段 `ahat_halfPlane_L` 管住 `g`，
`dot_nL_vJ1_nonneg` 管住那 `t` 步。⟹ 原先要的「`z` 留在 `ℓ` 墙内侧」那条 binder 不必要。 -/
theorem lwall_of_shell (c : ChainDataGeomParts η xper vl p S gen) (ε : ℕ) (z : ℤ × ℤ)
    (hz : z ∈ MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε) :
    c.cL ≤ dot (det p c.vJ • ((-p.2), p.1)) z := by
  rw [MaxEnv.shell_eq_reach_inter] at hz
  obtain ⟨⟨g, hg, t, rfl⟩, -⟩ := hz
  have hgL := c.ahat_halfPlane_L g hg
  have hstep : (0 : ℤ) ≤ (t : ℤ) * dot (det p c.vJ • ((-p.2), p.1)) c.vJ1 :=
    mul_nonneg (Int.natCast_nonneg t) (dot_nL_vJ1_nonneg c)
  rw [dot_add, Nivat.ColleReg.dot_zsmul_right]
  linarith

/-- ⭐⭐⭐ **楔形穷尽 ＋ 一条符号 binder ⟹ `hQexh`。**

与被否掉的半平面形（§13）的差：穷尽假设现在**两堵墙都要**，而 `z` 侧那堵墙由
`lwall_of_shell` 白送，所以净多一条 `hwL`。回退步数仍然 ≤ `ε`：壳的截线是
`cJ - ε ≤ ⟪nJ,z⟫`，字段 `hsweepW` 给 `⟪nJ,w⟫ ≤ -1`，于是 `q := z - ε • w` 已在 `cJ` 之上，
且 `z = q + ε • w` 把 `q` 沿 `w` 走 `ε` 步就回到 `z`——不需要任何「充分大的 `t`」。 -/
theorem stage_exh_of_wedge_exh (c : ChainDataGeomParts η xper vl p S gen)
    (hwL : dot (det p c.vJ • ((-p.2), p.1)) c.w ≤ 0)
    (hexhW : ∀ q : ℤ × ℤ, c.cJ ≤ dot c.nJ q →
      c.cL ≤ dot (det p c.vJ • ((-p.2), p.1)) q →
      ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → q ∈ hatOf c.A c.kk vl i)
    (ε : ℕ) (z : ℤ × ℤ)
    (hz : z ∈ MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → z ∈ ShellMink.shellInter (hatOf c.A c.kk vl i)
      (MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε) c.w := by
  have hzL := lwall_of_shell c ε z hz
  have hcut : c.cJ - (ε : ℤ) ≤ dot c.nJ z := by
    rw [MaxEnv.shell_eq_reach_inter] at hz
    exact hz.2
  have hw1 : dot c.nJ c.w ≤ -1 := by have := c.hsweepW; omega
  have hε : (0 : ℤ) ≤ (ε : ℤ) := Int.natCast_nonneg ε
  have hqJ : c.cJ ≤ dot c.nJ (z - (ε : ℤ) • c.w) := by
    have hmul : (ε : ℤ) * dot c.nJ c.w ≤ -(ε : ℤ) := by
      have := mul_le_mul_of_nonneg_left hw1 hε
      simpa using this
    rw [dot_sub, Nivat.ColleReg.dot_zsmul_right]
    linarith
  have hqL : c.cL ≤ dot (det p c.vJ • ((-p.2), p.1)) (z - (ε : ℤ) • c.w) := by
    have hmul : (ε : ℤ) * dot (det p c.vJ • ((-p.2), p.1)) c.w ≤ 0 := by
      have := mul_le_mul_of_nonneg_left hwL hε
      simpa using this
    rw [dot_sub, Nivat.ColleReg.dot_zsmul_right]
    linarith
  obtain ⟨i₀, hi₀⟩ := hexhW _ hqJ hqL
  refine ⟨i₀, fun i hi => ⟨⟨z - (ε : ℤ) • c.w, hi₀ i hi, ε, ?_⟩, hz⟩⟩
  exact (sub_add_cancel z ((ε : ℤ) • c.w)).symm

/-- ⭐⭐⭐ **链上形（楔形版）：`ShellFeed` ⟸ 「每个 `ε` 有包络阶」＋「楔形被穷尽」＋ `hwL`。**

这是 §12＋§13 的终点：`bottom` 在横截格里的唯一实质欠账 `ShellFeed`（§11）被压成
`henv` ＋ `hexhW` ＋ `hwL` 三条，其余一切由 `ChainDataGeomParts` 的字段兑现。 -/
theorem shellFeed_of_parts_of_envOf_wedgeExh (c : ChainDataGeomParts η xper vl p S gen)
    (d : Nivat.Colle35.DecompDataZ η)
    (hS : (↑S : Set (ℤ × ℤ)) = (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (henv : ∀ ε : ℕ, ∃ i₀ : ℕ, ∀ i, i₀ ≤ i →
      EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf c.A c.kk vl i)
        (MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε) c.w))
    (hwL : dot (det p c.vJ • ((-p.2), p.1)) c.w ≤ 0)
    (hexhW : ∀ q : ℤ × ℤ, c.cJ ≤ dot c.nJ q →
      c.cL ≤ dot (det p c.vJ • ((-p.2), p.1)) q →
      ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → q ∈ hatOf c.A c.kk vl i) :
    ShellFeed d (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ :=
  shellFeed_of_parts_of_envOf_exh c d hS henv
    (fun ε z hz => stage_exh_of_wedge_exh c hwL hexhW ε z hz)

end Nivat.LeafAShellBottomParts

#print axioms Nivat.LeafAShellBottomParts.hedge_of_parts
#print axioms Nivat.LeafAShellBottomParts.not_shellFeedLine_quadrant
#print axioms Nivat.LeafAShellBottomParts.bottom_of_triple_of_shellFeed
#print axioms Nivat.LeafAShellBottomParts.bottom_of_cover_shellFeed_collinear
#print axioms Nivat.LeafAShellBottomParts.bottom_of_wedge_shellFeed_transverse
#print axioms Nivat.LeafAShellBottomParts.bottom_of_cover_shellFeed_freewedge
#print axioms Nivat.LeafAShellBottomParts.bottom_of_shellFeed_transverse
#print axioms Nivat.LeafAShellBottomParts.mem_shell_quad_bench
#print axioms Nivat.LeafAShellBottomParts.shellFeed_geom_quad_bench
#print axioms Nivat.LeafAShellBottomParts.shellFeed_of_shellFeedLine
#print axioms Nivat.LeafAShellBottomParts.shellFeed_of_stage_family
#print axioms Nivat.LeafAShellBottomParts.stage_subset
#print axioms Nivat.LeafAShellBottomParts.stage_finite
#print axioms Nivat.LeafAShellBottomParts.stage_envOf_at_field_eps
#print axioms Nivat.LeafAShellBottomParts.shellFeed_of_parts_of_envOf_exh
#print axioms Nivat.LeafAShellBottomParts.dot_nL_vJ1_nonneg
#print axioms Nivat.LeafAShellBottomParts.lwall_of_shell
#print axioms Nivat.LeafAShellBottomParts.stage_exh_of_wedge_exh
#print axioms Nivat.LeafAShellBottomParts.shellFeed_of_parts_of_envOf_wedgeExh
