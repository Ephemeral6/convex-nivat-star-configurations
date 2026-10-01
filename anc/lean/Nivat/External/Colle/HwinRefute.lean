/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.FillCoverGuarded
import Nivat.External.Colle.Oct8Bench
import Nivat.External.Colle.TowerHbaseCut

/-!
# `hwin` 为假：带守卫的形状**也**不成立（§52 鉴别性收据）

lane-leafa-gen，2026-09-24。

## 结论

`FillCoverGuarded.fillCover_of_window`（`FillCoverGuarded.lean`，`theorem fillCover_of_window`）
的残项 binder `hwin` 在 oct8 台架上**为假**，而该台架上它的**其余全部 binder 与全部守卫都成立**：

* `hfin`：`Nivat.LaneTowerOct8.finite_hat`；
* `hsweepW : dot nJ w < 0`：`Nivat.LaneTowerOct8.fan_data` 的第八个合取分量；
* `hwin` 自己带的 `Enveloped` 守卫：`Nivat.LaneTowerOct8.enveloped_shellInter`，
  **对每个 `i` 都成立**（`ε = 1`）。⟹ 下面的否定**不是空真**（§41）。

⚠ **辖域（先读这一段再引用）**：本文件否掉的是 `fillCover_of_window` 的**假设** `hwin`，
即「把 `fillCover` 归约到『窗口整块落在同一个 `collarY i ε` 里』」这条**生产路线**；
它**不**否掉 `fillCover` 这条义务本身（`fillCover_of_window` 的**结论**），
也不否掉 `ChainExhaustInter` 的 `fillCover` 字段。与 §9 `not_hedge_at_a'` 同一辖域级别，
与 §7 `not_hR_of_top` 不同级别（那条否的是我自己的一条残项形状）。

⚠ **辖域再收一层：本文件谈的是「`shellInter`，未取交的那版壳」。**
lane-tower-hbase 第 213 轮的 `cut_eq`（内核）算出交集版
`Cut i = oct8 1 (2K-1) (2K) (8K-1) (6K) (8K-1) (2K) 0`——第七个常数从 `4K-1` **收回 `2K`**。
反例点 `(-16,-7)` 有 `-z.2 = 7 > 6 = 2·K_1`，**不在 `Cut 1` 里**。
⟹ 集成者第 215 轮已裁定交集路线升为主线，本文件对**那个新对象一个字都没说**（§54）。
引用本文件时必须带上这句辖域，否则就是超范围引用。

✅ **2026-09-25：上面那行常数我自己对读过了（§55），并登记它对常数订正的免疫面。**
主仓 `theorem cut_eq`（`Nivat/External/Colle/TowerHbaseCut.lean:136`）逐字是
`cutX i = oct8 1 (2 * KK i - 1) (2 * KK i) (8 * KK i - 1) (6 * KK i) (8 * KK i - 1) (2 * KK i) 0`
——八个常数与上一段**逐位相同**，不是转述。
且上一段的排除只读**第七个**常数（`-z.2 = 7 > 6 = 2 · K_1`）⟹ 另外七个常数（含 `c₁`）
日后若被订正，`(-16,-7) ∉ Cut 1` 这句**不受影响**；只有 `c₇` 被改才需要重算。

⚠ **`c₃ = c₇ = 2·KK i` 的同值巧合（lane-tower-hbase 2026-09-25 提，本行是我的答复）**：
数值确实同值，但两者界的是**不同的半平面**——按 `oct8` 的定义（`Oct8Bench.lean` `def oct8`）
第三条是 `z.2 ≤ c₃`、第七条是 `-z.2 ≤ c₇`。见证点 `(-16,-7)` 的排除读的是 `-z.2 = 7 > 6`，
即**第七条**；它的 `z.2 = -7 ≤ 6` 满足第三条，故 `c₃` 在这句里不承重。
⟹ 上面「只有 `c₇` 被改才需要重算」不变。

⭐ **lane-tower-hbase 后来把这一格升为「不可判」（§119），我不同意，理由在他们自己的两条定理里**：
同值不等于同一个量。`Nivat.LaneTowerOct8.shellInter_eq` 的第三、七位是
`2 * KK i` 与 **`4 * KK i - 1`**；`Nivat.LaneTowerHbaseCut.cut_eq` 的是 `2 * KK i` 与 **`2 * KK i`**。
⟹ 取交这一步**只改了第七位**（`4K-1 → 2K`），第三位是从壳原样继承的；
两个槽位的来源独立，在 `cutX` 上的相等是**数值巧合**（§51）。
所以「改 `c₃` 不用重算」是可判的，判定为**绿**。

⚠ **`hp_per` 空洞不波及本文件。**  集成者亲读了 `fillCover_of_window` 的完整 binder 表：
`hfin` / `hsweepW` / `F : FaceBlock S nJ vJ` / `gen_eq` / `hwin`——**没有 `p`，没有 `xper`，
没有 `hp_per`**。所以「oct8 上不存在满足 `hp_per ∧ hdet ∧ hpvJ` 的 `p`」这件事
（它把走 `ChainDataGeom.ofPartsExhaustsInter` 的那条反证判成空真）对本文件**完全不适用**：
本文件否的那个 conditional 的假设里根本没有周期侧的量词。⛔ 不要把这两份 oct8 结果合并。

⚠ **诚实的残余边界。**  `fillCover_of_window` 仍是一条**真的 conditional**；本文件否的是它
在 oct8 赋值下的**假设**。

> ⚠ **2026-09-25 订正（§14，原话留着）**：下面这句**参照系写错了**，已由后一段取代。
>
> > 这条路在**真链**上死掉，当且仅当真几何也带有本文件孤立出来的那个特征：
> > `collarY i ε` 与 `Â_i` **共用** `u₆` 面常数、**只在** `u₇` 上分开。

**正确的参照系是「目标 vs 整个底集的并」，不是「目标 vs `Â_i`」。**  按本文件 §2 的
`not_window_at_max` / `mem_of_hwin_at_support`，`hwin` 在某个 `(n, i₀, i)` 上破，要的是两条：

1. `gen` 在 `S` 上**不是** `n`-极大（`∃ b ∈ S, dot n gen < dot n b`）——这条给出越界的那一步
   `z + (b - gen)`；
2. `collarY i ε` 的某个 `n`-支撑点**不在整个底集 `Â_i ∪ collarY i₀ ε` 里**——注意守卫的两支
   是**并**，所以要比的是 `collarY i ε` 在 `n` 上的上确界与**并集**在 `n` 上的上确界，
   `Â_i` 一侧单独比对不足以定性。

原写法把 (2) 记成了「`collarY i ε` 与 `Â_i` 在哪面分开」，漏掉 `collarY i₀ ε` 那一支
⟹ 会把无害的面误判成致命的。台架上两种都有（§6 的数值实例，`i₀ = 0`、`i = 1`、`ε = 1`）：

* `u₁`：`collarY i ε` 与 `Â_i` **差 1**（`1` 对 `0`），但与**并集齐平** ⟹ **无害**，
  按原写法会被误记成一条独立的致命面；
* `u₇`：`collarY i ε` 的 `4K_i - 1` 高过并集的 `4K_{i₀} - 1`（`i₀ < i` ⟹ `K_{i₀} < K_i`）
  ⟹ **致命**，这才是 `(-16,-7)` 逃出去的那一面。

⟹ 「`hwin` 不是白拿」已成定论；⟹ 「`hwin` 在真链上必假」**尚未**成立。两者别合并。
⛔ 内核结论不受本条订正影响：`not_Hwin_oct8` / `not_Hstep_oct8` 钉的是具体点，
订正动的只是「什么样的真几何会重演这件事」这句**推广条件**的口径。

## 指向义务：本文件每条反面声明**否的是谁**（team-lead 2026-09-25 裁决）

红线那句「每条定义 / `Prop` / 字段 docstring 指到 `b3_colle2.txt:NNN`」对本文件**问错了问题**：
反例台架上的命题不是我们主张的数学，是「某个候选签名为假」的见证，向原文要行号要不出东西。
裁决（`FROZEN.md` 口径，措辞是「**指向义务从原文转到被否签名**」，不是「豁免」——
本文件仍然必须讲理由，只是理由的落点换了）：

> 每条反面声明的 docstring 必须写明：**否的是哪个具名声明的哪一版签名、是否带全部前提。**

⟹ 本文件的 `b3_colle2.txt` 锚点数 **= 0 是合规的**，不是欠账。被否签名的落点如下，
四条反面声明逐条在自己的 docstring 里重复一遍（这里是索引，不是替代）：

| 反面声明 | 否的具名声明 | 否的是它的哪个 binder |
|---|---|---|
| `not_Hwin_oct8` | `Nivat.FillCoverGuarded.fillCover_of_window`（`FillCoverGuarded.lean:271`） | 第五个显式 binder `hwin`（`:274-282`） |
| `not_Hwin_at_faceBlock` | 同上 | 同上，`gen := F.a'` 那一支 |
| `not_Hstep_oct8` | `Nivat.LaneFillCover.subset_genClosure_of_covector`（`FillCoverReduce.lean:113`） | 第三个显式 binder `hstep`（`:117`） |
| `not_Hstep_at_faceBlock` | 同上 | 同上，`gen := F.a'` 那一支 |

⚠ **本义务只落在「反面声明」上，别扩散。**  本文件另有六条 `∉` 引理
（`zc_not_mem_AB` / `zc_not_mem_YB0` / `p_not_mem_AB` / `p_not_mem_YB0` / `p_not_mem_YB1`，
以及 `b_mem_Sphi` 的对偶用法）——它们是**台架事实**（某个具体点在不在某个具体 `oct8` 里），
不是「某签名为假」的主张，没有被否对象可指。把指向义务摊到它们头上只会制造假锚点。

## 台架门槛（§90 / 常设纪律 1）

`Nivat.LaneTowerOct8.Sphi` 是 12 点 8 边（`coe_Sphi` 化到 `oct8 0 1 2 4 3 3 1 0`）
⟹ 四组对径边法向 ⟹ **`m ≥ 4` 满足**。引用本反证前该问的第一个问题（台架够不够宽）在此答完。


## 为什么这条比 §7 更贵

§7（`lane-leafa-gen-hwinseam.lean` 的 `not_hR_of_top`）证的是「无守卫的 `∀ z` 形为假」，
team-lead 第 213 轮据此在 OPEN 里登记的补救是「残项必须带 `z ∉ Â_i ∧ z ∉ collarY i₀` 守卫」。
本文件说明：**那个守卫救不了**。`hwin` 自己就已经带着那两条排除（它的第一个析取支
恰好是 `z ∈ Â_i ∪ collarY i₀ ε`），而它仍然为假。

⟹ 登记 1 的「补救」条目要改状态：加守卫不是修法。

## 机理（不依赖台架的那一半）

`not_window_at_max`：设 `z` 在某方向 `n` 上是 `Y` 的支撑点（`dot n`-极大），
而 `gen` 在 `S` 上**不是** `n`-极大（存在 `b ∈ S` 有 `dot n gen < dot n b`），
则 `z + (b - gen) ∉ Y`。三行，无台架。

由此 `hwin` 蕴含一条**可检验的必要条件**（`mem_of_hwin_at_support`）：
`collarY i ε` 在每个这样的方向上的支撑点都必须落进 `Â_i ∪ collarY i₀ ε`。
`gen = F.a'` 只在 `-n_J` 这**一个**方向上是 `S` 的极大点，别的七个方向上都不是，
所以这条必要条件要 `collarY i ε` 的七个面的支撑点全部被守卫吃掉。

台架上被吃掉的只有一部分：`collarY i ε` 与 `Â_i` **共用** `u₆ = (-1,-1)` 那面的常数
（两边都是 `8K_i - 1`），而 `collarY i ε` 在 `u₇ = (0,-1)` 那面比 `Â_i` 宽
（`4K_i - 1` 对 `2K_i`）。于是 `u₆`-面上、`u₇` 方向超出 `Â_i` 的那条缝里的点
既在 `collarY i ε` 的支撑面上、又不在 `Â_i` 里；`i₀ < i` 时它也不在 `collarY i₀ ε` 里
（`u₅ = (-1,0)` 那面 `6K_{i₀} < 6K_i`）。`(-16,-7)`（`i = 1`、`i₀ = 0`、`ε = 1`）就是一个。

数值旁证（`tmp/scratch-leafa-gen/hfit2.py`，**不是**证据，只是定位用）：`i₀ = 0`、`i = 1`
时守卫剩下 30 个点，其中 15 个（`gen = (0,0)`）／20 个（`gen = (0,1)`）破；
把 `gen` 在 `[-40,20)²` 上扫一遍，**没有任何一个 `gen` 能让残项为真**。
本文件只把其中一个点写进内核，并只对 `-3 < gen.1 + gen.2` 的 `gen` 陈述
（这一条就覆盖了全部合法锚点，见 `faceBlock_a'_gen`）。

⚠ `i₀ = i` 时 `hwin` 的守卫集为空（`z ∈ collarY i ε` 与 `z ∉ collarY i₀ ε` 直接打架），
整条 binder 恒真——这与 `FillCoverGuarded.Ahat_subset_collarY` 的注记一致。
所以反例必须取 `i₀ < i`，本文件取 `i₀ = 0 < 1 = i`。

## 锚点：不需要知道 `F` 长什么样

`faceBlock_a'_gen`：**任何** `F : FaceBlock 𝒮_φ n_J v_J`（`v_J` 任意）都满足
`-3 < F.a'.1 + F.a'.2`。只用 `F.a'_mem` 与 `F.lex'`，不用 `edge` / `edge'` / `dot_nJ_vJ`，
所以与 `v_J` 取 `dir n_J` 还是 `-dir n_J` 无关（§97：`F.a` / `F.a'` / 底侧 `a` 三个同名物）。
⟹ `not_Hwin_at_faceBlock` 对该台架上的每一个 `FaceBlock` 都成立。

⚠ **「与定向无关」≠「与台架无关」**（hlev 第 215 轮实扫要求写死）：Lean 里绑的是
`FaceBlock Nivat.LaneTowerOct8.Sphi Nivat.LaneTowerOct8.nJx vJ`——**台架的** `Sphi` / `nJx`，
**不是**任意 `S` / `n_J`。⛔ 不许读成「任何面块的 `hwin` 都假」。

> ⚠ **2026-09-25 订正（§14，原话留着）**：下面这条「未复核」已由我自己的内核收据结清，
> 且它对 `v_J` 的**两个方向给出相反的答案**——原话只问了「存不存在」，问法本身太粗。
>
> > ⚠ **本台架上是否真存在 `FaceBlock 𝒮_φ n_Jx v_J`，我没有证**（需要 `LatticeConvex 𝒮_φ`）。
> > lane-tower-hbase 2026-09-24 报他在 `tmp/wip/lane-tower-hbase-faceblock.lean` 里钉死了一个，
> > **我未复核**（§55）。

**空真与否取决于 `v_J` 取哪个方向**（我自己跑的 `#check` / `#print axioms`，
`tmp/wip/lane-leafa-gen-faceblock-audit.lean`，EXIT=0，三条全是
`[propext, Classical.choice, Quot.sound]`）：

⚠ **该收据已在绿树上重取一次**（第 217 轮）。首次取证时 `Oct8Bench.lean` 的源内容与其
olean 所据的内容**不一致**（`.trace` 记 `d2958a2dc30bdb82`、现算 `d0648e586a058b07`），
而源 mtime 反而**比 olean 早** ⟹ mtime 判据在那一格给的是假阴，我据此把收据自降为待验。
全量 build（`BUILD_RC=0`）之后按 `tmp/scratch-leafa-gen/contenthash.py` 复核：
`SCANNED 396 / OK 396 / DRIFT 0 / NO_OLEAN 0`，四个哨兵全 PASS ⟹ 396 个 olean 都是用
磁盘上这一版源编的；在此前提下原样重跑，EXIT=0、三条公理仍全干净。
⟹ 下面两条引用的是**重取后**的读数，不是首次那份。

⚠ **第三次取数（同轮，晚些时候）——上一段那次我自己降过级，这里结清**（§103：换判据/
换读数一律**追加新收据**，不回改旧的；上面那段一个字没动）。上一段取数之后我在本文件
落了一次注释层改动，而当时 `Oct8Bench`（本文件 131 模块闭包里的成员）正处于漂移
（`trace记=d0648e586a058b07` / `现算=fc2b0252239b17bf`，lane-tower-hbase 的等长注释替换），
于是我把那次「改完之后的 `check1.sh` EXIT=0」自记为**未定**——对队友用什么尺，对自己
用同一把（§55）。现在那一格结清，四个读数**同一树态**：

* `python tmp/scratch-leafa-gen/contenthash.py`（03:04:23）：`TREE_MOVING 0`（树静）、
  `TREE_STATE ad34d803d6f415d3`、`SCANNED 399 / COMPARED 399 / OK 399 / DRIFT 0 /`
  `NO_TRACE 0 / BAD_TRACE 0 / NO_OLEAN 0`，四哨兵全 PASS，`EXIT 0`；
* `python tmp/scratch-leafa-gen/contentclosure.py Nivat/External/Colle/HwinRefute.lean`：
  `闭包=131`、`CLOSURE_STATE 842deb261ae81f8a`、缺 olean / 内容漂移 / 无 trace 全 `0`，
  扰动式哨兵 `3/3 + 3/3` PASS，`EXIT 0`；
* `bash scripts/check1.sh Nivat/External/Colle/HwinRefute.lean` → **EXIT=0**，本文件
  20 条声明公理全干净（其中 `dot_add_sub_anchor` / `not_window_at_max` 更紧，
  只用 `[propext, Quot.sound]`）；
* 跑完 `check1.sh` 之后再取一次 `TREE_STATE` 仍是 `ad34d803d6f415d3`
  ⟹ 这四个读数**具备合成资格**（同一树态才准合成，不同就重采、不靠加注释补救）。

⚠ 仍然只是内容级一致 + 单文件 `check1.sh`。**「这条链绿了」只有集成者的全量 `lake build`
说了算**（硬规矩 2），本段不越过那一条。

⚠ **第四次取数（第 219 轮 03:54–03:58）——上一段那张已被别人的编辑作废，这里重取**
（§103：追加，不回改；上面三段一个字没动）。作废的原因不是判据出错，而是**绿有保质期**：
`AhatMono.lean`（本文件 131 模块闭包里的成员）在 03:31:43 被改过，上一段引的
`CLOSURE_STATE 842deb261ae81f8a` 就此成为历史树态。集成者第 219 轮的全量 build
重编了它，现在重取：

* `contenthash.py`（03:54:49，左端）：`TREE_MOVING 0`、`SCAN_WINDOW 0`、
  `TREE_STATE 59a0ca9b66bfe8ea`、`TOOL_SHA b698b58378da`；
* `contentclosure.py Nivat/External/Colle/HwinRefute.lean`：`闭包=131`、
  **`CLOSURE_STATE 60425767272eecc7`**（≠ 上一段的 `842deb…`，正是 `AhatMono` 换了版本）、
  缺 olean / 内容漂移 / 无 trace 全 `0`，扰动式哨兵 `3/3 + 3/3` PASS，`EXIT 0`；
* `bash scripts/check1.sh Nivat/External/Colle/HwinRefute.lean` → **EXIT=0**，公理全干净；
* `contenthash.py`（03:58:23，右端）：`TREE_STATE 59a0ca9b66bfe8ea`、`TOOL_SHA` 同左端。

🔴 **这次的取法本身是订正过的**：`check1.sh` 整个跑在两次 `TREE_STATE` **之间**。
理由是同轮实测——03:32:14 量到的「树静」是真的，03:34:35 一条 `lake` 就起来了，
10 秒后 `AhatMono.olean` / `L1Residual.olean` 在盘上双双消失（lake 原地重写）。
⟹ 「树静」是**向后**窗口，它给的通行证管不了下一秒；**只有把被认证的那个贵动作
括在两张同指纹读数之间，合成才成立**。（把仪器自己括起来没用：一次扫描只有 0.5 秒。）

⚠ 与上段同：仍只是内容级一致 + 单文件 `check1.sh`，不越过硬规矩 2。
⚠ 本段写入后，本文件自身相对其 olean 即进入内容漂移，等集成者重编——这不是新问题，
是**任何** docstring 落地的必然状态，写在这里免得下一个人把它读成「树脏了」。

⚠ **写入后复核的读数（03:59–04:00）不干净，照记不藏**：那次 `check1.sh` 仍 `EXIT=0`，
但同刻 `contentclosure.py` 报 `内容漂移 = 1 ['Nivat.External.Colle.ChainPartsFeed']`
（别的 lane 在 03:59 改了该源）⟹ **那张 `EXIT=0` 按内容判据不可信，不算收据**。
上面 03:54–03:58 那四条不受影响：它们取自 `CLOSURE_STATE 60425767272eecc7` 那个树态，
闭包漂移为 0，且 `check1.sh` 跑在两端之间。

🔴 **这里分出两个不同的钥匙，别混用**（同轮实测逼出来的）：
* 全树 `TREE_STATE` 是**全树**结论的钥匙。拿它当单文件收据的钥匙**太强**：
  03:59:27→03:59:38 两端 `TREE_STATE` 不等（`f26f6df68c00ac9d` / `f425a61ce9ae748d`），
  而变的是 `PartsToGeom`——**根本不在本文件的 131 闭包里**。判据太严会把好收据判死，
  和判据太松一样没有鉴别力。
* 单文件收据的钥匙是 `CLOSURE_STATE`。
* 且**指纹相等 ≠ 读数干净**：上面那对 `0f6fdc6abe15d086` 两端相等（同态），
  可闭包漂移是 1（不可信）。**相等答「两端是不是同一态」，漂移答「该态能不能用」。**

⭐ **第五次取数（第 219 轮 04:12:36–04:12:49）——这一次越过了硬规矩 2，前四段一个字没动**
（§103）。本段认证的是抬头「指向义务」一节 ＋ 四条反面声明 docstring 那次落地
（源写入 04:08:18，内容哈希 `e0b6e114605c0e9c`）：

* 集成者的**全量** `lake build` 在 04:09:27 为本模块写下 `.olean` ＋ `.trace`，
  `.trace` 记的源内容哈希**逐字就是** `e0b6e114605c0e9c`（我现算复核，一致）
  ⟹ 编的是这一版源，**不是** lake 跳过未重放（盲区 8 的那一格在这里被排除的方式是
  「产物被写了」，不是「rc=0」）；该次 build 在 `tmp/gate219f.log:6353` 报 `[lake_build] rc=0`。
* 括号（两端逐字相同）：`TREE_STATE 7ac41ea0e1ce8a9d`、`TOOL_SHA 5b910b77f10c`、
  `TREE_MOVING 0`、`SCAN_WINDOW 0`、全树 `SCANNED 400 / OK 400 / DRIFT 0 / NO_OLEAN 0`；
* 括号内：`contentclosure.py` 闭包 `131`、**`CLOSURE_STATE 16a6908bf5b24db7`**、
  缺 olean / 内容漂移 / 无 trace 全 `0`，扰动哨兵 `3/3 + 3/3` PASS；
  `bash scripts/check1.sh …` **EXIT=0**，20 条声明公理全干净
  （`dot_add_sub_anchor` / `not_window_at_max` 仍是更紧的 `[propext, Quot.sound]`）。

⚠ **自限两条，别读过头**：(i) 我拿到的是「本模块在全量 build 里编过且 rc=0」，
**不是**「`GATE_RC=0`」——同一次 gate 报 `GATE_RC=1`（`check_axioms` rc=1，链上两条 `sorry`），
那是别的账，不归本文件；(ii) 本段本身是**后写的追加**，写完这一刻本文件相对其 olean
重新进入内容漂移，等下一次 build——这是任何 docstring 落地的必然状态，不是树脏了。

* `v_J := Nivat.LaneTowerOct8.vJx`：`Nivat.LaneTowerOct8.faceBlock_oct8 :`
  `Nonempty (FaceBlock Sphi nJx vJx)` ⟹ `not_Hwin_at_faceBlock` 在这个方向上
  **非空真**，确实否掉了一个活的面块；
* `v_J := Nivat.LaneTowerOct8.vJ1x`：`Nivat.LaneTowerOct8.no_faceBlock_at_vJ1x :`
  `¬Nonempty (FaceBlock Sphi nJx vJ1x)` ⟹ 在这个方向上**是空真**（`FaceBlock` 的第十一个字段
  `dot_nJ_vJ : dot n v = 0`（`ANormal.lean:616`）要求 `dot nJx vJ1x = 0`，而它 `= -1`）。
  ⛔ 不许拿 `vJ1x` 那一侧当收据。

`LatticeConvex 𝒮_φ` 这个前提也已兑现：`Nivat.LaneTowerOct8.latticeConvex_Sphi_oct8`
（同一次 `check1.sh`，公理干净）⟹ 原话括号里那句「需要 `LatticeConvex 𝒮_φ`」不再是欠账。

⚠ **§97 一名多物**：`vJ1x` 在本文件里出现在**两个位置**——它恒是 `Hwin` 的 `vJ1` 实参
（`collarY` 的参数，与面块方向无关），此外它还可以被当作上面那个 `v_J` 的取值。
第二种用法是空的，第一种不是。读到 `vJ1x` 先分清是哪一个。

因此**载重的那条仍是 `not_Hwin_oct8`（对 `gen` 全称，不依赖 `FaceBlock` 存在性）**；
`not_Hwin_at_faceBlock` 是它的包装，现在在 `vJx` 方向上有了活体。

## `Hwin` 与真 binder 同一：内核检查

`hwin_is_the_binder` 把 `Hwin` 喂给 `fillCover_of_window`，编译通过即证明
`Hwin` 与该 binder 的类型逐字定义相等（项目里 `type_of%` / `rfl` 护栏的同一用法）。
它用 `F : FaceBlock S nJ vJ` 作**假设**，不构造，所以不需要任何台架。
-/

set_option autoImplicit false

namespace Nivat.LaneLeafAGenHwinRefute

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35

/-! ## §1. `hwin` binder 的名字，与它确实是那个 binder 的内核检查 -/

/-- `FillCoverGuarded.fillCover_of_window` 的 `hwin` binder，用 `collarY` 写出来
（`collarY` 是 `def`，与 binder 里展开的 `shellInter …` 定义相等；下面 `hwin_is_the_binder`
是内核确认）。 -/
def Hwin (S : Finset (ℤ × ℤ)) (Ahat : ℕ → Set (ℤ × ℤ)) (vJ1 nJ w : ℤ × ℤ) (cJ : ℤ)
    (gen : ℤ × ℤ) : Prop :=
  ∀ ε i₀ : ℕ, 0 < ε →
    (∀ i, i₀ ≤ i → Enveloped (↑S : Set (ℤ × ℤ))
      (Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i ε)) →
    ∀ i, i₀ ≤ i →
    ∀ z ∈ Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i ε,
      z ∈ Ahat i ∪ Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i₀ ε ∨
      ∀ b ∈ S, z + (b - gen) ∈ Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i ε

/-- **内核检查：`Hwin` 就是 `fillCover_of_window` 的 `hwin`。**  本定理只把 `Hwin` 原样喂进去，
类型不逐字相等就编译不过。`F` 是假设不是构造，所以与台架无关。 -/
theorem hwin_is_the_binder {S : Finset (ℤ × ℤ)} {Ahat : ℕ → Set (ℤ × ℤ)}
    {vJ1 nJ vJ w : ℤ × ℤ} {cJ : ℤ}
    (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0) (F : FaceBlock S nJ vJ)
    (h : Hwin S Ahat vJ1 nJ w cJ F.a') :
    ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w)) →
      ∀ i, i₀ ≤ i →
      ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
        {z | Colle37.GenClosure S (Ahat i ∪
          ShellMink.shellInter (Ahat i₀)
            (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) z} :=
  Nivat.FillCoverGuarded.fillCover_of_window hfin hsweepW F rfl h

/-! ## §2. 机理：支撑点上的一般障碍（无台架） -/

/-- `dot` 在 `z + (b - g)` 上拆开。 -/
theorem dot_add_sub_anchor (n z b g : ℤ × ℤ) :
    dot n (z + (b - g)) = dot n z + dot n b - dot n g := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **一般障碍（无台架、无 `ε`、无 `i`）**：`z` 是 `Y` 在方向 `n` 上的支撑点，
而 `gen` 在该方向上被某个 `b` 严格超过，则窗口的 `b` 那一片掉出 `Y`。 -/
theorem not_window_at_max {n : ℤ × ℤ} {Y : Set (ℤ × ℤ)} {z gen b : ℤ × ℤ}
    (hmax : ∀ y ∈ Y, dot n y ≤ dot n z) (hlt : dot n gen < dot n b) :
    z + (b - gen) ∉ Y := by
  intro hmem
  have h := hmax _ hmem
  rw [dot_add_sub_anchor] at h
  omega

/-- **`hwin` 的可检验必要条件**：`collarY i ε` 在任一「`gen` 不极大」的方向上的支撑点，
都必须落进守卫 `Â_i ∪ collarY i₀ ε`。这是下面台架反例的一般形状；反过来，
要救 `hwin` 就得证明这条必要条件，而 `gen = F.a'` 只在 `-n_J` 一个方向上极大。 -/
theorem mem_of_hwin_at_support {S : Finset (ℤ × ℤ)} {Ahat : ℕ → Set (ℤ × ℤ)}
    {vJ1 nJ w gen : ℤ × ℤ} {cJ : ℤ} (h : Hwin S Ahat vJ1 nJ w cJ gen)
    {ε i₀ i : ℕ} (hε : 0 < ε)
    (hguard : ∀ j, i₀ ≤ j → Enveloped (↑S : Set (ℤ × ℤ))
      (Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ j ε))
    (hi : i₀ ≤ i) {n z b : ℤ × ℤ}
    (hz : z ∈ Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i ε)
    (hmax : ∀ y ∈ Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i ε, dot n y ≤ dot n z)
    (hb : b ∈ S) (hlt : dot n gen < dot n b) :
    z ∈ Ahat i ∪ Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i₀ ε := by
  rcases h ε i₀ hε hguard i hi z hz with hx | hw
  · exact hx
  · exact absurd (hw b hb) (not_window_at_max hmax hlt)

/-! ## §3. 台架：oct8 上的显式反例

⚠⚠ **2026-09-25 改判（第 231 轮，lane-leafa-gen 自核）：本节与 §6 的反例是「链外」的。**
反例点族 `zc i = (-6·KK i + 2, -2·KK i - 1)` 恰好是 **`shellSubStrip` 字段在本台架上失效的那个点**
（`Oct8Bench.lean` 的 `escape_not_mem_halfStrip` / `not_shellSubStrip_body` /
`binders_hold_but_not_shellSubStrip` 早已落地；且该文件 §10 还给出另一条独立理由：
对含 `hp_per` 的新表，本台架空真）。
⇒ 这组 oct8 数据 **当不了 `ChainDataGeomParts` 的居民**，
所以本节与 §6 否掉的是 **不带 `shellSubStrip` 守卫的抽象蕴涵**，
⛔ **不是**「链上的 `hwin` 为假」。
带守卫的那一版（`HwinI₀Strip`，参见 `tmp/wip/lane-leafa-gen-stripguard.lean`）
在本台架上**空真** ⇒ 本节对它一个字都没说。 -/

/-- 台架的 `Â`（`abbrev`，可约，好让 `collarY` 与 `shellInter_eq` 对得上）。 -/
abbrev AB : ℕ → Set (ℤ × ℤ) :=
  hatOf Nivat.LaneTowerOct8.Ax Nivat.LaneTowerOct8.kkx Nivat.LaneTowerOct8.vlx

/-- 台架上的第 `i` 层领，`c_J = 0`、`ε = 1`。 -/
abbrev YB (i : ℕ) : Set (ℤ × ℤ) :=
  Nivat.FillCoverGuarded.collarY AB Nivat.LaneTowerOct8.vJ1x Nivat.LaneTowerOct8.nJx
    Nivat.LaneTowerOct8.wfan 0 i 1

theorem KK_zero : Nivat.LaneTowerOct8.KK 0 = 2 := by
  simp [Nivat.LaneTowerOct8.KK]

theorem KK_one : Nivat.LaneTowerOct8.KK 1 = 3 := by
  simp [Nivat.LaneTowerOct8.KK]

theorem YB_eq (i : ℕ) :
    YB i = Nivat.LaneTowerOct8.oct8 1 (2 * Nivat.LaneTowerOct8.KK i - 1)
      (2 * Nivat.LaneTowerOct8.KK i) (8 * Nivat.LaneTowerOct8.KK i - 1)
      (6 * Nivat.LaneTowerOct8.KK i) (8 * Nivat.LaneTowerOct8.KK i - 1)
      (4 * Nivat.LaneTowerOct8.KK i - 1) 0 :=
  Nivat.LaneTowerOct8.shellInter_eq i

theorem mem_YB_iff (i : ℕ) {z : ℤ × ℤ} :
    z ∈ YB i ↔ z.1 ≤ 1 ∧ z.1 + z.2 ≤ 2 * Nivat.LaneTowerOct8.KK i - 1 ∧
      z.2 ≤ 2 * Nivat.LaneTowerOct8.KK i ∧
      -z.1 + z.2 ≤ 8 * Nivat.LaneTowerOct8.KK i - 1 ∧
      -z.1 ≤ 6 * Nivat.LaneTowerOct8.KK i ∧
      -z.1 - z.2 ≤ 8 * Nivat.LaneTowerOct8.KK i - 1 ∧
      -z.2 ≤ 4 * Nivat.LaneTowerOct8.KK i - 1 ∧ z.1 - z.2 ≤ 0 := by
  rw [YB_eq i]
  exact Nivat.LaneTowerOct8.mem_oct8

theorem mem_AB_iff (i : ℕ) {z : ℤ × ℤ} :
    z ∈ AB i ↔ z.1 ≤ 0 ∧ z.1 + z.2 ≤ 2 * Nivat.LaneTowerOct8.KK i - 1 ∧
      z.2 ≤ 2 * Nivat.LaneTowerOct8.KK i ∧
      -z.1 + z.2 ≤ 8 * Nivat.LaneTowerOct8.KK i - 1 ∧
      -z.1 ≤ 6 * Nivat.LaneTowerOct8.KK i ∧
      -z.1 - z.2 ≤ 8 * Nivat.LaneTowerOct8.KK i - 1 ∧
      -z.2 ≤ 2 * Nivat.LaneTowerOct8.KK i ∧ z.1 - z.2 ≤ 0 := by
  show z ∈ hatOf Nivat.LaneTowerOct8.Ax Nivat.LaneTowerOct8.kkx Nivat.LaneTowerOct8.vlx i ↔ _
  rw [Nivat.LaneTowerOct8.hatOf_eq i]
  exact Nivat.LaneTowerOct8.mem_oct8

/-- 反例点：`collarY … 1 1` 的 `u₆ = (-1,-1)` 支撑面上的一点。 -/
theorem zc_mem_YB : ((-16 : ℤ), (-7 : ℤ)) ∈ YB 1 := by
  rw [mem_YB_iff, KK_one]
  norm_num

theorem zc_not_mem_AB : ((-16 : ℤ), (-7 : ℤ)) ∉ AB 1 := by
  rw [mem_AB_iff, KK_one]
  norm_num

theorem zc_not_mem_YB0 : ((-16 : ℤ), (-7 : ℤ)) ∉ YB 0 := by
  rw [mem_YB_iff, KK_zero]
  norm_num

/-- `(-3,0)` 是 `𝒮_φ` 的 `u₆`-极大点之一（`-x-y = 3`）。 -/
theorem b_mem_Sphi : ((-3 : ℤ), (0 : ℤ)) ∈ Nivat.LaneTowerOct8.Sphi := by
  decide

/-- **本轮的鉴别性收据：`hwin` 在 oct8 上为假**，对每个 `-3 < gen.1 + gen.2` 的锚点。

守卫由 `Nivat.LaneTowerOct8.enveloped_shellInter` 当场兑现，所以本条**非空真**。

**否的是谁**（台架文件的指向义务，见抬头「指向义务」一节）：

* **具名声明**：`Nivat.FillCoverGuarded.fillCover_of_window`（`FillCoverGuarded.lean:271`）。
* **哪一版签名**：隐式 `{S gen nJ vJ vJ1 w cJ Ahat}`（该文件 `variable`，`FillCoverGuarded.lean:129`）
  ＋ 五条显式 binder `hfin`（`:272`）/ `hsweepW : dot nJ w < 0`（`:272`）/
  `F : FaceBlock S nJ vJ`（`:273`）/ `gen_eq : gen = F.a'`（`:273`）/ `hwin`（`:274-282`）。
  否掉的是**第五条** `hwin`，其余四条不动。
* **是否带全部前提：带，而且是内核确认的。**  `hwin_is_the_binder`（本文件 §1）把 `Hwin`
  原样喂进**这一版**签名并编译通过 ⟹ `Hwin` 与 `:274-282` 那个 binder 类型逐字定义相等；
  本条否的不是「我转写出来的一个形状」。台架上其余四条**正面兑现**（§41，不是空真）：
  `hfin` = `Nivat.LaneTowerOct8.finite_hat`（`Oct8Bench.lean:788`）；
  `hsweepW` = `Nivat.LaneTowerOct8.fan_data`（`Oct8Bench.lean:541`）的第八个合取分量；
  `hwin` 自带的 `Enveloped` 守卫 = `Nivat.LaneTowerOct8.enveloped_shellInter`（`Oct8Bench.lean:761`），
  下面证明体里 `hguard` 就是它，对每个 `j` 都真；
  `gen_eq` 在本条里被抽成对 `gen` 的**全称**（不是被绕过）——`faceBlock_a'_gen` 说明任何
  `F.a'` 都落在 `-3 < gen.1 + gen.2` 里 ⟹ 本条**不是**靠「`gen_eq` 在台架上无解」取胜。
* ⛔ **否的不是**：`fillCover_of_window` 本身（它是条真 conditional）、它的**结论**、
  `ChainDataGeom.ofPartsInter` / `ofPartsExhaustsInter` 的 `fillCover` 字段。
  也**不是**交集版壳 `cutX`（见抬头第二段辖域）。 -/
theorem not_Hwin_oct8 {gen : ℤ × ℤ} (hgen : -3 < gen.1 + gen.2) :
    ¬ Hwin Nivat.LaneTowerOct8.Sphi AB Nivat.LaneTowerOct8.vJ1x Nivat.LaneTowerOct8.nJx
        Nivat.LaneTowerOct8.wfan 0 gen := by
  intro h
  have hguard : ∀ j, (0 : ℕ) ≤ j → Enveloped (↑Nivat.LaneTowerOct8.Sphi : Set (ℤ × ℤ)) (YB j) :=
    fun j _ => Nivat.LaneTowerOct8.enveloped_shellInter j
  rcases h 1 0 Nat.one_pos hguard 1 (Nat.zero_le 1) _ zc_mem_YB with hx | hw
  · rcases hx with h1 | h2
    · exact zc_not_mem_AB h1
    · exact zc_not_mem_YB0 h2
  · have hbad := hw ((-3 : ℤ), (0 : ℤ)) b_mem_Sphi
    rw [mem_YB_iff, KK_one] at hbad
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hbad
    omega

/-! ## §4. 锚点：任何 `FaceBlock` 的 `a'` 都落在被否掉的范围里 -/

/-- **`F.a'` 的第一坐标是 `0`**，只用 `lex'` 与 `a'_mem`：`-n_Jx = (1,0)`，`lex'` 说
`𝒮_φ` 的其余点在该方向上不超过 `a'`，而 `(0,0) ∈ 𝒮_φ`。与 `v_J` 无关。 -/
theorem faceBlock_a'_fst_nonneg {vJ : ℤ × ℤ}
    (F : FaceBlock Nivat.LaneTowerOct8.Sphi Nivat.LaneTowerOct8.nJx vJ) : 0 ≤ F.a'.1 := by
  by_cases he : F.a' = ((0 : ℤ), (0 : ℤ))
  · rw [he]
  · have hb : ((0 : ℤ), (0 : ℤ)) ∈ Nivat.LaneTowerOct8.Sphi.erase F.a' :=
      Finset.mem_erase.mpr ⟨fun hh => he hh.symm, by decide⟩
    rcases F.lex' _ hb with h | ⟨h, -⟩ <;>
      · simp only [Nivat.LaneTowerOct8.nJx, dot, Prod.fst_neg, Prod.snd_neg] at h
        omega

/-- **任何 `FaceBlock` 的锚点都在 `not_Hwin_oct8` 的适用范围内。** -/
theorem faceBlock_a'_gen {vJ : ℤ × ℤ}
    (F : FaceBlock Nivat.LaneTowerOct8.Sphi Nivat.LaneTowerOct8.nJx vJ) :
    -3 < F.a'.1 + F.a'.2 := by
  have h0 := faceBlock_a'_fst_nonneg F
  have hmem := F.a'_mem
  simp only [Nivat.LaneTowerOct8.Sphi, Finset.mem_insert, Finset.mem_singleton,
    Prod.ext_iff] at hmem
  omega

/-- **合起来：台架上每一个 `FaceBlock` 的 `hwin` 都为假。**

⚠ 空真与否随 `vJ` 而变（见抬头的 2026-09-25 订正）：`vJ := Nivat.LaneTowerOct8.vJx` 那一侧
有活体（`Nivat.LaneTowerOct8.faceBlock_oct8`），`vJ := Nivat.LaneTowerOct8.vJ1x` 那一侧空
（`Nivat.LaneTowerOct8.no_faceBlock_at_vJ1x`）。载重的仍是 `not_Hwin_oct8`。

**否的是谁**：与 `not_Hwin_oct8` 同一个具名声明、同一版签名、同一条 binder
（`Nivat.FillCoverGuarded.fillCover_of_window`，`FillCoverGuarded.lean:271`，第五条 `hwin`，
`:274-282`），差别只在 `gen` 的取法：本条把 `gen` 钉在 `F.a'` 上，正是 `gen_eq`（`:273`）
要求的那个值 ⟹ 它否的是**该签名唯一允许的 `gen`**，不是一个随手取的点。
**前提带全**，理由逐条同 `not_Hwin_oct8`；但 ⚠ 「非空真」这一格在本条上是**分方向的**：
只有 `vJx` 那一侧有面块活体，`vJ1x` 那一侧本条为空真，⛔ 不许拿 `vJ1x` 那一侧当收据。 -/
theorem not_Hwin_at_faceBlock {vJ : ℤ × ℤ}
    (F : FaceBlock Nivat.LaneTowerOct8.Sphi Nivat.LaneTowerOct8.nJx vJ) :
    ¬ Hwin Nivat.LaneTowerOct8.Sphi AB Nivat.LaneTowerOct8.vJ1x Nivat.LaneTowerOct8.nJx
        Nivat.LaneTowerOct8.wfan 0 F.a' :=
  not_Hwin_oct8 (faceBlock_a'_gen F)

/-! ## §5. 更贵的一条：`fillCover_of_window` **内部实际要的**那条局部步也为假

`fillCover_of_window` 的证明体并不直接用 `hwin`，它把 `hwin` 削弱成 `hstep`
（`FillCoverGuarded.lean` 的 `have hstep`），再喂给
`LaneFillCover.subset_genClosure_of_covector`（`FillCoverReduce.lean`，
`theorem subset_genClosure_of_covector`）的同名 binder：

  `∀ z ∈ Y, z ∈ X ∨ ∀ b ∈ S.erase gen, z + (b - gen) ∈ X ∪ Y`

这条比 `hwin` **弱**三处：窗口只跑 `S.erase gen`；落点允许在 `X ∪ Y` 而不必在 `Y`；
`z ∈ X` 那一支同样是守卫。所以「`hwin` 为假」本身还留了一个口子——也许弱版为真。
本节堵上：在同一个点、同一个 `b` 上，**弱版也为假**。

理由是三条包含都栽在**同一条**约束 `u₆ = (-1,-1)` 上：`collarY i ε`、`Â_i`、
`collarY i₀ ε` 三个集合在 `u₆` 方向的常数分别是 `8K_i - 1`、`8K_i - 1`、`8K_{i₀} - 1`，
前两者**相等**，第三个更小。`(-19 - gen.1, -7 - gen.2)` 的 `u₆`-值是 `26 + gen.1 + gen.2`，
在 `-3 < gen.1 + gen.2` 下 `> 23 = 8·3 - 1`，一次超出三个集合。

⚠ 辖域：否掉的是 `subset_genClosure_of_covector` 在
`X := Â_i ∪ collarY i₀ ε`、`Y := collarY i ε`、`gen := F.a'` 这一**组**实参上的 binder，
**不是** `subset_genClosure_of_covector` 本身（它是条真定理），也**不是** `fillCover` 义务。
换 `X` / `Y` / `gen` 的别的归约不受本节影响。 -/

/-- `LaneFillCover.subset_genClosure_of_covector` 的 `hstep` binder。 -/
def Hstep (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) (X Y : Set (ℤ × ℤ)) : Prop :=
  ∀ z ∈ Y, z ∈ X ∨ ∀ b ∈ S.erase gen, z + (b - gen) ∈ X ∪ Y

/-- **内核检查：`Hstep` 就是那个 binder。** -/
theorem hstep_is_the_binder {S : Finset (ℤ × ℤ)} {gen n' : ℤ × ℤ} {X Y : Set (ℤ × ℤ)} {C : ℤ}
    (hbdd : ∀ z ∈ Y, dot n' z ≤ C)
    (hgen : ∀ b ∈ S.erase gen, dot n' gen < dot n' b)
    (h : Hstep S gen X Y) :
    Y ⊆ genClosure S gen X :=
  Nivat.LaneFillCover.subset_genClosure_of_covector hbdd hgen h

/-- `(-19 - gen.1, -7 - gen.2)` 不在 `Â_1` 里。 -/
theorem p_not_mem_AB {gen : ℤ × ℤ} (hgen : -3 < gen.1 + gen.2) :
    ((-16 : ℤ), (-7 : ℤ)) + (((-3 : ℤ), (0 : ℤ)) - gen) ∉ AB 1 := by
  rw [mem_AB_iff, KK_one]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  omega

/-- …也不在 `collarY … 0 1` 里。 -/
theorem p_not_mem_YB0 {gen : ℤ × ℤ} (hgen : -3 < gen.1 + gen.2) :
    ((-16 : ℤ), (-7 : ℤ)) + (((-3 : ℤ), (0 : ℤ)) - gen) ∉ YB 0 := by
  rw [mem_YB_iff, KK_zero]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  omega

/-- …也不在 `collarY … 1 1` 里。 -/
theorem p_not_mem_YB1 {gen : ℤ × ℤ} (hgen : -3 < gen.1 + gen.2) :
    ((-16 : ℤ), (-7 : ℤ)) + (((-3 : ℤ), (0 : ℤ)) - gen) ∉ YB 1 := by
  rw [mem_YB_iff, KK_one]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  omega

/-- **本文件最贵的一条：弱版局部步在 oct8 上也为假。**

**否的是谁**（台架文件的指向义务，见抬头「指向义务」一节）：

* **具名声明**：`Nivat.LaneFillCover.subset_genClosure_of_covector`（`FillCoverReduce.lean:113`）。
* **哪一版签名**：隐式 `{S : Finset (ℤ × ℤ)} {gen n' : ℤ × ℤ} {X Y : Set (ℤ × ℤ)} {C : ℤ}`
  （`:114`）＋ 三条显式 binder `hbdd : ∀ z ∈ Y, dot n' z ≤ C`（`:115`）/
  `hgen : ∀ b ∈ S.erase gen, dot n' gen < dot n' b`（`:116`）/ `hstep`（`:117`）。
  否掉的是**第三条** `hstep`，且只在这一**组**实参上：
  `S := Nivat.LaneTowerOct8.Sphi`、`X := AB 1 ∪ YB 0`、`Y := YB 1`、`gen` 全称于
  `-3 < gen.1 + gen.2`。
* **是否带全部前提：分两半答，不含糊。**
  (i) `hstep` 这一条**逐字带全**：`hstep_is_the_binder`（本文件 §5）把 `Hstep` 原样喂进
  这一版签名并编译通过 ⟹ 类型逐字定义相等。它比 `hwin` 弱三处（窗口只跑 `S.erase gen`、
  落点允许 `X ∪ Y`、`z ∈ X` 那支是守卫），本条堵的正是这三处放宽后剩下的口子。
  (ii) ⚠ **另两条 `hbdd` / `hgen` 我没有在内核里兑现**（§51：记「我没算」，不记「不需要」）。
  论证层面两条都可满足——`Y = YB 1` 是有界 `oct8`（`mem_YB_iff`）⟹ `hbdd` 平凡；
  `hgen` 恰是 `Nivat.LaneFillCover.exists_lex_covector`（`FillCoverReduce.lean:142`）
  在 `gen = F.a'` 上的结论——但**这两句是论证不是见证**。
  ⟹ 本条的辖域：「`hstep` 在这组实参上为假」。它**不**主张「这条归约路线在台架上整体可用」，
  也**不**需要那个主张：`hstep` 为假与 `hbdd` / `hgen` 真假无关，三条是并列的假设。
* **非空真（§41）**：`Hstep` 的头是 `∀ z ∈ Y, …`，而 `Y = YB 1` 有活体
  （`zc_mem_YB : (-16,-7) ∈ YB 1`）⟹ 被否的那个命题不是对空集的全称。 -/
theorem not_Hstep_oct8 {gen : ℤ × ℤ} (hgen : -3 < gen.1 + gen.2) :
    ¬ Hstep Nivat.LaneTowerOct8.Sphi gen (AB 1 ∪ YB 0) (YB 1) := by
  intro h
  have hbne : ((-3 : ℤ), (0 : ℤ)) ≠ gen := by
    intro hh
    rw [← hh] at hgen
    norm_num at hgen
  rcases h _ zc_mem_YB with hx | hw
  · rcases hx with h1 | h2
    · exact zc_not_mem_AB h1
    · exact zc_not_mem_YB0 h2
  · rcases hw ((-3 : ℤ), (0 : ℤ)) (Finset.mem_erase.mpr ⟨hbne, b_mem_Sphi⟩) with hx | hy
    · rcases hx with h1 | h2
      · exact p_not_mem_AB hgen h1
      · exact p_not_mem_YB0 hgen h2
    · exact p_not_mem_YB1 hgen hy

/-- 合起来：台架上每一个 `FaceBlock` 的弱版局部步也为假。

**否的是谁**：与 `not_Hstep_oct8` 同一个具名声明、同一版签名、同一条 binder
（`Nivat.LaneFillCover.subset_genClosure_of_covector`，`FillCoverReduce.lean:113`，
第三条 `hstep`，`:117`），实参组也相同，差别只在 `gen` 钉死为 `F.a'`——那正是
`exists_lex_covector`（`FillCoverReduce.lean:142`）给 `hgen` 的那个锚点。
前提与自限逐条同 `not_Hstep_oct8`（含 `hbdd` / `hgen` 未在内核里兑现这一格）；
⚠ 「非空真」同样分方向：面块活体只在 `vJ := Nivat.LaneTowerOct8.vJx` 那一侧
（`faceBlock_oct8`），`vJ1x` 那一侧空（`no_faceBlock_at_vJ1x`）。 -/
theorem not_Hstep_at_faceBlock {vJ : ℤ × ℤ}
    (F : FaceBlock Nivat.LaneTowerOct8.Sphi Nivat.LaneTowerOct8.nJx vJ) :
    ¬ Hstep Nivat.LaneTowerOct8.Sphi F.a' (AB 1 ∪ YB 0) (YB 1) :=
  not_Hstep_oct8 (faceBlock_a'_gen F)

/-! ## §6. `I₀` 救不了 `hwin`：障碍对 `i` 一致（lane-leafa-gen，2026-09-25）

**为什么要问这一问。** `FillCoverGuarded.fillCover_of_window` 的残项 `hwin` 带守卫 `i₀ ≤ i`，
而它要填的字段 `ChainDataGeomParts.fillCover`（`ChainPartsFeed.lean:271-279`）守卫是
`max i₀ I₀ ≤ i`，`I₀` 是**生产者自选的字段**。⟹ 残项被写强了一档（`FillCoverGuarded.lean` §9
自报），于是有一个显而易见的救法：**把 `I₀` 交还给残项**，让 `hwin` 只在 `i ≥ max i₀ I₀` 处
成立就行 —— `§3` 的反例点落在 `i = 1`，看上去正是「`i` 太小」。
`FillCoverGuarded.fillCover_field_of_window_at_I₀` 已经把这条弱残项接通到字段。

**答案：救不了。** 本节把 §3 的见证点 `(-16,-7)` 推广成一族随 `i` 平移的见证点
`zc i := (-6·KK i + 2, -(2·KK i + 1))`（`KK i = i + 2`，`Oct8Bench.lean:491`），
在 `i = 1` 处恰好回到 `(-16,-7)`（`zc_one_eq`，内核）。这族点对**每个** `i` 都：

* 落在 `collarY … i 1` 的 `u₆ = (-1,-1)` 支撑面上（`-x-y = 8·KK i - 1`，取到上确界）；
* 因 `u₇`（`-y = 2·KK i + 1 > 2·KK i`）落在 `Â_i` 外；
* 因 `u₆`（`8·KK i - 1 > 8·KK i₀ - 1`，只要 `i₀ < i`）落在 `collarY … i₀ 1` 外。

⟹ 给定任何 `I₀`，取 `i₀ := 0`、`i := max I₀ 1`，守卫 `max 0 I₀ = I₀ ≤ i` 满足而 `0 < i`，
见证点照样越界。`not_HwinI₀_oct8`。

⚠ **辖域与 §3 逐字相同**（见抬头那两段）：同一个对象 `collarY`（＝字段里那个
`shellInter (Â_i) (MaxEnv.shell (⋃ Â) vJ1 nJ cJ ε) w`）、同一座 oct8 台架、同样**不**谈
`TowerHbaseCut.cutX`（那里 `c₇` 收回 `2·KK i`，本族见证点的 `-y = 2·KK i + 1` 同样不在其中）。
本节**只**把 §3 的 `i = 1` 提升为对一切 `i` 一致，不扩大任何别的射程。

⛔ 与 §3 一样，否的是 `fillCover_of_window` / `fillCover_field_of_window_at_I₀` 的**假设**
`hwin`，**不是** `fillCover` 这条义务本身，也不是字段。 -/

/-- `hwin` 的**弱守卫**版本，即 `FillCoverGuarded.fillCover_field_of_window_at_I₀` 的残项：
守卫从 `i₀ ≤ i` 放松到 `max i₀ I₀ ≤ i`。 -/
def HwinI₀ (S : Finset (ℤ × ℤ)) (Ahat : ℕ → Set (ℤ × ℤ)) (vJ1 nJ w : ℤ × ℤ) (cJ : ℤ)
    (gen : ℤ × ℤ) (I₀ : ℕ) : Prop :=
  ∀ ε i₀ : ℕ, 0 < ε →
    (∀ i, i₀ ≤ i → Enveloped (↑S : Set (ℤ × ℤ))
      (Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i ε)) →
    ∀ i, max i₀ I₀ ≤ i →
    ∀ z ∈ Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i ε,
      z ∈ Ahat i ∪ Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i₀ ε ∨
      ∀ b ∈ S, z + (b - gen) ∈ Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i ε

/-- **内核检查：`HwinI₀` 就是 `fillCover_field_of_window_at_I₀` 的残项。**  与
`hwin_is_the_binder`（§1）同一招：原样喂进去，类型不逐字相等就编译不过。 -/
theorem hwinI₀_is_the_binder {S : Finset (ℤ × ℤ)} {Ahat : ℕ → Set (ℤ × ℤ)}
    {vJ1 nJ vJ w : ℤ × ℤ} {cJ : ℤ} {I₀ : ℕ}
    (hfin : ∀ i, (Ahat i).Finite) (hsweepW : dot nJ w < 0) (F : FaceBlock S nJ vJ)
    (h : HwinI₀ S Ahat vJ1 nJ w cJ F.a' I₀) :
    ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
        {z | Colle37.GenClosure S (Ahat i ∪
          ShellMink.shellInter (Ahat i₀)
            (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) z} :=
  Nivat.FillCoverGuarded.fillCover_field_of_window_at_I₀ hfin hsweepW F rfl I₀ h

/-- 随 `i` 平移的见证点族。 -/
def zc (i : ℕ) : ℤ × ℤ :=
  (-6 * Nivat.LaneTowerOct8.KK i + 2, -2 * Nivat.LaneTowerOct8.KK i - 1)

/-- `i = 1` 处回到 §3 的 `(-16,-7)`，所以本节是那一条的推广而非另一条。 -/
theorem zc_one_eq : zc 1 = ((-16 : ℤ), (-7 : ℤ)) := by
  simp only [zc, KK_one]
  norm_num

theorem zc_mem_YB_all (i : ℕ) : zc i ∈ YB i := by
  have h2 := Nivat.LaneTowerOct8.two_le_KK i
  rw [mem_YB_iff]
  simp only [zc]
  omega

theorem zc_not_mem_AB_all (i : ℕ) : zc i ∉ AB i := by
  have h2 := Nivat.LaneTowerOct8.two_le_KK i
  rw [mem_AB_iff]
  simp only [zc]
  omega

/-- 出 `collarY … i₀ 1` 走的是 `u₆` 面（`-x-y`），要的只是 `KK i₀ < KK i`。 -/
theorem zc_not_mem_YB_of_lt {i₀ i : ℕ} (h : i₀ < i) : zc i ∉ YB i₀ := by
  have h2 := Nivat.LaneTowerOct8.two_le_KK i
  have hK : Nivat.LaneTowerOct8.KK i₀ < Nivat.LaneTowerOct8.KK i := by
    simp only [Nivat.LaneTowerOct8.KK]
    omega
  rw [mem_YB_iff]
  simp only [zc]
  omega

/-- **`I₀` 救不了 `hwin`。**  对**任何** `I₀`，弱守卫版在 oct8 上仍为假，
锚点范围与 §3 的 `not_Hwin_oct8` 逐字相同（`-3 < gen.1 + gen.2`）。

⛔ 辖域见 §6 抬头：同对象、同台架、同样不谈 `cutX`。 -/
theorem not_HwinI₀_oct8 (I₀ : ℕ) {gen : ℤ × ℤ} (hgen : -3 < gen.1 + gen.2) :
    ¬ HwinI₀ Nivat.LaneTowerOct8.Sphi AB Nivat.LaneTowerOct8.vJ1x Nivat.LaneTowerOct8.nJx
        Nivat.LaneTowerOct8.wfan 0 gen I₀ := by
  intro h
  have hguard : ∀ j, (0 : ℕ) ≤ j → Enveloped (↑Nivat.LaneTowerOct8.Sphi : Set (ℤ × ℤ)) (YB j) :=
    fun j _ => Nivat.LaneTowerOct8.enveloped_shellInter j
  have hpos : 0 < max I₀ 1 := lt_of_lt_of_le Nat.one_pos (le_max_right I₀ 1)
  rcases h 1 0 Nat.one_pos hguard (max I₀ 1) (by simp) _ (zc_mem_YB_all (max I₀ 1)) with hx | hw
  · rcases hx with h1 | h2
    · exact zc_not_mem_AB_all _ h1
    · exact zc_not_mem_YB_of_lt hpos h2
  · have hbad := hw ((-3 : ℤ), (0 : ℤ)) b_mem_Sphi
    have h2 := Nivat.LaneTowerOct8.two_le_KK (max I₀ 1)
    rw [mem_YB_iff] at hbad
    simp only [zc, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hbad
    omega

/-- **任何 `FaceBlock` 的锚点都在 §6 的适用范围内**（同 `not_Hwin_at_faceBlock`）。 -/
theorem not_HwinI₀_at_faceBlock (I₀ : ℕ) {vJ : ℤ × ℤ}
    (F : FaceBlock Nivat.LaneTowerOct8.Sphi Nivat.LaneTowerOct8.nJx vJ) :
    ¬ HwinI₀ Nivat.LaneTowerOct8.Sphi AB Nivat.LaneTowerOct8.vJ1x Nivat.LaneTowerOct8.nJx
        Nivat.LaneTowerOct8.wfan 0 F.a' I₀ :=
  not_HwinI₀_oct8 I₀ (faceBlock_a'_gen F)

/-! ## §7. ⭐ 换对象：`hwin` 在 `cutX` 上**活下来**，而且只在真锚点上活

lane-leafa-gen，2026-09-25。集成者第 230 轮同意的下一格。

§3 / §6 否掉的是 `collarY`（`b3_colle2.txt:518` 的 `Â_i^{(ε)}`，纯 sweep 之后与外壳取交）
上的 `hwin`，对一切 `I₀`、对一切合法锚点。本节换的是**对象**：
`Nivat.LaneTowerHbaseCut.cutX`（`TowerHbaseCut.lean:146`），即再把 `shellSubStrip` 的**体**
交进去的那个版本。`cut_eq`（`TowerHbaseCut.lean:155`）把它钉成同族八边形，
**只把第 7 条从 `4K_i - 1` 收紧到 `2K_i`** ——收紧之后它与 `Â_i`（`Ahat`，`Oct8Bench.lean:497`）
**只差第一条**（`z.1 ≤ 1` 对 `z.1 ≤ 0`）。

**结论有两半，互为对照（分母 2/2，同一台架、同一族、同一 `𝒮_φ`）：**

| 锚点 | `HwinCut` | 见证 |
|---|---|---|
| `(0,1)` ＝ `Nivat.LaneTowerOct8.genx`（**台架上活着的那个 `FaceBlock` 的 `a'`**，`Oct8Bench.lean:1675`） | **真**，对一切 `I₀`、一切 `i₀ ≤ i` | `hwinCut_at_genx` |
| `(0,0)` | **假**，对一切 `I₀` | `not_hwinCut_at_zero_zero`，见证点 `zq i = (1, 2K_i - 2)` |

而 `faceBlock_a'_cases` 说台架上**只有这两个**可能的锚点（`F.a'.1 = 0` ＋ `a' ∈ 𝒮_φ`），
`Nivat.LaneTowerOct8.faceBlockX` 取到的正是活的那个。
⟹ **`fillCover_of_window` 这条归约在 oct8 上没有死**：死的是「用纯 sweep 的 `collarY` 当对象」，
不是归约本身，也不是锚点的选法。

⛔⛔ **本节的正面结论以 `shellSubStrip` 的体为因子，而本台架上 `shellSubStrip` 的 containment
为假**（`Nivat.LaneTowerHbaseCut.cut_env_and_strict` 第三合取，见证经 `cut_ne_shellInter` /
`escape_not_mem_cut`，lane-tower-hbase 2026-09-25 给出）。⟹ 本节是**链侧归约的正控**，
**不是**本台架上 `fillCover` 的兑现，也**不**与 §3 / §6 的反例矛盾。

⚠ **第 231 轮补记（lane-leafa-gen 自核，收据 `tmp/wip/lane-leafa-gen-collarbody.lean`）：
换对象这一步在链上是恒等操作，因此它不减债。**
`FillCoverGuarded.collarY` 的定义体逐字符就是 `ChainDataGeomParts.shellSubStrip` /
`fillCover` 两条字段结论的左端（内核见证 `collarY_is_shellSubStrip`，证明体即 `c.shellSubStrip`）；
于是在字段自己的守卫下 `collarY ∩ 体 = collarY`（`collarY_inter_body_eq`），
两个对象上的残项**互推**（`hwin_inter_iff`）。
⟹ 两个对象**只在 `shellSubStrip` 为假的地方分开，而正好在那里过户桥拿不到 `hsub`**。
⛔ 故不许把本节读成「链上 `hwin` 因此可得」。

⚠ 另一条继承的辖域：`TowerHbaseCut.lean` 的 `ε` **写死为 `1`**（`cutX` 体内是 `shell … 0 1`，
无 `ε` 参数），而链上字段是 `∀ ε` ⟹ 本节的结论只覆盖 `ε = 1` 那一格。

`fillCover_on_cut_at_genx` 把这条正面结论接成 `fillCover` 的**结论形状**
（经 `FillCoverGuarded.fillCover_pointwise_generic`，`FillCoverGuarded.lean` §10）。

## 辖域（PROTOCOL §54，与 §3 同样严格）

1. ⛔ **本节不说链上的 `fillCover` 字段已兑现。** 字段要的对象是 `collarY`
   （`ChainPartsFeed.lean:271-279`），不是 `cutX`；要把本节的正面变成字段的正面，
   必须先有人证「链上的 `Â_i^{(ε)}` 可以取成 `cutX` 那一版」——那是 lane-tower-hbase 那条线
   （✅ **2026-09-25 订正，lane-tower-hbase 指出**：`not_shellSubStrip_body` 在
   **`Oct8Bench.lean`**（`Nivat.LaneTowerOct8.not_shellSubStrip_body`），`TowerHbaseCut.lean`
   里 0 命中；自陈是**反证台架**的也是 `Oct8Bench.lean` 的抬头，不是 `TowerHbaseCut.lean` 的。
   ⛔ 那条不许当一般事实引用这一点不变）。本节只把「换对象之后残项还成不成立」这一格填上。
   ⚠ 而由第 231 轮的 `hwin_inter_iff`（见 §7 抬头），这一格在**链上**与原格等价，
   ⟹ 它不是链上 `fillCover` 的减债项。
2. ⛔ **本节不撤回 §3 / §6。** 那两节对 `collarY` 仍然有效；两者对象不同，不冲突。
3. ⚠ 本节是**这一族八边形**上的话。`hwinCut_at_genx` 的证明只用 `cut_eq` 的八个常数与
   `coe_Sphi` 的八条外围不等式，不用任何别的台架性质；但它仍然是台架，不是一般定理。
4. ⚠ 数值旁证（`tmp/_cutwin_num.py`，**不是**证据，只为定位）：`(i₀,i)` 取
   `(0,1)/(0,2)/(1,2)/(0,3)/(1,3)/(2,3)/(0,5)/(3,5)` 八组，`genx` 侧守卫集 2–10 点**全过**，
   `(0,0)` 侧每组**恰破 1 点**（正是 `zq i`），同组 `collarY`（`YB`）侧两个锚点各破 15–61 点。
   守卫集只有 2–10 点 ⟹ 数值本身分辨力弱，载重的是下面对一切 `i` 的内核证明。 -/

/-- `cutX i` 的八条不等式（`TowerHbaseCut.cut_eq` 的直接读出）。
与 `mem_AB_iff`（`:385`）逐条对比：**只有第一条不同**（`z.1 ≤ 1` 对 `z.1 ≤ 0`），
其余七条逐字相同。这就是 `∩ shellSubStrip` 把第 7 条收紧之后的全部效果。 -/
theorem mem_cut_iff (i : ℕ) {z : ℤ × ℤ} :
    z ∈ Nivat.LaneTowerHbaseCut.cutX i ↔ z.1 ≤ 1 ∧
      z.1 + z.2 ≤ 2 * Nivat.LaneTowerOct8.KK i - 1 ∧
      z.2 ≤ 2 * Nivat.LaneTowerOct8.KK i ∧
      -z.1 + z.2 ≤ 8 * Nivat.LaneTowerOct8.KK i - 1 ∧
      -z.1 ≤ 6 * Nivat.LaneTowerOct8.KK i ∧
      -z.1 - z.2 ≤ 8 * Nivat.LaneTowerOct8.KK i - 1 ∧
      -z.2 ≤ 2 * Nivat.LaneTowerOct8.KK i ∧ z.1 - z.2 ≤ 0 := by
  rw [Nivat.LaneTowerHbaseCut.cut_eq i]
  exact Nivat.LaneTowerOct8.mem_oct8

/-- `𝒮_φ` 的八条外围不等式，来自 `coe_Sphi : ↑𝒮_φ = oct8 0 1 2 4 3 3 1 0`
（`Oct8Bench.lean:482`）。这是下面所有算术的**全部**输入：不对 12 个点逐个 case。 -/
theorem sphi_bounds {b : ℤ × ℤ} (hb : b ∈ Nivat.LaneTowerOct8.Sphi) :
    b.1 ≤ 0 ∧ b.1 + b.2 ≤ 1 ∧ b.2 ≤ 2 ∧ -b.1 + b.2 ≤ 4 ∧ -b.1 ≤ 3 ∧
      -b.1 - b.2 ≤ 3 ∧ -b.2 ≤ 1 ∧ b.1 - b.2 ≤ 0 := by
  have h : b ∈ (↑Nivat.LaneTowerOct8.Sphi : Set (ℤ × ℤ)) := Finset.mem_coe.mpr hb
  rw [Nivat.LaneTowerOct8.coe_Sphi] at h
  exact h

theorem KK_mono {i₀ i : ℕ} (h : i₀ ≤ i) :
    Nivat.LaneTowerOct8.KK i₀ ≤ Nivat.LaneTowerOct8.KK i := by
  simp only [Nivat.LaneTowerOct8.KK]
  omega

theorem finite_cut (i : ℕ) : (Nivat.LaneTowerHbaseCut.cutX i).Finite := by
  rw [Nivat.LaneTowerHbaseCut.cut_eq]
  exact Nivat.LaneTowerOct8.finite_oct8 _ _ _ _ _ _ _ _

/-- `HwinCut gen I₀`：`HwinI₀`（§6）的形状，对象换成 `cutX`。
`cutX` 把 `ε` 内建成 `1`（`TowerHbaseCut.lean:144-145`），所以**没有** `∀ ε`，
相应地也没有 `Enveloped` 守卫那条前提——它在这一族上恒真（`TowerHbaseCut.envOf_cut`，
`TowerHbaseCut.lean:202`，对每个 `i`）⟹ 下面的正面与负面**都不是空真**（§41）。

⛔ **这不是 `fillCover_of_window` 收的那条 binder。** 那条要 `collarY`（§1 `Hwin`
已用 `hwin_is_the_binder` 内核确认过）。本条是同形状、换对象；两者之间的桥是
`FillCoverGuarded.fillCover_pointwise_generic`，见 `fillCover_on_cut_at_genx`。 -/
def HwinCut (gen : ℤ × ℤ) (I₀ : ℕ) : Prop :=
  ∀ i₀ i : ℕ, max i₀ I₀ ≤ i →
    ∀ z ∈ Nivat.LaneTowerHbaseCut.cutX i,
      z ∈ AB i ∪ Nivat.LaneTowerHbaseCut.cutX i₀ ∨
      ∀ b ∈ Nivat.LaneTowerOct8.Sphi, z + (b - gen) ∈ Nivat.LaneTowerHbaseCut.cutX i

/-- ⭐ **`hwin` 在 `cutX` 上、台架真锚点 `genx = (0,1)` 处为真**，对一切 `I₀`、一切 `i₀ ≤ i`。

三分支，全部是 `omega`：
* `z.1 ≤ 0` ⟹ `z ∈ Â_i`（`cutX` 与 `Â_i` 只差第一条，见 `mem_cut_iff` 的注）；
* `z.1 = 1` 且 `z.2 ≤ 2K_{i₀} - 2` ⟹ `z ∈ cutX i₀`；
* 否则 `z.2 ≥ 2K_{i₀} - 1 ≥ 3`，此时八条对每个 `b ∈ 𝒮_φ` 都留有余量。
关键的两条是 `u₂ = (1,1)`（用 `b.1 + b.2 ≤ 1` ＝ `gen` 在该方向上已是 `𝒮_φ` 的极大点）
与 `u₈ = (1,-1)`（用 `b.1 - b.2 ≤ 0` 与 `z.2 ≥ 3`）。 -/
theorem hwinCut_at_genx (I₀ : ℕ) : HwinCut ((0 : ℤ), (1 : ℤ)) I₀ := by
  intro i₀ i hle z hz
  have hK := Nivat.LaneTowerOct8.two_le_KK i
  have hK0 := Nivat.LaneTowerOct8.two_le_KK i₀
  have hKm : Nivat.LaneTowerOct8.KK i₀ ≤ Nivat.LaneTowerOct8.KK i :=
    KK_mono (le_trans (le_max_left i₀ I₀) hle)
  rw [mem_cut_iff] at hz
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hz
  by_cases hx : z.1 ≤ 0
  · exact Or.inl (Set.mem_union_left _ ((mem_AB_iff i).mpr ⟨hx, h2, h3, h4, h5, h6, h7, h8⟩))
  by_cases hy : z.2 ≤ 2 * Nivat.LaneTowerOct8.KK i₀ - 2
  · refine Or.inl (Set.mem_union_right _ ((mem_cut_iff i₀).mpr ⟨by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega⟩))
  refine Or.inr fun b hb => ?_
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := sphi_bounds hb
  rw [mem_cut_iff]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- ⭐ **接成 `fillCover` 的结论形状。**  `X := Â_i`、`Y := cutX i`、`Y₀ := cutX i₀`
喂进 `FillCoverGuarded.fillCover_pointwise_generic`，锚点由 `Nivat.LaneTowerOct8.faceBlockX`
与 `gen_eq_x`（`Oct8Bench.lean:1760`）提供 ⟹ `gen` 不是随手取的，是那个 `FaceBlock` 的 `a'`。

⛔ 辖域重申：这是 `cutX` 上的结论。链上字段要 `collarY`（见本节抬头第 1 条）。 -/
theorem fillCover_on_cut_at_genx (I₀ : ℕ) :
    ∀ i₀ i : ℕ, max i₀ I₀ ≤ i →
      Nivat.LaneTowerHbaseCut.cutX i ⊆
        {z | Colle37.GenClosure Nivat.LaneTowerOct8.Sphi
          (AB i ∪ Nivat.LaneTowerHbaseCut.cutX i₀) z} :=
  fun i₀ i hle =>
    Nivat.FillCoverGuarded.fillCover_pointwise_generic (finite_cut i)
      Nivat.LaneTowerOct8.faceBlockX Nivat.LaneTowerOct8.gen_eq_x (hwinCut_at_genx I₀ i₀ i hle)

/-- `u₂ = (1,1)` 那面的端点 `(1, 2K_i - 2)`：`cutX i` 里 `x = 1` 的最高点，
也是 `x = 1` 这条边与 `u₂` 面唯一的公共点。 -/
def zq (i : ℕ) : ℤ × ℤ := ((1 : ℤ), 2 * Nivat.LaneTowerOct8.KK i - 2)

theorem zq_mem_cut (i : ℕ) : zq i ∈ Nivat.LaneTowerHbaseCut.cutX i := by
  have hK := Nivat.LaneTowerOct8.two_le_KK i
  rw [mem_cut_iff]
  simp only [zq]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem zq_not_mem_AB (i : ℕ) : zq i ∉ AB i := by
  rw [mem_AB_iff]
  simp only [zq]
  rintro ⟨h1, -⟩
  omega

theorem zq_not_mem_cut_of_lt {i₀ i : ℕ} (h : i₀ < i) :
    zq i ∉ Nivat.LaneTowerHbaseCut.cutX i₀ := by
  have hKm : Nivat.LaneTowerOct8.KK i₀ < Nivat.LaneTowerOct8.KK i := by
    simp only [Nivat.LaneTowerOct8.KK]; omega
  rw [mem_cut_iff]
  simp only [zq]
  rintro ⟨-, h2, -⟩
  omega

theorem zeroOne_mem_Sphi : ((0 : ℤ), (1 : ℤ)) ∈ Nivat.LaneTowerOct8.Sphi := by decide

/-- **锚点 `(0,0)` 处 `HwinCut` 为假**，对一切 `I₀`。
见证点 `zq i` 在 `u₂ = (1,1)` 面上，而 `(0,0)` 在该方向上被 `(0,1) ∈ 𝒮_φ` 严格超过
（`not_window_at_max`（§2）的机理，这里直接算）。⟹ 换对象**没有**把锚点的区别抹掉，
反而是它把两个锚点分开的：`collarY` 上两个锚点都死（§3/§6），`cutX` 上只有 `(0,0)` 死。 -/
theorem not_hwinCut_at_zero_zero (I₀ : ℕ) : ¬ HwinCut ((0 : ℤ), (0 : ℤ)) I₀ := by
  intro h
  have hpos : 0 < max I₀ 1 := lt_of_lt_of_le Nat.one_pos (le_max_right I₀ 1)
  rcases h 0 (max I₀ 1) (by simp) _ (zq_mem_cut (max I₀ 1)) with hx | hw
  · rcases hx with h1 | h2
    · exact zq_not_mem_AB _ h1
    · exact zq_not_mem_cut_of_lt hpos h2
  · have hbad := hw ((0 : ℤ), (1 : ℤ)) zeroOne_mem_Sphi
    have hK := Nivat.LaneTowerOct8.two_le_KK (max I₀ 1)
    rw [mem_cut_iff] at hbad
    simp only [zq, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hbad
    omega

/-- **台架上只有两个可能的锚点。**  `faceBlock_a'_fst_nonneg`（`:455`）给 `0 ≤ F.a'.1`，
`F.a'_mem` 给 `F.a' ∈ 𝒮_φ`（其中只有 `(0,0)`、`(0,1)` 的第一坐标非负）。与 `vJ` 无关。
⟹ 与 `hwinCut_at_genx` / `not_hwinCut_at_zero_zero` 合起来：`cutX` 上 `hwin` 的成败
**完全由锚点决定**，而台架上有活体的那个 `FaceBlock`（`faceBlockX`）取的正是成功的那个。 -/
theorem faceBlock_a'_cases {vJ : ℤ × ℤ}
    (F : FaceBlock Nivat.LaneTowerOct8.Sphi Nivat.LaneTowerOct8.nJx vJ) :
    F.a' = ((0 : ℤ), (0 : ℤ)) ∨ F.a' = ((0 : ℤ), (1 : ℤ)) := by
  have h0 := faceBlock_a'_fst_nonneg F
  have hmem := F.a'_mem
  simp only [Nivat.LaneTowerOct8.Sphi, Finset.mem_insert, Finset.mem_singleton,
    Prod.ext_iff] at hmem ⊢
  omega

/-! ## §9. `b3_colle2.txt:38` 的 `0 < i₀`：∀ 侧**不是**纯记账（lane-leafa-gen，第 234 轮）

`b3_colle2.txt:38`（「We use $\mathbb{N}=\{1,2,\ldots\}$ …」）⟹ `:520` 的 `i_0` 是正的，
`ChainDataGeomParts` 的 `escapeW` / `shellSubStrip` / `fillCover` 各比原文多 `i₀ = 0` 一个实例。
给字段补上 `0 < i₀` 会让所有**取 `i₀ = 0` 的反例**失效 —— 本节把 §6 那条补回来。

⭐ **这一节订正我自己第 233 轮的一句话。** 当时我说 `0 < i₀` 的修正是「纯记账」，
依据是 `shellSubStrip` 那一格（`i := max 1 I₀` 就够，因为那里的越界理由是 `u₇`，不看 `i₀`）。
`fillCover` 这一格**不够**：`HwinI₀` 的反例要 `i₀ < i` 才能把见证点挤出 `collarY … i₀ ε`
（`zc_not_mem_YB_of_lt`）。`i₀ := 0` 时 `i := max I₀ 1` 自动满足 `0 < i`；`i₀ := 1` 时不再自动，
必须改成 `i := max I₀ 1 + 1`（守卫 `max 1 I₀ ≤ i` 照样满足）。

⟹ 判据一句话：**`i₀` 只出现在守卫里的反例，抬 `i₀` 免费；`i₀` 还出现在见证点越界理由里的，
要重取实例。** ∃ 侧（`shellEnv`）的对照见 `FillCoverWitness.lean` §8 的 `exists_pos_i₀`：那边恒为零。

⛔ 辖域与 §6 逐字相同（同一座 oct8 台架、同一族 `zc`、同样不谈 `cutX`），改的只有两个下标。 -/

/-- `HwinI₀` 的 `0 < i₀` 版：字段按 `b3_colle2.txt:38` 修正之后，
`fillCover_field_of_window_at_I₀` 的残项会长成的样子。 -/
def HwinI₀Pos (S : Finset (ℤ × ℤ)) (Ahat : ℕ → Set (ℤ × ℤ)) (vJ1 nJ w : ℤ × ℤ) (cJ : ℤ)
    (gen : ℤ × ℤ) (I₀ : ℕ) : Prop :=
  ∀ ε i₀ : ℕ, 0 < ε → 0 < i₀ →
    (∀ i, i₀ ≤ i → Enveloped (↑S : Set (ℤ × ℤ))
      (Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i ε)) →
    ∀ i, max i₀ I₀ ≤ i →
    ∀ z ∈ Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i ε,
      z ∈ Ahat i ∪ Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i₀ ε ∨
      ∀ b ∈ S, z + (b - gen) ∈ Nivat.FillCoverGuarded.collarY Ahat vJ1 nJ w cJ i ε

/-- 旧残项推新残项（新的多一条前件）⟹ `¬` 新的是**更强**的话，本节不是把 §6 搬轻。 -/
theorem hwinI₀Pos_of_hwinI₀ {S : Finset (ℤ × ℤ)} {Ahat : ℕ → Set (ℤ × ℤ)}
    {vJ1 nJ w : ℤ × ℤ} {cJ : ℤ} {gen : ℤ × ℤ} {I₀ : ℕ}
    (h : HwinI₀ S Ahat vJ1 nJ w cJ gen I₀) : HwinI₀Pos S Ahat vJ1 nJ w cJ gen I₀ :=
  fun ε i₀ hε _ henv i hi => h ε i₀ hε henv i hi

/-- ⭐ **oct8 上的 `hwin` 反例在 `0 < i₀` 下仍然成立**，实例改成
`i₀ := 1`、`i := max I₀ 1 + 1`（§6 是 `i₀ := 0`、`i := max I₀ 1`）。 -/
theorem not_HwinI₀Pos_oct8 (I₀ : ℕ) {gen : ℤ × ℤ} (hgen : -3 < gen.1 + gen.2) :
    ¬ HwinI₀Pos Nivat.LaneTowerOct8.Sphi AB Nivat.LaneTowerOct8.vJ1x
        Nivat.LaneTowerOct8.nJx Nivat.LaneTowerOct8.wfan 0 gen I₀ := by
  intro h
  have hguard : ∀ j, (1 : ℕ) ≤ j → Enveloped (↑Nivat.LaneTowerOct8.Sphi : Set (ℤ × ℤ)) (YB j) :=
    fun j _ => Nivat.LaneTowerOct8.enveloped_shellInter j
  have hlt : (1 : ℕ) < max I₀ 1 + 1 := Nat.succ_lt_succ_iff.mpr (le_max_right I₀ 1)
  have hge : max (1 : ℕ) I₀ ≤ max I₀ 1 + 1 := by
    rw [Nat.max_comm]; exact Nat.le_succ _
  rcases h 1 1 Nat.one_pos Nat.one_pos hguard (max I₀ 1 + 1) hge _
    (zc_mem_YB_all (max I₀ 1 + 1)) with hx | hw
  · rcases hx with h1 | h2
    · exact zc_not_mem_AB_all _ h1
    · exact zc_not_mem_YB_of_lt hlt h2
  · have hbad := hw ((-3 : ℤ), (0 : ℤ)) b_mem_Sphi
    have h2 := Nivat.LaneTowerOct8.two_le_KK (max I₀ 1 + 1)
    rw [mem_YB_iff] at hbad
    simp only [zc, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hbad
    omega

/-- **任何 `FaceBlock` 的锚点都在 §9 的适用范围内**（同 `not_HwinI₀_at_faceBlock`）。 -/
theorem not_HwinI₀Pos_at_faceBlock (I₀ : ℕ) {vJ : ℤ × ℤ}
    (F : FaceBlock Nivat.LaneTowerOct8.Sphi Nivat.LaneTowerOct8.nJx vJ) :
    ¬ HwinI₀Pos Nivat.LaneTowerOct8.Sphi AB Nivat.LaneTowerOct8.vJ1x
        Nivat.LaneTowerOct8.nJx Nivat.LaneTowerOct8.wfan 0 F.a' I₀ :=
  not_HwinI₀Pos_oct8 I₀ (faceBlock_a'_gen F)

end Nivat.LaneLeafAGenHwinRefute

#print axioms Nivat.LaneLeafAGenHwinRefute.hwinI₀Pos_of_hwinI₀
#print axioms Nivat.LaneLeafAGenHwinRefute.not_HwinI₀Pos_oct8
#print axioms Nivat.LaneLeafAGenHwinRefute.not_HwinI₀Pos_at_faceBlock

#print axioms Nivat.LaneLeafAGenHwinRefute.hwin_is_the_binder
#print axioms Nivat.LaneLeafAGenHwinRefute.dot_add_sub_anchor
#print axioms Nivat.LaneLeafAGenHwinRefute.not_window_at_max
#print axioms Nivat.LaneLeafAGenHwinRefute.mem_of_hwin_at_support
#print axioms Nivat.LaneLeafAGenHwinRefute.mem_YB_iff
#print axioms Nivat.LaneLeafAGenHwinRefute.mem_AB_iff
#print axioms Nivat.LaneLeafAGenHwinRefute.zc_mem_YB_all
#print axioms Nivat.LaneLeafAGenHwinRefute.zc_not_mem_AB_all
#print axioms Nivat.LaneLeafAGenHwinRefute.zc_not_mem_YB0
#print axioms Nivat.LaneLeafAGenHwinRefute.b_mem_Sphi
#print axioms Nivat.LaneLeafAGenHwinRefute.not_Hwin_oct8
#print axioms Nivat.LaneLeafAGenHwinRefute.faceBlock_a'_fst_nonneg
#print axioms Nivat.LaneLeafAGenHwinRefute.faceBlock_a'_gen
#print axioms Nivat.LaneLeafAGenHwinRefute.not_Hwin_at_faceBlock
#print axioms Nivat.LaneLeafAGenHwinRefute.hstep_is_the_binder
#print axioms Nivat.LaneLeafAGenHwinRefute.p_not_mem_AB
#print axioms Nivat.LaneLeafAGenHwinRefute.p_not_mem_YB0
#print axioms Nivat.LaneLeafAGenHwinRefute.p_not_mem_YB1
#print axioms Nivat.LaneLeafAGenHwinRefute.not_Hstep_oct8
#print axioms Nivat.LaneLeafAGenHwinRefute.not_Hstep_at_faceBlock
#print axioms Nivat.LaneLeafAGenHwinRefute.hwinI₀_is_the_binder
#print axioms Nivat.LaneLeafAGenHwinRefute.zc_one_eq
#print axioms Nivat.LaneLeafAGenHwinRefute.zc_mem_YB_all
#print axioms Nivat.LaneLeafAGenHwinRefute.zc_not_mem_AB_all
#print axioms Nivat.LaneLeafAGenHwinRefute.zc_not_mem_YB_of_lt
#print axioms Nivat.LaneLeafAGenHwinRefute.not_HwinI₀_oct8
#print axioms Nivat.LaneLeafAGenHwinRefute.not_HwinI₀_at_faceBlock

#print axioms Nivat.LaneLeafAGenHwinRefute.mem_cut_iff
#print axioms Nivat.LaneLeafAGenHwinRefute.sphi_bounds
#print axioms Nivat.LaneLeafAGenHwinRefute.KK_mono
#print axioms Nivat.LaneLeafAGenHwinRefute.finite_cut
#print axioms Nivat.LaneLeafAGenHwinRefute.hwinCut_at_genx
#print axioms Nivat.LaneLeafAGenHwinRefute.fillCover_on_cut_at_genx
#print axioms Nivat.LaneLeafAGenHwinRefute.zq_mem_cut
#print axioms Nivat.LaneLeafAGenHwinRefute.zq_not_mem_AB
#print axioms Nivat.LaneLeafAGenHwinRefute.zq_not_mem_cut_of_lt
#print axioms Nivat.LaneLeafAGenHwinRefute.not_hwinCut_at_zero_zero
#print axioms Nivat.LaneLeafAGenHwinRefute.faceBlock_a'_cases
