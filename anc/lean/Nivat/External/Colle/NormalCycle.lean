/-
# `b3_colle2.txt:319` + `:424` 转录成一个索引族 `NormalCycle`

lane-tower-hlev, 2026-09-24。**唯一 `import` 是 `Nivat.External.Colle.PolyChainSum`**
（`grep -n "^import"`，集成者第 185 轮实测；旧写「只 import `LatticeEdges`」是假话，已改。
`LatticeEdges` 是经 `PolyChainSum` 传递引入的，不是直接 import——这两件事不一样，
按 `PROTOCOL.md` §57 属 B 类，文件头自报的 import 表必须与 `grep -n "^import"` 一致）。

## §0.1  这是什么

team-lead 第 186 轮头号派工：把 `:319`（`|E(𝒮_φ)| = 2m`，每条边与某个 `h_i` 平行或反平行）与
`:424`（`ℓ_1, …, ℓ_{2m}` 按 successor 环序枚举，下标模 `2m`）转录成**一个索引族**，供四条 lane
共用（我、lane-leafa-shell 的 `hbdd`/`:506`、lane-hole3-nlmax、lane-leafa-gen 的举证责任翻转，
以及 lane-tower-hbase 的「缺口二」枚举半边）。

## §0.2  原文逐字（本轮亲读，`sed -n '310,330p'` / `sed -n '415,440p'`）

`:319`：

> Then `|E(𝒮_φ)| = 2m` and, for each `w ∈ E(𝒮_φ)`, `w` is either parallel or antiparallel to
> some vector `h_i`, with `1 ≤ i ≤ m`.

`:424`（Lemma 3.5 的假设段）：

> Let `η ∈ 𝒜^{ℤ²}` be a configuration with `φ(X) = (X^{h_1}-1)⋯(X^{h_m}-1) ∈ ann_R(η)`, where
> `h_1, …, h_m ∈ ℤ²`, with `m ≥ 2`, are vectors in pairwise distinct directions. Suppose
> `ℓ_1, …, ℓ_{2m} ⊂ ℝ²` is an enumeration of the oriented lines through the origin parallels to
> the edges of `𝒮_φ` where the edge parallel to `ℓ_{i+1}` is a successor of the edge parallel to
> `ℓ_i` and indices are taken modulo `2m`.

⚠ **全文唯一定义环序的地方，一个方向词都没有**（「successor」不含 cw/ccw）。这不是原文的疏漏，
是规范自由：`:351` 对 `v⃗_ℓ` 只规定「平行于 `ℓ` 的最短非零向量」，符号本来就自由。本文件把这个
比特参数化成 `σ : ℤ`（`σ = 1` 逆时针 / `σ = -1` 顺时针），**两支逐字同一个结构**，并在 §7 给出
显式 `GL₂(ℤ)` 对合把一支搬成另一支（`PROTOCOL.md §54` 对合不变式法）。

🔴 **订正（第 198 轮，集成者亲读原文）：上一段第一句「全文唯一定义环序的地方，一个方向词都没有」
是错的，已作废。** 错因是只 grep 了**用** `successor` 的那几句（`:424`/`:541`/`:738`/`:764`），
没去找 `successor` 的**定义处**。定义在 `b3_colle2.txt:255`（§2.1）：
「our standard convention is that the boundary of `conv(S)` is **positively oriented**…
our convention endows each `w ∈ E(S)` with a well-defined **successor** edge」——
方向词在这里，且 `S_φ` 满足其「`conv(S)` 有正面积」的前提。⟹ **原文的 successor ＝ 逆时针。**
逐量词三步与前提核对见 §9 第 5 条。

⚠ 本段**其余部分仍然成立且仍然要读**：`σ` 作为**参数**是规范自由（§7 的 `mirror` 是定理，
`ncy_both_sigma_inhabited` 也照旧真），`:351` 对 `v⃗_ℓ` 符号确实不作规定。
`:255` 改变的不是「比特可不可自由」，而是「原文把它选在哪一支」。

⚠⚠ **但规范已经选定：接链一律用 `σ = 1`（§9 的 `NormalCycleCcw`）。** team-lead 第 186 轮
裁决：主仓现有三个独立的朝向锚（`exists_preamble_pair` 恒出 `0 < det nℓ vl`；`exists_nnextJ`
恒要 `0 < det ℓ J`；`PolyChainSum.Arc` 的 docstring 自称 counter-clockwise），都在法向侧。
镜像论证**没有被证伪**——比特本身仍是规范，`ncy_both_sigma_inhabited` 仍成立；变的是同一个
规范里另有三处携带朝向的量被独立钉死，所以写成「两支任选」接链时会差一个号（编译期错误）。
一般 `σ` 版本留着，因为它是诚实的一般陈述，而且 §7 的对合需要它。

## §0.3  ⚠ 转录债：哪些字段不是原文字面（团队长纪律 2，硬规矩 5）

逐字段交代「原文说了什么 / 我额外用了什么」，**不假装字面**：

| 字段 | 原文出处 | 中间推理（＝债） |
|---|---|---|
| `hm` | `:424`「with `m ≥ 2`」 | 无，字面 |
| `nu` | `:424`「an enumeration of the oriented lines ... `ℓ_1, …, ℓ_{2m}`」 | 存**法向**不存方向，见 §0.4 |
| `mem` | `:424`「parallels to the edges of `𝒮_φ`」 | 无 |
| `ne_zero` | `:424`「lines **through the origin**」+ `:351`「最短**非零**向量」 | 无 |
| `anti` | `:319`「`|E| = 2m`，每条边平行或反平行于某个 `h_i`」 | **两步**：(a) `𝒮_φ` 凸 ⟹ 每个有向方向至多一条边 ⟹ `2m` 条边恰是 `m` 对 `±`；(b) 加 `:424` 的环序 ⟹ 对径映射是环序上无不动点的保序对合 ⟹ 恰为平移 `m` |
| `step` | `:424`「successor」 | **规范**：原文无方向词，`σ` 的全部来源就是这一条；见 §0.5 |
| `hnoArc` | `:424`「successor」 | **债已清**：与主仓 `Arc … = ∅` 互为改写（§8 `hnoArc_iff_arc_empty`），不是我们的解读 |
| `indep` | `:424`「pairwise distinct directions」+ `:319` | 同 `anti` 的 (a)(b)：同方向类 ⟺ 下标差恰 `m` |

⛔ **没有**任何字段断言「法向按角序排」——那是团队长纪律 2 点名禁止的造债。排序是 `hnoArc`+`step`
的**推论**（`window_pos`），不是公理。

## §0.4  法向侧 vs 方向侧：`det` 对这 90° 是瞎的

原文的 `ℓ_i` 是**有向直线**（方向侧），Lean 的 `E ↑𝒮_φ` 是**外法向**（`LatticeEdges.lean:217`），
两者差 `dir`（90°）。但

```
det (dir a) (dir b) = det a b        -- `ncy_det_dir_dir`，恒等式
```

⟹ 「按 `det` 正负定义的环序」在两侧**逐字同一个**，本文件存法向、lane-tower-hbase 的
`sortedCand` 存方向，接口不需要任何转换引理。⚠ 唯一会错位的是**混合型**的量
（`dot a (dir b) = -det a b`，`LatticeEdges.lean:264`），例如 `⟪n_J, w⟫`、`⟪n_J, p⟫`——
那种接口必须说清哪个槽在哪侧。

## §0.5  `step` 为什么必须是字段（试过，推不出来）

`hnoArc k` 喂 `y := -(nu k)` 时第一个合取退化成 `0 < σ * 0`，喂 `y := -(nu (k+1))` 时第二个合取
退化成 `0 < σ * 0`，两边都拿不到信息。相邻步的号在原文里没有来源（`:424` 无方向词），
所以它只能是规范位 `σ`。这与 `Nivat/External/Colle/OrientationFree.lean`（集成者第 185 轮，
`det nℓ vl` 的号不可推导）是同一现象的另一处实例。

## §0.6  台架先行（硬规矩 6）

§4 给正八边形 `m = 4` 的**两个**完整实例：`NormalCycle ncyOctN 4 1` 与
`NormalCycle ncyOctN 4 (-1)`——**同一个法向集 `ncyOctN`，两个 `σ` 都可满足**，全部字段 `decide`
（零公理）。⟹ (a) 结构非空、非空真；(b) `σ` 确实自由，不是可推导的；(c) `m = 4` 有鉴别力
（`m ≤ 3` 对角度类判据零鉴别力，第 183 轮纪律；⚠ lane-leafa-gen 本轮的限定：幺模类守卫
`m = 3` 就够，那条纪律是两维的，别当成「一律 m = 4」）。

## §0.65  ⭐ successor 那一半**不必转录**（team-lead 第 186 轮裁决 3）

`hnoArc` 与主仓 `Nivat.PolyChainSum.Arc … = ∅` **互为改写**（§8 `hnoArc_iff_arc_empty`，双向，
不是单向推出），依据 `mem_Arc`（`PolyChainSum.lean:107`）逐字。供给方
`LeafAShellNNext.exists_w_hsweepW`（`LeafAShellNNext.lean:70`）的同一条输出还带
`0 < det J νJ1`（＝ `step`）。⟹ 九个字段里 **`step` 与 `hnoArc` 都有主仓现货**，
剩下的转录债只有 `anti` 和 `indep` 两条。

⚠ 字段名用 `hnoArc` 不用 `hgap`：`hgap` 已被 `OPEN.md:470` / `CORE-HOLES.md:1736` 的层区间
条件占用（`∀ n, ∃ z ∈ Rinf, lev (n+1) ≤ dot m z ∧ dot m z < lev n`），后来者改名。

## §0.7  交付的下游接口

* `NormalCycle.window_pos`：`1 ≤ s → s < m → 0 < σ * det (nu i) (nu (i+s))`，**任意起点 `i`**。
  归纳一步只用 `hnoArc (i+s)` 喂 `y := -(nu i)`（由 `anti`+`mem` 免费在 `N` 里）＋ `indep`；
  **不需要**相邻性之外的任何东西。
* `NormalCycle.dot_prev_p_nonpos`：`t + 1 < m → σ * dot (nu (i+t)) (-(dir (nu i))) ≤ 0`
  ——即 `⟪ν_{J-1}, p⟫ ≤ 0`（`p = -(dir ν_ι)`，`NOTATION.md`），`:432` 窗口 `ι+1 ≤ J ≤ ι+m-1`
  逐字对应。这是我第 5 节那条「双瓶颈」，本轮兑现。
* `NormalCycle.det_at_m`：`det (nu i) (nu (i+m)) = 0`——`:432` 的上界 `J ≤ ι+m-1` **不是松的**，
  它与 `indep` 自己的定义域重合。
* `NormalCycle.mirror`：`NormalCycle N m σ → NormalCycle (ncyMir '' N) m (-σ)`。
* §9 的 `NormalCycleCcw N m := NormalCycle N m 1` 及其五条去 `σ` 形
  （`window_pos_ccw` / `dot_prev_p_nonpos_ccw'` / `e_pos_ccw` / `d_pos_ccw` / `D_pos_ccw`）
  与 `NormalCycle.arc_empty`（与主仓 `Arc` 直通）。**接链用这一组。**

🔴 **订正（第 198 轮，集成者亲读原文）**：原写「本文件**不**断言原文说了逆时针……后者是约定」。
**后半句已失效**：`b3_colle2.txt:255` 把 `successor` 定义为「`conv(S)` 的边界取 positively
oriented 之后的下一条边」，而 `:424`/`:541`/`:738`/`:764` 四处枚举句用的正是这个 `successor`
⟹ **逆时针不是我们的约定，是原文的约定**（详见 §9 第 5 条，含逐量词三步与 `S_φ` 正面积的前提核对）。

仍然成立的那半句：比特 `σ` 本身是**规范**——`§7` 的 `NormalCycle.mirror` 证的是
「孤立地看这一族前提，两读可互换」，那是定理，不受 `:255` 影响。变的只是：原文对这个规范
做了哪一个选择，现在有字面出处了，不再只是我方选定。
-/

import Nivat.External.Colle.PolyChainSum

set_option autoImplicit false

namespace Nivat.LaneTowerHlevNormalCycle

open Nivat Nivat.LE2

/-! ## §1  `det` / `dir` 代数 -/

/-- `det` 对同时旋转 90° 是瞎的。§0.4 的那条恒等式：法向侧与方向侧的环序逐字相同。 -/
theorem ncy_det_dir_dir (a b : ℤ × ℤ) : det (dir a) (dir b) = det a b := by
  simp only [det, dir]; ring

theorem ncy_det_self (a : ℤ × ℤ) : det a a = 0 := by
  simp only [det]; ring

theorem ncy_det_neg_left (a b : ℤ × ℤ) : det (-a) b = - det a b := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

theorem ncy_det_neg_right (a b : ℤ × ℤ) : det a (-b) = - det a b := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

/-- `⟪a, -(dir b)⟫ = det a b`.  配 `NOTATION.md` 的 `p = -(dir ν_ι)`：
`⟪ν_{J-1}, p⟫ = det ν_{J-1} ν_ι`。 -/
theorem ncy_dot_neg_dir (a b : ℤ × ℤ) : dot a (-(dir b)) = det a b := by
  simp only [dot, det, dir, Prod.fst_neg, Prod.snd_neg]; ring

/-! ## §2  索引族 -/

/-- **`b3_colle2.txt:319` + `:424` 的索引族转录。**

`N` 是 `E(𝒮_φ)`（法向侧，见 §0.4），`m` 是 `:424` 的 `m`，`σ` 是朝向规范位。
逐字段的原文出处与转录债见文件头 §0.3，**每一条都请连那张表一起引**。 -/
structure NormalCycle (N : Set (ℤ × ℤ)) (m : ℕ) (σ : ℤ) where
  /-- `:424`「`h_1, …, h_m ∈ ℤ²`, **with `m ≥ 2`**」。字面。 -/
  hm : 2 ≤ m
  /-- 朝向规范位只取 `±1`。原文 `:424` 无方向词，见 §0.5；这不是原文的量词，是规范。 -/
  hsigma : σ = 1 ∨ σ = -1
  /-- `:424`「`ℓ_1, …, ℓ_{2m}` is an **enumeration** of the oriented lines through the origin
  parallels to the edges of `𝒮_φ`」。存法向（§0.4），下标用 `ℕ`，周期性由 `anti` 蕴含。 -/
  nu : ℕ → ℤ × ℤ
  /-- `:424`「parallels to the **edges of `𝒮_φ`**」：每一项都是 `E(𝒮_φ)` 的元素。 -/
  mem : ∀ k, nu k ∈ N
  /-- `:424`「lines **through the origin**」＋ `:351`「shortest **nonzero** vector」。 -/
  ne_zero : ∀ k, nu k ≠ 0
  /-- `:319`「`|E(𝒮_φ)| = 2m`，每个 `w` 与某个 `h_i` 平行或反平行」。
  ⚠ **不是字面**：中间有两步（`𝒮_φ` 凸 ⟹ `2m` 条边恰是 `m` 对 `±`；`:424` 的环序 ⟹ 对径
  映射是无不动点保序对合 ⟹ 平移 `m`）。见 §0.3 的表。

  ⭐ **2026-09-24（第 197 轮）订正：偏移量 `m` 现在有字面出处，上面那条 ⚠ 的第二步降级。**
  `b3_colle2.txt:880` 逐字（lane-tower-hlev 首见，集成者亲读复核）：
  「but as $\ell_{\iota-1}$ is **antiparallel** to $\ell_{\iota+m-1}$」——
  `(ι−1) + m = ι+m−1` ⟹ **偏移量取值逐字就是 `m`**。
  ⚠ 同句前半的 Claims 4.9 / 4.10 是**禁区**（顺序禁令：Claim 4.10 在 Claim 4.7 下游），
  此处只引黑体那半句，不引不用前半句。

  ⚠⚠ **同轮再订正（lane-towerpkg 挑出，lane-tower-hlev 复核，集成者采纳）：
  本条初稿曾写「该半句里一个 `η` 都没有 ⟹ 不需要 Lemma 4.5（`:770`）的『`ι` 全称』那条腿」，
  那句话是错的，已删。** 理由：**η-free ≠ 下标 free**。`:880` 只在**一个下标** `j = ι−1` 上断言，
  而本字段是 `∀ k`；更要命的是 `:880` 里的 `ι` **本身就是 η-依赖的**（它是 Lemma 4.5 假设
  `-ℓ_ι, ℓ_ι ∈ nexpd(η)` 绑的那个 `ι`）⟹「与 `η` 无关」只对该半句的**内容**成立，
  对它的**下标位置**不成立。从单实例推广到 `∀ k` 仍需一条腿，而**那条腿只能是上面那两步几何**。

  ⚠⚠⚠ **第 199 轮再订正（lane-towerpkg 自提自撤，lane-tower-hlev 独立同意，集成者亲读 `:770` 复核）：
  上一段初稿在「那条腿」处并列写了「`:770` 的 `ι` 全称」，该选项不存在，已删。**
  `:770`（Lemma 4.5）逐字是「If `-ℓ_ι, ℓ_ι ∈ nexpd(η)` **for some** `1 ≤ ι ≤ 2m`, then …」——
  那个 `ι` 被**假设**管着，是存在量词的见证，不是全称。它与同段已指出的「`:880` 的 `ι` 本身 η-依赖」
  是同一件事的两面：正因为 `ι` 由 `η` 与 `nexpd(η)` 选出，它才既不 η-free、也不能全称化。

  ⭐⭐ **但链侧不欠，而且连「搬」这个动作都没有。** `∀ k, nu (k + m) = -(nu k)` 在链上是
  **证出来的**，不依赖任何原文腿：`NormalCycleExists.exists_ncy_of_set`（`:740`）的形参表逐字只有
  `hfin` / `hm : 2 ≤ m` / `hzero` / `hneg` / `hpar` / `hcard : … = 2 * m`——**全是集合性质，
  一句原文都不引**（集成者第 197 轮亲读复核）。上面 ⚠ 的那两步（「凸 ⟹ `2m` 边恰 `m` 对 ±」、
  「环序 ⟹ 对径映射是无不动点保序对合 ⟹ 平移 `m`」）已经在 `exists_ncy_of_set` 内部形式化掉了。
  ⟹ **`anti` 不是转录债**：`:880` 只买**保真**（偏移量取值），**可证性**链上早就有。
  第 179 轮红线在这一条上也无关——红线管的是跨侧搬运，而这里没有跨侧。 -/
  anti : ∀ k, nu (k + m) = -(nu k)
  /-- `:424`「successor」的**朝向分量**。
  🔴 **订正（第 198–199 轮，集成者亲读）：本条初稿写「⚠ 原文无方向词，这一条是规范（§0.5）」，
  与本文件 §0 的第 198 轮订正自相矛盾，已作废。** 方向词在 `successor` 的**定义处** `:255`
  （"the boundary of `conv(S)` is **positively oriented**"），不在 `:424` 这个**使用处**——
  初稿只扫了使用句。⟹ 原文的 successor ＝ 逆时针 ＝ 本文件的 `σ = 1` 支。
  ⚠ 保留 `σ` 参数化不动：`σ = -1` 支仍是镜像收据（§7 的 `GL₂(ℤ)` 对合），接链时取 `σ = 1`。
  ⚠ 「positively oriented ＝ 逆时针」按 §50 记作**标准约定**（非内核、非我方加的量词）；
  `:255` 的前置条件「`conv(S)` 有正面积」在 `𝒮_φ` 上已核（`h_i` 方向两两不同 ＋ `m ≥ 2`）。
  ⚠ 全文 grep "counterclockwise/clockwise/ccw/cw" 零命中（lane-hole3-cone 实测），
  故此约定的出处在 Green 公式式的通用惯例，不在本文里；这是本条唯一的外部依赖。 -/
  step : ∀ k, 0 < σ * det (nu k) (nu (k + 1))
  /-- `:424`「the edge parallel to `ℓ_{i+1}` is a **successor** of the edge parallel to `ℓ_i`」
  的**枚举分量**：`N` 里没有任何 `y` 严格落在开楔形 `(nu k, nu (k+1))` 内。 -/
  hnoArc : ∀ k, ∀ y ∈ N, ¬ (0 < σ * det (nu k) y ∧ 0 < σ * det y (nu (k + 1)))
  /-- `:424`「`h_1, …, h_m` are vectors in **pairwise distinct directions**」＋ `:319`。
  同方向类 ⟺ 下标差恰为 `m`（同 `anti` 的中间推理），故下标差 `1 ≤ s < m` 时方向不同。 -/
  indep : ∀ k s, 1 ≤ s → s < m → det (nu k) (nu (k + s)) ≠ 0

namespace NormalCycle

variable {N : Set (ℤ × ℤ)} {m : ℕ} {σ : ℤ}

/-! ## §3  直接推论 -/

/-- `N` 在对径下闭（`:319`），而且见证就是下标平移 `m`：不需要额外字段。 -/
theorem neg_mem (C : NormalCycle N m σ) (k : ℕ) : -(C.nu k) ∈ N := by
  rw [← C.anti k]; exact C.mem _

/-- `anti` 蕴含周期 `2m`（`:424`「indices are taken modulo `2m`」），所以周期性不占字段。 -/
theorem periodic (C : NormalCycle N m σ) (k : ℕ) : C.nu (k + 2 * m) = C.nu k := by
  have h1 : k + 2 * m = (k + m) + m := by omega
  rw [h1, C.anti (k + m), C.anti k, neg_neg]

/-- **`:432` 的上界 `J ≤ ι + m - 1` 不是松的**：`s = m` 处 `det` 恰好为 `0`，
`indep` 自己的定义域到此为止。 -/
theorem det_at_m (C : NormalCycle N m σ) (i : ℕ) : det (C.nu i) (C.nu (i + m)) = 0 := by
  rw [C.anti i, ncy_det_neg_right, ncy_det_self, neg_zero]

theorem sigma_mul_ne_zero (C : NormalCycle N m σ) {x : ℤ} (h : x ≠ 0) : σ * x ≠ 0 := by
  rcases C.hsigma with rfl | rfl
  · simpa using h
  · simpa using h

/-! ## §4  台架：正八边形 `m = 4`，同一个 `N` 上两个 `σ` 都可满足（硬规矩 6） -/

end NormalCycle

/-- 正八边形的 8 个外法向。 -/
def ncyOctN : Set (ℤ × ℤ) :=
  {((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (1 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((-1 : ℤ), (1 : ℤ)),
   ((-1 : ℤ), (0 : ℤ)), ((-1 : ℤ), (-1 : ℤ)), ((0 : ℤ), (-1 : ℤ)), ((1 : ℤ), (-1 : ℤ))}

/-- 逆时针遍历的一个周期。 -/
def ncyOctBase : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (1, 1)
  | 2 => (0, 1)
  | 3 => (-1, 1)
  | 4 => (-1, 0)
  | 5 => (-1, -1)
  | 6 => (0, -1)
  | 7 => (1, -1)
  | _ => (1, 0)

/-- 顺时针遍历的一个周期：同一个 `ncyOctN`，反向走。 -/
def ncyOctBaseCw : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (1, -1)
  | 2 => (0, -1)
  | 3 => (-1, -1)
  | 4 => (-1, 0)
  | 5 => (-1, 1)
  | 6 => (0, 1)
  | 7 => (1, 1)
  | _ => (1, 0)

/-- 逆时针枚举，`ℕ` 下标。 -/
def ncyOctCcw (k : ℕ) : ℤ × ℤ := ncyOctBase (k % 8)

/-- 顺时针枚举，`ℕ` 下标。 -/
def ncyOctCw (k : ℕ) : ℤ × ℤ := ncyOctBaseCw (k % 8)

theorem ncy_mod8_add (k s : ℕ) (hs : s < 8) : (k + s) % 8 = (k % 8 + s) % 8 := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt hs]

theorem ncy_mod8_lt (k : ℕ) : k % 8 < 8 := Nat.mod_lt _ (by norm_num)

/-- **逆时针实例**：`σ = 1`。全部字段 `decide`。 -/
def ncyOctCycleCcw : NormalCycle ncyOctN 4 1 where
  hm := by norm_num
  hsigma := Or.inl rfl
  nu := ncyOctCcw
  mem := by
    intro k
    have key : ∀ r : ℕ, r < 8 → ncyOctBase r ∈ ncyOctN := by
      intro r hr
      interval_cases r <;>
        simp only [ncyOctBase, ncyOctN, Set.mem_insert_iff, Set.mem_singleton_iff] <;> norm_num
    exact key _ (ncy_mod8_lt k)
  ne_zero := by
    intro k
    have key : ∀ r : ℕ, r < 8 → ncyOctBase r ≠ 0 := by
      intro r hr; interval_cases r <;> decide
    exact key _ (ncy_mod8_lt k)
  anti := by
    intro k
    have key : ∀ r : ℕ, r < 8 → ncyOctBase ((r + 4) % 8) = -(ncyOctBase r) := by
      intro r hr; interval_cases r <;> decide
    simp only [ncyOctCcw, ncy_mod8_add k 4 (by norm_num)]
    exact key _ (ncy_mod8_lt k)
  step := by
    intro k
    have key : ∀ r : ℕ, r < 8 → 0 < (1 : ℤ) * det (ncyOctBase r) (ncyOctBase ((r + 1) % 8)) := by
      intro r hr; interval_cases r <;> decide
    simp only [ncyOctCcw, ncy_mod8_add k 1 (by norm_num)]
    exact key _ (ncy_mod8_lt k)
  hnoArc := by
    intro k y hy
    have key : ∀ r : ℕ, r < 8 → ∀ z ∈ ncyOctN,
        ¬ (0 < (1 : ℤ) * det (ncyOctBase r) z ∧
           0 < (1 : ℤ) * det z (ncyOctBase ((r + 1) % 8))) := by
      intro r hr z hz
      simp only [ncyOctN, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      interval_cases r <;>
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [ncyOctCcw, ncy_mod8_add k 1 (by norm_num)]
    exact key _ (ncy_mod8_lt k) y hy
  indep := by
    intro k s hs1 hs4
    have key : ∀ r : ℕ, r < 8 → ∀ t : ℕ, 1 ≤ t → t < 4 →
        det (ncyOctBase r) (ncyOctBase ((r + t) % 8)) ≠ 0 := by
      intro r hr t ht1 ht4
      interval_cases r <;> interval_cases t <;> decide
    simp only [ncyOctCcw, ncy_mod8_add k s (by omega)]
    exact key _ (ncy_mod8_lt k) s hs1 hs4

/-- **顺时针实例**：`σ = -1`，**同一个 `ncyOctN`**。
⟹ 朝向比特 `σ` 不是 `N` 的函数，它是规范（`PROTOCOL.md §54` 对合不变式法的一个实例）。 -/
def ncyOctCycleCw : NormalCycle ncyOctN 4 (-1) where
  hm := by norm_num
  hsigma := Or.inr rfl
  nu := ncyOctCw
  mem := by
    intro k
    have key : ∀ r : ℕ, r < 8 → ncyOctBaseCw r ∈ ncyOctN := by
      intro r hr
      interval_cases r <;>
        simp only [ncyOctBaseCw, ncyOctN, Set.mem_insert_iff, Set.mem_singleton_iff] <;> norm_num
    exact key _ (ncy_mod8_lt k)
  ne_zero := by
    intro k
    have key : ∀ r : ℕ, r < 8 → ncyOctBaseCw r ≠ 0 := by
      intro r hr; interval_cases r <;> decide
    exact key _ (ncy_mod8_lt k)
  anti := by
    intro k
    have key : ∀ r : ℕ, r < 8 → ncyOctBaseCw ((r + 4) % 8) = -(ncyOctBaseCw r) := by
      intro r hr; interval_cases r <;> decide
    simp only [ncyOctCw, ncy_mod8_add k 4 (by norm_num)]
    exact key _ (ncy_mod8_lt k)
  step := by
    intro k
    have key : ∀ r : ℕ, r < 8 →
        0 < (-1 : ℤ) * det (ncyOctBaseCw r) (ncyOctBaseCw ((r + 1) % 8)) := by
      intro r hr; interval_cases r <;> decide
    simp only [ncyOctCw, ncy_mod8_add k 1 (by norm_num)]
    exact key _ (ncy_mod8_lt k)
  hnoArc := by
    intro k y hy
    have key : ∀ r : ℕ, r < 8 → ∀ z ∈ ncyOctN,
        ¬ (0 < (-1 : ℤ) * det (ncyOctBaseCw r) z ∧
           0 < (-1 : ℤ) * det z (ncyOctBaseCw ((r + 1) % 8))) := by
      intro r hr z hz
      simp only [ncyOctN, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      interval_cases r <;>
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [ncyOctCw, ncy_mod8_add k 1 (by norm_num)]
    exact key _ (ncy_mod8_lt k) y hy
  indep := by
    intro k s hs1 hs4
    have key : ∀ r : ℕ, r < 8 → ∀ t : ℕ, 1 ≤ t → t < 4 →
        det (ncyOctBaseCw r) (ncyOctBaseCw ((r + t) % 8)) ≠ 0 := by
      intro r hr t ht1 ht4
      interval_cases r <;> interval_cases t <;> decide
    simp only [ncyOctCw, ncy_mod8_add k s (by omega)]
    exact key _ (ncy_mod8_lt k) s hs1 hs4

/-- **台架结论：同一个法向集上两个 `σ` 都可满足。** 所以
(a) `NormalCycle` 非空、非空真；(b) `σ` 不可从 `N` 推出；(c) 任何「原文读法是逆时针」的断言
都不是定理，只能是约定。
🔴 **(c) 第 198 轮订正**：`(c)` 的**内核部分**仍然成立——`σ` 确实不是 `N` 的函数，
所以「逆时针」永远不会是关于 `NormalCycle` 的**定理**。但 `(c)` 原本被用来支持
「原文没选边」，那个用法作废：`b3_colle2.txt:255` 把 `successor` 定义在正定向边界上
⟹ 原文选了逆时针。⟹ 正确表述是「不是定理，但是**原文的**约定，不是我方的」。 -/
theorem ncy_both_sigma_inhabited :
    Nonempty (NormalCycle ncyOctN 4 1) ∧ Nonempty (NormalCycle ncyOctN 4 (-1)) :=
  ⟨⟨ncyOctCycleCcw⟩, ⟨ncyOctCycleCw⟩⟩

namespace NormalCycle

variable {N : Set (ℤ × ℤ)} {m : ℕ} {σ : ℤ}

/-! ## §5  `:432` 的窗口：严格号沿整条枚举传播 -/

/-- **主定理。** `:432` 的窗口 `ι + 1 ≤ J ≤ ι + m - 1` 上，`σ * det ν_ι ν_J` 严格为正。

归纳一步用的只有 `hnoArc (i+s)` 喂 `y := -(nu i)`（由 `anti`+`mem` 免费在 `N` 里）＋ `indep`；
**相邻性只在 `s = 1` 的基例用一次**。几何上：若 `σ * det ν_ι ν_{ι+s+1} ≤ 0` 而
`σ * det ν_ι ν_{ι+s} > 0`，则 `-ν_ι` 严格落在开楔形 `(ν_{ι+s}, ν_{ι+s+1})` 内，
与 `:424` 的「successor」矛盾。 -/
theorem window_pos (C : NormalCycle N m σ) (i : ℕ) :
    ∀ s, 1 ≤ s → s < m → 0 < σ * det (C.nu i) (C.nu (i + s)) := by
  intro s
  induction s with
  | zero => intro h; exact absurd h (by omega)
  | succ t ih =>
    intro _ hsm
    rcases Nat.eq_zero_or_pos t with rfl | ht1
    · exact C.step i
    · have IH : 0 < σ * det (C.nu i) (C.nu (i + t)) := ih ht1 (by omega)
      have hne : det (C.nu i) (C.nu (i + (t + 1))) ≠ 0 := C.indep i (t + 1) (by omega) hsm
      have hgap := C.hnoArc (i + t) _ (C.neg_mem i)
      have e1 : det (C.nu (i + t)) (-(C.nu i)) = det (C.nu i) (C.nu (i + t)) := by
        simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
      have e2 : det (-(C.nu i)) (C.nu (i + t + 1)) = - det (C.nu i) (C.nu (i + t + 1)) := by
        simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
      have hfirst : 0 < σ * det (C.nu (i + t)) (-(C.nu i)) := by rw [e1]; exact IH
      have hsecond : ¬ (0 < σ * det (-(C.nu i)) (C.nu (i + t + 1))) := fun h => hgap ⟨hfirst, h⟩
      rw [e2, not_lt] at hsecond
      have hring : σ * -det (C.nu i) (C.nu (i + t + 1)) = -(σ * det (C.nu i) (C.nu (i + t + 1))) :=
        by ring
      rw [hring] at hsecond
      have hle : 0 ≤ σ * det (C.nu i) (C.nu (i + t + 1)) := by linarith
      have hz : σ * det (C.nu i) (C.nu (i + (t + 1))) ≠ 0 := C.sigma_mul_ne_zero hne
      have : (i : ℕ) + (t + 1) = i + t + 1 := by omega
      rw [this]
      rw [this] at hz
      exact lt_of_le_of_ne hle (Ne.symm hz)

/-- 非严格版本，包含 `s = 0`（`det ν_ι ν_ι = 0`）。下游 `⟪ν_{J-1}, p⟫ ≤ 0` 只要这一条。 -/
theorem window_nonneg (C : NormalCycle N m σ) (i : ℕ) :
    ∀ s, s < m → 0 ≤ σ * det (C.nu i) (C.nu (i + s)) := by
  intro s hs
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · rw [Nat.add_zero, ncy_det_self, mul_zero]
  · exact le_of_lt (C.window_pos i s hs1 hs)

/-! ## §6  交付：`⟪ν_{J-1}, p⟫ ≤ 0` -/

/-- **`⟪ν_{J-1}, p⟫ ≤ 0`**，其中 `p = -(dir ν_ι)`（`NOTATION.md`），`J = ι + t + 1`。

`t + 1 < m` 逐字就是 `:432` 的窗口 `ι + 1 ≤ J ≤ ι + m - 1`：`t` 跑遍 `0 … m-2`，
故 `J - 1 = ι + t` 跑遍 `ι … ι + m - 2`，`J` 跑遍 `ι+1 … ι+m-1`。

⚠ 带 `σ`：`σ = 1`（逆时针）时读作 `⟪ν_{J-1}, p⟫ ≤ 0`；`σ = -1` 时读作 `0 ≤ ⟪ν_{J-1}, p⟫`。
朝向不押（团队长纪律 1）。 -/
theorem dot_prev_p_nonpos (C : NormalCycle N m σ) (i t : ℕ) (ht : t + 1 < m) :
    σ * dot (C.nu (i + t)) (-(dir (C.nu i))) ≤ 0 := by
  have e : dot (C.nu (i + t)) (-(dir (C.nu i))) = det (C.nu (i + t)) (C.nu i) :=
    ncy_dot_neg_dir _ _
  have eskew : det (C.nu (i + t)) (C.nu i) = - det (C.nu i) (C.nu (i + t)) := by
    simp only [det]; ring
  have hnn : 0 ≤ σ * det (C.nu i) (C.nu (i + t)) := C.window_nonneg i t (by omega)
  rw [e, eskew]
  have : σ * -det (C.nu i) (C.nu (i + t)) = -(σ * det (C.nu i) (C.nu (i + t))) := by ring
  rw [this]
  linarith

/-- 逆时针读法下的形状，供消费者直接用。 -/
theorem dot_prev_p_nonpos_ccw (C : NormalCycle N m 1) (i t : ℕ) (ht : t + 1 < m) :
    dot (C.nu (i + t)) (-(dir (C.nu i))) ≤ 0 := by
  have h := C.dot_prev_p_nonpos i t ht
  linarith [h]

/-- 顺时针读法下的形状（号相反）。 -/
theorem dot_prev_p_nonneg_cw (C : NormalCycle N m (-1)) (i t : ℕ) (ht : t + 1 < m) :
    0 ≤ dot (C.nu (i + t)) (-(dir (C.nu i))) := by
  have h := C.dot_prev_p_nonpos i t ht
  nlinarith [h]

/-! ## §6.5  `e` / `d` / `D` 三分表在这个结构上塌成一条 `m` 的二分

`NOTATION.md`（内容锚点：三分判据那一行）的 `e := det ν_{J-1} ν_J`、`d := det ν_J ν_{J+1}`、
`D := det ν_{J-1} ν_{J+1}`，在 `NormalCycle` 里分别是下标差 `1`、`1`、`2`。⟹ 它们全部落在
`window_pos` 的定义域 `s < m` 内，**当且仅当** `m ≥ 3`（对 `D` 而言）。

这一节把 team-lead 第 186 轮第 3 条的举证责任兑现：`0 < D` 从此是「**相对 `NormalCycle`**」
的定理，不再是挂在未转录的 `hsym`/`hcons` 上的一句话。 -/

/-- `e := det ν_{J-1} ν_J` 的号，直接就是 `step`（`:424` 的朝向分量）。 -/
theorem e_pos (C : NormalCycle N m σ) (k : ℕ) : 0 < σ * det (C.nu k) (C.nu (k + 1)) :=
  C.step k

/-- `d := det ν_J ν_{J+1}` 的号，同上，平移一格。 -/
theorem d_pos (C : NormalCycle N m σ) (k : ℕ) : 0 < σ * det (C.nu (k + 1)) (C.nu (k + 2)) := by
  have h := C.step (k + 1)
  have e : k + 1 + 1 = k + 2 := by omega
  rwa [e] at h

/-- **`0 < D`（`m ≥ 3`）**，相对 `NormalCycle` 的转录成立。
下标差为 `2`，`window_pos` 要 `2 < m`。 -/
theorem D_pos (C : NormalCycle N m σ) (hm3 : 3 ≤ m) (k : ℕ) :
    0 < σ * det (C.nu k) (C.nu (k + 2)) :=
  C.window_pos k 2 (by omega) (by omega)

/-- **`m = 2` 时 `D = 0` 是定理，不是反例。**
下标差 `2` 恰好等于 `m`，落在 `det_at_m` 上。lane-leafa-shell 的正方形扇
`square_D_eq_zero` 正是这一点的一个具体见证：那不是「`0 < D` 错了」，
而是 `0 < D` 的定义域到 `m ≥ 3` 为止，而这个边界由 `:424` 的「`2m` 条边走半周」逼出来。 -/
theorem D_zero_of_m_two (C : NormalCycle N 2 σ) (k : ℕ) : det (C.nu k) (C.nu (k + 2)) = 0 :=
  C.det_at_m k

end NormalCycle

/-! ## §7  朝向比特是规范：显式 `GL₂(ℤ)` 对合（`PROTOCOL.md §54`） -/

/-- 镜像 `(x, y) ↦ (y, x)`，`GL₂(ℤ)` 的一个元素，`det = -1`。保 `ℤ²`、保 `dot`、翻 `det` 的号。 -/
def ncyMir (z : ℤ × ℤ) : ℤ × ℤ := (z.2, z.1)

theorem ncy_mir_invol (z : ℤ × ℤ) : ncyMir (ncyMir z) = z := by
  obtain ⟨a, b⟩ := z; simp [ncyMir]

theorem ncy_mir_neg (z : ℤ × ℤ) : ncyMir (-z) = -(ncyMir z) := by
  obtain ⟨a, b⟩ := z; simp [ncyMir]

theorem ncy_det_mir (a b : ℤ × ℤ) : det (ncyMir a) (ncyMir b) = - det a b := by
  simp only [det, ncyMir]; ring

theorem ncy_dot_mir (a b : ℤ × ℤ) : dot (ncyMir a) (ncyMir b) = dot a b := by
  simp only [dot, ncyMir]; ring

theorem ncy_mir_ne_zero {z : ℤ × ℤ} (h : z ≠ 0) : ncyMir z ≠ 0 := by
  intro hc
  apply h
  have := congrArg ncyMir hc
  rwa [ncy_mir_invol] at this

/-- **一条读法经镜像逐字变成另一条读法。** 八个字段一一对应，没有一条需要额外输入。
⟹ `σ` 不是任何输入的函数（§54 对合不变式法）；`:424` 的朝向词不是原文漏掉的信息。 -/
def NormalCycle.mirror {N : Set (ℤ × ℤ)} {m : ℕ} {σ : ℤ} (C : NormalCycle N m σ) :
    NormalCycle (ncyMir '' N) m (-σ) where
  hm := C.hm
  hsigma := by
    rcases C.hsigma with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl (by norm_num)
  nu := fun k => ncyMir (C.nu k)
  mem := fun k => ⟨C.nu k, C.mem k, rfl⟩
  ne_zero := fun k => ncy_mir_ne_zero (C.ne_zero k)
  anti := by
    intro k
    rw [C.anti k, ncy_mir_neg]
  step := by
    intro k
    rw [ncy_det_mir]
    have h : -σ * -det (C.nu k) (C.nu (k + 1)) = σ * det (C.nu k) (C.nu (k + 1)) := by ring
    rw [h]
    exact C.step k
  hnoArc := by
    rintro k y ⟨x, hx, rfl⟩
    rw [ncy_det_mir, ncy_det_mir]
    have h1 : -σ * -det (C.nu k) x = σ * det (C.nu k) x := by ring
    have h2 : -σ * -det x (C.nu (k + 1)) = σ * det x (C.nu (k + 1)) := by ring
    rw [h1, h2]
    exact C.hnoArc k x hx
  indep := by
    intro k s hs1 hsm
    rw [ncy_det_mir]
    have h := C.indep k s hs1 hsm
    intro hc
    exact h (by linarith)

/-! ## §8  `hnoArc` 就是主仓 `Arc … = ∅`：successor 那一半不必转录

team-lead 第 186 轮裁决 3：`:424` 的 successor 语义**已经是主仓现货**，转录派工缩小到
`:319` 的 `±` 闭、`:432` 的窗口、`:764` 那一半。本节把改写编译出来，供给方接口直通。

`Arc`（`PolyChainSum.lean:104`）的成员判定 `mem_Arc`（`PolyChainSum.lean:107`）逐字：

```
ν ∈ Arc hfin ν₀ n ↔ ν ∈ E T ∧ 0 < det ν₀ ν ∧ 0 < det ν n
```

取 `N := E T`、`σ = 1` 即与 `hnoArc` 互为改写。⚠ `Arc` 的 docstring 自己写的就是
「the edges of `T` strictly between `ν₀` and `n` in **counter-clockwise** order」
（`PolyChainSum.lean:98`），所以这个改写**只在逆时针支成立**，这也是 §9 把规范钉在
`σ = 1` 的第三个锚。

主仓供给方：`LeafAShellNNext.exists_w_hsweepW`（`LeafAShellNNext.lean:70`），同一条输出
还带 `0 < det J νJ1`（＝ `step`）和 `w = -(dir νJ1)`。
⟹ 任何要造 `NormalCycleCcw (E T) m` 的消费者，`step` 与 `hnoArc` 两个字段都有主仓现货，
**只剩 `anti` / `indep` 两条转录债**（§0.3 的表）。

`import` 安全性本轮独立复算：`PolyChainSum` 的传递 import 闭包 34 个模块，不含
`RegionSteps` / `ColleRegion` / `Case2WindowProbe` / `NfpLPreamble`（与 lane-leafa-shell
的计数一致）。 -/

/-- **`hnoArc`（`σ = 1`）与 `Arc … = ∅` 互为改写。** 双向，不是单向推出。 -/
theorem hnoArc_iff_arc_empty {T : Set (ℤ × ℤ)} (hfin : T.Finite) (a b : ℤ × ℤ) :
    (∀ y ∈ E T, ¬ (0 < (1 : ℤ) * det a y ∧ 0 < (1 : ℤ) * det y b)) ↔
      Nivat.PolyChainSum.Arc hfin a b = ∅ := by
  constructor
  · intro h
    ext ν
    constructor
    · intro hν
      obtain ⟨hm, h1, h2⟩ := Nivat.PolyChainSum.mem_Arc.mp hν
      exact absurd ⟨by linarith, by linarith⟩ (h ν hm)
    · intro hν
      simp at hν
  · rintro h y hy ⟨h1, h2⟩
    have hmem : y ∈ Nivat.PolyChainSum.Arc hfin a b :=
      Nivat.PolyChainSum.mem_Arc.mpr ⟨hy, by linarith, by linarith⟩
    rw [h] at hmem
    simp at hmem

/-- 消费者方向：拿着主仓的 `Arc … = ∅` 直接得到 `hnoArc` 字段。 -/
theorem hnoArc_of_arc_empty {T : Set (ℤ × ℤ)} (hfin : T.Finite) (a b : ℤ × ℤ)
    (h : Nivat.PolyChainSum.Arc hfin a b = ∅) :
    ∀ y ∈ E T, ¬ (0 < (1 : ℤ) * det a y ∧ 0 < (1 : ℤ) * det y b) :=
  (hnoArc_iff_arc_empty hfin a b).mpr h

/-! ## §9  逆时针支：接链用的形状

⚠ **规范已经选定，转录固定在逆时针支**（team-lead 第 186 轮裁决 2/4）。主仓本轮新增的锚，
都在法向侧：

1. `ColleReg.exists_preamble_pair`（`RegionSteps.lean:785`）恒出 `0 < det nℓ vl`
   （`¬hle` 支改交 `-v₀ = dir (-ℓ)`，两支都变成 `vl = dir nℓ`）；
2. `LeafAShellNNext.exists_nnextJ`（`LeafAShellNNext.lean:33`）恒要 `0 < det ℓ J`；
3. ⚠ **撤回（第 181 轮，lane-leafa-shell 指出，本轮亲读复核）**：原写「`PolyChainSum.Arc`
   （`PolyChainSum.lean:98` 的 docstring「counter-clockwise order」）」**不成立**。
   `PolyChainSum.lean:97-99` 的「counter-clockwise order」在 `/-! ## §2 -/` **节注释**里，
   不是 `Arc` 的 docstring；`Arc` 自己的 docstring（`PolyChainSum.lean:103`）逐字只有
   「`Arc T ν₀ n`, as a `Finset`.」，`def`（`PolyChainSum.lean:104-105`）逐字是
   `filter (fun ν => 0 < det ν₀ ν ∧ 0 < det ν n)`，**不含任何朝向**——两个参数对调即得
   互补弧。⟹ 这里的逆时针是**对参数顺序的读法约定**，比 docstring 还软，不许当锚用。
4. **替代锚（本轮亲读，比撤回的那条硬得多，且是链上 binder）**：
   `hsweepW : dot nJ w < 0`（`ChainDataGeom.ofPartsExhaustsInter`，`ChainExhaustInter.lean`；
   ⚠ **该 binder 表一律不写行号**（第 217 轮裁决）：它的行号偏移是**年代地层**
   （+127 / +118 / +43 / +130 四代并存），任何「整体加常数」的修法都会在某一代上错。
   此处旧写的 `:126` / `:121` 读回来是 `hfin` 而不是 `hsweepW`，属 `PROTOCOL.md` §57 的
   **B 类**，已随行号一并删）配主仓现货
   `LatticeEdges.dot_neg_dir_neg_lt_iff`（`LatticeEdges.lean:308`，无前提，两个量词都对
   `ℤ × ℤ` 全称）：`dot (-ν_J) (-(dir ν_{J+1})) < 0 ↔ 0 < det ν_J ν_{J+1}`。
   即在 `nJ = -ν_J`、`w = -(dir ν_{J+1})` 下，**`hsweepW` 逐字就是 `σ = 1` 在 `k = J` 这一步**。
   ⚠ 三条限定，别当白送：(i) 要 `w = -(dir ν_{J+1})`，生产者是
   `LeafAShellNNext.exists_w_hsweepW`（`LeafAShellNNext.lean:75`），它的主仓**项级**消费者
   自第 181 轮起存在（`WFanWiring.exists_w_fan_dichotomy`，`WFanWiring.lean:85`），但
   `WFanWiring` 自身尚无链上消费者；(ii) 这只钉住 `k = J` **一步**，推到全体 `k` 要先有
   「链上法向环是某个 `NormalCycle N m σ` 的 `nu`」这条实例化，而它尚未建（需要 `anti`，
   见 §0.3 债表）；(iii) ⟹ **`σ = 1` 的来源是 Lean binder，不是原文 `:424`**，`hsigma`
   的 docstring 那句「这不是原文的量词，是规范」继续有效，不许改成「原文字面」。
   佐证：`blueprint/NOTATION.md`（内容锚点：`:424` 的 successor 条目）明写「`b3_colle2.txt:424`
   逐字只说 successor，**没说顺时针还是逆时针**」。
   🔴 **上一句（(iii) 连同这条佐证）第 198 轮被推翻，见下面第 5 条。**

5. 🔴🔴 **订正（第 198 轮，集成者亲读原文）：`σ = 1` 有原文字面出处，上面 (iii) 那句「不是原文
   `:424`」是错的。错在只读了用 `successor` 的那句，没去读 `successor` 的定义处。**

   `b3_colle2.txt:255`（§2.1 Geometric notations，对一般凸 `S ⊂ ℤ²`）逐字：

   > If `S ⊂ ℤ²` is a convex set (possibly infinite) such that `conv(S)` has positive area,
   > **our standard convention is that the boundary of `conv(S)` is positively oriented**.
   > With this convention, each edge `w ∈ E(S)` inherits a natural orientation from the
   > boundary of `conv(S)`. If `|E(S)| < ∞`, our convention endows each `w ∈ E(S)` with a
   > well-defined **successor** edge `w_s ∈ E(S)` and a well-defined predecessor edge `w_p`.

   ⟹ `successor` 不是原文未定义的口语词，是 `:255` **定义过的术语**，且其定义把朝向钉死在
   「`conv(S)` 的边界取正定向」。而 `:424` / `:764` / `:541` / `:738` 四处枚举句用的
   **正是这个 `successor`**（同一篇、同一术语、`:255` 在前）。

   逐量词对应（三步，缺一不可）：
   (α) `:255`「positively oriented」＝平面区域边界的正定向＝**逆时针**。
       ⚠ §50 等级：这一步是**标准约定**（Green 定理那套），不是内核事实，也不是原文再说一遍；
       但它不是我们加的量词——原文自己选了「positively oriented」这个有标准含义的词。
   (β) 沿正定向遍历，`successor` 就是下一条边 ⟹ **下标 `i → i+1` 是逆时针**。
   (γ) 主仓侧：`0 < det a b ⟺ b 在 a 的逆时针侧`（`det u v = u.1*v.2 - u.2*v.1`），
       而 `σ = 1` 的读法逐字是「下标递增时 `0 < det (nu k) (nu (k+1))`」（见下面 📌 那条）。
   (α)(β)(γ) 合起来：**`σ = 1` ⟺ 原文的 successor 方向**。

   ⚠ **`S_φ` 确实满足 `:255` 的前提**：`φ = (X^{h_1}-1)⋯(X^{h_m}-1)`，`h_i` 方向两两不同、
   `m ≥ 2`（`:424`/`:764` 的前提）⟹ `S_φ` 是至少两个线性无关向量生成的 zonotope
   ⟹ `conv(S_φ)` 有正面积 ⟹ `:255` 的约定适用。
   ⚠ **`ℓ_i` 的朝向也一并钉死**：`:255` 说边从边界继承朝向，`:424`/`:764` 说 `ℓ_i` 平行于
   第 `i` 条边（作为**有向**直线）⟹ `ℓ_i` 的指向就是该边在正定向遍历下的指向。

   **这条推翻什么、不推翻什么**：
   - ✅ 推翻 (iii) 的「`σ = 1` 的来源是 Lean binder，不是原文」，以及 `NOTATION.md` 那条
     「没说顺时针还是逆时针」。两处本轮同步改。
   - ✅ 连带解禁第 179 轮红线里「旋向」「后继序」两格（`b3_colle2.txt:255` 是字面出处），
     以及「哪一格是 `ℓ_{ι−1}`」（＝`ℓ_ι` 的 predecessor，即逆时针方向退一步）。
   - ❌ **不推翻 §7**（见下），也**不改任何已证声明的语句**——本条只把 `σ = 1` 这个选择的
     **依据**从「我们的规范」升格成「原文的约定」，Lean 侧一行代码都不动。
   - ❌ 不解禁「`I` 增大是增角还是减角」里**依赖 Claim 4.10 的那半**：顺序禁令不变
     （`:860` 的 `𝒦` 来自 Claim 4.7 + Lemma 4.1，Claim 4.10 的证明 `:878` 用 `𝒦`
     ⟹ Claim 4.10 在 Claim 4.7 下游，而 `hstrict` 在 Claim 4.7 的消解里）。
     ⭐ 但纯下标方向本身现在有了独立来源：`:806` 的递归 `R_i := {g + t·v⃗_{ℓ_i} : g ∈ R_{i+1}}`
     配 `:810` 的 `R_{ι−1} ⊂ R_{ι−2} ⊂ ⋯ ⊂ R_{ι−m+1}` ⟹ **下标递减＝区域变大＝顺时针退**，
     与 (β) 一致，互为交叉验证，且这两行都在 Claim 4.7 **上游**，可当 binder。

⚠ **这不推翻 §7**：`NormalCycle.mirror` 证的是「孤立地看 `:424` 这一族前提，两读可互换」，
那条仍然成立，`ncy_both_sigma_inhabited` 也仍然成立。变的是：同一个规范里另有三处独立
携带朝向的量被钉死了，所以**接链时必须写在 `σ = 1` 支**——写成「两支任选」会与这三个锚
差一个号，而那个号是编译期错误，不是口径分歧。

📌 对 lane-tower-hbase 的 σ 对应（他要求写死一次）：
**`σ = 1` ⟺ 下标递增时 `0 < det (nu k) (nu (k+1))`**（就是 `step` 字段在 `σ = 1` 的读法）；
`σ = -1` ⟺ `det (nu k) (nu (k+1)) < 0`。
⚠ **订正（第 181 轮，lane-tower-hbase 指出）**：原写「他的 `hdetPos : 0 < det u' vl` 那支
对应 `σ = 1`」**是错的，已撤回**。`det u' vl` 的号决定的是 `towerIdx`
（`TowerConstruct.lean:374`）——即 `wtower` **正向还是反向读** `sortedCand`
（`TowerConstruct.lean:263`）——不是 σ。按他的 `sortedCand_det_pos_of_lt`
（`tmp/wip/lane-tower-hbase-sortdir.lean` §1；他的收据，本文件不复核、不背书）
`sortedCand` **无分支无条件** ccw，故 σ 恒为 1，与 `det u' vl` 的号无关；把 σ 挂到
`det u' vl` 上，会在 backward 支得出「`sortedCand` 是 CW」的错论。若要给 `wtower` 链
（而不是 `sortedCand`）定 σ，那才是反向支 σ = -1。 -/

/-- 逆时针支的简写。接链一律用这个。 -/
abbrev NormalCycleCcw (N : Set (ℤ × ℤ)) (m : ℕ) := NormalCycle N m 1

namespace NormalCycle

variable {N : Set (ℤ × ℤ)} {m : ℕ}

/-- `:432` 窗口，逆时针形。 -/
theorem window_pos_ccw (C : NormalCycleCcw N m) (i s : ℕ) (h1 : 1 ≤ s) (h2 : s < m) :
    0 < det (C.nu i) (C.nu (i + s)) := by
  have h := C.window_pos i s h1 h2
  linarith

/-- `⟪ν_{J-1}, p⟫ ≤ 0`，逆时针形，`p = -(dir ν_ι)`，`J = ι + t + 1`。
`t + 1 < m` 逐字是 `:432` 的 `ι+1 ≤ J ≤ ι+m-1`。 -/
theorem dot_prev_p_nonpos_ccw' (C : NormalCycleCcw N m) (i t : ℕ) (ht : t + 1 < m) :
    dot (C.nu (i + t)) (-(dir (C.nu i))) ≤ 0 := by
  have h := C.dot_prev_p_nonpos i t ht
  linarith

/-- `e := det ν_{J-1} ν_J > 0`，逆时针形。 -/
theorem e_pos_ccw (C : NormalCycleCcw N m) (k : ℕ) : 0 < det (C.nu k) (C.nu (k + 1)) := by
  have h := C.e_pos k
  linarith

/-- `d := det ν_J ν_{J+1} > 0`，逆时针形。 -/
theorem d_pos_ccw (C : NormalCycleCcw N m) (k : ℕ) :
    0 < det (C.nu (k + 1)) (C.nu (k + 2)) := by
  have h := C.d_pos k
  linarith

/-- `D := det ν_{J-1} ν_{J+1} > 0`（`m ≥ 3`），逆时针形。`m = 2` 时见 `D_zero_of_m_two`。 -/
theorem D_pos_ccw (C : NormalCycleCcw N m) (hm3 : 3 ≤ m) (k : ℕ) :
    0 < det (C.nu k) (C.nu (k + 2)) := by
  have h := C.D_pos hm3 k
  linarith

/-- 与主仓 `Arc` 直通：逆时针族的每一相邻对都给一个空 `Arc`。 -/
theorem arc_empty {T : Set (ℤ × ℤ)} (hfin : T.Finite) {m : ℕ}
    (C : NormalCycleCcw (E T) m) (k : ℕ) :
    Nivat.PolyChainSum.Arc hfin (C.nu k) (C.nu (k + 1)) = ∅ :=
  (hnoArc_iff_arc_empty hfin _ _).mp (C.hnoArc k)

end NormalCycle

end Nivat.LaneTowerHlevNormalCycle

open Nivat.LaneTowerHlevNormalCycle in
#print axioms ncy_det_dir_dir
open Nivat.LaneTowerHlevNormalCycle in
#print axioms ncy_dot_neg_dir
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.neg_mem
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.periodic
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.det_at_m
open Nivat.LaneTowerHlevNormalCycle in
#print axioms ncyOctCycleCcw
open Nivat.LaneTowerHlevNormalCycle in
#print axioms ncyOctCycleCw
open Nivat.LaneTowerHlevNormalCycle in
#print axioms ncy_both_sigma_inhabited
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.window_pos
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.window_nonneg
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.dot_prev_p_nonpos
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.dot_prev_p_nonpos_ccw
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.dot_prev_p_nonneg_cw
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.e_pos
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.d_pos
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.D_pos
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.D_zero_of_m_two
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.mirror
open Nivat.LaneTowerHlevNormalCycle in
#print axioms hnoArc_iff_arc_empty
open Nivat.LaneTowerHlevNormalCycle in
#print axioms hnoArc_of_arc_empty
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.window_pos_ccw
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.dot_prev_p_nonpos_ccw'
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.D_pos_ccw
open Nivat.LaneTowerHlevNormalCycle in
#print axioms NormalCycle.arc_empty
