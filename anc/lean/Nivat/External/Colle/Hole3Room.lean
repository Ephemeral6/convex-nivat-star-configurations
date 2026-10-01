/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ConeRecession
import Nivat.External.Colle.LatticeEdges

/-!
# 洞 3（`RegionSteps.lean:1934` 的 `have hroom`）的两步归约

原文：`scratch/b3_colle2.txt:824`（Claim 4.7 的**挑选条件** "for any translation `𝒯` of `𝒮`
where `𝒯 ∖ ℓ'_𝒯 ⊂ ℛ^N_I`, but `𝒯 ⊄ ℛ^N_I`"）＋ `:842`（"by using that `𝒮_φ` is η-generating"）
＋ `:848-856` 的 Figure 11(B) 图注。

⚠ **「房间」条件在原文里没有对应句**（第 169 轮集成者逐行核对 `:824-846`）。此前本行写的
`:826` 是错的：`:826` 开的是反证（"suppose, by contradiction, that there exists an integer
`t₀ ∈ ℤ_+` such that `N_𝒯(ℓ',γ)=1`"），`:826-846` 整段是周期性传播，落点是 `:844` 的
`𝓡^{N+1}_I` 与 `N` 的极大性矛盾，通篇没有房间条件。房间条件是**我们**为了把 `:838` 的
"by induction" 和 `:842` 的 "by using that `𝒮_φ` is η-generating" 写成 Lean 而补出来的：
要对 `𝓡^{N+1}_I` 里每个待定点跑一次生成集归纳，就得保证有一个 `𝒮_φ` 的平移，其余各点
全落在已知区域里。这是硬规矩 5 意义上的**我们的量词**，不是原文的；`Hole3Room` 里所有以
它为前提的引理都继承这一债务。

`Nivat.RecessionCone.room_of_cone`（`Nivat/External/Colle/ConeRecession.lean:135`）把房间条件
化归到 `hcone`：`𝒮_φ` 里每个使 `dot m (b-a) > 0` 的 `b`，其 `b - a` 都落进 `vl`、`w` 张成的锥。
本文件把 `hcone` 再往前推两步，最后只剩一条前提 `hwadj`：

```
hwadj  --nlmax_of_wadj-->  hnlmax  --room_of_nlmax-->  房间条件
```

合成结果是 `room_of_wadj`。

## 几何读法

`Rinf` 的两条半无限边经 `RecessionCone.recession_of_ray` 张成
`cone(vl, w) = {z | 0 ≤ dot m z ∧ dot nl z ≤ 0}`（用 `dot m w = 0 < dot m vl`、
`dot nl vl = 0 > dot nl w`）。`ha_min` 给了 `0 ≤ dot m (b - a)` 那一半；另一半
`dot nl (b - a) ≤ 0` 就是 `hnlmax`，即「`dot m`-最小点 `a` 同时是 `dot nl`-最大点」。
而 `hnlmax` 又只需要 `𝒮_φ` 的边法向都不落在 `-m` 与 `nl` 张成的开锥内部（`hwadj`）。

## 债务

`hwadj` 在本文件里是前提，**尚无生产者**。它的直观内容是「**`-w` 与 `vl`** 在 `𝒮_φ` 的边方向
循环序里相邻」（原文 `:810` 的扫掠序里 `w = v⃗_{ℓ_I}`、`vl = −v⃗_ℓ`）。

⚠ **本行此前写的是「`vl` 与 `w` 相邻」，差一个负号，已于第 171 轮更正**（lane-tower-hbase
发现，集成者独立复核）。算法：`dir v = (-v.2, v.1)`，取 `vl = (0,1)`、`w = (-1,0)`，六条符号
binder 逼出 `m = (0,1)`、`nl = (1,0)`，于是 `dir m = (-1,0) = w`、`dir nl = (0,1) = vl`。
`hwadj` 禁的开锥 `cone(-m, nl)` 经 `dir` 旋转落成 `cone(-w, vl)` ⟹ 它约束的是
**`vl` 与 `-w` 之间那段弧**，「`vl` 与 `w` 之间」是它的**补弧**。
`tmp/wip/lane-hroom-hcone-refute.lean` 给出的实例说明：塔包的全部**纯几何**合取都成立时
`hnlmax` 仍可为假，故 `hwadj` 的生产者只能来自带 `ξ` 的那几条合取（原文 `:838-846`）。
见 `blueprint/OPEN.md` #13 / #13d。

### ⛔ 第 169 轮：`hstrict` 不是新目标，它就是 `hcone`

`room_of_strict`（本文件 `:117`）曾被当作绕开 `hcone` 的入口。内核否掉了：其第二个合取经
Cramer 恒等式 `(det vl w)^2 * dot nl x = (det vl w * det vl x) * dot nl w` 归约，而
`hdet : det vl w ≠ 0` 与 `hwneg : dot nl w < 0` **两条都是严格的**，所以该步是**等价**而非单向
蕴含——`hstrict ⟺ hcone`。`tmp/wip/lane-hroom-hcone-refute.lean:178` 的反例
（`a = (1,0)`、`b = (2,1)`、`m = (0,1)`）满足 `dot m a = 0 < 1 = dot m b`，正落在 `hstrict`
的前件里，一个见证同时杀两条。第 168 轮「归约到 `hstrict` 可能重开纯几何路线」的说法作废。

### ↩ 第 171 轮整块撤回：`hwadj` **不假**。下面第 169 轮那段的计数错了一个负号

~~`hwadj` 在 `m ≥ 3` 时按原文自己的编号约定为假~~ —— **撤回**（lane-tower-hbase 自报并给内核
收据 `tmp/wip/lane-tower-hbase-sphi-frame.lean`，EXIT=0；集成者独立复核符号与下标，确认）。

错因：`hwadj` 禁的开锥是 `cone(-m, nl)`，经 `dir`（CCW 90°，`dir v = (-v.2, v.1)`）落成
`cone(-w, vl)`——约束的是 **`vl` 与 `-w`** 之间那段弧。下面数的 `m-2` 条是**补弧**上的。
代进下标：`ℛ_I` 是 `(-ℓ_ι, ℓ_{ι-1})`-region（`:760` 逐字：`ℓ'` ∥ `w_{ι+2m-1} = w_{ι-1}`），
`vl = -v⃗_{ℓ_ι}` ⟹ 方向是 `ℓ_{ι+m}`；`w = v⃗_{ℓ_{ι-1}}` ⟹ `-w` 方向是 `ℓ_{ι+m-1}`。
下标差 **1**，**对任意 `m` 都相邻** ⟹ `hwadj` 在原文构型下为**真**，依据是 `:764` 的相邻性，
不需要 `ξ`。

内核佐证（同一个 `m = 3` 的 `𝒮_φ = zono((1,0),(0,1),(1,1))`，七点，`SphiX_is_a_genuine_Sphi`
兑现了 `DecompData` 的 `Sphi_eq`/`Sphi_supp`/`Sphi_conv` 三条）：

| 框架 | `vl` | `w` | `-w` | `vl`↔`-w` 下标差 | `hnlmax` |
|---|---|---|---|---|---|
| 反例用的（第 153/161/169 轮） | `(0,1)` | `(-1,0)` | `(1,0)` | **2**（夹着 `(1,1)`） | **假** |
| `:760` 指定的 | `(-1,-1)` | `(1,0)` | `(-1,0)` | **1** | **真**（`hnlmaxS`，`a=(1,2)`） |

原文框架里 `hcone` 也直接成立（`hconeS`），`b - a` 根本不取 `(1,1)`，要付账的点全在窄锥里。
⟹ **此前所有 `hnlmax` / `hcone` / `hstrict` 的反例都建在下标差 2 的框架上，而那个框架被
`:760`+`:764` 排除。** 它们否掉的是「不带下标关系的签名」，不是原文的命题。

⟹ **洞 3 的真缺口由此改写**：不是「原文的房间条件为假」，是**塔包只导出纯符号事实
（`hw_det`/`hmw`/`hmvl`/`hperp`/`hwneg`），不含下标关系**，所以签名容得下被原文排除的框架。
缺的那一条 binder 是「`-w` 与 `vl` 在 `E ↑𝒮_φ` 的循环序里相邻」；桥是现成的
`nlmax_of_wadj`（本文件，同文件自引不写行号——见 `PROTOCOL.md` §57）。

⚠ 强度：内核证的是「在这**一个** `m = 3` 实例上，原文框架真、反例框架假」。
「对任意 `m` 原文框架都相邻」是上面那段下标算术，**无内核背书**（要背书得枚举 `E ↑𝒮_φ`）。
按这个强度引用。

### ✅ 第 172 轮：上面那条强度限定可以放宽——第 154 轮的见证里早有内核背书

集成者本轮逐点重算了第 154 轮两个反例文件的**下标构型**（不是转述 lane 的报告）。
`tmp/wip/lane-env-refute-MinIdx.lean` 同时测了两个 `w`，共用 `vlZ = (0,1)`（`:81`），
生成元 `(0,1),(-1,1),(-1,0),(-1,-1)`（`m = 4`，8 条边方向每 45° 一条）：

| 分支 | `w` | `vl`↔`w` 下标差 | `vl`↔`-w` 下标差 | `hwadj`（内核） |
|---|---|---|---|---|
| `wNarrow`（`:84`） | `(-1,0)` | 2 | **2** | **假**（`not_hwadj_narrow`，`:259`） |
| `wWide`（`:87`） | `(-1,-1)` | **3（`m=4` 能取到的最远）** | **1** | **真**（`hwadj_wide`，`:238`） |

**wide 分支里 `vl` 与 `w` 隔了 3 步——该塔上最远的一对——`hwadj` 照样成立。**
所以「`hwadj` ＝ `vl` 与 `w` 相邻」**在内核上直接为假**，不必依赖上面那段下标算术；
真假跟着 `vl`↔`-w` 走。这是与第 171 轮完全独立的第二条路线（`PROTOCOL.md §13`），
而且它 09-23 就在仓里，我们引用了三轮没看见。

⟹ 强度现在是：`m = 3`（本文件的实例、`#13f` 的 `SphiX`）与 `m = 4`（上表两行）
**四个内核实例**，全部满足「`hwadj` ⟺ `vl` 与 `-w` 下标差为 1」。仍**不是**对任意 `m` 的证明，
但「`hwadj` ≠ `vl` 与 `w` 相邻」这半句**已有内核背书，可以无保留引用**。

🔑 **负号是怎么丢的，写死在这里以免第四次**：`lane-env-refute-Hadj.lean:48` 第 154 轮
就把锥写对了——「`-m` 与 `nℓ` 恰是象限 `{n | dot n vl ≤ 0 ∧ dot n w ≤ 0}` 的两条边界射线」。
代入 `m = (0,1)`、`nl = (1,0)`：边界射线是 `nl = (1,0)` 与 `-m = (0,-1)`，经 `dir` 得
`dir nl = (0,1) = vl`、`dir (-m) = (1,0) = -w`，**象限的像就是 `cone(-w, vl)`**。
**在法向图景里从头到尾是对的；负号是在转述成方向图景时丢的**——即 `E(·)` 一名两物
（`blueprint/NOTATION.md`：原文 `b3_colle2.txt:253` 是**边**，Lean `LatticeEdges.lean:217` 是
**外法向**，差 90°）。**计数论证永远一致，方向论证静默旋转 90°**，所以它不会报错、只会静静地翻号。
⟹ 本文件此后每写一条相邻性，**先声明在哪个图景里**。

三个见证（`#13f`、`#13g` 的 narrow、第 169 轮）违反 `hwadj` 的边法向都是 `(1,-1)`，
而 `dir (1,-1) = (1,1)` ——恰是那条夹在 `-w` 与 `vl` 之间的边方向。同一机理，三次。

🛡 **不连坐**：`#13g` 自陈的「链的最小性（纯组合版）⟹ `hwadj`」为假**仍然成立**，
`#13f` 自陈的「`u'` 版 `hadj` 成立而 `hnlmax` 假」**仍然成立**。作废的只是第 164 轮
**从它们推出**的「`hnlmax` 本来就该假」。两条 lane 当时写的口径都是准的，是引用者越了界。

### ⛔ 第 169 轮（已被上面整块撤回，留作历史）：`hwadj` 在 `m ≥ 3` 时按原文自己的编号约定为假

`:764` 把 `ℓ₁,…,ℓ_{2m}` 排成「平行于 `ℓ_{i+1}` 的边是平行于 `ℓ_i` 的边的 successor」，`:255`
把 successor 的转向定死为正定向，于是相邻＝下标差 1。而 `ℛ_I` 按 `:806` 是
`(-ℓ_ι, ℓ_{ι-1})`-region，两条边界方向是 `ℓ_{ι+m}` 与 `ℓ_{ι-1}`，短弧间隔 `m-1`，**严格夹在
中间的边方向恰好 `m-2` 条**；原文扫掠对 `(v⃗_{ℓ_{I-1}}, v⃗_{ℓ_I})` 的间隔是 1。`m = 2` 时两者
重合，这就是低维一路自洽的原因。`𝒮_φ` 是 `2m` 条边齐全的 zonotope（`:317`、`:319`），那
`m-2` 个方向确实存在，所以 `m ≥ 3` 时 `hwadj` 是**假的**，不只是未证。
（计数只用 `:760` + `:764` + `:255` + `:319`，不用 `:812`。）

### ⚠ `hadj` 不是 `hwadj` / `hnlmax` 的生产者——符号方向相反（2026-09-24，第 161 轮）

消费点 `RegionSteps.lean:1934` 的 `have hroom` 处，作用域里**唯一**约束 `𝒮_φ` 边法向的
binder 是

```
hadj : ∀ n ∈ E ↑d.Sphi, ¬ (dot n vl < 0 ∧ 0 < dot n u')      -- RegionSteps.lean:1779
```

它与 `hwadj` 只差第二个合取项（`0 < dot n u'` 对 `dot n w < 0`），但**两者不互推，
而且方向相反**，所以不是「差一步」：

> `w` 落在 `u'` 与 `−vl` 张成的锥里（`TowerConstruct.lean:1009` 的 `det_pos_extChain`）。
> 写成 `w = α·u' + β·(−vl)`（`α, β ≥ 0`），则 `dot n vl < 0` 给 `−β·dot n vl ≥ 0`，
> 于是 `dot n w < 0` 逼出 `α·dot n u' < 0`，即 **`dot n u' < 0`**——而 `hadj` 禁的是
> `dot n u' > 0`。`hadj` 管的是弧的另一侧。

内核见证（`check1.sh` EXIT=0、`#print axioms` 全白名单，均在 `tmp/wip/`，未进 build）：
`Nivat.LaneTowerPkgHadj.hadj_does_not_imply_hwadj` 与 `…hadj_does_not_imply_hnlmax`
（`tmp/wip/lane-towerpkg-hadj-nowadj.lean`）在同一实例上兑现 11 条几何 binder
（`hmw`/`hmvl`/`hperp`/`hwneg`/`hdet`/`hnu`/`hunimod`/`hprim`/`a ∈ 𝒮_φ`/`ha_min`/`ha_end`），
证明 `hadj` **成立**而 `hwadj`、`hnlmax` **都为假**。实例：`vl = (0,1)`、`w = (-1,0)`、
`m = (0,1)`、`nl = (1,0)`、`u' = (-1,0)`、`a = (1,0)`、`𝒮_φ` = 生成元 `(1,0),(1,1),(0,1)`
的 zonotope 格点；`hwadj` 的见证是边法向 `(1,-1)`，`hnlmax` 的见证是 `b = (2,1)`。
`…hnlmax_fails_all_nl` 进一步说明这不是「`nl` 挑错了」：`hperp` + `hwneg` 在该实例上把
`nl` 钉成 `(t, 0)`、`t > 0`，整族都不行。

⚠ 限定（`PROTOCOL.md §41`）：以上**不**断言 `hroom` 为假。那 11 条不含
`hξ` / `hgen` / `hgenφ`，带 `hξ : IsMinimalCounterexample ξ` 的命题不派证伪（空真）。
断言的只是：**`hadj` 这条通路死了**，下一个 lane 不要再往这个方向撞。

### 归约已接到消费者的逐字符签名上

`tmp/wip/lane-towerpkg-hroom-nlmax.lean` 把 `room_of_nlmax` / `room_of_wadj` 接到
`RegionSteps.lean:1934-1938` 那条 `have hroom` 的**逐字符结论**与该处作用域里现成的
48 条 binder 上（`hroom_target_of_nlmax` / `hroom_target_of_wadj`），并把结果插回
`:1942` 的 `step_all_of_hroom` 槽位（`hstep_all_of_nlmax`），三条都 0 sorry、公理白名单。
效果：链上 `:1938` 的 `sorry` 与 `hnlmax` 这**一条**命题等价可换。
-/

set_option autoImplicit false

namespace Nivat.Hole3Room

open Nivat Nivat.LE2

/-! ## 1. `hnlmax ⟹ hcone ⟹ 房间条件` -/

/-- `dot` 对右边的标量乘法是线性的（`dot_smul` 只给了左边，这里用 `dot_comm` 搬到右边）。 -/
private theorem dot_smul_right (n : ℤ × ℤ) (g : ℤ) (z : ℤ × ℤ) :
    dot n (g • z) = g * dot n z := by
  rw [dot_comm, dot_smul, dot_comm z n]

/-- Cramer 恒等式两边取 `dot m ·`，用 `hmw : dot m w = 0` 化简掉一项。 -/
private theorem dot_m_cramer (vl w m x : ℤ × ℤ) (hmw : dot m w = 0) :
    det vl w * dot m x = det x w * dot m vl := by
  have hc := Nivat.RecessionCone.cramer_smul vl w x
  have := congrArg (dot m) hc
  simp only [dot_add, dot_smul_right, hmw, mul_zero, add_zero] at this
  linarith

/-- Cramer 恒等式两边取 `dot nl ·`，用 `hperp : dot nl vl = 0` 化简掉一项。 -/
private theorem dot_nl_cramer (vl w nl x : ℤ × ℤ) (hperp : dot nl vl = 0) :
    det vl w * dot nl x = det vl x * dot nl w := by
  have hc := Nivat.RecessionCone.cramer_smul vl w x
  have := congrArg (dot nl) hc
  simp only [dot_add, dot_smul_right, hperp, mul_zero, zero_add] at this
  linarith

/-- **房间归约第一步的真正形态**（第 167 轮）：只需要「`dot m` **严格**更高的 `b` 不把
`dot nl` 抬过 `a`」。

与 `room_of_nlmax` 的唯一差别是 `hstrict` 多带一条前件 `dot m a < dot m b`；而结论本身就在
`0 < dot m (b - a)` 之下讨论，所以这条前件在调用处**白拿**。

⚠ 对原文的态度：点 `a` **不是 `scratch/b3_colle2.txt:806-870` 的对象**（那一段只有 `ℛ_i`、
`ℛ^n_I`、`N`、`h`、`𝒯`），它是 `RegionSteps.lean:1819-1826` 我们自己按字典序极值造的。
按硬规矩 5，凡是加在 `a` 上的额外要求都要先问「哪个量词是我们加的」——本条就是把多加的那半
（极小层上的极大性，由 `NlmaxReduce.nlmax_on_min_level` 白送）摘掉之后剩下的部分。 -/
theorem room_of_strict
    {Rinf : Set (ℤ × ℤ)} {vl w m nl a : ℤ × ℤ} {Sφ : Finset (ℤ × ℤ)}
    (hconv : Nivat.IsLatticeConvexRegion Rinf)
    (hvl : ∀ z ∈ Rinf, z + vl ∈ Rinf) (hw : ∀ z ∈ Rinf, z + w ∈ Rinf)
    (hdet : Nivat.det vl w ≠ 0)
    (hmw : Nivat.LE2.dot m w = 0) (hmvl : 0 < Nivat.LE2.dot m vl)
    (hperp : Nivat.LE2.dot nl vl = 0) (hwneg : Nivat.LE2.dot nl w < 0)
    (hstrict : ∀ b ∈ Sφ, Nivat.LE2.dot m a < Nivat.LE2.dot m b →
      Nivat.LE2.dot nl b ≤ Nivat.LE2.dot nl a) :
    ∀ q ∈ Rinf, ∀ b ∈ Sφ, 0 < Nivat.LE2.dot m (b - a) → q + (b - a) ∈ Rinf := by
  refine Nivat.RecessionCone.room_of_cone hconv hvl hw hdet ?_
  intro b hb hpos
  set x : ℤ × ℤ := b - a with hx
  constructor
  · -- `0 ≤ det vl w * det x w`
    have hEq := dot_m_cramer vl w m x hmw
    have hEq2 : (det vl w) ^ 2 * dot m x = (det vl w * det x w) * dot m vl := by
      linear_combination det vl w * hEq
    have hlhs : 0 ≤ (det vl w) ^ 2 * dot m x := by
      have : (0:ℤ) ≤ (det vl w) ^ 2 := sq_nonneg _
      exact mul_nonneg this (le_of_lt hpos)
    by_contra hcon
    push Not at hcon
    have : (det vl w * det x w) * dot m vl < 0 :=
      mul_neg_of_neg_of_pos hcon hmvl
    linarith
  · -- `0 ≤ det vl w * det vl x`
    have hEq := dot_nl_cramer vl w nl x hperp
    have hEq2 : (det vl w) ^ 2 * dot nl x = (det vl w * det vl x) * dot nl w := by
      linear_combination det vl w * hEq
    have hnlx : dot nl x ≤ 0 := by
      have hmlt : dot m a < dot m b := by
        have hxm : dot m x = dot m b - dot m a := by simp only [hx, dot_sub]
        linarith [hpos, hxm]
      have := hstrict b hb hmlt
      simp only [hx, dot_sub]
      linarith
    have hlhs : (det vl w) ^ 2 * dot nl x ≤ 0 := by
      have h2 : (0:ℤ) ≤ (det vl w) ^ 2 := sq_nonneg _
      exact mul_nonpos_of_nonneg_of_nonpos h2 hnlx
    by_contra hcon
    push Not at hcon
    have : (det vl w * det vl x) * dot nl w > 0 :=
      mul_pos_of_neg_of_neg hcon hwneg
    linarith

/-- **房间归约第一步**（`scratch/b3_colle2.txt:824` 的挑选条件、`:848-856` Figure 11(B)）：
`nl`-极大性给出房间条件。

`nl` 是与 `vl` 垂直（`hperp`）、在 `w` 方向上为负（`hwneg`，即朝 `Rinf` 外侧）的法向；
`hnlmax` 说它在 `a` 处于 `𝒮_φ` 上取极大。`m` 是与 `w` 垂直（`hmw`）、在 `vl` 方向上为正
（`hmvl`）的法向，用来挑出「朝上」的 `b`（`0 < dot m (b - a)`）。

推导：对 `x := b - a` 用 Cramer 恒等式 `det vl w • x = det x w • vl + det vl x • w`
分别取 `dot m ·` 与 `dot nl ·`：
* `det vl w * dot m x = det x w * dot m vl`（`hmw` 杀掉 `w`-项）；`dot m x > 0`、
  `dot m vl > 0`，两边再乘 `det vl w` 得
  `(det vl w)^2 * dot m x = (det vl w * det x w) * dot m vl`，左边 `≥ 0`，`dot m vl > 0`，
  故 `0 ≤ det vl w * det x w`。
* `det vl w * dot nl x = det vl x * dot nl w`（`hperp` 杀掉 `vl`-项）；`dot nl x ≤ 0`
  （由 `hnlmax`）、`dot nl w < 0`，两边再乘 `det vl w` 得
  `(det vl w)^2 * dot nl x = (det vl w * det vl x) * dot nl w`，左边 `≤ 0`，`dot nl w < 0`，
  故 `0 ≤ det vl w * det vl x`。

两条合起来正是 `RecessionCone.room_of_cone` 的 `hcone`，直接调用即得结论。

── 2026-09-24（第 167 轮，集成者）：本条现由 `room_of_strict` 导出 ──
证明里 `hnlmax` **只在 `hpos : 0 < dot m (b - a)` 的那个 `b` 上用了一次**（原 `:156`），
所以真正需要的前提是严格更弱的 `hstrict`。`room_of_strict` 直接吃 `hstrict`，本条保留为它的
推论（`strict_of_nlmax` 的特例），旧消费者签名不变。 -/
theorem room_of_nlmax
    {Rinf : Set (ℤ × ℤ)} {vl w m nl a : ℤ × ℤ} {Sφ : Finset (ℤ × ℤ)}
    (hconv : Nivat.IsLatticeConvexRegion Rinf)
    (hvl : ∀ z ∈ Rinf, z + vl ∈ Rinf) (hw : ∀ z ∈ Rinf, z + w ∈ Rinf)
    (hdet : Nivat.det vl w ≠ 0)
    (hmw : Nivat.LE2.dot m w = 0) (hmvl : 0 < Nivat.LE2.dot m vl)
    (hperp : Nivat.LE2.dot nl vl = 0) (hwneg : Nivat.LE2.dot nl w < 0)
    (hnlmax : ∀ b ∈ Sφ, Nivat.LE2.dot nl b ≤ Nivat.LE2.dot nl a) :
    ∀ q ∈ Rinf, ∀ b ∈ Sφ, 0 < Nivat.LE2.dot m (b - a) → q + (b - a) ∈ Rinf :=
  room_of_strict hconv hvl hw hdet hmw hmvl hperp hwneg (fun b hb _ => hnlmax b hb)

/-! ## 2. `hwadj ⟹ hnlmax` -/

/-- **房间归约第二步**（`scratch/b3_colle2.txt:824` 的挑选条件、`:848-856` Figure 11(B) 的角点 `a`）：
若 `𝒮_φ` 没有边法向落在 `-m` 与 `nl` 张成的开锥内部（`hwadj`），则 `dot m`-最小点 `a`
（由 `ha_min` / `ha_end` 钉死）同时是 `dot nl`-最大点。

证法（纯组合，不用凸性/zonotope 结构）：反证，设 `v ∈ 𝒮_φ` 严格超过 `a`
（`dot nl v > dot nl a`）。对 `c ∈ 𝒮_φ` 记 `Δm c := dot m c - dot m a ≥ 0`（`ha_min`）、
`Δnl c := dot nl c - dot nl a`。在 `T := {c ∈ 𝒮_φ | 0 < Δnl c}`（非空，含 `v`）中取使有理数
`Δm c / (Δm c + Δnl c)` 最小的 `c`（即「`-m` 转向 `nl` 的过程中第一个追上 `a` 的点」）。
用 `ha_end` + `dot nl w < 0` 排除 `Δm c = 0` 的退化情形，再用最小性做交叉相乘，得到对所有
`z ∈ 𝒮_φ`：`Δm c * Δnl z ≤ Δnl c * Δm z`。这恰是整数法向
`N := Δnl c • (-m) + Δm c • nl` 满足 `dot N z ≤ dot N a`（等号在 `z = a, c` 处成立，`a ≠ c`）
的代数改写，故 `N` 的本原化 `primPart N` 是 `𝒮_φ` 的一条边法向。直接计算给出
`dot N vl = -Δnl c * dot m vl < 0`（用 `hperp`）、`dot N w = Δm c * dot nl w < 0`（用 `hmw`），
同号传到 `primPart N`（正数倍），与 `hwadj` 矛盾。 -/
theorem nlmax_of_wadj
    {vl w m nl a : ℤ × ℤ} {Sφ : Finset (ℤ × ℤ)}
    (hmw : dot m w = 0) (hmvl : 0 < dot m vl)
    (hperp : dot nl vl = 0) (hwneg : dot nl w < 0)
    (hdet : det vl w ≠ 0)
    (hwadj : ∀ n ∈ Nivat.LE2.E (↑Sφ : Set (ℤ × ℤ)),
      ¬ (dot n vl < 0 ∧ dot n w < 0))
    (ha : a ∈ Sφ)
    (ha_min : ∀ b ∈ Sφ, dot m a ≤ dot m b)
    (ha_end : ∀ b ∈ Sφ, dot m b = dot m a →
      ∃ t : ℕ, b = a + (t : ℤ) • w) :
    ∀ b ∈ Sφ, dot nl b ≤ dot nl a := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨v, hvS, hvgt⟩ := hcon
  -- `T` : competitors that strictly beat `a` in the `nl` direction.
  set T : Finset (ℤ × ℤ) := Sφ.filter (fun c => 0 < dot nl c - dot nl a) with hT_def
  have hvT : v ∈ T := by
    rw [hT_def, Finset.mem_filter]
    refine ⟨hvS, ?_⟩
    omega
  have hTne : T.Nonempty := ⟨v, hvT⟩
  obtain ⟨c, hcT, hcmin⟩ := T.exists_min_image
      (fun z => (dot m z - dot m a : ℚ) / ((dot m z - dot m a : ℚ) + (dot nl z - dot nl a : ℚ)))
      hTne
  obtain ⟨hcS, hΔnl_c_pos⟩ := Finset.mem_filter.mp hcT
  -- Non-negativity of `Δm` over `Sφ` (`ha_min`).
  have hΔm_nonneg : ∀ z ∈ Sφ, 0 ≤ dot m z - dot m a := by
    intro z hz; have := ha_min z hz; omega
  -- **Claim 1**: `Δm c > 0` — the degenerate case is excluded by `ha_end` + `hwneg`.
  have hΔm_c_pos : 0 < dot m c - dot m a := by
    rcases lt_or_eq_of_le (hΔm_nonneg c hcS) with h | h
    · exact h
    · exfalso
      obtain ⟨t, ht⟩ := ha_end c hcS (by omega)
      have hdotc : dot nl c = dot nl a + (t : ℤ) * dot nl w := by
        rw [ht, dot_add]
        congr 1
        rw [dot_comm, dot_smul, dot_comm nl w]
      have ht_nonneg : (0 : ℤ) ≤ (t : ℤ) := by positivity
      nlinarith [hwneg, hΔnl_c_pos, hdotc]
  -- **Claim 2** (global tightness): for every `z ∈ Sφ`,
  -- `(dot m c - dot m a) * (dot nl z - dot nl a) ≤ (dot nl c - dot nl a) * (dot m z - dot m a)`.
  have hkey : ∀ z ∈ Sφ,
      (dot m c - dot m a) * (dot nl z - dot nl a) ≤
        (dot nl c - dot nl a) * (dot m z - dot m a) := by
    intro z hz
    by_cases hzT : 0 < dot nl z - dot nl a
    · -- `z ∈ T`: cross-multiply the minimality of `c`'s fraction.
      have hzT' : z ∈ T := by
        rw [hT_def, Finset.mem_filter]; exact ⟨hz, hzT⟩
      have hcross := hcmin z hzT'
      have hDc : (0 : ℚ) < (dot m c - dot m a : ℚ) + (dot nl c - dot nl a : ℚ) := by
        have h1 : (0:ℚ) ≤ (dot m c - dot m a : ℚ) := by exact_mod_cast hΔm_nonneg c hcS
        have h2 : (0:ℚ) < (dot nl c - dot nl a : ℚ) := by exact_mod_cast hΔnl_c_pos
        linarith
      have hDz : (0 : ℚ) < (dot m z - dot m a : ℚ) + (dot nl z - dot nl a : ℚ) := by
        have h1 : (0:ℚ) ≤ (dot m z - dot m a : ℚ) := by exact_mod_cast hΔm_nonneg z hz
        have h2 : (0:ℚ) < (dot nl z - dot nl a : ℚ) := by exact_mod_cast hzT
        linarith
      rw [div_le_div_iff₀ hDc hDz] at hcross
      have : (dot m c - dot m a : ℚ) * (dot nl z - dot nl a) ≤
          (dot nl c - dot nl a : ℚ) * (dot m z - dot m a) := by nlinarith [hcross]
      exact_mod_cast this
    · -- `z ∉ T`: LHS is `≤ 0`, RHS is `≥ 0`.
      push_neg at hzT
      have h1 : (dot m c - dot m a) * (dot nl z - dot nl a) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hΔm_c_pos.le hzT
      have h2 : (0:ℤ) ≤ (dot nl c - dot nl a) * (dot m z - dot m a) :=
        mul_nonneg hΔnl_c_pos.le (hΔm_nonneg z hz)
      linarith
  -- The integer normal witnessing the forbidden edge.
  set N : ℤ × ℤ := (dot nl c - dot nl a) • (-m) + (dot m c - dot m a) • nl with hN_def
  have hdotN : ∀ z : ℤ × ℤ,
      dot N z = -(dot nl c - dot nl a) * dot m z + (dot m c - dot m a) * dot nl z := by
    intro z
    simp only [hN_def, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_neg, Prod.snd_neg, smul_eq_mul]
    ring
  have hNvl : dot N vl = -(dot nl c - dot nl a) * dot m vl := by
    rw [hdotN, hperp]; ring
  have hNw : dot N w = (dot m c - dot m a) * dot nl w := by
    rw [hdotN, hmw]; ring
  have hNvl_neg : dot N vl < 0 := by
    rw [hNvl]; nlinarith [hΔnl_c_pos, hmvl]
  have hNw_neg : dot N w < 0 := by
    rw [hNw]; nlinarith [hΔm_c_pos, hwneg]
  have hNa_ge : ∀ z ∈ Sφ, dot N z ≤ dot N a := by
    intro z hz
    rw [hdotN, hdotN]
    nlinarith [hkey z hz]
  have hNc_eq : dot N c = dot N a := by
    rw [hdotN, hdotN]; ring
  have hac : a ≠ c := by
    intro h; rw [← h] at hΔnl_c_pos; omega
  have hN_ne : N ≠ 0 := by
    intro h
    rw [h] at hNvl_neg
    simp [dot] at hNvl_neg
  obtain ⟨hprim, g, hg, hgeq⟩ := primPart_spec hN_ne
  have hface_eq : Nivat.LE2.face (↑Sφ : Set (ℤ × ℤ)) N
      = Nivat.LE2.face (↑Sφ : Set (ℤ × ℤ)) (primPart N) := by
    conv_lhs => rw [hgeq]
    exact Nivat.LE2.face_smul hg _
  have haF : a ∈ Nivat.LE2.face (↑Sφ : Set (ℤ × ℤ)) N := by
    rw [Nivat.LE2.mem_face_iff]
    exact ⟨ha, fun y hy => hNa_ge y hy⟩
  have hcF : c ∈ Nivat.LE2.face (↑Sφ : Set (ℤ × ℤ)) N := by
    rw [Nivat.LE2.mem_face_iff]
    refine ⟨hcS, fun y hy => ?_⟩
    rw [hNc_eq]; exact hNa_ge y hy
  have hnontriv : (Nivat.LE2.face (↑Sφ : Set (ℤ × ℤ)) (primPart N)).Nontrivial := by
    rw [← hface_eq]
    exact ⟨a, haF, c, hcF, hac⟩
  have hgR : (0:ℤ) < g := hg
  have hν_vl : dot (primPart N) vl < 0 := by
    have : dot N vl = g * dot (primPart N) vl := by
      conv_lhs => rw [hgeq]
      exact dot_smul g (primPart N) vl
    nlinarith [hNvl_neg, this, hgR]
  have hν_w : dot (primPart N) w < 0 := by
    have : dot N w = g * dot (primPart N) w := by
      conv_lhs => rw [hgeq]
      exact dot_smul g (primPart N) w
    nlinarith [hNw_neg, this, hgR]
  have hνE : primPart N ∈ Nivat.LE2.E (↑Sφ : Set (ℤ × ℤ)) := ⟨hprim, hnontriv⟩
  exact hwadj (primPart N) hνE ⟨hν_vl, hν_w⟩

/-! ## 3. 合成：洞 3 的全部债务收缩成一条 `hwadj` -/

/-- **洞 3 的合成归约**（`RegionSteps.lean:1934` 的 `have hroom`；原文
`scratch/b3_colle2.txt:824` 的挑选条件、`:848-856` Figure 11(B)）。

把 `nlmax_of_wadj` 与 `room_of_nlmax` 串起来：在 `Rinf` 的两条半无限边方向 `vl`、`w`
（`hvl` / `hw` / `hdet`）与两条法向 `m`、`nl`（`hmw` / `hmvl` / `hperp` / `hwneg`）给定后，
房间条件**只需要** `hwadj`——即 `𝒮_φ` 的边法向都不落在 `-m` 与 `nl` 张成的开锥内部，
几何上就是「`vl` 与 `w` 在 `𝒮_φ` 的边方向循环序里于顶点 `a` 处相邻」。

`hwadj` 本身尚无生产者，见本文件头部的「债务」一节与 `blueprint/OPEN.md` #13。 -/
theorem room_of_wadj
    {Rinf : Set (ℤ × ℤ)} {vl w m nl a : ℤ × ℤ} {Sφ : Finset (ℤ × ℤ)}
    (hconv : Nivat.IsLatticeConvexRegion Rinf)
    (hvl : ∀ z ∈ Rinf, z + vl ∈ Rinf) (hw : ∀ z ∈ Rinf, z + w ∈ Rinf)
    (hdet : Nivat.det vl w ≠ 0)
    (hmw : dot m w = 0) (hmvl : 0 < dot m vl)
    (hperp : dot nl vl = 0) (hwneg : dot nl w < 0)
    (hwadj : ∀ n ∈ Nivat.LE2.E (↑Sφ : Set (ℤ × ℤ)),
      ¬ (dot n vl < 0 ∧ dot n w < 0))
    (ha : a ∈ Sφ)
    (ha_min : ∀ b ∈ Sφ, dot m a ≤ dot m b)
    (ha_end : ∀ b ∈ Sφ, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w) :
    ∀ q ∈ Rinf, ∀ b ∈ Sφ, 0 < dot m (b - a) → q + (b - a) ∈ Rinf :=
  room_of_nlmax hconv hvl hw hdet hmw hmvl hperp hwneg
    (nlmax_of_wadj hmw hmvl hperp hwneg hdet hwadj ha ha_min ha_end)

end Nivat.Hole3Room

#print axioms Nivat.Hole3Room.room_of_strict
#print axioms Nivat.Hole3Room.room_of_nlmax
#print axioms Nivat.Hole3Room.nlmax_of_wadj
#print axioms Nivat.Hole3Room.room_of_wadj
