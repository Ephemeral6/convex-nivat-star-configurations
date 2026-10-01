/-
Copyright (c) 2026 Nivat Formalization Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lane-leafa-gen
-/
import Nivat.External.Colle.PartsToGeom

/-!
# (G-a) `rec_vJ` 的生产者：`ChainDataGeomParts` 的字段够用（lane-leafa-gen，team-lead 第 197 轮派工）

⚠ **2026-09-26 订正（lane-env-refute，集成者裁决 (5) 授权，只改注释不动声明）**：
本文件原先写的「24 个字段」「第 25 条」是陈旧计数。`ChainDataGeomParts` 的字段数经内核
`run_cmd` 实测为 **37**（⛔ 不要用正则数，非 ASCII 下标如 `I₀` 会被漏掉）。下文凡出现
「24 个字段」一律读作「`ChainDataGeomParts` 的全部字段（37 条）」，结论与证明不受影响。
本条只改计数措辞，文内的 `文件名:行号` 锚点一律原样保留（PROTOCOL §99）——其中
`ChainPartsFeed.lean:201` / `:202` / `:218` 三处经我复核**已经腐烂**（`hhp` / `hswept` /
`hsweep` 现分别在 `:292` / `:293` / `:290`），留给文件作者按 §123 处理。

派工目标逐字：`∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i`，
消费者是 `PartsToGeom.lean:43` 的显式参数 `rec_vJ`。

**结论：`ChainDataGeomParts` 的字段（37 条）够用，不欠新几何义务。** 见 `rec_vJ_of_parts`。

## 1. 为什么以前以为不够（订正一条既有记载）

派工单列的死路 1 只说对了一半。`rec_vJ_of_exists_chainData_layer`（`ChainPartsFeed.lean:118`）
的结论 `IsLatticeConvexRegion (⋃ i, hatOf A kk vl i)` 确实**单独**推不出 `rec_vJ`
（有界集反例，`ChainPartsFeed.lean:269` 的 🔴 订正），这条我复核无误。
但它不是单独用的：`Nivat.Colle35.rec_vJ_of_bottom`（`ItemII.lean:766`，树中已证）把它
**配上另外五条**就给出 `rec_vJ`，而那五条**逐条都是 `ChainDataGeomParts` 的字段**：

| `rec_vJ_of_bottom` 的形参 | 来源 |
|---|---|
| `hconv : IsLatticeConvexRegion (⋃ i, hatOf …)` | `latticeConvex_of_parts`（下面，由 `maxA`/`hfin`/`AhatMono` 造） |
| `hd : dot nJ vJ1 < 0` | `c.hsweep`（`ChainPartsFeed.lean:218`） |
| `hR : ∀ g ∈ ⋃ …, cJ ≤ dot nJ g` | `c.hhp`（`:201`）经 `Set.iUnion_subset` |
| `hswept : SweptClosed … vJ1 nJ cJ` | `c.hswept`（`:202`） |
| `hvJ : dot nJ vJ = 0` | `c.F.dot_nJ_vJ`（`FaceBlock` 字段，`ANormal.lean:616`） |
| `bottom` | `c.bottom`（`:223-229`），`a := c.F.a`、`shellInf := shell (⋃ …) vJ1 nJ cJ` |

这条合成**树里已经写过一遍**：`ChainDataGeom.ofPartsExhausts`（`ChainExhaust.lean:103-105`）
逐字就是 `rec_vJ_of_bottom (latticeConvex_iUnion_hatOf …) hsweep (fun _ hg => Set.iUnion_subset
hhp hg) hswept F.dot_nJ_vJ bottom`。⟹ 缺的从来不是数学，是**接线**。

## 2. 为什么在 `ofParts` 上接不通、在 `ChainDataGeomParts` 上接得通（关键差别）

`ChainExhaust.lean:27-31` 逐字记着当初不接的理由：「**Measured: `ofParts`'s 25 binders leave
`Env` unconstrained**, so the lattice-convexity of `Â_∞` that `rec_vJ_of_bottom` needs is
**not** derivable from them」。这条对 `ofParts` 成立——那里 `Env : Set (ℤ × ℤ) → Prop` 是自由变量，
`latticeConvex_iUnion_hatOf`（`ChainAssemble.lean:339`）要的 `hEnv : Env = EnvOf ↑S` 无从取得，
所以当年做了 25→25 的 swap（`rec_vJ` 换 `hEnv`）。

**但 `ChainDataGeomParts` 没有自由 `Env`。** `c.maxA`（`ChainPartsFeed.lean:209`）逐字就写死了
`IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) …`，而 `toChainDataGeom`（`PartsToGeom.lean:40`）也把
`Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ))` 硬喂给 `ofParts` 的 `Env` 槽。⟹ 取 `Env := EnvOf ↑S`、
`hEnv := rfl`，当年那道障碍在这张表上**根本不存在**。

⚠ 这不是推翻 `ChainExhaust.lean:27-31`：那句对它自己说的对象（`ofParts`）是对的。
按 PROTOCOL §11，本文件否掉的只是「该结论可以搬到 `ChainDataGeomParts` 上」这个读法。

## 3. 原文那句理由在哪（派工点名要）

派工单猜的是盒子条款（`b3_colle2.txt:476`；⚠ 2026-09-25 逐字对读订正：原写 `:474`，
而 `:474` 是**光秃秃的项目标签 "(ii)"**，内容在 `:476`——"`B_i` contains both `A_{i-1}` and
`[-i+1,i-1]^2 ∩ H(ℓ^{(−)})`"。行号指到标签行是集成者本轮 §106 点的那一类病：**能编过、
能被引用、却指不到任何断言**）。**不是那条。** `ItemII.lean:700-717`（本轮亲读）
把来路写得很明白：`+v_J` 方向的无界性来自 **`J`-选择的极小性**（`b3_colle2.txt:500-506`）——
`J` 取**最小**的使 `|Â_i ∩ w_i(J)| < |Â_{i+1} ∩ w_{i+1}(J)|` 无穷多次成立的指标；极小性保证
`ι+1 ≤ j ≤ J-1` 的边长最终恒定，于是 `ℓ_J`-边从 `:488` 那个**钉死的** `g₁` 链出一个固定起点
`g_J`，只往 `+v_J` 端长。

⚠ 而这条在 Lean 侧**已经被打包进 `bottom` 字段**（`ItemII.lean:704-706`：「the ray is **not a
new obligation** — it is `bottom` (ii) + `hswept` + `hhp` + `hsweep`」）。⟹ (G-a) 不需要新的
原文性质；欠原文的是 `bottom` 本身（`ANormal.not_bottom_of_shell_data`：`bottom` 推不出自 shell
数据），而 `bottom` 是**已有字段**，不在本格。

硬规矩 6 的数值实例：`ItemII.lean` 的 `NoPinModel`（`:818` 起，盒子 `[-i,0] × [0,i]`）正是
「去掉钉死起点就不成立」的反例——嵌套、有限、并集格凸、`vJ1 = (0,-1)`/`nJ = (0,1)`/`cJ = 0`
下 swept-closed、`ℓ_J`-面基数 `i+1 → ∞`，**但沿 `-(1,0)` 长**，没有 `+(1,0)`-射线，
`bottom` (ii) 对 `vJ = (1,0)` 为假。⟹ 承重的是 `bottom` 的钉死起点，不是面基数无界。
我核对了这个台架在本文件路线里的位置：它否的是**绕过 `bottom`** 的读法，不否本文件（我用的是
`bottom` 本身）。

## 4. 查重（PROTOCOL §20 / §58 / §61）

声明头 grep `rec_vJ_of_parts` / `latticeConvex_of_parts` 在 `Nivat/` 下 **RC=1，0 命中**。
按语句形状：全树唯一产出 `∀ g ∈ ⋃ i, hatOf …, g + vJ ∈ ⋃ i, hatOf …` 的地方是
`ChainExhaust.lean:103`/`:172` 与 `ChainExhaustInter.lean` 的 `let rec_vJ' := …`——
**都是 `let`，不是可复用的声明**，且都要自由 `Env` ＋ `hEnv` 形参。本文件是第一条以
`ChainDataGeomParts` 为唯一输入的版本，按 §56 与它们**不是同一份证据**（输入不同）。
-/

set_option autoImplicit false

namespace Nivat.LaneLeafAGenRecVJ

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm.Aparts

variable {α : Type*}

/-- **`Â_∞` 的格凸性，只吃 `ChainDataGeomParts` 的字段。**
`latticeConvex_iUnion_hatOf`（`ChainAssemble.lean:339`）要 `hEnv : Env = EnvOf ↑S`；
这里取 `Env := EnvOf ↑S`，`hEnv := rfl`——`c.maxA`（`ChainPartsFeed.lean:209`）本来就是用
`EnvOf (↑S)` 写死的，没有自由 `Env`（对比 `ofParts`，见文件头 §2）。 -/
theorem latticeConvex_of_parts {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataGeomParts η xper vl p S gen) :
    IsLatticeConvexRegion (⋃ i, hatOf c.A c.kk vl i) :=
  latticeConvex_iUnion_hatOf η xper vl S (EnvOf (↑S : Set (ℤ × ℤ)))
    c.B c.A c.u c.kk rfl c.maxA c.hfin c.AhatMono

/-- ⭐ **(G-a) 的生产者：`rec_vJ` 由 `ChainDataGeomParts` 的字段（37 条）推出。**

逐字就是 `PartsToGeom.lean:43` 那个显式参数的类型，故
`c.toChainDataGeom (rec_vJ_of_parts c)` 无需任何额外输入即可造出 `ChainDataGeom`。

六个形参的来源见文件头 §1 的表；`hconv` 由 `latticeConvex_of_parts` 供给。 -/
theorem rec_vJ_of_parts {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataGeomParts η xper vl p S gen) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i :=
  rec_vJ_of_bottom (latticeConvex_of_parts c) c.hsweep
    (fun _ hg => Set.iUnion_subset c.hhp hg) c.hswept c.F.dot_nJ_vJ c.bottom

/-- **接线收据**：`ChainDataGeomParts` 的字段直接造出 `ChainDataGeom`，`rec_vJ` 不再是输入。
这条的存在本身就是护栏——若 `rec_vJ_of_parts` 的类型与 `toChainDataGeom` 的形参差一个字符，
这里就不通过。 -/
noncomputable def toChainDataGeom_of_parts {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataGeomParts η xper vl p S gen) :
    ChainDataGeom η xper vl p S gen :=
  c.toChainDataGeom (rec_vJ_of_parts c)

#print axioms latticeConvex_of_parts
#print axioms rec_vJ_of_parts
#print axioms toChainDataGeom_of_parts

end Nivat.LaneLeafAGenRecVJ
