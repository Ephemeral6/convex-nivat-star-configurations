/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-tower-hbase
-/
import Nivat.External.Colle.ChainPartsFeed
import Nivat.External.Colle.PartsToGeom
import Nivat.External.Colle.ItemII
import Nivat.External.Colle.TwoMGon

/-!
# 洞 1 第 25 条义务 `rec_vJ`：归约到三向量的格算术条件

消费者钉死在 `ChainDataGeomParts.toChainDataGeom`（`Nivat/External/Colle/PartsToGeom.lean`）的
显式参数上：`rec_vJ : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i`。

## 先按硬规矩 6 找原文给理由的那一句

`b3_colle2.txt:506`（按名/按串重量的，不是算的）：

> In particular, `Â_∞ := ⋃ Â_i` is a weakly `E(S_φ)`-enveloped set (see Figure 6), **with two
> semi-infinite edges, one of which is parallel to `ℓ` and the other one is parallel to `ℓ_J`**.
> Actually, `Â_∞` is an `(ℓ, ℓ_J)`-region.

⟹ `rec_vJ` 逐字就是「`ℓ_J`-方向那条边是半无限的」，`rec_p` 是「`ℓ`-方向那条边是半无限的」。
**两条边的理由不同源**，这是本格的要害：

* `ℓ` 那条：`x_per` 的周期平行于 `ℓ`（`b3_colle2.txt:494` 那段），周期性直接给平移不变。
* `ℓ_J` 那条：靠 **`b3_colle2.txt:500` 的严格增长** `|Â_i ∩ w_i(J)| < |Â_{i+1} ∩ w_{i+1}(J)|`
  （`b3_colle2.txt:498` 把 `J` 定义成**最小**的使该式对无穷多 `i` 成立的下标，再取子列使其对**所有** `i` 成立），
  配 `b3_colle2.txt:498` 的 `⋃ A_i = ℋ(ℓ^(−))`。**J-面的长度沿 `i` 严格涨、层又是递增的 ⟹ 并集在 `ℓ_J`
  方向上无界。**

⚠ **`ChainDataGeomParts`（`ChainPartsFeed.lean`）的 24 个字段里没有 J-面严格增长这一条**
（最接近的是 `AhatMono`，只给包含不给严格；和 `hfin`，每层有限）。我一开始据此判它是缺口——
**那个判断是错的，见下一节**：`bottom` 字段把 `b3_colle2.txt:500` 的增长结论以**射线**形式装进去了，
所以原文那句理由的前提其实落在了签名里，只是不以「面长严格涨」的形状。

⛔ 也**不许**走 `rec_vJ_of_exists_chainData_layer`（`ChainPartsFeed.lean` 的 2026-09-21 订正）：
它的结论是 `IsLatticeConvexRegion (⋃ i, hatOf A kk vl i)`，而 `IsLatticeConvexRegion R` 按定义
（`Nivat/Section8/HalfPlane.lean` 的 `IsLatticeConvexRegion`）只是
`∃ C, Convex ℝ C ∧ IsClosed C ∧ R = toReal ⁻¹' C`，**有界集照样满足** ⟹ 凸性不蕴含平移不变。
`PartsToGeom.lean` 那句 docstring「should be derivable …」按此为假，本文件不依赖它。

## ⛔ 先撤回本文件原来的定位：`rec_vJ` **已经有无条件的主仓生产者**

派工时说 `rec_vJ` 是「洞 1 上唯一一条已知走不通的义务」、「真生产者尚未确定」。
**那个状态是过期的**，我落地后才查到（按名 grep `^import …PartsToGeom` 的反向依赖时撞上的）：

> `Nivat.LaneLeafAGenRecVJ.rec_vJ_of_parts`（`Nivat/External/Colle/RecVJFromParts.lean`，
> lane-leafa-gen 产），**无任何额外前提**，从 `c` 的 24 个字段直接给出
> `∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i`，
> 并有接线收据 `toChainDataGeom_of_parts`。
>
> 我第一手复核（不是读它的 docstring）：`Nivat/All.lean` 有
> `import Nivat.External.Colle.RecVJFromParts` ⟹ **在 build 里**；欠账标记计数 0；
> `check1.sh EXIT=0 / ERRORS=0`；三条 `#print axioms` 全为
> `[propext, Classical.choice, Quot.sound]`。

它走的是 `rec_vJ_of_bottom`（`Nivat/External/Colle/ItemII.lean` 的 `rec_vJ_of_bottom`）＋
**`c.bottom` 字段**——`bottom` 的第二个合取项在 `ε = 0` 档给出整条 `vJ`-射线，配
`IsLatticeConvexRegion` 的回收锥即得平移封闭。⟹ 上面那句「24 个字段里没有 J-面严格增长」
仍是真的，但它**不是**缺口：`bottom` 把 `b3_colle2.txt:500` 的增长结论**以射线形式**已经装进字段了。

⟹ 本文件的 `rec_of_comb` / `parts_rec_vJ` / `toChainDataGeom_of_comb` 多一条 `hcomb` 侧条件，而
`rec_vJ_of_parts` 无条件 ⟹ 这三条不是 `rec_vJ` 的生产者。⚠ **但「严格弱」这个词原先用错了**：
它只对上面这三条成立，**不**及于 `dot_nJ_p_pos_of_comb`（见下表该行）——那条是撤回后的定位。

## 本文件真正独立的那一格：**`bottom` 是承重的**

| 声明 | 内容 |
|---|---|
| `bottom_load_bearing` | ⭐ `rec_vJ_of_bottom` 的前五条 binder（`hconv`/`hd`/`hR`/`hswept`/`hvJ`）**全真**而结论为假 ⟹ `bottom` 不可去 |
| `Uwedge_latticeConvex` | 见证集合真的格凸（走 `TwoMGon.isLatticeConvexRegion_iInter_halfPlaneLE`），所以否掉的不是凸性那一格 |
| `comb_not_removable` | 四条抽象性质（含 `rec_p`）＋ 侧条件不成立 ⟹ `+vJ` 封闭为假 |
| `dot_nJ_p_pos_of_comb` | `hcomb` 蕴含 `0 < ⟪nJ,p⟫`（字段 `dot_nJ_p` 只给 `≠ 0`）。⭐ 撤回原「严格弱于 `dot_p_pos`」：两者 binder 集**不相交**（本条纯算术 `hperp`/`hsweep`/`ht`/`hcomb`；`dot_p_pos`（`EscapeW.lean` 的 `dot_p_pos`）要 `U` 的四条性质）⟹ **不可比**，且本条**不经 `bottom`** |
| `rec_of_comb` 等三条 | 抽象/结构/接线骨架，**已被 `rec_vJ_of_parts` 取代**，见上 |

⭐ `bottom_load_bearing` 比 `ChainPartsFeed.lean` 那条 2026-09-21 订正**强一格**：那条只说
「凸性单独不蕴含平移不变」（见证 `R = {(0,0)}`，一个有界集，其余 binder 一条都没兑现）；
本条的见证把 `hd`/`hR`/`hswept`/`hvJ` **也全部正面兑现**（§41），所以它排除的是
「那四条里某一条其实够用」这个可能，而不只是「凸性不够用」。

## 机理（先算的数值实例，再写的 Lean）

`rec_of_comb` 那一侧：`nJ = (0,1)`、`cJ = 0`、`vJ = (1,0)`（`⟪nJ,vJ⟫ = 0` ✓）、
`vJ1 = (0,-1)`（`⟪nJ,vJ1⟫ = -1 < 0` ✓）、`p = (1,1)`（`⟪nJ,p⟫ = 1 ≠ 0` ✓）。
则 `1•p + 1•vJ1 = (1,1) + (0,-1) = (1,0) = vJ`。走法：`g --rec_p--> g+p`（`nJ`-层 +1）
`--hswept(t=1)--> g+p+vJ1 = g+vJ`（`nJ`-层回到原处）。

⭐ 要害是 `SweptClosed`（`MaximalEnveloped.lean` 的 `SweptClosed`）**只要求终点在半平面里**
（`∀ g ∈ A, ∀ t, c ≤ ⟪n, g + t•v⟫ → g + t•v ∈ A`），不要求中间点。而终点的层数
`⟪nJ, g+vJ⟫ = ⟪nJ,g⟫ + 0 ≥ cJ` 由 `hhp` 白送 ⟹ 守卫自动兑现，不是额外负担。

`bottom_load_bearing` 那一侧：同样的 `nJ`/`cJ`/`vJ`/`vJ1`，见证集换成第二象限楔形
`Uwedge = {z | 0 ≤ z.2 ∧ z.1 ≤ 0}`，它对 `+vJ1 = (0,-1)`（在半平面内）与 `+(0,1)` 都封闭、
格凸、在 `⟪nJ,·⟫ ≥ 0` 里，而 `(0,0) + vJ = (1,0)` 的第一坐标 `1 > 0` ⟹ 出楔形。
`bottom` 在它上面必然为假（否则和 `rec_vJ_of_bottom` 矛盾），这正是「`bottom` 承重」的含义。

⚠ **未主张**（§85.2）：`comb_not_removable` / `bottom_load_bearing` 否掉的都是「**列出的那几条
性质**推出 `+vJ` 封闭」，**不是**「`ChainDataGeomParts` 的 24 个字段推不出 `rec_vJ`」——
后者已被 `rec_vJ_of_parts` 证否（它就是推出来了）。本文件**不报** `rec_vJ` 为假。

⚠ 未主张：`vJ = a•p + t•vJ1` 在链上成不成立（它要 Bezout 型的整性条件，不是符号条件；
见 `dot_nJ_p_pos_of_comb` 的注）；也未主张 `bottom` 字段本身在链上谁产。
-/

namespace Nivat.LaneTowerHbaseRecVJ

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm.Aparts

variable {α : Type*}

/-! ## §1  抽象归约 -/

/-- `rec_p` 迭代 `a` 次。 -/
private theorem iter_rec {U : Set (ℤ × ℤ)} {p : ℤ × ℤ}
    (hrec : ∀ g ∈ U, g + p ∈ U) : ∀ (a : ℕ) (g : ℤ × ℤ), g ∈ U → g + (a : ℤ) • p ∈ U := by
  intro a
  induction a with
  | zero => intro g hg; simpa using hg
  | succ n ih =>
      intro g hg
      have h := hrec _ (ih g hg)
      have heq : g + (n : ℤ) • p + p = g + ((n + 1 : ℕ) : ℤ) • p := by
        push_cast
        rw [add_smul, one_smul, add_assoc]
      rwa [heq] at h

/-- ⭐ **第 25 条义务的抽象归约。**

`U` 的四条性质全部是 `ChainDataGeomParts` 现成字段的并集形（见 §2）：`hhp` ＝ `hhp`，
`hswept` ＝ `hswept`，`hrec_p` ＝ `rec_p`，`hperp` ＝ `c.F.dot_nJ_vJ`
（`FaceBlock.dot_nJ_vJ`，`ANormal.lean` 的 `FaceBlock`）。**唯一新增的是 `hcomb`。**

守卫为什么自动兑现：`SweptClosed` 只查终点，而终点层数 `⟪nJ, g+vJ⟫ = ⟪nJ,g⟫` 由 `hperp` 保住、
再由 `hhp` 压在 `cJ` 之上。 -/
theorem rec_of_comb {U : Set (ℤ × ℤ)} {p vJ vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ g ∈ U, cJ ≤ dot nJ g)
    (hswept : SweptClosed U vJ1 nJ cJ)
    (hrec_p : ∀ g ∈ U, g + p ∈ U)
    (hperp : dot nJ vJ = 0)
    {a t : ℕ} (hcomb : vJ = (a : ℤ) • p + (t : ℤ) • vJ1) :
    ∀ g ∈ U, g + vJ ∈ U := by
  intro g hg
  have hsplit : g + (a : ℤ) • p + (t : ℤ) • vJ1 = g + vJ := by
    rw [hcomb, add_assoc]
  have h1 : g + (a : ℤ) • p ∈ U := iter_rec hrec_p a g hg
  have hlev : cJ ≤ dot nJ (g + (a : ℤ) • p + (t : ℤ) • vJ1) := by
    rw [hsplit, dot_add, hperp, add_zero]
    exact hhp g hg
  have h2 := hswept _ h1 t hlev
  rwa [hsplit] at h2

/-- 侧条件带**符号**信息，而字段 `dot_nJ_p` 只给 `≠ 0`。

`0 = ⟪nJ,vJ⟫ = a·⟪nJ,p⟫ + t·⟪nJ,vJ1⟫` 配 `⟪nJ,vJ1⟫ < 0` 与 `1 ≤ t` ⟹ `a·⟪nJ,p⟫ > 0`，
于是 `a ≥ 1` 且 `⟪nJ,p⟫ > 0`。

⟹ 链上要用 `rec_of_comb`，先得知道 `0 < ⟪nJ,p⟫`（哪一支由定向决定，本文件不主张）。
⚠ 而且符号**不够**：`hcomb` 还含 `vJ`-分量那条等式，是 Bezout 型的整性条件。 -/
theorem dot_nJ_p_pos_of_comb {p vJ vJ1 nJ : ℤ × ℤ} {a t : ℕ}
    (hperp : dot nJ vJ = 0) (hsweep : dot nJ vJ1 < 0) (ht : 1 ≤ t)
    (hcomb : vJ = (a : ℤ) • p + (t : ℤ) • vJ1) :
    0 < dot nJ p := by
  obtain ⟨n1, n2⟩ := nJ
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := vJ1
  subst hcomb
  simp only [Nivat.LE2.dot, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul] at hperp hsweep ⊢
  have ht' : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
  have ha : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  nlinarith [mul_pos (lt_of_lt_of_le zero_lt_one ht') (neg_pos.mpr hsweep)]

/-! ## §2  结构形：结论逐字是消费者那个参数的类型 -/

/-- `hhp` 的并集形：`c.hhp` 是逐层的，消费者要的是并集上的。 -/
private theorem union_hhp {η xper : Config α} {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    {gen : ℤ × ℤ} (c : ChainDataGeomParts η xper vl p S gen) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, c.cJ ≤ dot c.nJ g := by
  intro g hg
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
  exact c.hhp i hi

/-- ⭐ **结构形。**  除 `hcomb` 外每条前提都是 `c` 的字段：`c.hhp` / `c.hswept` / `c.rec_p` /
`c.F.dot_nJ_vJ`。结论与 `ChainDataGeomParts.toChainDataGeom` 的第 25 个参数**逐字符相同**
（见下条 `toChainDataGeom_of_comb`，那是内核对这句话的检验）。 -/
theorem parts_rec_vJ {η xper : Config α} {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    {gen : ℤ × ℤ} (c : ChainDataGeomParts η xper vl p S gen)
    {a t : ℕ} (hcomb : c.vJ = (a : ℤ) • p + (t : ℤ) • c.vJ1) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i :=
  rec_of_comb (union_hhp c) c.hswept c.rec_p c.F.dot_nJ_vJ hcomb

/-- ⭐ **收据：第 25 个参数真被喂进去了。**  这条 `def` 只在 `parts_rec_vJ` 的类型与
`toChainDataGeom` 的第 25 个参数类型逐字符一致时才居留 —— 不是我对着签名抄的对位表，
是内核维护的。 -/
noncomputable def toChainDataGeom_of_comb {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataGeomParts η xper vl p S gen)
    {a t : ℕ} (hcomb : c.vJ = (a : ℤ) • p + (t : ℤ) • c.vJ1) :
    ChainDataGeom η xper vl p S gen :=
  c.toChainDataGeom (parts_rec_vJ c hcomb)

/-! ## §3  侧条件非空真（§71 第一类） -/

/-- `nJ = (0,1)`、`cJ = 0`、`U = {z | 0 ≤ z.2}`、`p = (1,1)`、`vJ1 = (0,-1)`、`vJ = (1,0)`，
`a = t = 1`：四条前提全真、侧条件成立、结论成立。⟹ `rec_of_comb` 不是空真。 -/
theorem comb_nonvacuous :
    ((1 : ℤ), (0 : ℤ)) = ((1 : ℕ) : ℤ) • ((1 : ℤ), (1 : ℤ))
        + ((1 : ℕ) : ℤ) • ((0 : ℤ), (-1 : ℤ)) ∧
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 ∧
    dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) < 0 ∧
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (1 : ℤ)) ≠ 0 ∧
    (∀ g ∈ {z : ℤ × ℤ | 0 ≤ z.2}, (0 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) g) ∧
    SweptClosed {z : ℤ × ℤ | 0 ≤ z.2} ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ∧
    (∀ g ∈ {z : ℤ × ℤ | 0 ≤ z.2}, g + ((1 : ℤ), (1 : ℤ)) ∈ {z : ℤ × ℤ | 0 ≤ z.2}) := by
  refine ⟨by norm_num, by simp [Nivat.LE2.dot], by simp [Nivat.LE2.dot],
    by simp [Nivat.LE2.dot], ?_, ?_, ?_⟩
  · intro g hg; simpa [Nivat.LE2.dot] using hg
  · intro g hg tt hlev
    simpa [Nivat.LE2.dot] using hlev
  · intro g hg
    simp only [Set.mem_ofPred_eq, Prod.snd_add] at hg ⊢
    omega

/-- 上条的结论侧，走 `rec_of_comb`：同一组数值下 `+vJ` 封闭**真**。 -/
theorem rec_vJ_on_nonvacuous_bench :
    ∀ g ∈ {z : ℤ × ℤ | 0 ≤ z.2}, g + ((1 : ℤ), (0 : ℤ)) ∈ {z : ℤ × ℤ | 0 ≤ z.2} :=
  rec_of_comb (p := ((1 : ℤ), (1 : ℤ))) (vJ1 := ((0 : ℤ), (-1 : ℤ)))
    (nJ := ((0 : ℤ), (1 : ℤ))) (cJ := 0)
    (fun g hg => by simpa [Nivat.LE2.dot] using hg)
    (fun g _ tt hlev => by simpa [Nivat.LE2.dot] using hlev)
    (fun g hg => by
      simp only [Set.mem_ofPred_eq, Prod.snd_add] at hg ⊢
      omega)
    (by simp [Nivat.LE2.dot]) (a := 1) (t := 1) (by norm_num)

/-! ## §4  侧条件不可去 -/

/-- 偶数竖条：`U = {z | 0 ≤ z.2 ∧ 2 ∣ z.1}`。 -/
private def Ueven : Set (ℤ × ℤ) := {z | 0 ≤ z.2 ∧ (2 : ℤ) ∣ z.1}

/-- ⭐ **`hcomb` 不可去。**  同样四条前提（`nJ = (0,1)`、`cJ = 0`、`vJ1 = (0,-1)`、`vJ = (1,0)`），
`p` 换成 `(2,1)`：`U` 对 `+p` 封闭、对 `vJ1` 扫闭、在半平面里、`⟪nJ,vJ⟫ = 0` 全真，
而 `+vJ` 封闭**假**（`(0,0) ∈ U`、`(1,0) ∉ U`，奇偶性）。

侧条件为什么在这里不成立：`a•(2,1) + t•(0,-1) = (1,0)` 的第一坐标要 `2a = 1`，无解。

⚠ **未主张**（§85.2）：本条否掉的是「这四条抽象性质 ⟹ `+vJ` 封闭」，**不是**
「`ChainDataGeomParts` 的 24 字段 ⟹ `rec_vJ`」。后者需要整个 24 字段的实例，本文件没构造。 -/
theorem comb_not_removable :
    (∀ g ∈ Ueven, (0 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) g) ∧
    SweptClosed Ueven ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ∧
    (∀ g ∈ Ueven, g + ((2 : ℤ), (1 : ℤ)) ∈ Ueven) ∧
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 ∧
    ¬ (∀ g ∈ Ueven, g + ((1 : ℤ), (0 : ℤ)) ∈ Ueven) := by
  refine ⟨?_, ?_, ?_, by simp [Nivat.LE2.dot], ?_⟩
  · intro g hg; simpa [Nivat.LE2.dot] using hg.1
  · intro g hg tt hlev
    refine ⟨?_, ?_⟩
    · simpa [Nivat.LE2.dot] using hlev
    · simpa using hg.2
  · intro g hg
    obtain ⟨h1, k, hk⟩ := hg
    refine ⟨by simp only [Prod.snd_add]; omega, ⟨k + 1, ?_⟩⟩
    simp only [Prod.fst_add]
    omega
  · intro h
    have h0 : ((0 : ℤ), (0 : ℤ)) ∈ Ueven := ⟨le_rfl, ⟨0, by norm_num⟩⟩
    obtain ⟨-, k, hk⟩ := h _ h0
    simp only [Prod.fst_add] at hk
    omega

/-- `Ueven` 上无侧条件的那句确实假，单独拎出来（`comb_not_removable` 的第五合取项）。 -/
theorem not_rec_vJ_on_Ueven :
    ¬ (∀ g ∈ Ueven, g + ((1 : ℤ), (0 : ℤ)) ∈ Ueven) :=
  comb_not_removable.2.2.2.2

/-! ## §5  ⭐ `rec_vJ_of_bottom` 的 `bottom` 是承重的

`rec_vJ_of_bottom`（`Nivat/External/Colle/ItemII.lean` 的 `rec_vJ_of_bottom`）有六条 binder：
`hconv` / `hd` / `hR` / `hswept` / `hvJ` / `bottom`。本节给一个见证，**前五条全部正面兑现
而结论为假** ⟹ `bottom` 不可去。 -/

/-- 第二象限楔形 `{z | 0 ≤ z.2 ∧ z.1 ≤ 0}`。 -/
def Uwedge : Set (ℤ × ℤ) := {z | 0 ≤ z.2 ∧ z.1 ≤ 0}

/-- `Uwedge` 是两条半平面的交，故格凸
（`Nivat.TwoMGon.isLatticeConvexRegion_iInter_halfPlaneLE`）。

⭐ 这一条是让 §5 有鉴别力的关键：`ChainPartsFeed.lean` 那条 2026-09-21 订正用的见证是有界集
`{(0,0)}`，凸性那一格是**唯一**兑现的；这里凸性也兑现，所以否掉的不是凸性。 -/
theorem Uwedge_latticeConvex : IsLatticeConvexRegion Uwedge := by
  have he : {z : ℤ × ℤ | ∀ i : Fin 2,
      dot (![((0 : ℤ), (-1 : ℤ)), ((1 : ℤ), (0 : ℤ))] i) z ≤ (![(0 : ℤ), (0 : ℤ)] i)}
      = Uwedge := by
    ext z
    simp only [Set.mem_ofPred_eq, Uwedge, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Nivat.LE2.dot]
    omega
  rw [← he]
  exact Nivat.TwoMGon.isLatticeConvexRegion_iInter_halfPlaneLE 2 _ _

/-- ⭐ **`bottom` 不可去。**  `nJ = (0,1)`、`cJ = 0`、`vJ1 = (0,-1)`、`vJ = (1,0)`、
`R = Uwedge`：`rec_vJ_of_bottom` 的前五条 binder 全真（第六项 `bottom` 因此必假），
而结论 `∀ g ∈ R, g + vJ ∈ R` 为假 —— 见证 `(0,0) ∈ Uwedge`、`(1,0) ∉ Uwedge`。

附带第六合取项：`Uwedge` 对 `+(0,1)` 也封闭，且 `⟪nJ,(0,1)⟫ = 1 ≠ 0`
（正是字段 `dot_nJ_p` 的形状）⟹ 连 `rec_p` 一起兑现也还是不够。

⚠ **未主张**：本条**不**说 `rec_vJ` 在链上为假（`rec_vJ_of_parts` 已无条件证出它），只说
`rec_vJ_of_bottom` 的 binder 表里 `bottom` 那一条承重、删不掉。 -/
theorem bottom_load_bearing :
    IsLatticeConvexRegion Uwedge ∧
    dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) < 0 ∧
    (∀ g ∈ Uwedge, (0 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) g) ∧
    SweptClosed Uwedge ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ∧
    dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 ∧
    ((∀ g ∈ Uwedge, g + ((0 : ℤ), (1 : ℤ)) ∈ Uwedge) ∧
      dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (1 : ℤ)) ≠ 0) ∧
    ¬ (∀ g ∈ Uwedge, g + ((1 : ℤ), (0 : ℤ)) ∈ Uwedge) := by
  refine ⟨Uwedge_latticeConvex, by simp [Nivat.LE2.dot], ?_, ?_,
    by simp [Nivat.LE2.dot], ⟨?_, by simp [Nivat.LE2.dot]⟩, ?_⟩
  · intro g hg; simpa [Nivat.LE2.dot] using hg.1
  · intro g hg tt hlev
    exact ⟨by simpa [Nivat.LE2.dot] using hlev, by simpa using hg.2⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hg
    refine ⟨?_, ?_⟩
    · simp only [Prod.snd_add]; omega
    · simp only [Prod.fst_add]; omega
  · intro h
    have h0 : ((0 : ℤ), (0 : ℤ)) ∈ Uwedge := ⟨le_rfl, le_rfl⟩
    have := (h _ h0).2
    simp only [Prod.fst_add] at this
    omega

end Nivat.LaneTowerHbaseRecVJ

#print axioms Nivat.LaneTowerHbaseRecVJ.rec_of_comb
#print axioms Nivat.LaneTowerHbaseRecVJ.dot_nJ_p_pos_of_comb
#print axioms Nivat.LaneTowerHbaseRecVJ.parts_rec_vJ
#print axioms Nivat.LaneTowerHbaseRecVJ.toChainDataGeom_of_comb
#print axioms Nivat.LaneTowerHbaseRecVJ.comb_nonvacuous
#print axioms Nivat.LaneTowerHbaseRecVJ.rec_vJ_on_nonvacuous_bench
#print axioms Nivat.LaneTowerHbaseRecVJ.comb_not_removable
#print axioms Nivat.LaneTowerHbaseRecVJ.not_rec_vJ_on_Ueven
#print axioms Nivat.LaneTowerHbaseRecVJ.Uwedge_latticeConvex
#print axioms Nivat.LaneTowerHbaseRecVJ.bottom_load_bearing

#print axioms Nivat.LaneTowerHbaseRecVJ.iter_rec
#print axioms Nivat.LaneTowerHbaseRecVJ.union_hhp
#print axioms Nivat.LaneTowerHbaseRecVJ.Ueven
#print axioms Nivat.LaneTowerHbaseRecVJ.Uwedge
