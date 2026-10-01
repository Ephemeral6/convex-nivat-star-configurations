/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.L1Line0

/-!
# `hstrip` 的无角点归约（`b3_colle2.txt:786-804` + Figure 10）

消费者：`RegionSteps.lean` 的 `hstrip`（洞 6，`:2617-2620`）。

`StripPlace.stripStep_of_corner_of_place`（`StripPlace.lean:77`）走的是「`B` 有一个左下角
`b₀`，全体 `B` 落在 `b₀ + ℕvl − ℕu'` 里」那条路。**那条前提 `hBcorner` 不是免费的**：
链上只有 `hczmem`（`cz` 这一层被取到）给出层极小点，而层极小点不必同时是 `vl`-极小点——
两者要同一个点，需要 `B` 的下边界单调，那本身就是待证的几何内容。

本文件给**不提角点**的归约，只要两条 `hplaceB` / `hdown`。

🔴 **2026-09-21 订正：下面的 `stripStep_of_place_of_down` 是真定理，但 `hplaceB` 在链上
不可满足，所以这条归约不能用来关洞 6。** 算术：`dot nℓ vl = 0` ⟹ `halfStrip B vl = B + ℕvl`
的**层集合等于 `B` 的层集合**，上界是 `B` 的最高层。取 `b` 为 `B` 的 `nℓ`-最高点、`z ∈ Sw`
比 `a₀` 高 `δ > 0`，则 `b + (z − a₀)` 的层超出 `B` 的最高层，**不可能**在 `halfStrip` 里。
本归约先把点抬到 `b + (z − a₀)` 再降 `t` 步，**抬那一下就出界**。
死因可机械复述：它**丢掉了洞 6 的 `dot nℓ w < cz`**，而那条正是把层压回 `B` 值域的唯一耦合。
这是「比原文强 = 债」（硬规矩 7）落在**前提**位置上的实例——真定理 ＋ 空前提 ＝ 零进度。

保留本文件的理由（`PROTOCOL.md` §14）：`iterate_down` / `halfStrip_add_zsmul_vl` /
`place_of_down` 三条仍然可用，它们是正确分解里 (O2) 的「向下」那一支；
正确分解 (O1)/(O2) 写在 `RegionSteps.lean` 洞 6 的注释里。

两条前提原本的原文对应（仍然准确，作废的是「两条就够」这个判断）：

* **`hplaceB`** ＝ `:798` Figure 10 那句
  "knowledge of `T^u η` on `H_B(ℓ)` determines it on `A_1`"：窗口 `Ŝ_{φ_ι}`（`Sw`，锚点 `a₀`）
  平移到 `B` 的**任意**一点 `b` 上之后，只要没掉到割线 `cz` 以下，整块就落在 `H_B(ℓ)` 里。
  量词对应：`∀ b ∈ B`（原文的 "`Ŝ_{φ_ι}` is a translation of `𝒮_{φ_ι}`"，平移量遍历 `B`）、
  `∀ z ∈ Sw`（窗口的每个点）、`cz ≤ dot nℓ (b + (z − a₀))`（原文 "on `H_B(ℓ)`"，即不越过
  `ℓ_B^{(−)}`，`:794`）。
* **`hdown`** ＝ `:794-796` 的逐行下降
  "`A_1 := 𝓡_{ι−1} ∩ l_1`, `l_1 := ℓ_B^{(−)}`, then `A_2 := 𝓡_{ι−1} ∩ l_2`, `l_2 := l_1^{(−)}`,
  by induction"：`H_B(ℓ)` 沿 `v⃗_{ℓ_{ι−1}}`（即 `u'`，`dot nℓ u' = −1`）往下走一行仍在 `H_B(ℓ)`
  里，**只要没掉到 `cz` 以下**。原文正是「逐行」，本前提就是那一行。

算术（这才是原文没写、我们必须自己算的那步）：`w = b + s•vl + t•u'`（`s t : ℕ`），
`dot nℓ vl = 0`、`dot nℓ u' = −1` 给

```
dot nℓ (z + (w − a₀)) = dot nℓ (b + (z − a₀)) − t
```

所以前提 `cz ≤ dot nℓ (z + (w − a₀))` **自动**蕴含 `hplaceB` 要的 `cz ≤ dot nℓ (b + (z − a₀))`
（因为 `t ≥ 0`），并且下降过程中每一行的层都 `≥ cz`。于是 `hdown` 的 `t` 次迭代合法。
⚠ 本归约**用不上** `dot nℓ w < cz`，也用不上 `hcz`——它们只在 `StripPlace` 那条角点写法里
用来逼出 `C < t`。本写法里 `t` 的非负性直接来自 `coneRegion` 的 `t : ℕ`。
-/

set_option autoImplicit false

namespace Nivat.StripDescend

open Nivat.LE2 (dot halfStrip)
open Nivat.ConeRegion (coneRegion)

variable {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {cz : ℤ}

/-- `dot nℓ` 在基 `(vl, u')` 下的展开，`hperp`/`hnu` 两条归一化一次用掉。 -/
private theorem dot_shift (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (g : ℤ × ℤ) (a b : ℤ) :
    dot nℓ (g + a • vl + b • u') = dot nℓ g - b := by
  have h : dot nℓ (g + a • vl + b • u')
      = dot nℓ g + a * dot nℓ vl + b * dot nℓ u' := by
    unfold dot
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [h, hperp, hnu]; ring

/-- `halfStrip` 对 `+ℕvl` 封闭（`halfStrip B vl = B + ℕvl`，`LatticeEdges.lean:1810`）。 -/
theorem halfStrip_add_zsmul_vl {g : ℤ × ℤ} {k : ℤ} (hk : 0 ≤ k)
    (hg : g ∈ halfStrip B vl) : g + k • vl ∈ halfStrip B vl := by
  obtain ⟨b, hb, t, hgt⟩ := hg
  obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le hk
  refine ⟨b, hb, t + k', ?_⟩
  rw [hgt]; push_cast; rw [add_smul]; abel

/-- 沿 `u'` 逐行下降 `d` 步，全程层不低于 `cz`（`:794-796` 的归纳，无角点版）。 -/
theorem iterate_down
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hdown : ∀ g ∈ halfStrip B vl, cz ≤ dot nℓ (g + u') → g + u' ∈ halfStrip B vl)
    (g : ℤ × ℤ) (hg : g ∈ halfStrip B vl) (d : ℕ) (hlev : cz ≤ dot nℓ g - d) :
    g + (d : ℤ) • u' ∈ halfStrip B vl := by
  induction d with
  | zero => simpa using hg
  | succ d' ih =>
      have hstep : g + (d' : ℤ) • u' ∈ halfStrip B vl := ih (by push_cast at hlev ⊢; omega)
      have hnext : cz ≤ dot nℓ (g + (d' : ℤ) • u' + u') := by
        have := dot_shift (nℓ := nℓ) (vl := vl) (u' := u') hperp hnu g 0 ((d' : ℤ) + 1)
        simp only [zero_smul, add_zero] at this
        have heq : g + ((d' : ℤ) + 1) • u' = g + (d' : ℤ) • u' + u' := by
          rw [add_smul, one_smul, add_assoc]
        rw [heq] at this
        rw [this]
        push_cast at hlev
        omega
      have heq : g + ((d' + 1 : ℕ) : ℤ) • u' = g + (d' : ℤ) • u' + u' := by
        push_cast
        rw [add_smul, one_smul, add_assoc]
      rw [heq]
      exact hdown _ hstep hnext

/-- **`hstrip` 的无角点归约**（`RegionSteps.lean` 洞 6 的目标）。

原文：`b3_colle2.txt:786-804` + Figure 10（`:798`）。两条前提的逐词对应见文件头。

与 `StripPlace.stripStep_of_corner_of_place`（`StripPlace.lean:77`）的区别：**不要 `hBcorner`、
不要 `hb₀`/`hb₀cz`、不要 `hcz`，也不要 `dot nℓ w < cz`。** 代价是 `hplaceB` 的锚点遍历整个
`B` 而不只是一个角点——而这正是原文 Figure 10 说的（`Ŝ_{φ_ι}` 是 `𝒮_{φ_ι}` 的**平移**，
平移量没有被限定成某个角）。 -/
theorem stripStep_of_place_of_down {Sw : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hplaceB : ∀ b ∈ B, ∀ z ∈ Sw, cz ≤ dot nℓ (b + (z - a₀)) →
      b + (z - a₀) ∈ halfStrip B vl)
    (hdown : ∀ g ∈ halfStrip B vl, cz ≤ dot nℓ (g + u') → g + u' ∈ halfStrip B vl) :
    ∀ w ∈ coneRegion B vl u', dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ Nivat.LE2.halfStrip B vl := by
  intro w hw _ z hz hzcross
  rw [Nivat.ConeRegion.mem_coneRegion_iff] at hw
  obtain ⟨b, hb, s, t, rfl⟩ := hw
  have hzSw : z ∈ Sw := Finset.mem_of_mem_erase hz
  -- `z + (w − a₀) = (b + (z − a₀)) + s•vl + t•u'`
  have hsplit : z + (b + (s : ℤ) • vl + (t : ℤ) • u' - a₀)
      = b + (z - a₀) + (s : ℤ) • vl + (t : ℤ) • u' := by abel
  rw [hsplit] at hzcross ⊢
  -- 层等式：`dot nℓ (… + s•vl + t•u') = dot nℓ (b + (z − a₀)) − t`
  have hlev := dot_shift (nℓ := nℓ) (vl := vl) (u' := u') hperp hnu
    (b + (z - a₀)) (s : ℤ) (t : ℤ)
  rw [hlev] at hzcross
  -- `hplaceB` 的层前提由 `t ≥ 0` 免费
  have hg₀lev : cz ≤ dot nℓ (b + (z - a₀)) := by
    have : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    omega
  have hg₀ : b + (z - a₀) ∈ halfStrip B vl := hplaceB b hb z hzSw hg₀lev
  -- 横向 `s•vl` 免费
  have h1 : b + (z - a₀) + (s : ℤ) • vl ∈ halfStrip B vl :=
    halfStrip_add_zsmul_vl (Int.natCast_nonneg s) hg₀
  -- 纵向 `t` 步下降
  have h2 := dot_shift (nℓ := nℓ) (vl := vl) (u' := u') hperp hnu (b + (z - a₀)) (s : ℤ) 0
  simp only [zero_smul, add_zero, sub_zero] at h2
  exact iterate_down hperp hnu hdown _ h1 t (by rw [h2]; omega)

/-- **`hplaceB` 的「向下」一半是免费的。**

把 `b + (z − a₀)` 在幺模基 `(vl, u')` 下写成 `b + A•vl + C•u'`：

* `0 ≤ A` 由 `hvlmin`（`RegionSteps.lean:2561`，`VlMinAdj.vlmin_of_adjacent`，已在链上）给出——
  窗口锚在 `hstrict` 选出的 `vl`-极小顶点上，原文 `:792` 的 `𝒮_{φ_ι}` 就是这么取的；
* `0 ≤ C` 即窗口这一点**低于或齐平**于 `b`（`dot nℓ u' = −1`，`C > 0` 就是往下）。

这一半**不需要任何新几何**：`b + A•vl ∈ halfStrip B vl` 是定义，再沿 `u'` 下降 `C` 步，
层从 `dot nℓ b` 掉到 `dot nℓ b − C ≥ cz`（就是 `hlev`），全程合法。

**推论（订正版）**：`hplaceB` 整条为假（见文件头），所以「真债只剩 `C < 0`」这句作废——
`C ≥ 0` 那一支不是「一半债」，而是**正确分解 (O2) 在 `L ≤ dot nℓ b` 时的现成形式**，
见 `RegionSteps.lean` 洞 6 注释。本定理本身无 `sorry`、公理干净，可直接被 (O2) 消费。 -/
theorem place_of_down
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hdown : ∀ g ∈ halfStrip B vl, cz ≤ dot nℓ (g + u') → g + u' ∈ halfStrip B vl)
    {b : ℤ × ℤ} (hb : b ∈ B) {A C : ℤ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hlev : cz ≤ dot nℓ (b + A • vl + C • u')) :
    b + A • vl + C • u' ∈ halfStrip B vl := by
  obtain ⟨C', rfl⟩ := Int.eq_ofNat_of_zero_le hC
  have hbmem : b ∈ halfStrip B vl := ⟨b, hb, 0, by simp⟩
  have h1 : b + A • vl ∈ halfStrip B vl := halfStrip_add_zsmul_vl hA hbmem
  have h2 := dot_shift (nℓ := nℓ) (vl := vl) (u' := u') hperp hnu b A (C' : ℤ)
  rw [h2] at hlev
  have h3 := dot_shift (nℓ := nℓ) (vl := vl) (u' := u') hperp hnu b A 0
  simp only [zero_smul, add_zero, sub_zero] at h3
  exact iterate_down hperp hnu hdown _ h1 C' (by rw [h3]; omega)

/-- **`halfStrip` 成员资格的坐标判据**：`p ∈ H_B(ℓ)` 当且仅当 `B` 在 `p` 的那一层上有一个
点不在 `p` 右边。

原文：`b3_colle2.txt:796` 的逐行下降 "`A₂ := 𝓡_{ι−1} ∩ l₂`, `l₂ := l₁^{(−)}`, proceeding
this way, we get by induction"。原文说「一行一行往下」，本引理把「在第几行、行内靠多左」
这两件事拆成两个线性泛函——`dot nℓ` 读行号（`hperp` 使 `vl` 不改行号），
`dot m` 读行内位置（`hmu'` 使 `u'` 不改行内位置）。量词逐个对应：
`∃ b ∈ B` ＝ 原文那一行上的基点，`dot nℓ b = dot nℓ p` ＝ 「同一行 `l_k`」，
`dot m b ≤ dot m p` ＝ 「`p` 在该基点沿 `+vl` 的一侧」，即 `H_B(ℓ) = B + ℕvl` 的 `ℕ`。

**用途（洞 6 的 (O2)）**：它把 `RegionSteps.lean:2666` 洞 6 的结论化成**一条**存在性义务，
取消了 `place_of_down` 那条路上的 `L ≤ dot nℓ b` / `L > dot nℓ b` 分情形——两支的区别
只是怎么**找到**那个基点，而结论形状是同一个。找基点的两条途径：
`L ≤ dot nℓ b` 时从 `b` 沿 `hstepdown` 逐行下降（`place_of_down` 仍是现成形式），
`L > dot nℓ b` 时需要「第 `L` 行非空」，由 `vl`-方向单位弦 ＋ `nℓ` 本原得到。

⚠ `↔` 的两个方向都**不需要** `hdown`，也不需要 `B` 有限、凸或 enveloped——
这纯粹是幺模基下的坐标改写。几何内容全部留在「怎么找那个 `b`」里。 -/
theorem mem_halfStrip_iff_level_left {m : ℤ × ℤ}
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hmvl : dot m vl = 1) (hmu' : dot m u' = 0) (p : ℤ × ℤ) :
    p ∈ halfStrip B vl ↔ ∃ b ∈ B, dot nℓ b = dot nℓ p ∧ dot m b ≤ dot m p := by
  constructor
  · rintro ⟨b, hb, t, rfl⟩
    refine ⟨b, hb, ?_, ?_⟩
    · rw [Nivat.LE2.dot_add, Nivat.ConeRegion.dot_zsmul, hperp]; ring
    · rw [Nivat.LE2.dot_add, Nivat.ConeRegion.dot_zsmul, hmvl]
      have : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
      omega
  · rintro ⟨b, hb, hlev, hleft⟩
    obtain ⟨A, C, hdec, -⟩ := Nivat.L1Line0.exists_decomp (u' := u') (vl := vl) hunimod b p
    have hC : C = 0 := by
      have h := congrArg (dot nℓ) hdec
      rw [Nivat.LE2.dot_add, Nivat.LE2.dot_add, Nivat.ConeRegion.dot_zsmul,
        Nivat.ConeRegion.dot_zsmul, hperp, hnu] at h
      omega
    have hA : A = dot m p - dot m b := by
      have h := congrArg (dot m) hdec
      rw [Nivat.LE2.dot_add, Nivat.LE2.dot_add, Nivat.ConeRegion.dot_zsmul,
        Nivat.ConeRegion.dot_zsmul, hmvl, hmu'] at h
      omega
    have hA0 : (0 : ℤ) ≤ A := by omega
    obtain ⟨A', rfl⟩ := Int.eq_ofNat_of_zero_le hA0
    exact ⟨b, hb, A', by rw [hdec, hC]; simp⟩

/-- **`hdown` 的装配**：把「`B` 的每一层都能往下走一步而不右移」（`hstepdown`）
升级成 `halfStrip B vl` 对 `+u'` 的封闭性，即洞 6 里 `place_of_down` / `iterate_down`
所要的那条 `hdown`。

原文：`b3_colle2.txt:796` 的逐行下降 "`A₂ := 𝓡_{ι−1} ∩ l₂`, `l₂ := l₁^{(−)}`,
proceeding this way, we get by induction"。逐个量词：`∀ g ∈ halfStrip B vl` ＝ 原文的
`A_k ⊆ H_B(ℓ)`；`cz ≤ dot nℓ (g + u')` ＝ 「还没掉到 `ℓ_B^{(−)}` 以下」（`:794`）；
结论 ＝ 原文的 `A_{k+1} ⊆ H_B(ℓ)`。`hstepdown` 是原文**默认**、没有写出来的那一步：
下一行非空，且它的左端不在这一行左端的右边。

⚠ `hstepdown` 是本条的**全部**几何内容，两半分别是
「第 `L−1` 层非空」（`vl`-方向单位弦 ＋ `nℓ` 本原）与
「左轮廓不右移」（`hadj`，`:766` 的循环序）。本定理本身是纯坐标改写。 -/
theorem halfStrip_down_of_stepdown {m : ℤ × ℤ}
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hmvl : dot m vl = 1) (hmu' : dot m u' = 0)
    (hstepdown : ∀ b ∈ B, cz ≤ dot nℓ b - 1 →
      ∃ b' ∈ B, dot nℓ b' = dot nℓ b - 1 ∧ dot m b' ≤ dot m b) :
    ∀ g ∈ halfStrip B vl, cz ≤ dot nℓ (g + u') → g + u' ∈ halfStrip B vl := by
  intro g hg hlev
  have hchar := mem_halfStrip_iff_level_left (B := B) hunimod hperp hnu hmvl hmu'
  obtain ⟨b, hb, hblev, hbleft⟩ := (hchar g).mp hg
  have hgu_lev : dot nℓ (g + u') = dot nℓ g - 1 := by
    rw [Nivat.LE2.dot_add, hnu]; ring
  have hgu_m : dot m (g + u') = dot m g := by
    rw [Nivat.LE2.dot_add, hmu']; ring
  obtain ⟨b', hb', hb'lev, hb'left⟩ := hstepdown b hb (by omega)
  exact (hchar (g + u')).mpr ⟨b', hb', by omega, by omega⟩

/-- **`hstepdown` 的左轮廓一半**（`b3_colle2.txt:796`，`hadj` 是全部内容）。

原文：`:796` "Let `A₂ := 𝓡_{ι−1} ∩ l₂`, where `l₂ := l₁^{(−)}`, proceeding this way,
we get by induction"。原文说「这样继续下去」，默认了下一行**不会向右缩**——本引理就是那句
默认。逐个量词：`b ∈ B` ＝ 当前行 `l₁` 上的基点；`c ∈ B` 与 `hclev` ＝ 下一行 `l₂` 非空
（本引理**不证**这一条，它由 `halfStrip_down_of_adj` 的 `hrow` 提供）；结论的 `b'` ＝
`l₂` 上不比 `b` 更靠右的那个点。

**`hadj` 为什么正好是对的前提**（硬规矩 10 要的「为什么」，不是「长什么样」）：
`B` 在层 `L` 的左边界落在某条左边（`dot n vl < 0`）上，位置 `α = (c + L·⟪n,u'⟫)/⟪n,vl⟫`，
于是 `dα/dL = ⟪n,u'⟫/⟪n,vl⟫`。往下走时左边界不右漂 ⟺ `dα/dL ≥ 0` ⟺ `⟪n,u'⟫ ≤ 0`，
这正是 `hadj : ∀ n ∈ E B, ¬(dot n vl < 0 ∧ 0 < dot n u')`，即 `:764`/`:766` 的
`𝒮_φ` 法向循环序。

**去掉 `hadj` 结论就假**（承重反例，不是装饰）：取 `nℓ=(0,1)`、`vl=(1,0)`、`u'=(0,-1)`、
`m=(1,0)`、`B = conv{(0,1),(5,0),(5,1)} ∩ ℤ²`。层 1 是 `{(0,1)..(5,1)}`，层 0 只有
`{(5,0)}`，所以 `b := (0,1)` 在层 0 找不到任何 `dot m b' ≤ 0` 的点。它的左下边法向
`(-1,-5)` 满足 `dot n vl = -1 < 0` 且 `dot n u' = 5 > 0`——恰好违反 `hadj`。

`hBfin`/`hBne`/`harea`/`hlc` 四条只为 `mem_of_dot_le_suppVal`（`LatticeEdges.lean:1393`）
服务：它把「`b + u'` 在 `B` 外」翻成「被某条**边**法向切掉」，`hadj` 才咬得住。
链上生产者：`harea` ← `AhatMono.posArea_of_enveloped`；`hlc` ← `WeaklyEnveloped` 第一合取。 -/
theorem exists_level_down_left {m : ℤ × ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (harea : Nivat.LE2.PosArea B) (hlc : Nivat.IsLatticeConvexRegion B)
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hadj : ∀ n ∈ Nivat.LE2.E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hmvl : dot m vl = 1) (hmu' : dot m u' = 0)
    {b c : ℤ × ℤ} (hb : b ∈ B) (hc : c ∈ B)
    (hclev : dot nℓ c = dot nℓ b - 1) :
    ∃ b' ∈ B, dot nℓ b' = dot nℓ b - 1 ∧ dot m b' ≤ dot m b := by
  by_cases hle : dot m c ≤ dot m b
  · exact ⟨c, hc, hclev, hle⟩
  · -- `dot m b < dot m c`：这时 `b + u'` 自己就在 `B` 里
    push_neg at hle
    refine ⟨b + u', ?_, ?_, ?_⟩
    · apply Nivat.LE2.mem_of_dot_le_suppVal hBfin hBne harea hlc
      intro n hn
      by_contra hgt
      push_neg at hgt
      have h1 : dot n b ≤ Nivat.LE2.suppVal B n := Nivat.LE2.le_suppVal hBfin hBne hb
      have h2 : dot n c ≤ Nivat.LE2.suppVal B n := Nivat.LE2.le_suppVal hBfin hBne hc
      have hu'pos : 0 < dot n u' := by
        rw [Nivat.LE2.dot_add] at hgt
        omega
      have hvlnn : 0 ≤ dot n vl := by
        have := hadj n hn
        by_contra hneg
        push_neg at hneg
        exact this ⟨hneg, hu'pos⟩
      obtain ⟨A, C, hdec, -⟩ := Nivat.L1Line0.exists_decomp hunimod b c
      have hC_eq : C = 1 := by
        have : dot nℓ c = dot nℓ (b + A • vl + C • u') := by rw [← hdec]
        rw [Nivat.LE2.dot_add, Nivat.LE2.dot_add, Nivat.ConeRegion.dot_zsmul,
            Nivat.ConeRegion.dot_zsmul, hperp, hnu] at this
        omega
      have hA_eq : A = dot m c - dot m b := by
        have : dot m c = dot m (b + A • vl + C • u') := by rw [← hdec]
        rw [Nivat.LE2.dot_add, Nivat.LE2.dot_add, Nivat.ConeRegion.dot_zsmul,
            Nivat.ConeRegion.dot_zsmul, hmvl, hmu'] at this
        omega
      have hA_pos : 0 < A := by rw [hA_eq]; omega
      have hc_eq : c = (b + u') + A • vl := by
        rw [hdec, hC_eq]
        simp only [one_smul]
        abel
      have : dot n c = dot n (b + u') + A * dot n vl := by
        rw [hc_eq, Nivat.LE2.dot_add, Nivat.ConeRegion.dot_zsmul]
      nlinarith [mul_nonneg hA_pos.le hvlnn]
    · rw [Nivat.LE2.dot_add, hnu]; ring
    · rw [Nivat.LE2.dot_add, hmu']; simp

/-- **`hdown` ⟸ `hadj` ＋「下一行非空」。**

把 `exists_level_down_left`（左轮廓不右漂，由 `:764` 的循环序给出）与
`halfStrip_down_of_stepdown`（纯坐标改写）接起来，于是洞 6 所要的 `hdown` 只剩
**一条**几何义务 `hrow`：`cz` 之上每一行都非空。

原文：`:796` 的逐行下降。`hrow` 对应原文默认的「`l₂ := l₁^{(−)}` 与 `𝓡_{ι−1}` 有交」，
这一条由 `vl`-方向单位弦（`SweepCrit.unitCovered_of_opposite_segments`，
来自 Definition 3.2 `:402` 的 enveloped 两侧边）＋ `nℓ` 本原给出，**不在本文件**。

⚠ 本定理不减少几何内容，它把三块分开的东西（`hadj` / 行非空 / 坐标改写）接成一条，
使 `hrow` 成为洞 6 在这一支上唯一还欠的东西。 -/
theorem halfStrip_down_of_adj {m : ℤ × ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (harea : Nivat.LE2.PosArea B) (hlc : Nivat.IsLatticeConvexRegion B)
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hadj : ∀ n ∈ Nivat.LE2.E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hmvl : dot m vl = 1) (hmu' : dot m u' = 0)
    (hrow : ∀ b ∈ B, cz ≤ dot nℓ b - 1 → ∃ c ∈ B, dot nℓ c = dot nℓ b - 1) :
    ∀ g ∈ halfStrip B vl, cz ≤ dot nℓ (g + u') → g + u' ∈ halfStrip B vl := by
  refine halfStrip_down_of_stepdown (cz := cz) hunimod hperp hnu hmvl hmu' ?_
  intro b hb hlev
  obtain ⟨c, hc, hclev⟩ := hrow b hb hlev
  exact exists_level_down_left hBfin hBne harea hlc hunimod hadj hperp hnu hmvl hmu'
    hb hc hclev

/-- **迭代下降：从 `b` 一路降到任意层 `L ∈ [cz, dot nℓ b]`，`m`-坐标全程不右移。**

原文：`b3_colle2.txt:796` 的 "proceeding this way, we get by induction" —— 原文只写了
「这样继续下去」，本引理就是那句归纳的展开。逐个量词：`b ∈ B` ＝ 起点所在的行 `l₁`；
`L` ＝ 原文第 `k` 步到达的行 `l_k`；`cz ≤ L` ＝ 「没掉到 `ℓ_B^{(−)}` 以下」（`:794`）；
`L ≤ dot nℓ b` ＝ 「往下走」；结论的 `dot m b' ≤ dot m b` ＝ 左端逐步不右移的传递闭包。

⚠ 本引理**无几何内容**：`hstepdown` 一步的几何在 `exists_level_down_left`（`hadj`），
这里只是对层差 `(dot nℓ b − L).toNat` 做归纳、把 `≤` 传递起来。 -/
theorem exists_row_left_of_stepdown {m : ℤ × ℤ}
    (hstepdown : ∀ b ∈ B, cz ≤ dot nℓ b - 1 →
      ∃ b' ∈ B, dot nℓ b' = dot nℓ b - 1 ∧ dot m b' ≤ dot m b)
    {b : ℤ × ℤ} (hb : b ∈ B) {L : ℤ}
    (hLcz : cz ≤ L) (hLb : L ≤ dot nℓ b) :
    ∃ b' ∈ B, dot nℓ b' = L ∧ dot m b' ≤ dot m b := by
  have hgap : 0 ≤ dot nℓ b - L := by omega
  generalize h : (dot nℓ b - L).toNat = n
  revert b L
  induction n with
  | zero =>
    intro b hb L hLcz hLb hgap h
    have hLeq : L = dot nℓ b := by
      have : dot nℓ b - L = 0 := by rw [Int.toNat_eq_zero] at h; omega
      omega
    exact ⟨b, hb, hLeq.symm, le_refl _⟩
  | succ n ih =>
    intro b hb L hLcz hLb hgap h
    have hLb_strict : L < dot nℓ b := by
      have : dot nℓ b - L ≠ 0 := by
        intro heq; rw [heq, Int.toNat_zero] at h; omega
      omega
    obtain ⟨b', hb', hlev_b', hmono⟩ := hstepdown b hb (by omega)
    have hgap' : 0 ≤ dot nℓ b' - L := by omega
    have h' : (dot nℓ b' - L).toNat = n := by
      have heq : dot nℓ b - L = ((n + 1 : ℕ) : ℤ) := by
        have := Int.toNat_of_nonneg hgap; rw [h] at this; exact this.symm
      have eq' : dot nℓ b' - L = (n : ℤ) := by rw [hlev_b']; omega
      have := Int.toNat_of_nonneg hgap'
      rw [eq'] at this
      omega
    obtain ⟨b'', hb'', hlev_b'', hmono'⟩ := ih hb' hLcz (by omega) hgap' h'
    exact ⟨b'', hb'', hlev_b'', le_trans hmono' hmono⟩

/-- **`hstrip_of_profile` 的 `hdesc` 的生产者**：`hadj` ＋「每行非空」＋「`cz` 是 `B` 的底层」。

原文：`:796` 的逐行下降走到 `ℓ_B^{(−)}`。本定理把三件已有的东西接起来：
`exists_level_down_left`（一步，几何 ＝ `hadj` ＝ `:764/:766` 循环序）、
`exists_row_left_of_stepdown`（归纳）、以及 `hczlow`（`cz` 不高于 `B` 的任何一层）。

逐个量词：`∀ b ∈ B` ＝ 原文 `A_k` 上的基点；`hrow` ＝ 原文默认的「`l_{k+1}` 与 `𝓡_{ι−1}`
有交」；`hczlow` ＝ 「`ℓ_B^{(−)}` 在 `B` 之下」，即 `cz` 的定义（链上由 `hcz` 给出）。

⚠ 本定理**无新几何**。唯一还欠的是 `hrow`，它由 `vl`-方向弦长 ≥ 1
（`SweepCrit.UnitCovered`，来自 Def 3.2 `:402` 的两侧边）＋ `nℓ` 本原给出。 -/
theorem hdesc_of_row {m : ℤ × ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (harea : Nivat.LE2.PosArea B) (hlc : Nivat.IsLatticeConvexRegion B)
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hadj : ∀ n ∈ Nivat.LE2.E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hmvl : dot m vl = 1) (hmu' : dot m u' = 0)
    (hczlow : ∀ b ∈ B, cz ≤ dot nℓ b)
    (hrow : ∀ b ∈ B, cz ≤ dot nℓ b - 1 → ∃ c ∈ B, dot nℓ c = dot nℓ b - 1) :
    ∀ b ∈ B, ∃ b₀ ∈ B, dot nℓ b₀ = cz ∧ dot m b₀ ≤ dot m b := by
  intro b hb
  refine exists_row_left_of_stepdown (cz := cz) (m := m) ?_ hb le_rfl (hczlow b hb)
  intro b' hb' hlev
  obtain ⟨c, hc, hclev⟩ := hrow b' hb' hlev
  exact exists_level_down_left hBfin hBne harea hlc hunimod hadj hperp hnu hmvl hmu'
    hb' hc hclev

/-- **`hprof` 的生产者：一个「贴角」的窗口平移。**

原文：`b3_colle2.txt:798` Figure 10 那句
"Since `Ŝ_{φ_ι}` is an `η − η̄_{ι₀}`-generating set, then the knowledge of `T^u η` on
`H_B(ℓ)` determines uniquely `T^u η` on `A₁`"。

**为什么不需要「轮廓比较」**（硬规矩 10：对齐的是理由，不是形状）。上一版把 `hprof`
读成「`B` 的左轮廓从底层升得比窗口慢」，那要整套折线斜率序列。真正的理由短得多：
Definition 3.2（`:402`）的 enveloped 说 `E B = E 𝒮_φ` 且 `B` 每条边**不短于** `𝒮_φ`
的对应边——对凸多边形这正是「`B` 是 `𝒮_φ` 的 Minkowski 被加项」，即
`B = 𝒮_φ + K`。而 Minkowski 和在任一方向上的面是两个面之和，
**对字典序极值（先取层极小、再取 `m` 极小）同样成立**，所以可以选平移量 `c` 使
`𝒮_φ + c` 的左下角**正好落在 `B` 的左下角**上。又 `φ_ι = ∏_{i≠ι₀}(X^{h_i}−1)` 整除 `φ`，
故 `𝒮_{φ_ι}` 也是 `𝒮_φ` 的被加项，窗口 `Sw` 随之落进 `B`。

于是 `hprof` 只是两步算术：`z + c ∈ B` 位于层 `cz + δ`（`hfit`＋`hbase`），
而目标层 `L ≤ cz + δ − 1` 在它**下面**，用已证的逐行下降 `exists_row_left_of_stepdown`
降过去即可；`m` 的比较由 `hleft`（`a₀ + c` 是 `B` 底层最左点）一步给出。

逐个量词：`c` ＝ 原文 "`Ŝ_{φ_ι}` denotes a translation of `𝒮_{φ_ι}`"（`:798`）的平移量；
`hfit` ＝ 「整块 `Ŝ_{φ_ι}` 落在 `H_B(ℓ)` 的产生区里」；`hbase`＋`hleft` ＝ Figure 10 里
`Ŝ_{φ_ι}` 的最低点贴在 `ℓ_B^{(−)}` 一侧的角上（贴角是可以选的，不是额外假设）；
`hrow` ＝ 原文默认的「每条 `l_k` 与 `𝓡_{ι−1}` 有交」。

⚠ **本定理无几何内容**，几何全部搬进 `hfit`／`hbase`／`hleft` 三条，
它们的共同生产者是上面说的 Minkowski 被加项事实（尚未形式化）。 -/
theorem hprof_of_fit {m : ℤ × ℤ} {Sw : Finset (ℤ × ℤ)} {a₀ c : ℤ × ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (harea : Nivat.LE2.PosArea B) (hlc : Nivat.IsLatticeConvexRegion B)
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hadj : ∀ n ∈ Nivat.LE2.E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hmvl : dot m vl = 1) (hmu' : dot m u' = 0)
    (hrow : ∀ b ∈ B, cz ≤ dot nℓ b - 1 → ∃ c' ∈ B, dot nℓ c' = dot nℓ b - 1)
    (hfit : ∀ z ∈ Sw, z + c ∈ B)
    (hbase : dot nℓ (a₀ + c) = cz)
    (hleft : ∀ b ∈ B, dot nℓ b = cz → dot m (a₀ + c) ≤ dot m b) :
    ∀ z ∈ Sw, ∀ b₀ ∈ B, dot nℓ b₀ = cz → ∀ L : ℤ, cz ≤ L →
      L ≤ cz + dot nℓ (z - a₀) - 1 →
      ∃ b'' ∈ B, dot nℓ b'' = L ∧ dot m b'' ≤ dot m b₀ + dot m (z - a₀) := by
  intro z hz b₀ hb₀ hb₀lev L hLcz hLup
  have hzc : z + c ∈ B := hfit z hz
  -- `z + c` 的层：`cz + δ`
  have hlev : dot nℓ (z + c) = cz + dot nℓ (z - a₀) := by
    have h := hbase
    rw [Nivat.LE2.dot_add] at h
    rw [Nivat.LE2.dot_add, Nivat.LE2.dot_sub]
    omega
  -- `z + c` 的 `m`-坐标
  have hmc : dot m (z + c) = dot m (a₀ + c) + dot m (z - a₀) := by
    rw [Nivat.LE2.dot_add, Nivat.LE2.dot_add, Nivat.LE2.dot_sub]; ring
  -- 从 `z + c` 逐行降到层 `L`
  obtain ⟨b'', hb'', hb''lev, hb''m⟩ :=
    exists_row_left_of_stepdown (cz := cz) (m := m)
      (fun b hb hl => by
        obtain ⟨c', hc', hc'lev⟩ := hrow b hb hl
        exact exists_level_down_left hBfin hBne harea hlc hunimod hadj hperp hnu hmvl hmu'
          hb hc' hc'lev)
      hzc hLcz (by omega)
  exact ⟨b'', hb'', hb''lev, by
    have := hleft b₀ hb₀ hb₀lev
    omega⟩

/-- **洞 6（`hstrip`）的完整归约：两支合并成一条。**

原文：`b3_colle2.txt:786-804`（Claim 4.6）＋ Figure 10（`:798`）。

`RegionSteps.lean` 洞 6 的注释此前把 (O2) 分成 `L ≤ dot nℓ b` 与 `L > dot nℓ b` 两支，
并把后者记为「Claim 4.6 原文没写的那一步」。**那个分情形是多余的**，去掉它靠的是
把轮廓比较的基点从 `b` 换成 `cz`（`B` 的**底层**，`hcz` ＋ `hczmem` 保证取得到）：

```
dot m (z + (w − a₀)) = dot m b + s + dot m (z − a₀)      （s : ℕ，故 s ≥ 0）
                     ≥ dot m b₀    + dot m (z − a₀)      （hdesc：b 降到底层，m 不右移）
                     ≥ leftprof_B L                       （hprof）
```

而 `L` 的范围**免费**：`dot nℓ w < cz` 给 `dot nℓ w ≤ cz − 1`，于是
`L = dot nℓ w + dot nℓ (z − a₀) ≤ cz + dot nℓ (z − a₀) − 1`。
这一步正是上一版漏掉的耦合——`L` 是相对 `cz` 受控的，不是相对 `dot nℓ b`，
所以 `L > dot nℓ b` 根本不是一个需要单独处理的情形。

两条前提的原文对应：

* **`hdesc`** ＝ `:796` 的逐行下降走到底层：`b ∈ B` 沿 `u'` 一路降到 `ℓ_B^{(−)}` 所在层 `cz`，
  左轮廓不右移。生产者 ＝ `exists_level_down_left`（本文件，`hadj`＝`:764/:766` 循环序）
  的迭代 ＋ `hczmem`（`cz` 层非空）。逐个量词：`∀ b ∈ B` ＝ 原文 `A_k` 上的基点；
  `dot nℓ b₀ = cz` ＝ 「走到 `ℓ_B^{(−)}`」；`dot m b₀ ≤ dot m b` ＝ 「不右移」。
* **`hprof`** ＝ Figure 10 那句
  "knowledge of `T^u η` on `H_B(ℓ)` determines it on `A_1`" 的几何内容，即
  **`Ŝ_{φ_ι}` 从它的最低点 `a₀` 往上长的速度不慢于 `B` 从底层往上长的速度**。
  逐个量词：`∀ z ∈ Sw` ＝ 窗口的每个点（`Ŝ_{φ_ι}` 是 `𝒮_{φ_ι}` 的平移，`:798`）；
  `b₀` ＝ 底层的基点；`L ∈ [cz, cz + dot nℓ (z − a₀) − 1]` ＝ 落在 `B` 的层值域内
  （这一段同时吃掉了原 (O1) 的层上界，所以 (O1) **不再是独立义务**）；
  结论 ＝ 第 `L` 层有一个点不比 `b₀ + (z − a₀)` 更靠右。
  **为什么成立**（硬规矩 10）：`B` 是 `E(𝒮_φ)`-enveloped（`:777`，Def 3.2 `:402`），
  故 `E B = E 𝒮_φ`（`Enveloped.E_eq`，`LatticeEdges.lean:1657`）且 `B` 的每条边**不短于**
  `𝒮_φ` 的对应边；又 `E ↑Sw ⊆ E ↑𝒮_φ`（`hEsub`，`RegionSteps.lean:2557`）。
  左轮廓是关于层的凸折线，斜率序列 ＝ 左边法向的 `dot n u' / dot n vl` 排序，
  每个斜率用掉的层数 ＝ 该边的 `nℓ`-跨度。两边斜率序列同源而 `B` 的跨度更大，
  故从各自底层出发同样升 `Δ` 层时 `B` 升得更少。`dot m (z − a₀) ≥ leftprof_W δ − leftprof_W 0`
  则由 `hvlmin`（`a₀` 同时是窗口的最低点与 `m`-最左点）给出。

⚠ **本定理不含几何内容**，它是坐标改写 ＋ 上面那条算术。全部几何都在 `hprof` 里，
`hdesc` 的几何在 `exists_level_down_left`（已证）。所以洞 6 现在**只欠 `hprof` 一条**。 -/
theorem hstrip_of_profile {m : ℤ × ℤ} {Sw : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hmvl : dot m vl = 1) (hmu' : dot m u' = 0)
    (hdesc : ∀ b ∈ B, ∃ b₀ ∈ B, dot nℓ b₀ = cz ∧ dot m b₀ ≤ dot m b)
    (hprof : ∀ z ∈ Sw, ∀ b₀ ∈ B, dot nℓ b₀ = cz → ∀ L : ℤ, cz ≤ L →
      L ≤ cz + dot nℓ (z - a₀) - 1 →
      ∃ b'' ∈ B, dot nℓ b'' = L ∧ dot m b'' ≤ dot m b₀ + dot m (z - a₀)) :
    ∀ w ∈ coneRegion B vl u', dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ halfStrip B vl := by
  intro w hw hwlt z hz hL
  rw [Nivat.ConeRegion.mem_coneRegion_iff] at hw
  obtain ⟨b, hb, s, t, rfl⟩ := hw
  set W : ℤ × ℤ := b + (s : ℤ) • vl + (t : ℤ) • u' with hW
  have hlevW : dot nℓ W = dot nℓ b - (t : ℤ) :=
    dot_shift (nℓ := nℓ) (vl := vl) (u' := u') hperp hnu b (s : ℤ) (t : ℤ)
  have hmW : dot m W = dot m b + (s : ℤ) := by
    rw [hW, Nivat.LE2.dot_add, Nivat.LE2.dot_add, Nivat.ConeRegion.dot_zsmul,
      Nivat.ConeRegion.dot_zsmul, hmvl, hmu']
    ring
  have hlevP : dot nℓ (z + (W - a₀)) = dot nℓ W + dot nℓ (z - a₀) := by
    rw [Nivat.LE2.dot_add, Nivat.LE2.dot_sub, Nivat.LE2.dot_sub]; ring
  have hmP : dot m (z + (W - a₀)) = dot m W + dot m (z - a₀) := by
    rw [Nivat.LE2.dot_add, Nivat.LE2.dot_sub, Nivat.LE2.dot_sub]; ring
  have hs0 : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
  -- `b` 沿 `u'` 降到底层 `cz`，`m`-坐标不右移
  obtain ⟨b₀, hb₀, hb₀lev, hb₀m⟩ := hdesc b hb
  -- 从底层出发的轮廓比较；`L` 的上界由 `dot nℓ W < cz` 免费给出
  obtain ⟨b'', hb'', hb''lev, hb''m⟩ :=
    hprof z (Finset.mem_of_mem_erase hz) b₀ hb₀ hb₀lev (dot nℓ (z + (W - a₀))) hL (by omega)
  exact (mem_halfStrip_iff_level_left (B := B) hunimod hperp hnu hmvl hmu'
    (z + (W - a₀))).mpr ⟨b'', hb'', hb''lev, by omega⟩

/-- **`hfit` 的支撑函数形式**（纯机械，零几何）。

`B` 格凸 ＋ 正面积 ⟹ `B` 就是它自己那组边不等式的解集
（`Nivat.LE2.mem_of_dot_le_suppVal`，`LatticeEdges.lean:1393`）。于是
「`U` 平移 `c` 之后整块落进 `B`」只是每个边法向上的一条数值不等式。

原文：Definition 3.2（`b3_colle2.txt:402`）"for every edge `ϖ ∈ E(𝒯)`, there exists an
edge `w ∈ E(𝒰)` parallel to `ϖ`"——逐条边比较正是本引理把问题归约成的形状。 -/
theorem fit_of_suppVal_le {U : Set (ℤ × ℤ)} (hUfin : U.Finite) (hUne : U.Nonempty)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (harea : Nivat.LE2.PosArea B) (hlc : Nivat.IsLatticeConvexRegion B)
    {c : ℤ × ℤ}
    (h : ∀ n ∈ Nivat.LE2.E B, Nivat.LE2.suppVal U n + dot n c ≤ Nivat.LE2.suppVal B n) :
    ∀ z ∈ U, z + c ∈ B := by
  intro z hz
  refine Nivat.LE2.mem_of_dot_le_suppVal hBfin hBne harea hlc (fun n hn => ?_)
  have h1 : dot n z ≤ Nivat.LE2.suppVal U n := Nivat.LE2.le_suppVal hUfin hUne hz
  have h2 := h n hn
  have h3 : dot n (z + c) = dot n z + dot n c := Nivat.LE2.dot_add n z c
  omega

/-- **`B` 的左下角存在**（`hleft` 的生产者，纯有限性，无几何）。

原文：`b3_colle2.txt:780` 的 `H_B(ℓ)`——`ℓ_B` 是切割线，`cz` 那一层非空由链上的
`hczmem` 给出。本引理只是在那一层上取 `dot m` 的极小点。 -/
theorem exists_bottom_left {m : ℤ × ℤ} (hBfin : B.Finite)
    {b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ B) (hb₀lev : dot nℓ b₀ = cz) :
    ∃ g ∈ B, dot nℓ g = cz ∧ ∀ b ∈ B, dot nℓ b = cz → dot m g ≤ dot m b := by
  have hfin : {b | b ∈ B ∧ dot nℓ b = cz}.Finite := hBfin.subset (fun _ h => h.1)
  have hne : {b | b ∈ B ∧ dot nℓ b = cz}.Nonempty := ⟨b₀, hb₀, hb₀lev⟩
  obtain ⟨g, ⟨hgB, hglev⟩, hmin⟩ := hfin.exists_minimalFor (dot m) _ hne
  refine ⟨g, hgB, hglev, fun b hb hblev => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact absurd (hmin ⟨hb, hblev⟩ (le_of_lt hlt)) (by omega)

/-- **洞 6（`hstrip`，`RegionSteps.lean:2669`）的一条龙归约。**

原文：Claim 4.6 的 `b3_colle2.txt:786-804`。把 `hstrip_of_profile` / `hdesc_of_row` /
`hprof_of_fit` 三条串起来，剩下的前提只有两类：

* **`hrow`**（「`𝓡_{ι−1}` 与每条 `l_k` 都有交」，原文 `:796` 的 "Proceeding this way"
  默认成立）——由 `RowHit` / `EnvChord` / `FaceStep` 那条链兑现，根在
  `Enveloped.face_encard_le`（`LatticeEdges.lean:1664`）。
* **`hfit` / `hbase` / `hleft`**（贴着 `B` 左下角的窗口平移，原文 `:798` 的
  "a translation of `𝒮_{φ_ι}`"）——由 Def 3.2（`:402`）的 Minkowski 被加项性质兑现，
  **尚未形式化**，这是洞 6 仅存的几何内容。

⚠ **读法（硬规矩 3）**：本定理把几何**搬走**了，没有**消掉**。上一版注释说「两支合并成
一支」只对陈述形状成立；真正的难点先在 `hprof` 里，现在在 `hfit`/`hbase`/`hleft` 里。 -/
theorem hstrip_of_fit {m : ℤ × ℤ} {Sw : Finset (ℤ × ℤ)} {a₀ c : ℤ × ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (harea : Nivat.LE2.PosArea B) (hlc : Nivat.IsLatticeConvexRegion B)
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hadj : ∀ n ∈ Nivat.LE2.E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hmvl : dot m vl = 1) (hmu' : dot m u' = 0)
    (hczlow : ∀ b ∈ B, cz ≤ dot nℓ b)
    (hrow : ∀ b ∈ B, cz ≤ dot nℓ b - 1 → ∃ c' ∈ B, dot nℓ c' = dot nℓ b - 1)
    (hfit : ∀ z ∈ Sw, z + c ∈ B)
    (hbase : dot nℓ (a₀ + c) = cz)
    (hleft : ∀ b ∈ B, dot nℓ b = cz → dot m (a₀ + c) ≤ dot m b) :
    ∀ w ∈ coneRegion B vl u', dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ halfStrip B vl :=
  hstrip_of_profile (m := m) (Sw := Sw) (a₀ := a₀) hunimod hperp hnu hmvl hmu'
    (hdesc_of_row hBfin hBne harea hlc hunimod hadj hperp hnu hmvl hmu' hczlow hrow)
    (hprof_of_fit hBfin hBne harea hlc hunimod hadj hperp hnu hmvl hmu' hrow hfit hbase hleft)

/-- **洞 6 的最终形：残余只剩一条支撑函数不等式。**

把 `exists_bottom_left`（角点存在，有限性）、`fit_of_suppVal_le`（H-表示，机械）与
`hstrip_of_fit` 串起来之后，洞 6 只欠 `hsupp` 一条：

```
∀ n ∈ E B, suppVal Sw n + dot n (g − a₀) ≤ suppVal B n
```

其中 `g` 是 `B` 的左下角、`a₀` 是窗口 `Sw` 的左下角（`hstrict` ＋ `hvlmin` 选出的那个）。
移项就是**相对支撑函数的支配**：`suppVal Sw n − dot n a₀ ≤ suppVal B n − dot n g`，
即「从各自的角出发，`B` 在每个方向上伸得不比窗口近」。

原文对应（硬规矩 10，对齐的是理由）：这正是 Definition 3.2（`:402`）
"`|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|`" ＋ `Enveloped.E_eq`（`LatticeEdges.lean:1657`）的几何内容——
两个多边形边法向集合相同、`B` 的每条边不短，沿边界从角点走一圈时 `B` 每一步走得不比
窗口少，于是每个方向上的相对支撑函数都被支配。**这一步原文没写**，是 Claim 4.6
（`:786-804`）默认的那句 "we may place `Ŝ_{φ_ι}`"。 -/
theorem hstrip_of_suppVal {m : ℤ × ℤ} {Sw : Finset (ℤ × ℤ)} {a₀ g : ℤ × ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (harea : Nivat.LE2.PosArea B) (hlc : Nivat.IsLatticeConvexRegion B)
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hadj : ∀ n ∈ Nivat.LE2.E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1)
    (hmvl : dot m vl = 1) (hmu' : dot m u' = 0)
    (hczlow : ∀ b ∈ B, cz ≤ dot nℓ b)
    (hrow : ∀ b ∈ B, cz ≤ dot nℓ b - 1 → ∃ c' ∈ B, dot nℓ c' = dot nℓ b - 1)
    (hSwne : Sw.Nonempty)
    (hglev : dot nℓ g = cz)
    (hgleft : ∀ b ∈ B, dot nℓ b = cz → dot m g ≤ dot m b)
    (hsupp : ∀ n ∈ Nivat.LE2.E B,
      Nivat.LE2.suppVal (↑Sw : Set (ℤ × ℤ)) n + dot n (g - a₀) ≤ Nivat.LE2.suppVal B n) :
    ∀ w ∈ coneRegion B vl u', dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ halfStrip B vl := by
  have hga : a₀ + (g - a₀) = g := by abel
  refine hstrip_of_fit (m := m) (Sw := Sw) (a₀ := a₀) (c := g - a₀)
    hBfin hBne harea hlc hunimod hadj hperp hnu hmvl hmu' hczlow hrow
    (fun z hz => fit_of_suppVal_le (Sw.finite_toSet) (by exact_mod_cast hSwne)
      hBfin hBne harea hlc hsupp z hz)
    (by rw [hga]; exact hglev)
    (by rw [hga]; exact hgleft)

end Nivat.StripDescend
#print axioms Nivat.StripDescend.halfStrip_add_zsmul_vl
#print axioms Nivat.StripDescend.iterate_down
#print axioms Nivat.StripDescend.stripStep_of_place_of_down
#print axioms Nivat.StripDescend.place_of_down
#print axioms Nivat.StripDescend.mem_halfStrip_iff_level_left
#print axioms Nivat.StripDescend.halfStrip_down_of_stepdown
#print axioms Nivat.StripDescend.exists_level_down_left
#print axioms Nivat.StripDescend.halfStrip_down_of_adj
#print axioms Nivat.StripDescend.exists_row_left_of_stepdown
#print axioms Nivat.StripDescend.hdesc_of_row
#print axioms Nivat.StripDescend.hstrip_of_profile
#print axioms Nivat.StripDescend.exists_bottom_left
#print axioms Nivat.StripDescend.hprof_of_fit
#print axioms Nivat.StripDescend.hstrip_of_fit
#print axioms Nivat.StripDescend.fit_of_suppVal_le
#print axioms Nivat.StripDescend.hstrip_of_suppVal
