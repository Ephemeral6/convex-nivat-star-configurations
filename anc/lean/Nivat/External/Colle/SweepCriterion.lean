/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.HalfPlane
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.RegionConvex
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# 扫掠保持格凸性的判据（`b3_colle2.txt:806` / `:780` 的缺失论证）

原文：`b3_colle2.txt:806`

> For each integer `ι−m+1 ≤ i ≤ ι−2`, we define the `(-ℓ, ℓ_i)`-region
> `𝓡_i := {g + t·v⃗_{ℓ_i} ∈ ℤ² : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}`.

原文直接把 `𝓡_i` 叫作 region，**没有证明它是格凸的**；`:780`（Claim 4.6 的
`𝓡_{ι−1} = H_B(ℓ) + ℕ v⃗_{ℓ_{ι−1}}`）同理。按 `:31`（`𝒮 = conv(𝒮) ∩ ℤ²`）
这条断言一般**为假**——两个内核反例：

* `Colle41.not_isLatticeConvexRegion_sweep_quadrant`（`SweepNotRegion.lean:194`）：
  象限沿 `(2,−3)` 扫，`(1,−1)` 在凸包里不在集合里。打掉「补 `det ≠ 0` ＋ 锥内」。
* `SweepEdge.not_isLatticeConvexRegion_swept`（`SweepEdgeFail.lean`）：三角形
  `(0,0),(1,0),(7,20)` 沿**它自己的边方向** `(1,0)` 扫，`(7,13)` 在凸包里不在集合里。
  打掉「扫掠方向平行于被扫集合的一条边」。

本文件给**正面**判据，把那条断言归约成一条可检查的义务。

## 机制（这才是原文缺的那一步）

记 `w = toReal v`，`C` 是 `B` 的实凸包。`halfStrip B v` 的实凸包候选是
`sweepHull C v = C + ℝ≥0·w`。一个格点 `z ∈ sweepHull C v` 落进 `halfStrip B v`
当且仅当**能沿 `−w` 退回一个整数步**：`∃ t : ℕ, z − t·w ∈ C`（此时 `z − t·v ∈ B`，
因为 `B = toReal ⁻¹' C`）。

集合 `{r : ℝ | z − r·w ∈ C}` 由凸性是一个区间（弦）。所以：

* **`isLatticeConvexRegion_halfStrip_of_chord`**：弦上有非负整数 ⟹ 扫掠保持格凸。
* **`chord_of_unit_backstep`**：弦长 ≥ 1（存在 `s ≥ 0` 使 `s` 与 `s+1` 两个参数都在 `C` 里）
  ⟹ 弦上有非负整数，取 `t = ⌈s⌉₊`。

反例之所以是反例，正是因为弦长 < 1 且夹在两个整数之间：`SweepEdgeFail` 里 `y = 13`
那一层弦是 `[4.55, 4.9]`，长 0.35。

## 为什么原文那步还有救（写给 `OPEN.md #22`）

`v`-方向的弦长作为横向坐标的函数是**凹**的。若被扫集合在横向的**两个极端层**上都有
一条平行于 `v`、含 ≥ 2 个格点的边，凹性就把弦长在所有中间层上顶到 ≥ 1。
`𝒮_φ`（`φ = ∏(X^{h_i}−1)`）是 zonotope，边成 `±` 对出现；Def 3.2（`:402`）的
`|E(T)| = |E(𝒰)|` ＋ 每条边的格点数不少于对应边，正好给出**每个方向两侧各一条边**。
`SweepEdgeFail` 的三角形只有**一条** `(1,0)`-平行边（顶点 `(7,20)` 不是边），
所以它不满足 enveloped，打不到原文——**单侧不够，双侧才是原文的理由**。

本文件落地到「弦长处处 ≥ 1 ⟹ 扫掠保持格凸」为止（`unitCovered_of_long_chords`）。
**唯一剩下的缺口**是「双侧 `v`-平行边 ⟹ 弦长处处 ≥ 1」那步凹性论证，尚未形式化。
（`unitCovered_of_two_sided` 只覆盖 `C` 由两条段张成的特例，六边形那类两侧外凸的不在其内。）
-/

namespace Nivat.SweepCrit

open Nivat
open scoped Pointwise

/-- 扫掠集合 `halfStrip B v` 的实凸包候选：`C + ℝ≥0·toReal v`。 -/
def sweepHull (C : Set (ℝ × ℝ)) (v : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {q | ∃ c ∈ C, ∃ r : ℝ, 0 ≤ r ∧ q = c + r • toReal v}

theorem convex_sweepHull {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C) (v : ℤ × ℤ) :
    Convex ℝ (sweepHull C v) := by
  rintro _ ⟨c₁, hc₁, r₁, hr₁, rfl⟩ _ ⟨c₂, hc₂, r₂, hr₂, rfl⟩ a b ha hb hab
  refine ⟨a • c₁ + b • c₂, hconv hc₁ hc₂ ha hb hab, a * r₁ + b * r₂, by positivity, ?_⟩
  module

theorem subset_sweepHull {C : Set (ℝ × ℝ)} (v : ℤ × ℤ) : C ⊆ sweepHull C v :=
  fun c hc => ⟨c, hc, 0, le_rfl, by simp⟩

/-- `toReal` 与沿 `v` 的整数步平移相容。 -/
theorem toReal_sub_nsmul (z v : ℤ × ℤ) (t : ℕ) :
    toReal z - (t : ℝ) • toReal v = toReal (z - (t : ℤ) • v) := by
  simp only [toReal, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd]
  push_cast
  ring_nf

theorem toReal_add_nsmul (z v : ℤ × ℤ) (t : ℕ) :
    toReal (z + (t : ℤ) • v) = toReal z + (t : ℝ) • toReal v := by
  have h := toReal_sub_nsmul (z + (t : ℤ) • v) v t
  rw [add_sub_cancel_right] at h
  rw [← h]
  module

/-- **扫掠保持格凸性的弦判据。**

`B` 由闭凸 `C` 切出（`B = toReal ⁻¹' C`）。若 `sweepHull C v` 里的**每个格点**都能
沿 `−toReal v` 退回一个非负整数步落回 `C`，则 `halfStrip B v` 是格凸区域。

这条把原文 `b3_colle2.txt:806` 那句无证断言归约成唯一的一条义务 `hchord`；
`hchord` 一般**不成立**（见 `SweepEdgeFail.not_isLatticeConvexRegion_swept`），
所以它必须由 enveloped 条件另行兑现，不能当作定义的一部分白拿。 -/
theorem isLatticeConvexRegion_halfStrip_of_chord
    {B : Set (ℤ × ℤ)} {v : ℤ × ℤ} {C : Set (ℝ × ℝ)}
    (hconv : Convex ℝ C) (hBC : B = toReal ⁻¹' C)
    (hclosed : IsClosed (sweepHull C v))
    (hchord : ∀ z : ℤ × ℤ, toReal z ∈ sweepHull C v →
      ∃ t : ℕ, toReal z - (t : ℝ) • toReal v ∈ C) :
    IsLatticeConvexRegion (Nivat.LE2.halfStrip B v) := by
  refine ⟨sweepHull C v, convex_sweepHull hconv v, hclosed, ?_⟩
  ext z
  constructor
  · rintro ⟨b, hb, t, rfl⟩
    rw [hBC] at hb
    exact ⟨toReal b, hb, (t : ℝ), by positivity, toReal_add_nsmul b v t⟩
  · intro hz
    obtain ⟨t, ht⟩ := hchord z hz
    rw [toReal_sub_nsmul] at ht
    refine ⟨z - (t : ℤ) • v, ?_, t, by ring⟩
    rw [hBC]
    exact ht

/-- **弦长 ≥ 1 蕴含弦判据。**

若沿 `−toReal v` 存在一个**非负**参数 `s`，使 `s` 与 `s+1` 两处都落在 `C` 里，
则 `t = ⌈s⌉₊` 也落在 `C` 里（凸性 ＋ `s ≤ ⌈s⌉₊ ≤ s+1`）。

这是把几何「弦长 ≥ 1」翻成 `isLatticeConvexRegion_halfStrip_of_chord` 的 `hchord`
所需的全部内容；反例失败的正是这一条（`SweepEdgeFail` 中该层弦长 0.35）。 -/
theorem chord_of_unit_backstep
    {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C) {v z : ℤ × ℤ} {s : ℝ}
    (hs : 0 ≤ s) (h₀ : toReal z - s • toReal v ∈ C)
    (h₁ : toReal z - (s + 1) • toReal v ∈ C) :
    ∃ t : ℕ, toReal z - (t : ℝ) • toReal v ∈ C := by
  refine ⟨⌈s⌉₊, ?_⟩
  have hlo : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
  have hhi : (⌈s⌉₊ : ℝ) ≤ s + 1 := le_of_lt (Nat.ceil_lt_add_one hs)
  have ha : (0 : ℝ) ≤ s + 1 - (⌈s⌉₊ : ℝ) := by linarith
  have hb : (0 : ℝ) ≤ (⌈s⌉₊ : ℝ) - s := by linarith
  have hab : (s + 1 - (⌈s⌉₊ : ℝ)) + ((⌈s⌉₊ : ℝ) - s) = 1 := by ring
  have hmem := hconv h₀ h₁ ha hb hab
  have heq : (s + 1 - (⌈s⌉₊ : ℝ)) • (toReal z - s • toReal v)
      + ((⌈s⌉₊ : ℝ) - s) • (toReal z - (s + 1) • toReal v)
      = toReal z - (⌈s⌉₊ : ℝ) • toReal v := by
    have : (s + 1 - (⌈s⌉₊ : ℝ)) + ((⌈s⌉₊ : ℝ) - s) = 1 := by ring
    match_scalars <;> ring
  rwa [heq] at hmem

/-- `C` 被**单位 `v`-段覆盖**：每个点都落在一条含于 `C` 的、从 `p` 到 `p + toReal v` 的段上。

这是 `:806` 那步真正需要的几何前提。`𝒮_φ`（`φ = ∏(X^{h_i}−1)`）是 zonotope，边成 `±` 对
出现；Def 3.2（`:402`）的 `|E(T)| = |E(𝒰)|` ＋ 每条边格点数不少于对应边，给出 `B` 在
**每个方向的两侧各有一条边**，于是横向两个极端层上各有一条 `v`-平行单位段，弦长的凹性
把中间所有层都顶到 ≥ 1，再经 `unitCovered_of_long_chords` 得本谓词。 -/
def UnitCovered (C : Set (ℝ × ℝ)) (v : ℤ × ℤ) : Prop :=
  ∀ q ∈ C, ∃ p ∈ C, p + toReal v ∈ C ∧ ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧ q = p + μ • toReal v

/-- 单位段覆盖 ⟹ 弦判据。 -/
theorem chord_of_unitCovered
    {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C) {v : ℤ × ℤ} (hU : UnitCovered C v)
    (z : ℤ × ℤ) (hz : toReal z ∈ sweepHull C v) :
    ∃ t : ℕ, toReal z - (t : ℝ) • toReal v ∈ C := by
  obtain ⟨c, hc, r, hr, hzc⟩ := hz
  obtain ⟨p, hp, hpw, μ, hμ0, hμ1, hcp⟩ := hU c hc
  have hzp : toReal z = p + (μ + r) • toReal v := by rw [hzc, hcp]; module
  rcases le_or_gt 1 (μ + r) with h1 | h1
  · refine chord_of_unit_backstep hconv (v := v) (z := z) (s := μ + r - 1) (by linarith) ?_ ?_
    · have : toReal z - (μ + r - 1) • toReal v = p + toReal v := by rw [hzp]; module
      rw [this]; exact hpw
    · have : toReal z - (μ + r - 1 + 1) • toReal v = p := by rw [hzp]; module
      rw [this]; exact hp
  · refine ⟨0, ?_⟩
    have hmem := hconv hp hpw (show (0:ℝ) ≤ 1 - (μ + r) by linarith)
      (show (0:ℝ) ≤ μ + r by linarith) (by ring)
    have heq : (1 - (μ + r)) • p + (μ + r) • (p + toReal v)
        = toReal z - ((0 : ℕ) : ℝ) • toReal v := by
      rw [hzp]; push_cast; module
    rwa [heq] at hmem

/-- **双侧单位段 ⟹ 中间每一层都有单位段**（弦长凹性的初等写法）。

`x, x + v` 与 `y, y + v` 是 `C` 里横向两端的两条单位 `v`-段；它们的凸组合
`(1−λ)x + λy` 与 `(1−λ)(x+v) + λ(y+v) = (1−λ)x + λy + v` 又是一条单位段，
所以整个中间带都被覆盖。**反例之所以是反例，正是因为只有一端有段**：
`SweepEdgeFail` 的三角形顶点 `(7,20)` 是顶点不是边。 -/
theorem unitCovered_of_two_sided
    {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C) {v : ℤ × ℤ} {x y : ℝ × ℝ}
    (hx : x ∈ C) (hxw : x + toReal v ∈ C) (hy : y ∈ C) (hyw : y + toReal v ∈ C)
    (hspan : ∀ q ∈ C, ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧
      q = (1 - lam) • x + lam • y + μ • toReal v) :
    UnitCovered C v := by
  intro q hq
  obtain ⟨lam, hl0, hl1, μ, hμ0, hμ1, hqe⟩ := hspan q hq
  refine ⟨(1 - lam) • x + lam • y, hconv hx hy (by linarith) hl0 (by ring), ?_, μ, hμ0, hμ1, hqe⟩
  have hmem := hconv hxw hyw (show (0:ℝ) ≤ 1 - lam by linarith) hl0 (by ring)
  have heq : (1 - lam) • (x + toReal v) + lam • (y + toReal v)
      = (1 - lam) • x + lam • y + toReal v := by module
  rwa [heq] at hmem

/-- **每点都在一条长度 ≥ 1 的 `v`-弦上 ⟹ 单位段覆盖。**

这是 `UnitCovered` 的一般生产者（`unitCovered_of_two_sided` 只覆盖「`C` 由两条段张成」
那种平行四边形式的特例，六边形那类两侧顶点外凸的区域不在其内）。

前提就是几何上的「`v`-方向宽度处处 ≥ 1」。反例失败的正是这一条：`SweepEdgeFail` 里
`y = 13` 那层的弦是 `[4.55, 4.9]`，长 0.35。 -/
theorem unitCovered_of_long_chords
    {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C) {v : ℤ × ℤ}
    (hlong : ∀ q ∈ C, ∃ q₀ ∈ C, ∃ s : ℝ, 1 ≤ s ∧ q₀ + s • toReal v ∈ C ∧
      ∃ a : ℝ, 0 ≤ a ∧ a ≤ s ∧ q = q₀ + a • toReal v) :
    UnitCovered C v := by
  intro q hq
  obtain ⟨q₀, hq₀, s, hs, hqs, a, ha0, has, hqe⟩ := hlong q hq
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have hseg : ∀ b : ℝ, 0 ≤ b → b ≤ s → q₀ + b • toReal v ∈ C := by
    intro b hb0 hbs
    have hmem := hconv hq₀ hqs (show (0:ℝ) ≤ 1 - b / s by
        rw [sub_nonneg, div_le_one hs0]; exact hbs)
      (show (0:ℝ) ≤ b / s by positivity) (by ring)
    have heq : (1 - b / s) • q₀ + (b / s) • (q₀ + s • toReal v) = q₀ + b • toReal v := by
      -- `field_simp` 关掉一部分分量，`ring` 收尾剩下的；linter 的 `<;>` 提示可忽略。
      match_scalars <;> field_simp <;> ring
    rwa [heq] at hmem
  rcases le_or_gt a (s - 1) with h | h
  · refine ⟨q, hq, ?_, 0, le_rfl, zero_le_one, by simp⟩
    have heq : q + toReal v = q₀ + (a + 1) • toReal v := by rw [hqe]; module
    rw [heq]
    exact hseg (a + 1) (by linarith) (by linarith)
  · refine ⟨q₀ + (s - 1) • toReal v, hseg (s - 1) (by linarith) (by linarith), ?_,
      a - (s - 1), by linarith, by linarith, ?_⟩
    · have heq : q₀ + (s - 1) • toReal v + toReal v = q₀ + s • toReal v := by module
      rw [heq]; exact hqs
    · rw [hqe]; module

/-! ### 弦长凹性：`unitCovered_of_two_sided` 的去 `hspan` 版 -/

/-- `Colle35.ip` 在差上可加。私有，避免与 `Colle35` 日后可能补的同名引理撞名。 -/
private theorem ip_sub (n : ℤ × ℤ) (q q' : ℝ × ℝ) :
    Nivat.Colle35.ip n (q - q') = Nivat.Colle35.ip n q - Nivat.Colle35.ip n q' := by
  simp only [Nivat.Colle35.ip, Prod.fst_sub, Prod.snd_sub]; ring

/-- 两个都与非零整法向 `n` 正交的实向量必共线（二维）。 -/
theorem cross_eq_of_ip_zero {n : ℤ × ℤ} (hn : n ≠ 0) {v : ℤ × ℤ}
    (hperp : Nivat.LE2.dot n v = 0) {w : ℝ × ℝ} (hw : Nivat.Colle35.ip n w = 0) :
    w.1 * (v.2 : ℝ) = w.2 * (v.1 : ℝ) := by
  have hpv : (n.1 : ℝ) * (v.1 : ℝ) + (n.2 : ℝ) * (v.2 : ℝ) = 0 := by
    have : ((Nivat.LE2.dot n v : ℤ) : ℝ) = 0 := by rw [hperp]; norm_num
    simpa [Nivat.LE2.dot, Int.cast_add, Int.cast_mul] using this
  have hpw : (n.1 : ℝ) * w.1 + (n.2 : ℝ) * w.2 = 0 := hw
  have hn' : (n.1 : ℝ) ≠ 0 ∨ (n.2 : ℝ) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hn (Prod.ext (by exact_mod_cast hc.1) (by exact_mod_cast hc.2))
  rcases hn' with h1 | h2
  · have hz : (n.1 : ℝ) * (w.1 * (v.2 : ℝ) - w.2 * (v.1 : ℝ)) = 0 := by
      linear_combination (v.2 : ℝ) * hpw - w.2 * hpv
    have := (mul_eq_zero.mp hz).resolve_left h1
    linarith
  · have hz : (n.2 : ℝ) * (w.1 * (v.2 : ℝ) - w.2 * (v.1 : ℝ)) = 0 := by
      linear_combination w.1 * hpv - (v.1 : ℝ) * hpw
    have := (mul_eq_zero.mp hz).resolve_left h2
    linarith

/-- 共线化：`w ⟂ n`、`v ⟂ n`、`n ≠ 0`、`v ≠ 0` ⟹ `w = c • v`。 -/
theorem exists_smul_of_ip_zero {n : ℤ × ℤ} (hn : n ≠ 0) {v : ℤ × ℤ} (hv : v ≠ 0)
    (hperp : Nivat.LE2.dot n v = 0) {w : ℝ × ℝ} (hw : Nivat.Colle35.ip n w = 0) :
    ∃ c : ℝ, w = c • toReal v := by
  have hcross := cross_eq_of_ip_zero hn hperp hw
  by_cases hv2 : (v.2 : ℝ) = 0
  · have hv1 : (v.1 : ℝ) ≠ 0 := by
      intro h
      exact hv (Prod.ext (by exact_mod_cast h) (by exact_mod_cast hv2))
    have hw2 : w.2 = 0 := by
      rw [hv2, mul_zero] at hcross
      exact (mul_eq_zero.mp hcross.symm).resolve_right hv1
    refine ⟨w.1 / (v.1 : ℝ), ?_⟩
    refine Prod.ext ?_ ?_ <;>
      simp only [toReal, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · field_simp
    · simp [hw2, hv2]
  · refine ⟨w.2 / (v.2 : ℝ), ?_⟩
    refine Prod.ext ?_ ?_ <;>
      simp only [toReal, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · field_simp
      linarith [hcross]
    · field_simp

/-- **弦长凹性，一般形（`unitCovered_of_two_sided` 的 `hspan`-free 替代）。**

原文：`b3_colle2.txt:806` 那句无证断言（扫掠保持格凸）所需的几何前提；两条对置单位段
的来源是 Definition 3.2（`:402`）的 enveloped——`|E(B)| = |E(𝒰)|` 且每条边的格点数不少于
对应边，于是 `B` 在**每个方向的两侧各有一条边**，特别地在 `n` 的极大面与极小面上各有一条
`v`-平行的单位段。

逐个量词的对应：`n` ＝ 定义 `:402` 里那个方向（`E` 的一条法向）；`x` ＝ `n`-极大面上
那条单位段的起点（`hxmax` 就是「在极大面上」）；`y` ＝ `n`-极小面上那条的起点
（`hymin`）；`hperp : dot n v = 0` ＝ 「段与 `n` 的面平行」，即 `v` 是该面的边方向。

与 `unitCovered_of_two_sided` 的差别是**去掉了 `hspan`**（`q = (1−λ)x + λy + μ•v`）。
`hspan` 只在 `C` 是由两条段张成的平行四边形时成立，六边形那类两侧顶点外凸的区域不在其内，
而 `𝒮_φ` 正是 zonotope、一般就是六边形以上。

去掉它的办法：在 `q` 的 `n`-层上用**一次**凸组合造出中间段 `p, p + v`，
而**始终不把 `q` 本身写进那个组合**——`q` 改由沿 `v` 平移到达，
这正是原先需要 `hspan` 的那一步。`q − p ⟂ n` 由 `hip_p` 给出，
`exists_smul_of_ip_zero` 把它变成 `q = p + c • v`，再按 `c ≤ 0 / 0 < c ≤ 1 / c > 1`
三分接到 `unitCovered_of_long_chords`。 -/
theorem unitCovered_of_opposite_segments
    {C : Set (ℝ × ℝ)} {v n : ℤ × ℤ} {x y : ℝ × ℝ}
    (hconv : Convex ℝ C) (hn_ne : n ≠ 0) (hv_ne : v ≠ 0) (hperp : Nivat.LE2.dot n v = 0)
    (hx : x ∈ C) (hxw : x + toReal v ∈ C)
    (hxmax : ∀ q ∈ C, Nivat.Colle35.ip n q ≤ Nivat.Colle35.ip n x)
    (hy : y ∈ C) (hyw : y + toReal v ∈ C)
    (hymin : ∀ q ∈ C, Nivat.Colle35.ip n y ≤ Nivat.Colle35.ip n q) :
    UnitCovered C v := by
  refine unitCovered_of_long_chords hconv ?_
  intro q hq
  have hlo : Nivat.Colle35.ip n y ≤ Nivat.Colle35.ip n q := hymin q hq
  have hhi : Nivat.Colle35.ip n q ≤ Nivat.Colle35.ip n x := hxmax q hq
  -- 把 `p` 放到 `q` 所在层的插值参数
  obtain ⟨θ, hθ0, hθ1, hθs⟩ :
      ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
        (1 - θ) * Nivat.Colle35.ip n y + θ * Nivat.Colle35.ip n x = Nivat.Colle35.ip n q := by
    rcases eq_or_lt_of_le (hymin x hx) with heq | hlt
    · exact ⟨0, le_rfl, zero_le_one, by simp; linarith⟩
    · refine ⟨(Nivat.Colle35.ip n q - Nivat.Colle35.ip n y) /
        (Nivat.Colle35.ip n x - Nivat.Colle35.ip n y), by apply div_nonneg <;> linarith,
        by rw [div_le_one (by linarith)]; linarith, ?_⟩
      field_simp
      ring
  set p : ℝ × ℝ := (1 - θ) • y + θ • x with hp_def
  have hp : p ∈ C := hconv hy hx (by linarith) hθ0 (by ring)
  have hpw : p + toReal v ∈ C := by
    have heq : p + toReal v = (1 - θ) • (y + toReal v) + θ • (x + toReal v) := by
      rw [hp_def]; module
    rw [heq]; exact hconv hyw hxw (by linarith) hθ0 (by ring)
  -- `p` 与 `q` 同层，故 `q − p ⟂ n`
  have hip_p : Nivat.Colle35.ip n p = Nivat.Colle35.ip n q := by
    rw [hp_def, Nivat.Colle35.ip_add, Nivat.Colle35.ip_smul, Nivat.Colle35.ip_smul]
    exact hθs
  obtain ⟨c, hc⟩ := exists_smul_of_ip_zero hn_ne hv_ne hperp
    (w := q - p) (by rw [ip_sub, hip_p]; ring)
  have hq_eq : q = p + c • toReal v := by
    have := hc
    rw [sub_eq_iff_eq_add] at this
    rw [this]; abel
  -- 沿 `v` 平移，造出过 `q` 的长度 ≥ 1 的弦
  rcases le_or_gt c 0 with hcle | hcpos
  · refine ⟨q, hq, 1 - c, by linarith, ?_, 0, le_rfl, by linarith, by simp⟩
    have heq : q + (1 - c) • toReal v = p + toReal v := by rw [hq_eq]; module
    rw [heq]; exact hpw
  · rcases le_or_gt c 1 with hcle1 | hcgt1
    · exact ⟨p, hp, 1, le_rfl, by simpa using hpw, c, by linarith, hcle1, hq_eq⟩
    · refine ⟨p, hp, c, by linarith, ?_, c, by linarith, le_rfl, hq_eq⟩
      rw [← hq_eq]; exact hq

/-- **一条边上的两个格点 ⟹ 这条边上有一个单位 `v`-步。**

原文：Definition 3.2（`b3_colle2.txt:402`）只说 `B` 的每条边**格点数不少于**对应边
（`Nivat.LE2.Enveloped.face_encard_le`），即该面上至少有两个格点；`unitCovered_convHullOf_of_faces`
要的却是**相邻**的一对 `c, c + v`。本引理补上这一步。

逐个量词的对应：`n` ＝ `:402` 里那条边的法向；`a, b` ＝ 该边上任意两个不同格点（`:402`
的 `|face| ≥ 2` 直接给出）；`v` ＝ 该边的本原方向（`hperp : dot n v = 0`）。
结论里的 `c` 不由原文指定——原文只需要「存在」，我们取的是 `a` 或 `b` 中靠后的那个。

证明是**纯整数**的，不走实凸包：`a, b` 同在面上 ⟹ `dot n (b - a) = 0` ⟹
`det v (b - a) = 0`（`LatticeEdges.lean:110`）⟹ `b - a = k • v`（`v` 本原）。取 `k > 0` 的一侧，
则对每个 `n' ∈ E B` 有 `k • dot n' v = dot n' b - dot n' a`，于是
`dot n' (a + v) ≤ suppVal B n'` 由 `dot n' v` 的符号分情况即得（`dot n' v < 0` 时平凡；
`≥ 0` 时用 `dot n' v ≤ k * dot n' v`）。再由 `mem_of_dot_le_suppVal`（`:1393`）得 `a + v ∈ B`。
⚠ 走实数会撞上 `toReal ((k : ℤ) • v)` 不自动化简的转型摩擦；整数路线绕开它。 -/
theorem exists_unit_step_in_face {B : Set (ℤ × ℤ)} (hBfin : B.Finite) (hBne : B.Nonempty)
    (harea : Nivat.LE2.PosArea B) (hlc : Nivat.IsLatticeConvexRegion B)
    {n v : ℤ × ℤ} (hn : n ≠ 0) (hvp : Nivat.Primitive v) (hperp : Nivat.LE2.dot n v = 0)
    {a b : ℤ × ℤ} (ha : a ∈ Nivat.LE2.face B n) (hb : b ∈ Nivat.LE2.face B n) (hab : a ≠ b) :
    ∃ c ∈ Nivat.LE2.face B n, c + v ∈ Nivat.LE2.face B n := by
  -- 主步：`k > 0` 且 `b - a = k • v` 时，`a` 与 `a + v` 都在面上。
  have main : ∀ {a' b' : ℤ × ℤ} {k : ℤ}, a' ∈ Nivat.LE2.face B n → b' ∈ Nivat.LE2.face B n →
      0 < k → b' - a' = k • v → ∃ c ∈ Nivat.LE2.face B n, c + v ∈ Nivat.LE2.face B n := by
    intro a' b' k ha' hb' hk hba
    have hmem : a' + v ∈ B := by
      refine Nivat.LE2.mem_of_dot_le_suppVal hBfin hBne harea hlc (fun n' hn' => ?_)
      have h1 : Nivat.LE2.dot n' a' ≤ Nivat.LE2.suppVal B n' :=
        Nivat.LE2.le_suppVal hBfin hBne ha'.1
      have h2 : Nivat.LE2.dot n' b' ≤ Nivat.LE2.suppVal B n' :=
        Nivat.LE2.le_suppVal hBfin hBne hb'.1
      have hzs : Nivat.LE2.dot n' (k • v) = k * Nivat.LE2.dot n' v := by
        unfold Nivat.LE2.dot
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have h3 : Nivat.LE2.dot n' b' - Nivat.LE2.dot n' a' = k * Nivat.LE2.dot n' v := by
        rw [← Nivat.LE2.dot_sub, hba, hzs]
      have h5 : Nivat.LE2.dot n' (a' + v) = Nivat.LE2.dot n' a' + Nivat.LE2.dot n' v :=
        Nivat.LE2.dot_add n' a' v
      rcases le_or_gt 0 (Nivat.LE2.dot n' v) with hV | hV
      · have hstep : Nivat.LE2.dot n' v ≤ k * Nivat.LE2.dot n' v := by nlinarith
        omega
      · omega
    have hdoteq : Nivat.LE2.dot n (a' + v) = Nivat.LE2.dot n a' := by
      rw [Nivat.LE2.dot_add, hperp]; ring
    exact ⟨a', ha', hmem, fun y hy => by rw [hdoteq]; exact ha'.2 y hy⟩
  -- `a`、`b` 同面 ⟹ 差与 `n` 正交 ⟹ 与 `v` 平行 ⟹ 是 `v` 的整数倍。
  have hdotab : Nivat.LE2.dot n (b - a) = 0 := by
    rw [Nivat.LE2.dot_sub, Nivat.LE2.dot_eq_of_mem_face ha hb]; ring
  obtain ⟨k, hk⟩ :=
    Nivat.eq_zsmul_of_det_eq_zero hvp (Nivat.LE2.det_eq_zero_of_dot_eq_zero hn hperp hdotab)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_eq_zero] at hk
    exact hab hk.symm
  rcases lt_or_gt_of_ne hk0 with hneg | hpos
  · refine main hb ha (k := -k) (by omega) ?_
    rw [neg_smul, ← hk]; abel
  · exact main ha hb hpos hk

/-- **`hrow`：`cz` 与顶层之间每一行都非空。**

原文：`b3_colle2.txt:794-796`。那里写 `A₁ := 𝓡_{ι−1} ∩ l₁`、`A₂ := 𝓡_{ι−1} ∩ l₂`，
接着 "Proceeding this way, we get by induction"——**默认每条 `l_k` 与 `𝓡_{ι−1}` 有交**，
这一步原文没证。本引理就是它。

逐个量词：`b` ＝ 原文归纳里当前那条线 `l_k` 上的点；结论的 `c` ＝ 下一条线
`l_{k+1} := l_k^{(−)}` 上的点；`b₀` ＝ 归纳的下界（`hlow` 保证还没走到底，
对应原文 "proceeding this way" 的终止条件）；`nℓ` ＝ `ℓ` 的法向，`vl` ＝ `ℓ` 的方向；
`u'` ＝ 下降一层的步（`hnu : dot nℓ u' = -1`）。

⚠ **这条必须走实凸包，整数路线不可能。** 从 `b` 到 `b₀` 的线段与第 `dot nℓ b - 1` 层的
交点一般**不是格点**，所以 `IsLatticeConvexRegion` 单独给不出任何东西；真正的内容是
「该层上的弦长 ≥ 1」，即 `UnitCovered`。反面见证：`B = Conv{(0,0),(3,1),(1,3)} ∩ ℤ²`、
`nℓ = (1,1)` 本原、`PosArea` 成立、格凸，但只有第 0 层与第 4 层有格点，第 1 层是空的
——`hrow` 在没有 enveloped 条件时**就是假的**。

证明：取层 `dot nℓ b - 1` 上的实点 `q`（`b` 与 `b₀` 的凸组合），`hU` 给出含 `q` 的单位
`vl`-段 `[p, p + vl] ⊆ Conv B`；`p` 与格点 `b + u'` 同层，故 `p = toReal (b+u') + σ • vl`；
取 `k := ⌈σ⌉ ∈ [σ, σ+1]`，则 `b + u' + k • vl` 的实像落在该段上，由格凸回到 `B`。 -/
theorem exists_level_down_of_unitCovered {B : Set (ℤ × ℤ)}
    (hlc : Nivat.IsLatticeConvexRegion B)
    {nℓ vl u' : ℤ × ℤ} (hn : nℓ ≠ 0) (hvl : vl ≠ 0)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hU : UnitCovered (Nivat.convHullOf B) vl)
    {b b₀ : ℤ × ℤ} (hb : b ∈ B) (hb₀ : b₀ ∈ B)
    (hlow : Nivat.LE2.dot nℓ b₀ < Nivat.LE2.dot nℓ b) :
    ∃ c ∈ B, Nivat.LE2.dot nℓ c = Nivat.LE2.dot nℓ b - 1 := by
  classical
  have hconv : Convex ℝ (Nivat.convHullOf B) := Nivat.LE2.convex_convHullOf B
  -- `ip` 与 `dot` 在格点上一致。
  have hip : ∀ (n z : ℤ × ℤ), Nivat.Colle35.ip n (Nivat.toReal z) = (Nivat.LE2.dot n z : ℝ) := by
    intro n z
    simp only [Nivat.Colle35.ip, Nivat.toReal, Nivat.LE2.dot]
    push_cast; ring
  set d : ℤ := Nivat.LE2.dot nℓ b - Nivat.LE2.dot nℓ b₀ with hd
  have hd1 : (1 : ℤ) ≤ d := by omega
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  set lam : ℝ := 1 / (d : ℝ) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlam, div_le_one (by linarith)]; linarith
  -- 层 `dot nℓ b - 1` 上的实点。
  set q : ℝ × ℝ := (1 - lam) • Nivat.toReal b + lam • Nivat.toReal b₀ with hq
  have hqmem : q ∈ Nivat.convHullOf B :=
    hconv (Nivat.LE2.toReal_mem_convHullOf hb) (Nivat.LE2.toReal_mem_convHullOf hb₀)
      (by linarith) hlam0 (by ring)
  have hipq : Nivat.Colle35.ip nℓ q = (Nivat.LE2.dot nℓ b : ℝ) - 1 := by
    have hexp : Nivat.Colle35.ip nℓ q
        = (1 - lam) * Nivat.Colle35.ip nℓ (Nivat.toReal b)
          + lam * Nivat.Colle35.ip nℓ (Nivat.toReal b₀) := by
      simp only [hq, Nivat.Colle35.ip, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      ring
    rw [hexp, hip, hip]
    have hne : (d : ℝ) ≠ 0 := by linarith
    have hdcast : (Nivat.LE2.dot nℓ b : ℝ) - (Nivat.LE2.dot nℓ b₀ : ℝ) = (d : ℝ) := by
      rw [hd]; push_cast; ring
    have key : (1 - lam) * (Nivat.LE2.dot nℓ b : ℝ) + lam * (Nivat.LE2.dot nℓ b₀ : ℝ)
        = (Nivat.LE2.dot nℓ b : ℝ)
          - lam * ((Nivat.LE2.dot nℓ b : ℝ) - (Nivat.LE2.dot nℓ b₀ : ℝ)) := by ring
    rw [key, hdcast, hlam]
    field_simp
  -- 单位 `vl`-段。
  obtain ⟨p, hp, hpw, μ, _hμ0, _hμ1, hqe⟩ := hU q hqmem
  have hipvl : Nivat.Colle35.ip nℓ (Nivat.toReal vl) = 0 := by rw [hip, hperp]; norm_num
  have hipp : Nivat.Colle35.ip nℓ p = (Nivat.LE2.dot nℓ b : ℝ) - 1 := by
    have : Nivat.Colle35.ip nℓ q = Nivat.Colle35.ip nℓ p + μ * Nivat.Colle35.ip nℓ (Nivat.toReal vl) := by
      rw [hqe]
      simp only [Nivat.Colle35.ip, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      ring
    rw [hipvl, mul_zero, add_zero] at this
    rw [← this, hipq]
  -- `p` 与格点 `b + u'` 同层 ⟹ 差是 `vl` 的实倍数。
  have hlevw : Nivat.LE2.dot nℓ (b + u') = Nivat.LE2.dot nℓ b - 1 := by
    rw [Nivat.LE2.dot_add, hnu]; ring
  have hzero : Nivat.Colle35.ip nℓ (p - Nivat.toReal (b + u')) = 0 := by
    have hsub : Nivat.Colle35.ip nℓ (p - Nivat.toReal (b + u'))
        = Nivat.Colle35.ip nℓ p - Nivat.Colle35.ip nℓ (Nivat.toReal (b + u')) := by
      simp only [Nivat.Colle35.ip, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hsub, hipp, hip, hlevw]
    push_cast; ring
  obtain ⟨σ, hσ⟩ := exists_smul_of_ip_zero hn hvl hperp hzero
  -- 取 `k := ⌈σ⌉`，落在 `[σ, σ+1]`。
  refine ⟨b + u' + (⌈σ⌉ : ℤ) • vl, ?_, ?_⟩
  · -- 格凸：实像在段 `[p, p + vl]` 上。
    have hlo : σ ≤ (⌈σ⌉ : ℝ) := Int.le_ceil σ
    have hhi : (⌈σ⌉ : ℝ) ≤ σ + 1 := le_of_lt (Int.ceil_lt_add_one σ)
    set t : ℝ := (⌈σ⌉ : ℝ) - σ with ht
    have ht0 : 0 ≤ t := by rw [ht]; linarith
    have ht1 : t ≤ 1 := by rw [ht]; linarith
    have hmem := hconv hp hpw (show (0:ℝ) ≤ 1 - t by linarith) ht0 (by ring)
    have hreal : Nivat.toReal (b + u' + (⌈σ⌉ : ℤ) • vl)
        = (1 - t) • p + t • (p + Nivat.toReal vl) := by
      have hstep : Nivat.toReal (b + u' + (⌈σ⌉ : ℤ) • vl)
          = Nivat.toReal (b + u') + ((⌈σ⌉ : ℤ) : ℝ) • Nivat.toReal vl := by
        refine Prod.ext ?_ ?_ <;>
          simp only [Nivat.toReal, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
            smul_eq_mul] <;> push_cast <;> ring
      have hp' : Nivat.toReal (b + u') = p - σ • Nivat.toReal vl := by
        rw [← hσ]; abel
      rw [hstep, hp', ht]
      push_cast
      module
    rw [Nivat.eq_preimage_convHullOf hlc]
    show Nivat.toReal (b + u' + (⌈σ⌉ : ℤ) • vl) ∈ Nivat.convHullOf B
    rw [hreal]
    exact hmem
  · have hzs : Nivat.LE2.dot nℓ ((⌈σ⌉ : ℤ) • vl) = (⌈σ⌉ : ℤ) * Nivat.LE2.dot nℓ vl := by
      unfold Nivat.LE2.dot
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [Nivat.LE2.dot_add, hzs, hperp, hlevw]
    ring

/-- **把「两条对置单位段」换成 `B` 的两个对置面上的格点对。**

`unitCovered_of_opposite_segments` 的前提是实数形式（`x, x + toReal v` 落在实凸包里，
且 `x` 在 `n`-极大层）。链上真正拿得到的却是**格点**形式：Definition 3.2（`:402`）的
enveloped 给出 `|E(B)| = |E(𝒰)|`（`Nivat.LE2.Enveloped.E_eq`）＋每条边的格点数不少于
对应边（`Enveloped.face_encard_le`），于是 `face B n` 与 `face B (-n)` 上各有 ≥ 2 个格点，
相邻两点之差就是 `v`。本引理做的就是这一步翻译，没有别的内容。

逐个量词的对应：`n` ＝ `:402` 里那个方向；`a, a + v ∈ face B n` ＝ `n`-极大面上那条边的
两个相邻格点；`b, b + v ∈ face B (-n)` ＝ 对面那条；`hperp : dot n v = 0` ＝ 「`v` 沿着
这两个面」，即 `v` 是该边方向。

`hxmax` / `hymin`（「在极大 / 极小层上」）由 `convHullOf_subset_realHalfPlaneLE`
＋ `suppVal_eq` 免费得到：面上的点把支撑值取满，实凸包整体被该半平面压住。 -/
theorem unitCovered_convHullOf_of_faces {B : Set (ℤ × ℤ)} {n v : ℤ × ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hn : n ≠ 0) (hv : v ≠ 0) (hperp : Nivat.LE2.dot n v = 0)
    {a : ℤ × ℤ} (ha : a ∈ Nivat.LE2.face B n) (haw : a + v ∈ Nivat.LE2.face B n)
    {b : ℤ × ℤ} (hb : b ∈ Nivat.LE2.face B (-n)) (hbw : b + v ∈ Nivat.LE2.face B (-n)) :
    UnitCovered (Nivat.convHullOf B) v := by
  apply unitCovered_of_opposite_segments
    (C := Nivat.convHullOf B) (x := Nivat.toReal a) (y := Nivat.toReal b)
  · exact Nivat.LE2.convex_convHullOf B
  · exact hn
  · exact hv
  · exact hperp
  · exact Nivat.LE2.toReal_mem_convHullOf (Nivat.LE2.face_subset _ _ ha)
  · have heq : Nivat.toReal (a + v) = Nivat.toReal a + Nivat.toReal v := by
      simp only [Nivat.toReal, Prod.fst_add, Prod.snd_add]
      push_cast
      rfl
    rw [← heq]
    exact Nivat.LE2.toReal_mem_convHullOf (Nivat.LE2.face_subset _ _ haw)
  · intro q hq
    have h1 := Nivat.LE2.convHullOf_subset_realHalfPlaneLE hBfin hBne n hq
    simp only [Nivat.LE2.mem_realHalfPlaneLE] at h1
    have h2 := Nivat.LE2.suppVal_eq ha
    rw [h2] at h1
    have h3 : (Nivat.LE2.dot n a : ℝ) = Nivat.Colle35.ip n (Nivat.toReal a) := by
      simp only [Nivat.Colle35.ip, Nivat.LE2.dot, Nivat.toReal]
      push_cast; ring
    rw [h3] at h1
    exact h1
  · exact Nivat.LE2.toReal_mem_convHullOf (Nivat.LE2.face_subset _ _ hb)
  · have heq : Nivat.toReal (b + v) = Nivat.toReal b + Nivat.toReal v := by
      simp only [Nivat.toReal, Prod.fst_add, Prod.snd_add]
      push_cast
      rfl
    rw [← heq]
    exact Nivat.LE2.toReal_mem_convHullOf (Nivat.LE2.face_subset _ _ hbw)
  · intro q hq
    have h1 := Nivat.LE2.convHullOf_subset_realHalfPlaneLE hBfin hBne (-n) hq
    simp only [Nivat.LE2.mem_realHalfPlaneLE, Prod.fst_neg, Prod.snd_neg, Int.cast_neg] at h1
    have h2 := Nivat.LE2.suppVal_eq hb
    rw [h2] at h1
    have hdot : (Nivat.LE2.dot (-n) b : ℝ)
        = ((-n).1 : ℝ) * (b.1 : ℝ) + ((-n).2 : ℝ) * (b.2 : ℝ) := by
      simp only [Nivat.LE2.dot]; push_cast; ring
    rw [hdot] at h1
    simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg] at h1
    simp only [Nivat.Colle35.ip, Nivat.toReal]
    linarith

/-- **`b3_colle2.txt:806` 的可用形式。**

`B` 由闭凸 `C` 切出，`C` 被单位 `v`-段覆盖 ⟹ `halfStrip B v` 仍是格凸区域。
这是原文那句无证断言在补上 enveloped 的**双侧**性之后的正确陈述。 -/
theorem isLatticeConvexRegion_halfStrip_of_unitCovered
    {B : Set (ℤ × ℤ)} {v : ℤ × ℤ} {C : Set (ℝ × ℝ)}
    (hconv : Convex ℝ C) (hBC : B = toReal ⁻¹' C)
    (hclosed : IsClosed (sweepHull C v)) (hU : UnitCovered C v) :
    IsLatticeConvexRegion (Nivat.LE2.halfStrip B v) :=
  isLatticeConvexRegion_halfStrip_of_chord hconv hBC hclosed (chord_of_unitCovered hconv hU)

/-- **洞 6 的 `hrow` 完全归约：只剩「`B` 的 `±nℓ` 两个面上各有两个不同格点」。**

原文：`b3_colle2.txt:794-796` 的逐行下降默认每条 `l_k` 与 `𝓡_{ι−1}` 有交（见
`exists_level_down_of_unitCovered` 的 docstring）；本引理把那一步**整条**接到
Definition 3.2（`:402`）的 `|ϖ ∩ 𝒯| ≥ |w ∩ 𝒰|` 上。

逐个量词：`htop` / `hbot` ＝ Def 3.2 那条边计数不等式在 `n = ±nℓ` 两个方向上的实例
（`Nivat.LE2.Enveloped.face_encard_le`，`LatticeEdges.lean:1664`，配 `𝒮_φ` 的
`nℓ`-面含生成元 `h_{ι₀} ∥ vl` 给出的两个点）；`hczmem` ＝ 底层非空，链上由
`exists_cutLevel` 白给；其余是 `(vl, u')` 幺模基的常备绑定。

三步：面上两点 ⟹ 相邻一对（`exists_unit_step_in_face`）⟹ 双侧单位段 ⟹
`UnitCovered`（`unitCovered_convHullOf_of_faces`）⟹ 逐行下降
（`exists_level_down_of_unitCovered`）。 -/
theorem hrow_of_two_in_faces {B : Set (ℤ × ℤ)} {nℓ vl u' : ℤ × ℤ}
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (harea : Nivat.LE2.PosArea B) (hlc : Nivat.IsLatticeConvexRegion B)
    (hn : nℓ ≠ 0) (hvlp : Nivat.Primitive vl) (hvl : vl ≠ 0)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hnu : Nivat.LE2.dot nℓ u' = -1)
    (htop : ∃ a b, a ∈ Nivat.LE2.face B nℓ ∧ b ∈ Nivat.LE2.face B nℓ ∧ a ≠ b)
    (hbot : ∃ a b, a ∈ Nivat.LE2.face B (-nℓ) ∧ b ∈ Nivat.LE2.face B (-nℓ) ∧ a ≠ b)
    {cz : ℤ} (hczmem : ∃ b ∈ B, Nivat.LE2.dot nℓ b = cz) :
    ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b - 1 →
      ∃ c ∈ B, Nivat.LE2.dot nℓ c = Nivat.LE2.dot nℓ b - 1 := by
  obtain ⟨a1, a2, ha1, ha2, ha12⟩ := htop
  obtain ⟨b1, b2, hb1, hb2, hb12⟩ := hbot
  obtain ⟨ca, hca, hcaw⟩ :=
    exists_unit_step_in_face hBfin hBne harea hlc hn hvlp hperp ha1 ha2 ha12
  have hnneg : (-nℓ) ≠ 0 := by simpa using hn
  have hperp' : Nivat.LE2.dot (-nℓ) vl = 0 := by
    unfold Nivat.LE2.dot at hperp ⊢
    simp only [Prod.fst_neg, Prod.snd_neg]
    linarith
  obtain ⟨cb, hcb, hcbw⟩ :=
    exists_unit_step_in_face hBfin hBne harea hlc hnneg hvlp hperp' hb1 hb2 hb12
  have hUC : UnitCovered (Nivat.convHullOf B) vl :=
    unitCovered_convHullOf_of_faces hBfin hBne hn hvl hperp hca hcaw hcb hcbw
  intro b hb hlev
  obtain ⟨b₀, hb₀, hb₀lev⟩ := hczmem
  exact exists_level_down_of_unitCovered hlc hn hvl hperp hnu hUC hb hb₀ (by omega)

/-- **Definition 3.2 的边计数不等式，用成「两个格点」的形式。**

原文：`b3_colle2.txt:402`，Definition 3.2 的 `|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|`——`𝒯` 的每条边上的
格点数不少于 `𝒰` 对应边上的。本引理就是它在「≥ 2」这一档的实例化。

逐个量词：`U` ＝ 原文的 `𝒰`（链上是 `𝒮_φ`）；`T` ＝ 原文的 `𝒯`（链上是 `B`）；
`n` ＝ 原文那条边 `w` 的法向；`htwo` ＝ `|w ∩ 𝒰| ≥ 2`。 -/
theorem exists_two_in_face_of_enveloped {U T : Set (ℤ × ℤ)}
    (hUE : (Nivat.LE2.E U).Finite) (henv : Nivat.LE2.Enveloped U T)
    {n : ℤ × ℤ} (hn : n ∈ Nivat.LE2.E U)
    (htwo : ∃ a b, a ∈ Nivat.LE2.face U n ∧ b ∈ Nivat.LE2.face U n ∧ a ≠ b) :
    ∃ a b, a ∈ Nivat.LE2.face T n ∧ b ∈ Nivat.LE2.face T n ∧ a ≠ b := by
  obtain ⟨a, b, ha, hb, hab⟩ := htwo
  have hUnt : (Nivat.LE2.face U n).Nontrivial := ⟨a, ha, b, hb, hab⟩
  have h1 : (1 : ℕ∞) < (Nivat.LE2.face U n).encard :=
    Set.one_lt_encard_iff_nontrivial.mpr hUnt
  have h2 : (1 : ℕ∞) < (Nivat.LE2.face T n).encard :=
    lt_of_lt_of_le h1 (Nivat.LE2.Enveloped.face_encard_le hUE henv hn)
  obtain ⟨a', ha', b', hb', hab'⟩ := Set.one_lt_encard_iff_nontrivial.mp h2
  exact ⟨a', b', ha', hb', hab'⟩

/-- **`hrow` from enveloped condition (洞 6 的 `hrow` 完整证明)。**

原文：`b3_colle2.txt:402` (Definition 3.2) + `:794-796` (逐行下降)。

把 Definition 3.2 的 enveloped 条件直接接到 `hrow`（「`cz` 之上每一行非空」）上。
三步：enveloped ⟹ `±nℓ` 两个面上各有 ≥ 2 个格点 (`exists_two_in_face_of_enveloped`)
⟹ 各有一对相邻格点 (`exists_unit_step_in_face`) ⟹ 双侧单位段
(`unitCovered_convHullOf_of_faces`) ⟹ 逐行下降 (`exists_level_down_of_unitCovered`)。

逐个量词的对应：
- `U` ＝ 原文的 `𝒰`（链上是 `𝒮_φ`）
- `B` ＝ 原文的 `𝒯`（链上取作 `B`）
- `henv : Enveloped U B` ＝ Definition 3.2 (`:402`)
- `nℓ` ＝ 扫掠方向的法向（`:792` 的 `ℓ`）
- `vl` ＝ 该方向的本原向量（`dot nℓ vl = 0`）
- `u'` ＝ 下降一层的步（`dot nℓ u' = −1`）
- `hnU, h_nU` ＝ `±nℓ ∈ E U`，保证 `U` 的对应面非空
- `htwoPos, htwoNeg` ＝ `U` 的 `±nℓ` 面上各有 ≥ 2 个格点（链上由 `𝒮_φ` 的生成元给出）
- `hczmem` ＝ `cz` 这一层非空（链上由 `exists_cutLevel` 给出）

消费者：`StripDescend.halfStrip_down_of_adj` (`:342`)，它要的就是这条 `hrow`。 -/
theorem hrow_of_enveloped_segments {U B : Set (ℤ × ℤ)} {nℓ vl u' : ℤ × ℤ}
    (hUE : (Nivat.LE2.E U).Finite)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (harea : Nivat.LE2.PosArea B) (hlc : Nivat.IsLatticeConvexRegion B)
    (henv : Nivat.LE2.Enveloped U B)
    (hn : nℓ ≠ 0) (hvlp : Nivat.Primitive vl) (hvl : vl ≠ 0)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hnU : nℓ ∈ Nivat.LE2.E U) (h_nU : -nℓ ∈ Nivat.LE2.E U)
    (htwoPos : ∃ a b, a ∈ Nivat.LE2.face U nℓ ∧ b ∈ Nivat.LE2.face U nℓ ∧ a ≠ b)
    (htwoNeg : ∃ a b, a ∈ Nivat.LE2.face U (-nℓ) ∧ b ∈ Nivat.LE2.face U (-nℓ) ∧ a ≠ b)
    {cz : ℤ} (hczmem : ∃ b ∈ B, Nivat.LE2.dot nℓ b = cz) :
    ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b - 1 →
      ∃ c ∈ B, Nivat.LE2.dot nℓ c = Nivat.LE2.dot nℓ b - 1 := by
  -- 步骤 1：enveloped ⟹ B 的 ±nℓ 面上各有 ≥ 2 个格点
  obtain ⟨a1, a2, ha1, ha2, ha12⟩ := exists_two_in_face_of_enveloped hUE henv hnU htwoPos
  obtain ⟨b1, b2, hb1, hb2, hb12⟩ := exists_two_in_face_of_enveloped hUE henv h_nU htwoNeg
  -- 步骤 2：应用已有的 hrow_of_two_in_faces
  exact hrow_of_two_in_faces hBfin hBne harea hlc hn hvlp hvl hperp hnu
    ⟨a1, a2, ha1, ha2, ha12⟩ ⟨b1, b2, hb1, hb2, hb12⟩ hczmem

/-- **The closed convex hull of a finite set of lattice points is compact.**

原文：b3_colle2.txt:777-812 — the sweep argument (Claim 4.6) relies on `H_B(ℓ)`
being the half-strip from a finite base `B`, so `convHullOf B` is compact. -/
theorem isCompact_convHullOf_of_finite {B : Set (ℤ × ℤ)} (hfin : B.Finite) :
    IsCompact (Nivat.convHullOf B) := by
  rw [convHullOf]
  have h1 : (toReal '' B).Finite := hfin.image _
  have h2 : IsCompact (convexHull ℝ (toReal '' B)) := h1.isCompact_convexHull ℝ
  exact IsCompact.closure h2

/-- **A ray from the origin is closed in ℝ².**

The ray `{t • v | t ≥ 0}` is closed as the continuous image of `[0, ∞)` when `v ≠ 0`,
and equals `{0}` when `v = 0`. -/
theorem isClosed_ray (v : ℝ × ℝ) : IsClosed {q : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ q = t • v} := by
  by_cases hv : v = 0
  · -- When v = 0, the ray is just {0}
    have : {q : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ q = t • v} = {0} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, hv, smul_zero]
      constructor
      · rintro ⟨t, _, rfl⟩; rfl
      · intro rfl; exact ⟨0, le_refl _, rfl⟩
    rw [this]
    exact isClosed_singleton
  · -- When v ≠ 0, express as intersection of closed sets
    have heq : {q : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ q = t • v}
        = {q : ℝ × ℝ | q.1 * v.2 = q.2 * v.1} ∩ {q : ℝ × ℝ | 0 ≤ q.1 * v.1 + q.2 * v.2} := by
      ext q; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨t, ht, rfl⟩
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        exact ⟨by ring, by nlinarith [mul_self_nonneg v.1, mul_self_nonneg v.2]⟩
      · intro ⟨hcol, hnn⟩
        have hpos : 0 < v.1 * v.1 + v.2 * v.2 := by
          by_contra hle
          apply hv
          have h1 : v.1 = 0 := by nlinarith [mul_self_nonneg v.1, mul_self_nonneg v.2]
          have h2 : v.2 = 0 := by nlinarith [mul_self_nonneg v.1, mul_self_nonneg v.2]
          exact Prod.ext h1 h2
        refine ⟨(q.1 * v.1 + q.2 * v.2) / (v.1 * v.1 + v.2 * v.2), div_nonneg hnn hpos.le, ?_⟩
        refine Prod.ext ?_ ?_ <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        · rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']; linear_combination v.2 * hcol
        · rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']; linear_combination -v.1 * hcol
    rw [heq]
    apply IsClosed.inter
    · have : {q : ℝ × ℝ | q.1 * v.2 = q.2 * v.1}
          = (fun q : ℝ × ℝ => q.1 * v.2 - q.2 * v.1) ⁻¹' {0} := by
        ext q; simp [sub_eq_zero]
      rw [this]
      refine IsClosed.preimage ?_ isClosed_singleton
      exact continuous_fst.mul continuous_const |>.sub (continuous_snd.mul continuous_const)
    · have : {q : ℝ × ℝ | 0 ≤ q.1 * v.1 + q.2 * v.2}
          = (fun q : ℝ × ℝ => q.1 * v.1 + q.2 * v.2) ⁻¹' Set.Ici 0 := by
        ext q; simp [Set.mem_Ici]
      rw [this]
      refine IsClosed.preimage ?_ isClosed_Ici
      exact continuous_fst.mul continuous_const |>.add (continuous_snd.mul continuous_const)

/-- **The sweep hull `C + ℝ≥0 • toReal v` is closed when `C` is compact.** -/
theorem isClosed_sweepHull_of_isCompact {C : Set (ℝ × ℝ)} (hC : IsCompact C) (v : ℤ × ℤ) :
    IsClosed (sweepHull C v) := by
  have heq : sweepHull C v = C + {t • toReal v | (t : ℝ) (h : 0 ≤ t)} := by
    ext q
    simp only [sweepHull, Set.mem_setOf_eq, Set.mem_add]
    constructor
    · rintro ⟨c, hc, r, hr, rfl⟩
      exact ⟨c, hc, r • toReal v, ⟨r, hr, rfl⟩, rfl⟩
    · rintro ⟨c, hc, w, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨c, hc, r, hr, rfl⟩
  rw [heq]
  have hray : IsClosed {t • toReal v | (t : ℝ) (h : 0 ≤ t)} := by
    convert isClosed_ray (toReal v) using 1
    ext q
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  exact hray.add_left_of_isCompact hC

end Nivat.SweepCrit

#print axioms Nivat.SweepCrit.isCompact_convHullOf_of_finite
#print axioms Nivat.SweepCrit.isClosed_ray
#print axioms Nivat.SweepCrit.isClosed_sweepHull_of_isCompact

#print axioms Nivat.SweepCrit.convex_sweepHull
#print axioms Nivat.SweepCrit.isLatticeConvexRegion_halfStrip_of_chord
#print axioms Nivat.SweepCrit.chord_of_unit_backstep
#print axioms Nivat.SweepCrit.chord_of_unitCovered
#print axioms Nivat.SweepCrit.unitCovered_of_two_sided
#print axioms Nivat.SweepCrit.isLatticeConvexRegion_halfStrip_of_unitCovered

#print axioms Nivat.SweepCrit.unitCovered_of_long_chords
#print axioms Nivat.SweepCrit.cross_eq_of_ip_zero
#print axioms Nivat.SweepCrit.exists_smul_of_ip_zero
#print axioms Nivat.SweepCrit.unitCovered_of_opposite_segments
#print axioms Nivat.SweepCrit.exists_unit_step_in_face
#print axioms Nivat.SweepCrit.exists_level_down_of_unitCovered
#print axioms Nivat.SweepCrit.unitCovered_convHullOf_of_faces
#print axioms Nivat.SweepCrit.hrow_of_two_in_faces
#print axioms Nivat.SweepCrit.exists_two_in_face_of_enveloped
#print axioms Nivat.SweepCrit.hrow_of_enveloped_segments
