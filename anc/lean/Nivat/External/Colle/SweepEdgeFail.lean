/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.HalfPlane

/-!
# 扫掠**沿一条边的方向**依然会破坏格凸性（`b3_colle2.txt:806` 的第二个反例）

原文：`b3_colle2.txt:806`

> For each integer `ι−m+1 ≤ i ≤ ι−2`, we define the `(-ℓ, ℓ_i)`-region
> `𝓡_i := {g + t·v⃗_{ℓ_i} ∈ ℤ² : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}`.

**这是断言，原文没有证明**；而按 `:31` 的定义（凸 ⟺ `𝒮 = conv(𝒮) ∩ ℤ²`）它一般为假。

已有的两个见证打的是别的东西：

* `Colle41.not_forall_isRegion_sweep`（`SweepNotRegion.lean`）：`K = ℤ×{0}` 退化，
  只说明我们的 `Colle41.IsRegion` 比 Def 3.1（`:386`）弱。
* `Colle41.not_isLatticeConvexRegion_sweep_quadrant`（同文件）：象限沿 `(2,−3)` 扫，
  说明「补 `det u u' ≠ 0` ＋ 锥内」那条修法不够。

**本文件打掉第三条、也是最自然的一条修法**：「扫掠方向平行于被扫集合的一条边」。
`b3_colle2.txt:766` 的循环序 ＋ Def 3.2（`:402`）的 enveloped 条件合起来正好给出这条，
所以它是最像原文意图的补法——而它**仍然不够**。

见证（全部整数，可手验）：

```
R   := {(x,y) | 0 ≤ y ∧ 7y ≤ 20x ∧ 10x ≤ 10 + 3y}     -- 三角形 (0,0),(1,0),(7,20) 的格点
v   := (1,0)                                           -- 平行于 R 的边 (0,0)—(1,0)
S   := R + ℕv
(7,0)  ∈ S   -- (1,0) + 6v
(7,20) ∈ S   -- t = 0，三角形的顶点
(7,13) ∉ S   -- 需要 21 ≤ 10t ∧ 20t ≤ 49，无整数解
(7,13) = (7/20)·(7,0) + (13/20)·(7,20)                 -- 凸组合，两点即可
```

几何原因（这才是可复用的那条）：`z − r·v ∈ conv(R)` 的参数区间在 `y = 13` 这一层长度只有
`4.9 − 4.55 = 0.35`，且落在两个整数之间。**扫掠保持格凸 ⟺ 每条 `v`-方向弦都含一个整参数**，
而「有一条平行边」只保证**那条边所在的那一层**弦够长，远离该边的层可以任意细。

**推论（写给 `OPEN.md #22` 的裁决）**：`:806` 要么按闭包读（`conv(·) ∩ ℤ²`），
要么必须用上 enveloped 的**双向**性（`𝒮_φ` 是 zonotope，边成 `±` 对出现，
所以 `B` 在每个方向上都有边，上下都被兜住）——单向的「有一条平行边」已被本文件否掉。
-/

namespace Nivat.SweepEdge

open Nivat

/-- 三角形 `(0,0), (1,0), (7,20)` 的格点集，写成三个半平面的交（故 `IsLatticeConvexRegion`
显然成立，见 `isLatticeConvexRegion_tri`）。 -/
def tri : Set (ℤ × ℤ) :=
  {p | 0 ≤ p.2 ∧ 7 * p.2 ≤ 20 * p.1 ∧ 10 * p.1 ≤ 10 + 3 * p.2}

/-- `tri` 沿它自己的一条边方向 `(1,0)` 扫掠所得的集合。 -/
def swept : Set (ℤ × ℤ) :=
  {z | ∃ g ∈ tri, ∃ t : ℕ, z = g + (t : ℤ) • ((1 : ℤ), (0 : ℤ))}

theorem isLatticeConvexRegion_tri : IsLatticeConvexRegion tri := by
  refine ⟨{q : ℝ × ℝ | 0 ≤ q.2 ∧ 7 * q.2 ≤ 20 * q.1 ∧ 10 * q.1 ≤ 10 + 3 * q.2}, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    obtain ⟨hx0, hx1, hx2⟩ := hx
    obtain ⟨hy0, hy1, hy2⟩ := hy
    show 0 ≤ (a • x + b • y).2 ∧ _ ∧ _
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · have h1 : IsClosed {q : ℝ × ℝ | 0 ≤ q.2} :=
      isClosed_le continuous_const continuous_snd
    have h2 : IsClosed {q : ℝ × ℝ | 7 * q.2 ≤ 20 * q.1} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have h3 : IsClosed {q : ℝ × ℝ | 10 * q.1 ≤ 10 + 3 * q.2} :=
      isClosed_le (by fun_prop) (by fun_prop)
    exact h1.inter (h2.inter h3)
  · ext p
    simp only [tri, Set.mem_ofPred_eq, Set.mem_preimage, toReal]
    constructor
    · rintro ⟨h0, h1, h2⟩
      exact ⟨by exact_mod_cast h0, by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h0, h1, h2⟩
      refine ⟨by exact_mod_cast h0, by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem mem_swept_7_0 : ((7 : ℤ), (0 : ℤ)) ∈ swept :=
  ⟨((1 : ℤ), (0 : ℤ)), ⟨by norm_num, by norm_num, by norm_num⟩, 6, by norm_num⟩

theorem mem_swept_7_20 : ((7 : ℤ), (20 : ℤ)) ∈ swept :=
  ⟨((7 : ℤ), (20 : ℤ)), ⟨by norm_num, by norm_num, by norm_num⟩, 0, by norm_num⟩

theorem not_mem_swept_7_13 : ((7 : ℤ), (13 : ℤ)) ∉ swept := by
  rintro ⟨g, ⟨-, h1, h2⟩, t, ht⟩
  have hg1 : g.1 = 7 - (t : ℤ) := by
    have := congrArg Prod.fst ht
    simp at this
    omega
  have hg2 : g.2 = 13 := by
    have := congrArg Prod.snd ht
    simp at this
    omega
  rw [hg1, hg2] at h1 h2
  omega

/-- **扫掠方向平行于一条边**仍然不足以保证格凸性（原文 `b3_colle2.txt:806`）。

`tri` 的边 `(0,0)—(1,0)` 方向正是 `(1,0)`，而 `swept = tri + ℕ(1,0)` 不是格凸的：
`(7,13) = (7/20)·(7,0) + (13/20)·(7,20)` 落在凸包里，却不在集合里。 -/
theorem not_isLatticeConvexRegion_swept : ¬ IsLatticeConvexRegion swept := by
  rintro ⟨C, hCconv, -, hSeq⟩
  have h1 : toReal ((7 : ℤ), (0 : ℤ)) ∈ C := by
    have : ((7 : ℤ), (0 : ℤ)) ∈ toReal ⁻¹' C := by rw [← hSeq]; exact mem_swept_7_0
    exact this
  have h2 : toReal ((7 : ℤ), (20 : ℤ)) ∈ C := by
    have : ((7 : ℤ), (20 : ℤ)) ∈ toReal ⁻¹' C := by rw [← hSeq]; exact mem_swept_7_20
    exact this
  have hmid := hCconv h1 h2 (by norm_num : (0 : ℝ) ≤ 7 / 20) (by norm_num : (0 : ℝ) ≤ 13 / 20)
    (by norm_num : (7 : ℝ) / 20 + 13 / 20 = 1)
  have heq : (7 / 20 : ℝ) • toReal ((7 : ℤ), (0 : ℤ)) + (13 / 20 : ℝ) • toReal ((7 : ℤ), (20 : ℤ))
      = toReal ((7 : ℤ), (13 : ℤ)) := by
    simp only [toReal, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    norm_num
  rw [heq] at hmid
  have : ((7 : ℤ), (13 : ℤ)) ∈ swept := by
    rw [hSeq]; exact hmid
  exact not_mem_swept_7_13 this

end Nivat.SweepEdge

#print axioms Nivat.SweepEdge.isLatticeConvexRegion_tri
#print axioms Nivat.SweepEdge.not_isLatticeConvexRegion_swept
