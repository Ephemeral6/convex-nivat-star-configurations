/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.StrictWindow
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.L1StraddleWedge

set_option autoImplicit false

/-!
# Half-strip vs half-plane gap analysis

**原文：b3_colle2.txt:412-414, Definition 3.4**

This file establishes that `Nivat.LE2.halfStrip` correctly implements Collé's `H_B(ℓ)`
(Definition 3.4), which is a **half-strip** (half-band), not a half-plane.

The gap between half-strip and half-plane is real and documented here through:
1. A kernel-verified counterexample showing the difference
2. Confirmation that the paper's definition matches our implementation
3. A bridge lemma for when half-strip containment is needed

-/

open Nivat.LE2 Nivat.ConeRegion

namespace Nivat.SweepBase

/-- **Deliverable 1: Half-strip is not a half-plane (kernel-verified refutation)**

**原文对应**: Definition 3.4 (b3_colle2.txt:414) defines
`H_B(ℓ) := {g + t•v_ℓ : g ∈ B, t ∈ ℤ₊}`, which is a half-strip.

This theorem proves that half-strips are strictly smaller than half-planes in two ways:
- **Transverse boundedness**: `{z | c₀ ≤ dot m z}` contains points arbitrarily far
  perpendicular to `vl`, but `halfStrip B vl` only reaches `dot m '' B`.
- **Half-line per layer**: Each transverse level of the half-plane is a full line,
  but each level of `halfStrip B vl` is only the ray `{g + t•vl : t ≥ 0}`.

**Witness**: `B := {(0,0)}`, `vl := (0,1)` (vertical), `m := (1,0)` (horizontal),
`c₀ := 0`. The half-plane `{z | 0 ≤ z.1}` contains `(1,0)` and `(1,-1)`, but
`halfStrip {(0,0)} (0,1) = {(0,t) : t ≥ 0}` contains neither.

**量词对应原文**:
- `B`: the base set from Definition 3.4 (line 412)
- `vl`: the direction vector `v_ℓ` (line 414)
- `m`: transverse direction (perpendicular to `vl`)
- `c₀`: the infimum `dot m b` for `b ∈ B`
- Half-plane: `{z | c₀ ≤ dot m z}`, which would be needed for full sweeping
- Half-strip: `H_B(ℓ) = {g + t•v_ℓ : g ∈ B, t ∈ ℤ₊}` (paper's definition)

-/
theorem not_halfPlane_subset_halfStrip :
    ∃ (B : Finset (ℤ × ℤ)) (vl m : ℤ × ℤ) (c₀ : ℤ),
      B.Nonempty ∧
      m ≠ 0 ∧ dot m vl = 0 ∧
      (∀ b ∈ B, c₀ ≤ dot m b) ∧
      ∃ z : ℤ × ℤ, c₀ ≤ dot m z ∧ z ∉ halfStrip (↑B : Set (ℤ × ℤ)) vl := by
  refine ⟨{(0, 0)}, (0, 1), (1, 0), 0, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Finset.Nonempty]
  · decide
  · simp [dot]
  · intro b hb
    simp at hb
    simp [hb, dot]
  · refine ⟨(1, 0), ?_, ?_⟩
    · simp [dot]
    · intro ⟨b, hb, t, heq⟩
      simp at hb
      rw [hb] at heq
      simp at heq

/-! **Deliverable 2: Paper's definition confirmation (b3_colle2.txt:412-414)**

**Line 412**: "Let ℓ ⊂ ℝ² be a rational oriented line and suppose B ⊂ ℤ² is a
non-empty, finite, convex set. The half-strip from B in the direction of ℓ is
defined as"

**Line 414**: "H_B(ℓ) := {g + t•v_ℓ ∈ ℤ² : g ∈ B, t ∈ ℤ₊}."

**Judgment**: The paper's `H_B(ℓ)` is **a half-strip (half-band), not a half-plane**.
Our `Nivat.LE2.halfStrip` at `LatticeEdges.lean:1810-1811` is the correct
implementation:
```
def halfStrip (B : Set (ℤ × ℤ)) (v : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {g | ∃ b ∈ B, ∃ t : ℕ, g = b + (t : ℤ) • v}
```

This is **not a definition error**. The gap between half-strip and half-plane is
real, and the horizontal sweep mechanism (lines 792-804) must work with the
half-strip as defined, not with a full half-plane.

-/

/-! **Deliverable 3 撤回 (2026-09-20, 集成者)**

原稿的 `halfStrip_eq_halfPlane_iff` 带 `sorry` 落进主仓，红线违例，整条删除。
它本身也不成立作陈述：`c₀` 写成默认值参数（`(c₀ : ℤ := sInf (dot m '' B))`），
所以结论里的 `c₀` 是**自由变量**而不是 `B` 的横向下确界，两个方向都不是要证的东西。

**Deliverable 1 已经把这个问题答完了**：`not_halfPlane_subset_halfStrip` 是内核见证的
`halfStrip ⊊ 半平面`，所以横向扫掠**不能**假装种子是半平面。横向扫掠真正需要的不是
「halfStrip 等于半平面」，而是原文 `:792-804` 的逐行归纳——第 `i` 行的窗口落回
`D ∪ (⋃ i'<i, lines i')`，而不是落回某个半平面。见 `SweepLines.lean`。 -/

/-! **Deliverable 4 降级 (2026-09-20, 集成者)：`lbase_stripStep_of_envOf_of_coneRegion`**

原稿带 `sorry` 落进主仓，红线违例（硬规矩 4：落地的东西照样 0 sorry）。签名本身**没有问题**，
逐记号追溯见下，所以保留成拟证目标；证出来之前不要再落地。

**原文对应**: Lines 792-798, Figure 10. The placement step for points in `A₁ = ℛ_{ι-1} ∩ l₁`.

**Mechanism**: For `w ∈ ℛ_{ι-1}` below the cut (`dot nℓ w < cz`), when a window point
`z ∈ S \ {a₀}` translates to `z + (w - a₀)` and reaches or crosses `cz`, it lands
in the half-strip `H_B(ℓ)`.

**Quantifier tracing**:
- `B`: enveloped set (line 778: "B ⊂ ℤ² be an E(𝒮_φ)-enveloped set")
- `S`: generating set `𝒮_{φ_ι}` (line 792: "𝒮_{φ_ι} is an η - η̄_{ι₀}-generating set")
- `vl`: direction `v_ℓ` (line 778: "H_B(ℓ)")
- `u'`: direction `v_{ℓ_{ι-1}}` (line 784: "ℛ_{ι-1} := {g + t•v_{ℓ_{ι-1}} : g ∈ H_B(ℓ), t ∈ ℤ₊}")
- `nℓ`: normal to `ℓ` (perpendicular to `vl`)
- `cz`: cut level (line 796: "l₁ := ℓ_B^{(-)}"), the first line below `B`'s support
- `a₀`: reference point in `S` (not required to be ψ-minimal per Wlines' finding)

**Premises** (from Definition 3.2, line 402, and line 792-798):
- `hEnv : EnvOf S B` — `B` is `E(S)`-enveloped (line 778)
- `hBlc : IsLatticeConvexRegion B` — lattice convexity (Definition 3.2)
- Height bound from item (ii) (line 474-476) — encoded in the conclusion via level occupancy

**Consumer**: `Nivat.ColleReg.wedgeResidualR_of_case1_of_cone`, binder `hstrip`, with
`B := Nivat.LE2.shift (-((k:ℤ) • vl)) B`.

拟证签名（**尚未证明**，骨架带 `sorry` 已删）：

```lean
theorem lbase_stripStep_of_envOf_of_coneRegion
    {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {vl u' nℓ a₀ : ℤ × ℤ} {cz : ℤ}
    (hEnv : EnvOf S B)
    (hBlc : IsLatticeConvexRegion B)
    (hBfin : B.Finite)
    (hBne : B.Nonempty)
    (hnvl : dot nℓ vl = 0)
    (hnu : dot nℓ u' = -1)
    (hczdef : cz = -suppVal B (-nℓ))
    (ha₀ : a₀ ∈ S) :
    ∀ w ∈ coneRegion B vl u', dot nℓ w < cz →
      ∀ z ∈ S.erase a₀, cz ≤ dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ halfStrip B vl
```

⚠ 与 `StrictWindow.lean:1695` 的 `not_hstrip_of_occupancy_without_mu` 对照：`hstrip` 光有
层占据是不够的，还要 μ 子句。上面这条若证不出来，先看是不是缺了 μ 方向的前提。 -/

/-! **Deliverable 4b 降级 (2026-09-20, 集成者第二次)：`lbase_stripStep_of_envOf_of_coneRegion`**

Lbase 第二次把同一条带 `sorry` 的骨架落进主仓（自报
`[propext, sorryAx, Classical.choice, Quot.sound]`），红线违例，再次删除。
**这一版比上一版前进了三步，前进的部分记在下面，不要重做。**

1. **签名已对准新消费者**：消费者是
   `Nivat.ColleReg.wedgeResidualR_of_case1_of_cone_at_base`（`RegionSteps.lean`）的 binder
   `hstrip`，**在平白的 `B` 上**（`k := 0`，没有 shift 层）。
2. **`hczdef` 换成 `hcz` + `hczmem`**，与消费者逐字一致；两条由
   `Nivat.ColleReg.exists_cutLevel`（`RegionSteps.lean`）对有限非空 `B` 无条件产出。
3. **`hunimod` / `hstrict` 加进签名不增加债**——两条在消费者处都已经是 binder。

**唯一缺口**：`rw [Nivat.StrictWindow.hstrip_iff_fit_window hunimod hnvl hnu hcz]` 之后，
目标化为 `fit`——对每个中间层 `cz + j` 要给出

```
∃ g ∈ B, dot nℓ g = cz + j ∧
  dot (expNormal u' vl) g ≤ dot (expNormal u' vl) b + dot (expNormal u' vl) (z - a₀)
```

**这一步就是 μ 子句**，而 `hEnv : EnvOf S B` 是唯一还没被用上的前提。对照
`StrictWindow.lean:1695` 的 `not_hstrip_of_occupancy_without_mu`：光有层占据不够，
μ 方向的界必须从 envelopedness 出来。

## 🔴 2026-09-20 Hstrip 报告：envelopedness 不直接给 μ-bound

已读 `b3_colle2.txt:777-798`、`StrictWindow.lean:1695` 反例、`hstrip_iff_fit_window` 签名。

**核心问题**：`EnvOf S B` 约束的是**边集** `E B ⊆ E S` + 基数相等，**不直接**约束格点的
μ-坐标分布。`hstrip_iff_fit_window` 的 RHS 要的是：对每个 `b ∈ B`、每个 `z ∈ S.erase a₀`、
每个中间层 `cz + j`（`j < ⟪nℓ, z-a₀⟫`），必存在 `g ∈ B` 同层且 `μ g ≤ μ b + μ(z-a₀)`。

**原文机制（`:794-798`）**：Lemma 2.6 保证 `𝒮_{φ_ι}` 无边平行于 `±ℓ`，使窗口平移后落进 `H_B(ℓ)`。
但我们的 `EnvOf S B` **未要求** `S` 无边平行于 `vl`——那条在 `hnoedge` binder 里
（`PhiIotaWindow.lean:157`），**不在本文件签名**。

**已排除路线**：
1. **不能从 `IsLatticeConvexRegion B` 直接推层占据**——`L1LevelSpan.lean:30-44` 明确记着
   `LatticeConvex` 不蕴含 `LevelInterval`（`not_levelInterval_maxB` 是反例）。
2. **不能从边集相等推格点分布**——`E_eq_of_envOf` 只说边方向，不说每层有多少点、μ 怎么排。
3. **不能从 `hstrict` 推**——`hstrict` 只说 `a₀` 是 `nℓ`-极小，不说 `B` 的每层都连续覆盖到那里。

**Gap**：`EnvOf S B` + `IsLatticeConvexRegion B` ⇏ 每层 μ-连续。反例 `slantPara`（StrictWindow.lean:1605）
满足格凸 + 正面积 + `hlean`，**但第 2 层缺点**——它有 level 0, 1, 3 的点，level 2 空。
任何 `u'` 满足 `⟪nℓ,u'⟫ = -1` 的都会把 level 3 的点送到 level 2，而那里没东西接。

**需要的前提（未在签名里）**：
- `hnoedge : ∀ n ∈ E S, dot n vl ≠ 0` — Lemma 2.6，在 `PhiIotaWindow` 有、这里没有
- 或 `B` 的层填满性 — `∀ b ∈ B, ∀ ℓ ∈ [cz, dot nℓ b), ∃ g ∈ B, dot nℓ g = ℓ` 这种

**结论**：当前签名**可能**证不出来。需集成者裁决：(a) 加 `hnoedge` 到签名，或 (b) 换消费者
签名给更强的 `B` 性质，或 (c) 我漏了某个已证引理。

🔴 **2026-09-21 集成者裁决：上面这个 "Gap" 是对反例的过度解读，撤回。三条裁决选项都不选。**
（按 §14 保留原文不删，只改状态。）
- `slantPara` **不是** `E(wS)`-enveloped，`wS` 只有两点也不是合法的 `𝒮_{φ_ι}`——
  这两句白纸黑字写在该反例自己的 docstring 里（`StrictWindow.lean:1712-1715`）。
- 它打中的是 `hstrip_of_lean_of_occupancy`（`StrictWindow.lean:1595`），那条签名里
  **一个 envelopedness 前提都没有**。所以它证的是「`hocc` 的 μ 子句不可删」，
  **对带 `EnvOf` 的这一版一个字都没说**。
- 据此加 `hnoedge` 就是硬规矩 10 的对偶失误：**拿一个弱化版的反例去改原文那版的签名**。
  加之前必须先有一个**真·enveloped** 的反例。

**因此当前任务是证伪而不是证明**：找 `EnvOf ↑S B`、`S` 合法（≥3 点、`LatticeConvex (S.erase a₀)`、
`PosArea`）、而 μ 子句失败的见证。envelopedness 在这里是硬约束：`Enveloped.E_eq`
（`LatticeEdges.lean:1657`）逼出 `E B = E S`，`Enveloped.face_encard_le`（`:1663`）逼出
`B` 的**每条**面都不短于 `S` 的对应面——这正是 `slantPara` 不满足的那条。
找不到见证时，撞上的那条边长约束就是证明草图。

⚠ **不能**在没确认前提够的情况下落带 `sorry` 的骨架——上两轮都因此红线违例。 -/

/-! ## Step 1: Extract `IsLatticeConvexRegion B` from `EnvOf`

**原文**：Definition 3.2 (b3_colle2.txt:402) — enveloped sets are lattice-convex regions.

`EnvOf S B` 展开为 `Enveloped S B`（`LatticeEdges.lean:628`），即
`WeaklyEnveloped S B ∧ (E B).encard = (E S).encard`。而 `WeaklyEnveloped.latticeConvex`
（`LatticeEdges.lean:634`）直接给出 `IsLatticeConvexRegion B`。
-/

/-- **从 `EnvOf` 提取格凸性。**

**原文对应**：Definition 3.2 (b3_colle2.txt:402)。`E(S)`-enveloped 集合是格凸区域。

**Consumer**: `lbase_stripStep_of_envOf_of_coneRegion` (本文件，待证)。
-/
theorem latticeConvex_of_envOf {S B : Set (ℤ × ℤ)}
    (henv : Nivat.LE2.EnvOf S B) :
    Nivat.IsLatticeConvexRegion B := by
  obtain ⟨hweak, _⟩ := henv
  exact Nivat.LE2.WeaklyEnveloped.latticeConvex hweak

/-- **从 `Enveloped` 提取边集相等（加 `E_subset` 给出 `E B = E S`）。**

**原文对应**：Definition 3.2 (b3_colle2.txt:402)。Enveloped 定义的第二合取。

**Consumer**: `lbase_stripStep_of_envOf_of_coneRegion` (本文件，待证) 需要用到
`B` 与 `S` 的边法向集合相同这一事实，以确保 `B` 的宽度下界。
-/
theorem E_encard_eq_of_envOf {S B : Set (ℤ × ℤ)}
    (henv : Nivat.LE2.EnvOf S B) :
    (Nivat.LE2.E B).encard = (Nivat.LE2.E (↑S : Set (ℤ × ℤ))).encard := by
  obtain ⟨_, heq⟩ := henv
  exact heq

/-! ## Step 2: Arithmetic bound on target level

**原文对应**：b3_colle2.txt:792-798。窗口点 `z ∈ Sw \ {a₀}` 平移后的层数落在有界区间内。

令 `y := z + (w - a₀)`。则：
- `dot nℓ w ≤ cz - 1` （由 `dot nℓ w < cz`）
- `dot nℓ z - dot nℓ a₀ ≥ 1` （由 `hstrict : ∀ z ∈ Sw.erase a₀, dot nℓ a₀ < dot nℓ z`）
- `cz ≤ dot nℓ y` （binder）

所以 `dot nℓ y = dot nℓ w + (dot nℓ z - dot nℓ a₀) ∈ [cz, cz + D - 1]`，
其中 `D` 是窗口 `Sw` 在 `nℓ` 方向的层跨度。
-/

/-- **目标点 `y := z + (w - a₀)` 的层数上界。**

**原文对应**：b3_colle2.txt:792-798。平移后的点落在切割线上方的有界区间内。

**量词对应**：
- `w ∈ coneRegion B vl u'`：锥内点 (line 784)
- `dot nℓ w < cz`：在切割线下方 (line 796)
- `z ∈ Sw.erase a₀`：窗口点 (line 792)
- `dot nℓ a₀ < dot nℓ z`：`a₀` 是 `nℓ`-严格极小点 (line 796-798 机制)
- `cz ≤ dot nℓ (z + (w - a₀))`：越过切割线 (binder)

**结论**：`dot nℓ (z + (w - a₀)) < cz + (max_level - min_level)`，
其中 `max_level` / `min_level` 是窗口在 `nℓ` 方向的极值。

**Consumer**: `lbase_stripStep_of_envOf_of_coneRegion` (本文件，待证)。
-/
theorem target_level_bounded
    {B : Set (ℤ × ℤ)} {Sw : Finset (ℤ × ℤ)} {vl u' nℓ a₀ w z : ℤ × ℤ} {cz : ℤ}
    (hSwne : Sw.Nonempty)
    (ha₀ : a₀ ∈ Sw)
    (hstrict : ∀ z' ∈ Sw.erase a₀, dot nℓ a₀ < dot nℓ z')
    (hw_cone : w ∈ Nivat.ConeRegion.coneRegion B vl u')
    (hnw : dot nℓ w < cz)
    (hz : z ∈ Sw.erase a₀)
    (hcross : cz ≤ dot nℓ (z + (w - a₀))) :
    dot nℓ (z + (w - a₀)) < cz + (Sw.sup' hSwne (dot nℓ) - Sw.inf' hSwne (dot nℓ)) := by
  have hza₀ : dot nℓ a₀ < dot nℓ z := hstrict z hz
  have hy_eq : dot nℓ (z + (w - a₀)) = dot nℓ w + (dot nℓ z - dot nℓ a₀) := by
    simp only [dot_add, dot_sub]
    ring
  rw [hy_eq]
  -- `dot nℓ w < cz` 给出 `dot nℓ w ≤ cz - 1`
  have hw_le : dot nℓ w ≤ cz - 1 := Int.le_sub_one_of_lt hnw
  -- `dot nℓ z - dot nℓ a₀ < Sw.sup' - Sw.inf'` (因为 `z ∈ Sw` 且 `a₀ ∈ Sw`)
  have hz_mem : z ∈ Sw := Finset.mem_of_mem_erase hz
  have hsup : dot nℓ z ≤ Sw.sup' hSwne (dot nℓ) := Finset.le_sup' (dot nℓ) hz_mem
  have hinf : Sw.inf' hSwne (dot nℓ) ≤ dot nℓ a₀ := Finset.inf'_le (dot nℓ) ha₀
  omega

/-! ## Step 2b: Coordinate criterion for `halfStrip` membership

**原文对应**：b3_colle2.txt:412-414, Definition 3.4。`H_B(ℓ) = {g + t•v_ℓ : g ∈ B, t ∈ ℤ₊}` 的
坐标刻画。

在幺模基 `(u', vl)` 下，`g ∈ halfStrip B vl` 当且仅当存在 `b ∈ B` 使：
- 同层：`dot nℓ b = dot nℓ g` （因 `dot nℓ vl = 0`）
- 不在右侧：`dot (expNormal u' vl) b ≤ dot (expNormal u' vl) g` （因 `t : ℕ` 且 `dot (expNormal u' vl) vl = 1`）

镜像 `Nivat.EnvFit.mem_coneRegion_iff_coords`（`EnvFit.lean:153`），证明用相同的 `eq_coords` 论证。
-/

/-- **`halfStrip` 的坐标刻画。**

**原文对应**：Definition 3.4 (b3_colle2.txt:412-414)。在幺模基下，半带成员资格等价于
两个坐标不等式：同 `nℓ`-层 + `expNormal` 坐标不超。

**量词对应**：
- `hunimod`：`(u', vl)` 构成 ℤ-基 (Definition 3.2)
- `hperp`：`nℓ ⊥ vl` (line 778)
- `hnu`：`dot nℓ u' = -1` (规范化法向)
- `b ∈ B`：基点 (line 414: `g ∈ B`)
- `dot nℓ b = dot nℓ g`：同层（因 `t•vl` 不改变 `nℓ`-坐标）
- `dot (expNormal u' vl) b ≤ dot (expNormal u' vl) g`：`b` 不在 `g` 右侧（因 `t ∈ ℕ` 且 `dot (expNormal u' vl) vl = 1`）

**Consumer**: `lbase_stripStep_of_envOf_of_coneRegion` (本文件，待证)。
-/
theorem mem_halfStrip_iff_coords {B : Set (ℤ × ℤ)} {u' vl nℓ g : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0)
    (hnu : dot nℓ u' = -1) :
    g ∈ Nivat.LE2.halfStrip B vl ↔
      ∃ b ∈ B, dot nℓ b = dot nℓ g ∧
        dot (Nivat.ColleReg.expNormal u' vl) b ≤ dot (Nivat.ColleReg.expNormal u' vl) g := by
  -- 集成者之手（2026-09-20）：原稿用了三个不存在的名字（`Nivat.LE2.expNormal`、
  -- `Nivat.EnvFit.dot_expNormal_vl`、右乘 `dot_smul`），主 build 判红；换成真名
  -- `Nivat.ColleReg.expNormal` / `Nivat.ColleReg.dot_expNormal_vl` / `dot_smul_right`，
  -- 反向用 `L1StraddleWedge.eq_coords`（`u'`-系数 = `uCoord u' vl 0`，由 `hnu` 压成零）。
  have h1 : dot (Nivat.ColleReg.expNormal u' vl) vl = 1 :=
    Nivat.ColleReg.dot_expNormal_vl hunimod
  constructor
  · rintro ⟨b, hb, t, rfl⟩
    refine ⟨b, hb, ?_, ?_⟩
    · rw [dot_add, Nivat.ColleReg.dot_smul_right, hperp]; ring
    · rw [dot_add, Nivat.ColleReg.dot_smul_right, h1]; omega
  · rintro ⟨b, hb, hlev, hmu⟩
    have heq := Nivat.L1StraddleWedge.eq_coords (u' := u') (vl := vl) hunimod (g - b)
    have hβ : Nivat.L1Line0.uCoord u' vl 0 (g - b) = 0 := by
      have h0 : dot nℓ (g - b) = 0 := by rw [dot_sub, hlev]; ring
      have h2 := congrArg (dot nℓ) heq
      rw [dot_add, Nivat.ColleReg.dot_smul_right, Nivat.ColleReg.dot_smul_right, hperp, hnu,
        h0] at h2
      linarith
    rw [hβ, zero_smul, add_zero] at heq
    have hα : 0 ≤ dot (Nivat.ColleReg.expNormal u' vl) (g - b) := by
      rw [dot_sub]; omega
    refine ⟨b, hb, (dot (Nivat.ColleReg.expNormal u' vl) (g - b)).toNat, ?_⟩
    rw [Int.toNat_of_nonneg hα, ← heq]
    abel

/-! ## Step 3: Level occupancy and envelope extent

Three named targets for completing hole 6 (`RegionSteps.lean:2345`).
-/

/-- **Target (1): Edge sets equal under envelopedness.**

**原文对应**：Definition 3.2 (b3_colle2.txt:402)。Enveloped 给出 `E B ⊆ E S` 且基数相等。

Combines `E_encard_eq_of_envOf` with `WeaklyEnveloped.E_subset` to get equality.
-/
theorem E_eq_of_envOf {S B : Set (ℤ × ℤ)} (hfin : (Nivat.LE2.E S).Finite)
    (henv : Nivat.LE2.EnvOf S B) : Nivat.LE2.E B = Nivat.LE2.E S := by
  obtain ⟨hweak, heq⟩ := henv
  have hsub := Nivat.LE2.WeaklyEnveloped.E_subset hweak
  exact (hfin.subset hsub).eq_of_subset_of_encard_le hsub heq.ge

/-! ### Target (2)/(3) 已撤下（2026-09-20，集成者之手）

`exists_mem_of_level_between` 与 `extent_ge_of_envOf` 两条骨架曾以 `sorry` 落在此处，
**违反「agent 不许把 `sorry` 落进主仓」的红线**，已整体删除，签名改记在 `blueprint/OPEN.md #20`。
上游 `E_eq_of_envOf` 是真证明，保留。

⚠ 撤下时同步发现 `extent_ge_of_envOf` 的签名（集成者本人写的派工单）**本身可疑**：
`nℓ` 被自由量化、与 `E S` 无任何关系，而 `Enveloped`（`LatticeEdges.lean:628`）只说
「同方向的边不更短」。对不是边法向的 `nℓ`，「展宽不减」并非自明——重新立案前不要再按
那个形状去证（硬规矩 7：比原文强 = 债）。
-/

/-! ### 撤回 (2026-09-21, 集成者): `exists_shift_subset_of_envOf` 整条删除

lane Hstrip 第三次把带 `sorry` 的骨架落进主仓（自报
`[propext, sorryAx, Classical.choice, Quot.sound]`），红线违例，已删。**签名与诊断保留在下面**
——它们是对的，欠的是真数学（格凸多边形的 Minkowski 分解），不是接线。

拟证签名（**尚未证明**）：

```lean
theorem exists_shift_subset_of_envOf {U T : Set (ℤ × ℤ)}
    (hUfin : U.Finite) (hUconv : Nivat.IsLatticeConvexRegion U)
    (hUpos : Nivat.LE2.PosArea U) (h : Nivat.LE2.EnvOf U T) :
    ∃ c : ℤ × ℤ, Nivat.LE2.shift c U ⊆ T
```

已在内核里走通的两步（删除时一并记下，重开时不必重做）：
`hEeq : E T = E U` 由 `Nivat.LE2.Enveloped.E_eq (finite_E_of_finite hUfin) h`；
`hface : ∀ n ∈ E U, (face U n).encard ≤ (face T n).encard` 由 `h.1.2` 的第二分量配 `hEeq` 改写。
断在第三步：要从 `hface` 造出那个平移 `c`，需要 `EnvTranslate.shift_subset_iff_suppVal_le`
加上格凸多边形的 Minkowski 分解（`EnvTranslate.lean:134-148` 写明路径，非平凡）。

原文与量词对应（下面这段是原 docstring，逐字保留）：

**Definition 3.2 的几何内容：法向集合相同 + 每条边不短 ⟹ `U` 的一个整格平移含于 `T`。**

原文：b3_colle2.txt:402 — Definition 3.2, "A set `𝒯 ⊆ ℤ²` weakly `E(𝒰)`-enveloped where
`|E(𝒯)| = |E(𝒰)|` is said to be `E(𝒰)`-enveloped."

This is the Minkowski domination principle: if two lattice-convex polygons have the same
normal fan and T's edges are at least as long as U's edges (in the lattice metric), then
some integer translate of U fits inside T.

**Mechanism**: `EnvTranslate.shift_subset_iff_suppVal_le` reduces the existence question
to a finite linear system `∀ n ∈ E T, suppVal U n + ⟪n,v⟫ ≤ suppVal T n`. Since
`E T = E U` and edge lengths satisfy `L_T(n) ≥ L_U(n)`, the differences
`D(n) := L_T(n) - L_U(n)` satisfy `D(n) ≥ 0` and the Minkowski closure condition
`Σ_n D(n) • n = 0` (edge vectors close the boundary). Therefore the system is feasible.

**量词对应原文 (hard rule 7)**:
- `EnvOf U T` ↔ `:402` "`𝒯` is `E(𝒰)`-enveloped"
- `∃ c : ℤ × ℤ` ↔ the translation shown in Figure 10 (`:798`)
- `shift c U ⊆ T` ↔ the containment "`𝒰 + v ⊆ 𝒯`" drawn there

**Consumer**: `lbase_stripStep_of_envOf_of_coneRegion` (this file :139) via the μ-clause.

**反例尝试失败记录（保留作为反面教材）**: 第一次尝试 `U = [0,1]² ∩ ℤ²`、`T = {(0,0), (2,0), (0,2), (2,2)}`
（2× 缩放）。死因：`T` 不是 `IsLatticeConvexRegion`（`(1,1) ∈ conv T` 但 `∉ T`），`EnvOf U T`
的第一个合取不满足。这正是 `EnvTranslate.lean:124-130` 记载的同一个错误。教训（`PROTOCOL.md` §7）：
反例见证落地前必须在内核里把被否命题的**全部**前提验一遍。 -/

end Nivat.SweepBase

#print axioms Nivat.SweepBase.not_halfPlane_subset_halfStrip
#print axioms Nivat.SweepBase.latticeConvex_of_envOf
#print axioms Nivat.SweepBase.E_encard_eq_of_envOf
#print axioms Nivat.SweepBase.target_level_bounded
#print axioms Nivat.SweepBase.mem_halfStrip_iff_coords
#print axioms Nivat.SweepBase.E_eq_of_envOf
