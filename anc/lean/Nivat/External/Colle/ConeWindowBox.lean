/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.RegionCut

/-!
# `ConeWindowBox` — the window discharge for Claim 4.6's line-by-line sweep

原文：b3_colle2.txt:780-804（Claim 4.6），Figure 10 的说明在 `:798`，
盒子假设来自 Lemma 3.5 证明中的 item (ii)，`b3_colle2.txt:474`。

## What the paper says

`:784`  `𝓡_{ι-1} := {g + t·v⃗_{ℓ_{ι-1}} : g ∈ H_B(ℓ), t ∈ ℤ₊}`，即
        `B + ℤ₊·v⃗_ℓ + ℤ₊·v⃗_{ℓ_{ι-1}}`（`H_B(ℓ)` 的定义在 `:414`）。
`:796`  `A₁ := 𝓡_{ι-1} ∩ l₁`，`l₁ := ℓ_B^{(-)}`；`:802` `A₂ := 𝓡_{ι-1} ∩ l₂`，
        `l₂ := l₁^{(-)}`；`:804`「proceeding this way, we get by induction」。
`:798`  Figure 10：「the knowledge of `T^u η` on `H_B(ℓ)` determines uniquely
        `T^u η` on `A₁`」。
`:792`  Lemma 2.6 ⟹ `𝒮_{φ_ι}` 没有平行于 `±ℓ` 的边，所以它的 `ℓ`-支撑线只碰到
        它一个点 —— 那个点就是下面的 `a`（`dot nℓ` 的**严格**最小点）。

## What this file lands

消费者是 `Nivat.SweepLines.hbase_at_of_sweep_lines`（`SweepLines.lean:177`），它唯一
未兑现的义务是

```
hwinL : ∀ i, ∀ w ∈ lines i, ∀ z ∈ S.erase a,
          z + (w - a) ∈ D ∪ (⋃ i' < i, lines i')
```

本文件给出**盖住这条义务的真陈述**，并给出**盒子假设救不了原始陈述**的内核反例。

### 关键的几何事实（本文件的全部内容）

把 `w = b + s·vl + t·u'`、`z - a = α·vl - δ·u'` 展开（`δ ≥ 1`，因为 `a` 是严格
`dot nℓ`-最小点，且 `dot nℓ u' = -1`），得

```
z + (w - a) = b + (s + α)·vl + (t - δ)·u'.
```

`vl` 方向的系数 `s + α` **可以为负**：`𝒮_{φ_ι}` 是中心对称的（它是
`∏_{i≠ι₀}(X^{h_i} - 1)` 的支撑，一个 zonotope），所以它必定有点落在 `a` 的
`-vl` 一侧，即 `α ≤ -1` 的 `z` 一定存在；而 `w` 可以取在 `𝓡_{ι-1}` 的
`ℓ_{ι-1}`-边上（`s = 0`）。于是 `z + (w - a)` 从锥的那条边上**漏出去**。

- `not_window_subset_of_enveloped_seed` / `..._seed'`（§6，**本文件的主结论**）把这件事
  做成内核反例，种子 `B` 是货真价实的 `E(U)`-enveloped set（`Nivat.LE2.enveloped_sq`，
  `:402` Definition 3.2），**没有任何附加大小假设** —— 这正是 `:778` Case 1 给的
  那种 `B`。两个 `det u' vl` 符号都覆盖了。反例里 `z + (w - a)` 的 level 落在 `B` 的
  两条 `ℓ`-支撑线**之间**，所以**竖直方向（宽度支配）不是病灶**：
  `width_le_of_enveloped` 即便证出来也解不开 `hwinL`。
- `not_window_subset_of_box_seed`（§4）是同一件事的盒子版本，对**任意大**的盒子成立，
  所以 `:474` item (ii) 的盒子条件也不是修法。
- `window_subset_seed_union_prev_lines`（§2）是**真**陈述：把第二条射线方向从 `u'`
  换成 `u'' := u' + c·vl`（`c` = `𝒮_{φ_ι}` 在 `-vl` 方向相对 `a` 的宽度），
  每下一行就向 `vl` 方向内缩 `c` 步。内缩后的区域仍然是 `:386` 意义下的
  `(-ℓ, ℓ'')`-region（两条半无限边分别平行于 `-ℓ` 和 `ℓ''`），只是
  `ℓ'' ≠ ℓ_{ι-1}`。

§2 里 `hcap` 与 `hSfit` 的 `δ ≤ czTop - cz + 1` 挡的是**另一个**漏洞：`δ` 可以
大于 1，于是 `z + (w - a)` 可能落到 `B` 的支撑线**之上**，而 `H_B(ℓ)` 只是一条
宽度有限的半带（`Nivat.SweepBase.not_halfPlane_subset_halfStrip` 是这条的内核
见证）。⚠ **`hcap` 目前只对 `(vl, u'')`-坐标下的盒子证过（`boxSeed_cap`），
从一般的 `EnvOf 𝒮_φ B` 推不出来** —— 见文件末尾的欠账说明。
-/

set_option autoImplicit false

namespace Nivat.ConeWindowBox

open Nivat.LE2 Nivat.ConeRegion

/-! ## §1  Level bookkeeping -/

/-- The `dot nℓ`-level of a cone point `b + A·vl + J·u''`, when `vl` is parallel to the
lines (`dot nℓ vl = 0`) and `u''` steps down exactly one line (`dot nℓ u'' = -1`).

原文：b3_colle2.txt:796-802 —— `l₁ := ℓ_B^{(-)}`、`l₂ := l₁^{(-)}`，即每一步恰好
跨过一条格线，这就是 `dot nℓ u'' = -1`；`vl` 平行于 `ℓ`，即 `dot nℓ vl = 0`。

Quantifiers: `nℓ vl u''` 三个向量，`b` 基点，`A J : ℤ` 两个系数 —— 全部是记号，
没有新的存在/全称断言。 -/
theorem dot_cone_point {nℓ vl u'' : ℤ × ℤ}
    (hperp : dot nℓ vl = 0) (hstep : dot nℓ u'' = -1) (b : ℤ × ℤ) (A J : ℤ) :
    dot nℓ (b + A • vl + J • u'') = dot nℓ b - J := by
  rw [dot_add, dot_add, dot_zsmul, dot_zsmul, hperp, hstep]; ring

/-- Tilting the second ray direction by a multiple of `vl` does not change the level step.

原文：b3_colle2.txt:786 —— `𝓡_{ι-1}` 是一个 `(-ℓ, ℓ_{ι-1})`-region（`:386` 的定义：
两条半无限边分别平行于给定的两条有向直线）。把 `ℓ_{ι-1}` 换成方向
`u'' := u' + c·v⃗_ℓ` 得到的仍然是一个 region，只是第二条边的方向变了；
`dot nℓ u'' = dot nℓ u' = -1` 说明**逐行**的归纳结构（`:804`）一字不变。 -/
theorem dot_tilt {nℓ vl u' : ℤ × ℤ} (c : ℤ)
    (hperp : dot nℓ vl = 0) (hstep : dot nℓ u' = -1) :
    dot nℓ (u' + c • vl) = -1 := by
  rw [dot_add, dot_zsmul, hperp, hstep]; ring

/-! ## §2  The true window-containment statement -/

/-- **The paper's window discharge, on the tilted cone.**

原文：b3_colle2.txt:780-804（Claim 4.6）+ Figure 10 (`:798`) + `:474` item (ii).

结论正是 `Nivat.SweepLines.hbase_at_of_sweep_lines`（`SweepLines.lean:177`）的
`hwinL`，取 `D := halfStrip B vl`、`lines i := coneRegion B vl u'' ∩ {level = cz-1-i}`，
其中 `u'' := u' + c·vl`。

**逐个量词对照原文：**

* `B` ↔ `:778` 的 `B`（`E(𝒮_φ)`-enveloped set）。
* `vl` ↔ `v⃗_ℓ`（`:784`），`u'` ↔ `v⃗_{ℓ_{ι-1}}`（`:784`）。
* `nℓ` ↔ `ℓ` 的法向：`hperp : dot nℓ vl = 0` 说 `vl ∥ ℓ`；
  `hstep : dot nℓ u' = -1` 说沿 `u'` 走一步恰好跨一条格线，这是 `:796`/`:802`
  里 `l₁ := ℓ_B^{(-)}`、`l₂ := l₁^{(-)}` 的逐行结构。
* `cz` ↔ `ℓ_B` 的水平：`hBlow` 说 `B` 全在 `ℓ_B` 的上闭侧（`:796` `l₁ = ℓ_B^{(-)}`
  在其下**一**步，即 `level = cz - 1`）。
* `czTop` ↔ `B` 的另一条 `ℓ`-支撑线：`B` 是有限凸集（`:416`「non-empty, finite,
  convex set `B`」），故其 `ℓ`-横向宽度有限，`hBhigh` 就是这条。
* `a` ↔ `:792` 的那个唯一点：Lemma 2.6 给出 `𝒮_{φ_ι}` 没有平行于 `±ℓ` 的边，
  所以它的 `ℓ`-支撑线只与它相交于一点；`hmin` 就是「严格最小、唯一」。
* `c` ↔ `𝒮_{φ_ι}` 在 `-v⃗_ℓ` 方向相对 `a` 的宽度（`𝒮_{φ_ι}` 是有限集，
  `:790` 它是 `∏_{i≠ι₀}(X^{h_i}-1)` 的支撑）。`hSfit` 的 `-(c:ℤ) ≤ α` 就是这条。
* `hSfit` 的 `(δ:ℤ) ≤ czTop - cz + 1` ↔ `:474` item (ii)：`B_i` 要装得下
  `[-i+1,i-1]² ∩ ℋ(ℓ^{(-)})`，即 `B` 的横向宽度最终超过 `𝒮_{φ_ι}` 的横向宽度。
* `hcap` ↔ `:414` 的 `H_B(ℓ)` 定义 + `:474` item (ii)：锥中**高于 `ℓ_B`** 的那部分
  已经被半带 `H_B(ℓ)` 盖住。对 `(vl, u'')`-坐标下的盒子 `B` 这是恒真的，
  见 `boxSeed_cap`（本文件），所以本假设非空洞。
* `i` ↔ `:796`-`:804` 的行号（`A₁, A₂, …`），`w ∈ lines i` ↔ `w ∈ A_{i+1}`，
  `z ∈ S.erase a` ↔ `Ŝ_{φ_ι}` 去掉那个落在新行上的唯一点后剩下的点，
  结论「落在 `H_B(ℓ) ∪ 前面各行`」↔ `:794`/`:802` 的
  `H_B(ℓ) ∪ A₁ ∪ ⋯ ∪ A_i`。

没有一个量词是我们发明的。**唯一与原文不同的地方**是第二条射线方向
`u'' = u' + c·vl` 而不是 `u'`；`not_window_subset_of_box_seed` 证明这个改动
不可省略。 -/
theorem window_subset_seed_union_prev_lines
    {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {vl u' nℓ a : ℤ × ℤ} {cz czTop : ℤ} {c : ℕ}
    (hperp : dot nℓ vl = 0) (hstep : dot nℓ u' = -1)
    (hmin : ∀ z ∈ S.erase a, dot nℓ a < dot nℓ z)
    (hBlow : ∀ b ∈ B, cz ≤ dot nℓ b)
    (hcap : ∀ b ∈ B, ∀ j : ℤ, cz ≤ dot nℓ b - j → dot nℓ b - j ≤ czTop →
      b + j • (u' + (c : ℤ) • vl) ∈ halfStrip B vl)
    (hSfit : ∀ z ∈ S.erase a, ∃ (α : ℤ) (δ : ℕ),
      -(c : ℤ) ≤ α ∧ (δ : ℤ) ≤ czTop - cz + 1 ∧ z = a + α • vl - (δ : ℤ) • u') :
    ∀ i : ℕ, ∀ w ∈ (coneRegion B vl (u' + (c : ℤ) • vl) ∩
        {y | dot nℓ y = cz - 1 - (i : ℤ)}),
      ∀ z ∈ S.erase a,
        z + (w - a) ∈ halfStrip B vl ∪
          (⋃ i' ∈ {i' : ℕ | i' < i},
            coneRegion B vl (u' + (c : ℤ) • vl) ∩ {y | dot nℓ y = cz - 1 - (i' : ℤ)}) := by
  have hstep'' : dot nℓ (u' + (c : ℤ) • vl) = -1 := dot_tilt _ hperp hstep
  intro i w hw z hz
  obtain ⟨hwcone, hwlev⟩ := hw
  simp only [Set.mem_setOf_eq] at hwlev
  rw [mem_coneRegion_iff] at hwcone
  obtain ⟨b, hb, s, t, rfl⟩ := hwcone
  obtain ⟨α, δ, hα, hδtop, hzeq⟩ := hSfit z hz
  -- Level of `w`: `dot nℓ b - t = cz - 1 - i`.
  have hlvlw : dot nℓ b - (t : ℤ) = cz - 1 - (i : ℤ) := by
    rw [dot_cone_point hperp hstep'' b (s : ℤ) (t : ℤ)] at hwlev; exact hwlev
  -- `δ ≥ 1` because `a` is the *strict* `dot nℓ`-minimum of `S`.
  have hzlev : dot nℓ z = dot nℓ a + (δ : ℤ) := by
    rw [hzeq, dot_sub, dot_add, dot_zsmul, dot_zsmul, hperp, hstep]; ring
  have hδpos : (1 : ℤ) ≤ (δ : ℤ) := by
    have := hmin z hz; omega
  -- `t ≥ 1 + i` because `B` sits on or above level `cz`.
  have htge : (1 : ℤ) + (i : ℤ) ≤ (t : ℤ) := by
    have := hBlow b hb; omega
  -- Rewrite the translated window in the tilted basis.
  have key : z + ((b + (s : ℤ) • vl + (t : ℤ) • (u' + (c : ℤ) • vl)) - a)
      = b + ((s : ℤ) + α + (c : ℤ) * (δ : ℤ)) • vl
          + ((t : ℤ) - (δ : ℤ)) • (u' + (c : ℤ) • vl) := by
    rw [hzeq]; module
  rw [key]
  -- The `vl`-coefficient is non-negative: this is where the tilt `c` pays off.
  have hA0 : (0 : ℤ) ≤ (s : ℤ) + α + (c : ℤ) * (δ : ℤ) := by
    have h1 : (c : ℤ) * 1 ≤ (c : ℤ) * (δ : ℤ) :=
      mul_le_mul_of_nonneg_left hδpos (by positivity)
    have h2 : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
    omega
  obtain ⟨A, hA⟩ : ∃ A : ℕ, ((s : ℤ) + α + (c : ℤ) * (δ : ℤ)) = (A : ℤ) :=
    ⟨((s : ℤ) + α + (c : ℤ) * (δ : ℤ)).toNat, (Int.toNat_of_nonneg hA0).symm⟩
  rw [hA]
  by_cases hcase : (δ : ℤ) ≤ (i : ℤ)
  · -- **Case B**: the window lands on an earlier line of the same cone.
    refine Or.inr ?_
    have hJ0 : (0 : ℤ) ≤ (t : ℤ) - (δ : ℤ) := by omega
    obtain ⟨J, hJ⟩ : ∃ J : ℕ, ((t : ℤ) - (δ : ℤ)) = (J : ℤ) :=
      ⟨((t : ℤ) - (δ : ℤ)).toNat, (Int.toNat_of_nonneg hJ0).symm⟩
    rw [hJ]
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨i - δ, by omega, ?_, ?_⟩
    · rw [mem_coneRegion_iff]; exact ⟨b, hb, A, J, rfl⟩
    · show dot nℓ _ = _
      rw [dot_cone_point hperp hstep'' b (A : ℤ) (J : ℤ)]
      have : ((i - δ : ℕ) : ℤ) = (i : ℤ) - (δ : ℤ) := by omega
      omega
  · -- **Case A**: the window lands back inside the half-strip `H_B(ℓ)`.
    refine Or.inl ?_
    have hlow : cz ≤ dot nℓ b - ((t : ℤ) - (δ : ℤ)) := by omega
    have hhigh : dot nℓ b - ((t : ℤ) - (δ : ℤ)) ≤ czTop := by omega
    obtain ⟨b₁, hb₁, k, hk⟩ := hcap b hb ((t : ℤ) - (δ : ℤ)) hlow hhigh
    refine ⟨b₁, hb₁, k + A, ?_⟩
    have : b + (A : ℤ) • vl + ((t : ℤ) - (δ : ℤ)) • (u' + (c : ℤ) • vl)
        = (b + ((t : ℤ) - (δ : ℤ)) • (u' + (c : ℤ) • vl)) + (A : ℤ) • vl := by module
    rw [this, hk]
    push_cast
    module

/-! ## §3  The box seed: `hcap` is not vacuous

原文：b3_colle2.txt:474 item (ii) —— `B_i` contains `[-i+1,i-1]² ∩ ℋ(ℓ^{(-)})`.
A box, read in the `(vl, u'')` basis. -/

/-- **A box seed**: the `(vl, u'')`-parallelogram with corner `b₀`, `P+1` columns along
`vl` and `Q+1` rows along `-u''`.

原文：b3_colle2.txt:474 item (ii) —— `[-i+1,i-1]²`，一个方盒；`:416` 说 `B` 是
非空有限凸集。这里把方盒写在 `(vl, u'')` 基底下。

Quantifiers: `p ≤ P` ↔ 盒子沿 `v⃗_ℓ` 的一边；`q ≤ Q` ↔ 盒子沿 `-u''` 的一边
（`-u''` 指向 `ℓ_B` 的上方，因为 `dot nℓ u'' = -1`）。 -/
def boxSeed (b₀ vl u'' : ℤ × ℤ) (P Q : ℕ) : Set (ℤ × ℤ) :=
  {z | ∃ p q : ℕ, p ≤ P ∧ q ≤ Q ∧ z = b₀ + (p : ℤ) • vl - (q : ℤ) • u''}

theorem mem_boxSeed {b₀ vl u'' : ℤ × ℤ} {P Q : ℕ} {z : ℤ × ℤ} :
    z ∈ boxSeed b₀ vl u'' P Q ↔
      ∃ p q : ℕ, p ≤ P ∧ q ≤ Q ∧ z = b₀ + (p : ℤ) • vl - (q : ℤ) • u'' := Iff.rfl

/-- The box seed lies on or above the level `cz := dot nℓ b₀` of its `ℓ`-support line.

原文：b3_colle2.txt:796 —— `l₁ := ℓ_B^{(-)}`，所以 `ℓ_B` 是 `B` 的下支撑线。 -/
theorem boxSeed_low {b₀ vl u'' nℓ : ℤ × ℤ} {P Q : ℕ}
    (hperp : dot nℓ vl = 0) (hstep : dot nℓ u'' = -1) :
    ∀ b ∈ boxSeed b₀ vl u'' P Q, dot nℓ b₀ ≤ dot nℓ b := by
  rintro b ⟨p, q, _, _, rfl⟩
  rw [dot_sub, dot_add, dot_zsmul, dot_zsmul, hperp, hstep]
  have : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
  omega

/-- The box seed has transverse width `Q`: its other `ℓ`-support line is at `cz + Q`.

原文：b3_colle2.txt:416 —— `B` 是有限凸集，故横向宽度有限。 -/
theorem boxSeed_high {b₀ vl u'' nℓ : ℤ × ℤ} {P Q : ℕ}
    (hperp : dot nℓ vl = 0) (hstep : dot nℓ u'' = -1) :
    ∀ b ∈ boxSeed b₀ vl u'' P Q, dot nℓ b ≤ dot nℓ b₀ + (Q : ℤ) := by
  rintro b ⟨p, q, _, hq, rfl⟩
  rw [dot_sub, dot_add, dot_zsmul, dot_zsmul, hperp, hstep]
  have : (q : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hq
  omega

/-- **`hcap` holds for the box seed.**  The part of the cone that is between the two
`ℓ`-support lines of `B` is already inside the half-strip `H_B(ℓ)`.

原文：b3_colle2.txt:414（`H_B(ℓ)` 的定义）+ `:474` item (ii)（`B` 是个盒子）。

这条的作用是证明 `window_subset_seed_union_prev_lines` 的 `hcap` 假设**不空洞**。 -/
theorem boxSeed_cap {b₀ vl u'' nℓ : ℤ × ℤ} {P Q : ℕ}
    (hperp : dot nℓ vl = 0) (hstep : dot nℓ u'' = -1) :
    ∀ b ∈ boxSeed b₀ vl u'' P Q, ∀ j : ℤ,
      dot nℓ b₀ ≤ dot nℓ b - j → dot nℓ b - j ≤ dot nℓ b₀ + (Q : ℤ) →
      b + j • u'' ∈ halfStrip (boxSeed b₀ vl u'' P Q) vl := by
  rintro b ⟨p, q, hp, hq, rfl⟩ j hlow hhigh
  rw [dot_sub, dot_add, dot_zsmul, dot_zsmul, hperp, hstep] at hlow hhigh
  have hq' : (q : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hq
  have hrange : (0 : ℤ) ≤ (q : ℤ) - j ∧ (q : ℤ) - j ≤ (Q : ℤ) := by omega
  obtain ⟨r, hr⟩ : ∃ r : ℕ, ((q : ℤ) - j) = (r : ℤ) :=
    ⟨((q : ℤ) - j).toNat, (Int.toNat_of_nonneg hrange.1).symm⟩
  refine ⟨b₀ + (p : ℤ) • vl - (r : ℤ) • u'', ⟨p, r, hp, ?_, rfl⟩, 0, ?_⟩
  · have : (r : ℤ) ≤ (Q : ℤ) := by omega
    exact_mod_cast this
  · have hj : j = (q : ℤ) - (r : ℤ) := by omega
    rw [hj]; module

/-! ## §4  Refutation: no box rescues the *un-tilted* cone

原文：b3_colle2.txt:798 —— Figure 10 的「the knowledge of `T^u η` on `H_B(ℓ)`
determines uniquely `T^u η` on `A₁`」。 -/

/-- **Counterexample: `:474` item (ii) does NOT discharge the window containment for
the un-tilted cone `𝓡_{ι-1} = B + ℤ₊·v⃗_ℓ + ℤ₊·v⃗_{ℓ_{ι-1}}`.**

原文：b3_colle2.txt:784（`𝓡_{ι-1}` 的定义）+ `:798`（Figure 10 的那句
「determines uniquely `T^u η` on `A₁`」）+ `:474` item (ii)（盒子条件）。

对**每一对** `P Q : ℕ`（盒子可以任意大）我们给出一个见证，它满足
`window_subset_seed_union_prev_lines` 的**全部**假设，只把倾斜量 `c` 换成 `0`
（即第二条射线方向就是原文的 `v⃗_{ℓ_{ι-1}} = u'` 本身）：

* `hperp : dot nℓ vl = 0`、`hstep : dot nℓ u' = -1`（`:796`/`:802` 的逐行结构）；
* `a ∈ S` 且 `a` 是 `S` 上 `dot nℓ` 的**严格**最小点（`:792` Lemma 2.6）；
* `hBlow` / `hBhigh`：`B` 夹在自己的两条 `ℓ`-支撑线之间（`:414`, `:416`）；
* `hcap`：锥在两条支撑线之间的部分已被 `H_B(ℓ)` 盖住（`:474` item (ii)）；
* `hSfit` 的竖直部分 `(δ:ℤ) ≤ czTop - cz + 1`（`:474` item (ii)）。

结论仍然为假：取 `i = 0`（即 `A₁`，`:796`），存在 `w ∈ A₁` 和
`z ∈ 𝒮_{φ_ι} \ {a}` 使 `z + (w - a) ∉ H_B(ℓ)`，而 `i = 0` 时前面没有别的行。

唯一被违反的假设是 `hSfit` 的水平部分 `-(c:ℤ) ≤ α`：见证里 `α = -1 < 0 = -c`。
这正说明**倾斜 `c ≥ 1` 不可省**，而盒子大小（`P`, `Q` 任意）与此无关。 -/
theorem not_window_subset_of_box_seed (P Q : ℕ) :
    ∃ (B : Set (ℤ × ℤ)) (S : Finset (ℤ × ℤ)) (vl u' nℓ a : ℤ × ℤ) (cz czTop : ℤ),
      B = boxSeed (0, 0) vl u' P Q ∧
      dot nℓ vl = 0 ∧ dot nℓ u' = -1 ∧
      a ∈ S ∧ (∀ z ∈ S.erase a, dot nℓ a < dot nℓ z) ∧
      (∀ b ∈ B, cz ≤ dot nℓ b) ∧ (∀ b ∈ B, dot nℓ b ≤ czTop) ∧
      (∀ b ∈ B, ∀ j : ℤ, cz ≤ dot nℓ b - j → dot nℓ b - j ≤ czTop →
        b + j • u' ∈ halfStrip B vl) ∧
      (∀ z ∈ S.erase a, ∃ δ : ℕ, (δ : ℤ) ≤ czTop - cz + 1 ∧
        ∃ α : ℤ, z = a + α • vl - (δ : ℤ) • u') ∧
      (∃ w ∈ coneRegion B vl u' ∩ {y | dot nℓ y = cz - 1 - ((0 : ℕ) : ℤ)},
        ∃ z ∈ S.erase a,
          z + (w - a) ∉ halfStrip B vl ∪
            (⋃ i' ∈ {i' : ℕ | i' < 0},
              coneRegion B vl u' ∩ {y | dot nℓ y = cz - 1 - (i' : ℤ)})) := by
  classical
  refine ⟨boxSeed (0, 0) (1, 0) (0, 1) P Q, {(0, 0), (-1, -1)}, (1, 0), (0, 1), (0, -1),
    (0, 0), 0, (Q : ℤ), rfl, by simp [dot], by simp [dot], by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `a = (0,0)` is the strict `dot nℓ`-minimum of `S`.
    intro z hz
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz
    obtain ⟨hne, hz'⟩ := hz
    rcases hz' with rfl | rfl
    · exact absurd rfl hne
    · simp [dot]
  · -- `hBlow`
    have := @boxSeed_low (0, 0) (1, 0) (0, 1) (0, -1) P Q (by simp [dot]) (by simp [dot])
    simpa [dot] using this
  · -- `hBhigh`
    have := @boxSeed_high (0, 0) (1, 0) (0, 1) (0, -1) P Q (by simp [dot]) (by simp [dot])
    simpa [dot] using this
  · -- `hcap`
    have := @boxSeed_cap (0, 0) (1, 0) (0, 1) (0, -1) P Q (by simp [dot]) (by simp [dot])
    simpa [dot] using this
  · -- `hSfit`, vertical part only
    intro z hz
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz
    obtain ⟨hne, hz'⟩ := hz
    rcases hz' with rfl | rfl
    · exact absurd rfl hne
    · refine ⟨1, by omega, -1, ?_⟩
      simp
  · -- the failing window: `w = (0,1) ∈ A₁`, `z = (-1,-1)`, `z + (w - a) = (-1,0)`.
    refine ⟨(0, 1), ⟨?_, ?_⟩, (-1, -1), ?_, ?_⟩
    · rw [mem_coneRegion_iff]
      exact ⟨(0, 0), ⟨0, 0, Nat.zero_le _, Nat.zero_le _, by simp⟩, 0, 1, by simp⟩
    · simp [dot]
    · simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      refine ⟨?_, Or.inr trivial⟩
      norm_num [Prod.ext_iff]
    · rintro (⟨b, hb, k, hk⟩ | hU)
      · obtain ⟨p, q, _, _, rfl⟩ := hb
        simp only [Prod.ext_iff] at hk
        simp at hk
        omega
      · simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hU
        obtain ⟨i', hi', -⟩ := hU
        exact absurd hi' (Nat.not_lt_zero i')

/-! ## §5  Non-vacuity: every hypothesis of §2 is simultaneously satisfiable

一条带 `hξ`-式前提的引理最容易的死法是**空真**。本节给出一个具体见证，
同时满足 `window_subset_seed_union_prev_lines` 的全部假设，并且
`S.erase a` 与第 0 行 `A₁` 都**非空** —— 所以 §2 的结论不是对空集说话。 -/

/-- **`window_subset_seed_union_prev_lines` 的假设组非空洞。**

见证：`vl = (1,0)`（`v⃗_ℓ`），`u' = (0,1)`（`v⃗_{ℓ_{ι-1}}`），`nℓ = (0,-1)`，
倾斜量 `c = 1`，故 `u'' = (1,1)`；`B` 是 `(vl, u'')` 基底下的 `3 × 3` 盒子
（`b3_colle2.txt:474` item (ii)），`cz = 0`，`czTop = 2`；
`S = {(0,0), (-1,-1), (1,-2)}`，`a = (0,0)` 是它唯一的 `dot nℓ`-最小点。

`S` 的三条边分别沿 `(1,1)`、`(2,-1)`、`(1,-2)`，**没有一条平行于 `±vl`**，
所以它也满足 `:792`（Lemma 2.6）对 `𝒮_{φ_ι}` 的几何要求；
`(-1,-1)` 落在 `a` 的 `-vl` 一侧（`α = -1`），所以 `c = 0` 在这里**不可行**
—— 这正是 `not_window_subset_of_box_seed` 所刻画的那个漏洞。 -/
theorem window_hypotheses_satisfiable :
    ∃ (B : Set (ℤ × ℤ)) (S : Finset (ℤ × ℤ)) (vl u' nℓ a : ℤ × ℤ) (cz czTop : ℤ) (c : ℕ),
      (S.erase a).Nonempty ∧
      (coneRegion B vl (u' + (c : ℤ) • vl) ∩
        {y | dot nℓ y = cz - 1 - ((0 : ℕ) : ℤ)}).Nonempty ∧
      dot nℓ vl = 0 ∧ dot nℓ u' = -1 ∧
      (∀ z ∈ S.erase a, dot nℓ a < dot nℓ z) ∧
      (∀ b ∈ B, cz ≤ dot nℓ b) ∧
      (∀ b ∈ B, ∀ j : ℤ, cz ≤ dot nℓ b - j → dot nℓ b - j ≤ czTop →
        b + j • (u' + (c : ℤ) • vl) ∈ halfStrip B vl) ∧
      (∀ z ∈ S.erase a, ∃ (α : ℤ) (δ : ℕ),
        -(c : ℤ) ≤ α ∧ (δ : ℤ) ≤ czTop - cz + 1 ∧ z = a + α • vl - (δ : ℤ) • u') := by
  classical
  refine ⟨boxSeed (0, 0) (1, 0) (1, 1) 2 2, {(0, 0), (-1, -1), (1, -2)},
    (1, 0), (0, 1), (0, -1), (0, 0), 0, 2, 1, ?_, ?_, by simp [dot], by simp [dot],
    ?_, ?_, ?_, ?_⟩
  · exact ⟨(-1, -1), by norm_num [Prod.ext_iff]⟩
  · refine ⟨(1, 1), ⟨?_, ?_⟩⟩
    · rw [mem_coneRegion_iff]
      exact ⟨(0, 0), ⟨0, 0, Nat.zero_le _, Nat.zero_le _, by simp⟩, 0, 1, by norm_num⟩
    · simp [dot]
  · intro z hz
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz
    obtain ⟨hne, hz'⟩ := hz
    rcases hz' with rfl | rfl | rfl
    · exact absurd rfl hne
    · simp [dot]
    · simp [dot]
  · have := @boxSeed_low (0, 0) (1, 0) (1, 1) (0, -1) 2 2 (by simp [dot]) (by simp [dot])
    simpa [dot] using this
  · have := @boxSeed_cap (0, 0) (1, 0) (1, 1) (0, -1) 2 2 (by simp [dot]) (by simp [dot])
    simpa [dot] using this
  · intro z hz
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz
    obtain ⟨hne, hz'⟩ := hz
    rcases hz' with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact ⟨-1, 1, by norm_num, by norm_num, by simp⟩
    · exact ⟨1, 2, by norm_num, by norm_num, by simp⟩

/-! ## §6  The refutation with a genuinely `E(U)`-enveloped seed

原文：b3_colle2.txt:402（Definition 3.2，`E(𝒰)`-enveloped）+ `:778`（Case 1 的 `B`
就是一个 `E(𝒮_φ)`-enveloped set，没有别的大小条件）+ `:798`（Figure 10 那句
「the knowledge of `T^u η` on `H_B(ℓ)` determines uniquely `T^u η` on `A₁`」）。

§4 用的是盒子，可能被反驳为「盒子不是 `EnvOf` 给的东西」。本节把种子换成
`Nivat.LE2.sq2`，它由**已落地的** `Nivat.LE2.enveloped_sq` 见证为
`Enveloped sq1 sq2`，`sq1` 有正面积、四条边（`posArea_sq1`, `E_sq1`）。所以本节的
见证满足 `:778` 对 `B` 的**全部**要求，没有任何附加大小假设。

**关键读数：竖直方向不是病灶。** 见证里 `z + (w - a)` 落在 `B` 的两条 `ℓ`-支撑线
**之间**（level `= cz`），也就是说「窗口不比 `B` 高」这一半（`Enveloped` 的宽度
支配所要给的东西）**已经满足**，失败纯粹发生在 `v⃗_ℓ` 方向。
**推论：宽度支配（`width_le_of_enveloped`）即便证出来也解不开 `hwinL`。**

**病灶的精确定位。** 要让 `:798` 成立，需要的不是 `𝒮_{φ_ι}` 没有平行于 `±ℓ` 的边
（`:792`），而是更强的
```
𝒮_{φ_ι} - a ⊆ {s·v⃗_ℓ + t·(-v⃗_{ℓ_{ι-1}}) : s, t ∈ ℤ₊},
```
即 `a` **同时**是 `ℓ`-极点和 `-v⃗_ℓ`-极点。而 `𝒮_{φ_ι}` 是
`∏_{i≠ι₀}(X^{h_i}-1)` 的支撑，是个 zonotope，**中心对称**，所以它在 `a` 的
`-v⃗_ℓ` 一侧必有点 —— 这个更强的条件在原文里不可满足。 -/

/-- **Refutation with an `E(sq1)`-enveloped seed, `det u' vl = -1`.**

原文：b3_colle2.txt:402, :778, :784, :798.

见证：`U = sq1 = [0,1]²`，`B = sq2 = [0,2]²`（`Enveloped sq1 sq2` 由
`Nivat.LE2.enveloped_sq` 给出），`vl = (1,0) = v⃗_ℓ`，`u' = (0,1) = v⃗_{ℓ_{ι-1}}`，
`nℓ = (0,-1)`，`cz = -2`，`czTop = 0`；
`S = {(0,0), (-1,-1), (1,-2)}`，`a = (0,0)`。

`S` 的三个点的 `dot nℓ` 值是 `0 < 1 < 2`，所以 `a` 是**严格唯一**的 `ℓ`-极点
（`:792` Lemma 2.6 的结论）；三个点的 `dot nℓ` 两两不同 ⟹ `S` 没有任何平行于
`±ℓ` 的边，所以 `:792` 的几何前提也满足。

失败点：`w = (0,3) ∈ A₁`（`:796`，`level = cz - 1 = -3`），
`z = (-1,-1)`，`z + (w - a) = (-1,2)`，它的 level 是 `-2 = cz`（在 `B` 的
level 带内），但 `v⃗_ℓ`-坐标是 `-1 < 0`，落在 `H_B(ℓ)` 的左边界之外。 -/
theorem not_window_subset_of_enveloped_seed :
    ∃ (U B : Set (ℤ × ℤ)) (S : Finset (ℤ × ℤ)) (vl u' nℓ a : ℤ × ℤ) (cz czTop : ℤ),
      Enveloped U B ∧ PosArea U ∧ U.Finite ∧ B.Finite ∧ B.Nonempty ∧
      Nivat.det u' vl = -1 ∧
      dot nℓ vl = 0 ∧ dot nℓ u' = -1 ∧
      a ∈ S ∧ (∀ z ∈ S.erase a, dot nℓ a < dot nℓ z) ∧
      (∀ y ∈ S, ∀ z ∈ S, dot nℓ y = dot nℓ z → y = z) ∧
      (∀ b ∈ B, cz ≤ dot nℓ b) ∧ (∀ b ∈ B, dot nℓ b ≤ czTop) ∧
      (∀ z ∈ S.erase a, ∃ (α : ℤ) (δ : ℕ), (δ : ℤ) ≤ czTop - cz + 1 ∧
        z = a + α • vl - (δ : ℤ) • u') ∧
      (∃ w ∈ coneRegion B vl u' ∩ {y | dot nℓ y = cz - 1 - ((0 : ℕ) : ℤ)},
        ∃ z ∈ S.erase a,
          cz ≤ dot nℓ (z + (w - a)) ∧ dot nℓ (z + (w - a)) ≤ czTop ∧
          z + (w - a) ∉ halfStrip B vl ∪
            (⋃ i' ∈ {i' : ℕ | i' < 0},
              coneRegion B vl u' ∩ {y | dot nℓ y = cz - 1 - (i' : ℤ)})) := by
  classical
  refine ⟨sq1, sq2, {(0, 0), (-1, -1), (1, -2)}, (1, 0), (0, 1), (0, -1), (0, 0), -2, 0,
    enveloped_sq, posArea_sq1, finite_sq1', ?_, ⟨(0, 0), by exact ⟨le_refl _, by norm_num,
      le_refl _, by norm_num⟩⟩, by simp [Nivat.det], by simp [dot], by simp [dot],
    by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Set.Finite.subset (Set.finite_Icc ((0 : ℤ), (0 : ℤ)) ((2 : ℤ), (2 : ℤ))) ?_
    rintro z ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · -- `a = (0,0)` is the strict `dot nℓ`-minimum
    intro z hz
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz
    obtain ⟨hne, hz'⟩ := hz
    rcases hz' with rfl | rfl | rfl
    · exact absurd rfl hne
    · simp [dot]
    · simp [dot]
  · -- `S` has no edge parallel to `±ℓ`: `dot nℓ` is injective on `S`
    intro y hy z hz h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz
    rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
      simp_all [dot]
  · -- `hBlow`
    rintro b ⟨-, -, hb3, hb4⟩
    simp only [dot]
    omega
  · -- `hBhigh`
    rintro b ⟨-, -, hb3, -⟩
    simp only [dot]
    omega
  · -- `hSfit`, vertical part
    intro z hz
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz
    obtain ⟨hne, hz'⟩ := hz
    rcases hz' with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact ⟨-1, 1, by norm_num, by simp⟩
    · exact ⟨1, 2, by norm_num, by simp⟩
  · -- the escape at `i = 0`
    refine ⟨(0, 3), ⟨?_, ?_⟩, (-1, -1), ?_, ?_, ?_, ?_⟩
    · rw [mem_coneRegion_iff]
      refine ⟨(0, 0), ⟨le_refl _, by norm_num, le_refl _, by norm_num⟩, 0, 3, by norm_num⟩
    · simp [dot]
    · simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      refine ⟨?_, Or.inr (Or.inl trivial)⟩
      norm_num [Prod.ext_iff]
    · simp [dot]
    · simp [dot]
    · rintro (⟨b, hb, k, hk⟩ | hU)
      · obtain ⟨hb1, -, -, -⟩ := hb
        simp only [Prod.ext_iff] at hk
        simp at hk
        omega
      · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hU
        obtain ⟨i', hi', -⟩ := hU
        exact absurd hi' (Nat.not_lt_zero i')

/-- **The same failure with the opposite orientation `det u' vl = 1`.**

原文：同上。团队提出「`det u' vl` 的符号可能是承重假设」；本条把另一个符号也堵上。
见证只把 `vl` 换成 `(-1,0)` 并把 `S` 镜像：`S = {(0,0), (1,-1), (-1,-2)}`，
失败点 `w = (2,3) ∈ A₁`，`z = (1,-1)`，`z + (w - a) = (3,2)`，level `= -2 = cz`
仍在 `B` 的 level 带内，而 `v⃗_ℓ`-坐标越过了 `H_B(ℓ)` 的边界。

**结论：两个符号都不救。** 失败是对称的 —— 半带 `H_B(ℓ)` 只朝 `+v⃗_ℓ` 无限延伸，
而 `𝒮_{φ_ι}` 在 `a` 的 `-v⃗_ℓ` 一侧必有点。 -/
theorem not_window_subset_of_enveloped_seed' :
    ∃ (U B : Set (ℤ × ℤ)) (S : Finset (ℤ × ℤ)) (vl u' nℓ a : ℤ × ℤ) (cz czTop : ℤ),
      Enveloped U B ∧ PosArea U ∧ U.Finite ∧ B.Finite ∧ B.Nonempty ∧
      Nivat.det u' vl = 1 ∧
      dot nℓ vl = 0 ∧ dot nℓ u' = -1 ∧
      a ∈ S ∧ (∀ z ∈ S.erase a, dot nℓ a < dot nℓ z) ∧
      (∀ y ∈ S, ∀ z ∈ S, dot nℓ y = dot nℓ z → y = z) ∧
      (∀ b ∈ B, cz ≤ dot nℓ b) ∧ (∀ b ∈ B, dot nℓ b ≤ czTop) ∧
      (∀ z ∈ S.erase a, ∃ (α : ℤ) (δ : ℕ), (δ : ℤ) ≤ czTop - cz + 1 ∧
        z = a + α • vl - (δ : ℤ) • u') ∧
      (∃ w ∈ coneRegion B vl u' ∩ {y | dot nℓ y = cz - 1 - ((0 : ℕ) : ℤ)},
        ∃ z ∈ S.erase a,
          cz ≤ dot nℓ (z + (w - a)) ∧ dot nℓ (z + (w - a)) ≤ czTop ∧
          z + (w - a) ∉ halfStrip B vl ∪
            (⋃ i' ∈ {i' : ℕ | i' < 0},
              coneRegion B vl u' ∩ {y | dot nℓ y = cz - 1 - (i' : ℤ)})) := by
  classical
  refine ⟨sq1, sq2, {(0, 0), (1, -1), (-1, -2)}, (-1, 0), (0, 1), (0, -1), (0, 0), -2, 0,
    enveloped_sq, posArea_sq1, finite_sq1', ?_, ⟨(0, 0), by exact ⟨le_refl _, by norm_num,
      le_refl _, by norm_num⟩⟩, by simp [Nivat.det], by simp [dot], by simp [dot],
    by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Set.Finite.subset (Set.finite_Icc ((0 : ℤ), (0 : ℤ)) ((2 : ℤ), (2 : ℤ))) ?_
    rintro z ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · intro z hz
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz
    obtain ⟨hne, hz'⟩ := hz
    rcases hz' with rfl | rfl | rfl
    · exact absurd rfl hne
    · simp [dot]
    · simp [dot]
  · intro y hy z hz h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz
    rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
      simp_all [dot]
  · rintro b ⟨-, -, hb3, hb4⟩
    simp only [dot]
    omega
  · rintro b ⟨-, -, hb3, -⟩
    simp only [dot]
    omega
  · intro z hz
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz
    obtain ⟨hne, hz'⟩ := hz
    rcases hz' with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact ⟨-1, 1, by norm_num, by simp⟩
    · exact ⟨1, 2, by norm_num, by simp⟩
  · refine ⟨(2, 3), ⟨?_, ?_⟩, (1, -1), ?_, ?_, ?_, ?_⟩
    · rw [mem_coneRegion_iff]
      refine ⟨(2, 0), ⟨by norm_num, le_refl _, le_refl _, by norm_num⟩, 0, 3, by norm_num⟩
    · simp [dot]
    · simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      refine ⟨?_, Or.inr (Or.inl trivial)⟩
      norm_num [Prod.ext_iff]
    · simp [dot]
    · simp [dot]
    · rintro (⟨b, hb, k, hk⟩ | hU)
      · obtain ⟨-, hb2, -, -⟩ := hb
        simp only [Prod.ext_iff] at hk
        simp at hk
        omega
      · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hU
        obtain ⟨i', hi', -⟩ := hU
        exact absurd hi' (Nat.not_lt_zero i')

/-! ## §7  Definition 3.2 does **not** dominate widths

原文：b3_colle2.txt:402 —— Definition 3.2（`Nivat.LE2.Enveloped`，`LatticeEdges.lean:628`）：
`𝒯` 是 `E(𝒰)`-enveloped，当 `𝒯` 格凸、`𝒯` 的每条边 `ϖ` 都有平行的 `w ∈ E(𝒰)` 且
`|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|`，并且 `|E(𝒯)| = |E(𝒰)|`。

**被否的命题（两个版本一起否掉）**

```
width_le_of_enveloped  : Enveloped U T → ∀ n,       suppVal U n + suppVal U (-n)
                                                  ≤ suppVal T n + suppVal T (-n)
width_le_of_enveloped' : Enveloped U T → ∀ n ∈ E U, 同上
```

`not_width_le_of_enveloped` 的见证 `n` **落在 `E U` 里**，所以它同时否掉两条；
限制到边法向不是修法。

**病灶是 `U` 不格凸，不是别的。** 见证里 `U` 有限、非空、`PosArea`（所以
「加 `PosArea U`」不是修法），`T = sq1` 有限、非空、`PosArea`、格凸，
`Enveloped U T` 逐条在内核里验过（`PROTOCOL.md` §7）。唯一不成立的前提是
`IsLatticeConvexRegion U`——`not_isLatticeConvexRegion_stretch` 把这一条也在内核里证了。

**读法**：Definition 3.2 只数**边上的格点个数**。`U` 不格凸时，一条「边」可以只有
两个格点却横跨很长一段（`stretch` 的左右两条边各只有 2 个格点，却长 2），
于是 `|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|` 完全不约束长度。要把点数换成长度，必须假设 `U` 格凸；
那一步（边点数 → 边向量长度 → 绕边界一圈的宽度公式）本文件**没有**做，见 §7.5。

**真陈述在这里**：`width_le_of_translate_subset`。宽度支配是**平移包含的推论**，
不是它的平行结论——所以它不该被单独立项。 -/

/-- **宽度支配来自平移包含。**

原文：b3_colle2.txt:402 —— Definition 3.2 的用处是让 `𝒰` 的某个平移装进 `𝒯`
（Figure 10，`:798`，把 `𝒮_φ` 的一个平移摆进 `B`）。一旦有了那个平移，宽度支配是
三行的推论。

**量词对应原文**：
- `v` ↔ 原文里把 `𝒰` 摆进 `𝒯` 的那个平移向量；
- `h : ∀ z ∈ U, z + v ∈ T` ↔ `𝒰 + v ⊆ 𝒯`（等价于 `Nivat.LE2.shift v U ⊆ T`，
  因为 `shift v U = {z | z - v ∈ U}`；这里不写 `shift` 是为了不与正在改
  `EnvTranslate.lean` 的那条 lane 争文件）；
- `n` ↔ 任意方向，**不限于边法向**；结论对每个 `n` 都成立。

`suppVal U n + suppVal U (-n)` 是 `U` 在 `n` 方向的宽度（`≥ 0`）。 -/
theorem width_le_of_translate_subset {U T : Set (ℤ × ℤ)}
    (hUfin : U.Finite) (hUne : U.Nonempty) (hTfin : T.Finite) (hTne : T.Nonempty)
    {v : ℤ × ℤ} (h : ∀ z ∈ U, z + v ∈ T) (n : ℤ × ℤ) :
    suppVal U n + suppVal U (-n) ≤ suppVal T n + suppVal T (-n) := by
  obtain ⟨p, hp, hpe⟩ := exists_suppVal_eq hUfin hUne n
  obtain ⟨q, hq, hqe⟩ := exists_suppVal_eq hUfin hUne (-n)
  have h1 : dot n (p + v) ≤ suppVal T n := le_suppVal hTfin hTne (h p hp)
  have h2 : dot (-n) (q + v) ≤ suppVal T (-n) := le_suppVal hTfin hTne (h q hq)
  rw [dot_add, hpe] at h1
  rw [dot_add, hqe, dot_neg_left] at h2
  linarith

/-! ### §7.1  见证：`stretch`，四个角点，竖直方向拉长到 2

这不是原文的记号，是反例见证。`stretch` 与 `sq1 = [0,1]²` 有**同一个法扇**
（四条轴向边），每条边上都恰好两个格点，所以 Definition 3.2 的每一条都成立；
但它在 `(0,1)` 方向的宽度是 2，而 `sq1` 只有 1。 -/

/-- 反例见证：`{(0,0), (1,0), (0,2), (1,2)}`，`[0,1] × [0,2]` 的四个角点。 -/
def stretch : Set (ℤ × ℤ) := {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 2), (1, 2)}

theorem mem_stretch {z : ℤ × ℤ} :
    z ∈ stretch ↔ z = (0, 0) ∨ z = (1, 0) ∨ z = (0, 2) ∨ z = (1, 2) := Iff.rfl

theorem zz_mem_stretch : ((0 : ℤ), (0 : ℤ)) ∈ stretch := by rw [mem_stretch]; tauto
theorem zo_mem_stretch : ((1 : ℤ), (0 : ℤ)) ∈ stretch := by rw [mem_stretch]; tauto
theorem zt_mem_stretch : ((0 : ℤ), (2 : ℤ)) ∈ stretch := by rw [mem_stretch]; tauto
theorem ot_mem_stretch : ((1 : ℤ), (2 : ℤ)) ∈ stretch := by rw [mem_stretch]; tauto

theorem finite_stretch : stretch.Finite :=
  (((Set.finite_singleton ((1 : ℤ), (2 : ℤ))).insert ((0 : ℤ), (2 : ℤ))).insert
    ((1 : ℤ), (0 : ℤ))).insert ((0 : ℤ), (0 : ℤ))

theorem nonempty_stretch : stretch.Nonempty := ⟨(0, 0), zz_mem_stretch⟩

/-- `dot` on an explicit pair, in components — keeps `omega` away from `Prod` projections. -/
theorem dot_mk (n : ℤ × ℤ) (a b : ℤ) : dot n (a, b) = n.1 * a + n.2 * b := rfl

/-- Off the two axis directions, `stretch` exposes a single corner: it has no other edge. -/
theorem face_stretch_subsingleton {n : ℤ × ℤ} (h1 : n.1 ≠ 0) (h2 : n.2 ≠ 0) :
    (face stretch n).Subsingleton := by
  rintro x ⟨hxS, hxm⟩ y ⟨hyS, hym⟩
  have a1 := hxm _ zz_mem_stretch
  have a2 := hxm _ zo_mem_stretch
  have a3 := hxm _ zt_mem_stretch
  have a4 := hxm _ ot_mem_stretch
  have b1 := hym _ zz_mem_stretch
  have b2 := hym _ zo_mem_stretch
  have b3 := hym _ zt_mem_stretch
  have b4 := hym _ ot_mem_stretch
  rw [mem_stretch] at hxS hyS
  rcases hxS with rfl | rfl | rfl | rfl <;> rcases hyS with rfl | rfl | rfl | rfl <;>
    simp only [dot_mk] at a1 a2 a3 a4 b1 b2 b3 b4 <;>
    first
      | rfl
      | (exfalso; omega)

/-- The four axis faces of `stretch`, as memberships (for `Set.Nontrivial`). -/
theorem mem_face_stretch_right_a : ((1 : ℤ), (0 : ℤ)) ∈ face stretch ((1 : ℤ), (0 : ℤ)) := by
  refine ⟨zo_mem_stretch, ?_⟩
  intro y hy; rw [mem_stretch] at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp

theorem mem_face_stretch_right_b : ((1 : ℤ), (2 : ℤ)) ∈ face stretch ((1 : ℤ), (0 : ℤ)) := by
  refine ⟨ot_mem_stretch, ?_⟩
  intro y hy; rw [mem_stretch] at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp

theorem mem_face_stretch_left_a : ((0 : ℤ), (0 : ℤ)) ∈ face stretch ((-1 : ℤ), (0 : ℤ)) := by
  refine ⟨zz_mem_stretch, ?_⟩
  intro y hy; rw [mem_stretch] at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp

theorem mem_face_stretch_left_b : ((0 : ℤ), (2 : ℤ)) ∈ face stretch ((-1 : ℤ), (0 : ℤ)) := by
  refine ⟨zt_mem_stretch, ?_⟩
  intro y hy; rw [mem_stretch] at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp

theorem mem_face_stretch_top_a : ((0 : ℤ), (2 : ℤ)) ∈ face stretch ((0 : ℤ), (1 : ℤ)) := by
  refine ⟨zt_mem_stretch, ?_⟩
  intro y hy; rw [mem_stretch] at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp

theorem mem_face_stretch_top_b : ((1 : ℤ), (2 : ℤ)) ∈ face stretch ((0 : ℤ), (1 : ℤ)) := by
  refine ⟨ot_mem_stretch, ?_⟩
  intro y hy; rw [mem_stretch] at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp

theorem mem_face_stretch_bot_a : ((0 : ℤ), (0 : ℤ)) ∈ face stretch ((0 : ℤ), (-1 : ℤ)) := by
  refine ⟨zz_mem_stretch, ?_⟩
  intro y hy; rw [mem_stretch] at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp

theorem mem_face_stretch_bot_b : ((1 : ℤ), (0 : ℤ)) ∈ face stretch ((0 : ℤ), (-1 : ℤ)) := by
  refine ⟨zo_mem_stretch, ?_⟩
  intro y hy; rw [mem_stretch] at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp

/-- **`stretch` has exactly the four edge normals of `sq1`.** -/
theorem E_stretch : E stretch = {((1 : ℤ), (0 : ℤ)), (-1, 0), (0, 1), (0, -1)} := by
  ext n
  constructor
  · rintro ⟨hprim, hnt⟩
    by_cases h1 : n.1 = 0
    · rcases prim_eq_of_fst_eq_zero hprim h1 with rfl | rfl <;> simp
    · by_cases h2 : n.2 = 0
      · rcases prim_eq_of_snd_eq_zero hprim h2 with rfl | rfl <;> simp
      · exfalso
        obtain ⟨p, hp, q, hq, hpq⟩ := hnt
        exact hpq (face_stretch_subsingleton h1 h2 hp hq)
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨by decide, ⟨_, mem_face_stretch_right_a, _, mem_face_stretch_right_b,
        by norm_num [Prod.ext_iff]⟩⟩
    · exact ⟨by decide, ⟨_, mem_face_stretch_left_a, _, mem_face_stretch_left_b,
        by norm_num [Prod.ext_iff]⟩⟩
    · exact ⟨by decide, ⟨_, mem_face_stretch_top_a, _, mem_face_stretch_top_b,
        by norm_num [Prod.ext_iff]⟩⟩
    · exact ⟨by decide, ⟨_, mem_face_stretch_bot_a, _, mem_face_stretch_bot_b,
        by norm_num [Prod.ext_iff]⟩⟩

/-! ### §7.2  Each edge of `stretch` carries at most two lattice points -/

theorem encard_face_stretch_right : (face stretch ((1 : ℤ), (0 : ℤ))).encard ≤ 2 := by
  have hsub : face stretch ((1 : ℤ), (0 : ℤ)) ⊆ {((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} := by
    rintro z ⟨hz, hm⟩
    have h := hm _ zo_mem_stretch
    rw [mem_stretch] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all
  exact le_trans (Set.encard_mono hsub) (le_of_eq (Set.encard_pair (by norm_num [Prod.ext_iff])))

theorem encard_face_stretch_left : (face stretch ((-1 : ℤ), (0 : ℤ))).encard ≤ 2 := by
  have hsub : face stretch ((-1 : ℤ), (0 : ℤ)) ⊆ {((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (2 : ℤ))} := by
    rintro z ⟨hz, hm⟩
    have h := hm _ zz_mem_stretch
    rw [mem_stretch] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all
  exact le_trans (Set.encard_mono hsub) (le_of_eq (Set.encard_pair (by norm_num [Prod.ext_iff])))

theorem encard_face_stretch_top : (face stretch ((0 : ℤ), (1 : ℤ))).encard ≤ 2 := by
  have hsub : face stretch ((0 : ℤ), (1 : ℤ)) ⊆ {((0 : ℤ), (2 : ℤ)), ((1 : ℤ), (2 : ℤ))} := by
    rintro z ⟨hz, hm⟩
    have h := hm _ zt_mem_stretch
    rw [mem_stretch] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all
  exact le_trans (Set.encard_mono hsub) (le_of_eq (Set.encard_pair (by norm_num [Prod.ext_iff])))

theorem encard_face_stretch_bot : (face stretch ((0 : ℤ), (-1 : ℤ))).encard ≤ 2 := by
  have hsub : face stretch ((0 : ℤ), (-1 : ℤ)) ⊆ {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} := by
    rintro z ⟨hz, hm⟩
    have h := hm _ zz_mem_stretch
    rw [mem_stretch] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all
  exact le_trans (Set.encard_mono hsub) (le_of_eq (Set.encard_pair (by norm_num [Prod.ext_iff])))

/-! ### §7.3  `sq1` is `E(stretch)`-enveloped, verbatim Definition 3.2 -/

/-- **`Enveloped stretch sq1`**，原文 `b3_colle2.txt:402` 的三条逐条验过：
`sq1` 格凸（`isLatticeConvexRegion_sq1`）；`E sq1` 的每个法向都是 `E stretch` 的法向
且格点数被支配（`2 ≤ 2`）；`|E sq1| = |E stretch|`（两边都是同一个四元集）。 -/
theorem enveloped_stretch_sq1 : Enveloped stretch sq1 := by
  refine ⟨⟨isLatticeConvexRegion_sq1, ?_⟩, ?_⟩
  · intro n hn
    rw [E_sq1] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨by rw [E_stretch]; simp,
        by rw [encard_face_sq1_right]; exact encard_face_stretch_right⟩
    · exact ⟨by rw [E_stretch]; simp,
        by rw [encard_face_sq1_left]; exact encard_face_stretch_left⟩
    · exact ⟨by rw [E_stretch]; simp,
        by rw [encard_face_sq1_top]; exact encard_face_stretch_top⟩
    · exact ⟨by rw [E_stretch]; simp,
        by rw [encard_face_sq1_bot]; exact encard_face_stretch_bot⟩
  · rw [E_sq1, E_stretch]

/-- `stretch` has positive area, so "add `PosArea U`" is **not** a repair. -/
theorem posArea_stretch : PosArea stretch :=
  ⟨(0, 0), zz_mem_stretch, (1, 0), zo_mem_stretch, (0, 2), zt_mem_stretch, by
    norm_num [Nivat.det]⟩

/-- **`stretch` is not lattice-convex** — this is the one hypothesis of
`width_le_of_enveloped` that the witness violates. `(0,1)` is the midpoint of
`(0,0)` and `(0,2)`, both in `stretch`, but is not in `stretch`. -/
theorem not_isLatticeConvexRegion_stretch : ¬ IsLatticeConvexRegion stretch := by
  rintro ⟨C, hconv, -, heq⟩
  have h00 : Nivat.toReal ((0 : ℤ), (0 : ℤ)) ∈ C := by
    have hm : ((0 : ℤ), (0 : ℤ)) ∈ stretch := zz_mem_stretch
    rw [heq] at hm; exact hm
  have h02 : Nivat.toReal ((0 : ℤ), (2 : ℤ)) ∈ C := by
    have hm : ((0 : ℤ), (2 : ℤ)) ∈ stretch := zt_mem_stretch
    rw [heq] at hm; exact hm
  have hmid := hconv h00 h02 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hpt : (1 / 2 : ℝ) • Nivat.toReal ((0 : ℤ), (0 : ℤ))
      + (1 / 2 : ℝ) • Nivat.toReal ((0 : ℤ), (2 : ℤ)) = Nivat.toReal ((0 : ℤ), (1 : ℤ)) := by
    simp only [Nivat.toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
    norm_num
  rw [hpt] at hmid
  have hmem : ((0 : ℤ), (1 : ℤ)) ∈ stretch := by rw [heq]; exact hmid
  rw [mem_stretch] at hmem
  norm_num [Prod.ext_iff] at hmem

/-! ### §7.4  The refutation -/

/-- **`IsLatticeConvexRegion U` 是我们这版 Definition 3.2 的承重前提。**

⚠ **读法已改（2026-09-20，集成者裁决，`NOTE.md` 末节「已裁决」）。** 本条**不再**读作
「宽度引理是假的」。原文 `b3_colle2.txt:402` 对 `𝒰` 带三条常备前提：

> Let `𝒰 ⊂ ℤ²` be a **finite, convex set** such that `conv(𝒰)` has positive area.
> A **convex set** `𝒯 ⊂ ℤ²` is said to be weakly `E(𝒰)`-enveloped if, for every edge
> `ϖ ∈ E(𝒯)`, there exists an edge `w ∈ E(𝒰)` parallel to `ϖ` with `|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|`.

而 `:31` 定的「convex」正是我们的 `IsLatticeConvexRegion`（`𝒮 = conv(𝒮) ∩ ℤ^d`，
闭凸包取交）。我们的 `Nivat.LE2.Enveloped`（`LatticeEdges.lean:625-629`）只要求 `T` 格凸，
`U` 的**三条**一条都没写进去。所以下面这个见证否掉的是**我们的转写**，不是 Collé。

**集成者裁决：`Enveloped` 不改**（它作为**前提**出现，弱一点更好用；`U` 的凸性归生产者，
链上由 `ChainAsm.isLatticeConvexRegion_coe`（`ChainAssemble.lean:347`）免费给出）。
真正要用「边点数 = 边长」的引理各自带 `IsLatticeConvexRegion U` 作侧前提——
那一步现在已经证了，见 §8 的 `encard_face_eq_of_latticeConvex`。

**本条保留的理由（`PROTOCOL.md` §14）**：它是「被否的是我们的编码，不是原文」的实例，
并且在内核里钉死了**哪一条前提承重**。被否的陈述是

```
Enveloped U T → suppVal U n + suppVal U (-n) ≤ suppVal T n + suppVal T (-n)
```

见证 `U = stretch`、`T = sq1`、`n = (0,1)`：宽度 `2 ≰ 1`，而 `n ∈ E U`，所以
把 `∀ n` 换成 `∀ n ∈ E U` 也照样假——**限制到边法向不是修法**。

**见证逐条验过前提**（`PROTOCOL.md` §7）：`Enveloped U T` 是 `enveloped_stretch_sq1`；
`U` 有限、非空、`PosArea`（所以「加 `PosArea U`」也不是修法）；`T` 有限、非空、
`PosArea`、格凸。唯一失败的是 `IsLatticeConvexRegion U`
（`not_isLatticeConvexRegion_stretch`）——那**恰好**是原文 `:402` 写了而我们漏了的那条。 -/
theorem not_width_le_of_enveloped :
    ∃ U T : Set (ℤ × ℤ),
      Enveloped U T ∧
      U.Finite ∧ U.Nonempty ∧ PosArea U ∧
      T.Finite ∧ T.Nonempty ∧ PosArea T ∧ IsLatticeConvexRegion T ∧
      ¬ IsLatticeConvexRegion U ∧
      ∃ n ∈ E U,
        ¬ (suppVal U n + suppVal U (-n) ≤ suppVal T n + suppVal T (-n)) := by
  refine ⟨stretch, sq1, enveloped_stretch_sq1, finite_stretch, nonempty_stretch,
    posArea_stretch, finite_sq1', nonempty_sq1, posArea_sq1, isLatticeConvexRegion_sq1,
    not_isLatticeConvexRegion_stretch, (0, 1), by rw [E_stretch]; simp, ?_⟩
  have hneg : -((0 : ℤ), (1 : ℤ)) = ((0 : ℤ), (-1 : ℤ)) := by norm_num [Prod.ext_iff]
  rw [hneg]
  have e1 : suppVal stretch ((0 : ℤ), (1 : ℤ)) = 2 := by
    rw [suppVal_eq mem_face_stretch_top_a]; simp
  have e2 : suppVal stretch ((0 : ℤ), (-1 : ℤ)) = 0 := by
    rw [suppVal_eq mem_face_stretch_bot_a]; simp
  have e3 : suppVal sq1 ((0 : ℤ), (1 : ℤ)) = 1 := by
    rw [suppVal_eq face_sq1_top]; simp
  have e4 : suppVal sq1 ((0 : ℤ), (-1 : ℤ)) = 0 := by
    rw [suppVal_eq face_sq1_bot]; simp
  rw [e1, e2, e3, e4]
  norm_num

/-! ### §7.5  欠账

`width_le_of_enveloped` 的**正确**版本要带 `IsLatticeConvexRegion U`（原文 `:402` 本来
就写了，见上条 docstring 的裁决）。缺的两步：

1. ~~**边点数 → 边向量长度**~~ 🟢 **2026-09-20 已证，见 §8
   `encard_face_eq_of_latticeConvex`**：`U` 格凸时 `face U n` 是一条线段上的**连续**格点，
   于是 `(face U n).encard = L + 1`，`L` 是边向量沿 `dir n` 的格长。没有 `U` 格凸
   这一步就是假的——`stretch` 的左边只有 2 个格点却长 2，这正是上面反例的机理。
2. **绕边界一圈的宽度公式**：`width_P(n) = Σ_{ν ∈ E P, dot n (dir ν) > 0} L(ν) · dot n (dir ν)`。
   要先把 `E P` 按角序排好、证边向量之和为零。Mathlib 没有多边形边界游走的 API。
   **集成者裁决（2026-09-20）：这一步不做，不立项。**

⚠ **不要为此单独立项。** `width_le_of_translate_subset`（§7 开头）表明宽度支配是
`Enveloped U T → ∃ v, shift v U ⊆ T` 的**推论**；那条平移陈述本来就在另一条 lane 上。
平移一旦拿到，宽度三行就出来了；平移拿不到，单独证宽度也不解决任何下游义务
（`hwinL` 的 level 半边在 §6 的反例里本来就已经满足，见 §6 结论的两条 level 合取）。 -/

/-! ## §8  边上的格点数 = 边的格长 + 1（原文 `:402` 的 `|w ∩ 𝒰|`）

**原文：b3_colle2.txt:402 + :31。** `:402` 的大小条款数的是 `|w ∩ 𝒰|`，即边 `w` 上的
**格点个数**；`:31` 定的「convex」是 `𝒮 = conv(𝒮) ∩ ℤ^d`，也就是我们的
`IsLatticeConvexRegion`。本节把点数换成**长度**：格凸时一条边上的格点恰是一个
以边的本原方向 `d` 为公差的等差数列，于是 `|w ∩ 𝒰| = L + 1`。

这一步**必须**带 `U` 格凸：§7 的 `stretch` 就是去掉它之后的反例（左右两条边各 2 个
格点、却长 2）。§7.5 的第二步（绕边界一圈的宽度公式）不在本节范围内。 -/

/-! ### §8.1  复用已有引理（`PROTOCOL.md` §20：先查再写）

本节需要的三件几何事实**主仓已经有了**，在 `Nivat.LE2` 里，由 `RegionCut.lean` 提供：

* `Nivat.LE2.prim_dir_of_prim`（`RegionCut.lean:161`）：`Prim n → Prim (dir n)`；
* `Nivat.LE2.exists_zsmul_dir_of_mem_face`（`RegionCut.lean:172`）：同一条 face 上的两点
  相差 `dir n` 的整数倍；
* `Nivat.LE2.mem_of_between`（`RegionCut.lean:201`）：格凸集上一条直线的两点之间的格点仍在集内
  （`IsLatticeConvexRegion` 在那里经 `eq_preimage_convHullOf` 展开）。

⚠ 本节初稿把这三条各自重证了一遍才发现重复（§20 的实例）。现在一律引用，不再自证；
新内容只有下面 `encard_face_eq_of_latticeConvex` 一条——点数与长度的换算，
全树此前没有。 -/

/-- **原文 `:402` 的 `|w ∩ 𝒰|`：格凸集的一条边上的格点数 = 边的格长 + 1。**

原文：b3_colle2.txt:402（`|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|`，数的是边上的格点个数）
＋ b3_colle2.txt:31（「convex」= `𝒮 = conv(𝒮) ∩ ℤ^d` = `IsLatticeConvexRegion`）。

**量词对应原文**：
- `U` ↔ `𝒰`；`:402` 对 `𝒰` 的三条常备前提 "finite, convex, `conv(𝒰)` has positive area"
  里，本条只用到前两条 —— `hUfin`、`hUlc`；
- `n ∈ E U` ↔ `w ∈ E(𝒰)`，`𝒰` 的一条边（的外法向）；
- `face U n` ↔ `w ∩ 𝒰`，那条边上的格点集；
- `d` ↔ 边的**本原**方向（取 `dir n`，与 `n` 垂直）；
- `L` ↔ 边向量沿 `d` 的格长，`|w ∩ 𝒰| = L + 1` 就是「点数 = 长度 + 1」；
- 第二个合取 ↔ 「`w ∩ 𝒰` 共线」，即这些格点是以 `d` 为公差的等差数列。

⚠ **`PosArea U` 不是本条的前提**（2026-09-20 集成者裁决：初版带过一个 `hUarea` binder，
证明里从未用到，未用的前提只会让下游更难调用，已删）。`:402` 把正面积写成 `𝒰` 的常备前提，
但这一步用不上；需要它的调用者在链上免费就有（`posArea_of_envOf`）。
真正承重的是 `hUlc`：去掉它这条就是假的，反例是 §7 的 `stretch`
（`posArea_stretch` 为真，所以**不是**正面积在分开这两者）。 -/
theorem encard_face_eq_of_latticeConvex {U : Set (ℤ × ℤ)} {n : ℤ × ℤ}
    (hUlc : IsLatticeConvexRegion U) (hUfin : U.Finite)
    (hn : n ∈ E U) :
    ∃ d : ℤ × ℤ, Primitive d ∧ ∃ L : ℕ, (face U n).encard = L + 1 ∧
      (∀ z ∈ face U n, ∀ w ∈ face U n, ∃ t : ℤ, w = z + t • d) := by
  classical
  obtain ⟨hprim, hnt⟩ := hn
  have hnne : n ≠ 0 := hprim.ne_zero
  have hdprim : Prim (dir n) := prim_dir_of_prim hprim
  have hdne : dir n ≠ 0 := hdprim.ne_zero
  have hdotd : dot n (dir n) = 0 := dot_dir n
  -- 同一条边上的任意两点相差 `dir n` 的整数倍（`RegionCut.lean:172`）
  have hpar : ∀ z ∈ face U n, ∀ w ∈ face U n, ∃ t : ℤ, w = z + t • dir n :=
    fun _ hz _ hw => exists_zsmul_dir_of_mem_face hprim hz hw
  refine ⟨dir n, prim_iff_primitive.mp hdprim, ?_⟩
  obtain ⟨z₀, hz₀, w₀, hw₀, hne₀⟩ := hnt
  -- 沿 `dir n` 的坐标
  set f : ℤ → ℤ × ℤ := fun t => z₀ + t • dir n with hf
  have hinj : Function.Injective f := by
    intro s t hst
    have h0 : (s - t) • dir n = 0 := by
      have := sub_eq_zero.mpr hst
      simp only [hf] at this
      simpa [sub_smul] using this
    rcases smul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hdne
  set Tset : Set ℤ := {t | f t ∈ face U n} with hT
  have hffin : (face U n).Finite := hUfin.subset (face_subset _ _)
  have hTfin : Tset.Finite := Set.Finite.preimage hinj.injOn hffin
  have hT0 : (0 : ℤ) ∈ Tset := by
    show f 0 ∈ face U n
    simpa [hf] using hz₀
  have himg : face U n = f '' Tset := by
    ext w
    constructor
    · intro hw
      obtain ⟨t, ht⟩ := hpar z₀ hz₀ w hw
      have hft : f t = w := ht.symm
      exact ⟨t, by show f t ∈ face U n; rw [hft]; exact hw, hft⟩
    · rintro ⟨t, ht, rfl⟩
      exact ht
  -- 格凸 ⟹ 坐标集是一个整数区间
  have hTne : hTfin.toFinset.Nonempty := ⟨0, hTfin.mem_toFinset.mpr hT0⟩
  set a : ℤ := hTfin.toFinset.min' hTne with ha
  set b : ℤ := hTfin.toFinset.max' hTne with hb
  have haT : a ∈ Tset := hTfin.mem_toFinset.mp (Finset.min'_mem _ _)
  have hbT : b ∈ Tset := hTfin.mem_toFinset.mp (Finset.max'_mem _ _)
  have hab : a ≤ b := Finset.min'_le _ _ (Finset.max'_mem _ hTne)
  have hIcc : Tset = Set.Icc a b := by
    ext t
    constructor
    · intro ht
      exact ⟨Finset.min'_le _ _ (hTfin.mem_toFinset.mpr ht),
        Finset.le_max' _ _ (hTfin.mem_toFinset.mpr ht)⟩
    · rintro ⟨h1, h2⟩
      show f t ∈ face U n
      have hU : f t ∈ U := mem_of_between hUlc haT.1 hbT.1 h1 h2
      refine ⟨hU, ?_⟩
      intro y hy
      have hlev : dot n (f t) = dot n z₀ := by
        simp only [hf, dot_add, Nivat.ConeRegion.dot_zsmul, hdotd, mul_zero, add_zero]
      rw [hlev]
      exact hz₀.2 y hy
  have hcard : (Set.Icc a b : Set ℤ).encard = ((b + 1 - a).toNat : ℕ∞) := by
    rw [← Finset.coe_Icc, Set.encard_coe_eq_coe_finsetCard, Int.card_Icc]
  refine ⟨(b - a).toNat, ?_, hpar⟩
  rw [himg, hIcc, Set.InjOn.encard_image hinj.injOn, hcard]
  have hnat : (b + 1 - a).toNat = (b - a).toNat + 1 := by omega
  rw [hnat]
  push_cast
  ring

/-! ## §9  宽度公式的**逐项**那一半（`§7.5` 第二步的可做部分）

原文：b3_colle2.txt:402（Definition 3.2 的大小条款 `|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|`）。

§7.5 把 `width_le_of_enveloped` 的欠账拆成两步，第一步（点数 → 格长）是 §8。本节做的是
第二步里**不需要绕边界一圈**的那部分：**单条边的贡献已经被支配**。写成公式，
待证的宽度等式是

```
width_P(n) = Σ_{ν ∈ E P, ⟪n, dir ν⟫ > 0} L_P(ν) · ⟪n, dir ν⟫       （仍然欠着）
```

而本节证的是**同一个和式的每一项对 `≤` 都已经成立**：

```
L_U(ν) · |⟪n, dir ν⟫| ≤ width_T(ν 那一项所在的 width_T(n))        （edgeLen_mul_le_width_of_enveloped）
```

⚠ **逐项成立推不出求和成立**，因为待证的是 `Σ_ν (项_U) ≤ width_T`，而本节给的是
`∀ν, 项_U ≤ width_T`——右端没有被拆开。要把右端拆成同一个和式，正是 §7.5 第二步
（法向按角排序、边向量首尾相接、`Σ L(ν)·dir ν = 0`），**本文件没有做，也不声称做了**。
所以本节**不是** `width_le_of_enveloped`，只是它的逐项分量；`not_width_le_of_enveloped`
（§7.4）仍然是那条陈述在缺 `IsLatticeConvexRegion U` 时的内核反例。

量词对应原文：`ν ↔ w ∈ E(𝒰)` 那条边；`L_U(ν) ↔ |w ∩ 𝒰| - 1`（§8 的换算）；
`n` 是任意方向，不限于边法向——原文没有这个量词，它是我们为了谈「宽度」引入的，
所以本节三条都**只**断言不等式，不断言任何原文语句。 -/

/-- **一条边的两个端点，相距 `≥ L` 步 `dir n`。**

`encard_face_eq_of_latticeConvex`（§8）只给出「点数 `= L + 1`」与共线性，没有交出端点；
本条把端点取出来。⚠ **不需要 `IsLatticeConvexRegion U`**：共线的 `L+1` 个格点无论是否
连续，最外两个的间距都 `≥ L`。（格凸只在把「点数」读成「格长」时才承重，那是 §8。） -/
theorem exists_face_endpoints {U : Set (ℤ × ℤ)} {n : ℤ × ℤ} {L : ℕ}
    (hUfin : U.Finite) (hn : n ∈ E U) (hL : (face U n).encard = L + 1) :
    ∃ z ∈ face U n, ∃ w ∈ face U n, ∃ t : ℤ, (L : ℤ) ≤ t ∧ w = z + t • dir n := by
  classical
  obtain ⟨hprim, hnt⟩ := hn
  have hdprim : Prim (dir n) := prim_dir_of_prim hprim
  have hdne : dir n ≠ 0 := hdprim.ne_zero
  obtain ⟨z₀, hz₀, w₀, -, -⟩ := hnt
  set f : ℤ → ℤ × ℤ := fun t => z₀ + t • dir n with hf
  have hinj : Function.Injective f := by
    intro s t hst
    have h0 : (s - t) • dir n = 0 := by
      have := sub_eq_zero.mpr hst
      simp only [hf] at this
      simpa [sub_smul] using this
    rcases smul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hdne
  set Tset : Set ℤ := {t | f t ∈ face U n} with hTdef
  have hffin : (face U n).Finite := hUfin.subset (face_subset _ _)
  have hTfin : Tset.Finite := Set.Finite.preimage hinj.injOn hffin
  have hT0 : (0 : ℤ) ∈ Tset := by
    show f 0 ∈ face U n
    simpa [hf] using hz₀
  have himg : face U n = f '' Tset := by
    ext w
    constructor
    · intro hw
      obtain ⟨t, ht⟩ := exists_zsmul_dir_of_mem_face hprim hz₀ hw
      have hft : f t = w := ht.symm
      exact ⟨t, by show f t ∈ face U n; rw [hft]; exact hw, hft⟩
    · rintro ⟨t, ht, rfl⟩
      exact ht
  have hTne : hTfin.toFinset.Nonempty := ⟨0, hTfin.mem_toFinset.mpr hT0⟩
  set a : ℤ := hTfin.toFinset.min' hTne with ha
  set b : ℤ := hTfin.toFinset.max' hTne with hb
  have haT : a ∈ Tset := hTfin.mem_toFinset.mp (Finset.min'_mem _ _)
  have hbT : b ∈ Tset := hTfin.mem_toFinset.mp (Finset.max'_mem _ _)
  have hab : a ≤ b := Finset.min'_le _ _ (Finset.max'_mem _ hTne)
  -- 点数 = `Tset` 的基数
  have hTcard : Tset.encard = (hTfin.toFinset.card : ℕ∞) := by
    rw [← Set.encard_coe_eq_coe_finsetCard, hTfin.coe_toFinset]
  have hcardE : ((hTfin.toFinset.card : ℕ) : ℕ∞) = ((L : ℕ) : ℕ∞) + 1 := by
    rw [← hTcard, ← Set.InjOn.encard_image (f := f) hinj.injOn, ← himg, hL]
  have hcard : hTfin.toFinset.card = L + 1 := by exact_mod_cast hcardE
  have hsub : hTfin.toFinset ⊆ Finset.Icc a b := fun t ht =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ ht, Finset.le_max' _ _ ht⟩
  have hle := Finset.card_le_card hsub
  rw [hcard, Int.card_Icc] at hle
  refine ⟨f a, haT, f b, hbT, b - a, by omega, ?_⟩
  show z₀ + b • dir n = z₀ + a • dir n + (b - a) • dir n
  rw [sub_smul]
  abel

/-- **宽度的下界原子**：`T` 里任意两点的 `n`-差都 `≤` `T` 在 `n` 方向的宽度。 -/
theorem dot_sub_le_width {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    {z w : ℤ × ℤ} (hz : z ∈ T) (hw : w ∈ T) (n : ℤ × ℤ) :
    dot n (w - z) ≤ suppVal T n + suppVal T (-n) := by
  have h1 : dot n w ≤ suppVal T n := le_suppVal hfin hne hw
  have h2 : dot (-n) z ≤ suppVal T (-n) := le_suppVal hfin hne hz
  rw [dot_neg_left] at h2
  rw [dot_sub]
  omega

/-- **Definition 3.2 的大小条款换算成格长的不等式。**

原文：b3_colle2.txt:402 的 `|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|`，两端各用 §8 换成「格长 + 1」之后
就是 `L_U(ν) ≤ L_T(ν)`。这是 envelopedness 在整条宽度论证里**唯一**进入的地方。 -/
theorem edgeLen_le_of_enveloped {U T : Set (ℤ × ℤ)} {n : ℤ × ℤ} {LU LT : ℕ}
    (hEUfin : (E U).Finite) (henv : Enveloped U T) (hn : n ∈ E U)
    (hLU : (face U n).encard = LU + 1) (hLT : (face T n).encard = LT + 1) :
    LU ≤ LT := by
  have h := Enveloped.face_encard_le hEUfin henv hn
  rw [hLU, hLT] at h
  have h2 : ((LU + 1 : ℕ) : ℕ∞) ≤ ((LT + 1 : ℕ) : ℕ∞) := by push_cast; exact h
  have h3 : LU + 1 ≤ LT + 1 := by exact_mod_cast h2
  omega

/-- **逐项支配：`𝒰` 的一条边对宽度的贡献，已经被 `𝒯` 的宽度支配。**

原文：b3_colle2.txt:402。`ν ↔ w ∈ E(𝒰)`；`LU ↔ |w ∩ 𝒰| - 1`；`n` 为任意方向。

⚠ **这不是 `width_le_of_enveloped`。** 待证的是 `Σ_ν 项_U(n) ≤ width_T(n)`；本条给的是
`∀ ν, 项_U(n) ≤ width_T(n)`。把左端的和式合起来需要 §7.5 第二步（绕边界一圈），
**未做**。本条的用处是把「envelopedness 够不够」这个问题精确化：**逐项够，求和不够**。 -/
theorem edgeLen_mul_le_width_of_enveloped {U T : Set (ℤ × ℤ)} {ν : ℤ × ℤ} {LU : ℕ}
    (hEUfin : (E U).Finite) (hTfin : T.Finite) (hTne : T.Nonempty)
    (henv : Enveloped U T) (hν : ν ∈ E U)
    (hLU : (face U ν).encard = LU + 1) (n : ℤ × ℤ) :
    (LU : ℤ) * |dot n (dir ν)| ≤ suppVal T n + suppVal T (-n) := by
  have hνT : ν ∈ E T := by rw [Enveloped.E_eq hEUfin henv]; exact hν
  obtain ⟨-, -, LT, hLT, -⟩ :=
    encard_face_eq_of_latticeConvex henv.1.1 hTfin hνT
  have hLUT : LU ≤ LT := edgeLen_le_of_enveloped hEUfin henv hν hLU hLT
  obtain ⟨z, hz, w, hw, t, hLt, hwz⟩ := exists_face_endpoints hTfin hνT hLT
  have hzT : z ∈ T := face_subset _ _ hz
  have hwT : w ∈ T := face_subset _ _ hw
  have hdiff : w - z = t • dir ν := by rw [hwz]; abel
  have hdot : dot n (w - z) = t * dot n (dir ν) := by
    rw [hdiff, dot_zsmul]
  have htL : (LU : ℤ) ≤ t := le_trans (by exact_mod_cast hLUT) hLt
  have hLU0 : (0 : ℤ) ≤ (LU : ℤ) := Int.natCast_nonneg LU
  by_cases hsign : 0 ≤ dot n (dir ν)
  · have h1 : dot n (w - z) ≤ suppVal T n + suppVal T (-n) :=
      dot_sub_le_width hTfin hTne hzT hwT n
    rw [hdot] at h1
    have h2 : (LU : ℤ) * dot n (dir ν) ≤ t * dot n (dir ν) :=
      mul_le_mul_of_nonneg_right htL hsign
    rw [abs_of_nonneg hsign]
    omega
  · have hsign' : dot n (dir ν) < 0 := by omega
    have h1 : dot n (z - w) ≤ suppVal T n + suppVal T (-n) :=
      dot_sub_le_width hTfin hTne hwT hzT n
    have hdot' : dot n (z - w) = t * (-dot n (dir ν)) := by
      have hzw : z - w = (-t) • dir ν := by rw [neg_zsmul, ← hdiff]; abel
      rw [hzw, dot_zsmul]; ring
    rw [hdot'] at h1
    have hpos : (0 : ℤ) ≤ -dot n (dir ν) := by omega
    have h2 : (LU : ℤ) * (-dot n (dir ν)) ≤ t * (-dot n (dir ν)) :=
      mul_le_mul_of_nonneg_right htL hpos
    rw [abs_of_neg hsign']
    omega

end Nivat.ConeWindowBox

#print axioms Nivat.ConeWindowBox.dot_cone_point
#print axioms Nivat.ConeWindowBox.dot_tilt
#print axioms Nivat.ConeWindowBox.window_subset_seed_union_prev_lines
#print axioms Nivat.ConeWindowBox.boxSeed
#print axioms Nivat.ConeWindowBox.mem_boxSeed
#print axioms Nivat.ConeWindowBox.boxSeed_low
#print axioms Nivat.ConeWindowBox.boxSeed_high
#print axioms Nivat.ConeWindowBox.boxSeed_cap
#print axioms Nivat.ConeWindowBox.not_window_subset_of_box_seed
#print axioms Nivat.ConeWindowBox.window_hypotheses_satisfiable
#print axioms Nivat.ConeWindowBox.not_window_subset_of_enveloped_seed
#print axioms Nivat.ConeWindowBox.not_window_subset_of_enveloped_seed'
#print axioms Nivat.ConeWindowBox.width_le_of_translate_subset
#print axioms Nivat.ConeWindowBox.stretch
#print axioms Nivat.ConeWindowBox.mem_stretch
#print axioms Nivat.ConeWindowBox.finite_stretch
#print axioms Nivat.ConeWindowBox.nonempty_stretch
#print axioms Nivat.ConeWindowBox.dot_mk
#print axioms Nivat.ConeWindowBox.face_stretch_subsingleton
#print axioms Nivat.ConeWindowBox.E_stretch
#print axioms Nivat.ConeWindowBox.encard_face_stretch_right
#print axioms Nivat.ConeWindowBox.encard_face_stretch_left
#print axioms Nivat.ConeWindowBox.encard_face_stretch_top
#print axioms Nivat.ConeWindowBox.encard_face_stretch_bot
#print axioms Nivat.ConeWindowBox.enveloped_stretch_sq1
#print axioms Nivat.ConeWindowBox.posArea_stretch
#print axioms Nivat.ConeWindowBox.not_isLatticeConvexRegion_stretch
#print axioms Nivat.ConeWindowBox.not_width_le_of_enveloped
#print axioms Nivat.ConeWindowBox.encard_face_eq_of_latticeConvex
#print axioms Nivat.ConeWindowBox.exists_face_endpoints
#print axioms Nivat.ConeWindowBox.dot_sub_le_width
#print axioms Nivat.ConeWindowBox.edgeLen_le_of_enveloped
#print axioms Nivat.ConeWindowBox.edgeLen_mul_le_width_of_enveloped
