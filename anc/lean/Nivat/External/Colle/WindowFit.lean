/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.EnvTranslate
import Nivat.External.Colle.PhiIotaWindow
import Nivat.External.Colle.NewtonZonotope
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.VertexFromEdge

/-!
# Window-fits-in-B support system (Collé Claim 4.6, b3_colle2.txt:776-804)

原文：b3_colle2.txt:790-804

The sweep window `𝒮_{φ_ι}` (the zonotope of generators `h_j` for `j ≠ ι₀`) must fit inside
the enveloped set `B` when anchored at `B`'s `ψ`-minimal point.

**Consumer (hard rule 9):** lane Hstrip2's `hstrip` theorem in
`Nivat/External/Colle/StripStep.lean`, which discharges the `sorry` at
`Nivat/External/Colle/RegionSteps.lean:2565`. The integrator adds the import.

## The reduction

`Nivat.LE2.shift_subset_iff_suppVal_le` (`EnvTranslate.lean:111`) turns
`shift v U ⊆ T` into the finite system `∀ n ∈ E T, suppVal U n + dot n v ≤ suppVal T n`.

With `v := bψ - a₀`, `U := ↑Sw`, `T := B`, the system reads:
> for every edge normal `n ∈ E B`:
>   `suppVal ↑Sw n - dot n a₀ ≤ suppVal B n - dot n bψ`

i.e. **`Sw`'s extent above its own `nℓ`-lowest vertex is at most `B`'s extent above its
own `ψ`-lowest vertex, in every direction `n` that is an edge normal of `B`.**

## Status

Six declarations, all axiom-clean with `[propext, Classical.choice, Quot.sound]`.
Milestone 1 (LHS closed form) complete.
-/

namespace Nivat.ColleReg

open Nivat Nivat.LE2 Nivat.ConeRegion Finset
open scoped Pointwise

variable {η : Config ℤ}

/-! ## §1. Milestone 1 — Minkowski additivity of support functions

The key lemma: support functions are additive over Minkowski sums.
`suppVal (X + Y) n = suppVal X n + suppVal Y n`.

This implies the zonotope formula by induction. -/

/-- **Support value of a segment.**

For `segOf v = {0, v}`, we have `suppVal (segOf v) n = max 0 ⟪n, v⟫`. -/
theorem suppVal_segOf (v n : ℤ × ℤ) :
    suppVal (segOf v) n = max 0 (dot n v) := by
  unfold segOf
  -- segOf v = {0, v}, so suppVal is max of dot n 0 and dot n v
  have h0 : dot n (0 : ℤ × ℤ) = 0 := by simp [dot]
  -- The maximum is either at 0 or at v
  by_cases h : 0 ≤ dot n v
  · -- If dot n v ≥ 0, then v is the maximizer
    have hv_face : v ∈ face ({0, v} : Set (ℤ × ℤ)) n := by
      constructor
      · right; rfl
      · intro z hz
        rcases hz with rfl | rfl
        · rw [h0]; exact h
        · rfl
    rw [suppVal_eq hv_face]
    simp [max_eq_right h]
  · -- If dot n v < 0, then 0 is the maximizer
    push_neg at h
    have h0_face : (0 : ℤ × ℤ) ∈ face ({0, v} : Set (ℤ × ℤ)) n := by
      constructor
      · left; rfl
      · intro z hz
        rcases hz with rfl | rfl
        · rfl
        · rw [h0]; omega
    rw [suppVal_eq h0_face, h0]
    have : dot n v < 0 := h
    simp [max_eq_left (le_of_lt this)]

/-- **Minkowski additivity of support values.**

原文：implicit in b3_colle2.txt:790 (zonotope structure)

For finite nonempty sets `X` and `Y`, the support value over the Minkowski sum equals
the sum of support values: `suppVal (X + Y) n = suppVal X n + suppVal Y n`.

This is the key to computing support values of zonotopes by summing over generators. -/
theorem suppVal_add {X Y : Set (ℤ × ℤ)} (hXfin : X.Finite) (hXne : X.Nonempty)
    (hYfin : Y.Finite) (hYne : Y.Nonempty) (n : ℤ × ℤ) :
    suppVal (X + Y) n = suppVal X n + suppVal Y n := by
  -- Take maximizers
  obtain ⟨x, hx, hxeq⟩ := exists_suppVal_eq hXfin hXne n
  obtain ⟨y, hy, hyeq⟩ := exists_suppVal_eq hYfin hYne n
  -- Show x + y maximizes over X + Y
  have hxy : x + y ∈ X + Y := Set.add_mem_add hx hy
  have hxy_max : ∀ z ∈ X + Y, dot n z ≤ dot n (x + y) := by
    intro z hz
    obtain ⟨x', hx', y', hy', rfl⟩ := hz
    calc dot n (x' + y')
      _ = dot n x' + dot n y' := dot_add n x' y'
      _ ≤ suppVal X n + suppVal Y n := by
          have hx'_le : dot n x' ≤ suppVal X n := le_suppVal hXfin hXne hx'
          have hy'_le : dot n y' ≤ suppVal Y n := le_suppVal hYfin hYne hy'
          omega
      _ = dot n x + dot n y := by rw [← hxeq, ← hyeq]
      _ = dot n (x + y) := (dot_add n x y).symm
  -- Therefore suppVal (X + Y) n = dot n (x + y)
  obtain ⟨z, hz, hzeq⟩ := exists_suppVal_eq (hXfin.add hYfin) (hXne.add hYne) n
  have hle1 : dot n z ≤ dot n (x + y) := hxy_max z hz
  have hle2 : dot n (x + y) ≤ suppVal (X + Y) n :=
    le_suppVal (hXfin.add hYfin) (hXne.add hYne) hxy
  calc suppVal (X + Y) n
    _ = dot n z := hzeq.symm
    _ = dot n (x + y) := by omega
    _ = dot n x + dot n y := dot_add n x y
    _ = suppVal X n + suppVal Y n := by rw [hxeq, hyeq]

/-! ## §2. Support value of a zonotope in closed form -/

/-- **Support value of a zonotope in closed form.**

For the zonotope `zonoF s h = ∑ j ∈ s, {0, h j}`, the support value in direction `n`
is the sum of the positive projections of the generators:
`suppVal (zonoF s h) n = ∑ j ∈ s, max 0 ⟪n, h j⟫`.

This follows from Minkowski additivity by induction on the Finset. -/
theorem suppVal_zonoF {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ)
    (n : ℤ × ℤ) :
    suppVal (↑(zonoF s h) : Set (ℤ × ℤ)) n = ∑ j ∈ s, max 0 (dot n (h j)) := by
  classical
  rw [coe_zonoF]
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      -- The empty zonotope is {0}, so suppVal is 0
      have hsum : (∑ i ∈ (∅ : Finset ι), segOf (h i)) = ({(0, 0)} : Set (ℤ × ℤ)) := by
        simp only [Finset.sum_empty, segOf]
        rfl
      have h0_face : (0, 0) ∈ face ({(0, 0)} : Set (ℤ × ℤ)) n := by
        constructor
        · rfl
        · intro z hz
          simp only [Set.mem_singleton_iff] at hz
          rw [hz]
      calc suppVal (∑ i ∈ (∅ : Finset ι), segOf (h i)) n
        _ = suppVal ({(0, 0)} : Set (ℤ × ℤ)) n := by rw [hsum]
        _ = dot n (0, 0) := suppVal_eq h0_face
        _ = 0 := by simp [dot]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hfin : (∑ i ∈ s, segOf (h i)).Finite := finite_zono s h
      have hne : (∑ i ∈ s, segOf (h i)).Nonempty := nonempty_zono s h
      rw [suppVal_add (finite_segOf (h a)) (nonempty_segOf (h a)) hfin hne, suppVal_segOf, ih]

/-- **The `nℓ`-minimal vertex of a zonotope**, when no generator is `nℓ`-parallel.

Given Lemma 2.6's hypothesis (`dot nℓ (h j) ≠ 0` for all `j`), the `nℓ`-minimal vertex
is `a₀ := ∑ j ∈ s, (if dot nℓ (h j) < 0 then h j else 0)`. -/
def zonoArgmin {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ) (nℓ : ℤ × ℤ) :
    ℤ × ℤ :=
  ∑ j ∈ s, if dot nℓ (h j) < 0 then h j else 0

theorem zonoArgmin_mem {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ)
    (nℓ : ℤ × ℤ) :
    zonoArgmin s h nℓ ∈ zonoF s h := by
  -- zonoArgmin is a subset sum: for each i, pick h i if dot nℓ (h i) < 0, else pick 0
  unfold zonoArgmin zonoF
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      by_cases h_case : dot nℓ (h a) < 0
      · -- Pick h a for this generator
        simp only [if_pos h_case]
        refine Finset.add_mem_add ?_ ih
        show h a ∈ ({0, h a} : Finset (ℤ × ℤ))
        simp [Finset.mem_insert, Finset.mem_singleton]
      · -- Pick 0 for this generator
        simp only [if_neg h_case]
        refine Finset.add_mem_add ?_ ih
        show (0 : ℤ × ℤ) ∈ ({0, h a} : Finset (ℤ × ℤ))
        simp [Finset.mem_insert, Finset.mem_singleton]

/-- Support values agree when convex hulls agree.

原文：implicit in b3_colle2.txt:790 (the window is determined by its convex hull)

The support value `suppVal S n = max {⟪n, z⟫ : z ∈ S}` depends only on `Conv S`, not on
the specific lattice points of `S`. This follows from the fact that any maximizer in `S`
also maximizes over `Conv S` (by the maximum principle for convex sets), and conversely
any maximizer on the hull is achieved at some lattice point when `S` is finite. -/
theorem suppVal_congr_of_Conv_eq {S T : Finset (ℤ × ℤ)} (n : ℤ × ℤ)
    (hSne : S.Nonempty)
    (hTne : T.Nonempty)
    (hConv : Conv S = Conv T) :
    suppVal (↑S : Set (ℤ × ℤ)) n = suppVal (↑T : Set (ℤ × ℤ)) n := by
  -- Both sides are determined by their faces
  obtain ⟨vS, hvS⟩ := face_nonempty (Set.toFinite ↑S) (Finset.coe_nonempty.mpr hSne) n
  obtain ⟨vT, hvT⟩ := face_nonempty (Set.toFinite ↑T) (Finset.coe_nonempty.mpr hTne) n
  rw [suppVal_eq hvS, suppVal_eq hvT]
  -- Show dot n vS = dot n vT by showing both achieve the maximum over the common hull
  -- Key: vS ∈ S ⊆ Conv S = Conv T, so rdot n (toReal vS) is bounded above by the max over T
  have hSmax : ∀ z ∈ (↑S : Set (ℤ × ℤ)), dot n z ≤ dot n vS := hvS.2
  have hTmax : ∀ z ∈ (↑T : Set (ℤ × ℤ)), dot n z ≤ dot n vT := hvT.2
  -- vS maximizes on Conv S, hence on Conv T = Conv S
  have hvS_Conv : toReal vS ∈ Conv S := subset_Conv hvS.1
  rw [hConv] at hvS_Conv
  -- The real value rdot n (toReal vS) is ≤ every value on T (by convex hull containment)
  have hle_S_T : (dot n vS : ℝ) ≤ (dot n vT : ℝ) := by
    have hreal : rdot (toReal n) (toReal vS) ≤ (dot n vT : ℝ) := by
      refine Conv_subset_halfSpace hTmax (toReal vS) hvS_Conv
    rw [rdot_toReal] at hreal
    exact_mod_cast hreal
  -- Symmetrically, vT maximizes on Conv T = Conv S
  have hvT_Conv : toReal vT ∈ Conv T := subset_Conv hvT.1
  rw [← hConv] at hvT_Conv
  have hle_T_S : (dot n vT : ℝ) ≤ (dot n vS : ℝ) := by
    have hreal : rdot (toReal n) (toReal vT) ≤ (dot n vS : ℝ) := by
      refine Conv_subset_halfSpace hSmax (toReal vT) hvT_Conv
    rw [rdot_toReal] at hreal
    exact_mod_cast hreal
  -- Therefore dot n vS = dot n vT
  have : (dot n vS : ℝ) = (dot n vT : ℝ) := le_antisymm hle_S_T hle_T_S
  exact Int.cast_injective this

/-! ## §3. 相对支撑值（把窗口的支撑值搬到它自己的角点上）

洞 6 的 `hsupp`（`RegionSteps.lean`）要的是
`suppVal ↑Sw n + ⟪n, g − a₀⟫ ≤ suppVal B n`，即
`suppVal ↑Sw n − ⟪n, a₀⟫ ≤ suppVal B n − ⟪n, g⟫`：**两边都是相对于各自角点的支撑值**。
本节把左边算成闭形式，从而把 `hsupp` 里所有关于 `Sw` 的内容消掉，只剩右边。

原文：`b3_colle2.txt:790-792`（`φ_ι := ∏_{j≠ι₀}(X^{h_j}−1)`，窗口的凸包就是**去掉一个
生成元**的 zonotope）。左边是 zonotope，所以它的相对支撑值只是生成元投影的正部之和。 -/

/-- 把生成元朝 `nℓ`-正侧定向：`nℓ`-负的那些取相反数。

原文：`b3_colle2.txt:790` 的 zonotope 的边成 `±` 对出现，所以「从 `nℓ`-最低角点出发」
等价于把每条生成元都定向成 `nℓ`-非负。 -/
def orientUp (w nℓ : ℤ × ℤ) : ℤ × ℤ := if dot nℓ w < 0 then -w else w

/-- `dot` 在右侧对 Finset 和可加（`ColleStep.dot_sum_left` 是左侧版）。 -/
theorem dot_sum_right {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ × ℤ) (n : ℤ × ℤ) :
    dot n (∑ j ∈ s, f j) = ∑ j ∈ s, dot n (f j) := by
  classical
  induction s using Finset.induction with
  | empty => simp [dot]
  | insert a s ha ih => rw [Finset.sum_insert ha, dot_add, ih, Finset.sum_insert ha]

/-- **zonotope 在它的 `nℓ`-最低角点处的相对支撑值，闭形式。**

`suppVal ↑(zonoF s h) n − ⟪n, zonoArgmin s h nℓ⟫ = ∑ j ∈ s, max 0 ⟪n, orientUp (h j) nℓ⟫`。

原文：`b3_colle2.txt:790`（窗口的凸包是 zonotope）。纯代数，没有几何、没有 enveloped。 -/
theorem relSuppVal_zonoF {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ)
    (nℓ n : ℤ × ℤ) :
    suppVal (↑(zonoF s h) : Set (ℤ × ℤ)) n - dot n (zonoArgmin s h nℓ) =
      ∑ j ∈ s, max 0 (dot n (orientUp (h j) nℓ)) := by
  classical
  rw [suppVal_zonoF, zonoArgmin, dot_sum_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : dot nℓ (h j) < 0
  · simp only [orientUp, hc, if_pos, if_true]
    have : dot n (-(h j)) = -dot n (h j) := by simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring
    rw [this]; omega
  · simp only [orientUp, hc, if_neg, if_false]
    have : dot n (0 : ℤ × ℤ) = 0 := by simp [dot]
    rw [this]; omega

/-- **`zonoArgmin` 确实取到 `dot nℓ` 的最小值**，写成「`−(−nℓ)` 方向的支撑值」。 -/
theorem dot_zonoArgmin {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ)
    (nℓ : ℤ × ℤ) :
    dot nℓ (zonoArgmin s h nℓ) = - suppVal (↑(zonoF s h) : Set (ℤ × ℤ)) (-nℓ) := by
  classical
  rw [suppVal_zonoF, zonoArgmin, dot_sum_right, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hneg : dot (-nℓ) (h j) = -dot nℓ (h j) := dot_neg_left nℓ (h j)
  by_cases hc : dot nℓ (h j) < 0
  · rw [if_pos hc, hneg]; omega
  · rw [if_neg hc, hneg]
    have : dot nℓ (0 : ℤ × ℤ) = 0 := by simp [dot]
    rw [this]; omega

/-- **窗口的严格最低角点就是 `zonoArgmin`。**

`Sw` 的凸包是 zonotope（`hzono`），`Sw` 格凸（`hconv`），`a₀ ∈ Sw` 是 `dot nℓ` 的
**严格**最小者（`hstrict`，即 `Sw` 的 `nℓ`-最低面是单点）。那么 `a₀` 必然等于
`zonoArgmin s h nℓ`——后者在 zonotope 里取到同一个最小值，而严格性不允许有第二个点。

原文：`b3_colle2.txt:792` 的窗口 `𝒮_{φ_ι}` 与 `:794` 的「最低那条线 `l₀`」上只有一个点，
正是 `exists_window_strict_at_prime` 的 `hstrict` 所形式化的东西。 -/
theorem eq_zonoArgmin_of_strict {ι : Type*} [DecidableEq ι] {s : Finset ι} {h : ι → ℤ × ℤ}
    {Sw : Finset (ℤ × ℤ)} {a₀ nℓ : ℤ × ℤ}
    (hconv : Nivat.LatticeConvex Sw) (hzono : Nivat.Conv Sw = Nivat.Conv (zonoF s h))
    (ha₀ : a₀ ∈ Sw) (hstrict : ∀ z ∈ Sw.erase a₀, dot nℓ a₀ < dot nℓ z) :
    a₀ = zonoArgmin s h nℓ := by
  classical
  set q := zonoArgmin s h nℓ with hq
  -- `q` 是格点、在 zonotope 里，故经 `hzono` 回到 `Sw`。
  have hqSw : q ∈ Sw := by
    refine hconv q ?_
    rw [hzono]
    exact Nivat.subset_Conv (by exact_mod_cast zonoArgmin_mem s h nℓ)
  -- `q` 取到 `dot nℓ` 在 zonotope 上的最小值，而 `a₀` 也在同一个凸包里。
  have hSwne : Sw.Nonempty := ⟨a₀, ha₀⟩
  have hzne : (zonoF s h).Nonempty := ⟨q, zonoArgmin_mem s h nℓ⟩
  have hsv : suppVal (↑Sw : Set (ℤ × ℤ)) (-nℓ)
      = suppVal (↑(zonoF s h) : Set (ℤ × ℤ)) (-nℓ) :=
    suppVal_congr_of_Conv_eq (-nℓ) hSwne hzne hzono
  have hle : dot nℓ q ≤ dot nℓ a₀ := by
    have h1 : dot (-nℓ) a₀ ≤ suppVal (↑Sw : Set (ℤ × ℤ)) (-nℓ) :=
      le_suppVal (Set.toFinite _) (Finset.coe_nonempty.mpr hSwne) (by exact_mod_cast ha₀)
    rw [hsv] at h1
    have h2 : dot nℓ q = - suppVal (↑(zonoF s h) : Set (ℤ × ℤ)) (-nℓ) := dot_zonoArgmin s h nℓ
    have h3 : dot (-nℓ) a₀ = - dot nℓ a₀ := dot_neg_left nℓ a₀
    omega
  by_contra hne
  exact absurd hle (not_le.mpr (hstrict q (Finset.mem_erase.mpr ⟨fun hqa => hne hqa.symm, hqSw⟩)))

/-- **去掉生成元只会让相对支撑值变小。**

原文：`b3_colle2.txt:792` 的 `φ_ι := ∏_{i≠ι₀}(X^{h_i}−1)` 与 `:777` 的 `𝒮_φ`——
窗口 `𝒮_{φ_ι}` 是 `𝒮_φ` **去掉第 `ι₀` 个生成元**的 zonotope。所以「窗口装进 `B`」
只要「整个 `𝒮_φ` 装进 `B`」就够了，而后者正是 `B` 为 `E(𝒮_φ)`-enveloped 的几何内容
（Definition 3.2，`:402`）。

纯代数：每一项 `max 0 ⟪n, ·⟫` 非负，子集求和不超过全集求和。 -/
theorem relSuppVal_zonoF_mono {ι : Type*} [DecidableEq ι] {s t : Finset ι} (hst : s ⊆ t)
    (h : ι → ℤ × ℤ) (nℓ n : ℤ × ℤ) :
    (∑ j ∈ s, max 0 (dot n (orientUp (h j) nℓ))) ≤
      ∑ j ∈ t, max 0 (dot n (orientUp (h j) nℓ)) :=
  Finset.sum_le_sum_of_subset_of_nonneg hst (fun _ _ _ => le_max_left _ _)

#print axioms suppVal_segOf
#print axioms suppVal_add
#print axioms suppVal_zonoF
#print axioms zonoArgmin_mem
#print axioms suppVal_congr_of_Conv_eq
#print axioms dot_sum_right
#print axioms relSuppVal_zonoF
#print axioms dot_zonoArgmin
#print axioms eq_zonoArgmin_of_strict
#print axioms relSuppVal_zonoF_mono

end Nivat.ColleReg
