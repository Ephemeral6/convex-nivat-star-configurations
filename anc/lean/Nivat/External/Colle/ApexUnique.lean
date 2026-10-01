/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.NoEdgePlacement

set_option autoImplicit false

/-!
# Strict extreme vertex from "no edge parallel to `ℓ`"

原文：b3_colle2.txt:792
> Lemma 2.6 implies that `𝒮_{φ_ι}` does not have any edge parallel to `-ℓ` or `ℓ`.

Lane Wlines needs the **argmax** form

    hstrict : ∀ z ∈ S.erase a, dot m z < dot m a

to feed `hwinL` (`SweepLines.lean:177`).

⚠ **本文件不是新数学，是一次符号翻面 + 一条判据的兑现。** `PROTOCOL.md` §20 扫描先做了：
`Nivat.LE2.exists_unique_argmin_strict`（`NoEdgePlacement.lean:119`，已落地、公理干净）
已经给出**同一条引理的 argmin 形式**。取 `n := -m` 即得 argmax 形式，见 §2。
所以 §2 的 `exists_strict_argmax_of_no_edge_parallel` 只是适配器，**不要把它当独立结果引用**。

§1 兑现的是**硬规矩 7 的对应关系本身**：`hno` 写成 `∀ n ∈ E 𝒮, dot n vl ≠ 0`，
而原文说的是「没有平行于 `ℓ` 的边」。这两句相等不是显然的，此前只写在 docstring 的散文里
（`NoEdgePlacement.lean:47`、`:114`）。`face_parallel_iff` 把它变成内核事实：
`n` 处的边（face 上任意两点之差）平行于 `vl` ⟺ `dot n vl = 0`。

## Main results

* `Nivat.ApexUnique.face_parallel_iff` — 「`n` 处的边平行于 `vl`」⟺ `dot n vl = 0`。
* `Nivat.ApexUnique.exists_strict_argmax_of_no_edge_parallel` — 目标，argmax 形式。
-/

namespace Nivat.ApexUnique

open Nivat Nivat.LE2

/-! ## §1  「边平行于 `ℓ`」⟺ 法向量与 `ℓ` 正交

这一节存在的唯一理由是硬规矩 7：`hno` 的写法 `∀ n ∈ E 𝒮, dot n vl ≠ 0` 必须可以逐词对上
原文 `:792` 的「没有平行于 `ℓ` 的边」。 -/

/-- 与 `Nivat.LE2.det_eq_zero_of_dot_eq_zero`（`LatticeEdges.lean:110`）互补的一半：
`d ≠ 0`、`d ⊥ n`、`det d vl = 0` ⟹ `vl ⊥ n`。

几何读法：`d` 与 `vl` 共线（`det = 0`）且 `d` 非零，所以 `vl` 落在 `d` 张成的直线上；
`n` 已经与 `d` 正交，于是也与 `vl` 正交。 -/
theorem dot_eq_zero_of_det_eq_zero {n vl d : ℤ × ℤ} (hd : d ≠ 0)
    (hdn : dot n d = 0) (hdet : det d vl = 0) : dot n vl = 0 := by
  have h1 : dot n vl * d.1 = 0 := by
    simp only [dot, det] at *
    linear_combination vl.1 * hdn + n.2 * hdet
  have h2 : dot n vl * d.2 = 0 := by
    simp only [dot, det] at *
    linear_combination vl.2 * hdn - n.1 * hdet
  by_contra h
  refine hd ?_
  have e1 : d.1 = 0 := (mul_eq_zero.mp h1).resolve_left h
  have e2 : d.2 = 0 := (mul_eq_zero.mp h2).resolve_left h
  exact Prod.ext e1 e2

/-- **原文 `:792` 的「边平行于 `ℓ`」就是 `dot n vl = 0`。**

原文：b3_colle2.txt:792 — *"Lemma 2.6 implies that `𝒮_{φ_ι}` does not have any edge parallel
to `-ℓ` or `ℓ`."*

**量词对应：**
- `S : Set (ℤ × ℤ)` ↔ `𝒮_{φ_ι}`（生成集）
- `n : ℤ × ℤ` ↔ 一条边的外法向量；`hnt : (face S n).Nontrivial` ↔ 「`n` 处确实是一条**边**
  而不是单个顶点」，即 `n ∈ E S` 的第二个合取（`mem_E_iff`，`LatticeEdges.lean:219`）
- `vl : ℤ × ℤ` ↔ `v⃗_ℓ`，直线 `ℓ` 的方向向量
- 左端 `∀ z w ∈ face S n, det (w - z) vl = 0` ↔ 「这条边平行于 `ℓ`」：边上任意两点之差与
  `v⃗_ℓ` 共线。`-ℓ` 与 `ℓ` 在这个写法下是同一句（`det (w-z) (-vl) = -det (w-z) vl`），
  所以原文的「`-ℓ` or `ℓ`」不需要分两条
- 右端 `dot n vl = 0` ↔ 消费者侧的写法（`hno`，`generatingSet_no_edge_parallel`
  `Claim36.lean:749` 正是产出这一形式）

`hn : n ≠ 0` 是必需的：`n = 0` 时每个点都在 face 上、左端恒真，而右端 `dot 0 vl = 0` 也恒真，
两端仍相等，但 `dot_eq_zero_of_det_eq_zero` 的反方向走不过去。链上由 `Prim n` 免费给出
（`Prim.ne_zero`，`LatticeEdges.lean:101`）。 -/
theorem face_parallel_iff {S : Set (ℤ × ℤ)} {n vl : ℤ × ℤ} (hn : n ≠ 0)
    (hnt : (face S n).Nontrivial) :
    (∀ z ∈ face S n, ∀ w ∈ face S n, det (w - z) vl = 0) ↔ dot n vl = 0 := by
  constructor
  · intro hpar
    obtain ⟨z, hz, w, hw, hzw⟩ := hnt
    have hd : w - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzw)
    exact dot_eq_zero_of_det_eq_zero hd (dot_sub_eq_zero_of_mem_face hz hw) (hpar z hz w hw)
  · intro hperp z hz w hw
    exact det_eq_zero_of_dot_eq_zero hn (dot_sub_eq_zero_of_mem_face hz hw) hperp

/-! ## §2  目标：严格 argmax

⚠ **适配器，不是新证明。** 内容全部来自 `Nivat.LE2.exists_unique_argmin_strict`
（`NoEdgePlacement.lean:119`）。 -/

/-- **严格极值顶点，argmax 形式**（lane Wlines 的 `hstrict`）。

原文：b3_colle2.txt:792 — 同 `face_parallel_iff`，`hno` 即该行的「没有平行于 `ℓ` 的边」，
经 §1 逐词对上。

**量词对应：**
- `S : Finset (ℤ × ℤ)` ↔ `𝒮_{φ_ι}`
- `hne : S.Nonempty` ↔ 生成集非空（原文默认；极值点的存在性需要它）
- `m : ℤ × ℤ` ↔ 横截法向量，原文 `:792` 里「平行于 `ℓ` 的诸直线」的公共法向
- `vl : ℤ × ℤ` ↔ `v⃗_ℓ`
- `hperp : dot m vl = 0` ↔ `m ⊥ ℓ`
- `hno : ∀ n ∈ E ↑S, dot n vl ≠ 0` ↔ 「`𝒮_{φ_ι}` 没有平行于 `-ℓ` 或 `ℓ` 的边」
- 结论 `∃ a ∈ S, ∀ z ∈ S.erase a, dot m z < dot m a` ↔ `dot m` 的最大值被**唯一**且**严格**
  地取到（没有平行于 `ℓ` 的边 ⟹ `m` 方向的支撑面是一个点，不是一条边）

**`hprim : Primitive m` 是承重的，`Primitive vl` 不是。** `hno` 只对 `E ↑S` 的元素说话，
而 `E` 按定义只含本原法向（`IsEdge`，`LatticeEdges.lean`），所以 `m` 非本原时 `hno` 对 `m`
一个字都没说，结论推不出来。反过来 `vl` 的本原性在这条路径上完全没用到——
它只在「同一 `dot m` 层上的两点相差 `vl` 的整数倍」那种写法里才需要（那句话要 `m`、`vl`
**两个**都本原），而本证明走的是 face 非平凡 ⟹ `m ∈ E ↑S` 的矛盾，不经过那一步。 -/
theorem exists_strict_argmax_of_no_edge_parallel
    {S : Finset (ℤ × ℤ)} (hne : S.Nonempty) {m vl : ℤ × ℤ} (hprim : Primitive m)
    (hperp : dot m vl = 0)
    (hno : ∀ n ∈ E (↑S : Set (ℤ × ℤ)), dot n vl ≠ 0) :
    ∃ a ∈ S, ∀ z ∈ S.erase a, dot m z < dot m a := by
  have hm : Prim m := prim_iff_primitive.mpr hprim
  obtain ⟨a, ha, hmin⟩ :=
    exists_unique_argmin_strict (ℓ := vl) (n := -m) hm.neg hne hno
      (by rw [dot_neg_left, hperp]; ring)
  refine ⟨a, ha, fun z hz => ?_⟩
  have h := hmin z hz
  rw [dot_neg_left, dot_neg_left] at h
  linarith

/-! ## §3  `hapex` 比 `hstrict` **严格地强**：引理 2.6 ＋ 幺模性推不出它

原文：b3_colle2.txt:794-798（Figure 10：把 `𝒮_{φ_ι}` 平移到极值顶点落在 `w` 上，
其余点落进区域内）。

Emink 的锥版 `hwinL` 需要的是

    hapex : ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u'

即「`𝒮_{φ_ι} - a` 整个落在 `vl`、`u'` 张成的**锥**里」。在 `det u' vl = ±1` 下
`(vl, u')` 是 ℤ² 的基，所以 `hapex` 等价于「每个 `z - a` 的两个基坐标都 `≥ 0`」。

**结论：(c)，按所述为假。** 见证 `Sap`，下面把被否命题的**每一条**前提都在内核里验过
（`PROTOCOL.md` §7；`EnvTranslate.lean:124-132` 的撤回就是漏验前提的反面教材）。

**死因不是技术性的。** `hstrict` 只约束 `u'` 方向的坐标 `t`（`dot m u' = -1`，所以
`dot m (z-a) = -t < 0` ⟺ `t ≥ 1`）；`vl` 方向的坐标 `s` 它**一个字都没说**，因为
`dot m vl = 0` —— `m` 对 `vl` 方向是瞎的。而引理 2.6 给出的全部信息就是
「`m` 方向的支撑面是单点」。所以任何只用引理 2.6 ＋ 幺模性的推导都碰不到 `s` 的符号。
`Sap` 就是把 `s` 的符号拨到负的：三个点的 `u'`-坐标（纵坐标）两两不同（0/1/2，
于是没有平行于 `ℓ` 的边，引理 2.6 的结论成立），但纵坐标最小的那个点的横坐标**不是**最小的。

⚠ **`hapex` 不是空的，别按「无意义」处理。** §3.2 的 `Spos` 满足全部同样的前提**并且**
满足 `hapex`。所以缺的是一个**生产者**，不是一条该删的 `Prop`：原文必须在 `:794-798`
之外的某处给出 `a` 的位置信息，光靠 `:792` 不够。 -/

/-- 反例的横向方向 `v⃗_ℓ`。 -/
def vlap : ℤ × ℤ := (1, 0)

/-- 反例的第二条射线方向 `v⃗_{ℓ_{ι-1}}`。 -/
def u'ap : ℤ × ℤ := (0, 1)

/-- 反例的横截法向：`dot map vlap = 0`、`dot map u'ap = -1`，与 `ConeRegion` 的层级约定一致。 -/
def map : ℤ × ℤ := (0, -1)

/-! ### §3.1  反例 `Sap = {(0,0), (-1,1), (-1,2)}` -/

/-- 反例见证：一个幺模三角形，纵坐标 0/1/2 两两不同。 -/
def Sap : Finset (ℤ × ℤ) := {(0, 0), (-1, 1), (-1, 2)}

theorem mem_Sap {z : ℤ × ℤ} : z ∈ Sap ↔ z = (0, 0) ∨ z = (-1, 1) ∨ z = (-1, 2) := by
  simp [Sap]

/-- `Sap` 的三个点纵坐标两两不同，所以纵坐标决定点。 -/
theorem snd_inj_Sap {z w : ℤ × ℤ} (hz : z ∈ Sap) (hw : w ∈ Sap) (h : z.2 = w.2) : z = w := by
  rw [mem_Sap] at hz hw
  rcases hz with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> simp_all

/-- `Sap` 的三角形，写成三个半平面的交。 -/
def triAp : Set (ℝ × ℝ) := {q : ℝ × ℝ | -1 ≤ q.1 ∧ 0 ≤ q.1 + q.2 ∧ 2 * q.1 + q.2 ≤ 0}

theorem convex_triAp : Convex ℝ triAp := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hu1, hu2, hu3⟩ := hu
  obtain ⟨hv1, hv2, hv3⟩ := hv
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    nlinarith

theorem latticeConvex_Sap : LatticeConvex Sap := by
  intro z hz
  have hsub : Conv Sap ⊆ triAp := by
    refine convexHull_min ?_ convex_triAp
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe, mem_Sap] at hw
    rcases hw with rfl | rfl | rfl <;>
      exact ⟨by norm_num [toReal], by norm_num [toReal], by norm_num [toReal]⟩
  obtain ⟨h1, h2, h3⟩ := hsub hz
  simp only [toReal] at h1 h2 h3
  have g1 : (-1 : ℤ) ≤ z.1 := by exact_mod_cast h1
  have g2 : (0 : ℤ) ≤ z.1 + z.2 := by exact_mod_cast h2
  have g3 : 2 * z.1 + z.2 ≤ 0 := by exact_mod_cast h3
  obtain ⟨x, y⟩ := z
  rw [mem_Sap]
  simp only [Prod.mk.injEq]
  simp only at g1 g2 g3
  omega

theorem posArea_Sap : PosArea (↑Sap : Set (ℤ × ℤ)) := by
  refine ⟨(0, 0), by rw [Finset.mem_coe, mem_Sap]; tauto,
    (-1, 1), by rw [Finset.mem_coe, mem_Sap]; tauto,
    (-1, 2), by rw [Finset.mem_coe, mem_Sap]; tauto, ?_⟩
  decide

/-- **引理 2.6 的结论在 `Sap` 上成立**：没有平行于 `v⃗_ℓ` 的边。

证明就是「三个纵坐标两两不同」：与 `vlap = (1,0)` 正交的本原法向只有 `(0,±1)`，
它们的支撑面各是一个点。 -/
theorem no_edge_parallel_Sap : ∀ n ∈ E (↑Sap : Set (ℤ × ℤ)), dot n vlap ≠ 0 := by
  intro n hn hdot
  obtain ⟨hprim, hnt⟩ := mem_E_iff.mp hn
  have hn1 : n.1 = 0 := by simpa [dot, vlap] using hdot
  have hn2 : n.2 ≠ 0 := by
    intro h
    exact hprim.ne_zero (Prod.ext hn1 h)
  obtain ⟨z, hz, w, hw, hzw⟩ := hnt
  have h0 : dot n (w - z) = 0 := dot_sub_eq_zero_of_mem_face hz hw
  have hy : z.2 = w.2 := by
    simp only [dot, hn1, Prod.fst_sub, Prod.snd_sub, zero_mul, zero_add] at h0
    have : n.2 * (w.2 - z.2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hn2
    · omega
  exact hzw (snd_inj_Sap (Finset.mem_coe.mp hz.1) (Finset.mem_coe.mp hw.1) hy)

/-- **`hstrict` 在 `Sap` 上成立** —— 用 §2 的适配器，不重证。 -/
theorem exists_strict_argmax_Sap :
    ∃ a ∈ Sap, ∀ z ∈ Sap.erase a, dot map z < dot map a :=
  exists_strict_argmax_of_no_edge_parallel ⟨(0, 0), by rw [mem_Sap]; tauto⟩
    (prim_iff_primitive.mp (by decide)) (by decide) no_edge_parallel_Sap

/-- **`hapex` 不是引理 2.6 ＋ 幺模性的推论。**

原文：b3_colle2.txt:792（引理 2.6：没有平行于 `±ℓ` 的边）＋ `:794-798`（Figure 10 的平移）。

见证 `Sap = {(0,0), (-1,1), (-1,2)}`、`vl = (1,0)`、`u' = (0,1)`、`m = (0,-1)`。
被否命题的前提**逐条在内核里验过**：非空、`LatticeConvex`、`PosArea`、三个方向都本原、
`det u' vl = -1`（幺模）、`dot m vl = 0`、`dot m u' = -1`、引理 2.6 的结论 `hno`，
**外加 `hstrict` 本身成立**（倒数第二个合取）——所以这不是「`hstrict` 也不成立」的退化见证，
恰恰是 `hstrict` 真而 `hapex` 假的分离见证。

结论里的 `¬ ∃ a ∈ S` 是对**所有**候选顶点说的，不只是 `m`-argmax：`Sap` 的三个点里
没有任何一个在 `(vl, u')` 基下逐坐标不超过其余两点。 -/
theorem not_exists_apex_of_no_edge_parallel :
    ∃ (S : Finset (ℤ × ℤ)) (vl u' m : ℤ × ℤ),
      S.Nonempty ∧ LatticeConvex S ∧ PosArea (↑S : Set (ℤ × ℤ)) ∧
      Primitive vl ∧ Primitive u' ∧ Primitive m ∧
      det u' vl = -1 ∧
      dot m vl = 0 ∧ dot m u' = -1 ∧
      (∀ n ∈ E (↑S : Set (ℤ × ℤ)), dot n vl ≠ 0) ∧
      (∃ a ∈ S, ∀ z ∈ S.erase a, dot m z < dot m a) ∧
      ¬ ∃ a ∈ S, ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u' := by
  refine ⟨Sap, vlap, u'ap, map, ⟨(0, 0), by rw [mem_Sap]; tauto⟩, latticeConvex_Sap,
    posArea_Sap, prim_iff_primitive.mp (by decide), prim_iff_primitive.mp (by decide),
    prim_iff_primitive.mp (by decide), by decide, by decide, by decide,
    no_edge_parallel_Sap, exists_strict_argmax_Sap, ?_⟩
  rintro ⟨a, ha, hall⟩
  rw [mem_Sap] at ha
  rcases ha with rfl | rfl | rfl
  · obtain ⟨s, t, heq⟩ := hall (-1, 1) (by rw [Finset.mem_erase, mem_Sap]; exact ⟨by decide, by tauto⟩)
    have h1 : (-1 : ℤ) = (s : ℤ) := by
      simpa [vlap, u'ap, Prod.ext_iff] using congrArg Prod.fst heq
    omega
  · obtain ⟨s, t, heq⟩ := hall (0, 0) (by rw [Finset.mem_erase, mem_Sap]; exact ⟨by decide, by tauto⟩)
    have h2 : (-1 : ℤ) = (t : ℤ) := by
      simpa [vlap, u'ap, Prod.ext_iff] using congrArg Prod.snd heq
    omega
  · obtain ⟨s, t, heq⟩ := hall (0, 0) (by rw [Finset.mem_erase, mem_Sap]; exact ⟨by decide, by tauto⟩)
    have h2 : (-2 : ℤ) = (t : ℤ) := by
      simpa [vlap, u'ap, Prod.ext_iff] using congrArg Prod.snd heq
    omega

/-! ### §3.2  `hapex` 是可满足的：`Spos = {(0,0), (1,1), (1,2), (2,1)}`

这一节存在的理由是把 (c) 与「`hapex` 根本没意义」区分开。`Spos` 满足 §3.1 里
**同一组**前提，并且有顶点 `(0,0)` 使 `hapex` 成立。所以 `hapex` 欠的是一个**生产者**。 -/

/-- `hapex` 的正面见证。 -/
def Spos : Finset (ℤ × ℤ) := {(0, 0), (1, 1), (1, 2), (2, 1)}

theorem mem_Spos {z : ℤ × ℤ} :
    z ∈ Spos ↔ z = (0, 0) ∨ z = (1, 1) ∨ z = (1, 2) ∨ z = (2, 1) := by
  simp [Spos]

/-- `Spos` 的三角形 `(0,0)`–`(1,2)`–`(2,1)`，写成三个半平面的交。 -/
def triPos : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 ≤ 2 * q.1 - q.2 ∧ q.1 - 2 * q.2 ≤ 0 ∧ q.1 + q.2 ≤ 3}

theorem convex_triPos : Convex ℝ triPos := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hu1, hu2, hu3⟩ := hu
  obtain ⟨hv1, hv2, hv3⟩ := hv
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    nlinarith

theorem latticeConvex_Spos : LatticeConvex Spos := by
  intro z hz
  have hsub : Conv Spos ⊆ triPos := by
    refine convexHull_min ?_ convex_triPos
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe, mem_Spos] at hw
    rcases hw with rfl | rfl | rfl | rfl <;>
      exact ⟨by norm_num [toReal], by norm_num [toReal], by norm_num [toReal]⟩
  obtain ⟨h1, h2, h3⟩ := hsub hz
  simp only [toReal] at h1 h2 h3
  have g1 : (0 : ℤ) ≤ 2 * z.1 - z.2 := by exact_mod_cast h1
  have g2 : z.1 - 2 * z.2 ≤ 0 := by exact_mod_cast h2
  have g3 : z.1 + z.2 ≤ 3 := by exact_mod_cast h3
  obtain ⟨x, y⟩ := z
  rw [mem_Spos]
  simp only [Prod.mk.injEq]
  simp only at g1 g2 g3
  omega

/-- `Spos` 的纵坐标极值面各只有一个点：最高的是 `(1,2)`，最低的是 `(0,0)`。
所以与 `vlap` 正交的两个本原法向 `(0,±1)` 的支撑面都是单点。 -/
theorem eq_of_mem_face_Spos {n : ℤ × ℤ} (hn1 : n.1 = 0) (hcase : n.2 = 1 ∨ n.2 = -1)
    {z w : ℤ × ℤ} (hz : z ∈ face (↑Spos : Set (ℤ × ℤ)) n)
    (hw : w ∈ face (↑Spos : Set (ℤ × ℤ)) n) : z = w := by
  have hzS : z ∈ Spos := Finset.mem_coe.mp hz.1
  have hwS : w ∈ Spos := Finset.mem_coe.mp hw.1
  rcases hcase with h | h
  · have hz2 := hz.2 (1, 2) (by rw [Finset.mem_coe, mem_Spos]; tauto)
    have hw2 := hw.2 (1, 2) (by rw [Finset.mem_coe, mem_Spos]; tauto)
    simp only [dot, hn1, h, zero_mul, zero_add, one_mul] at hz2 hw2
    rw [mem_Spos] at hzS hwS
    rcases hzS with rfl | rfl | rfl | rfl <;> rcases hwS with rfl | rfl | rfl | rfl <;>
      simp_all
  · have hz2 := hz.2 (0, 0) (by rw [Finset.mem_coe, mem_Spos]; tauto)
    have hw2 := hw.2 (0, 0) (by rw [Finset.mem_coe, mem_Spos]; tauto)
    simp only [dot, hn1, h, zero_mul, zero_add, neg_mul, one_mul, neg_zero] at hz2 hw2
    rw [mem_Spos] at hzS hwS
    rcases hzS with rfl | rfl | rfl | rfl <;> rcases hwS with rfl | rfl | rfl | rfl <;>
      simp_all

/-- **`hapex` 在 `Spos` 上成立**，且 `Spos` 满足 §3.1 的同一组前提。 -/
theorem exists_apex_Spos :
    Spos.Nonempty ∧ LatticeConvex Spos ∧ PosArea (↑Spos : Set (ℤ × ℤ)) ∧
      (∀ n ∈ E (↑Spos : Set (ℤ × ℤ)), dot n vlap ≠ 0) ∧
      ∃ a ∈ Spos, ∀ z ∈ Spos.erase a,
        ∃ s t : ℕ, z - a = (s : ℤ) • vlap + (t : ℤ) • u'ap := by
  refine ⟨⟨(0, 0), by rw [mem_Spos]; tauto⟩, latticeConvex_Spos, ?_, ?_, ?_⟩
  · exact ⟨(0, 0), by rw [Finset.mem_coe, mem_Spos]; tauto,
      (1, 1), by rw [Finset.mem_coe, mem_Spos]; tauto,
      (1, 2), by rw [Finset.mem_coe, mem_Spos]; tauto, by decide⟩
  · intro n hn hdot
    obtain ⟨hprim, hnt⟩ := mem_E_iff.mp hn
    have hn1 : n.1 = 0 := by simpa [dot, vlap] using hdot
    have hgcd : n.2.natAbs = 1 := by
      have h := hprim
      simp only [Prim, hn1, Int.gcd_zero_left] at h
      exact h
    have hcase : n.2 = 1 ∨ n.2 = -1 := by omega
    obtain ⟨z, hz, w, hw, hzw⟩ := hnt
    exact hzw (eq_of_mem_face_Spos hn1 hcase hz hw)
  · refine ⟨(0, 0), by rw [mem_Spos]; tauto, ?_⟩
    intro z hz
    rw [Finset.mem_erase, mem_Spos] at hz
    rcases hz.2 with rfl | rfl | rfl | rfl
    · exact absurd rfl hz.1
    · exact ⟨1, 1, by decide⟩
    · exact ⟨1, 2, by decide⟩
    · exact ⟨2, 1, by decide⟩

/-! ## §4  `hapex` 的**存在量词版本恒真**：任何有限种子都有顶点与幺模基使它成立

派工要的是

    not_hapex_of_hexagon : ∃ S, LatticeConvex S ∧ … ∧
      ∀ a ∈ S, ∀ vl u', det u' vl = ±1 → ¬ hapex

**这条按所述为假，而且对每一个 `S` 都为假**，所以不存在可用的见证 `S`——六边形也不行。
下面 §4.1 的 `exists_unimodular_apex` 是内核证明：**任何非空有限 `S`** 都有 `a ∈ S`
与幺模对 `(vl, u')` 使 `hapex` 成立。连 `LatticeConvex` 都不需要。

**几何原因（一句话）**：`hapex` 说的是「`S - a` 落在 `(vl,u')` 张成的锥里」。幺模锥
**不是直角锥**——`vl = (1,0)`、`u' = (-K, 1)` 对**任意** `K` 都满足 `det u' vl = -1`，
张角随 `K` 增大趋近 180°。于是只要把 `a` 取成 `S` 的最低点（同层里最靠左的那个），
再把 `K` 取得足够大，`S - a` 就整个被吞进去。派工里「正方形可以、六边形不行」的直觉
默认了锥是 90° 的；六边形的三条边确实会跑出**某个**直角锥，但跑不出足够钝的幺模锥。

🔴 **但这不救链上的 `hwinL_coneRegion`。** 那里的 `vl`、`u'` **不是自由变量**：
`vl ∥ ℓ`（`ℓ` 是给定的非扩张方向），`u'` 是扇上相邻的边方向（`b3_colle2.txt:770`）。
在 `(vl, u')` 被配置钉死之后 `hapex` 仍然可以为假——那正是 §3.1 的 `Sap`
（`not_exists_apex_of_no_edge_parallel`，`:256`），它在**固定**的 `(1,0)`、`(0,1)` 下对
**每一个** `a ∈ Sap` 都失败，且 `hno`、`hstrict` 同时为真。
**所以该被攻的是「给定 `vl` 时 `hapex` 的生产者」，不是 `hapex` 本身。**

§4.2 把派工点名的六边形算进内核，作为 §4.1 的具体实例，并且顺带把
`hwinL_coneRegion`（`LineIndex.lean:144`）的**整组前提**一次性满足，证明它非空转。 -/

/-! ### §4.1  存在量词版本：对任意非空有限 `S` 恒真 -/

/-- **对任何非空有限 `S`，都存在顶点 `a` 与幺模对 `(vl, u')` 使 `hapex` 成立。**

构造（全在证明里，无隐藏选择公理以外的东西）：
- `a` := `S` 中 `y` 最小的点，同层内取 `x` 最小的那个；
- `vl := (1, 0)`，`u' := (-K, 1)`，其中 `K := max 0 (max_{z ∈ S} (a.1 - z.1))`。
  对**任意** `K` 都有 `det u' vl = -1`，这正是幺模锥可以任意钝的原因。

则每个 `z ∈ S.erase a` 的两个基坐标是 `t = z.2 - a.2 ≥ 0`（`a` 层最低）与
`s = (z.1 - a.1) + t·K ≥ 0`（`t = 0` 时由同层最左给出，`t ≥ 1` 时由 `K` 的取法给出）。

⚠ **本条不给 `ht_pos`**（`t = 0` 的点确实存在：同层里 `a` 右边的点）。`ht_pos` 要的是
「没有平行于 `vl` 的边」，是另一回事（`face_parallel_iff`，`:83`）。

⚠ **本条不救 `hwinL_coneRegion`**：那里的 `vl` 由 `ℓ` 钉死，不能按 `S` 来选。 -/
theorem exists_unimodular_apex (S : Finset (ℤ × ℤ)) (hne : S.Nonempty) :
    ∃ a ∈ S, ∃ vl u' : ℤ × ℤ, det u' vl = -1 ∧
      ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u' := by
  classical
  obtain ⟨y0, hy0S, hy0min⟩ := S.exists_min_image (fun z => z.2) hne
  have hTne : (S.filter (fun z => z.2 = y0.2)).Nonempty :=
    ⟨y0, Finset.mem_filter.mpr ⟨hy0S, rfl⟩⟩
  obtain ⟨a, haT, hamin⟩ :=
    (S.filter (fun z => z.2 = y0.2)).exists_min_image (fun z => z.1) hTne
  obtain ⟨haS, ha2⟩ := Finset.mem_filter.mp haT
  obtain ⟨zm, hzmS, hzmmax⟩ := S.exists_max_image (fun z => a.1 - z.1) hne
  refine ⟨a, haS, (1, 0), (-(max 0 (a.1 - zm.1)), 1), by simp [det], ?_⟩
  set K : ℤ := max 0 (a.1 - zm.1) with hKdef
  have hK0 : (0 : ℤ) ≤ K := le_max_left _ _
  have hKz : ∀ z ∈ S, a.1 - z.1 ≤ K := fun z hz =>
    le_trans (hzmmax z hz) (le_max_right _ _)
  intro z hz
  obtain ⟨hzne, hzS⟩ := Finset.mem_erase.mp hz
  have hy : a.2 ≤ z.2 := by rw [ha2]; exact hy0min z hzS
  have htcast : (((z.2 - a.2).toNat : ℕ) : ℤ) = z.2 - a.2 := Int.toNat_of_nonneg (by omega)
  have hs0 : 0 ≤ z.1 - a.1 + (((z.2 - a.2).toNat : ℕ) : ℤ) * K := by
    rw [htcast]
    by_cases h : z.2 = a.2
    · have h1 : a.1 ≤ z.1 := hamin z (Finset.mem_filter.mpr ⟨hzS, by rw [h, ha2]⟩)
      rw [h]
      omega
    · have ht1 : (1 : ℤ) ≤ z.2 - a.2 := by omega
      have hKzz := hKz z hzS
      nlinarith
  refine ⟨(z.1 - a.1 + (((z.2 - a.2).toNat : ℕ) : ℤ) * K).toNat, (z.2 - a.2).toNat,
    Prod.ext ?_ ?_⟩
  · simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    rw [Int.toNat_of_nonneg hs0, htcast]
    ring
  · simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [Int.toNat_of_nonneg hs0, htcast]
    ring

/-! ### §4.2  派工点名的六边形：`hwinL_coneRegion` 的整组前提同时可满足

`Shex = {0 ≤ x ≤ 2, 0 ≤ y ≤ 2, -1 ≤ x - y ≤ 1}` 的 7 个格点，是
`Nivat.ShellSweep.hexShape 2 2 1 1 0`（`ShellSweep.lean:101`）的 `Finset` 版本——
那边是 `Set`，而 `hapex` 要 `Finset`，所以这里重新给一份。

取 `a = (0,0)`、`vl = (1,-1)`、`u' = (0,1)`、`m = (-1,-1)`。**注意 `vl` 不是 `a` 处的边方向**
（`a` 处的两条边方向是 `(1,0)` 与 `(0,1)`）——正是这个「往外拨」让锥同时吞下六个点
**并且**让 `t ≥ 1` 对每个点成立。 -/

/-- 派工点名的六边形，7 个格点。 -/
def Shex : Finset (ℤ × ℤ) := {(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2)}

theorem mem_Shex {z : ℤ × ℤ} :
    z ∈ Shex ↔ z = (0, 0) ∨ z = (0, 1) ∨ z = (1, 0) ∨ z = (1, 1) ∨ z = (1, 2) ∨
      z = (2, 1) ∨ z = (2, 2) := by
  simp [Shex]

/-- 六边形的六条支撑不等式，作为一次性可用的坐标界。 -/
theorem bounds_Shex {z : ℤ × ℤ} (hz : z ∈ Shex) :
    0 ≤ z.1 ∧ z.1 ≤ 2 ∧ 0 ≤ z.2 ∧ z.2 ≤ 2 ∧ -1 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ 1 := by
  rw [mem_Shex] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- 六边形的横向方向。**不是 `a` 处的边方向**，见 §4.2 抬头。 -/
def vlhex : ℤ × ℤ := (1, -1)

/-- 六边形的第二条射线方向。 -/
def u'hex : ℤ × ℤ := (0, 1)

/-- 六边形的横截法向：`dot mhex vlhex = 0`、`dot mhex u'hex = -1`。 -/
def mhex : ℤ × ℤ := (-1, -1)

/-- `Shex` 的实数六边形，写成六个半平面的交。 -/
def hexBox : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ 2 ∧ 0 ≤ q.2 ∧ q.2 ≤ 2 ∧ -1 ≤ q.1 - q.2 ∧ q.1 - q.2 ≤ 1}

theorem convex_hexBox : Convex ℝ hexBox := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hu1, hu2, hu3, hu4, hu5, hu6⟩ := hu
  obtain ⟨hv1, hv2, hv3, hv4, hv5, hv6⟩ := hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    nlinarith

theorem latticeConvex_Shex : LatticeConvex Shex := by
  intro z hz
  have hsub : Conv Shex ⊆ hexBox := by
    refine convexHull_min ?_ convex_hexBox
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe, mem_Shex] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by norm_num [toReal], by norm_num [toReal], by norm_num [toReal],
        by norm_num [toReal], by norm_num [toReal], by norm_num [toReal]⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hsub hz
  simp only [toReal] at h1 h2 h3 h4 h5 h6
  have g1 : (0 : ℤ) ≤ z.1 := by exact_mod_cast h1
  have g2 : z.1 ≤ 2 := by exact_mod_cast h2
  have g3 : (0 : ℤ) ≤ z.2 := by exact_mod_cast h3
  have g4 : z.2 ≤ 2 := by exact_mod_cast h4
  have g5 : (-1 : ℤ) ≤ z.1 - z.2 := by exact_mod_cast h5
  have g6 : z.1 - z.2 ≤ 1 := by exact_mod_cast h6
  obtain ⟨x, y⟩ := z
  rw [mem_Shex]
  simp only [Prod.mk.injEq]
  simp only at g1 g2 g3 g4 g5 g6
  omega

theorem posArea_Shex : PosArea (↑Shex : Set (ℤ × ℤ)) := by
  refine ⟨(0, 0), by rw [Finset.mem_coe, mem_Shex]; tauto,
    (1, 0), by rw [Finset.mem_coe, mem_Shex]; tauto,
    (0, 1), by rw [Finset.mem_coe, mem_Shex]; tauto, ?_⟩
  decide

/-- 与 `vlhex = (1,-1)` 正交的本原法向只有 `±(1,1)`，它们的支撑面分别是单点
`(2,2)` 与 `(0,0)`。 -/
theorem eq_of_mem_face_Shex {n : ℤ × ℤ}
    (hcase : (n.1 = 1 ∧ n.2 = 1) ∨ (n.1 = -1 ∧ n.2 = -1))
    {z w : ℤ × ℤ} (hz : z ∈ face (↑Shex : Set (ℤ × ℤ)) n)
    (hw : w ∈ face (↑Shex : Set (ℤ × ℤ)) n) : z = w := by
  have hzb := bounds_Shex (Finset.mem_coe.mp hz.1)
  have hwb := bounds_Shex (Finset.mem_coe.mp hw.1)
  obtain ⟨hz1, hz2, hz3, hz4, -, -⟩ := hzb
  obtain ⟨hw1, hw2, hw3, hw4, -, -⟩ := hwb
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hzt := hz.2 (2, 2) (by rw [Finset.mem_coe, mem_Shex]; tauto)
    have hwt := hw.2 (2, 2) (by rw [Finset.mem_coe, mem_Shex]; tauto)
    simp only [dot, h1, h2] at hzt hwt
    exact Prod.ext (by omega) (by omega)
  · have hzt := hz.2 (0, 0) (by rw [Finset.mem_coe, mem_Shex]; tauto)
    have hwt := hw.2 (0, 0) (by rw [Finset.mem_coe, mem_Shex]; tauto)
    simp only [dot, h1, h2] at hzt hwt
    exact Prod.ext (by omega) (by omega)

/-- **引理 2.6 的结论在 `Shex` 上成立**：没有平行于 `vlhex` 的边。 -/
theorem no_edge_parallel_Shex : ∀ n ∈ E (↑Shex : Set (ℤ × ℤ)), dot n vlhex ≠ 0 := by
  intro n hn hdot
  obtain ⟨hprim, hnt⟩ := mem_E_iff.mp hn
  have hdot' : n.1 * 1 + n.2 * (-1) = 0 := hdot
  have hn12 : n.2 = n.1 := by omega
  have hgcd : n.1.natAbs = 1 := by
    have h := hprim
    simp only [Prim, hn12] at h
    rwa [Int.gcd_self] at h
  have hcase : (n.1 = 1 ∧ n.2 = 1) ∨ (n.1 = -1 ∧ n.2 = -1) := by omega
  obtain ⟨z, hz, w, hw, hzw⟩ := hnt
  exact hzw (eq_of_mem_face_Shex hcase hz hw)

/-- **派工点名的六边形不是反例：它满足 `hapex`，而且满足 `hwinL_coneRegion` 的整组前提。**

原文：b3_colle2.txt:792（引理 2.6）＋ `:794-798`（Figure 10）。

见证 `Shex`、`a = (0,0)`、`vl = (1,-1)`、`u' = (0,1)`、`m = (-1,-1)`。逐条在内核里验过：
`LatticeConvex`、`PosArea`、三个方向本原、`det u' vl = -1`、`dot m vl = 0`、`dot m u' = -1`、
引理 2.6 的结论 `hno`，以及结论里的三条 —— `hstrict`、`hapex`、`ht_pos`。

**读法：`hwinL_coneRegion`（`LineIndex.lean:144`）不是空转的。** 它的四条前提
（`hapex`、`ht_pos`、`hm`、`hu'`）在此见证上同时成立，且底下的 `S` 是一个货真价实的
非退化格凸六边形，不是退化的点或线段。

⚠ **这不证明 `hapex` 在链上成立**，只证明它不空。链上 `vl` 由 `ℓ` 钉死，见 §4 抬头的红字。 -/
theorem exists_hapex_hexagon :
    Shex.Nonempty ∧ LatticeConvex Shex ∧ PosArea (↑Shex : Set (ℤ × ℤ)) ∧
      Primitive vlhex ∧ Primitive u'hex ∧ Primitive mhex ∧
      det u'hex vlhex = -1 ∧
      dot mhex vlhex = 0 ∧ dot mhex u'hex = -1 ∧
      (∀ n ∈ E (↑Shex : Set (ℤ × ℤ)), dot n vlhex ≠ 0) ∧
      ∃ a ∈ Shex,
        (∀ z ∈ Shex.erase a, dot mhex z < dot mhex a) ∧
        (∀ z ∈ Shex.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vlhex + (t : ℤ) • u'hex) ∧
        (∀ z ∈ Shex.erase a, ∃ s t : ℕ,
          z - a = (s : ℤ) • vlhex + (t : ℤ) • u'hex ∧ t ≥ 1) := by
  refine ⟨⟨(0, 0), by rw [mem_Shex]; tauto⟩, latticeConvex_Shex, posArea_Shex,
    prim_iff_primitive.mp (by decide), prim_iff_primitive.mp (by decide),
    prim_iff_primitive.mp (by decide), by decide, by decide, by decide,
    no_edge_parallel_Shex, (0, 0), by rw [mem_Shex]; tauto, ?_, ?_, ?_⟩
  · intro z hz
    rw [Finset.mem_erase, mem_Shex] at hz
    rcases hz.2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hz.1
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
  · intro z hz
    rw [Finset.mem_erase, mem_Shex] at hz
    rcases hz.2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hz.1
    · exact ⟨0, 1, by decide⟩
    · exact ⟨1, 1, by decide⟩
    · exact ⟨1, 2, by decide⟩
    · exact ⟨1, 3, by decide⟩
    · exact ⟨2, 3, by decide⟩
    · exact ⟨2, 4, by decide⟩
  · intro z hz
    rw [Finset.mem_erase, mem_Shex] at hz
    rcases hz.2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hz.1
    · exact ⟨0, 1, by decide, by decide⟩
    · exact ⟨1, 1, by decide, by decide⟩
    · exact ⟨1, 2, by decide, by decide⟩
    · exact ⟨1, 3, by decide, by decide⟩
    · exact ⟨2, 3, by decide, by decide⟩
    · exact ⟨2, 4, by decide, by decide⟩

end Nivat.ApexUnique

#print axioms Nivat.ApexUnique.dot_eq_zero_of_det_eq_zero
#print axioms Nivat.ApexUnique.face_parallel_iff
#print axioms Nivat.ApexUnique.exists_strict_argmax_of_no_edge_parallel
#print axioms Nivat.ApexUnique.latticeConvex_Sap
#print axioms Nivat.ApexUnique.posArea_Sap
#print axioms Nivat.ApexUnique.no_edge_parallel_Sap
#print axioms Nivat.ApexUnique.exists_strict_argmax_Sap
#print axioms Nivat.ApexUnique.not_exists_apex_of_no_edge_parallel
#print axioms Nivat.ApexUnique.latticeConvex_Spos
#print axioms Nivat.ApexUnique.exists_apex_Spos
#print axioms Nivat.ApexUnique.exists_unimodular_apex
#print axioms Nivat.ApexUnique.latticeConvex_Shex
#print axioms Nivat.ApexUnique.posArea_Shex
#print axioms Nivat.ApexUnique.no_edge_parallel_Shex
#print axioms Nivat.ApexUnique.exists_hapex_hexagon
