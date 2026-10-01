/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.EnvelopedConvex

set_option autoImplicit false

/-!
# Translation containment for enveloped sets

**Collé, Definition 3.2** (`scratch/b3_colle2.txt:402`): `T` is `E(U)`-enveloped if
`T` is lattice-convex, every edge normal of `T` is also one of `U` with at least the
same edge length, and `|E(T)| = |E(U)|`.

This file reduces the translation-containment question
`Enveloped U T → ∃ v, shift v U ⊆ T`
to the feasibility of a finite linear system in `v`, via the H-representation
`Nivat.LE2.mem_of_dot_le_suppVal` (`LatticeEdges.lean:1393`).

## Main results

* `Nivat.LE2.suppVal_shift` — `suppVal (shift v U) n = suppVal U n + ⟪n,v⟫`.
* `Nivat.LE2.shift_subset_iff_suppVal_le` — `shift v U ⊆ T` **iff**
  `∀ n ∈ E T, suppVal U n + ⟪n,v⟫ ≤ suppVal T n`.

`E T = E U` is **not** reproved here; it is `Nivat.LE2.Enveloped.E_eq`
(`LatticeEdges.lean:1656`), and edge-length dominance on every edge of `U` is
`Nivat.LE2.Enveloped.face_encard_le` (`:1663`).  What remains open is the *feasibility*
of the system — see §3.
-/

namespace Nivat.LE2

open Nivat Nivat.Colle

/-! ## §1. Support value of a shifted set -/

/-- The support value of `shift v U` in direction `n` is `suppVal U n + dot n v`. -/
theorem suppVal_shift {U : Set (ℤ × ℤ)} (hfin : U.Finite) (hne : U.Nonempty) (v n : ℤ × ℤ) :
    suppVal (shift v U) n = suppVal U n + dot n v := by
  obtain ⟨z, hzU, hzeq⟩ := exists_suppVal_eq hfin hne n
  have hshift : z + v ∈ shift v U := by
    show z + v - v ∈ U
    simp [hzU]
  have hmax : ∀ w ∈ shift v U, dot n w ≤ dot n (z + v) := by
    intro w hw
    have hwv : w - v ∈ U := hw
    have hle : dot n (w - v) ≤ dot n z := by
      rw [hzeq]
      exact le_suppVal hfin hne hwv
    calc dot n w
        = dot n ((w - v) + v) := by simp
      _ = dot n (w - v) + dot n v := dot_add n (w - v) v
      _ ≤ dot n z + dot n v := by linarith
      _ = dot n (z + v) := by rw [dot_add]
  have hface : z + v ∈ face (shift v U) n := ⟨hshift, hmax⟩
  rw [suppVal_eq hface, dot_add, hzeq]

/-! ## §2. Translation containment -/

/-- **Translation containment reduces to the support inequalities.**

原文：b3_colle2.txt:402 — Definition 3.2 constrains `𝒯` through its edges, and
`mem_of_dot_le_suppVal` (`LatticeEdges.lean:1393`) says a lattice-convex region of
positive area is exactly the lattice points obeying its own edge inequalities.  So
`shift v U ⊆ T` holds as soon as the *translated* support values of `U` are dominated
by those of `T` on each edge normal of `T`.

**量词对应原文**:
- `n ∈ E T` ↔ the edges `ϖ ∈ E(𝒯)` of Definition 3.2; by `Enveloped.E_eq` this set is
  `E U`, the `w ∈ E(𝒰)` of the same sentence
- `suppVal U n + dot n v` ↔ the support value of the translate `𝒰 + v` at `n`
- the conclusion is the containment drawn in Figure 10 (`:798`)

Envelopedness is **not** assumed: this is the geometry, and Definition 3.2 enters only
when a caller produces a `v` satisfying the hypothesis. -/
theorem shift_subset_of_suppVal_le {U T : Set (ℤ × ℤ)}
    (hTfin : T.Finite) (hTne : T.Nonempty) (hTarea : PosArea T)
    (hTlc : IsLatticeConvexRegion T)
    (hUfin : U.Finite) (hUne : U.Nonempty) {v : ℤ × ℤ}
    (h : ∀ n ∈ E T, suppVal U n + dot n v ≤ suppVal T n) :
    shift v U ⊆ T := by
  intro z hz
  have hzU : z - v ∈ U := hz
  refine mem_of_dot_le_suppVal hTfin hTne hTarea hTlc ?_
  intro n hn
  have h1 : dot n (z - v) ≤ suppVal U n := le_suppVal hUfin hUne hzU
  rw [dot_sub] at h1
  linarith [h n hn]

/-- The converse: containment forces the support inequalities, in **every** direction.
Together with `shift_subset_of_suppVal_le` this makes the reduction an equivalence, so a
caller may work entirely with the finite linear system in `v`. -/
theorem suppVal_le_of_shift_subset {U T : Set (ℤ × ℤ)}
    (hTfin : T.Finite) (hTne : T.Nonempty)
    (hUfin : U.Finite) (hUne : U.Nonempty) {v : ℤ × ℤ}
    (h : shift v U ⊆ T) (n : ℤ × ℤ) :
    suppVal U n + dot n v ≤ suppVal T n := by
  obtain ⟨y, hy, hyeq⟩ := exists_suppVal_eq hUfin hUne n
  have hmem : y + v ∈ T := h (show y + v - v ∈ U by simpa using hy)
  have hle := le_suppVal hTfin hTne (n := n) hmem
  rw [dot_add] at hle
  linarith

/-- **The reduction, as an equivalence.**  `shift v U ⊆ T` is exactly the finite system
`∀ n ∈ E T, suppVal U n + ⟪n,v⟫ ≤ suppVal T n`.

This is what turns "does a translate of `𝒮_φ` fit inside `B`?" into a feasibility
question about finitely many integers, one per edge of the shared normal fan. -/
theorem shift_subset_iff_suppVal_le {U T : Set (ℤ × ℤ)}
    (hTfin : T.Finite) (hTne : T.Nonempty) (hTarea : PosArea T)
    (hTlc : IsLatticeConvexRegion T)
    (hUfin : U.Finite) (hUne : U.Nonempty) {v : ℤ × ℤ} :
    shift v U ⊆ T ↔ ∀ n ∈ E T, suppVal U n + dot n v ≤ suppVal T n :=
  ⟨fun h n _ => suppVal_le_of_shift_subset hTfin hTne hUfin hUne h n,
   fun h => shift_subset_of_suppVal_le hTfin hTne hTarea hTlc hUfin hUne h⟩

/-! ## §3. 撤回 (2026-09-20, 集成者)：`exists_shift_subset_of_enveloped` 的 `sorry` 桩

该声明带 `sorry` 落进主仓（红线违例），已删；上面三条是它的**可用部分**，把存在性问题
归约成 `v` 的有限线性系统，三条都无 `sorry`。

⚠ 同时撤回本文件一个更早的版本里的「反例」`not_exists_shift_subset_of_enveloped`
（取 `U = {(0,0),(1,0),(0,1),(1,1)}`、`T = {(0,0),(2,0),(0,2),(2,2)}`，声称 `Enveloped U T`）。
**那条反例是错的**：`WeaklyEnveloped` 的第一个合取是 `IsLatticeConvexRegion T`
（`LatticeEdges.lean:625`），而 `conv T` 的格点含 `(1,0)`、`(1,1)`、`(2,1)` 等，`T` 一个都没有
——`T` 不是格凸区域，`Enveloped U T` 为假，见证不存在。其附带论证
「2 倍位似把边长翻倍、面积翻四倍，所以原图形平移装不进去」也直接为假：`[0,2]²` 含 `[0,1]²`。

**教训（`PROTOCOL.md` §7 的实例）**：反例落地前必须在内核里把被否命题的**全部**前提
在自己的见证上验一遍。此处只要试证 `IsLatticeConvexRegion T` 就会当场失败。 -/

/-! ## §4. 存在性问题的状态（读法）

**此条为真，缺的是 Minkowski 重建；⛔ 按裁决不立项**（`CORE-HOLES.md` 的
「Minkowski 重建不立项」一条）。

`Enveloped U T` 给 `E T = E U`（同法锥）与格边长 `L_T(n) ≥ L_U(n)` 对每个 `n`。
格凸多边形 `P` 与原始边法向满足 Minkowski 关系 `Σ_n L_P(n) • n = 0`（边向量
`L_P(n)·dir(n)` 闭合边界，而 `dir = rot90` 线性且单射）。所以 `D(n) := L_T(n) − L_U(n)`
满足 `≥ 0` 且 `Σ_n D(n) • n = 0`，故其自身是格多边形 `K` 的边长向量（按角排序法向、
串接——关系闭合路径，排序角使其凸）。则 `U + K` 有同法锥且边长 `L_U + D = L_T`，
所以 `U + K = T + v₀`，且 `T ⊇ U + v` 对任何 `v ∈ K − v₀`。候选 `v := z_T − z_U`
在相邻法向失败，恰是因为单顶点一般不在 `K − v₀` 中。

路径是 Minkowski 重建——昂贵，且 ⛔ **按裁决不立项**（`CORE-HOLES.md` 的
「Minkowski 重建不立项」）。

⚠ **记账订正（本条原先写的理由已过期，不要再复用）**：原文写的是「未派工，因为
`EnvTranslate.lean` 无消费者且不可达任何 `sorry`」。**「无消费者」这个理由现在是假的**——
`shift_subset_iff_suppVal_le` 的一个消费者已经存在：`TowerHlevTile` 的 `htile`
（「`𝒮_φ` 的某个平移落在 `Â_∞` 里」正是本文件归约的那个形状，`Enveloped ↑S (Â_i)` 逐层成立）。
⟹ 不立项的**唯一**现行理由是上面那条裁决，不是「没人要」。谁想重开这条路线，要推翻的是裁决。 -/

end Nivat.LE2

#print axioms Nivat.LE2.suppVal_shift
#print axioms Nivat.LE2.shift_subset_of_suppVal_le
#print axioms Nivat.LE2.suppVal_le_of_shift_subset
#print axioms Nivat.LE2.shift_subset_iff_suppVal_le
