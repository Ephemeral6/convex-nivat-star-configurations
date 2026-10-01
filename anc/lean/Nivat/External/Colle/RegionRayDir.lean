/-
lane-env-refute，第 167 轮：**`LE2.IsRegion` 的 `semiInf` → `Colle41.RayIn`，方向钉成 `±dir n`。**

team-lead 派的目标（`ray_of_infinite_face`）**主仓已经有八成**：
`Nivat.LE2.exists_nat_ray_of_infinite_face`（`RegionCut.lean:234`，0 sorry）给出

    ∃ q e, e ≠ 0 ∧ dot n e = 0 ∧ ∀ k : ℕ, q + (k:ℤ) • e ∈ R

缺的只有**一句话**：它把方向说成「某个垂直于 `n` 的非零向量」，而消费者
`Colle41.IsRegion`（`Lemma41.lean:688`）要的是**具体**方向 `u`、`u'`。
本文件把 `e` 钉成 `dir n` 或 `-(dir n)` 本身。

补法不是重证：由 `Prim n` 与 `dot n e = 0` 得 `e = m • dir n`（`m ≠ 0`），
再用格凸性把「每 `|m|` 步一个点」的稀疏射线补成**每步一个点**的射线
（`mem_of_between`，`RegionCut.lean:201`）。

**符号不在这里定**——§1 的数值实例证明它**定不了**：同一个第一象限上，
`n = (-1,0)` 落在 `-(dir n)` 那支、`n = (0,-1)` 落在 `+dir n` 那支，
而且 `(-1,0)` 的 `+dir n` 那支**可证为假**（`quad_no_ray_left_dir`）。
定号必须由 `detPos` / `precedes`（`LatticeEdges.lean:2238`/`:2240`）从外面给，
这正是 team-lead 第 167 轮收据 `tmp/region_orientation_probe.lean` 那张表的内容。
-/
import Nivat.External.Colle.RegionCut
import Nivat.External.Colle.Lemma41

set_option autoImplicit false

namespace Nivat.RegionRayDir

open Nivat Nivat.LE2

/-! ## §1 数值实例（硬规矩 6）：第一象限，两条半无穷边的射线方向一正一反 -/

theorem prim_left : Prim ((-1 : ℤ), (0 : ℤ)) := by decide

theorem prim_bot : Prim ((0 : ℤ), (-1 : ℤ)) := by decide

/-- ℓ 边（外法向 `(-1,0)`）：射线方向是 **`-(dir n)`**，`dir (-1,0) = (0,-1)`。 -/
theorem quad_ray_left :
    Colle41.RayIn quad ((0 : ℤ), (0 : ℤ)) (-(dir ((-1 : ℤ), (0 : ℤ)))) := by
  intro k
  have h : ((0 : ℤ), (0 : ℤ)) + (k : ℤ) • (-(dir ((-1 : ℤ), (0 : ℤ))))
      = ((0 : ℤ), (k : ℤ)) := by
    norm_num [dir, Prod.ext_iff, Prod.smul_def]
  rw [h, mem_quad]
  exact ⟨le_refl 0, Int.natCast_nonneg k⟩

/-- ℓ_J 边（外法向 `(0,-1)`）：射线方向是 **`+dir n`**，`dir (0,-1) = (1,0)`。 -/
theorem quad_ray_bot :
    Colle41.RayIn quad ((0 : ℤ), (0 : ℤ)) (dir ((0 : ℤ), (-1 : ℤ))) := by
  intro k
  have h : ((0 : ℤ), (0 : ℤ)) + (k : ℤ) • (dir ((0 : ℤ), (-1 : ℤ)))
      = ((k : ℤ), (0 : ℤ)) := by
    norm_num [dir, Prod.ext_iff, Prod.smul_def]
  rw [h, mem_quad]
  exact ⟨Int.natCast_nonneg k, le_refl 0⟩

/-- **析取收不成单支.**  同一个 `quad`，`n = (-1,0)` 的 `+dir n` 那支是**假**的：
`dir (-1,0) = (0,-1)` 指向 `y` 轴负向，走够远就出第一象限。 -/
theorem quad_no_ray_left_dir :
    ¬ ∃ z₀ : ℤ × ℤ, Colle41.RayIn quad z₀ (dir ((-1 : ℤ), (0 : ℤ))) := by
  rintro ⟨z₀, h⟩
  have hk := h (z₀.2 + 1).toNat
  rw [mem_quad] at hk
  have hc : (((z₀.2 + 1).toNat : ℕ) : ℤ) = max (z₀.2 + 1) 0 := Int.toNat_eq_max _
  simp only [dir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    hc] at hk
  omega

/-! ## §2 把稀疏射线补密：格凸性沿直线补中间格点 -/

/-- 沿 `m • v`（`m > 0`）的射线可补全成沿 `v` 的射线。
中间格点由 `mem_of_between`（`RegionCut.lean:201`）给出，这是本文件唯一用到凸性的地方。 -/
theorem rayIn_of_rayIn_zsmul {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {q v : ℤ × ℤ} {m : ℤ} (hm : 0 < m) (h : ∀ k : ℕ, q + (k : ℤ) • (m • v) ∈ R) :
    Colle41.RayIn R q v := by
  intro j
  have h0 : q + (0 : ℤ) • v ∈ R := by simpa using h 0
  have hj : q + ((j : ℤ) * m) • v ∈ R := by
    have hk := h j
    rwa [smul_smul] at hk
  have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
  exact mem_of_between hR h0 hj hj0 (by nlinarith)

/-! ## §3 一般式：无界暴露面里的整点射线，方向恰是 `±dir n` -/

/-- **`exists_nat_ray_of_infinite_face` 的定向版.**
`RegionCut.lean:234` 只说方向「非零且垂直于 `n`」；这里钉成 `dir n` 或 `-(dir n)` 本身，
正是 `Colle41.IsRegion` 的两个 `∃ z₀, RayIn K z₀ u` 字段要的形状。

**符号留给外面**：§1 证明了两支都会真的出现，所以这条析取不能收窄；
`detPos` / `precedes`（`LatticeEdges.lean:2238`/`:2240`）才是定号的那条 binder。 -/
theorem ray_of_infinite_face {R : Set (ℤ × ℤ)} {n : ℤ × ℤ}
    (hR : IsLatticeConvexRegion R) (hn : Prim n) (hinf : (face R n).Infinite) :
    (∃ z₀ : ℤ × ℤ, Colle41.RayIn R z₀ (dir n)) ∨
      (∃ z₀ : ℤ × ℤ, Colle41.RayIn R z₀ (-(dir n))) := by
  obtain ⟨q, e, he0, hne, hray⟩ := exists_nat_ray_of_infinite_face hR hn hinf
  have hdet : det (dir n) e = 0 := det_eq_zero_of_dot_eq_zero hn.ne_zero (dot_dir n) hne
  obtain ⟨m, hm⟩ := exists_smul_of_det_eq_zero (prim_dir_of_prim hn) hdet
  have hme : e = m • dir n := by rw [hm]; rfl
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact he0 (by simpa using hme)
  rcases lt_or_gt_of_ne hm0 with hneg | hpos
  · refine Or.inr ⟨q, rayIn_of_rayIn_zsmul hR (m := -m) (by omega) fun k => ?_⟩
    have hk := hray k
    rw [hme] at hk
    have heq : (-m) • (-(dir n)) = m • dir n := by rw [smul_neg, neg_smul, neg_neg]
    rwa [heq]
  · exact Or.inl ⟨q, rayIn_of_rayIn_zsmul hR (m := m) hpos fun k => by
      have hk := hray k; rwa [hme] at hk⟩

/-- team-lead 指定的那个形状（析取在 `∃` 里面）。两者互推，消费者按顺手的取。 -/
theorem exists_ray_dir_or_neg {R : Set (ℤ × ℤ)} {n : ℤ × ℤ}
    (hR : IsLatticeConvexRegion R) (hn : Prim n) (hinf : (face R n).Infinite) :
    ∃ z₀ : ℤ × ℤ, Colle41.RayIn R z₀ (dir n) ∨ Colle41.RayIn R z₀ (-(dir n)) := by
  rcases ray_of_infinite_face hR hn hinf with ⟨z₀, h⟩ | ⟨z₀, h⟩
  exacts [⟨z₀, Or.inl h⟩, ⟨z₀, Or.inr h⟩]

/-! ## §4 接口：直接从 `LE2.IsRegion` 的两个 `semiInf` 字段出发 -/

/-- **给 lane-hole3-cone 的接口.**  `LE2.IsRegion R n n'` 的两条半无穷边各给一条射线，
方向各是 `±dir n` / `±dir n'`，符号未定。

桥 `LE2.IsRegion R n n' → Colle41.IsRegion R (-(dir n)) (dir n')` 剩下的**全部**工作
就是用 `detPos` / `precedes` 把这两个析取各消成一支。本条不碰那一步。 -/
theorem rays_of_isRegion {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ} (h : IsRegion R n n') :
    ((∃ z₀ : ℤ × ℤ, Colle41.RayIn R z₀ (dir n)) ∨
        (∃ z₀ : ℤ × ℤ, Colle41.RayIn R z₀ (-(dir n)))) ∧
      ((∃ z₀ : ℤ × ℤ, Colle41.RayIn R z₀ (dir n')) ∨
        (∃ z₀ : ℤ × ℤ, Colle41.RayIn R z₀ (-(dir n')))) :=
  ⟨ray_of_infinite_face h.latticeConvex (mem_E_iff.mp h.semiInf.1).1 h.semiInf.2,
    ray_of_infinite_face h.latticeConvex (mem_E_iff.mp h.semiInf'.1).1 h.semiInf'.2⟩

end Nivat.RegionRayDir

#print axioms Nivat.RegionRayDir.quad_ray_left
#print axioms Nivat.RegionRayDir.quad_ray_bot
#print axioms Nivat.RegionRayDir.quad_no_ray_left_dir
#print axioms Nivat.RegionRayDir.rayIn_of_rayIn_zsmul
#print axioms Nivat.RegionRayDir.ray_of_infinite_face
#print axioms Nivat.RegionRayDir.exists_ray_dir_or_neg
#print axioms Nivat.RegionRayDir.rays_of_isRegion
