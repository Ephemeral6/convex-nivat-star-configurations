/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.NlmaxReachMin
import Nivat.External.Colle.EnvRefuteCover
import Nivat.External.Colle.EnvRefuteOrient
import Nivat.External.Colle.ChainPartsFeed

set_option autoImplicit false

/-!
# `bottom` 的 `hz₀` 与 `hline0` 是**一条**靶子，且等于一条纯算术条件

`BottomReachMin.bottom_of_reachMin`（`BottomReachMin.lean:151`）把 `bottom` 字段
（`ChainPartsFeed.lean:360`）拆成六条 binder：`hdz` / `hz₀` / `hline0` / `hedge` / `hlow` / `hhigh`。
集成者第 240 轮按「一条 binder 一条 lane」派工时，把 `hz₀`（存在性）与 `hline0`（reach-最小性）
当作两条分别派了出去。**本文件证明它们是一条**：`NlmaxReachMin.exists_reachMin_of_L`
（`NlmaxReachMin.lean:107`）一次同时产出三者（前两条正是 `hdz` ∧ `hz₀`，第三条正是 `hline0`），
而它唯一的非字段前提 `hne`（「该层高度非空」）又恰好是
`EnvRefuteCover.heights_iff_cover`（`EnvRefuteCover.lean:104`）的左边。

⟹ 在**共线格**（`det p vJ1 = 0`，即 `J = ι+1`）里，六条残余中的前三条一起塌成：

  `∀ r : ℤ, ∃ g ∈ ⋃ i, hatOf A kk vl i, (-dot nJ vJ1) ∣ (dot nJ g - r)`   （剩余类覆盖）

即「`Âinf` 的高度谱打满 mod `-dot nJ vJ1` 的每个剩余类」。原文对应 `b3_colle2.txt:518-520`
（`NlmaxReachMin.lean` 抬头记的同一段），共线构型 `p = -c • vl`、`vJ1 = m • vl` 见 `:506`。

⭐ **§2 把这条推到两格通用**（第 241 轮下半，lane-env-refute 同轮独立落地的
`EnvRefuteOrient.hline0_of_supp`（`EnvRefuteOrient.lean:1850`）使之成为可能）：该条把楔形抽象成
一个法向/顶点对 `(nprevJ, V)` ＋ 三条前提，**不吃 `hpar`**。取 `nprevJ := (vJ1.2, -vJ1.1)`
（`vJ1` 的旋转）时 `⟪nprevJ, vJ1⟫ = 0` **自动成立、与格无关**，于是同一条归约在
**横截格**（`det p vJ1 ≠ 0`）上照样跑。⟹ 集成者第 241 轮上半发给 lane-tower-hbase 的
「横截格里 `hz₀`/`hline0` 仍是两条独立残余」**是错的**，同轮内已订正。

⚠ **辖域（PROTOCOL §50）**：§1 的 `exists_reachMin_of_L` 路线只在共线格（楔形法向
`n_prev := -(det p vJ • (-p.2, p.1))` 的 `⟪n_prev, vJ1⟫ = 0` 一步用掉 `hpar`）；§2 的路线两格通用，
但把欠账换成了楔形的另外两条（定向 `⟪nprevJ, vJ⟫ < 0` ＋ 支撑界 `hsupp`）。
**两条都留，辖域不同**：共线格走 §1 时那两条由 `ahat_halfPlane_L` / `ahat_attained_L` 白送。

⚠ 本文件**不**声称覆盖条件成立。`EnvRefuteCover` 的 §4 `not_heights_of_rec_fields` 已内核证明
覆盖条件**不**从 `ahat_nonempty` / `rec_p` / `ahat_halfPlane` / `hsweep` / `dot_nJ_p` 五条字段推出，
`§3 cover_without_gcd_one` 又证明它严格弱于 `gcd = 1`。⟹ 覆盖条件是**真欠账**，本文件只是把
三条残余压成它这一条。
-/

namespace Nivat.BottomHz0Collapse

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm Nivat.ChainAsm.Aparts

variable {α : Type*} {η xper : Config α} {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}

/-- 字段 `hhp` 的并集逐点形。`ChainDataGeomParts.hhp` 写成 `∀ i, hatOf … ⊆ halfPlaneGE nJ cJ`，
`heights_iff_cover` 要的是 `∀ g ∈ ⋃ …, cJ ≤ dot nJ g`。 -/
theorem union_hhp_ge (c : ChainDataGeomParts η xper vl p S gen) :
    ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, c.cJ ≤ dot c.nJ g := by
  intro g hg
  obtain ⟨_, ⟨i, rfl⟩, hgi⟩ := hg
  exact c.hhp i hgi

/-- ⭐ **`det p vJ ≠ 0` 是字段的推论，零成本。**

`exists_reachMin_of_L` 的 `hdet` 不必派工：若 `det p vJ = 0`，由 `vJ_prim` 得 `p = k • vJ`，
于是 `dot nJ p = k * dot nJ vJ = 0`（`F.dot_nJ_vJ`），与字段 `dot_nJ_p` 矛盾。 -/
theorem det_p_vJ_ne (c : ChainDataGeomParts η xper vl p S gen) : det p c.vJ ≠ 0 := by
  intro h
  have hvJ : Prim c.vJ := prim_iff_primitive.mpr c.vJ_prim
  have h' : det c.vJ p = 0 := by unfold det at h ⊢; linarith
  obtain ⟨k, hk⟩ := exists_smul_of_det_eq_zero hvJ h'
  apply c.dot_nJ_p
  have hd : dot c.nJ p = k * dot c.nJ c.vJ := by simp only [dot, hk]; ring
  rw [hd, c.F.dot_nJ_vJ, mul_zero]

/-- **剩余类覆盖 ⟹ 每层高度非空**，纯字段（`hsweep` ＋ `hhp`）。

这是 `heights_iff_cover` 的 ⟸ 方向在字段上的实例；它同时就是 `bottom` 第 1 合取的高度部分。 -/
theorem heights_of_cover (c : ChainDataGeomParts η xper vl p S gen)
    (hcov : ∀ r : ℤ, ∃ g ∈ ⋃ i, hatOf c.A c.kk vl i,
      (-dot c.nJ c.vJ1) ∣ (dot c.nJ g - r)) :
    ∀ ε : ℕ, ∃ z ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1,
      dot c.nJ z = c.cJ - (ε : ℤ) - 1 :=
  (Nivat.EnvRefuteCover.heights_iff_cover c.hsweep (union_hhp_ge c)).mpr hcov

/-- ⭐⭐⭐ **共线格：`hdz` ∧ `hz₀` ∧ `hline0` 三条残余一次到手，代价只有剩余类覆盖。**

`exists_reachMin_of_L` 的六条前提里，五条由字段供（`nJ_prim` / `vJ_prim` / `F.dot_nJ_vJ` /
`ahat_halfPlane_L` / `ahat_attained_L`），`hdet` 由 `det_p_vJ_ne` 白拿，只剩 `hne` 需要 `hcov`。

⟹ 供给 `BottomReachMin.bottom_of_reachMin` 的六条 binder 里，共线格下**只剩三条**：
`hedge` / `hlow` / `hhigh`（都是 `S` 上的成员关系，见 `BottomReachMin.hseedS_of_edge`）。 -/
theorem hdz_hz0_hline0_of_cover_collinear (c : ChainDataGeomParts η xper vl p S gen)
    (hpar : det p c.vJ1 = 0)
    (hcov : ∀ r : ℤ, ∃ g ∈ ⋃ i, hatOf c.A c.kk vl i,
      (-dot c.nJ c.vJ1) ∣ (dot c.nJ g - r))
    (ε : ℕ) :
    ∃ z₀ : ℤ × ℤ,
      dot c.nJ z₀ = c.cJ - (ε : ℤ) - 1 ∧
      z₀ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1 ∧
      ∀ z ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1,
        dot c.nJ z = c.cJ - (ε : ℤ) - 1 → ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • c.vJ :=
  Nivat.NlmaxReachMin.exists_reachMin_of_L
    (prim_iff_primitive.mpr c.nJ_prim) (prim_iff_primitive.mpr c.vJ_prim)
    c.F.dot_nJ_vJ hpar (det_p_vJ_ne c) c.ahat_halfPlane_L c.ahat_attained_L
    (heights_of_cover c hcov ε)

/-! ## §2 两格通用的版本：楔形抽象成 `(nprevJ, V)`，不吃 `hpar`

`EnvRefuteOrient.hline0_of_supp`（`EnvRefuteOrient.lean:1850`）是 §1 那条定理的去构型化版本。
它同样一次产出 `hdz` ∧ `hz₀` ∧ `hline0`，而对楔形只要三条：
`⟪nprevJ, vJ1⟫ = 0`、`⟪nprevJ, vJ⟫ < 0`、`∀ z ∈ T, ⟪nprevJ, z⟫ ≤ ⟪nprevJ, V⟫`。

⚠ 同文件 `not_hline0_without_supp`（`:1920`）已内核证明：**去掉 `hsupp` 结论就假**
（上半平面居民，层线上没有 `vJ`-最小点）⟹ 支撑界不是可省的技术前提，是本质的。
`supp_fails_on_halfPlane`（`:1959`）进一步说明该居民对**任何** `V` 都不满足 `hsupp`。 -/

/-- 字段层的 `hcov ⟹ hne` ＋ `hline0_of_supp`，楔形留成 binder。**与格无关。** -/
theorem hdz_hz0_hline0_of_wedge (c : ChainDataGeomParts η xper vl p S gen)
    (nprevJ V : ℤ × ℤ)
    (hnpvJ1 : dot nprevJ c.vJ1 = 0) (hnpvJ : dot nprevJ c.vJ < 0)
    (hsupp : ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i, dot nprevJ z ≤ dot nprevJ V)
    (hcov : ∀ r : ℤ, ∃ g ∈ ⋃ i, hatOf c.A c.kk vl i,
      (-dot c.nJ c.vJ1) ∣ (dot c.nJ g - r))
    (ε : ℕ) :
    ∃ z₀ : ℤ × ℤ, dot c.nJ z₀ = c.cJ - (ε : ℤ) - 1 ∧
      z₀ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1 ∧
      ∀ z ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1,
        dot c.nJ z = c.cJ - (ε : ℤ) - 1 → ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • c.vJ :=
  Nivat.EnvRefuteOrient.hline0_of_supp
    (prim_iff_primitive.mpr c.nJ_prim).ne_zero (prim_iff_primitive.mpr c.vJ_prim)
    c.F.dot_nJ_vJ hnpvJ1 hnpvJ hsupp (heights_of_cover c hcov ε)

/-- `vJ1` 的旋转与 `vJ1` 正交——**恒等式，不需要任何前提，与格无关**。
这是让 §2 越过 `hpar` 的那一步。 -/
theorem dot_rot_self (v : ℤ × ℤ) : dot (v.2, -v.1) v = 0 := by
  simp only [dot]; ring

/-- ⭐⭐⭐ **横截格：`hdz` ∧ `hz₀` ∧ `hline0` 同样一次到手。**

楔形法向取 `nprevJ := (vJ1.2, -vJ1.1)`，第 1 条前提由 `dot_rot_self` 白送，**与
`det p vJ1` 是否为零无关**。⟹ 横截格欠的是：剩余类覆盖 ＋ 定向 `⟪nprevJ, vJ⟫ < 0`
＋ 支撑界 `hsupp` ＋ `hedge` / `hlow` / `hhigh`。

⚠ 与 §1 比：共线格走 §1 时定向与支撑界由 `ahat_halfPlane_L` / `ahat_attained_L` 白送，
横截格没有对应字段，所以这两条在这里是真 binder。**这正是两格的真实差别**——
不是「塌不塌」，而是「楔形从哪来」。 -/
theorem hdz_hz0_hline0_transverse (c : ChainDataGeomParts η xper vl p S gen)
    (V : ℤ × ℤ)
    (hdir : dot (c.vJ1.2, -c.vJ1.1) c.vJ < 0)
    (hsupp : ∀ z ∈ ⋃ i, hatOf c.A c.kk vl i,
      dot (c.vJ1.2, -c.vJ1.1) z ≤ dot (c.vJ1.2, -c.vJ1.1) V)
    (hcov : ∀ r : ℤ, ∃ g ∈ ⋃ i, hatOf c.A c.kk vl i,
      (-dot c.nJ c.vJ1) ∣ (dot c.nJ g - r))
    (ε : ℕ) :
    ∃ z₀ : ℤ × ℤ, dot c.nJ z₀ = c.cJ - (ε : ℤ) - 1 ∧
      z₀ ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1 ∧
      ∀ z ∈ reachSet (⋃ i, hatOf c.A c.kk vl i) c.vJ1,
        dot c.nJ z = c.cJ - (ε : ℤ) - 1 → ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • c.vJ :=
  hdz_hz0_hline0_of_wedge c _ V (dot_rot_self c.vJ1) hdir hsupp hcov ε

end Nivat.BottomHz0Collapse

#print axioms Nivat.BottomHz0Collapse.union_hhp_ge
#print axioms Nivat.BottomHz0Collapse.det_p_vJ_ne
#print axioms Nivat.BottomHz0Collapse.heights_of_cover
#print axioms Nivat.BottomHz0Collapse.hdz_hz0_hline0_of_cover_collinear
#print axioms Nivat.BottomHz0Collapse.hdz_hz0_hline0_of_wedge
#print axioms Nivat.BottomHz0Collapse.dot_rot_self
#print axioms Nivat.BottomHz0Collapse.hdz_hz0_hline0_transverse
