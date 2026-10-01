/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.EnvRefuteCover
import Nivat.External.Colle.ChainMax

/-!
# 格凸 ＋ 全部线性几何字段，抽掉 `rec_vJ` 之后**既不给**剩余类覆盖、**也不给**沿 `vJ` 无界

## ⚠ 本文件先记一条重复品普查（§111「多」形态，我自己的账）

我上一轮在本文件里写的**甲**（`cover_of_rec_vJ`：格凸 ＋ `rec_p` ＋ `rec_vJ` ⟹ 覆盖）
与**链侧实例**（`cover_of_parts_of_rec_vJ`）**都是重复品**，本轮已整段删除。现货（按标识符名）：

* `LeafAShellPinGrow.cover_of_latticeConvex_rec` —— 与我的甲逐条同前提，而且**更强**：
  那里只要 `vJ ≠ 0`，我要的是 `Primitive vJ`。
* `LeafAShellLsideFork.heights_covered_of_latticeConvex_lside` /
  `LeafAShellLsideFork.residue_covered_of_latticeConvex_lside` —— 同一件事的高度谱形与模形。
* `LeafAShellLsideFork.residue_coverage_of_parts_lside` —— 链侧实例，而且是**零 binder** 的
  （比我那条带 `hrecvJ` 的还短），它自己的 docstring 已经写明「不能拿来产 `bottom`，那是循环的」。
* `RecVJSubsume.subsumes_collinear` 那道护栏同时说明：**凡吃 `c : ChainDataGeomParts` 的
  `rec_vJ` 前提都是零增量**（`rec_vJ_of_parts c` 白送），所以我那条 `cover_of_parts_of_rec_vJ`
  的 `hrecvJ` 形参本来就是多余的。

⟹ 按「有消费者才导出，导出了就只留一份」，甲与链侧实例**不落地、不保留**。

## 本文件剩下的两件（都是内核见证，③）

### 第一件

`not_cover_of_geom_bundle`：**二十条**前提 —— 含 `IsLatticeConvexRegion`、真
`⋃ i, Colle35.hatOf A kk vl i` 载体、`hfin` / `AhatMono` / `ahat_nonempty` / `hhp` /
`hswept` / `rec_p` / `0 < dot nJ p` / 四条 `Primitive` / `p = -cc • vl`（`cc > 0`）/
共线 `det p vJ1 = 0` / `det p vJ ≠ 0` / 两条 `ℓ_ι`-侧字段 —— **不蕴含**剩余类覆盖。

⭐ **它是什么**（§52，两座台架之差）：`LeafAShellPinGrow.cover_of_latticeConvex_rec` 的前提表
减去 `hrecvJ`、再加上七条链侧字段，结论仍然假。⟹ 那条里的 **`hrecvJ` 不可删**。

⭐ **与已有两条收据的分工（§91，别当同一条用）**：

| 收据 | 居民 | 格凸？ | `rec_vJ`？ | 否掉的 |
|---|---|---|---|---|
| `LeafAShellLsideFork.stock_witness_recvJ_not_latticeConvex_lside` | `{z \| 0 ≤ z.2 ∧ 2 ∣ z.2}` | **否** | 是 | 覆盖（⟸ 缺格凸） |
| `LeafAShellLsideFork.rec_vJ_not_from_linear_fields_collinear_lside` | `{z \| z.1 ≤ 0 ∧ z.2 = 0}` | 是 | **否** | **`rec_vJ`**，不是覆盖 |
| 本条 `not_cover_of_geom_bundle` | `{(-t, 2t) : t ∈ ℕ}` | 是 | **否** | **覆盖** |

第二行那条**不能替代**本条：它的居民在 `nJ = (-1,0)` 下高度集是**全部**非负整数，
覆盖在那上面**成立**；「`rec_vJ` 假」并不蕴含「覆盖假」。本条换了一条斜率为 `-2` 的
格射线，才让高度集变成 `{2t}`、在 `e = 2` 下漏掉奇数类。
⟹ 三条合起来把 `cover_of_latticeConvex_rec` 的两条非字段输入（格凸、`rec_vJ`）
**各自**钉成承重。

⚠ 机制与 `EnvRefuteCover.not_heights_of_rec_fields` 同源（偶高度壁垒，§91 记明），
增量在**前提表**（5 条抽象字段 → 20 条、含格凸、载体是真 `⋃ hatOf`），不在机制。

## 数值实例（硬规矩 6：先算再写）

`nJ = (0,1)`、`vJ = (1,0)`、`vl = vJ1 = (1,-2)`、`cc = 1`、`p = -(1) • vl = (-1,2)`、
`cJ = cL = 0`。⟹ `e = -⟪nJ,vJ1⟫ = 2`、`⟪nJ,p⟫ = 2 > 0`、`det p vJ1 = 0`（共线）、
`det p vJ = -2 ≠ 0`、`ℓ_ι`-侧法向 `det p vJ • (-p.2, p.1) = (4,2)` 在射线上恒 `0`
（⟹ `ahat_halfPlane_L` 与 `ahat_attained_L` 同时成立）。
高度集 `{2t : t ∈ ℕ}` ⟹ `r = 1` 上覆盖为假。
`Rdeg` 的格凸性取 `C = {q : ℝ × ℝ | q.1 ≤ 0 ∧ q.2 = -2 * q.1}`（闭半平面 ∩ 直线）。
⛔ `rec_vJ` 在这个居民上确实为假：`(0,0) + (1,0) = (1,0) ∉ Rdeg`。

## 射程（§50 等级）

* 本条本身：**③ 内核见证**（`#print axioms` 见文末）。
* §3 那条同样 ③，且**不主张**「`hunb` 为假」——它主张的是「这二十条推不出 `hunb`」。
  `maxA` 一格**本文件**没测；该格已由 `EnvRefuteMaxA.lean`（lane-env-refute）双向内核回答，
  结论是「不是挡板，代价是一个下标位移」，详见 §3 末尾那段。
* ⛔ **不主张**「共线格 `bottom` 为假」：本条否的是一条**蕴含式**，见证**不是**一个
  `ChainDataGeomParts`——`envB` / `maxA` / `envShift` / `subBA` / `subAB` / `escapeW` /
  `shellSubStrip` / `shellEnv` / `fillCover` / `nfp_L` 一条都没测。
  ⟹ 覆盖条件的活路仍只能来自那批 `α`-侧 / 窗口侧字段，与 `CORE-HOLES.md` ⑤ 同向、更窄。
* ⛔ **不主张**「共线格里 `rec_vJ` 没有产者」：那是 ② 级读数，归持有者报。

### 第二件（§3）

`not_unbounded_along_vJ_of_geom_bundle`：**同一张前提表**（逐字符相同的二十条）**不蕴含**
「`⋃ hatOf` 沿 `vJ` 方向无界」，即不蕴含 `TowerHbase.rec_vJ_of_unbounded_line` 的 `hunb` 槽位。

⭐ 为什么这一条比第一件更靠近堵点：共线格里 `bottom ⟸ 覆盖 ⟸ rec_vJ ⟸ bottom` 这个环，
唯一已知的非循环出口就是 `rec_vJ_of_unbounded_line`（`hconv` / `hz₀` 链上免费，
欠账只剩 `hunb`）。第二件说：**那条出口的欠账也不在这二十条里**。

⚠ 两件的逻辑关系：`not_unb_vJ_Rdeg` ⟹ `not_rec_vJ_Rdeg`（`rec_vJ` 成立则从 `(0,0)`
迭代即得无界），反之不然。但两条 bundle 结论**互不蕴含**（结论形状不同），所以都留。
⚠ 沿 `vJ` 走不改高度（`⟪nJ,vJ⟫ = 0`），所以 `hhp` 的半平面界**没有**参与这次否定——
挡住无界性的是「射线上第二坐标决定第一坐标」，纯几何，不是高度界。

## import 表（与 `grep -n "^import"` 一致，§57）

`EnvRefuteCover`（`dot_add_loc` / `dot_zsmul_loc`）、`ChainMax`（`Colle35.hatOf`）。
⚠ 上一轮为甲拉的 `Claim43` 与 `RecVJFromParts` 两条 import 随甲一起删掉了
（`RecVJFromParts` 正是集成者要定价的那条新边，现在不再需要）。
-/

namespace Nivat.TowerHlevCover

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.EnvRefuteCover

/-! ## §1 居民：一条斜率 `-2` 的格射线，装在真 `⋃ hatOf` 里 -/

/-- 第 `i` 层：射线的前 `i+1` 个格点。 -/
def Adeg : ℕ → Set (ℤ × ℤ) := fun i => {z | ∃ t : ℕ, t ≤ i ∧ z = (-(t : ℤ), 2 * (t : ℤ))}

/-- `kk ≡ 0` ⟹ `hatOf` 上的平移是恒等，居民是真 `⋃ hatOf`，不是抽象集合。 -/
def kkdeg : ℕ → ℕ := fun _ => 0

/-- 整条射线。 -/
def Rdeg : Set (ℤ × ℤ) := {z | ∃ t : ℕ, z = (-(t : ℤ), 2 * (t : ℤ))}

theorem hatOf_deg (i : ℕ) :
    Nivat.Colle35.hatOf Adeg kkdeg ((1 : ℤ), (-2 : ℤ)) i = Adeg i := by
  ext z
  simp only [Nivat.Colle35.hatOf, kkdeg, Set.mem_ofPred_eq, Nat.cast_zero, zero_smul,
    add_zero]

theorem iUnion_hatOf_deg :
    (⋃ i, Nivat.Colle35.hatOf Adeg kkdeg ((1 : ℤ), (-2 : ℤ)) i) = Rdeg := by
  ext z
  simp only [Set.mem_iUnion, hatOf_deg, Adeg, Rdeg, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, t, -, rfl⟩; exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩; exact ⟨t, t, le_rfl, rfl⟩

theorem finite_Adeg (i : ℕ) : (Adeg i).Finite := by
  have hsub : Adeg i ⊆ (fun t : ℕ => ((-(t : ℤ), 2 * (t : ℤ)) : ℤ × ℤ)) '' Set.Iic i := by
    rintro z ⟨t, hti, rfl⟩
    exact ⟨t, hti, rfl⟩
  exact Set.Finite.subset ((Set.finite_Iic i).image _) hsub

theorem mono_Adeg : ∀ i j : ℕ, i ≤ j → Adeg i ⊆ Adeg j := by
  rintro i j hij z ⟨t, hti, rfl⟩
  exact ⟨t, hti.trans hij, rfl⟩

theorem mem_Rdeg_zero : ((0 : ℤ), (0 : ℤ)) ∈ Rdeg := ⟨0, by norm_num⟩

theorem nonempty_Rdeg : Rdeg.Nonempty := ⟨_, mem_Rdeg_zero⟩

theorem hhp_Rdeg : ∀ g ∈ Rdeg, (0 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) g := by
  rintro g ⟨t, rfl⟩
  simp only [dot]
  omega

/-- `hswept`：沿 `vJ1 = (1,-2)` 下扫，只要不掉出 `cJ = 0` 就还在射线上。 -/
theorem swept_Rdeg :
    MaxEnv.SweptClosed Rdeg ((1 : ℤ), (-2 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 := by
  rintro g ⟨s, rfl⟩ t hlev
  rw [dot_add_loc, dot_zsmul_loc] at hlev
  simp only [dot] at hlev
  have hts : (t : ℤ) ≤ (s : ℤ) := by omega
  refine ⟨s - t, ?_⟩
  have h1 : ((s - t : ℕ) : ℤ) = (s : ℤ) - (t : ℤ) := by omega
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, h1] <;>
    ring

theorem rec_p_Rdeg : ∀ g ∈ Rdeg, g + ((-1 : ℤ), (2 : ℤ)) ∈ Rdeg := by
  rintro g ⟨t, rfl⟩
  refine ⟨t + 1, ?_⟩
  have h1 : ((t + 1 : ℕ) : ℤ) = (t : ℤ) + 1 := by push_cast; ring
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, h1] <;> ring

/-- ⭐ **射线是格凸区域**：取 `C = {q : ℝ × ℝ | q.1 ≤ 0 ∧ q.2 = -2 * q.1}`，
即闭半平面 ∩ 过原点的直线。方向 `(-1,2)` 本原 ⟹ `C` 里的格点恰是 `(-t, 2t)`，`t : ℕ`。

⟹ 本条把本文件的见证与 `LeafAShellLsideFork.stock_witness_recvJ_not_latticeConvex_lside`
的见证分开：那一条的居民**不**格凸，本条的居民格凸。 -/
theorem latticeConvex_Rdeg : IsLatticeConvexRegion Rdeg := by
  refine ⟨{q : ℝ × ℝ | q.1 ≤ 0 ∧ q.2 = -2 * q.1}, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb _
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have h1 : a * x.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hx.1
      have h2 : b * y.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hy.1
      linarith
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [hx.2, hy.2]
      ring
  · have h1 : IsClosed {q : ℝ × ℝ | q.1 ≤ 0} := isClosed_le continuous_fst continuous_const
    have h2 : IsClosed {q : ℝ × ℝ | q.2 = -2 * q.1} :=
      isClosed_eq continuous_snd (continuous_const.mul continuous_fst)
    exact h1.inter h2
  · ext z
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨?_, ?_⟩
      · show ((-(t : ℤ) : ℤ) : ℝ) ≤ 0
        have : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
        have h : ((-(t : ℤ) : ℤ) : ℝ) = -((t : ℤ) : ℝ) := by push_cast; ring
        rw [h]
        have : (0 : ℝ) ≤ ((t : ℤ) : ℝ) := by exact_mod_cast Int.natCast_nonneg t
        linarith
      · show (((2 * (t : ℤ)) : ℤ) : ℝ) = -2 * ((-(t : ℤ) : ℤ) : ℝ)
        push_cast
        ring
    · rintro ⟨h1, h2⟩
      have h1r : ((z.1 : ℤ) : ℝ) ≤ 0 := h1
      have h2r : ((z.2 : ℤ) : ℝ) = -2 * ((z.1 : ℤ) : ℝ) := h2
      have h1' : z.1 ≤ 0 := by exact_mod_cast h1r
      have h2' : z.2 = -2 * z.1 := by exact_mod_cast h2r
      refine ⟨(-z.1).toNat, ?_⟩
      have ht : ((-z.1).toNat : ℤ) = -z.1 := Int.toNat_of_nonneg (by omega)
      rw [Prod.ext_iff]
      refine ⟨?_, ?_⟩ <;> simp only [ht] <;> omega

/-- `ℓ_ι`-侧法向 `det p vJ • (-p.2, p.1)` 在这组数上是 `(4,2)`。 -/
theorem nL_eq :
    (det ((-1 : ℤ), (2 : ℤ)) ((1 : ℤ), (0 : ℤ)) •
      (-((-1 : ℤ), (2 : ℤ)).2, ((-1 : ℤ), (2 : ℤ)).1) : ℤ × ℤ) = ((4 : ℤ), (2 : ℤ)) := by
  simp only [det]
  norm_num [Prod.ext_iff]

/-- 射线上 `ℓ_ι`-侧高度恒为 `0` ⟹ `ahat_halfPlane_L` ＋ `ahat_attained_L` 同时成立。 -/
theorem dot_nL_Rdeg : ∀ g ∈ Rdeg, dot ((4 : ℤ), (2 : ℤ)) g = 0 := by
  rintro g ⟨t, rfl⟩
  simp only [dot]
  ring

/-- 高度集是 `{2t}` ⟹ 模 `e = 2` 只中一类，`r = 1` 落空。 -/
theorem not_cover_Rdeg :
    ¬ ∀ r : ℤ, ∃ g ∈ Rdeg, (-dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (-2 : ℤ))) ∣
        (dot ((0 : ℤ), (1 : ℤ)) g - r) := by
  intro h
  obtain ⟨g, ⟨t, rfl⟩, k, hk⟩ := h 1
  simp only [dot] at hk
  omega

/-- ⛔ 见证上 `rec_vJ` 确实为假 —— 这就是本条与
`LeafAShellPinGrow.cover_of_latticeConvex_rec` 的分界线。 -/
theorem not_rec_vJ_Rdeg : ¬ ∀ g ∈ Rdeg, g + ((1 : ℤ), (0 : ℤ)) ∈ Rdeg := by
  intro h
  obtain ⟨t, ht⟩ := h _ mem_Rdeg_zero
  rw [Prod.ext_iff] at ht
  have h1 : (1 : ℤ) = -(t : ℤ) := ht.1
  have h2 : (0 : ℤ) = 2 * (t : ℤ) := ht.2
  omega

theorem prim_01 : Primitive ((0 : ℤ), (1 : ℤ)) := ⟨0, 1, by norm_num⟩
theorem prim_10 : Primitive ((1 : ℤ), (0 : ℤ)) := ⟨1, 0, by norm_num⟩
theorem prim_1m2 : Primitive ((1 : ℤ), (-2 : ℤ)) := ⟨1, 0, by norm_num⟩

/-! ## §2 二十条前提不蕴含剩余类覆盖 -/

/-- ⭐⭐⭐ **格凸 ＋ 十九条线性几何前提 ⇏ 剩余类覆盖。**

前提表逐条对到 `ChainDataGeomParts` 的字段（`ChainPartsFeed.lean`，按标识符名）：
`hfin` / `AhatMono` / `ahat_nonempty` / `hhp` / `hswept` / `rec_p` / `dot_nJ_p` /
`nJ_prim` / `vJ_prim` / `F.dot_nJ_vJ` / `hsweep` / `ahat_halfPlane_L` / `ahat_attained_L`，
外加 `Primitive vl` / `Primitive vJ1`、`p = -cc • vl`（`cc > 0`）、共线 `det p vJ1 = 0`、
`det p vJ ≠ 0`，以及 **`IsLatticeConvexRegion`**（它本身不是字段，而是
`ChainAssemble.latticeConvex_iUnion_hatOf` 从 `maxA` / `hfin` / `AhatMono` 的产出）。

⟹ `LeafAShellPinGrow.cover_of_latticeConvex_rec` 里的 **`hrecvJ` 不可删**。

⛔ **不在前提表里、因此不被本条否掉的**：`envB` / `maxA` / `envShift` / `subBA` / `subAB` /
`escapeW` / `shellSubStrip` / `shellEnv` / `fillCover` / `nfp_L` / `F` 的其余字段。
（`maxA` 这一格的现状见 §3 末尾那段：它**不是**挡板，代价是一个下标位移，
但位移后的见证不在本文件里。） -/
theorem not_cover_of_geom_bundle :
    ¬ ∀ (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl p vJ1 nJ vJ : ℤ × ℤ) (cc : ℕ) (cJ cL : ℤ),
        Primitive nJ → Primitive vJ → Primitive vl → Primitive vJ1 →
        dot nJ vJ = 0 →
        vJ1 = vl →
        0 < cc →
        p = -(cc : ℤ) • vl →
        det p vJ1 = 0 →
        det p vJ ≠ 0 →
        dot nJ vJ1 < 0 →
        0 < dot nJ p →
        IsLatticeConvexRegion (⋃ i, Nivat.Colle35.hatOf A kk vl i) →
        (∀ i, (Nivat.Colle35.hatOf A kk vl i).Finite) →
        (∀ i j, i ≤ j → Nivat.Colle35.hatOf A kk vl i ⊆ Nivat.Colle35.hatOf A kk vl j) →
        (⋃ i, Nivat.Colle35.hatOf A kk vl i).Nonempty →
        (∀ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i, cJ ≤ dot nJ g) →
        MaxEnv.SweptClosed (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1 nJ cJ →
        (∀ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i, g + p ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i) →
        (∀ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i,
          cL ≤ dot (det p vJ • (-p.2, p.1)) g) →
        (∃ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i,
          dot (det p vJ • (-p.2, p.1)) g = cL) →
        (∀ r : ℤ, ∃ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i,
          (-dot nJ vJ1) ∣ (dot nJ g - r)) := by
  intro h
  have hcov := h Adeg kkdeg ((1 : ℤ), (-2 : ℤ)) ((-1 : ℤ), (2 : ℤ)) ((1 : ℤ), (-2 : ℤ))
      ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) 1 0 0
    prim_01 prim_10 prim_1m2 prim_1m2
    (by norm_num [dot])
    rfl
    Nat.one_pos
    (by norm_num [Prod.ext_iff])
    (by norm_num [det])
    (by norm_num [det])
    (by norm_num [dot])
    (by norm_num [dot])
    (by rw [iUnion_hatOf_deg]; exact latticeConvex_Rdeg)
    (by intro i; rw [hatOf_deg]; exact finite_Adeg i)
    (by intro i j hij; rw [hatOf_deg, hatOf_deg]; exact mono_Adeg i j hij)
    (by rw [iUnion_hatOf_deg]; exact nonempty_Rdeg)
    (by rw [iUnion_hatOf_deg]; exact hhp_Rdeg)
    (by rw [iUnion_hatOf_deg]; exact swept_Rdeg)
    (by rw [iUnion_hatOf_deg]; exact rec_p_Rdeg)
    (by rw [iUnion_hatOf_deg, nL_eq]
        intro g hg
        exact le_of_eq (dot_nL_Rdeg g hg).symm)
    (by rw [iUnion_hatOf_deg, nL_eq]
        exact ⟨_, mem_Rdeg_zero, dot_nL_Rdeg _ mem_Rdeg_zero⟩)
  rw [iUnion_hatOf_deg] at hcov
  exact not_cover_Rdeg hcov

/-! ## §3 同一见证把「沿 `vJ` 无界」也钉成假

共线格里 `rec_vJ` 的唯一非循环产者形态是
`TowerHbase.rec_vJ_of_unbounded_line`（`hconv` ＋ `hz₀` ＋ `hunb` ⟹ `rec_vJ`），
其中 `hconv` / `hz₀` 在链上免费，欠账只有 `hunb`。本节证明：**`hunb` 在同一组数上也为假**，
所以那条出口在这一格里被同一个见证一起堵住。

⭐ **链侧消费者（量词骨架逐字相同的那一条）**：`TowerHbase.rec_vJ_of_parts_unbounded_line'`
的 `hunb` binder 就是本节 `not_unb_vJ_Rdeg` 的被否形
（`∃ z₀ ∈ ⋃ i, hatOf c.A c.kk vl i, ∀ N : ℤ, ∃ k : ℤ, N ≤ k ∧ z₀ + k • c.vJ ∈ ⋃ …`）。
⚠ 那条链侧产者的签名里**没有** `det p vJ1`，共线格与横截格共用同一条 ⟹ 本节只对
**共线格**那一侧说话：横截格里它的 `hunb` 本文件**没测**。

⚠ 逻辑方向：本节**不是**从 `not_rec_vJ_Rdeg` 推出来的（那要经
`rec_vJ_of_unbounded_line` 的逆，不成立）；`not_unb_vJ_Rdeg` 是独立直证。
反过来它**蕴含** `not_rec_vJ_Rdeg`：若 `rec_vJ` 成立则从 `(0,0)` 迭代即得无界。 -/

/-- ⭐ 沿 `vJ = (1,0)` 平移改第一坐标而不改第二坐标，而射线上第二坐标决定第一坐标
⟹ 只有 `k = 0` 留在集合里 ⟹ **没有任何起点沿 `vJ` 无界**。

这是 `TowerHbase.rec_vJ_of_unbounded_line` 的 `hunb` 槽位的逐字否定式
（`∃ z₀ ∈ R, ∀ N, ∃ k, N ≤ k ∧ z₀ + k • v ∈ R`）。-/
theorem not_unb_vJ_Rdeg :
    ¬ ∃ z₀ ∈ Rdeg, ∀ N : ℤ, ∃ k : ℤ, N ≤ k ∧ z₀ + k • ((1 : ℤ), (0 : ℤ)) ∈ Rdeg := by
  rintro ⟨z₀, ⟨t, rfl⟩, hunb⟩
  obtain ⟨k, hk1, s, hs⟩ := hunb 1
  rw [Prod.ext_iff] at hs
  have h1 : -(t : ℤ) + k * 1 = -(s : ℤ) := hs.1
  have h2 : 2 * (t : ℤ) + k * 0 = 2 * (s : ℤ) := hs.2
  omega

/-- ⭐⭐⭐ **格凸 ＋ 同一张十九条线性几何前提表 ⇏ 「`Âinf` 沿 `vJ` 无界」。**

前提表与 `not_cover_of_geom_bundle` **逐字符相同**（同一组实参兑现），只换结论。
⟹ `TowerHbase.rec_vJ_of_unbounded_line` 的 `hunb` 槽位在共线格里
**不能只靠这十九条前提填**，需要新的承重输入。

⛔ **不在前提表里、因此不被本条否掉的**（与 §2 同一张排除表）：`envB` / **`maxA`** /
`envShift` / `subBA` / `subAB` / `escapeW` / `shellSubStrip` / `shellEnv` / `fillCover` /
`nfp_L` / `F` 的其余字段。其中 `maxA` 是排除表里唯一有希望单独杀掉细射线的字段
（判据：`Rdeg` 能不能配某个 `S` 兑现 `IsMaxEnvIn (EnvOf ↑S) …`），本条**不回答**它。

**`maxA` 这一格已由 lane-env-refute 回答，两个方向都是内核件**（`EnvRefuteMaxA.lean`，
按标识符名；该文件 import 本文件，故本文件**不能**反向 import 它，下面只是记账不是引用）：
`not_maxA_Adeg` 说本文件现在写的 `Adeg` 配不出任何 `S`（理由是边集基数，与几何无关：
`Adeg 0` 是单点 ⟹ `E` 为空，`Adeg 1` 两点共线 ⟹ `E` 基数 2）；`exists_maxA_for_ray`
说取 `Aray i := Adeg (i+1)` 就免费兑现，且 `iUnion_hatOf_ray` 给出**并集逐字不变**
（仍是 `Rdeg`）。⟹ **代价是一个下标位移，不是挡板**：前提表加上 `maxA` 之后 §2 / §3
两条结论一个字都不用改，因为二十条 binder 里只有 `hfin` / `AhatMono` 以及并集那条提到
`A` 本身，其余都在 `⋃ i, hatOf …` 层。
⚠ 但该位移的见证**不在本文件里**：本文件的 `Adeg` 兑现的是不含 `maxA` 的那张前提表。
要一条「含 `maxA` 的前提表同样可反」的内核件，得在 `EnvRefuteMaxA` 的下游另写，
本文件给不出（方向不对）。**别把本条读成「`maxA` 已经打进前提表了」。** -/
theorem not_unbounded_along_vJ_of_geom_bundle :
    ¬ ∀ (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl p vJ1 nJ vJ : ℤ × ℤ) (cc : ℕ) (cJ cL : ℤ),
        Primitive nJ → Primitive vJ → Primitive vl → Primitive vJ1 →
        dot nJ vJ = 0 →
        vJ1 = vl →
        0 < cc →
        p = -(cc : ℤ) • vl →
        det p vJ1 = 0 →
        det p vJ ≠ 0 →
        dot nJ vJ1 < 0 →
        0 < dot nJ p →
        IsLatticeConvexRegion (⋃ i, Nivat.Colle35.hatOf A kk vl i) →
        (∀ i, (Nivat.Colle35.hatOf A kk vl i).Finite) →
        (∀ i j, i ≤ j → Nivat.Colle35.hatOf A kk vl i ⊆ Nivat.Colle35.hatOf A kk vl j) →
        (⋃ i, Nivat.Colle35.hatOf A kk vl i).Nonempty →
        (∀ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i, cJ ≤ dot nJ g) →
        MaxEnv.SweptClosed (⋃ i, Nivat.Colle35.hatOf A kk vl i) vJ1 nJ cJ →
        (∀ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i, g + p ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i) →
        (∀ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i,
          cL ≤ dot (det p vJ • (-p.2, p.1)) g) →
        (∃ g ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i,
          dot (det p vJ • (-p.2, p.1)) g = cL) →
        (∃ z₀ ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i,
          ∀ N : ℤ, ∃ k : ℤ, N ≤ k ∧ z₀ + k • vJ ∈ ⋃ i, Nivat.Colle35.hatOf A kk vl i) := by
  intro h
  have hunb := h Adeg kkdeg ((1 : ℤ), (-2 : ℤ)) ((-1 : ℤ), (2 : ℤ)) ((1 : ℤ), (-2 : ℤ))
      ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) 1 0 0
    prim_01 prim_10 prim_1m2 prim_1m2
    (by norm_num [dot])
    rfl
    Nat.one_pos
    (by norm_num [Prod.ext_iff])
    (by norm_num [det])
    (by norm_num [det])
    (by norm_num [dot])
    (by norm_num [dot])
    (by rw [iUnion_hatOf_deg]; exact latticeConvex_Rdeg)
    (by intro i; rw [hatOf_deg]; exact finite_Adeg i)
    (by intro i j hij; rw [hatOf_deg, hatOf_deg]; exact mono_Adeg i j hij)
    (by rw [iUnion_hatOf_deg]; exact nonempty_Rdeg)
    (by rw [iUnion_hatOf_deg]; exact hhp_Rdeg)
    (by rw [iUnion_hatOf_deg]; exact swept_Rdeg)
    (by rw [iUnion_hatOf_deg]; exact rec_p_Rdeg)
    (by rw [iUnion_hatOf_deg, nL_eq]
        intro g hg
        exact le_of_eq (dot_nL_Rdeg g hg).symm)
    (by rw [iUnion_hatOf_deg, nL_eq]
        exact ⟨_, mem_Rdeg_zero, dot_nL_Rdeg _ mem_Rdeg_zero⟩)
  rw [iUnion_hatOf_deg] at hunb
  exact not_unb_vJ_Rdeg hunb

/-- 记账用：见证上 `a := ⟪nJ,p⟫ = 2`、`e := -⟪nJ,vJ1⟫ = 2`、`vJ1 = (-1) • p`
⟹ `a ∣ e` 且 `e / a = 1`，即 `+p` 射线在模 `e` 下只命中 2 个剩余类里的 1 个。
这是「共线格里 `+p` 单独永远不够」的一个数值实例（硬规矩 6）。 -/
theorem arith_a_dvd_e_Rdeg :
    dot ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (2 : ℤ)) = 2 ∧
      -dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (-2 : ℤ)) = 2 ∧
      ((1 : ℤ), (-2 : ℤ)) = (-1 : ℤ) • ((-1 : ℤ), (2 : ℤ)) := by
  refine ⟨by norm_num [dot], by norm_num [dot], ?_⟩
  rw [Prod.ext_iff]
  norm_num

end Nivat.TowerHlevCover

#print axioms Nivat.TowerHlevCover.Adeg
#print axioms Nivat.TowerHlevCover.kkdeg
#print axioms Nivat.TowerHlevCover.Rdeg
#print axioms Nivat.TowerHlevCover.hatOf_deg
#print axioms Nivat.TowerHlevCover.iUnion_hatOf_deg
#print axioms Nivat.TowerHlevCover.finite_Adeg
#print axioms Nivat.TowerHlevCover.mono_Adeg
#print axioms Nivat.TowerHlevCover.mem_Rdeg_zero
#print axioms Nivat.TowerHlevCover.nonempty_Rdeg
#print axioms Nivat.TowerHlevCover.hhp_Rdeg
#print axioms Nivat.TowerHlevCover.swept_Rdeg
#print axioms Nivat.TowerHlevCover.rec_p_Rdeg
#print axioms Nivat.TowerHlevCover.latticeConvex_Rdeg
#print axioms Nivat.TowerHlevCover.nL_eq
#print axioms Nivat.TowerHlevCover.dot_nL_Rdeg
#print axioms Nivat.TowerHlevCover.not_cover_Rdeg
#print axioms Nivat.TowerHlevCover.not_rec_vJ_Rdeg
#print axioms Nivat.TowerHlevCover.prim_01
#print axioms Nivat.TowerHlevCover.prim_10
#print axioms Nivat.TowerHlevCover.prim_1m2
#print axioms Nivat.TowerHlevCover.not_cover_of_geom_bundle
#print axioms Nivat.TowerHlevCover.not_unb_vJ_Rdeg
#print axioms Nivat.TowerHlevCover.not_unbounded_along_vJ_of_geom_bundle
#print axioms Nivat.TowerHlevCover.arith_a_dvd_e_Rdeg
