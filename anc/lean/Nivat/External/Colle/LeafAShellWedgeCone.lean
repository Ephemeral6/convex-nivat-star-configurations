import Nivat.External.Colle.LeafAShellBottomParts

/-!
# `hexhW` ⟸ 格凸 ＋ `rec_p` ＋ `rec_vJ` ＋ 一条角点（lane-leafa-shell）

## §0 这个文件做什么

消费者是主仓 `LeafAShellBottomParts.lean` 的 `stage_exh_of_wedge_exh` /
`shellFeed_of_parts_of_envOf_wedgeExh` 的 binder `hexhW`（两处逐字符相同）：

```
(hexhW : ∀ q, cJ ≤ dot nJ q → cL ≤ dot (det p vJ • (-p.2, p.1)) q →
    ∃ i₀, ∀ i, i₀ ≤ i → q ∈ hatOf A kk vl i)
```

本文件把它归约成**一条存在性**：

    hcorner : ∃ g ∈ Â_∞, ⟪nJ,g⟫ = cJ ∧ ⟪n_L,g⟫ = cL      （两堵墙**同时**取到）

外加 `rec_vJ`（binder，见 §3 的循环说明）。其余全是字段或白送。

## §1 为什么成立（原文给理由的那一句 ＋ 逐前提对应）

两墙交**恰是**从角点出发、由 `vJ` 与 `p` 张成的**实锥**：
* `⟪nJ,q⟫ ≥ cJ` ⟺ `p`-系数 `≥ 0`，因为 `⟪nJ,vJ⟫ = 0`（字段 `F.dot_nJ_vJ`）而
  `⟪nJ,p⟫ > 0`（`EnvRefuteOrient.dot_nJ_p_pos_of_parts`）；
* `⟪n_L,q⟫ ≥ cL` ⟺ `vJ`-系数 `≥ 0`，因为 `⟪n_L,p⟫ = 0`（`n_L := det p vJ • dir p` 与 `p` 正交，
  纯恒等式）而 `⟪n_L,vJ⟫ = (det p vJ)² > 0`（lane-env-refute 的 `dot_nL_vJ_eq_det_sq`，
  这里由 `det_p_vJ_ne_zero_of_parts` 升成严格）。

而格凸区域**就是**它的实凸包与 `ℤ²` 的交（`Nivat.eq_preimage_convHullOf`，
`Section8/HalfPlane.lean` 的 `IsLatticeConvexRegion` 定义体 `∃ C, Convex ℝ C ∧ IsClosed C ∧
R = toReal ⁻¹' C`）⟹ 锥内的**每个格点**都在 `Â_∞` 里。落点那一步用本 lane 已在主仓的
`LeafAShellLsideFork.mem_of_cone_lside`（格凸 ＋ 含 `z₀` ＋ 对 `+x`/`+y` 封闭 ⟹
`toReal z₀ + aa·x + bb·y` 形的整点都在里面）。

⟹ 本文件的数学内容只有一件事：**把 `q` 的两个实系数算出来并证明它们非负**，
即 `aa = A/(det p vJ)²`、`bb = B/⟪nJ,p⟫`，其中 `A := ⟪n_L,q⟫ - cL`、`B := ⟪nJ,q⟫ - cJ`。
Cramer 那一步（§5 `cramer_comp`）是**纯 ring 恒等式模 `⟪nJ,vJ⟫ = 0`** 一条。

⚠ 原文（`scratch/b3_colle2.txt`）这一侧：`:506` 逐字「Actually, `Â_∞` is an
`(ℓ,ℓ_J)`-region」，`:386` 的 `(ℓ,ℓ')`-region 定义里 `w ≺ ⋯ ≺ w'` 的 `⋯` **允许**两条半无穷
边之间夹有限边 ⟹ 原文**不**给「`Â_∞` 就是两墙交」。本文件因此**不**主张 `hexhW` 为真，
只主张「它 ⟸ 上面那一条角点存在性」。角点存在**就**等于说没有那些有限边。

## §2 与本 lane 上一轮那座台架的关系（§52：两座台架之间的差）

`tmp/wip/lane-leafa-shell-exhw-bench.lean` 用偶数高度层造过一个「`hexhW` 为假」的台架，
**已由本 lane 自己撤回**：那座台架的 `Â_∞` **不格凸**（`(0,0)`、`(0,2)` 在里面、中点 `(0,1)`
不在），而格凸性在链上白送（`RecVJFromParts.latticeConvex_of_parts`，经 `maxA`/`hfin`/`AhatMono`）。
⟹ 本文件正是那次撤回的**正面替代品**：补上被漏掉的那一条自由性质之后，方向整个反过来。

## §3 欠什么（射程，PROTOCOL §50）

1. **`hcorner`**：字段只给 `ahat_attained_L`（`ℓ` 墙在**某个**高度 `h_L` 被取到），
   而从 `h_L` 的墙上点出发、`rec_p`/`rec_vJ` 张出的锥只覆盖 `h_L` 以上 ⟹ 丢掉带
   `[cJ, h_L)`。**这是本文件唯一新增的债**，形状是一条存在性，不是 `∀ q`。
2. **`rec_vJ` 按 binder 记，不按白送。** `RecVJFromParts.rec_vJ_of_parts` 的证明体吃
   `c.bottom`，而本条的下游正是造 `bottom` ⟹ 那是 `blueprint/LANDING.md` 记的
   `bottom ⟸ 覆盖 ⟸ rec_vJ ⟸ bottom` 那个环。非循环出口是 lane-tower-hlev 那条无界性 `hunb`
   （经 `rec_vJ_of_unbounded_line`）。本文件把 `rec_vJ` 原样收成 binder，**不**调用那个环。
3. 本文件**不** range over `escapeW` / `shellSubStrip` / `shellEnv` / `fillCover` / `bottom` /
   `nfp_L` / `w` / `hsweepW` / `I₀` / `B` / `u`。

## §4 归属（§91）

落点机器 `mem_of_cone_lside` 与高度谱 `heights_covered_of_latticeConvex_lside` 是本 lane 早先
落在主仓的件；`latticeConvex_of_parts` / `rec_vJ_of_parts` 是 lane-leafa-gen（`RecVJFromParts`）；
`dot_nJ_p_pos_of_parts` / `det_p_vJ_ne_zero_of_parts` / `dot_nL_vJ_eq_det_sq` 是 lane-env-refute；
「两墙交 = 从角点张成的实锥」这一步的代入、Cramer 系数、以及归约到 `hcorner` 是本轮增量。
`Â_∞` 不格凸的那族假反例由集成者的 `ConeCover.aeven_not_latticeConvex` 钉死，本文件受它约束。
-/

namespace Nivat.LeafAShellWedgeCone

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm Nivat.ChainAsm.Aparts

variable {η xper : Config ℤ} {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}

/-! ## §5 Cramer：两个实系数的整数分子（纯 ring 恒等式模 `⟪nJ,vJ⟫ = 0`） -/

/-- `n_L := det p vJ • dir p` 在差向量上的值就是 `det p vJ · det p v`，无前提。 -/
theorem dot_nL_sub (vJ p q z₀ : ℤ × ℤ) :
    dot (det p vJ • ((-p.2), p.1)) q - dot (det p vJ • ((-p.2), p.1)) z₀
      = det p vJ * det p (q - z₀) := by
  simp only [dot, det, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  ring

theorem dot_sub_eq (nJ q z₀ : ℤ × ℤ) : dot nJ (q - z₀) = dot nJ q - dot nJ z₀ := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub]
  ring

/-- ⭐ **Cramer 分量式。** `v = aa·vJ + bb·p` 的两个系数分别是 `det p vJ · det p v / (det p vJ)²`
与 `⟪nJ,v⟫ / ⟪nJ,p⟫`；这里给的是清分母之后的整数形，唯一的前提是 `⟪nJ,vJ⟫ = 0`。 -/
theorem cramer_comp (nJ vJ p v : ℤ × ℤ) (h : dot nJ vJ = 0) :
    v.1 * (det p vJ) ^ 2 * dot nJ p
        = (det p vJ * det p v) * dot nJ p * vJ.1 + dot nJ v * (det p vJ) ^ 2 * p.1
      ∧ v.2 * (det p vJ) ^ 2 * dot nJ p
        = (det p vJ * det p v) * dot nJ p * vJ.2 + dot nJ v * (det p vJ) ^ 2 * p.2 := by
  simp only [dot, det] at h ⊢
  refine ⟨?_, ?_⟩
  · linear_combination
      (-((p.1 * vJ.2 - p.2 * vJ.1) * p.1 * (p.1 * v.2 - p.2 * v.1))) * h
  · linear_combination
      (-((p.1 * vJ.2 - p.2 * vJ.1) * p.2 * (p.1 * v.2 - p.2 * v.1))) * h

/-! ## §6 抽象形：两墙交 ⊆ `U` -/

/-- ⭐⭐⭐ **两墙交落在 `U` 里**，只吃：格凸、含角点、对 `+vJ` 与 `+p` 封闭、
`⟪nJ,vJ⟫ = 0`、`0 < ⟪nJ,p⟫`、`det p vJ ≠ 0`。

角点 `z₀` 是**两堵墙同时取到**的那个点（`hJ0` ＋ `hL0`）。 -/
theorem wedge_sub_of_corner {U : Set (ℤ × ℤ)} {nJ vJ p z₀ : ℤ × ℤ} {cJ cL : ℤ}
    (hconv : IsLatticeConvexRegion U) (hz₀ : z₀ ∈ U)
    (hrecvJ : ∀ z ∈ U, z + vJ ∈ U) (hrecp : ∀ z ∈ U, z + p ∈ U)
    (hJ0 : dot nJ z₀ = cJ) (hL0 : dot (det p vJ • ((-p.2), p.1)) z₀ = cL)
    (hnJvJ : dot nJ vJ = 0) (hnJp : 0 < dot nJ p) (hdet : det p vJ ≠ 0)
    {q : ℤ × ℤ} (hqJ : cJ ≤ dot nJ q)
    (hqL : cL ≤ dot (det p vJ • ((-p.2), p.1)) q) :
    q ∈ U := by
  have hA : (0 : ℤ) ≤ det p vJ * det p (q - z₀) := by
    rw [← dot_nL_sub vJ p q z₀, hL0]
    linarith
  have hB : (0 : ℤ) ≤ dot nJ (q - z₀) := by
    rw [dot_sub_eq, hJ0]
    linarith
  have hDsq : (0 : ℤ) < (det p vJ) ^ 2 := by positivity
  have hDsqR : (0 : ℝ) < ((det p vJ : ℤ) : ℝ) ^ 2 := by
    have : ((det p vJ : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hdet
    positivity
  have hdR : (0 : ℝ) < ((dot nJ p : ℤ) : ℝ) := by exact_mod_cast hnJp
  refine Nivat.LaneLeafAShellLsideFork.mem_of_cone_lside hconv hz₀ hrecvJ hrecp
    (aa := ((det p vJ * det p (q - z₀) : ℤ) : ℝ) / ((det p vJ : ℤ) : ℝ) ^ 2)
    (bb := ((dot nJ (q - z₀) : ℤ) : ℝ) / ((dot nJ p : ℤ) : ℝ))
    (div_nonneg (by exact_mod_cast hA) (le_of_lt hDsqR))
    (div_nonneg (by exact_mod_cast hB) (le_of_lt hdR)) ?_
  obtain ⟨hc1, hc2⟩ := cramer_comp nJ vJ p (q - z₀) hnJvJ
  have hc1R : ((q - z₀).1 : ℝ) * ((det p vJ : ℤ) : ℝ) ^ 2 * ((dot nJ p : ℤ) : ℝ)
      = ((det p vJ * det p (q - z₀) : ℤ) : ℝ) * ((dot nJ p : ℤ) : ℝ) * (vJ.1 : ℝ)
        + ((dot nJ (q - z₀) : ℤ) : ℝ) * ((det p vJ : ℤ) : ℝ) ^ 2 * (p.1 : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hc1
  have hc2R : ((q - z₀).2 : ℝ) * ((det p vJ : ℤ) : ℝ) ^ 2 * ((dot nJ p : ℤ) : ℝ)
      = ((det p vJ * det p (q - z₀) : ℤ) : ℝ) * ((dot nJ p : ℤ) : ℝ) * (vJ.2 : ℝ)
        + ((dot nJ (q - z₀) : ℤ) : ℝ) * ((det p vJ : ℤ) : ℝ) ^ 2 * (p.2 : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hc2
  have hs1 : ((q - z₀).1 : ℝ) = (q.1 : ℝ) - (z₀.1 : ℝ) := by
    simp only [Prod.fst_sub, Int.cast_sub]
  have hs2 : ((q - z₀).2 : ℝ) = (q.2 : ℝ) - (z₀.2 : ℝ) := by
    simp only [Prod.snd_sub, Int.cast_sub]
  rw [hs1] at hc1R
  rw [hs2] at hc2R
  simp only [toReal, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨?_, ?_⟩
  · field_simp
    linarith [hc1R]
  · field_simp
    linarith [hc2R]

/-! ## §7 链上形：`hexhW` ⟸ `rec_vJ` ＋ `hcorner` -/

/-- ⭐⭐⭐ **链上形。** `hexhW`（消费者处那一版 binder，逐字符）由两条给出：
`rec_vJ`（binder，非循环产者见 §3 第 2 条）＋ `hcorner`（两墙同时取到的角点）。
其余全部由字段或白送件兑现：格凸 `latticeConvex_of_parts`、`rec_p` 是字段、
`⟪nJ,vJ⟫ = 0` 是 `F.dot_nJ_vJ`、`0 < ⟪nJ,p⟫` 是 `dot_nJ_p_pos_of_parts`、
`det p vJ ≠ 0` 是 `det_p_vJ_ne_zero_of_parts`。

末一步 `∃ i₀, ∀ i ≥ i₀` 由字段 `AhatMono` 从 `∈ ⋃` 单调化（与本 lane
`lane-leafa-shell-exhunion.lean` 的 `eventually_mem_iff_mem_union` 是同一步；tmp↔tmp
不许 import，故此处按消费者要的形状直接给，三行）。 -/
theorem wedgeExh_of_recvJ_of_corner (c : ChainDataGeomParts η xper vl p S gen)
    (hrecvJ : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i)
    (hcorner : ∃ g ∈ ⋃ i, hatOf c.A c.kk vl i,
      dot c.nJ g = c.cJ ∧ dot (det p c.vJ • ((-p.2), p.1)) g = c.cL) :
    ∀ q : ℤ × ℤ, c.cJ ≤ dot c.nJ q →
      c.cL ≤ dot (det p c.vJ • ((-p.2), p.1)) q →
      ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → q ∈ hatOf c.A c.kk vl i := by
  obtain ⟨z₀, hz₀, hJ0, hL0⟩ := hcorner
  intro q hqJ hqL
  have hmem : q ∈ ⋃ i, hatOf c.A c.kk vl i :=
    wedge_sub_of_corner (Nivat.LaneLeafAGenRecVJ.latticeConvex_of_parts c) hz₀ hrecvJ c.rec_p
      hJ0 hL0 c.F.dot_nJ_vJ (Nivat.EnvRefuteOrient.dot_nJ_p_pos_of_parts c)
      (Nivat.EnvRefuteOrient.det_p_vJ_ne_zero_of_parts c) hqJ hqL
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp hmem
  exact ⟨i₀, fun i hi => c.AhatMono i₀ i hi hi₀⟩

/-- **接线收据**：把 `wedgeExh_of_recvJ_of_corner` 直接喂给消费者
`LeafAShellBottomParts.stage_exh_of_wedge_exh`，`hexhW` 那一栏消失，
剩下的前提是 `hwL`（populator 位）＋ `rec_vJ` ＋ `hcorner`。
这条的存在本身就是护栏：若上面那条的类型与 binder 差一个字符，这里就不通过。 -/
theorem stage_exh_of_recvJ_of_corner (c : ChainDataGeomParts η xper vl p S gen)
    (hwL : dot (det p c.vJ • ((-p.2), p.1)) c.w ≤ 0)
    (hrecvJ : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i)
    (hcorner : ∃ g ∈ ⋃ i, hatOf c.A c.kk vl i,
      dot c.nJ g = c.cJ ∧ dot (det p c.vJ • ((-p.2), p.1)) g = c.cL)
    (ε : ℕ) (z : ℤ × ℤ)
    (hz : z ∈ MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → z ∈ ShellMink.shellInter (hatOf c.A c.kk vl i)
      (MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε) c.w :=
  Nivat.LeafAShellBottomParts.stage_exh_of_wedge_exh c hwL
    (wedgeExh_of_recvJ_of_corner c hrecvJ hcorner) ε z hz

/-- **接线收据（终点）**：`ShellFeed` 现在只剩 `henv` ＋ `hwL` ＋ `rec_vJ` ＋ `hcorner`。 -/
theorem shellFeed_of_recvJ_of_corner (c : ChainDataGeomParts η xper vl p S gen)
    (d : Nivat.Colle35.DecompDataZ η)
    (hS : (↑S : Set (ℤ × ℤ)) = (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
    (henv : ∀ ε : ℕ, ∃ i₀ : ℕ, ∀ i, i₀ ≤ i →
      EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf c.A c.kk vl i)
        (MaxEnv.shell (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ ε) c.w))
    (hwL : dot (det p c.vJ • ((-p.2), p.1)) c.w ≤ 0)
    (hrecvJ : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i)
    (hcorner : ∃ g ∈ ⋃ i, hatOf c.A c.kk vl i,
      dot c.nJ g = c.cJ ∧ dot (det p c.vJ • ((-p.2), p.1)) g = c.cL) :
    Nivat.LeafAShellBottomParts.ShellFeed d (⋃ j, hatOf c.A c.kk vl j) c.vJ1 c.nJ c.cJ :=
  Nivat.LeafAShellBottomParts.shellFeed_of_parts_of_envOf_wedgeExh c d hS henv hwL
    (wedgeExh_of_recvJ_of_corner c hrecvJ hcorner)

end Nivat.LeafAShellWedgeCone

#print axioms Nivat.LeafAShellWedgeCone.dot_nL_sub
#print axioms Nivat.LeafAShellWedgeCone.dot_sub_eq
#print axioms Nivat.LeafAShellWedgeCone.cramer_comp
#print axioms Nivat.LeafAShellWedgeCone.wedge_sub_of_corner
#print axioms Nivat.LeafAShellWedgeCone.wedgeExh_of_recvJ_of_corner
#print axioms Nivat.LeafAShellWedgeCone.stage_exh_of_recvJ_of_corner
#print axioms Nivat.LeafAShellWedgeCone.shellFeed_of_recvJ_of_corner
