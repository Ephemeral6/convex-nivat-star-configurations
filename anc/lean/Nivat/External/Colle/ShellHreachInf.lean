/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-leafa-shell
-/
import Nivat.External.Colle.RegionConvex
import Nivat.External.Colle.ShellRegionJ
import Nivat.External.Colle.ShellSubStrip
import Nivat.External.Colle.LaneHole3ConeHlcTWire

/-!
# `hreachInf`：`shellEnv` 的第二个格凸因子，归约到**一个格点**

lane-leafa-shell，2026-09-24。目标是 `tmp/wip/LeafAAssemble.lean` 的 `shellEnv`
（该文件 §`(shellEnv := by sorry)`）所需的 `hlcT`。

## 这一格现在的账

`LaneCdHlc.isLatticeConvexRegion_shellInter`（`ShellSubStrip.lean` §
`isLatticeConvexRegion_shellInter`）把 `hlcT` 拆成两个因子：

1. `IsLatticeConvexRegion (reachSet Â_i w)` —— **本文件不做，主仓已有成品**：
   `LaneShellEnv.isLatticeConvexRegion_reachSet_hatOf_of_mem_E`（`ShellEnvHlcA.lean` § 同名，
   0 sorry），它是 `LaneCdOppEdge.isLatticeConvexRegion_reachSet_dir_of_mem_E`
   （`SweepOppEdge.lean` § 同名）在 `w := dir (-ν_{J+1})` 上的合成。
   ⚠ 它**不是**在合并后的作用域里免费的：判别性前提是 `±ν ∈ E ↑𝒮_φ` 双边，而把 `w` 钉到
   `±dir ν` 上的那条等式是**分支局部**的（ccw `wJ = -(dir νJ1)`，cw `wJ = dir nnextJ`），
   共用 `J`-package 存在式关于 `wJ` 只导出 `dot (-J) wJ < 0`。⟹ 必须在合并前的两支里各调
   一次、把结论当合取支导出（`tmp/wip/LeafAAssemble.lean` 的 `hlcReachW`）；
2. `IsLatticeConvexRegion (reachSet Â_∞ v_{J-1})` —— 就是 `RegionConvex.lean` 的 `hreach`，
   **本文件做的是这一条**。

`ShellSubStrip.lean` § "hlcT decomposes into two sweep-convexity facts" 自己就写着因子 (2)
「is exactly `RegionConvex.lean`'s already isolated `hreach` side condition, with
`EdgeJ1Data.isLatticeConvexRegion_reachSet` as one producer」。

**本文件把因子 (2) 兑现掉，剩一个格点。** `EdgeJ1Data`（`RegionConvex.lean` §
`EdgeJ1Data`）有八个字段，在 `LeafAAssemble.lean` 的调用点上：

| 字段 / binder | 调用点供给 |
|---|---|
| `a₀ := g_J`，`a₀_mem` | `hgJmemT`（`hray 0`） |
| `a₀_on : ⟪n_J, g_J⟫ = c_J` | `set cJ := dot nJ g_J`，`rfl` |
| `nJ1 := -n_{prevJ}`，`dot_nJ1_v` | `hnpvJ1 : ⟪n_{prevJ}, v_{J-1}⟫ = 0` 取负 |
| `nJ1_ne` | `n_{prevJ} ∈ E ↑𝒮_φ` ⟹ `Prim` ⟹ `≠ 0` |
| `support` | `hsupp_prev_U`（`g_J` 是 `n_{prevJ}`-最大 ⟺ `-n_{prevJ}`-最小） |
| `hA` | `hAhatConvU` |
| `hAhalf` | `Set.iUnion_subset hhp_all` |
| `hzero` | `hswept_all`（§2，`SweptClosed` 逐字符展开就是它） |
| `hrec` | `hrecT`（`rec_of_ray hAhatConvU … hray`） |
| `hnJvJ` / `hnJv` / `hvJ` | `hnJvJ` / `hsweep` / `hv_prim` |
| **`prev_mem : g_J - v_{J-1} ∈ Â_∞`** | **§3**，本文件唯一的内容 |

## §3 为什么成立（原文对应）

`prev_mem` 是原文 `scratch/b3_colle2.txt:402` 那句
「`|ϖ ∩ Â_∞| ≥ |w ∩ 𝒮_φ| ≥ 2`」在 `ℓ_{J-1}` 边上的实例：这条边至少有两个格点。
但本文件**不走 `Enveloped` 的面数条款**——那条更贵。走的是更便宜的一条：

* `n_{prevJ} ∈ E Â_i` 本身就蕴含 `faceLen ≥ 1`（`PolyChain.one_le_faceLen`，
  `E` 的定义里 `face` 是 `Nontrivial`），所以边上至少两个格点是**免费**的；
* 缺的只是**方向**：第二个点在 `g_J` 的哪一侧。这由墙定：`g_J` 坐在 `⟪n_J,·⟫ = c_J`
  上而整个 `Â_i` 在 `⟪n_J,·⟫ ≥ c_J` 里（`hhp`），又 `⟪n_J, v_{J-1}⟫ < 0`，
  所以**朝 `+v_{J-1}` 的那一侧会掉到墙下面，不可能有点** ⟹ 第二个点只能是 `g_J - v_{J-1}`。

⟹ 量词上本文件比原文 `:402` **弱**（只要一个点，不要 `≥ |w ∩ 𝒮_φ|`），不是加强。

## 复用而非重造（PROTOCOL §61，写之前也跑）

`Nivat.PolyChain.face_eq_segment` / `one_le_faceLen`、`Nivat.LE2.face_subset`、
`Nivat.ShellRegionJ.dir_nℓ_eq_or_neg_vl`、`Nivat.EdgeJ1Data.isLatticeConvexRegion_reachSet`
全部直接调，本文件不重证任何一步。六个新名字对 `Nivat/` + `tmp/wip/` 的声明头 grep 均 0 命中。

⚠ 本文件**不**主张 `shellEnv` 落地。它只关 `hlcT` 的因子 (2)；`hattain` / `hwedgeF` /
`hD` / 面段供给那几条仍然开着（见 `tmp/wip/lane-leafa-shell-shellenv.lean` §50/§53）。
-/

set_option autoImplicit false

namespace Nivat.LaneLeafAShellHreachInf

open Nivat Nivat.LE2 Nivat.PolyChain Nivat.MaxEnv Nivat.Colle35

variable {T R : Set (ℤ × ℤ)} {nJ vJ1 m gJ : ℤ × ℤ} {cJ : ℤ}

/-! ## §1. `hzero`：`SweptClosed` 逐字符就是它 -/

/-- `EdgeJ1Data.isLatticeConvexRegion_reachSet` 的 `hzero` binder
（`RegionConvex.lean` § `section Main` 的 `variable` 块）由 `SweptClosed`
（`MaximalEnveloped.lean` § `SweptClosed`）直接给：两边都是
「扫到墙上方的点还在集合里」，只差一个 `∩` 的展开。 -/
theorem reachSet_inter_halfPlaneGE_subset_of_swept
    (hsw : Nivat.MaxEnv.SweptClosed T vJ1 nJ cJ) :
    reachSet T vJ1 ∩ Nivat.CK224.halfPlaneGE nJ cJ ⊆ T := by
  rintro z ⟨⟨g, hg, t, rfl⟩, hlev⟩
  exact hsw g hg t hlev

/-! ## §2. `prev_mem`：墙把边的方向定死 -/

/-- **`g_J - v_{J-1} ∈ R`**，只要 `g_J` 在 `R` 的 `m`-面上、`R` 贴着墙 `⟪n_J,·⟫ ≥ c_J`
而 `g_J` 恰在墙上，且 `dir m = ± v_{J-1}`、`⟪n_J, v_{J-1}⟫ < 0`。

面是一条格线段（`face_eq_segment`），`g_J` 落在参数 `t₀`。朝 `+v_{J-1}` 走一步就掉到
`c_J` 以下，与 `hhp` 矛盾 ⟹ 那一侧不可能还有面上的点 ⟹ `t₀` 顶在该侧的端点上；
而 `faceLen ≥ 1`（`one_le_faceLen`，由 `m ∈ E R` 免费），所以另一侧必有一步，
那一步就是 `g_J - v_{J-1}`。两种 `dir m` 取向各走一遍，结论同一条。 -/
theorem sub_vJ1_mem_of_face
    (hfin : R.Finite) (hlc : IsLatticeConvexRegion R) (hmE : m ∈ Nivat.LE2.E R)
    (hgJ : gJ ∈ Nivat.LE2.face R m)
    (hhp : ∀ z ∈ R, cJ ≤ dot nJ z) (hcJ : dot nJ gJ = cJ)
    (hsweep : dot nJ vJ1 < 0)
    (hdir : Nivat.LE2.dir m = vJ1 ∨ Nivat.LE2.dir m = -vJ1) :
    gJ - vJ1 ∈ R := by
  have hseg := Nivat.PolyChain.face_eq_segment hlc hfin hmE
  have hlen1 : 1 ≤ faceLen R m := Nivat.PolyChain.one_le_faceLen hfin hmE
  obtain ⟨t₀, ht₀le, ht₀⟩ : ∃ t : ℕ, t ≤ faceLen R m ∧
      gJ = faceStart R m + (t : ℤ) • Nivat.LE2.dir m := by
    rw [hseg] at hgJ; exact hgJ
  -- 面上参数为 `t` 的点，写成从 `gJ` 出发的形式
  have hpt : ∀ t : ℕ, t ≤ faceLen R m →
      faceStart R m + (t : ℤ) • Nivat.LE2.dir m ∈ R := by
    intro t ht
    refine Nivat.LE2.face_subset R m ?_
    rw [hseg]; exact ⟨t, ht, rfl⟩
  -- 面上参数为 `t` 的点的高度
  have hlevel : ∀ t : ℕ, faceStart R m + (t : ℤ) • Nivat.LE2.dir m
      = gJ + ((t : ℤ) - (t₀ : ℤ)) • Nivat.LE2.dir m := by
    intro t
    rw [ht₀, sub_smul]
    abel
  rcases hdir with hd | hd
  · -- `dir m = vJ1`：`t > t₀` 的点掉到墙下 ⟹ `t₀ = faceLen`，往回走一步
    have htop : t₀ = faceLen R m := by
      by_contra hne
      have hlt : t₀ + 1 ≤ faceLen R m := by omega
      have hmem := hpt (t₀ + 1) hlt
      rw [hlevel (t₀ + 1), hd] at hmem
      have hlev := hhp _ hmem
      rw [Nivat.LE2.dot_add] at hlev
      have hone : ((t₀ : ℤ) + 1 - (t₀ : ℤ)) = 1 := by ring
      rw [show (((t₀ + 1 : ℕ) : ℤ) - (t₀ : ℤ)) = 1 by push_cast; ring,
        one_smul, hcJ] at hlev
      omega
    have hmem := hpt (t₀ - 1) (by omega)
    rw [hlevel (t₀ - 1), hd] at hmem
    have hcast : (((t₀ - 1 : ℕ)) : ℤ) - (t₀ : ℤ) = -1 := by
      have : 1 ≤ t₀ := by omega
      push_cast [Nat.cast_sub this]; ring
    rw [hcast, neg_smul, one_smul] at hmem
    have : gJ + -vJ1 = gJ - vJ1 := by abel
    rwa [this] at hmem
  · -- `dir m = -vJ1`：`t < t₀` 的点掉到墙下 ⟹ `t₀ = 0`，往前走一步
    have hbot : t₀ = 0 := by
      by_contra hne
      have hmem := hpt (t₀ - 1) (by omega)
      rw [hlevel (t₀ - 1), hd] at hmem
      have hlev := hhp _ hmem
      have hcast : (((t₀ - 1 : ℕ)) : ℤ) - (t₀ : ℤ) = -1 := by
        have : 1 ≤ t₀ := by omega
        push_cast [Nat.cast_sub this]; ring
      rw [hcast] at hlev
      rw [Nivat.LE2.dot_add] at hlev
      have hval : dot nJ ((-1 : ℤ) • (-vJ1)) = dot nJ vJ1 := by
        rw [show ((-1 : ℤ) • (-vJ1)) = vJ1 by abel]
      rw [hval, hcJ] at hlev
      omega
    have hmem := hpt 1 (by omega)
    rw [hlevel 1, hd, hbot] at hmem
    have hone : ((1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = 1 := by omega
    rw [hone, one_smul] at hmem
    have : gJ + -vJ1 = gJ - vJ1 := by abel
    rwa [this] at hmem

/-- 同一条，方向前提换成「`m` 本原、`v_{J-1}` 本原、两者正交」——调用点拿到的就是这个形状
（`ShellRegionJ.dir_nℓ_eq_or_neg_vl` 逐字给出那个析取）。 -/
theorem sub_vJ1_mem_of_face_of_perp
    (hfin : R.Finite) (hlc : IsLatticeConvexRegion R) (hmE : m ∈ Nivat.LE2.E R)
    (hgJ : gJ ∈ Nivat.LE2.face R m)
    (hhp : ∀ z ∈ R, cJ ≤ dot nJ z) (hcJ : dot nJ gJ = cJ)
    (hsweep : dot nJ vJ1 < 0)
    (hm_ne : m ≠ 0) (hm_prim : Nivat.LE2.Prim m) (hv_prim : Primitive vJ1)
    (hperp : dot m vJ1 = 0) :
    gJ - vJ1 ∈ R :=
  sub_vJ1_mem_of_face hfin hlc hmE hgJ hhp hcJ hsweep
    (Nivat.ShellRegionJ.dir_nℓ_eq_or_neg_vl hm_ne hm_prim hv_prim hperp)

/-! ## §3. `EdgeJ1Data` 与 `hreachInf` -/

/-- **调用点的 `EdgeJ1Data`**：`a₀ := g_J`，`nJ1 := -n_{prevJ}`。
`support` 那一条是 `hsupp_prev_U` 取负：`g_J` 是 `n_{prevJ}`-最大 ⟺ `-n_{prevJ}`-最小。 -/
def edgeJ1_of_site {nprevJ : ℤ × ℤ}
    (hgJmem : gJ ∈ T) (hcJ : dot nJ gJ = cJ)
    (hprev : gJ - vJ1 ∈ T)
    (hnp_ne : nprevJ ≠ 0) (hnpvJ1 : dot nprevJ vJ1 = 0)
    (hsupp : ∀ z ∈ T, dot nprevJ z ≤ dot nprevJ gJ) :
    Nivat.Colle35.EdgeJ1Data T vJ1 nJ cJ where
  a₀ := gJ
  a₀_mem := hgJmem
  a₀_on := hcJ
  prev_mem := hprev
  nJ1 := -nprevJ
  dot_nJ1_v := by rw [Nivat.LE2.dot_neg_left, hnpvJ1, neg_zero]
  nJ1_ne := neg_ne_zero.mpr hnp_ne
  support := by
    intro g hg
    rw [Nivat.LE2.dot_neg_left, Nivat.LE2.dot_neg_left]
    exact neg_le_neg (hsupp g hg)

/-- **`hreachInf`，全部 binder 显式**：`shellEnv` 的 `hlcT` 第二因子。
结论逐字符是 `LaneCdHlc.isLatticeConvexRegion_shellInter` 的 `hreachInf` 位
（`ShellSubStrip.lean` § `isLatticeConvexRegion_shellInter`）。 -/
theorem isLatticeConvexRegion_reachSet_of_edge {nprevJ vJ : ℤ × ℤ}
    (hgJmem : gJ ∈ T) (hcJ : dot nJ gJ = cJ) (hprev : gJ - vJ1 ∈ T)
    (hnp_ne : nprevJ ≠ 0) (hnpvJ1 : dot nprevJ vJ1 = 0)
    (hsupp : ∀ z ∈ T, dot nprevJ z ≤ dot nprevJ gJ)
    (hA : IsLatticeConvexRegion T)
    (hAhalf : ∀ g ∈ T, cJ ≤ dot nJ g)
    (hsw : Nivat.MaxEnv.SweptClosed T vJ1 nJ cJ)
    (hrec : ∀ g ∈ T, g + vJ ∈ T)
    (hnJvJ : dot nJ vJ = 0) (hsweep : dot nJ vJ1 < 0) (hvJ : vJ ≠ 0) :
    IsLatticeConvexRegion (reachSet T vJ1) :=
  (edgeJ1_of_site hgJmem hcJ hprev hnp_ne hnpvJ1 hsupp).isLatticeConvexRegion_reachSet
    hA hAhalf (reachSet_inter_halfPlaneGE_subset_of_swept hsw) hrec hnJvJ hsweep hvJ

/-- **本文件的交付面**：`prev_mem` 也兑现掉，`hreachInf` 只吃调用点现成的东西。

`gJ ∈ face R m`（`m := n_{prevJ}`、`R := Â_{i₁}` 某个含 `g_J` 的有限阶段）是
`hsupp_prev_all i₁` 的逐字符形状；`hRsub : R ⊆ T` 是 `Set.subset_iUnion`。

**`hnpE` 的出处**（team-lead 三选一，取第一项「指到消费者处哪条 binder」）：
调用点 `tmp/wip/LeafAAssemble.lean` 那条大 `obtain` 的第 15 条合取逐字是
`nprevJ ∈ Nivat.LE2.E (↑d.Sphi : Set (ℤ × ℤ))`，绑成 `hnprevE_S`。把它沿
`E (hatOf A kk vl i) = E (↑𝒮_φ)` 搬到 `R := hatOf A kk vl i₁` 上即得本条，而那条相等由
主仓 `AhatEnv.E_eq_of_enveloped` 作用在 `ShellSubStrip.enveloped_hatOf` 上给出。
⟹ 不是债，是现货；⚠ 这条搬运本 lane **尚未在 Lean 里走过**（读出来的，§55）。 -/
theorem isLatticeConvexRegion_reachSet_of_site {nprevJ vJ : ℤ × ℤ}
    (hRfin : R.Finite) (hRlc : IsLatticeConvexRegion R) (hRsub : R ⊆ T)
    (hnpE : nprevJ ∈ Nivat.LE2.E R)
    (hgJface : gJ ∈ Nivat.LE2.face R nprevJ)
    (hnp_ne : nprevJ ≠ 0) (hnp_prim : Nivat.LE2.Prim nprevJ) (hv_prim : Primitive vJ1)
    (hnpvJ1 : dot nprevJ vJ1 = 0)
    (hgJmem : gJ ∈ T) (hcJ : dot nJ gJ = cJ)
    (hsupp : ∀ z ∈ T, dot nprevJ z ≤ dot nprevJ gJ)
    (hA : IsLatticeConvexRegion T)
    (hAhalf : ∀ g ∈ T, cJ ≤ dot nJ g)
    (hsw : Nivat.MaxEnv.SweptClosed T vJ1 nJ cJ)
    (hrec : ∀ g ∈ T, g + vJ ∈ T)
    (hnJvJ : dot nJ vJ = 0) (hsweep : dot nJ vJ1 < 0) (hvJ : vJ ≠ 0) :
    IsLatticeConvexRegion (reachSet T vJ1) :=
  isLatticeConvexRegion_reachSet_of_edge (vJ := vJ) hgJmem hcJ
    (hRsub (sub_vJ1_mem_of_face_of_perp hRfin hRlc hnpE hgJface
      (fun z hz => hAhalf z (hRsub hz)) hcJ hsweep hnp_ne hnp_prim hv_prim hnpvJ1))
    hnp_ne hnpvJ1 hsupp hA hAhalf hsw hrec hnJvJ hsweep hvJ

/-! ## §4. 端到端：调用点事实 ⟹ `hlcT`

§3 交出的是 `hreachInf`，它是 `tmp/wip/lane-leafa-shell-shellenv.lean` §5 `lcT_of_reach`
的第二个 binder。**本节不重造 `lcT_of_reach`**（§61：那条已存在、0 sorry），只把
「调用点事实 ⟹ `hlcT`」这条合成走完一遍，好处是它和 §1–§3 在**同一个文件**里过内核
——`check1.sh` 看不见 `tmp/wip/` 之间的 import，分在两个文件里就没法机器验证这条接缝。

与 `lcT_of_reach` 的差（PROTOCOL §52）：`lcT_of_reach` 把 `hreachInf` 当 binder **收**下，
本条把它**兑现**掉，只收调用点现货；两者共用的那一步是
`LaneCdHlc.isLatticeConvexRegion_shellInter` 的一次调用，一行。

⚠ `hreachA`（因子 (1)，`reachSet Â_i w` 的格凸性）仍是 binder。**已复核并已在调用点兑现**
（lane-leafa-shell 2026-09-24，第 203 轮）：`tmp/wip/LeafAAssemble.lean` 的共用 `J`-package
存在式现在导出 `hlcReachW : ∀ i, IsLatticeConvexRegion (reachSet (hatOf A kk vl i) wJ)`，
与本条的 `hreachA` 逐字符同形，`check1.sh` EXIT=0。
⚠ 兑现方式与原先的读法**不同**：不是「调用点直接调 `LaneCdOppEdge
.isLatticeConvexRegion_reachSet_dir_of_mem_E` 就免费」——把 `wJ` 钉到 `±dir ν` 的那条等式是
**分支局部**的（ccw `wJ = -(dir νJ1)`，cw `wJ = dir nnextJ`），合并后只剩 `dot (-J) wJ < 0`。
必须在合并前的两支里各调一次 `LaneShellEnv.isLatticeConvexRegion_reachSet_hatOf_of_mem_E`
（`ShellEnvHlcA.lean` § 同名）、把**结论**当合取支导出。原先「lane-leafa-gen 报、本 lane
未复核」那句作废。 -/

/-- **`hlcT`，从调用点事实一步到位。**  结论逐字符是
`tmp/wip/lane-leafa-shell-shellenv.lean` § `shellEnv_of_positive_class` /
§ `shellEnv_of_faceEndpoints` 的 `hlcT` binder（`∀ i, i₀ ≤ i → IsLatticeConvexRegion (shellT …)`）。

合成那一步**不自己做**：直接调主仓的 `LaneHole3ConeHlcTWire.hlcT_of_reach`
（`LaneHole3ConeHlcTWire.lean` § "§1. The bridge"），本条只补它的 `hreachInf` 位。
⟹ 主仓里这条合成只有一份。

`hreachA` 之外的每一条，在 `tmp/wip/LeafAAssemble.lean` 的 `shellEnv` 调用点都是现货
——见本文件抬头的对照表。⚠ 那张表是**读**出来的，本 lane 尚未在 Lean 里实例化过。 -/
theorem hlcT_of_site {Afam : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl w vJ : ℤ × ℤ} {nprevJ : ℤ × ℤ} {ε i₀ : ℕ}
    (hreachA : ∀ i, IsLatticeConvexRegion (reachSet (hatOf Afam kk vl i) w))
    (hRfin : R.Finite) (hRlc : IsLatticeConvexRegion R)
    (hRsub : R ⊆ ⋃ j, hatOf Afam kk vl j)
    (hnpE : nprevJ ∈ Nivat.LE2.E R)
    (hgJface : gJ ∈ Nivat.LE2.face R nprevJ)
    (hnp_ne : nprevJ ≠ 0) (hnp_prim : Nivat.LE2.Prim nprevJ) (hv_prim : Primitive vJ1)
    (hnpvJ1 : dot nprevJ vJ1 = 0)
    (hgJmem : gJ ∈ ⋃ j, hatOf Afam kk vl j) (hcJ : dot nJ gJ = cJ)
    (hsupp : ∀ z ∈ ⋃ j, hatOf Afam kk vl j, dot nprevJ z ≤ dot nprevJ gJ)
    (hA : IsLatticeConvexRegion (⋃ j, hatOf Afam kk vl j))
    (hAhalf : ∀ g ∈ ⋃ j, hatOf Afam kk vl j, cJ ≤ dot nJ g)
    (hsw : Nivat.MaxEnv.SweptClosed (⋃ j, hatOf Afam kk vl j) vJ1 nJ cJ)
    (hrec : ∀ g ∈ ⋃ j, hatOf Afam kk vl j, g + vJ ∈ ⋃ j, hatOf Afam kk vl j)
    (hnJvJ : dot nJ vJ = 0) (hsweep : dot nJ vJ1 < 0) (hvJ : vJ ≠ 0) :
    ∀ i, i₀ ≤ i →
      IsLatticeConvexRegion (Nivat.LaneCdSite.shellT Afam kk vl vJ1 nJ w cJ ε i) :=
  Nivat.LaneHole3ConeHlcTWire.hlcT_of_reach (i₀ := i₀) (ε := ε) hreachA
    (isLatticeConvexRegion_reachSet_of_site (vJ := vJ) hRfin hRlc hRsub hnpE hgJface
      hnp_ne hnp_prim hv_prim hnpvJ1 hgJmem hcJ hsupp hA hAhalf hsw hrec hnJvJ hsweep hvJ)

/-! ## §5. 朝向盲：一条覆盖 `cw` 与 `ccw` 两个符号

主仓 `LaneHole3ConeHlcTWire.hreachInf_of_pinned_cw`（`LaneHole3ConeHlcTWire.lean` §2）把
`v_{J-1}` 的符号钉死成 `hvJ1 : vJ1 = -dir nprevJ`（**cw**），`ccw` 镜像另起一条
（该文件 §「On the `:517` clipping」上方的说明段指向 `tmp/wip/lane-shellenv-edgeJ1.lean` 的
`ahatUnion_reachSet_latticeConvex_of_pinned_ccw`，**未落主仓**）。

§3 那条的方向前提是 `dot nprevJ vJ1 = 0` ＋ `Primitive vJ1`，**不含符号**
（§2 的 `dir_nℓ_eq_or_neg_vl` 把两个取向各走了一遍）。本节把两个符号各实例化一次，
给出「一条顶两条」的内核见证；两条的证明体逐字符相同，只差 `Prim.neg` 那一步。

⚠ 本节**不新增数学**，只是 §3 的两次实例化；不引原文，故无 `b3_colle2.txt:NNN`。 -/

/-- **`ccw` 分支**：`v_{J-1} = dir n_{prevJ}`。 -/
theorem isLatticeConvexRegion_reachSet_of_site_ccw {nprevJ vJ : ℤ × ℤ}
    (hRfin : R.Finite) (hRlc : IsLatticeConvexRegion R) (hRsub : R ⊆ T)
    (hnpE : nprevJ ∈ Nivat.LE2.E R)
    (hgJface : gJ ∈ Nivat.LE2.face R nprevJ)
    (hnp_ne : nprevJ ≠ 0) (hnp_prim : Nivat.LE2.Prim nprevJ)
    (hvJ1 : vJ1 = Nivat.LE2.dir nprevJ)
    (hgJmem : gJ ∈ T) (hcJ : dot nJ gJ = cJ)
    (hsupp : ∀ z ∈ T, dot nprevJ z ≤ dot nprevJ gJ)
    (hA : IsLatticeConvexRegion T)
    (hAhalf : ∀ g ∈ T, cJ ≤ dot nJ g)
    (hsw : Nivat.MaxEnv.SweptClosed T vJ1 nJ cJ)
    (hrec : ∀ g ∈ T, g + vJ ∈ T)
    (hnJvJ : dot nJ vJ = 0) (hsweep : dot nJ vJ1 < 0) (hvJ : vJ ≠ 0) :
    IsLatticeConvexRegion (reachSet T vJ1) := by
  subst hvJ1
  exact isLatticeConvexRegion_reachSet_of_site (vJ := vJ) hRfin hRlc hRsub hnpE hgJface
    hnp_ne hnp_prim (Nivat.CK224.prim_dir hnp_prim) (Nivat.LE2.dot_dir nprevJ)
    hgJmem hcJ hsupp hA hAhalf hsw hrec hnJvJ hsweep hvJ

/-- **`cw` 分支**：`v_{J-1} = -dir n_{prevJ}`——这正是主仓 `hreachInf_of_pinned_cw` 钉死的那个
符号，所以本条与它的覆盖面相同，而 `ccw` 那条是主仓当前没有的。 -/
theorem isLatticeConvexRegion_reachSet_of_site_cw {nprevJ vJ : ℤ × ℤ}
    (hRfin : R.Finite) (hRlc : IsLatticeConvexRegion R) (hRsub : R ⊆ T)
    (hnpE : nprevJ ∈ Nivat.LE2.E R)
    (hgJface : gJ ∈ Nivat.LE2.face R nprevJ)
    (hnp_ne : nprevJ ≠ 0) (hnp_prim : Nivat.LE2.Prim nprevJ)
    (hvJ1 : vJ1 = -(Nivat.LE2.dir nprevJ))
    (hgJmem : gJ ∈ T) (hcJ : dot nJ gJ = cJ)
    (hsupp : ∀ z ∈ T, dot nprevJ z ≤ dot nprevJ gJ)
    (hA : IsLatticeConvexRegion T)
    (hAhalf : ∀ g ∈ T, cJ ≤ dot nJ g)
    (hsw : Nivat.MaxEnv.SweptClosed T vJ1 nJ cJ)
    (hrec : ∀ g ∈ T, g + vJ ∈ T)
    (hnJvJ : dot nJ vJ = 0) (hsweep : dot nJ vJ1 < 0) (hvJ : vJ ≠ 0) :
    IsLatticeConvexRegion (reachSet T vJ1) := by
  subst hvJ1
  have hprim : Primitive (-(Nivat.LE2.dir nprevJ)) :=
    Nivat.LE2.prim_iff_primitive.mp
      (Nivat.LE2.prim_iff_primitive.mpr (Nivat.CK224.prim_dir hnp_prim)).neg
  have hperp : dot nprevJ (-(Nivat.LE2.dir nprevJ)) = 0 := by
    simp only [Nivat.LE2.dot, Nivat.LE2.dir, Prod.neg_mk]
    ring
  exact isLatticeConvexRegion_reachSet_of_site (vJ := vJ) hRfin hRlc hRsub hnpE hgJface
    hnp_ne hnp_prim hprim hperp
    hgJmem hcJ hsupp hA hAhalf hsw hrec hnJvJ hsweep hvJ

end Nivat.LaneLeafAShellHreachInf

#print axioms Nivat.LaneLeafAShellHreachInf.reachSet_inter_halfPlaneGE_subset_of_swept
#print axioms Nivat.LaneLeafAShellHreachInf.sub_vJ1_mem_of_face
#print axioms Nivat.LaneLeafAShellHreachInf.sub_vJ1_mem_of_face_of_perp
#print axioms Nivat.LaneLeafAShellHreachInf.isLatticeConvexRegion_reachSet_of_edge
#print axioms Nivat.LaneLeafAShellHreachInf.isLatticeConvexRegion_reachSet_of_site

#print axioms Nivat.LaneLeafAShellHreachInf.hlcT_of_site

#print axioms Nivat.LaneLeafAShellHreachInf.isLatticeConvexRegion_reachSet_of_site_ccw
#print axioms Nivat.LaneLeafAShellHreachInf.isLatticeConvexRegion_reachSet_of_site_cw

