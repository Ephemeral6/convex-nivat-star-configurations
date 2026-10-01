/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainPartsFeed
import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.ChainAssembleInter

set_option autoImplicit false

namespace Nivat.ChainAsm.Aparts

open Nivat.Colle35

variable {α : Type*}

/-- Bridge from `ChainDataGeomParts` to `ChainDataGeom`. The 25th premise `rec_vJ` is taken
as an explicit parameter.

⚠ **2026-09-25 订正（集成者）：本段原有的推导建议已作废，且该义务现已关闭。**

原文曾写「`rec_vJ` should be derivable from `rec_vJ_of_exists_chainData_layer` (which yields
`IsLatticeConvexRegion (⋃ i, hatOf A kk vl i)`) plus an extraction step … but that extraction
is not connected here」。两句都过期：

1. ⛔ **那条推导路径为假。** `IsLatticeConvexRegion R`（`Section8/HalfPlane.lean` 的
   `IsLatticeConvexRegion`）＝ `∃ C, Convex ℝ C ∧ IsClosed C ∧ R = toReal ⁻¹' C`，
   **有界集照样满足**（取 `R = {(0,0)}`）⟹ 格凸性**单独**不蕴含对 `+vJ` 的封闭性。
2. ✅ **但该义务已被无条件关闭**，走的是另一条路：`rec_vJ_of_parts`
   （`RecVJComb` 的姊妹文件 `RecVJFromParts.lean`，namespace `Nivat.LaneLeafAGenRecVJ`）
   由 `rec_vJ_of_bottom`（`ItemII.lean:766`）产出，后者要的是格凸性**加五条**：
   `hsweep` / `hhp` / `hswept` / `F.dot_nJ_vJ` / **`bottom`**（结构字段，`ChainPartsFeed.lean:242`）。
   有界集 `{(0,0)}` 兑现不了 `bottom`，故第 1 条的反例对这条路**无效**（PROTOCOL §110.4）。
   缺的那个格凸性 binder 由 `latticeConvex_of_parts` 从 `c.maxA` / `c.hfin` / `c.AhatMono`
   经 `latticeConvex_iUnion_hatOf`（`ChainAssemble.lean:339`）产出。

⟹ 本 `def` 的第 25 个显式参数**不再是欠账**：`toChainDataGeom_of_parts` 已把它填成全函数。
本参数保留为显式形，是为了让 `RecVJComb.lean` 的第二条独立路径也能喂进来（两条互为签名护栏）。
原文对应：`b3_colle2.txt:506`「two semi-infinite edges, one parallel to `ℓ` and the other to `ℓ_J`」
——`rec_p` 是 `ℓ` 侧（`x_per` 周期性给），`rec_vJ` 是 `ℓ_J` 侧（`:500` 严格增长 ＋ `:498` 取子列，
其 Lean 凝结形就是字段 `bottom`）。 -/
noncomputable def ChainDataGeomParts.toChainDataGeom {η xper : Config α}
    {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (c : ChainDataGeomParts η xper vl p S gen)
    (rec_vJ : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i) :
    ChainDataGeom η xper vl p S gen :=
  ChainDataGeom.ofPartsInter η xper vl p S gen
    (Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ)))
    c.B c.A c.u c.kk
    c.envShift
    c.envB
    c.maxA
    c.subBA
    c.subAB
    c.AhatMono
    c.vJ1 c.nJ c.cJ
    c.hsweep
    c.hfin
    c.hhp
    c.hswept
    c.ahat_nonempty
    c.w c.hsweepW
    c.I₀
    c.escapeW
    c.shellSubStrip
    c.shellEnv
    c.fillCover
    c.vJ c.F
    c.gen_eq
    c.vJ_prim c.nJ_prim
    c.bottom
    c.rec_p
    c.dot_nJ_p
    rec_vJ
    c.cL
    c.ahat_halfPlane_L
    c.ahat_attained_L
    c.nfp_L

/-- The `Env` field of the constructed `ChainDataGeom` matches the intended environment. -/
theorem toChainDataGeom_Env {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (c : ChainDataGeomParts η xper vl p S gen)
    (rec_vJ : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i) :
    (c.toChainDataGeom rec_vJ).toChainData.Env = Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ)) :=
  rfl

end Nivat.ChainAsm.Aparts

#print axioms Nivat.ChainAsm.Aparts.ChainDataGeomParts.toChainDataGeom
#print axioms Nivat.ChainAsm.Aparts.toChainDataGeom_Env
