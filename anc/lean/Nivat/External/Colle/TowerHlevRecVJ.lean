/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-tower-hlev
-/
import Nivat.External.Colle.ItemII
import Nivat.External.Colle.ChainAssemble

/-!
# `rec_vJ` 对 `bottom` 的归约：只吃第 1、2 合取，**第 3、4 合取不参与**

Lane `lane-tower-hlev`，第 227 轮（2026-09-25）。0 `sorry`。
`import` 两条（与 `grep -n "^import"` 逐字一致，`PROTOCOL §57`）：`ItemII`、`ChainAssemble`。
不 `import` `RegionSteps` / `ColleRegion` / `Case2WindowProbe` / `NfpLPreamble`。

⚠ **本文件设计上无证明项消费者，是 `rec_vJ` 这一格「定价」的回归护栏**
（(C) 类，`PROTOCOL §111.1`）。消费者是人：谁要重新估 `bottom` 这条字段的代价，
先看 §1 的签名。若 `Nivat.Colle35.rec_vJ_of_bottom`（`ItemII.lean`）的 binder 表变了，
§3 的 `rec_vJ_of_bottom_via₁₂` 会当场编不过。

## 订正：第 3、4 合取 `rec_vJ` 一条也不用

`Nivat.Colle35.rec_vJ_of_bottom`（`ItemII.lean`）的证明体第一行逐字是

```lean
obtain ⟨z₀, L, hz₀, hline, -, -⟩ := bottom 0
```

—— 两个 `-` 就是第 3、4 合取，当场丢掉；而且 `ε` 只在 `0` 处用一次。
⟹ `rec_vJ` 欠的是 **`bottom 0` 的前两个合取**，不是「1–2 已有、3–4 挂着」。

第 3、4 合取有**别的**消费者，与 `rec_vJ` 无关：`Nivat.ChainGeom` 里同时取 `hstab`
与 `hsplit` 的那一处，以及 `RegionClaim411` 里取 `hsplit` 的那一处。
把它们记在 `rec_vJ` 名下会让 `rec_vJ` 这一格看起来比实际贵——那正是 `PROTOCOL §111`
的第三形态（merge），分子分母同时少一。

本文件把这件事写成签名：`rec_vJ_of_bottom₁₂` 的 binder 表里**没有**第 3、4 合取，
也没有 `∀ ε`——只有 `ε = 0` 的那一条实例。

## 原文对应

`b3_colle2.txt:500`（`R_i` 沿 `ℓ_J` 方向严格增长）＋ `:498`（取子列），
其 Lean 凝结形是 `ChainDataGeomParts.bottom`（`ChainPartsFeed.lean`）。
`rec_vJ` 本身是 `:506`「two semi-infinite edges … the other parallel to `ℓ_J`」的 `ℓ_J` 侧。

## 与 `w` 裁决的关系（`w := −v⃗_{ℓ_{J+1}}`，横截）

本文件一个字都不碰 `w`。`rec_vJ` 侧只出现 `vJ1`、`vJ`、`nJ`，
而 `NOTATION.md`（内容锚：`vJ1` / `nJ` / `nprevJ` 那节）已把 `vJ1 := v⃗_{ℓ_{J−1}}` 与
`w := −v⃗_{ℓ_{J+1}}` 判成两个不同对象（下标差 2）。⟹ `w` 怎么裁都不影响本文件。
-/

set_option autoImplicit false

namespace Nivat.LaneTowerHlevRecVJ

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35

/-! ## §1  归约本体：只要 `bottom 0` 的前两个合取 -/

/-- ⭐ **`rec_vJ` ⟸ `bottom 0` 的前两个合取。**
与 `Nivat.Colle35.rec_vJ_of_bottom`（`ItemII.lean`）相比，binder 表里少了：`∀ ε` 的量词、
第 3 合取（`∀ b ∈ S, …`，连带整个 `S`）、第 4 合取（`shellInf` 的分层，连带整个 `shellInf`）。
其余五条（`hconv` / `hd` / `hR` / `hswept` / `hvJ`）逐字不动。

⟹ 这是**严格更弱的前提**；§3 的 `rec_vJ_of_bottom_via₁₂` 是「新形不比旧形弱」那一半的
内核见证，另一半（「新形真的更少」）不是命题，就是本条的签名本身。 -/
theorem rec_vJ_of_bottom₁₂ {R : Set (ℤ × ℤ)} {vJ1 nJ vJ : ℤ × ℤ} {cJ : ℤ}
    (hconv : IsLatticeConvexRegion R)
    (hd : dot nJ vJ1 < 0) (hR : ∀ g ∈ R, cJ ≤ dot nJ g)
    (hswept : MaxEnv.SweptClosed R vJ1 nJ cJ) (hvJ : dot nJ vJ = 0)
    (hbot : ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - 1 ∧
      ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet R vJ1) :
    ∀ g ∈ R, g + vJ ∈ R := by
  obtain ⟨z₀, L, hz₀, hline⟩ := hbot
  exact rec_of_ray hconv (ray_of_bottom_swept hd hR hswept hz₀ hvJ hline)

/-- **`hd` 的整数等式形。**若 `dot nJ vJ1 = -1`，`hd : dot nJ vJ1 < 0` 白送。
本条只做这一步换算，**不**主张 `dot nJ vJ1 = -1` 成立。

⚠ **2026-09-25 记账（集成者订正，本 lane 未独立复核，`PROTOCOL §51`）**：
`dot nJ vJ1 = -1` **不能**从 `dot nJ vJ1 ≠ -2` 得到（不排除 `-3`）——那条旧账已死。
当前登记的真入口是 `det vJ vJ1 = ±1`（已派 lane-env-refute）。
从 `det vJ vJ1 = ±1` 到本条的 `hd1` 之间还差一步换算（`nJ ⟂ vJ` ＋ 两者本原
⟹ `nJ = ±perp vJ`，再用 `Nivat.ColleReg.dot_perp` 与 `hsweep` 定符号）；
那一步**本文件没有**，也没有被派给本 lane。写这句是为了不让本条被读成
「`= -1` 已经有产者」（`PROTOCOL §40` 的反向形态）。

⚠ 另记：`dot nJ vJ1 = -1` 与被禁令点名的 `⟪n_J, w⟫ = −1` **不是同一条**
（`w ≠ vJ1`，见 `NOTATION.md` 的 `vJ1` / `nJ` / `nprevJ` 那节，下标差 2）；
本条对两者都不作存在性主张。 -/
theorem rec_vJ_of_bottom₁₂_of_eq_neg_one {R : Set (ℤ × ℤ)} {vJ1 nJ vJ : ℤ × ℤ} {cJ : ℤ}
    (hconv : IsLatticeConvexRegion R)
    (hd1 : dot nJ vJ1 = -1) (hR : ∀ g ∈ R, cJ ≤ dot nJ g)
    (hswept : MaxEnv.SweptClosed R vJ1 nJ cJ) (hvJ : dot nJ vJ = 0)
    (hbot : ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - 1 ∧
      ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet R vJ1) :
    ∀ g ∈ R, g + vJ ∈ R :=
  rec_vJ_of_bottom₁₂ hconv (by omega) hR hswept hvJ hbot

/-! ## §2  链侧形：直接产出 `rec_vJ` 槽位 -/

variable {α : Type*}

/-- **链侧形。**前提逐条是 `ChainAsm.Aparts.ChainDataGeomParts`（`ChainPartsFeed.lean`）
的同名字段（`maxA` / `hfin` / `AhatMono` / `hsweep` / `hhp` / `hswept`，外加
`F.dot_nJ_vJ` 给的 `hvJ`），再加 `bottom 0` 的前两个合取；结论逐字是
`ChainDataGeomParts.toChainDataGeom`（`PartsToGeom.lean`）的第 25 个显式形参。

`Env` 在这里仍留成形参 ＋ `hEnv`，因为本条也要服务 `ChainDataGeom.ofParts` 那个
更泛的签名；`ChainDataGeomParts` 侧取 `hEnv := rfl`。 -/
theorem rec_vJ_of_parts_bottom₁₂
    (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i))
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    {vJ1 nJ vJ : ℤ × ℤ} {cJ : ℤ}
    (hsweep : dot nJ vJ1 < 0)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hswept : MaxEnv.SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (hvJ : dot nJ vJ = 0)
    (hbot : ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - 1 ∧
      ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) vJ1) :
    ∀ g ∈ ⋃ i, hatOf A kk vl i, g + vJ ∈ ⋃ i, hatOf A kk vl i :=
  rec_vJ_of_bottom₁₂
    (latticeConvex_iUnion_hatOf η xper vl S Env B A u kk hEnv maxA hfin AhatMono)
    hsweep (fun _ hg => Set.iUnion_subset hhp hg) hswept hvJ hbot

/-! ## §3  「新形不比旧形弱」的内核见证

旧形 `rec_vJ_of_bottom` 的 `bottom` binder 蕴含新形的 `hbot`（取 `ε = 0`，丢后两个合取），
所以任何现在能用旧形的地方都能用新形。 -/

/-- 旧形的 `bottom` binder ⟹ 新形的 `hbot`。 -/
theorem bottom₁₂_of_bottom {R : Set (ℤ × ℤ)} {vJ1 nJ vJ a : ℤ × ℤ} {cJ : ℤ}
    {S : Finset (ℤ × ℤ)} {shellInf : ℕ → Set (ℤ × ℤ)}
    (bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet R vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet R vJ1) ∧
      (∀ z ∈ shellInf (ε + 1), z ∈ shellInf ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ)) :
    ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - 1 ∧
      ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet R vJ1 := by
  obtain ⟨z₀, L, hz₀, hline, -, -⟩ := bottom 0
  simp only [Nat.cast_zero, sub_zero] at hz₀
  exact ⟨z₀, L, hz₀, hline⟩

/-- **替换检查**：拿旧形**整张** binder 表，只经新形交出 `rec_vJ`。
⟹ 凡是旧形能用的地方新形都能用。

⚠ 这里**不**写「两个证明项相等」那种等式：`∀ g ∈ R, g + vJ ∈ R` 是 `Prop`，
证明无关性使任何这样的等式自动 `rfl`，它零信息（`PROTOCOL §79`：自洽的回测不证明覆盖率）。
真正承载内容的是 §1 的**签名**——第 3、4 合取在那里根本没出现。 -/
theorem rec_vJ_of_bottom_via₁₂ {R : Set (ℤ × ℤ)} {vJ1 nJ vJ a : ℤ × ℤ} {cJ : ℤ}
    {S : Finset (ℤ × ℤ)} {shellInf : ℕ → Set (ℤ × ℤ)}
    (hconv : IsLatticeConvexRegion R)
    (hd : dot nJ vJ1 < 0) (hR : ∀ g ∈ R, cJ ≤ dot nJ g)
    (hswept : MaxEnv.SweptClosed R vJ1 nJ cJ) (hvJ : dot nJ vJ = 0)
    (bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet R vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet R vJ1) ∧
      (∀ z ∈ shellInf (ε + 1), z ∈ shellInf ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ)) :
    ∀ g ∈ R, g + vJ ∈ R :=
  rec_vJ_of_bottom₁₂ hconv hd hR hswept hvJ (bottom₁₂_of_bottom bottom)

end Nivat.LaneTowerHlevRecVJ

#print axioms Nivat.LaneTowerHlevRecVJ.rec_vJ_of_bottom₁₂
#print axioms Nivat.LaneTowerHlevRecVJ.rec_vJ_of_bottom₁₂_of_eq_neg_one
#print axioms Nivat.LaneTowerHlevRecVJ.rec_vJ_of_parts_bottom₁₂
#print axioms Nivat.LaneTowerHlevRecVJ.bottom₁₂_of_bottom
#print axioms Nivat.LaneTowerHlevRecVJ.rec_vJ_of_bottom_via₁₂
