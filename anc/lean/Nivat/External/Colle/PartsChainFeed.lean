/-
# 洞 1 的链半边：从 `exists_chainData` 自己的 binder 直接产出 `ChainDataGeomParts` 的链侧字段

**这个文件回答的是一个具体的会计问题**，不是一条新数学。

`RegionSteps.exists_chainData`（`RegionSteps.lean`，`sorry` 就在它的 `by` 之后）要的是一个
`ChainDataGeom`；`toChainDataGeom_of_parts`（`RecVJFromParts.lean`）说只要有一个
`ChainDataGeomParts`（`ChainPartsFeed.lean`）就够。于是问题变成「那 37 个字段各欠多少」
（37 是内核 `getStructureFields` 的读数，口径与订正见 `ChainPartsFeed.lean` 的
「字段总数的计数口径」一条；⛔ 别用正则数，`I₀` 的下标不在 ASCII 里）。

## 本文件证的事

`ChainDataGeomParts` 的**链侧十条**——`B` `A` `u` `kk` `envShift` `envB` `maxA` `subBA`
`subAB` `AhatMono`，外加 `hfin`（Parts 里是 `hatOf` 形）与 `kk` 单调、`halign`——
**在 `exists_chainData` 现有的 binder 下全部免费，不欠任何新前提**。

链条是现成的、都在主仓里：

* `Nivat.ItemIIFeed.nonempty_itemIIRecursionData_of_chainData_binders`（`ItemIIFeed.lean`）
  只吃 `exists_chainData` 签名里已有的 binder，产出 `ItemIIRecursionData`；
* `ItemIIRecursionData`（`ItemIIRecursion.lean` 的 `structure`）的字段表里
  **最后一条就是 `AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j`**，
  与 Parts 的同名字段逐字符相同；
* `envShift` 由 `Nivat.Colle35.envOf_shift_mem`（`ChainMax.lean`）给出，与链无关；
* Parts 的 `hfin` 是 `hatOf` 形，由 `Nivat.LeafAItemII.finite_hatOf`（`LeafAItemII.lean`）
  从 `ItemIIRecursionData.hfin` 转过来。

## ⚠ 由此**订正**两条本仓里流传的读法（PROTOCOL §15 口径）

**(1) `PartsReindex.lean` 的「残余是 `habs` ＋ `hkk` ＋ `halign`」过时了。** 那份读法假定
`AhatMono` 拿不到、必须靠子列重标定（`LeafAItemII.exists_subseq_ahatMono_of_endpoint_shift`）
去换，于是并集变小、`∃ g ∈ 并集` 型字段要靠 `habs` 补回来。**但 `AhatMono` 根本不用换**：
`exists_normalised_chain`（`ChainKK.lean`）的结论最后一个合取支就把它交出来了
（`ItemIIRecursion.exists_itemII_recursion` 的 `obtain` 里那个 `AhatMono` 即是）。
⟹ 重标定路线对洞 1 **不必要**；`PartsReindex.lean` 的五条定理仍然为真、仍可用，但它
文首那段「洞 1 在重标定路线下的残余」只是**那条路线**的账，不是洞 1 的账。

**(2) 洞 1 的真残余是几何半边，不是链半边。** `ItemIIRecursion.lean` §2 的 docstring
自己就写着「**What's not here**: the shell block, `bottom`, `fill`, `rec_p`」。按 Parts 的
字段表逐行对照，欠的恰好是**其余 26 个字段**：`vJ1` `nJ` `cJ` `hsweep` `hhp` `hswept`
`ahat_nonempty` `w` `hsweepW` `I₀` `escapeW` `shellSubStrip` `shellEnv` `fillCover` `vJ` `F`
`gen_eq` `vJ_prim` `nJ_prim` `bottom` `rec_p` `dot_nJ_p` `cL` `ahat_halfPlane_L`
`ahat_attained_L` `nfp_L`（11 个链侧字段 ＋ 这 26 个 ＝ 内核报的 37）。
这些全部锚在 `b3_colle2.txt:440-520`（Lemma 3.5 与 `(ℓ, ℓ_J)`-region），**一条都不锚在
`:466-504` 的递归里**——这就是为什么链侧再深推也不动闸门。

⛔ 本文件**不产出** `ChainDataGeomParts`，也不主张洞 1 只欠上面那 25 条中的某几条。
它证的就是签名里写的那一条：链侧十三项可从现有 binder 同时兑现。硬规矩 1 的闸门不因本文件移动。
-/
import Nivat.External.Colle.ItemIIFeed
import Nivat.External.Colle.LeafAItemII
import Nivat.External.Colle.ChainPartsFeed

namespace Nivat.PartsChainFeed

open Nivat Nivat.LE2 Nivat.Colle35

/-- **`ChainDataGeomParts` 的链侧字段，从 `exists_chainData` 的 binder 一次性兑现。**

前提表与 `Nivat.ItemIIFeed.nonempty_itemIIRecursionData_of_chainData_binders`
（`ItemIIFeed.lean`）**逐字符相同**——即 `RegionSteps.exists_chainData` 签名里已有的那些
（`nℓ` / `cz` 由该签名的 `hpartner` 拆出，`hnℓ_prim` / `hnℓ_perp` 是 `hpartner` 的两个合取支；
⛔ `0 < det nℓ vl` 不进，第 179 轮红线）。

结论的十三个合取支按 `ChainDataGeomParts`（`ChainPartsFeed.lean` 的 `structure`）的字段
**原样**书写，顺序也照字段表：`envShift` `envB` `maxA` `subBA` `subAB` `AhatMono` `hfin`，
再加 `kk` 单调与 `:488` 的端点对齐（后两条不是 Parts 的字段，但是几何侧多条义务的输入，
故一并导出）。 -/
theorem exists_parts_chain_half {ξ xper : Config ℤ}
    (d : DecompDataZ ξ) {ℓ nℓ vl : ℤ × ℤ} (cz : ℤ)
    (hxper : xper ∈ orbitClosure ξ)
    (hvl_ne : vl ≠ 0) (hvl_prim : Primitive vl)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hdet_ℓ : dot ℓ vl = 0)
    (hnℓ_prim : Primitive nℓ) (hnℓ_perp : dot nℓ vl = 0)
    (hcase2 : Nivat.ColleReg.Case2 ξ xper d.toDecompData.Sphi vl) :
    ∃ (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ) (g₁ : ℤ × ℤ),
      (∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)),
          EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) T →
          EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) {z | z + v ∈ T}) ∧
      (∀ i, EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) (B i)) ∧
      (∀ i, IsMaxEnvIn (EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
          (canonA ξ xper vl B u i) (A i)) ∧
      (∀ i, B i ⊆ A i) ∧
      (∀ i, A i ⊆ B (i + 1)) ∧
      (∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) ∧
      (∀ i, (hatOf A kk vl i).Finite) ∧
      (∀ i j, i ≤ j → kk i ≤ kk j) ∧
      (∀ i, IsGreatest
          {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) := by
  obtain ⟨rd⟩ :=
    Nivat.ItemIIFeed.nonempty_itemIIRecursionData_of_chainData_binders d cz hxper hvl_ne
      hvl_prim hℓ_nel hℓ_pos hℓ_neg hdet_ℓ hnℓ_prim hnℓ_perp hcase2
  exact ⟨rd.B, rd.A, rd.u, rd.kk, rd.g₁,
    fun v T hT => Nivat.Colle35.envOf_shift_mem _ v T hT,
    rd.envB, rd.maxA, rd.subBA, rd.subAB, rd.AhatMono,
    fun i => Nivat.LeafAItemII.finite_hatOf (rd.hfin i),
    rd.kk_mono, rd.halign⟩

#print axioms Nivat.PartsChainFeed.exists_parts_chain_half

end Nivat.PartsChainFeed
