/-
# 洞 1 的重标定接线（`ChainDataGeomParts` 在子列下的行为）

**为什么有这个文件。** `LeafAItemII.lean` 的模块 docstring 末尾逐字写着：

> ⚠ **What this does not do.**  It does not produce a chain.  It converts the debt
> "`AhatMono` for the chain the recursion builds" into "the consumer must accept a re-indexed
> chain", and §2 below discharges that conversion for every other chain-side binder
> (`envB`, `maxA`, `subBA`, `subAB`, `ItemII`, `Exhausts`, `hfin`, `hhp`).  `ChainDataGeomParts`
> (`ChainPartsFeed.lean`) is the consumer; **wiring it is the integrator's.**

本文件就是那条接线，**并且同时把那句话的射程钉死**——见下面的「⚠ 射程订正」。

## `hatOf` 在子列下是 `rfl`

`hatOf A kk vl i = {z | z + (kk i : ℤ) • vl ∈ A i}`（`ChainMax.lean`，按 §85 用标识符名定位）
只透过 `A i` / `kk i` 依赖 `i`。⟹ 把 `A`、`kk` 同时换成 `A ∘ σ`、`kk ∘ σ`，第 `i` 项**逐字**
就是原链的第 `σ i` 项：`hatOf_comp` 是 `rfl`。这条把「重标定」从一件要逐字段重证的事
降成「把下标换成 `σ i`」。

## ⚠ 射程订正（集成者 2026-09-25 亲读字段表）

`LeafAItemII` 那句「§2 discharges every other chain-side binder」列的八条
（`envB` `maxA` `subBA` `subAB` `ItemII` `Exhausts` `hfin` `hhp`）**全是逐点 `∀ i` 型的**。
`ChainDataGeomParts`（`ChainPartsFeed.lean` 的 `structure`）的字段表里还有一类它**没提**：
**以 `⋃ i, hatOf A kk vl i` 整体为主语的字段**。按 `structure` 逐行核对，这类是

* `hswept`、`ahat_nonempty`、`rec_p`、`ahat_attained_L`、`nfp_L`、`bottom`
  （`bottom` 的 `∃ z₀`），以及 shell 四条 `escapeW` / `shellSubStrip` / `shellEnv` / `fillCover`。

**为什么它们不随逐点字段一起免费**：子列的并集**会变小**——

    ⋃ i, hatOf (A ∘ σ) (kk ∘ σ) vl i = ⋃ i, hatOf A kk vl (σ i) ⊆ ⋃ i, hatOf A kk vl i

（等号由 `hatOf_comp`，包含由 `iUnion_hatOf_comp_subset`）。方向是**单向**的：

* 「`∀ g ∈ 并集, …`」型（`hhp`、`rec_p` 的前件、`ahat_halfPlane_L`）定义域变小 ⟹ **免费**；
* 「`∃ g ∈ 并集, …`」型（`ahat_nonempty`、`ahat_attained_L`、`bottom` 的 `∃ z₀`）⟹ **不免费**；
* `rec_p : ∀ g ∈ U, g + p ∈ U` 的**结论**也落在 `U` 里 ⟹ 小并集未必对 `+p` 封闭 ⟹ **不免费**；
* `hswept`（`SweptClosed`）同理，结论在 `U` 内 ⟹ **不免费**。

而原链的 `AhatMono` 恰恰是我们**没有**的那条（正因为没有才要重标定），所以不能用
「`hatOf` 单调 ⟹ 子列并集 ＝ 全并集」把这一类补回来。**补回来的充分条件只有一条**，
即 `iUnion_hatOf_comp_eq_of_absorb` 的 `habs`：子列**吸收**原链的每一项。

⟹ **洞 1 在重标定路线下的残余，是字段级的、有名字的：`habs` ＋ `hkk` ＋ `halign`。**
（`hkk`、`halign` 不是本文件消掉的——`exists_subseq_ahatMono_of_endpoint_shift` 自己
就把这两条留在 binder 里，见该定理签名。）

## ⛔ 上面这一整段读法已作废（集成者 2026-09-26，第 235 轮）

**作废范围**：本 docstring 里「洞 1 …残余 …`habs` ＋ `hkk` ＋ `halign`」这一句，以及一切把
**重标定**当成洞 1 必经之路的推论。**不作废**：本文件的五条定理（它们仍为真、仍可被引用），
以及上面关于「子列并集变小 ⟹ `∃ g ∈ 并集` 型字段不免费」的那段——那段对**任何**子列都对。

**为什么作废**：本文件的前提是「`AhatMono` 拿不到，所以必须用子列去换」。这个前提是假的。
`Nivat.ChainKK.exists_normalised_chain`（`ChainKK.lean`）**结论的最后一个合取支**逐字就是

    (∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)

即 `AhatMono` 本身；`ItemIIRecursionData`（`ItemIIRecursion.lean` 的 `structure`）把它列成
**最后一个字段**；而 `Nivat.ItemIIFeed.nonempty_itemIIRecursionData_of_chainData_binders`
（`ItemIIFeed.lean`）只吃 `RegionSteps.exists_chainData` 签名里**已有**的 binder 就能产出它。
⟹ 链上根本不需要换子列，`AhatMono` 是现成的。接线收据是
`Nivat.PartsChainFeed.exists_parts_chain_half`（`PartsChainFeed.lean`），公理干净。

**洞 1 的真残余在几何半边**（`b3_colle2.txt:440-520`），逐字段列表见 `PartsChainFeed.lean` 文首。

⚠ 本条按 §82 写下：两个文件对同一笔账不许各记各的。此处是被覆盖的一方。

⚠ 本文件**不产出**任何 `ChainDataGeomParts`，也不主张「只欠这三条」。它证的是
`hatOf_comp` / `iUnion_hatOf_comp_subset` / `B_mono_of_subBA_subAB` / `subAB_comp` /
`iUnion_hatOf_comp_eq_of_absorb` 五条，其余都是上面那段**读法**（PROTOCOL §15 口径，
与 `RegionSteps.lean` 文末 (3) 同）。硬规矩 1 的闸门不因本文件移动。
-/
import Nivat.External.Colle.ChainPartsFeed

namespace Nivat.PartsReindex

open Nivat Nivat.Colle35 Nivat.ChainAsm.Aparts

variable {α : Type*} {η xper : Config α} {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}

/-- **子列下 `hatOf` 逐字不变**：把 `A`、`kk` 一起沿 `σ` 复合，第 `i` 项就是原链第 `σ i` 项。
`hatOf` 只透过 `A i` / `kk i` 依赖 `i`，故这是 `rfl`。 -/
theorem hatOf_comp (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (v : ℤ × ℤ) (σ : ℕ → ℕ) (i : ℕ) :
    hatOf (fun n => A (σ n)) (fun n => kk (σ n)) v i = hatOf A kk v (σ i) := rfl

/-- **子列的并集只会变小。** 这条给出上面射程订正里「`∀ g ∈ 并集` 型字段免费」的那一半。 -/
theorem iUnion_hatOf_comp_subset (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (v : ℤ × ℤ) (σ : ℕ → ℕ) :
    (⋃ i, hatOf (fun n => A (σ n)) (fun n => kk (σ n)) v i) ⊆ ⋃ i, hatOf A kk v i := by
  refine Set.iUnion_subset fun i => ?_
  rw [hatOf_comp]
  exact Set.subset_iUnion (fun j => hatOf A kk v j) (σ i)

/-- **并集在子列下不变的充分条件：子列吸收原链每一项。** 这就是射程订正里点名的 `habs`——
「`∃ g ∈ 并集` 型」字段（`ahat_nonempty` / `ahat_attained_L` / `bottom` 的 `∃ z₀`）与
「结论落在并集内」型字段（`rec_p` / `hswept`）能不能随重标定过去，**全押在这一条上**。 -/
theorem iUnion_hatOf_comp_eq_of_absorb (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (v : ℤ × ℤ)
    (σ : ℕ → ℕ) (habs : ∀ i, ∃ j, hatOf A kk v i ⊆ hatOf A kk v (σ j)) :
    (⋃ i, hatOf (fun n => A (σ n)) (fun n => kk (σ n)) v i) = ⋃ i, hatOf A kk v i := by
  refine Set.Subset.antisymm (iUnion_hatOf_comp_subset A kk v σ) ?_
  refine Set.iUnion_subset fun i => ?_
  obtain ⟨j, hj⟩ := habs i
  refine hj.trans ?_
  rw [← hatOf_comp A kk v σ j]
  exact Set.subset_iUnion (fun n => hatOf (fun n => A (σ n)) (fun n => kk (σ n)) v n) j

/-- **`B` 单调**，由 `subBA` / `subAB` 复合而得（`A_mono_of_subBA_subAB`
（`ChainPartsFeed.lean`）的 `B` 侧孪生条）。`subAB_comp` 需要它。 -/
theorem B_mono_of_subBA_subAB (c : ChainDataGeomParts η xper vl p S gen) :
    ∀ i j, i ≤ j → c.B i ⊆ c.B j := by
  have hstep : ∀ i, c.B i ⊆ c.B (i + 1) := fun i => (c.subBA i).trans (c.subAB i)
  intro i j hij
  induction j with
  | zero => obtain rfl : i = 0 := Nat.le_zero.mp hij; exact subset_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact (ih (Nat.lt_succ_iff.mp h)).trans (hstep n)
    · obtain rfl : i = n + 1 := le_antisymm hij h; exact subset_rfl

/-- **`subAB` 挺过重标定。** `c.subAB (σ i)` 只给到 `B (σ i + 1)`，而重标定后要的是
`B (σ (i+1))`；`StrictMono σ` 给 `σ i + 1 ≤ σ (i+1)`，再由 `B_mono_of_subBA_subAB` 补上。
⟹ 这条是「逐点字段在子列下免费」里**唯一**真正需要 `StrictMono σ` 的一条（其余逐点字段
直接把下标换成 `σ i` 即可）。 -/
theorem subAB_comp (c : ChainDataGeomParts η xper vl p S gen) {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    ∀ i, c.A (σ i) ⊆ c.B (σ (i + 1)) :=
  fun i => (c.subAB (σ i)).trans
    (B_mono_of_subBA_subAB c _ _ (Nat.succ_le_of_lt (hσ (Nat.lt_succ_self i))))

#print axioms Nivat.PartsReindex.hatOf_comp
#print axioms Nivat.PartsReindex.iUnion_hatOf_comp_subset
#print axioms Nivat.PartsReindex.iUnion_hatOf_comp_eq_of_absorb
#print axioms Nivat.PartsReindex.B_mono_of_subBA_subAB
#print axioms Nivat.PartsReindex.subAB_comp

end Nivat.PartsReindex
