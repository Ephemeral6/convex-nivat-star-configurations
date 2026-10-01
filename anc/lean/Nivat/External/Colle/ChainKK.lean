/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ItemIIChain
import Nivat.External.Colle.LeafAItemII
import Nivat.External.Colle.AItemFour

/-!
# The normalised chain: `kk` from `:488`, `AhatMono` from `:496-504`, on the item-(ii) chain

Lane LeafA (kk redesign), 2026-09-21.  **Consumer**: `exists_chainData` (`RegionSteps.lean`)
through `ChainAsm.Aparts.ChainDataGeomParts` (`ChainPartsFeed.lean`).  Upstream of
`RegionSteps`: both imports are already in its closure (`ItemIIChain` directly,
`LeafAItemII` through `ChainPartsFeed`).

## Why `kk` is a genuine function of `i` here

`kk ≡ 0` is dead, and as of 2026-09-25 the reason is **this file's own output**, not a `tmp/`
receipt.  ⚠ 订正 2026-09-25（集成者，第 226 轮）：本句原引 `tmp/chaindata_kkzero_false.lean` 与
`tmp/aenvfix_kk_forced.lean`，**两者在盘上都已不存在**（`ls` 实测），且 `not_exhausts_of_kk_zero`
全树零定义 ⟹ 那两个引用是死的，该论断一度**无依据**。活着的替代品由 lane-tower-hbase 2026-09-25
给出（`tmp/wip/hbase_anchor.lean`，`check1.sh` EXIT=0，公理全白名单）：
`not_kkZero_of_anchor` / `not_const_kk_of_anchor` 证明**本文件 `:114` 的锚点合取项**与常值 `kk`
不相容——机理是该合取项的 `IsGreatest` 上界半边逐字说「`kk i` 恰是使 `g₁ + s•vl ∈ A i` 的最大 `s`」
（即 `hkk_max`），配 `hreach` 即迫使 `kk` 无界。
⚠ 该不相容**吃掉链的穷竭性**，不是签名层矛盾：`anchor_const_kk_consistent_without_reach` 是内核
见证——去掉 `hreach` 后（`A i = {g₁}`）锚点合取项与常值 `kk` 可以共存。
⚠ 上述收据仍在 `tmp/wip/`，**未进主仓**（硬规矩 22：尚无消费者）⟹ 按红线这条论断目前是
「有内核收据、未落地」，不是「主仓已证」。
and the recursion `B (i+1) := A i` is dead regardless of `kk`
(`ChainAsm.not_chainDataGeom_of_chainRecursion`).  The surviving route is Collé's item (ii)
chain, `ItemIIChain.exists_itemII_chain`, which exhausts the half plane `ℋ(ℓ^(−))`.  On that
chain `kk` **must** be `:488`'s endpoint normalisation, and the producer of exactly that is
already on the tree: `AItemFour.exists_endpoint_shift`.  This file composes the two and then
passes to the subsequence of `:496`/`:500`/`:504` (`LeafAItemII.exists_subseq_chain`) so that
`AhatMono` — refuted at the given indexing five times in `AhatMono.lean` — holds.

## What is produced (`exists_normalised_chain`)

One chain `(B, A, u, kk)` with `g₁` such that every *chain-side* binder of `ChainDataGeomParts`
holds (`envB maxA subBA subAB hfin AhatMono`), together with the item-(ii) facts
(`ItemII`, `Exhausts`, `∀ z ∈ B i, cz ≤ ⟪nℓ,z⟫`) and the `:488` alignment at **every** index.
Nothing about the shell block, the face block, `bottom`, `rec_p` is claimed here.

## The sign of `p` (`rec_p_forces_backward`)

`:488` pins the `+v⃗_ℓ` end of `Â_i ∩ ℓ^(−)` at `g₁` for every `i`, so `Â_∞ ∩ ℓ^(−)` is a
half-line ending at `g₁` and **`Â_∞` recedes along `−v⃗_ℓ`, not `+v⃗_ℓ`**.  Consequently
`ofParts.rec_p` can only hold for `p = c • vl` with `c < 0`.  The call site of
`exists_chainData` fixes `p` with `det p vl = 0` and no sign; `Per xper` is a subgroup, so the
sign is free upstream — but it is *not* free inside `exists_chainData`, whose conclusion names
`p`.  Kernel cross-check: the toy bundle `cgw` (`Step_PeriodsRays2.lean`) has
`pv = (0,1) = -vlv`.
-/

set_option autoImplicit false

namespace Nivat.ChainKK

open Nivat Nivat.LE2 Nivat.Colle35 Nivat.LeafAItemII

/-- `A` is monotone from `subBA`/`subAB` (`b3_colle2.txt:466`). -/
theorem A_mono {B A : ℕ → Set (ℤ × ℤ)}
    (subBA : ∀ i, B i ⊆ A i) (subAB : ∀ i, A i ⊆ B (i + 1)) :
    ∀ i j, i ≤ j → A i ⊆ A j := by
  have hstep : ∀ i, A i ⊆ A (i + 1) := fun i => (subAB i).trans (subBA (i + 1))
  intro i j hij
  induction j with
  | zero => obtain rfl : i = 0 := Nat.le_zero.mp hij; exact subset_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact (ih (Nat.lt_succ_iff.mp h)).trans (hstep n)
    · obtain rfl : i = n + 1 := le_antisymm hij h; exact subset_rfl

/-- The support-line clause of item (i) (`:472`, `B_i ∩ ℓ_{B_i} ⊂ ℓ^(−)`) gives a point of
`A_i` **on** the line `{⟪nℓ,·⟫ = cz}` — the tacit hypothesis `hne` of
`AItemFour.exists_endpoint_shift`. -/
theorem exists_mem_on_line {B A : ℕ → Set (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz : ℤ}
    (finB : ∀ i, (B i).Finite) (neB : ∀ i, (B i).Nonempty)
    (hsupp : ∀ i, suppVal (B i) (-nℓ) = -cz) (subBA : ∀ i, B i ⊆ A i) (i : ℕ) :
    (A i ∩ {z | dot nℓ z = cz}).Nonempty := by
  obtain ⟨b, hb, hbeq⟩ := exists_suppVal_eq (finB i) (neB i) (-nℓ)
  refine ⟨b, subBA i hb, ?_⟩
  show dot nℓ b = cz
  rw [hsupp i, dot_neg_left] at hbeq
  linarith

/-- **The normalised chain.**

原文：b3_colle2.txt:466-504.  Quantifier ledger (hard rule 7):
* `B A u` ↔ `:466`/`:472`/`:474`/`:480`/`:484`, exactly the conjuncts of
  `ItemIIChain.exists_itemII_chain`;
* `kk`, `g₁` ↔ `:488` ("let `k_i ∈ ℕ` be such that the final point of `(A_i − k_i v⃗_ℓ) ∩ ℓ^(−)`
  coincides with `g₁`"), produced by `AItemFour.exists_endpoint_shift`;
* the last conjunct ↔ `:496`/`:500`/`:504` ("by passing to a subsequence"), produced by
  `LeafAItemII.exists_subseq_chain`; the paper's Figure 6 inclusion `Â_1 ⊂ Â_2 ⊂ ⋯` is
  asserted only for the extracted subsequence (`OPEN.md #17`).

The output is re-indexed twice (a tail shift so that `:488`'s `i ≥ 1` alignment holds at
every index, then the subsequence); `Exhausts` and `ItemII` survive both because the chain is
monotone.  The `IsGreatest` conjunct is `:488` verbatim and is what `rec_p_forces_backward`
and any future `bottom`/shell producer read. -/
theorem exists_normalised_chain {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl nℓ : ℤ × ℤ}
    (cz : ℤ) (hS : LatticeConvex S) (hSne : S.Nonempty)
    (hxper : xper ∈ orbitClosure ξ)
    (hvl : vl ≠ 0) (hvl_prim : Primitive vl)
    (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hnℓ' : -nℓ ∈ E (↑S : Set (ℤ × ℤ)))
    {n m : ℤ × ℤ} (hdet : det n m ≠ 0)
    (hn : n ∈ E (↑S : Set (ℤ × ℤ))) (hn' : -n ∈ E (↑S : Set (ℤ × ℤ)))
    (hm : m ∈ E (↑S : Set (ℤ × ℤ))) (hm' : -m ∈ E (↑S : Set (ℤ × ℤ)))
    (hcase2 : Nivat.ColleReg.Case2 ξ xper S vl) :
    ∃ (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ) (g₁ : ℤ × ℤ),
      (∀ i, EnvOf (↑S : Set (ℤ × ℤ)) (B i)) ∧
      (∀ i, (B i).Finite) ∧
      (∀ i, ∀ z ∈ B i, cz ≤ dot nℓ z) ∧
      (∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA ξ xper vl B u i) (A i)) ∧
      (∀ i, B i ⊆ A i) ∧
      (∀ i, A i ⊆ B (i + 1)) ∧
      (∀ i, (A i).Finite) ∧
      ItemII B nℓ cz ∧
      Exhausts A nℓ cz ∧
      (∀ i j, i ≤ j → kk i ≤ kk j) ∧
      dot nℓ g₁ = cz ∧
      (∀ i, IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0) ∧
      (∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) := by
  obtain ⟨B, A, u, envB, finB, hsupp, hlev, maxA, subBA, subAB, -, hII, hexh⟩ :=
    Nivat.ItemIIChain.exists_itemII_chain cz hS hSne hxper hprim hperp hnℓ' hdet hn hn' hm hm'
      hcase2
  have hUarea : PosArea (↑S : Set (ℤ × ℤ)) :=
    Nivat.ItemIIChain.posArea_of_envOf_of_pair hn hn' hm hdet (ChainAsm.envOf_coe_self hS)
  have neB : ∀ i, (B i).Nonempty := fun i => by
    obtain ⟨a, ha, -⟩ := Nivat.ItemIIChain.posArea_of_envOf_of_pair hn hn' hm hdet (envB i)
    exact ⟨a, ha⟩
  have hAfin : ∀ i, (A i).Finite := fun i => (finB (i + 1)).subset (subAB i)
  have hAmono := A_mono subBA subAB
  have hnℓ : nℓ ≠ 0 := hprim.ne_zero
  -- `:488`: `g₁` and `kk`, aligned for `1 ≤ i`.
  obtain ⟨g₁, kk, -, hg₁cz, halign⟩ :=
    Nivat.AItemFour.exists_endpoint_shift (nℓ := nℓ) (cz := cz) hAfin
      (exists_mem_on_line finB neB hsupp subBA) hnℓ hperp hvl hvl_prim hAmono
  -- Tail shift: drop the seed so that alignment holds at every index.
  set B₁ : ℕ → Set (ℤ × ℤ) := fun i => B (i + 1) with hB₁
  set A₁ : ℕ → Set (ℤ × ℤ) := fun i => A (i + 1) with hA₁
  set u₁ : ℕ → ℤ × ℤ := fun i => u (i + 1) with hu₁
  set kk₁ : ℕ → ℕ := fun i => kk (i + 1) with hkk₁
  have hsucc : StrictMono (fun i : ℕ => i + 1) := fun _ _ h => Nat.succ_lt_succ h
  have halign₁ : ∀ i, IsGreatest
      {t : ℤ | g₁ + t • vl ∈ hatOf A₁ kk₁ vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0 :=
    fun i => halign (i + 1) (by omega)
  have hkk₁ : ∀ i j, i ≤ j → kk₁ i ≤ kk₁ j := fun i j hij =>
    Nivat.AhatMono.kk_le_of_endpointAligned hperp hg₁cz hAmono halign (by omega) (by omega)
  have hg₁₁ : ∀ i, g₁ ∈ hatOf A₁ kk₁ vl i := fun i => by
    have h := (halign₁ i).1.1
    simpa using h
  have subBA₁ : ∀ i, B₁ i ⊆ A₁ i := fun i => subBA (i + 1)
  have subAB₁ : ∀ i, A₁ i ⊆ B₁ (i + 1) := fun i => subAB (i + 1)
  have maxA₁ : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA ξ xper vl B₁ u₁ i) (A₁ i) :=
    fun i => by
      rw [hB₁, hu₁, canonA_comp]
      exact maxA (i + 1)
  have hII₁ : ItemII B₁ nℓ cz :=
    itemII_comp hsucc (B_mono_of_subBA_subAB subBA subAB) hII
  have hexh₁ : Exhausts A₁ nℓ cz := exhausts_comp hsucc hAmono hexh
  -- `:496`/`:500`/`:504`: the subsequence along which `AhatMono` holds.
  obtain ⟨σ, hσ, envB₂, maxA₂, subBA₂, subAB₂, hfin₂, hII₂, hexh₂, hmono₂⟩ :=
    exists_subseq_chain (η := ξ) (xper := xper) (U := (↑S : Set (ℤ × ℤ))) (B := B₁) (A := A₁)
      (u := u₁) (kk := kk₁) (vl := vl) (g₁ := g₁) (nℓ := nℓ) (cz := cz)
      S.finite_toSet hUarea (fun i => envB (i + 1)) maxA₁ (fun i => (maxA₁ i).1)
      (fun i => hAfin (i + 1)) subBA₁ subAB₁ hkk₁ hg₁₁ hII₁ hexh₁
  refine ⟨fun i => B₁ (σ i), fun i => A₁ (σ i), fun i => u₁ (σ i), fun i => kk₁ (σ i), g₁,
    envB₂, fun i => finB (σ i + 1), fun i => hlev (σ i + 1), maxA₂, subBA₂, subAB₂, hfin₂,
    hII₂, hexh₂, fun i j hij => hkk₁ _ _ (hσ.monotone hij), hg₁cz,
    fun i => halign₁ (σ i), hmono₂⟩

/-! ## The sign of `p` -/

/-- **`Â_∞` does not recede forward along `v⃗_ℓ`.**

原文：b3_colle2.txt:488 — the final point of `Â_i ∩ ℓ^(−)` is `g₁` for every `i`, so
`g₁ + c v⃗_ℓ` (`c > 0`), which is on `ℓ^(−)`, lies in no `Â_i`. -/
theorem not_rec_forward {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nℓ g₁ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0) (hg₁cz : dot nℓ g₁ = cz)
    (halign : ∀ i, IsGreatest
      {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0)
    {c : ℤ} (hc : 0 < c) :
    ¬ ∀ g ∈ ⋃ i, hatOf A kk vl i, g + c • vl ∈ ⋃ i, hatOf A kk vl i := by
  intro hrec
  have hg₁ : g₁ ∈ ⋃ i, hatOf A kk vl i :=
    Set.mem_iUnion.mpr ⟨0, by simpa using (halign 0).1.1⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hrec g₁ hg₁)
  have hlev : dot nℓ (g₁ + c • vl) = cz := by
    rw [dot_add, Nivat.AItemFour.dot_zsmul, hperp, mul_zero, add_zero, hg₁cz]
  have := (halign j).2 ⟨hj, hlev⟩
  omega

/-- **`rec_p` forces `p` to be a *negative* multiple of `v⃗_ℓ`** on any chain aligned as in
`:488`.  This is the numerical sign check hard rule 10 asks for, as a theorem: the producer of
`exists_chainData` cannot satisfy `ofParts.rec_p` for the `p` it is handed unless
`p = c • vl` with `c < 0`.  `Per xper` is a subgroup, so `-p` is available upstream; the
conclusion of `exists_chainData` names `p`, so the sign must be fixed *there* or one level up
(`exists_preamble_pair`). -/
theorem rec_p_forces_backward {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nℓ g₁ p : ℤ × ℤ}
    {cz : ℤ}
    (hperp : dot nℓ vl = 0) (hg₁cz : dot nℓ g₁ = cz)
    (halign : ∀ i, IsGreatest
      {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0)
    (hvl_prim : Primitive vl) (hp : p ≠ 0) (hdet : det p vl = 0)
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i) :
    ∃ c : ℤ, c < 0 ∧ p = c • vl := by
  have hdet' : det vl p = 0 := by
    have h := hdet
    simp only [det] at h ⊢
    linarith
  obtain ⟨c, rfl⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl_prim hdet'
  refine ⟨c, ?_, rfl⟩
  rcases lt_trichotomy c 0 with h | h | h
  · exact h
  · subst h; simp at hp
  · exact absurd rec_p (not_rec_forward hperp hg₁cz halign h)

end Nivat.ChainKK

#print axioms Nivat.ChainKK.A_mono
#print axioms Nivat.ChainKK.exists_mem_on_line
#print axioms Nivat.ChainKK.exists_normalised_chain
#print axioms Nivat.ChainKK.not_rec_forward
#print axioms Nivat.ChainKK.rec_p_forces_backward
