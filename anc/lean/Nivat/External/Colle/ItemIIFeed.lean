/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ANormal
import Nivat.External.Colle.ItemIIRecursion

/-!
# `exists_itemII_recursion` is callable from `exists_chainData`'s binders

集成者, 2026-09-24 (第 210 轮).  Integration half of the `ItemIIRecursion` wiring;
lane-tower-hlev supplied the two binder lemmas (§1 below, moved here verbatim from
`tmp/wip/lane-tower-hlev-itemii-binders.lean`), this file adds the receipt that closes the
call (§2).

## ⚠ What this does and does not do (硬规矩 1)

`RegionSteps.exists_chainData`'s `sorry` is **not** replaced by this file, and cannot be:
`exists_itemII_recursion`'s conclusion is `∃ _rd : ItemIIRecursionData …, True`, whereas
`exists_chainData` must produce a `ChainDataGeom`.  `ItemIIRecursion.lean` §5 lists what item (ii)
still leaves open — the shell block (`shellInf_sup` / `shellInf_union` / `shellInf_eq` /
`shellSubStrip`), `bottom`, `rec_p` — and none of those is a field of `ItemIIRecursionData`.
Anyone reading this file as "item (ii) closes `exists_chainData`" is reading it wrong.

What *is* closed is a question that was open until today: **whether the call is even applicable.**
`exists_itemII_recursion` takes eleven premises; two of them (`hnℓ'`, and the `n`/`m` pair)名不见于
`exists_chainData`'s context, so it was not known whether reaching item (ii) from the on-chain
producer needed new geometric input.  §2's `nonempty_itemIIRecursionData_of_chainData_binders`
answers no: it takes only binders that `exists_chainData` already has and produces the data.
That turns "call item (ii)" from a conjecture about the producer into a kernel-checked step.

## §1's two binders (lane-tower-hlev)

* `hnℓ' : -nℓ ∈ E ↑S` — `exists_chainData`'s `nℓ` comes out of `hpartner` carrying
  `Primitive nℓ` and `dot nℓ vl = 0`, but **no** edge membership.
* `{n m} (hdet : det n m ≠ 0)` with all four of `n`, `-n`, `m`, `-m` in `E ↑S` — nothing in
  `exists_chainData`'s context names a second edge direction at all.

Both are proved from stock: the first spends the sign ambiguity of a primitive normal, the second
spends `DecompData.hm : 2 ≤ m` and `h_dir` (原文 `scratch/b3_colle2.txt:424`, the standing
hypothesis of Lemma 3.5 — "`h₁, …, h_m ∈ ℤ²`, **with `m ≥ 2`**, are vectors in pairwise distinct
directions").  Neither introduces a new `Prop`: both conclusions are conjunctions of premises of
the existing `exists_itemII_recursion`, copied from its binder list (硬规矩 5).

### `hnℓ'`: why the sign ambiguity is harmless

`exists_chainData` already binds a direction `ℓ` with `hℓ_nel`/`hℓ_pos`/`hℓ_neg` and
`hdet_ℓ : dot ℓ vl = 0`, and `ONEDRational.mem_E_Sphi_and_neg_mem_E_Sphi_of_biONED` puts **both**
`ℓ` and `-ℓ` in `E ↑d.Sphi`.  Two primitive vectors orthogonal to the same non-zero `vl` are equal
up to sign (`LE2.det_eq_zero_of_dot_eq_zero` then `eq_or_eq_neg_of_det_eq_zero`), so `nℓ = ±ℓ` —
and because the conclusion is a **pair** closed under negation, which of the two signs holds never
has to be decided.  ⛔ The orientation fact `0 < det nℓ vl` that `hpartner` also carries is **not**
used and must not be: pinning the sign here would re-open the orientation question
(第 179 轮红线 — no orientation-sensitive criterion moves between the chain side and the source
side until `vl = v⃗_{ℓ_ι}` is proved).

### The `n`/`m` pair

Take `n ⟂ h₀` transverse to `h₁` and `m ⟂ h₁` transverse to `h₀`
(`Colle35.exists_prim_dot_zero_dot_ne_zero`, `ANormal.lean`), push both into `E ↑Sphi` with
`DecompData.mem_E_Sphi_of_dot_eq_zero` / `neg_mem_E_Sphi_of_dot_eq_zero` (`FaceDistinct.lean`).
`det n m ≠ 0` is then forced: were they parallel, both being primitive they would be equal up to
sign, and `m`'s transversality to `h₀` would contradict `n ⟂ h₀`.  This duplicates no existing
declaration — `AhatMono.posArea_Sphi_of_two_le_m` runs the same three lines but discards the pair,
concluding `PosArea ↑d.Sphi` instead (PROTOCOL §58: checked by conclusion shape).

## import 表 (PROTOCOL §57)

`ANormal` (which pulls in `FaceDistinct` and `ONEDRational`) and `ItemIIRecursion`.  Neither
`RegionSteps` nor `ColleRegion` nor `Case2WindowProbe` nor `NfpLPreamble` is in the closure, so
`RegionSteps` can import this file; that import is what puts the receipt in the main theorem's
reachable closure (硬规矩 9).
-/

set_option autoImplicit false

namespace Nivat.ItemIIFeed

open Nivat Nivat.LE2 Nivat.Colle35

/-! ## §1. The two binders `exists_chainData` does not carry (lane-tower-hlev) -/

/-- **`hnℓ'` is free.**  Given `exists_chainData`'s own `ℓ` (bi-one-sided-nonexpansive and
orthogonal to `vl`) and any primitive `nℓ` orthogonal to `vl`, both `nℓ` and `-nℓ` are edge
normals of `𝒮_φ`.

`nℓ = ±ℓ` because two primitive vectors orthogonal to the same non-zero `vl` are parallel; the
conclusion is closed under negation, so the sign is never decided.  `0 < det nℓ vl` is
deliberately **not** a binder (第 179 轮红线). -/
theorem mem_E_Sphi_and_neg_of_prim_perp {ξ : Config ℤ} (d : DecompDataZ ξ)
    {ℓ nℓ vl : ℤ × ℤ} (hvl_ne : vl ≠ 0)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hdet_ℓ : dot ℓ vl = 0)
    (hnℓ_prim : Primitive nℓ) (hnℓ_perp : dot nℓ vl = 0) :
    nℓ ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ∧
      -nℓ ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) := by
  have hℓprim : Primitive ℓ := hℓ_nel.1
  have hpar : det ℓ nℓ = 0 := by
    refine det_eq_zero_of_dot_eq_zero (n := vl) hvl_ne ?_ ?_
    · rw [dot_comm]; exact hdet_ℓ
    · rw [dot_comm]; exact hnℓ_perp
  obtain ⟨hp, hn⟩ :=
    Nivat.ONEDRational.mem_E_Sphi_and_neg_mem_E_Sphi_of_biONED d hℓ_nel hℓ_pos hℓ_neg
  rcases eq_or_eq_neg_of_det_eq_zero hℓprim hnℓ_prim hpar with h | h
  · rw [h]; exact ⟨hp, hn⟩
  · rw [h, neg_neg]; exact ⟨hn, hp⟩

/-- **The `n`/`m` pair is free.**  Every `DecompData` carries two edge normals of `𝒮_φ` in
non-parallel directions, both signs of each.

原文 `scratch/b3_colle2.txt:424` (`m ≥ 2`, pairwise distinct directions) is exactly `d.hm` and
`d.h_dir`, so this is a projection of the standing hypothesis, not a new one. -/
theorem exists_det_ne_zero_pair_mem_E_Sphi {α : Type*} [AddCommMonoid α] {η : Config α}
    (d : DecompData η) :
    ∃ n m : ℤ × ℤ, det n m ≠ 0 ∧
      n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧
      m ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -m ∈ E (↑d.Sphi : Set (ℤ × ℤ)) := by
  have hm2 := d.hm
  have hne01 : (⟨0, by omega⟩ : Fin d.m) ≠ (⟨1, by omega⟩ : Fin d.m) := by
    simp [Fin.ext_iff]
  obtain ⟨n, hnp, hnd, hnne⟩ :=
    exists_prim_dot_zero_dot_ne_zero (d.h_ne ⟨0, by omega⟩) (d.h_dir _ _ hne01.symm)
  obtain ⟨m, hmp, hmd, hmne⟩ :=
    exists_prim_dot_zero_dot_ne_zero (d.h_ne ⟨1, by omega⟩) (d.h_dir _ _ hne01)
  refine ⟨n, m, ?_, d.mem_E_Sphi_of_dot_eq_zero (prim_iff_primitive.mpr hnp) _ hnd,
    d.neg_mem_E_Sphi_of_dot_eq_zero (prim_iff_primitive.mpr hnp) _ hnd,
    d.mem_E_Sphi_of_dot_eq_zero (prim_iff_primitive.mpr hmp) _ hmd,
    d.neg_mem_E_Sphi_of_dot_eq_zero (prim_iff_primitive.mpr hmp) _ hmd⟩
  intro hdet0
  rcases eq_or_eq_neg_of_det_eq_zero hnp hmp hdet0 with h | h
  · exact hmne (by rw [h]; exact hnd)
  · exact hmne (by rw [h, dot_neg_left, hnd, neg_zero])

/-! ## §2. The receipt: the call is applicable

Every binder below appears verbatim in `RegionSteps.exists_chainData`'s signature, except that
`nℓ`'s two properties are the destructured `Primitive nℓ` / `dot nℓ vl = 0` conjuncts of its
`hpartner`, and `cz` is `hpartner`'s level.  `hpartner`'s remaining conjuncts — including
`0 < det nℓ vl` — are **not** binders here (第 179 轮红线), and neither is `hξ`, `w`, `p`, or any
of the `hp_*` data.

`hS` / `hSne` are `d.Sphi_conv` (`DecompData.lean`, a field) and `DecompDataZ.Sphi_nonempty`
(derived, not assumed), so they are not binders either.
-/

/-- **`exists_itemII_recursion` is callable from `exists_chainData`'s own binders.**

No new geometric input is needed to reach Collé item (ii) (`b3_colle2.txt:466-504`) from the
on-chain producer: §1's two lemmas supply exactly the two premises that `exists_chainData`'s
context does not name, and the other nine are already in scope there.

⚠ This is *applicability*, not `exists_chainData`.  The shell block, `bottom` and `rec_p` are not
fields of `ItemIIRecursionData` and remain open — see this file's header. -/
theorem nonempty_itemIIRecursionData_of_chainData_binders {ξ xper : Config ℤ}
    (d : DecompDataZ ξ) {ℓ nℓ vl : ℤ × ℤ} (cz : ℤ)
    (hxper : xper ∈ orbitClosure ξ)
    (hvl_ne : vl ≠ 0) (hvl_prim : Primitive vl)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hdet_ℓ : dot ℓ vl = 0)
    (hnℓ_prim : Primitive nℓ) (hnℓ_perp : dot nℓ vl = 0)
    (hcase2 : Nivat.ColleReg.Case2 ξ xper d.toDecompData.Sphi vl) :
    Nonempty (Nivat.ItemIIRecursion.ItemIIRecursionData ξ xper d.toDecompData.Sphi vl nℓ cz) := by
  obtain ⟨-, hnℓ'⟩ :=
    mem_E_Sphi_and_neg_of_prim_perp d hvl_ne hℓ_nel hℓ_pos hℓ_neg hdet_ℓ hnℓ_prim hnℓ_perp
  obtain ⟨n, m, hdet, hn, hn', hm, hm'⟩ := exists_det_ne_zero_pair_mem_E_Sphi d.toDecompData
  obtain ⟨rd, -⟩ :=
    Nivat.ItemIIRecursion.exists_itemII_recursion cz d.Sphi_conv d.Sphi_nonempty hxper
      hvl_ne hvl_prim hnℓ_prim hnℓ_perp hnℓ' hdet hn hn' hm hm' hcase2
  exact ⟨rd⟩

end Nivat.ItemIIFeed

#print axioms Nivat.ItemIIFeed.mem_E_Sphi_and_neg_of_prim_perp
#print axioms Nivat.ItemIIFeed.exists_det_ne_zero_pair_mem_E_Sphi
#print axioms Nivat.ItemIIFeed.nonempty_itemIIRecursionData_of_chainData_binders
