/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.KariMoutot

/-!
# Kari–Moutot §2.2: the determinism window, and the gap that `colle_doublyPeriodic` really has

Two independent contributions, both **proved outright** (no `sorry`, no new `axiom`).

## 1. Why Kari–Moutot Theorem 4 cannot discharge `Nivat.colle_doublyPeriodic`

`Nivat.Section8.External.colle_doublyPeriodic` (Colle arXiv:1909.08195v4, Theorem 1.14)
concludes `DoublyPeriodic ξ` — about `ξ` **itself**.  Kari–Moutot Theorem 4, together with
Boyle–Lind, yields only

> `∃ x ∈ orbitClosure ξ, DoublyPeriodic x`

(this is `Nivat.Colle.exists_doublyPeriodic_in_orbitClosure`, step 2 of Colle §3.1).  The two
are **not** interchangeable, and the gap between them is the whole of Colle §3.1 after its
second paragraph (Claim 3.6, Lemma 3.5, Claim 3.7, Proposition 2.12).

`orbitClosure_doublyPeriodic_not_sufficient` below makes the gap machine-checked: the
vertical-line configuration `Nivat.KM.vline` has finite range, a non-trivial annihilator, and a
doubly periodic element in its orbit closure (namely the all-zero configuration), yet is itself
**not** doubly periodic.  So no amount of work on Kari–Moutot §4 — Proposition 18, Lemmas 14–17,
or the `KMWeakDescent` variant — can by itself close `colle_doublyPeriodic`.  The `hONED`
hypothesis of Theorem 1.14 is exactly what rules `vline` out (`vline` has **both** horizontal
orientations in `ONED`, by `Nivat.KM.vline_ONED_eq`), and making that hypothesis do its work on
`ξ` itself is Colle's step 3.

## 2. The determinism window `B` of Kari–Moutot §2.2

Kari–Moutot §2.2 (p. 131), verbatim:

> "Moreover, by compactness, determinism in direction `u` implies that there is a finite number
> `k` such that already the contents of a configuration in the discrete box
> `B_u^k = {x ∈ ℤ² | −k < ⟨x, u⟩ < 0 and −k < ⟨x, ũ⟩ < k}` are enough to uniquely determine the
> contents in cell `0`."

This is the compactness fact that the whole of Kari–Moutot §4 rests on: it is what produces the
box `B` of their property (2), hence of Lemma 14, Corollary 15 and Lemma 16(b).  It is **not**
formalised anywhere else in this development.  `exists_window_of_det` proves it, in the form
actually needed (a finite `B` inside the open half-plane, not the specific rectangle `B_u^k`;
the shape of `B` is never used downstream, only its finiteness and its position).

The proof is Kari–Moutot's own compactness argument, run through an ultrafilter exactly as
`Nivat.subseqLimits_nonempty` does: negating the conclusion gives, for each finite `B ⊆ H_u`, a
*pair* of elements of `X` agreeing on `B` but differing at `0`; an ultrafilter limit of the pairs
agrees on all of `H_u` and still differs at `0`, contradicting determinism.  The supporting
`exists_pair_limit` (joint compactness for a pair of sequences) and
`mem_orbitClosure_of_pointwise_limit` are of independent use.

## Status

No `sorry`.  No new `axiom`.  Kernel footprint of every result here is `[propext,
Classical.choice, Quot.sound]`.  This file is **not** imported by `Nivat.lean` and discharges
neither Colle structure axiom; see the module docstring of `Nivat.External.Colle.KariMoutot`
for what a proof of Kari–Moutot Theorem 4 would and would not buy.
-/

namespace Nivat.KMBox

open Nivat

/-! ### §1. Step 2 of Colle §3.1 is strictly weaker than Theorem 1.14 -/

/-- The all-zero configuration is doubly periodic: `(1,0)` and `(0,1)` are periods. -/
theorem const0_doublyPeriodic : DoublyPeriodic BL.const0 := by
  refine ⟨((1 : ℤ), (0 : ℤ)), ?_, ((0 : ℤ), (1 : ℤ)), ?_, ?_⟩
  · rw [mem_Per_iff]; funext z; rfl
  · rw [mem_Per_iff]; funext z; rfl
  · show ¬ ((1 : ℤ) * 1 - 0 * 0 = 0)
    norm_num

/-- **A doubly periodic element of the orbit closure does not make the configuration doubly
periodic.**

`Nivat.KM.vline` — the configuration that is `1` on the column `z.1 = 0` and `0` elsewhere — has
finite range and a non-trivial annihilator, and the all-zero configuration lies in its orbit
closure and is doubly periodic; but `vline` is not doubly periodic (all its periods are
vertical, `Nivat.KM.fst_eq_zero_of_mem_Per_vline`).

Consequence for the axiom `Nivat.colle_doublyPeriodic`: the conclusion of Colle's step 2
(`Nivat.Colle.exists_doublyPeriodic_in_orbitClosure`, which is what Kari–Moutot Theorem 4 plus
Boyle–Lind deliver) does **not** imply the conclusion of Theorem 1.14.  Discharging the axiom
therefore requires Colle's step 3 as well; Kari–Moutot §4 alone cannot do it. -/
theorem orbitClosure_doublyPeriodic_not_sufficient :
    ∃ ξ : Config ℤ, (Set.range ξ).Finite ∧ HasNonzeroAnn ξ ∧
      (∃ x ∈ orbitClosure ξ, DoublyPeriodic x) ∧ ¬ DoublyPeriodic ξ :=
  ⟨KM.vline, KM.vline_range_finite, KM.vline_hasNonzeroAnn,
    ⟨BL.const0, KM.const0_mem_orbitClosure_vline, const0_doublyPeriodic⟩,
    KM.vline_not_doublyPeriodic⟩

/-! ### §2. Joint compactness for a pair of sequences of configurations -/

/-- **Joint compactness.**  Over a finite alphabet, any *pair* of sequences of configurations has
a simultaneous pointwise subsequential limit: a pair `(x', y')` such that on every finite window
`W` and beyond every time `M`, some single index `n ≥ M` realises `x'|_W = x n|_W` **and**
`y'|_W = y n|_W`.

Taking the limit of the pair jointly (rather than of each sequence separately) is the whole
point: it is what lets a relation between `x n` and `y n` — here "agree on a box, differ at the
origin" — survive to the limit.

The limit is read off from any ultrafilter `𝔲` on `ℕ` refining `atTop`: for each `w` the
pushforward of `𝔲` along `n ↦ (x n w, y n w)` is an ultrafilter on the finite type `α × α`,
hence principal at a unique pair, and that pair is `(x' w, y' w)`.  Same argument as
`Nivat.subseqLimits_nonempty`, run on `α × α`. -/
theorem exists_pair_limit {α : Type*} [Finite α] (x y : ℕ → Config α) :
    ∃ x' y' : Config α, ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ n : ℕ, M ≤ n ∧
      (∀ w ∈ W, x' w = x n w) ∧ (∀ w ∈ W, y' w = y n w) := by
  classical
  set 𝔲 : Ultrafilter ℕ := Ultrafilter.of Filter.atTop with h𝔲
  have key : ∀ w : ℤ × ℤ, ∃ p : α × α, {n : ℕ | (x n w, y n w) = p} ∈ 𝔲 := by
    intro w
    obtain ⟨p, hp⟩ :=
      Ultrafilter.eq_pure_of_finite (Ultrafilter.map (fun n : ℕ => (x n w, y n w)) 𝔲)
    refine ⟨p, ?_⟩
    have hmem : ({p} : Set (α × α)) ∈ Ultrafilter.map (fun n : ℕ => (x n w, y n w)) 𝔲 := by
      rw [hp]; exact Ultrafilter.mem_pure.mpr rfl
    rwa [Ultrafilter.mem_map] at hmem
  choose z hz using key
  refine ⟨fun w => (z w).1, fun w => (z w).2, ?_⟩
  intro W M
  have h1 : {n : ℕ | M ≤ n} ∈ 𝔲 := Ultrafilter.of_le Filter.atTop (Filter.mem_atTop M)
  have h2 : (⋂ w ∈ W, {n : ℕ | (x n w, y n w) = z w}) ∈ 𝔲 :=
    (Filter.biInter_finset_mem W).mpr fun w _ => hz w
  obtain ⟨n, hn⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h1 h2)
  have hn2 := hn.2
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hn2
  refine ⟨n, hn.1, fun w hw => ?_, fun w hw => ?_⟩
  · exact (congrArg Prod.fst (hn2 w hw)).symm
  · exact (congrArg Prod.snd (hn2 w hw)).symm

/-- A pointwise subsequential limit of configurations drawn from `orbitClosure c` lies in
`orbitClosure c`: the orbit closure is closed (`Nivat.orbitClosure_closed`). -/
theorem mem_orbitClosure_of_pointwise_limit {α : Type*} {c : Config α} {x : ℕ → Config α}
    {x' : Config α} (hx : ∀ n, x n ∈ orbitClosure c)
    (hlim : ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ n : ℕ, M ≤ n ∧ ∀ w ∈ W, x' w = x n w) :
    x' ∈ orbitClosure c := by
  refine orbitClosure_closed ?_
  intro W
  obtain ⟨n, -, hn⟩ := hlim W 0
  exact ⟨x n, hx n, hn⟩

/-! ### §3. The determinism window -/

/-- An exhaustion of `ℤ × ℤ` by finite sets: `boxUpTo n` is the image of `Finset.range n` under a
fixed enumeration of `ℤ × ℤ`.  Every lattice point lies in `boxUpTo n` for all large `n`, and
the family is monotone in `n`. -/
noncomputable def boxUpTo (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range n).image (Denumerable.eqv (ℤ × ℤ)).symm

theorem mem_boxUpTo {z : ℤ × ℤ} {n : ℕ} (h : Denumerable.eqv (ℤ × ℤ) z < n) :
    z ∈ boxUpTo n := by
  refine Finset.mem_image.mpr ⟨Denumerable.eqv (ℤ × ℤ) z, Finset.mem_range.mpr h, ?_⟩
  simp

/-- **Kari–Moutot §2.2, the determinism window.**

> "by compactness, determinism in direction `u` implies that there is a finite number `k` such
> that already the contents of a configuration in the discrete box `B_u^k` are enough to
> uniquely determine the contents in cell `0`."

Stated with the hypothesis in the form `Nivat.KM.notMem_ONED_iff_det` produces it (determinism
with respect to the **open** half-plane `H_u = {z | ⟨z, u⟩ < 0}`, which is Kari–Moutot's own
convention), and with the conclusion carrying the two properties of the box that §4 actually
consumes: it is finite, and it sits inside `H_u`.

The specific rectangle `B_u^k` of the source is not reconstructed, because nothing downstream
uses its shape — Lemma 14 uses only that `B` is a finite subset of `H_u` determining cell `0`,
and Corollary 15 uses only `|A|^{|B|} < ∞`. -/
theorem exists_window_of_det {α : Type*} [Finite α] {c : Config α} {u : ℝ × ℝ}
    (hdet : ∀ p ∈ orbitClosure c, ∀ q ∈ orbitClosure c,
      (∀ z : ℤ × ℤ, inner2 u z < 0 → p z = q z) → p = q) :
    ∃ B : Finset (ℤ × ℤ), (∀ z ∈ B, inner2 u z < 0) ∧
      ∀ p ∈ orbitClosure c, ∀ q ∈ orbitClosure c,
        (∀ z ∈ B, p z = q z) → p 0 = q 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  -- For each `n`, the finite set `H n = boxUpTo n ∩ H_u` fails to determine cell `0`.
  set H : ℕ → Finset (ℤ × ℤ) := fun n => (boxUpTo n).filter (fun z => inner2 u z < 0) with hH
  have hHsub : ∀ n, ∀ z ∈ H n, inner2 u z < 0 := by
    intro n z hz
    exact (Finset.mem_filter.mp hz).2
  have hfail : ∀ n : ℕ, ∃ p ∈ orbitClosure c, ∃ q ∈ orbitClosure c,
      (∀ z ∈ H n, p z = q z) ∧ p 0 ≠ q 0 := by
    intro n
    obtain ⟨p, hp, q, hq, hagr, hne⟩ := hcon (H n) (hHsub n)
    exact ⟨p, hp, q, hq, hagr, hne⟩
  choose p hp q hq hagr hne using hfail
  -- Take a joint ultrafilter limit of the pairs `(p n, q n)`.
  obtain ⟨p', q', hlim⟩ := exists_pair_limit p q
  have hp' : p' ∈ orbitClosure c :=
    mem_orbitClosure_of_pointwise_limit hp fun W M => (hlim W M).imp fun _ h => ⟨h.1, h.2.1⟩
  have hq' : q' ∈ orbitClosure c :=
    mem_orbitClosure_of_pointwise_limit hq fun W M => (hlim W M).imp fun _ h => ⟨h.1, h.2.2⟩
  -- The limits still differ at the origin, ...
  have hne' : p' 0 ≠ q' 0 := by
    obtain ⟨n, -, h1, h2⟩ := hlim {0} 0
    rw [h1 0 (Finset.mem_singleton_self _), h2 0 (Finset.mem_singleton_self _)]
    exact hne n
  -- ... but agree on the whole open half-plane, contradicting determinism.
  have hagr' : ∀ z : ℤ × ℤ, inner2 u z < 0 → p' z = q' z := by
    intro z hz
    set k : ℕ := Denumerable.eqv (ℤ × ℤ) z with hk
    obtain ⟨n, hnk, h1, h2⟩ := hlim {z} (k + 1)
    have hzH : z ∈ H n :=
      Finset.mem_filter.mpr ⟨mem_boxUpTo (by omega), hz⟩
    rw [h1 z (Finset.mem_singleton_self _), h2 z (Finset.mem_singleton_self _)]
    exact hagr n z hzH
  exact hne' (congrFun (hdet p' hp' q' hq' hagr') 0)

/-- The determinism window in `ONED` vocabulary: a non-zero direction that is **not** one-sided
nonexpansive admits a finite window inside its open half-plane determining cell `0`.  This is
`exists_window_of_det` composed with the open/closed half-plane dictionary
`Nivat.KM.notMem_ONED_iff_det`. -/
theorem exists_window_of_notMem_ONED {α : Type*} [Finite α] {c : Config α} {u : ℝ × ℝ}
    (hu : u ≠ 0) (hdet : u ∉ ONED c) :
    ∃ B : Finset (ℤ × ℤ), (∀ z ∈ B, inner2 u z < 0) ∧
      ∀ p ∈ orbitClosure c, ∀ q ∈ orbitClosure c,
        (∀ z ∈ B, p z = q z) → p 0 = q 0 :=
  exists_window_of_det ((KM.notMem_ONED_iff_det hu).mp hdet)

end Nivat.KMBox
