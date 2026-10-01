/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.HalfPlaneDoublyPeriodic
import Nivat.External.Colle.RecessionCone

/-!
# Collé item (ii), exhaustion of `ℋ(ℓ^(−))`, and the placement `cL = k·cz`

Lane Amink, 2026-09-19.  Upstream of `RegionSteps.lean`; imports `ChainAssemble.lean`
(Aenvfix's, read only) for `hatOf` and the `ofParts` binder shapes, and
`HalfPlaneDoublyPeriodic.lean` for `nfp_L_of_notDP`.

## What this file is for

`ChainDataGeom.nfp_L` (`ChainGeom.lean`) is "`x_per|{cL ≤ ⟪n_ℓ,·⟫}` is not fully periodic",
stated at the level `cL` that the bundle itself fixes.  `Colle35.wlog_notDP`
(`HalfPlaneDoublyPeriodic.lean`) gives the same statement at the level `cz` of the ambiguity
pair's disagreement line, for the pair's own normal `nℓ`.  `Colle35.nfp_L_of_notDP` transports
the one to the other **provided** `n_ℓ = k • nℓ` with `0 < k` and `cL ≤ k * cz` — the
*placement* of `Â_∞`.  Until now that placement was an unexplained obligation on the producer
(`ChainGeom.lean`, docstring of `nfp_L`: "What is *not* supplied and remains on the
construction is the placement").

This file shows the placement is **not** a separate obligation: it is a consequence of Collé's
`b3_colle2.txt:498`, *"Since `⋃ A_i = ℋ(ℓ^(−))`"*, which in turn is what item (ii) of the chain
(`:474`, *"`B_i` contains both `A_{i-1}` and `[-i+1,i-1]² ∩ ℋ(ℓ^(−))`"*) is for.  Precisely:

* `ItemII B nℓ cz` is the box half of item (ii), with `ℋ(ℓ^(−)) = {cz ≤ ⟪nℓ,·⟫}`.
* `Exhausts A nℓ cz` is `:498` verbatim: `⋃ A_i = {cz ≤ ⟪nℓ,·⟫}`.  ⚠ It is stated on the
  **un-normalised** `A`, as the paper does.  The normalised union `Â_∞ = ⋃ Â_i` is an
  `(ℓ, ℓ_J)`-region (`ahat_halfPlane`), not a half plane; only the `⟪nℓ,·⟫`-*range* survives
  normalisation, because `nℓ ⊥ v_ℓ` (`dot_add_zsmul_of_perp`).
* `exhausts_of_itemII`: item (ii) + `B_i ⊆ ℋ(ℓ^(−))` (item (i)'s "`B_i ∩ ℓ_{B_i} ⊂ ℓ^(−)`") +
  `subBA` + `subStrip` give `Exhausts`.
* `placement_of_exhausts`: from `Exhausts A nℓ cz`, `nℓ` primitive and `⊥ v_ℓ`, `p ∥ v_ℓ`,
  `det p v_J ≠ 0`, and the two `ℓ_ι`-support fields `ahat_halfPlane_L` / `ahat_attained_L`,
  there is `k > 0` with `n_ℓ = k • nℓ` **and `cL = k * cz`** — the *equality* of `:922`
  ("the support line of `Â^(ε)_∞` determined by `ℓ` coincides with `ℓ^(−)`"), not merely the
  inequality `nfp_L_of_notDP` asks for.
* `nfp_L_of_exhausts`: the corollary in exactly the shape of `ofParts`'s `nfp_L` binder, from
  the `cz`-level statement `wlog_notDP` produces.

Everything is stated on the raw parts (`A kk vl p vJ cL`), not on a `cg : ChainDataGeom`, so
that a producer working through `ChainDataGeom.ofParts` can use it *before* the bundle exists;
`ChainDataGeom.cL_eq_of_exhausts` restates the placement on a bundle for readers.

## What this does not do

It does not supply `Exhausts` — that is the producer's item (ii), which (kernel receipt,
`tmp/itemII_probe.lean`, not landed) neither `cgwA` nor `cgg` satisfies for any admissible `nℓ`,
so no existing bundle can be used to test it.  The price of `nfp_L` is now exactly item (ii),
and item (ii) is what the producer has to build anyway (`ChainAssemble.lean`, §5).
-/

set_option autoImplicit false

namespace Nivat.Colle35

open Nivat Nivat.LE2

variable {α : Type*}

/-! ## §1. Item (ii) and exhaustion -/

/-- **Collé item (ii), box half** (`b3_colle2.txt:476`), with `ℋ(ℓ^(−)) = {cz ≤ ⟪nℓ,·⟫}`:
every lattice point of `[-i+1,i-1]²` on the half plane lies in `B i`.  The other half,
`A_{i-1} ⊆ B_i`, is `ChainData.subAB`.

**Index convention (team-lead ruling, 2026-09-19).**  The paper's chain starts at `B' ⊂ B₁`
and quantifies over `i ∈ ℕ = {1,2,…}` (`:38`, `:468`); here `i : ℕ` includes `0`, whose
instance is vacuous (`|z.1| ≤ -1`), so the two are equivalent when Lean's `B 0` is the seed `B'`
(`tmp/amink_itemII_audit.lean`, `itemII_iff_pos`).  If instead Lean's `B 0` is the paper's
`B₁`, this definition is one box *weaker* than the faithful transcription
`|z.1| ≤ i → |z.2| ≤ i → cz ≤ ⟪nℓ,z⟫ → z ∈ B (i+1)`.  Weaker is the safe direction for a
hypothesis, so the definition is kept; but **any producer of `ItemII` must prove the shifted
version and land it through `itemII_shift` below** — proving `ItemII` directly risks proving
something too weak for downstream.  The finite-seed refutation below does not depend on the
convention (`not_itemII_shifted_of_chain`, `tmp/amink_itemII_audit.lean`, not landed). -/
def ItemII (B : ℕ → Set (ℤ × ℤ)) (nℓ : ℤ × ℤ) (cz : ℤ) : Prop :=
  ∀ i : ℕ, ∀ z : ℤ × ℤ, |z.1| ≤ (i : ℤ) - 1 → |z.2| ≤ (i : ℤ) - 1 → cz ≤ dot nℓ z → z ∈ B i

/-- **The producer's entry point** (team-lead ruling, 2026-09-19): the faithful transcription of
`:476` under the convention "Lean `B 0` = paper `B₁`" implies `ItemII`.  Producers prove the
hypothesis of this lemma, never `ItemII` directly. -/
theorem itemII_shift {B : ℕ → Set (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz : ℤ}
    (h : ∀ i : ℕ, ∀ z : ℤ × ℤ, |z.1| ≤ (i : ℤ) → |z.2| ≤ (i : ℤ) → cz ≤ dot nℓ z → z ∈ B (i + 1)) :
    ItemII B nℓ cz := by
  intro i z h1 h2 hz
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exfalso; simp only [Nat.cast_zero, zero_sub] at h1; linarith [abs_nonneg z.1]
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact h j z (by push_cast at h1; linarith) (by push_cast at h2; linarith) hz

/-- **`b3_colle2.txt:498`**: `⋃ A_i = ℋ(ℓ^(−))`. -/
def Exhausts (A : ℕ → Set (ℤ × ℤ)) (nℓ : ℤ × ℤ) (cz : ℤ) : Prop :=
  (⋃ i, A i) = {z | cz ≤ dot nℓ z}

/-- Item (ii) puts the whole half plane into `⋃ B_i`: the point `z` is in the box of side
`|z.1| + |z.2| + 1`. -/
theorem ItemII.halfPlane_subset_iUnion {B : ℕ → Set (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz : ℤ}
    (h : ItemII B nℓ cz) : {z : ℤ × ℤ | cz ≤ dot nℓ z} ⊆ ⋃ i, B i := by
  intro z hz
  refine Set.mem_iUnion.mpr ⟨(|z.1| + |z.2| + 1).toNat, h _ z ?_ ?_ hz⟩ <;>
    rw [Int.toNat_of_nonneg (by positivity)] <;> linarith [abs_nonneg z.1, abs_nonneg z.2]

/-- `⟪nℓ,·⟫` is invariant under translation along `v_ℓ` when `nℓ ⊥ v_ℓ`. -/
theorem dot_add_zsmul_of_perp {nℓ vl : ℤ × ℤ} (hperp : dot nℓ vl = 0) (z : ℤ × ℤ) (t : ℤ) :
    dot nℓ (z + t • vl) = dot nℓ z := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    at hperp ⊢
  linear_combination t * hperp

theorem dot_sub_zsmul_of_perp {nℓ vl : ℤ × ℤ} (hperp : dot nℓ vl = 0) (z : ℤ × ℤ) (t : ℤ) :
    dot nℓ (z - t • vl) = dot nℓ z := by
  rw [sub_eq_add_neg, ← neg_smul, dot_add_zsmul_of_perp hperp]

/-- The half strip along `v_ℓ` does not leave `ℋ(ℓ^(−))`. -/
theorem halfStrip_subset_halfPlane {B : Set (ℤ × ℤ)} {nℓ vl : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0) (hB : ∀ z ∈ B, cz ≤ dot nℓ z) :
    halfStrip B vl ⊆ {z | cz ≤ dot nℓ z} := by
  rintro g ⟨b, hb, t, rfl⟩
  show cz ≤ dot nℓ (b + (t : ℤ) • vl)
  rw [dot_add_zsmul_of_perp hperp]
  exact hB b hb

/-- **Exhaustion from item (ii).**  With `B_i ⊆ ℋ(ℓ^(−))` (item (i)'s support-line clause) and
the chain fields `subBA` / `subStrip`, item (ii) gives `⋃ A_i = ℋ(ℓ^(−))` (`:498`). -/
theorem exhausts_of_itemII {B A : ℕ → Set (ℤ × ℤ)} {nℓ vl : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0)
    (hB : ∀ i, ∀ z ∈ B i, cz ≤ dot nℓ z)
    (subBA : ∀ i, B i ⊆ A i) (subStrip : ∀ i, A i ⊆ halfStrip (B i) vl)
    (hII : ItemII B nℓ cz) : Exhausts A nℓ cz := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact halfStrip_subset_halfPlane hperp (hB i) (subStrip i hi)
  · intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hII.halfPlane_subset_iUnion hz)
    exact Set.mem_iUnion.mpr ⟨i, subBA i hi⟩

/-! ## §2. The `⟪nℓ,·⟫`-range survives normalisation -/

/-- A point of `A_i`, pulled back by `k_i v_ℓ`, is a point of `Â_i`. -/
theorem sub_zsmul_mem_Ahat {A Ahat : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ}
    (hAhat : ∀ i, Ahat i = {z | z + (kk i : ℤ) • vl ∈ A i}) {i : ℕ} {w : ℤ × ℤ}
    (hw : w ∈ A i) : w - (kk i : ℤ) • vl ∈ Ahat i := by
  rw [hAhat, Set.mem_ofPred_eq, sub_add_cancel]
  exact hw

/-- Under exhaustion, every point of `Â_∞` is on the half plane. -/
theorem le_dot_of_mem_Ahat_of_exhausts {A Ahat : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl nℓ : ℤ × ℤ} {cz : ℤ} (hperp : dot nℓ vl = 0)
    (hAhat : ∀ i, Ahat i = {z | z + (kk i : ℤ) • vl ∈ A i})
    (hexh : Exhausts A nℓ cz) {g : ℤ × ℤ} (hg : g ∈ ⋃ i, Ahat i) : cz ≤ dot nℓ g := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
  rw [hAhat, Set.mem_ofPred_eq] at hi
  have hmem : g + (kk i : ℤ) • vl ∈ ⋃ i, A i := Set.mem_iUnion.mpr ⟨i, hi⟩
  rw [hexh, Set.mem_ofPred_eq, dot_add_zsmul_of_perp hperp] at hmem
  exact hmem

/-- Under exhaustion, every level `≥ cz` attained by `⟪nℓ,·⟫` is attained on `Â_∞`. -/
theorem exists_mem_Ahat_dot_eq_of_exhausts {A Ahat : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl nℓ : ℤ × ℤ} {cz : ℤ} (hperp : dot nℓ vl = 0)
    (hAhat : ∀ i, Ahat i = {z | z + (kk i : ℤ) • vl ∈ A i})
    (hexh : Exhausts A nℓ cz) {w : ℤ × ℤ} (hw : cz ≤ dot nℓ w) :
    ∃ g ∈ ⋃ i, Ahat i, dot nℓ g = dot nℓ w := by
  have hmem : w ∈ ⋃ i, A i := by rw [hexh]; exact hw
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  exact ⟨w - (kk i : ℤ) • vl, Set.mem_iUnion.mpr ⟨i, sub_zsmul_mem_Ahat hAhat hi⟩,
    dot_sub_zsmul_of_perp hperp w _⟩

/-! ## §3. The placement -/

/-- `n_ℓ := det p v_J • (-p.2, p.1)` is orthogonal to `p`. -/
theorem dot_nL_self (p vJ : ℤ × ℤ) : dot p (det p vJ • (-p.2, p.1)) = 0 := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- `n_ℓ ≠ 0` as soon as `det p v_J ≠ 0`. -/
theorem nL_ne_zero {p vJ : ℤ × ℤ} (hpvJ : det p vJ ≠ 0) : det p vJ • (-p.2, p.1) ≠ 0 := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_zero, Prod.snd_zero,
    mul_eq_zero, hpvJ, false_or, neg_eq_zero] at h1 h2
  apply hpvJ
  simp [det, h1, h2]

/-- **The placement of `Â_∞`, from exhaustion (`b3_colle2.txt:498` ⇒ `:922`).**

Hypotheses, in the shapes `ChainDataGeom.ofParts` already takes: `hAhat` is `AhatEq`
(`hatOf_eq` for `ofParts`), `hhp` / `hatt` are `ahat_halfPlane_L` / `ahat_attained_L`;
`hvl`, `hdet` are `exists_chainData`'s `hvl_ne`, `hdet_vl`; `hpvJ` is
`ColleReg.det_ne_zero_of_dot vJ_ne dot_nJ_vJ dot_nJ_p`.  The one genuinely new input is
`hexh`, item (ii)'s consequence `:498`.

Conclusion: `n_ℓ = k • nℓ` with `k > 0` and **`cL = k * cz`** — the `ℓ_ι`-support line of
`Â_∞` *is* the disagreement line `ℓ^(−)` (`:922`, "coincides").

Why `nℓ` must be primitive: `cz` is only determined by the half plane `{cz ≤ ⟪nℓ,·⟫}` when
`⟪nℓ,·⟫` is onto `ℤ` (`nℓ = (2,0)`, `cz ∈ {1, 2}` give the same half plane).  The pair's `nℓ`
is the normal of a lattice line, hence primitive in the paper (`:253`); a producer holding a
non-primitive normal rescales it first (`Nivat.exists_primitive_nsmul_eq`). -/
theorem placement_of_exhausts {A Ahat : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl p vJ nℓ : ℤ × ℤ} {cz cL : ℤ}
    (hvl : vl ≠ 0) (hdet : det p vl = 0) (hpvJ : det p vJ ≠ 0)
    (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hAhat : ∀ i, Ahat i = {z | z + (kk i : ℤ) • vl ∈ A i})
    (hexh : Exhausts A nℓ cz)
    (hhp : ∀ g ∈ ⋃ i, Ahat i, cL ≤ dot (det p vJ • (-p.2, p.1)) g)
    (hatt : ∃ g ∈ ⋃ i, Ahat i, dot (det p vJ • (-p.2, p.1)) g = cL) :
    ∃ k : ℤ, 0 < k ∧ det p vJ • (-p.2, p.1) = k • nℓ ∧ cL = k * cz := by
  set nL : ℤ × ℤ := det p vJ • (-p.2, p.1) with hnL
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hpvJ (by simp [det])
  -- `nℓ ⊥ p` because `nℓ ⊥ v_ℓ ∥ p`; `n_ℓ ⊥ p` by construction; so `nℓ ∥ n_ℓ`.
  have hpnℓ : dot p nℓ = 0 :=
    dot_eq_zero_of_det_eq_zero hvl hdet (by rw [dot_comm]; exact hperp)
  have hpar : det nℓ nL = 0 :=
    det_eq_zero_of_dot_eq_zero hp0 hpnℓ (dot_nL_self p vJ)
  obtain ⟨k, hk⟩ := exists_smul_of_det_eq_zero (prim_iff_primitive.mpr hprim) hpar
  have hnLk : nL = k • nℓ := by rw [hk]; rfl
  have hd : ∀ z, dot nL z = k * dot nℓ z := fun z => by rw [hnLk, dot_smul]
  -- `k ≠ 0` since `n_ℓ ≠ 0`.
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact nL_ne_zero hpvJ (by rw [← hnL, hnLk, zero_smul])
  -- `k > 0`: otherwise `⟪n_ℓ,·⟫ = k ⟪nℓ,·⟫` is unbounded below on `Â_∞`, against `hhp`.
  have hkpos : 0 < k := by
    by_contra hneg
    have hkle : k ≤ -1 := by omega
    have hN : 0 < nℓ.1 * nℓ.1 + nℓ.2 * nℓ.2 := by
      have hnℓ0 : nℓ ≠ 0 := hprim.ne_zero
      rcases eq_or_ne nℓ.1 0 with h1 | h1
      · have h2 : nℓ.2 ≠ 0 := fun h2 => hnℓ0 (Prod.ext h1 h2)
        nlinarith [mul_self_pos.mpr h2, mul_self_nonneg nℓ.1]
      · nlinarith [mul_self_pos.mpr h1, mul_self_nonneg nℓ.2]
    set N := nℓ.1 * nℓ.1 + nℓ.2 * nℓ.2 with hNdef
    set t : ℤ := |cz| + |cL| + 1 with ht
    have hdw : dot nℓ (t • nℓ) = t * N := by
      simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hNdef]; ring
    clear_value t N
    have ht0 : 0 ≤ t := by rw [ht]; linarith [abs_nonneg cz, abs_nonneg cL]
    have hN1 : 1 ≤ N := by omega
    have h3 : t ≤ t * N := le_mul_of_one_le_right ht0 hN1
    have htN : cz ≤ t * N := by linarith [le_abs_self cz, abs_nonneg cL]
    obtain ⟨g, hg, hgeq⟩ :=
      exists_mem_Ahat_dot_eq_of_exhausts hperp hAhat hexh (w := t • nℓ) (by rw [hdw]; exact htN)
    have h1 := hhp g hg
    rw [hd, hgeq, hdw] at h1
    -- `k * (t * N) ≤ -(t * N) ≤ -t < -|cL| ≤ cL`
    have h2 : k * (t * N) ≤ -1 * (t * N) :=
      mul_le_mul_of_nonneg_right hkle (by positivity)
    have h4 : cL ≤ -(t * N) := by linarith
    have h5 : cL ≤ -t := by linarith
    have h6 : -|cL| ≤ cL := neg_abs_le cL
    rw [ht] at h5
    linarith [abs_nonneg cz]
  refine ⟨k, hkpos, hnLk, le_antisymm ?_ ?_⟩
  · -- `cL ≤ k * cz`: the level `cz` is attained on `Â_∞`.
    obtain ⟨z₀, hz₀⟩ := dot_surjective (prim_iff_primitive.mpr hprim) cz
    obtain ⟨g, hg, hgeq⟩ :=
      exists_mem_Ahat_dot_eq_of_exhausts hperp hAhat hexh (w := z₀) (le_of_eq hz₀.symm)
    have := hhp g hg
    rwa [hd, hgeq, hz₀] at this
  · -- `k * cz ≤ cL`: the attaining point of `hatt` is on the half plane.
    obtain ⟨g, hg, hgeq⟩ := hatt
    have hge := le_dot_of_mem_Ahat_of_exhausts hperp hAhat hexh hg
    rw [hd] at hgeq
    rw [← hgeq]
    exact mul_le_mul_of_nonneg_left hge hkpos.le

/-- **`nfp_L` from exhaustion.**  Exactly the shape of `ChainDataGeom.ofParts`'s `nfp_L`
binder, from the `cz`-level non-periodicity that `Colle35.wlog_notDP` produces.  The price
of `nfp_L` is therefore item (ii) (through `exhausts_of_itemII`), nothing else. -/
theorem nfp_L_of_exhausts {xper : Config α} {A Ahat : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl p vJ nℓ : ℤ × ℤ} {cz cL : ℤ}
    (hvl : vl ≠ 0) (hdet : det p vl = 0) (hpvJ : det p vJ ≠ 0)
    (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hAhat : ∀ i, Ahat i = {z | z + (kk i : ℤ) • vl ∈ A i})
    (hexh : Exhausts A nℓ cz)
    (hhp : ∀ g ∈ ⋃ i, Ahat i, cL ≤ dot (det p vJ • (-p.2, p.1)) g)
    (hatt : ∃ g ∈ ⋃ i, Ahat i, dot (det p vJ • (-p.2, p.1)) g = cL)
    (hnotDP : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cz ≤ dot nℓ z} h ∧ PeriodicOnWith xper {z | cz ≤ dot nℓ z} h') :
    ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h' := by
  obtain ⟨k, hk, hnL, hcL⟩ :=
    placement_of_exhausts hvl hdet hpvJ hprim hperp hAhat hexh hhp hatt
  exact nfp_L_of_notDP hk hnL hcL.le hnotDP

/-- The placement restated on a bundle, for readers: on any `cg : ChainDataGeom` whose
un-normalised chain exhausts `{cz ≤ ⟪nℓ,·⟫}`, `cg.cL = k * cz`. -/
theorem ChainDataGeom.cL_eq_of_exhausts {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen)
    (hvl : vl ≠ 0) (hdet : det p vl = 0) {nℓ : ℤ × ℤ} (hprim : Primitive nℓ)
    (hperp : dot nℓ vl = 0) {cz : ℤ} (hexh : Exhausts cg.toChainData.A nℓ cz) :
    ∃ k : ℤ, 0 < k ∧ det p cg.vJ • (-p.2, p.1) = k • nℓ ∧ cg.cL = k * cz :=
  placement_of_exhausts hvl hdet
    (ColleReg.det_ne_zero_of_dot cg.vJ_ne cg.dot_nJ_vJ cg.dot_nJ_p) hprim hperp
    cg.toChainData.AhatEq hexh cg.ahat_halfPlane_L cg.ahat_attained_L

/-! ## §4. Item (ii) forces `|B_i| → ∞`, and so contradicts any finite-seed half-strip chain

The question (team-lead, 2026-09-19): does item (ii)'s all-direction growth, on a *finite* seed,
require `B_i` to be unbounded?  The answer is **yes, and more**:

* `ItemII.exists_le_encard`: item (ii) alone (with `nℓ ≠ 0`) makes `(B i).encard` unbounded
  in `i` — every `N`-point subset of the half plane sits in one box `[-i+1,i-1]²`.
* `not_itemII_of_chain`: a chain with `A i ⊆ H_{B_i}(ℓ)` (`subStrip`) and
  `B (i+1) ⊆ H_{A_i}(ℓ)` — in particular `ChainRecursion`'s `B (i+1) := A i` — started from a
  **finite** `B 0` is trapped in `H_{B_0}(ℓ)`, on which `det v_ℓ` is bounded
  (`ChainAsm.det_bounded_on_halfStrip`); the half plane `{cz ≤ ⟪nℓ,·⟫}` is not (its points
  `t • nℓ` have `|det v_ℓ (t • nℓ)| ≥ t`).  So **item (ii) is false** for such a chain, for
  every `cz` and every `nℓ ⊥ v_ℓ`.

Read together with `ChainAsm.not_chainDataGeom_of_chainRecursion` (`ChainAssemble.lean`): that
theorem says the finite-seed recursion produces no `ChainDataGeom`; this section says the same
recursion cannot satisfy item (ii) either.  Item (ii) does not *rescue* the finite-seed reading
— it is *incompatible* with it.  Collé's `B_i` are not obtained by iterating a half-strip step
from one finite seed; item (ii) is an independent growth requirement that the producer has to
build in (the box `[-i+1,i-1]² ∩ ℋ(ℓ^(−))` is added at every stage, `b3_colle2.txt:474`). -/

/-- The half plane `{cz ≤ ⟪nℓ,·⟫}` is infinite: the ray `t ↦ (t + |cz|) • nℓ` lies on it. -/
theorem halfPlane_infinite {nℓ : ℤ × ℤ} (hn : nℓ ≠ 0) (cz : ℤ) :
    ({z : ℤ × ℤ | cz ≤ dot nℓ z}).Infinite := by
  have hN : 0 < dot nℓ nℓ := ColleReg.dot_self_pos hn
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℕ => ((t : ℤ) + |cz|) • nℓ) ?_ ?_
  · intro s t hst
    have h := congrArg (dot nℓ) hst
    simp only [ColleReg.dot_zsmul_right] at h
    have h' := mul_right_cancel₀ hN.ne' h
    exact_mod_cast (by linarith : (s : ℤ) = t)
  · intro t
    show cz ≤ dot nℓ (((t : ℤ) + |cz|) • nℓ)
    rw [ColleReg.dot_zsmul_right]
    have h1 : (t : ℤ) + |cz| ≤ ((t : ℤ) + |cz|) * dot nℓ nℓ :=
      le_mul_of_one_le_right (by positivity) hN
    linarith [le_abs_self cz, Int.natCast_nonneg t]

/-- **Item (ii) forces `|B_i| → ∞`.**  For every `N` some `B i` has at least `N` points:
an `N`-point subset of the half plane lies in the box of side `i := max (|z.1|+|z.2|+1)`. -/
theorem ItemII.exists_le_encard {B : ℕ → Set (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz : ℤ}
    (hII : ItemII B nℓ cz) (hn : nℓ ≠ 0) (N : ℕ) : ∃ i, (N : ℕ∞) ≤ (B i).encard := by
  classical
  obtain ⟨t, hts, htcard⟩ := (halfPlane_infinite hn cz).exists_subset_card_eq N
  set i : ℕ := t.sup (fun z : ℤ × ℤ => (|z.1| + |z.2| + 1).toNat) with hi
  refine ⟨i, ?_⟩
  have hsub : (↑t : Set (ℤ × ℤ)) ⊆ B i := by
    intro z hz
    have hz' : z ∈ t := hz
    have hle : (|z.1| + |z.2| + 1).toNat ≤ i :=
      Finset.le_sup (f := fun z : ℤ × ℤ => (|z.1| + |z.2| + 1).toNat) hz'
    have hle' : (((|z.1| + |z.2| + 1).toNat : ℕ) : ℤ) ≤ (i : ℤ) := Int.ofNat_le.mpr hle
    rw [Int.toNat_of_nonneg (by positivity)] at hle'
    exact hII i z (by linarith [abs_nonneg z.2]) (by linarith [abs_nonneg z.1]) (hts hz)
  calc (N : ℕ∞) = (↑t : Set (ℤ × ℤ)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, htcard]
    _ ≤ _ := Set.encard_le_encard hsub

/-- **Item (ii) is incompatible with a chain trapped in the half strip of a finite set.**
`det v_ℓ` is bounded on `H_{B₀}(ℓ)` for finite `B₀`, but unbounded on the half plane
along `nℓ` (`det v_ℓ nℓ ≠ 0` since `nℓ ⊥ v_ℓ`, `nℓ ≠ 0`). -/
theorem not_itemII_of_halfStrip_finite {B : ℕ → Set (ℤ × ℤ)} {B0 : Set (ℤ × ℤ)}
    {vl nℓ : ℤ × ℤ} (hB0 : B0.Finite) (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0) (hn : nℓ ≠ 0)
    (hstrip : ∀ i, B i ⊆ halfStrip B0 vl) (cz : ℤ) : ¬ ItemII B nℓ cz := by
  intro hII
  obtain ⟨M, hM⟩ := ChainAsm.det_bounded_on_halfStrip hB0 vl
  have hN : 0 < dot nℓ nℓ := ColleReg.dot_self_pos hn
  have hd : det nℓ vl ≠ 0 := ColleReg.det_ne_zero_of_dot hvl hperp hN.ne'
  have hd' : det vl nℓ ≠ 0 := by
    intro h; apply hd; simp only [det] at h ⊢; linarith
  set t : ℤ := |cz| + |M| + 1 with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hz : cz ≤ dot nℓ (t • nℓ) := by
    rw [ColleReg.dot_zsmul_right]
    have := le_mul_of_one_le_right ht0 hN
    linarith [le_abs_self cz, abs_nonneg M]
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hII.halfPlane_subset_iUnion hz)
  obtain ⟨hlo, hhi⟩ := hM _ (hstrip i hi)
  rw [ColleReg.det_smul_right] at hlo hhi
  rcases lt_or_gt_of_ne hd' with hneg | hpos
  · have h1 : t * det vl nℓ ≤ t * (-1) :=
      mul_le_mul_of_nonneg_left (by omega) ht0
    linarith [le_abs_self M, abs_nonneg cz]
  · have h1 : t * 1 ≤ t * det vl nℓ :=
      mul_le_mul_of_nonneg_left (by omega) ht0
    linarith [le_abs_self M, abs_nonneg cz]

/-- **Item (ii) is false for every finite-seed chain with `A i ⊆ H_{B_i}(ℓ)` and
`B (i+1) ⊆ H_{A_i}(ℓ)`**, for every `cz` and every `nℓ ⊥ v_ℓ`.  The chain is trapped in
`H_{B_0}(ℓ)` (`ChainAsm.chain_subset_halfStrip`). -/
theorem not_itemII_of_chain {B A : ℕ → Set (ℤ × ℤ)} {vl nℓ : ℤ × ℤ}
    (hB0 : (B 0).Finite) (hvl : vl ≠ 0) (hperp : dot nℓ vl = 0) (hn : nℓ ≠ 0)
    (subStrip : ∀ i, A i ⊆ halfStrip (B i) vl)
    (hchain : ∀ i, B (i + 1) ⊆ halfStrip (A i) vl) (cz : ℤ) : ¬ ItemII B nℓ cz := by
  refine not_itemII_of_halfStrip_finite hB0 hvl hperp hn (fun i => ?_) cz
  cases i with
  | zero => exact subset_halfStrip _ vl
  | succ i =>
    intro z hz
    exact ChainAsm.halfStrip_halfStrip _ vl
      (ChainAsm.halfStrip_mono (ChainAsm.chain_subset_halfStrip subStrip hchain i) (hchain i hz))

/-- **On a real `ChainData` bundle**: the `subStrip` used here is the field projection
`cd.subStrip` (`Lemma35.lean`), not a transcription.  ⚠ `hchain` is **not** a `ChainData`
field — `ChainData` only has `subAB : A i ⊆ B (i+1)`, the *reverse* inclusion.  `hchain` is
exactly `ChainRecursion`'s construction choice `B (i+1) := A i`.  So this does **not** refute
`ChainData`'s field table; it refutes `ChainData` + finite seed + `hchain`. -/
theorem ChainData.not_itemII_of_chain {η xper : Config α} {vl : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cd : ChainData η xper vl S gen)
    (hB0 : (cd.B 0).Finite) (hvl : vl ≠ 0) {nℓ : ℤ × ℤ} (hperp : dot nℓ vl = 0) (hn : nℓ ≠ 0)
    (hchain : ∀ i, cd.B (i + 1) ⊆ halfStrip (cd.A i) vl) (cz : ℤ) : ¬ ItemII cd.B nℓ cz :=
  Nivat.Colle35.not_itemII_of_chain hB0 hvl hperp hn cd.subStrip hchain cz

/-- **`ChainRecursion`'s chain never satisfies item (ii)** from a finite seed — the recursion
`B (i+1) := A i` (`ColleReg4.chainB_succ_eq_chainA`) is exactly the `hchain` of
`not_itemII_of_chain`.  Companion to `ChainAsm.not_chainDataGeom_of_chainRecursion`. -/
theorem not_itemII_chainB (ξ xper : Config ℤ) (S : Finset (ℤ × ℤ)) (vl u₀ : ℤ × ℤ)
    (hstep : ColleReg4.StepHyp ξ xper S vl u₀)
    (B0 : Set (ℤ × ℤ)) (hB0 : EnvOf (↑S : Set (ℤ × ℤ)) B0)
    (hagree0 : ∀ z ∈ B0, T u₀ ξ z = xper z) (hB0fin : B0.Finite) (hvl : vl ≠ 0)
    {nℓ : ℤ × ℤ} (hperp : dot nℓ vl = 0) (hn : nℓ ≠ 0) (cz : ℤ) :
    ¬ ItemII (ColleReg4.chainB ξ xper S vl u₀ hstep B0 hB0 hagree0) nℓ cz :=
  not_itemII_of_chain (A := ColleReg4.chainA ξ xper S vl u₀ hstep B0 hB0 hagree0)
    hB0fin hvl hperp hn (ColleReg4.subStrip_chain ξ xper S vl u₀ hstep B0 hB0 hagree0)
    (fun i => by
      rw [ColleReg4.chainB_succ_eq_chainA]
      exact subset_halfStrip _ vl) cz

/-! ## §5. The whole `ℓ_ι` side of `ofParts` from exhaustion and `rec_vJ`

`ChainDataGeom.ofParts` (`ChainAssemble.lean:211-216`) asks the producer for four things on
the `ℓ_ι` side: a level `cL`, `ahat_halfPlane_L`, `ahat_attained_L`, and `nfp_L`.  §3 showed
that *given* the first three, `nfp_L` costs only item (ii).  This section shows the first
three cost only item (ii) **and `rec_vJ`** (which the producer owes anyway): the level is
`cL := k * cz`, and the missing sign `0 < k` is exactly `0 < ⟪nℓ, v_J⟫`, which `rec_vJ` forces
because `Â_∞` cannot recede below its own half plane.  So the `ℓ_ι` side of `ofParts` is
entirely a consequence of `Exhausts` + `rec_vJ` + the pair's `¬DP`; nothing on it is a
separate obligation. -/

/-- **`⟪nℓ, v_J⟫ > 0` from exhaustion and recession along `v_J`.**  Zero is impossible
(`v_J ∥ p` would contradict `det p v_J ≠ 0`); negative would push a point at level `cz`
below `cz` by one step of `rec_vJ`. -/
theorem dot_vJ_pos_of_exhausts {A Ahat : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl p vJ nℓ : ℤ × ℤ} {cz : ℤ}
    (hvl : vl ≠ 0) (hdet : det p vl = 0) (hpvJ : det p vJ ≠ 0)
    (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hAhat : ∀ i, Ahat i = {z | z + (kk i : ℤ) • vl ∈ A i})
    (hexh : Exhausts A nℓ cz)
    (rec_vJ : ∀ g ∈ ⋃ i, Ahat i, g + vJ ∈ ⋃ i, Ahat i) : 0 < dot nℓ vJ := by
  have hn0 : nℓ ≠ 0 := hprim.ne_zero
  have hpnℓ : dot p nℓ = 0 :=
    dot_eq_zero_of_det_eq_zero hvl hdet (by rw [dot_comm]; exact hperp)
  obtain ⟨z₀, hz₀⟩ := dot_surjective (prim_iff_primitive.mpr hprim) cz
  obtain ⟨g, hg, hgeq⟩ :=
    exists_mem_Ahat_dot_eq_of_exhausts hperp hAhat hexh (w := z₀) (le_of_eq hz₀.symm)
  rcases lt_trichotomy 0 (dot nℓ vJ) with h | h | h
  · exact h
  · exfalso
    exact hpvJ (det_eq_zero_of_dot_eq_zero hn0 (by rw [dot_comm]; exact hpnℓ) h.symm)
  · exfalso
    have hle := le_dot_of_mem_Ahat_of_exhausts hperp hAhat hexh (rec_vJ g hg)
    rw [dot_add] at hle
    linarith

/-- **The `ℓ_ι` side of `ChainDataGeom.ofParts`, from exhaustion and `rec_vJ`.**  Exactly the
binder shapes of `cL` / `ahat_halfPlane_L` / `ahat_attained_L` / `nfp_L`
(`ChainAssemble.lean:211-216`, with `Ahat := hatOf A kk vl`), with `cL = k * cz` for the
`k > 0` of `n_ℓ = k • nℓ`.  The producer supplies `Exhausts` (item (ii) through
`exhausts_of_itemII`), `rec_vJ`, and the pair's `hnotDP` (`exists_preamble_pair`'s last
conjunct); nothing else on this side. -/
theorem ell_side_of_exhausts {xper : Config α} {A Ahat : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {vl p vJ nℓ : ℤ × ℤ} {cz : ℤ}
    (hvl : vl ≠ 0) (hdet : det p vl = 0) (hpvJ : det p vJ ≠ 0)
    (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hAhat : ∀ i, Ahat i = {z | z + (kk i : ℤ) • vl ∈ A i})
    (hexh : Exhausts A nℓ cz)
    (rec_vJ : ∀ g ∈ ⋃ i, Ahat i, g + vJ ∈ ⋃ i, Ahat i)
    (hnotDP : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cz ≤ dot nℓ z} h ∧ PeriodicOnWith xper {z | cz ≤ dot nℓ z} h') :
    ∃ (k cL : ℤ), 0 < k ∧ det p vJ • (-p.2, p.1) = k • nℓ ∧ cL = k * cz ∧
      (∀ g ∈ ⋃ i, Ahat i, cL ≤ dot (det p vJ • (-p.2, p.1)) g) ∧
      (∃ g ∈ ⋃ i, Ahat i, dot (det p vJ • (-p.2, p.1)) g = cL) ∧
      ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
        PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h ∧
        PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h' := by
  set nL : ℤ × ℤ := det p vJ • (-p.2, p.1) with hnL
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hpvJ (by simp [det])
  have hpnℓ : dot p nℓ = 0 :=
    dot_eq_zero_of_det_eq_zero hvl hdet (by rw [dot_comm]; exact hperp)
  have hpar : det nℓ nL = 0 :=
    det_eq_zero_of_dot_eq_zero hp0 hpnℓ (dot_nL_self p vJ)
  obtain ⟨k, hk⟩ := exists_smul_of_det_eq_zero (prim_iff_primitive.mpr hprim) hpar
  have hnLk : nL = k • nℓ := by rw [hk]; rfl
  have hd : ∀ z, dot nL z = k * dot nℓ z := fun z => by rw [hnLk, dot_smul]
  -- `⟪n_ℓ, v_J⟫ = (det p v_J)² > 0` and `⟪nℓ, v_J⟫ > 0` force `k > 0`.
  have hvJ : 0 < dot nℓ vJ :=
    dot_vJ_pos_of_exhausts hvl hdet hpvJ hprim hperp hAhat hexh rec_vJ
  have hnLvJ : 0 < dot nL vJ := by
    have h1 : dot nL vJ = det p vJ * det p vJ := by
      simp only [hnL, dot, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [h1]; exact mul_self_pos.mpr hpvJ
  have hkpos : 0 < k := by
    rw [hd] at hnLvJ
    by_contra hneg
    have hk0 : k ≤ 0 := not_lt.mp hneg
    nlinarith
  refine ⟨k, k * cz, hkpos, hnLk, rfl, ?_, ?_, ?_⟩
  · intro g hg
    rw [hd]
    exact mul_le_mul_of_nonneg_left (le_dot_of_mem_Ahat_of_exhausts hperp hAhat hexh hg) hkpos.le
  · obtain ⟨z₀, hz₀⟩ := dot_surjective (prim_iff_primitive.mpr hprim) cz
    obtain ⟨g, hg, hgeq⟩ :=
      exists_mem_Ahat_dot_eq_of_exhausts hperp hAhat hexh (w := z₀) (le_of_eq hz₀.symm)
    exact ⟨g, hg, by rw [hd, hgeq, hz₀]⟩
  · exact nfp_L_of_notDP hkpos hnLk le_rfl hnotDP

/-! ## §6. Item (ii) against the `ofParts` binder table (measurement, 2026-09-19)

Which of `ChainDataGeom.ofParts`'s obligations (`ChainAssemble.lean:182-216`) does item (ii)
discharge?  Exactly these, in the binder shapes, with `Ahat := hatOf A kk vl`:

* `ahat_nonempty` (`:192`) — from `ItemII` + `subBA` alone;
* the datum `cL` and the three `ℓ_ι` obligations `ahat_halfPlane_L` / `ahat_attained_L` /
  `nfp_L` (`:211-216`) — from `ItemII` + item (i)'s half-plane clause `hB` + `subBA` + `maxA`
  (for `subStrip`) + `rec_vJ` + the pair's `hnotDP`.

Nothing else on the table is a *lower* bound on `B`, so nothing else can follow from item (ii)
(reading, not a kernel fact).  In particular `subAB : A i ⊆ B (i+1)` is item (ii)'s other
half and stays a separate field. -/

/-- `ahat_nonempty` (`ChainAssemble.lean:192`) from item (ii): the half plane is nonempty, so
some `B i`, hence `A i`, hence `Â_i`, is. -/
theorem ahat_nonempty_of_itemII {B A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nℓ : ℤ × ℤ} {cz : ℤ}
    (hn : nℓ ≠ 0) (subBA : ∀ i, B i ⊆ A i) (hII : ItemII B nℓ cz) :
    (⋃ i, hatOf A kk vl i).Nonempty := by
  obtain ⟨z, hz⟩ := (halfPlane_infinite hn cz).nonempty
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hII.halfPlane_subset_iUnion hz)
  exact ⟨z - (kk i : ℤ) • vl, Set.mem_iUnion.mpr ⟨i, sub_zsmul_mem_Ahat hatOf_eq (subBA i hi)⟩⟩

/-- **The `ℓ_ι` block of `ofParts` from item (ii)**, with `maxA` in `ofParts`'s own shape
(`ChainAssemble.lean:184`) supplying `subStrip`.  `ell_side_of_exhausts` through
`exhausts_of_itemII`. -/
theorem ell_side_of_itemII {η xper : Config α} {Env : Set (ℤ × ℤ) → Prop}
    {B A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ} {vl p vJ nℓ : ℤ × ℤ} {cz : ℤ}
    (hvl : vl ≠ 0) (hdet : det p vl = 0) (hpvJ : det p vJ ≠ 0)
    (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hB : ∀ i, ∀ z ∈ B i, cz ≤ dot nℓ z)
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i)
    (hII : ItemII B nℓ cz)
    (rec_vJ : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + vJ ∈ ⋃ i, hatOf A kk vl i)
    (hnotDP : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cz ≤ dot nℓ z} h ∧ PeriodicOnWith xper {z | cz ≤ dot nℓ z} h') :
    ∃ (k cL : ℤ), 0 < k ∧ det p vJ • (-p.2, p.1) = k • nℓ ∧ cL = k * cz ∧
      (∀ g ∈ ⋃ i, hatOf A kk vl i, cL ≤ dot (det p vJ • (-p.2, p.1)) g) ∧
      (∃ g ∈ ⋃ i, hatOf A kk vl i, dot (det p vJ • (-p.2, p.1)) g = cL) ∧
      ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
        PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h ∧
        PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h' :=
  ell_side_of_exhausts hvl hdet hpvJ hprim hperp (fun i => hatOf_eq i)
    (exhausts_of_itemII hperp hB subBA (subStrip_of_max maxA) hII) rec_vJ hnotDP


/-! ## §7. `rec_vJ` does **not** reduce to item (ii) (kernel counter-model, 2026-09-19)

Question (team-lead): is `ofParts`'s `rec_vJ` (`ChainAssemble.lean:210`) a consequence of item
(ii) the way the `ℓ_ι` block (§5–§6) is?  **No.**  The model below satisfies every `ofParts`
binder that does not mention `Env / η / xper / S / gen / F` — `subBA subAB AhatMono hsweep hfin
hhp hswept ahat_nonempty` — plus `ItemII`, item (i)'s half-plane clause, `subStrip`,
`Exhausts`, and the vector-side facts (`vl ≠ 0`, `det p vl = 0`, `det p vJ ≠ 0`, `Primitive nℓ`,
`dot nℓ vl = 0`, `dot nJ vJ = 0`, `0 < dot nℓ vJ`, `vJ`/`nJ` primitive), and `rec_vJ` is
**false**: `Â_∞ = {z.1 ≤ -2, z.1 ≤ z.2 ≤ 0} ∪ {(0,0)}` has the isolated vertex `(0,0)`, from
which `v_J = (-1,0)` leaves the set.

Data: `vl = p = (1,1)`, `kk i = 2i`, `nℓ = (-1,1)`, `cz = 0`, `nJ = (0,-1)`, `cJ = 0`,
`vJ = (-1,0)`, `vJ1 = (0,1)`, `B := A`, `A i := Â_i + (2i,2i)`.  The box
`[-i+1,i-1]² ∩ {z.1 ≤ z.2}` translates into the wedge (`-3i+1 ≤ z.1 ≤ z.2 ≤ -i-1`), so item (ii)
holds and never sees `(0,0)`.

⚠ Scope (§21): the model is **not** lattice-convex, so it does not refute "`rec_vJ` from
item (ii) + `hc_env`" — lattice-convexity of `Â_∞` is available on the chain
(`ColleReg.region_latticeConvex`, `RegionSteps.lean:1810`, from `Env = EnvOf ↑S`).  What it
shows is that the *direction* `v_J` is not chosen by item (ii): in the paper it is the
`:500-506` selection of `J` (the edge `w_i(J)` whose length grows), and the ray-to-recession
step is `Claim414.rec_of_rayIn` (`Claim414EllPrime.lean:35`), which needs convexity **and** a
`v_J`-ray in `Â_∞`.  The ray is the producer's genuinely new input. -/

namespace RecVJModel

open Nivat.MaxEnv

/-- `Â_i`. -/
def Ah (i : ℕ) : Set (ℤ × ℤ) :=
  {z | (-3 * (i : ℤ) ≤ z.1 ∧ z.1 ≤ -2 ∧ z.1 ≤ z.2 ∧ z.2 ≤ 0) ∨ z = (0, 0)}

/-- `A_i = Â_i + 2i·(1,1)`. -/
def Aw (i : ℕ) : Set (ℤ × ℤ) := {z | z - (2 * (i : ℤ), 2 * (i : ℤ)) ∈ Ah i}

def kw (i : ℕ) : ℕ := 2 * i

theorem hatOf_Aw (i : ℕ) : hatOf Aw kw (1, 1) i = Ah i := by
  ext z
  simp only [hatOf, Aw, kw, Set.mem_ofPred_eq]
  have : z + ((2 * i : ℕ) : ℤ) • ((1 : ℤ), (1 : ℤ)) - (2 * (i : ℤ), 2 * (i : ℤ)) = z := by
    ext <;> simp
  rw [this]

theorem itemII_Aw : ItemII Aw (-1, 1) 0 := by
  intro i z h1 h2 hz
  simp only [Aw, Ah, Set.mem_ofPred_eq, dot, Prod.fst_sub, Prod.snd_sub] at hz ⊢
  rw [abs_le] at h1 h2
  left
  omega

theorem hB_Aw : ∀ i, ∀ z ∈ Aw i, (0 : ℤ) ≤ dot (-1, 1) z := by
  intro i z hz
  simp only [Aw, Ah, Set.mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub, Prod.ext_iff] at hz
  simp only [dot]
  rcases hz with h | h <;> omega

theorem ahatMono_Aw : ∀ i j, i ≤ j → hatOf Aw kw (1, 1) i ⊆ hatOf Aw kw (1, 1) j := by
  intro i j hij z hz
  rw [hatOf_Aw] at hz ⊢
  simp only [Ah, Set.mem_ofPred_eq] at hz ⊢
  rcases hz with h | h
  · left; have : (i : ℤ) ≤ j := by exact_mod_cast hij
    omega
  · right; exact h

theorem hfin_Aw : ∀ i, (hatOf Aw kw (1, 1) i).Finite := by
  intro i
  rw [hatOf_Aw]
  refine ((Finset.Icc (-3 * (i : ℤ)) 0 ×ˢ Finset.Icc (-3 * (i : ℤ)) 0).finite_toSet).subset ?_
  intro z hz
  simp only [Ah, Set.mem_ofPred_eq, Prod.ext_iff] at hz
  simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
  rcases hz with h | h <;> omega

theorem hhp_Aw : ∀ i, hatOf Aw kw (1, 1) i ⊆ halfPlaneGE (0, -1) 0 := by
  intro i z hz
  rw [hatOf_Aw] at hz
  simp only [Ah, Set.mem_ofPred_eq, Prod.ext_iff] at hz
  simp only [halfPlaneGE, Set.mem_ofPred_eq, dot]
  rcases hz with h | h <;> omega

theorem hswept_Aw : SweptClosed (⋃ i, hatOf Aw kw (1, 1) i) (0, 1) (0, -1) 0 := by
  intro g hg t ht
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  rw [hatOf_Aw] at hi ⊢
  simp only [Ah, Set.mem_ofPred_eq, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, dot] at hi ht ⊢
  rcases hi with h | h
  · left; omega
  · right; omega

theorem ahat_nonempty_Aw : (⋃ i, hatOf Aw kw (1, 1) i).Nonempty :=
  ⟨(0, 0), Set.mem_iUnion.mpr ⟨0, by rw [hatOf_Aw]; exact Or.inr rfl⟩⟩

theorem exhausts_Aw : Exhausts Aw (-1, 1) 0 :=
  exhausts_of_itemII (nℓ := (-1, 1)) (vl := (1, 1)) (by simp [dot]) hB_Aw (fun _ => le_rfl)
    (fun i => Nivat.LE2.subset_halfStrip _ _) itemII_Aw

/-- **`rec_vJ` fails.** -/
theorem not_rec_vJ_Aw :
    ¬ ∀ g ∈ ⋃ i, hatOf Aw kw (1, 1) i, g + (-1, 0) ∈ ⋃ i, hatOf Aw kw (1, 1) i := by
  intro h
  have h0 : ((0 : ℤ), (0 : ℤ)) ∈ ⋃ i, hatOf Aw kw (1, 1) i :=
    Set.mem_iUnion.mpr ⟨0, by rw [hatOf_Aw]; exact Or.inr rfl⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h _ h0)
  rw [hatOf_Aw] at hi
  simp only [Ah, Set.mem_ofPred_eq, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at hi
  omega

/-- The vector-side facts of `exists_chainData` / `ofParts` all hold in the model. -/
theorem vectors_Aw :
    ((1 : ℤ), (1 : ℤ)) ≠ 0 ∧ det (1, 1) (1, 1) = 0 ∧ det (1, 1) (-1, 0) ≠ 0 ∧
    Primitive ((-1 : ℤ), (1 : ℤ)) ∧ dot (-1, 1) (1, 1) = 0 ∧ dot (0, -1) (-1, 0) = 0 ∧
    dot (0, -1) (0, 1) < 0 ∧ 0 < dot (-1, 1) (-1, 0) ∧ Primitive ((-1 : ℤ), (0 : ℤ)) ∧
    Primitive ((0 : ℤ), (-1 : ℤ)) := by
  refine ⟨by decide, by decide, by decide, ?_, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · exact ⟨0, 1, by norm_num⟩
  · exact ⟨-1, 0, by norm_num⟩
  · exact ⟨0, -1, by norm_num⟩

end RecVJModel

/-! ## §8. The `v_J`-ray: statement, its producer inside `bottom`, and the `J`-selection

Team-lead ruling (2026-09-19): the `v_J`-ray `∃ z₀, ∀ k : ℕ, z₀ + k • vJ ∈ Â_∞` replaces
`rec_vJ` as the explicit `ofParts` binder, `rec_vJ` being derived from lattice-convexity.

**Measurement first.**  The ray is *already inside* `ofParts`'s data: conjunct (ii) of `bottom`
at `ε = 0` (`ChainAssemble.lean:201-203`) puts the half-line `z₀ + k • vJ`, `k ≥ L`, at level
`cJ - 1` into `MaxEnv.reachSet Â_∞ vJ1`, and `hswept` (`:191`) pulls it back one `vJ1`-step into
`Â_∞` itself (`ray_of_bottom_swept`).  So the ray is **not a new obligation** — it is
`bottom` (ii) + `hswept` + `hhp` + `hsweep`; and `rec_vJ` is those plus convexity
(`rec_vJ_of_bottom`, slot-checked against `ofParts`'s binders below).  What remains unpaid is
`bottom` itself (`ANormal.not_bottom_of_shell_data`: not derivable from the shell data).
Reading (not a kernel fact): replacing `rec_vJ` by a ray binder would add a *redundant*
obligation; the honest edit is to **delete** `rec_vJ` from `ofParts` and derive it.

**The `J`-selection** (`b3_colle2.txt:500-506`) is what produces `bottom` (ii)/the ray in the
paper: `J` is the *least* index with `|Â_i ∩ w_i(J)| < |Â_{i+1} ∩ w_{i+1}(J)|` infinitely
often.  Minimality is load-bearing: for `ι+1 ≤ j ≤ J-1` the edge lengths are then eventually
constant, so — chained from the pinned point `g₁` of the `ℓ`-edge (`:488`) — the `ℓ_J`-edge
of every `Â_i` **starts at one fixed lattice point `g_J`** and grows in the `+v_J` direction.
The honest Lean transcription is `ray_of_pinned_growth`'s hypothesis `hgrow`.  The un-pinned
reading "the face cardinality is unbounded" is **not** enough: `NoPinModel` below is a
lattice-convex nested chain with `|Â_i ∩ w_i(J)| → ∞` and no `+v_J`-ray. -/

/-- **The `v_J`-ray from `bottom` (ii) and `hswept`.**  Hypotheses in `ofParts`'s shapes
(`hd` = `hsweep`, `hR` = `hhp` on the union, `hz₀`/`hline` = `bottom 0`'s first two
conjuncts, `hvJ` = `F.dot_nJ_vJ`).  A point of the reached half-line at level `cJ - 1` is
`g + t • vJ1` with `g ∈ R`; since `dot nJ g ≥ cJ > cJ - 1` and `dot nJ vJ1 < 0`, `t ≥ 1`, and
`hswept` at `t - 1` keeps `g + (t-1) • vJ1 = (z₀ + k • vJ) - vJ1` in `R`.  The ray base is
`z₀ - vJ1 + L • vJ`. -/
theorem ray_of_bottom_swept {R : Set (ℤ × ℤ)} {vJ1 nJ vJ z₀ : ℤ × ℤ} {cJ L : ℤ}
    (hd : dot nJ vJ1 < 0) (hR : ∀ g ∈ R, cJ ≤ dot nJ g)
    (hswept : MaxEnv.SweptClosed R vJ1 nJ cJ)
    (hz₀ : dot nJ z₀ = cJ - 1) (hvJ : dot nJ vJ = 0)
    (hline : ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet R vJ1) :
    ∀ k : ℕ, (z₀ - vJ1 + L • vJ) + (k : ℤ) • vJ ∈ R := by
  intro k
  obtain ⟨g, hg, t, ht⟩ := MaxEnv.mem_reachSet.mp (hline (L + k) (by omega))
  have hlev : dot nJ (z₀ + (L + (k : ℤ)) • vJ) = cJ - 1 := by
    rw [dot_add, ColleReg.dot_zsmul_right, hvJ, mul_zero, add_zero, hz₀]
  have hgt : dot nJ g + (t : ℤ) * dot nJ vJ1 = cJ - 1 := by
    rw [← hlev, ht, dot_add, ColleReg.dot_zsmul_right]
  have hg0 := hR g hg
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = s + 1 := by
    refine ⟨t - 1, ?_⟩
    rcases Nat.eq_zero_or_pos t with rfl | h
    · exfalso; simp at hgt; omega
    · omega
  have hmem : g + (s : ℤ) • vJ1 ∈ R := by
    refine hswept g hg s ?_
    rw [dot_add, ColleReg.dot_zsmul_right]
    push_cast at hgt
    nlinarith
  convert hmem using 1
  have h2 : z₀ - vJ1 + L • vJ + (k : ℤ) • vJ = z₀ + (L + (k : ℤ)) • vJ - vJ1 := by
    rw [add_smul]; abel
  rw [h2, ht]; push_cast; rw [add_smul, one_smul]; abel

/-- **`rec_vJ` from a `v_J`-ray and lattice-convexity.**

⭐ **2026-09-26 去重（lane-tower-hlev，集成者派工）：本条现在是转发，正本是
`Nivat.RecessionCone.recession_of_ray`（`RecessionCone.lean`）。**保留本名是因为它有 18 个
直接消费者（盲区 3：撞名/断链风险），**不删**。

正本为什么选 `RecessionCone` 那份而不是这份：它是**链上真正被消费**的那份
（`RegionSteps.lean` 的 `region_case1` 一段与 `exists_case2_window` 一段都直接调它），
并且它位置最上游（只 import `LatticeEdges`），所以让另两份转发过来的 import 代价是
**各加 1 个模块**；反过来把它转发到本条则要给 `Claim414EllPrime` 加 26 个。

⚠ **一名多物**：正本所在的 `RecessionCone.lean` 与被禁读的 `ConeRecession.lean` 是两个
不同文件（名字互为颠倒），本文件 import 的是前者。

⚠ **旧 docstring 的理由是错的，已订正（`PROTOCOL §57` B 类引用腐烂）**：原文写
「`Claim414EllPrime` 位于 `RegionSteps` 下游、装配点无法 import」。方向反了——
实测 `RegionSteps` 传递 import 了 `Claim414EllPrime`，不是相反；两者其实是兄弟模块，
互相 import 都不成环。真正的理由只是代价，见上。 -/
theorem rec_of_ray {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R) {z₀ d : ℤ × ℤ}
    (hray : ∀ k : ℕ, z₀ + (k : ℤ) • d ∈ R) : ∀ g ∈ R, g + d ∈ R :=
  Nivat.RecessionCone.recession_of_ray hR hray

/-- **`rec_vJ` is derivable inside `ofParts`** from `bottom` (its `ε = 0` instance, first two
conjuncts), `hsweep`, `hhp`, `F.dot_nJ_vJ`, and lattice-convexity of `Â_∞` (free on the chain:
`ColleReg.region_latticeConvex`, `RegionSteps.lean:1810`).  Stated on the raw union `R`; `a`
abstracts `F.a`; the third and fourth conjuncts of `bottom` are carried only so the binder
matches `ChainAssemble.lean:201-207` verbatim. -/
theorem rec_vJ_of_bottom {R : Set (ℤ × ℤ)} {vJ1 nJ vJ a : ℤ × ℤ} {cJ : ℤ}
    {S : Finset (ℤ × ℤ)} {shellInf : ℕ → Set (ℤ × ℤ)}
    (hconv : IsLatticeConvexRegion R)
    (hd : dot nJ vJ1 < 0) (hR : ∀ g ∈ R, cJ ≤ dot nJ g)
    (hswept : MaxEnv.SweptClosed R vJ1 nJ cJ) (hvJ : dot nJ vJ = 0)
    (bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet R vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet R vJ1) ∧
      (∀ z ∈ shellInf (ε + 1), z ∈ shellInf ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ)) :
    ∀ g ∈ R, g + vJ ∈ R := by
  obtain ⟨z₀, L, hz₀, hline, -, -⟩ := bottom 0
  simp only [Nat.cast_zero, sub_zero] at hz₀
  exact rec_of_ray hconv (ray_of_bottom_swept hd hR hswept hz₀ hvJ hline)

/-- **`b3_colle2.txt:500-506`, pinned form.**  If for every `N` the initial segment
`g_J + t • vJ`, `t ≤ N`, of the `ℓ_J`-edge lies in some `Â_i`, then `Â_∞` contains the ray
from `g_J`.  The hypothesis is what the *least* `J` buys (§8 header): the edge's start is the
fixed point `g_J`, only its `+v_J` end moves.  Trivial once stated — the content of the
selection is in producing `hgrow`, not in this lemma. -/
theorem ray_of_pinned_growth {Ahat : ℕ → Set (ℤ × ℤ)} {g vJ : ℤ × ℤ}
    (hgrow : ∀ N : ℕ, ∃ i, ∀ t : ℕ, t ≤ N → g + (t : ℤ) • vJ ∈ Ahat i) :
    ∀ k : ℕ, g + (k : ℤ) • vJ ∈ ⋃ i, Ahat i := by
  intro k
  obtain ⟨i, hi⟩ := hgrow k
  exact Set.mem_iUnion.mpr ⟨i, hi k le_rfl⟩

/-- **Slot check**: `rec_vJ_of_bottom` consumes `ofParts`'s binders verbatim (`hsweep hhp hswept
F.dot_nJ_vJ bottom`, `ChainAssemble.lean:188-207`) plus one extra, lattice-convexity of `Â_∞`,
and produces `rec_vJ` (`:210`) in its exact type. -/
example {α : Type*} (_η _xper : Config α) (vl _p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (_gen : ℤ × ℤ)
    (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vJ1 nJ : ℤ × ℤ) (cJ : ℤ)
    (hsweep : dot nJ vJ1 < 0)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hswept : MaxEnv.SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (vJ : ℤ × ℤ) (F : FaceBlock S nJ vJ)
    (bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • vJ + (b - F.a) ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ (ε + 1),
        z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ))
    (hconv : IsLatticeConvexRegion (⋃ i, hatOf A kk vl i)) :
    ∀ g ∈ ⋃ i, hatOf A kk vl i, g + vJ ∈ ⋃ i, hatOf A kk vl i :=
  rec_vJ_of_bottom hconv hsweep (fun _ hg => Set.iUnion_subset hhp hg) hswept F.dot_nJ_vJ bottom

/-! ### `NoPinModel`: unbounded face cardinality alone gives no `+v_J`-ray

Boxes `[-i, 0] × [0, i]`: nested, finite, lattice-convex union (the closed quadrant
`{z.1 ≤ 0, 0 ≤ z.2}`), swept-closed for `vJ1 = (0,-1)`, `nJ = (0,1)`, `cJ = 0`, with the
`ℓ_J`-face `{y = 0}` of cardinality `i + 1 → ∞` — but growing in the `-(1,0)` direction.  No
`+(1,0)`-ray exists, and `bottom` (ii) fails for `vJ = (1,0)`.  So the un-pinned reading of
`:500-504` ("`|Â_i ∩ w_i(J)|` unbounded") is **not** the statement that produces the ray;
the pinning of the edge's start (`:488`'s `g₁`, propagated through the eventually-constant
edges `ι+1 ≤ j ≤ J-1` that minimality of `J` provides) is load-bearing. -/
namespace NoPinModel

def Ah (i : ℕ) : Set (ℤ × ℤ) := {z | -(i : ℤ) ≤ z.1 ∧ z.1 ≤ 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ (i : ℤ)}

theorem mono : ∀ i j, i ≤ j → Ah i ⊆ Ah j := by
  intro i j hij z hz
  simp only [Ah, Set.mem_ofPred_eq] at hz ⊢
  have : (i : ℤ) ≤ j := by exact_mod_cast hij
  omega

theorem finite (i : ℕ) : (Ah i).Finite := by
  refine ((Finset.Icc (-(i : ℤ)) 0 ×ˢ Finset.Icc 0 (i : ℤ)).finite_toSet).subset ?_
  intro z hz
  simp only [Ah, Set.mem_ofPred_eq] at hz
  simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
  omega

theorem halfPlane (i : ℕ) : ∀ g ∈ Ah i, (0 : ℤ) ≤ dot (0, 1) g := by
  intro g hg
  simp only [Ah, Set.mem_ofPred_eq] at hg
  simp only [dot]
  omega

theorem iUnion_eq : (⋃ i, Ah i) = {z | z.1 ≤ 0 ∧ 0 ≤ z.2} := by
  ext z
  simp only [Set.mem_iUnion, Ah, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, h⟩; omega
  · rintro ⟨h1, h2⟩
    refine ⟨(-z.1 + z.2).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    omega

theorem latticeConvex : IsLatticeConvexRegion (⋃ i, Ah i) := by
  rw [iUnion_eq]
  refine ⟨{x : ℝ × ℝ | x.1 ≤ 0 ∧ 0 ≤ x.2}, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hx hy ⊢
    constructor <;> nlinarith
  · exact (isClosed_le continuous_fst continuous_const).inter
      (isClosed_le continuous_const continuous_snd)
  · ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, toReal]
    exact ⟨fun h => ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩,
      fun h => ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩⟩

theorem swept : MaxEnv.SweptClosed (⋃ i, Ah i) (0, -1) (0, 1) 0 := by
  intro g hg t ht
  rw [iUnion_eq] at hg ⊢
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, dot] at hg ht ⊢
  omega

theorem face_unbounded : ∀ N : ℕ, ∃ i, (N : ℕ∞) ≤ {z ∈ Ah i | dot (0, 1) z = 0}.encard := by
  intro N
  refine ⟨N, ?_⟩
  have hsub : (↑((Finset.range (N + 1)).image fun t : ℕ => ((-(t : ℤ), (0 : ℤ)))) :
      Set (ℤ × ℤ)) ⊆ {z ∈ Ah N | dot (0, 1) z = 0} := by
    intro z hz
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    simp only [Set.mem_ofPred_eq, Ah, dot]
    omega
  calc (N : ℕ∞) ≤ ((N + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ N
    _ = (↑((Finset.range (N + 1)).image fun t : ℕ => ((-(t : ℤ), (0 : ℤ)))) :
          Set (ℤ × ℤ)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _
          (fun s t h => by simpa using h), Finset.card_range]
    _ ≤ _ := Set.encard_le_encard hsub

theorem not_ray : ¬ ∃ z₀ : ℤ × ℤ, ∀ k : ℕ, z₀ + (k : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈ ⋃ i, Ah i := by
  rintro ⟨z₀, h⟩
  have := h (1 - z₀.1).toNat
  rw [iUnion_eq] at this
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one] at this
  omega

theorem not_bottom_line : ¬ ∃ (z₀ : ℤ × ℤ) (L : ℤ), ∀ k : ℤ, L ≤ k →
    z₀ + k • ((1 : ℤ), (0 : ℤ)) ∈ MaxEnv.reachSet (⋃ i, Ah i) (0, -1) := by
  rintro ⟨z₀, L, h⟩
  obtain ⟨g, hg, t, ht⟩ := MaxEnv.mem_reachSet.mp (h (max L (1 - z₀.1)) (le_max_left _ _))
  rw [iUnion_eq] at hg
  have h1 := congrArg Prod.fst ht
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one, mul_zero, add_zero] at h1
  simp only [Set.mem_ofPred_eq] at hg
  have := le_max_right L (1 - z₀.1)
  omega

end NoPinModel

end Nivat.Colle35

#print axioms Nivat.Colle35.dot_vJ_pos_of_exhausts
#print axioms Nivat.Colle35.ell_side_of_exhausts
#print axioms Nivat.Colle35.ItemII.halfPlane_subset_iUnion
#print axioms Nivat.Colle35.exhausts_of_itemII
#print axioms Nivat.Colle35.placement_of_exhausts
#print axioms Nivat.Colle35.nfp_L_of_exhausts
#print axioms Nivat.Colle35.ChainDataGeom.cL_eq_of_exhausts
#print axioms Nivat.Colle35.halfPlane_infinite
#print axioms Nivat.Colle35.ItemII.exists_le_encard
#print axioms Nivat.Colle35.not_itemII_of_halfStrip_finite
#print axioms Nivat.Colle35.not_itemII_of_chain
#print axioms Nivat.Colle35.ChainData.not_itemII_of_chain
#print axioms Nivat.Colle35.not_itemII_chainB
#print axioms Nivat.Colle35.itemII_shift
#print axioms Nivat.Colle35.ahat_nonempty_of_itemII
#print axioms Nivat.Colle35.ell_side_of_itemII
#print axioms Nivat.Colle35.RecVJModel.itemII_Aw
#print axioms Nivat.Colle35.RecVJModel.exhausts_Aw
#print axioms Nivat.Colle35.RecVJModel.hswept_Aw
#print axioms Nivat.Colle35.RecVJModel.not_rec_vJ_Aw
#print axioms Nivat.Colle35.RecVJModel.vectors_Aw
#print axioms Nivat.Colle35.ray_of_bottom_swept
#print axioms Nivat.Colle35.rec_of_ray
#print axioms Nivat.Colle35.rec_vJ_of_bottom
#print axioms Nivat.Colle35.ray_of_pinned_growth
#print axioms Nivat.Colle35.NoPinModel.latticeConvex
#print axioms Nivat.Colle35.NoPinModel.swept
#print axioms Nivat.Colle35.NoPinModel.face_unbounded
#print axioms Nivat.Colle35.NoPinModel.not_ray
#print axioms Nivat.Colle35.NoPinModel.not_bottom_line
