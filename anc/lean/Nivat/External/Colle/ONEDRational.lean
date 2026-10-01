/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ONEDEdge
import Nivat.External.Colle.KariMoutot
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.DecompData

/-!
# Every one-sided nonexpansive direction is rational — closing the gate on the `ONED`/`E` bridge

`ONEDEdge.lean` carries Collé's corollary of Lemma 2.3 in the form
`exists_mem_E_of_mem_ONED_of_rational`, which asks for the real normal `w ∈ ONED ξ` to be given
*as* a positive multiple `s • toReal m` of a lattice vector.  The consumer at
`ColleReg.colle_region` (`ColleRegion.lean:276-277`) only has `hw₁ : w ∈ ONED ξ`,
`hw₂ : -w ∈ ONED ξ` for a bare `w : ℝ × ℝ`, and so does everything it passes them on to
(`exists_biONED_direction`, `exists_preamble`, `exists_chainData`, `RegionSteps.lean`).

This file removes the hypothesis.  Collé, `scratch/b3_colle2.txt:273`, right after Lemma 2.3's
corollary:

> *"In particular, lines in `nexpl(η)` or oriented lines in `nexpd(η)` are rational, where by
> rational we mean a line or an oriented line in `ℝ²` with a rational slope."*

and Lemma 2.6 (`:309-311`): *"suppose `φ(X) = (X^{h₁}−1)⋯(X^{h_m}−1) ∈ ann_R(η)` [...]. If
`ℓ ∈ nexpl(η)`, then `ℓ` contains some vector `h_i`."*

The repository already has the directional half of Lemma 2.6 for a single orientation:
`Nivat.Colle.exists_tangent_of_mem_ONED` (`Interfaces.lean:60`) produces, from any product
annihilator `∏ (X^{h i} − 1)` with pairwise non-parallel `h i` and any `w ∈ ONED ξ`, an index
`i` with `⟨w, h i⟩ = 0`.  Kari–Szabados (`Nivat.kari_szabados_prodShift`,
`Section8/External.lean:256`) supplies such an annihilator from `(Set.range ξ).Finite` and
`HasNonzeroAnn ξ`, and `Nivat.KM.exists_smul_perpOf` (`KariMoutot.lean:222`) turns
`⟨w, h⟩ = 0`, `h ≠ 0` into `w = t • toReal (perpOf h)`.  The only new step is the sign
normalisation `t > 0`.

`Step_BiONED.lean` runs exactly this computation inside the proof of
`exists_biONED_direction` (its steps 3–4), but exports only the lattice `ℓ`, not the relation
`w = s • toReal m`; this file states that relation as a theorem so that the bridge can be used
at every call site where `hξ` (or merely `HasNonzeroAnn ξ`) is in scope.

## Main results

* `exists_smul_toReal_of_mem_ONED` — **the rationality theorem**: with a non-zero annihilator,
  every `w ∈ ONED ξ` is `s • toReal m` with `m ≠ 0`, `s > 0`.
* `exists_mem_E_of_mem_ONED` — the bridge with the rationality hypothesis discharged:
  `w ∈ ONED ξ` is a positive multiple of `toReal ℓ` for some `ℓ ∈ E ↑S`, `S` any generating set.
* `exists_mem_E_of_mem_ONED_of_neg_mem_ONED` — both orientations: `ℓ ∈ E ↑S ∧ -ℓ ∈ E ↑S`.
* `exists_mem_E_of_minimalCounterexample` — the same, stated on exactly the hypotheses of
  `ColleReg.colle_region` (`hξ`, `hw₁`, `hw₂`), and `exists_mem_E_Sphi_of_minimalCounterexample`
  for `S := d.Sphi`.
* `mem_E_of_isOneSidedNonexpansive`, `mem_E_and_neg_mem_E_of_biONED` — the lattice-direction
  form: the `ℓ` that `exists_biONED_direction` hands to `exists_preamble` / `exists_chainData`
  (`hℓ_nel`, `hℓ_pos`, `hℓ_neg`, `RegionSteps.lean:812-814`) is an edge normal of every
  generating set in both signs, with **no** annihilator hypothesis at all — this is the form
  leaf A can consume directly.

All statements are over `Config ℤ` because Kari–Szabados is.  No `PosArea` is needed, for the
reason given in `ONEDEdge.lean`.
-/

namespace Nivat.ONEDRational

open Nivat Nivat.Colle Nivat.LE2

/-! ### The rationality theorem -/

/-- **Collé, `b3_colle2.txt:273`: oriented lines in `nexpd(η)` are rational.**  Given a
configuration with finite alphabet and a non-zero annihilator, every one-sided nonexpansive
direction `w` is a *positive* real multiple of a non-zero lattice vector.

Route: Kari–Szabados gives `∏ (X^{h i} − 1)` annihilating `ξ` with the `h i` pairwise
non-parallel; `Nivat.Colle.exists_tangent_of_mem_ONED` (Lemma 2.6's directional half) gives `i`
with `⟨w, h i⟩ = 0`; `Nivat.KM.exists_smul_perpOf` writes `w = t • toReal (perpOf (h i))`;
`w ≠ 0` (the first conjunct of `w ∈ ONED ξ`) makes `t ≠ 0`, and `t < 0` is absorbed into
`m := -perpOf (h i)`. -/
theorem exists_smul_toReal_of_mem_ONED {ξ : Config ℤ} (hA : (Set.range ξ).Finite)
    (hann : HasNonzeroAnn ξ) {w : ℝ × ℝ} (hw : w ∈ ONED ξ) :
    ∃ (m : ℤ × ℤ) (s : ℝ), m ≠ 0 ∧ 0 < s ∧ w = s • toReal m := by
  obtain ⟨n, h, -, hhne, hnp, hact⟩ := kari_szabados_prodShift hA hann
  obtain ⟨i, hi⟩ := Nivat.Colle.exists_tangent_of_mem_ONED hnp hact hw
  obtain ⟨t, ht⟩ := Nivat.KM.exists_smul_perpOf (hhne i) hi
  have hw0 : w ≠ 0 := hw.1
  have hpne : Nivat.KM.perpOf (h i) ≠ 0 := Nivat.KM.perpOf_ne_zero (hhne i)
  have htne : t ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [ht, zero_smul])
  rcases lt_or_gt_of_ne htne with hneg | hpos
  · refine ⟨-(Nivat.KM.perpOf (h i)), -t, neg_ne_zero.mpr hpne, neg_pos.mpr hneg, ?_⟩
    rw [Nivat.KM.toReal_neg, smul_neg, neg_smul, neg_neg]
    exact ht
  · exact ⟨Nivat.KM.perpOf (h i), t, hpne, hpos, ht⟩

/-- A counterexample (`Section8/ExternalDefs.lean:48`) has a non-zero annihilator: its
`LowConvexComplexity` conjunct is exactly the input of `Nivat.hasNonzeroAnn_of_low_complexity`
(Kari–Szabados 8.4(a)).  Same extraction as `Step_BiONED.lean:78-80` and
`ExternalDischarged.lean:71-73`. -/
theorem hasNonzeroAnn_of_isCounterexample {ξ : Config ℤ} (hξ : IsCounterexample ξ) :
    HasNonzeroAnn ξ := by
  obtain ⟨hA, -, -, S, hSne, -, hSP⟩ := hξ
  exact hasNonzeroAnn_of_low_complexity hA hSne hSP

/-- `exists_smul_toReal_of_mem_ONED` for a counterexample. -/
theorem exists_smul_toReal_of_mem_ONED_of_isCounterexample {ξ : Config ℤ}
    (hξ : IsCounterexample ξ) {w : ℝ × ℝ} (hw : w ∈ ONED ξ) :
    ∃ (m : ℤ × ℤ) (s : ℝ), m ≠ 0 ∧ 0 < s ∧ w = s • toReal m :=
  exists_smul_toReal_of_mem_ONED hξ.1 (hasNonzeroAnn_of_isCounterexample hξ) hw

/-! ### The bridge with the rationality hypothesis discharged -/

/-- **Collé's corollary of Lemma 2.3 (`b3_colle2.txt:273`), for an arbitrary real direction.**
With a non-zero annihilator, every `w ∈ ONED ξ` is a positive multiple of `toReal ℓ` for some
edge normal `ℓ ∈ E ↑S` of every generating set `S`.  This is
`ONEDEdge.exists_mem_E_of_mem_ONED_of_rational` with its `w = s • toReal m` hypothesis supplied
by `exists_smul_toReal_of_mem_ONED`. -/
theorem exists_mem_E_of_mem_ONED {ξ : Config ℤ} (hA : (Set.range ξ).Finite)
    (hann : HasNonzeroAnn ξ) {S : Finset (ℤ × ℤ)} (hgen : IsGeneratingSet ξ S)
    {w : ℝ × ℝ} (hw : w ∈ ONED ξ) :
    ∃ ℓ ∈ E (↑S), ∃ t : ℝ, 0 < t ∧ w = t • toReal ℓ := by
  obtain ⟨m, s, hm, hs, hwm⟩ := exists_smul_toReal_of_mem_ONED hA hann hw
  exact ONEDEdge.exists_mem_E_of_mem_ONED_of_rational hgen hw hm hs hwm

/-- Both orientations.  If `w` and `-w` are one-sided nonexpansive, the edge normal `ℓ`
produced for `w` has `-ℓ ∈ E ↑S` as well, since `-w = t • toReal (-ℓ)` with the same `t > 0`
and `-ℓ` is primitive. -/
theorem exists_mem_E_of_mem_ONED_of_neg_mem_ONED {ξ : Config ℤ} (hA : (Set.range ξ).Finite)
    (hann : HasNonzeroAnn ξ) {S : Finset (ℤ × ℤ)} (hgen : IsGeneratingSet ξ S)
    {w : ℝ × ℝ} (hw₁ : w ∈ ONED ξ) (hw₂ : -w ∈ ONED ξ) :
    ∃ ℓ ∈ E (↑S), -ℓ ∈ E (↑S) ∧ ∃ t : ℝ, 0 < t ∧ w = t • toReal ℓ := by
  obtain ⟨ℓ, hℓ, t, ht, hwℓ⟩ := exists_mem_E_of_mem_ONED hA hann hgen hw₁
  refine ⟨ℓ, hℓ, ?_, t, ht, hwℓ⟩
  have hℓp : Prim ℓ := (mem_E_iff.mp hℓ).1
  exact ONEDEdge.isEdge_of_mem_ONED_of_eq_smul hgen hw₂ hℓp.neg ht
    (by rw [hwℓ, Nivat.KM.toReal_neg, smul_neg])

/-- **The gate, closed at the hypotheses of `ColleReg.colle_region`**
(`ColleRegion.lean:276-277`: `hξ : IsMinimalCounterexample ξ`, `hw₁ : w ∈ ONED ξ`,
`hw₂ : -w ∈ ONED ξ`).  For every generating set `S`, the direction `w` is a positive multiple of
an edge normal `ℓ ∈ E ↑S`, and `-ℓ ∈ E ↑S`.  Only `hξ.1 : IsCounterexample ξ` is used;
minimality is not. -/
theorem exists_mem_E_of_minimalCounterexample {ξ : Config ℤ} (hξ : IsMinimalCounterexample ξ)
    {S : Finset (ℤ × ℤ)} (hgen : IsGeneratingSet ξ S)
    {w : ℝ × ℝ} (hw₁ : w ∈ ONED ξ) (hw₂ : -w ∈ ONED ξ) :
    ∃ ℓ ∈ E (↑S), -ℓ ∈ E (↑S) ∧ ∃ t : ℝ, 0 < t ∧ w = t • toReal ℓ :=
  exists_mem_E_of_mem_ONED_of_neg_mem_ONED hξ.1.1 (hasNonzeroAnn_of_isCounterexample hξ.1)
    hgen hw₁ hw₂

/-- The same at `S := d.Sphi`, the set over which `exists_chainData` and `Case1`/`Case2` are
stated (`RegionSteps.lean:822`, "Which set"); `d.isGeneratingSet` is
`DecompDataZ.isGeneratingSet` (`DecompData.lean:195`). -/
theorem exists_mem_E_Sphi_of_minimalCounterexample {ξ : Config ℤ}
    (hξ : IsMinimalCounterexample ξ) (d : Colle35.DecompDataZ ξ)
    {w : ℝ × ℝ} (hw₁ : w ∈ ONED ξ) (hw₂ : -w ∈ ONED ξ) :
    ∃ ℓ ∈ E (↑d.Sphi), -ℓ ∈ E (↑d.Sphi) ∧ ∃ t : ℝ, 0 < t ∧ w = t • toReal ℓ :=
  exists_mem_E_of_minimalCounterexample hξ d.isGeneratingSet hw₁ hw₂

/-! ### The lattice-direction form, for the `ℓ` already in scope downstream

`exists_biONED_direction` (`Step_BiONED.lean:72`) hands `exists_preamble` and
`exists_chainData` a lattice direction `ℓ` with `hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ`,
`hℓ_pos : IsOneSidedNonexpansive ξ ℓ`, `hℓ_neg : IsOneSidedNonexpansive ξ (-ℓ)`
(`RegionSteps.lean:812-814`).  `IsOneSidedNonexpansive ξ ℓ` (`Lemma45.lean:95`) *is*
`toReal ℓ ∈ ONED ξ` up to unfolding `sideOf` and `inner2_toReal`, so for that `ℓ` the bridge
needs no rationality argument and no annihilator: `ONEDEdge.mem_E_of_toReal_mem_ONED` applies
on the nose. -/

/-- `IsOneSidedNonexpansive ξ ℓ` is `toReal ℓ ∈ ONED ξ`: `sideOf (toReal ℓ) = {z | dot ℓ z ≤ 0}`
by `inner2_toReal`. -/
theorem toReal_mem_ONED_of_isOneSidedNonexpansive {ξ : Config ℤ} {ℓ : ℤ × ℤ} (hℓ : ℓ ≠ 0)
    (h : Colle45.IsOneSidedNonexpansive ξ ℓ) : toReal ℓ ∈ ONED ξ := by
  obtain ⟨x, y, hx, hy, hne, hagree⟩ := h
  refine ⟨Nivat.KM.toReal_ne_zero hℓ, x, hx, y, hy, hne, ?_⟩
  intro z hz
  apply hagree z
  have hz' : inner2 (toReal ℓ) z ≤ 0 := hz
  rw [inner2_toReal] at hz'
  exact_mod_cast hz'

/-- A primitive one-sided nonexpansive lattice direction is an edge normal of every generating
set. -/
theorem mem_E_of_isOneSidedNonexpansive {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    (hgen : IsGeneratingSet ξ S) {ℓ : ℤ × ℤ} (hℓ : Prim ℓ)
    (h : Colle45.IsOneSidedNonexpansive ξ ℓ) : ℓ ∈ E (↑S) :=
  ONEDEdge.mem_E_of_toReal_mem_ONED hgen hℓ
    (toReal_mem_ONED_of_isOneSidedNonexpansive hℓ.ne_zero h)

/-- **For the `ℓ` of `exists_biONED_direction`, in the exact shape `exists_preamble` /
`exists_chainData` bind it** (`RegionSteps.lean:513-515`, `:812-814`): `ℓ ∈ E ↑S` and
`-ℓ ∈ E ↑S` for every generating set `S`.  `hℓ_nel` is used only for `Primitive ℓ`. -/
theorem mem_E_and_neg_mem_E_of_biONED {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    (hgen : IsGeneratingSet ξ S) {ℓ : ℤ × ℤ}
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ)) :
    ℓ ∈ E (↑S) ∧ -ℓ ∈ E (↑S) := by
  have hℓp : Prim ℓ := prim_iff_primitive.mpr hℓ_nel.1
  exact ⟨mem_E_of_isOneSidedNonexpansive hgen hℓp hℓ_pos,
    mem_E_of_isOneSidedNonexpansive hgen hℓp.neg hℓ_neg⟩

/-- The same at `S := d.Sphi`. -/
theorem mem_E_Sphi_and_neg_mem_E_Sphi_of_biONED {ξ : Config ℤ} (d : Colle35.DecompDataZ ξ)
    {ℓ : ℤ × ℤ}
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ)) :
    ℓ ∈ E (↑d.Sphi) ∧ -ℓ ∈ E (↑d.Sphi) :=
  mem_E_and_neg_mem_E_of_biONED d.isGeneratingSet hℓ_nel hℓ_pos hℓ_neg

end Nivat.ONEDRational
