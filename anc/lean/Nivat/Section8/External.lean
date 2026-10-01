/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.HalfPlane
import Nivat.Section8.ExternalDefs
import Nivat.Section8.RegionUpgrade
import Nivat.AppendixD
import Nivat.External.KSAnnihilator
import Nivat.External.KSDecomposition
import Nivat.External.KSCorollary

/-!
# §8.2. The results quoted, and counterexamples of minimal order

Formalisation of §8.2 of *The Convex Nivat Conjecture* (Pan).

This file used to be the only one of the development that introduces `axiom`s.  **As of
2026-09-18 it introduces none**, and neither does any other file: `#print axioms` on the main
theorem reports no project axiom.  The four that were once here, and where each went:

* `Nivat.kari_szabados_prodShift` — Theorem 8.4(b), Kari–Szabados [11].  Discharged
  2026-09-13 in `Nivat.External.KSCorollary`, on top of the source's Theorem 3.1 chain in
  `Nivat.External.KS.{Nullstellensatz, Lemma3, Lemma4, Theorem31}`.  (Theorem 8.4(**a**) was
  likewise an axiom and is proved in `Nivat.External.KSAnnihilator`.)
* `Nivat.kari_szabados_decomp` — the second half of Theorem 8.4(b), also [11].  Discharged in
  `Nivat.External.KSDecomposition`.
* `Nivat.colle_doublyPeriodic` — Theorem 8.6, Colle [2, Theorem 1.9].  Discharged by
  `Nivat.Colle.theorem114`; the declaration was deleted from this file 2026-09-18, together
  with its consequence `exists_mem_ONED`, whose proved counterpart is
  `Nivat.exists_mem_ONED'` (`Section8/ExternalDischarged.lean`).
* `Nivat.colle_region` — Theorem 8.7, Colle [2, proof of Lemma 4.6].  Discharged by
  `Nivat.ColleReg.colle_region` (`External/Colle/ColleRegion.lean`); the declaration was
  deleted 2026-09-18 together with `exists_fullyPeriodic_region`, whose proved counterpart is
  `Nivat.exists_fullyPeriodic_region'` (`Section8/ExternalDischarged.lean`).

The converse of `kari_szabados_decomp` is *not* quoted: it is the elementary
`Nivat.act_prodShift_sum_eq_zero`, proved below.

Everything else in this file — Remark 8.3 and Lemma 8.5 — is proved in the development.

## Main definitions

* `Nivat.Ann`, `Nivat.HasNonzeroAnn` — the annihilator of a configuration in `ℤ[T₁^±, T₂^±]`.
* `Nivat.prodShift` — `Δ = ∏ᵢ (X^{hᵢ} - 1)`.
* `Nivat.ONED` — the one-sided nonexpansive directions of the orbit closure, in the sense of [2].
* `Nivat.IsCounterexample`, `Nivat.IsMinimalCounterexample` — Remark 8.3.

## Status

Complete; no `sorry`, no `axiom`.

**Closed 2026-09-30.**  The last open leaf of `Nivat/External/Colle/RegionSteps.lean`
(`exists_chainData`) is proved by `Nivat.ColleReg.exists_chainData_closed`
(`External/Colle/Hole1PushShell.lean`); measured that day, `bash scripts/sorries.sh` reports
`TOTAL: 0` and `#print axioms Nivat.nivat_conjecture` reports
`[propext, Classical.choice, Quot.sound]`.  Re-run `scripts/sorries.sh` and
`scripts/check_axioms.sh` for the current numbers; do not read them off this paragraph.

History (2026-09-18 → 2026-09-30): removing the axioms moved the open work onto the main chain
rather than finishing it — in that period `Nivat.nivat_conjecture` measured
`[propext, sorryAx, Classical.choice, Quot.sound]`, the `sorryAx` being the open leaves of
`RegionSteps.lean`, put on the main chain by the substituted `Nivat.ColleReg.colle_region` call
inside `Nivat.exists_fullyPeriodic_region'`.

**Correction history.**  This block has twice carried a stale axiom count — it read "Three
`axiom`s remain" after `kari_szabados_prodShift` had become a theorem (corrected 2026-09-13),
and "Two `axiom`s remain (line 631 and line 683)" after both line numbers had drifted
(corrected 2026-09-18, when the axioms themselves were deleted).  The count is the one number
a reader consults to learn how much is assumed, so both errors overstated it.  Recorded rather
than silently overwritten.

-/

namespace Nivat

open Finset

variable {α : Type*}

/-! ### Annihilators -/

/-- The annihilator of `g` in `R[T₁^±, T₂^±]`.  Paper §8.2 writes `Ann_ℤ(ξ)` for `R = ℤ`. -/
def Ann {R : Type*} [CommRing R] (g : Config R) : Set (LaurentTwo R) := {f | act f g = 0}

/-- `g` has a non-trivial annihilator.  Paper §8.2: `Ann_ℤ(ξ) ≠ 0`. -/
def HasNonzeroAnn {R : Type*} [CommRing R] (g : Config R) : Prop :=
  ∃ f : LaurentTwo R, f ≠ 0 ∧ act f g = 0

/-- `Δ = ∏ᵢ (X^{hᵢ} - 1)`, the annihilator produced by Theorem 8.4(b). -/
noncomputable def prodShift {R : Type*} [CommRing R] {n : ℕ} (h : Fin n → ℤ × ℤ) :
    LaurentTwo R :=
  ∏ i, (mono (h i) - 1)

theorem prodShift_ne_zero {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R] {n : ℕ}
    {h : Fin n → ℤ × ℤ} (hh : ∀ i, h i ≠ 0) : (prodShift h : LaurentTwo R) ≠ 0 := by
  rw [prodShift, Finset.prod_ne_zero_iff]
  exact fun i _ => mono_sub_one_ne_zero (hh i)

/-- If one factor of `Δ = ∏ⱼ (T^{hⱼ} − 1)` kills `g`, then so does `Δ`. -/
theorem act_prodShift_eq_zero_of_mem_Per {R : Type*} [CommRing R] {n : ℕ}
    {h : Fin n → ℤ × ℤ} {g : Config R} {i : Fin n} (hg : h i ∈ Per g) :
    act (prodShift h) g = 0 := by
  classical
  rw [prodShift, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), act_mul,
    (act_mono_sub_one_eq_zero_iff _ _).mpr hg, act_zero_right]

/-- `Δ = ∏ᵢ (T^{hᵢ} − 1)` annihilates any sum `∑ᵢ fᵢ` whose `i`-th term has period `hᵢ`.
This is the easy half of Theorem 8.4(b), and the only half used to produce annihilators. -/
theorem act_prodShift_sum_eq_zero {R : Type*} [CommRing R] {n : ℕ} {h : Fin n → ℤ × ℤ}
    {f : Fin n → Config R} {g : Config R} (hper : ∀ i, h i ∈ Per (f i))
    (hsum : ∀ z, g z = ∑ i, f i z) : act (prodShift h) g = 0 := by
  have hg : g = ∑ i, f i := by
    funext z
    rw [hsum z, Finset.sum_apply]
  rw [hg, act_sum_right]
  exact Finset.sum_eq_zero fun i _ => act_prodShift_eq_zero_of_mem_Per (hper i)

/-- An annihilation relation `act f g = 0` is a **local** identity: it constrains only the
pattern of `g` on the finite window `supp f`.  Hence it passes to every element of the orbit
closure.  This is the mechanism behind Lemma 8.5(a). -/
theorem act_eq_zero_of_mem_orbitClosure {f : LaurentTwo ℤ} {ξ : Config ℤ}
    (hann : act f ξ = 0) {ζ : Config ℤ} (hζ : ζ ∈ orbitClosure ξ) : act f ζ = 0 := by
  classical
  set W : Finset (ℤ × ℤ) := supp f with hW
  set F : (W → ℤ) → ℤ := fun π => ∑ s : W, f.coeff (s : ℤ × ℤ) * π s with hFdef
  have hkey : ∀ (x : Config ℤ) (z : ℤ × ℤ), F (pattern x W z) = act f x z := by
    intro x z
    show (∑ s : W, f.coeff (s : ℤ × ℤ) * x (z + (s : ℤ × ℤ)))
        = f.coeff.sum fun u c => c * x (z + u)
    rw [Finsupp.sum]
    exact Finset.sum_coe_sort W fun s => f.coeff s * x (z + s)
  have h0 : ∀ z, F (pattern ξ W z) = 0 := fun z => (hkey ξ z).trans (congrFun hann z)
  funext z
  show act f ζ z = 0
  rw [← hkey ζ z]
  exact IsLocal.eq_zero_of_mem_orbitClosure h0 hζ z

/-! ### Merging two components of a decomposition

Both Remark 8.3 (a minimal decomposition has pairwise non-parallel periods) and Lemma 8.5(c)
(Operation A) proceed by folding the `i`-th component of a decomposition into the `j`-th one and
deleting the index `i`.  The following three lemmas are the shared bookkeeping. -/

private theorem zsmul_ne_zero_prod {N : ℤ} (hN : N ≠ 0) {u : ℤ × ℤ} (hu : u ≠ 0) : N • u ≠ 0 := by
  intro hcon
  refine hu (Prod.ext ?_ ?_)
  · have h1 : N * u.1 = 0 := by
      have := congrArg Prod.fst hcon
      simpa [Prod.smul_def] using this
    exact (mul_eq_zero.mp h1).resolve_left hN
  · have h2 : N * u.2 = 0 := by
      have := congrArg Prod.snd hcon
      simpa [Prod.smul_def] using this
    exact (mul_eq_zero.mp h2).resolve_left hN

private theorem det_zsmul_left (N : ℤ) (u v : ℤ × ℤ) : det (N • u) v = N * det u v := by
  simp only [det, Prod.smul_def, smul_eq_mul]; ring

private theorem det_zsmul_right (N : ℤ) (u v : ℤ × ℤ) : det u (N • v) = N * det u v := by
  simp only [det, Prod.smul_def, smul_eq_mul]; ring

private theorem mem_Per_add {α : Type*} [AddCommGroup α] {a b : Config α} {u : ℤ × ℤ}
    (ha : u ∈ Per a) (hb : u ∈ Per b) : u ∈ Per (a + b) := by
  rw [mem_Per_iff]
  funext z
  show a (z + u) + b (z + u) = a z + b z
  rw [Per.apply ha z, Per.apply hb z]

/-- Two parallel non-zero periods have a common non-zero multiple, so two components of a
decomposition with parallel periods can be added into a single periodic component. -/
private theorem exists_common_period {α : Type*} [AddCommGroup α] {a b : Config α}
    {u v : ℤ × ℤ} (hu : u ≠ 0) (hv : v ≠ 0) (hdet : det u v = 0)
    (hau : u ∈ Per a) (hbv : v ∈ Per b) : IsPeriodic (a + b) := by
  have hd : u.1 * v.2 - u.2 * v.1 = 0 := hdet
  have key : ∃ s t : ℤ, s ≠ 0 ∧ s • u = t • v := by
    by_cases h1 : u.1 = 0
    · have hu2 : u.2 ≠ 0 := fun hc => hu (Prod.ext h1 hc)
      have hv1 : v.1 = 0 := by
        rw [h1, zero_mul] at hd
        exact (mul_eq_zero.mp (by linarith : u.2 * v.1 = 0)).resolve_left hu2
      have hv2 : v.2 ≠ 0 := fun hc => hv (Prod.ext hv1 hc)
      refine ⟨v.2, u.2, hv2, Prod.ext ?_ ?_⟩
      · simp only [Prod.smul_def, smul_eq_mul, h1, hv1, mul_zero]
      · simp only [Prod.smul_def, smul_eq_mul]; ring
    · have hv1 : v.1 ≠ 0 := by
        intro hc
        rw [hc, mul_zero] at hd
        exact hv (Prod.ext hc ((mul_eq_zero.mp (by linarith : u.1 * v.2 = 0)).resolve_left h1))
      refine ⟨v.1, u.1, hv1, Prod.ext ?_ ?_⟩
      · simp only [Prod.smul_def, smul_eq_mul]; ring
      · simp only [Prod.smul_def, smul_eq_mul]; linarith
  obtain ⟨s, t, hs, hst⟩ := key
  exact ⟨s • u, mem_Per_add (AddSubgroup.zsmul_mem _ hau s)
    (hst ▸ AddSubgroup.zsmul_mem _ hbv t), zsmul_ne_zero_prod hs hu⟩

/-- Fold the `i`-th component of a family into the `j`-th one and delete the index `i`. -/
private def mergeAt {α : Type*} [Add α] {m : ℕ} (G : Fin (m + 1) → Config α)
    (i j : Fin (m + 1)) : Fin m → Config α :=
  fun k => if i.succAbove k = j then G j + G i else G (i.succAbove k)

private theorem sum_mergeAt {α : Type*} [AddCommGroup α] {m : ℕ} (G : Fin (m + 1) → Config α)
    {i j : Fin (m + 1)} (hij : j ≠ i) (z : ℤ × ℤ) :
    ∑ k : Fin m, mergeAt G i j k z = ∑ k, G k z := by
  classical
  set V : Fin (m + 1) → α := fun l => if l = j then G j z + G i z else G l z with hVdef
  have hV : ∀ l, V l = G l z + (if l = j then G i z else 0) := by
    intro l
    rw [hVdef]
    by_cases hl : l = j
    · subst hl; simp
    · simp [hl]
  have htot : ∑ l, V l = (∑ l, G l z) + G i z := by
    rw [Finset.sum_congr rfl fun l _ => hV l, Finset.sum_add_distrib]
    congr 1
    simp
  have hVi : V i = G i z := by rw [hVdef]; simp only [if_neg (Ne.symm hij)]
  have hmerge : ∀ k : Fin m, mergeAt G i j k z = V (i.succAbove k) := by
    intro k
    simp only [mergeAt, hVdef]
    by_cases hk : i.succAbove k = j <;> simp [hk]
  have hsplit := Fin.sum_univ_succAbove V i
  rw [htot, hVi] at hsplit
  rw [Finset.sum_congr rfl fun k _ => hmerge k]
  exact add_left_cancel (a := G i z) (by rw [← hsplit]; abel)

/-! ### One-sided nonexpansive directions, counterexamples of minimal order

`sideOf`, `ONED`, `PeriodicDecompZ`, `HasOrderZ`, `IsCounterexample` and
`IsMinimalCounterexample` were extracted verbatim into `Nivat.Section8.ExternalDefs`, so that
`Nivat.External.Colle.ColleRegion` can state `colle_region` without depending on this file.
They arrive here through that import; the definitions are unchanged. -/

/-! ### Theorem 8.4 -/

/-- **Theorem 8.4(b) (Kari–Szabados [11], Corollary 1).**  Reference [11]: J. Kari and
M. Szabados, *An algebraic geometric approach to Nivat's conjecture*, Inform. and Comput. **271**
(2020), 104481.

If `Ann_ℤ(ξ) ≠ 0`, then there are pairwise non-parallel `h₁, …, h_m ∈ ℤ² \ {0}` such that
`Δ = ∏ᵢ (X^{hᵢ} − 1)` annihilates `ξ`.

Quoted from [11] (source Corollary 1); **not** proved in this development.  Its proof goes
through the source's structure theory of annihilator ideals (Hilbert's Nullstellensatz, line
polynomials, Theorem 3.2), none of which is formalised here.

**Fidelity check** (against arXiv:1605.05929 / Inform. and Comput. 271 (2020)): source
Corollary 1 states the existence of a product of line polynomials in *pairwise distinct
directions* annihilating `c`; "direction" there is the one-dimensional subspace `⟨v⟩`, so
"pairwise distinct directions" is exactly `det (h i) (h j) ≠ 0` for `i ≠ j`.  Stated by the
source for the un-normalised alphabet `A ⊆ ℤ`, matching the Lean hypothesis
`(Set.range ξ).Finite` exactly — no strengthening.

**No longer an axiom (2026-09-13).**  It is now a theorem, proved in
`Nivat.External.KSCorollary` (`Nivat.KSC.kari_szabados_prodShift'`) on top of
`Nivat.External.KS.Nullstellensatz` (source Theorem 3.1 / Hilbert's Nullstellensatz transported
to the Laurent ring), `Nivat.External.KS.Lemma3` (the Frobenius scaling lemma) and
`Nivat.External.KS.Lemma4`.  The statement below is unchanged, character for character, from
when it was an `axiom`; `#print axioms` on it shows only `[propext, Classical.choice,
Quot.sound]`. -/
theorem kari_szabados_prodShift {ξ : Config ℤ} (hA : (Set.range ξ).Finite) :
    HasNonzeroAnn ξ → ∃ (n : ℕ) (h : Fin n → ℤ × ℤ),
      0 < n ∧ (∀ i, h i ≠ 0) ∧ (Pairwise fun i j => det (h i) (h j) ≠ 0) ∧
        act (prodShift h) ξ = 0 :=
  fun hann => Nivat.KSC.kari_szabados_prodShift' hA hann

/-- **Theorem 8.4 (Kari–Szabados [11]).**  Reference [11]: J. Kari and M. Szabados,
*An algebraic geometric approach to Nivat's conjecture*, Inform. and Comput. **271** (2020),
104481.  Quoted in `nivat.pdf` §8.2, p. 20.  Let `ξ : ℤ² → A` with `A ⊆ ℤ` finite.

(a) If `P_ξ(S) ≤ |S|` for some non-empty finite `S ⊆ ℤ²`, then `Ann_ℤ(ξ) ≠ 0`.

(b) If `Ann_ℤ(ξ) ≠ 0`, then there are pairwise non-parallel `h₁, …, h_m ∈ ℤ² \ {0}` such that
`Δ = ∏ᵢ (X^{hᵢ} − 1)` annihilates `ξ`.

Part **(a) is proved** in this development, in `Nivat.External.KSAnnihilator`
(`Nivat.hasNonzeroAnn_of_low_complexity'`, a formalisation of source Lemma 1 in its integral
form); part **(b) is also proved**, as `Nivat.kari_szabados_prodShift` in
`Nivat.External.KSCorollary`.  The second half of 8.4(b), the decomposition statement, is
likewise proved, as `Nivat.kari_szabados_decomp` in `Nivat.External.KSDecomposition`.
(Both were axioms in earlier revisions; this paragraph still described them as axioms until
2026-09-13, when the stale wording was corrected.  Neither is an `axiom` now — see the
`Status` block above for the two that are.)

**Fidelity check** (against the source, arXiv:1605.05929 / Inform. and Comput. 271 (2020)):
part (a) is source Lemma 1 (existence of a non-zero annihilator from low complexity), stated
there for an arbitrary *finite domain* `D ⊂ ℤᵈ` with `P_c(D) ≤ |D|`; the Lean form additionally
assumes `(Set.range ξ).Finite` and `S.Nonempty`, i.e. it is *weaker* than the source.  Source
Lemma 1 produces a `ℂ`-annihilator; the integral conclusion needed here is obtained not via
source Lemma 2 but by running the same linear-dependence argument over `ℤ` directly, which is
legitimate because `ℤ` satisfies the strong rank condition (see the module docstring of
`Nivat.External.KSAnnihilator`).  The "pairwise non-parallel" existence claim of (b) is source
Corollary 1.  No discrepancy found. -/
theorem kari_szabados {ξ : Config ℤ} (hA : (Set.range ξ).Finite) :
    (∀ S : Finset (ℤ × ℤ), S.Nonempty → P ξ S ≤ S.card → HasNonzeroAnn ξ) ∧
      (HasNonzeroAnn ξ → ∃ (n : ℕ) (h : Fin n → ℤ × ℤ),
        0 < n ∧ (∀ i, h i ≠ 0) ∧ (Pairwise fun i j => det (h i) (h j) ≠ 0) ∧
          act (prodShift h) ξ = 0) :=
  ⟨fun _S hne hP => hasNonzeroAnn_of_low_complexity' hA hne hP, kari_szabados_prodShift hA⟩

/-- **Theorem 8.4(b), second half (Kari–Szabados [11]).**  Reference [11]: J. Kari and
M. Szabados, *An algebraic geometric approach to Nivat's conjecture*, Inform. and Comput. **271**
(2020), 104481.  Every `η : ℤ² → ℤ` annihilated by `Δ = ∏ᵢ (X^{hᵢ} − 1)`, with the `hᵢ` non-zero
and pairwise non-parallel, decomposes as `η = ∑ᵢ ηᵢ` with `ηᵢ` of period `hᵢ`.

**No longer an axiom.**  This is source Lemma 8 of [11], specialised to `fᵢ = X^{hᵢ} − 1`, and
it is now *proved* in `Nivat.External.KSDecomposition` (`Nivat.kari_szabados_decomp'`).  In the
specialised case the source's division lemma (Lemma 7 of [11], which solves recurrence (3) in a
basis adapted to the direction of `fᵢ`) degenerates into the telescoping recurrence
`c'(z + q) − c'(z) = c(z)`, solved by a two-sided antidifference; integrality of the components
comes from that recurrence having leading coefficient `1` and constant term `−1`, which is the
observation made inside the proof of Theorem 3.2 of [11] (*not* Example 4 of [11], which is
about the components failing to be finitary — a separate point, and the reason the Lean
conclusion targets `Config ℤ` with unbounded values rather than a finite alphabet).

The converse direction was never quoted either — it is the easy
`Nivat.act_prodShift_sum_eq_zero`, proved above. -/
theorem kari_szabados_decomp {n : ℕ} {h : Fin n → ℤ × ℤ} (hne : ∀ i, h i ≠ 0)
    (hnp : Pairwise fun i j => det (h i) (h j) ≠ 0) {η : Config ℤ}
    (hann : act (prodShift h) η = 0) :
    ∃ f : Fin n → Config ℤ, (∀ i, h i ∈ Per (f i)) ∧ ∀ z, η z = ∑ i, f i z :=
  kari_szabados_decomp' hne hnp hann

/-- **Theorem 8.4(a).** -/
theorem hasNonzeroAnn_of_low_complexity {ξ : Config ℤ} (hA : (Set.range ξ).Finite)
    {S : Finset (ℤ × ℤ)} (hne : S.Nonempty) (hP : P ξ S ≤ S.card) : HasNonzeroAnn ξ :=
  hasNonzeroAnn_of_low_complexity' hA hne hP

/-- **Theorem 8.4(b).** -/
theorem exists_prodShift_ann {ξ : Config ℤ} (hA : (Set.range ξ).Finite)
    (hann : HasNonzeroAnn ξ) :
    ∃ (n : ℕ) (h : Fin n → ℤ × ℤ), 0 < n ∧ (∀ i, h i ≠ 0) ∧
      (Pairwise fun i j => det (h i) (h j) ≠ 0) ∧ act (prodShift h) ξ = 0 ∧
      ∀ η : Config ℤ, act (prodShift h) η = 0 →
        ∃ f : Fin n → Config ℤ, (∀ i, h i ∈ Per (f i)) ∧ ∀ z, η z = ∑ i, f i z := by
  obtain ⟨n, h, hn, hne, hnp, hann'⟩ := (kari_szabados hA).2 hann
  exact ⟨n, h, hn, hne, hnp, hann', fun _ hη => kari_szabados_decomp hne hnp hη⟩

/-! ### Remark 8.3 -/

/-- A periodic decomposition of **minimal** length has pairwise non-parallel periods: if
`hᵢ ∥ hⱼ` for some `i ≠ j`, then by `Nivat.exists_common_period` the two components have a
common non-zero period and can be merged into one, shortening the decomposition.  Consequently
`Δ = ∏ᵢ (X^{hᵢ} − 1)` annihilates `ξ`, and Theorem 8.4(b) applies to it. -/
private theorem exists_nonparallel_decomp {ξ : Config ℤ} {n : ℕ}
    (hD : PeriodicDecompZ ξ n) (hmin : ∀ k, PeriodicDecompZ ξ k → n ≤ k) :
    ∃ h : Fin n → ℤ × ℤ, (∀ i, h i ≠ 0) ∧ (Pairwise fun i j => det (h i) (h j) ≠ 0) ∧
      act (prodShift h : LaurentTwo ℤ) ξ = 0 := by
  classical
  obtain ⟨f, hfp, hfsum⟩ := hD
  choose h hhper hhne using hfp
  refine ⟨h, hhne, ?_, act_prodShift_sum_eq_zero hhper hfsum⟩
  intro i j hij hdet
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmerged : IsPeriodic (f j + f i) :=
    exists_common_period (hhne j) (hhne i) (by rw [det_comm, hdet, neg_zero])
      (hhper j) (hhper i)
  have hDm : PeriodicDecompZ ξ m := by
    refine ⟨mergeAt f i j, fun k => ?_,
      fun z => (hfsum z).trans (sum_mergeAt f (Ne.symm hij) z).symm⟩
    simp only [mergeAt]
    by_cases hk : i.succAbove k = j
    · rw [if_pos hk]; exact hmerged
    · rw [if_neg hk]; exact ⟨h (i.succAbove k), hhper _, hhne _⟩
  exact absurd (hmin m hDm) (by omega)

/-- A configuration of low complexity has a finite periodic decomposition, so `ord` is defined.
Paper Remark 8.3, via Theorem 8.4. -/
theorem exists_hasOrderZ {ξ : Config ℤ} (hA : (Set.range ξ).Finite)
    (hlow : LowConvexComplexity ξ) : ∃ n, HasOrderZ ξ n := by
  obtain ⟨S, hSne, -, hSP⟩ := hlow
  obtain ⟨n, h, -, hne, hnp, hann⟩ :=
    (kari_szabados hA).2 (hasNonzeroAnn_of_low_complexity hA hSne hSP)
  obtain ⟨f, hfper, hfsum⟩ := kari_szabados_decomp hne hnp hann
  have hdne : {k | PeriodicDecompZ ξ k}.Nonempty :=
    ⟨n, f, fun i => ⟨h i, hfper i, hne i⟩, hfsum⟩
  exact ⟨sInf {k | PeriodicDecompZ ξ k}, Nat.sInf_mem hdne, fun k hk => Nat.sInf_le hk⟩

/-- If the convex Nivat conjecture has a counterexample, it has one of minimal order.
Paper Remark 8.3. -/
theorem exists_minimalCounterexample (h : ∃ ξ : Config ℤ, IsCounterexample ξ) :
    ∃ ξ : Config ℤ, IsMinimalCounterexample ξ := by
  obtain ⟨ξ₀, hξ₀⟩ := h
  obtain ⟨n₀, hn₀⟩ := exists_hasOrderZ hξ₀.1 hξ₀.2.2.2
  obtain ⟨ζ, hζ, hord⟩ :=
    Nat.sInf_mem (⟨n₀, ξ₀, hξ₀, hn₀⟩ :
      {n | ∃ ζ : Config ℤ, IsCounterexample ζ ∧ HasOrderZ ζ n}.Nonempty)
  exact ⟨ζ, hζ, _, hord, fun ζ' hζ' k hk => Nat.sInf_le ⟨ζ', hζ', hk⟩⟩

/-- **Remark 8.3.**  For a counterexample `ξ` of minimal order, every non-periodic `ζ ∈ X` is
again a counterexample of the same order.

That `ζ` is a counterexample is immediate: its values are values of `ξ`, and complexity does not
increase along the orbit closure.  That its order is not *smaller* is the minimality of `ξ`;
that it is not *larger* is Lemma 8.5(a): a minimal decomposition of `ξ` has pairwise
non-parallel periods, the resulting `Δ` annihilates `ξ`, hence also `ζ`, and Theorem 8.4(b)
decomposes `ζ` into the same number of components. -/
theorem IsMinimalCounterexample.of_mem_orbitClosure {ξ : Config ℤ}
    (hξ : IsMinimalCounterexample ξ) {ζ : Config ℤ} (hζ : ζ ∈ orbitClosure ξ)
    (hnp : ¬ IsPeriodic ζ) :
    IsMinimalCounterexample ζ ∧ ∀ n, HasOrderZ ξ n → HasOrderZ ζ n := by
  classical
  obtain ⟨⟨hA, hpos, -, S, hSne, hSconv, hSP⟩, n₀, hord₀, hmin₀⟩ := hξ
  have hval : ∀ z, ∃ w, ζ z = ξ w := by
    intro z
    obtain ⟨u, hu⟩ := hζ {z}
    exact ⟨u + z, hu z (Finset.mem_singleton_self z)⟩
  have hζA : (Set.range ζ).Finite := by
    refine hA.subset ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hval z
    exact ⟨w, hw.symm⟩
  have hζpos : ∀ z, 0 < ζ z := by
    intro z
    obtain ⟨w, hw⟩ := hval z
    rw [hw]
    exact hpos w
  have hζc : IsCounterexample ζ :=
    ⟨hζA, hζpos, hnp, S, hSne, hSconv,
      le_trans (P_le_of_mem_orbitClosure hζ S (patterns_finite_of_range_finite hA S)) hSP⟩
  have hζord : ∀ n, HasOrderZ ξ n → HasOrderZ ζ n := by
    intro n hn
    obtain ⟨h, hhne, hhnp, hann⟩ := exists_nonparallel_decomp hn.1 hn.2
    obtain ⟨g, hgper, hgsum⟩ :=
      kari_szabados_decomp hhne hhnp (act_eq_zero_of_mem_orbitClosure hann hζ)
    refine ⟨⟨g, fun i => ⟨h i, hgper i, hhne i⟩, hgsum⟩, fun k hk => ?_⟩
    have hdne : {j | PeriodicDecompZ ζ j}.Nonempty := ⟨k, hk⟩
    have hk' : HasOrderZ ζ (sInf {j | PeriodicDecompZ ζ j}) :=
      ⟨Nat.sInf_mem hdne, fun j hj => Nat.sInf_le hj⟩
    have hnn : n = n₀ := le_antisymm (hn.2 n₀ hord₀.1) (hord₀.2 n hn.1)
    rw [hnn]
    exact le_trans (hmin₀ ζ hζc _ hk') (Nat.sInf_le hk)
  exact ⟨⟨hζc, n₀, hζord n₀ hord₀, hmin₀⟩, hζord⟩

/-! ### Lemma 8.5 -/

/-- Reduction of a `ℤ`-valued configuration mod `p`. -/
def modP (p : ℕ) (ξ : Config ℤ) : Config (ZMod p) := fun z => (ξ z : ZMod p)

/-- Distinct values in `[[p]] = {1, …, p−1}` stay distinct mod `p`.  This is the whole content
of Lemma 8.5(b): the hypothesis `A ⊆ [[p]]` is exactly what makes reduction injective on the
alphabet. -/
private theorem intCast_inj_of_lt {p : ℕ} {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hap : a < p) (hbp : b < p) (hab : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have hp : (0 : ℤ) < p := lt_trans ha hap
  have : NeZero p := ⟨by exact_mod_cast hp.ne'⟩
  have h0 : ((a - b : ℤ) : ZMod p) = 0 := by push_cast; rw [hab, sub_self]
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) p).mp h0
  have hlt1 : a - b < (p : ℤ) := by omega
  have hgt1 : -(p : ℤ) < a - b := by omega
  rw [hk] at hlt1 hgt1
  have h3 : k < 1 := by
    by_contra hc
    push Not at hc
    exact absurd hlt1 (not_lt.mpr (le_mul_of_one_le_right hp.le hc))
  have h4 : (-1 : ℤ) < k := by
    by_contra hc
    push Not at hc
    have hmul : (p : ℤ) * k ≤ (p : ℤ) * (-1) := mul_le_mul_of_nonneg_left hc hp.le
    rw [mul_neg_one] at hmul
    linarith
  have hk0 : k = 0 := by omega
  rw [hk0, mul_zero] at hk
  omega

/-- No colours are merged when `A ⊆ [[p]]`, so the complexity is unchanged.
Paper Lemma 8.5(b). -/
theorem P_modP {p : ℕ} {ξ : Config ℤ} (hpos : ∀ z, 0 < ξ z) (hlt : ∀ z, ξ z < p)
    (S : Finset (ℤ × ℤ)) : P (modP p ξ) S = P ξ S := by
  classical
  have himg : patterns (modP p ξ) S
      = (fun g : S → ℤ => fun q => ((g q : ℤ) : ZMod p)) '' patterns ξ S := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨pattern ξ S u, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨g, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
  rw [P, P, himg, Set.InjOn.ncard_image]
  rintro g₁ ⟨u₁, rfl⟩ g₂ ⟨u₂, rfl⟩ heq
  funext q
  exact intCast_inj_of_lt (hpos _) (hpos _) (hlt _) (hlt _) (congrFun heq q)

/-- No colours are merged when `A ⊆ [[p]]`, so periodicity is unchanged.
Paper Lemma 8.5(b). -/
theorem isPeriodic_modP_iff {p : ℕ} {ξ : Config ℤ} (hpos : ∀ z, 0 < ξ z) (hlt : ∀ z, ξ z < p) :
    IsPeriodic (modP p ξ) ↔ IsPeriodic ξ := by
  have hPer : Per (modP p ξ) = Per ξ := by
    ext u
    simp only [mem_Per_iff]
    constructor
    · intro hu
      funext z
      exact intCast_inj_of_lt (hpos _) (hpos _) (hlt _) (hlt _) (congrFun hu z)
    · intro hu
      funext z
      have hz : ξ (z + u) = ξ z := congrFun hu z
      show ((ξ (z + u) : ℤ) : ZMod p) = ((ξ z : ℤ) : ZMod p)
      rw [hz]
  constructor
  · rintro ⟨u, hu, hu0⟩; exact ⟨u, hPer ▸ hu, hu0⟩
  · rintro ⟨u, hu, hu0⟩; exact ⟨u, hPer ▸ hu, hu0⟩

/-- **Lemma 8.5(a).**  An annihilation relation is a local identity, hence passes to the orbit
closure; Theorem 8.4(b) then decomposes every `ζ ∈ X`. -/
theorem ann_of_mem_orbitClosure {ξ : Config ℤ} {n : ℕ} {h : Fin n → ℤ × ℤ}
    (hann : act (prodShift h) ξ = 0) {ζ : Config ℤ} (hζ : ζ ∈ orbitClosure ξ) :
    act (prodShift h) ζ = 0 :=
  act_eq_zero_of_mem_orbitClosure hann hζ

/-- **Operation A**, in the form needed for Lemma 8.5(c).  A doubly periodic component `Gᵢ` can
be absorbed into any other component `Gⱼ`: since `Per(Gᵢ)` contains `N • w` for a fixed `N ≠ 0`
and every `w`, the merged component `Gⱼ + Gᵢ` has the non-zero period `N • hⱼ`, which is still
non-parallel to all the remaining `hₖ` because `det (N • hⱼ) hₖ = N · det hⱼ hₖ`.  Each merge
shortens the decomposition, so the process terminates; non-periodicity of `ζ` keeps the length
at least `2`. -/
private theorem exists_decomp_not_doublyPeriodic {α : Type*} [AddCommGroup α]
    {zeta : Config α} (hnper : ¬ IsPeriodic zeta) (n : ℕ) :
    ∀ (h : Fin n → ℤ × ℤ) (G : Fin n → Config α), (∀ i, h i ≠ 0) →
      (Pairwise fun i j => det (h i) (h j) ≠ 0) → (∀ i, h i ∈ Per (G i)) →
      (∀ z, zeta z = ∑ i, G i z) →
      ∃ (n' : ℕ) (h' : Fin n' → ℤ × ℤ) (G' : Fin n' → Config α),
        2 ≤ n' ∧ (∀ i, h' i ≠ 0) ∧ (Pairwise fun i j => det (h' i) (h' j) ≠ 0) ∧
          (∀ i, h' i ∈ Per (G' i)) ∧ (∀ i, ¬ DoublyPeriodic (G' i)) ∧
          ∀ z, zeta z = ∑ i, G' i z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro h G hne hnp hper hsum
  -- `ζ` is not periodic, so the decomposition cannot have length `0` or `1`.
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    interval_cases n
    · refine hnper ⟨(1, 0), mem_Per_iff.mpr (funext fun z => ?_),
        fun hc => one_ne_zero (congrArg Prod.fst hc)⟩
      show zeta (z + (1, 0)) = zeta z
      rw [hsum (z + (1, 0)), hsum z, Fin.sum_univ_zero, Fin.sum_univ_zero]
    · refine hnper ⟨h 0, mem_Per_iff.mpr (funext fun z => ?_), hne 0⟩
      show zeta (z + h 0) = zeta z
      rw [hsum (z + h 0), hsum z, Fin.sum_univ_one, Fin.sum_univ_one]
      exact Per.apply (hper 0) z
  by_cases hdp : ∃ i, DoublyPeriodic (G i)
  · obtain ⟨i, hi⟩ := hdp
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hnt : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.mpr hn2
    obtain ⟨j, hj⟩ := exists_ne i
    obtain ⟨N, hN0, hNmem⟩ := hi.exists_smul_mem
    set h' : Fin m → ℤ × ℤ :=
      fun k => if i.succAbove k = j then N • h j else h (i.succAbove k) with hh'def
    have hh'val : ∀ k, h' k = if i.succAbove k = j then N • h j else h (i.succAbove k) :=
      fun k => by rw [hh'def]
    refine ih m (by omega) h' (mergeAt G i j) ?_ ?_ ?_
      (fun z => (hsum z).trans (sum_mergeAt G hj z).symm)
    · intro k
      rw [hh'val k]
      split_ifs with hk
      · exact zsmul_ne_zero_prod hN0 (hne j)
      · exact hne (i.succAbove k)
    · intro k l hkl
      have hsa : i.succAbove k ≠ i.succAbove l := fun hc =>
        hkl (Fin.succAbove_right_injective hc)
      show det (h' k) (h' l) ≠ 0
      rw [hh'val k, hh'val l]
      by_cases hk : i.succAbove k = j <;> by_cases hl : i.succAbove l = j
      · exact absurd (hk.trans hl.symm) hsa
      · rw [if_pos hk, if_neg hl, det_zsmul_left]
        exact mul_ne_zero hN0 (hnp (by rw [← hk]; exact hsa))
      · rw [if_neg hk, if_pos hl, det_zsmul_right]
        exact mul_ne_zero hN0 (hnp hk)
      · rw [if_neg hk, if_neg hl]
        exact hnp hsa
    · intro k
      rw [hh'val k]
      simp only [mergeAt]
      by_cases hk : i.succAbove k = j
      · rw [if_pos hk, if_pos hk]
        exact mem_Per_add (AddSubgroup.zsmul_mem _ (hper j) N) (hNmem (h j))
      · rw [if_neg hk, if_neg hk]
        exact hper (i.succAbove k)
  · push Not at hdp
    exact ⟨n, h, G, hn2, hne, hnp, hper, hdp, hsum⟩

/-- **Lemma 8.5(a)(b)(c).**  Let `ξ` be as in Theorem 8.4 with `A ⊆ ℤ_{>0}`, let
`Δ = ∏ᵢ (X^{hᵢ} − 1)` annihilate `ξ` with the `hᵢ` non-zero and pairwise non-parallel, and let
`p > max A` be prime.  Then every non-periodic `ζ ∈ X` has an `𝔽_p`-decomposition
`ζ mod p = ∑ᵢ Ḡᵢ` into at least two components, with non-zero pairwise non-parallel periods. -/
theorem exists_modP_decomp {ξ : Config ℤ} (_hA : (Set.range ξ).Finite) (hpos : ∀ z, 0 < ξ z)
    {n : ℕ} {h : Fin n → ℤ × ℤ} (hne : ∀ i, h i ≠ 0)
    (hnp : Pairwise fun i j => det (h i) (h j) ≠ 0) (hann : act (prodShift h) ξ = 0)
    {ζ : Config ℤ} (hζ : ζ ∈ orbitClosure ξ) (hζnp : ¬ IsPeriodic ζ)
    {p : ℕ} [Fact p.Prime] (hlt : ∀ z, ξ z < p) :
    ∃ (n' : ℕ) (h' : Fin n' → ℤ × ℤ) (G : Fin n' → Config (ZMod p)),
      2 ≤ n' ∧ (∀ i, h' i ≠ 0) ∧ (Pairwise fun i j => det (h' i) (h' j) ≠ 0) ∧
        (∀ i, h' i ∈ Per (G i)) ∧ (∀ i, ¬ DoublyPeriodic (G i)) ∧
        ∀ z, modP p ζ z = ∑ i, G i z := by
  classical
  -- The values of `ζ` are values of `ξ`, so `ζ` also has its alphabet in `[[p]]`.
  have hval : ∀ z, ∃ w, ζ z = ξ w := by
    intro z
    obtain ⟨u, hu⟩ := hζ {z}
    exact ⟨u + z, hu z (Finset.mem_singleton_self z)⟩
  have hζpos : ∀ z, 0 < ζ z := fun z => by
    obtain ⟨w, hw⟩ := hval z; rw [hw]; exact hpos w
  have hζlt : ∀ z, ζ z < p := fun z => by
    obtain ⟨w, hw⟩ := hval z; rw [hw]; exact hlt w
  -- (a) The annihilation passes to `ζ`, and Theorem 8.4(b) decomposes it over `ℤ`.
  obtain ⟨f, hfper, hfsum⟩ :=
    kari_szabados_decomp hne hnp (ann_of_mem_orbitClosure hann hζ)
  -- (b) Reduce mod `p`; nothing is lost.
  have hmsum : ∀ z, modP p ζ z = ∑ i, modP p (f i) z := by
    intro z
    show ((ζ z : ℤ) : ZMod p) = ∑ i, ((f i z : ℤ) : ZMod p)
    rw [hfsum z]
    push_cast
    rfl
  have hmnp : ¬ IsPeriodic (modP p ζ) := fun hc =>
    hζnp ((isPeriodic_modP_iff hζpos hζlt).mp hc)
  -- (c) Operation A removes the doubly periodic components.
  exact exists_decomp_not_doublyPeriodic hmnp n h (fun i => modP p (f i)) hne hnp
    (fun i => mem_Per_comp (hfper i) (fun a : ℤ => (a : ZMod p))) hmsum

/-! ### Theorems 8.6 and 8.7 -/

/-! **Theorem 8.6 (Colle [2, Theorem 1.9]).**  Reference [2]: C. F. Colle, *On periodic
decompositions, one-sided nonexpansive directions and Nivat's conjecture*, Discrete Contin. Dyn.
Syst. **43** (2023), no. 12, 4299–4327.  Let `A ⊆ ℤ` be finite and let `ξ ∈ A^{ℤ²}` have a
non-trivial annihilator.  If for every line `ℓ` either `−ℓ ∉ ONED(ξ)` or `ℓ ∉ ONED(ξ)`, then `ξ`
is fully periodic.

Quoted from [2]; not proved in this development.  Its proof uses the periodic-limit theorem of
Kari–Moutot [9, 10] and the Boyle–Lind theorem [1]; it does not depend on the equal-order
assumption of [2, §4.1].

**Fidelity check**: the arXiv preprint of [2] (arXiv:1909.08195v4; content matches, though the
published DCDS pagination/numbering may differ per the paper's own note "Theorem and lemma
numbers of the cited works are those of the originals") states this, verbatim in content, as its
Theorem 1.14: *"Let `η ∈ A^{ℤ²}`, with `A ⊂ ℤ`, be a configuration with a non-trivial
annihilator. If `−ℓ ∉ ONED(η)` or `ℓ ∉ ONED(η)` for all lines `ℓ ⊂ ℝ²` through the origin, then
`η` is fully periodic."*  The Lean `hONED` hypothesis quantifies over all non-zero direction
vectors `w` rather than "lines `ℓ`"; since `¬(w ∈ ONED ∧ −w ∈ ONED)` is invariant under
`w ↦ −w`, this is a faithful, sound reformulation (each unoriented line has exactly the two
directions `±w`).  The "fully periodic on the whole plane" conclusion is exactly
`DoublyPeriodic ξ`, matching source Definition 1.5/notation `X` restricted to `𝒰 = ℤ²`.  No
discrepancy found; only the citation number "Theorem 1.9" could not be cross-checked against the
published (rather than preprint) numbering. -/
-- **Theorem 8.6 (Colle [2, Theorem 1.9] = arXiv:1909.08195v4, Theorem 1.14)** was stated here
-- as the `axiom colle_doublyPeriodic`, with `exists_mem_ONED` as its stated consequence.
-- **Deleted 2026-09-18**: both are proved, as `Nivat.Colle.theorem114` and
-- `Nivat.exists_mem_ONED'` (`Section8/ExternalDischarged.lean`), and nothing in the tree
-- referred to the axiom version any more.  The fidelity check of the statement against the
-- source, which used to sit in the docstring here, moved with the proof to
-- `Nivat/External/Colle/Theorem114Final.lean`.

-- **Theorem 8.7 (Colle [2, proof of Lemma 4.6])** was stated here as the
-- `axiom colle_region`, with `exists_fullyPeriodic_region` combining it with Theorem 8.6.
-- **Deleted 2026-09-18**: `Nivat.ColleReg.colle_region` (`External/Colle/ColleRegion.lean`)
-- now carries a statement that is `rfl`-identical to what the axiom declared — checked by
-- `tmp/subst_check.lean`, which prints both `#check`s side by side — and is substituted at the
-- one call site, `Nivat.exists_fullyPeriodic_region'`
-- (`Section8/ExternalDischarged.lean`).  `Nivat.nivat_conjecture` no longer mentions
-- `Nivat.colle_region`.  Its closure carried `sorryAx` (the open leaves of
-- `External/Colle/RegionSteps.lean`) until 2026-09-30, when the last leaf closed; it now
-- measures `[propext, Classical.choice, Quot.sound]` (see the Status section above).
--
-- ⚠ This file is *upstream* of everything under `Nivat/External/Colle/`, so the proof could
-- never be substituted here; that is why the axiom existed at all, and why the substitution
-- had to happen downstream in `ExternalDischarged.lean`.

end Nivat
