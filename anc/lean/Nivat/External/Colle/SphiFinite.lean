/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.EdgeNormals
import Nivat.External.Colle.NewtonZonotope
import Nivat.External.Colle.ConvTransport
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.MaximalEnveloped

/-!
# `hSfin` for the real `d.Sphi` (team-lead's 6-step chain, verified and compiled)

Discharges the finiteness obligation left open in `tmp/L1_lemma35i_antecedent.lean`:
`∀ B', Enveloped (↑d.Sphi) B' → B'.Finite` for a genuine `d : DecompDataZ ξ`, not an assumed
hypothesis. Chain, checked at each declaration rather than trusted:

1. `d.Sphi_eq` (`DecompData.lean:107`): `Conv d.Sphi = Conv (supp (∏ i, mono (d.h i) - 1))`.
2. `Conv_supp_prod_eq_Conv_zonoF` (`NewtonZonotope.lean:181-183`, **not `:42-43`** as first
   cited — that line range is a docstring paragraph describing the theorem, the actual
   `theorem` keyword is at `:181`): `Conv (supp ∏(mono(h i)-1)) = Conv (zonoF univ h)`.
3. `E_congr_of_Conv_eq` (`ConvTransport.lean:233`, **not `:12`** — `:12` is inside a module
   docstring quoting the signature as the file's own motivating example; the live `theorem`
   is at `:233`): transports the edge set across the `Conv` equality.
4. `coe_zonoF` (`NewtonZonotope.lean:137-138`, confirmed as cited): identifies
   `↑(zonoF s h) = ∑ i ∈ s, segOf (h i)`.
5. `exists_two_nonparallel_edge_normals` (`EdgeNormals.lean:38-42`, confirmed as cited, fully
   proved, no `sorry`) fed `d.hm`, `d.h_ne`, `d.h_dir` — all three are genuine `DecompData`
   fields (`DecompData.lean:88`, `:96`(approx), `:103`(approx)), not new obligations: **`m ≥ 2`
   is already a field (`hm : 2 ≤ m`, line 88), contrary to the "not found as a field, only in
   prose at `:50`/`:73`" note in the retasking message.** `DecompDataZ.of_minimalCounterexample`
   (`DecompData.lean:314-316`) is the sole producer and genuinely populates it
   (`hm := hn2`, constructed by case-splitting away `m = 0` and `m = 1` earlier in that proof).
   So **no residual obligation for `m ≥ 2`.**
6. The antipodal halves `-n, -n' ∈ E (∑ segOf (d.h i))`: unfold membership via `E_zono`
   (`MinkowskiEdges.lean:292`) to find the witnessing index, then close under negation via
   `E_segOf` (`MinkowskiEdges.lean:204`) + `Prim.neg` (`LatticeEdges.lean:106`) +
   `dot_neg_left` (`LatticeEdges.lean:82`), then re-pack via `E_zono`.
7. `finite_E_of_finite` (`LatticeEdges.lean:317`) on `(↑d.Sphi).Finite` (free, `d.Sphi` is a
   `Finset`) gives `(E ↑d.Sphi).Finite`.
8. `Enveloped.finite` (`MaximalEnveloped.lean:157-161`) closes it.

Compiled via `bash scripts/check1.sh tmp/L1_hSfin.lean` (see `#print axioms` at bottom).
-/

namespace Nivat.L1Sfin

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Pointwise

theorem hSfin_of_decompDataZ {ξ : Config ℤ} (d : DecompDataZ ξ) :
    ∀ B' : Set (ℤ × ℤ), Enveloped (d.Sphi : Set (ℤ × ℤ)) B' → B'.Finite := by
  classical
  -- Step 5: the two independent edge normals of the zonotope, from `DecompData`'s own fields.
  obtain ⟨n, n', hnmem, hn'mem, hdet⟩ :=
    exists_two_nonparallel_edge_normals d.hm d.h_ne d.h_dir
  -- Steps 1–4: transport `E ↑d.Sphi = E (∑ i, segOf (d.h i))`.
  have hConv : Conv d.Sphi = Conv (zonoF Finset.univ d.h) := by
    rw [d.Sphi_eq]
    exact Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun i _ => d.h_ne i)
  have hEeq : E (d.Sphi : Set (ℤ × ℤ)) = E (↑(zonoF Finset.univ d.h) : Set (ℤ × ℤ)) :=
    E_congr_of_Conv_eq hConv
  have hcoe : (↑(zonoF Finset.univ d.h) : Set (ℤ × ℤ))
      = ∑ i ∈ Finset.univ, segOf (d.h i) := coe_zonoF _ _
  rw [hcoe] at hEeq
  -- Step 6: the antipodal halves.
  have hzono := E_zono (Finset.univ : Finset (Fin d.m)) d.h
  obtain ⟨i, -, hni⟩ := Set.mem_iUnion₂.mp (hzono ▸ hnmem)
  obtain ⟨i', -, hn'i'⟩ := Set.mem_iUnion₂.mp (hzono ▸ hn'mem)
  have hnegn : -n ∈ E (segOf (d.h i)) := by
    rw [E_segOf (d.h_ne i)] at hni ⊢
    exact ⟨hni.1.neg, by rw [dot_neg_left, hni.2, neg_zero]⟩
  have hnegn' : -n' ∈ E (segOf (d.h i')) := by
    rw [E_segOf (d.h_ne i')] at hn'i' ⊢
    exact ⟨hn'i'.1.neg, by rw [dot_neg_left, hn'i'.2, neg_zero]⟩
  have hnegn_zono : -n ∈ ⋃ j ∈ (Finset.univ : Finset (Fin d.m)), E (segOf (d.h j)) :=
    Set.mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, hnegn⟩
  have hnegn'_zono : -n' ∈ ⋃ j ∈ (Finset.univ : Finset (Fin d.m)), E (segOf (d.h j)) :=
    Set.mem_iUnion₂.mpr ⟨i', Finset.mem_univ i', hnegn'⟩
  rw [← hzono] at hnegn_zono hnegn'_zono
  -- Transport all four back to `E ↑d.Sphi`.
  have hn_S : n ∈ E (d.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hnmem
  have hn'_S : n' ∈ E (d.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hn'mem
  have hnegn_S : -n ∈ E (d.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hnegn_zono
  have hnegn'_S : -n' ∈ E (d.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hnegn'_zono
  -- Steps 7–8.
  have hUfin : (E (d.Sphi : Set (ℤ × ℤ))).Finite :=
    finite_E_of_finite d.Sphi.finite_toSet
  intro B' hB'
  exact Enveloped.finite hUfin hdet hn_S hnegn_S hn'_S hnegn'_S hB'

/-- **The edge-normal package `TLSeam.stepHyp_of_case2` needs**, extracted from the same
six-step chain as `hSfin_of_decompDataZ` above (steps 5–6 give `hn`/`hn'`/`hdet`/the antipodal
halves; step 7 gives `hU`).  Landed 2026-09-22 (lane-leafa), closing the `hSfin_of_decompDataZ`
blocker flagged in `blueprint/LEAF-A.md`'s "2026-09-22（续）" section: `StepHypSeam.lean:59`'s
`stepHyp_of_case2` wants exactly `(hU, hdet, hn, hn', hm, hm')` for `S := d.Sphi`, and this is
that tuple, packaged so the assembly does not have to re-derive it. -/
theorem exists_edge_normal_package {ξ : Config ℤ} (d : DecompDataZ ξ) :
    ∃ n m : ℤ × ℤ, (E (d.Sphi : Set (ℤ × ℤ))).Finite ∧ det n m ≠ 0 ∧
      n ∈ E (d.Sphi : Set (ℤ × ℤ)) ∧ -n ∈ E (d.Sphi : Set (ℤ × ℤ)) ∧
      m ∈ E (d.Sphi : Set (ℤ × ℤ)) ∧ -m ∈ E (d.Sphi : Set (ℤ × ℤ)) := by
  classical
  obtain ⟨n, n', hnmem, hn'mem, hdet⟩ :=
    exists_two_nonparallel_edge_normals d.hm d.h_ne d.h_dir
  have hConv : Conv d.Sphi = Conv (zonoF Finset.univ d.h) := by
    rw [d.Sphi_eq]
    exact Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun i _ => d.h_ne i)
  have hEeq : E (d.Sphi : Set (ℤ × ℤ)) = E (↑(zonoF Finset.univ d.h) : Set (ℤ × ℤ)) :=
    E_congr_of_Conv_eq hConv
  have hcoe : (↑(zonoF Finset.univ d.h) : Set (ℤ × ℤ))
      = ∑ i ∈ Finset.univ, segOf (d.h i) := coe_zonoF _ _
  rw [hcoe] at hEeq
  have hzono := E_zono (Finset.univ : Finset (Fin d.m)) d.h
  obtain ⟨i, -, hni⟩ := Set.mem_iUnion₂.mp (hzono ▸ hnmem)
  obtain ⟨i', -, hn'i'⟩ := Set.mem_iUnion₂.mp (hzono ▸ hn'mem)
  have hnegn : -n ∈ E (segOf (d.h i)) := by
    rw [E_segOf (d.h_ne i)] at hni ⊢
    exact ⟨hni.1.neg, by rw [dot_neg_left, hni.2, neg_zero]⟩
  have hnegn' : -n' ∈ E (segOf (d.h i')) := by
    rw [E_segOf (d.h_ne i')] at hn'i' ⊢
    exact ⟨hn'i'.1.neg, by rw [dot_neg_left, hn'i'.2, neg_zero]⟩
  have hnegn_zono : -n ∈ ⋃ j ∈ (Finset.univ : Finset (Fin d.m)), E (segOf (d.h j)) :=
    Set.mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, hnegn⟩
  have hnegn'_zono : -n' ∈ ⋃ j ∈ (Finset.univ : Finset (Fin d.m)), E (segOf (d.h j)) :=
    Set.mem_iUnion₂.mpr ⟨i', Finset.mem_univ i', hnegn'⟩
  rw [← hzono] at hnegn_zono hnegn'_zono
  have hn_S : n ∈ E (d.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hnmem
  have hn'_S : n' ∈ E (d.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hn'mem
  have hnegn_S : -n ∈ E (d.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hnegn_zono
  have hnegn'_S : -n' ∈ E (d.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hnegn'_zono
  have hUfin : (E (d.Sphi : Set (ℤ × ℤ))).Finite :=
    finite_E_of_finite d.Sphi.finite_toSet
  exact ⟨n, n', hUfin, hdet, hn_S, hnegn_S, hn'_S, hnegn'_S⟩

end Nivat.L1Sfin

#print axioms Nivat.L1Sfin.hSfin_of_decompDataZ
#print axioms Nivat.L1Sfin.exists_edge_normal_package
