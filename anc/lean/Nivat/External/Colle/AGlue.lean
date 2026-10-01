/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ItemIIChain
import Nivat.External.Colle.ONEDRational
import Nivat.External.Colle.SfinBound

/-!
# Two glue lemmas for leaf A

Connects `ItemIIChain.exists_itemII_chain` to the `exists_chainData` call site.

1. `eq_or_neg_of_primitive_of_perp`: primitive vectors perpendicular to the same non-zero
   vector are ± each other.
2. `exists_four_edge_normals`: extract the four-normal fact from `DecompDataZ`.

Both theorems are pure geometry/linear algebra, no `Config` content.
-/

set_option autoImplicit false

namespace Nivat.AGlue

open Nivat Nivat.LE2

/-- **Two primitive vectors perpendicular to the same non-zero vector are ± each other.**

The rank-1 subgroup of `ℤ²` perpendicular to a non-zero vector has exactly two primitive
elements, which are negatives of each other. -/
theorem eq_or_neg_of_primitive_of_perp
    {vl n n' : ℤ × ℤ} (hvl : vl ≠ 0)
    (hn : Primitive n) (hn' : Primitive n')
    (hperp : dot n vl = 0) (hperp' : dot n' vl = 0) :
    n = n' ∨ n = -n' := by
  -- `n` and `n'` are parallel because both are perpendicular to `vl`.
  have hdet : det n n' = 0 := det_eq_zero_of_dot_eq_zero hvl (dot_comm n vl ▸ hperp) (dot_comm n' vl ▸ hperp')
  -- Since they're parallel and both primitive, they're equal or opposite.
  have hn_prim : Prim n := prim_iff_primitive.mpr hn
  have hn'_prim : Prim n' := prim_iff_primitive.mpr hn'
  have hdet' : det n' n = 0 := by rw [det_comm, hdet]; simp
  exact eq_or_neg_of_prim_of_det_eq_zero hn'_prim hn_prim hdet'

/-- **Extract four edge normals `±n, ±m` with `det n m ≠ 0` from `DecompDataZ`.**

The proof extracts the intermediate result from `hSfin_of_decompDataZ`'s proof body,
which already constructs these normals but only exports finiteness. -/
theorem exists_four_edge_normals {ξ : Config ℤ} (d : Colle35.DecompDataZ ξ) :
    ∃ n m : ℤ × ℤ, det n m ≠ 0 ∧
      n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧
      m ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -m ∈ E (↑d.Sphi : Set (ℤ × ℤ)) := by
  -- Step 1: the two independent edge normals from the zonotope.
  obtain ⟨n, n', hnmem, hn'mem, hdet⟩ :=
    exists_two_nonparallel_edge_normals d.hm d.h_ne d.h_dir
  -- Step 2: transport `E ↑d.Sphi = E (∑ i, segOf (d.h i))`.
  have hConv : Conv d.Sphi = Conv (zonoF Finset.univ d.h) := by
    rw [d.Sphi_eq]
    exact Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun i _ => d.h_ne i)
  have hEeq : E (d.Sphi : Set (ℤ × ℤ)) = E (↑(zonoF Finset.univ d.h) : Set (ℤ × ℤ)) :=
    E_congr_of_Conv_eq hConv
  rw [coe_zonoF] at hEeq
  -- Step 3: transport the positive halves to `E ↑d.Sphi`.
  have hn_S : n ∈ E (d.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hnmem
  have hn'_S : n' ∈ E (d.Sphi : Set (ℤ × ℤ)) := hEeq ▸ hn'mem
  -- Step 4: the antipodal halves via `Colle35.Sphi_negSymm`.
  have hneg_n_S : -n ∈ E (d.Sphi : Set (ℤ × ℤ)) := (Colle35.Sphi_negSymm d.toDecompData n).mp hn_S
  have hneg_n'_S : -n' ∈ E (d.Sphi : Set (ℤ × ℤ)) := (Colle35.Sphi_negSymm d.toDecompData n').mp hn'_S
  exact ⟨n, n', hdet, hn_S, hneg_n_S, hn'_S, hneg_n'_S⟩

end Nivat.AGlue

#print axioms Nivat.AGlue.eq_or_neg_of_primitive_of_perp
#print axioms Nivat.AGlue.exists_four_edge_normals
