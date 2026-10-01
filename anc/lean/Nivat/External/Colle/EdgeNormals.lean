/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.MinkowskiEdges

/-!
# Two non-parallel edge normals of the zonotope `S_φ`

Collé's construction needs a *second* edge direction `ℓ' = ℓ_J` of `S_φ`, non-parallel to
the first (`scratch/b3_colle2.txt:890`, `:904`).  The geometric reason is Lemma 3.5's own
hypothesis (`:424`, verbatim):

> "where `h₁, …, h_m ∈ ℤ²`, with `m ≥ 2`, are vectors in pairwise distinct directions"

Each generator `h_i` contributes the segment `[0, h_i]` to `S_φ = ∑ᵢ [0, h_i]`, and
`E_segOf` (`MinkowskiEdges.lean:204`) identifies the edge normals of a segment with the
primitive vectors orthogonal to it, while `E_zono` (`:292`) says the zonotope's edge set is
the union of those.  So two generators in distinct directions give two edge normals in
distinct directions.

Both building blocks were already in the tree — `exists_prim_orthogonal`
(`MinkowskiEdges.lean:397`) and `dot_eq_zero_of_det_eq_zero` (`LatticeEdges.lean:1702`);
this file only assembles them.

## Main results

* `exists_two_nonparallel_edge_normals`
* `exists_edge_normal_nonparallel_to` — the form used by Collé at `:890`.
-/

namespace Nivat.LE2

open Nivat Pointwise

/-- **A zonotope over pairwise non-parallel generators has two non-parallel edge normals.**

Transcribes the consequence of `b3_colle2.txt:424` that lets Collé name `ℓ_J`. -/
theorem exists_two_nonparallel_edge_normals {m : ℕ} (hm : 2 ≤ m)
    {h : Fin m → ℤ × ℤ} (hh_ne : ∀ i, h i ≠ 0)
    (hh_dir : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0) :
    ∃ n n' : ℤ × ℤ, n ∈ E (∑ i ∈ Finset.univ, segOf (h i)) ∧
      n' ∈ E (∑ i ∈ Finset.univ, segOf (h i)) ∧ det n n' ≠ 0 := by
  have h0m : 0 < m := by omega
  have h1m : 1 < m := by omega
  obtain ⟨n, hn_prim, hn_orth⟩ := exists_prim_orthogonal (hh_ne ⟨0, h0m⟩)
  obtain ⟨n', hn'_prim, hn'_orth⟩ := exists_prim_orthogonal (hh_ne ⟨1, h1m⟩)
  refine ⟨n, n', ?_, ?_, ?_⟩
  · rw [E_zono]
    refine Set.mem_biUnion (x := (⟨0, h0m⟩ : Fin m)) (Finset.mem_univ _) ?_
    rw [E_segOf (hh_ne ⟨0, h0m⟩)]
    exact ⟨hn_prim, by rw [dot_comm]; exact hn_orth⟩
  · rw [E_zono]
    refine Set.mem_biUnion (x := (⟨1, h1m⟩ : Fin m)) (Finset.mem_univ _) ?_
    rw [E_segOf (hh_ne ⟨1, h1m⟩)]
    exact ⟨hn'_prim, by rw [dot_comm]; exact hn'_orth⟩
  · intro hdet
    refine hh_dir ⟨0, h0m⟩ ⟨1, h1m⟩ (by simp [Fin.ext_iff]) ?_
    -- `h 0 ⟂ n` and, since `n ∥ n'` and `h 1 ⟂ n'`, also `h 1 ⟂ n`.
    refine det_eq_zero_of_dot_eq_zero hn_prim.ne_zero ?_ ?_
    · rw [dot_comm]; exact hn_orth
    · refine dot_eq_zero_of_det_eq_zero hn'_prim.ne_zero hdet ?_
      rw [dot_comm]; exact hn'_orth

/-- **Given one edge normal, produce a second one non-parallel to it.**

This is the form Collé uses at `b3_colle2.txt:890`: `ℓ` is already fixed and `ℓ' = ℓ_J`
must be chosen non-parallel to it. -/
theorem exists_edge_normal_nonparallel_to {m : ℕ} (hm : 2 ≤ m)
    {h : Fin m → ℤ × ℤ} (hh_ne : ∀ i, h i ≠ 0)
    (hh_dir : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0)
    {ℓ : ℤ × ℤ} (hℓ : ℓ ∈ E (∑ i ∈ Finset.univ, segOf (h i))) :
    ∃ n' : ℤ × ℤ, n' ∈ E (∑ i ∈ Finset.univ, segOf (h i)) ∧ det ℓ n' ≠ 0 := by
  classical
  rw [E_zono] at hℓ
  simp only [Set.mem_iUnion, exists_prop] at hℓ
  obtain ⟨i, -, hℓi⟩ := hℓ
  rw [E_segOf (hh_ne i)] at hℓi
  obtain ⟨hℓ_prim, hℓ_orth⟩ := hℓi
  -- pick an index different from `i`
  have h0m : 0 < m := by omega
  have h1m : 1 < m := by omega
  set j : Fin m := if i = ⟨0, h0m⟩ then ⟨1, h1m⟩ else ⟨0, h0m⟩ with hj
  have hji : j ≠ i := by
    rw [hj]; split_ifs with hc
    · rw [hc]; simp [Fin.ext_iff]
    · exact fun hcon => hc hcon.symm
  obtain ⟨n', hn'_prim, hn'_orth⟩ := exists_prim_orthogonal (hh_ne j)
  refine ⟨n', ?_, ?_⟩
  · rw [E_zono]
    refine Set.mem_biUnion (x := j) (Finset.mem_univ j) ?_
    rw [E_segOf (hh_ne j)]
    exact ⟨hn'_prim, by rw [dot_comm]; exact hn'_orth⟩
  · intro hdet
    refine hh_dir i j (Ne.symm hji) ?_
    refine det_eq_zero_of_dot_eq_zero hℓ_prim.ne_zero hℓ_orth ?_
    refine dot_eq_zero_of_det_eq_zero hn'_prim.ne_zero hdet ?_
    rw [dot_comm]; exact hn'_orth

end Nivat.LE2
