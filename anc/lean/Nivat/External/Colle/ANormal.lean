/-
Copyright (c) 2026 Nivat formalisation project.
-/
import Nivat.External.Colle.FaceDistinct
import Nivat.External.Colle.FaceData
import Nivat.External.Colle.Claim47Core
import Nivat.External.Colle.EdgeNormals
import Nivat.External.Colle.ONEDRational

/-!
# Constructing `n_J`: the `ℓ_J`-normal of `S_φ`, with its orthogonal generator

`FaceDistinct.lean` (landed 2026-09-18) reduced the `a ≠ a'` gap of `ChainDataGeom` to a single
*bookkeeping* obligation on the producer of `exists_chainData` (`RegionSteps.lean:822`):

    ∃ i : Fin d.m, dot nJ (d.h i) = 0

`blueprint/OPEN.md` #7 records that this is **not** free — trying to read it off `E_zono`
(`MinkowskiEdges.lean:292`) requires `nJ ∈ E ↑d.Sphi` first, which is the very thing one wants.

The circle is broken by going the other way round: **do not derive the orthogonality from
`n_J`, manufacture `n_J` from the orthogonality.**  `ℓ_J` is by definition one of the lines
through the origin parallel to an edge of `S_φ` (`b3_colle2.txt:424`, `:541`), and `S_φ` is the
zonotope on the decomposition periods `h_1, …, h_m`, so the construction is: *pick a generator
`h i`, take the primitive normal of `h i`.*  Then

* `dot n_J (h i) = 0` holds **by construction** — nothing to prove downstream;
* `n_J ∈ E ↑d.Sphi` and `-n_J ∈ E ↑d.Sphi` follow from `DecompData.mem_E_Sphi_of_dot_eq_zero`
  (`FaceDistinct.lean:146`) and its antipodal companion;
* `a ≠ a'` follows from `ChainDataGeom.a_ne_a'_of_dot_h_eq_zero` (`FaceDistinct.lean:174`).

The one genuine constraint is the *choice of index*: `ChainDataGeom.dot_nJ_p` (`ChainGeom.lean`)
demands `dot n_J p ≠ 0`, i.e. `n_J` must not be orthogonal to the recession direction `p`.  Since
`n_J ⊥ h i`, that says exactly `p ∦ h i`.  `DecompData.h_dir` (`DecompData.lean:104`) makes the
generators pairwise non-parallel, so **at most one** of them is parallel to `p`, and `hm : 2 ≤ m`
(`DecompData.lean:88`) leaves a choice.  This is `DecompData.exists_index_det_ne_zero` below, and
it is why the construction needs nothing beyond `p ≠ 0`.

## What is delivered

* `DecompData.exists_index_det_ne_zero` — the index choice.
* `DecompData.exists_nJ` — `n_J` itself: primitive, orthogonal to `d.h i`, transverse to `p`,
  and an edge normal of `S_φ` in both signs.
* `DecompData.exists_nJ_vJ` — `n_J` together with `v_J`, the primitive part of `d.h i`, which is
  the `ChainDataGeom.vJ` the same edge determines (`dot_nJ_vJ`, `vJ_prim`, `vJ_ne`, and
  `det p vJ ≠ 0`, the non-degeneracy the `ℓ_ι`-normal `det p vJ • (-p.2, p.1)` of
  `ahat_halfPlane_L` (`ChainGeom.lean:180`) needs).
* `DecompData.exists_edge_block` — the whole `ℓ_J`-edge block of `ChainDataGeom`
  (`vJ a a' r a_mem a'_mem lex lex' edge edge' dot_nJ_vJ vJ_prim vJ_ne nJ_prim dot_nJ_p`,
  `ChainGeom.lean:69-93`, `:95`, `:111`, `:113`, `:163`) in one existential, plus `0 < r` and
  `a ≠ a'`.  Assembled from `FaceData.exists_lex_max` / `exists_lex_max'` / `exists_r_edge` /
  `exists_edge'` (`FaceData.lean:137`, `:149`, `:189`, `:294`).

⚠ **`exists_lex_max` 的「max」是对 `dot (-n)` 取的，所以 `FaceBlock.a` 是 `S` 的
`n`-极小面端点，不是极大。** `lex` 字段逐字是
`dot (-n) b < dot (-n) a ∨ …` ⟹ `dot n a < dot n b`。
这是一名两物（§97）：名字里的 `max` 与几何上的「低端」指同一件事。
lane-leafa-gen 2026-09-25 在他们的窗口判据里碰到过这个方向，特此在本文件登记。

Second, the **assembly of three orphan lemmas** into Collé's `b3_colle2.txt:890` chain (no new
mathematics; see the section header below for the diagram):

* `DecompData.E_Sphi_eq_zonoF` / `E_Sphi_eq` — the seam `E ↑d.Sphi = E ↑(zonoF univ d.h)`.
* `DecompData.existsUnique_index_dot_eq_zero` — `FaceData.lean:36` through the seam.
* `DecompData.exists_edge_normal_nonparallel` — `EdgeNormals.lean:68` through the seam.
* `DecompData.exists_nJ_of_edge` — the two composed.
* `ChainDataGeom.a_ne_a'_iff_nJ_mem_E`, `a_ne_a'_iff_exists_dot_h_eq_zero` — the
  `FaceDistinct.lean` end, with the antipode removed by `Sphi_negSymm`.

## What is **not** delivered

Nothing here touches `Env`, the shell block, `bottom`, `rec_p`, `rec_vJ`, `cL`, `nfp_L`, or
`ahat_halfPlane` — `n_J` is constructed, the *placement* of `Â_∞` relative to it is untouched.
In particular this does **not** discharge `exists_chainData`.  See `blueprint/LEAF-A.md`.
-/

set_option autoImplicit false

namespace Nivat.Colle35

open Nivat Nivat.LE2

variable {α : Type*}

/-! ## Parallelism is transitive away from the origin

`det p · = 0` is `dot (perp p) · = 0` (`Nivat.ColleReg.dot_perp`, `Claim47Core.lean:47`), so
`det_eq_zero_of_dot_eq_zero` (`LatticeEdges.lean:110`) transfers verbatim. -/

/-- `perp` (`Claim47Core.lean:45`) does not kill a nonzero vector. -/
theorem perp_ne_zero {v : ℤ × ℤ} (hv : v ≠ 0) : Nivat.ColleReg.perp v ≠ 0 := by
  intro h
  apply hv
  have h' : (-v.2, v.1) = ((0 : ℤ), (0 : ℤ)) := h
  rw [Prod.ext_iff] at h'
  exact Prod.ext (by simpa using h'.2) (by simpa using h'.1)

/-- Two vectors parallel to one and the same nonzero `p` are parallel to each other.  The
`det`-analogue of `det_eq_zero_of_dot_eq_zero` (`LatticeEdges.lean:110`). -/
theorem det_eq_zero_of_det_eq_zero {p u v : ℤ × ℤ} (hp : p ≠ 0)
    (hu : det p u = 0) (hv : det p v = 0) : det u v = 0 :=
  det_eq_zero_of_dot_eq_zero (perp_ne_zero hp)
    (by rw [Nivat.ColleReg.dot_perp]; exact hu)
    (by rw [Nivat.ColleReg.dot_perp]; exact hv)

/-! ## The index choice -/

/-- **Some decomposition period is transverse to `p`.**

`h_dir` (`DecompData.lean:104`) makes the `h_i` pairwise non-parallel, so at most one of them
can be parallel to a fixed nonzero `p`; `hm : 2 ≤ m` (`DecompData.lean:88`) then leaves at least
one that is not.  Only `hm` and `h_dir` are used — no minimality, no annihilator hypothesis. -/
theorem DecompData.exists_index_det_ne_zero [AddCommMonoid α] {η : Config α}
    (d : DecompData η) {p : ℤ × ℤ} (hp : p ≠ 0) :
    ∃ i : Fin d.m, det p (d.h i) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hm := d.hm
  have hne : (⟨0, by omega⟩ : Fin d.m) ≠ (⟨1, by omega⟩ : Fin d.m) := by
    simp [Fin.ext_iff]
  exact d.h_dir _ _ hne
    (det_eq_zero_of_det_eq_zero hp (hcon ⟨0, by omega⟩) (hcon ⟨1, by omega⟩))

/-! ## The normal itself -/

/-- **The primitive normal of `w`, transverse to `p`.**

Take the primitive part of `perp w` (`exists_primitive_nsmul_eq`, `Lattice/Primitive.lean:52`).
Orthogonality to `w` is `det w w = 0` divided by the multiplier; transversality to `p` is the
hypothesis `det p w ≠ 0` read through `det_eq_zero_of_dot_eq_zero`. -/
theorem exists_prim_dot_zero_dot_ne_zero {w p : ℤ × ℤ} (hw : w ≠ 0) (hdet : det p w ≠ 0) :
    ∃ n : ℤ × ℤ, Primitive n ∧ dot n w = 0 ∧ dot n p ≠ 0 := by
  obtain ⟨v, k, hprim, hkpos, heq⟩ := exists_primitive_nsmul_eq (perp_ne_zero hw)
  have hk : (k : ℤ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hcomp : -w.2 = (k : ℤ) * v.1 ∧ w.1 = (k : ℤ) * v.2 := by
    have h' := heq
    simp only [Nivat.ColleReg.perp, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at h'
    exact h'
  obtain ⟨e1, e2⟩ := hcomp
  have hdotvw : dot v w = 0 := by
    have hkey : (k : ℤ) * dot v w = 0 := by
      simp only [dot]
      linear_combination (-w.1) * e1 + (-w.2) * e2
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h hk
    · exact h
  refine ⟨v, hprim, hdotvw, ?_⟩
  intro hvp
  exact hdet (det_eq_zero_of_dot_eq_zero hprim.ne_zero hvp hdotvw)

/-- **`n_J`.**  The producer's obligation `∃ i, dot nJ (d.h i) = 0` is discharged *by the
construction of `nJ`*, not derived from it.

The two `E ↑d.Sphi` memberships come free from `DecompData.mem_E_Sphi_of_dot_eq_zero` and
`DecompData.neg_mem_E_Sphi_of_dot_eq_zero` (`FaceDistinct.lean:146`, `:159`); the second is
what `ChainDataGeom.a_ne_a'_iff_negNJ_mem_E` (`FaceDistinct.lean:125`) consumes.

`dot n p ≠ 0` is `ChainDataGeom.dot_nJ_p` (`ChainGeom.lean`) and is the only place the
index choice is spent. -/
theorem DecompData.exists_nJ [AddCommMonoid α] {η : Config α} (d : DecompData η)
    {p : ℤ × ℤ} (hp : p ≠ 0) :
    ∃ (n : ℤ × ℤ) (i : Fin d.m), Primitive n ∧ dot n (d.h i) = 0 ∧ dot n p ≠ 0 ∧
      n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) := by
  obtain ⟨i, hi⟩ := d.exists_index_det_ne_zero hp
  obtain ⟨n, hprim, hdw, hdp⟩ := exists_prim_dot_zero_dot_ne_zero (d.h_ne i) hi
  exact ⟨n, i, hprim, hdw, hdp,
    d.mem_E_Sphi_of_dot_eq_zero (prim_iff_primitive.mpr hprim) i hdw,
    d.neg_mem_E_Sphi_of_dot_eq_zero (prim_iff_primitive.mpr hprim) i hdw⟩

/-- **`n_J` and `v_J` from the same generator.**

`v_J` is the primitive part of `d.h i`.  It delivers `dot_nJ_vJ` (`ChainGeom.lean:96`),
`vJ_prim` (`:151`), `vJ_ne` (`:113`) and `det p vJ ≠ 0` — the last is the non-degeneracy of the
`ℓ_ι`-normal `det p vJ • (-p.2, p.1)` that `ahat_halfPlane_L` (`:153`) is written with. -/
theorem DecompData.exists_nJ_vJ [AddCommMonoid α] {η : Config α} (d : DecompData η)
    {p : ℤ × ℤ} (hp : p ≠ 0) :
    ∃ (n v : ℤ × ℤ) (i : Fin d.m) (k : ℕ), Primitive n ∧ Primitive v ∧ 0 < k ∧
      d.h i = (k : ℤ) • v ∧ dot n (d.h i) = 0 ∧ dot n v = 0 ∧ dot n p ≠ 0 ∧
      det p v ≠ 0 ∧ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) := by
  obtain ⟨n, i, hprim, hdw, hdp, hmem, hmem'⟩ := d.exists_nJ hp
  obtain ⟨v, k, hvprim, hkpos, hveq⟩ := exists_primitive_nsmul_eq (d.h_ne i)
  have hk : (k : ℤ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hdotnv : dot n v = 0 := by
    have hkey : (k : ℤ) * dot n v = 0 := by
      rw [← Nivat.ColleReg.dot_zsmul_right, ← hveq]; exact hdw
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h hk
    · exact h
  exact ⟨n, v, i, k, hprim, hvprim, hkpos, hveq, hdw, hdotnv, hdp,
    Nivat.ColleReg.det_ne_zero_of_dot hvprim.ne_zero hdotnv hdp, hmem, hmem'⟩

/-! ## The whole `ℓ_J`-edge block

`FaceData` (`FaceData.lean`) turns `(n, v)` with `n ≠ 0`, `v` primitive, `dot n v = 0` into the
lexicographic endpoints `a`, `a'` and the run length `r`.  Combined with the construction above
this produces every `ChainDataGeom` field that mentions only `S`, `n_J`, `v_J`, `a`, `a'`, `r`. -/

/-- `0 < r`: the `-n_J`-face of `S_φ` is an edge, so `edge` (`ChainGeom.lean:89-90`) must have a
nonempty run.  A second face point `c ≠ a` cannot satisfy `1 ≤ dot n (c - a)` (it sits at `a`'s
own `n`-level, `a` being in `S`), so `edge`'s first branch fires with `1 ≤ j ≤ r`. -/
theorem r_pos_of_mem_E {S : Finset (ℤ × ℤ)} {n v a : ℤ × ℤ} {r : ℕ}
    (ha : a ∈ S) (hmem : -n ∈ E (↑S : Set (ℤ × ℤ)))
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a + (j : ℤ) • v) ∨ 1 ≤ dot n (b - a)) :
    0 < r := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hmem.2
  have hpick : ∃ c ∈ face (↑S : Set (ℤ × ℤ)) (-n), c ≠ a := by
    rcases eq_or_ne x a with rfl | hxa
    · exact ⟨y, hy, Ne.symm hxy⟩
    · exact ⟨x, hx, hxa⟩
  obtain ⟨c, hc, hca⟩ := hpick
  have hcS : c ∈ S.erase a := Finset.mem_erase.mpr ⟨hca, hc.1⟩
  have hle : dot (-n) a ≤ dot (-n) c := hc.2 a ha
  have hle' : dot n c ≤ dot n a := by
    simp only [dot_neg_left] at hle; omega
  rcases hedge c hcS with ⟨j, hj1, hjr, -⟩ | hpos
  · omega
  · rw [dot_sub] at hpos; omega

/-- **The `ℓ_J`-edge block of `ChainDataGeom`, constructed.**

Everything a producer of `exists_chainData` (`RegionSteps.lean:822`) needs about the pair
`(n_J, v_J)` and the face it exposes, from `p ≠ 0` and `d.Sphi.Nonempty` alone. -/
theorem DecompData.exists_edge_block [AddCommMonoid α] {η : Config α} (d : DecompData η)
    (hSne : d.Sphi.Nonempty) {p : ℤ × ℤ} (hp : p ≠ 0) :
    ∃ (n v a a' : ℤ × ℤ) (r : ℕ) (i : Fin d.m),
      Primitive n ∧ Primitive v ∧ v ≠ 0 ∧
      dot n v = 0 ∧ dot n (d.h i) = 0 ∧ dot n p ≠ 0 ∧ det p v ≠ 0 ∧
      n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧
      a ∈ d.Sphi ∧ a' ∈ d.Sphi ∧
      (∀ b ∈ d.Sphi.erase a,
        dot (-n) b < dot (-n) a ∨ (dot (-n) b = dot (-n) a ∧ dot (-v) b < dot (-v) a)) ∧
      (∀ b ∈ d.Sphi.erase a',
        dot (-n) b < dot (-n) a' ∨ (dot (-n) b = dot (-n) a' ∧ dot v b < dot v a')) ∧
      (∀ b ∈ d.Sphi.erase a,
        (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a + (j : ℤ) • v) ∨ 1 ≤ dot n (b - a)) ∧
      (∀ b ∈ d.Sphi.erase a',
        (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a' - (j : ℤ) • v) ∨ 1 ≤ dot n (b - a')) ∧
      a' = a + (r : ℤ) • v ∧ 0 < r ∧ a ≠ a' := by
  obtain ⟨n, v, i, k, hprim, hvprim, hkpos, hveq, hdw, hdotnv, hdp, hdetpv, hmem, hmem'⟩ :=
    d.exists_nJ_vJ hp
  have hnne : n ≠ 0 := hprim.ne_zero
  have hvne : v ≠ 0 := hvprim.ne_zero
  obtain ⟨a, ha, hlex⟩ := exists_lex_max d.Sphi hSne hnne hvne hdotnv
  obtain ⟨a', ha', hlex'⟩ := exists_lex_max' d.Sphi hSne hnne hvne hdotnv
  obtain ⟨r, hr_eq, hedge⟩ := exists_r_edge hnne ha ha' hvprim hdotnv hlex hlex'
  have hedge' := exists_edge' hdotnv hr_eq hedge
  have hrpos : 0 < r := r_pos_of_mem_E ha hmem' hedge
  have hane : a ≠ a' := by
    intro h
    have hrne : (r : ℤ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have h2 : a = a + (r : ℤ) • v := h.trans hr_eq
    have h3 : a + (0 : ℤ × ℤ) = a + (r : ℤ) • v := by rw [add_zero]; exact h2
    exact zsmul_ne_zero_of_ne_zero hrne hvne (add_left_cancel h3).symm
  exact ⟨n, v, a, a', r, i, hprim, hvprim, hvne, hdotnv, hdw, hdp, hdetpv, hmem, hmem',
    ha, ha', hlex, hlex', hedge, hedge', hr_eq, hrpos, hane⟩

/-! ## Wiring three orphans into one chain

Everything in this section is **assembly only** — no new mathematics.  The three pieces were
each already proved and each had zero consumers outside its own file:

```
EdgeNormals.lean:68   exists_edge_normal_nonparallel_to   ℓ ∈ E → ∃ n' ∈ E, det ℓ n' ≠ 0
        ↓  seam: Sphi_eq → Conv_supp_prod_eq_Conv_zonoF → E_congr_of_Conv_eq   (E_Sphi_eq_zonoF)
FaceData.lean:36      exists_unique_orthogonal_generator  n ∈ E → ∃! i, dot n (h i) = 0
        ↓
FaceDistinct.lean:125 a_ne_a'_iff_negNJ_mem_E             a ≠ a' ↔ -n_J ∈ E
        +  DecompData.lean:417  Sphi_negSymm              n ∈ E ↔ -n ∈ E   (the sign is free)
```

The seam is the only thing that had to be written, and it is the three-line template already
inlined in `Sphi_negSymm`'s own proof — recompiled here rather than cited, since `Sphi_negSymm`
states `n ↔ -n`, not the transport.

Note the two routes to `n_J` in this file are *independent* and neither subsumes the other:

* `exists_nJ` above asks only `p ≠ 0` and returns `dot n_J p ≠ 0` (`ChainGeom.lean`,
  field `dot_nJ_p`);
* `exists_nJ_of_edge` below asks `ℓ ∈ E ↑d.Sphi` and returns `det ℓ n_J ≠ 0`, which is the
  paper's "`ℓ_J` not parallel to `ℓ_ι`" (`b3_colle2.txt:890`).

⚠ This chain travels through `E` (the set of edge *normals*) only.  It never touches the
pointwise structure of `face`, which is what `FaceData.lean`'s Step C records as **BLOCKED**
(vertex-level face of `zonoF` vs lattice-point face of `d.Sphi`; `Conv d.Sphi = Conv (zonoF …)`
is an equality of hulls, not of sets).  `E_congr_of_Conv_eq` needs only the hull equality, which
is why the seam below is legitimate and Step C is not on this path. -/

open scoped Pointwise

/-- **The seam: `E ↑d.Sphi` is the edge set of the zonotope `zonoF univ d.h`.**

`Sphi_eq` (`DecompData.lean:108`) → `Conv_supp_prod_eq_Conv_zonoF` (`NewtonZonotope.lean:181`)
→ `E_congr_of_Conv_eq` (`ConvTransport.lean:233`).  This is the transport that
`Sphi_negSymm` (`DecompData.lean:417`) and `mem_E_Sphi_of_dot_eq_zero` (`FaceDistinct.lean:146`)
each inline; stated once so the two orphan consumers can be reached. -/
theorem DecompData.E_Sphi_eq_zonoF [AddCommMonoid α] {η : Config α} (d : DecompData η) :
    E (↑d.Sphi : Set (ℤ × ℤ)) = E (↑(zonoF Finset.univ d.h) : Set (ℤ × ℤ)) := by
  have hconv : Conv d.Sphi = Conv (zonoF Finset.univ d.h) := by
    rw [d.Sphi_eq, Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun i _ => d.h_ne i)]
  exact E_congr_of_Conv_eq hconv

/-- The `∑ segOf` shape of the seam, which is what `EdgeNormals.lean:68` is stated in.
`coe_zonoF` (`NewtonZonotope.lean:137`) is the only extra step. -/
theorem DecompData.E_Sphi_eq [AddCommMonoid α] {η : Config α} (d : DecompData η) :
    E (↑d.Sphi : Set (ℤ × ℤ)) = E (∑ i ∈ Finset.univ, segOf (d.h i)) := by
  rw [d.E_Sphi_eq_zonoF, coe_zonoF]

/-- **The converse of `mem_E_Sphi_of_dot_eq_zero`** (`FaceDistinct.lean:146`), and it comes out
`∃!` rather than `∃`: this is `exists_unique_orthogonal_generator` (`FaceData.lean:36`) read
through the seam.  `h_ne` and `h_dir` are its hypotheses; both are `DecompData` fields.

This is what lets an `n_J` obtained from `EdgeNormals.lean:68` — which knows only that it is
*some* member of `E ↑d.Sphi` — hand back the index `i` that
`ChainDataGeom.a_ne_a'_of_dot_h_eq_zero` (`FaceDistinct.lean:174`) consumes. -/
theorem DecompData.existsUnique_index_dot_eq_zero [AddCommMonoid α] {η : Config α}
    (d : DecompData η) {n : ℤ × ℤ} (hn : n ∈ E (↑d.Sphi : Set (ℤ × ℤ))) :
    ∃! i : Fin d.m, dot n (d.h i) = 0 :=
  exists_unique_orthogonal_generator d.h_ne d.h_dir (d.E_Sphi_eq_zonoF ▸ hn)

/-- **Membership in `E ↑d.Sphi`, characterised.**  Forward is
`existsUnique_index_dot_eq_zero`; backward is `mem_E_Sphi_of_dot_eq_zero`
(`FaceDistinct.lean:146`).  `Prim n` is `hn.1` — `E R = {n | Prim n ∧ (face R n).Nontrivial}`
(`IsEdge`, `LatticeEdges.lean:214`) — so it costs nothing. -/
theorem DecompData.mem_E_Sphi_iff [AddCommMonoid α] {η : Config α} (d : DecompData η)
    (n : ℤ × ℤ) :
    n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ↔ Prim n ∧ ∃ i : Fin d.m, dot n (d.h i) = 0 := by
  constructor
  · exact fun hn => ⟨hn.1, (d.existsUnique_index_dot_eq_zero hn).exists⟩
  · rintro ⟨hprim, i, hdot⟩
    exact d.mem_E_Sphi_of_dot_eq_zero hprim i hdot

/-- **`EdgeNormals.lean:68` on a `DecompData`.**  Given an edge normal `ℓ` of `S_φ`, there is a
second edge normal non-parallel to it.  Pure adaptation: the three hypotheses are the fields
`hm` (`DecompData.lean:88`), `h_ne` (`:98`), `h_dir` (`:104`), and the shape change
`E ↑d.Sphi ↦ E (∑ segOf (h i))` is `E_Sphi_eq`. -/
theorem DecompData.exists_edge_normal_nonparallel [AddCommMonoid α] {η : Config α}
    (d : DecompData η) {ℓ : ℤ × ℤ} (hℓ : ℓ ∈ E (↑d.Sphi : Set (ℤ × ℤ))) :
    ∃ n' : ℤ × ℤ, n' ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ det ℓ n' ≠ 0 := by
  rw [d.E_Sphi_eq] at hℓ ⊢
  exact Nivat.LE2.exists_edge_normal_nonparallel_to d.hm d.h_ne d.h_dir hℓ

/-- **`n_J` from `ℓ_ι`, with its unique index recovered.**  The `b3_colle2.txt:890` form: `ℓ` is
the already-fixed `ℓ_ι`, `n` is `n_J`, `det ℓ n ≠ 0` is "`ℓ_J` is not parallel to `ℓ_ι`", and
`i` is the generator `n_J` is orthogonal to — exactly what `exists_chainData`'s producer owes
(`OPEN.md` #7).

The antipodal membership costs nothing (`Sphi_negSymm`, `DecompData.lean:417`), and `Prim n` is
the first component of edge membership. -/
theorem DecompData.exists_nJ_of_edge [AddCommMonoid α] {η : Config α} (d : DecompData η)
    {ℓ : ℤ × ℤ} (hℓ : ℓ ∈ E (↑d.Sphi : Set (ℤ × ℤ))) :
    ∃ n : ℤ × ℤ, Prim n ∧ det ℓ n ≠ 0 ∧
      n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧
      ∃! i : Fin d.m, dot n (d.h i) = 0 := by
  obtain ⟨n, hmem, hdet⟩ := d.exists_edge_normal_nonparallel hℓ
  exact ⟨n, hmem.1, hdet, hmem, (Sphi_negSymm d n).mp hmem,
    d.existsUnique_index_dot_eq_zero hmem⟩

/-! ### The `a ≠ a'` end of the chain

`Sphi_negSymm` (`DecompData.lean:417`) holds for *any* `DecompData` using only `h_ne`, so the
antipode in `a_ne_a'_iff_negNJ_mem_E` (`FaceDistinct.lean:125`) is free and the obligation can be
restated on `n_J` itself. -/

/-- **`a ≠ a'` ⟺ `n_J` is an edge normal of `S_φ`** — the antipode of
`a_ne_a'_iff_negNJ_mem_E` (`FaceDistinct.lean:125`), with the sign supplied by `Sphi_negSymm`. -/
theorem ChainDataGeom.a_ne_a'_iff_nJ_mem_E [AddCommMonoid α] {η xper : Config α}
    {vl p gen : ℤ × ℤ} (d : DecompData η)
    (cg : ChainDataGeom η xper vl p d.Sphi gen) :
    cg.a ≠ cg.a' ↔ cg.nJ ∈ E (↑d.Sphi : Set (ℤ × ℤ)) :=
  cg.a_ne_a'_iff_negNJ_mem_E.trans (Sphi_negSymm d cg.nJ).symm

/-- **`a ≠ a'` is exactly "`n_J` is orthogonal to some decomposition period".**

`FaceDistinct.lean` proved `←` (`a_ne_a'_of_dot_h_eq_zero`, `:174`) and left `→` open.  With
`FaceData.lean:36` reached through the seam both directions hold, so the `OPEN.md` #7 obligation
is not merely *sufficient* for `a ≠ a'` — it is equivalent to it, and cannot be weakened.  The
index is moreover unique. -/
theorem ChainDataGeom.a_ne_a'_iff_exists_dot_h_eq_zero [AddCommMonoid α] {η xper : Config α}
    {vl p gen : ℤ × ℤ} (d : DecompData η)
    (cg : ChainDataGeom η xper vl p d.Sphi gen) :
    cg.a ≠ cg.a' ↔ ∃! i : Fin d.m, dot cg.nJ (d.h i) = 0 := by
  rw [ChainDataGeom.a_ne_a'_iff_nJ_mem_E d cg]
  constructor
  · exact d.existsUnique_index_dot_eq_zero
  · rintro ⟨i, hi, -⟩
    exact ChainDataGeom.nJ_mem_E_Sphi_of_dot_h_eq_zero d cg i hi

/-! ## The two routes composed

`exists_nJ` (transversality to `p`) and `exists_nJ_of_edge` (non-parallelism to `ℓ_ι`) both
produce an `n_J`, but *different* ones, and a producer of `exists_chainData` needs one vector
satisfying both.  They compose **only at an index that avoids two degeneracies at once**, and
`not_exists_nJ_full_of_m_eq_two` below shows that is a real restriction, not a proof artefact.

The index criterion.  Writing `n_i` for the primitive normal of `d.h i`:

* `dot n_i p = 0` ⟺ `det p (d.h i) = 0` (`p` is parallel to the generator);
* `det ℓ n_i = 0` ⟺ `dot ℓ (d.h i) = 0` (`ℓ` is orthogonal to the generator).

`h_dir` (`DecompData.lean:104`) makes the generators pairwise non-parallel, so each degeneracy
can strike **at most one** index — hence `3 ≤ d.m` always leaves a good one.  At `d.m = 2` the
two bad indices can be distinct and exhaust the range, and then no `n` works at all: that is
`not_exists_nJ_full_of_m_eq_two`.  ⚠ `DecompData.hm` only gives `2 ≤ m`, so `exists_nJ_full`
carries `3 ≤ d.m` as a genuine extra hypothesis; the `d.m = 2` case has to be routed through
`exists_nJ_full_of_index` with the index supplied by the caller. -/

/-- **The normal transverse to `p` and non-parallel to `ℓ`.**  Strengthens
`exists_prim_dot_zero_dot_ne_zero` by the second conclusion; the extra input `dot ℓ w ≠ 0` is
what rules out `ℓ ∥ n`.  `dot_eq_zero_of_det_eq_zero` is `LatticeEdges.lean:1702`. -/
theorem exists_prim_dot_zero_dot_ne_zero_det_ne_zero {w p ℓ : ℤ × ℤ} (hw : w ≠ 0)
    (hdp : det p w ≠ 0) (hdℓ : dot ℓ w ≠ 0) :
    ∃ n : ℤ × ℤ, Primitive n ∧ dot n w = 0 ∧ dot n p ≠ 0 ∧ det ℓ n ≠ 0 := by
  obtain ⟨n, hprim, hnw, hnp⟩ := exists_prim_dot_zero_dot_ne_zero hw hdp
  refine ⟨n, hprim, hnw, hnp, fun hℓn => hdℓ ?_⟩
  exact dot_eq_zero_of_det_eq_zero hprim.ne_zero hℓn hnw

/-- **An index avoiding both degeneracies, from `3 ≤ m`.**  Each degeneracy hits at most one
index by `h_dir`, so three indices cannot all be bad.  `hm : 2 ≤ m` (`DecompData.lean:88`) is
**not** enough — see `not_exists_nJ_full_of_m_eq_two`. -/
theorem DecompData.exists_index_det_ne_zero_dot_ne_zero [AddCommMonoid α] {η : Config α}
    (d : DecompData η) (hm3 : 3 ≤ d.m) {p ℓ : ℤ × ℤ} (hp : p ≠ 0) (hℓ : ℓ ≠ 0) :
    ∃ i : Fin d.m, det p (d.h i) ≠ 0 ∧ dot ℓ (d.h i) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have keyA : ∀ i j : Fin d.m, i ≠ j → det p (d.h i) = 0 → det p (d.h j) = 0 → False :=
    fun i j hij hi hj => d.h_dir i j hij (det_eq_zero_of_det_eq_zero hp hi hj)
  have keyB : ∀ i j : Fin d.m, i ≠ j → dot ℓ (d.h i) = 0 → dot ℓ (d.h j) = 0 → False :=
    fun i j hij hi hj => d.h_dir i j hij (det_eq_zero_of_dot_eq_zero hℓ hi hj)
  set i0 : Fin d.m := ⟨0, by omega⟩ with hi0
  set i1 : Fin d.m := ⟨1, by omega⟩ with hi1
  set i2 : Fin d.m := ⟨2, by omega⟩ with hi2
  have n01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have n02 : i0 ≠ i2 := by simp [hi0, hi2, Fin.ext_iff]
  have n12 : i1 ≠ i2 := by simp [hi1, hi2, Fin.ext_iff]
  have c0 := hcon i0
  have c1 := hcon i1
  have c2 := hcon i2
  by_cases h0 : det p (d.h i0) = 0
  · by_cases h1 : det p (d.h i1) = 0
    · exact keyA _ _ n01 h0 h1
    · by_cases h2 : det p (d.h i2) = 0
      · exact keyA _ _ n02 h0 h2
      · exact keyB _ _ n12 (c1 h1) (c2 h2)
  · by_cases h1 : det p (d.h i1) = 0
    · by_cases h2 : det p (d.h i2) = 0
      · exact keyA _ _ n12 h1 h2
      · exact keyB _ _ n02 (c0 h0) (c2 h2)
    · exact keyB _ _ n01 (c0 h0) (c1 h1)

/-- **`exists_nJ` and `exists_nJ_of_edge` composed, at a caller-chosen index.**

The conclusion carries every `n_J`-only obligation of `ChainDataGeom` at once: `Primitive n` is
`nJ_prim` (`ChainGeom.lean`, all three fields cited here by name), `dot n p ≠ 0` is `dot_nJ_p`,
`dot n (d.h i) = 0` feeds `dot_nJ_vJ` through `exists_nJ_vJ`'s primitive part, `det ℓ n ≠ 0` is
the paper's non-parallelism at `b3_colle2.txt:890`, and the two `E ↑d.Sphi` memberships are what
`a_ne_a'_iff_nJ_mem_E` consumes.

§85: the `ChainGeom.lean` line numbers this file used to carry — `:111` for `dot_nJ_p` (actual
`:142`), `:157` for `nJ_prim` (actual `:194`), `:95` for `dot_nJ_vJ` (actual `:96`) — were all
measured rotten 2026-09-24 and replaced by field names.  The `:157` case is the instructive one:
it landed *inside `vJ_prim`'s docstring*, which reads entirely self-consistently, so the citation
was wrong without looking wrong. -/
theorem DecompData.exists_nJ_full_of_index [AddCommMonoid α] {η : Config α} (d : DecompData η)
    {p ℓ : ℤ × ℤ} {i : Fin d.m} (hdp : det p (d.h i) ≠ 0) (hdℓ : dot ℓ (d.h i) ≠ 0) :
    ∃ n : ℤ × ℤ, Primitive n ∧ dot n (d.h i) = 0 ∧ dot n p ≠ 0 ∧ det ℓ n ≠ 0 ∧
      n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) := by
  obtain ⟨n, hprim, hnw, hnp, hℓn⟩ :=
    exists_prim_dot_zero_dot_ne_zero_det_ne_zero (d.h_ne i) hdp hdℓ
  exact ⟨n, hprim, hnw, hnp, hℓn,
    d.mem_E_Sphi_of_dot_eq_zero (prim_iff_primitive.mpr hprim) i hnw,
    d.neg_mem_E_Sphi_of_dot_eq_zero (prim_iff_primitive.mpr hprim) i hnw⟩

/-- **The composition, with the index found rather than supplied.**  Needs `3 ≤ d.m`. -/
theorem DecompData.exists_nJ_full [AddCommMonoid α] {η : Config α} (d : DecompData η)
    (hm3 : 3 ≤ d.m) {p ℓ : ℤ × ℤ} (hp : p ≠ 0) (hℓ : ℓ ≠ 0) :
    ∃ (n : ℤ × ℤ) (i : Fin d.m), Primitive n ∧ dot n (d.h i) = 0 ∧ dot n p ≠ 0 ∧
      det ℓ n ≠ 0 ∧ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) := by
  obtain ⟨i, hdp, hdℓ⟩ := d.exists_index_det_ne_zero_dot_ne_zero hm3 hp hℓ
  obtain ⟨n, h1, h2, h3, h4, h5, h6⟩ := d.exists_nJ_full_of_index hdp hdℓ
  exact ⟨n, i, h1, h2, h3, h4, h5, h6⟩

/-- **The composition genuinely fails at `d.m = 2`.**

If one generator is parallel to `p` and a *different* one is orthogonal to `ℓ`, then with only
two generators there is no edge normal of `S_φ` that is both transverse to `p` and
non-parallel to `ℓ`.  The proof is `mem_E_Sphi_iff`: edge membership pins `n` to one of the two
generators' normals, and each choice is killed by one of the two hypotheses.

⚠ Both hypotheses are satisfiable together at `d.m = 2`, so this is not vacuous — and note the
second one is exactly what `ℓ ∈ E ↑d.Sphi` *gives* (`existsUnique_index_dot_eq_zero`).  So the
failure mode is reachable from the intended call site, and `3 ≤ d.m` in `exists_nJ_full` cannot
be dropped. -/
theorem DecompData.not_exists_nJ_full_of_m_eq_two [AddCommMonoid α] {η : Config α}
    (d : DecompData η) (hm2 : d.m = 2) {p ℓ : ℤ × ℤ} {i j : Fin d.m} (hij : i ≠ j)
    (hdp : det p (d.h i) = 0) (hdℓ : dot ℓ (d.h j) = 0) :
    ¬ ∃ n : ℤ × ℤ, n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ dot n p ≠ 0 ∧ det ℓ n ≠ 0 := by
  rintro ⟨n, hmem, hnp, hℓn⟩
  obtain ⟨k, hkdot⟩ := ((d.mem_E_Sphi_iff n).mp hmem).2
  have hcases : k = i ∨ k = j := by
    have hi2 : (i : ℕ) < 2 := by rw [← hm2]; exact i.isLt
    have hj2 : (j : ℕ) < 2 := by rw [← hm2]; exact j.isLt
    have hk2 : (k : ℕ) < 2 := by rw [← hm2]; exact k.isLt
    have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    simp only [Fin.ext_iff]
    omega
  rcases hcases with hki | hkj
  · rw [hki] at hkdot
    refine hnp ?_
    rw [dot_comm]
    exact dot_eq_zero_of_det_eq_zero (d.h_ne i) hdp (by rw [dot_comm]; exact hkdot)
  · rw [hkj] at hkdot
    exact hℓn (det_eq_zero_of_dot_eq_zero (d.h_ne j) (by rw [dot_comm]; exact hdℓ)
      (by rw [dot_comm]; exact hkdot))

/-! ## End to end: from the `exists_chainData` binders to `n_J`

`Nivat.ONEDRational.mem_E_Sphi_and_neg_mem_E_Sphi_of_biONED` (`ONEDRational.lean:201`) is the
producer of `ℓ ∈ E ↑d.Sphi` that `exists_nJ_of_edge` was missing.  It consumes exactly the three
binders `hℓ_nel` / `hℓ_pos` / `hℓ_neg` that `exists_chainData` already has in scope
(`RegionSteps.lean:812-814`) — no `IsMinimalCounterexample`, no rationality detour — so the
chain below adds **no** hypothesis beyond `p ≠ 0` and `3 ≤ d.m`.

`DecompDataZ` (`DecompData.lean:154`) extends `DecompData`, so the `DecompData` lemmas apply to
it by parent projection; no bridge is needed. -/

/-- **The merge, toward the edge version.**  `ℓ ≠ 0` is the `Prim` component of edge
membership, so `exists_nJ_full` applies with nothing extra to prove. -/
theorem DecompData.exists_nJ_full_of_edge [AddCommMonoid α] {η : Config α} (d : DecompData η)
    (hm3 : 3 ≤ d.m) {p ℓ : ℤ × ℤ} (hp : p ≠ 0) (hℓ : ℓ ∈ E (↑d.Sphi : Set (ℤ × ℤ))) :
    ∃ (n : ℤ × ℤ) (i : Fin d.m), Primitive n ∧ dot n (d.h i) = 0 ∧ dot n p ≠ 0 ∧
      det ℓ n ≠ 0 ∧ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) :=
  d.exists_nJ_full hm3 hp hℓ.1.ne_zero

/-- **`exists_nJ_of_edge` reached from the `exists_chainData` binder list.**  The `ℓ ∈ E ↑d.Sphi`
side condition is discharged by `ONEDRational.mem_E_Sphi_and_neg_mem_E_Sphi_of_biONED`. -/
theorem DecompDataZ.exists_nJ_of_biONED {ξ : Config ℤ} (d : DecompDataZ ξ) {ℓ : ℤ × ℤ}
    (hℓ_nel : ℓ ∈ Nivat.Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Nivat.Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Nivat.Colle45.IsOneSidedNonexpansive ξ (-ℓ)) :
    ∃ n : ℤ × ℤ, Prim n ∧ det ℓ n ≠ 0 ∧
      n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧
      ∃! i : Fin d.m, dot n (d.h i) = 0 :=
  d.exists_nJ_of_edge
    (Nivat.ONEDRational.mem_E_Sphi_and_neg_mem_E_Sphi_of_biONED d hℓ_nel hℓ_pos hℓ_neg).1

/-- **The whole chain in one statement**: from `exists_chainData`'s own binders plus `p ≠ 0` and
`3 ≤ d.m`, an `n_J` satisfying every `n_J`-only obligation of `ChainDataGeom` simultaneously —
`nJ_prim`, `dot_nJ_p`, the generator orthogonality feeding `dot_nJ_vJ`, the paper's
non-parallelism `det ℓ n_J ≠ 0` (`b3_colle2.txt:890`), and both `E ↑d.Sphi` memberships.

⚠ `3 ≤ d.m` is not free: `DecompData.hm` gives only `2 ≤ m`, and
`not_exists_nJ_full_of_m_eq_two` shows the conclusion is *false* at `m = 2` when the generator
parallel to `p` and the generator orthogonal to `ℓ` are distinct.  At `m = 2` a caller must
supply the index itself and go through `exists_nJ_full_of_index`. -/
theorem DecompDataZ.exists_nJ_full_of_biONED {ξ : Config ℤ} (d : DecompDataZ ξ)
    (hm3 : 3 ≤ d.m) {p ℓ : ℤ × ℤ} (hp : p ≠ 0)
    (hℓ_nel : ℓ ∈ Nivat.Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Nivat.Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Nivat.Colle45.IsOneSidedNonexpansive ξ (-ℓ)) :
    ∃ (n : ℤ × ℤ) (i : Fin d.m), Primitive n ∧ dot n (d.h i) = 0 ∧ dot n p ≠ 0 ∧
      det ℓ n ≠ 0 ∧ n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) :=
  d.exists_nJ_full_of_edge hm3 hp
    (Nivat.ONEDRational.mem_E_Sphi_and_neg_mem_E_Sphi_of_biONED d hℓ_nel hℓ_pos hℓ_neg).1

/-! ## Tier 2: the face block of `ChainDataGeom`, as a structure

`exists_edge_block` above already produces, in one existential, every `ChainDataGeom` field
that mentions only `S_φ`, `n_J`, `v_J`, `a`, `a'`, `r`.  Consuming a 23-conjunct existential
at a construction site is not workable, so this section does the mechanical move of
`CLAUDE.md` rule 4 (「拆而后落」): the eleven components that are *literally fields of*
`ChainDataGeom` become named fields of a `structure`, and the remaining components stay in the
existential of the producer, where they belong (they are facts about `n_J, v_J, p` and the run
length, not fields of the bundle).

Two receipts keep the shapes honest, both checked by the kernel rather than by reading:

* `FaceBlock.ofChainDataGeom` is a **pure projection** — `⟨cg.a, …, cg.dot_nJ_vJ⟩` with no
  proof steps.  It elaborates only if each field of `FaceBlock` is the *same proposition* as
  the `ChainDataGeom` field of that name, so any future edit to `ChainGeom.lean:82-96` breaks
  the build here instead of silently drifting.
* `FaceBlock.gen` feeds the block to the one existing consumer of these four fields,
  `ChainDataWithShell.gen` (`ChainShell.lean:110`), with **no adapter**: the eight loose
  hypotheses `hS ha ha' hlex hlex' hedge hedge' hdn` are exactly eight field projections.

**`d.Sphi.Nonempty` is free.**  `exists_edge_block` takes it as a hypothesis; for the
`DecompDataZ` that leaf A actually holds it is already proved — `DecompDataZ.Sphi_nonempty`
(`DecompData.lean:180`), derived from `φ ≠ 0` rather than assumed.  So
`DecompDataZ.exists_faceBlock` below has `p ≠ 0` as its only hypothesis. -/

/-- **The face block of `ChainDataGeom`** (`ChainGeom.lean:69-96`): the endpoints `a`, `a'` of
the `ℓ_J`-parallel face of `S`, its run length `r`, and the eight obligations that mention
nothing else.  Field names are copied from `ChainDataGeom`; see `FaceBlock.ofChainDataGeom`
for the kernel check that the *types* agree too. -/
structure FaceBlock (S : Finset (ℤ × ℤ)) (n v : ℤ × ℤ) where
  /-- The `v`-minimal endpoint of the face. -/
  a : ℤ × ℤ
  /-- The `v`-maximal endpoint of the face. -/
  a' : ℤ × ℤ
  /-- The face has `r + 1` lattice points `a, a + v, …, a + r • v = a'`. -/
  r : ℕ
  /-- `ChainDataGeom.latticeConvex_S`. -/
  latticeConvex_S : LatticeConvex S
  /-- `ChainDataGeom.a_mem`. -/
  a_mem : a ∈ S
  /-- `ChainDataGeom.a'_mem`. -/
  a'_mem : a' ∈ S
  /-- `ChainDataGeom.lex`. -/
  lex : ∀ b ∈ S.erase a,
    dot (-n) b < dot (-n) a ∨ (dot (-n) b = dot (-n) a ∧ dot (-v) b < dot (-v) a)
  /-- `ChainDataGeom.lex'`. -/
  lex' : ∀ b ∈ S.erase a',
    dot (-n) b < dot (-n) a' ∨ (dot (-n) b = dot (-n) a' ∧ dot v b < dot v a')
  /-- `ChainDataGeom.edge`. -/
  edge : ∀ b ∈ S.erase a,
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a + (j : ℤ) • v) ∨ 1 ≤ dot n (b - a)
  /-- `ChainDataGeom.edge'`. -/
  edge' : ∀ b ∈ S.erase a',
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a' - (j : ℤ) • v) ∨ 1 ≤ dot n (b - a')
  /-- `ChainDataGeom.dot_nJ_vJ`. -/
  dot_nJ_vJ : dot n v = 0

/-- **Shape receipt, checked by the kernel.**  Every component below is a bare projection of
the `ChainDataGeom` field of the same name, so this definition elaborates only while the two
sets of types agree verbatim.  It is also the honest statement of what `FaceBlock` *is*: no
more than a `ChainDataGeom` knows about its own face. -/
def FaceBlock.ofChainDataGeom {η xper : Config α} {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (cg : ChainDataGeom η xper vl p S gen) : FaceBlock S cg.nJ cg.vJ :=
  ⟨cg.a, cg.a', cg.r, cg.latticeConvex_S, cg.a_mem, cg.a'_mem,
    cg.lex, cg.lex', cg.edge, cg.edge', cg.dot_nJ_vJ⟩

/-- **The face block of `S_φ`, from `p ≠ 0` alone.**

`exists_edge_block` with its `d.Sphi.Nonempty` hypothesis discharged by
`DecompDataZ.Sphi_nonempty` (`DecompData.lean:180`), and its face half packaged as a
`FaceBlock`.  The components left in the existential are the ones that are *not*
`ChainDataGeom` fields: the run identity `a' = a + r • v` and `0 < r` (consumed by
`FaceDistinct.lean`'s `a ≠ a'` route), and the facts about `n`, `v`, `p` themselves, which the
producer of `ChainDataGeom` needs in order to know *which* normal and direction it is choosing
(`dot n (d.h i) = 0` is what `a_ne_a'_iff_exists_dot_h_eq_zero` above consumes).

⚠ No cardinality hypothesis: this is the `2 ≤ m` route.  The strengthened package carrying
`det ℓ n ≠ 0` (`exists_nJ_full`) is the one that needs `3 ≤ d.m`, and `ℓ` is not a parameter of
`ChainDataGeom` at all. -/
theorem DecompDataZ.exists_faceBlock {ξ : Config ℤ} (d : DecompDataZ ξ) {p : ℤ × ℤ}
    (hp : p ≠ 0) :
    ∃ (n v : ℤ × ℤ) (i : Fin d.m) (F : FaceBlock d.Sphi n v),
      Primitive n ∧ Primitive v ∧ v ≠ 0 ∧ dot n (d.h i) = 0 ∧ dot n p ≠ 0 ∧ det p v ≠ 0 ∧
      n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧ -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ∧
      F.a' = F.a + (F.r : ℤ) • v ∧ 0 < F.r ∧ F.a ≠ F.a' := by
  obtain ⟨n, v, a, a', r, i, hprim, hvprim, hvne, hdotnv, hdw, hdp, hdetpv, hmem, hmem',
    ha, ha', hlex, hlex', hedge, hedge', hr_eq, hrpos, hane⟩ :=
    d.toDecompData.exists_edge_block d.Sphi_nonempty hp
  exact ⟨n, v, i,
    ⟨a, a', r, d.Sphi_conv, ha, ha', hlex, hlex', hedge, hedge', hdotnv⟩,
    hprim, hvprim, hvne, hdw, hdp, hdetpv, hmem, hmem', hr_eq, hrpos, hane⟩

section Gen

open Nivat.MaxEnv Nivat.Colle Nivat.Colle37

/-- **Consumer receipt: the block plugs into the sweep with no adapter.**

`ChainDataWithShell.gen` (`ChainShell.lean:110`) is the only consumer of `lex`, `lex'`, `edge`,
`edge'` in the tree, and it takes them as eight loose hypotheses.  Here all eight are field
projections of a single `FaceBlock`, so a producer that has built one has nothing left to prove
about the face; what remains (`hdz`, `hline`, `hstab`, `hsplit`) is the `bottom` field
of `ChainDataGeom` (`ChainGeom.lean`), which is about `Â_∞`, not about `S_φ`.  (The mirror
hypothesis `hstab'` at `a'` was deleted 2026-09-19 together with `bottom`'s conjunct (iv);
`gen_of_shell` derives it, `ShellGeom.lean`.) -/
theorem FaceBlock.gen {η xper : Config α} {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (cd : ChainDataWithShell η xper vl S gen) {vJ z₀ : ℤ × ℤ} {L : ℤ}
    (F : FaceBlock S cd.nJ vJ) (ε : ℕ)
    (hdz : dot cd.nJ z₀ = cd.cJ - (ε : ℤ) - 1)
    (hline : ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet (⋃ i, cd.toChainData.Ahat i) cd.vJ1)
    (hstab : ∀ b ∈ S, 1 ≤ dot cd.nJ (b - F.a) → ∀ k : ℤ, L ≤ k →
      z₀ + k • vJ + (b - F.a) ∈ reachSet (⋃ i, cd.toChainData.Ahat i) cd.vJ1)
    (hsplit : ∀ z ∈ cd.toChainData.shellInf (ε + 1),
      z ∈ cd.toChainData.shellInf ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ) :
    ∃ i M : ℕ, ∀ t : ℕ, M ≤ t → ∀ z ∈ cd.toChainData.shellInf (ε + 1),
      GenClosure S (cd.toChainData.shellInf ε ∪
        (cd.toChainData.shellInf (ε + 1) ∩ winS i ((t : ℤ) • vJ))) z :=
  cd.gen ε F.latticeConvex_S F.a_mem F.a'_mem F.lex F.lex' F.edge F.edge' F.dot_nJ_vJ
    hdz hline hstab hsplit

end Gen

/-! ## The sign of the sweep, and what is left of `bottom`

`vJ1` (Collé's `v_{ℓ_{J-1}}`, the direction the shell is swept along, `ChainShell.lean:52`) and
`vJ` (`v_{ℓ_J}`, the direction of the region's second semi-infinite edge, `ChainGeom.lean:69`)
are directions of *different* lines, and the bundle relates them only through `nJ`:
`dot_nJ_vJ = 0` is a field, while the sign of `dot nJ vJ1` was recorded nowhere.  It does not
need to be recorded: **it is forced**, see `ChainDataGeom.dot_nJ_vJ1_neg`.  That closes the
question without adding a field to `ChainDataGeom` — the obligation count of leaf A is
unchanged by this section.

Why the sign matters at all: `MaxEnv.shell` (`MaximalEnveloped.lean:564`) constrains the swept
points by `cJ - ε ≤ dot nJ ·`, and by `ahat_halfPlane` every point of `Â_∞` already satisfies
`cJ ≤ dot nJ ·`.  So if `dot nJ vJ1` were `≥ 0` the constraint would never bite, every layer
would equal `reachSet`, and the filtration `Â_∞^{(ε)}` would be constant.

The rest of the section reduces `bottom` (`ChainGeom.lean`) and then measures what is
left.  `bottom_of_seed` replaces its two `∀ k ≥ L` conjuncts — infinitely many memberships —
by the single slice at `k = L`, which is `1 + S.card` memberships; the upgrade is
`reachSet_add_zsmul_of_rec`, since `rec_vJ` makes `Â_∞` closed under `· + vJ` and `reachSet`
inherits that.  Its last conjunct is routed through `MaxEnv.mem_shell_succ_iff`
(`ShellLine.lean:54`, already proved: the layer increment is the single line
`dot nJ · = cJ - ε - 1`), so what a producer must supply there is a one-dimensional statement,
not a two-dimensional one.

**What remains is genuinely new input, not bookkeeping.**  `not_bottom_of_shell_data` exhibits
`A`, `nJ`, `vJ`, `vJ1`, `cJ` satisfying *every* hypothesis this section uses — `Â_∞` nonempty,
`ahat_halfPlane`, `rec_vJ`, `dot nJ vJ = 0`, and the now-forced `dot nJ vJ1 < 0` — for which
`bottom`'s first two conjuncts are already false: with `dot nJ vJ1 = -2` the swept levels skip
`cJ - 1` entirely.  So no sign convention can discharge `bottom`; the producer has to place
`Â_∞`. -/

section Bottom

open Nivat.MaxEnv

/-- **`reachSet` inherits the recession directions of the set it sweeps.**  If `A` is closed
under `· + w` then so is `reachSet A v`, for every non-negative integer multiple of `w`: the
translate is absorbed into the seed `g`, leaving the sweep parameter `t` untouched. -/
theorem reachSet_add_natCast_zsmul_of_rec {A : Set (ℤ × ℤ)} {v w z : ℤ × ℤ}
    (hrec : ∀ g ∈ A, g + w ∈ A) (hz : z ∈ reachSet A v) (m : ℕ) :
    z + (m : ℤ) • w ∈ reachSet A v := by
  obtain ⟨g, hg, t, rfl⟩ := hz
  have key : ∀ j : ℕ, g + (j : ℤ) • w ∈ A := by
    intro j
    induction j with
    | zero => simpa using hg
    | succ k ih =>
      have hstep : g + ((k + 1 : ℕ) : ℤ) • w = (g + ((k : ℕ) : ℤ) • w) + w := by
        push_cast; rw [add_smul, one_smul, add_assoc]
      rw [hstep]; exact hrec _ ih
  refine ⟨g + (m : ℤ) • w, key m, t, ?_⟩
  abel

/-- The `ℤ`-indexed form of `reachSet_add_natCast_zsmul_of_rec`. -/
theorem reachSet_add_zsmul_of_rec {A : Set (ℤ × ℤ)} {v w z : ℤ × ℤ}
    (hrec : ∀ g ∈ A, g + w ∈ A) (hz : z ∈ reachSet A v) {j : ℤ} (hj : 0 ≤ j) :
    z + j • w ∈ reachSet A v := by
  have := reachSet_add_natCast_zsmul_of_rec hrec hz j.toNat
  rwa [Int.toNat_of_nonneg hj] at this

/-- **The sweep direction points strictly out of the `ℓ_J` half-plane: `dot nJ vJ1 < 0`.**

Forced by the fields the bundle already has, so **no new field and no sign convention**.
`bottom 0` puts a point of `reachSet Â_∞ vJ1` at level `cJ - 1`; writing it as `g + t • vJ1`
with `cJ ≤ dot nJ g` (`ahat_halfPlane`) gives `t * dot nJ vJ1 ≤ -1`, and `t : ℕ` then rules out
`0 ≤ dot nJ vJ1`.  `dot_nJ_vJ` is what keeps the `k • vJ` displacement off the level.

Measured against the only complete inhabitant in the tree,
`Nivat.ColleStep.PeriodsRays2.cgw` (`Step_PeriodsRays2.lean:233`), where `nJ = (0, 1)` and
`vJ1 = (0, -1)`, so `dot nJ vJ1 = -1`: consistent, and now not a coincidence of that choice. -/
theorem ChainDataGeom.dot_nJ_vJ1_neg {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (cg : ChainDataGeom η xper vl p S gen) :
    dot cg.nJ cg.vJ1 < 0 := by
  obtain ⟨z₀, L, hdz, hline, -, -⟩ := cg.bottom 0
  obtain ⟨g, hg, t, heq⟩ := hline L le_rfl
  have hL : dot cg.nJ (z₀ + L • cg.vJ) = cg.cJ - 1 := by
    rw [dot_add, Nivat.ColleReg.dot_zsmul_right, cg.dot_nJ_vJ, hdz]
    push_cast; ring
  have hR : dot cg.nJ (g + (t : ℤ) • cg.vJ1)
      = dot cg.nJ g + (t : ℤ) * dot cg.nJ cg.vJ1 := by
    rw [dot_add, Nivat.ColleReg.dot_zsmul_right]
  have hkey : dot cg.nJ g + (t : ℤ) * dot cg.nJ cg.vJ1 = cg.cJ - 1 := by
    rw [← hR, ← heq, hL]
  have hgh : cg.cJ ≤ dot cg.nJ g := cg.ahat_halfPlane g hg
  by_contra hle
  push Not at hle
  have hprod : 0 ≤ (t : ℤ) * dot cg.nJ cg.vJ1 :=
    mul_nonneg (Int.natCast_nonneg t) hle
  linarith

/-- **`bottom` from a single slice.**

The two `∀ k ≥ L` conjuncts of `bottom` (`ChainGeom.lean`) are re-derived from their
`k = L` instances alone, using `rec_vJ` (passed as `hrec_vJ`) through
`reachSet_add_zsmul_of_rec`; the last conjunct is re-derived from the bottom row being a
half-line, using `MaxEnv.mem_shell_succ_iff` (`ShellLine.lean:54`) through `shellInf_eq`.
A producer therefore owes `1 + S.card` memberships and one containment, not a family of
statements indexed by `k`.  (The `a'`-slice `hseedS'` went with `bottom`'s conjunct (iv),
2026-09-19.) -/
theorem ChainDataWithShell.bottom_of_seed {η xper : Config α} {vl gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (cd : ChainDataWithShell η xper vl S gen)
    {vJ a z₀ : ℤ × ℤ} {L : ℤ} (ε : ℕ)
    (hrec_vJ : ∀ g ∈ ⋃ i, cd.toChainData.Ahat i, g + vJ ∈ ⋃ i, cd.toChainData.Ahat i)
    (hdz : dot cd.nJ z₀ = cd.cJ - (ε : ℤ) - 1)
    (hseed : z₀ + L • vJ ∈ reachSet (⋃ i, cd.toChainData.Ahat i) cd.vJ1)
    (hseedS : ∀ b ∈ S, z₀ + L • vJ + (b - a) ∈ reachSet (⋃ i, cd.toChainData.Ahat i) cd.vJ1)
    (hline_only : ∀ z ∈ reachSet (⋃ i, cd.toChainData.Ahat i) cd.vJ1,
      dot cd.nJ z = cd.cJ - (ε : ℤ) - 1 → ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ) :
    ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot cd.nJ z₀ = cd.cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet (⋃ i, cd.toChainData.Ahat i) cd.vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • vJ + (b - a) ∈ reachSet (⋃ i, cd.toChainData.Ahat i) cd.vJ1) ∧
      (∀ z ∈ cd.toChainData.shellInf (ε + 1),
        z ∈ cd.toChainData.shellInf ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ) := by
  have hshift : ∀ w : ℤ × ℤ, w ∈ reachSet (⋃ i, cd.toChainData.Ahat i) cd.vJ1 →
      ∀ k : ℤ, L ≤ k → w + (k - L) • vJ ∈ reachSet (⋃ i, cd.toChainData.Ahat i) cd.vJ1 :=
    fun w hw k hk => reachSet_add_zsmul_of_rec hrec_vJ hw (by omega)
  refine ⟨z₀, L, hdz, ?_, ?_, ?_⟩
  · intro k hk
    have := hshift _ hseed k hk
    have hre : z₀ + L • vJ + (k - L) • vJ = z₀ + k • vJ := by
      rw [add_assoc, ← add_smul]; ring_nf
    rwa [hre] at this
  · intro b hb k hk
    have := hshift _ (hseedS b hb) k hk
    have hre : z₀ + L • vJ + (b - a) + (k - L) • vJ = z₀ + k • vJ + (b - a) := by
      rw [add_right_comm, add_assoc z₀, ← add_smul]; ring_nf
    rwa [hre] at this
  · intro z hz
    rw [cd.shellInf_eq (ε + 1), mem_shell_succ_iff] at hz
    rcases hz with h | ⟨hr, hd⟩
    · exact Or.inl (by rw [cd.shellInf_eq ε]; exact h)
    · exact Or.inr (hline_only z hr hd)

/-- **Shape receipt.**  `bottom_of_seed`'s conclusion is the `bottom` field verbatim — the proof
is the bare projection `cg.bottom ε`, so it elaborates only while the two agree.  (Four
conjuncts since 2026-09-19.) -/
theorem ChainDataGeom.bottom_shape {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (cg : ChainDataGeom η xper vl p S gen) (ε : ℕ) :
    ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot cg.nJ z₀ = cg.cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • cg.vJ ∈ reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • cg.vJ + (b - cg.a) ∈ reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1) ∧
      (∀ z ∈ cg.toChainData.shellInf (ε + 1),
        z ∈ cg.toChainData.shellInf ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • cg.vJ) :=
  cg.bottom ε

/-- **`bottom` is not derivable from the shell data, even with the sign pinned.**

A counter-model to the implication, not to `bottom` itself: `A = {z | z.2 = 0}`, `nJ = (0, 1)`,
`vJ = (1, 0)`, `vJ1 = (0, -2)`, `cJ = 0` satisfies every hypothesis available to this section —
nonemptiness, `ahat_halfPlane`, `rec_vJ`, `dot nJ vJ = 0`, and `dot nJ vJ1 < 0` — and yet the
first two conjuncts of `bottom` fail at `ε = 0`, because the swept levels are the even integers
`≤ 0` and `cJ - 1 = -1` is not one of them.

So the remaining content of `bottom` is a statement about where `Â_∞` is *placed*, which is an
obligation on `exists_chainData` (`RegionSteps.lean:826`); it cannot be recovered by fixing a
sign convention, and the step size `dot nJ vJ1 = -1` is not free either. -/
theorem not_bottom_of_shell_data :
    ∃ (A : Set (ℤ × ℤ)) (vJ1 nJ vJ : ℤ × ℤ) (cJ : ℤ),
      A.Nonempty ∧ (∀ g ∈ A, cJ ≤ dot nJ g) ∧ (∀ g ∈ A, g + vJ ∈ A) ∧
      dot nJ vJ = 0 ∧ dot nJ vJ1 < 0 ∧
      ¬ ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - 1 ∧
          ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet A vJ1 := by
  refine ⟨{z : ℤ × ℤ | z.2 = 0}, (0, -2), (0, 1), (1, 0), 0, ⟨(0, 0), rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; simp only [dot, Set.mem_ofPred_eq] at *; omega
  · intro g hg; simp only [Set.mem_ofPred_eq] at *; simpa using hg
  · simp [dot]
  · simp [dot]
  · rintro ⟨z₀, L, h1, h2⟩
    obtain ⟨g, hg, t, heq⟩ := h2 L le_rfl
    simp only [dot, Set.mem_ofPred_eq] at h1 hg
    have h2' : z₀.2 + L * 0 = g.2 + (t : ℤ) * (-2) := by
      have := congrArg Prod.snd heq
      simpa [Prod.snd_add, Prod.smul_snd] using this
    omega

end Bottom

end Nivat.Colle35

#print axioms Nivat.Colle35.perp_ne_zero
#print axioms Nivat.Colle35.det_eq_zero_of_det_eq_zero
#print axioms Nivat.Colle35.DecompData.exists_index_det_ne_zero
#print axioms Nivat.Colle35.exists_prim_dot_zero_dot_ne_zero
#print axioms Nivat.Colle35.DecompData.exists_nJ
#print axioms Nivat.Colle35.DecompData.exists_nJ_vJ
#print axioms Nivat.Colle35.r_pos_of_mem_E
#print axioms Nivat.Colle35.DecompData.exists_edge_block
#print axioms Nivat.Colle35.DecompData.E_Sphi_eq_zonoF
#print axioms Nivat.Colle35.DecompData.E_Sphi_eq
#print axioms Nivat.Colle35.DecompData.existsUnique_index_dot_eq_zero
#print axioms Nivat.Colle35.DecompData.mem_E_Sphi_iff
#print axioms Nivat.Colle35.DecompData.exists_edge_normal_nonparallel
#print axioms Nivat.Colle35.DecompData.exists_nJ_of_edge
#print axioms Nivat.Colle35.ChainDataGeom.a_ne_a'_iff_nJ_mem_E
#print axioms Nivat.Colle35.ChainDataGeom.a_ne_a'_iff_exists_dot_h_eq_zero
#print axioms Nivat.Colle35.exists_prim_dot_zero_dot_ne_zero_det_ne_zero
#print axioms Nivat.Colle35.DecompData.exists_index_det_ne_zero_dot_ne_zero
#print axioms Nivat.Colle35.DecompData.exists_nJ_full_of_index
#print axioms Nivat.Colle35.DecompData.exists_nJ_full
#print axioms Nivat.Colle35.DecompData.not_exists_nJ_full_of_m_eq_two
#print axioms Nivat.Colle35.DecompData.exists_nJ_full_of_edge
#print axioms Nivat.Colle35.DecompDataZ.exists_nJ_of_biONED
#print axioms Nivat.Colle35.DecompDataZ.exists_nJ_full_of_biONED
#print axioms Nivat.Colle35.FaceBlock
#print axioms Nivat.Colle35.FaceBlock.ofChainDataGeom
#print axioms Nivat.Colle35.DecompDataZ.exists_faceBlock
#print axioms Nivat.Colle35.FaceBlock.gen
#print axioms Nivat.Colle35.reachSet_add_natCast_zsmul_of_rec
#print axioms Nivat.Colle35.reachSet_add_zsmul_of_rec
#print axioms Nivat.Colle35.ChainDataGeom.dot_nJ_vJ1_neg
#print axioms Nivat.Colle35.ChainDataWithShell.bottom_of_seed
#print axioms Nivat.Colle35.ChainDataGeom.bottom_shape
#print axioms Nivat.Colle35.not_bottom_of_shell_data
