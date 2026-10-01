/-
Copyright (c) 2026 Nivat formalisation project.
-/
import Nivat.External.Colle.ChainGeom
import Nivat.External.Colle.DecompData

/-!
# `a ≠ a'`: the `ℓ_J`-face of `S_φ` is an edge, not a vertex

`ChainDataGeom` (`ChainGeom.lean:66-174`) records the two endpoints `a` (`:72`) and `a'`
(`:74`) of the `ℓ_J`-parallel face of `S_φ`, pinned by the lexicographic extremality fields
`lex` (`ChainGeom.lean:83-84`) and `lex'` (`:86-87`), but it does **not** record that they are
distinct.  Collé's face dichotomy (`b3_colle2.txt:203-205`: a supporting line meets a lattice
polygon in either a vertex or a parallel edge; `:253` for the vertex/edge definitions) is what
makes `a ≠ a'` true in the intended construction, and downstream the difference is the whole
content of the `ℓ_J`-edge: `r ≥ 1`, `S_φ` has an edge with outer normal `-n_J`, and
`n_J ∈ E(S_φ)`.

This file closes that gap.  Three layers:

* `ChainDataGeom.a_mem_face_negNJ` / `a'_mem_face_negNJ` — `lex` and `lex'` alone already put
  both endpoints in `face ↑S (-n_J)`.  No use of `edge`, `edge'`, or `dot_nJ_vJ`.
* `ChainDataGeom.a_ne_a'_iff_face_nontrivial` — `a ≠ a'` is *equivalent* to that face being
  nontrivial, hence (with `nJ_prim`, `:151`) to `-n_J ∈ E ↑S`.  The reverse direction is real
  content, not bookkeeping: a third face point is forced strictly `v_J`-above `a` by `lex`
  and strictly `v_J`-below `a' = a` by `lex'`.
* `DecompData.mem_E_Sphi_of_dot_eq_zero` and `ChainDataGeom.a_ne_a'_of_dot_h_eq_zero` — the
  **source**.  `S_φ` is a zonotope over the decomposition periods `h_i` (`DecompData.Sphi_eq`,
  `DecompData.lean:108`), so its edge normals are exactly the primitive vectors orthogonal to
  some `h_i`.  A producer that chooses `n_J` primitive and orthogonal to *any one* generator
  `h i` therefore gets `a ≠ a'` for free.

The last item is what discharges the obligation at the real call site: `exists_chainData`
(`RegionSteps.lean:822`) produces a `ChainDataGeom ξ xper vl p d.Sphi genφ` for
`d : DecompDataZ ξ`, i.e. its `S` **is** `d.Sphi`, and `ℓ_J` is by construction one of the
decomposition directions (`DecompData.h_dir`'s docstring, `DecompData.lean:104-106`, citing
paper `:890`/`:896`).  So no new `ChainDataGeom` field is needed: `a ≠ a'` is derivable from
the existing fields together with the orthogonality that the producer must supply anyway.

## Relation to `Sphi_negSymm`

`Sphi_negSymm` (`DecompData.lean:417`) says `E ↑d.Sphi` is closed under `n ↦ -n`.  It is not
needed below — `dot (-n) (h i) = 0` is as immediate as `dot n (h i) = 0` — but it is what makes
the two memberships `n_J ∈ E ↑d.Sphi` and `-n_J ∈ E ↑d.Sphi` interchangeable for consumers, so
`mem_E_Sphi_of_dot_eq_zero` below delivers whichever sign is asked for.
-/

set_option autoImplicit false

namespace Nivat.Colle35

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle

variable {α : Type*}

/-! ## The two endpoints lie on the `-n_J`-face -/

/-- **`a` is in the `-n_J`-face of `S`.**  `lex` (`ChainGeom.lean:83-84`) alone: it already
says every other point of `S` is weakly below `a` for `dot (-n_J) ·`.  `edge` and
`dot_nJ_vJ` are not used. -/
theorem ChainDataGeom.a_mem_face_negNJ {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen) :
    cg.a ∈ face (↑S : Set (ℤ × ℤ)) (-cg.nJ) := by
  refine ⟨cg.a_mem, fun y hy => ?_⟩
  rcases eq_or_ne y cg.a with rfl | hy'
  · exact le_refl _
  · rcases cg.lex y (Finset.mem_erase.mpr ⟨hy', hy⟩) with h | ⟨h, -⟩
    · exact le_of_lt h
    · exact le_of_eq h

/-- **`a'` is in the `-n_J`-face of `S`.**  Mirror of `a_mem_face_negNJ`, from `lex'`
(`ChainGeom.lean:86-87`) alone. -/
theorem ChainDataGeom.a'_mem_face_negNJ {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen) :
    cg.a' ∈ face (↑S : Set (ℤ × ℤ)) (-cg.nJ) := by
  refine ⟨cg.a'_mem, fun y hy => ?_⟩
  rcases eq_or_ne y cg.a' with rfl | hy'
  · exact le_refl _
  · rcases cg.lex' y (Finset.mem_erase.mpr ⟨hy', hy⟩) with h | ⟨h, -⟩
    · exact le_of_lt h
    · exact le_of_eq h

/-! ## `a ≠ a'` is exactly "the face is an edge" -/

/-- **`a ≠ a'` ↔ the `-n_J`-face of `S` is nontrivial.**

Forward is immediate from the two lemmas above.  The reverse is the content: let `c` be a face
point other than `a`.  Being in the face, `c` sits at `a`'s `(-n_J)`-level, so `lex`'s strict
branch is unavailable and its tiebreak fires, giving `dot v_J a < dot v_J c`.  If `a = a'`,
then `c` is also in `S.erase a'` at `a'`'s level, so `lex'`'s tiebreak fires too, giving
`dot v_J c < dot v_J a' = dot v_J a` — contradiction.  Hence `a = a'` forces the face to be the
singleton `{a}`. -/
theorem ChainDataGeom.a_ne_a'_iff_face_nontrivial {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen) :
    cg.a ≠ cg.a' ↔ (face (↑S : Set (ℤ × ℤ)) (-cg.nJ)).Nontrivial := by
  constructor
  · intro hne
    exact ⟨cg.a, cg.a_mem_face_negNJ, cg.a', cg.a'_mem_face_negNJ, hne⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    by_contra heq
    apply hxy
    have keyA : ∀ c ∈ face (↑S : Set (ℤ × ℤ)) (-cg.nJ), c = cg.a := by
      intro c hc
      rcases eq_or_ne c cg.a with rfl | hcne
      · rfl
      · exfalso
        have hcS : c ∈ S.erase cg.a := Finset.mem_erase.mpr ⟨hcne, hc.1⟩
        have hlevel : dot (-cg.nJ) c = dot (-cg.nJ) cg.a :=
          le_antisymm (cg.a_mem_face_negNJ.2 c hc.1) (hc.2 cg.a cg.a_mem_face_negNJ.1)
        rcases cg.lex c hcS with h | ⟨-, hv⟩
        · exact absurd hlevel (ne_of_lt h)
        · have hcS' : c ∈ S.erase cg.a' := by rw [← heq]; exact hcS
          have hlevel' : dot (-cg.nJ) c = dot (-cg.nJ) cg.a' := by rw [← heq]; exact hlevel
          rcases cg.lex' c hcS' with h' | ⟨-, hv'⟩
          · exact absurd hlevel' (ne_of_lt h')
          · have hgt : dot cg.vJ cg.a < dot cg.vJ c := by
              rw [dot_neg_left, dot_neg_left] at hv; omega
            rw [heq] at hgt
            exact absurd hv' (not_lt.mpr (le_of_lt hgt))
    rw [keyA x hx, keyA y hy]

/-- **`a ≠ a'` ↔ `-n_J` is an edge normal of `S`.**  Packaging of the previous theorem with
`nJ_prim` (`ChainGeom.lean`, field `nJ_prim`); `IsEdge` is `Prim ∧ face nontrivial`
(`LatticeEdges.lean`, `IsEdge`).

§85: the old citation `ChainGeom.lean:151` was measured rotten 2026-09-24 — `nJ_prim` is at
`:194`, and `:151` lands inside `vJ_prim`'s docstring, so it read self-consistently while
pointing at the wrong field. -/
theorem ChainDataGeom.a_ne_a'_iff_negNJ_mem_E {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen) :
    cg.a ≠ cg.a' ↔ -cg.nJ ∈ E (↑S : Set (ℤ × ℤ)) := by
  rw [cg.a_ne_a'_iff_face_nontrivial]
  constructor
  · exact fun h => ⟨(prim_iff_primitive.mpr cg.nJ_prim).neg, h⟩
  · exact fun h => h.2

/-! ## The source: edge normals of the zonotope `S_φ` -/

/-- **Every primitive vector orthogonal to a decomposition period is an edge normal of
`S_φ`.**

`S_φ` has the convex hull of the zonotope `∑ᵢ [0, h_i]` (`DecompData.Sphi_eq`,
`DecompData.lean:108`), and `E` of a Minkowski sum of segments is the union of the `E`'s
(`E_zono`, `MinkowskiEdges.lean:292`), each of which is `{n | Prim n ∧ dot n (h i) = 0}`
(`E_segOf`, `MinkowskiEdges.lean:204`).  Only the field `h_ne` (`DecompData.lean:98`) is used;
in particular this holds for *any* `DecompData`, with no minimality or annihilator hypothesis.

Same skeleton as `Sphi_negSymm` (`DecompData.lean:417`), which is the `n ↦ -n` statement over
the same three transport lemmas. -/
theorem DecompData.mem_E_Sphi_of_dot_eq_zero [AddCommMonoid α] {η : Config α}
    (d : DecompData η) {n : ℤ × ℤ} (hprim : Prim n) (i : Fin d.m)
    (hdot : dot n (d.h i) = 0) :
    n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) := by
  have hconv : Conv d.Sphi = Conv (zonoF Finset.univ d.h) := by
    rw [d.Sphi_eq, Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun j _ => d.h_ne j)]
  rw [E_congr_of_Conv_eq hconv, coe_zonoF, E_zono]
  simp only [Set.mem_iUnion]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  rw [E_segOf (d.h_ne i)]
  exact ⟨hprim, hdot⟩

/-- Antipodal form, for consumers that want the normal with the other sign. -/
theorem DecompData.neg_mem_E_Sphi_of_dot_eq_zero [AddCommMonoid α] {η : Config α}
    (d : DecompData η) {n : ℤ × ℤ} (hprim : Prim n) (i : Fin d.m)
    (hdot : dot n (d.h i) = 0) :
    -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) :=
  d.mem_E_Sphi_of_dot_eq_zero hprim.neg i (by rw [dot_neg_left, hdot, neg_zero])

/-! ## Discharge -/

/-- **`a ≠ a'`, from orthogonality of `n_J` to one decomposition period.**

This is the intended discharge of the gap.  At the producer (`RegionSteps.exists_chainData`,
`:822`) the `S` of the bundle is literally `d.Sphi`, and `ℓ_J` is chosen among the
decomposition directions, so `dot n_J (h i) = 0` for the corresponding `i` — from which the
endpoints of the `ℓ_J`-face are distinct with no further work, and in particular
`r ≥ 1`.  No new `ChainDataGeom` field is required. -/
theorem ChainDataGeom.a_ne_a'_of_dot_h_eq_zero [AddCommMonoid α] {η xper : Config α}
    {vl p gen : ℤ × ℤ} (d : DecompData η)
    (cg : ChainDataGeom η xper vl p d.Sphi gen) (i : Fin d.m)
    (hdot : dot cg.nJ (d.h i) = 0) :
    cg.a ≠ cg.a' :=
  cg.a_ne_a'_iff_negNJ_mem_E.mpr
    (d.neg_mem_E_Sphi_of_dot_eq_zero (prim_iff_primitive.mpr cg.nJ_prim) i hdot)

/-- Companion: the `n_J`-edge membership itself, on the same hypothesis.  Together with
`a_ne_a'_of_dot_h_eq_zero` this closes both halves of the `n_J`/`a ≠ a'` pair from a single
orthogonality. -/
theorem ChainDataGeom.nJ_mem_E_Sphi_of_dot_h_eq_zero [AddCommMonoid α] {η xper : Config α}
    {vl p gen : ℤ × ℤ} (d : DecompData η)
    (cg : ChainDataGeom η xper vl p d.Sphi gen) (i : Fin d.m)
    (hdot : dot cg.nJ (d.h i) = 0) :
    cg.nJ ∈ E (↑d.Sphi : Set (ℤ × ℤ)) :=
  d.mem_E_Sphi_of_dot_eq_zero (prim_iff_primitive.mpr cg.nJ_prim) i hdot

/-- `r ≥ 1` whenever the face is a genuine edge: `a' = a + r • v_J` with `a ≠ a'` and
`v_J ≠ 0` forces `r ≠ 0`.  Recorded here because `r = 0` is the degenerate reading of the
`edge`/`edge'` fields (`ChainGeom.lean:89-93`) that `a ≠ a'` is meant to exclude. -/
theorem ChainDataGeom.r_pos_of_a_ne_a' {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen)
    (hr : cg.a' = cg.a + (cg.r : ℤ) • cg.vJ) (hne : cg.a ≠ cg.a') :
    0 < cg.r := by
  rcases Nat.eq_zero_or_pos cg.r with h0 | h
  · exact absurd (by rw [hr, h0]; simp) hne
  · exact h

end Nivat.Colle35
