/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.R2Orientation
import Nivat.External.Colle.LatticeEdges
import Nivat.Lattice.Primitive

/-!
# The bridge from `ONED` to `E`/`IsEdge`

Colle, arXiv:1909.08195v4, the paragraph after Definition 2.2 (`scratch/b3_colle2.txt:272`):

> *"as an immediate corollary from Lemma 2.3 [...] one has that all one-sided nonexpansive
> directions on `X_η` are parallel to some edge of every `η`-generating set whose convex
> hull has positive area."*

The repository carries two face vocabularies that never met:

* the **real-normal** one, `Nivat.R2.face S w c = S.filter (inner2 w · = c)`
  (`R2Orientation.lean`, `face`), which is what `ONED ξ` and Colle Lemma 2.3 in the form
  `Nivat.R2.two_le_face_card_of_mem_ONED` speak;
* the **integer-normal** one, `Nivat.LE2.face R n = {z ∈ R | ∀ y ∈ R, dot n y ≤ dot n z}`
  (`LatticeEdges.lean`, `face`), which feeds `IsEdge R n := Prim n ∧ (face R n).Nontrivial`
  and `E R = {n | IsEdge R n}`.

Both use the **outer-normal / maximal-face** convention (see the sign-convention sections of
both files: `w ∈ ONED ξ` corresponds to Colle's `ℓ ∈ nexpd(η)` with `w = -n_ℓ`, and in that
dictionary Colle's `S ∩ ℓ_S` is the `w`-*maximal* face), so no sign flip is needed here: the
two faces agree on the nose once the real normal is a positive multiple of the integer one and
the real level is the corresponding maximum.

## Main results

* `face_eq_face_of_forall_inner2_eq` — the two faces coincide as sets whenever
  `inner2 w = t * dot n` with `t > 0` and `c` is the `w`-maximum of `S`.
* `isEdge_of_mem_ONED_of_forall_inner2_eq` — **the bridge**: for a generating set `S` and a
  primitive `n` whose real image is a positive multiple of `w ∈ ONED ξ`, `IsEdge ↑S n`.
* `isEdge_of_toReal_mem_ONED`, `mem_E_of_toReal_mem_ONED` — the special case `w = toReal n`.
* `isEdge_of_mem_ONED_of_eq_smul` — the special case `w = t • toReal n`.
* `exists_mem_E_of_toReal_mem_ONED` — the `Prim` half discharged: a *non-zero* lattice vector
  `m` with `toReal m ∈ ONED ξ` is a positive multiple of a primitive `ℓ ∈ E ↑S`.
* `exists_mem_E_of_mem_ONED_of_rational` — Colle's corollary verbatim: a rational
  `w ∈ ONED ξ` is a positive multiple of `toReal ℓ` for some edge normal `ℓ ∈ E ↑S`.

No `PosArea` hypothesis is needed: `IsEdge` only asks for a nontrivial face, which is exactly
what Lemma 2.3 delivers.  The converse (an edge normal of a generating set lies in `ONED`) is
false in general and is not claimed.
-/

namespace Nivat.ONEDEdge

open Nivat Nivat.Colle Nivat.LE2

/-! ### The two faces agree at a support level -/

/-- If `inner2 w = t * dot n` pointwise with `t > 0`, then the `LE2` face of `S` with outer
normal `n` is the `R2` face of `S` exposed by `w` at the level `c := t * (max of dot n on S)`.
The maximiser `z₀` is any point of `S` at which `dot n` is maximal. -/
theorem face_eq_face_of_forall_inner2_eq {S : Finset (ℤ × ℤ)} {w : ℝ × ℝ} {n : ℤ × ℤ}
    {t : ℝ} (ht : 0 < t) (hform : ∀ z : ℤ × ℤ, inner2 w z = t * (dot n z : ℝ))
    {z₀ : ℤ × ℤ} (hz₀S : z₀ ∈ S) (hz₀max : ∀ z ∈ S, dot n z ≤ dot n z₀) :
    LE2.face (↑S) n = ↑(R2.face S w (t * (dot n z₀ : ℝ))) := by
  rw [face_eq_of_support (c := dot n z₀) (fun z hz => hz₀max z hz) ⟨z₀, hz₀S, rfl⟩]
  ext z
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, R2.mem_face]
  constructor
  · rintro ⟨hzS, hz⟩
    exact ⟨hzS, by rw [hform z, hz]⟩
  · rintro ⟨hzS, hz⟩
    refine ⟨hzS, ?_⟩
    rw [hform z] at hz
    exact_mod_cast mul_left_cancel₀ ht.ne' hz

/-! ### The bridge -/

/-- **`ONED` ⟹ `IsEdge`.**  Let `S` be a generating set for `ξ`, `w ∈ ONED ξ`, and `n` a
primitive lattice vector with `inner2 w = t * dot n` for some `t > 0` (i.e. `w` is a positive
real multiple of `toReal n`).  Then `n` is an edge normal of `S`.

This is Colle's corollary of Lemma 2.3 (`b3_colle2.txt:272`) in the repository's two
vocabularies: `Nivat.R2.two_le_face_card_of_mem_ONED` supplies "the exposed face is not a
vertex" for the real normal, and `face_eq_face_of_forall_inner2_eq` carries that across to the
integer normal. -/
theorem isEdge_of_mem_ONED_of_forall_inner2_eq {A : Type*} {ξ : Config A}
    {S : Finset (ℤ × ℤ)} (hgen : IsGeneratingSet ξ S) {w : ℝ × ℝ} (hw : w ∈ ONED ξ)
    {n : ℤ × ℤ} (hn : Prim n) {t : ℝ} (ht : 0 < t)
    (hform : ∀ z : ℤ × ℤ, inner2 w z = t * (dot n z : ℝ)) :
    IsEdge (↑S) n := by
  classical
  refine ⟨hn, ?_⟩
  obtain ⟨z₀, hz₀S, hz₀max⟩ := Finset.exists_max_image S (dot n) hgen.1
  have hmax : ∀ z ∈ S, inner2 w z ≤ t * (dot n z₀ : ℝ) := by
    intro z hz
    rw [hform z]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hz₀max z hz) ht.le
  have hface : (R2.face S w (t * (dot n z₀ : ℝ))).Nonempty :=
    ⟨z₀, R2.mem_face.mpr ⟨hz₀S, hform z₀⟩⟩
  have h2 := R2.two_le_face_card_of_mem_ONED hgen hmax hface hw
  rw [face_eq_face_of_forall_inner2_eq ht hform hz₀S hz₀max]
  exact Finset.nontrivial_coe.mpr (Finset.one_lt_card_iff_nontrivial.mp (by omega))

/-- The bridge for a lattice direction: if the real image of a primitive `n` is one-sided
nonexpansive, `n` is an edge normal of every generating set. -/
theorem isEdge_of_toReal_mem_ONED {A : Type*} {ξ : Config A}
    {S : Finset (ℤ × ℤ)} (hgen : IsGeneratingSet ξ S) {n : ℤ × ℤ} (hn : Prim n)
    (hw : toReal n ∈ ONED ξ) : IsEdge (↑S) n :=
  isEdge_of_mem_ONED_of_forall_inner2_eq hgen hw hn one_pos
    (fun z => by rw [inner2_toReal, one_mul])

/-- `mem_E` form of `isEdge_of_toReal_mem_ONED`. -/
theorem mem_E_of_toReal_mem_ONED {A : Type*} {ξ : Config A}
    {S : Finset (ℤ × ℤ)} (hgen : IsGeneratingSet ξ S) {n : ℤ × ℤ} (hn : Prim n)
    (hw : toReal n ∈ ONED ξ) : n ∈ E (↑S) :=
  isEdge_of_toReal_mem_ONED hgen hn hw

/-- `⟨z, t • w⟩ = t ⟨z, w⟩`.  (Also `Nivat.KM.inner2_smul_left`; restated here to keep this
file's imports light.) -/
theorem inner2_smul_left (t : ℝ) (w : ℝ × ℝ) (z : ℤ × ℤ) :
    inner2 (t • w) z = t * inner2 w z := by
  simp only [inner2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The bridge for a real direction given as a positive multiple of a lattice one. -/
theorem isEdge_of_mem_ONED_of_eq_smul {A : Type*} {ξ : Config A}
    {S : Finset (ℤ × ℤ)} (hgen : IsGeneratingSet ξ S) {w : ℝ × ℝ} (hw : w ∈ ONED ξ)
    {n : ℤ × ℤ} (hn : Prim n) {t : ℝ} (ht : 0 < t) (hwn : w = t • toReal n) :
    IsEdge (↑S) n :=
  isEdge_of_mem_ONED_of_forall_inner2_eq hgen hw hn ht
    (fun z => by rw [hwn, inner2_smul_left, inner2_toReal])

/-! ### Discharging the `Prim` half -/

/-- `toReal` of a natural multiple. -/
theorem toReal_natCast_smul (k : ℕ) (v : ℤ × ℤ) :
    toReal ((k : ℤ) • v) = (k : ℝ) • toReal v := by
  simp only [toReal, Prod.smul_def, smul_eq_mul, Prod.mk.injEq]
  constructor <;> push_cast <;> ring

/-- A **non-zero** lattice vector `m` with `toReal m ∈ ONED ξ` is a positive multiple of a
primitive edge normal `ℓ ∈ E ↑S` of every generating set `S`.  This discharges the `Prim`
conjunct of `IsEdge` from `Nivat.exists_primitive_nsmul_eq`. -/
theorem exists_mem_E_of_toReal_mem_ONED {A : Type*} {ξ : Config A}
    {S : Finset (ℤ × ℤ)} (hgen : IsGeneratingSet ξ S) {m : ℤ × ℤ} (hm : m ≠ 0)
    (hw : toReal m ∈ ONED ξ) :
    ∃ (ℓ : ℤ × ℤ) (k : ℕ), Prim ℓ ∧ 0 < k ∧ m = (k : ℤ) • ℓ ∧ ℓ ∈ E (↑S) := by
  obtain ⟨ℓ, k, hℓ, hk, hmk⟩ := Nivat.exists_primitive_nsmul_eq hm
  have hℓp : Prim ℓ := prim_iff_primitive.mpr hℓ
  refine ⟨ℓ, k, hℓp, hk, hmk, ?_⟩
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  exact isEdge_of_mem_ONED_of_eq_smul hgen hw hℓp hkR (by rw [hmk, toReal_natCast_smul])

/-- **Colle's corollary of Lemma 2.3, verbatim** (`b3_colle2.txt:272`): a *rational* one-sided
nonexpansive direction — one that is a positive real multiple of a non-zero lattice vector — is
parallel to an edge of every generating set, with matching orientation: `w = t • toReal ℓ` for
some `t > 0` and some edge normal `ℓ ∈ E ↑S`. -/
theorem exists_mem_E_of_mem_ONED_of_rational {A : Type*} {ξ : Config A}
    {S : Finset (ℤ × ℤ)} (hgen : IsGeneratingSet ξ S) {w : ℝ × ℝ} (hw : w ∈ ONED ξ)
    {m : ℤ × ℤ} (hm : m ≠ 0) {s : ℝ} (hs : 0 < s) (hwm : w = s • toReal m) :
    ∃ ℓ ∈ E (↑S), ∃ t : ℝ, 0 < t ∧ w = t • toReal ℓ := by
  obtain ⟨ℓ, k, hℓ, hk, hmk⟩ := Nivat.exists_primitive_nsmul_eq hm
  have hℓp : Prim ℓ := prim_iff_primitive.mpr hℓ
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hwℓ : w = (s * (k : ℝ)) • toReal ℓ := by
    rw [hwm, hmk, toReal_natCast_smul, smul_smul]
  refine ⟨ℓ, isEdge_of_mem_ONED_of_eq_smul hgen hw hℓp (mul_pos hs hkR) hwℓ,
    s * (k : ℝ), mul_pos hs hkR, hwℓ⟩

end Nivat.ONEDEdge
