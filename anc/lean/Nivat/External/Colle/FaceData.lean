/-
Lane 735D scratch file — NOT part of the main tree. Investigates whether ChainDataGeom's
fields 2-12 (vJ, a, a', r, latticeConvex_S, a_mem, a'_mem, lex, lex', edge, edge') can be
derived from the zonotope structure of S_φ, per team-lead's request.

Do not import this from Nivat/. Verify with:
  bash scripts/check1.sh tmp/lane735D_face.lean
-/
import Nivat.External.Colle.ChainGeom
import Nivat.External.Colle.MinkowskiEdges
import Nivat.External.Colle.NewtonZonotope
import Nivat.Lattice.Primitive

set_option autoImplicit false

namespace Nivat.Colle35

open Nivat Nivat.LE2

/-- **The unique generator orthogonal to an edge normal `nJ` of `S_φ`.**

Given pairwise-distinct-direction generators `h : Fin m → ℤ × ℤ` (`DecompData.h_dir`) and a
nonzero `nJ` with two indices `i, j` both orthogonal to it, `i = j`. -/
theorem unique_orthogonal_generator {m : ℕ} {h : Fin m → ℤ × ℤ}
    (h_dir : ∀ i j : Fin m, i ≠ j → det (h i) (h j) ≠ 0)
    {nJ : ℤ × ℤ} (hnJ : nJ ≠ 0) {i j : Fin m}
    (hi : dot nJ (h i) = 0) (hj : dot nJ (h j) = 0) : i = j := by
  by_contra hne
  exact h_dir i j hne (det_eq_zero_of_dot_eq_zero hnJ hi hj)

/-! ## Step B: locating that generator among the zonotope's edge normals

`E_zono` (`MinkowskiEdges.lean:292`) plus `E_segOf` (`:204`) say: `nJ` is an edge normal of
the zonotope `zonoF univ h` iff it is primitive and orthogonal to some `h i`.  Combined with
Step A, that `i` is unique. -/
theorem exists_unique_orthogonal_generator {m : ℕ} {h : Fin m → ℤ × ℤ}
    (hne : ∀ i, h i ≠ 0) (h_dir : ∀ i j : Fin m, i ≠ j → det (h i) (h j) ≠ 0)
    {nJ : ℤ × ℤ}
    (hnJ : nJ ∈ E (↑(Nivat.LE2.zonoF (Finset.univ : Finset (Fin m)) h) : Set (ℤ × ℤ))) :
    ∃! i : Fin m, dot nJ (h i) = 0 := by
  classical
  rw [coe_zonoF, E_zono] at hnJ
  simp only [Set.mem_iUnion] at hnJ
  obtain ⟨i, _, hi⟩ := hnJ
  rw [E_segOf (hne i)] at hi
  obtain ⟨hprim, hdot⟩ := hi
  have hnJne : nJ ≠ 0 := Prim.ne_zero hprim
  refine ⟨i, hdot, fun j hj => (unique_orthogonal_generator h_dir hnJne hdot hj).symm⟩

/-! ## Step C: the vertex-level face and primitive step

`face_add` decomposes the face of the zonotope into a sum of single-segment faces.  For the
distinguished index `i0` (orthogonal to `nJ`), `face_segOf_of_dot_eq_zero` gives the whole
segment `{0, h i0}`; every other index contributes a single point.  This section is NOT yet
attempted — see the blocker note below. -/

/-- **BLOCKED.**  We can name the candidate `vJ` (primitive part of `h i0`) via
`exists_primitive_nsmul_eq`, but connecting the *vertex-level* face of `zonoF` to the
*lattice-point* face of the actual generating Finset `S` (`d.Sphi`, with
`Conv d.Sphi = Conv (zonoF univ h)` only as convex hulls, not as sets) requires a bridge
lemma of the form:

    `face (↑S : Set (ℤ×ℤ)) n = {lattice points of the real edge determined by
      face (Conv S) (as a real linear functional maximiser)}`

i.e. a statement connecting the discrete `LatticeEdges.face` (defined by `dot`-comparison
directly on `S`) to the vertex set of the *real* convex hull `Conv S`.  Candidates searched:
`face_eq_of_support` (`LatticeEdges.lean:182`), `face_eq_of_supportLevel` (`:197`) — these
characterise a face given its support VALUE `c`, but do not supply `c` for `S` from `Conv S`
alone; that requires knowing `S`'s support value in direction `n` equals the zonotope
vertex-sum's support value, i.e. `suppVal S n = suppVal (zonoF univ h) n` — not found by
grep (`suppVal.*zonoF` returns 0 hits) and not attempted here for lack of time. -/
theorem exists_face_data_STUB {m : ℕ} {h : Fin m → ℤ × ℤ} (hne : ∀ i, h i ≠ 0)
    {nJ : ℤ × ℤ} {i0 : Fin m} (hi0 : dot nJ (h i0) = 0) :
    ∃ (vJ : ℤ × ℤ) (r : ℕ), vJ ≠ 0 ∧ dot nJ vJ = 0 ∧ h i0 = ((r : ℤ) + 1) • vJ := by
  obtain ⟨v, k, hprim, hkpos, heq⟩ := exists_primitive_nsmul_eq (hne i0)
  refine ⟨v, k - 1, Primitive.ne_zero hprim, ?_, ?_⟩
  · -- dot nJ v = 0 from dot nJ (h i0) = 0 and h i0 = (k:ℤ) • v, k ≠ 0
    rw [heq] at hi0
    rw [dot_comm nJ ((k : ℤ) • v), dot_smul, dot_comm v nJ] at hi0
    rcases mul_eq_zero.mp hi0 with hk0 | hv0
    · exact absurd (by exact_mod_cast hk0 : k = 0) (by omega)
    · exact hv0
  · have hcast : ((k - 1 : ℕ) : ℤ) + 1 = (k : ℤ) := by
      have h1 : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
      exact_mod_cast h1
    rw [hcast]; exact heq

/-! ## Step D: `lex` — the lattice-combinatorics half of ChainDataGeom fields 2-12

Per team-lead's correction: `a`/`a'`/`lex`/`lex'`/`edge`/`edge'` (`ChainGeom.lean:66-93`) are
pure `dot`-comparisons on the Finset `S`, not a face/vertex-bridge question.  `lex` says `a` is
the strict lexicographic maximum of `S` under `(dot (-nJ) ·, dot (-vJ) ·)`.  Since
`nJ ≠ 0`, `vJ ≠ 0`, `dot nJ vJ = 0` give `det nJ vJ ≠ 0` (`ChainGeom.lean:193`
`det_ne_zero_of_dot`), the map `b ↦ (dot nJ b, dot vJ b)` is injective on `ℤ × ℤ`, so the
lex-max is automatically *strict*. -/

/-- General lex-max helper, factored out so `lex` (`a`) and `lex'` (`a'`) share it: for any
nonzero, orthogonal `n', v'`, `S` has a strict lex-max under `(dot n' ·, dot v' ·)`. -/
theorem exists_lex_max_gen (S : Finset (ℤ × ℤ)) (hne : S.Nonempty) {n' v' : ℤ × ℤ}
    (hn'0 : n' ≠ 0) (hv'0 : v' ≠ 0) (hdot' : dot n' v' = 0) :
    ∃ a ∈ S, ∀ b ∈ S.erase a,
      dot n' b < dot n' a ∨ (dot n' b = dot n' a ∧ dot v' b < dot v' a) := by
  classical
  have hn'n' : dot n' n' ≠ 0 := by
    simp only [dot]
    intro h
    apply hn'0
    have h1 : n'.1 = 0 := by nlinarith [sq_nonneg n'.1, sq_nonneg n'.2]
    have h2 : n'.2 = 0 := by nlinarith [sq_nonneg n'.1, sq_nonneg n'.2]
    exact Prod.ext h1 h2
  have hdet : det n' v' ≠ 0 := Nivat.ColleReg.det_ne_zero_of_dot hv'0 hdot' hn'n'
  obtain ⟨a, ha, hmax⟩ :=
    Finset.exists_max_image S (fun b => toLex (dot n' b, dot v' b)) hne
  refine ⟨a, ha, fun b hb => ?_⟩
  have hbS : b ∈ S := Finset.mem_of_mem_erase hb
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  have hle : toLex (dot n' b, dot v' b) ≤ toLex (dot n' a, dot v' a) := hmax b hbS
  have hne2 : toLex (dot n' b, dot v' b) ≠ toLex (dot n' a, dot v' a) := by
    intro heq
    apply hba
    have heq' : (dot n' b, dot v' b) = (dot n' a, dot v' a) := toLex.injective heq
    have h1 : dot n' b = dot n' a := (Prod.ext_iff.mp heq').1
    have h2 : dot v' b = dot v' a := (Prod.ext_iff.mp heq').2
    by_contra hne3
    have hw : b - a ≠ 0 := sub_ne_zero.mpr hne3
    have hu1 : dot (b - a) n' = 0 := by rw [dot_comm, dot_sub, h1, sub_self]
    have hu2 : dot (b - a) v' = 0 := by rw [dot_comm, dot_sub, h2, sub_self]
    exact hdet (det_eq_zero_of_dot_eq_zero hw hu1 hu2)
  have hlt : toLex (dot n' b, dot v' b) < toLex (dot n' a, dot v' a) :=
    lt_of_le_of_ne hle hne2
  rw [Prod.Lex.toLex_lt_toLex] at hlt
  exact hlt

/-- Existence of the strict lexicographic maximum required by `ChainDataGeom.lex`
(`ChainGeom.lean:83-84`), for `a`. Instance of `exists_lex_max_gen` at `n' := -nJ, v' := -vJ`. -/
theorem exists_lex_max (S : Finset (ℤ × ℤ)) (hne : S.Nonempty) {nJ vJ : ℤ × ℤ}
    (hnJ : nJ ≠ 0) (hvJ : vJ ≠ 0) (hdot : dot nJ vJ = 0) :
    ∃ a ∈ S, ∀ b ∈ S.erase a,
      dot (-nJ) b < dot (-nJ) a ∨ (dot (-nJ) b = dot (-nJ) a ∧ dot (-vJ) b < dot (-vJ) a) := by
  have hdot' : dot (-nJ) (-vJ) = 0 := by
    simp only [dot, Prod.fst_neg, Prod.snd_neg]
    simp only [dot] at hdot
    linear_combination hdot
  exact exists_lex_max_gen S hne (neg_ne_zero.mpr hnJ) (neg_ne_zero.mpr hvJ) hdot'

/-- Existence of the strict lexicographic maximum required by `ChainDataGeom.lex'`
(`ChainGeom.lean:86-87`), for `a'`. Instance of `exists_lex_max_gen` at `n' := -nJ, v' := vJ`. -/
theorem exists_lex_max' (S : Finset (ℤ × ℤ)) (hne : S.Nonempty) {nJ vJ : ℤ × ℤ}
    (hnJ : nJ ≠ 0) (hvJ : vJ ≠ 0) (hdot : dot nJ vJ = 0) :
    ∃ a' ∈ S, ∀ b ∈ S.erase a',
      dot (-nJ) b < dot (-nJ) a' ∨ (dot (-nJ) b = dot (-nJ) a' ∧ dot vJ b < dot vJ a') := by
  have hdot' : dot (-nJ) vJ = 0 := by
    rw [dot_neg_left, hdot, neg_zero]
  exact exists_lex_max_gen S hne (neg_ne_zero.mpr hnJ) hvJ hdot'

/-! ## Step E: the `dot nJ a = dot nJ a'` corollary and `edge`

`a`/`a'` (as witnessed by `exists_lex_max`/`exists_lex_max'`) sit on the same `nJ`-row, and
`edge` follows by case-splitting on `lex`'s two branches for `b`, using
`Nivat.eq_zsmul_of_det_eq_zero` (`Lattice/Primitive.lean:83-84`) to place tied-row members on
the `vJ`-line through `a`, and `lex`/`lex'` again to bound the multiplier between `0` and `r`. -/

/-- `a` and `a'` (as produced by `exists_lex_max`/`exists_lex_max'`) lie on the same `nJ`-row.
Combines `lex` applied to `b := a'` with `lex'` applied to `b := a`; if the strict branch fired
on either side, the other side's conclusion contradicts it, so both land in the tie branch. -/
theorem dot_nJ_eq_of_lex {nJ vJ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {a a' : ℤ × ℤ}
    (ha : a ∈ S) (ha' : a' ∈ S)
    (lex : ∀ b ∈ S.erase a,
      dot (-nJ) b < dot (-nJ) a ∨ (dot (-nJ) b = dot (-nJ) a ∧ dot (-vJ) b < dot (-vJ) a))
    (lex' : ∀ b ∈ S.erase a',
      dot (-nJ) b < dot (-nJ) a' ∨ (dot (-nJ) b = dot (-nJ) a' ∧ dot vJ b < dot vJ a')) :
    dot nJ a = dot nJ a' := by
  by_cases haa' : a = a'
  · rw [haa']
  · have h1 := lex a' (Finset.mem_erase.mpr ⟨Ne.symm haa', ha'⟩)
    have h2 := lex' a (Finset.mem_erase.mpr ⟨haa', ha⟩)
    simp only [dot_neg_left] at h1 h2
    rcases h1 with h1 | ⟨h1eq, _⟩ <;> rcases h2 with h2 | ⟨h2eq, _⟩ <;> linarith

/-- **`edge` (`ChainGeom.lean:89-90`), together with the `r` (`:75`) it needs.**

Given `a, a' ∈ S` witnessed by `lex`/`lex'`, `vJ` primitive, and `dot nJ vJ = 0`, produces `r`
with `a' = a + r•vJ` and the `edge` property.  Proof: case on `lex`'s two branches for `b` — the
strict branch gives `1 ≤ dot nJ (b-a)` directly (integers); the tie branch places `b` on the
`vJ`-line through `a` via `eq_zsmul_of_det_eq_zero` (`Primitive.lean:83-84`), with the multiple
`j'` bounded below by `1` (from `lex`'s own strict `vJ`-tiebreak) and above by `r` (from `lex'`,
using that `b` and `a'` share the same row via `dot_nJ_eq_of_lex`). -/
theorem exists_r_edge {nJ vJ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {a a' : ℤ × ℤ}
    (hnJ : nJ ≠ 0) (ha : a ∈ S) (ha' : a' ∈ S)
    (hvJprim : Primitive vJ) (hdotnJvJ : dot nJ vJ = 0)
    (lex : ∀ b ∈ S.erase a,
      dot (-nJ) b < dot (-nJ) a ∨ (dot (-nJ) b = dot (-nJ) a ∧ dot (-vJ) b < dot (-vJ) a))
    (lex' : ∀ b ∈ S.erase a',
      dot (-nJ) b < dot (-nJ) a' ∨ (dot (-nJ) b = dot (-nJ) a' ∧ dot vJ b < dot vJ a')) :
    ∃ r : ℕ, a' = a + (r : ℤ) • vJ ∧
      ∀ b ∈ S.erase a,
        (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a) := by
  classical
  have hvJne : vJ ≠ 0 := hvJprim.ne_zero
  have hvJvJ : 0 < dot vJ vJ := by
    simp only [dot]
    have h12 : vJ.1 ≠ 0 ∨ vJ.2 ≠ 0 := by
      rcases eq_or_ne vJ.1 0 with h1 | h1
      · exact Or.inr (fun h2 => hvJne (Prod.ext h1 h2))
      · exact Or.inl h1
    rcases h12 with h | h
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg vJ.2]
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg vJ.1]
  have hrow : dot nJ a = dot nJ a' := dot_nJ_eq_of_lex ha ha' lex lex'
  by_cases haa' : a = a'
  · refine ⟨0, by simp [haa'], fun b hb => ?_⟩
    right
    rw [dot_sub]
    rcases lex b hb with h | ⟨heq, hlt⟩
    · simp only [dot_neg_left] at h
      omega
    · exfalso
      simp only [dot_neg_left] at heq hlt
      have hb' : b ∈ S.erase a' := haa' ▸ hb
      rcases lex' b hb' with h' | ⟨_, hlt'⟩
      · rw [← haa'] at h'
        simp only [dot_neg_left] at h'
        omega
      · rw [← haa'] at hlt'
        omega
  · have hdz : det vJ (a' - a) = 0 := by
      have h1 : dot nJ (a' - a) = 0 := by rw [dot_sub, hrow, sub_self]
      exact det_eq_zero_of_dot_eq_zero hnJ hdotnJvJ h1
    obtain ⟨c, hc⟩ := eq_zsmul_of_det_eq_zero hvJprim hdz
    have hdvjc : dot vJ (a' - a) = c * dot vJ vJ := by
      rw [hc, dot_comm vJ (c • vJ), dot_smul]
    have hltaa' : dot vJ a < dot vJ a' := by
      have hmem : a' ∈ S.erase a := Finset.mem_erase.mpr ⟨Ne.symm haa', ha'⟩
      rcases lex a' hmem with h | ⟨heq, hlt⟩
      · exfalso; simp only [dot_neg_left] at h; omega
      · simp only [dot_neg_left] at hlt; omega
    have hcpos : 0 < c := by
      have hpos : 0 < dot vJ (a' - a) := by rw [dot_sub]; linarith
      rw [hdvjc] at hpos
      by_contra hc'
      push_neg at hc'
      nlinarith
    set r : ℕ := c.toNat with hrdef
    have hrc : (r : ℤ) = c := Int.toNat_of_nonneg hcpos.le
    have hc' : a' - a = (r : ℤ) • vJ := by rw [hrc]; exact hc
    refine ⟨r, sub_eq_iff_eq_add'.mp hc', fun b hb => ?_⟩
    have hbS : b ∈ S := Finset.mem_of_mem_erase hb
    rcases lex b hb with h | ⟨heq, hlt⟩
    · right; rw [dot_sub]; simp only [dot_neg_left] at h; omega
    · left
      have hbeq : dot nJ b = dot nJ a := by
        simp only [dot_neg_left] at heq; omega
      have hbrow : dot nJ (b - a) = 0 := by rw [dot_sub, hbeq, sub_self]
      have hdzb : det vJ (b - a) = 0 := det_eq_zero_of_dot_eq_zero hnJ hdotnJvJ hbrow
      obtain ⟨j', hj'⟩ := eq_zsmul_of_det_eq_zero hvJprim hdzb
      have hdvjb : dot vJ (b - a) = j' * dot vJ vJ := by
        rw [hj', dot_comm vJ (j' • vJ), dot_smul]
      have hbagt : dot vJ a < dot vJ b := by
        simp only [dot_neg_left] at hlt; omega
      have hj'pos : 0 < j' := by
        have hpos : 0 < dot vJ (b - a) := by rw [dot_sub]; linarith
        rw [hdvjb] at hpos
        by_contra hc''
        push_neg at hc''
        nlinarith
      have hj'le : j' ≤ (r : ℤ) := by
        by_cases hba' : b = a'
        · have heqd : j' * dot vJ vJ = c * dot vJ vJ := by
            rw [← hdvjb, ← hdvjc, hba']
          have hjc : j' = c := mul_right_cancel₀ hvJvJ.ne' heqd
          omega
        · have hmem' : b ∈ S.erase a' := Finset.mem_erase.mpr ⟨hba', hbS⟩
          rcases lex' b hmem' with h' | ⟨heq', hlt'⟩
          · exfalso
            simp only [dot_neg_left] at h'
            omega
          · have hlt2 : dot vJ b - dot vJ a < dot vJ a' - dot vJ a := by linarith
            rw [← dot_sub, ← dot_sub, hdvjb, hdvjc] at hlt2
            have hjc2 : j' < c := lt_of_mul_lt_mul_right hlt2 hvJvJ.le
            omega
      have hj'len : j'.toNat ≤ r := by omega
      have hj'eqn : (j'.toNat : ℤ) = j' := Int.toNat_of_nonneg hj'pos.le
      have hj'' : b - a = (j'.toNat : ℤ) • vJ := by rw [hj'eqn]; exact hj'
      refine ⟨j'.toNat, by omega, hj'len, sub_eq_iff_eq_add'.mp hj''⟩

/-- **`edge'` (`ChainGeom.lean:92-93`), the mirror of `edge` at `a'`.**

Given `r`, `a' = a + r•vJ`, and `edge` (bookkeeping for `a`), derives `edge'` directly:
for `b ∈ S.erase a'`, either `b = a` (needs `r > 0`, forced by `a ≠ a'`), or `b ≠ a` so
`edge` applies to `b`, giving `b = a + j•vJ` with `j < r` (since `b ≠ a'`) — reindex
`j' := r - j` — or `1 ≤ dot nJ (b - a)`, which equals `dot nJ (b - a')` since
`dot nJ (a' - a) = r * dot nJ vJ = 0`. -/
theorem exists_edge' {nJ vJ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {a a' : ℤ × ℤ} {r : ℕ}
    (hdotnJvJ : dot nJ vJ = 0) (hr_eq : a' = a + (r : ℤ) • vJ)
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a)) :
    ∀ b ∈ S.erase a',
      (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a' - (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a') := by
  intro b hb
  have hbS : b ∈ S := Finset.mem_of_mem_erase hb
  have hba' : b ≠ a' := Finset.ne_of_mem_erase hb
  by_cases hba : b = a
  · have haa' : a ≠ a' := by rw [← hba]; exact hba'
    have hrpos : 0 < r := by
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · exfalso; apply haa'; rw [hr_eq, hr0]; simp
      · exact hr0
    left
    refine ⟨r, hrpos, le_refl r, ?_⟩
    rw [hba, hr_eq]; abel
  · have hbSa : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hba, hbS⟩
    rcases hedge b hbSa with ⟨j, hj1, hjr, hjeq⟩ | hpos
    · have hjr' : j ≠ r := by
        intro hjeqr
        exact hba' (by rw [hjeq, hjeqr, ← hr_eq])
      have hjlt : j < r := lt_of_le_of_ne hjr hjr'
      left
      have hj'cast : ((r - j : ℕ) : ℤ) = (r : ℤ) - (j : ℤ) := Nat.cast_sub hjlt.le
      refine ⟨r - j, by omega, by omega, ?_⟩
      rw [hjeq, hr_eq, hj'cast, sub_smul]
      abel
    · right
      have hzero : dot nJ (a' - a) = 0 := by
        have haux : a' - a = (r : ℤ) • vJ := by rw [hr_eq]; abel
        rw [haux, dot_comm nJ ((r:ℤ) • vJ), dot_smul, dot_comm vJ nJ, hdotnJvJ, mul_zero]
      have heq2 : dot nJ (b - a') = dot nJ (b - a) := by
        have haux2 : b - a' = (b - a) - (a' - a) := by abel
        rw [haux2, dot_sub, hzero, sub_zero]
      rw [heq2]
      exact hpos

end Nivat.Colle35

