/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.RegionCut

/-!
# `PolyChain` — boundary-chain machinery for `hsuppZ`

原文：Definition 3.2（`b3_colle2.txt:402`）＋ `blueprint/LEAF-HSUPP.md` §2(A)(B)(C).

Lane `lane-hsupp`, dispatched by team-lead 2026-09-22.  Three parts, in dependency
order:

* (C) `det_pos_trans` — a half-plane determinant-transitivity fact.
* (B) `faceStart` / `faceLen` / `face_eq_segment` / `faceEnd_mem` / `one_le_faceLen` —
  a finite edge face of a lattice-convex region is exactly a lattice segment.
* (A) `adjacent_shared_vertex` — fan-adjacent edges share a vertex (no determinant
  case split; the threshold/ratio-minimisation argument of `LEAF-HSUPP.md` §2(A)).

Consumer: `lane-chain`'s `tmp/wip/PolyChainSum.lean` (part (D) of the same blueprint),
ultimately `RegionSteps.lean:2899`'s `hsuppZ`.

## Status

(A), (B), (C) all proved, 0 `sorry`, `#print axioms` clean:
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Nivat.PolyChain

open Nivat Nivat.LE2 Finset Classical

/-! ## Part (C): determinant transitivity across a half-plane -/

/-- **Half-plane determinant transitivity.**  If `a, b, c` all lie strictly on the
`e`-positive side, and `det a b > 0`, `det b c > 0` (i.e. `a → b → c` turns
counterclockwise), then `det a c > 0`.

原文：`blueprint/LEAF-HSUPP.md` §2(C).  Key identity (checked by `ring`):
`dot e b * det a c = dot e a * det b c + dot e c * det a b`. -/
theorem det_pos_trans {e a b c : ℤ × ℤ}
    (ha : 0 < Nivat.LE2.dot e a) (hb : 0 < Nivat.LE2.dot e b) (hc : 0 < Nivat.LE2.dot e c)
    (hab : 0 < Nivat.det a b) (hbc : 0 < Nivat.det b c) : 0 < Nivat.det a c := by
  have hid : Nivat.LE2.dot e b * Nivat.det a c
      = Nivat.LE2.dot e a * Nivat.det b c + Nivat.LE2.dot e c * Nivat.det a b := by
    simp only [Nivat.LE2.dot, Nivat.det]; ring
  by_contra hcon
  push_neg at hcon
  have h1 : Nivat.LE2.dot e b * Nivat.det a c ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hb.le hcon
  nlinarith [mul_pos ha hbc, mul_pos hc hab]

/-! ## Part (B): a finite edge face is a lattice segment -/

/-- **A `dot (dir ν)`-minimal point of `face T ν` exists.**  Auxiliary existence lemma
feeding the `dite` inside `faceStart`. -/
theorem exists_faceStart {T : Set (ℤ × ℤ)} {ν : ℤ × ℤ} (hfin : T.Finite) (hν : ν ∈ E T) :
    ∃ a ∈ face T ν, ∀ b ∈ face T ν, dot (dir ν) a ≤ dot (dir ν) b := by
  have hfaceFin : (face T ν).Finite := hfin.subset (face_subset T ν)
  have hfaceNe : (face T ν).Nonempty := (mem_E_iff.mp hν).2.nonempty
  obtain ⟨g, hgmem, hmin⟩ := hfaceFin.exists_minimalFor (dot (dir ν)) _ hfaceNe
  refine ⟨g, hgmem, fun b hb => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact absurd (hmin hb hlt.le) (by omega)

/-- **The start of a face**: the `dot (dir ν)`-minimal point of `face T ν`.  Well-defined
(via `exists_faceStart`) whenever `T` is finite and `ν ∈ E T`; junk value `(0,0)`
otherwise. -/
noncomputable def faceStart (T : Set (ℤ × ℤ)) (ν : ℤ × ℤ) : ℤ × ℤ :=
  if h : ∃ a ∈ face T ν, ∀ b ∈ face T ν, dot (dir ν) a ≤ dot (dir ν) b then h.choose
  else (0, 0)

theorem faceStart_mem {T : Set (ℤ × ℤ)} {ν : ℤ × ℤ} (hfin : T.Finite) (hν : ν ∈ E T) :
    faceStart T ν ∈ face T ν := by
  unfold faceStart
  rw [dif_pos (exists_faceStart hfin hν)]
  exact (exists_faceStart hfin hν).choose_spec.1

theorem faceStart_min {T : Set (ℤ × ℤ)} {ν : ℤ × ℤ} (hfin : T.Finite) (hν : ν ∈ E T) :
    ∀ b ∈ face T ν, dot (dir ν) (faceStart T ν) ≤ dot (dir ν) b := by
  unfold faceStart
  rw [dif_pos (exists_faceStart hfin hν)]
  exact (exists_faceStart hfin hν).choose_spec.2

/-- **The (lattice) length of a face**: `encard - 1` as a natural number.  Since
`face T ν` is `Nontrivial` for `ν ∈ E T`, `encard ≥ 2` and `faceLen ≥ 1`
(`one_le_faceLen`). -/
noncomputable def faceLen (T : Set (ℤ × ℤ)) (ν : ℤ × ℤ) : ℕ := (face T ν).encard.toNat - 1

/-- The self-pairing of a nonzero `dir ν` (equivalently, of a primitive `ν`) is
strictly positive: `dir ν ≠ 0` and `dot` is a sum of two squares. -/
theorem dot_dir_pos {ν : ℤ × ℤ} (hν : Prim ν) : 0 < dot (dir ν) (dir ν) := by
  have hdirne : dir ν ≠ 0 := (prim_dir_of_prim hν).ne_zero
  have hnonneg : 0 ≤ dot (dir ν) (dir ν) := by
    simp only [dot]; exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  rcases eq_or_lt_of_le hnonneg with heq | hgt
  · exfalso
    apply hdirne
    simp only [dot] at heq
    have h1 : (dir ν).1 * (dir ν).1 ≤ 0 := by nlinarith [mul_self_nonneg (dir ν).2]
    have h2 : (dir ν).2 * (dir ν).2 ≤ 0 := by nlinarith [mul_self_nonneg (dir ν).1]
    have hx : (dir ν).1 = 0 := mul_self_eq_zero.mp (le_antisymm h1 (mul_self_nonneg _))
    have hy : (dir ν).2 = 0 := mul_self_eq_zero.mp (le_antisymm h2 (mul_self_nonneg _))
    exact Prod.ext hx hy
  · exact hgt

/-- Every point of `face T ν` is `faceStart T ν` shifted by a *natural* multiple of
`dir ν`: the integer `t` from `exists_zsmul_dir_of_mem_face` is forced `≥ 0` by
minimality of `faceStart`. -/
theorem exists_nat_shift_of_mem_face {T : Set (ℤ × ℤ)} {ν : ℤ × ℤ}
    (hfin : T.Finite) (hν : ν ∈ E T) {z : ℤ × ℤ} (hz : z ∈ face T ν) :
    ∃ t : ℕ, z = faceStart T ν + (t : ℤ) • dir ν := by
  have hprimν : Prim ν := (mem_E_iff.mp hν).1
  obtain ⟨t, ht⟩ := exists_zsmul_dir_of_mem_face hprimν (faceStart_mem hfin hν) hz
  have hsq_pos : 0 < dot (dir ν) (dir ν) := dot_dir_pos hprimν
  have hmin := faceStart_min hfin hν z hz
  have hexp : dot (dir ν) z = dot (dir ν) (faceStart T ν) + t * dot (dir ν) (dir ν) := by
    rw [ht]; simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  have ht0 : 0 ≤ t := by nlinarith
  refine ⟨t.toNat, ?_⟩
  rw [ht, Int.toNat_of_nonneg ht0]

/-- The parameter `t` in `faceStart T ν + t • dir ν` is unique. -/
theorem eq_of_faceStart_add_zsmul_eq {T : Set (ℤ × ℤ)} {ν : ℤ × ℤ} (hν : ν ∈ E T)
    {t1 t2 : ℤ} (h : faceStart T ν + t1 • dir ν = faceStart T ν + t2 • dir ν) : t1 = t2 := by
  have hprimν : Prim ν := (mem_E_iff.mp hν).1
  have hsq_pos : 0 < dot (dir ν) (dir ν) := dot_dir_pos hprimν
  have hcong := congrArg (dot (dir ν)) h
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hcong
  have hd' : t1 * dot (dir ν) (dir ν) = t2 * dot (dir ν) (dir ν) := by
    simp only [dot]; linear_combination hcong
  exact mul_right_cancel₀ (ne_of_gt hsq_pos) hd'

/-- Every point on the `dir ν`-line through `faceStart T ν` has the same `dot ν`-value as
`faceStart T ν` itself, since `dot ν (dir ν) = 0`. -/
theorem dot_faceStart_add_zsmul (T : Set (ℤ × ℤ)) (ν : ℤ × ℤ) (t : ℤ) :
    dot ν (faceStart T ν + t • dir ν) = dot ν (faceStart T ν) := by
  have hzero : dot ν (dir ν) = 0 := dot_dir ν
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hzero ⊢
  linear_combination t * hzero

/-- **Order-convexity of the "achieved parameter" set.**  If `s, u : ℕ` both give points of
`face T ν` (via `faceStart + · • dir ν`), and `s ≤ t ≤ u`, then `t` does too.  This is where
`IsLatticeConvexRegion T` and `mem_of_between` enter: the segment `faceStart+s•dirν` … `faceStart+u•dirν`
lies in `T` (convexity), and every point of it has the same `dot ν`-value as `faceStart` (since
`dot ν (dir ν) = 0`), hence — being a maximiser of `dot ν` over `T` — lies in `face T ν`. -/
theorem mem_face_of_between {T : Set (ℤ × ℤ)} (hlc : IsLatticeConvexRegion T) {ν : ℤ × ℤ}
    {s t u : ℕ} (hst : s ≤ t) (htu : t ≤ u)
    (hs : faceStart T ν + (s : ℤ) • dir ν ∈ face T ν)
    (hu : faceStart T ν + (u : ℤ) • dir ν ∈ face T ν) :
    faceStart T ν + (t : ℤ) • dir ν ∈ face T ν := by
  have hmem : faceStart T ν + (t : ℤ) • dir ν ∈ T :=
    mem_of_between hlc (face_subset T ν hs) (face_subset T ν hu)
      (by exact_mod_cast hst) (by exact_mod_cast htu)
  refine mem_face_iff.mpr ⟨hmem, fun y hy => ?_⟩
  have hy' := hs.2 y hy
  rw [dot_faceStart_add_zsmul T ν (s : ℤ)] at hy'
  rw [dot_faceStart_add_zsmul T ν (t : ℤ)]
  exact hy'

/-- `faceLen T ν ≥ 1`: a face is `Nontrivial` (for `ν ∈ E T`), so `encard ≥ 2`. -/
theorem one_le_faceLen {T : Set (ℤ × ℤ)} (hfin : T.Finite) {ν : ℤ × ℤ} (hν : ν ∈ E T) :
    1 ≤ faceLen T ν := by
  have hnt : (face T ν).Nontrivial := (mem_E_iff.mp hν).2
  have hfaceFin : (face T ν).Finite := hfin.subset (face_subset T ν)
  have h1lt : 1 < (face T ν).encard := Set.one_lt_encard_iff_nontrivial.mpr hnt
  obtain ⟨n, hn⟩ := hfaceFin.exists_encard_eq_coe
  rw [hn] at h1lt
  have h1ltn : 1 < n := by exact_mod_cast h1lt
  unfold faceLen
  rw [hn, ENat.toNat_natCast]
  omega

/-- **A finite edge face is exactly a lattice segment.**  Combines injectivity
(`eq_of_faceStart_add_zsmul_eq`), surjectivity (`exists_nat_shift_of_mem_face`), and
order-convexity (`mem_face_of_between`) to show `face T ν` is *exactly* the segment
`{faceStart T ν + t • dir ν | 0 ≤ t ≤ faceLen T ν}`. -/
theorem face_eq_segment {T : Set (ℤ × ℤ)} (hlc : IsLatticeConvexRegion T) {ν : ℤ × ℤ}
    (hfin : T.Finite) (hν : ν ∈ E T) :
    face T ν = {z | ∃ t : ℕ, t ≤ faceLen T ν ∧ z = faceStart T ν + (t : ℤ) • dir ν} := by
  set φ : ℕ → ℤ × ℤ := fun t => faceStart T ν + (t : ℤ) • dir ν with hφ
  set S : Set ℕ := φ ⁻¹' (face T ν) with hS
  have hφinj : Set.InjOn φ S := by
    intro t1 _ t2 _ h12
    have heq : (t1 : ℤ) = (t2 : ℤ) := eq_of_faceStart_add_zsmul_eq hν h12
    exact_mod_cast heq
  have hSfin : S.Finite := Set.Finite.preimage hφinj (hfin.subset (face_subset T ν))
  have h0S : 0 ∈ S := by
    show φ 0 ∈ face T ν
    simpa [hφ] using faceStart_mem hfin hν
  have hSne : S.Nonempty := ⟨0, h0S⟩
  obtain ⟨M, hMS, hMmax⟩ := Set.exists_max_image S id hSfin hSne
  have hSeq : S = {t : ℕ | t < M + 1} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro ht; exact Nat.lt_succ_of_le (hMmax t ht)
    · intro htlt
      have htM : t ≤ M := Nat.lt_succ_iff.mp htlt
      show φ t ∈ face T ν
      have h0 : φ 0 ∈ face T ν := Set.mem_preimage.mp h0S
      have hM : φ M ∈ face T ν := Set.mem_preimage.mp hMS
      exact mem_face_of_between hlc (Nat.zero_le t) htM h0 hM
  have hface_eq : face T ν = φ '' S := by
    ext z
    constructor
    · intro hz
      obtain ⟨t, ht⟩ := exists_nat_shift_of_mem_face hfin hν hz
      have htS : t ∈ S := by
        show φ t ∈ face T ν
        rw [show φ t = z from ht.symm]; exact hz
      exact ⟨t, htS, ht.symm⟩
    · rintro ⟨t, htS, rfl⟩
      exact Set.mem_preimage.mp htS
  have hcard : (face T ν).encard = ((M + 1 : ℕ) : ℕ∞) := by
    rw [hface_eq, hφinj.encard_image, hSeq, Set.Nat.encard_range]
  have hfaceLen : faceLen T ν = M := by
    unfold faceLen
    rw [hcard, ENat.toNat_natCast]; omega
  rw [hface_eq, hSeq, hfaceLen]
  ext z
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Nat.lt_succ_iff.mp ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Nat.lt_succ_iff.mpr ht, rfl⟩

/-- The endpoint `faceStart T ν + faceLen T ν • dir ν` is (unsurprisingly) itself in
`face T ν`: the `t = faceLen T ν` case of `face_eq_segment`. -/
theorem faceEnd_mem {T : Set (ℤ × ℤ)} (hlc : IsLatticeConvexRegion T) {ν : ℤ × ℤ}
    (hfin : T.Finite) (hν : ν ∈ E T) :
    faceStart T ν + (faceLen T ν : ℤ) • dir ν ∈ face T ν := by
  rw [face_eq_segment hlc hfin hν]
  exact ⟨faceLen T ν, le_refl _, rfl⟩

/-! ## Part (A): fan adjacency ⟹ shared vertex -/

/-- **Fan-adjacent edges share a vertex.**  `LEAF-HSUPP.md` §2(A) — the
threshold/ratio-minimisation argument; **no determinant case split** (the replacement for
the route `EnvCornerFit.lean:596-601` got stuck on). -/
theorem adjacent_shared_vertex {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hlc : IsLatticeConvexRegion T)
    {ν ν' : ℤ × ℤ} (hν : ν ∈ E T) (hν' : ν' ∈ E T) (hdet : 0 < det ν ν')
    (hadj : ∀ μ ∈ E T, ¬(0 < det ν μ ∧ 0 < det μ ν')) :
    faceStart T ν + (faceLen T ν : ℤ) • dir ν = faceStart T ν' := by
  set Q : ℤ × ℤ := faceStart T ν + (faceLen T ν : ℤ) • dir ν with hQdef
  have hQmem : Q ∈ face T ν := faceEnd_mem hlc hfin hν
  -- (B)-style monotonicity: `dot ν' (faceStart T ν + s • dir ν) = dot ν' faceStart + s * det ν ν'`.
  have hexpand : ∀ s : ℤ,
      dot ν' (faceStart T ν + s • dir ν) = dot ν' (faceStart T ν) + s * det ν ν' := by
    intro s
    simp only [dot, det, dir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  -- Step 2: `Q` maximises `dot ν'` over `face T ν` (the coefficient `det ν ν' > 0`).
  have hQmax : ∀ z ∈ face T ν, dot ν' z ≤ dot ν' Q := by
    intro z hz
    rw [face_eq_segment hlc hfin hν] at hz
    obtain ⟨t, htle, htz⟩ := hz
    rw [htz, hexpand, hQdef, hexpand]
    have htcast : (t : ℤ) ≤ (faceLen T ν : ℤ) := by exact_mod_cast htle
    have hmul : (t : ℤ) * det ν ν' ≤ (faceLen T ν : ℤ) * det ν ν' :=
      mul_le_mul_of_nonneg_right htcast hdet.le
    linarith
  -- Step 3: `Q ∈ face T ν'`.
  have hQinfaceν' : Q ∈ face T ν' := by
    by_contra hQnot
    have hYex : ∃ y ∈ T, dot ν' Q < dot ν' y := by
      by_contra hcon
      push_neg at hcon
      exact hQnot (mem_face_iff.mpr ⟨face_subset T ν hQmem, hcon⟩)
    set Y : Set (ℤ × ℤ) := {y | y ∈ T ∧ dot ν' Q < dot ν' y} with hYdef
    obtain ⟨y0, hy0T, hy0Q⟩ := hYex
    have hYne : Y.Nonempty := ⟨y0, hy0T, hy0Q⟩
    have hYfin : Y.Finite := hfin.subset (fun y hy => hy.1)
    have hYlt : ∀ y ∈ Y, dot ν y < dot ν Q := by
      intro y hy
      obtain ⟨hyT, hyQ⟩ := hy
      have hle : dot ν y ≤ dot ν Q := (mem_face_iff.mp hQmem).2 y hyT
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso
        have hyface : y ∈ face T ν :=
          mem_face_iff.mpr ⟨hyT, fun w hw => by rw [h]; exact (mem_face_iff.mp hQmem).2 w hw⟩
        exact absurd (hQmax y hyface) (not_le.mpr hyQ)
    set p : ℤ × ℤ → ℤ := fun y => dot ν Q - dot ν y with hpdef
    set q : ℤ × ℤ → ℤ := fun y => dot ν' y - dot ν' Q with hqdef
    have hppos : ∀ y ∈ Y, 0 < p y := fun y hy => sub_pos.mpr (hYlt y hy)
    have hqpos : ∀ y ∈ Y, 0 < q y := fun y hy => sub_pos.mpr hy.2
    obtain ⟨ystar, hystarY, hystarmin⟩ :=
      Set.exists_min_image Y (fun y => (p y : ℚ) / (q y)) hYfin hYne
    have hcross : ∀ y ∈ Y, p ystar * q y ≤ p y * q ystar := by
      intro y hy
      have hqy : (0 : ℚ) < (q y : ℚ) := by exact_mod_cast hqpos y hy
      have hqystar : (0 : ℚ) < (q ystar : ℚ) := by exact_mod_cast hqpos ystar hystarY
      have hle := hystarmin y hy
      rw [div_le_div_iff₀ hqystar hqy] at hle
      exact_mod_cast hle
    have hpystarpos := hppos ystar hystarY
    have hqystarpos := hqpos ystar hystarY
    set μ₀ : ℤ × ℤ := (q ystar) • ν + (p ystar) • ν' with hμ0def
    have hdetνμ0 : 0 < det ν μ₀ := by
      have hid : det ν μ₀ = (q ystar) * det ν ν + (p ystar) * det ν ν' := by
        simp only [hμ0def, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add,
          Prod.snd_add]
        ring
      rw [hid, det_self]
      nlinarith [hdet, hpystarpos]
    have hdetμ0ν' : 0 < det μ₀ ν' := by
      have hid : det μ₀ ν' = (q ystar) * det ν ν' + (p ystar) * det ν' ν' := by
        simp only [hμ0def, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add,
          Prod.snd_add]
        ring
      rw [hid, det_self]
      nlinarith [hdet, hqystarpos]
    have hμ0ne : μ₀ ≠ (0 : ℤ × ℤ) := by
      intro h0
      rw [h0] at hdetνμ0
      simp only [det] at hdetνμ0
      exact absurd hdetνμ0 (by norm_num)
    obtain ⟨hprimμ, g, hgpos, hgeq⟩ := primPart_spec hμ0ne
    set μ : ℤ × ℤ := primPart μ₀ with hμdef
    have hfaceEq : face T μ₀ = face T μ := by rw [hgeq]; exact face_smul hgpos μ
    have hμ0max : ∀ y ∈ T, dot μ₀ y ≤ dot μ₀ Q := by
      intro y hyT
      by_cases hyY : y ∈ Y
      · have hcy := hcross y hyY
        have hexpμ0 : dot μ₀ y - dot μ₀ Q
            = (q ystar) * (dot ν y - dot ν Q) + (p ystar) * (dot ν' y - dot ν' Q) := by
          simp only [hμ0def, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add,
            Prod.snd_add]
          ring
        have hpy : dot ν y - dot ν Q = -(p y) := by rw [hpdef]; ring
        have hqy' : dot ν' y - dot ν' Q = q y := by rw [hqdef]
        nlinarith [hexpμ0]
      · have hνle : dot ν y ≤ dot ν Q := (mem_face_iff.mp hQmem).2 y hyT
        have hν'le : dot ν' y ≤ dot ν' Q := by
          by_contra hcc
          push_neg at hcc
          exact hyY ⟨hyT, hcc⟩
        have hexpμ0y : dot μ₀ y = (q ystar) * dot ν y + (p ystar) * dot ν' y := by
          simp only [hμ0def, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add,
            Prod.snd_add]
          ring
        have hexpμ0Q : dot μ₀ Q = (q ystar) * dot ν Q + (p ystar) * dot ν' Q := by
          simp only [hμ0def, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add,
            Prod.snd_add]
          ring
        rw [hexpμ0y, hexpμ0Q]
        have h1 : q ystar * dot ν y ≤ q ystar * dot ν Q :=
          mul_le_mul_of_nonneg_left hνle hqystarpos.le
        have h2 : p ystar * dot ν' y ≤ p ystar * dot ν' Q :=
          mul_le_mul_of_nonneg_left hν'le hpystarpos.le
        linarith
    have hQTmem : Q ∈ T := face_subset T ν hQmem
    have hQfaceμ0 : Q ∈ face T μ₀ := mem_face_iff.mpr ⟨hQTmem, hμ0max⟩
    have hystarTmem : ystar ∈ T := hystarY.1
    have hystareq : dot μ₀ ystar = dot μ₀ Q := by
      have hexpμ0 : dot μ₀ ystar - dot μ₀ Q
          = (q ystar) * (dot ν ystar - dot ν Q) + (p ystar) * (dot ν' ystar - dot ν' Q) := by
        simp only [hμ0def, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add,
          Prod.snd_add]
        ring
      have hp' : dot ν ystar - dot ν Q = -(p ystar) := by rw [hpdef]; ring
      have hq' : dot ν' ystar - dot ν' Q = q ystar := by rw [hqdef]
      nlinarith [hexpμ0]
    have hystarfaceμ0 : ystar ∈ face T μ₀ :=
      mem_face_iff.mpr ⟨hystarTmem, fun w hw => by rw [hystareq]; exact hμ0max w hw⟩
    have hQnestar : Q ≠ ystar := by
      intro heq
      have hcontra := hystarY.2
      rw [heq] at hcontra
      exact lt_irrefl _ hcontra
    have hnontrivμ0 : (face T μ₀).Nontrivial := ⟨Q, hQfaceμ0, ystar, hystarfaceμ0, hQnestar⟩
    have hμE : μ ∈ E T := mem_E_iff.mpr ⟨hprimμ, hfaceEq ▸ hnontrivμ0⟩
    have hbil1 : det ν μ₀ = g * det ν μ := by
      rw [hgeq]; simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have hdetνμ : 0 < det ν μ := by
      by_contra hcon
      push_neg at hcon
      have : det ν μ₀ ≤ 0 := by
        rw [hbil1]; exact mul_nonpos_of_nonneg_of_nonpos hgpos.le hcon
      linarith [hdetνμ0]
    have hbil2 : det μ₀ ν' = g * det μ ν' := by
      rw [hgeq]; simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have hdetμν' : 0 < det μ ν' := by
      by_contra hcon
      push_neg at hcon
      have : det μ₀ ν' ≤ 0 := by
        rw [hbil2]; exact mul_nonpos_of_nonneg_of_nonpos hgpos.le hcon
      linarith [hdetμ0ν']
    exact hadj μ hμE ⟨hdetνμ, hdetμν'⟩
  -- Step 4: `Q`, being also a max of `dot ν` over all of `T` (hence over `face T ν'`),
  -- is forced to sit at `t = 0` on `face T ν'`, i.e. `Q = faceStart T ν'`.
  rw [face_eq_segment hlc hfin hν'] at hQinfaceν'
  obtain ⟨t, htle, htQ⟩ := hQinfaceν'
  have hexpand' : ∀ s : ℤ,
      dot ν (faceStart T ν' + s • dir ν') = dot ν (faceStart T ν') + s * det ν' ν := by
    intro s
    simp only [dot, det, dir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  have hQdotν : dot ν Q = dot ν (faceStart T ν') + (t : ℤ) * det ν' ν := by rw [htQ, hexpand']
  have hstartmemT : faceStart T ν' ∈ T := face_subset T ν' (faceStart_mem hfin hν')
  have hQge : dot ν (faceStart T ν') ≤ dot ν Q :=
    (mem_face_iff.mp hQmem).2 (faceStart T ν') hstartmemT
  have hdetν'ν : det ν' ν = -det ν ν' := by simp only [det]; ring
  have hdetν'νneg : det ν' ν < 0 := by rw [hdetν'ν]; linarith [hdet]
  have ht0 : t = 0 := by
    rcases Nat.eq_zero_or_pos t with h | h
    · exact h
    · exfalso
      have htpos : (0 : ℤ) < (t : ℤ) := by exact_mod_cast h
      have hneg : (t : ℤ) * det ν' ν < 0 := mul_neg_of_pos_of_neg htpos hdetν'νneg
      linarith [hQdotν, hQge]
  rw [htQ, ht0]
  simp

end Nivat.PolyChain
