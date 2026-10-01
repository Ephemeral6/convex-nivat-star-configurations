/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.RegionClaim411
import Nivat.External.Colle.L1Assemble
import Nivat.External.Colle.L3Band
import Nivat.External.Colle.ONEDRational

/-!
# Leaf C — Collé's (4.1) run from Lemma 2.3

**Target**: `ColleReg.exists_case2_run` (`RegionSteps.lean`, the `sorry` leaf C was reduced to on
2026-09-19).  Its conclusion is `exists_run` below, verbatim: a point `q` of the Lemma 2.4
generating set `Sgen` strictly above the `n_J`-minimal face, carrying `|face| - 1` consecutive
`v_J`-points inside `Sgen`.

**Source**: `b3_colle2.txt:627` — *"Since the oriented lines `−ℓ, ℓ ∈ nexpd(η)`, from Lemma 2.3
we get that `𝒮` has an edge parallel to `ℓ` and another one parallel to `−ℓ`"* — and `:637`,
(4.1).  Both `vl`-faces of `Sgen` being edges is the input; the run is then the `j = 0` point of
`L1Data.maxB_wide` (`L1Assemble.lean`) at `u := vl`, `u' := v_J`, read through
`Claim411.exists_cutNormal_eq` (`toReal (-n_J)` is one of the two cut normals of `v_J`).

**What this needs beyond `exists_case2_run`'s current binders**: the bi-nonexpansive data
`hℓ_nel / hℓ_pos / hℓ_neg` (Lemma 2.3's hypothesis `±ℓ ∈ nexpd(η)`, `Lemma 4.1`'s standing
assumption at `:607`) and `hvl_prim / hdet_vl / hdet_ℓ` tying `vl` to `ℓ` and `p`.  All six are
binders of `exists_case2_window` since 2026-09-19 10:47 and are in scope at `ColleRegion.lean:356-363`.
⚠ Without them the statement is not provable from `IsGeneratingSet` alone: a `Sgen` lying in a
single `n_J`-level has no `q` above its face at all.

Receipt: `tmp/shadow_check.sh` against the 10:01 `RegionClaim411.lean` (its `.lake` olean predates
`exists_cutNormal_eq` / `exists_case2_window_maxB_weak_of_run`, so `check1.sh` cannot see them).
-/

set_option autoImplicit false

namespace Nivat.ColleReg.C11Bridge

open Nivat Nivat.LE2 Nivat.Colle Nivat.Colle35 Nivat.Colle41 Nivat.ColleReg.Claim411

variable {ξ xper : Config ℤ} {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}

/-- `det vl v_J ≠ 0`: `vl ∥ p`, `⟪n_J, p⟫ ≠ 0`, `⟪n_J, v_J⟫ = 0`. -/
theorem det_vl_vJ_ne_zero (cg : ChainDataGeom ξ xper vl p S gen)
    (hvl_prim : Primitive vl) (hdet_vl : det p vl = 0) : det vl cg.vJ ≠ 0 := by
  have hdet' : det vl p = 0 := by simp only [det] at hdet_vl ⊢; linarith
  obtain ⟨c, hc⟩ := eq_zsmul_of_det_eq_zero hvl_prim hdet'
  have hnvl : dot cg.nJ vl ≠ 0 := by
    intro h
    apply cg.dot_nJ_p
    have e : dot cg.nJ p = c * dot cg.nJ vl := by
      have := congrArg (dot cg.nJ) hc
      rwa [dot_zsmul_right] at this
    rw [e, h, mul_zero]
  exact det_ne_zero_of_dot cg.vJ_ne cg.dot_nJ_vJ hnvl

/-- `±toReal (perp vl) ∈ ONED ξ` from `±ℓ ∈ nexpd(ξ)` and `ℓ ⟂ vl` (both primitive). -/
theorem perp_vl_mem_ONED (hvl_prim : Primitive vl)
    {ℓ : ℤ × ℤ} (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hdet_ℓ : dot ℓ vl = 0) :
    toReal (perp vl) ∈ ONED ξ ∧ toReal (-perp vl) ∈ ONED ξ := by
  have hperp : Primitive (perp vl) := primitive_perp hvl_prim
  have hℓprim : Primitive ℓ := hℓ_nel.1
  have hℓ0 : ℓ ≠ 0 := hℓprim.ne_zero
  have hℓ0' : -ℓ ≠ 0 := neg_ne_zero.mpr hℓ0
  have hd : det (perp vl) ℓ = 0 := by
    simp only [det, perp, dot] at hdet_ℓ ⊢; linarith
  have hpos := Nivat.ONEDRational.toReal_mem_ONED_of_isOneSidedNonexpansive hℓ0 hℓ_pos
  have hneg := Nivat.ONEDRational.toReal_mem_ONED_of_isOneSidedNonexpansive hℓ0' hℓ_neg
  rcases eq_or_eq_neg_of_det_eq_zero hperp hℓprim hd with h | h
  · rw [← h]; exact ⟨hpos, hneg⟩
  · have h' : perp vl = -ℓ := by rw [h, neg_neg]
    rw [h', neg_neg]; exact ⟨hneg, hpos⟩

/-- Both `vl`-faces of a generating set are edges (Collé Lemma 2.3, `b3_colle2.txt:627`). -/
theorem two_le_faces_vl {Sgen : Finset (ℤ × ℤ)} (hSgen : IsGeneratingSet ξ Sgen)
    (hvl_prim : Primitive vl)
    {ℓ : ℤ × ℤ} (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hdet_ℓ : dot ℓ vl = 0) :
    2 ≤ (L1Data.topFace true vl Sgen).card ∧ 2 ≤ (L1Data.bottomFace true vl Sgen).card := by
  have hne : Sgen.Nonempty := hSgen.1
  obtain ⟨hpos, hneg⟩ := perp_vl_mem_ONED hvl_prim hℓ_nel hℓ_pos hℓ_neg hdet_ℓ
  have hct : L1Data.cutNormal true vl = toReal (perp vl) := rfl
  have hcf : L1Data.cutNormal false vl = toReal (-perp vl) := rfl
  constructor
  · show 2 ≤ (Nivat.R2.face Sgen (L1Data.cutNormal true vl) _).card
    exact Nivat.R2.two_le_face_card_of_mem_ONED hSgen (L1Data.le_levelMax hne)
      (L1Data.face_levelMax_nonempty hne) (by rw [hct]; exact hpos)
  · have h := L1Data.topFace_not true vl hne
    simp only [Bool.not_true] at h
    rw [← h]
    show 2 ≤ (Nivat.R2.face Sgen (L1Data.cutNormal false vl) _).card
    exact Nivat.R2.two_le_face_card_of_mem_ONED hSgen (L1Data.le_levelMax hne)
      (L1Data.face_levelMax_nonempty hne) (by rw [hcf]; exact hneg)

/-- `levelMax` for the normal `-n_J` is attained at any `⟪n_J, ·⟫`-minimal point. -/
theorem levelMax_neg_nJ (cg : ChainDataGeom ξ xper vl p S gen)
    {Sgen : Finset (ℤ × ℤ)} (hne : Sgen.Nonempty)
    {a₀ : ℤ × ℤ} (ha₀ : a₀ ∈ Sgen) (hmin : ∀ w ∈ Sgen, dot cg.nJ a₀ ≤ dot cg.nJ w) :
    L1Data.levelMax Sgen (toReal (-cg.nJ)) = inner2 (toReal (-cg.nJ)) a₀ := by
  apply Nivat.L3Band.levelMax_eq_of_max hne ha₀
  intro z hz
  rw [inner2_toReal, inner2_toReal, dot_neg_left, dot_neg_left]
  have := hmin z hz
  exact_mod_cast (by linarith : -dot cg.nJ z ≤ -dot cg.nJ a₀)

/-- **The `ℓ'`-face is the `n_J`-minimal level set**, for the `e` with
`cutNormal e v_J = toReal (-n_J)` (`Claim411.exists_cutNormal_eq`). -/
theorem topFace_eq_filter_min (cg : ChainDataGeom ξ xper vl p S gen)
    {Sgen : Finset (ℤ × ℤ)} (hne : Sgen.Nonempty) {e : Bool}
    (he : L1Data.cutNormal e cg.vJ = toReal (-cg.nJ))
    {a₀ : ℤ × ℤ} (ha₀ : a₀ ∈ Sgen) (hmin : ∀ w ∈ Sgen, dot cg.nJ a₀ ≤ dot cg.nJ w) :
    L1Data.topFace e cg.vJ Sgen = Sgen.filter fun w => dot cg.nJ w = dot cg.nJ a₀ := by
  unfold L1Data.topFace
  rw [he, levelMax_neg_nJ cg hne ha₀ hmin]
  unfold Nivat.R2.face
  refine Finset.filter_congr fun w _ => ?_
  rw [inner2_toReal, inner2_toReal, Int.cast_inj, dot_neg_left, dot_neg_left, neg_inj]

/-- **Collé's (4.1) run** (`b3_colle2.txt:637`): a point `q` of `Sgen` strictly above the
`n_J`-minimal level carrying `|face| - 1` consecutive `v_J`-points, from Lemma 2.3 through
`L1Data.maxB_wide` at `u := vl`. -/
theorem exists_run (cg : ChainDataGeom ξ xper vl p S gen)
    {Sgen : Finset (ℤ × ℤ)} (hSgen : IsGeneratingSet ξ Sgen)
    (hvl_prim : Primitive vl) (hdet_vl : det p vl = 0)
    {ℓ : ℤ × ℤ} (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hdet_ℓ : dot ℓ vl = 0)
    {a₀ : ℤ × ℤ} (ha₀ : a₀ ∈ Sgen) (hmin : ∀ w ∈ Sgen, dot cg.nJ a₀ ≤ dot cg.nJ w) :
    ∃ q ∈ Sgen, dot cg.nJ a₀ < dot cg.nJ q ∧
      ∀ i : ℕ, i < (Sgen.filter fun w => dot cg.nJ w = dot cg.nJ a₀).card - 1 →
        q + (i : ℤ) • cg.vJ ∈ Sgen := by
  have hne : Sgen.Nonempty := hSgen.1
  have hS : LatticeConvex Sgen := hSgen.2.1
  have hdet := det_vl_vJ_ne_zero cg hvl_prim hdet_vl
  obtain ⟨h2t, h2b⟩ := two_le_faces_vl hSgen hvl_prim hℓ_nel hℓ_pos hℓ_neg hdet_ℓ
  obtain ⟨e, he⟩ := exists_cutNormal_eq cg
  obtain ⟨b₀, w, -, hrun⟩ := L1Data.maxB_wide hS hne hvl_prim cg.vJ_prim hdet e
  have hb₀ := hrun 0 (by omega)
  simp only [Nat.cast_zero, zero_smul, add_zero] at hb₀
  obtain ⟨hb₀Q, hb₀run⟩ := L1Data.mem_maxB.mp hb₀
  have hsub : L1Data.derivedQ e cg.vJ Sgen ⊆ Sgen := by
    unfold L1Data.derivedQ; exact Finset.filter_subset _ _
  have hface := topFace_eq_filter_min cg hne he ha₀ hmin
  refine ⟨b₀, hsub hb₀Q, ?_, ?_⟩
  · have h := (Finset.mem_filter.mp hb₀Q).2
    rw [he, levelMax_neg_nJ cg hne ha₀ hmin, inner2_toReal, inner2_toReal, dot_neg_left,
      dot_neg_left] at h
    have h' : -dot cg.nJ b₀ < -dot cg.nJ a₀ := by exact_mod_cast h
    linarith
  · intro i hi
    rw [← hface] at hi
    exact hsub (hb₀run i hi)

end Nivat.ColleReg.C11Bridge

section AxiomReceipts

#print axioms Nivat.ColleReg.C11Bridge.det_vl_vJ_ne_zero
#print axioms Nivat.ColleReg.C11Bridge.perp_vl_mem_ONED
#print axioms Nivat.ColleReg.C11Bridge.two_le_faces_vl
#print axioms Nivat.ColleReg.C11Bridge.levelMax_neg_nJ
#print axioms Nivat.ColleReg.C11Bridge.topFace_eq_filter_min
#print axioms Nivat.ColleReg.C11Bridge.exists_run

end AxiomReceipts
