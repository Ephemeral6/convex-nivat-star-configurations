/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.PolyChain
import Nivat.External.Colle.PolyChainSum
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.WindowFit
import Nivat.External.Colle.ZonoEdgeGen
import Nivat.External.Colle.Claim47Core
import Nivat.External.Colle.L1RegionBuild

/-!
# `HsuppCaseCW` — the clockwise sub-case of Part (E), `blueprint/LEAF-HSUPP.md` §2(E)

Lane `lane-hsupp`, assigned by team-lead 2026-09-22: prove

```
theorem case_pos_cw : 0 < det n (-nℓ) →
  (∑ j ∈ univ.erase i, max 0 (dot n (orientUp (h j) nℓ))) ≤ suppVal B n - dot n g
```

against `tmp/wip/HsuppAssemble.lean`'s scope (`lane-chain`), reusing the now-landed
`Nivat.External.Colle.PolyChain` (parts (A)(B)(C)) and `Nivat.External.Colle.PolyChainSum`
(part (D), `chain_cw_scalar_final`).

## Status

DONE. `case_pos_cw` fully proved, 0 `sorry`, `#print axioms` clean
(`[propext, Classical.choice, Quot.sound]`). §1 (the `g ↔ faceStart/faceEnd B (-nℓ)`
bridge) and §2 (the `ν_j`/`nuC`/gcd length bound + final assembly) both landed.
-/

namespace Nivat.HsuppCaseCW

open Nivat Nivat.LE2 Nivat.ColleReg Nivat.Colle35 Finset Classical Pointwise

variable {ξ : Config ℤ} (d : DecompDataZ ξ)
variable {B : Set (ℤ × ℤ)} (hBfin : B.Finite) (hBne : B.Nonempty)
variable (hareaB : Nivat.LE2.PosArea B) (hlcB : Nivat.IsLatticeConvexRegion B)
variable {vl nℓ u' : ℤ × ℤ}
variable (hprim : Nivat.LE2.Prim nℓ) (hperp : Nivat.LE2.dot nℓ vl = 0)
variable {i : Fin d.toDecompData.m} (hdoth : Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0)
variable (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hnu : Nivat.LE2.dot nℓ u' = -1)
variable {cz : ℤ}
variable {Sphi : Set (ℤ × ℤ)}
variable (hEeq : Nivat.LE2.E B = Nivat.LE2.E Sphi)
variable (hnℓ_neg_mem : -nℓ ∈ Nivat.LE2.E Sphi)

/-! ## §1. The `g ↔ faceStart/faceEnd B (-nℓ)` bridge -/

/-- Rotation by `dir` preserves the dot product. -/
theorem dot_dir_dir (a b : ℤ × ℤ) : Nivat.LE2.dot (Nivat.LE2.dir a) (Nivat.LE2.dir b) =
    Nivat.LE2.dot a b := by
  simp only [Nivat.LE2.dot, Nivat.LE2.dir]; ring

include hEeq hnℓ_neg_mem in
/-- `-nℓ ∈ E B`: free from `hEeq` and `hnℓ_neg_mem`. -/
theorem negnl_mem_EB : -nℓ ∈ Nivat.LE2.E B := by rw [hEeq]; exact hnℓ_neg_mem

/-- `g ∈ face B (-nℓ)`: `g` is `dot nℓ`-minimal on `B` (from `hgcz`/`hgle`), i.e.
`dot (-nℓ)`-maximal, i.e. in the face. -/
theorem g_mem_face_negnl {g : ℤ × ℤ} (hgB : g ∈ B) (hgcz : Nivat.LE2.dot nℓ g = cz)
    (hgle : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b) : g ∈ Nivat.LE2.face B (-nℓ) := by
  refine ⟨hgB, fun y hy => ?_⟩
  have h1 : cz ≤ Nivat.LE2.dot nℓ y := hgle y hy
  have h2 : Nivat.LE2.dot (-nℓ) y = - Nivat.LE2.dot nℓ y := Nivat.LE2.dot_neg_left nℓ y
  have h3 : Nivat.LE2.dot (-nℓ) g = - Nivat.LE2.dot nℓ g := Nivat.LE2.dot_neg_left nℓ g
  rw [h2, h3, hgcz]; omega

include hnu in
/-- The key linear identity: `dot (expNormal u' vl) (dir (-nℓ)) = det u' vl`. Direct
component computation from `hnu : dot nℓ u' = -1`. -/
theorem dot_expNormal_dir_negnl :
    Nivat.LE2.dot (expNormal u' vl) (Nivat.LE2.dir (-nℓ)) = det u' vl := by
  have hnu' : nℓ.1 * u'.1 + nℓ.2 * u'.2 = -1 := hnu
  simp only [Nivat.LE2.dot, Nivat.LE2.dir, expNormal, Prod.fst_neg, Prod.snd_neg,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination (-(det u' vl)) * hnu'

include hBfin hlcB hEeq hnℓ_neg_mem hnu in
/-- **The bridge lemma.** Under `det u' vl = 1`, `g = faceStart B (-nℓ)`; under
`det u' vl = -1`, `g` is the *other* end of the face,
`faceStart B (-nℓ) + (faceLen B (-nℓ) : ℤ) • dir (-nℓ)`. -/
theorem g_eq_faceStart_or_faceEnd {g : ℤ × ℤ} (hgB : g ∈ B) (hgcz : Nivat.LE2.dot nℓ g = cz)
    (hgle : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b)
    (hgmin : ∀ b ∈ B, Nivat.LE2.dot nℓ b = cz →
      Nivat.LE2.dot (expNormal u' vl) g ≤ Nivat.LE2.dot (expNormal u' vl) b) :
    (det u' vl = 1 → g = Nivat.PolyChain.faceStart B (-nℓ)) ∧
    (det u' vl = -1 → g = Nivat.PolyChain.faceStart B (-nℓ) +
      (Nivat.PolyChain.faceLen B (-nℓ) : ℤ) • Nivat.LE2.dir (-nℓ)) := by
  have hnmem : -nℓ ∈ Nivat.LE2.E B := negnl_mem_EB hEeq hnℓ_neg_mem
  have hgface : g ∈ Nivat.LE2.face B (-nℓ) := g_mem_face_negnl hgB hgcz hgle
  have hgmax : ∀ y ∈ B, Nivat.LE2.dot (-nℓ) y ≤ Nivat.LE2.dot (-nℓ) g := hgface.2
  have hseg := Nivat.PolyChain.face_eq_segment hlcB hBfin hnmem
  have hgface' := hgface
  rw [hseg] at hgface'
  obtain ⟨t0, ht0le, ht0eq⟩ := hgface'
  have hmemOfT : ∀ t : ℕ, t ≤ Nivat.PolyChain.faceLen B (-nℓ) →
      Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ) ∈
        Nivat.LE2.face B (-nℓ) := by
    intro t htle; rw [hseg]; exact ⟨t, htle, rfl⟩
  have hlevel : ∀ t : ℕ, t ≤ Nivat.PolyChain.faceLen B (-nℓ) →
      Nivat.LE2.dot nℓ (Nivat.PolyChain.faceStart B (-nℓ) +
        (t : ℤ) • Nivat.LE2.dir (-nℓ)) = cz := by
    intro t htle
    have hmemt := hmemOfT t htle
    have hmemB : Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ) ∈ B :=
      hmemt.1
    -- both `pt` and `g` lie in `face B (-nℓ)`, so they achieve the same `dot (-nℓ)` value.
    have h1 : Nivat.LE2.dot (-nℓ) g ≤ Nivat.LE2.dot (-nℓ)
        (Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ)) :=
      hmemt.2 g hgB
    have h2 : Nivat.LE2.dot (-nℓ)
        (Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ)) ≤
        Nivat.LE2.dot (-nℓ) g := hgmax _ hmemB
    have heq : Nivat.LE2.dot (-nℓ)
        (Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ)) =
        Nivat.LE2.dot (-nℓ) g := le_antisymm h2 h1
    have e1 : Nivat.LE2.dot (-nℓ)
        (Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ)) =
        - Nivat.LE2.dot nℓ
          (Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ)) :=
      Nivat.LE2.dot_neg_left nℓ _
    have e2 : Nivat.LE2.dot (-nℓ) g = - Nivat.LE2.dot nℓ g := Nivat.LE2.dot_neg_left nℓ g
    rw [e1, e2] at heq
    omega
  have hexp : ∀ t : ℕ, t ≤ Nivat.PolyChain.faceLen B (-nℓ) →
      Nivat.LE2.dot (expNormal u' vl)
        (Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ)) =
      Nivat.LE2.dot (expNormal u' vl) (Nivat.PolyChain.faceStart B (-nℓ)) +
        (t : ℤ) * det u' vl := by
    intro t _
    rw [Nivat.LE2.dot_add, Nivat.PolyChainSum.dot_zsmul_right, dot_expNormal_dir_negnl hnu]
  constructor
  · intro hbranch
    have hforall : ∀ t : ℕ, t ≤ Nivat.PolyChain.faceLen B (-nℓ) → (t0 : ℤ) ≤ (t : ℤ) := by
      intro t htle
      have hmemB : Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ) ∈ B :=
        (hmemOfT t htle).1
      have hlevt := hlevel t htle
      have hmin := hgmin _ hmemB hlevt
      rw [ht0eq, hexp t0 ht0le, hexp t htle, hbranch] at hmin
      linarith
    have ht00 : t0 = 0 := by have := hforall 0 (Nat.zero_le _); omega
    rw [ht0eq, ht00]; simp
  · intro hbranch
    have hforall : ∀ t : ℕ, t ≤ Nivat.PolyChain.faceLen B (-nℓ) → (t : ℤ) ≤ (t0 : ℤ) := by
      intro t htle
      have hmemB : Nivat.PolyChain.faceStart B (-nℓ) + (t : ℤ) • Nivat.LE2.dir (-nℓ) ∈ B :=
        (hmemOfT t htle).1
      have hlevt := hlevel t htle
      have hmin := hgmin _ hmemB hlevt
      rw [ht0eq, hexp t0 ht0le, hexp t htle, hbranch] at hmin
      linarith
    have ht0max : t0 = Nivat.PolyChain.faceLen B (-nℓ) := by
      have := hforall (Nivat.PolyChain.faceLen B (-nℓ)) (le_refl _)
      omega
    rw [ht0eq, ht0max]


/-! ## §2. The clockwise chain: `ν_j`, injectivity, the `gcd` length bound, assembly -/

open Nivat.Colle35 in
/-- Generic 2-point face of a zonotope, for **any** edge normal `ν` orthogonal to some
generator `h j` (not just `genPerp' (h j)` itself). Same proof as
`Nivat.LE2.face_encard_zonoF`, generalised away from the sign built into `genPerp'`. -/
theorem face_zonoF_eq_pair {mm : ℕ} (hgen : Fin mm → ℤ × ℤ)
    (h_ne : ∀ k, hgen k ≠ 0) (h_dir : ∀ j k, j ≠ k → det (hgen j) (hgen k) ≠ 0)
    {ν : ℤ × ℤ} (hνne : ν ≠ 0) {j : Fin mm} (hj_orth : Nivat.LE2.dot ν (hgen j) = 0) :
    Nivat.LE2.face (↑(Nivat.LE2.zonoF Finset.univ hgen) : Set (ℤ × ℤ)) ν =
      {(∑ k ∈ (Finset.univ : Finset (Fin mm)).erase j,
          (if 0 < Nivat.LE2.dot ν (hgen k) then hgen k else 0)),
       (∑ k ∈ (Finset.univ : Finset (Fin mm)).erase j,
          (if 0 < Nivat.LE2.dot ν (hgen k) then hgen k else 0)) + hgen j} := by
  have hk_orth : ∀ k, k ≠ j → Nivat.LE2.dot ν (hgen k) ≠ 0 := fun k hkj hk =>
    hkj (Nivat.LE2.at_most_one_orthogonal hgen h_dir ν hνne k j hk hj_orth)
  set x : ℤ × ℤ := ∑ k ∈ ((Finset.univ : Finset (Fin mm)).erase j),
      (if 0 < Nivat.LE2.dot ν (hgen k) then hgen k else 0) with hxdef
  have hrest : ∑ k ∈ ((Finset.univ : Finset (Fin mm)).erase j),
      Nivat.LE2.face (Nivat.LE2.segOf (hgen k)) ν = {x} := by
    rw [← Nivat.LE2.sum_singleton_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    rw [Nivat.LE2.face_segOf_cases, if_neg (hk_orth k hkj)]
    split_ifs <;> rfl
  rw [Nivat.LE2.coe_zonoF, Nivat.LE2.face_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    hrest, Nivat.LE2.face_segOf_cases, if_pos hj_orth]
  simp only [Nivat.LE2.segOf, Set.singleton_add, Set.image_insert_eq, Set.image_singleton, add_zero]

/-- `primPart` is odd (holds even at `0`, where both sides are `0` by convention). -/
theorem primPart_neg (w : ℤ × ℤ) : Nivat.LE2.primPart (-w) = - Nivat.LE2.primPart w := by
  by_cases hw : w = 0
  · simp [hw, Nivat.LE2.primPart]
  set G : ℤ := (Int.gcd w.1 w.2 : ℤ) with hGdef
  have hGdvd1 : G ∣ w.1 := hGdef ▸ Int.gcd_dvd_left w.1 w.2
  have hGdvd2 : G ∣ w.2 := hGdef ▸ Int.gcd_dvd_right w.1 w.2
  have hGne0 : G ≠ 0 := by
    intro hz
    apply hw
    have hz' : Int.gcd w.1 w.2 = 0 := by rw [hGdef] at hz; exact_mod_cast hz
    rcases Int.gcd_eq_zero_iff.mp hz' with ⟨h1, h2⟩
    exact Prod.ext h1 h2
  have hGeq : (Int.gcd (-w).1 (-w).2 : ℤ) = G := by
    rw [hGdef]
    show (Int.gcd (-w.1) (-w.2) : ℤ) = (Int.gcd w.1 w.2 : ℤ)
    congr 1
    unfold Int.gcd; simp
  have hdiv1 : (-w).1 / G = -(w.1 / G) := by
    obtain ⟨k, hk⟩ := hGdvd1
    have hk1 : w.1 / G = k := by rw [hk]; exact Int.mul_ediv_cancel_left k hGne0
    have hk2 : (-w).1 / G = -k := by
      rw [Prod.fst_neg, hk, show -(G * k) = G * (-k) by ring]
      exact Int.mul_ediv_cancel_left (-k) hGne0
    rw [hk1, hk2]
  have hdiv2 : (-w).2 / G = -(w.2 / G) := by
    obtain ⟨k, hk⟩ := hGdvd2
    have hk1 : w.2 / G = k := by rw [hk]; exact Int.mul_ediv_cancel_left k hGne0
    have hk2 : (-w).2 / G = -k := by
      rw [Prod.snd_neg, hk, show -(G * k) = G * (-k) by ring]
      exact Int.mul_ediv_cancel_left (-k) hGne0
    rw [hk1, hk2]
  ext
  · show (-w).1 / (Int.gcd (-w).1 (-w).2 : ℤ) = -(w.1 / (Int.gcd w.1 w.2 : ℤ))
    rw [hGeq, ← hGdef]; exact hdiv1
  · show (-w).2 / (Int.gcd (-w).1 (-w).2 : ℤ) = -(w.2 / (Int.gcd w.1 w.2 : ℤ))
    rw [hGeq, ← hGdef]; exact hdiv2

/-- `genPerp'` is odd. -/
theorem genPerp'_neg (v : ℤ × ℤ) :
    Nivat.LE2.genPerp' (-v) = - Nivat.LE2.genPerp' v := by
  have hdirneg : Nivat.LE2.dir (-v) = - Nivat.LE2.dir v := by
    simp only [Nivat.LE2.dir]; ext <;> simp
  show Nivat.LE2.primPart (Nivat.LE2.dir (-v)) = - Nivat.LE2.primPart (Nivat.LE2.dir v)
  rw [hdirneg, primPart_neg]


/-! ## §2c. Small identities: `det` antisymmetry, `dot`-`dir` pairing, `primPart` scaling -/

theorem det_antisymm (a b : ℤ × ℤ) : det a b = - det b a := by
  simp only [det]; ring

theorem dot_dir_eq_det (x ν : ℤ × ℤ) : Nivat.LE2.dot x (Nivat.LE2.dir ν) = det ν x := by
  simp only [Nivat.LE2.dot, Nivat.LE2.dir, det]; ring

theorem dot_neg_right (a b : ℤ × ℤ) : Nivat.LE2.dot a (-b) = - Nivat.LE2.dot a b := by
  simp only [Nivat.LE2.dot, Prod.fst_neg, Prod.snd_neg]; ring

theorem primPart_scale (z : ℤ × ℤ) :
    z = (Int.gcd z.1 z.2 : ℤ) • Nivat.LE2.primPart z := by
  unfold Nivat.LE2.primPart
  ext
  · simp only [Prod.smul_fst, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left z.1 z.2)).symm
  · simp only [Prod.smul_snd, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right z.1 z.2)).symm

theorem dir_genPerp' {v : ℤ × ℤ} (hv : v ≠ 0) :
    Nivat.LE2.dir (Nivat.LE2.genPerp' v) = - Nivat.LE2.primPart v := by
  set G : ℤ := (Int.gcd v.1 v.2 : ℤ) with hGdef
  have hGdvd2 : G ∣ v.2 := hGdef ▸ Int.gcd_dvd_right (a := v.1) (b := v.2)
  have hGne0 : G ≠ 0 := by
    intro hz
    rw [hGdef] at hz
    apply hv
    have hz' : Int.gcd v.1 v.2 = 0 := by exact_mod_cast hz
    rcases Int.gcd_eq_zero_iff.mp hz' with ⟨h1, h2⟩
    exact Prod.ext h1 h2
  have hGeq : (Int.gcd (-v.2) v.1 : ℤ) = G := by
    have h1 : Int.gcd (-v.2) v.1 = Int.gcd v.2 v.1 := by unfold Int.gcd; simp
    rw [h1, Int.gcd_comm]
  have hdivneg : (-v.2) / G = -(v.2 / G) := by
    obtain ⟨k, hk⟩ := hGdvd2
    have hk1 : v.2 / G = k := by rw [hk]; exact Int.mul_ediv_cancel_left k hGne0
    have hk2 : (-v.2) / G = -k := by
      rw [hk, show -(G * k) = G * (-k) by ring]
      exact Int.mul_ediv_cancel_left (-k) hGne0
    rw [hk1, hk2]
  show Nivat.LE2.dir (Nivat.LE2.primPart (Nivat.LE2.dir v)) = - Nivat.LE2.primPart v
  ext
  · show -(Nivat.LE2.primPart (Nivat.LE2.dir v)).2 = -(Nivat.LE2.primPart v).1
    show -(v.1 / (Int.gcd (-v.2) v.1 : ℤ)) = -(v.1 / G)
    rw [hGeq]
  · show (Nivat.LE2.primPart (Nivat.LE2.dir v)).1 = -(Nivat.LE2.primPart v).2
    show (-v.2) / (Int.gcd (-v.2) v.1 : ℤ) = -(v.2 / G)
    rw [hGeq]; exact hdivneg

theorem gcd_neg_neg (a b : ℤ) : Int.gcd (-a) (-b) = Int.gcd a b := by
  unfold Int.gcd; simp

theorem mem_face_of_dot_eq {T : Set (ℤ × ℤ)} {n z w : ℤ × ℤ}
    (hz : z ∈ Nivat.LE2.face T n) (hw : w ∈ T) (heq : Nivat.LE2.dot n w = Nivat.LE2.dot n z) :
    w ∈ Nivat.LE2.face T n :=
  ⟨hw, fun y hy => heq ▸ hz.2 y hy⟩

theorem mem_face_of_Conv_eq {S T : Finset (ℤ × ℤ)} (hConv : Conv S = Conv T) (n : ℤ × ℤ)
    {a : ℤ × ℤ} (ha : a ∈ Nivat.LE2.face (↑S : Set (ℤ × ℤ)) n) (haT : a ∈ T) :
    a ∈ Nivat.LE2.face (↑T : Set (ℤ × ℤ)) n := by
  refine ⟨haT, fun y hy => ?_⟩
  have hA : ∀ z ∈ Conv S, Nivat.LE2.rdot (toReal n) z ≤ ((Nivat.LE2.dot n a : ℤ) : ℝ) :=
    Nivat.LE2.Conv_subset_halfSpace (fun z hz => ha.2 z hz)
  have hy' := hA (toReal y) (hConv ▸ subset_Conv hy)
  rw [Nivat.LE2.rdot_toReal] at hy'
  exact_mod_cast hy'

variable (nℓ)

/-! ## §2d. `uGen`, `nuC`, and their basic facts -/

include d in
/-- The oriented generator `u_j := orientUp (h j) nℓ`. -/
noncomputable def uGen (j : Fin d.toDecompData.m) : ℤ × ℤ :=
  Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ

include d in
/-- The clockwise per-generator edge normal: `nuC j := genPerp' (u_j)`. -/
noncomputable def nuC (j : Fin d.toDecompData.m) : ℤ × ℤ :=
  Nivat.LE2.genPerp' (uGen d nℓ j)

include d in
theorem uGen_cases (j : Fin d.toDecompData.m) :
    uGen d nℓ j = d.toDecompData.h j ∨ uGen d nℓ j = -(d.toDecompData.h j) := by
  unfold uGen Nivat.ColleReg.orientUp
  split_ifs with h
  · right; rfl
  · left; rfl

include d in
theorem uGen_ne_zero (j : Fin d.toDecompData.m) : uGen d nℓ j ≠ 0 := by
  rcases uGen_cases d nℓ j with hc | hc <;> rw [hc]
  · exact d.toDecompData.h_ne j
  · exact neg_ne_zero.mpr (d.toDecompData.h_ne j)

include d in
theorem nuC_ne_zero (j : Fin d.toDecompData.m) : nuC d nℓ j ≠ 0 :=
  (Nivat.LE2.genPerp'_prim (uGen_ne_zero d nℓ j)).ne_zero

include d in
theorem dot_nuC_h (j : Fin d.toDecompData.m) :
    Nivat.LE2.dot (nuC d nℓ j) (d.toDecompData.h j) = 0 := by
  have h0 : Nivat.LE2.dot (uGen d nℓ j) (nuC d nℓ j) = 0 :=
    Nivat.LE2.dot_genPerp' (uGen_ne_zero d nℓ j)
  have h1 : Nivat.LE2.dot (nuC d nℓ j) (uGen d nℓ j) = 0 := by
    rw [Nivat.LE2.dot_comm]; exact h0
  rcases uGen_cases d nℓ j with hc | hc
  · rwa [hc] at h1
  · rw [hc, dot_neg_right] at h1; linarith

include d in
theorem nuC_inj ⦃j k : Fin d.toDecompData.m⦄ (heq : nuC d nℓ j = nuC d nℓ k) : j = k := by
  have hj : Nivat.LE2.dot (nuC d nℓ j) (d.toDecompData.h j) = 0 := dot_nuC_h d nℓ j
  have hk : Nivat.LE2.dot (nuC d nℓ j) (d.toDecompData.h k) = 0 := by
    rw [heq]; exact dot_nuC_h d nℓ k
  exact Nivat.LE2.at_most_one_orthogonal d.toDecompData.h d.toDecompData.h_dir
    (nuC d nℓ j) (nuC_ne_zero d nℓ j) j k hj hk

/-! ## §2e. `Sphi` transport: `zonoF univ h` embeds in `Sphi` -/

include d in
theorem Econv_zonoF_Sphi :
    Conv (Nivat.LE2.zonoF Finset.univ d.toDecompData.h) = Conv d.toDecompData.Sphi := by
  rw [← Nivat.LE2.Conv_supp_prod_eq_Conv_zonoF Finset.univ d.toDecompData.h
    (fun i _ => d.toDecompData.h_ne i), d.toDecompData.Sphi_eq]

include d in
theorem zonoF_subset_Sphi :
    (Nivat.LE2.zonoF Finset.univ d.toDecompData.h : Finset (ℤ × ℤ)) ⊆ d.toDecompData.Sphi :=
  fun z hz => d.Sphi_conv z ((Econv_zonoF_Sphi d) ▸ subset_Conv hz)

variable (hEeqD : Nivat.LE2.E B = Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)))
variable (henv : ∀ ν ∈ Nivat.LE2.E B,
  (Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ν).encard ≤
    (Nivat.LE2.face B ν).encard)

include d in
theorem nuC_mem_E_zonoF (j : Fin d.toDecompData.m) :
    nuC d nℓ j ∈ Nivat.LE2.E (↑(Nivat.LE2.zonoF Finset.univ d.toDecompData.h) : Set (ℤ × ℤ)) := by
  rcases uGen_cases d nℓ j with hc | hc
  · have he : nuC d nℓ j = Nivat.LE2.genPerp' (d.toDecompData.h j) := by unfold nuC; rw [hc]
    rw [he]
    exact (Nivat.LE2.mem_E_zonoF d.toDecompData.h d.toDecompData.h_ne d.toDecompData.h_dir j).1
  · have he : nuC d nℓ j = - Nivat.LE2.genPerp' (d.toDecompData.h j) := by
      unfold nuC; rw [hc, genPerp'_neg]
    rw [he]
    exact (Nivat.LE2.mem_E_zonoF d.toDecompData.h d.toDecompData.h_ne d.toDecompData.h_dir j).2

include hEeqD in
theorem nuC_mem_EB (j : Fin d.toDecompData.m) : nuC d nℓ j ∈ Nivat.LE2.E B := by
  rw [hEeqD, ← Nivat.LE2.E_congr_of_Conv_eq (Econv_zonoF_Sphi d)]
  exact nuC_mem_E_zonoF d nℓ j

/-! ## §2f. The `gcd` scaling identity and the sign/positivity chain -/

include d in
noncomputable def gcdU (j : Fin d.toDecompData.m) : ℤ :=
  (Int.gcd (uGen d nℓ j).1 (uGen d nℓ j).2 : ℤ)

include d in
noncomputable def gcdH (j : Fin d.toDecompData.m) : ℤ :=
  (Int.gcd (d.toDecompData.h j).1 (d.toDecompData.h j).2 : ℤ)

include d in
theorem gcdU_pos (j : Fin d.toDecompData.m) : 0 < gcdU d nℓ j := by
  unfold gcdU
  have hne := uGen_ne_zero d nℓ j
  have hg0 : Int.gcd (uGen d nℓ j).1 (uGen d nℓ j).2 ≠ 0 := by
    intro h0
    rcases Int.gcd_eq_zero_iff.mp h0 with ⟨h1, h2⟩
    exact hne (Prod.ext h1 h2)
  exact_mod_cast Nat.pos_of_ne_zero hg0

include d in
theorem gcdH_pos (j : Fin d.toDecompData.m) : 0 < gcdH d j := by
  unfold gcdH
  have hne := d.toDecompData.h_ne j
  have hg0 : Int.gcd (d.toDecompData.h j).1 (d.toDecompData.h j).2 ≠ 0 := by
    intro h0
    rcases Int.gcd_eq_zero_iff.mp h0 with ⟨h1, h2⟩
    exact hne (Prod.ext h1 h2)
  exact_mod_cast Nat.pos_of_ne_zero hg0

include d in
theorem gcdU_eq_gcdH (j : Fin d.toDecompData.m) : gcdU d nℓ j = gcdH d j := by
  unfold gcdU gcdH
  rcases uGen_cases d nℓ j with hc | hc
  · rw [hc]
  · rw [hc, Prod.fst_neg, Prod.snd_neg]
    exact_mod_cast gcd_neg_neg (d.toDecompData.h j).1 (d.toDecompData.h j).2

include d in
theorem uGen_eq_neg_gcdU_smul_dir (j : Fin d.toDecompData.m) :
    uGen d nℓ j = (-(gcdU d nℓ j)) • Nivat.LE2.dir (nuC d nℓ j) := by
  have h1 : uGen d nℓ j = gcdU d nℓ j • Nivat.LE2.primPart (uGen d nℓ j) := by
    unfold gcdU; exact primPart_scale (uGen d nℓ j)
  have h2 : Nivat.LE2.dir (nuC d nℓ j) = - Nivat.LE2.primPart (uGen d nℓ j) :=
    dir_genPerp' (uGen_ne_zero d nℓ j)
  rw [h1, h2]
  simp [neg_smul, smul_neg]

include d in
theorem dot_n_uGen_eq (n : ℤ × ℤ) (j : Fin d.toDecompData.m) :
    Nivat.LE2.dot n (uGen d nℓ j) = gcdU d nℓ j * det n (nuC d nℓ j) := by
  rw [uGen_eq_neg_gcdU_smul_dir d nℓ j, Nivat.PolyChainSum.dot_zsmul_right,
    dot_dir_eq_det n (nuC d nℓ j), det_antisymm n (nuC d nℓ j)]
  ring

include d in
theorem dot_nℓ_uGen_eq (j : Fin d.toDecompData.m) :
    Nivat.LE2.dot nℓ (uGen d nℓ j) = gcdU d nℓ j * det (nuC d nℓ j) (-nℓ) := by
  have hneg : det (nuC d nℓ j) (-nℓ) = - det (nuC d nℓ j) nℓ := by
    simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  rw [uGen_eq_neg_gcdU_smul_dir d nℓ j, Nivat.PolyChainSum.dot_zsmul_right,
    dot_dir_eq_det nℓ (nuC d nℓ j), hneg]
  ring

include d in
theorem dot_nℓ_uGen_nonneg (j : Fin d.toDecompData.m) : 0 ≤ Nivat.LE2.dot nℓ (uGen d nℓ j) := by
  unfold uGen Nivat.ColleReg.orientUp
  by_cases hc : Nivat.LE2.dot nℓ (d.toDecompData.h j) < 0
  · rw [if_pos hc, dot_neg_right]; omega
  · rw [if_neg hc]; push_neg at hc; omega

include hprim hdoth in
theorem dot_nℓ_uGen_pos (j : Fin d.toDecompData.m) (hji : j ≠ i) :
    0 < Nivat.LE2.dot nℓ (uGen d nℓ j) := by
  rcases (dot_nℓ_uGen_nonneg d nℓ j).lt_or_eq with h | h
  · exact h
  · exfalso
    have hzero : Nivat.LE2.dot nℓ (uGen d nℓ j) = 0 := h.symm
    have hj0 : Nivat.LE2.dot nℓ (d.toDecompData.h j) = 0 := by
      rcases uGen_cases d nℓ j with hc | hc
      · rw [hc] at hzero; exact hzero
      · rw [hc, dot_neg_right] at hzero; linarith
    have hnℓne : nℓ ≠ 0 := hprim.ne_zero
    have heqij := Nivat.LE2.at_most_one_orthogonal d.toDecompData.h d.toDecompData.h_dir
      nℓ hnℓne i j hdoth hj0
    exact hji heqij.symm

include hprim hdoth in
theorem det_nuC_negnl_pos (j : Fin d.toDecompData.m) (hji : j ≠ i) :
    0 < det (nuC d nℓ j) (-nℓ) := by
  have heq := dot_nℓ_uGen_eq d nℓ j
  have hpos := dot_nℓ_uGen_pos d nℓ hprim hdoth j hji
  have hg := gcdU_pos d nℓ j
  nlinarith [heq, hpos, hg]

/-! ## §2g. The `gcd` length bound: `gcdH d j ≤ faceLen B (nuC d nℓ j)` -/

include d hEeqD henv hBfin in
theorem gcd_le_faceLen (j : Fin d.toDecompData.m) :
    gcdH d j ≤ (Nivat.PolyChain.faceLen B (nuC d nℓ j) : ℤ) := by
  have hνne := nuC_ne_zero d nℓ j
  have hjorth := dot_nuC_h d nℓ j
  have hface := face_zonoF_eq_pair d.toDecompData.h d.toDecompData.h_ne d.toDecompData.h_dir
    hνne hjorth
  set x : ℤ × ℤ := ∑ k ∈ (Finset.univ : Finset (Fin d.toDecompData.m)).erase j,
    (if 0 < Nivat.LE2.dot (nuC d nℓ j) (d.toDecompData.h k) then d.toDecompData.h k else 0)
    with hxdef
  have hx_mem : x ∈ Nivat.LE2.face
      (↑(Nivat.LE2.zonoF Finset.univ d.toDecompData.h) : Set (ℤ × ℤ)) (nuC d nℓ j) := by
    rw [hface]; exact Set.mem_insert _ _
  have hx2_mem : x + d.toDecompData.h j ∈ Nivat.LE2.face
      (↑(Nivat.LE2.zonoF Finset.univ d.toDecompData.h) : Set (ℤ × ℤ)) (nuC d nℓ j) := by
    rw [hface]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hxSphi : x ∈ d.toDecompData.Sphi :=
    zonoF_subset_Sphi d (Finset.mem_coe.mp hx_mem.1)
  have hx2Sphi : x + d.toDecompData.h j ∈ d.toDecompData.Sphi :=
    zonoF_subset_Sphi d (Finset.mem_coe.mp hx2_mem.1)
  have hx_faceSphi : x ∈ Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) (nuC d nℓ j) :=
    mem_face_of_Conv_eq (Econv_zonoF_Sphi d) (nuC d nℓ j) hx_mem hxSphi
  -- the primitive step vector along `h j`, and the "same face" fact.
  have hpjne : Nivat.LE2.primPart (d.toDecompData.h j) ≠ 0 :=
    (Nivat.LE2.primPart_spec (d.toDecompData.h_ne j)).1.ne_zero
  have hpj_orth : Nivat.LE2.dot (nuC d nℓ j) (Nivat.LE2.primPart (d.toDecompData.h j)) = 0 := by
    have hscale : d.toDecompData.h j = gcdH d j • Nivat.LE2.primPart (d.toDecompData.h j) := by
      unfold gcdH; exact primPart_scale (d.toDecompData.h j)
    have h1 : Nivat.LE2.dot (nuC d nℓ j) (d.toDecompData.h j) =
        gcdH d j * Nivat.LE2.dot (nuC d nℓ j) (Nivat.LE2.primPart (d.toDecompData.h j)) := by
      conv_lhs => rw [hscale]
      exact Nivat.PolyChainSum.dot_zsmul_right _ _ _
    rw [hjorth] at h1
    have hgne : gcdH d j ≠ 0 := (gcdH_pos d j).ne'
    rcases mul_eq_zero.mp h1.symm with h2 | h2
    · exact absurd h2 hgne
    · exact h2
  set v : ℤ × ℤ := Nivat.LE2.primPart (d.toDecompData.h j) with hvdef
  have hstep : ∀ t : ℕ, t ≤ (gcdH d j).toNat → x + (t : ℤ) • v ∈ d.toDecompData.Sphi := by
    intro t ht
    have ht' : (t : ℤ) ≤ gcdH d j := by
      have h0 : (t : ℤ) ≤ ((gcdH d j).toNat : ℤ) := by exact_mod_cast ht
      rwa [Int.toNat_of_nonneg (gcdH_pos d j).le] at h0
    have ha : x + (0 : ℤ) • v ∈ d.toDecompData.Sphi := by simpa using hxSphi
    have hb : x + gcdH d j • v ∈ d.toDecompData.Sphi := by
      have hscale : d.toDecompData.h j = gcdH d j • v := by unfold gcdH v; exact primPart_scale _
      rw [← hscale]; exact hx2Sphi
    exact Nivat.Claim47.latticeConvex_between d.Sphi_conv ha hb (by positivity) ht'
  have hface_mem : ∀ t : ℕ, t ≤ (gcdH d j).toNat →
      x + (t : ℤ) • v ∈ Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) (nuC d nℓ j) := by
    intro t ht
    have hmemS := hstep t ht
    have heqdot : Nivat.LE2.dot (nuC d nℓ j) (x + (t : ℤ) • v) =
        Nivat.LE2.dot (nuC d nℓ j) x := by
      rw [Nivat.LE2.dot_add, Nivat.PolyChainSum.dot_zsmul_right, hpj_orth]; ring
    exact mem_face_of_dot_eq hx_faceSphi (Finset.mem_coe.mpr hmemS) heqdot
  set pts : Finset (ℤ × ℤ) :=
    (Finset.range ((gcdH d j).toNat + 1)).image (fun (t : ℕ) => x + (t : ℤ) • v) with hptsdef
  have hcard : pts.card = (gcdH d j).toNat + 1 := by
    rw [hptsdef, Finset.card_image_of_injOn, Finset.card_range]
    intro t1 h1 t2 h2 heq
    simp only [Finset.mem_coe, Finset.mem_range] at h1 h2
    have heq2 : (t1 : ℤ) • v = (t2 : ℤ) • v := add_left_cancel heq
    have hcancel : ((t1 : ℤ) - t2) • v = 0 := by rw [sub_smul, heq2, sub_self]
    rcases smul_eq_zero.mp hcancel with h3 | h3
    · have h4 : (t1 : ℤ) = (t2 : ℤ) := by linarith [sub_eq_zero.mp h3]
      exact_mod_cast h4
    · exact absurd h3 hpjne
  have hptsSub : (↑pts : Set (ℤ × ℤ)) ⊆
      Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) (nuC d nℓ j) := by
    intro a ha
    rw [hptsdef, Finset.coe_image, Finset.coe_range] at ha
    obtain ⟨t, htlt, hta⟩ := ha
    exact hta ▸ hface_mem t (by simpa using Nat.lt_succ_iff.mp htlt)
  have hencard_le : (pts.card : ℕ∞) ≤
      (Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) (nuC d nℓ j)).encard :=
    (Set.encard_coe_eq_coe_finsetCard pts) ▸ Set.encard_mono hptsSub
  have hmemEB : nuC d nℓ j ∈ Nivat.LE2.E B := nuC_mem_EB d nℓ hEeqD j
  have hface_le : (Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) (nuC d nℓ j)).encard ≤
      (Nivat.LE2.face B (nuC d nℓ j)).encard := henv (nuC d nℓ j) hmemEB
  have hBfin' : (Nivat.LE2.face B (nuC d nℓ j)).Finite := hBfin.subset (fun z hz => hz.1)
  have hcardfin : (Nivat.LE2.face B (nuC d nℓ j)).encard = (hBfin'.toFinset.card : ℕ∞) :=
    hBfin'.encard_eq_coe_toFinset_card
  have hfinal : (gcdH d j).toNat + 1 ≤ hBfin'.toFinset.card := by
    have hcardNE : (pts.card : ℕ∞) = ((gcdH d j).toNat + 1 : ℕ) := by exact_mod_cast hcard
    have h5 : (pts.card : ℕ∞) ≤ (hBfin'.toFinset.card : ℕ∞) := by
      rw [← hcardfin]; exact le_trans hencard_le hface_le
    rw [hcardNE] at h5
    exact_mod_cast h5
  have hfaceLen_eq : Nivat.PolyChain.faceLen B (nuC d nℓ j) = hBfin'.toFinset.card - 1 := by
    unfold Nivat.PolyChain.faceLen; rw [hcardfin]; simp
  have hnatle : (gcdH d j).toNat ≤ hBfin'.toFinset.card - 1 := by omega
  calc gcdH d j = ((gcdH d j).toNat : ℤ) := (Int.toNat_of_nonneg (gcdH_pos d j).le).symm
    _ ≤ ((hBfin'.toFinset.card - 1 : ℕ) : ℤ) := by exact_mod_cast hnatle
    _ = (Nivat.PolyChain.faceLen B (nuC d nℓ j) : ℤ) := by rw [hfaceLen_eq]

/-! ## §2h. Final assembly: `case_pos_cw` -/

include hprim hdoth hBfin hlcB hEeqD henv hEeq hnℓ_neg_mem hnu hunimod in
/-- **`case_pos_cw`**: the clockwise sub-case of Part (E). Consumer:
`tmp/wip/HsuppAssemble.lean`'s `hsuppZ_target`. -/
theorem case_pos_cw {n : ℤ × ℤ} (hn : n ∈ Nivat.LE2.E B) (hpos : 0 < det n (-nℓ))
    {g : ℤ × ℤ} (hgB : g ∈ B) (hgcz : Nivat.LE2.dot nℓ g = cz)
    (hgle : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b)
    (hgmin : ∀ b ∈ B, Nivat.LE2.dot nℓ b = cz →
      Nivat.LE2.dot (expNormal u' vl) g ≤ Nivat.LE2.dot (expNormal u' vl) b) :
    (∑ j ∈ (Finset.univ : Finset (Fin d.toDecompData.m)).erase i,
        max 0 (Nivat.LE2.dot n (uGen d nℓ j))) ≤
      Nivat.LE2.suppVal B n - Nivat.LE2.dot n g := by
  have hbridge := g_eq_faceStart_or_faceEnd hBfin hlcB hnu hEeq hnℓ_neg_mem hgB hgcz hgle hgmin
  have hdotg_le : Nivat.LE2.dot n g ≤ Nivat.LE2.dot n (Nivat.PolyChain.faceStart B (-nℓ)) := by
    rcases hunimod with h1 | h1
    · rw [hbridge.1 h1]
    · rw [hbridge.2 h1, Nivat.LE2.dot_add, Nivat.PolyChainSum.dot_zsmul_right,
        dot_dir_eq_det n (-nℓ)]
      have hflen : (0 : ℤ) ≤ (Nivat.PolyChain.faceLen B (-nℓ) : ℤ) := by positivity
      have hdetneg : det (-nℓ) n ≤ 0 := by
        have hanti : det (-nℓ) n = - det n (-nℓ) := det_antisymm (-nℓ) n
        linarith [hanti]
      have hprod : (Nivat.PolyChain.faceLen B (-nℓ) : ℤ) * det (-nℓ) n ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hflen hdetneg
      linarith
  set S : Finset (Fin d.toDecompData.m) :=
    (Finset.univ.erase i).filter (fun j => 0 < Nivat.LE2.dot n (uGen d nℓ j)) with hSdef
  have hLHS : (∑ j ∈ (Finset.univ : Finset (Fin d.toDecompData.m)).erase i,
      max 0 (Nivat.LE2.dot n (uGen d nℓ j))) = ∑ j ∈ S, Nivat.LE2.dot n (uGen d nℓ j) := by
    rw [hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 0 < Nivat.LE2.dot n (uGen d nℓ j)
    · rw [if_pos hc]; exact max_eq_right hc.le
    · rw [if_neg hc]
      push_neg at hc
      exact max_eq_left hc
  have hterm_le : ∀ j ∈ S, Nivat.LE2.dot n (uGen d nℓ j) ≤
      (Nivat.PolyChain.faceLen B (nuC d nℓ j) : ℤ) * det n (nuC d nℓ j) := by
    intro j hjS
    have hjS' := hjS
    rw [hSdef, Finset.mem_filter] at hjS'
    obtain ⟨_, hposj⟩ := hjS'
    have heqn := dot_n_uGen_eq d nℓ n j
    have hgcdeq := gcdU_eq_gcdH d nℓ j
    have hgpos := gcdU_pos d nℓ j
    have hdetpos : 0 < det n (nuC d nℓ j) := by
      by_contra hcon
      push_neg at hcon
      have hle0 : Nivat.LE2.dot n (uGen d nℓ j) ≤ 0 := by
        rw [heqn]; exact mul_nonpos_of_nonneg_of_nonpos hgpos.le hcon
      linarith
    have hbound := gcd_le_faceLen d nℓ (hEeqD := hEeqD) (henv := henv) (hBfin := hBfin) j
    calc Nivat.LE2.dot n (uGen d nℓ j) = gcdU d nℓ j * det n (nuC d nℓ j) := heqn
      _ = gcdH d j * det n (nuC d nℓ j) := by rw [hgcdeq]
      _ ≤ (Nivat.PolyChain.faceLen B (nuC d nℓ j) : ℤ) * det n (nuC d nℓ j) :=
          mul_le_mul_of_nonneg_right hbound hdetpos.le
  have hinjS : Set.InjOn (nuC d nℓ) ↑S := fun j _ k _ heq => nuC_inj d nℓ heq
  have hreindex : ∑ j ∈ S, (Nivat.PolyChain.faceLen B (nuC d nℓ j) : ℤ) * det n (nuC d nℓ j) =
      ∑ ν ∈ S.image (nuC d nℓ), (Nivat.PolyChain.faceLen B ν : ℤ) * det n ν := by
    rw [Finset.sum_image hinjS]
  have hSubArc : S.image (nuC d nℓ) ⊆
      (Nivat.LE2.finite_E_of_finite hBfin).toFinset.filter
        (fun ν => 0 < det ν (-nℓ) ∧ 0 < det n ν) := by
    intro ν hν
    rw [Finset.mem_image] at hν
    obtain ⟨j, hjS, hjeq⟩ := hν
    have hjS' := hjS
    rw [hSdef, Finset.mem_filter] at hjS'
    obtain ⟨hji', hposj⟩ := hjS'
    have hji : j ≠ i := Finset.ne_of_mem_erase hji'
    have hmemEB : nuC d nℓ j ∈ Nivat.LE2.E B := nuC_mem_EB d nℓ hEeqD j
    have hdetneg := det_nuC_negnl_pos d nℓ hprim hdoth j hji
    have heqn := dot_n_uGen_eq d nℓ n j
    have hgpos := gcdU_pos d nℓ j
    have hdetpos : 0 < det n (nuC d nℓ j) := by
      by_contra hcon
      push_neg at hcon
      have hle0 : Nivat.LE2.dot n (uGen d nℓ j) ≤ 0 := by
        rw [heqn]; exact mul_nonpos_of_nonneg_of_nonpos hgpos.le hcon
      linarith
    rw [Finset.mem_filter, (Nivat.LE2.finite_E_of_finite hBfin).mem_toFinset, ← hjeq]
    exact ⟨hmemEB, hdetneg, hdetpos⟩
  have hextend : ∑ ν ∈ S.image (nuC d nℓ), (Nivat.PolyChain.faceLen B ν : ℤ) * det n ν ≤
      ∑ ν ∈ (Nivat.LE2.finite_E_of_finite hBfin).toFinset.filter
        (fun ν => 0 < det ν (-nℓ) ∧ 0 < det n ν), (Nivat.PolyChain.faceLen B ν : ℤ) * det n ν := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hSubArc
    intro ν hνmem _
    rw [Finset.mem_filter] at hνmem
    have hnn : (0 : ℤ) ≤ (Nivat.PolyChain.faceLen B ν : ℤ) := by positivity
    exact mul_nonneg hnn hνmem.2.2.le
  have hfinal_eq := Nivat.PolyChainSum.chain_cw_scalar_final hBfin hlcB
    (negnl_mem_EB hEeq hnℓ_neg_mem) hn hpos
  calc (∑ j ∈ (Finset.univ : Finset (Fin d.toDecompData.m)).erase i,
      max 0 (Nivat.LE2.dot n (uGen d nℓ j)))
      = ∑ j ∈ S, Nivat.LE2.dot n (uGen d nℓ j) := hLHS
    _ ≤ ∑ j ∈ S, (Nivat.PolyChain.faceLen B (nuC d nℓ j) : ℤ) * det n (nuC d nℓ j) :=
        Finset.sum_le_sum hterm_le
    _ = ∑ ν ∈ S.image (nuC d nℓ), (Nivat.PolyChain.faceLen B ν : ℤ) * det n ν := hreindex
    _ ≤ ∑ ν ∈ (Nivat.LE2.finite_E_of_finite hBfin).toFinset.filter
        (fun ν => 0 < det ν (-nℓ) ∧ 0 < det n ν), (Nivat.PolyChain.faceLen B ν : ℤ) * det n ν :=
        hextend
    _ = Nivat.LE2.suppVal B n - Nivat.LE2.dot n (Nivat.PolyChain.faceStart B (-nℓ)) :=
        hfinal_eq.symm
    _ ≤ Nivat.LE2.suppVal B n - Nivat.LE2.dot n g := by linarith [hdotg_le]

end Nivat.HsuppCaseCW


#print axioms Nivat.HsuppCaseCW.dot_dir_dir
#print axioms Nivat.HsuppCaseCW.negnl_mem_EB
#print axioms Nivat.HsuppCaseCW.g_mem_face_negnl
#print axioms Nivat.HsuppCaseCW.dot_expNormal_dir_negnl
#print axioms Nivat.HsuppCaseCW.g_eq_faceStart_or_faceEnd

#print axioms Nivat.HsuppCaseCW.face_zonoF_eq_pair
#print axioms Nivat.HsuppCaseCW.primPart_neg
#print axioms Nivat.HsuppCaseCW.genPerp'_neg

#print axioms Nivat.HsuppCaseCW.nuC_inj
#print axioms Nivat.HsuppCaseCW.nuC_mem_EB
#print axioms Nivat.HsuppCaseCW.gcdU_eq_gcdH
#print axioms Nivat.HsuppCaseCW.dot_n_uGen_eq
#print axioms Nivat.HsuppCaseCW.dot_nℓ_uGen_pos
#print axioms Nivat.HsuppCaseCW.det_nuC_negnl_pos
#print axioms Nivat.HsuppCaseCW.gcd_le_faceLen
#print axioms Nivat.HsuppCaseCW.case_pos_cw
