/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.TowerBuild
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.L1Line0

set_option autoImplicit false

/-!
# Half-plane in tower top

原文：b3_colle2.txt:810

Collé writes: "Note that $(T^u η)|_{\mathcal{H}(\boldsymbol{\ell}_{\iota-m})}$ does not have
a period..." — the tower top contains a half-plane `ℋ(ℓ_{ι-m})`.

The key is that `ℓ_{ι-m} = -ℓ` (zonotope edges come in `±` pairs). So the **final tower step
sweeps by `-vl` itself**, making `R' = R + ℤ•vl + ℕ•u'`. Since `(vl, u')` is unimodular,
this covers the half-plane `{z | dot nℓ z ≤ c}` for any threshold `c`.

## Geometric proof

Given `z` with `dot nℓ z ≤ dot nℓ b` for some `b ∈ B ⊆ R`:
1. Decompose `z - b = A•vl + C•u'` via unimodularity (`L1Line0.exists_decomp`).
2. Compute `dot nℓ (z - b) = A·(dot nℓ vl) + C·(dot nℓ u') = 0 + C·(-1) = -C`.
3. Since `dot nℓ z ≤ dot nℓ b`, we have `dot nℓ z - dot nℓ b ≤ 0`, so `-C ≤ 0`, hence `C ≥ 0`.
4. Then `z = b + A•vl + C•u'`. Since `R` is closed under `±vl` and `+u'`, and `b ∈ R`,
   we have `z ∈ R`.
-/

namespace Nivat.HalfPlaneTowerTop

open Nivat Nivat.LE2

/-- **Tower top contains a half-plane** (`:810`).

原文：b3_colle2.txt:810 — "$(T^u η)|_{\mathcal{H}(\boldsymbol{\ell}_{\iota-m})}$" where
`ℓ_{ι-m} = -ℓ`.

If `R` contains `B` and is closed under `±vl` and `+u'`, and `(vl, u')` is unimodular with
`dot nℓ vl = 0` and `dot nℓ u' = -1`, then `R` contains the half-plane
`{z | dot nℓ z ≤ dot nℓ b}`.

The proof uses the unimodular decomposition `z - b = A•vl + C•u'` and observes that
`dot nℓ z ≤ dot nℓ b` forces `C ≥ 0`, so `z` is reachable from `b` by the allowed moves. -/
theorem halfPlane_subset_of_zsmul_vl {R : Set (ℤ×ℤ)} {B : Set (ℤ×ℤ)} {vl u' nℓ : ℤ×ℤ} {b : ℤ×ℤ}
    (hb : b ∈ B) (hBR : B ⊆ R)
    (hvl : ∀ z ∈ R, z + vl ∈ R) (hvl' : ∀ z ∈ R, z - vl ∈ R)
    (hu' : ∀ z ∈ R, z + u' ∈ R)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hperp : dot nℓ vl = 0) (hnu : dot nℓ u' = -1) :
    {z | dot nℓ z ≤ dot nℓ b} ⊆ R := by
  intro z hz
  -- Decompose `z - b = A•vl + C•u'`
  have ⟨A, C, hdecomp, _⟩ := Nivat.L1Line0.exists_decomp (u' := u') (vl := vl) hunimod b z
  -- Compute `dot nℓ (z - b) = C·(-1)`
  have hdot : dot nℓ (z - b) = C * (dot nℓ u') := by
    calc dot nℓ (z - b)
        = dot nℓ (b + A • vl + C • u' - b) := by rw [hdecomp]
      _ = dot nℓ (A • vl + C • u') := by ring_nf
      _ = dot nℓ (A • vl) + dot nℓ (C • u') := dot_add _ _ _
      _ = A * dot nℓ vl + C * dot nℓ u' := by
          have hvl_term : dot nℓ (A • vl) = A * (dot nℓ vl) := by
            obtain ⟨n1, n2⟩ := nℓ; obtain ⟨v1, v2⟩ := vl
            simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
          have hu'_term : dot nℓ (C • u') = C * (dot nℓ u') := by
            obtain ⟨n1, n2⟩ := nℓ; obtain ⟨u1, u2⟩ := u'
            simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
          rw [hvl_term, hu'_term]
      _ = A * 0 + C * dot nℓ u' := by rw [hperp]
      _ = C * dot nℓ u' := by ring
  rw [hnu] at hdot
  -- Since `dot nℓ z ≤ dot nℓ b`, we get `C ≥ 0`
  have hC : 0 ≤ C := by
    have hdiff : dot nℓ (z - b) = dot nℓ z - dot nℓ b := by
      obtain ⟨n1, n2⟩ := nℓ; obtain ⟨z1, z2⟩ := z; obtain ⟨b1, b2⟩ := b
      simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hdiff] at hdot
    simp only [Set.mem_ofPred_eq] at hz
    omega
  -- Now `z = b + A•vl + C•u'` and `C ≥ 0`
  rw [hdecomp]
  -- Helper: moving by ℤ•vl
  have hvl_zsmul : ∀ (w : ℤ × ℤ) (a : ℤ), w ∈ R → w + a • vl ∈ R := by
    intro w a hw
    obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
    · -- a = n : ℕ
      induction n with
      | zero => simpa
      | succ k ih =>
          convert hvl _ ih using 1
          simp [add_smul]; ring
    · -- a = -n
      induction n with
      | zero => simpa
      | succ k ih =>
          convert hvl' _ ih using 1
          simp [add_smul, sub_eq_add_neg]; ring
  -- Apply: b + A•vl ∈ R
  have hbA : b + A • vl ∈ R := hvl_zsmul b A (hBR hb)
  -- Apply: (b + A•vl) + C•u' ∈ R, using C ≥ 0
  obtain ⟨C', hC'⟩ : ∃ C' : ℕ, C = (C' : ℤ) := ⟨C.toNat, by omega⟩
  subst hC'
  clear hdot hdecomp hz hC hvl_zsmul hBR hb
  -- Prove by induction on C'
  suffices ∀ k : ℕ, b + A • vl + (k : ℤ) • u' ∈ R by exact this C'
  intro k
  induction k with
  | zero => simpa using hbA
  | succ n ih =>
      have eq : b + A • vl + ((n + 1 : ℕ) : ℤ) • u' = (b + A • vl + (n : ℤ) • u') + u' := by
        push_cast; rw [add_smul, one_smul]; ring
      rw [eq]
      exact hu' _ ih

#print axioms halfPlane_subset_of_zsmul_vl

end Nivat.HalfPlaneTowerTop
