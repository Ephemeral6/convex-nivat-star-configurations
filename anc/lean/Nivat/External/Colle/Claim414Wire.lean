/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Claim414
import Nivat.External.Colle.RegionTranslate

set_option autoImplicit false

/-!
# Claim 4.14 at the `colle_region` call site

`Claim414.claim414` (`Claim414.lean:67`) states Collé's Claim 4.14 with all twenty-odd
hypotheses of its two halves spelled out.  This file specialises it to the data that is
actually in scope in the Case 2 branch of `ColleReg.colle_region` (`ColleRegion.lean:336-381`),
discharging every hypothesis that `ChainDataGeom` or `region_periods_and_rays` already
supplies, so that what remains is visible and typed rather than argued in prose.

## What is discharged here

| hypothesis of `claim414` | source |
|---|---|
| `hsupp`, `hatt` | `cg.ahat_halfPlane_L`, `cg.ahat_attained_L` (`ChainGeom.lean`) |
| `hnfp` | `cg.nfp_L` (`ChainGeom.lean`) — see below |
| `hK`, `hrayq`, `hper'` | `region_periods_and_rays` (`RegionSteps.lean:1202`) |
| `hrayv` | ditto, through `rayIn_of_rayIn_nsmul` and the `h' = n • vJ` clause |
| `hh'_ne`, `hh'_par` | ditto, from `0 < n` and `vJ ≠ 0` |
| `hvJ_ne` | `cg.vJ_ne` |
| `hdet_qv` | `det h h' ≠ 0` and `h' = n • vJ` |
| `hℓ'`, `hℓ'_vJ` | `cg.nJ_prim`, `cg.dot_nJ_vJ`, at `ℓ' := cg.nJ` |
| `hdet_lines` | `cg.dot_nJ_p`, `cg.dot_nJ_vJ` and `p ∥ vl` |
| `hno_fp` | `ColleReg.region_not_periodic` (`RegionSteps.lean:1245`) — verbatim shape |

Every hypothesis of `claim414` is now discharged: at this call site Claim 4.14 takes only the
chain data and the two theorems of `RegionSteps.lean` named in the table.

## Where `hnfp` went

As of 2026-09-18 `hnfp` — *"`x_per|ℋ(ℓ^(−))` is not fully periodic"*, the Case 2 standing
assumption of `b3_colle2.txt:890` — is the `ChainDataGeom` field `nfp_L` rather than a loose
hypothesis here.

An earlier version of this docstring said a bundle field would be the wrong place, on the
grounds that the assumption is about `x_per`, which `exists_preamble` (`RegionSteps.lean:502`)
fixes long before `cg` exists.  That was wrong about the half plane.  `claim414`'s level `c`
comes with `hatt` (`Claim414.lean:80`), so it is the *attained* `ℓ_ι`-support value of `Â_∞`,
namely `cL`; and it cannot be lowered, because `claim414_ell`'s `hexh` (`Claim414Ell.lean:122`)
needs every point of the half plane to reach `Â_∞` along `p`, while `dot n_ℓ p = 0` makes `p`
tangent to `ℓ_ι`.  So `hnfp` is a joint condition on `x_per` **and** `cL`, and `cL` is the
chain's.  This matches `b3_colle2.txt:922` — *"the support line of `Â^(ε)_∞` determined by `ℓ`
coincides with `ℓ^(−)`"* — which is an assertion about the chain that was built.

The obligation is therefore on `ColleReg.exists_chainData` (`RegionSteps.lean:751`, already
`sorry`), which must place `Â_∞` so that its `ℓ_ι`-support line carries the disagreement of the
ambiguous pair.  The implication it will use, `Colle35.not_doublyPeriodicOn_both`
(`HalfPlaneDoublyPeriodic.lean`), is proved and kernel-clean, and the ambiguity partner
`y_per` it consumes reaches `exists_chainData` as the `hpartner` hypothesis, exported by
`exists_preamble` on 2026-09-18.  Only the placement is open.
-/

namespace Nivat.ColleReg

open Nivat Nivat.Colle35 Nivat.LE2

/-- **Claim 4.14 with everything `ChainDataGeom` and `region_periods_and_rays` supply already
discharged.**  The single remaining hypothesis is `hnfp`; see the module docstring. -/
theorem claim414_of_chainDataGeom {ξ xper ϑ : Config ℤ} {vl p ℓ : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (cg : ChainDataGeom ξ xper vl p S gen) {K : ℕ}
    (hξ : IsMinimalCounterexample ξ)
    (hϑ_mem : ϑ ∈ orbitClosure ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ) (hdet_ℓ : LE2.dot ℓ vl = 0)
    (hp_ne : p ≠ 0) (hvl_ne : vl ≠ 0) (hdet_vl : det p vl = 0) (hp_per : p ∈ Per xper)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    (hagree : ∀ z ∈ ⋃ i, cg.toChainData.Ahat i, ϑ z = T ((K : ℤ) • vl) xper z)
    -- the output of `region_periods_and_rays` (`RegionSteps.lean:1202`)
    {R : Set (ℤ × ℤ)} (hRreg : IsLatticeConvexRegion R)
    {h h' z₀ z₀' : ℤ × ℤ} (hdet : det h h' ≠ 0)
    (hray_h : ∀ k : ℕ, z₀ + (k : ℤ) • h ∈ R)
    (hray_h' : ∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ R)
    (hper_h' : ∀ z ∈ R, z + h' ∈ R → ϑ (z + h') = ϑ z)
    {n : ℕ} (hn : 0 < n) (hh'_eq : h' = (n : ℤ) • cg.vJ)
    -- the output of `region_not_periodic` (`RegionSteps.lean:1245`)
    (hno_fp : ¬ ∃ y : Config ℤ, Colle45.IsFullyPeriodic y ∧
      ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧
        ∀ z ∈ W, y z = T ((t : ℤ) • cg.vJ) ϑ z) :
    ¬ IsPeriodic ϑ := by
  have hn0 : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn.ne'
  -- `p` is transverse to `ℓ_J`, hence so is `vl ∥ p`
  have hdet_pvJ : det p cg.vJ ≠ 0 :=
    det_ne_zero_of_dot cg.vJ_ne cg.dot_nJ_vJ cg.dot_nJ_p
  have hdet_lines : det vl cg.vJ ≠ 0 := by
    obtain ⟨k, l, hk, hkl⟩ := Colle.exists_common_multiple_of_det_eq_zero hp_ne hvl_ne hdet_vl
    have e1 : det (k • p) cg.vJ = det (l • vl) cg.vJ := by rw [hkl]
    have e2 : det (k • p) cg.vJ = k * det p cg.vJ := by
      simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have e3 : det (l • vl) cg.vJ = l * det vl cg.vJ := by
      simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [e2, e3] at e1
    intro hz
    rw [hz, mul_zero] at e1
    exact mul_ne_zero hk hdet_pvJ e1
  -- the `h'`-data, rewritten along `h' = n • vJ`
  have hh'_ne : h' ≠ 0 := by
    rw [hh'_eq]; exact smul_ne_zero hn0 cg.vJ_ne
  have hh'_par : det h' cg.vJ = 0 := by
    rw [hh'_eq]; simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hdet_qv : det cg.vJ h ≠ 0 := by
    have e : det h h' = (n : ℤ) * det h cg.vJ := by
      rw [hh'_eq]; simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have hhv : det h cg.vJ ≠ 0 := by
      intro hz; rw [hz, mul_zero] at e; exact hdet e
    intro hz
    exact hhv (by rw [det_comm, hz, neg_zero])
  -- refine the `h'`-ray to a `vJ`-ray; this is where `0 < n` is consumed
  have hrayv : ∀ k : ℕ, z₀' + (k : ℤ) • cg.vJ ∈ R :=
    rayIn_of_rayIn_nsmul hRreg hn (by rw [← hh'_eq]; exact hray_h')
  exact Claim414.claim414 cg (K := K) (ℓ' := cg.nJ) hξ hϑ_mem hℓ_nel hdet_ℓ hp_ne hvl_ne
    hdet_vl hp_per hRconv hagree cg.ahat_halfPlane_L cg.ahat_attained_L cg.nfp_L
    hRreg hray_h hrayv cg.vJ_ne hdet_qv hh'_ne hh'_par hper_h' cg.nJ_prim cg.dot_nJ_vJ
    hno_fp hdet_lines

end Nivat.ColleReg
