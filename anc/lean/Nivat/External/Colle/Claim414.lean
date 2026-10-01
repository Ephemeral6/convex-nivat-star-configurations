/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Claim414EllPrime

set_option autoImplicit false

/-!
# Collé Claim 4.14, assembled (`delivery/scratch/b3_colle2.txt:918-922`)

`Claim414Ell.lean` and `Claim414EllPrime.lean` prove the two halves of Claim 4.14 and the
step that turns them into non-periodicity.  All three were kernel-clean on 2026-09-18 and
had **zero consumers** in `Nivat/`: built, verified, never wired up.  This file wires them.

## Why this matters for the gate

Until 2026-09-18 `Nivat.colle_region` (then an `axiom` in `Section8/External.lean`) was the last
live axiom in the closure of `Nivat.nivat_conjecture`.  Its second clause is `¬ IsPeriodic ξ'`,
while `ColleReg.colle_region` at the time exported only the weaker "no fully periodic
accumulation point along `vl`".  That mismatch was a *signature* gap, not a `sorry`, so
`scripts/sorries.sh` could not see it, and clearing the `sorry`s in `RegionSteps.lean` would not
have closed it.  `claim414` below is exactly the missing implication for Case 2: it ends in
`¬ IsPeriodic ϑ`.  It was wired into `ColleReg.colle_region` through `Claim414Wire.lean` on
2026-09-18; the theorem was then substituted for the axiom and the axiom deleted.

## What is and is not done here

This file is **pure composition**: every hypothesis below is copied verbatim from the
signature of the theorem that consumes it, and the proof is four applications.  No new
mathematical content, and in particular no claim that these hypotheses are *available* at
the `colle_region` call site — that was established the same day in `Claim414Wire.lean`
(`claim414_of_chainDataGeom`), not here.  The value of this file is that the obligation has a
single name and an exact shape.

## The paper's argument (`b3_colle2.txt:922`, last sentence)

"Therefore, from Claim 4.13 we conclude that `ℓ, ℓ′ ∈ nexpl(ϑ)`" — combined with
`b3_colle2.txt:90`, "any configuration `η ∈ 𝒜^{ℤ²}` where `nexpl(η)` has at least two
elements can not be periodic".

## Direction bookkeeping (the point that took longest to pin down)

The two halves run along *different* directions, and neither is `+v_ℓ`:

* the `ℓ`-half uses the recession direction `p ∥ vl` of `Â_∞`, which stands in for the
  paper's `−v_ℓ` because "the sign of `p` against `vl` is not recorded in `ChainDataGeom`"
  (`Claim414Ell.lean:293-295`);
* the `ℓ′`-half uses `cg.vJ = v_{ℓ′}`, which is also the orbit direction of
  `ColleReg.region_not_periodic` (`RegionSteps.lean:1241`, "not `vl = v_{ℓ_ι}`"), so
  `hno_fp` below can be discharged by that theorem verbatim.

Independence of the two lines enters as `hdet_lines : det vl cg.vJ ≠ 0`, which
`det_ne_zero_of_normals` (`Claim414EllPrime.lean:105`) converts into `det ℓ ℓ' ≠ 0`.
-/

open Nivat

namespace Nivat.Claim414

/-- **Collé's Claim 4.14** (`b3_colle2.txt:918-922`), assembled.

Hypotheses `cg … hnfp` are those of `claim414_ell` (`Claim414Ell.lean:302`); hypotheses
`hK … hno_fp` are those of `claim414_ellprime` (`Claim414EllPrime.lean:160`), specialised to
`vJ := cg.vJ`; `hdet_lines` says the two lines are distinct.  The conclusion is the clause
the axiom `Nivat.colle_region` needs and `ColleReg.colle_region` does not currently export.

`hno_fp` is in the verbatim shape of the conclusion of `ColleReg.region_not_periodic`. -/
theorem claim414 {ξ xper ϑ : Config ℤ} {vl p ℓ ℓ' : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (cg : Colle35.ChainDataGeom ξ xper vl p S gen) {K : ℕ}
    (hξ : IsMinimalCounterexample ξ)
    (hϑ_mem : ϑ ∈ orbitClosure ξ)
    -- the `ℓ`-half (`Claim414Ell.lean:302`)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ) (hdet_ℓ : LE2.dot ℓ vl = 0)
    (hp_ne : p ≠ 0) (hvl_ne : vl ≠ 0) (hdet_vl : det p vl = 0) (hp_per : p ∈ Per xper)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    (hagree : ∀ z ∈ ⋃ i, cg.toChainData.Ahat i, ϑ z = T ((K : ℤ) • vl) xper z)
    {c : ℤ}
    (hsupp : ∀ g ∈ ⋃ i, cg.toChainData.Ahat i,
      c ≤ LE2.dot (det p cg.vJ • (-p.2, p.1)) g)
    (hatt : ∃ g ∈ ⋃ i, cg.toChainData.Ahat i,
      LE2.dot (det p cg.vJ • (-p.2, p.1)) g = c)
    (hnfp : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      Colle35.PeriodicOnWith xper {z | c ≤ LE2.dot (det p cg.vJ • (-p.2, p.1)) z} h ∧
      Colle35.PeriodicOnWith xper {z | c ≤ LE2.dot (det p cg.vJ • (-p.2, p.1)) z} h')
    -- the `ℓ′`-half (`Claim414EllPrime.lean:160`), at `vJ := cg.vJ`
    {𝒦 : Set (ℤ × ℤ)} (hK : IsLatticeConvexRegion 𝒦)
    {q z₀ z₀' : ℤ × ℤ} (hrayq : ∀ k : ℕ, z₀ + (k : ℤ) • q ∈ 𝒦)
    (hrayv : ∀ k : ℕ, z₀' + (k : ℤ) • cg.vJ ∈ 𝒦)
    (hvJ_ne : cg.vJ ≠ 0) (hdet_qv : det cg.vJ q ≠ 0)
    {h' : ℤ × ℤ} (hh'_ne : h' ≠ 0) (hh'_par : det h' cg.vJ = 0)
    (hper' : ∀ z ∈ 𝒦, z + h' ∈ 𝒦 → ϑ (z + h') = ϑ z)
    (hℓ' : Primitive ℓ') (hℓ'_vJ : LE2.dot ℓ' cg.vJ = 0)
    (hno_fp : ¬ ∃ y : Config ℤ, Colle45.IsFullyPeriodic y ∧
      ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧
        ∀ z ∈ W, y z = T ((t : ℤ) • cg.vJ) ϑ z)
    -- the two lines are distinct
    (hdet_lines : det vl cg.vJ ≠ 0) :
    ¬ IsPeriodic ϑ := by
  have hℓ_mem : ℓ ∈ Colle45.NonExpansiveLine ϑ :=
    claim414_ell cg (K := K) hξ hℓ_nel hdet_ℓ hp_ne hvl_ne hdet_vl hp_per hϑ_mem hRconv
      hagree hsupp hatt hnfp
  have hℓ'_mem : ℓ' ∈ Colle45.NonExpansiveLine ϑ :=
    claim414_ellprime hξ hϑ_mem hK hrayq hrayv hvJ_ne hdet_qv hh'_ne hh'_par hper' hℓ'
      hℓ'_vJ hno_fp
  exact not_isPeriodic_of_two_nonExpansiveLines hℓ_mem hℓ'_mem
    (det_ne_zero_of_normals hℓ_nel.1.ne_zero hℓ'.ne_zero hdet_ℓ hℓ'_vJ hdet_lines)

end Nivat.Claim414
