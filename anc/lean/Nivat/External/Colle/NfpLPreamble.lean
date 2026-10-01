/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.RegionSteps
import Nivat.External.Colle.ItemII

/-!
# Lane Aparts: `tmp/nfpL_preamble.lean` — status check and the preamble/item(ii) seam

**Dispatch was to land `tmp/nfpL_preamble.lean` (`wlog_notDP` + `exists_preamble_pair`).**
§20 orphan scan first, per protocol: both declarations are **already landed**, not just in
`tmp/`, and have moved on from the `tmp/` receipt's exact shape:

* `wlog_notDP` / `notDP_mono` / `nfp_L_of_notDP` — `Nivat.Colle35`,
  `HalfPlaneDoublyPeriodic.lean:315/343/356`. Generalised to `Config α` (the `tmp/` version was
  `Config ℤ`-only, in a throwaway `Nivat.AnfpL` namespace).
* `exists_preamble_pair` — `Nivat.ColleReg`, `RegionSteps.lean:661`, **already the live
  `hpartner` producer** consumed at `ColleRegion.lean:363`. Differs from the `tmp/` receipt in
  one place: the inner existential adds `Primitive nℓ` (nine conjuncts, not eight) — exactly the
  extra hypothesis `ell_side_of_exhausts` below needs and the `tmp/` version did not carry.

So there is nothing to move out of `tmp/`; that work happened between the `tmp/` receipt's
timestamp (2026-09-19 10:25) and now, under different names, already wired into the real
`exists_chainData` call chain. Landing a second copy under the old names would duplicate,
not progress (PROTOCOL §20).

## The composition — and the correction it forces

The task's premise was: "`nfp_L` has a route independent of item (ii)." **That premise is
false**, and this file's real contribution is finding out why, by attempting the composition
and reading where it lands.

`nfp_L_of_notDP` only consumes the *placement* data `k`, `hnL : nL = k • nℓ`, `hcL : cL ≤ k*cz`,
plus the *pair* fact `hnotDP` (which `exists_preamble_pair`'s `hpartner` supplies for free, no
item (ii) needed). But the placement data itself — `k`, hence `cL` — is **only produced** by
`Nivat.Colle35.ell_side_of_exhausts` (`ItemII.lean:476-489`), whose derivation of `0 < k`
(`dot_vJ_pos_of_exhausts`, `ItemII.lean` §5) uses `hexh : Exhausts A nℓ cz` essentially: it is
what pins `Â_∞`'s support line to the correct side of `ℓ^(−)`. `ItemII.lean`'s own §6 audit
(`:465-475`, written by team-lead 2026-09-19) says this in so many words: item (ii) is what
discharges `cL`, `ahat_halfPlane_L`, `ahat_attained_L`, **and `nfp_L`**, all four together —
there is no separate placement producer anywhere in the tree, `tmp/` included.

**Correction to the previous window's report**: `nfp_L` is not a `(b)`-wired field independent
of the recursion. It is `(c)` owed, and **recursion-dependent** (routes only through `Exhausts`
= Collé item (ii)), same bucket as `ahat_halfPlane_L` / `ahat_attained_L` / `ahat_nonempty`.
What is genuinely independent of item (ii) is only the *pair* half (`hnotDP`, from
`exists_preamble_pair`) — and that half was already free, already reported, and was never the
missing piece. Revised tally for the 24-field classification: **16 of 24 owed are
recursion-blocked** (up from 15), **1 attackable today (`hsweep`)**, **0 pending only a `tmp/`
landing** (down from 1). `sorry TOTAL` unaffected — this file adds a verification wrapper, not
new project mathematics, and lands nothing that changes leaf A's obligation count.

The wrapper below exists so the "does the composition go through" check is a kernel fact rather
than a docstring claim: it takes `exists_preamble_pair`'s `hpartner` output at exactly the shape
`ColleRegion.lean:363`'s `obtain` produces it, plus `Exhausts`/`rec_vJ`/`hpvJ`, and calls
`ell_side_of_exhausts` unchanged — confirming the two already-landed pieces' types meet with no
adaptation needed (in particular `Primitive nℓ` lines up, which the superseded `tmp/` shape could
not have supplied). -/

set_option autoImplicit false

namespace Nivat.ChainAsm.Aparts

open Nivat Nivat.LE2 Nivat.Colle35

/-- The seam check: `exists_preamble_pair`'s pair data (`xper`, `nℓ`, `cz`, `hnotDP`, and now
`Primitive nℓ`) feeds `ell_side_of_exhausts` with no adaptation, **once a producer also supplies
`Exhausts A nℓ cz`** (Collé item (ii)) and `rec_vJ`. This is the full composition asked for; its
premises make plain that `Exhausts` is doing the work `hnotDP` alone cannot. -/
theorem nfp_L_of_preamble_and_exhausts {xper : Config ℤ}
    {A Ahat : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl p vJ nℓ : ℤ × ℤ} {cz : ℤ}
    (hvl : vl ≠ 0) (hdet : det p vl = 0) (hpvJ : det p vJ ≠ 0)
    (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hAhat : ∀ i, Ahat i = {z | z + (kk i : ℤ) • vl ∈ A i})
    (hexh : Exhausts A nℓ cz)
    (rec_vJ : ∀ g ∈ ⋃ i, Ahat i, g + vJ ∈ ⋃ i, Ahat i)
    (hnotDP : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cz ≤ dot nℓ z} h ∧ PeriodicOnWith xper {z | cz ≤ dot nℓ z} h') :
    ∃ (k cL : ℤ), 0 < k ∧ det p vJ • (-p.2, p.1) = k • nℓ ∧ cL = k * cz ∧
      (∀ g ∈ ⋃ i, Ahat i, cL ≤ dot (det p vJ • (-p.2, p.1)) g) ∧
      (∃ g ∈ ⋃ i, Ahat i, dot (det p vJ • (-p.2, p.1)) g = cL) ∧
      ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
        PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h ∧
        PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h' :=
  ell_side_of_exhausts hvl hdet hpvJ hprim hperp hAhat hexh rec_vJ hnotDP

/-- Extraction lemma: `exists_preamble_pair`'s `hpartner` at `ColleRegion.lean:363`'s exact
destructuring shape supplies `hnotDP` (and `Primitive nℓ`) for `nfp_L_of_preamble_and_exhausts`
directly — no gap between the two landed theorems. This is the "compose it" step made a kernel
fact: given the full `hpartner` existential, extracting the last conjunct and feeding it forward
type-checks with no adaptation.

**Updated 2026-09-24 (集成者)** for the orientation normalisation: `hpartner` now carries
`0 < det nℓ vl` (the producer exports `vl = dir nℓ` in both branches of its `by_cases`, see
`RegionSteps.lean`'s `have hdetpos` block), so the hypothesis gains that conjunct and the
conclusion re-exports it.

⚠ **Corrected the same day**: the first version of this paragraph said that sign is what
`Hole3Room.nlmax_of_wadj`'s `hmvl` (`Hole3Room.lean:321`) consumes.  It is not — that `hmvl`
is `0 < dot m vl` for the *cut* normal `m` (`dot m w = 0`), which the tower package already
discharges (a component of the `obtain` at `RegionSteps.lean:1949`).  What `0 < det nℓ vl` actually buys is listed in
`exists_preamble`'s docstring (`dir vl = -nℓ`, `0 < det vl w`, `det u' vl = -1`). -/
theorem hnotDP_of_hpartner {ξ xper : Config ℤ} {vl : ℤ × ℤ}
    (hpartner : ∃ (yper : Config ℤ) (nℓ : ℤ × ℤ) (cz : ℤ) (g : ℤ × ℤ),
      yper ∈ orbitClosure ξ ∧ xper ≠ yper ∧
      nℓ ≠ 0 ∧ Primitive nℓ ∧ dot nℓ vl = 0 ∧ 0 < det nℓ vl ∧
      (∀ z : ℤ × ℤ, cz < dot nℓ z → xper z = yper z) ∧
      dot nℓ g = cz ∧ xper g ≠ yper g ∧
      ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
        PeriodicOnWith xper {z | cz ≤ dot nℓ z} h ∧
        PeriodicOnWith xper {z | cz ≤ dot nℓ z} h') :
    ∃ (nℓ : ℤ × ℤ) (cz : ℤ), Primitive nℓ ∧ dot nℓ vl = 0 ∧ 0 < det nℓ vl ∧
      ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
        PeriodicOnWith xper {z | cz ≤ dot nℓ z} h ∧
        PeriodicOnWith xper {z | cz ≤ dot nℓ z} h' := by
  obtain ⟨yper, nℓ, cz, g, hy, hne, hnℓ0, hprim, hperp, hdetpos, hagree, hgz, hgne, hnotDP⟩ :=
    hpartner
  exact ⟨nℓ, cz, hprim, hperp, hdetpos, hnotDP⟩

end Nivat.ChainAsm.Aparts

#print axioms Nivat.ColleReg.exists_preamble_pair
#print axioms Nivat.Colle35.wlog_notDP
#print axioms Nivat.Colle35.nfp_L_of_notDP
#print axioms Nivat.Colle35.ell_side_of_exhausts
#print axioms Nivat.ChainAsm.Aparts.nfp_L_of_preamble_and_exhausts
#print axioms Nivat.ChainAsm.Aparts.hnotDP_of_hpartner
