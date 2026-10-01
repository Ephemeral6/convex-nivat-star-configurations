/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellConvex
import Nivat.External.Colle.ShellMink
import Nivat.External.Colle.Case2WindowProbe

/-!
# `AResidual` — which `ChainDataGeom` instances can witness `exists_chainData`?

`exists_chainData` (`RegionSteps.lean`, `theorem exists_chainData`; one of the project's two
remaining `sorry`s — `scripts/sorries.sh` reports `TOTAL: 2`, 2026-09-24).  §85: the old
citation here was `:1001-1029`, measured rotten 2026-09-24 (actual `:1341`); recording the
identifier instead, since a line number rots again on the next edit above it.
concludes `∃ genφ, cg : ChainDataGeom ξ xper vl p d.Sphi genφ, …`, subject to (fresh `#check`,
2026-09-19, this file's mtime): `hξ : IsMinimalCounterexample ξ`, `d : DecompDataZ ξ`,
`{w} (hw hw₁ hw₂)`, `hℓ_nel hℓ_pos hℓ_neg`, `hxper : xper ∈ orbitClosure ξ`, `hp_mem : p ∈ Per
xper`, `hp_ne hvl_ne hvl_prim`, **`hdet_vl : det p vl = 0`**, `hdet_ℓ`, `hpartner` (the
2026-09-19-strengthened eight-conjunct existential, `:1016-1023`), `hcase2 : Case2 ξ xper
d.Sphi vl`.

The tree currently has five `ChainDataGeom` instances: `cgw` (`Step_PeriodsRays2.lean:233`),
`cgn` (`ShellConvex.lean:197`), `cgc` (`ShellConvex.lean:583`), `cgwA` (`ShellMink.lean:1572`),
`cgg` (`Case2WindowProbe.lean:943`). Team-lead's question: after threading *all* of
`exists_chainData`'s binders, how many of these five survive as witnesses? This file answers it
for the cheapest, most decisive binder first: `hdet_vl`. `p` and `vl` are baked into a
`ChainDataGeom`'s *type*, not chosen by a producer, so `det p vl = 0` is an arithmetic fact about
each instance alone — true or false independent of every other binder (`ξ`, `hpartner`,
`hcase2`, …). **Three of the five fail it outright**, for every possible instantiation of the
remaining binders.

The other two (`cgw`, `cgwA`, sharing `p = pv = (0,1)`, `vl = vlv = (0,-1)`, `det = 0`) pass
`hdet_vl` — but **all five fail overall**: `cgw`/`cgwA` (`ξ = etaC`) and `cgg` (`ξ = ξg`) fail the
binder `hξ : IsMinimalCounterexample ξ` itself, at the single point `(0,0)` (`etaC (0,0) = 0`,
`ξg (0,0) = 0`, violating `IsCounterexample`'s `∀ z, 0 < ξ z` clause). This is cheaper than the
`hpartner`/`hxper` route and needs no case analysis on any other binder. See the scoreboard
section below for the full statement of scope: this refutes these five *bundles* as witnesses,
not the Nivat conjecture itself.
-/

set_option autoImplicit false

namespace Nivat.AResidual

open Nivat Nivat.ColleStep.PeriodsRays2 Nivat.ShellConvex Nivat.Case2WindowProbe.Gen

/-! ## `cgn` dies on `hdet_vl` -/

/-- `cgn : ChainDataGeom etaC xperC vln pv Sw genw` (`ShellConvex.lean:197`) has `p = pv = (0,1)`
and `vl = vln = (1,-1)`.  `det p vl = 0·(-1) - 1·1 = -1 ≠ 0`, so `cgn` cannot instantiate
`exists_chainData`'s conclusion for *any* choice of `ξ`, `w`, `ℓ`, `d`, `hpartner`, `hcase2` —
the failure is purely in the fixed pair `(pv, vln)`, before any of those are even chosen. -/
theorem det_pv_vln_ne_zero : det pv vln ≠ 0 := by decide

/-- Restated for the scoreboard below: `cgn` fails `exists_chainData`'s `hdet_vl` binder,
unconditionally. -/
theorem not_hdet_vl_cgn : det pv vln ≠ 0 := det_pv_vln_ne_zero

/-! ## `cgc` dies on `hdet_vl` -/

/-- `cgc : ChainDataGeom etaC xperC vl2 p2 Sw genw` (`ShellConvex.lean:583`) has `p = p2 = (2,1)`
and `vl = vl2 = (1,-2)`.  `det p vl = 2·(-2) - 1·1 = -5 ≠ 0`. Same argument as `cgn`: this is a
fact about the fixed pair `(p2, vl2)` baked into `cgc`'s type, independent of every other
binder. -/
theorem det_p2_vl2_ne_zero : det p2 vl2 ≠ 0 := by decide

/-! ## `cgg` dies on `hdet_vl` -/

/-- `cgg : ChainDataGeom ξg xperg vlg pg Sg geng` (`Case2WindowProbe.lean:943`) has
`p = pg = (1,1)` and `vl = vlg = (1,-1)`.  `det p vl = 1·(-1) - 1·1 = -2 ≠ 0`.  (This is in
addition to the `hxper`/`ξ = ξg` obstructions Amink flagged earlier — `hdet_vl` alone already
suffices and needs no orbit-closure reasoning.) -/
theorem det_pg_vlg_ne_zero : det pg vlg ≠ 0 := by decide

/-! ## `cgw` and `cgwA` die on `hξ`, not on `hpartner`

Both share `ξ = etaC` and pass `hdet_vl` (`det pv vlv = 0`), so the arithmetic filter above does
not touch them. The cheapest binder that does is `hξ : IsMinimalCounterexample ξ` itself:
unfolded, `IsMinimalCounterexample ξ → IsCounterexample ξ → ∀ z, 0 < ξ z`
(`Nivat.IsCounterexample`, `Section8/ExternalDefs.lean:48`), and `etaC (0,0) = 0`
(`etaC := fun z => z.1 + (if z.2 < 0 then 1 else 0)`, `Step_PeriodsRays2.lean:55`; at `z=(0,0)`,
`z.2 = 0` is not `< 0`, so the `if` contributes `0` and `z.1 = 0`). One point refutes the clause
outright, before `w`, `ℓ`, `d`, `hpartner`, `hcase2` are ever chosen — strictly cheaper than
`hxper` (which needs `orbitClosure`) and vastly cheaper than `hpartner` (an eight-conjunct
existential). The same one-line shape kills `cgg` a second, independent way: `ξg (0,0) = 0`. -/

theorem etaC_zero_zero : etaC ((0:ℤ), (0:ℤ)) = 0 := by
  show (0:ℤ) + (if (0:ℤ) < 0 then 1 else 0) = 0
  norm_num

/-- `etaC` is not a counterexample: `IsCounterexample`'s positivity clause fails at `(0,0)`. -/
theorem not_isCounterexample_etaC : ¬ IsCounterexample etaC := by
  rintro ⟨-, hpos, -, -⟩
  have := hpos ((0:ℤ), (0:ℤ))
  rw [etaC_zero_zero] at this
  exact absurd this (lt_irrefl 0)

/-- Hence `etaC` is not a *minimal* counterexample either — this is the binder actually on
`exists_chainData` (`hξ`), and it is what `cgw`/`cgwA` (both built on `ξ = etaC`) fail. -/
theorem not_isMinimalCounterexample_etaC : ¬ IsMinimalCounterexample etaC :=
  fun h => not_isCounterexample_etaC h.1

theorem ξg_zero_zero : ξg ((0:ℤ), (0:ℤ)) = 0 := by
  show (0:ℤ) % 2 = 0
  decide

/-- Independent second reason `cgg` is excluded: `ξg` also fails `IsCounterexample` at `(0,0)`,
via the same clause `hdet_vl` never touches (redundant with `det_pg_vlg_ne_zero` above, but a
different mechanism — worth recording since `hdet_vl` and `hξ` are logically unrelated
binders). -/
theorem not_isCounterexample_ξg : ¬ IsCounterexample ξg := by
  rintro ⟨-, hpos, -, -⟩
  have := hpos ((0:ℤ), (0:ℤ))
  rw [ξg_zero_zero] at this
  exact absurd this (lt_irrefl 0)

theorem not_isMinimalCounterexample_ξg : ¬ IsMinimalCounterexample ξg :=
  fun h => not_isCounterexample_ξg h.1

/-! ## Scoreboard, and what is still open

**Killed, decisively, by `hdet_vl` alone (arithmetic, no case analysis on the other binders
needed): `cgn`, `cgc`, `cgg`.** For each, `det p vl` is a fixed nonzero integer computed from the
instance's own defining data, so no choice of `ξ`, `w`, `ℓ`, `d`, `hpartner`, `hcase2` can ever
make `exists_chainData`'s `hdet_vl` binder true for that instance — the obstruction is at the
type level, before any hypothesis is inspected.

**Killed, decisively, by `hξ` alone (arithmetic on a single point, no orbit-closure or
half-plane reasoning needed): `cgw`, `cgwA` (both `ξ = etaC`), and redundantly `cgg`
(`ξ = ξg`).** `not_isMinimalCounterexample_etaC` / `not_isMinimalCounterexample_ξg` above are
unconditional: for *every* choice of the remaining binders, `hξ : IsMinimalCounterexample ξ`
itself cannot be discharged when `ξ = etaC` or `ξ = ξg`, so no completion of
`exists_chainData`'s binder list can ever be built with those `ξ`.

**⚠ Scope of what has just been proved — read this before citing the above.** These theorems
show **these five specific bundles' `ξ` are not minimal counterexamples**. They do **not** show
"no minimal counterexample exists" — that unconditional statement *is* the Nivat conjecture
itself, and proving it here would end the whole project. The only thing `hξ` being unconditional
license us to conclude about `exists_chainData` is narrower but still load-bearing: **no leaf-A
statement carrying an `hξ` binder may ever be tested against `cgw`, `cgwA`, or `cgg`** — any such
test is vacuous (`hξ` is false for their `ξ`, so the implication holds trivially regardless of
what the rest of the statement says). This closes, as a kernel fact rather than prose, exactly
the gap that let earlier rounds spend compute testing `hpartner`, `nfp_L`, and `hxper` against
these three bundles: those tests were vacuously true from the start.

**§14 status update on the paragraph below**: the `cgwA`/`hpartner` question this file previously
left open is now **moot, not resolved** — `cgwA` is excluded by `hξ` regardless of what
`hpartner` says about it, so a fresh proof against `hpartner`'s current signature is no longer a
useful next unit. The paragraph is kept for the record (§14: status changes in place, nothing
deleted), with this note prepended.

**Not settled by `hdet_vl` (superseded by `hξ` above, kept for the record):** `cgw` and `cgwA`.
Both have `p = pv = (0,1)`, `vl = vlv = (0,-1)`, `det pv vlv = 0·(-1) - 1·0 = 0` — they *pass*
`hdet_vl`, and also pass the cheap checks `hp_ne : pv ≠ 0`, `hvl_ne : vlv ≠ 0` (`decide`),
`hp_mem : pv ∈ Per xperC` (`Step_PeriodsRays2.hp_per`, already on chain). Team-lead relayed a
prior (Amink) measurement that `cgwA` fails `hpartner` — `nℓ ⊥ vlv` forces `nℓ = (n, 0)`
(horizontal), and the resulting vertical half-plane agreement clause is claimed to force every
candidate `yper` to coincide with `xperC` itself, contradicting `hpartner`'s `xper ≠ yper`
conjunct. **This file does not verify that claim, and per the update above, no longer needs
to** — `hξ` already excludes `cgwA` unconditionally. Two reasons the claim was never verified
here: (1) no landed `.lean` declaration of it exists anywhere in the tree (only a docstring
cross-reference in `tmp/afill_faceblock_cgwA.lean`, which is a receipt, not a proof — `tmp/`
claims are not evidence per project policy); (2) `hpartner` was strengthened 2026-09-19
(`RegionSteps.lean:1009-1023`, three new conjuncts: strict inequality, a pinned disagreement
point `g`, and the `¬∃ h h', …` non-doubly-periodic clause) *after* whatever measurement produced
that claim, so even if the old argument was once verified, it targeted a different (weaker)
closure. -/

end Nivat.AResidual

#print axioms Nivat.AResidual.det_pv_vln_ne_zero
#print axioms Nivat.AResidual.not_hdet_vl_cgn
#print axioms Nivat.AResidual.det_p2_vl2_ne_zero
#print axioms Nivat.AResidual.det_pg_vlg_ne_zero
#print axioms Nivat.AResidual.etaC_zero_zero
#print axioms Nivat.AResidual.not_isCounterexample_etaC
#print axioms Nivat.AResidual.not_isMinimalCounterexample_etaC
#print axioms Nivat.AResidual.ξg_zero_zero
#print axioms Nivat.AResidual.not_isCounterexample_ξg
#print axioms Nivat.AResidual.not_isMinimalCounterexample_ξg
