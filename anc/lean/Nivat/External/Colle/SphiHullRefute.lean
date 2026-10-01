/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Claim36
import Nivat.External.Colle.NewtonZonotope
import Nivat.External.Colle.DecompData

/-!
# `hS_hull` is false for the `S` actually on the chain

team-lead's 2026-09-19 assignment: `Nivat.Colle36.generatingSet_no_edge_parallel`
(`Claim36.lean:741`) needs `hS_hull : Conv S = Conv (supp (∏ i ∈ univ.erase i_m, (mono (h i) -
1)))` — the **erased** product (Collé's `𝒮_ψ`, `b3_colle2.txt:563-571`, "`η − η̄_m`"). What is
actually on the chain is `Nivat.Colle.DecompData.Sphi_eq` (`DecompData.lean:108`):
`Conv Sphi = Conv (supp (∏ i : Fin m, (mono (h i) - 1)))` — the **full** product, index `i_m`
**included** (Collé's `𝒮_φ`). `RegionSteps.lean:1122,1182,1220,1759` all run `Case1` on
`d.Sphi`, i.e. on `𝒮_φ`, not `𝒮_ψ`.

This file settles, at the kernel, that these are not interchangeable: `hS_hull` — read with
`S := zonoF (Finset.univ) h`, the natural `𝒮_φ` witness — is **false** for a concrete
`m = 2` instance. Not merely "unavailable": refuted.

## The instance

`h := ![(1,0), (0,1)]`, `i_m := 0`, `ℓ_m := (1,0)` (`h i_m = 1 • ℓ_m`). Both existing lemmas
this reuses are already on-chain and `sorry`-free:

* `Nivat.LE2.zonoF_unit_square` (`NewtonZonotope.lean:218`) — the **full** product's zonotope
  (`Finset.univ`, both generators) is the unit square `{(0,0),(1,0),(0,1),(1,1)}`.
* `Nivat.LE2.mem_E_zonoF_unit_square` (`NewtonZonotope.lean:229`) — `(0,1)` is an edge normal
  of that square, and `dot (0,1) (1,0) = 0`.

So the full hull has an edge normal `n₀ := (0,1)` with `dot n₀ ℓ_m = 0` — i.e.
`IsEdge (↑(zonoF univ h)) n₀` holds. If `hS_hull` held for `S := zonoF univ h` against the
**erased** product (index `0` dropped, leaving only `h 1 = (0,1)`, whose hull is the segment
`[0,(0,1)]`), `generatingSet_no_edge_parallel` would force `dot n₀ ℓ_m ≠ 0` for every edge
normal of `S` — contradicting the `n₀` just exhibited. Hence `hS_hull` is false for this `S`.

## Reading

This refutes the *instance* `S := zonoF univ h`, not merely a route to a general statement,
so PROTOCOL §25 does not blunt it: no `hξ`/`¬∀`-style binder shields this conclusion, the
witness is fully concrete and closed. What it shows is structural, not an artefact of this
particular `h`: the erased product drops exactly the generator `h i_m` that, together with a
neighbour, produces the edge `n₀ ⊥ ℓ_m` in the full zonotope — Collé erases that factor
(Claim 3.6 is about `η − η̄_m`, `b3_colle2.txt:563-571`) precisely because the *full* hull can
carry such an edge and the *erased* one provably cannot (`zono_no_edge_parallel`). So `𝒮_φ`
and `𝒮_ψ` are hulls of genuinely different shape in general, not just in this witness.
-/

set_option autoImplicit false

namespace Nivat.SphiHullRefute

open Nivat Nivat.LE2

/-! ## The instance data -/

/-- The two generators: the standard basis, matching `zonoF_unit_square`/
`mem_E_zonoF_unit_square` verbatim so no new zonotope computation is needed. -/
def hGen : Fin 2 → ℤ × ℤ := ![((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))]

theorem hGen_ne (i : Fin 2) : hGen i ≠ 0 := by fin_cases i <;> decide

theorem hGen_dir : ∀ i j : Fin 2, i ≠ j → det (hGen i) (hGen j) ≠ 0 := by decide

/-- `i_m := 0`; the erased direction `ℓ_m := hGen 0 = (1,0)`, primitive, `c := 1`. -/
theorem hℓ_dir_inst : ∃ c : ℤ, c ≠ 0 ∧ hGen (0 : Fin 2) = c • ((1 : ℤ), (0 : ℤ)) := ⟨1, by decide, by decide⟩

theorem ℓm_prim : Primitive ((1 : ℤ), (0 : ℤ)) := ⟨1, 0, by ring⟩

/-! ## The edge that survives in the full product but is forbidden in the erased one -/

/-- **The refutation.** `hS_hull` — with the natural `𝒮_φ` witness `S := zonoF univ hGen`,
against the *erased* product at `i_m := 0` — is false. -/
theorem not_hS_hull_of_full_zonoF :
    ¬ (Conv (zonoF (Finset.univ : Finset (Fin 2)) hGen)
        = Conv (supp (∏ i ∈ (Finset.univ : Finset (Fin 2)).erase (0 : Fin 2),
            (mono (hGen i) - 1 : LaurentTwo ℤ)))) := by
  intro heq
  have hforbidden := Nivat.Colle36.generatingSet_no_edge_parallel
    (h := hGen) (le_refl 2) hGen_ne hGen_dir
    (i_m := (0 : Fin 2)) (ℓ_m := ((1 : ℤ), (0 : ℤ))) ℓm_prim hℓ_dir_inst heq
  have hedge : ((0 : ℤ), (1 : ℤ)) ∈
      E (↑(zonoF (Finset.univ : Finset (Fin 2)) hGen) : Set (ℤ × ℤ)) :=
    mem_E_zonoF_unit_square
  exact hforbidden _ hedge (by decide)

/-- **Named per team-lead's request**: the full product's hull carries an edge with normal
`⊥ ℓ_m` — `IsEdge` holds outright, unconditionally (no `hS_hull` needed to state this half). -/
theorem isEdge_perp_of_full_product :
    IsEdge (↑(zonoF (Finset.univ : Finset (Fin 2)) hGen) : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ))
      ∧ dot ((0 : ℤ), (1 : ℤ)) (hGen (0 : Fin 2)) = 0 :=
  ⟨mem_E_zonoF_unit_square, by decide⟩

end Nivat.SphiHullRefute

#print axioms Nivat.SphiHullRefute.not_hS_hull_of_full_zonoF
#print axioms Nivat.SphiHullRefute.isEdge_perp_of_full_product
