/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LeafAJSelect
import Nivat.External.Colle.ShellRegionJ

/-!
# `hhp` from the `g_J`-pinning: `exists_gJ_pinned_ccw` feeds `hhp_of_faceStart_pinned`

Consumer: `ChainDataGeomParts.hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ`
(`ChainPartsFeed.lean`, `nJ := -J`, `cJ := dot nJ g_J`; `b3_colle2.txt:506`, the `ℓ_J` edge of
`Â_∞` is pinned once `faceStart (Â_i) J` stabilises).

`exists_gJ_pinned_ccw` (`LeafAJSelect.lean`) yields `σ`, `i₀` with
`∀ i ≥ i₀, faceStart (Ahat (σ i)) J = g_J`, i.e. a statement about the *re-indexed* tower.
`hhp_of_faceStart_pinned` (`ShellRegionJ.lean`) needs `hJmem`/`hgJ` for `i ≥ i₀`.  Here they are
joined, `nprevJ := ℓ` (so `hnprevdet` is literally `hℓJ`), and `i₀` is absorbed by the shift
`σ' i := σ (i + i₀)`, so the conclusion is the unconditional `∀ i`.

Nothing is assumed beyond `exists_gJ_pinned_ccw`'s own binders plus `Nonempty (Ahat i)`.
-/

set_option autoImplicit false

namespace Nivat.ConeHhpFeed

open Nivat Nivat.LE2 Nivat.PolyChain Nivat.PolyChainSum

theorem hhp_of_pinned_ccw
    {Ahat : ℕ → Set (ℤ × ℤ)} {Sphi : Finset (ℤ × ℤ)} {ℓ J g₁ : ℤ × ℤ}
    (hfin : ∀ i, (Ahat i).Finite) (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J)
    (hg₁ : ∀ i, faceStart (Ahat i) ℓ + (faceLen (Ahat i) ℓ : ℤ) • dir ℓ = g₁)
    (hArcbdd : ∀ μ ∈ Arc (Sphi.finite_toSet) ℓ J,
      ∃ L : ℕ, ∀ i, faceLen (Ahat i) μ ≤ L) :
    ∃ (g_J : ℤ × ℤ) (σ : ℕ → ℕ), StrictMono σ ∧
      (∀ i, faceStart (Ahat (σ i)) J = g_J) ∧
      ∀ i, Ahat (σ i) ⊆ halfPlaneGE (-J) (dot (-J) g_J) := by
  obtain ⟨g_J, σ, hσ, i₀, hpin⟩ :=
    LeafAJSelect.exists_gJ_pinned_ccw hfin hlc henv hSfin hSarea hℓE hJE hℓJ hg₁ hArcbdd
  have hσ' : StrictMono (fun i => σ (i + i₀)) := fun a b h => hσ (by omega)
  refine ⟨g_J, fun i => σ (i + i₀), hσ', fun i => hpin (i + i₀) (by omega), ?_⟩
  have hJmem : ∀ i, 0 ≤ i → J ∈ E (Ahat (σ (i + i₀))) := fun i _ => by
    rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv _)]; exact hJE
  have := ShellRegionJ.hhp_of_faceStart_pinned (Ahat := fun i => Ahat (σ (i + i₀)))
    (J := J) (gJ := g_J) (i₀ := 0) (fun i => hfin _) (fun i => hne _) (fun i => hlc _)
    hJmem (fun i _ => hpin (i + i₀) (by omega))
  exact fun i => this i (Nat.zero_le _)

end Nivat.ConeHhpFeed

#print axioms Nivat.ConeHhpFeed.hhp_of_pinned_ccw
