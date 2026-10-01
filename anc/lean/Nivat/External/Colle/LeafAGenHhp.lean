/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellRegionJ
import Nivat.External.Colle.AhatEnv
import Nivat.External.Colle.LeafAJSelect

/-!
# `leafagen-hhp-all` — `hhp` as a standalone declaration (lane-leafa-gen)

`ChainDataGeomParts.hhp` (`ChainPartsFeed.lean:220`) is
`∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ`, **unguarded and on the raw index**.  The
on-tree producer `ShellRegionJ.hhp_of_faceStart_pinned` (`ShellRegionJ.lean:72`) delivers
`∀ i, i₀ ≤ i → …`, and the `g_J` it needs arrives from
`LeafAJSelect.exists_gJ_pinned_ccw` (`LeafAJSelect.lean:488`) only **along a subsequence
`σ`** (`:499-500`).  Two mismatches, both absorbed here by `AhatMono`.

⚠ **This is an extraction, not a new proof.**  The argument already exists as a `have`
inside `tmp/wip/LeafAAssemble.lean`'s big theorem (`hhp_all`, `:778-781`, and the `cw`
twin at `:907`), whose enclosing declaration is **not** sorry-free (`:1162-1163`).
`:750-755` of that file records the step as a named GAP requiring "a second full
reindexing pass"; `:771-777` withdraws that claim in place.  What this file adds is that
the step becomes a named, chain-generic, `#print axioms`-checkable declaration instead of
a fragment of a sorry-carrying proof body — the same service `LeafAGenRecP` performs for
`rec_p`.

Paper: the `(ℓ,ℓ_J)`-region sentence at `scratch/b3_colle2.txt:506` ("In particular,
`Â_∞ := ⋃ Â_i` is a weakly `E(𝒮_φ)`-enveloped set … with two semi-infinite edges, one of
which is parallel to `ℓ` and the other one is parallel to `ℓ_J`").  §1's four upstream
premises of that "In particular" are `:496` (period-`ℓ` subsequence), `:498` (`w_i(j)`
and the choice of `J`), `:500` (the strict-growth defining `J`), `:504` (the
layerwise-constant intermediate edges).  ⛔ **None of them is discharged here**: they are
`exists_gJ_pinned_ccw`'s own hypotheses, and §3 below takes that theorem's conclusion as
given.  §1/§2 are exactly the two index mismatches, nothing more.

⚠ `nJ := -J` and `cJ := dot nJ g_J` are **not choices made here**: they are pinned by
`LaneCdSwept.sweptClosed_of_pinned_ccw`'s binders `hnJ`/`hcJ`
(`LeafASwept.lean:102-103`), so §4 states the field in exactly that parametrisation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Nivat.LeafAGenHhp

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.PolyChain

/-! ## §0. The two `halfPlaneGE`s are the same set

`ChainPartsFeed.lean:220` / `ShellRegionJ.lean:77` read `halfPlaneGE` in `Nivat.LE2`
(`LatticeEdges.lean:1836`); `tmp/wip/LeafAAssemble.lean:778` writes
`Nivat.CK224.halfPlaneGE` (`CyrKra224.lean:86`) while feeding it a `ShellRegionJ` result.
That wiring is already silently relying on the two being the same object.  They are —
both are `{z | c ≤ dot n z}` — but nothing on the tree said so. -/

theorem halfPlaneGE_eq (n : ℤ × ℤ) (c : ℤ) :
    Nivat.LE2.halfPlaneGE n c = Nivat.CK224.halfPlaneGE n c := rfl

/-! ## §1. `J ∈ E (Â_i)` costs nothing, and holds at **every** index

`hhp_of_faceStart_pinned`'s `hJmem` binder is guarded (`i₀ ≤ i`), which invites reading
it as content.  It is not: envelopment pins the whole normal fan
(`AhatEnv.E_eq_of_enveloped`, `AhatEnv.lean:61`), so `J ∈ E ↑Sphi` transports to every
layer with no index condition at all. -/

theorem mem_E_all_of_enveloped {Ahat : ℕ → Set (ℤ × ℤ)} {Sphi : Finset (ℤ × ℤ)} {J : ℤ × ℤ}
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ))) :
    ∀ i, J ∈ E (Ahat i) := by
  intro i
  rw [Nivat.AhatEnv.E_eq_of_enveloped hSfin hSarea (henv i)]
  exact hJE

/-! ## §2. The two index mismatches, absorbed by `AhatMono`

Given `i`, the index `j := σ (i + i₀)` clears both guards at once: `i₀ ≤ i + i₀` lets
`hhp_of_faceStart_pinned` fire at it, and `i ≤ i + i₀ ≤ σ (i + i₀)`
(`StrictMono.le_apply`) lets `AhatMono` carry the bound back down to `Â_i`.  So neither
the `i₀`-guard nor the subsequence `σ` survives, and **no second reindexing of the chain
is required** — in particular `envB` / `maxA` / `subBA` / `subAB` / `hfin` /
`ahat_nonempty` / `rec_p` / `hexh` are untouched. -/

theorem hhp_all_of_gJ_pinned {Ahat : ℕ → Set (ℤ × ℤ)} {J gJ : ℤ × ℤ}
    {σ : ℕ → ℕ} {i₀ : ℕ}
    (hfin : ∀ i, (Ahat i).Finite) (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (hmono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j)
    (hσ : StrictMono σ)
    (hJmem : ∀ i, J ∈ E (Ahat i))
    (hgJ : ∀ i, i₀ ≤ i → faceStart (Ahat (σ i)) J = gJ) :
    ∀ i, Ahat i ⊆ halfPlaneGE (-J) (dot (-J) gJ) := by
  have hpartial : ∀ i, i₀ ≤ i → Ahat (σ i) ⊆ halfPlaneGE (-J) (dot (-J) gJ) :=
    Nivat.ShellRegionJ.hhp_of_faceStart_pinned (Ahat := fun i => Ahat (σ i))
      (fun i => hfin (σ i)) (fun i => hne (σ i)) (fun i => hlc (σ i))
      (fun i _ => hJmem (σ i)) hgJ
  intro i
  refine subset_trans (hmono i (σ (i + i₀)) ?_) (hpartial (i + i₀) (by omega))
  exact le_trans (Nat.le_add_right i i₀) hσ.le_apply

/-! ## §3. End to end from `exists_gJ_pinned_ccw`

Binder for binder this is `LeafAJSelect.exists_gJ_pinned_ccw` (`LeafAJSelect.lean:488`)
plus `hne` and `hmono`.  The `σ` and the `i₀` it produces are both consumed here and do
not appear in the conclusion. -/

theorem exists_hhp_all_ccw {Ahat : ℕ → Set (ℤ × ℤ)} {Sphi : Finset (ℤ × ℤ)}
    {ℓ J g₁ : ℤ × ℤ}
    (hfin : ∀ i, (Ahat i).Finite) (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (hmono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j)
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (Ahat i))
    (hSfin : (E (↑Sphi : Set (ℤ × ℤ))).Finite) (hSarea : PosArea (↑Sphi : Set (ℤ × ℤ)))
    (hℓE : ℓ ∈ E (↑Sphi : Set (ℤ × ℤ))) (hJE : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hℓJ : 0 < det ℓ J)
    (hg₁ : ∀ i, faceStart (Ahat i) ℓ + (faceLen (Ahat i) ℓ : ℤ) • dir ℓ = g₁)
    (hArcbdd : ∀ μ ∈ Nivat.PolyChainSum.Arc (Sphi.finite_toSet) ℓ J,
      ∃ L : ℕ, ∀ i, faceLen (Ahat i) μ ≤ L) :
    ∃ gJ : ℤ × ℤ, ∀ i, Ahat i ⊆ halfPlaneGE (-J) (dot (-J) gJ) := by
  obtain ⟨gJ, σ, hσ, i₀, hgJ⟩ :=
    Nivat.LeafAJSelect.exists_gJ_pinned_ccw hfin hlc henv hSfin hSarea hℓE hJE hℓJ hg₁ hArcbdd
  exact ⟨gJ, hhp_all_of_gJ_pinned hfin hne hlc hmono hσ
    (mem_E_all_of_enveloped hSfin hSarea henv hJE) (fun i hi => hgJ i hi)⟩

/-! ## §4. The consumer's parametrisation

`ChainDataGeomParts.hhp` (`ChainPartsFeed.lean:220`) is stated in `nJ`/`cJ`, and those two
are pinned to `-J` / `dot nJ g_J` by `LaneCdSwept.sweptClosed_of_pinned_ccw`'s binders
`hnJ`/`hcJ` (`LeafASwept.lean:102-103`).  Under that substitution §2's conclusion is the
field, character for character. -/

theorem hhp_field_of_gJ_pinned {Ahat : ℕ → Set (ℤ × ℤ)} {J gJ nJ : ℤ × ℤ} {cJ : ℤ}
    {σ : ℕ → ℕ} {i₀ : ℕ}
    (hnJ : nJ = -J) (hcJ : cJ = dot nJ gJ)
    (hfin : ∀ i, (Ahat i).Finite) (hne : ∀ i, (Ahat i).Nonempty)
    (hlc : ∀ i, IsLatticeConvexRegion (Ahat i))
    (hmono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j)
    (hσ : StrictMono σ)
    (hJmem : ∀ i, J ∈ E (Ahat i))
    (hgJ : ∀ i, i₀ ≤ i → faceStart (Ahat (σ i)) J = gJ) :
    ∀ i, Ahat i ⊆ halfPlaneGE nJ cJ := by
  subst hnJ; subst hcJ
  exact hhp_all_of_gJ_pinned hfin hne hlc hmono hσ hJmem hgJ

/-! ## §5. Both absorbed binders are load-bearing (kernel witnesses)

Neither §2 hypothesis is decoration.  ⛔ These refute the **stated general forms only**;
they say nothing about whether a real tower satisfies them (§54). -/

/-- Without `hmono`, the `i₀`-guard cannot be dropped: layer `0` is unconstrained. -/
theorem not_all_of_guarded_without_mono :
    ¬ (∀ (Ahat : ℕ → Set (ℤ × ℤ)) (n : ℤ × ℤ) (c : ℤ) (i₀ : ℕ),
        (∀ i, i₀ ≤ i → Ahat i ⊆ halfPlaneGE n c) → ∀ i, Ahat i ⊆ halfPlaneGE n c) := by
  intro h
  have hcontra := h (fun i => if i = 0 then Set.univ else ∅) 0 1 1 ?_ 0
    (Set.mem_univ ((0 : ℤ), (0 : ℤ)))
  · have hx : (1 : ℤ) ≤ dot 0 ((0 : ℤ), (0 : ℤ)) := hcontra
    simp [Nivat.LE2.dot] at hx
  · intro i hi
    have hi0 : i ≠ 0 := by omega
    simp [hi0]

/-- Without `StrictMono σ`, a pinned `faceStart` along `σ` constrains only the layers `σ`
actually visits: a constant `σ` pins one layer and says nothing about the rest, even with
`hmono` in hand. -/
theorem not_all_of_subseq_without_strictMono :
    ¬ (∀ (Ahat : ℕ → Set (ℤ × ℤ)) (σ : ℕ → ℕ) (n : ℤ × ℤ) (c : ℤ) (i₀ : ℕ),
        (∀ i j, i ≤ j → Ahat i ⊆ Ahat j) →
        (∀ i, i₀ ≤ i → Ahat (σ i) ⊆ halfPlaneGE n c) → ∀ i, Ahat i ⊆ halfPlaneGE n c) := by
  intro h
  have hcontra := h (fun i => if i = 0 then ∅ else Set.univ) (fun _ => 0) 0 1 0 ?_ ?_ 1
    (Set.mem_univ ((0 : ℤ), (0 : ℤ)))
  · have hx : (1 : ℤ) ≤ dot 0 ((0 : ℤ), (0 : ℤ)) := hcontra
    simp [Nivat.LE2.dot] at hx
  · intro i j _
    by_cases hi : i = 0
    · simp [hi]
    · by_cases hj : j = 0
      · subst hj; omega
      · simp [hi, hj]
  · intro i _
    simp

end Nivat.LeafAGenHhp

#print axioms Nivat.LeafAGenHhp.halfPlaneGE_eq
#print axioms Nivat.LeafAGenHhp.mem_E_all_of_enveloped
#print axioms Nivat.LeafAGenHhp.hhp_all_of_gJ_pinned
#print axioms Nivat.LeafAGenHhp.exists_hhp_all_ccw
#print axioms Nivat.LeafAGenHhp.hhp_field_of_gJ_pinned
#print axioms Nivat.LeafAGenHhp.not_all_of_guarded_without_mono
#print axioms Nivat.LeafAGenHhp.not_all_of_subseq_without_strictMono
