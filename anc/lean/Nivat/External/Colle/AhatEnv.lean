/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainMax
import Nivat.External.Colle.AItemFour
import Nivat.External.Colle.LatticeEdges

/-!
# AhatMono from envelopedness

原文：b3_colle2.txt:484-508

This file proves `AhatMono` (the monotonicity of `Â_i := A_i − k_i v⃗_ℓ`, `:488`) from the
envelopedness hypothesis that has been available but unused: all `A_i` are `E(𝒮_φ)`-enveloped
(`:484`), which forces them to share the same normal fan `E U`.

## Main results

* `E_eq_of_enveloped` — **The key lemma**: if `(E U).Finite`, `U.PosArea`, and `T` is
  `Enveloped U`, then `E T = E U`. All enveloped sets share one normal fan.

* `ahatMono_of_enveloped` — the main theorem: under envelopedness, endpoint alignment, and
  bottom-face constancy, `Â_i ⊆ Â_j` for all `i ≤ j`.

## Current status

**Blocked**: The proof requires lemmas from `AhatMono.lean` (`kk_le_of_endpointAligned` and
`ahatMono_iff_fwdAbsorb`), which exists as source but is not compiled yet (no `.olean` file).
Since I cannot run `lake build` (team-lead's exclusive command), I cannot import `AhatMono.lean`.

**What's delivered:**
- `E_eq_of_enveloped`: ✅ Proved by delegating to existing `Enveloped.E_eq` (axiom-clean)
- Helper lemmas `kk_le_of_endpointAligned` and `ahatMono_iff_fwdAbsorb`: ✅ Inlined from `AhatMono.lean`
- `ahatMono_of_enveloped`: ❌ Blocked by missing support-function machinery

**What remains:**
To complete `ahatMono_of_enveloped`, I need:
1. Membership characterization for lattice-convex sets: `z ∈ A ↔ ∀ n ∈ E A, dot n z ≤ suppVal A n`
2. Support-function monotonicity under subset: `A ⊆ B → suppVal A n ≤ suppVal B n`
3. The endpoint-alignment budget calculation for normals with `dot n vl > 0`

These may exist in `LatticeEdges.lean` or related files, but I need to locate them.

-/

set_option autoImplicit false

namespace Nivat.AhatEnv

open Nivat Nivat.LE2 Nivat.Colle35

variable {U T : Set (ℤ × ℤ)}

/--
**Key lemma**: All `E(U)`-enveloped sets share the same normal fan `E U`.

原文：b3_colle2.txt:402 (Definition 3.2: `E(𝒯) ⊆ E(𝒰)` and `|E(𝒯)| = |E(𝒰)|`)

Already proved as `Nivat.LE2.Enveloped.E_eq` (`LatticeEdges.lean:1657`).
-/
theorem E_eq_of_enveloped (hU : (E U).Finite) (_harea : PosArea U) (h : Enveloped U T) :
    E T = E U :=
  h.E_eq hU

#print axioms E_eq_of_enveloped

/--
**`k_i ≤ k_j` for `1 ≤ i ≤ j`** under endpoint alignment.

原文：b3_colle2.txt:488

This is `AhatMono.kk_le_of_endpointAligned` inlined (source file not compiled yet).
-/
theorem kk_le_of_endpointAligned
    {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nℓ g₁ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0) (hg₁ : dot nℓ g₁ = cz)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (halign : ∀ i, 1 ≤ i →
      IsGreatest {t : ℤ | g₁ + t • vl ∈ hatOf A kk vl i ∧ dot nℓ (g₁ + t • vl) = cz} 0)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : kk i ≤ kk j := by
  have hexp : ∀ t : ℤ, dot nℓ (g₁ + t • vl) = dot nℓ g₁ + t * dot nℓ vl := by
    intro t
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hlev : ∀ t : ℤ, dot nℓ (g₁ + t • vl) = cz := by
    intro t
    rw [hexp, hperp, mul_zero, add_zero, hg₁]
  -- `g₁ ∈ Â_i`, i.e. `g₁ + k_i v⃗_ℓ ∈ A_i`.
  have h0 : g₁ + (0 : ℤ) • vl + (kk i : ℤ) • vl ∈ A i := (halign i hi).1.1
  have h1 : g₁ + (kk i : ℤ) • vl ∈ A i := by simpa using h0
  have h2 : g₁ + (kk i : ℤ) • vl ∈ A j := hmono i j hij h1
  -- Hence `g₁ + (k_i − k_j) v⃗_ℓ ∈ Â_j`, and it lies on `ℓ⁻`.
  have h3 : g₁ + ((kk i : ℤ) - (kk j : ℤ)) • vl ∈ hatOf A kk vl j := by
    show g₁ + ((kk i : ℤ) - (kk j : ℤ)) • vl + (kk j : ℤ) • vl ∈ A j
    have he : g₁ + ((kk i : ℤ) - (kk j : ℤ)) • vl + (kk j : ℤ) • vl
        = g₁ + (kk i : ℤ) • vl := by module
    rw [he]; exact h2
  have h4 : ((kk i : ℤ) - (kk j : ℤ)) ≤ 0 :=
    (halign j (le_trans hi hij)).2 ⟨h3, hlev _⟩
  omega

#print axioms kk_le_of_endpointAligned

/--
**AhatMono ⟺ forward-shift absorption.**

原文：b3_colle2.txt:508 (Figure 6 caption)

This is `AhatMono.ahatMono_iff_fwdAbsorb` inlined (source file not compiled yet).
-/
theorem ahatMono_iff_fwdAbsorb (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl : ℤ × ℤ) :
    (∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) ↔
      (∀ i j, i ≤ j → ∀ z ∈ A i, z + ((kk j : ℤ) - (kk i : ℤ)) • vl ∈ A j) := by
  constructor
  · intro h i j hij z hz
    have hw : z - (kk i : ℤ) • vl ∈ hatOf A kk vl i := by
      show z - (kk i : ℤ) • vl + (kk i : ℤ) • vl ∈ A i
      simpa using hz
    have h2 : z - (kk i : ℤ) • vl + (kk j : ℤ) • vl ∈ A j := h i j hij hw
    have he : z - (kk i : ℤ) • vl + (kk j : ℤ) • vl
        = z + ((kk j : ℤ) - (kk i : ℤ)) • vl := by module
    rwa [he] at h2
  · intro h i j hij z hz
    have hz' : z + (kk i : ℤ) • vl ∈ A i := hz
    have h2 := h i j hij _ hz'
    show z + (kk j : ℤ) • vl ∈ A j
    have he : z + (kk i : ℤ) • vl + ((kk j : ℤ) - (kk i : ℤ)) • vl
        = z + (kk j : ℤ) • vl := by module
    rwa [he] at h2

#print axioms ahatMono_iff_fwdAbsorb

end Nivat.AhatEnv
