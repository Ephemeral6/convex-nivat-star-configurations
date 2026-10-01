/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ItemII
import Nivat.External.Colle.ChainMax

/-!
# `rec_vJ`: closure under `+vJ` from the box conjunct

Lane RecVJ, 2026-09-19.  Produces the 25th hypothesis for `ChainDataGeom.ofParts`.

## The result

First prove that `⋃ i, hatOf A kk vl i` equals the half-plane `{z | cz ≤ ⟪nℓ,z⟫}` using
the box conjunct and `hkk` (kk-growth condition). Then `rec_vJ` is immediate from the identity.

**Key insight**: The ⊇ direction needs the box conjunct (`hbox`), not `Exhausts` — `hbox` lets
us pick the index that makes the shifted point land in the box, then `hkk` guarantees such an
index exists for any point in the half-plane.

-/

set_option autoImplicit false

open Nivat.LE2 Nivat.Colle35 Nivat.ChainAsm

namespace Nivat.RecVJ

/-- `hatOf` preserves membership up to a shift. -/
theorem mem_hatOf_iff {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ} {i : ℕ} {z : ℤ × ℤ} :
    z ∈ hatOf A kk vl i ↔ z + (kk i : ℤ) • vl ∈ A i :=
  Iff.rfl

/-- Adding `vJ` to a point preserves or increases the `nℓ`-layer when `0 ≤ dot nℓ vJ`. -/
theorem dot_add_vJ_mono {nℓ vJ : ℤ × ℤ} (hvJ : 0 ≤ dot nℓ vJ) (z : ℤ × ℤ) :
    dot nℓ z ≤ dot nℓ (z + vJ) := by
  simp only [dot_add]
  linarith

/-- The union `⋃ i, hatOf A kk vl i` equals the half-plane `{z | cz ≤ ⟪nℓ,z⟫}`.

**Proof sketch**:
- **⊆**: `g ∈ hatOf A kk vl i` means `g + (kk i)•vl ∈ A i ⊆ B (i+1)`, so `cz ≤ dot nℓ (g + kk i•vl)`.
  Since `vl ⊥ nℓ`, the `vl` term vanishes and we get `cz ≤ dot nℓ g`.
- **⊇**: Given `cz ≤ dot nℓ z`, take `i` from `hkk z` so `z + (kk (i+1))•vl` fits in the `i`-box.
  Then `hbox` gives `z + (kk (i+1))•vl ∈ B (i+1) ⊆ A (i+1)`, i.e., `z ∈ hatOf A kk vl (i+1)`.

原文：b3_colle2.txt:518-519 (双扫掠交集，item (ii) 的 `B_i` 增长) + :474 (item (ii) 的全方向增长)
-/
theorem iUnion_hatOf_eq_halfPlane
    {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0)
    (hlev  : ∀ i, ∀ z ∈ B i, cz ≤ dot nℓ z)
    (subBA : ∀ i, B i ⊆ A i)
    (subAB : ∀ i, A i ⊆ B (i + 1))
    (hbox  : ∀ i : ℕ, ∀ z : ℤ × ℤ, |z.1| ≤ (i : ℤ) → |z.2| ≤ (i : ℤ) → cz ≤ dot nℓ z →
              z ∈ B (i + 1))
    (hkk   : ∀ z : ℤ × ℤ, ∃ i : ℕ,
              |(z + (kk (i + 1) : ℤ) • vl).1| ≤ (i : ℤ) ∧
              |(z + (kk (i + 1) : ℤ) • vl).2| ≤ (i : ℤ)) :
    (⋃ i, hatOf A kk vl i) = {z | cz ≤ dot nℓ z} := by
  ext g
  constructor
  · -- ⊆ direction: if `g ∈ hatOf A kk vl i`, then `cz ≤ dot nℓ g`
    intro hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    rw [mem_hatOf_iff] at hi
    -- `g + (kk i)•vl ∈ A i ⊆ B (i+1)` by `subAB`
    have h_in_B : g + (kk i : ℤ) • vl ∈ B (i + 1) := subAB i hi
    -- `hlev (i+1)` gives `cz ≤ dot nℓ (g + (kk i)•vl)`
    have h_layer : cz ≤ dot nℓ (g + (kk i : ℤ) • vl) := hlev (i + 1) _ h_in_B
    -- Translation by `vl ⊥ nℓ` preserves layers
    have hdot_eq : dot nℓ (g + (kk i : ℤ) • vl) = dot nℓ g :=
      Colle35.dot_add_zsmul_of_perp hperp g (kk i : ℤ)
    rw [hdot_eq] at h_layer
    exact h_layer
  · -- ⊇ direction: if `cz ≤ dot nℓ z`, then `z ∈ ⋃ i, hatOf A kk vl i`
    intro hz
    -- Get `i` from `hkk g` such that `g + (kk (i+1))•vl` is in the `i`-box
    obtain ⟨i, hbox1, hbox2⟩ := hkk g
    -- Set `w := g + (kk (i+1))•vl`
    set w := g + (kk (i + 1) : ℤ) • vl with hw_def
    -- `dot nℓ w = dot nℓ g` by perpendicularity
    have hdot_w : dot nℓ w = dot nℓ g :=
      Colle35.dot_add_zsmul_of_perp hperp g (kk (i + 1) : ℤ)
    -- So `cz ≤ dot nℓ w`
    have hw_layer : cz ≤ dot nℓ w := by rw [hdot_w]; exact hz
    -- `hbox` gives `w ∈ B (i+1)` using the box bounds and layer bound
    have hw_in_B : w ∈ B (i + 1) := hbox i w hbox1 hbox2 hw_layer
    -- `subBA (i+1)` gives `w ∈ A (i+1)`
    have hw_in_A : w ∈ A (i + 1) := subBA (i + 1) hw_in_B
    -- This means `g ∈ hatOf A kk vl (i+1)`
    have : g ∈ hatOf A kk vl (i + 1) := by
      rw [mem_hatOf_iff]
      exact hw_in_A
    exact Set.mem_iUnion.mpr ⟨i + 1, this⟩

/-- The union `⋃ i, hatOf A kk vl i` is closed under `+vJ` when `0 ≤ ⟪nℓ, vJ⟫`.

This is the 25th hypothesis for `ChainDataGeom.ofParts` (`PartsToGeom.lean:15`).

**Supplied by the consumer**:
- `hperp`: `exists_itemII_chain`'s own standing assumption
- `hlev`: conjunct 4 of `exists_itemII_chain` (`ItemIIChain.lean:130`)
- `subBA`/`subAB`: conjuncts 6/7 (`:132-133`)
- `hbox`: conjunct 8 verbatim (`:134-135`)
- `hkk`: new, the kk-growth condition (honest residual)
- `hvJ`: to be supplied at call site; `dot nℓ vJ = 0` discharges it by `le_of_eq`/`simp`
-/
theorem rec_vJ_of_halfPlane
    {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nℓ vJ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0)
    (hlev  : ∀ i, ∀ z ∈ B i, cz ≤ dot nℓ z)
    (subBA : ∀ i, B i ⊆ A i)
    (subAB : ∀ i, A i ⊆ B (i + 1))
    (hbox  : ∀ i : ℕ, ∀ z : ℤ × ℤ, |z.1| ≤ (i : ℤ) → |z.2| ≤ (i : ℤ) → cz ≤ dot nℓ z →
              z ∈ B (i + 1))
    (hkk   : ∀ z : ℤ × ℤ, ∃ i : ℕ,
              |(z + (kk (i + 1) : ℤ) • vl).1| ≤ (i : ℤ) ∧
              |(z + (kk (i + 1) : ℤ) • vl).2| ≤ (i : ℤ))
    (hvJ : 0 ≤ dot nℓ vJ) :
    ∀ g ∈ (⋃ i, hatOf A kk vl i), g + vJ ∈ (⋃ i, hatOf A kk vl i) := by
  intro g hg
  -- Rewrite by the half-plane identity
  rw [iUnion_hatOf_eq_halfPlane hperp hlev subBA subAB hbox hkk] at hg ⊢
  -- `g` has `cz ≤ dot nℓ g`, and `g + vJ` has `dot nℓ (g + vJ) = dot nℓ g + dot nℓ vJ`
  simp only [Set.mem_setOf]
  calc cz ≤ dot nℓ g           := hg
       _  ≤ dot nℓ g + dot nℓ vJ := by linarith [hvJ]
       _  = dot nℓ (g + vJ)      := by rw [← dot_add]

end Nivat.RecVJ

-- verification
#print axioms Nivat.RecVJ.iUnion_hatOf_eq_halfPlane
#print axioms Nivat.RecVJ.rec_vJ_of_halfPlane
