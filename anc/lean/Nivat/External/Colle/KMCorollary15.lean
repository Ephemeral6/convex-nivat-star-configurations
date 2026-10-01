/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.KariMoutot

/-!
# Kari–Moutot Corollary 15

**Corollary 15** (p. 136 of Kari–Moutot 2023):

> "Let c₁, …, cₙ ∈ X be pairwise distinct. If φc₁ = ⋯ = φcₙ then n ≤ |A|^|B|."

Source: J. Kari, E. Moutot, *Decidability and Periodicity of Low Complexity Tilings*,
Theory of Computing Systems **67** (2023) 125–148, doi `10.1007/s00224-021-10063-8`,
Corollary 15 (p. 136).

## Context

This corollary bounds the number of pairwise distinct configurations in a subshift
that can have the same annihilator product value. It is used in the proof of
Proposition 18 to ensure the maximal n construction terminates.

## Statement

Given:
- A configuration c with finite range A ⊆ ℤ
- A discrete box B ⊆ ℤ²
- Pairwise distinct configurations c₁,...,cₙ

If all cᵢ have the same value under some map (in the paper, φcᵢ = φcⱼ for all i,j),
and Lemma 14 ensures they differ on B, then n ≤ |A|^|B| since there are only
|A|^|B| distinct patterns on B.

-/

namespace Nivat.KM15

open Nivat

/-- **Kari–Moutot Corollary 15** (p. 136): Bound on configurations with matching
annihilator products.

Given pairwise distinct configurations c₁,...,cₙ in the orbit closure, all taking
values in finite alphabet A, if they are pairwise distinct but some property
forces them to differ on a box B, then n ≤ |A|^|B|.

This is the combinatorial heart of the argument: there are only finitely many
patterns on B. -/
theorem corollary15 {A : Finset ℤ} {B : Finset (ℤ × ℤ)} {n : ℕ}
    {configs : Fin n → Config ℤ}
    (hrange : ∀ i z, configs i z ∈ A)
    (hdist : ∀ i j : Fin n, i ≠ j → configs i ≠ configs j)
    (hdistB : ∀ i j : Fin n, i ≠ j → ∃ z ∈ B, configs i z ≠ configs j z) :
    n ≤ A.card ^ B.card := by
  classical
  -- The key: restriction to B is injective and maps into A^B
  set g : Fin n → (B → A) := fun i z => ⟨configs i z.1, hrange i z.1⟩ with hg
  have hinj : Function.Injective g := by
    intro i j heq
    by_contra hij
    obtain ⟨z, hzB, hne⟩ := hdistB i j hij
    have : configs i z = configs j z := by
      have := congrFun heq ⟨z, hzB⟩
      exact Subtype.ext_iff.mp this
    exact hne this
  -- Injective function from Fin n into finite type B → A
  calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
       _ ≤ Fintype.card (B → A) := Fintype.card_le_of_injective g hinj
       _ = Fintype.card A ^ Fintype.card B := Fintype.card_fun
       _ = A.card ^ B.card := by simp [Fintype.card_coe]

end Nivat.KM15
