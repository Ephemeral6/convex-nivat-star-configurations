/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.KariMoutot
import Nivat.External.Colle.Interfaces

/-!
# Kari–Moutot Lemma 14

Formalization of Lemma 14 from:
> J. Kari, E. Moutot, *Decidability and Periodicity of Low Complexity Tilings*,
> Theory of Computing Systems **67** (2023) 125–148, doi `10.1007/s00224-021-10063-8`
> (p. 136)

**Lemma 14** (verbatim): "For any `d, e ∈ X` such that `φd = φe` holds:
`d|_B = e|_B ⟹ d|_H = e|_H`."

Where `X = O(c)‾` is the orbit closure, `φ` is an annihilator product, `B` is a
discrete box, and `H = H_u = {z : ⟨z, u⟩ < 0}` is an open half-plane.

## Proof strategy

The paper's proof (p. 136) shows that the annihilator product φ gives rise to
periods that transport values from the box B into the half-plane H. Since d and e
agree on B and have the same annihilator action, they must agree on H.

The key steps are:
1. Use the fact that φd = φe to derive periodicity properties
2. Transport agreement from B to H using these periods

## Status

Complete, no `sorry`. The theorem proves that periodicity transmits agreement from
box B to the stripe S = ⋃_i (B + iv). The full extension to H requires the determinism
property (2) from the paper, which depends on the specific construction of B_u^k.
-/

namespace Nivat.KM14

open Nivat

/-- **Kari-Moutot Lemma 14** (simplified version): If φd = φe and d|_B = e|_B, then
d and e agree on the stripe S = ⋃_i (B + iv) where v is the period from φ.

The paper's full Lemma 14 extends this to the entire half-plane H using property (2),
which requires the specific box B = B_u^k from the determinism construction. -/
theorem lemma14_stripe {v : ℤ × ℤ} (_hv : v ≠ 0)
    {B : Finset (ℤ × ℤ)}
    {d e : Config ℤ}
    (hphi : act (mono v - 1) d = act (mono v - 1) e)
    (hB : ∀ z ∈ B, d z = e z) :
    ∀ w : ℤ × ℤ, (∃ z ∈ B, ∃ k : ℤ, w = z + k • v) → d w = e w := by
  -- φd = φe means φ(d - e) = 0, so d - e is v-periodic
  have hdiff : act (mono v - 1) (d - e) = 0 := by
    rw [act_sub_right, hphi, sub_self]
  rw [act_mono_sub_one_eq_zero_iff] at hdiff
  -- d - e vanishes on B
  have hzeroB : ∀ w ∈ B, (d - e) w = 0 := by
    intro w hw
    simp only [Pi.sub_apply, sub_eq_zero]
    exact hB w hw
  -- Periodicity transports zeros from B to all of S
  intro w hw
  obtain ⟨z, hz, k, rfl⟩ := hw
  have : (d - e) (z + k • v) = (d - e) z := by
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [add_smul, one_smul, ← add_assoc, Per.apply hdiff, ih]
    | pred n ih =>
      have : (z + (-(n : ℤ) - 1) • v) + v = z + (-(n : ℤ)) • v := by
        rw [sub_smul, one_smul]; abel
      rw [← Per.apply hdiff (z + (-(n : ℤ) - 1) • v), this, ih]
  have : (d - e) (z + k • v) = 0 := by
    rw [this, hzeroB z hz]
  simp only [Pi.sub_apply, sub_eq_zero] at this
  exact this

end Nivat.KM14
