/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.NoEdgePlacement
import Nivat.External.Colle.LatticeEdges

/-!
# Strict argmin from unique argmin, and transverse step lemmas

原文：b3_colle2.txt:792-800

When a finite set has no edge parallel to a given direction (Lemma 2.6), the extreme vertex
in that direction is unique. This file derives the strict inequality form: all other points
are **strictly** on the opposite side, not just weakly. This strict separation is the key
to the transverse sweep step in Claim 4.6 (lines :794-798).

## Main results

* `strict_argmin_of_unique` — unique argmin ⟹ strict argmin
* `lt_dot_translate_of_strict` — translating preserves strict separation
* `succ_le_dot_translate` — integer grid: strict > means ≥ +1 (induction step)

-/

namespace Nivat.LE2

open Finset

/-- 原文：b3_colle2.txt:792（Lemma 2.6 无平行边）

唯一 argmin ⟹ 严格 argmin。

**量词对应：**
- `S : Finset (ℤ × ℤ)` ↔ the finite lattice set
- `n : ℤ × ℤ` ↔ the transverse normal (perpendicular to the line direction)
- `a : ℤ × ℤ` ↔ the unique argmin point
- `ha : a ∈ S` ↔ `a` is in the set
- `hmin : ∀ z ∈ S, dot n a ≤ dot n z` ↔ `a` achieves the minimum
- `huniq : ∀ b ∈ S, (∀ z ∈ S, dot n b ≤ dot n z) → b = a` ↔ uniqueness of argmin
- Conclusion: `∀ z ∈ S.erase a, dot n a < dot n z` ↔ all other points are strictly higher

Proof: by contradiction. If some `z ≠ a` has `dot n z = dot n a`, then `z` is also an argmin,
contradicting uniqueness. -/
theorem strict_argmin_of_unique {S : Finset (ℤ × ℤ)} {n a : ℤ × ℤ}
    (ha : a ∈ S) (hmin : ∀ z ∈ S, dot n a ≤ dot n z)
    (huniq : ∀ b ∈ S, (∀ z ∈ S, dot n b ≤ dot n z) → b = a) :
    ∀ z ∈ S.erase a, dot n a < dot n z := by
  intro z hz
  have hz_in : z ∈ S := mem_of_mem_erase hz
  have hz_ne : z ≠ a := ne_of_mem_erase hz
  -- We have dot n a ≤ dot n z by hmin
  have hle : dot n a ≤ dot n z := hmin z hz_in
  -- Claim: strict inequality
  by_contra h_not_strict
  push_neg at h_not_strict
  -- So dot n a = dot n z (since we have ≤ and not <)
  have heq : dot n a = dot n z := le_antisymm hle h_not_strict
  -- Now z is also an argmin
  have hz_min : ∀ w ∈ S, dot n z ≤ dot n w := by
    intro w hw
    calc dot n z = dot n a := by rw [← heq]
                _ ≤ dot n w := hmin w hw
  -- By uniqueness, z = a
  have : z = a := huniq z hz_in hz_min
  -- But z ≠ a, contradiction
  exact hz_ne this

/-- 原文：b3_colle2.txt:794-798

把 `S` 平移到 `a` 落在 `w`，其余点严格抬高一层。

**量词对应：**
- `S : Finset (ℤ × ℤ)` ↔ the finite lattice set
- `n : ℤ × ℤ` ↔ the transverse normal
- `a : ℤ × ℤ` ↔ the unique argmin point (to be placed at `w`)
- `w : ℤ × ℤ` ↔ the target position on the line
- `hstrict : ∀ z ∈ S.erase a, dot n a < dot n z` ↔ strict separation before translation
- Conclusion: `∀ z ∈ S.erase a, dot n w < dot n (z + (w - a))` ↔ strict separation after

The translation vector is `v := w - a`. After translation, `a` lands at `w`, and each
`z ∈ S.erase a` lands at `z + v = z + (w - a)`. The strict inequality is preserved. -/
theorem lt_dot_translate_of_strict {S : Finset (ℤ × ℤ)} {n a w : ℤ × ℤ}
    (hstrict : ∀ z ∈ S.erase a, dot n a < dot n z) :
    ∀ z ∈ S.erase a, dot n w < dot n (z + (w - a)) := by
  intro z hz
  have h : dot n a < dot n z := hstrict z hz
  -- Expand dot: dot n x = n.1 * x.1 + n.2 * x.2
  -- After translation by (w - a), point z becomes z + (w - a)
  -- We need: dot n w < dot n (z + (w - a))
  simp only [dot]
  -- Simplify the product components
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  -- Now goal: n.1 * w.1 + n.2 * w.2 < n.1 * (z.1 + w.1 - a.1) + n.2 * (z.2 + w.2 - a.2)
  -- From h: n.1 * a.1 + n.2 * a.2 < n.1 * z.1 + n.2 * z.2
  have h' : n.1 * a.1 + n.2 * a.2 < n.1 * z.1 + n.2 * z.2 := by simp only [dot] at h; exact h
  linarith

/-- 原文：b3_colle2.txt:794-798（归纳闭合关键）

整数格上「严格大于」就是「≥ +1」，这是归纳能闭合的关键一步。

**量词对应：**
- `S : Finset (ℤ × ℤ)` ↔ the finite lattice set
- `n : ℤ × ℤ` ↔ the transverse normal
- `a : ℤ × ℤ` ↔ the unique argmin point
- `w : ℤ × ℤ` ↔ the target position on the line
- `hstrict : ∀ z ∈ S.erase a, dot n a < dot n z` ↔ strict separation
- Conclusion: `∀ z ∈ S.erase a, dot n w + 1 ≤ dot n (z + (w - a))` ↔ ≥ +1 form

On the integer lattice, `dot n x` and `dot n y` are both integers, so `x < y` implies
`x + 1 ≤ y`. This is what makes the line-by-line induction in the sweep work: each
transverse step moves all points up by at least 1 level. -/
theorem succ_le_dot_translate {S : Finset (ℤ × ℤ)} {n a w : ℤ × ℤ}
    (hstrict : ∀ z ∈ S.erase a, dot n a < dot n z) :
    ∀ z ∈ S.erase a, dot n w + 1 ≤ dot n (z + (w - a)) := by
  intro z hz
  have h : dot n w < dot n (z + (w - a)) := lt_dot_translate_of_strict hstrict z hz
  -- dot n x : ℤ, so < means + 1 ≤
  omega

#print axioms strict_argmin_of_unique
#print axioms lt_dot_translate_of_strict
#print axioms succ_le_dot_translate

end Nivat.LE2
