/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma35

/-!
# `region_nonempty`: the region `Â_∞` is nonempty

This discharges the `region_nonempty` hole of
`Nivat/External/Colle/RegionSteps.lean` (`Nivat.ColleReg.region_nonempty`).  The statement
here is verbatim that one, with the ambient `variable` bindings it uses inlined --- in the
order `RegionSteps.lean`'s `variable` block introduces them (`{ξ xper : Config ℤ}`,
`{vl : ℤ × ℤ}`, `{S : Finset (ℤ × ℤ)}`, `{gen : ℤ × ℤ}`), which is what makes the two
statements the *same* `Prop` and not merely equivalent ones.

The argument is the one the hole's docstring predicts, and it needs no new mathematics:

* `hc_grow 0 : c.B 0 ⊂ c.B 1` is a *strict* inclusion, so `Set.exists_of_ssubset` hands over
  a point `x ∈ c.B 1` (the witness is in `c.B 1 \ c.B 0`; only membership in `c.B 1` is
  used).
* `c.subBA 1 : c.B 1 ⊆ c.A 1` puts `x` in `c.A 1`.
* `c.AhatEq 1 : c.Ahat 1 = {z | z + k₁ • vl ∈ c.A 1}` presents `Â_1` as the translate
  `A_1 - k₁ v_ℓ`, so `x - k₁ • vl ∈ c.Ahat 1`.
* Hence `x - k₁ • vl ∈ ⋃ i, c.Ahat i`.

Note that growth is only needed at index `0`; the statement takes it at every index because
that is the shape `exists_chainData` produces and the shape the extracted hole was given.

**2026-09-20 — the note above is now acted on.**  `region_nonempty_of_nonempty_B1` below is
the honest statement: the *only* thing used is that `c.B 1` is inhabited.  The strict
inclusion at index `0` is consumed by `Set.exists_of_ssubset`, whose `x ∉ c.B 0` half is
discarded on the spot, and indices `≥ 1` are never touched.  `region_nonempty` is kept as a
one-line wrapper so nothing downstream has to change at once.

Why this matters beyond tidiness: `∀ i, c.B i ⊂ c.B (i + 1)` was the third conjunct of
`exists_chainData`'s conclusion (`RegionSteps.lean`), and this file was its sole consumer.
An infinite family of strict containments was therefore being demanded to produce one point.
-/

namespace Nivat.ColleStep

open Nivat Nivat.Colle35

/-- **The region `Â_∞` is nonempty, from an inhabited `c.B 1` alone.**

This is `region_nonempty` with the hypothesis cut down to what the proof actually uses:
`c.subBA 1` moves the point into `c.A 1`, and `c.AhatEq 1` presents `c.Ahat 1` as the
translate `c.A 1 - k₁ v_ℓ`.  No growth, no strictness, no index other than `1`. -/
theorem region_nonempty_of_nonempty_B1 {ξ xper : Config ℤ} {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    {gen : ℤ × ℤ} (c : ChainData ξ xper vl S gen) (hB1 : (c.B 1).Nonempty) :
    (⋃ i, c.Ahat i).Nonempty := by
  obtain ⟨x, hxB⟩ := hB1
  have hxA : x ∈ c.A 1 := c.subBA 1 hxB
  have hxHat : x - (c.kk 1 : ℤ) • vl ∈ c.Ahat 1 := by
    rw [c.AhatEq 1]
    simpa using hxA
  exact ⟨x - (c.kk 1 : ℤ) • vl, Set.mem_iUnion.mpr ⟨1, hxHat⟩⟩

/-- The region `Â_∞` is nonempty.

`hc_grow` gives `c.B 0 ⊂ c.B 1`, hence `c.B 1` is inhabited; the rest is
`region_nonempty_of_nonempty_B1`.  Retained at the original strength so existing callers
keep elaborating; new callers should prefer the weaker form. -/
theorem region_nonempty {ξ xper : Config ℤ} {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (c : ChainData ξ xper vl S gen) (hc_grow : ∀ i, c.B i ⊂ c.B (i + 1)) :
    (⋃ i, c.Ahat i).Nonempty := by
  have hgrow0 : c.B 0 ⊂ c.B 1 := by simpa using hc_grow 0
  obtain ⟨x, hxB, -⟩ := Set.exists_of_ssubset hgrow0
  exact region_nonempty_of_nonempty_B1 c ⟨x, hxB⟩

end Nivat.ColleStep
