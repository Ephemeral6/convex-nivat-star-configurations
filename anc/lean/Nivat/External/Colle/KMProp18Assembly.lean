/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.KariMoutot
import Nivat.External.Colle.KMLemma14
import Nivat.External.Colle.KMCorollary15
import Nivat.External.Colle.KMLemma16
import Nivat.External.Colle.KMLemma17

/-!
# Kari–Moutot Proposition 18 Assembly

Assembly of **Kari–Moutot Proposition 18** from Lemmas 14, 15, 16, 17.

Source: J. Kari, E. Moutot, *Decidability and Periodicity of Low Complexity Tilings*,
Theory of Computing Systems **67** (2023) 125–148, doi `10.1007/s00224-021-10063-8`,
Proposition 18 (p. 138).

**Proposition 18** (verbatim):
> "Let `c` be a configuration with a non-trivial annihilator. If `u` is a one-sided
> direction of determinism in `O(c)‾` then there is a configuration `d ∈ O(c)‾` such
> that `u` is a two-sided direction of determinism in `O(d)‾`."

## Assembly strategy

The paper's proof (§4, pp. 136–139) constructs d as a compactness limit:
1. Use Corollary 15 to bound the maximal n of configs with matching φ-product
2. Apply Lemma 16 to extract subsequential limits preserving the product equality
3. Use Lemma 17 to show d is deterministic in -u
4. Use Lemma 14 to establish determinism in u

This file assumes the individual lemmas and assembles them into Proposition 18.

-/

namespace Nivat.KM18A

open Nivat

/-- **Kari–Moutot Proposition 18**: Removing one-sided determinism.

Given a configuration c with a nontrivial annihilator, if u is a one-sided direction
of determinism (u ∉ ONED but -u ∈ ONED), then there exists d in the orbit closure
where u becomes two-sided (both u and -u are deterministic).

**Now proved** (2026-09-14).  The body is `Nivat.KM17.kmProp18`, which follows the paper's §4
route: Kari–Szabados for a non-parallel product annihilator, Proposition 13 to find the factor
direction `v 0 ⟂ u`, Lemma 14 for the box `B`, Corollary 15 for a maximal `φ`-family, Lemma 16
for a **joint** subsequential limit of that family, and Lemma 17 for the conclusion.  No
`sorry`, no new axiom; `#print axioms` shows `[propext, Classical.choice, Quot.sound]`.

**Correction (2026-09-14).**  This declaration previously had a hand-rolled body that called
`Nivat.KM17.lemma17` — a `sorry`-theorem — and took a *single* compactness limit along `+u`
instead of a joint limit of the maximal family along `-u`.  Two things were wrong with it, and
both are recorded in Part 6 of `KMLemma17.lean`: (i) the sign — Kari–Moutot's `τ^t(c)_n = c_{n-t}`
makes their `d = lim_j τ^{n_j u}(c)` an element of `subseqLimits c (-u)` in this development's
conventions, and the direction is forced, not conventional, because the Lemma 14 half-plane
must be exhausted by the translates; (ii) the bypass of Lemma 16 — an arbitrary subsequential
limit is not the `i₀`-th component of a joint limit of a maximal family, which is what Lemma 17
consumes.  `Nivat.KM17.lemma17` still carries a `sorry` and is now **unused**; its statement has
defect (i) baked into its signature.

**Correction (2026-09-13).**  This docstring previously read "This assembly uses Lemmas 16 and
17, which are stated as axioms since their full proofs require the maximal multiplicity
construction and compactness arguments not yet formalized. The assembly shows how these lemmas
combine to yield Proposition 18."  Three things in that were false: Lemmas 16 and 17 are
sorry-theorems rather than axioms (the distinction decides whether `scripts/audit_axioms_raw.lean`
can see the debt); Lemma 16 is not used at all; and no combination of four lemmas is shown. -/
theorem kmProp18 : Nivat.KM.KMProp18 := Nivat.KM17.kmProp18

end Nivat.KM18A
