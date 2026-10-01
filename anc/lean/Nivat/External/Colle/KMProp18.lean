/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.KariMoutot
import Nivat.External.Colle.KMProp18Assembly

/-!
# Kari–Moutot Proposition 18 — Reduction to Lemmas 14-17

This file reduces **Kari–Moutot Proposition 18** to its constituent lemmas from the paper.

> "Let `c` be a configuration with a non-trivial annihilator. If `u` is a one-sided
> direction of determinism in `O(c)‾` then there is a configuration `d ∈ O(c)‾` such
> that `u` is a two-sided direction of determinism in `O(d)‾`."

Source: J. Kari, E. Moutot, *Theory Comput. Syst.* **67** (2023) 125–148,
doi 10.1007/s00224-021-10063-8, Proposition 18 (p. 138).

## Status (as of 2026-09-14)

**External dependencies closed:** The two key lemmas (`lemma17_of_maximal_family` and
`lemma17_of_lemma14`) are now fully proved with no axioms beyond the standard Lean kernel
axioms `[propext, Classical.choice, Quot.sound]`.

The old signature at `KMLemma17.lean:1068` has been retired (it was unprovable as stated).
The current path from Lemmas 14-17 to Proposition 18 contains no `sorry` and depends on
no external axioms.

## Reduction structure

The paper's proof constructs d as a compactness limit and uses four intermediate results.
We formalize these as explicit `Prop` definitions and derive Proposition 18 from them.

-/

namespace Nivat.KM18

open Nivat

/-! ## The four intermediate lemmas -/

/-- **Kari–Moutot Lemma 14** (p. 136): For configurations in the orbit closure with
matching annihilator product φd = φe, agreement on discrete box B implies agreement
on half-plane H.

This captures the "periodicity transmits zeros" argument. The paper uses a specific
box B = B_u^k and half-plane H = H_{-u}. -/
def KMLemma14 : Prop :=
  ∀ (φ : LaurentTwo ℤ) (c : Config ℤ) (u : ℤ × ℤ) (B : Finset (ℤ × ℤ)),
    (Set.range c).Finite →
    ∀ d e : Config ℤ,
      d ∈ orbitClosure c → e ∈ orbitClosure c →
      act φ d = 0 → act φ e = 0 →
      act φ d = act φ e →
      (∀ z ∈ B, d z = e z) →
      (∀ z : ℤ × ℤ, inner2 (toReal u) z < 0 → d z = e z)

/-- **Kari–Moutot Corollary 15** (p. 136): If c₁,...,cₙ ∈ O(c)‾ are pairwise distinct
with φc₁ = ··· = φcₙ, then n ≤ |A|^|B|.

This bounds the maximal n, ensuring the construction terminates. -/
def KMCorollary15 : Prop :=
  ∀ (φ : LaurentTwo ℤ) (c : Config ℤ) (A : Finset ℤ) (B : Finset (ℤ × ℤ)),
    (Set.range c ⊆ A) →
    ∀ (n : ℕ) (configs : Fin n → Config ℤ),
      (∀ i, configs i ∈ orbitClosure c) →
      (∀ i j, i ≠ j → configs i ≠ configs j) →
      (∀ i, act φ (configs i) = 0) →
      (∀ i j, act φ (configs i) = act φ (configs j)) →
      n ≤ A.card ^ B.card

/-! ## Derivation of Proposition 18

We show that Lemmas 14-17 together imply Proposition 18. The key steps:
1. Use Corollary 15 to bound the maximal n of configs with matching φ-product
2. Apply compactness to get subsequential limits (Lemma 16)
3. Use Lemma 17 to show the limit is deterministic in -u
4. Use ONED monotonicity to preserve determinism in u

The actual lemma statements are in their respective files:
- Lemma 14: `Nivat.KM14.lemma14_stripe` (proven)
- Corollary 15: `Nivat.KM15.corollary15` (proven)
- Lemma 16: `Nivat.KM16.lemma16` (a `theorem`, **not** an `axiom`)
- Lemma 17: `Nivat.KM17.lemma17` (a `theorem`, **not** an `axiom`; its body is `sorry`)

**Correction (2026-09-13).**  The two lines above previously read "(axiom)" for both Lemma 16
and Lemma 17.  That was false and it mattered: an `axiom` is invisible to the kernel audit in
`scripts/audit_axioms_raw.lean`, whereas a `theorem ... := by sorry` carries `sorryAx`, which
that audit does catch.  Describing sorry-theorems as axioms told a reader that the debt here
was *outside* the audit's reach when in fact it is inside it — the reverse of the truth.  The
repository convention is deliberate: unproved content is written `theorem ... := by sorry`
precisely so it stays visible to the kernel.

`KMProp18Assembly.lean` contains no `sorry` in its own text, and since 2026-09-14 its proof is
`Nivat.KM17.kmProp18`, which is complete: `Nivat.KM18A.kmProp18` depends on
`[propext, Classical.choice, Quot.sound]` only.  (Until 2026-09-14 it called
`Nivat.KM17.lemma17`, whose body is `sorry`, and therefore carried `sorryAx`; that sentence has
been corrected in place rather than deleted.  `Nivat.KM17.lemma17` still carries its `sorry` and
is now unused — see Part 6 of `KMLemma17.lean` for why its *statement*, not merely its proof, is
the obstruction.) -/

theorem kmProp18_of_lemmas_14_to_17 : Nivat.KM.KMProp18 :=
  Nivat.KM18A.kmProp18

/-! ## Status

This file is a thin re-export of `Nivat.KM18A.kmProp18`, which since 2026-09-14 is a **complete
proof** of `KMProp18`.

1. The lemma statements:
   - **KMLemma14**: Statement defined, stripe version proven in `KMLemma14.lean`
   - **KMCorollary15**: Fully proven in `KMCorollary15.lean`
   - **KMLemma16**: a `theorem` in `KMLemma16.lean` (not an `axiom`)
   - **KMLemma17**: `Nivat.KM17.lemma17_of_maximal_family` and `Nivat.KM17.lemma17_of_lemma14`
     are proved; the older, differently-stated `Nivat.KM17.lemma17` is still `sorry` and is now
     unused

2. `kmProp18_of_lemmas_14_to_17` is a complete proof: `#print axioms` on it shows
   `[propext, Classical.choice, Quot.sound]`.

**What `KMProp18Assembly.kmProp18` actually calls.**  `Nivat.KM17.kmProp18`, which follows the
paper's §4 route: `Nivat.kari_szabados_prodShift`, `Nivat.Colle.exists_tangent_of_mem_ONED`
(Proposition 13), `KM16.exists_lemma14HalfPlane_of_det` (Lemma 14),
`KM17.exists_maximalPhiFamily_of_lemma14` (Corollary 15), `KM16.exists_jointSubseqLimit`
(Lemma 16) and `KM17.lemma17_of_maximal_family` (Lemma 17).

**Correction (2026-09-14).**  The paragraph that used to stand here said the assembly bypasses
Lemma 16 with a single direct compactness call and that "whether that shortcut is legitimate has
**not** been established".  That was accurate about the old body.  The shortcut was in fact
*not* legitimate — it also had the translation direction backwards — and it has been replaced by
the paper's route.

**What remains**: nothing in this file.

**Correction (2026-09-13).**  This block previously called KMLemma16/17 "axioms" (they are
sorry-theorems), called the derivation "**complete** (no sorry)" (it carries `sorryAx`), and
claimed the assembly "properly constructs the subsequential limit using compactness" and
"applies Lemma 17" as if all four lemmas were combined.  It also asserted "The axioms are
consistent as shown by the proven special cases" — which does not follow, and which nothing
in the tree establishes.  Corrected rather than deleted so the overstatement stays on record.

-/

end Nivat.KM18
