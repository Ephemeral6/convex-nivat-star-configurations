/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainGeom
import Nivat.External.Colle.ANormal
import Nivat.External.Colle.ShellLine

set_option autoImplicit false

/-!
# `bottom`'s first conjunct via `gcd(d, e)`, `d := dot nJ p`, `e := -dot nJ vJ1`

Dispatched by the integrator (round 231, after `hz₀P` was withdrawn): `ChainDataGeom.bottom`'s
first conjunct (`ChainGeom.lean:132`, `∃ z₀ … dot nJ z₀ = cJ - ε - 1`) is not forced by `e = 1`
(the retired `hadj` claim — see `blueprint/NOTE.md` (Q)).  The actual mechanism: `rec_p` lets
`reachSet` climb by `d := dot nJ p > 0` per step (`p` transverse to `ℓ_J`, `b3_colle2.txt:506`),
and the `vJ1`-sweep descends by `e := -dot nJ vJ1 > 0` per step (`b3_colle2.txt:518-520`), so
every height congruent to `dot nJ g (mod gcd(d, e))`, arbitrarily far below, is attained.

* `dot_nJ_p_pos` — `d > 0` is forced by the existing fields, no new hypothesis (L1).
* `exists_reach_height` — the Bézout argument: any target height `m` with
  `gcd(d, e) ∣ m - dot nJ g` is attained from `g` (L2).
* `bottom_conj1_of_gcd_one` — `bottom`'s conjunct 1 at every `ε`, given `gcd(d, e) = 1` (L3).

⚠ **`gcd(d, e) = 1` (`hgcd`/`hcop`) has no counterpart in `b3_colle2.txt`.**  It is this route's
own debt, not something the original text asks for — flagged so nobody downstream reads it as
an original-text requirement (lane-tower-hlev, round 234; `TowerHbaseRecP.lean`'s `hcop` docstring
makes the identical disclaimer for the same condition under a different name).  Per round-233's
`GcdCollapse.lean`, this condition collapses to `dot nJ vl = -1` on the chain's own collinear
data, and per lane-env-refute's `EnvRefuteCover.lean`/`gcd_one_not_necessary` it is sufficient
but **not** necessary for `bottom`'s conjunct 1 — see the field-only section below for the
precise joint characterization.
-/

namespace Nivat.NlmaxGcd

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35

variable {α : Type*}

private theorem dotAdd (m x y : ℤ × ℤ) : dot m (x + y) = dot m x + dot m y := by
  simp only [dot, Prod.fst_add, Prod.snd_add]; ring

private theorem dotZ (m : ℤ × ℤ) (k : ℤ) (z : ℤ × ℤ) : dot m (k • z) = k * dot m z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- Iterating `rec_p` from any resident of `⋃ Ahat`. -/
private theorem iterate_rec_p {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (cg : Nivat.Colle35.ChainDataGeom η xper vl p S gen)
    {g : ℤ × ℤ} (hg : g ∈ ⋃ i, cg.toChainData.Ahat i) :
    ∀ k : ℕ, g + (k : ℤ) • p ∈ ⋃ i, cg.toChainData.Ahat i := by
  intro k
  induction k with
  | zero => simpa using hg
  | succ n ih =>
    have hstep : g + ((n + 1 : ℕ) : ℤ) • p = (g + (n : ℤ) • p) + p := by
      push_cast; rw [add_smul, one_smul, add_assoc]
    rw [hstep]; exact cg.rec_p _ ih

/-- **L1.**  `p`'s sign against `nJ` is forced positive: if `dot nJ p < 0`, iterating `rec_p`
drives `dot nJ` of a fixed point of `⋃ Ahat` to `-∞`, contradicting `ahat_halfPlane`.
No new hypothesis — `dot_nJ_p` (nonvanishing) and `ahat_nonempty`/`ahat_halfPlane` already
force the sign. -/
theorem dot_nJ_p_pos {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (cg : Nivat.Colle35.ChainDataGeom η xper vl p S gen) :
    0 < dot cg.nJ p := by
  rcases lt_trichotomy (dot cg.nJ p) 0 with hneg | hzero | hpos
  · exfalso
    obtain ⟨g₀, hg₀⟩ := cg.ahat_nonempty
    have hle : ∀ k : ℕ, cg.cJ ≤ dot cg.nJ g₀ + (k : ℤ) * dot cg.nJ p := by
      intro k
      have hh := cg.ahat_halfPlane _ (iterate_rec_p cg hg₀ k)
      rw [dotAdd, dotZ] at hh
      exact hh
    set m : ℤ := dot cg.nJ g₀ - cg.cJ + 1 with hm
    have hmk : m ≤ (m.toNat : ℤ) := Int.self_le_toNat m
    have hle' := hle m.toNat
    have hdle : dot cg.nJ p ≤ -1 := by omega
    have hprod : (m.toNat : ℤ) * dot cg.nJ p ≤ (m.toNat : ℤ) * (-1) :=
      mul_le_mul_of_nonneg_left hdle (Int.natCast_nonneg m.toNat)
    nlinarith
  · exact absurd hzero cg.dot_nJ_p
  · exact hpos

/-- **L2.**  Every height `m` with `gcd(d, e) ∣ m - dot nJ g` is attained in
`reachSet (⋃ Ahat) vJ1` from `g`, where `d := dot nJ p > 0` (L1) and `e := -dot nJ vJ1 > 0`
(`ChainDataGeom.dot_nJ_vJ1_neg`, `ANormal.lean:753`).  Pure Bézout: solve `k*d - t*e = m -
dot nJ g` in `k, t : ℤ` via `Int.gcd_eq_gcd_ab`, then shift `(k, t) ↦ (k + j*e, t + j*d)` —
which preserves `k*d - t*e` — by `j` large enough to make both coordinates nonnegative. -/
theorem exists_reach_height {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (cg : Nivat.Colle35.ChainDataGeom η xper vl p S gen)
    {g : ℤ × ℤ} (hg : g ∈ ⋃ i, cg.toChainData.Ahat i) (m : ℤ)
    (hdvd : (Int.gcd (dot cg.nJ p) (-dot cg.nJ cg.vJ1) : ℤ) ∣ (m - dot cg.nJ g)) :
    ∃ z ∈ reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1, dot cg.nJ z = m := by
  have hdpos : 0 < dot cg.nJ p := dot_nJ_p_pos cg
  have hepos : 0 < -dot cg.nJ cg.vJ1 := by
    have := cg.dot_nJ_vJ1_neg; omega
  set d : ℤ := dot cg.nJ p with hd
  set e : ℤ := -dot cg.nJ cg.vJ1 with he
  set D : ℤ := m - dot cg.nJ g with hD
  obtain ⟨c, hc⟩ := hdvd
  have hbez : (Int.gcd d e : ℤ) = d * Int.gcdA d e + e * Int.gcdB d e := Int.gcd_eq_gcd_ab d e
  set x := Int.gcdA d e with hx
  set y := Int.gcdB d e with hy
  set k1 : ℤ := c * x with hk1
  set t1 : ℤ := -(c * y) with ht1
  have hsolve : k1 * d - t1 * e = D := by
    rw [hc, hbez, hk1, ht1]; ring
  set j : ℤ := max 0 (max (-k1) (-t1)) with hjdef
  have hj0 : (0:ℤ) ≤ j := le_max_left _ _
  have hjk : -k1 ≤ j := le_trans (le_max_left _ _) (le_max_right _ _)
  have hjt : -t1 ≤ j := le_trans (le_max_right _ _) (le_max_right _ _)
  have hd1 : (1:ℤ) ≤ d := by omega
  have he1 : (1:ℤ) ≤ e := by omega
  have hje : j ≤ j * e := by nlinarith
  have hjd : j ≤ j * d := by nlinarith
  set k : ℤ := k1 + j * e with hkdef
  set t : ℤ := t1 + j * d with htdef
  have hknn : 0 ≤ k := by rw [hkdef]; linarith
  have htnn : 0 ≤ t := by rw [htdef]; linarith
  have hinv : k * d - t * e = D := by
    rw [hkdef, htdef]
    have : (k1 + j * e) * d - (t1 + j * d) * e = k1 * d - t1 * e := by ring
    rw [this, hsolve]
  refine ⟨(g + (k.toNat : ℤ) • p) + (t.toNat : ℤ) • cg.vJ1,
    ⟨g + (k.toNat : ℤ) • p, iterate_rec_p cg hg k.toNat, t.toNat, rfl⟩, ?_⟩
  have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hknn
  have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htnn
  rw [dotAdd, dotAdd, dotZ, dotZ, hkcast, htcast]
  have hvJ1 : dot cg.nJ cg.vJ1 = -e := by rw [he]; ring
  rw [hvJ1]
  have := hinv
  rw [hD] at this
  linarith

/-- **L3.**  `bottom`'s conjunct 1 (`ChainGeom.lean:132`) at every `ε`, given `gcd(d, e) = 1`. -/
theorem bottom_conj1_of_gcd_one {η xper : Config α} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (cg : Nivat.Colle35.ChainDataGeom η xper vl p S gen)
    (h1 : Int.gcd (dot cg.nJ p) (-dot cg.nJ cg.vJ1) = 1) (ε : ℕ) :
    ∃ z ∈ reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1, dot cg.nJ z = cg.cJ - (ε : ℤ) - 1 := by
  obtain ⟨g, hg⟩ := cg.ahat_nonempty
  refine exists_reach_height cg hg (cg.cJ - (ε : ℤ) - 1) ?_
  rw [h1]
  exact one_dvd _

/-! ### Field-only (structure-free) restatements

`lane-env-refute`'s refutation (`tmp/wip/lane-env-refute-gcd.lean`,
`not_bottom_heights_of_rec_fields`) shows the abstract implication from `A.Nonempty`,
`rec_p`-shape, `ahat_halfPlane`-shape, `hsweep`, `dot nJ p ≠ 0` alone (no `gcd` hypothesis) to
"every height is attained" is **false**.  These three lemmas are the `L1`/`L2`/`L3` results
above, restated on raw `A`/`nJ`/`vJ1`/`p`/`cJ` and their five field-hypotheses (no
`ChainDataGeom` bundle), with `hgcd` added, so the two halves compose into a single "iff up to
`gcd = 1`" — not a full close of `bottom`, since nothing here shows `ChainDataGeom`'s other
fields force `gcd = 1` (open, per the report to the integrator). -/

/-- **L1, field-only form.**  Identical argument to `dot_nJ_p_pos`, without the `ChainDataGeom`
bundle. -/
theorem dot_p_pos_of_fields {A : Set (ℤ × ℤ)} {nJ p : ℤ × ℤ} {cJ : ℤ}
    (hne : A.Nonempty) (hrec : ∀ g ∈ A, g + p ∈ A) (hhp : ∀ g ∈ A, cJ ≤ dot nJ g)
    (hp : dot nJ p ≠ 0) : 0 < dot nJ p := by
  rcases lt_trichotomy (dot nJ p) 0 with hneg | hzero | hpos
  · exfalso
    obtain ⟨g₀, hg₀⟩ := hne
    have hiter : ∀ k : ℕ, g₀ + (k : ℤ) • p ∈ A := by
      intro k
      induction k with
      | zero => simpa using hg₀
      | succ n ih =>
        have hstep : g₀ + ((n + 1 : ℕ) : ℤ) • p = (g₀ + (n : ℤ) • p) + p := by
          push_cast; rw [add_smul, one_smul, add_assoc]
        rw [hstep]; exact hrec _ ih
    have hle : ∀ k : ℕ, cJ ≤ dot nJ g₀ + (k : ℤ) * dot nJ p := by
      intro k
      have hh := hhp _ (hiter k)
      rw [dotAdd, dotZ] at hh
      exact hh
    set m : ℤ := dot nJ g₀ - cJ + 1 with hm
    have hmk : m ≤ (m.toNat : ℤ) := Int.self_le_toNat m
    have hle' := hle m.toNat
    have hdle : dot nJ p ≤ -1 := by omega
    have hprod : (m.toNat : ℤ) * dot nJ p ≤ (m.toNat : ℤ) * (-1) :=
      mul_le_mul_of_nonneg_left hdle (Int.natCast_nonneg m.toNat)
    nlinarith
  · exact absurd hzero hp
  · exact hpos

/-- **L2, field-only form.**  Identical argument to `exists_reach_height`. -/
theorem exists_reach_height_of_fields {A : Set (ℤ × ℤ)} {nJ vJ1 p : ℤ × ℤ} {cJ : ℤ}
    (hne : A.Nonempty) (hrec : ∀ g ∈ A, g + p ∈ A) (hhp : ∀ g ∈ A, cJ ≤ dot nJ g)
    (hsweep : dot nJ vJ1 < 0) (hp : dot nJ p ≠ 0)
    {g : ℤ × ℤ} (hg : g ∈ A) (m : ℤ)
    (hdvd : (Int.gcd (dot nJ p) (-dot nJ vJ1) : ℤ) ∣ (m - dot nJ g)) :
    ∃ z ∈ reachSet A vJ1, dot nJ z = m := by
  have hdpos : 0 < dot nJ p := dot_p_pos_of_fields hne hrec hhp hp
  have hepos : 0 < -dot nJ vJ1 := by omega
  have hiter : ∀ k : ℕ, g + (k : ℤ) • p ∈ A := by
    intro k
    induction k with
    | zero => simpa using hg
    | succ n ih =>
      have hstep : g + ((n + 1 : ℕ) : ℤ) • p = (g + (n : ℤ) • p) + p := by
        push_cast; rw [add_smul, one_smul, add_assoc]
      rw [hstep]; exact hrec _ ih
  set d : ℤ := dot nJ p with hd
  set e : ℤ := -dot nJ vJ1 with he
  set D : ℤ := m - dot nJ g with hD
  obtain ⟨c, hc⟩ := hdvd
  have hbez : (Int.gcd d e : ℤ) = d * Int.gcdA d e + e * Int.gcdB d e := Int.gcd_eq_gcd_ab d e
  set x := Int.gcdA d e with hx
  set y := Int.gcdB d e with hy
  set k1 : ℤ := c * x with hk1
  set t1 : ℤ := -(c * y) with ht1
  have hsolve : k1 * d - t1 * e = D := by
    rw [hc, hbez, hk1, ht1]; ring
  set j : ℤ := max 0 (max (-k1) (-t1)) with hjdef
  have hj0 : (0:ℤ) ≤ j := le_max_left _ _
  have hjk : -k1 ≤ j := le_trans (le_max_left _ _) (le_max_right _ _)
  have hjt : -t1 ≤ j := le_trans (le_max_right _ _) (le_max_right _ _)
  have hd1 : (1:ℤ) ≤ d := by omega
  have he1 : (1:ℤ) ≤ e := by omega
  have hje : j ≤ j * e := by nlinarith
  have hjd : j ≤ j * d := by nlinarith
  set k : ℤ := k1 + j * e with hkdef
  set t : ℤ := t1 + j * d with htdef
  have hknn : 0 ≤ k := by rw [hkdef]; linarith
  have htnn : 0 ≤ t := by rw [htdef]; linarith
  have hinv : k * d - t * e = D := by
    rw [hkdef, htdef]
    have : (k1 + j * e) * d - (t1 + j * d) * e = k1 * d - t1 * e := by ring
    rw [this, hsolve]
  refine ⟨(g + (k.toNat : ℤ) • p) + (t.toNat : ℤ) • vJ1,
    ⟨g + (k.toNat : ℤ) • p, hiter k.toNat, t.toNat, rfl⟩, ?_⟩
  have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hknn
  have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htnn
  rw [dotAdd, dotAdd, dotZ, dotZ, hkcast, htcast]
  have hvJ1 : dot nJ vJ1 = -e := by rw [he]; ring
  rw [hvJ1]
  have := hinv
  rw [hD] at this
  linarith

/-- **L3, field-only form — matches `lane-env-refute`'s suggested binder order exactly.**

⚠ Cross-pointer (round 234, per team-lead ruling, rule 14 — dispatched to us, not to
`EnvRefuteCover`): `Nivat.EnvRefuteCover.heights_of_gcd_one` (`EnvRefuteCover.lean:174`) proves
the same "`gcd = 1` ⟹ every height below `cJ` is reached" fact but for the **abstract** covering
set `AR` used by that file's window argument. This theorem is the **`bottom`-side** instance:
its `A`/`hrec`/`hhp` are literally `ChainDataGeom`'s own fields (`ahat_nonempty`/`rec_p`/
`bottom`'s half-plane bound), not a generic `AR`. Two different scopes, both kept — see
`EnvRefuteCover.lean`'s own docstring for why theirs stays too. -/
theorem bottom_heights_of_gcd_one {A : Set (ℤ × ℤ)} {nJ vJ1 p : ℤ × ℤ} {cJ : ℤ}
    (hne : A.Nonempty) (hrec : ∀ g ∈ A, g + p ∈ A) (hhp : ∀ g ∈ A, cJ ≤ dot nJ g)
    (hsweep : dot nJ vJ1 < 0) (hp : dot nJ p ≠ 0)
    (hgcd : Int.gcd (dot nJ p) (-dot nJ vJ1) = 1) :
    ∀ ε : ℕ, ∃ z ∈ reachSet A vJ1, dot nJ z = cJ - (ε : ℤ) - 1 := by
  intro ε
  obtain ⟨g, hg⟩ := hne
  refine exists_reach_height_of_fields ⟨g, hg⟩ hrec hhp hsweep hp hg (cJ - (ε : ℤ) - 1) ?_
  rw [hgcd]
  exact one_dvd _

end Nivat.NlmaxGcd

#print axioms Nivat.NlmaxGcd.dotAdd
#print axioms Nivat.NlmaxGcd.dotZ
#print axioms Nivat.NlmaxGcd.iterate_rec_p
#print axioms Nivat.NlmaxGcd.dot_nJ_p_pos
#print axioms Nivat.NlmaxGcd.exists_reach_height
#print axioms Nivat.NlmaxGcd.bottom_conj1_of_gcd_one
#print axioms Nivat.NlmaxGcd.dot_p_pos_of_fields
#print axioms Nivat.NlmaxGcd.exists_reach_height_of_fields
#print axioms Nivat.NlmaxGcd.bottom_heights_of_gcd_one
