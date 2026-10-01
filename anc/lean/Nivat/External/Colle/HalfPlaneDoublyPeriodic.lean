/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma35

set_option autoImplicit false

/-!
# Two configurations cannot both be doubly periodic on a half plane where they disagree

This file proves the one mathematical assertion behind Collé's WLOG at `b3_colle2.txt:890`:

> *"Initially, note that `(x_per)_g ≠ (y_per)_g` for some `g ∈ ℓ^(−) ∩ ℤ²` prevents **both**
> `x_per|ℋ(ℓ^(−))` and `y_per|ℋ(ℓ^(−))` from being fully periodic.  Therefore, we may assume
> that `x_per|ℋ(ℓ^(−))` is not fully periodic."*

The English "prevents both … from being fully periodic" admits two readings — "at most one of
them is" and "neither of them is".  Only the first is what the sentence needs (the next clause
*"we may assume"* is a rename, which is available exactly when at most one can be), and only
the first is true: nothing stops `y_per` from being doubly periodic on the half plane.
`not_doublyPeriodicOn_both` is that reading, stated as a refutation of the conjunction.

## The argument

`x_per` and `y_per` agree on `ℋ(ℓ)` and differ at a point `g` of the one extra lattice line
that `ℋ(ℓ^(−))` adds (`b3_colle2.txt:406`: `ℓ^(−)` is the line parallel to `ℓ`, closest to
`ℋ(ℓ)`, disjoint from it and meeting `ℤ²`).  Neither the "one line" nor the position of `g`
matters: all the proof uses is that `g` lies in the *larger* half plane and the agreement holds
on the *smaller* one, so the statement below takes two levels `cL ≤ … ≤ c` with no relation
imposed between them and no orientation convention to get wrong.

If both restrictions were doubly periodic we would produce a step `h` that is a period of
*both* on the larger half plane and points strictly inward, then push `g` up along `h` into the
agreement region:

    x g = x (g + k·h) = y (g + k·h) = y g.

Producing a *common* `h` is the only real content.  Two independent periods `a, b` of `x` on a
half plane generate `|det a b| · ℤ²` as periods there (`exists_index_period`), which is the
`ℤ`-linear-algebra fact `det a b • z = det z b • a + det a z • b` (`cramer`) plus the
observation that a walk `α·a + β·b` can always be ordered so that every partial sum stays in
the half plane — after replacing `a` by `-a` and `b` by `-b` as needed so that both point
weakly inward, `apply_add_zsmul_add_zsmul` needs only **two** cases, choosing the midpoint
`g + α·a` when `α ≥ 0` (which is above `g`) and `g + β·b` when `α < 0` (which is above the
endpoint).  Then `h := (D_x · D_y) • n` lies in both period groups.

## Scope

Nothing here mentions `ℓ`, `ℋ`, regions, or the minimal counterexample: it is a statement about
two arbitrary configurations and one half plane.  The half plane is written out as
`{z | c ≤ dot n z}` rather than named, to match `Claim414.claim414`'s `hnfp`
(`Claim414Wire.lean:63-65`) syntactically.

Not to be confused with `HalfPlanePeriodicity.lean`, which is about **tangent** periods
(`halfPlane_period_zsmul`, `:80`, assumes `inner2 w u = 0`, where the half plane is preserved
by the step for free and no ordering argument is needed) and states them as a total
`∀ z, c ≤ inner2 w z → f (z + u) = f z` rather than as `PeriodicOnWith`.  The whole difficulty
here is the opposite case, a step that leaves the half plane in one direction.

⚠ This file supplies the *implication*.  The pair it is fed is the `hpartner` hypothesis of
`ColleReg.exists_chainData` (`RegionSteps.lean:751`), exported by `ColleReg.exists_preamble`
(`RegionSteps.lean:496`) on 2026-09-18.  What remains on the construction is matching the
partner's agreement half plane against `cg.cL`, i.e. placing `Â_∞` so that its `ℓ_ι`-support
line carries a disagreement point; see `blueprint/NOTE.md`, entry
「`:890` 的 WLOG — 半平面口径 — 2026-09-18」.
-/

namespace Nivat.Colle35

open Nivat Nivat.LE2

variable {α : Type*}

/-! ### Elementary closure properties of `PeriodicOnWith` on a half plane -/

/-- A period of a restriction is a period in the opposite direction too. -/
theorem periodicOnWith_neg {x : Config α} {U : Set (ℤ × ℤ)} {h : ℤ × ℤ}
    (hp : PeriodicOnWith x U h) : PeriodicOnWith x U (-h) := by
  refine ⟨neg_ne_zero.mpr hp.1, ?_⟩
  intro g hg hgh
  have hmem : g + -h + h ∈ U := by
    have : g + -h + h = g := by abel
    rw [this]; exact hg
  have hstep := hp.2 (g + -h) hgh hmem
  rw [show g + -h + h = g by abel] at hstep
  exact hstep.symm

/-- `dot n` of a point translated by a multiple of `s`. -/
private theorem dot_add_zsmul (n g s : ℤ × ℤ) (m : ℤ) :
    dot n (g + m • s) = dot n g + m * dot n s := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **Walking inward.**  A weakly inward-pointing period may be applied any number of times
from any point of the half plane: every intermediate point is at least as deep as the start. -/
theorem apply_add_nsmul {x : Config α} {n : ℤ × ℤ} {c : ℤ} {s : ℤ × ℤ}
    (hs : PeriodicOnWith x {z | c ≤ dot n z} s) (hns : 0 ≤ dot n s)
    {g : ℤ × ℤ} (hg : c ≤ dot n g) : ∀ k : ℕ, x (g + (k : ℤ) • s) = x g := by
  intro k
  induction k with
  | zero => simp
  | succ m ih =>
    have hm : c ≤ dot n (g + (m : ℤ) • s) := by
      rw [dot_add_zsmul]
      have : 0 ≤ (m : ℤ) * dot n s := mul_nonneg (Int.natCast_nonneg m) hns
      linarith
    have hm1 : c ≤ dot n (g + ((m + 1 : ℕ) : ℤ) • s) := by
      rw [dot_add_zsmul]
      have : 0 ≤ ((m + 1 : ℕ) : ℤ) * dot n s := mul_nonneg (Int.natCast_nonneg _) hns
      linarith
    have heq : g + (m : ℤ) • s + s = g + ((m + 1 : ℕ) : ℤ) • s := by
      push_cast [add_smul, one_smul]; abel
    have hstep := hs.2 (g + (m : ℤ) • s) hm (by rw [heq]; exact hm1)
    rw [heq] at hstep
    exact hstep.trans ih

/-- **Walking inward or outward, one generator.**  A weakly inward-pointing period may be
applied with an arbitrary *integer* multiplicity, provided both endpoints lie in the half
plane: for a negative multiplicity run `apply_add_nsmul` from the endpoint instead. -/
theorem apply_add_zsmul {x : Config α} {n : ℤ × ℤ} {c : ℤ} {s : ℤ × ℤ}
    (hs : PeriodicOnWith x {z | c ≤ dot n z} s) (hns : 0 ≤ dot n s)
    (m : ℤ) {g : ℤ × ℤ} (hg : c ≤ dot n g) (hgm : c ≤ dot n (g + m • s)) :
    x (g + m • s) = x g := by
  rcases le_or_gt 0 m with hm | hm
  · have : ((m.toNat : ℤ)) = m := Int.toNat_of_nonneg hm
    rw [← this]
    exact apply_add_nsmul hs hns hg m.toNat
  · -- run the walk from `g + m • s`, which is the deeper of the two points
    have hneg : ((((-m).toNat : ℕ) : ℤ)) = -m := Int.toNat_of_nonneg (by omega)
    have hback : g + m • s + (((-m).toNat : ℕ) : ℤ) • s = g := by
      rw [hneg, neg_smul]; abel
    have := apply_add_nsmul hs hns hgm (-m).toNat
    rw [hback] at this
    exact this.symm

/-- **Walking with two weakly inward generators.**  Any `ℤ`-combination of `a` and `b` is a
period on the half plane.  Only two cases are needed: when `α ≥ 0` the midpoint `g + α·a` is at
least as deep as `g`, and when `α < 0` the midpoint `g + β·b` is at least as deep as the
endpoint `g + α·a + β·b`. -/
theorem apply_add_zsmul_add_zsmul {x : Config α} {n : ℤ × ℤ} {c : ℤ} {a b : ℤ × ℤ}
    (ha : PeriodicOnWith x {z | c ≤ dot n z} a) (hb : PeriodicOnWith x {z | c ≤ dot n z} b)
    (hna : 0 ≤ dot n a) (hnb : 0 ≤ dot n b) (α β : ℤ) {g : ℤ × ℤ}
    (hg : c ≤ dot n g) (hw : c ≤ dot n (g + α • a + β • b)) :
    x (g + α • a + β • b) = x g := by
  have hdg : dot n (g + α • a) = dot n g + α * dot n a := dot_add_zsmul n g a α
  have hdw : dot n (g + α • a + β • b) = dot n (g + α • a) + β * dot n b :=
    dot_add_zsmul n (g + α • a) b β
  rcases le_or_gt 0 α with hα | hα
  · -- midpoint `g + α • a`, deep because `α • a` points inward
    have hmid : c ≤ dot n (g + α • a) := by
      rw [hdg]
      have : 0 ≤ α * dot n a := mul_nonneg hα hna
      linarith
    have h1 : x (g + α • a) = x g := apply_add_zsmul ha hna α hg hmid
    exact (apply_add_zsmul hb hnb β hmid hw).trans h1
  · -- midpoint `g + β • b`, deep because removing `α • a` from the endpoint goes inward
    have hswap : g + α • a + β • b = g + β • b + α • a := by abel
    have hdg' : dot n (g + β • b) = dot n g + β * dot n b := dot_add_zsmul n g b β
    have hdw' : dot n (g + β • b + α • a) = dot n (g + β • b) + α * dot n a :=
      dot_add_zsmul n (g + β • b) a α
    have hmid : c ≤ dot n (g + β • b) := by
      have hle : α * dot n a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hα.le hna
      rw [hswap, hdw'] at hw
      linarith
    have h1 : x (g + β • b) = x g := apply_add_zsmul hb hnb β hg hmid
    rw [hswap] at hw ⊢
    exact (apply_add_zsmul ha hna α hmid hw).trans h1

/-! ### The index of the period group -/

/-- Cramer's rule in `ℤ²`: `det u v` clears the denominators of the change of basis. -/
private theorem cramer (u v w : ℤ × ℤ) : det u v • w = (det w v) • u + (det u w) • v := by
  ext <;>
    simp only [det, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul] <;>
    ring

/-- **Two independent periods on a half plane give a full-rank period group there.**

If `x|{c ≤ ⟪n,·⟫}` has two independent periods, then some `D > 0` makes *every* `D • z` a
period of that restriction. -/
theorem exists_index_period {x : Config α} {n : ℤ × ℤ} {c : ℤ}
    (hx : ∃ a b : ℤ × ℤ, det a b ≠ 0 ∧
      PeriodicOnWith x {z | c ≤ dot n z} a ∧ PeriodicOnWith x {z | c ≤ dot n z} b) :
    ∃ D : ℤ, 0 < D ∧ ∀ (z g : ℤ × ℤ), c ≤ dot n g → c ≤ dot n (g + D • z) →
      x (g + D • z) = x g := by
  obtain ⟨a₀, b₀, hdet₀, ha₀, hb₀⟩ := hx
  -- orient both generators weakly inward
  set a : ℤ × ℤ := if 0 ≤ dot n a₀ then a₀ else -a₀ with hadef
  set b : ℤ × ℤ := if 0 ≤ dot n b₀ then b₀ else -b₀ with hbdef
  have hdotneg : ∀ u : ℤ × ℤ, dot n (-u) = -dot n u := by
    intro u; simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring
  have ha : PeriodicOnWith x {z | c ≤ dot n z} a := by
    rw [hadef]; split
    · exact ha₀
    · exact periodicOnWith_neg ha₀
  have hb : PeriodicOnWith x {z | c ≤ dot n z} b := by
    rw [hbdef]; split
    · exact hb₀
    · exact periodicOnWith_neg hb₀
  have hna : 0 ≤ dot n a := by
    rw [hadef]; split
    · assumption
    · rw [hdotneg]; omega
  have hnb : 0 ≤ dot n b := by
    rw [hbdef]; split
    · assumption
    · rw [hdotneg]; omega
  -- reorienting changes `det` only by a sign
  have hdetneg₁ : ∀ u v : ℤ × ℤ, det (-u) v = -det u v := by
    intro u v; simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  have hdetneg₂ : ∀ u v : ℤ × ℤ, det u (-v) = -det u v := by
    intro u v; simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  have hdet : det a b ≠ 0 := by
    have h1 : det (-a₀) b₀ = -det a₀ b₀ := hdetneg₁ a₀ b₀
    have h2 : det a₀ (-b₀) = -det a₀ b₀ := hdetneg₂ a₀ b₀
    have h3 : det (-a₀) (-b₀) = det a₀ b₀ := by rw [hdetneg₁, hdetneg₂, neg_neg]
    rw [hadef, hbdef]
    split <;> split
    · exact hdet₀
    · rw [h2]; exact neg_ne_zero.mpr hdet₀
    · rw [h1]; exact neg_ne_zero.mpr hdet₀
    · rw [h3]; exact hdet₀
  refine ⟨|det a b|, abs_pos.mpr hdet, ?_⟩
  intro z g hg hgz
  -- write `|det a b| • z` in the basis `a, b`
  obtain ⟨zz, hzz⟩ : ∃ zz : ℤ × ℤ, |det a b| • z = (det zz b) • a + (det a zz) • b := by
    rcases abs_choice (det a b) with h | h
    · exact ⟨z, by rw [h]; exact cramer a b z⟩
    · refine ⟨-z, ?_⟩
      rw [h, neg_smul, ← smul_neg]
      exact cramer a b (-z)
  have hsplit : g + |det a b| • z = g + (det zz b) • a + (det a zz) • b := by
    rw [hzz]; abel
  rw [hsplit] at hgz ⊢
  exact apply_add_zsmul_add_zsmul ha hb hna hnb _ _ hg hgz

/-! ### Collé's WLOG -/

/-- **`b3_colle2.txt:890`.**  Two configurations that agree on the half plane
`{c ≤ ⟪n,·⟫}` but differ at a point of the larger half plane `{cL ≤ ⟪n,·⟫}` cannot *both* have
a doubly periodic restriction to the larger one.

This is the implication that licenses the WLOG *"we may assume that `x_per|ℋ(ℓ^(−))` is not
fully periodic"*: at most one of the two members of the ambiguous pair can have a fully
periodic restriction, so the one that does not may be named `x_per`.

No relation is imposed between `cL` and `c`, and no orientation convention is fixed: `n` is an
arbitrary nonzero normal and the two levels are arbitrary. -/
theorem not_doublyPeriodicOn_both {x y : Config α} {n : ℤ × ℤ} (hn : n ≠ 0) {c cL : ℤ}
    (hagree : ∀ z : ℤ × ℤ, c ≤ dot n z → x z = y z)
    {g : ℤ × ℤ} (hg : cL ≤ dot n g) (hne : x g ≠ y g)
    (hx : ∃ a b : ℤ × ℤ, det a b ≠ 0 ∧
      PeriodicOnWith x {z | cL ≤ dot n z} a ∧ PeriodicOnWith x {z | cL ≤ dot n z} b)
    (hy : ∃ a b : ℤ × ℤ, det a b ≠ 0 ∧
      PeriodicOnWith y {z | cL ≤ dot n z} a ∧ PeriodicOnWith y {z | cL ≤ dot n z} b) :
    False := by
  obtain ⟨Dx, hDx, hPx⟩ := exists_index_period hx
  obtain ⟨Dy, hDy, hPy⟩ := exists_index_period hy
  -- `n` itself points strictly inward
  have hdotnn : 0 < dot n n := by
    simp only [dot]
    rcases eq_or_ne n.1 0 with h1 | h1
    · have h2 : n.2 ≠ 0 := fun h => hn (by ext <;> simp [h1, h])
      nlinarith [mul_self_nonneg n.1, mul_self_pos.mpr h2]
    · nlinarith [mul_self_nonneg n.2, mul_self_pos.mpr h1]
  -- the common step, a period of both restrictions
  have hDxy : 0 < Dx * Dy := mul_pos hDx hDy
  have hstep : 0 < dot n ((Dx * Dy) • n) := by
    have : dot n ((Dx * Dy) • n) = (Dx * Dy) * dot n n := by
      simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [this]; exact mul_pos hDxy hdotnn
  -- push `g` up into the agreement region
  set k : ℕ := (c - dot n g).toNat with hk
  have hkge : c - dot n g ≤ (k : ℤ) := by rw [hk]; omega
  set G : ℤ × ℤ := g + (k : ℤ) • ((Dx * Dy) • n) with hG
  have hdG : dot n G = dot n g + (k : ℤ) * dot n ((Dx * Dy) • n) :=
    dot_add_zsmul n g _ (k : ℤ)
  have hGc : c ≤ dot n G := by
    rw [hdG]
    have h1 : (k : ℤ) * 1 ≤ (k : ℤ) * dot n ((Dx * Dy) • n) :=
      mul_le_mul_of_nonneg_left hstep (Int.natCast_nonneg k)
    have h2 : (k : ℤ) ≤ (k : ℤ) * dot n ((Dx * Dy) • n) := by linarith
    linarith
  have hGL : cL ≤ dot n G := by
    rw [hdG]
    have : 0 ≤ (k : ℤ) * dot n ((Dx * Dy) • n) :=
      mul_nonneg (Int.natCast_nonneg k) hstep.le
    linarith
  -- `G - g` is `Dx • (…)` and `Dy • (…)` at once
  have hGx : G = g + Dx • ((Dy * (k : ℤ)) • n) := by
    rw [hG, smul_smul, smul_smul]; congr 2; ring
  have hGy : G = g + Dy • ((Dx * (k : ℤ)) • n) := by
    rw [hG, smul_smul, smul_smul]; congr 2; ring
  have hxG : x G = x g := by rw [hGx]; exact hPx _ _ hg (by rw [← hGx]; exact hGL)
  have hyG : y G = y g := by rw [hGy]; exact hPy _ _ hg (by rw [← hGy]; exact hGL)
  exact hne (by rw [← hxG, ← hyG]; exact hagree G hGc)

/-! ### The WLOG as a lemma, and its transport to the bundle's level

Added 2026-09-19 (Amink), moved verbatim from `tmp/nfpL_transport.lean` after the integrator's
ruling.  `not_doublyPeriodicOn_both` above is only the *implication*; what `:890` actually uses
is the rename *"we may assume that `x_per|ℋ(ℓ^(−))` is not fully periodic"*.  With the pair
exported symmetrically by `Nivat.Colle.exists_ambiguousPair_of_oneSidedNonexpansive`
(`Prop210.lean`, 2026-09-19) — both members in `X_η`, each with a period `∥ v`, agreement
strictly above a level `cz`, disagreement at a point `g` *on* the line `cz` — the choice of
member can be made once, here, with no extra hypothesis, and transported to any larger half
plane by monotonicity.  The earlier receipt `tmp/nfpL_producer.lean` showed that from the
*asymmetric* export (partner without a period, disagreement point unnamed) the closer reaches
`ChainDataGeom.nfp_L` only with an `hswap` that nothing supplies; the symmetric export is what
removes it. -/

/-- **`b3_colle2.txt:890`, the WLOG as a lemma.**  Symmetric pair data in, the non-doubly-periodic
member named `xper` out.  Nothing in the output distinguishes the two members except the
`¬DP` conjunct, so a caller that built the pair symmetrically loses nothing by renaming. -/
theorem wlog_notDP {ξ x y : Config α} {p q v : ℤ × ℤ}
    (hx : x ∈ orbitClosure ξ) (hy : y ∈ orbitClosure ξ)
    (hp : p ∈ Per x) (hp0 : p ≠ 0) (hpv : det p v = 0)
    (hq : q ∈ Per y) (hq0 : q ≠ 0) (hqv : det q v = 0)
    {nℓ : ℤ × ℤ} (hnℓ : nℓ ≠ 0) {cz : ℤ}
    (hagree : ∀ z : ℤ × ℤ, cz < dot nℓ z → x z = y z)
    {g : ℤ × ℤ} (hg : dot nℓ g = cz) (hne : x g ≠ y g) :
    ∃ (xper yper : Config α) (p' : ℤ × ℤ),
      xper ∈ orbitClosure ξ ∧ yper ∈ orbitClosure ξ ∧
      p' ∈ Per xper ∧ p' ≠ 0 ∧ det p' v = 0 ∧
      (∀ z : ℤ × ℤ, cz < dot nℓ z → xper z = yper z) ∧
      dot nℓ g = cz ∧ xper g ≠ yper g ∧
      ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
        PeriodicOnWith xper {z | cz ≤ dot nℓ z} h ∧
        PeriodicOnWith xper {z | cz ≤ dot nℓ z} h' := by
  have hagree' : ∀ z : ℤ × ℤ, cz + 1 ≤ dot nℓ z → x z = y z :=
    fun z hz => hagree z (by omega)
  by_cases hDPy : ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith y {z | cz ≤ dot nℓ z} h ∧ PeriodicOnWith y {z | cz ≤ dot nℓ z} h'
  · -- `y` is doubly periodic there, so `x` is not: keep the names
    refine ⟨x, y, p, hx, hy, hp, hp0, hpv, hagree, hg, hne, fun hDPx => ?_⟩
    exact not_doublyPeriodicOn_both hnℓ hagree' (le_of_eq hg.symm) hne hDPx hDPy
  · -- `y` is not: rename
    refine ⟨y, x, q, hy, hx, hq, hq0, hqv, fun z hz => (hagree z hz).symm, hg,
      fun h => hne h.symm, hDPy⟩

/-- `¬DP` on a half plane passes to any larger half plane (a period of the restriction to the
larger set restricts to the smaller one). -/
theorem notDP_mono {x : Config α} {U V : Set (ℤ × ℤ)} (hUV : U ⊆ V)
    (hU : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧ PeriodicOnWith x U h ∧ PeriodicOnWith x U h') :
    ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧ PeriodicOnWith x V h ∧ PeriodicOnWith x V h' := by
  rintro ⟨h, h', hdet, hh, hh'⟩
  exact hU ⟨h, h', hdet, ⟨hh.1, fun g hg hgh => hh.2 g (hUV hg) (hUV hgh)⟩,
    ⟨hh'.1, fun g hg hgh => hh'.2 g (hUV hg) (hUV hgh)⟩⟩

/-- **`ChainDataGeom.nfp_L` verbatim from the upstream `¬DP`**, given the placement constraint
`n_ℓ = k • nℓ`, `0 < k`, `cL ≤ k * cz` — the `ℓ_ι`-support line of `Â_∞` at or below the
disagreement line, `b3_colle2.txt:922` *"coincides with `ℓ^(−)`"* as an inequality.  The
conclusion is the field's statement with `cg.cL`, `cg.vJ` abstracted (`ChainGeom.lean` is
downstream of this file, so the identification is checked at the consumer, not here).
Placement stays on the construction; the choice of member no longer does. -/
theorem nfp_L_of_notDP {xper : Config α} {p vJ nℓ : ℤ × ℤ} {cz cL : ℤ} {k : ℤ}
    (hk : 0 < k) (hnL : det p vJ • (-p.2, p.1) = k • nℓ) (hcL : cL ≤ k * cz)
    (hnotDP : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cz ≤ dot nℓ z} h ∧ PeriodicOnWith xper {z | cz ≤ dot nℓ z} h') :
    ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h' := by
  refine notDP_mono ?_ hnotDP
  intro z hz
  simp only [Set.mem_setOf_eq] at hz ⊢
  have hd : dot (det p vJ • (-p.2, p.1)) z = k * dot nℓ z := by
    rw [hnL]; simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [hd]
  nlinarith

end Nivat.Colle35

#print axioms Nivat.Colle35.not_doublyPeriodicOn_both
#print axioms Nivat.Colle35.wlog_notDP
#print axioms Nivat.Colle35.notDP_mono
#print axioms Nivat.Colle35.nfp_L_of_notDP
