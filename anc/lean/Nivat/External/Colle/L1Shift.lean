/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.L1Base0
import Nivat.External.Colle.HalfPlaneFamily

/-!
# The translation freedom `v`, and exactly how large it is

`exists_L1MaxBResidual` (`RegionSteps.lean:1092`) quantifies `v` **existentially in its own
conclusion**, alongside `e u u' c τ ε S₁ F`:

```
∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
  (F : RegionFamily (T e ξ) u u' c),
  S₁ = S.image (· + v) ∧ MaxBResidual (ξ := ξ) ε u u' c τ S₁ F
```

so whoever discharges the leaf **chooses** `v`.  That is the escape valve for the `lev₀`
conflict: `base` receives a determined half plane from `Nivat.Colle.colle_prop_2_10`, so `lev₀`
is not free, while `line0` and `base0` need the points of `S₁` (and of the sets derived from it)
to lie in `halfPlaneGE m lev₀`, i.e. need `lev₀` small.  With `lev₀` pinned, the only remaining
move is to translate `S₁`, and `forall_mem_halfPlaneGE_iff` (`L1Base0.lean:52`) makes that move
exactly measurable: the condition is `lev₀ ≤ dot m b + dot m z₀`, linear in the translation.

## What this file establishes

* **§1 — transport.**  Translating `S` by `v` translates every `m`-level by `dot m v`, and
  carries the `m`-minimal point to the `m`-minimal point.  The pointwise half of this is
  `Nivat.LE2.dot_add` (`LatticeEdges.lean:76`), already in the tree; only the minimality
  transport is new.
* **§2 — the size of the valve.**  `{dot m v | v : ℤ × ℤ}` is exactly the subgroup
  `gcd(m₁, m₂) • ℤ` (`exists_dot_eq_iff_gcd_dvd`).  Hence the valve is *all of `ℤ`* precisely
  when `m` is primitive — the positive direction is Rsweep's
  `HalfPlaneFamily.exists_dot_eq_of_primitive` (`HalfPlaneFamily.lean:120`), re-exported here,
  **not** reproved — and **not** otherwise (`not_forall_exists_dot_eq_of_not_primitive`, new).
  The negative direction is the live risk: a non-primitive `m` moves `S₁` only in steps of
  `gcd`, and then the two ends of `lev₀` need not meet.
* **§3 — the packaged form.**  For primitive `m`, *any* pinned `lev₀` and *any* `b`, there is a
  `v` putting all of `b + S.image (· + v)` inside `halfPlaneGE m lev₀`.  Monotonicity
  (`forall_mem_halfPlaneGE_of_subset`) then serves `derivedQ` and `maxB` from the same `v`,
  since both are `Finset.filter`s of `S₁`: **one `v` discharges all three lanes' membership
  demands at once**, which is what makes the valve usable without the lanes coordinating.

## ⚠ Scope

This file says the translation freedom is *sufficient to satisfy the membership constraints*.
It does not claim `lev₀`'s two ends are reconciled outright: translating `S₁` also moves every
other `S₁`-dependent quantity in `MaxBResidual` (`derivedQ`, `topFace`, `maxB`, the faces
feeding `hdef`), and this file proves nothing about those.  It removes the half-plane
membership obstruction and nothing else.

## 🔴 The primitivity of `m` is a hypothesis here, not a theorem

Every §3 statement takes `Primitive m`.  `m` enters through
`HalfPlaneFamily.ofHalfPlanes`'s implicit normal, constrained only by `dot m u' = 0` and
`0 < dot m u`; **neither forces primitivity**, and `§2`'s negative result shows the gap is not
cosmetic.  `dot_eq_zero_and_pos_of_primitivePart` below records the one cheap repair:
`m` may be replaced by `m / gcd`, which is primitive and satisfies the *same* two constraints,
so the obstruction is removable at the source as long as whoever builds the family is willing
to normalise its normal.  Whether `colle_prop_2_10`'s half plane survives that replacement is
**not** settled here — `halfPlaneGE m lev₀ ≠ halfPlaneGE (m/g) lev₀` in general, the levels
rescale too.
-/

set_option autoImplicit false

namespace Nivat.L1Shift

open Nivat Nivat.LE2

variable {m v : ℤ × ℤ}

/-! ## §1  Translating a window translates its `m`-levels -/

/-- The translate of a point of `S` is a point of the translated `S`. -/
theorem mem_image_add (S : Finset (ℤ × ℤ)) {z : ℤ × ℤ} (hz : z ∈ S) (v : ℤ × ℤ) :
    z + v ∈ S.image (· + v) :=
  Finset.mem_image.mpr ⟨z, hz, rfl⟩

/-- **The `m`-minimal point transports.**  If `z₀` minimises `dot m` on `S`, then `z₀ + v`
minimises it on `S.image (· + v)` — because `dot m` shifts by the constant `dot m v` on every
point at once (`dot_add`, `LatticeEdges.lean:76`).

This is the only new content of §1; the pointwise identity `dot m (z + v) = dot m z + dot m v`
is `Nivat.LE2.dot_add m z v` and is *not* restated here. -/
theorem min_image_add {S : Finset (ℤ × ℤ)} {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ S)
    (hz₀min : ∀ z ∈ S, dot m z₀ ≤ dot m z) (v : ℤ × ℤ) :
    z₀ + v ∈ S.image (· + v) ∧ ∀ z ∈ S.image (· + v), dot m (z₀ + v) ≤ dot m z := by
  refine ⟨mem_image_add S hz₀ v, fun z hz => ?_⟩
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  rw [dot_add, dot_add]
  exact Int.add_le_add_right (hz₀min w hw) _

/-! ## §2  How far the valve opens: `{dot m v} = gcd(m₁,m₂) • ℤ` -/

/-- Every value of `dot m ·` is a multiple of `gcd(m₁, m₂)`.  This is the obstruction half. -/
theorem gcd_dvd_dot (m v : ℤ × ℤ) : ((Int.gcd m.1 m.2 : ℤ)) ∣ dot m v := by
  simp only [dot]
  exact dvd_add (Dvd.dvd.mul_right (Int.gcd_dvd_left m.1 m.2) _)
    (Dvd.dvd.mul_right (Int.gcd_dvd_right m.1 m.2) _)

/-- **The valve is exactly the subgroup `gcd(m₁, m₂) • ℤ`.**

Forward is `gcd_dvd_dot`.  Backward is Bézout: `Int.gcd_eq_gcd_ab` writes `gcd` as
`m.1 * a + m.2 * b`, and scaling that certificate by `k / gcd` realises `k`. -/
theorem exists_dot_eq_iff_gcd_dvd (m : ℤ × ℤ) (k : ℤ) :
    (∃ v : ℤ × ℤ, dot m v = k) ↔ ((Int.gcd m.1 m.2 : ℤ)) ∣ k := by
  constructor
  · rintro ⟨v, rfl⟩
    exact gcd_dvd_dot m v
  · rintro ⟨t, rfl⟩
    refine ⟨(t * Int.gcdA m.1 m.2, t * Int.gcdB m.1 m.2), ?_⟩
    have hb : (Int.gcd m.1 m.2 : ℤ) = m.1 * Int.gcdA m.1 m.2 + m.2 * Int.gcdB m.1 m.2 :=
      Int.gcd_eq_gcd_ab m.1 m.2
    simp only [dot]
    rw [hb]
    ring

/-- **Primitive `m` ⟹ the valve is all of `ℤ`.**

⚠ **Not proved here — re-exported.**  This is
`Nivat.HalfPlaneFamily.exists_dot_eq_of_primitive` (`HalfPlaneFamily.lean:120`, lane Rsweep),
which was already in the tree when this file was written.  It is aliased rather than restated
so that §3 below reads in one namespace, and so that the duplicate this file originally
contained is not left standing.

The `gcd` statements above are the part that is new: Rsweep's file has the positive direction
only, and the negative one is what makes the primitivity hypothesis load-bearing rather than
decorative. -/
theorem exists_dot_eq_of_primitive (hm : Primitive m) (k : ℤ) : ∃ v : ℤ × ℤ, dot m v = k :=
  Nivat.HalfPlaneFamily.exists_dot_eq_of_primitive hm k

/-- **Non-primitive `m` ⟹ the valve is strictly smaller than `ℤ`.**

The live risk, compiled: if `m` is not primitive then `1` is not a value of `dot m ·`, so the
translation cannot realise an arbitrary shift of the `m`-levels.  A producer of
`HalfPlaneFamily.ofHalfPlanes` that hands back a non-primitive normal therefore hands back a
valve that moves only in steps of `gcd`.

No `m ≠ 0` hypothesis is needed: `gcd ∣ 1` forces `gcd = 1` on its own, and the degenerate
`m = 0` is covered because `Primitive 0` is false while `dot 0 v = 0` for every `v`. -/
theorem not_forall_exists_dot_eq_of_not_primitive (hm : ¬ Primitive m) :
    ¬ ∀ k : ℤ, ∃ v : ℤ × ℤ, dot m v = k := by
  intro h
  obtain ⟨v, hv⟩ := h 1
  have hg1 : ((Int.gcd m.1 m.2 : ℤ)) = 1 :=
    Int.eq_one_of_dvd_one (Int.natCast_nonneg _) (hv ▸ gcd_dvd_dot m v)
  exact hm (Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hg1))

/-- **The cheap repair at the source.**  Dividing `m` by `g = gcd(m₁, m₂)` preserves both
constraints that `ofHalfPlanes` puts on its normal — `dot m u' = 0` and `0 < dot m u` — because
`dot` is linear in its left argument and `g > 0`.

Stated so that "normalise the normal" is a checked option rather than a suggestion.  ⚠ It does
**not** follow that the *family* survives the replacement: `halfPlaneGE m lev₀` and
`halfPlaneGE (m/g) lev₀` are different sets, so `hbase` would have to be re-derived at the
rescaled level.  That is outside this file. -/
theorem dot_eq_zero_and_pos_of_primitivePart {u u' : ℤ × ℤ} {g : ℤ} {m' : ℤ × ℤ}
    (hg : 0 < g) (hm' : m = (g * m'.1, g * m'.2))
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u) :
    dot m' u' = 0 ∧ 0 < dot m' u := by
  have hlin : ∀ w : ℤ × ℤ, dot m w = g * dot m' w := by
    intro w; simp only [dot, hm']; ring
  refine ⟨?_, ?_⟩
  · have := hlin u'
    rw [hmu'] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hg.ne'
  · have hpos := hlin u
    rw [hpos] at hmu
    by_contra hcon
    have hle : dot m' u ≤ 0 := not_lt.mp hcon
    nlinarith

/-! ## §3  The packaged form the three lanes consume -/

/-- Membership in a half plane is inherited by subsets.  `derivedQ` and `maxB` are
`Finset.filter`s (`L1Cut.lean:98`, `:116`), hence subsets, so a single `v` chosen for `S₁`
serves them both without any further argument. -/
theorem forall_mem_halfPlaneGE_of_subset {S₁ T : Finset (ℤ × ℤ)} (hsub : T ⊆ S₁)
    {b : ℤ × ℤ} {lev₀ : ℤ} (h : ∀ z ∈ S₁, b + z ∈ halfPlaneGE m lev₀) :
    ∀ z ∈ T, b + z ∈ halfPlaneGE m lev₀ :=
  fun z hz => h z (hsub hz)

/-- **The valve discharges the membership constraint, for a pinned `lev₀`.**

Given a primitive `m`, a nonempty window `S`, a base point `b` and *any* level `lev₀` — in
particular the one `colle_prop_2_10` hands to `base`, which `base` cannot move — there is a
translation `v` with every point of `b + S.image (· + v)` in `halfPlaneGE m lev₀`.

The chosen `v` realises `dot m v = lev₀ - dot m b - dot m z₀` exactly, so the resulting
configuration sits *on* the threshold of `forall_mem_halfPlaneGE_iff` (`L1Base0.lean:52`); see
`exists_shift_forall_mem_halfPlaneGE_margin` for the version with slack. -/
theorem exists_shift_forall_mem_halfPlaneGE (hm : Primitive m) {S : Finset (ℤ × ℤ)}
    (hS : S.Nonempty) (lev₀ : ℤ) (b : ℤ × ℤ) :
    ∃ v : ℤ × ℤ, ∀ z ∈ S.image (· + v), b + z ∈ halfPlaneGE m lev₀ := by
  obtain ⟨z₀, hz₀, hz₀min⟩ := S.exists_min_image (fun z => dot m z) hS
  obtain ⟨v, hv⟩ := exists_dot_eq_of_primitive hm (lev₀ - dot m b - dot m z₀)
  obtain ⟨hmem, hmin⟩ := min_image_add (m := m) hz₀ hz₀min v
  refine ⟨v, (Nivat.ColleReg.L1Data.forall_mem_halfPlaneGE_iff hmem hmin).mpr ?_⟩
  rw [dot_add, hv]
  omega

/-- The same, with a prescribed margin: the translated window can be pushed an arbitrary
distance `margin` *beyond* the threshold, so a lane needing strict slack (rather than
membership on the boundary) can ask for it. -/
theorem exists_shift_forall_mem_halfPlaneGE_margin (hm : Primitive m) {S : Finset (ℤ × ℤ)}
    (hS : S.Nonempty) (lev₀ margin : ℤ) (b : ℤ × ℤ) :
    ∃ v : ℤ × ℤ, ∀ z ∈ S.image (· + v),
      lev₀ + margin ≤ dot m (b + z) := by
  obtain ⟨v, hv⟩ := exists_shift_forall_mem_halfPlaneGE (m := m) hm hS (lev₀ + margin) b
  exact ⟨v, fun z hz => hv z hz⟩

/-- **The form `base0` and `line0` can quote directly**: one `v`, and the membership holds on
`S₁ = S.image (· + v)` *and* on every subset of it — `derivedQ ε u' S₁` and
`maxB (derivedQ ε u' S₁) u' pw` included, by `forall_mem_halfPlaneGE_of_subset`. -/
theorem exists_shift_forall_mem_halfPlaneGE_subsets (hm : Primitive m) {S : Finset (ℤ × ℤ)}
    (hS : S.Nonempty) (lev₀ : ℤ) (b : ℤ × ℤ) :
    ∃ v : ℤ × ℤ, ∀ T ⊆ S.image (· + v), ∀ z ∈ T, b + z ∈ halfPlaneGE m lev₀ := by
  obtain ⟨v, hv⟩ := exists_shift_forall_mem_halfPlaneGE (m := m) hm hS lev₀ b
  exact ⟨v, fun _ hsub => forall_mem_halfPlaneGE_of_subset hsub hv⟩

end Nivat.L1Shift
