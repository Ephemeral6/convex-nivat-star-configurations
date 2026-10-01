/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.ExternalDefs
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.Generating
import Nivat.External.Colle.GenClosureWeaken
import Nivat.External.Colle.ShellGeom

/-!
# `region_periods_and_rays` was **false as extracted**

This file was opened to prove `Nivat.ColleReg.region_periods_and_rays` of
`Nivat/External/Colle/RegionSteps.lean`.  It does the opposite: it exhibits a machine-checked
counterexample, so the statement cannot be proved without changing it.

## Outcome, 2026-09-16 (r67 verdict)

The change was made: `hξ : IsMinimalCounterexample ξ` — dropped by the extraction, in scope
at the original hole — is back on the signature, and the witness below does **not** satisfy
it (`cx_not_minimalCounterexample`, `:477`; `cxEta` is periodic and `cxEta (0,0) = 0`).  So
this file refutes the *stripped* statement, which is what it was always measured against; it
says nothing about the repaired one, which is open.  The counterexample is kept because it is
what forced the repair, and because it pins down exactly how much context the extraction may
drop.

## The statement at issue (as extracted, without `hξ`)

```
theorem region_periods_and_rays (c : ChainData ξ xper vl S gen)
    (hc_env : c.Env = Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)))
    (hc_grow : ∀ i, c.B i ⊂ c.B (i + 1))
    (hgen : Nivat.Colle.GeneratesAt ξ S gen)
    (hvl_ne : vl ≠ 0) (hp_ne : p ≠ 0) (hdet_vl : det p vl = 0) (hdet_ℓ : det ℓ vl = 0)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hϑ_mem : ϑ ∈ orbitClosure ξ)
    (hϑ_periodic : PeriodicOnWith ϑ (⋃ i, c.Ahat i) p) :
    ∃ h h' z₀ z₀' : ℤ × ℤ, det h h' ≠ 0 ∧ ⋯
```

`not_region_periods_and_rays` below is the negation of exactly that `∀`-statement.

## Why it is false, in one line

Nothing in the hypotheses forces `Â_∞ = ⋃ i, c.Ahat i` to be two-dimensional.  Here it is the
half-strip `{z | 0 ≤ z.1 ∧ 0 ≤ z.2 ≤ 1}`, in which every ray is horizontal, so *any* two ray
directions `h, h'` have `det h h' = 0`.

`Lemma35.lean` says this out loud in its own module docstring, under "Deviations from the
source, stated loudly": *"The classification of `Â_∞` as an `(ℓ_ι, ℓ_J)`-region with
`ι+1 ≤ J ≤ ι+m-1` … is **not** formalised at all."*  That classification — two *semi-infinite
edges* in independent directions — is exactly the geometric input the conclusion needs, and
`ChainData` does not contain it.

## The witness

| object | value |
|---|---|
| `ξ` | `fun z => if 0 < z.2 then 1 else 0` (a horizontal half-plane, constant in `z.1`) |
| `xper` | `0` |
| `ϑ` | `T (0,-1) ξ = fun z => if 0 < z.2 - 1 then 1 else 0` |
| `vl = p = ℓ` | `(0,1)` |
| `S` | `{(0,0),(1,0),(0,1),(1,1)}`, `gen = (1,1)` |
| `B i = A i = Â i` | `[0, i+1] × [0,1]` |
| `Â_i^{(ε)}` | `[0, i+1] × [0, 1+ε]` |
| `Â_∞` | `[0,∞) × [0,1]` |

`vl` is forced to be horizontal-strip-compatible and `ℓ` is then forced to be `±(0,1)` by
`hdet_ℓ` together with primitivity, so the one-sided nonexpansive directions have to be the
*vertical* ones; `ξ` is constant in `z.1`, which is what makes `GeneratesAt ξ S (1,1)` hold
(the value at `(1,1)` equals the value at `(0,1)`, which is in `S.erase gen`) while
`(0,1)` and `(0,-1)` are both one-sided nonexpansive (translates of `ξ` far up / far down
agree with the constant configurations `1` / `0` on a half-plane and differ elsewhere).

## What is actually broken, and what would repair it

The extraction dropped every hypothesis of `colle_region` that the `sorry` did not visibly
use.  The contract in `RegionSteps.lean` calls that legitimate ("Dropping an unused hypothesis
is allowed — that strengthens the statement"), and for five of the six steps it is.  Here it
strengthened the statement past the point of truth: `hξ : IsMinimalCounterexample ξ` was in
scope at the original `sorry` and is *not* a hypothesis of the extracted theorem.  The `ξ`
below is periodic (period `(1,0)`), hence not a counterexample to Nivat at all, so `hξ`
excludes it.

To limit how much context can be blamed, the witness below satisfies, in addition to the
twelve hypotheses of the statement, five *further* facts that `colle_region` has in scope at
the extracted `sorry`: `xper ∈ orbitClosure ξ`, `p ∈ Per xper`, and all three outputs of
`Colle35.lemma35` (`hϑ_agree` at `K = 0`, `hshell` at `ε = 0`, `hshell_not` at `ε + 1 = 1`).
So re-admitting any one of those five would not repair the statement.

**That list is not exhaustive, and the following are *not* discharged here** (adversarial
audit, 2026-09-14).  Also in scope at the call site are `hfin : (Set.range ξ).Finite`,
`hR_lattice_convex`, `hR_nonempty`, and the Claim-4.6 inputs `hw`, `hw₁`, `hw₂`.  The audit
reports kernel-clean proofs of the first three for this witness and a by-hand check of the
last three at `w = (0,1)`; none of that is re-proved in this file, so treat it as unmeasured
here.

**What this file does *not* establish** is that `hξ` is the *weakest* repair.  It is not:
`¬ IsPeriodic ξ` alone already excludes the witness (`ξ` has period `(1,0)`), and so does the
positivity clause of `IsCounterexample` (`ξ (0,0) = 0`).  Both are strictly weaker than
`IsMinimalCounterexample ξ`.  The honest statement is the negative one: *the twelve
hypotheses actually written down do not suffice*, and any repair must add something that
rules out configurations like this one.

Whether re-adding `hξ` makes the statement *true* is not settled here — that is Collé's
argument, and it goes through the region classification that `Lemma35.lean` declares
unformalised; formalising it and demanding `IsRegion (⋃ i, c.Ahat i) ℓ ℓ'` would be the
repair closer to the source.  **Measured, not asserted:** everything in this file is
`sorry`-free; the counterexample is checked by the kernel.
-/

namespace Nivat.ColleStep

open Nivat Nivat.Colle35 Nivat.LE2

/-! ## The witness -/

namespace PeriodsRays

/-- `ξ`: the indicator of the open upper half-plane.  Constant in the first coordinate. -/
def cxEta : Config ℤ := fun z => if 0 < z.2 then 1 else 0

/-- `x_per`: the zero configuration. -/
def cxXper : Config ℤ := fun _ => 0

/-- `ϑ`: the same half-plane pushed down by one, i.e. `T (0,-1) ξ`. -/
def cxTheta : Config ℤ := fun z => if 0 < z.2 - 1 then 1 else 0

/-- The constant `1` configuration, used as a one-sided nonexpansive witness. -/
def cxOne : Config ℤ := fun _ => 1

/-- The generating window: the four lattice points of `[0,1]²`. -/
def cxS : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (0, 1), (1, 1)}

/-- Boxes anchored at the origin. -/
def cxBox (a b : ℤ) : Set (ℤ × ℤ) := box (0, 0) (a, b)

/-- `B i = A i = Â i = [0, i+1] × [0,1]`. -/
def cxB (i : ℕ) : Set (ℤ × ℤ) := cxBox ((i : ℤ) + 1) 1

/-- `Â_i^{(ε)} = [0, i+1] × [0, 1+ε]`. -/
def cxShell (i ε : ℕ) : Set (ℤ × ℤ) := cxBox ((i : ℤ) + 1) (1 + (ε : ℤ))

/-- `Â_∞^{(ε)} = [0,∞) × [0, 1+ε]`. -/
def cxShellInf (ε : ℕ) : Set (ℤ × ℤ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1 + (ε : ℤ)}

/-- The generation filtration: everything already known, plus the part of the shell below the
potential `z.1 + z.2 ≤ n`.  Each of the three sites the window needs to create `z` sits at a
strictly smaller potential. -/
def cxFill (i i₀ ε n : ℕ) : Set (ℤ × ℤ) :=
  cxB i ∪ cxShell i₀ ε ∪ {z | z ∈ cxShell i ε ∧ z.1 + z.2 ≤ (n : ℤ)}

theorem mem_cxBox {a b : ℤ} {z : ℤ × ℤ} :
    z ∈ cxBox a b ↔ 0 ≤ z.1 ∧ z.1 ≤ a ∧ 0 ≤ z.2 ∧ z.2 ≤ b := Iff.rfl

theorem mem_cxB {i : ℕ} {z : ℤ × ℤ} :
    z ∈ cxB i ↔ 0 ≤ z.1 ∧ z.1 ≤ (i : ℤ) + 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1 := Iff.rfl

theorem mem_cxB' {i : ℕ} {a b : ℤ} :
    ((a, b) : ℤ × ℤ) ∈ cxB i ↔ 0 ≤ a ∧ a ≤ (i : ℤ) + 1 ∧ 0 ≤ b ∧ b ≤ 1 := Iff.rfl

theorem mem_cxShell {i ε : ℕ} {z : ℤ × ℤ} :
    z ∈ cxShell i ε ↔ 0 ≤ z.1 ∧ z.1 ≤ (i : ℤ) + 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1 + (ε : ℤ) := Iff.rfl

/-! ### The window and the boxes are `E(S)`-enveloped -/

@[simp] theorem coe_cxS : (cxS : Set (ℤ × ℤ)) = sq1 := by
  ext z
  obtain ⟨a, b⟩ := z
  simp only [cxS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, sq1, mem_box, Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
  · rintro ⟨h1, h2, h3, h4⟩
    omega

theorem envOf_cxBox {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    EnvOf (cxS : Set (ℤ × ℤ)) (cxBox a b) := by
  rw [coe_cxS]
  refine envOf_of_E_eq (isLatticeConvexRegion_box _ _) ?_ ?_
  · rw [cxBox, E_box (p := (0, 0)) (q := (a, b)) ha hb, E_sq1]
  · intro n hn
    rw [E_sq1] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · rw [encard_face_sq1_right, cxBox, face_box_right (p := (0, 0)) (q := (a, b)) ha.le]
      exact two_le_encard_of_pair (a := (a, (0 : ℤ))) (b := (a, b))
        ⟨rfl, le_refl _, hb.le⟩ ⟨rfl, hb.le, le_refl _⟩
        (by intro h; rw [Prod.ext_iff] at h; omega)
    · rw [encard_face_sq1_left, cxBox, face_box_left (p := (0, 0)) (q := (a, b)) ha.le]
      exact two_le_encard_of_pair (a := ((0 : ℤ), (0 : ℤ))) (b := ((0 : ℤ), b))
        ⟨rfl, le_refl _, hb.le⟩ ⟨rfl, hb.le, le_refl _⟩
        (by intro h; rw [Prod.ext_iff] at h; omega)
    · rw [encard_face_sq1_top, cxBox, face_box_top (p := (0, 0)) (q := (a, b)) hb.le]
      exact two_le_encard_of_pair (a := ((0 : ℤ), b)) (b := (a, b))
        ⟨le_refl _, ha.le, rfl⟩ ⟨ha.le, le_refl _, rfl⟩
        (by intro h; rw [Prod.ext_iff] at h; omega)
    · rw [encard_face_sq1_bot, cxBox, face_box_bot (p := (0, 0)) (q := (a, b)) hb.le]
      exact two_le_encard_of_pair (a := ((0 : ℤ), (0 : ℤ))) (b := (a, (0 : ℤ)))
        ⟨le_refl _, ha.le, rfl⟩ ⟨ha.le, le_refl _, rfl⟩
        (by intro h; rw [Prod.ext_iff] at h; omega)

theorem cxBox_finite (a b : ℤ) : (cxBox a b).Finite :=
  Set.Finite.subset ((Set.finite_Icc (0 : ℤ) a).prod (Set.finite_Icc (0 : ℤ) b))
    (by rintro z ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩)

/-! ### The dynamics of `ξ` -/

theorem cxTheta_eq : cxTheta = T ((0 : ℤ), (-1 : ℤ)) cxEta := by
  funext z
  simp only [cxTheta, T, cxEta, Prod.snd_add]
  norm_num

/-- Every configuration in the orbit closure of `ξ` is constant along horizontal lines. -/
theorem cx_horiz {x : Config ℤ} (hx : x ∈ orbitClosure cxEta) {z w : ℤ × ℤ} (h : z.2 = w.2) :
    x z = x w := by
  obtain ⟨u, hu⟩ := hx {z, w}
  rw [hu z (by simp), hu w (by simp)]
  simp only [cxEta, Prod.snd_add, h]

theorem cxXper_mem : cxXper ∈ orbitClosure cxEta := by
  intro W
  obtain ⟨M, hM⟩ := (W.image (fun w : ℤ × ℤ => w.2)).exists_le
  refine ⟨((0 : ℤ), -M - 1), fun w hw => ?_⟩
  have hw2 : w.2 ≤ M := hM _ (Finset.mem_image_of_mem _ hw)
  simp only [cxXper, cxEta, Prod.snd_add]
  rw [if_neg (by omega)]

theorem cxOne_mem : cxOne ∈ orbitClosure cxEta := by
  intro W
  obtain ⟨M, hM⟩ := (W.image (fun w : ℤ × ℤ => -w.2)).exists_le
  refine ⟨((0 : ℤ), M + 1), fun w hw => ?_⟩
  have hw2 : -w.2 ≤ M := hM _ (Finset.mem_image_of_mem _ hw)
  simp only [cxOne, cxEta, Prod.snd_add]
  rw [if_pos (by omega)]

theorem cxTheta_mem : cxTheta ∈ orbitClosure cxEta := by
  rw [cxTheta_eq]; exact T_mem_orbitClosure _ _

/-- `GeneratesAt ξ S (1,1)`: the value at `(1,1)` is the value at `(0,1) ∈ S.erase (1,1)`. -/
theorem cx_generatesAt : Nivat.Colle.GeneratesAt cxEta cxS ((1 : ℤ), (1 : ℤ)) := by
  refine ⟨by decide, fun x hx y hy hxy => ?_⟩
  have h01 : ((0 : ℤ), (1 : ℤ)) ∈ cxS.erase ((1 : ℤ), (1 : ℤ)) := by decide
  calc x ((1 : ℤ), (1 : ℤ)) = x ((0 : ℤ), (1 : ℤ)) := cx_horiz hx rfl
    _ = y ((0 : ℤ), (1 : ℤ)) := hxy _ h01
    _ = y ((1 : ℤ), (1 : ℤ)) := cx_horiz hy rfl

theorem cx_nonexp_pos : Colle45.IsOneSidedNonexpansive cxEta ((0 : ℤ), (1 : ℤ)) := by
  refine ⟨T ((0 : ℤ), (-5 : ℤ)) cxEta, cxXper, T_mem_orbitClosure _ _, cxXper_mem, ?_, ?_⟩
  · intro h
    have := congrFun h ((0 : ℤ), (6 : ℤ))
    simp only [T, cxEta, cxXper, Prod.snd_add] at this
    norm_num at this
  · intro z hz
    simp only [dot] at hz
    simp only [T, cxEta, cxXper, Prod.snd_add]
    rw [if_neg (by omega)]

theorem cx_nonexp_neg : Colle45.IsOneSidedNonexpansive cxEta (-((0 : ℤ), (1 : ℤ))) := by
  refine ⟨T ((0 : ℤ), (5 : ℤ)) cxEta, cxOne, T_mem_orbitClosure _ _, cxOne_mem, ?_, ?_⟩
  · intro h
    have := congrFun h ((0 : ℤ), (-5 : ℤ))
    simp only [T, cxEta, cxOne, Prod.snd_add] at this
    norm_num at this
  · intro z hz
    simp only [dot, Prod.fst_neg, Prod.snd_neg] at hz
    simp only [T, cxEta, cxOne, Prod.snd_add]
    rw [if_pos (by omega)]

theorem cx_nel : ((0 : ℤ), (1 : ℤ)) ∈ Colle45.NonExpansiveLine cxEta := by
  obtain ⟨x, y, hx, hy, hne, hagree⟩ := cx_nonexp_pos
  exact ⟨isCoprime_one_right, x, y, hx, hy, hne, fun z hz => hagree z hz⟩

/-! ### The region has only horizontal rays -/

theorem cx_ray_flat {z₀ h : ℤ × ℤ} (hray : ∀ k : ℕ, z₀ + (k : ℤ) • h ∈ ⋃ i, cxB i) :
    h.2 = 0 := by
  obtain ⟨i0, h0⟩ := Set.mem_iUnion.1 (hray 0)
  obtain ⟨i3, h3⟩ := Set.mem_iUnion.1 (hray 3)
  rw [mem_cxB] at h0 h3
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Nat.cast_zero, Nat.cast_ofNat,
    zero_mul] at h0 h3
  omega

/-! ## The `ChainData` instance -/

theorem cx_maximalHat (i : ℕ) (Tset : Set (ℤ × ℤ))
    (hsub : Tset ⊆ {z | z + ((0 : ℕ) : ℤ) • ((0 : ℤ), (1 : ℤ)) ∈
      Nivat.Colle35.halfStrip (cxB i) ((0 : ℤ), (1 : ℤ))})
    (hagree : ∀ z ∈ Tset, cxEta (z + (((0 : ℕ) : ℤ) • ((0 : ℤ), (1 : ℤ)) + ((0 : ℤ), (-1 : ℤ)))) =
      cxXper (z + ((0 : ℕ) : ℤ) • ((0 : ℤ), (1 : ℤ)))) :
    Tset ⊆ cxB i := by
  intro z hz
  obtain ⟨b, hb, t, hbt⟩ := hsub hz
  rw [Nat.cast_zero, zero_smul, add_zero] at hbt
  rw [mem_cxB] at hb
  have hz1 : z.1 = b.1 := by
    rw [hbt]; simp
  have hz2 : z.2 = b.2 + (t : ℤ) := by
    rw [hbt]; simp
  have hag := hagree z hz
  rw [Nat.cast_zero, zero_smul, zero_add] at hag
  simp only [cxEta, cxXper, Prod.snd_add] at hag
  have hz2le : z.2 ≤ 1 := by
    by_contra hcon
    rw [if_pos (by omega)] at hag
    exact absurd hag (by norm_num)
  rw [mem_cxB]
  refine ⟨by omega, by omega, by omega, hz2le⟩

theorem cx_fillStep (i i₀ ε n : ℕ) (z : ℤ × ℤ) (hz : z ∈ cxFill i i₀ ε (n + 1)) :
    z ∈ cxFill i i₀ ε n ∨ ∃ t : ℤ × ℤ, z = ((1 : ℤ), (1 : ℤ)) + t ∧
      ∀ b ∈ cxS.erase ((1 : ℤ), (1 : ℤ)), b + t ∈ cxFill i i₀ ε n := by
  rcases hz with hz | hz
  · exact Or.inl (Or.inl hz)
  obtain ⟨hzs, hzn⟩ := hz
  rw [mem_cxShell] at hzs
  by_cases hle : z.1 + z.2 ≤ (n : ℤ)
  · exact Or.inl (Or.inr ⟨(mem_cxShell.2 hzs), hle⟩)
  by_cases hin : z ∈ cxB i ∪ cxShell i₀ ε
  · exact Or.inl (Or.inl hin)
  -- `z` is a genuinely new site: strictly above the base row and strictly right of `Â_{i₀}`
  push_cast at hzn
  have hz2 : 2 ≤ z.2 := by
    by_contra hcon
    exact hin (Or.inl (mem_cxB.2 ⟨hzs.1, hzs.2.1, hzs.2.2.1, by omega⟩))
  have hz1 : 1 ≤ z.1 := by
    by_contra hcon
    exact hin (Or.inr (mem_cxShell.2 ⟨hzs.1, by omega, hzs.2.2.1, hzs.2.2.2⟩))
  refine Or.inr ⟨z - ((1 : ℤ), (1 : ℤ)), by abel, fun b hb => ?_⟩
  have hb3 : b = ((0 : ℤ), (0 : ℤ)) ∨ b = ((1 : ℤ), (0 : ℤ)) ∨ b = ((0 : ℤ), (1 : ℤ)) := by
    have hb' := Finset.mem_of_mem_erase hb
    have hne := Finset.ne_of_mem_erase hb
    simp only [cxS, Finset.mem_insert, Finset.mem_singleton] at hb'
    tauto
  refine Or.inr ⟨mem_cxShell.2 ?_, ?_⟩ <;>
    rcases hb3 with rfl | rfl | rfl <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;>
        refine ?_ <;> omega

theorem cx_shellSubStrip (i ε : ℕ) : cxShell i ε ⊆
    {z | z + ((0 : ℕ) : ℤ) • ((0 : ℤ), (1 : ℤ)) ∈
      Nivat.Colle35.halfStrip (cxB i) ((0 : ℤ), (1 : ℤ))} := by
  intro z hz
  rw [mem_cxShell] at hz
  rw [Set.mem_ofPred_eq, Nat.cast_zero, zero_smul, add_zero]
  refine ⟨(z.1, (0 : ℤ)), mem_cxB.2 ⟨hz.1, hz.2.1, le_refl _, by norm_num⟩, z.2.toNat, ?_⟩
  have : ((z.2.toNat : ℤ)) = z.2 := Int.toNat_of_nonneg hz.2.2.1
  rw [Prod.ext_iff]
  constructor
  · simp
  · simp [this]

theorem cx_shellInfZero : cxShellInf 0 ⊆ ⋃ i, cxB i := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hz
  refine Set.mem_iUnion.2 ⟨z.1.toNat, mem_cxB.2 ⟨h1, ?_, h2, by simpa using h3⟩⟩
  have : ((z.1.toNat : ℤ)) = z.1 := Int.toNat_of_nonneg h1
  omega

/-- **The window `[0,1]²` is lattice convex.**  Needed because Round 80 rephrased
`ChainData.fillCover` (`Lemma35.lean:765`) against `Colle37.GenClosure`, whose `step` carries
the side condition `LatticeConvex (S.erase a)`.  Proof template: `CyrKra224.lean:539`. -/
theorem latticeConvex_cxS : LatticeConvex cxS := by
  have hsub : toReal '' ((cxS : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))
      ⊆ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1} := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [cxS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> norm_num [toReal]
  have hcvx : Convex ℝ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1} := by
    intro p hp q hq a b ha hb hab
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      nlinarith
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := convexHull_min hsub hcvx hz
  simp only [toReal] at h1 h2 h3 h4
  have h1' : (0 : ℤ) ≤ z.1 := by exact_mod_cast h1
  have h2' : z.1 ≤ 1 := by exact_mod_cast h2
  have h3' : (0 : ℤ) ≤ z.2 := by exact_mod_cast h3
  have h4' : z.2 ≤ 1 := by exact_mod_cast h4
  obtain ⟨a, b⟩ := z
  simp only at h1' h2' h3' h4'
  simp only [cxS, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

/-- `(1,1)` is the strict `⟪(1,1),·⟫`-maximum of `cxS`, so erasing it keeps lattice convexity
(`Colle37Geom.latticeConvex_erase_of_lexExtreme`, `ShellGeom.lean:74`). -/
theorem latticeConvex_cxS_erase :
    LatticeConvex (cxS.erase ((1 : ℤ), (1 : ℤ))) :=
  Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme latticeConvex_cxS
    (n := ((1 : ℤ), (1 : ℤ))) (d := ((1 : ℤ), (0 : ℤ))) (by decide)

/-- `ChainData.fillZero` for `cxFill`, factored out so `fillCover` can reuse it. -/
theorem cx_fillZero (i i₀ ε : ℕ) : cxFill i i₀ ε 0 ⊆ cxB i ∪ cxShell i₀ ε := by
  rintro z (hz | ⟨hz, hzn⟩)
  · exact hz
  · rw [mem_cxShell] at hz
    exact Or.inl (mem_cxB.2 ⟨hz.1, hz.2.1, hz.2.2.1, by push_cast at hzn; omega⟩)

/-- The full chain-data package for the counterexample. -/
def cxChain : ChainData cxEta cxXper ((0 : ℤ), (1 : ℤ)) cxS ((1 : ℤ), (1 : ℤ)) where
  Env := EnvOf (cxS : Set (ℤ × ℤ))
  B := cxB
  A := cxB
  u := fun _ => ((0 : ℤ), (-1 : ℤ))
  kk := fun _ => 0
  Ahat := cxB
  shell := cxShell
  shellInf := cxShellInf
  envB i := envOf_cxBox (by positivity) (by norm_num)
  envA i := envOf_cxBox (by positivity) (by norm_num)
  subBA i := subset_rfl
  subAB i := by
    intro z hz
    rw [mem_cxB] at hz ⊢
    push_cast
    omega
  subStrip i := Nivat.Colle35.subset_halfStrip _ _
  agreeA i := by
    intro z hz
    rw [mem_cxB] at hz
    simp only [cxEta, cxXper, Prod.snd_add]
    rw [if_neg (by omega)]
  AhatEq i := by
    ext z
    simp
  AhatMono i j hij := by
    intro z hz
    rw [mem_cxB] at hz ⊢
    have : (i : ℤ) ≤ (j : ℤ) := Int.ofNat_le.2 hij
    omega
  maximalHat i Tset _ _ hsub hagree := cx_maximalHat i Tset hsub hagree
  shellFinite i ε := cxBox_finite _ _
  subShell i ε := by
    intro z hz
    rw [mem_cxB] at hz
    exact mem_cxShell.2 ⟨hz.1, hz.2.1, hz.2.2.1, by omega⟩
  shellSubInf i ε := by
    intro z hz
    rw [mem_cxShell] at hz
    exact ⟨hz.1, hz.2.2.1, hz.2.2.2⟩
  shellInfZero := cx_shellInfZero
  -- `I₀`（第 162 轮，`b3_colle2.txt:520`）：本实例的 shell 字段都不看 `i` 的下界，取 0。
  I₀ := 0
  shellSubStrip := fun ε _ _ _ i _ => cx_shellSubStrip i ε
  shellProper ε _i₀ hε _hEnv i _hi := by
    intro hcon
    have : ((0 : ℤ), (2 : ℤ)) ∈ cxShell i ε :=
      mem_cxShell.2 ⟨le_refl _, by positivity, by norm_num, by
        have : (1 : ℤ) ≤ (ε : ℤ) := by exact_mod_cast hε
        omega⟩
    have := hcon this
    rw [mem_cxB] at this
    norm_num at this
  shellEnv := ⟨1, 0, by norm_num, fun i _ => envOf_cxBox (by positivity) (by norm_num)⟩
  fill := cxFill
  fillZero i i₀ ε := cx_fillZero i i₀ ε
  fillStep := cx_fillStep
  -- Round 80 (`Lemma35.lean:765`) rephrased `fillCover` against `Colle37.GenClosure`;
  -- `genFill_of_abstract_fill` (`GenClosureWeaken.lean:116`) turns the filtration data
  -- `cx_fillZero` / `cx_fillStep` into it, at the index `(z.1 + z.2).toNat` that the old
  -- `⋃ n` witness produced.
  fillCover ε i₀ _hε _hEnv i _hi := by
    intro z hz
    refine Nivat.GenClosureWeaken.genFill_of_abstract_fill (S := cxS)
      (gen := ((1 : ℤ), (1 : ℤ))) (fill := cxFill i i₀ ε) (by decide)
      latticeConvex_cxS_erase (cx_fillZero i i₀ ε) (cx_fillStep i i₀ ε)
      (z.1 + z.2).toNat z (Or.inr ⟨hz, ?_⟩)
    rw [mem_cxShell] at hz
    have : (((z.1 + z.2).toNat : ℤ)) = z.1 + z.2 := Int.toNat_of_nonneg (by omega)
    omega

@[simp] theorem cxChain_Ahat : cxChain.Ahat = cxB := rfl

@[simp] theorem cxChain_B : cxChain.B = cxB := rfl

theorem cx_grow (i : ℕ) : cxChain.B i ⊂ cxChain.B (i + 1) := by
  rw [Set.ssubset_iff_of_subset]
  · refine ⟨((i : ℤ) + 2, (0 : ℤ)), ?_, ?_⟩
    · show ((i : ℤ) + 2, (0 : ℤ)) ∈ cxB (i + 1)
      have hc : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
      rw [mem_cxB', hc]
      omega
    · show ¬ (((i : ℤ) + 2, (0 : ℤ)) ∈ cxB i)
      rw [mem_cxB']; push_cast; omega
  · show cxB i ⊆ cxB (i + 1)
    intro z hz
    rw [mem_cxB] at hz ⊢
    push_cast
    omega

theorem cx_periodicOn :
    PeriodicOnWith cxTheta (⋃ i, cxChain.Ahat i) ((0 : ℤ), (1 : ℤ)) := by
  refine ⟨by simp [Prod.ext_iff], fun g hg hg' => ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hg
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hg'
  rw [show cxChain.Ahat i = cxB i from rfl, mem_cxB] at hi
  rw [show cxChain.Ahat j = cxB j from rfl, mem_cxB] at hj
  simp only [Prod.snd_add] at hj
  simp only [cxTheta, Prod.snd_add]
  rw [if_neg (by omega), if_neg (by omega)]

/-! ## The refutation -/

theorem cx_no_two_rays :
    ¬ ∃ h h' z₀ z₀' : ℤ × ℤ, det h h' ≠ 0 ∧
      (∀ k : ℕ, z₀ + (k : ℤ) • h ∈ ⋃ i, cxChain.Ahat i) ∧
      (∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ ⋃ i, cxChain.Ahat i) ∧
      (∀ z ∈ ⋃ i, cxChain.Ahat i, z + h ∈ ⋃ i, cxChain.Ahat i →
        cxTheta (z + h) = cxTheta z) ∧
      (∀ z ∈ ⋃ i, cxChain.Ahat i, z + h' ∈ ⋃ i, cxChain.Ahat i →
        cxTheta (z + h') = cxTheta z) := by
  rintro ⟨h, h', z₀, z₀', hdet, hr, hr', -, -⟩
  exact hdet (by simp [det, cx_ray_flat hr, cx_ray_flat hr'])

/-! ### The diagnosis, made falsifiable

The prose above claims that `hξ` excludes this witness, and that strictly weaker conditions
already do.  Both claims are theorems, so a reader can check them rather than trust them. -/

/-- `ξ` is periodic, with period `(1,0)`.  Hence it is not a counterexample to Nivat. -/
theorem cx_isPeriodic : IsPeriodic cxEta := by
  refine ⟨((1 : ℤ), (0 : ℤ)), ?_, by simp [Prod.ext_iff]⟩
  show T ((1 : ℤ), (0 : ℤ)) cxEta = cxEta
  funext z
  simp [T, cxEta]

/-- Therefore `hξ : IsMinimalCounterexample ξ`, which the extraction dropped, does exclude
this witness. -/
theorem cx_not_minimalCounterexample : ¬ IsMinimalCounterexample cxEta :=
  fun h => h.1.2.2.1 cx_isPeriodic

/-- But `hξ` is **not** the weakest repair: `¬ IsPeriodic ξ` alone already excludes the
witness, by `cx_isPeriodic`, and so does the positivity clause of `IsCounterexample`. -/
theorem cx_not_pos : cxEta ((0 : ℤ), (0 : ℤ)) = 0 := rfl

end PeriodsRays

open PeriodsRays in
/-- **All twelve hypotheses of `region_periods_and_rays`, and none of its conclusion.**

The extra conjuncts after `PeriodicOnWith` are five *further* facts that `colle_region` has
in scope at the extracted `sorry`: the two remaining outputs of `exists_chainData`
(`xper ∈ orbitClosure ξ`, `p ∈ Per xper`) and all three outputs of `Colle35.lemma35`
(`hϑ_agree` at `K = 0`, `hshell` at `ε = 0`, `hshell_not` at `ε + 1 = 1`).  So the failure is
not an artefact of dropping those five.

They are **not** everything in scope: `hfin`, `hR_lattice_convex`, `hR_nonempty`, `hw`,
`hw₁`, `hw₂` are also available there and are not asserted here.  See the module docstring. -/
theorem region_periods_and_rays_counterexample :
    ∃ (ξ xper ϑ : Config ℤ) (vl p ℓ : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
      (c : ChainData ξ xper vl S gen),
      c.Env = Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)) ∧
      (∀ i, c.B i ⊂ c.B (i + 1)) ∧
      Nivat.Colle.GeneratesAt ξ S gen ∧
      vl ≠ 0 ∧ p ≠ 0 ∧ det p vl = 0 ∧ det ℓ vl = 0 ∧
      ℓ ∈ Colle45.NonExpansiveLine ξ ∧
      Colle45.IsOneSidedNonexpansive ξ ℓ ∧
      Colle45.IsOneSidedNonexpansive ξ (-ℓ) ∧
      ϑ ∈ orbitClosure ξ ∧
      PeriodicOnWith ϑ (⋃ i, c.Ahat i) p ∧
      xper ∈ orbitClosure ξ ∧ p ∈ Per xper ∧
      (∀ z ∈ ⋃ i, c.Ahat i, ϑ z = T (((0 : ℕ) : ℤ) • vl) xper z) ∧
      (∀ z ∈ c.shellInf 0, ϑ z = T (((0 : ℕ) : ℤ) • vl) xper z) ∧
      ¬ (∀ z ∈ c.shellInf 1, ϑ z = T (((0 : ℕ) : ℤ) • vl) xper z) ∧
      ¬ (∃ h h' z₀ z₀' : ℤ × ℤ, det h h' ≠ 0 ∧
          (∀ k : ℕ, z₀ + (k : ℤ) • h ∈ ⋃ i, c.Ahat i) ∧
          (∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ ⋃ i, c.Ahat i) ∧
          (∀ z ∈ ⋃ i, c.Ahat i, z + h ∈ ⋃ i, c.Ahat i → ϑ (z + h) = ϑ z) ∧
          (∀ z ∈ ⋃ i, c.Ahat i, z + h' ∈ ⋃ i, c.Ahat i → ϑ (z + h') = ϑ z)) := by
  refine ⟨cxEta, cxXper, cxTheta, ((0 : ℤ), (1 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((0 : ℤ), (1 : ℤ)),
    cxS, ((1 : ℤ), (1 : ℤ)), cxChain, rfl, cx_grow, cx_generatesAt, by simp [Prod.ext_iff],
    by simp [Prod.ext_iff], by simp [det], by simp [det], cx_nel, cx_nonexp_pos, cx_nonexp_neg,
    cxTheta_mem, cx_periodicOn, cxXper_mem, ?_, ?_, ?_, ?_, cx_no_two_rays⟩
  · show T ((0 : ℤ), (1 : ℤ)) cxXper = cxXper
    rfl
  · intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    rw [show cxChain.Ahat i = cxB i from rfl, mem_cxB] at hi
    simp only [cxTheta, T, cxXper]
    rw [if_neg (by omega)]
  · intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    simp only [cxTheta, T, cxXper]
    rw [if_neg (by push_cast at h3; omega)]
  · intro hcon
    have h2 : ((0 : ℤ), (2 : ℤ)) ∈ cxChain.shellInf 1 := by
      refine ⟨le_refl _, by norm_num, by norm_num⟩
    have := hcon _ h2
    simp only [cxTheta, T, cxXper] at this
    norm_num at this

/-- **The frozen statement of `Nivat.ColleReg.region_periods_and_rays` is false.**

The proposition negated here is the universal closure of that theorem, binder for binder
(the `variable` block of `RegionSteps.lean` is `{ξ xper ϑ : Config ℤ} {vl p ℓ : ℤ × ℤ}
{S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}`, in that order).  A proof of the theorem would give this
`∀`-statement by instantiation, so no proof of the theorem exists. -/
theorem not_region_periods_and_rays :
    ¬ (∀ {ξ xper ϑ : Config ℤ} {vl p ℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
        (_c : ChainData ξ xper vl S gen),
        _c.Env = Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)) →
        (∀ i, _c.B i ⊂ _c.B (i + 1)) →
        Nivat.Colle.GeneratesAt ξ S gen →
        vl ≠ 0 → p ≠ 0 → det p vl = 0 → det ℓ vl = 0 →
        ℓ ∈ Colle45.NonExpansiveLine ξ →
        Colle45.IsOneSidedNonexpansive ξ ℓ →
        Colle45.IsOneSidedNonexpansive ξ (-ℓ) →
        ϑ ∈ orbitClosure ξ →
        PeriodicOnWith ϑ (⋃ i, _c.Ahat i) p →
        ∃ h h' z₀ z₀' : ℤ × ℤ, det h h' ≠ 0 ∧
          (∀ k : ℕ, z₀ + (k : ℤ) • h ∈ ⋃ i, _c.Ahat i) ∧
          (∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ ⋃ i, _c.Ahat i) ∧
          (∀ z ∈ ⋃ i, _c.Ahat i, z + h ∈ ⋃ i, _c.Ahat i → ϑ (z + h) = ϑ z) ∧
          (∀ z ∈ ⋃ i, _c.Ahat i, z + h' ∈ ⋃ i, _c.Ahat i → ϑ (z + h') = ϑ z)) := by
  intro H
  obtain ⟨ξ, xper, ϑ, vl, p, ℓ, S, gen, c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    _, _, _, _, _, hno⟩ := region_periods_and_rays_counterexample
  exact hno (H c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12)

end Nivat.ColleStep
