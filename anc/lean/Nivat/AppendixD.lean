/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Orbit
import Nivat.MorseHedlund
import Nivat.Words
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Data.Int.Interval

/-!
# Appendix D. The `𝔽_p` and convex form of Szabados' theorem

Formalisation of Appendix D of *The Convex Nivat Conjecture* (Pan).

Szabados [17, Theorem 1] proved that a non-periodic sum of two `ℤ`-valued periodic
configurations with different period directions does not have low rectangular complexity; the
convex generalisation is [2, Theorem 1.7], and the `𝔽_p` and convex version is [5, Theorem 2.8].
This appendix proves the latter in full: pigeonhole, balanced sets, and the one-dimensional
Morse–Hedlund theorem, with the coefficient ring `𝔽_p` (only addition, subtraction, equality and
periodicity are used) and an arbitrary lattice-convex window (at each step of Lemma D.5 one
deletes whichever of the two extreme rows is the shorter).

Apart from the one-dimensional Morse–Hedlund theorem, nothing external is quoted, so nothing in
this file is an `axiom`: `periodic_of_subwords_le` and `periodic_of_two_sided_determinacy` are
imported from `Nivat.MorseHedlund` and `Nivat.Words`.

## Main definitions

* `Nivat.SzabadosData` — the data of Theorem D.1 in the normalised form of §D.1: the primitive
  direction `u` of `h₁ = c₁ u`, the linear form `φ = det(u, ·)`, and `Δ = φ(h₂) > 0`.
* `Nivat.SzabadosData.row`, `Nivat.SzabadosData.strip`, `Nivat.SzabadosData.ht`,
  `Nivat.SzabadosData.Etop`, `Nivat.SzabadosData.Ebot` — the notation of §D.1.
* `Nivat.SzabadosData.Balanced` — **Definition D.4**.
* `Nivat.SzabadosData.AmbiguityStrip` — **Definition D.6**.
* `Nivat.PeriodicDecomp`, `Nivat.HasOrder` — periodic decompositions and `ord(ξ)`.

## Main results

* `Nivat.periodic_of_subwords_le` — the one-dimensional Morse–Hedlund theorem [13].
* `Nivat.periodic_of_two_sided_determinacy` — the finite-state argument of step (6) of
  Lemma D.7, quoted again in Lemma 8.8.
* `Nivat.SzabadosData.period_of_strip` — **Lemma D.3**.
* `Nivat.SzabadosData.exists_balanced` — **Lemma D.5**.
* `Nivat.SzabadosData.isPeriodic_of_ambiguityStrip` — **Lemma D.7**.
* `Nivat.SzabadosData.xi_isPeriodic`, `Nivat.isPeriodic_of_add` — **Theorem D.1**.
* `Nivat.not_lowConvexComplexity_of_hasOrder_two` — **Corollary D.2**.

## Status

Skeleton; proofs are line D.
-/

namespace Nivat

open Finset
open scoped Pointwise

/-! ### Two one-dimensional inputs

`subwords`, `periodic_of_subwords_le` (the one-dimensional Morse–Hedlund theorem [13]) and
`periodic_of_two_sided_determinacy` (the finite-state argument of step (6) of Lemma D.7) are
imported from `Nivat.MorseHedlund` and `Nivat.Words` respectively. -/

/-! ### General translation invariance

Step (1) of Lemma D.7 translates `B` so that its top row lands on `L_b`.  These lemmas record
that `Conv`, `LatticeConvex` and `P` are translation invariant, so that this replacement changes
none of the hypotheses of `Balanced`. -/

/-- `toReal` is additive. -/
theorem toReal_add (z w : ℤ × ℤ) : toReal (z + w) = toReal z + toReal w := by
  simp [toReal]

/-- Translating a finite window by `v` translates its convex hull by `toReal v`. -/
theorem Conv_image_add (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    Conv (S.image (· + v)) = (fun x => x + toReal v) '' Conv S := by
  have hcoe : ((S.image (· + v) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))
      = (· + v) '' (S : Set (ℤ × ℤ)) := by
    simp [Finset.coe_image]
  have hset : toReal '' (↑(S.image (· + v)) : Set (ℤ × ℤ))
      = (fun y => y + toReal v) '' (toReal '' (↑S : Set (ℤ × ℤ))) := by
    rw [hcoe]
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨toReal w, ⟨w, hw, rfl⟩, by rw [toReal_add]⟩
    · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w + v, ⟨w, hw, rfl⟩, by rw [toReal_add]⟩
  have himg2 : (fun y => y + toReal v) '' (toReal '' (↑S : Set (ℤ × ℤ)))
      = toReal v +ᵥ (toReal '' (↑S : Set (ℤ × ℤ))) := by
    ext x; simp only [Set.mem_image, vadd_eq_add, Set.mem_vadd_set]; constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, add_comm _ _⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, add_comm _ _⟩
  unfold Conv
  rw [hset, himg2, convexHull_vadd]
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, add_comm _ _⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, add_comm _ _⟩

/-- A translate of a lattice-convex set is lattice-convex. -/
theorem LatticeConvex.translate {S : Finset (ℤ × ℤ)} (hS : LatticeConvex S) (v : ℤ × ℤ) :
    LatticeConvex (S.image (· + v)) := by
  intro z hz
  rw [Conv_image_add] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  have hyz' : y + toReal v = toReal z := hyz
  have hzv : toReal (z - v) = y := by
    have hsub : toReal (z - v) = toReal z - toReal v := by
      rw [show z = z - v + v from by abel, toReal_add]; abel_nf
    rw [hsub, ← hyz']; abel
  have hmem := hS (z - v) (hzv ▸ hy)
  exact Finset.mem_image.mpr ⟨z - v, hmem, by abel⟩

/-- Complexity is invariant under translating the window. -/
theorem P_translate {α : Type*} (θ : Config α) (Q : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    P θ (Q.image (· + v)) = P θ Q := by
  classical
  set r : (↥(Q.image (· + v)) → α) → (↥Q → α) :=
    fun g q => g ⟨(q : ℤ × ℤ) + v, Finset.mem_image_of_mem _ q.2⟩ with hr
  have himg : patterns θ Q = r '' patterns θ (Q.image (· + v)) := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨pattern θ (Q.image (· + v)) (w - v), ⟨w - v, rfl⟩, ?_⟩
      funext q
      simp only [hr, pattern]
      congr 1; abel
    · rintro ⟨g, ⟨u, rfl⟩, rfl⟩
      refine ⟨u + v, ?_⟩
      funext q
      simp only [hr, pattern]
      congr 1; abel
  have hrinj : Function.Injective r := by
    intro g1 g2 heq
    funext w
    obtain ⟨q, hq, hqw⟩ := Finset.mem_image.mp w.2
    have hw : w = ⟨q + v, Finset.mem_image_of_mem _ hq⟩ := Subtype.ext hqw.symm
    rw [hw]
    exact congrFun heq ⟨q, hq⟩
  rw [P, P, himg]
  exact (hrinj.injOn).ncard_image.symm

/-! ### §D.1 The data and the notation -/

/-- The data of Theorem D.1, normalised as in §D.1 of the paper: `ξ = ξ₁ + ξ₂` with `ξ₁` of
period `h₁ = c₁ u`, `u` primitive and `c₁ ≥ 1`, and `ξ₂` of period `h₂`, oriented (replacing
`h₂` by `-h₂` if necessary) so that `Δ = det(u, h₂) > 0`.

Linear independence of `h₁` and `h₂` over `ℝ` is `det h₁ h₂ = c₁ Δ ≠ 0`, a consequence of
`c₁_pos` and `delta_pos`; see `SzabadosData.det_h1_h2_pos`. -/
structure SzabadosData (p : ℕ) where
  /-- The first summand, of period `h₁ = c₁ u`. -/
  xi1 : Config (ZMod p)
  /-- The second summand, of period `h₂`. -/
  xi2 : Config (ZMod p)
  /-- The primitive vector in the direction of `h₁`. -/
  u : ℤ × ℤ
  /-- The multiplier in `h₁ = c₁ u`. -/
  c₁ : ℕ
  /-- The period of the second summand, oriented so that `Δ = φ(h₂) > 0`. -/
  h2 : ℤ × ℤ
  u_primitive : Primitive u
  c₁_pos : 0 < c₁
  h1_mem_Per : (c₁ : ℤ) • u ∈ Per xi1
  h2_mem_Per : h2 ∈ Per xi2
  delta_pos : 0 < det u h2

namespace SzabadosData

variable {p : ℕ} (Sz : SzabadosData p)

/-- `h₁ = c₁ u`, a period of `ξ₁`. -/
def h1 : ℤ × ℤ := (Sz.c₁ : ℤ) • Sz.u

/-- `ξ = ξ₁ + ξ₂`. -/
def xi : Config (ZMod p) := fun z => Sz.xi1 z + Sz.xi2 z

/-- `φ = det(u, ·) : ℤ² → ℤ`, surjective because `u` is primitive.  Paper §D.1. -/
def phi (z : ℤ × ℤ) : ℤ := pi Sz.u z

theorem phi_surjective : Function.Surjective Sz.phi := pi_surjective Sz.u_primitive

theorem phi_add (z w : ℤ × ℤ) : Sz.phi (z + w) = Sz.phi z + Sz.phi w := pi_add _ _ _

theorem phi_smul (c : ℤ) (z : ℤ × ℤ) : Sz.phi (c • z) = c * Sz.phi z := pi_smul _ _ _

@[simp] theorem phi_u : Sz.phi Sz.u = 0 := det_self _

@[simp] theorem phi_neg (z : ℤ × ℤ) : Sz.phi (-z) = -Sz.phi z := by
  simp only [phi, pi, det, Prod.fst_neg, Prod.snd_neg]
  ring

@[simp] theorem phi_h1 : Sz.phi Sz.h1 = 0 := by
  rw [h1, phi_smul, phi_u, mul_zero]

/-- `Δ = φ(h₂) > 0`.  Paper §D.1. -/
def Delta : ℤ := Sz.phi Sz.h2

theorem Delta_pos : 0 < Sz.Delta := Sz.delta_pos

theorem h1_ne_zero : Sz.h1 ≠ 0 := by
  rw [h1]
  simp only [ne_eq, smul_eq_zero, not_or]
  exact ⟨by exact_mod_cast Sz.c₁_pos.ne', Sz.u_primitive.ne_zero⟩

/-- `h₁` and `h₂` are linearly independent over `ℝ`: `det h₁ h₂ = c₁ Δ > 0`. -/
theorem det_h1_h2_pos : 0 < det Sz.h1 Sz.h2 := by
  have heq : det Sz.h1 Sz.h2 = (Sz.c₁ : ℤ) * det Sz.u Sz.h2 := by
    simp only [h1, det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [heq]
  have hc : (0 : ℤ) < (Sz.c₁ : ℤ) := by exact_mod_cast Sz.c₁_pos
  have hd : (0 : ℤ) < det Sz.u Sz.h2 := Sz.delta_pos
  positivity

theorem h1_mem_Per_xi1 : Sz.h1 ∈ Per Sz.xi1 := Sz.h1_mem_Per

/-- The row `L_t = φ⁻¹(t)`; neighbouring lattice points of a row differ by `u`.
Paper §D.1. -/
def row (t : ℤ) : Set (ℤ × ℤ) := {z | Sz.phi z = t}

/-- The strip `St[a, b] = {v : a ≤ φ(v) ≤ b}`, of width `b - a`, the union of the rows
`L_a, …, L_b`; `St[a, a-1] = ∅`.  Paper §D.1. -/
def strip (a b : ℤ) : Set (ℤ × ℤ) := {z | a ≤ Sz.phi z ∧ Sz.phi z ≤ b}

theorem mem_strip_iff {a b : ℤ} {z : ℤ × ℤ} :
    z ∈ Sz.strip a b ↔ a ≤ Sz.phi z ∧ Sz.phi z ≤ b := Iff.rfl

@[simp] theorem strip_self_sub_one (a : ℤ) : Sz.strip a (a - 1) = ∅ := by
  ext z
  simp only [strip, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
  intro h
  omega

/-- Strips are invariant under `± u`.  Paper §D.1. -/
theorem add_zsmul_u_mem_strip {a b : ℤ} {z : ℤ × ℤ} (hz : z ∈ Sz.strip a b) (n : ℤ) :
    z + n • Sz.u ∈ Sz.strip a b := by
  rw [mem_strip_iff, Sz.phi_add, Sz.phi_smul, Sz.phi_u, mul_zero, add_zero]
  exact hz

/-- Strips are invariant under `± h₁`. -/
theorem add_zsmul_h1_mem_strip {a b : ℤ} {z : ℤ × ℤ} (hz : z ∈ Sz.strip a b) (n : ℤ) :
    z + n • Sz.h1 ∈ Sz.strip a b := by
  rw [mem_strip_iff, Sz.phi_add, Sz.phi_smul, Sz.phi_h1, mul_zero, add_zero]
  exact hz

/-- `max φ(F)`, the index of the top row of a non-empty finite `F`. -/
def topIdx (F : Finset (ℤ × ℤ)) : ℤ :=
  if h : F.Nonempty then (F.image Sz.phi).max' (h.image Sz.phi) else 0

/-- `min φ(F)`, the index of the bottom row of a non-empty finite `F`. -/
def botIdx (F : Finset (ℤ × ℤ)) : ℤ :=
  if h : F.Nonempty then (F.image Sz.phi).min' (h.image Sz.phi) else 0

/-- `ht(F) = max φ(F) - min φ(F)`.  Paper §D.1; `F` *fits into* `St[a, b]` when
`ht(F) ≤ b - a`. -/
def ht (F : Finset (ℤ × ℤ)) : ℤ := Sz.topIdx F - Sz.botIdx F

theorem botIdx_le_phi {F : Finset (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ F) :
    Sz.botIdx F ≤ Sz.phi z := by
  rw [botIdx, dif_pos ⟨z, hz⟩]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hz)

theorem phi_le_topIdx {F : Finset (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ F) :
    Sz.phi z ≤ Sz.topIdx F := by
  rw [topIdx, dif_pos ⟨z, hz⟩]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hz)

theorem subset_strip {F : Finset (ℤ × ℤ)} :
    (F : Set (ℤ × ℤ)) ⊆ Sz.strip (Sz.botIdx F) (Sz.topIdx F) :=
  fun _ hz => ⟨Sz.botIdx_le_phi hz, Sz.phi_le_topIdx hz⟩

theorem ht_nonneg {F : Finset (ℤ × ℤ)} (h : F.Nonempty) : 0 ≤ Sz.ht F := by
  obtain ⟨z, hz⟩ := h
  have := Sz.botIdx_le_phi hz
  have := Sz.phi_le_topIdx hz
  simp only [ht]
  omega

/-- The top row `E⁺(F) = F ∩ L_{max φ(F)}`.  Paper §D.1. -/
def Etop (F : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  F.filter fun z => Sz.phi z = Sz.topIdx F

/-- The bottom row `E⁻(F) = F ∩ L_{min φ(F)}`.  Paper §D.1. -/
def Ebot (F : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  F.filter fun z => Sz.phi z = Sz.botIdx F

/-- `E^ε(F)`, with `ε = true` standing for `+` and `ε = false` for `-`. -/
def Eside (ε : Bool) (F : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  if ε then Sz.Etop F else Sz.Ebot F

theorem Eside_subset (ε : Bool) (F : Finset (ℤ × ℤ)) : Sz.Eside ε F ⊆ F := by
  cases ε <;> simp [Eside, Etop, Ebot, Finset.filter_subset]

theorem Etop_nonempty {F : Finset (ℤ × ℤ)} (h : F.Nonempty) : (Sz.Etop F).Nonempty := by
  have hmem : Sz.topIdx F ∈ F.image Sz.phi := by
    rw [topIdx, dif_pos h]
    exact Finset.max'_mem _ _
  obtain ⟨z, hz, hzt⟩ := Finset.mem_image.mp hmem
  exact ⟨z, Finset.mem_filter.mpr ⟨hz, hzt⟩⟩

theorem Ebot_nonempty {F : Finset (ℤ × ℤ)} (h : F.Nonempty) : (Sz.Ebot F).Nonempty := by
  have hmem : Sz.botIdx F ∈ F.image Sz.phi := by
    rw [botIdx, dif_pos h]
    exact Finset.min'_mem _ _
  obtain ⟨z, hz, hzt⟩ := Finset.mem_image.mp hmem
  exact ⟨z, Finset.mem_filter.mpr ⟨hz, hzt⟩⟩

theorem Eside_nonempty {ε : Bool} {F : Finset (ℤ × ℤ)} (h : F.Nonempty) :
    (Sz.Eside ε F).Nonempty := by
  cases ε
  · simpa [Eside] using Sz.Ebot_nonempty h
  · simpa [Eside] using Sz.Etop_nonempty h

/-! ### Reversing the orientation

Step (a) of §D.5 says "we may assume `ε = +`: otherwise replace `u, h₁, φ, h₂` by
`-u, -h₁, -φ, -h₂`".  That replacement is the involution `Sz ↦ Sz.neg`, which leaves `ξ`
unchanged and exchanges the two extreme rows. -/

/-- The same configuration with the opposite orientation of the lattice line.  Paper §D.5(a). -/
def neg : SzabadosData p where
  xi1 := Sz.xi1
  xi2 := Sz.xi2
  u := -Sz.u
  c₁ := Sz.c₁
  h2 := -Sz.h2
  u_primitive := by
    show IsCoprime (-Sz.u.1) (-Sz.u.2)
    exact Sz.u_primitive.neg_neg
  c₁_pos := Sz.c₁_pos
  h1_mem_Per := by
    rw [smul_neg]
    exact AddSubgroup.neg_mem _ Sz.h1_mem_Per
  h2_mem_Per := AddSubgroup.neg_mem _ Sz.h2_mem_Per
  delta_pos := by
    have h : det (-Sz.u) (-Sz.h2) = det Sz.u Sz.h2 := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [h]
    exact Sz.delta_pos

@[simp] theorem neg_u : Sz.neg.u = -Sz.u := rfl
@[simp] theorem neg_h2 : Sz.neg.h2 = -Sz.h2 := rfl
@[simp] theorem neg_xi1 : Sz.neg.xi1 = Sz.xi1 := rfl
@[simp] theorem neg_xi2 : Sz.neg.xi2 = Sz.xi2 := rfl
@[simp] theorem neg_xi : Sz.neg.xi = Sz.xi := rfl

@[simp] theorem neg_phi (z : ℤ × ℤ) : Sz.neg.phi z = -Sz.phi z := by
  simp only [phi, pi, det, neg_u, Prod.fst_neg, Prod.snd_neg]
  ring

@[simp] theorem neg_h1 : Sz.neg.h1 = -Sz.h1 := by
  simp [h1, neg]

@[simp] theorem neg_Delta : Sz.neg.Delta = Sz.Delta := by
  simp [Delta]

theorem neg_topIdx (F : Finset (ℤ × ℤ)) : Sz.neg.topIdx F = -Sz.botIdx F := by
  rcases F.eq_empty_or_nonempty with rfl | h
  · simp [topIdx, botIdx]
  · apply le_antisymm
    · obtain ⟨z1, hz1⟩ := Sz.neg.Etop_nonempty h
      rw [Etop, Finset.mem_filter] at hz1
      have hb := Sz.botIdx_le_phi hz1.1
      rw [← hz1.2, Sz.neg_phi]
      omega
    · obtain ⟨z0, hz0⟩ := Sz.Ebot_nonempty h
      rw [Ebot, Finset.mem_filter] at hz0
      have h2 := Sz.neg.phi_le_topIdx hz0.1
      rw [Sz.neg_phi, hz0.2] at h2
      exact h2

theorem neg_botIdx (F : Finset (ℤ × ℤ)) : Sz.neg.botIdx F = -Sz.topIdx F := by
  rcases F.eq_empty_or_nonempty with rfl | h
  · simp [topIdx, botIdx]
  · apply le_antisymm
    · obtain ⟨z1, hz1⟩ := Sz.Etop_nonempty h
      rw [Etop, Finset.mem_filter] at hz1
      have h2 := Sz.neg.botIdx_le_phi hz1.1
      rw [Sz.neg_phi, hz1.2] at h2
      exact h2
    · obtain ⟨z0, hz0⟩ := Sz.neg.Ebot_nonempty h
      rw [Ebot, Finset.mem_filter] at hz0
      have h3 := Sz.phi_le_topIdx hz0.1
      rw [← hz0.2, Sz.neg_phi]
      omega

theorem neg_ht (F : Finset (ℤ × ℤ)) : Sz.neg.ht F = Sz.ht F := by
  simp only [ht, neg_topIdx, neg_botIdx]
  ring

theorem neg_Eside (ε : Bool) (F : Finset (ℤ × ℤ)) : Sz.neg.Eside ε F = Sz.Eside (!ε) F := by
  cases ε <;>
    simp [Eside, Etop, Ebot, neg_topIdx, neg_botIdx, Sz.neg_phi, neg_eq_iff_eq_neg, eq_comm]

theorem neg_strip (a b : ℤ) : Sz.neg.strip a b = Sz.strip (-b) (-a) := by
  ext z
  simp only [mem_strip_iff, Sz.neg_phi]
  omega

theorem neg_row (t : ℤ) : Sz.neg.row t = Sz.row (-t) := by
  ext z
  simp only [row, Set.mem_ofPred_eq, Sz.neg_phi]
  omega

/-! ### §D.2 Two algebraic facts -/

/-- **(D.1).**  The `h₂`-periodicity of `ξ₂` gives
`ξ(v + s h₂) - ξ(v) = ξ₁(v + s h₂) - ξ₁(v)`. -/
theorem xi_sub_eq_xi1_sub (s : ℤ) (v : ℤ × ℤ) :
    Sz.xi (v + s • Sz.h2) - Sz.xi v = Sz.xi1 (v + s • Sz.h2) - Sz.xi1 v := by
  have hper : s • Sz.h2 ∈ Per Sz.xi2 := AddSubgroup.zsmul_mem _ Sz.h2_mem_Per s
  simp only [xi]
  rw [Per.apply hper v]
  ring

/-- **(D.1).**  The difference `ξ(· + s h₂) - ξ(·)` is `h₁`-periodic in `·`. -/
theorem xi_sub_h1_periodic (s n : ℤ) (v : ℤ × ℤ) :
    Sz.xi (v + n • Sz.h1 + s • Sz.h2) - Sz.xi (v + n • Sz.h1)
      = Sz.xi (v + s • Sz.h2) - Sz.xi v := by
  have hn : n • Sz.h1 ∈ Per Sz.xi1 := AddSubgroup.zsmul_mem _ Sz.h1_mem_Per_xi1 n
  have key := Sz.xi_sub_eq_xi1_sub s (v + n • Sz.h1)
  have key0 := Sz.xi_sub_eq_xi1_sub s v
  rw [key, key0, show v + n • Sz.h1 + s • Sz.h2 = v + s • Sz.h2 + n • Sz.h1 from by abel,
    Per.apply hn (v + s • Sz.h2), Per.apply hn v]

/-- **(D.1), consequence.**  If `T^{s h₂}` agrees with `ξ` on a set `F`, then it agrees with
`ξ` on `F + ℤ h₁`.  Paper §D.2. -/
theorem agree_add_zsmul_h1 {s : ℤ} {F : Set (ℤ × ℤ)}
    (hF : ∀ v ∈ F, Sz.xi (v + s • Sz.h2) = Sz.xi v) (n : ℤ) {v : ℤ × ℤ} (hv : v ∈ F) :
    Sz.xi (v + n • Sz.h1 + s • Sz.h2) = Sz.xi (v + n • Sz.h1) := by
  have hd := Sz.xi_sub_h1_periodic s n v
  rw [hF v hv, sub_self] at hd
  exact sub_eq_zero.mp hd

/-- **Lemma D.3 (Periodicity on a strip implies periodicity).**  If `b - a ≥ Δ`, `q ≥ 1` and
`ξ(v + q u) = ξ(v)` for every `v` in the strip `St[a, b]`, then `q h₁` is a period of `ξ`. -/
theorem period_of_strip {a b : ℤ} (hab : Sz.Delta ≤ b - a) {q : ℤ} (_hq : 1 ≤ q)
    (h : ∀ v ∈ Sz.strip a b, Sz.xi (v + q • Sz.u) = Sz.xi v) :
    q • Sz.h1 ∈ Per Sz.xi := by
  -- Step 1: `ξ(v + q h₁) = ξ(v)` for `v` in the strip, applying `h` `c₁` times.
  have step1 : ∀ v ∈ Sz.strip a b, Sz.xi (v + q • Sz.h1) = Sz.xi v := by
    intro v hv
    have key : ∀ k : ℕ, Sz.xi (v + ((k : ℤ) * q) • Sz.u) = Sz.xi v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hmem : v + ((k : ℤ) * q) • Sz.u ∈ Sz.strip a b := Sz.add_zsmul_u_mem_strip hv _
        have happ := h _ hmem
        have heq : v + ((k : ℤ) * q) • Sz.u + q • Sz.u
            = v + (((k : ℤ) + 1) * q) • Sz.u := by
          rw [add_assoc, ← add_smul]
          congr 2
          ring
        rw [heq] at happ
        push_cast
        rw [happ, ih]
    have hkey := key Sz.c₁
    have hc : ((Sz.c₁ : ℤ) * q) • Sz.u = q • Sz.h1 := by
      rw [h1, smul_smul]
      congr 1
      ring
    rwa [hc] at hkey
  -- Step 2: `d(v) := ξ(v + q h₁) - ξ(v)` has period `h₂`.
  set d : Config (ZMod p) := fun v => Sz.xi (v + q • Sz.h1) - Sz.xi v with hd_def
  have hqh1_mem1 : q • Sz.h1 ∈ Per Sz.xi1 := AddSubgroup.zsmul_mem _ Sz.h1_mem_Per_xi1 q
  have hd_period : Sz.h2 ∈ Per d := by
    rw [mem_Per_iff]
    funext v
    show Sz.xi (v + Sz.h2 + q • Sz.h1) - Sz.xi (v + Sz.h2) = Sz.xi (v + q • Sz.h1) - Sz.xi v
    have e1 : Sz.xi (v + Sz.h2 + q • Sz.h1) - Sz.xi (v + Sz.h2)
        = Sz.xi2 (v + Sz.h2 + q • Sz.h1) - Sz.xi2 (v + Sz.h2) := by
      simp only [xi]
      rw [Per.apply hqh1_mem1 (v + Sz.h2)]
      ring
    have e2 : Sz.xi (v + q • Sz.h1) - Sz.xi v = Sz.xi2 (v + q • Sz.h1) - Sz.xi2 v := by
      simp only [xi]
      rw [Per.apply hqh1_mem1 v]
      ring
    rw [e1, e2, show v + Sz.h2 + q • Sz.h1 = v + q • Sz.h1 + Sz.h2 from by abel,
      Per.apply Sz.h2_mem_Per (v + q • Sz.h1), Per.apply Sz.h2_mem_Per v]
  -- Step 3: use `Δ > 0` and `b - a ≥ Δ` to reach an arbitrary `v₀` from the strip via `h₂`.
  rw [mem_Per_iff]
  funext v0
  show Sz.xi (v0 + q • Sz.h1) = Sz.xi v0
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, a ≤ Sz.phi v0 - k * Sz.Delta ∧ Sz.phi v0 - k * Sz.Delta ≤ b := by
    have hr := Int.mul_ediv_add_emod (Sz.phi v0 - a) Sz.Delta
    have hr0 : 0 ≤ (Sz.phi v0 - a) % Sz.Delta := Int.emod_nonneg _ Sz.Delta_pos.ne'
    have hr1 : (Sz.phi v0 - a) % Sz.Delta < Sz.Delta := Int.emod_lt_of_pos _ Sz.Delta_pos
    refine ⟨(Sz.phi v0 - a) / Sz.Delta, ?_, ?_⟩
    · linarith [hr]
    · linarith [hr, hab]
  have hphi : Sz.phi (v0 - k • Sz.h2) = Sz.phi v0 - k * Sz.Delta := by
    have hrw : v0 - k • Sz.h2 = v0 + (-k) • Sz.h2 := by rw [neg_smul]; abel
    rw [hrw, Sz.phi_add, Sz.phi_smul]
    show Sz.phi v0 + -k * Sz.Delta = Sz.phi v0 - k * Sz.Delta
    ring
  have hmemstrip : v0 - k • Sz.h2 ∈ Sz.strip a b := by
    rw [mem_strip_iff, hphi]
    exact ⟨hk1, hk2⟩
  have hz : Sz.xi (v0 - k • Sz.h2 + q • Sz.h1) = Sz.xi (v0 - k • Sz.h2) := step1 _ hmemstrip
  have hkperiod : k • Sz.h2 ∈ Per d := AddSubgroup.zsmul_mem _ hd_period k
  have hdv0 := Per.apply hkperiod (v0 - k • Sz.h2)
  rw [show v0 - k • Sz.h2 + k • Sz.h2 = v0 from by abel] at hdv0
  have hzero : d (v0 - k • Sz.h2) = 0 := by
    show Sz.xi (v0 - k • Sz.h2 + q • Sz.h1) - Sz.xi (v0 - k • Sz.h2) = 0
    rw [hz]; ring
  have hd0 : d v0 = 0 := hdv0.trans hzero
  exact sub_eq_zero.mp hd0

/-! ### §D.3 Balanced sets -/

/-- **Definition D.4.**  A non-empty finite lattice-convex `B` is `ε`-balanced, where
`E = E^ε(B)`, if

* (i) `P_ξ(B) ≤ |B|`;
* (ii) `P_ξ(B) < P_ξ(B \ E) + |E|`;
* (iii) every row of `B` between its two extreme rows has at least `|E| - 1` points.

Condition (iii) is stated as `|E| ≤ |B ∩ L_t| + 1` to avoid truncated subtraction. -/
structure Balanced (Sz : SzabadosData p) (ε : Bool) (B : Finset (ℤ × ℤ)) : Prop where
  /-- `B` is non-empty. -/
  nonempty : B.Nonempty
  /-- `B` is lattice-convex. -/
  latticeConvex : LatticeConvex B
  /-- (i) `P_ξ(B) ≤ |B|`. -/
  low : P Sz.xi B ≤ B.card
  /-- (ii) `P_ξ(B) < P_ξ(B \ E) + |E|`. -/
  deficit : P Sz.xi B < P Sz.xi (B \ Sz.Eside ε B) + (Sz.Eside ε B).card
  /-- (iii) every intermediate row of `B` has at least `|E| - 1` points. -/
  rows : ∀ t : ℤ, Sz.botIdx B ≤ t → t ≤ Sz.topIdx B →
    (Sz.Eside ε B).card ≤ (B.filter fun z => Sz.phi z = t).card + 1

/-- Balancedness is exchanged by the orientation reversal of `SzabadosData.neg`. -/
theorem balanced_neg {ε : Bool} {B : Finset (ℤ × ℤ)} :
    Sz.neg.Balanced ε B ↔ Sz.Balanced (!ε) B := by
  constructor
  · intro hB
    refine ⟨hB.nonempty, hB.latticeConvex, ?_, ?_, ?_⟩
    · rw [← Sz.neg_xi]; exact hB.low
    · rw [← Sz.neg_xi, ← Sz.neg_Eside]; exact hB.deficit
    · intro t ht1 ht2
      have hrow := hB.rows (-t) (by rw [Sz.neg_botIdx]; omega) (by rw [Sz.neg_topIdx]; omega)
      rw [Sz.neg_Eside] at hrow
      have hfilter : (B.filter fun z => Sz.neg.phi z = -t) = (B.filter fun z => Sz.phi z = t) := by
        apply Finset.filter_congr
        intro z _
        rw [Sz.neg_phi]
        omega
      rwa [hfilter] at hrow
  · intro hB
    refine ⟨hB.nonempty, hB.latticeConvex, ?_, ?_, ?_⟩
    · rw [Sz.neg_xi]; exact hB.low
    · rw [Sz.neg_xi, Sz.neg_Eside]; exact hB.deficit
    · intro t ht1 ht2
      rw [Sz.neg_botIdx] at ht1
      rw [Sz.neg_topIdx] at ht2
      rw [Sz.neg_Eside]
      have hrow := hB.rows (-t) (by omega) (by omega)
      have hfilter : (B.filter fun z => Sz.phi z = -t) = (B.filter fun z => Sz.neg.phi z = t) := by
        apply Finset.filter_congr
        intro z _
        rw [Sz.neg_phi]
        omega
      rw [hfilter] at hrow
      exact hrow

/-- The real-linear extension of `φ = det(u, ·)` to `ℝ²`, used to bound `Conv` by half-planes. -/
def phiR (x : ℝ × ℝ) : ℝ := (Sz.u.1 : ℝ) * x.2 - (Sz.u.2 : ℝ) * x.1

theorem isLinearMap_phiR : IsLinearMap ℝ Sz.phiR :=
  ⟨fun x y => by simp only [phiR, Prod.fst_add, Prod.snd_add]; ring,
   fun c x => by simp only [phiR, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩

theorem phiR_toReal (z : ℤ × ℤ) : Sz.phiR (toReal z) = ((Sz.phi z : ℤ) : ℝ) := by
  simp only [phiR, toReal, phi, pi_apply]
  push_cast
  ring

/-- Deleting the top row of a lattice-convex set leaves a lattice-convex set: the remaining
points lie in the open half-plane `φ < topIdx B`, so the lattice points of their convex hull
still belong to `B` (by `hB`) and have `φ`-value strictly below `topIdx B`, hence avoid the
deleted row. -/
theorem latticeConvex_sdiff_Etop {B : Finset (ℤ × ℤ)} (hB : LatticeConvex B) :
    LatticeConvex (B \ Sz.Eside true B) := by
  intro z hz
  have hsub : (↑(B \ Sz.Eside true B) : Set (ℤ × ℤ)) ⊆ (↑B : Set (ℤ × ℤ)) := by
    exact_mod_cast Finset.sdiff_subset
  have hConvSub : Conv (B \ Sz.Eside true B) ⊆ Conv B :=
    convexHull_mono (Set.image_mono hsub)
  have hzB : z ∈ B := hB z (hConvSub hz)
  set c : ℝ := (Sz.topIdx B : ℝ) with hc
  have hhalf : Convex ℝ {x : ℝ × ℝ | Sz.phiR x < c} := convex_halfSpace_lt Sz.isLinearMap_phiR c
  have himg : toReal '' (↑(B \ Sz.Eside true B) : Set (ℤ × ℤ)) ⊆ {x : ℝ × ℝ | Sz.phiR x < c} := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe, Finset.mem_sdiff] at hw
    obtain ⟨hwB, hwne⟩ := hw
    simp only [Eside, if_pos, Etop, Finset.mem_filter, not_and] at hwne
    have hle := Sz.phi_le_topIdx hwB
    have hne : Sz.phi w ≠ Sz.topIdx B := hwne hwB
    rw [Set.mem_ofPred_eq, Sz.phiR_toReal, hc]
    have : Sz.phi w < Sz.topIdx B := lt_of_le_of_ne hle hne
    exact_mod_cast this
  have hConvHalf : Conv (B \ Sz.Eside true B) ⊆ {x : ℝ × ℝ | Sz.phiR x < c} :=
    convexHull_min himg hhalf
  have hzhalf := hConvHalf hz
  rw [Set.mem_ofPred_eq, Sz.phiR_toReal, hc] at hzhalf
  have hlt : Sz.phi z < Sz.topIdx B := by exact_mod_cast hzhalf
  have hzne : z ∉ Sz.Eside true B := by
    simp only [Eside, if_pos, Etop, Finset.mem_filter, not_and]
    intro _
    omega
  exact Finset.mem_sdiff.mpr ⟨hzB, hzne⟩

/-- Deleting an extreme row of a lattice-convex set leaves a lattice-convex set: the remaining
points lie in an open half-plane, so the lattice points of their convex hull still belong to the
set and do not lie on the deleted row.  Paper Lemma D.5. -/
theorem latticeConvex_sdiff_Eside {B : Finset (ℤ × ℤ)} (hB : LatticeConvex B) (ε : Bool) :
    LatticeConvex (B \ Sz.Eside ε B) := by
  cases ε
  · have h := Sz.neg.latticeConvex_sdiff_Etop hB
    rwa [Sz.neg_Eside] at h
  · exact Sz.latticeConvex_sdiff_Etop hB

/-- Lattice convexity makes every non-empty row of `B` a run of consecutive lattice points
`w, w + u, …, w + (n-1) u`.  Paper §D.1, and step (5) of Lemma D.7. -/
theorem row_eq_run {B : Finset (ℤ × ℤ)} (hB : LatticeConvex B) (t : ℤ)
    (hne : (B.filter fun z => Sz.phi z = t).Nonempty) :
    ∃ (w : ℤ × ℤ) (n : ℕ), 0 < n ∧
      (B.filter fun z => Sz.phi z = t)
        = (Finset.range n).image fun s : ℕ => w + (s : ℤ) • Sz.u := by
  classical
  obtain ⟨u', hu'⟩ := Sz.u_primitive.exists_dual
  have hphiu' : Sz.phi u' = 1 := hu'
  set p : ℤ → ℤ × ℤ := fun k => k • Sz.u + t • u' with hp_def
  have hphip : ∀ k : ℤ, Sz.phi (p k) = t := by
    intro k
    show Sz.phi (k • Sz.u + t • u') = t
    rw [Sz.phi_add, Sz.phi_smul, Sz.phi_u, mul_zero, zero_add, Sz.phi_smul, hphiu', mul_one]
  have hp_idx : ∀ z : ℤ × ℤ, Sz.phi z = t → p (det z u') = z := by
    intro z hz
    have key := eq_smul_add_smul hu' z
    show (det z u') • Sz.u + t • u' = z
    rw [← hz]
    exact key.symm
  have hp_inj : Function.Injective p := by
    intro k1 k2 hk
    have h0 : (k1 - k2) • Sz.u = 0 := by
      have heq : k1 • Sz.u = k2 • Sz.u := add_right_cancel (show k1 • Sz.u + t • u' = k2 • Sz.u + t • u' from hk)
      rw [sub_smul, heq, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · omega
    · exact absurd h Sz.u_primitive.ne_zero
  have hidx_p : ∀ k : ℤ, det (p k) u' = k := fun k => hp_inj (hp_idx (p k) (hphip k))
  set K : Finset ℤ := (B.filter fun z => Sz.phi z = t).image (fun z => det z u') with hK_def
  have hK_ne : K.Nonempty := hne.image _
  have hK_mem_filter : ∀ k ∈ K, p k ∈ B.filter fun z => Sz.phi z = t := by
    intro k hk
    obtain ⟨z0, hz0, hz0eq⟩ := Finset.mem_image.mp hk
    rw [← hz0eq, hp_idx z0 (Finset.mem_filter.mp hz0).2]
    exact hz0
  set k0 : ℤ := K.min' hK_ne with hk0_def
  set k1 : ℤ := K.max' hK_ne with hk1_def
  have hk0K : k0 ∈ K := Finset.min'_mem _ _
  have hk1K : k1 ∈ K := Finset.max'_mem _ _
  have hk0k1 : k0 ≤ k1 := Finset.min'_le K k1 hk1K
  have hpk0B : p k0 ∈ B := (Finset.mem_filter.mp (hK_mem_filter k0 hk0K)).1
  have hpk1B : p k1 ∈ B := (Finset.mem_filter.mp (hK_mem_filter k1 hk1K)).1
  have hK_interval : ∀ k : ℤ, k0 ≤ k → k ≤ k1 → k ∈ K := by
    intro k hka hkb
    rcases eq_or_lt_of_le hk0k1 with heq | hlt
    · have hkeq : k = k0 := by omega
      rw [hkeq]; exact hk0K
    · have hk0R : (k0 : ℝ) < (k1 : ℝ) := by exact_mod_cast hlt
      have hkaR : (k0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hka
      have hkbR : (k : ℝ) ≤ (k1 : ℝ) := by exact_mod_cast hkb
      set a : ℝ := ((k1 : ℝ) - (k : ℝ)) / ((k1 : ℝ) - (k0 : ℝ)) with ha_def
      set b : ℝ := ((k : ℝ) - (k0 : ℝ)) / ((k1 : ℝ) - (k0 : ℝ)) with hb_def
      have hd_pos : (0 : ℝ) < (k1 : ℝ) - (k0 : ℝ) := by linarith
      have ha_nonneg : 0 ≤ a := div_nonneg (by linarith) hd_pos.le
      have hb_nonneg : 0 ≤ b := div_nonneg (by linarith) hd_pos.le
      have hab : a + b = 1 := by
        have hsum : a + b = ((k1 : ℝ) - k + (k - k0)) / ((k1 : ℝ) - k0) := by
          rw [ha_def, hb_def]; ring
        rw [hsum, show (k1 : ℝ) - k + (k - k0) = k1 - k0 from by ring, div_self hd_pos.ne']
      have hconv : Convex ℝ (Conv B) := convex_convexHull ℝ _
      have hmem0 : toReal (p k0) ∈ Conv B := subset_Conv hpk0B
      have hmem1 : toReal (p k1) ∈ Conv B := subset_Conv hpk1B
      have hcomb : a • toReal (p k0) + b • toReal (p k1) ∈ Conv B :=
        hconv hmem0 hmem1 ha_nonneg hb_nonneg hab
      have heqpt : toReal (p k) = a • toReal (p k0) + b • toReal (p k1) := by
        apply Prod.ext
        · show ((p k).1 : ℝ) = a * ((p k0).1 : ℝ) + b * ((p k1).1 : ℝ)
          show (((k • Sz.u + t • u' : ℤ × ℤ)).1 : ℝ)
              = a * (((k0 • Sz.u + t • u' : ℤ × ℤ)).1 : ℝ) + b * (((k1 • Sz.u + t • u' : ℤ × ℤ)).1 : ℝ)
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          push_cast
          rw [ha_def, hb_def]
          field_simp
          ring
        · show ((p k).2 : ℝ) = a * ((p k0).2 : ℝ) + b * ((p k1).2 : ℝ)
          show (((k • Sz.u + t • u' : ℤ × ℤ)).2 : ℝ)
              = a * (((k0 • Sz.u + t • u' : ℤ × ℤ)).2 : ℝ) + b * (((k1 • Sz.u + t • u' : ℤ × ℤ)).2 : ℝ)
          simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          push_cast
          rw [ha_def, hb_def]
          field_simp
          ring
      have hpkB : p k ∈ B := hB (p k) (by rw [heqpt]; exact hcomb)
      have hmemfilter : p k ∈ B.filter fun z => Sz.phi z = t :=
        Finset.mem_filter.mpr ⟨hpkB, hphip k⟩
      rw [← hidx_p k]
      exact Finset.mem_image_of_mem _ hmemfilter
  refine ⟨p k0, (k1 - k0).toNat + 1, Nat.succ_pos _, ?_⟩
  ext z
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · intro hz
    have hzK : det z u' ∈ K := Finset.mem_image_of_mem _ hz
    have hzk0 : k0 ≤ det z u' := Finset.min'_le _ _ hzK
    have hzk1 : det z u' ≤ k1 := Finset.le_max' _ _ hzK
    refine ⟨(det z u' - k0).toNat, ?_, ?_⟩
    · have : (det z u' - k0).toNat < (k1 - k0).toNat + 1 := by omega
      exact this
    · have hcast : ((det z u' - k0).toNat : ℤ) = det z u' - k0 := by omega
      have step : p k0 + ((det z u' - k0).toNat : ℤ) • Sz.u = p (det z u') := by
        rw [hcast]
        show k0 • Sz.u + t • u' + (det z u' - k0) • Sz.u = (det z u') • Sz.u + t • u'
        rw [sub_smul]
        abel
      rw [step]
      exact hp_idx z (Finset.mem_filter.mp hz).2
  · rintro ⟨s, hs, rfl⟩
    have hle : (s : ℤ) ≤ k1 - k0 := by omega
    have hk0s : k0 ≤ k0 + (s : ℤ) := by omega
    have hk1s : k0 + (s : ℤ) ≤ k1 := by omega
    have hmem : k0 + (s : ℤ) ∈ K := hK_interval _ hk0s hk1s
    have := hK_mem_filter _ hmem
    have heq : p k0 + (s : ℤ) • Sz.u = p (k0 + (s : ℤ)) := by
      show p k0 + (s : ℤ) • Sz.u = (k0 + (s : ℤ)) • Sz.u + t • u'
      rw [add_smul]
      show p k0 + (s : ℤ) • Sz.u = k0 • Sz.u + (s : ℤ) • Sz.u + t • u'
      show k0 • Sz.u + t • u' + (s : ℤ) • Sz.u = k0 • Sz.u + (s : ℤ) • Sz.u + t • u'
      abel
    rw [heq]
    exact this

/-- The concavity input of condition (iii) of Lemma D.5: for a lattice-convex `B` whose two
extreme rows have at least `n` points each, every intermediate row has at least `n - 1` points.
This is the concavity of the length of the parallel chords of `Conv(B)`. -/
theorem card_row_ge_of_extreme {B : Finset (ℤ × ℤ)} (hB : LatticeConvex B) {n : ℕ}
    (htop : n ≤ (Sz.Etop B).card) (hbot : n ≤ (Sz.Ebot B).card) {t : ℤ}
    (hlo : Sz.botIdx B ≤ t) (hhi : t ≤ Sz.topIdx B) :
    n ≤ (B.filter fun z => Sz.phi z = t).card + 1 := by
  classical
  by_cases hn1 : n ≤ 1
  · omega
  push Not at hn1
  -- Degenerate case: a single row, `t = topIdx B = botIdx B`.
  by_cases hbt : Sz.botIdx B = Sz.topIdx B
  · have ht_eq : t = Sz.topIdx B := by omega
    have hrw : (B.filter fun z => Sz.phi z = t) = Sz.Etop B := by rw [ht_eq]; rfl
    rw [hrw]; omega
  have hbt_lt : Sz.botIdx B < Sz.topIdx B := lt_of_le_of_ne (by omega) hbt
  -- A unimodular dual `u'` of `u`, giving the second coordinate `idx z = det z u'`.
  obtain ⟨u', hu'⟩ := Sz.u_primitive.exists_dual
  have hphiu' : Sz.phi u' = 1 := hu'
  have hu'eq : Sz.u.1 * u'.2 - Sz.u.2 * u'.1 = 1 := hu'
  -- The extreme rows are non-empty runs of consecutive `u`-translates.
  have hEtop_ne : (Sz.Etop B).Nonempty := Finset.card_pos.mp (by omega)
  have hEbot_ne : (Sz.Ebot B).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨wtop, ntop, hntop_pos, hEtop_eq⟩ := Sz.row_eq_run hB (Sz.topIdx B) hEtop_ne
  obtain ⟨wbot, nbot, hnbot_pos, hEbot_eq⟩ := Sz.row_eq_run hB (Sz.botIdx B) hEbot_ne
  have hinj : ∀ w : ℤ × ℤ, Function.Injective (fun s : ℕ => w + (s : ℤ) • Sz.u) := by
    intro w s1 s2 hs
    have h0 : (s1 : ℤ) • Sz.u = (s2 : ℤ) • Sz.u := add_left_cancel hs
    have hz : ((s1 : ℤ) - (s2 : ℤ)) • Sz.u = 0 := by rw [sub_smul, h0, sub_self]
    rcases smul_eq_zero.mp hz with h | h
    · have : (s1 : ℤ) = (s2 : ℤ) := by omega
      exact_mod_cast this
    · exact absurd h Sz.u_primitive.ne_zero
  have hcard_top : (Sz.Etop B).card = ntop := by
    show (B.filter fun z => Sz.phi z = Sz.topIdx B).card = ntop
    rw [hEtop_eq, Finset.card_image_of_injective _ (hinj wtop), Finset.card_range]
  have hcard_bot : (Sz.Ebot B).card = nbot := by
    show (B.filter fun z => Sz.phi z = Sz.botIdx B).card = nbot
    rw [hEbot_eq, Finset.card_image_of_injective _ (hinj wbot), Finset.card_range]
  have hn_ntop : n ≤ ntop := hcard_top ▸ htop
  have hn_nbot : n ≤ nbot := hcard_bot ▸ hbot
  -- The four extreme points: the leftmost point and the `(n-1)`-th point of each extreme row.
  have hA_mem : wtop ∈ Sz.Etop B := by
    show wtop ∈ B.filter fun z => Sz.phi z = Sz.topIdx B
    rw [hEtop_eq]
    refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hntop_pos, ?_⟩
    simp
  have hA'_mem : wtop + ((n - 1 : ℕ) : ℤ) • Sz.u ∈ Sz.Etop B := by
    show wtop + ((n - 1 : ℕ) : ℤ) • Sz.u ∈ B.filter fun z => Sz.phi z = Sz.topIdx B
    rw [hEtop_eq]
    exact Finset.mem_image.mpr ⟨n - 1, Finset.mem_range.mpr (by omega), rfl⟩
  have hC_mem : wbot ∈ Sz.Ebot B := by
    show wbot ∈ B.filter fun z => Sz.phi z = Sz.botIdx B
    rw [hEbot_eq]
    refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hnbot_pos, ?_⟩
    simp
  have hC'_mem : wbot + ((n - 1 : ℕ) : ℤ) • Sz.u ∈ Sz.Ebot B := by
    show wbot + ((n - 1 : ℕ) : ℤ) • Sz.u ∈ B.filter fun z => Sz.phi z = Sz.botIdx B
    rw [hEbot_eq]
    exact Finset.mem_image.mpr ⟨n - 1, Finset.mem_range.mpr (by omega), rfl⟩
  have hAB : wtop ∈ B := (Finset.mem_filter.mp hA_mem).1
  have hA'B : wtop + ((n - 1 : ℕ) : ℤ) • Sz.u ∈ B := (Finset.mem_filter.mp hA'_mem).1
  have hCB : wbot ∈ B := (Finset.mem_filter.mp hC_mem).1
  have hC'B : wbot + ((n - 1 : ℕ) : ℤ) • Sz.u ∈ B := (Finset.mem_filter.mp hC'_mem).1
  have hAphi : Sz.phi wtop = Sz.topIdx B := (Finset.mem_filter.mp hA_mem).2
  have hCphi : Sz.phi wbot = Sz.botIdx B := (Finset.mem_filter.mp hC_mem).2
  have hA'phi : Sz.phi (wtop + ((n - 1 : ℕ) : ℤ) • Sz.u) = Sz.topIdx B := by
    rw [Sz.phi_add, Sz.phi_smul, Sz.phi_u, mul_zero, add_zero]; exact hAphi
  have hC'phi : Sz.phi (wbot + ((n - 1 : ℕ) : ℤ) • Sz.u) = Sz.botIdx B := by
    rw [Sz.phi_add, Sz.phi_smul, Sz.phi_u, mul_zero, add_zero]; exact hCphi
  -- Real-number bookkeeping: `s` interpolates row `t` between the two extreme rows.
  set T : ℝ := (Sz.topIdx B : ℝ) with hT_def
  set Bo : ℝ := (Sz.botIdx B : ℝ) with hBo_def
  set tt : ℝ := (t : ℝ) with htt_def
  have hTBo : Bo < T := by rw [hT_def, hBo_def]; exact_mod_cast hbt_lt
  have httlo : Bo ≤ tt := by rw [hBo_def, htt_def]; exact_mod_cast hlo
  have htthi : tt ≤ T := by rw [hT_def, htt_def]; exact_mod_cast hhi
  set s : ℝ := (T - tt) / (T - Bo) with hs_def
  have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith)
  have hs1 : s ≤ 1 := by rw [hs_def, div_le_one (by linarith)]; linarith
  have hsTBo : s * (T - Bo) = T - tt := by
    rw [hs_def]
    exact div_mul_cancel₀ (T - tt) (sub_pos.mpr hTBo).ne'
  -- The linear coordinate `idxR x = x.1 u'.2 - x.2 u'.1`, dual to `phiR`.
  set idxR : ℝ × ℝ → ℝ := fun x => x.1 * (u'.2 : ℝ) - x.2 * (u'.1 : ℝ) with hidxR_def
  have hidxR_add : ∀ x y : ℝ × ℝ, idxR (x + y) = idxR x + idxR y := by
    intro x y; show (x + y).1 * (u'.2 : ℝ) - (x + y).2 * (u'.1 : ℝ) = _
    simp only [Prod.fst_add, Prod.snd_add]; rw [hidxR_def]; ring
  have hidxR_smul : ∀ (c : ℝ) (x : ℝ × ℝ), idxR (c • x) = c * idxR x := by
    intro c x; show (c • x).1 * (u'.2 : ℝ) - (c • x).2 * (u'.1 : ℝ) = _
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; rw [hidxR_def]; ring
  have hidxR_toReal : ∀ z : ℤ × ℤ, idxR (toReal z) = ((det z u' : ℤ) : ℝ) := by
    intro z
    show (toReal z).1 * (u'.2 : ℝ) - (toReal z).2 * (u'.1 : ℝ) = ((det z u' : ℤ) : ℝ)
    show ((z.1 : ℝ)) * (u'.2 : ℝ) - ((z.2 : ℝ)) * (u'.1 : ℝ) = ((det z u' : ℤ) : ℝ)
    simp only [det]; push_cast; ring
  -- Real decomposition: every real point recovers its `(u, u')`-coordinates.
  have hu'R : (Sz.u.1 : ℝ) * (u'.2 : ℝ) - (Sz.u.2 : ℝ) * (u'.1 : ℝ) = 1 := by exact_mod_cast hu'eq
  have hdecomp : ∀ x : ℝ × ℝ, x = idxR x • toReal Sz.u + Sz.phiR x • toReal u' := by
    intro x
    have e1 : idxR x = x.1 * (u'.2 : ℝ) - x.2 * (u'.1 : ℝ) := by rw [hidxR_def]
    have e2 : Sz.phiR x = (Sz.u.1 : ℝ) * x.2 - (Sz.u.2 : ℝ) * x.1 := rfl
    apply Prod.ext
    · show x.1 = idxR x * (Sz.u.1 : ℝ) + Sz.phiR x * (u'.1 : ℝ)
      rw [e1, e2]
      linear_combination (-x.1) * hu'R
    · show x.2 = idxR x * (Sz.u.2 : ℝ) + Sz.phiR x * (u'.2 : ℝ)
      rw [e1, e2]
      linear_combination (-x.2) * hu'R
  -- The two segment endpoints `P, Q` at row `t`, forced there by the choice of `s`.
  set P : ℝ × ℝ := (1 - s) • toReal wtop + s • toReal wbot with hP_def
  set Q : ℝ × ℝ := (1 - s) • toReal (wtop + ((n - 1 : ℕ) : ℤ) • Sz.u)
      + s • toReal (wbot + ((n - 1 : ℕ) : ℤ) • Sz.u) with hQ_def
  have hPconv : P ∈ Conv B :=
    (convex_convexHull ℝ _) (subset_Conv hAB) (subset_Conv hCB) (by linarith) hs0 (by ring)
  have hQconv : Q ∈ Conv B :=
    (convex_convexHull ℝ _) (subset_Conv hA'B) (subset_Conv hC'B) (by linarith) hs0 (by ring)
  have hphiRP : Sz.phiR P = tt := by
    show Sz.phiR ((1 - s) • toReal wtop + s • toReal wbot) = tt
    rw [Sz.isLinearMap_phiR.map_add, Sz.isLinearMap_phiR.map_smul, Sz.isLinearMap_phiR.map_smul,
      Sz.phiR_toReal, Sz.phiR_toReal, hAphi, hCphi, ← hT_def, ← hBo_def]
    simp only [smul_eq_mul]
    have : (1 - s) * T + s * Bo = T - s * (T - Bo) := by ring
    rw [this, hsTBo]; ring
  have hphiRQ : Sz.phiR Q = tt := by
    show Sz.phiR ((1 - s) • toReal (wtop + ((n - 1 : ℕ) : ℤ) • Sz.u)
        + s • toReal (wbot + ((n - 1 : ℕ) : ℤ) • Sz.u)) = tt
    rw [Sz.isLinearMap_phiR.map_add, Sz.isLinearMap_phiR.map_smul, Sz.isLinearMap_phiR.map_smul,
      Sz.phiR_toReal, Sz.phiR_toReal, hA'phi, hC'phi, ← hT_def, ← hBo_def]
    simp only [smul_eq_mul]
    have : (1 - s) * T + s * Bo = T - s * (T - Bo) := by ring
    rw [this, hsTBo]; ring
  set cval : ℝ := idxR P with hcval_def
  have hidxRQ : idxR Q = cval + ((n - 1 : ℕ) : ℝ) := by
    rw [hcval_def, hP_def, hQ_def, hidxR_add, hidxR_add, hidxR_smul, hidxR_smul, hidxR_smul,
      hidxR_smul, hidxR_toReal, hidxR_toReal, hidxR_toReal, hidxR_toReal]
    have hdA' : det (wtop + ((n - 1 : ℕ) : ℤ) • Sz.u) u' = det wtop u' + ((n - 1 : ℕ) : ℤ) := by
      show (wtop + ((n - 1 : ℕ) : ℤ) • Sz.u).1 * u'.2 - (wtop + ((n - 1 : ℕ) : ℤ) • Sz.u).2 * u'.1
          = (wtop.1 * u'.2 - wtop.2 * u'.1) + ((n - 1 : ℕ) : ℤ)
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      linear_combination ((n - 1 : ℕ) : ℤ) * hu'eq
    have hdC' : det (wbot + ((n - 1 : ℕ) : ℤ) • Sz.u) u' = det wbot u' + ((n - 1 : ℕ) : ℤ) := by
      show (wbot + ((n - 1 : ℕ) : ℤ) • Sz.u).1 * u'.2 - (wbot + ((n - 1 : ℕ) : ℤ) • Sz.u).2 * u'.1
          = (wbot.1 * u'.2 - wbot.2 * u'.1) + ((n - 1 : ℕ) : ℤ)
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      linear_combination ((n - 1 : ℕ) : ℤ) * hu'eq
    rw [hdA', hdC']
    push_cast
    ring
  -- For each `0 ≤ j < n - 1`, an explicit lattice point on the segment `PQ` at height `t`.
  have hinj2 : ∀ k0 : ℤ, Function.Injective (fun j : ℕ => (k0 + (j : ℤ)) • Sz.u + t • u') := by
    intro k0 j1 j2 hj
    have h0 : (k0 + (j1 : ℤ)) • Sz.u = (k0 + (j2 : ℤ)) • Sz.u := add_right_cancel hj
    have hz : ((j1 : ℤ) - (j2 : ℤ)) • Sz.u = 0 := by
      have heq : (k0 + (j1 : ℤ)) - (k0 + (j2 : ℤ)) = (j1 : ℤ) - (j2 : ℤ) := by ring
      rw [← heq, sub_smul, h0, sub_self]
    rcases smul_eq_zero.mp hz with h | h
    · have : (j1 : ℤ) = (j2 : ℤ) := by omega
      exact_mod_cast this
    · exact absurd h Sz.u_primitive.ne_zero
  have hdet_gen : ∀ k0 j : ℤ, det ((k0 + j) • Sz.u + t • u') u' = k0 + j := by
    intro k0 j
    show ((k0 + j) • Sz.u + t • u').1 * u'.2 - ((k0 + j) • Sz.u + t • u').2 * u'.1 = k0 + j
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (k0 + j) * hu'eq
  have hphi_gen : ∀ k0 j : ℤ, Sz.phi ((k0 + j) • Sz.u + t • u') = t := by
    intro k0 j
    rw [Sz.phi_add, Sz.phi_smul, Sz.phi_u, mul_zero, zero_add, Sz.phi_smul, hphiu', mul_one]
  have hmR_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    have : 0 < n - 1 := by omega
    exact_mod_cast this
  have hZ_sub : (Finset.range (n - 1)).image (fun j : ℕ => (⌈cval⌉ + (j : ℤ)) • Sz.u + t • u')
      ⊆ B.filter fun z => Sz.phi z = t := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_range] at hj
    set kj : ℤ := ⌈cval⌉ + (j : ℤ) with hkj_def
    have hkj_lo : cval ≤ (kj : ℝ) := by
      rw [hkj_def]; push_cast
      have h1 := Int.le_ceil cval
      have h2 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      linarith
    have hkj_hi : (kj : ℝ) ≤ cval + ((n - 1 : ℕ) : ℝ) := by
      rw [hkj_def]; push_cast
      have h1 := Int.ceil_lt_add_one cval
      have h2 : (j : ℝ) ≤ ((n - 1 : ℕ) : ℝ) - 1 := by
        have hnat : j + 1 ≤ n - 1 := by omega
        have h3 : ((j + 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
        push_cast at h3
        linarith
      linarith
    set rj : ℝ := ((kj : ℝ) - cval) / ((n - 1 : ℕ) : ℝ) with hrj_def
    have hrj0 : 0 ≤ rj := div_nonneg (by linarith) hmR_pos.le
    have hrj1 : rj ≤ 1 := by rw [hrj_def, div_le_one hmR_pos]; linarith
    have hzreal : (1 - rj) • P + rj • Q ∈ Conv B :=
      (convex_convexHull ℝ _) hPconv hQconv (by linarith) hrj0 (by ring)
    have hidxR_zreal : idxR ((1 - rj) • P + rj • Q) = (kj : ℝ) := by
      rw [hidxR_add, hidxR_smul, hidxR_smul, ← hcval_def, hidxRQ, hrj_def]
      field_simp
      ring
    have hphiR_zreal : Sz.phiR ((1 - rj) • P + rj • Q) = tt := by
      rw [Sz.isLinearMap_phiR.map_add, Sz.isLinearMap_phiR.map_smul, Sz.isLinearMap_phiR.map_smul,
        hphiRP, hphiRQ]
      ring
    have heq : toReal ((kj • Sz.u + t • u' : ℤ × ℤ)) = (1 - rj) • P + rj • Q := by
      have h1 := hdecomp (toReal ((kj • Sz.u + t • u' : ℤ × ℤ)))
      have h2 := hdecomp ((1 - rj) • P + rj • Q)
      rw [hidxR_toReal] at h1
      have hdetkj : det (kj • Sz.u + t • u') u' = kj := by
        have := hdet_gen ⌈cval⌉ (j : ℤ)
        rwa [← hkj_def] at this
      rw [hdetkj] at h1
      have hphikj : Sz.phi (kj • Sz.u + t • u' : ℤ × ℤ) = t := by
        have := hphi_gen ⌈cval⌉ (j : ℤ)
        rwa [← hkj_def] at this
      rw [Sz.phiR_toReal, hphikj] at h1
      rw [hidxR_zreal, hphiR_zreal] at h2
      rw [h1, h2]
    have hzmem : (kj • Sz.u + t • u' : ℤ × ℤ) ∈ B := hB _ (by rw [heq]; exact hzreal)
    have hzphi : Sz.phi (kj • Sz.u + t • u' : ℤ × ℤ) = t := by
      have := hphi_gen ⌈cval⌉ (j : ℤ)
      rwa [← hkj_def] at this
    rw [show (⌈cval⌉ + (j : ℤ)) • Sz.u + t • u' = kj • Sz.u + t • u' from by rw [hkj_def]]
    exact Finset.mem_filter.mpr ⟨hzmem, hzphi⟩
  have hZ_card : ((Finset.range (n - 1)).image
      (fun j : ℕ => (⌈cval⌉ + (j : ℤ)) • Sz.u + t • u')).card = n - 1 := by
    rw [Finset.card_image_of_injective _ (hinj2 ⌈cval⌉), Finset.card_range]
  have := Finset.card_le_card hZ_sub
  rw [hZ_card] at this
  omega

/-- **Lemma D.5 (Existence).**  If `S` is non-empty, finite and lattice-convex with
`P_ξ(S) ≤ |S|`, then there are a sign `ε` and an `ε`-balanced `B ⊆ S`.

The construction deletes, at each step, whichever of the two extreme rows is the shorter; with
`f(i) = P_ξ(D_i) - |D_i|` one has `f(0) ≤ 0` and `f(K) = 1`, so some step crosses zero. -/
theorem exists_balanced [Fact p.Prime] {S : Finset (ℤ × ℤ)} (hne : S.Nonempty)
    (hS : LatticeConvex S) (hP : P Sz.xi S ≤ S.card) :
    ∃ (ε : Bool) (B : Finset (ℤ × ℤ)), B ⊆ S ∧ Sz.Balanced ε B := by
  classical
  -- Strong induction on the cardinality: repeatedly delete the shorter of the two extreme
  -- rows, stopping at the first set for which the deficit condition (ii) already holds.
  have aux : ∀ n : ℕ, ∀ B : Finset (ℤ × ℤ), B.card ≤ n → B.Nonempty → LatticeConvex B →
      P Sz.xi B ≤ B.card → ∃ (ε : Bool) (D : Finset (ℤ × ℤ)), D ⊆ B ∧ Sz.Balanced ε D := by
    intro n
    induction n with
    | zero =>
      intro B hcard hne _ _
      exact absurd (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)) hne.ne_empty
    | succ n ih =>
      intro B hcard hne hconv hP
      -- Choose the sign making `E^ε(B)` the (weakly) smaller extreme row.
      by_cases hle : (Sz.Etop B).card ≤ (Sz.Ebot B).card
      · -- `ε = true`, `E = E⁺(B)`.
        set E : Finset (ℤ × ℤ) := Sz.Eside true B with hE_def
        have hEeq : E = Sz.Etop B := by simp [hE_def, Eside]
        have hOeq : Sz.Eside false B = Sz.Ebot B := by simp [Eside]
        have hEsub : E ⊆ B := Sz.Eside_subset true B
        have hEcard_le : E.card ≤ (Sz.Eside false B).card := by rw [hEeq, hOeq]; exact hle
        set D' : Finset (ℤ × ℤ) := B \ E with hD'_def
        have hunion : D'.card + E.card = B.card := by
          rw [hD'_def]; exact Finset.card_sdiff_add_card_eq_card hEsub
        by_cases hdef : P Sz.xi B < P Sz.xi D' + E.card
        · -- `B` itself is `true`-balanced.
          refine ⟨true, B, subset_rfl, hne, hconv, hP, ?_, ?_⟩
          · exact hdef
          · intro t ht1 ht2
            have hntop : E.card ≤ (Sz.Etop B).card := by rw [hEeq]
            have hnbot : E.card ≤ (Sz.Ebot B).card := by rw [← hOeq]; exact hEcard_le
            exact Sz.card_row_ge_of_extreme hconv hntop hnbot ht1 ht2
        · push Not at hdef
          have hD'card_lt : D'.card < B.card := by
            have hEpos : 0 < E.card := Finset.card_pos.mpr (Sz.Eside_nonempty hne)
            omega
          have hD'card_le : D'.card ≤ n := by omega
          have hPD' : P Sz.xi D' ≤ D'.card := by omega
          have hD'ne : D'.Nonempty := by
            rcases D'.eq_empty_or_nonempty with h0 | h0
            · exfalso
              rw [h0, P_empty] at hPD'
              simp at hPD'
            · exact h0
          have hD'conv : LatticeConvex D' := by
            have := Sz.latticeConvex_sdiff_Eside hconv true
            rwa [← hE_def] at this
          obtain ⟨ε, D, hDsub, hbal⟩ := ih D' hD'card_le hD'ne hD'conv hPD'
          exact ⟨ε, D, hDsub.trans (hD'_def ▸ Finset.sdiff_subset), hbal⟩
      · push Not at hle
        -- `ε = false`, `E = E⁻(B)`.
        set E : Finset (ℤ × ℤ) := Sz.Eside false B with hE_def
        have hEeq : E = Sz.Ebot B := by simp [hE_def, Eside]
        have hOeq : Sz.Eside true B = Sz.Etop B := by simp [Eside]
        have hEsub : E ⊆ B := Sz.Eside_subset false B
        have hEcard_le : E.card ≤ (Sz.Eside true B).card := by rw [hEeq, hOeq]; exact hle.le
        set D' : Finset (ℤ × ℤ) := B \ E with hD'_def
        have hunion : D'.card + E.card = B.card := by
          rw [hD'_def]; exact Finset.card_sdiff_add_card_eq_card hEsub
        by_cases hdef : P Sz.xi B < P Sz.xi D' + E.card
        · -- `B` itself is `false`-balanced.
          refine ⟨false, B, subset_rfl, hne, hconv, hP, ?_, ?_⟩
          · exact hdef
          · intro t ht1 ht2
            have hnbot : E.card ≤ (Sz.Ebot B).card := by rw [hEeq]
            have hntop : E.card ≤ (Sz.Etop B).card := by rw [← hOeq]; exact hEcard_le
            exact Sz.card_row_ge_of_extreme hconv hntop hnbot ht1 ht2
        · push Not at hdef
          have hD'card_lt : D'.card < B.card := by
            have hEpos : 0 < E.card := Finset.card_pos.mpr (Sz.Eside_nonempty hne)
            omega
          have hD'card_le : D'.card ≤ n := by omega
          have hPD' : P Sz.xi D' ≤ D'.card := by omega
          have hD'ne : D'.Nonempty := by
            rcases D'.eq_empty_or_nonempty with h0 | h0
            · exfalso
              rw [h0, P_empty] at hPD'
              simp at hPD'
            · exact h0
          have hD'conv : LatticeConvex D' := by
            have := Sz.latticeConvex_sdiff_Eside hconv false
            rwa [← hE_def] at this
          obtain ⟨ε, D, hDsub, hbal⟩ := ih D' hD'card_le hD'ne hD'conv hPD'
          exact ⟨ε, D, hDsub.trans (hD'_def ▸ Finset.sdiff_subset), hbal⟩
  obtain ⟨ε, B, hBsub, hbal⟩ := aux S.card S le_rfl hne hS hP
  exact ⟨ε, B, hBsub, hbal⟩

/-- Two points of the same row differ by an integer multiple of `u`: the fibres of `φ` are exactly
the cosets of `ℤu`. -/
theorem exists_zsmul_of_phi_eq {z w : ℤ × ℤ} (h : Sz.phi z = Sz.phi w) :
    ∃ s : ℤ, z = w + s • Sz.u := by
  obtain ⟨u', hu'⟩ := Sz.u_primitive.exists_dual
  have hz : z = (det z u') • Sz.u + Sz.phi z • u' := by
    show z = (det z u') • Sz.u + (det Sz.u z) • u'
    exact eq_smul_add_smul hu' z
  have hw : w = (det w u') • Sz.u + Sz.phi w • u' := by
    show w = (det w u') • Sz.u + (det Sz.u w) • u'
    exact eq_smul_add_smul hu' w
  refine ⟨det z u' - det w u', ?_⟩
  nth_rewrite 1 [hz]
  nth_rewrite 1 [hw]
  rw [h]
  module

/-! ### §D.4 Ambiguity strips and the propagation lemma -/

/-- **Definition D.6.**  `ξ` has the `+`-ambiguity strip `St[a, b]`, `a ≤ b`, if some `x` in the
orbit closure agrees with `ξ` on `St[a, b-1]` — an empty condition when `a = b` — and differs
from `ξ` at some point of `L_b`.

The `-`-ambiguity strips are `Sz.neg.AmbiguityStrip`, `u` being replaced by `-u`. -/
def AmbiguityStrip (a b : ℤ) : Prop :=
  a ≤ b ∧ ∃ x ∈ orbitClosure Sz.xi,
    (∀ v ∈ Sz.strip a (b - 1), x v = Sz.xi v) ∧ ∃ v ∈ Sz.row b, x v ≠ Sz.xi v

/-- Steps (2)–(3) of Lemma D.7: the two determination rules.  Condition (ii) of Definition D.4
forces an index `k < n` at which the restriction `Pat(D_{k+1}, ξ) → Pat(D_k, ξ)` is a bijection,
so that for every `y` in the orbit closure and every `v` the value `y(e_{k+1} + v)` is determined
by `y` on `D_k + v`.

The core of `exists_forward_rule_aux`, generalised to an arbitrary non-zero direction `d`
along which `E` is a run `w, w + d, …, w + (m-1)d`.  Taking `d = u` recovers rule `(R_+)` of
Lemma D.7; taking `d = -u` and `w` the *other* endpoint of the run recovers rule `(R_-)`
(`exists_backward_rule_aux`). -/
private theorem injective_add_zsmul {w d : ℤ × ℤ} (hd : d ≠ 0) :
    Function.Injective (fun s : ℕ => w + (s : ℤ) • d) := by
  intro s1 s2 hs
  have h0 : (s1 : ℤ) • d = (s2 : ℤ) • d := add_left_cancel hs
  have hz : ((s1 : ℤ) - (s2 : ℤ)) • d = 0 := by rw [sub_smul, h0, sub_self]
  rcases smul_eq_zero.mp hz with h | h
  · have : (s1 : ℤ) = (s2 : ℤ) := by omega
    exact_mod_cast this
  · exact absurd h hd

private theorem exists_forward_rule_aux_dir [Fact p.Prime] {B : Finset (ℤ × ℤ)}
    {E : Finset (ℤ × ℤ)} (hEsub : E ⊆ B) (_hEne : E.Nonempty)
    (hdeficit : P Sz.xi B < P Sz.xi (B \ E) + E.card)
    {w d : ℤ × ℤ} (hd : d ≠ 0) {m : ℕ}
    (hEeq : E = (Finset.range m).image (fun s : ℕ => w + (s : ℤ) • d)) :
    ∃ (k : ℕ) (C : Finset (ℤ × ℤ)) (e : ℤ × ℤ), k < m ∧
      C = (B \ E) ∪ (Finset.range k).image (fun s : ℕ => w + (s : ℤ) • d) ∧
      e = w + (k : ℤ) • d ∧ C ⊆ B ∧ e ∈ E ∧
      ∀ (y : Config (ZMod p)) (_ : y ∈ orbitClosure Sz.xi)
        (y' : Config (ZMod p)) (_ : y' ∈ orbitClosure Sz.xi) (v w : ℤ × ℤ),
        (∀ c ∈ C, y (v + c) = y' (w + c)) → y (v + e) = y' (w + e) := by
  classical
  set B0 : Finset (ℤ × ℤ) := B \ E with hB0_def
  have hinj : Function.Injective (fun s : ℕ => w + (s : ℤ) • d) := by
    intro s1 s2 hs
    have h0 : (s1 : ℤ) • d = (s2 : ℤ) • d := add_left_cancel hs
    have hz : ((s1 : ℤ) - (s2 : ℤ)) • d = 0 := by rw [sub_smul, h0, sub_self]
    rcases smul_eq_zero.mp hz with h | h
    · have : (s1 : ℤ) = (s2 : ℤ) := by omega
      exact_mod_cast this
    · exact absurd h hd
  have hpart_sub : ∀ i ≤ m, (Finset.range i).image (fun s : ℕ => w + (s : ℤ) • d) ⊆ E := by
    intro i hi
    rw [hEeq]
    exact Finset.image_subset_image (Finset.range_subset_range.mpr hi)
  have hpart_card : ∀ i, ((Finset.range i).image (fun s : ℕ => w + (s : ℤ) • d)).card = i := by
    intro i
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hB0_disj : Disjoint B0 E := by rw [hB0_def]; exact Finset.sdiff_disjoint
  have union_insert_eq : ∀ (s t' : Finset (ℤ × ℤ)) (a : ℤ × ℤ),
      s ∪ insert a t' = insert a (s ∪ t') := by
    intro s t' a; ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
  -- The partial runs `D i := B0 ∪ {first i points of E}`.
  set D : ℕ → Finset (ℤ × ℤ) :=
    fun i => B0 ∪ (Finset.range i).image (fun s : ℕ => w + (s : ℤ) • d) with hD_def
  have hD0 : D 0 = B0 := by simp [hD_def]
  have hDm : D m = B := by
    show B0 ∪ (Finset.range m).image (fun s : ℕ => w + (s : ℤ) • d) = B
    rw [← hEeq, hB0_def, Finset.sdiff_union_of_subset hEsub]
  have hDmono : ∀ i j, i ≤ j → D i ⊆ D j := by
    intro i j hij
    show B0 ∪ (Finset.range i).image (fun s : ℕ => w + (s : ℤ) • d)
        ⊆ B0 ∪ (Finset.range j).image (fun s : ℕ => w + (s : ℤ) • d)
    exact Finset.union_subset_union_right (Finset.image_subset_image (Finset.range_subset_range.mpr hij))
  -- `f(i) = P(D i) - |D i|`, as an integer.
  set f : ℕ → ℤ := fun i => (P Sz.xi (D i) : ℤ) - (D i).card with hf_def
  have hf0 : f 0 = (P Sz.xi B0 : ℤ) - B0.card := by rw [hf_def]; simp [hD0]
  have hfm : f m = (P Sz.xi B : ℤ) - B.card := by rw [hf_def]; simp [hDm]
  have hdecrease : f m < f 0 := by
    rw [hfm, hf0]
    have hBcard : B.card = B0.card + E.card := by
      rw [hB0_def]
      have h1 := Finset.card_sdiff_add_card_eq_card hEsub
      omega
    have hPB_int : (P Sz.xi B : ℤ) < (P Sz.xi B0 : ℤ) + E.card := by exact_mod_cast hdeficit
    rw [hBcard]
    push_cast
    linarith
  -- Pigeonhole: some step strictly decreases `f`.
  have hex : ∃ k, k < m ∧ f (k + 1) < f k := by
    by_contra hcon
    push Not at hcon
    have hmono : ∀ i, i ≤ m → f 0 ≤ f i := by
      intro i
      induction i with
      | zero => intro _; exact le_refl _
      | succ i ihi => intro hi1; exact le_trans (ihi (by omega)) (hcon i (by omega))
    exact absurd (hmono m le_rfl) (not_le.mpr hdecrease)
  obtain ⟨k, hkm, hfk⟩ := hex
  set C : Finset (ℤ × ℤ) := D k with hC_def
  set e : ℤ × ℤ := w + (k : ℤ) • d with he_def
  have hCsub : C ⊆ B := (hDmono k m (by omega)).trans (by rw [hDm])
  have heE : e ∈ E := by
    rw [hEeq]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hkm, rfl⟩
  -- `D (k+1) = insert e C`.
  have hDk1 : D (k + 1) = insert e C := by
    show B0 ∪ (Finset.range (k + 1)).image (fun s : ℕ => w + (s : ℤ) • d) = insert e C
    rw [Finset.range_add_one, Finset.image_insert, union_insert_eq]
  have heC : e ∉ C := by
    rw [hC_def, hD_def, Finset.mem_union, Finset.mem_image]
    push Not
    refine ⟨fun hcon => absurd heE (Finset.disjoint_left.mp hB0_disj hcon), ?_⟩
    rintro s hs heq
    rw [Finset.mem_range] at hs
    rw [he_def] at heq
    have := hinj heq
    omega
  have hCsubDk1 : C ⊆ D (k + 1) := by rw [hDk1]; exact Finset.subset_insert e C
  have heDk1 : e ∈ D (k + 1) := by rw [hDk1]; exact Finset.mem_insert_self e C
  -- Cardinalities: `P(D(k+1)) = P(C)`.
  have hcardDk1 : (D (k + 1)).card = C.card + 1 := by
    rw [hDk1, Finset.card_insert_of_notMem heC]
  have hPmono : P Sz.xi C ≤ P Sz.xi (D (k + 1)) := P_mono hCsubDk1
  have hPeq : P Sz.xi C = P Sz.xi (D (k + 1)) := by
    have h1 : f (k + 1) = (P Sz.xi (D (k + 1)) : ℤ) - ((D (k + 1)).card : ℤ) := by rw [hf_def]
    have h2 : f k = (P Sz.xi C : ℤ) - (C.card : ℤ) := by rw [hf_def, hC_def]
    rw [h1, h2] at hfk
    rw [hcardDk1] at hfk
    push_cast at hfk
    omega
  -- The restriction map `Pat(D(k+1), ξ) → Pat(C, ξ)` is a bijection onto its image.
  set r : (D (k + 1) → ZMod p) → (C → ZMod p) := fun g q => g ⟨(q : ℤ × ℤ), hCsubDk1 q.2⟩ with hr_def
  have himg : patterns Sz.xi C = r '' patterns Sz.xi (D (k + 1)) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨pattern Sz.xi (D (k + 1)) u, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨g, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
  have hInj : Set.InjOn r (patterns Sz.xi (D (k + 1))) := by
    apply Set.injOn_of_ncard_image_eq (hs := patterns_finite Sz.xi (D (k + 1)))
    rw [← himg]
    exact hPeq
  -- The pure determination fact for `ξ` itself.
  have hdet : ∀ u u' : ℤ × ℤ, (∀ c ∈ C, Sz.xi (u + c) = Sz.xi (u' + c)) →
      Sz.xi (u + e) = Sz.xi (u' + e) := by
    intro u u' huu'
    have hp1 : pattern Sz.xi (D (k + 1)) u ∈ patterns Sz.xi (D (k + 1)) := ⟨u, rfl⟩
    have hp2 : pattern Sz.xi (D (k + 1)) u' ∈ patterns Sz.xi (D (k + 1)) := ⟨u', rfl⟩
    have hreq : r (pattern Sz.xi (D (k + 1)) u) = r (pattern Sz.xi (D (k + 1)) u') := by
      funext q
      show Sz.xi (u + (q : ℤ × ℤ)) = Sz.xi (u' + (q : ℤ × ℤ))
      exact huu' q q.2
    have heqpat := hInj hp1 hp2 hreq
    have hval := congrFun heqpat ⟨e, heDk1⟩
    simpa [pattern] using hval
  -- Lift the determination fact to any two elements of the orbit closure.
  refine ⟨k, C, e, hkm, by rw [hC_def, hB0_def], he_def, hCsub, heE, ?_⟩
  intro y hy y' hy' v vv huu'
  obtain ⟨z', hz'⟩ := exists_pattern_eq_of_mem_orbitClosure hy (D (k + 1)) v
  obtain ⟨z'', hz''⟩ := exists_pattern_eq_of_mem_orbitClosure hy' (D (k + 1)) vv
  have hzc : ∀ c ∈ C, y (v + c) = Sz.xi (z' + c) := by
    intro c hc
    exact congrFun hz' ⟨c, hCsubDk1 hc⟩
  have hzc' : ∀ c ∈ C, y' (vv + c) = Sz.xi (z'' + c) := by
    intro c hc
    exact congrFun hz'' ⟨c, hCsubDk1 hc⟩
  have hze : y (v + e) = Sz.xi (z' + e) := congrFun hz' ⟨e, heDk1⟩
  have hze' : y' (vv + e) = Sz.xi (z'' + e) := congrFun hz'' ⟨e, heDk1⟩
  have hmatch : ∀ c ∈ C, Sz.xi (z' + c) = Sz.xi (z'' + c) := by
    intro c hc
    rw [← hzc c hc, ← hzc' c hc]
    exact huu' c hc
  rw [hze, hze']
  exact hdet z' z'' hmatch

/-- Rule `(R_+)` of Lemma D.7, with the row enumeration `w, w+u, …, w+(m-1)u` and the pigeonhole
index `k` exposed (needed for the index bookkeeping in step (3) of `isPeriodic_of_ambiguityStrip`). -/
private theorem exists_forward_rule_aux [Fact p.Prime] {B : Finset (ℤ × ℤ)} {t : ℤ}
    (hBconv : LatticeConvex B) {E : Finset (ℤ × ℤ)}
    (hE_eq : E = B.filter fun z => Sz.phi z = t) (hEne : E.Nonempty)
    (hdeficit : P Sz.xi B < P Sz.xi (B \ E) + E.card) :
    ∃ (w : ℤ × ℤ) (m k : ℕ), 0 < m ∧ k < m ∧
      E = (Finset.range m).image (fun s : ℕ => w + (s : ℤ) • Sz.u) ∧
      (B \ E) ∪ (Finset.range k).image (fun s : ℕ => w + (s : ℤ) • Sz.u) ⊆ B ∧
      w + (k : ℤ) • Sz.u ∈ E ∧
      ∀ (y : Config (ZMod p)) (_ : y ∈ orbitClosure Sz.xi)
        (y' : Config (ZMod p)) (_ : y' ∈ orbitClosure Sz.xi) (v w' : ℤ × ℤ),
        (∀ c ∈ (B \ E) ∪ (Finset.range k).image (fun s : ℕ => w + (s : ℤ) • Sz.u),
          y (v + c) = y' (w' + c)) →
        y (v + (w + (k : ℤ) • Sz.u)) = y' (w' + (w + (k : ℤ) • Sz.u)) := by
  have hEsub : E ⊆ B := hE_eq ▸ Finset.filter_subset _ _
  obtain ⟨w, m, hmpos, hEeq⟩ := Sz.row_eq_run hBconv t (hE_eq ▸ hEne)
  rw [← hE_eq] at hEeq
  obtain ⟨k, C, e, hkm, hCeq, heeq, hCsub, heE, hdet⟩ :=
    Sz.exists_forward_rule_aux_dir hEsub hEne hdeficit Sz.u_primitive.ne_zero hEeq
  refine ⟨w, m, k, hmpos, hkm, hEeq, ?_, ?_, ?_⟩
  · rw [← hCeq]; exact hCsub
  · rw [← heeq]; exact heE
  · rw [← hCeq, ← heeq]; exact hdet

/-- Rule `(R_-)` of Lemma D.7, the same run `E` traversed backwards from its other endpoint
`w' = w + (m-1)u`, with the pigeonhole index `k'` exposed. -/
private theorem exists_backward_rule_aux [Fact p.Prime] {B : Finset (ℤ × ℤ)} {t : ℤ}
    (hBconv : LatticeConvex B) {E : Finset (ℤ × ℤ)}
    (hE_eq : E = B.filter fun z => Sz.phi z = t) (hEne : E.Nonempty)
    (hdeficit : P Sz.xi B < P Sz.xi (B \ E) + E.card) :
    ∃ (w' : ℤ × ℤ) (m k : ℕ), 0 < m ∧ k < m ∧
      E = (Finset.range m).image (fun s : ℕ => w' + (s : ℤ) • (-Sz.u)) ∧
      (B \ E) ∪ (Finset.range k).image (fun s : ℕ => w' + (s : ℤ) • (-Sz.u)) ⊆ B ∧
      w' + (k : ℤ) • (-Sz.u) ∈ E ∧
      ∀ (y : Config (ZMod p)) (_ : y ∈ orbitClosure Sz.xi)
        (y' : Config (ZMod p)) (_ : y' ∈ orbitClosure Sz.xi) (v w'' : ℤ × ℤ),
        (∀ c ∈ (B \ E) ∪ (Finset.range k).image (fun s : ℕ => w' + (s : ℤ) • (-Sz.u)),
          y (v + c) = y' (w'' + c)) →
        y (v + (w' + (k : ℤ) • (-Sz.u))) = y' (w'' + (w' + (k : ℤ) • (-Sz.u))) := by
  have hEsub : E ⊆ B := hE_eq ▸ Finset.filter_subset _ _
  obtain ⟨w, m, hmpos, hEeq⟩ := Sz.row_eq_run hBconv t (hE_eq ▸ hEne)
  rw [← hE_eq] at hEeq
  set w' : ℤ × ℤ := w + ((m : ℤ) - 1) • Sz.u with hw'_def
  have hEeq' : E = (Finset.range m).image (fun s : ℕ => w' + (s : ℤ) • (-Sz.u)) := by
    rw [hEeq]
    ext z
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨m - 1 - s, by omega, ?_⟩
      have hcast : ((m - 1 - s : ℕ) : ℤ) = (m : ℤ) - 1 - (s : ℤ) := by omega
      rw [hw'_def, hcast]
      module
    · rintro ⟨s, hs, rfl⟩
      refine ⟨m - 1 - s, by omega, ?_⟩
      have hcast : ((m - 1 - s : ℕ) : ℤ) = (m : ℤ) - 1 - (s : ℤ) := by omega
      rw [hw'_def, hcast]
      module
  obtain ⟨k, C, e, hkm, hCeq, heeq, hCsub, heE, hdet⟩ :=
    Sz.exists_forward_rule_aux_dir hEsub hEne hdeficit (neg_ne_zero.mpr Sz.u_primitive.ne_zero) hEeq'
  refine ⟨w', m, k, hmpos, hkm, hEeq', ?_, ?_, ?_⟩
  · rw [← hCeq]; exact hCsub
  · rw [← heeq]; exact heE
  · rw [← hCeq, ← heeq]; exact hdet

theorem exists_forward_rule [Fact p.Prime] {ε : Bool} {B : Finset (ℤ × ℤ)}
    (hB : Sz.Balanced ε B) :
    ∃ (C : Finset (ℤ × ℤ)) (e : ℤ × ℤ), C ⊆ B ∧ e ∈ Sz.Eside ε B ∧
      ∀ (y : Config (ZMod p)) (_ : y ∈ orbitClosure Sz.xi)
        (y' : Config (ZMod p)) (_ : y' ∈ orbitClosure Sz.xi) (v w : ℤ × ℤ),
        (∀ c ∈ C, y (v + c) = y' (w + c)) → y (v + e) = y' (w + e) := by
  cases ε
  · have hEeq : Sz.Eside false B = B.filter fun z => Sz.phi z = Sz.botIdx B := by
      simp [Eside, Ebot]
    have hdef := hB.deficit
    rw [hEeq] at hdef
    obtain ⟨w, m, k, -, hkm, hEeq', hCsub, heE, hdet⟩ :=
      Sz.exists_forward_rule_aux hB.latticeConvex hEeq (hEeq ▸ Sz.Eside_nonempty hB.nonempty) hdef
    exact ⟨_, _, hCsub, heE, hdet⟩
  · have hEeq : Sz.Eside true B = B.filter fun z => Sz.phi z = Sz.topIdx B := by
      simp [Eside, Etop]
    have hdef := hB.deficit
    rw [hEeq] at hdef
    obtain ⟨w, m, k, -, hkm, hEeq', hCsub, heE, hdet⟩ :=
      Sz.exists_forward_rule_aux hB.latticeConvex hEeq (hEeq ▸ Sz.Eside_nonempty hB.nonempty) hdef
    exact ⟨_, _, hCsub, heE, hdet⟩

/-- Rule `(R_-)` of Lemma D.7: same conclusion as `exists_forward_rule`, but built from the run
traversed in the opposite direction. -/
theorem exists_backward_rule [Fact p.Prime] {ε : Bool} {B : Finset (ℤ × ℤ)}
    (hB : Sz.Balanced ε B) :
    ∃ (C : Finset (ℤ × ℤ)) (e : ℤ × ℤ), C ⊆ B ∧ e ∈ Sz.Eside ε B ∧
      ∀ (y : Config (ZMod p)) (_ : y ∈ orbitClosure Sz.xi)
        (y' : Config (ZMod p)) (_ : y' ∈ orbitClosure Sz.xi) (v w : ℤ × ℤ),
        (∀ c ∈ C, y (v + c) = y' (w + c)) → y (v + e) = y' (w + e) := by
  cases ε
  · have hEeq : Sz.Eside false B = B.filter fun z => Sz.phi z = Sz.botIdx B := by
      simp [Eside, Ebot]
    have hdef := hB.deficit
    rw [hEeq] at hdef
    obtain ⟨w', m, k, -, hkm, hEeq', hCsub, heE, hdet⟩ :=
      Sz.exists_backward_rule_aux hB.latticeConvex hEeq (hEeq ▸ Sz.Eside_nonempty hB.nonempty) hdef
    exact ⟨_, _, hCsub, heE, hdet⟩
  · have hEeq : Sz.Eside true B = B.filter fun z => Sz.phi z = Sz.topIdx B := by
      simp [Eside, Etop]
    have hdef := hB.deficit
    rw [hEeq] at hdef
    obtain ⟨w', m, k, -, hkm, hEeq', hCsub, heE, hdet⟩ :=
      Sz.exists_backward_rule_aux hB.latticeConvex hEeq (hEeq ▸ Sz.Eside_nonempty hB.nonempty) hdef
    exact ⟨_, _, hCsub, heE, hdet⟩

/-! ### Translating a balanced set

Step (1) of Lemma D.7: "translate `B`" — replace `B` by `B + v` for a vector `v` with
`φ(v) = b - topIdx(B)`, obtainable since `φ` is surjective (`phi_surjective`).  Translating by `v`
shifts `φ` (hence `topIdx`, `botIdx`, `Etop`, `Ebot`) by `φ(v)`, leaves `ht` and the rows'
relative structure unchanged, and (by `P_translate`, `LatticeConvex.translate`) preserves every
hypothesis of `Balanced`. -/

theorem topIdx_add {F : Finset (ℤ × ℤ)} (hF : F.Nonempty) (v : ℤ × ℤ) :
    Sz.topIdx (F.image (· + v)) = Sz.topIdx F + Sz.phi v := by
  have hFv : (F.image (· + v)).Nonempty := hF.image _
  apply le_antisymm
  · obtain ⟨z, hz⟩ := Sz.Etop_nonempty hFv
    rw [Etop, Finset.mem_filter] at hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz.1
    have h2 := Sz.phi_le_topIdx hw
    rw [Sz.phi_add] at hz
    omega
  · obtain ⟨z, hz⟩ := Sz.Etop_nonempty hF
    rw [Etop, Finset.mem_filter] at hz
    have h2 := Sz.phi_le_topIdx (Finset.mem_image_of_mem (· + v) hz.1)
    rw [Sz.phi_add, hz.2] at h2
    exact h2

theorem botIdx_add {F : Finset (ℤ × ℤ)} (hF : F.Nonempty) (v : ℤ × ℤ) :
    Sz.botIdx (F.image (· + v)) = Sz.botIdx F + Sz.phi v := by
  have hFv : (F.image (· + v)).Nonempty := hF.image _
  apply le_antisymm
  · obtain ⟨z, hz⟩ := Sz.Ebot_nonempty hF
    rw [Ebot, Finset.mem_filter] at hz
    have h2 := Sz.botIdx_le_phi (Finset.mem_image_of_mem (· + v) hz.1)
    rw [Sz.phi_add, hz.2] at h2
    exact h2
  · obtain ⟨z, hz⟩ := Sz.Ebot_nonempty hFv
    rw [Ebot, Finset.mem_filter] at hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz.1
    have h2 := Sz.botIdx_le_phi hw
    rw [Sz.phi_add] at hz
    omega

theorem ht_add {F : Finset (ℤ × ℤ)} (hF : F.Nonempty) (v : ℤ × ℤ) :
    Sz.ht (F.image (· + v)) = Sz.ht F := by
  simp only [ht, Sz.topIdx_add hF, Sz.botIdx_add hF]
  ring

theorem Etop_add {F : Finset (ℤ × ℤ)} (hF : F.Nonempty) (v : ℤ × ℤ) :
    Sz.Etop (F.image (· + v)) = (Sz.Etop F).image (· + v) := by
  rw [Etop, Etop, Sz.topIdx_add hF]
  ext z
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    rw [Sz.phi_add] at hz
    exact ⟨w, ⟨hw, by omega⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hwphi⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, by rw [Sz.phi_add]; omega⟩

theorem Ebot_add {F : Finset (ℤ × ℤ)} (hF : F.Nonempty) (v : ℤ × ℤ) :
    Sz.Ebot (F.image (· + v)) = (Sz.Ebot F).image (· + v) := by
  rw [Ebot, Ebot, Sz.botIdx_add hF]
  ext z
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    rw [Sz.phi_add] at hz
    exact ⟨w, ⟨hw, by omega⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hwphi⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, by rw [Sz.phi_add]; omega⟩

theorem Eside_add {ε : Bool} {F : Finset (ℤ × ℤ)} (hF : F.Nonempty) (v : ℤ × ℤ) :
    Sz.Eside ε (F.image (· + v)) = (Sz.Eside ε F).image (· + v) := by
  cases ε
  · simpa [Eside] using Sz.Ebot_add hF v
  · simpa [Eside] using Sz.Etop_add hF v

/-- The row `t` of a translate is the shifted row `t - φ(v)` of the original. -/
theorem filter_phi_eq_add {F : Finset (ℤ × ℤ)} (t : ℤ) (v : ℤ × ℤ) :
    (F.image (· + v)).filter (fun z => Sz.phi z = t)
      = (F.filter fun z => Sz.phi z = t - Sz.phi v).image (· + v) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    rw [Sz.phi_add] at hz
    exact ⟨w, ⟨hw, by omega⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hwphi⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, by rw [Sz.phi_add]; omega⟩

/-- Translating a balanced set gives a balanced set: Step (1) of Lemma D.7. -/
theorem Balanced.translate [Fact p.Prime] {ε : Bool} {B : Finset (ℤ × ℤ)}
    (hB : Sz.Balanced ε B) (v : ℤ × ℤ) : Sz.Balanced ε (B.image (· + v)) where
  nonempty := hB.nonempty.image _
  latticeConvex := hB.latticeConvex.translate v
  low := by
    rw [Finset.card_image_of_injective _ (add_left_injective v), P_translate]
    exact hB.low
  deficit := by
    have hinj : Function.Injective (· + v : ℤ × ℤ → ℤ × ℤ) := add_left_injective v
    rw [Sz.Eside_add hB.nonempty, ← Finset.image_sdiff _ _ hinj,
      Finset.card_image_of_injective _ hinj, P_translate, P_translate]
    exact hB.deficit
  rows := by
    intro t hlo hhi
    have hinj : Function.Injective (· + v : ℤ × ℤ → ℤ × ℤ) := add_left_injective v
    rw [Sz.topIdx_add hB.nonempty] at hhi
    rw [Sz.botIdx_add hB.nonempty] at hlo
    rw [Sz.Eside_add hB.nonempty, Finset.card_image_of_injective _ hinj,
      Sz.filter_phi_eq_add, Finset.card_image_of_injective _ hinj]
    exact hB.rows (t - Sz.phi v) (by omega) (by omega)

/-- **Lemma D.7 (Propagation), placed form.**  Same statement as `isPeriodic_of_ambiguityStrip`,
with the extra hypothesis that `B`'s top row already sits on `L_b` (step (1) is then vacuous);
the general statement translates `B` to reduce to this case. -/
private theorem isPeriodic_of_ambiguityStrip_aux [Fact p.Prime] {B : Finset (ℤ × ℤ)}
    (hB : Sz.Balanced true B) {a b : ℤ} (htop : Sz.topIdx B = b)
    (hamb : Sz.AmbiguityStrip a b) (hfit : Sz.ht B ≤ b - a) : IsPeriodic Sz.xi := by
  classical
  obtain ⟨hab, x, hxmem, hxagree, v0, hv0mem, hv0ne⟩ := hamb
  -- `E := Etop B`, the top row of `B`, now known to be `B ∩ L_b`.
  set E : Finset (ℤ × ℤ) := B.filter fun z => Sz.phi z = b with hE_def
  have hEside_eq : Sz.Eside true B = E := by
    rw [hE_def]
    have h0 : Sz.Eside true B = B.filter fun z => Sz.phi z = Sz.topIdx B := by simp [Eside, Etop]
    rw [h0, htop]
  have hEne : E.Nonempty := by
    rw [hE_def, ← htop]
    simpa [Etop] using Sz.Etop_nonempty hB.nonempty
  have hdeficit : P Sz.xi B < P Sz.xi (B \ E) + E.card := by
    have hd := hB.deficit; rwa [hEside_eq] at hd
  set B0 : Finset (ℤ × ℤ) := B \ E with hB0_def
  -- The two determination rules `(R_+)`, `(R_-)`, with the run `E = {w, w+u, …, w+(m-1)u}`
  -- (equivalently traversed backwards from `w' = w + (m-1)u`) and pigeonhole indices `k`, `k'`.
  obtain ⟨w, m, k, hmpos, hkm, hEeqRun, hCsub, heE, hdet⟩ :=
    Sz.exists_forward_rule_aux hB.latticeConvex hE_def hEne hdeficit
  obtain ⟨w', m', k', hmpos', hkm', hEeqRun', hCsub', heE', hdet'⟩ :=
    Sz.exists_backward_rule_aux hB.latticeConvex hE_def hEne hdeficit
  have hmcard : E.card = m := by
    rw [hEeqRun, Finset.card_image_of_injective _ (injective_add_zsmul Sz.u_primitive.ne_zero),
      Finset.card_range]
  have hm'card : E.card = m' := by
    rw [hEeqRun',
      Finset.card_image_of_injective _ (injective_add_zsmul (neg_ne_zero.mpr Sz.u_primitive.ne_zero)),
      Finset.card_range]
  have hmm' : m = m' := by omega
  -- Step (1)'s remark: `B₀ + iu ⊆ St[a, b-1]` for every `i`, since `φ` is unchanged by adding
  -- multiples of `u`; hence the witness `x` agrees with `ξ` there.
  have hB0strip : ∀ z ∈ B0, z ∈ Sz.strip a (b - 1) := by
    intro z hz
    have hz' : z ∈ B ∧ Sz.phi z ≠ b := by
      have hz2 := hz
      rw [hB0_def, Finset.mem_sdiff, hE_def, Finset.mem_filter] at hz2
      exact ⟨hz2.1, fun h => hz2.2 ⟨hz2.1, h⟩⟩
    have h1 : Sz.phi z ≤ b := htop ▸ Sz.phi_le_topIdx hz'.1
    have hbot : a ≤ Sz.botIdx B := by
      have hht := hfit; simp only [ht, htop] at hht; omega
    have h2 : a ≤ Sz.phi z := le_trans hbot (Sz.botIdx_le_phi hz'.1)
    exact ⟨h2, by omega⟩
  have hB0_agree : ∀ z ∈ B0, ∀ i : ℤ, x (z + i • Sz.u) = Sz.xi (z + i • Sz.u) :=
    fun z hz i => hxagree _ (Sz.add_zsmul_u_mem_strip (hB0strip z hz) i)
  -- `D_k = B0 ∪ {e_1, …, e_k}`, and `e_{k+1} = w + k•u` is determined by `y` on `D_k + v`
  -- (`hdet`); symmetrically `D'_{k'} = B0 ∪ {e_{n-k'+1}, …, e_n}` (from the other end) determines
  -- `e_{n-k'} = w' + k'•(-u)` (`hdet'`).  Steps (3)-(7) of the paper proof remain: the two-sided
  -- induction showing `x` and `ξ` disagree on every translate `D_k + i•u` (step 3), the counting
  -- argument bounding the number of distinct patterns `ξ|_{B0 + i•u}` by `n - 1` (step 4), the
  -- one-dimensional Morse–Hedlund theorem applied to each row of `B0` (step 5,
  -- `periodic_of_subwords_le`), the finite-state extension one row at a time (step 6,
  -- `periodic_of_two_sided_determinacy`), and Lemma D.3 (step 7, `period_of_strip`).
  -- One step of the propagation along a run `C = B0 ∪ {w0, w0+d, …, w0+(kk-1)d}`, `e = w0+kk•d`,
  -- using a determination rule `hdetC` for `e` from `C` (this is `hdet`/`hdet'` with `d = ±u`),
  -- and the `d`-agreement of `x`, `ξ` on `B0` (this is `hB0_agree` itself for `d = u`, and its
  -- `-u`-translate for `d = -u`).
  have hpropagate : ∀ (C : Finset (ℤ × ℤ)) (d e w0 : ℤ × ℤ) (kk : ℕ),
      C = B0 ∪ (Finset.range kk).image (fun s : ℕ => w0 + (s : ℤ) • d) →
      e = w0 + (kk : ℤ) • d →
      (∀ z ∈ B0, ∀ i : ℤ, x (z + i • d) = Sz.xi (z + i • d)) →
      (∀ (y : Config (ZMod p)), y ∈ orbitClosure Sz.xi →
        ∀ (y' : Config (ZMod p)), y' ∈ orbitClosure Sz.xi → ∀ (v ww : ℤ × ℤ),
        (∀ c ∈ C, y (v + c) = y' (ww + c)) → y (v + e) = y' (ww + e)) →
      ∀ i₀ : ℤ, (∀ z ∈ C, x (z + i₀ • d) = Sz.xi (z + i₀ • d)) →
      ∀ n : ℕ, ∀ z ∈ C, x (z + (i₀ + (n : ℤ)) • d) = Sz.xi (z + (i₀ + (n : ℤ)) • d) := by
    intro C d e w0 kk hCeq he hB0d hdetC i₀ hbase n
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      intro z hz
      rw [hCeq, Finset.mem_union] at hz
      rcases hz with hzB0 | hzE
      · have h := hB0d z hzB0 (i₀ + ((n : ℤ) + 1))
        have hcast : i₀ + ((n + 1 : ℕ) : ℤ) = i₀ + ((n : ℤ) + 1) := by push_cast; ring
        rw [hcast]
        exact h
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hzE
        rw [Finset.mem_range] at hs
        by_cases hsk : s + 1 < kk
        · have hmem : (w0 + ((s + 1 : ℕ) : ℤ) • d) ∈ C := by
            rw [hCeq]
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s + 1, Finset.mem_range.mpr hsk, rfl⟩)
          have hres := ih _ hmem
          have heq : w0 + (s : ℤ) • d + (i₀ + ((n + 1 : ℕ) : ℤ)) • d
              = w0 + ((s + 1 : ℕ) : ℤ) • d + (i₀ + (n : ℤ)) • d := by push_cast; module
          rw [heq]
          exact hres
        · have hsk' : s + 1 = kk := by omega
          have hbaseshift : ∀ c ∈ C, x ((i₀ + (n : ℤ)) • d + c) = Sz.xi ((i₀ + (n : ℤ)) • d + c) := by
            intro c hc
            have hh := ih c hc
            rw [add_comm]; exact hh
          have hxOC : x ∈ orbitClosure Sz.xi := hxmem
          have hxiOC : Sz.xi ∈ orbitClosure Sz.xi := self_mem_orbitClosure Sz.xi
          have hde := hdetC x hxOC Sz.xi hxiOC ((i₀ + (n : ℤ)) • d) ((i₀ + (n : ℤ)) • d) hbaseshift
          have heq2 : w0 + (s : ℤ) • d + (i₀ + ((n + 1 : ℕ) : ℤ)) • d
              = (i₀ + (n : ℤ)) • d + e := by
            rw [he]
            have hkkeq : (kk : ℤ) = (s : ℤ) + 1 := by exact_mod_cast hsk'.symm
            rw [hkkeq]; push_cast; module
          rw [heq2]
          exact hde
  -- The `-u`-translate of `hB0_agree`, needed to feed `hpropagate` in the backward direction.
  have hB0_agree_neg : ∀ z ∈ B0, ∀ i : ℤ, x (z + i • (-Sz.u)) = Sz.xi (z + i • (-Sz.u)) := by
    intro z hz i
    have h := hB0_agree z hz (-i)
    have heq : z + i • (-Sz.u) = z + (-i) • Sz.u := by module
    rw [heq]; exact h
  -- The two degenerate cases `k = 0` (resp. `k' = 0`), where the single application of `(R_+)`
  -- (resp. `(R_-)`) to `B0` alone, with no induction needed, already forces `x = ξ` on all of
  -- `L_b`, contradicting the ambiguity witness `hv0ne` outright.
  have hphiv0 : Sz.phi v0 = b := hv0mem
  by_cases hk0 : k = 0
  · exfalso
    have heEw : Sz.phi w = b := by
      have h := heE
      rw [hk0] at h
      simp only [Nat.cast_zero, zero_smul, add_zero] at h
      rw [hE_def, Finset.mem_filter] at h
      exact h.2
    have hall : ∀ i₀ : ℤ, x (w + i₀ • Sz.u) = Sz.xi (w + i₀ • Sz.u) := by
      intro i₀
      have hbasei : ∀ c ∈ (B \ E) ∪ (Finset.range k).image (fun s : ℕ => w + (s : ℤ) • Sz.u),
          x (i₀ • Sz.u + c) = Sz.xi (i₀ • Sz.u + c) := by
        rw [hk0]
        simp only [Finset.range_zero, Finset.image_empty, Finset.union_empty]
        intro c hc
        have hc' : c ∈ B0 := by rw [hB0_def]; exact hc
        rw [add_comm]; exact hB0_agree c hc' i₀
      have hh := hdet x hxmem Sz.xi (self_mem_orbitClosure Sz.xi) (i₀ • Sz.u) (i₀ • Sz.u) hbasei
      rw [hk0] at hh
      rw [add_comm]
      simpa using hh
    obtain ⟨s, hs⟩ := Sz.exists_zsmul_of_phi_eq (z := v0) (w := w) (hphiv0.trans heEw.symm)
    rw [hs] at hv0ne
    exact hv0ne (hall s)
  by_cases hk'0 : k' = 0
  · exfalso
    have heEw' : Sz.phi w' = b := by
      have h := heE'
      rw [hk'0] at h
      simp only [Nat.cast_zero, zero_smul, add_zero] at h
      rw [hE_def, Finset.mem_filter] at h
      exact h.2
    have hall' : ∀ i₀ : ℤ, x (w' + i₀ • (-Sz.u)) = Sz.xi (w' + i₀ • (-Sz.u)) := by
      intro i₀
      have hbasei : ∀ c ∈ (B \ E) ∪ (Finset.range k').image (fun s : ℕ => w' + (s : ℤ) • (-Sz.u)),
          x (i₀ • (-Sz.u) + c) = Sz.xi (i₀ • (-Sz.u) + c) := by
        rw [hk'0]
        simp only [Finset.range_zero, Finset.image_empty, Finset.union_empty]
        intro c hc
        have hc' : c ∈ B0 := by rw [hB0_def]; exact hc
        rw [add_comm]; exact hB0_agree_neg c hc' i₀
      have hh := hdet' x hxmem Sz.xi (self_mem_orbitClosure Sz.xi) (i₀ • (-Sz.u)) (i₀ • (-Sz.u)) hbasei
      rw [hk'0] at hh
      rw [add_comm]
      simpa using hh
    have hphiww' : Sz.phi v0 = Sz.phi w' := hphiv0.trans heEw'.symm
    obtain ⟨s, hs⟩ := Sz.exists_zsmul_of_phi_eq (z := v0) (w := w') hphiww'
    have heq : v0 = w' + (-s) • (-Sz.u) := by rw [hs]; module
    rw [heq] at hv0ne
    exact hv0ne (hall' (-s))
  -- General case `k ≥ 1 ∧ k' ≥ 1`.  `φ` is invariant under adding any multiple of `u` (since
  -- `φ(u) = 0`), so both endpoints of the two runs lie on the same fibre `L_b = w + ℤ•u`.
  have hphiw : Sz.phi w = b := by
    have h2 : Sz.phi (w + (k : ℤ) • Sz.u) = b := by
      rw [hE_def, Finset.mem_filter] at heE; exact heE.2
    rwa [Sz.phi_add, Sz.phi_smul, Sz.phi_u, mul_zero, add_zero] at h2
  have hphiw' : Sz.phi w' = b := by
    have h2 : Sz.phi (w' + (k' : ℤ) • (-Sz.u)) = b := by
      rw [hE_def, Finset.mem_filter] at heE'; exact heE'.2
    rwa [Sz.phi_add, Sz.phi_smul, Sz.phi_neg, Sz.phi_u, neg_zero, mul_zero, add_zero] at h2
  obtain ⟨t0, ht0⟩ := Sz.exists_zsmul_of_phi_eq (z := w') (w := w) (hphiw'.trans hphiw.symm)
  obtain ⟨s0, hs0⟩ := Sz.exists_zsmul_of_phi_eq (z := v0) (w := w) (hphiv0.trans hphiw.symm)
  -- Step (3), the Claim: for no `i₀` does `x` agree with `ξ` on all of `D_k + i₀u`.  Given such
  -- an agreement, `hpropagate` (forward from `D_k`, then backward from `D'_{k'}` seeded inside
  -- the already-covered half-line) forces agreement on all of `L_b`, contradicting `hv0ne`.
  have hclaim3 : ∀ i₀ : ℤ,
      ¬ (∀ z ∈ B0 ∪ (Finset.range k).image (fun s : ℕ => w + (s : ℤ) • Sz.u),
          x (z + i₀ • Sz.u) = Sz.xi (z + i₀ • Sz.u)) := by
    intro i₀ hbase
    have hforward := hpropagate (B0 ∪ (Finset.range k).image (fun s : ℕ => w + (s : ℤ) • Sz.u))
      Sz.u (w + (k : ℤ) • Sz.u) w k rfl rfl hB0_agree hdet i₀ hbase
    have hwmemCk : w ∈ B0 ∪ (Finset.range k).image (fun s : ℕ => w + (s : ℤ) • Sz.u) := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hk0), by simp⟩
    have hforward_all : ∀ s : ℤ, i₀ ≤ s → x (w + s • Sz.u) = Sz.xi (w + s • Sz.u) := by
      intro s hs
      have hn := hforward (s - i₀).toNat w hwmemCk
      have hcast : ((s - i₀).toNat : ℤ) = s - i₀ := Int.toNat_of_nonneg (by omega)
      rw [hcast] at hn
      have hst : i₀ + (s - i₀) = s := by ring
      rw [hst] at hn
      exact hn
    set i₁ : ℤ := t0 - ((k' : ℤ) - 1) - i₀ with hi1_def
    have hbase' : ∀ z ∈ B0 ∪ (Finset.range k').image (fun s : ℕ => w' + (s : ℤ) • (-Sz.u)),
        x (z + i₁ • (-Sz.u)) = Sz.xi (z + i₁ • (-Sz.u)) := by
      intro z hz
      rw [Finset.mem_union] at hz
      rcases hz with hzB0 | hzE
      · exact hB0_agree_neg z hzB0 i₁
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hzE
        rw [Finset.mem_range] at ht
        have heq : w' + (t : ℤ) • (-Sz.u) + i₁ • (-Sz.u)
            = w + (t0 - (t : ℤ) - i₁) • Sz.u := by rw [ht0]; module
        rw [heq]
        apply hforward_all
        have ht' : (t : ℤ) < (k' : ℤ) := by exact_mod_cast ht
        rw [hi1_def]; omega
    have hbackward := hpropagate
      (B0 ∪ (Finset.range k').image (fun s : ℕ => w' + (s : ℤ) • (-Sz.u)))
      (-Sz.u) (w' + (k' : ℤ) • (-Sz.u)) w' k' rfl rfl hB0_agree_neg hdet' i₁ hbase'
    have hw'memCk' : w' ∈ B0 ∪ (Finset.range k').image (fun s : ℕ => w' + (s : ℤ) • (-Sz.u)) := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hk'0), by simp⟩
    have hbackward_all : ∀ s : ℤ, s ≤ t0 - i₁ → x (w + s • Sz.u) = Sz.xi (w + s • Sz.u) := by
      intro s hs
      have hn := hbackward (t0 - i₁ - s).toNat w' hw'memCk'
      have hcast : ((t0 - i₁ - s).toNat : ℤ) = t0 - i₁ - s := Int.toNat_of_nonneg (by omega)
      rw [hcast] at hn
      have heq : w' + (i₁ + (t0 - i₁ - s)) • (-Sz.u) = w + s • Sz.u := by
        rw [ht0]; module
      rw [heq] at hn
      exact hn
    by_cases hcmp : i₀ ≤ s0
    · rw [hs0] at hv0ne; exact hv0ne (hforward_all s0 hcmp)
    · have hs0le : s0 ≤ t0 - i₁ := by rw [hi1_def]; push Not at hcmp; omega
      rw [hs0] at hv0ne; exact hv0ne (hbackward_all s0 hs0le)
  -- Step (4): counting.  `n := |E|`.  For each `i`, `x|_{B+iu}` occurs literally as a
  -- `B`-pattern `θ|_{B+v}` of `θ` (since `x ∈ orbitClosure θ`); this pattern and `θ|_{B+iu}`
  -- both restrict to `θ|_{B0+iu}` on `B0 ⊆ B`, but are themselves distinct by `hclaim3` applied
  -- to `D_k ⊆ B`.  So the restriction map `r : Pat(B,θ) → Pat(B0,θ)` has fibre size `≥ 2` over
  -- every element of `Γ := {θ|_{B0+iu} : i ∈ ℤ}`, whence `|Γ| < n`.
  set n : ℕ := E.card with hn_def
  have hB0sub : B0 ⊆ B := by rw [hB0_def]; exact Finset.sdiff_subset
  set r : (↥B → ZMod p) → (↥B0 → ZMod p) := fun g q => g ⟨(q : ℤ × ℤ), hB0sub q.2⟩ with hr_def
  have hr_pattern : ∀ v : ℤ × ℤ, r (pattern Sz.xi B v) = pattern Sz.xi B0 v := by
    intro v; funext q; rfl
  set PB : Finset (↥B → ZMod p) := (patterns_finite Sz.xi B).toFinset with hPB_def
  set PB0 : Finset (↥B0 → ZMod p) := (patterns_finite Sz.xi B0).toFinset with hPB0_def
  have hPBcard : PB.card = P Sz.xi B := (Set.ncard_eq_toFinset_card _ _).symm
  have hPB0card : PB0.card = P Sz.xi B0 := (Set.ncard_eq_toFinset_card _ _).symm
  have hmem_PB : ∀ g : ↥B → ZMod p, g ∈ PB ↔ g ∈ patterns Sz.xi B := by
    intro g; rw [hPB_def, Set.Finite.mem_toFinset]
  have hmem_PB0 : ∀ g : ↥B0 → ZMod p, g ∈ PB0 ↔ g ∈ patterns Sz.xi B0 := by
    intro g; rw [hPB0_def, Set.Finite.mem_toFinset]
  have hmaps : (↑PB : Set (↥B → ZMod p)).MapsTo r PB0 := by
    intro g hg
    rw [Finset.mem_coe, hmem_PB] at hg
    obtain ⟨v, rfl⟩ := hg
    rw [Finset.mem_coe, hr_pattern]
    exact (hmem_PB0 _).mpr ⟨v, rfl⟩
  have hcard_eq : PB.card = ∑ b ∈ PB0, (PB.filter fun a => r a = b).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  -- `N(b) ≥ 1` for `b ∈ PB0`: `r` hits every `B0`-pattern.
  have hN1 : ∀ b ∈ PB0, 1 ≤ (PB.filter fun a => r a = b).card := by
    intro b hb
    obtain ⟨v, rfl⟩ := (hmem_PB0 b).mp hb
    rw [Finset.one_le_card]
    refine ⟨pattern Sz.xi B v, Finset.mem_filter.mpr ⟨?_, hr_pattern v⟩⟩
    exact (hmem_PB _).mpr ⟨v, rfl⟩
  set S : ℕ := ∑ b ∈ PB0, ((PB.filter fun a => r a = b).card - 1) with hS_def
  have hsplit : PB.card = PB0.card + S := by
    rw [hcard_eq]
    have hrw : ∀ b ∈ PB0, (PB.filter fun a => r a = b).card
        = ((PB.filter fun a => r a = b).card - 1) + 1 :=
      fun b hb => (Nat.sub_add_cancel (hN1 b hb)).symm
    rw [Finset.sum_congr rfl hrw, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      mul_one, hS_def]
    ring
  have hSlt : S < n := by
    have h1 : PB.card < PB0.card + n := by rw [hPBcard, hPB0card]; exact hdeficit
    omega
  -- `Γ := {θ|_{B0+iu} : i ∈ ℤ}`, a finite subset of `Pat(B0, θ)`.
  set Γ : Set (↥B0 → ZMod p) := Set.range (fun i : ℤ => pattern Sz.xi B0 (i • Sz.u)) with hGamma_def
  have hGammasub : Γ ⊆ (PB0 : Set (↥B0 → ZMod p)) := by
    rintro _ ⟨i, rfl⟩
    exact (hmem_PB0 _).mpr ⟨i • Sz.u, rfl⟩
  have hGammafin : Γ.Finite := Set.Finite.subset PB0.finite_toSet hGammasub
  set ΓF : Finset (↥B0 → ZMod p) := hGammafin.toFinset with hΓF_def
  have hΓFsub : ΓF ⊆ PB0 := by
    intro g hg
    rw [hΓF_def, Set.Finite.mem_toFinset] at hg
    exact hGammasub hg
  -- Every `b ∈ Γ` has fibre size `≥ 2`: `x|_{B+iu}` occurs as `θ|_{B+v}` (orbit closure),
  -- distinct from `θ|_{B+iu}` by `hclaim3` at a point of `D_k ⊆ B`, yet both restrict to `b`.
  have hfiber2 : ∀ b ∈ ΓF, 2 ≤ (PB.filter fun a => r a = b).card := by
    intro b hb
    rw [hΓF_def, Set.Finite.mem_toFinset] at hb
    obtain ⟨i, rfl⟩ := hb
    obtain ⟨v, hv⟩ := exists_pattern_eq_of_mem_orbitClosure hxmem B (i • Sz.u)
    have hne3 := hclaim3 i
    push Not at hne3
    obtain ⟨z, hzD, hzne⟩ := hne3
    have hzB : z ∈ B := hCsub hzD
    have hdist : pattern Sz.xi B (i • Sz.u) ≠ pattern Sz.xi B v := by
      intro heq
      have h1 : x (i • Sz.u + z) = Sz.xi (v + z) := congrFun hv ⟨z, hzB⟩
      have h2 : Sz.xi (i • Sz.u + z) = Sz.xi (v + z) := congrFun heq ⟨z, hzB⟩
      apply hzne
      rw [add_comm z (i • Sz.u), h1]
      exact h2.symm
    have hrxi : r (pattern x B (i • Sz.u)) = pattern Sz.xi B0 (i • Sz.u) := by
      funext q
      show x (i • Sz.u + (q : ℤ × ℤ)) = Sz.xi (i • Sz.u + (q : ℤ × ℤ))
      rw [add_comm (i • Sz.u) (q : ℤ × ℤ)]
      exact hB0_agree (q : ℤ × ℤ) q.2 i
    have heqB0 : pattern Sz.xi B0 (i • Sz.u) = pattern Sz.xi B0 v := by
      rw [← hrxi, congrArg r hv]
      exact hr_pattern v
    have hmemA : pattern Sz.xi B (i • Sz.u)
        ∈ PB.filter fun a => r a = pattern Sz.xi B0 (i • Sz.u) :=
      Finset.mem_filter.mpr ⟨(hmem_PB _).mpr ⟨i • Sz.u, rfl⟩, hr_pattern _⟩
    have hmemB : pattern Sz.xi B v ∈ PB.filter fun a => r a = pattern Sz.xi B0 (i • Sz.u) :=
      Finset.mem_filter.mpr ⟨(hmem_PB _).mpr ⟨v, rfl⟩, by rw [hr_pattern, ← heqB0]⟩
    have hpair : ({pattern Sz.xi B (i • Sz.u), pattern Sz.xi B v} : Finset (↥B → ZMod p))
        ⊆ PB.filter fun a => r a = pattern Sz.xi B0 (i • Sz.u) := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hmemA
      · exact hmemB
    have h2card :
        ({pattern Sz.xi B (i • Sz.u), pattern Sz.xi B v} : Finset (↥B → ZMod p)).card = 2 :=
      Finset.card_pair hdist
    calc 2 = ({pattern Sz.xi B (i • Sz.u), pattern Sz.xi B v} : Finset (↥B → ZMod p)).card :=
          h2card.symm
      _ ≤ (PB.filter fun a => r a = pattern Sz.xi B0 (i • Sz.u)).card := Finset.card_le_card hpair
  have hGammacard : ΓF.card ≤ S := by
    calc ΓF.card = ∑ _b ∈ ΓF, 1 := by simp
      _ ≤ ∑ b ∈ ΓF, ((PB.filter fun a => r a = b).card - 1) := by
          apply Finset.sum_le_sum
          intro b hb
          have := hfiber2 b hb
          omega
      _ ≤ ∑ b ∈ PB0, ((PB.filter fun a => r a = b).card - 1) :=
          Finset.sum_le_sum_of_subset hΓFsub
      _ = S := hS_def.symm
  have hGammaBound : ΓF.card < n := lt_of_le_of_lt hGammacard hSlt
  have hΓFne : ΓF.Nonempty :=
    ⟨pattern Sz.xi B0 (0 • Sz.u), by rw [hΓF_def, Set.Finite.mem_toFinset]; exact ⟨0, rfl⟩⟩
  have hn2 : 2 ≤ n := by
    have h1 := hΓFne.card_pos
    omega
  -- Step (5): periodicity of the rows of `B0`.  For `t ≠ b`, `B0 ∩ L_t = B ∩ L_t`.
  have hB0row : ∀ t : ℤ, t ≠ b →
      B0.filter (fun z => Sz.phi z = t) = B.filter (fun z => Sz.phi z = t) := by
    intro t ht
    rw [hB0_def]
    ext z
    simp only [Finset.mem_filter, Finset.mem_sdiff, hE_def]
    constructor
    · rintro ⟨⟨hzB, _⟩, hzt⟩
      exact ⟨hzB, hzt⟩
    · rintro ⟨hzB, hzt⟩
      refine ⟨⟨hzB, ?_⟩, hzt⟩
      rintro ⟨-, hzb⟩
      exact ht (hzt.symm.trans hzb)
  set t_ : ℤ := Sz.botIdx B with ht_def
  -- For every row `t ∈ [t_, b-1]`, `|B ∩ L_t| ≥ n - 1`, so (lattice convexity) it is a run
  -- `w_t, w_t+u, …, w_t+(m_t-1)u` with `m_t ≥ n - 1 ≥ 1`.
  have hrow_data : ∀ t : ℤ, t_ ≤ t → t ≤ b - 1 →
      ∃ (w_t : ℤ × ℤ) (m_t : ℕ), n - 1 ≤ m_t ∧
        B.filter (fun z => Sz.phi z = t) = (Finset.range m_t).image fun s : ℕ => w_t + (s : ℤ) • Sz.u := by
    intro t htlo hthi
    have htb : t ≤ Sz.topIdx B := by rw [htop]; omega
    have hcard : n ≤ (B.filter fun z => Sz.phi z = t).card + 1 := by
      have h2 := hB.rows t htlo htb
      rw [hEside_eq] at h2
      omega
    have hne : (B.filter fun z => Sz.phi z = t).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨w_t, m_t, hm_tpos, hEeq_t⟩ := Sz.row_eq_run hB.latticeConvex t hne
    refine ⟨w_t, m_t, ?_, hEeq_t⟩
    have hcard_t : (B.filter fun z => Sz.phi z = t).card = m_t := by
      rw [hEeq_t, Finset.card_image_of_injective _ (injective_add_zsmul Sz.u_primitive.ne_zero),
        Finset.card_range]
    omega
  -- Choose such data for every row (irrelevant values outside `[t_, b-1]`).
  choose! w_row m_row hm_row hEeq_row using hrow_data
  -- The row-word `ξ_t(s) := ξ(w_t + s • u)`.
  set xirow : ℤ → ℤ → ZMod p := fun t s => Sz.xi (w_row t + s • Sz.u) with hxirow_def
  -- `φ(w_t) = t`: `xirow t` is genuinely `ξ` restricted to row `t`.
  have hphi_w_row : ∀ t : ℤ, t_ ≤ t → t ≤ b - 1 → Sz.phi (w_row t) = t := by
    intro t htlo hthi
    have hmem0 : w_row t ∈ B.filter fun z => Sz.phi z = t := by
      rw [hEeq_row t htlo hthi]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by have := hm_row t htlo hthi; omega),
        by simp⟩
    exact (Finset.mem_filter.mp hmem0).2
  -- Every window of length `n - 1` of `xirow t` (`t ∈ [t_, b - 1]`) is the restriction of a
  -- pattern in `Γ` to the first `n - 1` points of row `t`, so there are at most `|Γ| ≤ n - 1`
  -- of them: the subword-complexity bound needed for Morse–Hedlund.
  have hsubword_bound : ∀ t : ℤ, t_ ≤ t → t ≤ b - 1 →
      (subwords (xirow t) (n - 1)).ncard ≤ n - 1 := by
    intro t htlo hthi
    have hmem_row : ∀ l : Fin (n - 1), (w_row t + (l : ℕ) • Sz.u) ∈ B0 := by
      intro l
      have hmemB : w_row t + (l : ℕ) • Sz.u ∈ B.filter fun z => Sz.phi z = t := by
        rw [hEeq_row t htlo hthi]
        exact Finset.mem_image.mpr ⟨l, Finset.mem_range.mpr (by have := hm_row t htlo hthi; omega),
          rfl⟩
      have hmemB0 : w_row t + (l : ℕ) • Sz.u ∈ B0.filter fun z => Sz.phi z = t := by
        rw [hB0row t (by omega)]; exact hmemB
      exact (Finset.mem_filter.mp hmemB0).1
    set windowMap : (↥B0 → ZMod p) → (Fin (n - 1) → ZMod p) :=
      fun g l => g ⟨w_row t + (l : ℕ) • Sz.u, hmem_row l⟩ with hwindowMap_def
    have hsubword_eq : subwords (xirow t) (n - 1) = windowMap '' Γ := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        refine ⟨pattern Sz.xi B0 (i • Sz.u), ⟨i, rfl⟩, ?_⟩
        funext l
        show Sz.xi (i • Sz.u + (w_row t + (l : ℕ) • Sz.u))
            = Sz.xi (w_row t + ((i : ℤ) + (l : ℕ)) • Sz.u)
        congr 1
        module
      · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
        refine ⟨i, ?_⟩
        funext l
        show Sz.xi (w_row t + ((i : ℤ) + (l : ℕ)) • Sz.u)
            = Sz.xi (i • Sz.u + (w_row t + (l : ℕ) • Sz.u))
        congr 1
        module
    rw [hsubword_eq]
    calc (windowMap '' Γ).ncard ≤ Γ.ncard := Set.ncard_image_le hGammafin
      _ = ΓF.card := Set.ncard_eq_toFinset_card Γ hGammafin
      _ ≤ n - 1 := by have := hGammaBound; omega
  -- Morse–Hedlund gives each row `t ∈ [t_, b - 1]` a period `q_t > 0`.
  have hrow_period : ∀ t : ℤ, t_ ≤ t → t ≤ b - 1 →
      ∃ q : ℕ, 0 < q ∧ ∀ i : ℤ, xirow t (i + q) = xirow t i :=
    fun t htlo hthi => periodic_of_subwords_le (xirow t) (by omega) (hsubword_bound t htlo hthi)
  choose! q_row hq_row_pos hq_row using hrow_period
  -- A period is a period under any positive integer multiple.
  have hxirow_mul : ∀ t : ℤ, t_ ≤ t → t ≤ b - 1 → ∀ (c : ℕ) (i : ℤ),
      xirow t (i + (c : ℤ) * (q_row t : ℤ)) = xirow t i := by
    intro t htlo hthi c
    induction c with
    | zero => intro i; simp
    | succ c ih =>
      intro i
      have e : i + (((c : ℕ) + 1 : ℕ) : ℤ) * (q_row t : ℤ)
          = (i + (c : ℤ) * (q_row t : ℤ)) + (q_row t : ℤ) := by push_cast; ring
      rw [e, hq_row t htlo hthi, ih]
  -- `Q0`, a common multiple of the row periods on `[t_, b - 1]`.
  set Q0 : ℕ := ∏ t ∈ Finset.Icc t_ (b - 1), q_row t with hQ0_def
  have hQ0dvd : ∀ t ∈ Finset.Icc t_ (b - 1), q_row t ∣ Q0 :=
    fun t ht => Finset.dvd_prod_of_mem q_row ht
  have hQ0pos : 0 < Q0 := by
    rw [hQ0_def]
    apply Finset.prod_pos
    intro t ht
    rw [Finset.mem_Icc] at ht
    exact hq_row_pos t ht.1 ht.2
  have hrow_periodQ0 : ∀ t : ℤ, t_ ≤ t → t ≤ b - 1 → ∀ i : ℤ, xirow t (i + Q0) = xirow t i := by
    intro t htlo hthi i
    obtain ⟨c, hc⟩ := hQ0dvd t (Finset.mem_Icc.mpr ⟨htlo, hthi⟩)
    have hcast : (Q0 : ℤ) = (c : ℤ) * (q_row t : ℤ) := by rw [hc]; push_cast; ring
    rw [hcast]
    exact hxirow_mul t htlo hthi c i
  -- Step (5)'s conclusion: `ξ(v + Q0 • u) = ξ(v)` for all `v` in the strip `St[t_, b - 1]`.
  have hstep5 : ∀ v : ℤ × ℤ, v ∈ Sz.strip t_ (b - 1) → Sz.xi (v + (Q0 : ℤ) • Sz.u) = Sz.xi v := by
    intro v hv
    obtain ⟨hvlo, hvhi⟩ := hv
    obtain ⟨s, hs⟩ := Sz.exists_zsmul_of_phi_eq (z := v) (w := w_row (Sz.phi v))
      (hphi_w_row (Sz.phi v) hvlo hvhi).symm
    have heq1 : Sz.xi (v + (Q0 : ℤ) • Sz.u) = xirow (Sz.phi v) (s + Q0) := by
      show Sz.xi (v + (Q0 : ℤ) • Sz.u) = Sz.xi (w_row (Sz.phi v) + (s + (Q0 : ℤ)) • Sz.u)
      nth_rewrite 1 [hs]
      congr 1
      module
    rw [heq1, hrow_periodQ0 (Sz.phi v) hvlo hvhi s]
    show Sz.xi (w_row (Sz.phi v) + s • Sz.u) = Sz.xi v
    exact congrArg Sz.xi hs.symm
  -- Step (6)-(7).  If `Δ < b - t_`, the strip `St[t_, b-1]` from (5) already contains
  -- `St[t_, t_+Δ]`; otherwise extend the period upwards one row at a time.
  by_cases hcase : Sz.Delta < b - t_
  · have hstripQ0 : ∀ v ∈ Sz.strip t_ (t_ + Sz.Delta), Sz.xi (v + (Q0 : ℤ) • Sz.u) = Sz.xi v := by
      intro v hv
      obtain ⟨hvlo, hvhi⟩ := hv
      exact hstep5 v ⟨hvlo, by omega⟩
    have hperQ : (Q0 : ℤ) • Sz.h1 ∈ Per Sz.xi :=
      Sz.period_of_strip (a := t_) (b := t_ + Sz.Delta) (by omega) (by exact_mod_cast hQ0pos)
        hstripQ0
    refine ⟨(Q0 : ℤ) • Sz.h1, hperQ, ?_⟩
    intro hcontra
    have hQ0ne : (Q0 : ℤ) ≠ 0 := by exact_mod_cast hQ0pos.ne'
    exact Sz.h1_ne_zero ((smul_eq_zero.mp hcontra).resolve_left hQ0ne)
  · -- hard case: `Δ ≥ b - t_`.
    -- One step of Step (6): given period `Q` (a multiple of `Q0`) on `St[t_, R-1]` with `R ≥ b`,
    -- produce a period `Q'` (again a multiple of `Q0`) on `St[t_, R]`.
    have hrow_ext : ∀ R : ℤ, b ≤ R → ∀ Q : ℕ, 0 < Q → Q0 ∣ Q →
        (∀ v ∈ Sz.strip t_ (R - 1), Sz.xi (v + (Q : ℤ) • Sz.u) = Sz.xi v) →
        ∃ Q' : ℕ, 0 < Q' ∧ Q0 ∣ Q' ∧
          ∀ v ∈ Sz.strip t_ R, Sz.xi (v + (Q' : ℤ) • Sz.u) = Sz.xi v := by
      intro R hR Q hQpos hQ0Q hQstrip
      -- Place a translate `Bw` of `B` with its top row on `L_R`.
      obtain ⟨w1, hw1⟩ := Sz.phi_surjective (R - b)
      set Bw : Finset (ℤ × ℤ) := B.image (· + w1) with hBw_def
      have hBwtop : Sz.topIdx Bw = R := by
        rw [hBw_def, Sz.topIdx_add hB.nonempty, hw1, htop]; ring
      have hBwbot : Sz.botIdx Bw = t_ + (R - b) := by
        rw [hBw_def, Sz.botIdx_add hB.nonempty, hw1, ht_def]
      have hBwbal : Sz.Balanced true Bw := Balanced.translate Sz hB w1
      -- Mirror the placement of `B` at its own top row: the top row `Ew` of `Bw`, and the two
      -- determination rules there.
      set Ew : Finset (ℤ × ℤ) := Bw.filter fun z => Sz.phi z = R with hEw_def
      have hEwside_eq : Sz.Eside true Bw = Ew := by
        rw [hEw_def]
        have h0 : Sz.Eside true Bw = Bw.filter fun z => Sz.phi z = Sz.topIdx Bw := by
          simp [Eside, Etop]
        rw [h0, hBwtop]
      have hEwne : Ew.Nonempty := by
        rw [hEw_def, ← hBwtop]
        simpa [Etop] using Sz.Etop_nonempty hBwbal.nonempty
      have hdeficitw : P Sz.xi Bw < P Sz.xi (Bw \ Ew) + Ew.card := by
        have hd := hBwbal.deficit; rwa [hEwside_eq] at hd
      obtain ⟨w_f, m_f, k_f, hm_fpos, hk_fm, hEweqRun, hCsub_f, heEw_f, hdetR⟩ :=
        Sz.exists_forward_rule_aux hBwbal.latticeConvex hEw_def hEwne hdeficitw
      obtain ⟨w_b, m_b, k_b, hm_bpos, hk_bm, hEweqRun', hCsub_b, heEw_b, hdetR'⟩ :=
        Sz.exists_backward_rule_aux hBwbal.latticeConvex hEw_def hEwne hdeficitw
      -- Both run-endpoints lie on row `R`, and are related by an offset `t0`.
      have hphiwf : Sz.phi w_f = R := by
        have h2 : Sz.phi (w_f + (k_f : ℤ) • Sz.u) = R := by
          rw [hEw_def, Finset.mem_filter] at heEw_f; exact heEw_f.2
        rwa [Sz.phi_add, Sz.phi_smul, Sz.phi_u, mul_zero, add_zero] at h2
      have hphiwb : Sz.phi w_b = R := by
        have h2 : Sz.phi (w_b + (k_b : ℤ) • (-Sz.u)) = R := by
          rw [hEw_def, Finset.mem_filter] at heEw_b; exact heEw_b.2
        rwa [Sz.phi_add, Sz.phi_smul, Sz.phi_neg, Sz.phi_u, neg_zero, mul_zero, add_zero] at h2
      obtain ⟨t0, ht0⟩ := Sz.exists_zsmul_of_phi_eq (z := w_b) (w := w_f) (hphiwb.trans hphiwf.symm)
      -- Rows of `Bw` other than `R` sit in the strip `St[t_, R-1]`.
      have hBwEwstrip : ∀ z ∈ Bw \ Ew, z ∈ Sz.strip t_ (R - 1) := by
        intro z hz
        have hz' : z ∈ Bw ∧ Sz.phi z ≠ R := by
          rw [Finset.mem_sdiff, hEw_def, Finset.mem_filter] at hz
          exact ⟨hz.1, fun h => hz.2 ⟨hz.1, h⟩⟩
        have h1 : Sz.phi z ≤ R := hBwtop ▸ Sz.phi_le_topIdx hz'.1
        have h2 : t_ ≤ Sz.phi z := by
          have := Sz.botIdx_le_phi hz'.1
          rw [hBwbot] at this
          omega
        exact ⟨h2, by omega⟩
      -- The period `Q` on `St[t_, R-1]` extends to every integer multiple, both directions.
      have hstrip_period_mul : ∀ v ∈ Sz.strip t_ (R - 1), ∀ c : ℤ,
          Sz.xi (v + (c * (Q : ℤ)) • Sz.u) = Sz.xi v := by
        intro v hv c
        induction c using Int.induction_on with
        | zero => simp
        | succ i ih =>
          have hvi : v + ((i : ℤ) * (Q : ℤ)) • Sz.u ∈ Sz.strip t_ (R - 1) :=
            Sz.add_zsmul_u_mem_strip hv _
          have hstep := hQstrip _ hvi
          have e : v + (((i : ℤ) + 1) * (Q : ℤ)) • Sz.u
              = (v + ((i : ℤ) * (Q : ℤ)) • Sz.u) + (Q : ℤ) • Sz.u := by module
          rw [e, hstep]
          exact ih
        | pred i ih =>
          set w0 : ℤ × ℤ := v + (-(i : ℤ) * (Q : ℤ)) • Sz.u with hw0_def
          have e : v + ((-(i : ℤ) - 1) * (Q : ℤ)) • Sz.u = w0 - (Q : ℤ) • Sz.u := by
            rw [hw0_def]; module
          have hw0mem : w0 - (Q : ℤ) • Sz.u ∈ Sz.strip t_ (R - 1) := by
            have h := Sz.add_zsmul_u_mem_strip hv ((-(i : ℤ) - 1) * (Q : ℤ))
            rwa [e] at h
          have hstep := hQstrip _ hw0mem
          have e2 : w0 - (Q : ℤ) • Sz.u + (Q : ℤ) • Sz.u = w0 := by module
          rw [e2] at hstep
          rw [e, ← hstep]
          exact ih
      -- Consequently `ξ` agrees on translates of any point of `Bw \ Ew` by congruent multiples
      -- of `u` modulo `Q`.
      have hBw_agree_mul : ∀ z ∈ Bw \ Ew, ∀ i j : ℤ, (i : ZMod Q) = (j : ZMod Q) →
          Sz.xi (z + i • Sz.u) = Sz.xi (z + j • Sz.u) := by
        intro z hz i j hij
        have hzstrip : z ∈ Sz.strip t_ (R - 1) := hBwEwstrip z hz
        obtain ⟨d, hd⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub i j Q).mp hij
        have hzi : z + i • Sz.u ∈ Sz.strip t_ (R - 1) := Sz.add_zsmul_u_mem_strip hzstrip i
        have hres := hstrip_period_mul (z + i • Sz.u) hzi d
        have e : z + i • Sz.u + (d * (Q : ℤ)) • Sz.u = z + j • Sz.u := by
          have hj : j = i + d * (Q : ℤ) := by rw [mul_comm] at hd; omega
          rw [hj]; module
        rw [e] at hres
        exact hres.symm
      -- The row-word `y_s := ξ(w_f + s•u)`, and a common window length `K` for both rules.
      set yR : ℤ → ZMod p := fun s => Sz.xi (w_f + s • Sz.u) with hyR_def
      set K : ℕ := max (max k_f k_b) 1 with hK_def
      have hKpos : 0 < K := lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
      have hKf : k_f ≤ K := le_trans (le_max_left k_f k_b) (le_max_left _ _)
      have hKb : k_b ≤ K := le_trans (le_max_right k_f k_b) (le_max_left _ _)
      have hfwd : ∀ i j : ℤ, (i : ZMod Q) = (j : ZMod Q) →
          (∀ l : ℕ, l < K → yR (i + l) = yR (j + l)) → yR (i + K) = yR (j + K) := by
        intro i j hij hwin
        set v : ℤ × ℤ := (i + ((K : ℤ) - (k_f : ℤ))) • Sz.u with hv_def
        set w0 : ℤ × ℤ := (j + ((K : ℤ) - (k_f : ℤ))) • Sz.u with hw0_def
        have hphase : ((i + ((K : ℤ) - (k_f : ℤ)) : ℤ) : ZMod Q)
            = ((j + ((K : ℤ) - (k_f : ℤ)) : ℤ) : ZMod Q) := by push_cast; rw [hij]
        have hbase : ∀ c ∈ (Bw \ Ew) ∪ (Finset.range k_f).image (fun s : ℕ => w_f + (s:ℤ)•Sz.u),
            Sz.xi (v + c) = Sz.xi (w0 + c) := by
          intro c hc
          rw [Finset.mem_union] at hc
          rcases hc with hcB | hcE
          · rw [add_comm v c, add_comm w0 c]
            exact hBw_agree_mul c hcB _ _ hphase
          · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hcE
            rw [Finset.mem_range] at hs
            set l : ℕ := K - k_f + s with hl_def
            have hlK : l < K := by omega
            have hlcast : (l : ℤ) = (K : ℤ) - (k_f : ℤ) + (s : ℤ) := by
              have hKf' : (k_f : ℤ) ≤ (K : ℤ) := by exact_mod_cast hKf
              rw [hl_def]; push_cast; omega
            have e1 : v + (w_f + (s : ℤ) • Sz.u) = w_f + (i + (l : ℤ)) • Sz.u := by
              rw [hv_def, hlcast]; module
            have e2 : w0 + (w_f + (s : ℤ) • Sz.u) = w_f + (j + (l : ℤ)) • Sz.u := by
              rw [hw0_def, hlcast]; module
            rw [e1, e2]
            exact hwin l hlK
        have hres := hdetR Sz.xi (self_mem_orbitClosure Sz.xi) Sz.xi (self_mem_orbitClosure Sz.xi)
          v w0 hbase
        have e5 : v + (w_f + (k_f : ℤ) • Sz.u) = w_f + (i + (K : ℤ)) • Sz.u := by
          rw [hv_def]; module
        have e6 : w0 + (w_f + (k_f : ℤ) • Sz.u) = w_f + (j + (K : ℤ)) • Sz.u := by
          rw [hw0_def]; module
        rw [e5, e6] at hres
        exact hres
      have hbwd : ∀ i j : ℤ, (i : ZMod Q) = (j : ZMod Q) →
          (∀ l : ℕ, l < K → yR (i + l) = yR (j + l)) → yR (i - 1) = yR (j - 1) := by
        intro i j hij hwin
        set i'' : ℤ := i - 1 - t0 + (k_b : ℤ) with hi''_def
        set j'' : ℤ := j - 1 - t0 + (k_b : ℤ) with hj''_def
        set v : ℤ × ℤ := i'' • Sz.u with hv_def
        set w0 : ℤ × ℤ := j'' • Sz.u with hw0_def
        have hd : (Q : ℤ) ∣ (j - i) := (ZMod.intCast_eq_intCast_iff_dvd_sub i j Q).mp hij
        have hphase : (i'' : ZMod Q) = (j'' : ZMod Q) := by
          have hdiff : j'' - i'' = j - i := by rw [hi''_def, hj''_def]; ring
          have hd' : (Q : ℤ) ∣ (j'' - i'') := by rw [hdiff]; exact hd
          exact (ZMod.intCast_eq_intCast_iff_dvd_sub i'' j'' Q).mpr hd'
        have hbase : ∀ c ∈ (Bw \ Ew) ∪ (Finset.range k_b).image (fun s : ℕ => w_b + (s:ℤ)•(-Sz.u)),
            Sz.xi (v + c) = Sz.xi (w0 + c) := by
          intro c hc
          rw [Finset.mem_union] at hc
          rcases hc with hcB | hcE
          · rw [add_comm v c, add_comm w0 c]
            exact hBw_agree_mul c hcB _ _ hphase
          · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hcE
            rw [Finset.mem_range] at hs
            set l : ℕ := k_b - 1 - s with hl_def
            have hlK : l < K := by omega
            have hlcast : (l : ℤ) = (k_b : ℤ) - 1 - (s : ℤ) := by
              have hsb : (s : ℤ) < (k_b : ℤ) := by exact_mod_cast hs
              rw [hl_def]; omega
            have e1 : v + (w_b + (s : ℤ) • (-Sz.u)) = w_f + (i + (l : ℤ)) • Sz.u := by
              rw [hv_def, hi''_def, ht0, hlcast]; module
            have e2 : w0 + (w_b + (s : ℤ) • (-Sz.u)) = w_f + (j + (l : ℤ)) • Sz.u := by
              rw [hw0_def, hj''_def, ht0, hlcast]; module
            rw [e1, e2]
            exact hwin l hlK
        have hres := hdetR' Sz.xi (self_mem_orbitClosure Sz.xi) Sz.xi (self_mem_orbitClosure Sz.xi)
          v w0 hbase
        have e5 : v + (w_b + (k_b : ℤ) • (-Sz.u)) = w_f + (i - 1) • Sz.u := by
          rw [hv_def, hi''_def, ht0]; module
        have e6 : w0 + (w_b + (k_b : ℤ) • (-Sz.u)) = w_f + (j - 1) • Sz.u := by
          rw [hw0_def, hj''_def, ht0]; module
        rw [e5, e6] at hres
        exact hres
      obtain ⟨Q', hQ'pos, hQdvdQ', hyRper⟩ :=
        periodic_of_two_sided_determinacy hQpos hKpos yR hfwd hbwd
      refine ⟨Q', hQ'pos, hQ0Q.trans hQdvdQ', ?_⟩
      intro v hv
      obtain ⟨hvlo, hvhi⟩ := hv
      by_cases hvR : Sz.phi v = R
      · obtain ⟨s, hs⟩ := Sz.exists_zsmul_of_phi_eq (z := v) (w := w_f) (hvR.trans hphiwf.symm)
        show Sz.xi (v + (Q' : ℤ) • Sz.u) = Sz.xi v
        have heq1 : Sz.xi (v + (Q' : ℤ) • Sz.u) = yR (s + Q') := by
          show Sz.xi (v + (Q' : ℤ) • Sz.u) = Sz.xi (w_f + (s + (Q' : ℤ)) • Sz.u)
          nth_rewrite 1 [hs]
          congr 1
          module
        rw [heq1, hyRper s]
        show Sz.xi (w_f + s • Sz.u) = Sz.xi v
        exact congrArg Sz.xi hs.symm
      · have hvstrip : v ∈ Sz.strip t_ (R - 1) := ⟨hvlo, by omega⟩
        obtain ⟨d, hd⟩ := hQdvdQ'
        have hcast : (Q' : ℤ) = (d : ℤ) * (Q : ℤ) := by rw [hd]; push_cast; ring
        show Sz.xi (v + (Q' : ℤ) • Sz.u) = Sz.xi v
        rw [hcast]
        exact hstrip_period_mul v hvstrip (d : ℤ)
    -- Iterate `hrow_ext` from `R = b - 1` (base: `hstep5`/`Q0`) up to `R = t_ + Δ`.
    have hmain : ∀ R : ℤ, b - 1 ≤ R → ∃ Q : ℕ, 0 < Q ∧ Q0 ∣ Q ∧
        ∀ v ∈ Sz.strip t_ R, Sz.xi (v + (Q : ℤ) • Sz.u) = Sz.xi v := by
      intro R hR
      induction R, hR using Int.leInduction with
      | base => exact ⟨Q0, hQ0pos, dvd_refl Q0, hstep5⟩
      | succ R hR ih =>
        obtain ⟨Q, hQpos, hQ0Q, hQstrip⟩ := ih
        have hbR : b ≤ R + 1 := by omega
        have heq : R + 1 - 1 = R := by ring
        exact hrow_ext (R + 1) hbR Q hQpos hQ0Q (by simpa [heq] using hQstrip)
    obtain ⟨Qstar, hQstarpos, -, hQstarstrip⟩ := hmain (t_ + Sz.Delta) (by omega)
    have hperQ : (Qstar : ℤ) • Sz.h1 ∈ Per Sz.xi :=
      Sz.period_of_strip (a := t_) (b := t_ + Sz.Delta) (by omega) (by exact_mod_cast hQstarpos)
        hQstarstrip
    refine ⟨(Qstar : ℤ) • Sz.h1, hperQ, ?_⟩
    intro hcontra
    have hQstarne : (Qstar : ℤ) ≠ 0 := by exact_mod_cast hQstarpos.ne'
    exact Sz.h1_ne_zero ((smul_eq_zero.mp hcontra).resolve_left hQstarne)

/-- **Lemma D.7 (Propagation).**  Let `B` be `+`-balanced.  If `ξ` has a `+`-ambiguity strip
`St[a, b]` into which `B` fits, that is with `b - a ≥ ht(B)`, then `ξ` is periodic.

The proof places `B` with its top row on `L_b` (`isPeriodic_of_ambiguityStrip_aux`, step (1)),
uses the two determination rules of `exists_forward_rule_aux`/`exists_backward_rule_aux` to
propagate the witness sideways (step (3)), counts the extensions of the patterns of `B₀`
(step (4)), derives periodicity of each row of `B₀` from the one-dimensional Morse–Hedlund
theorem (step (5)), extends upwards one row at a time by the finite-state argument
`periodic_of_two_sided_determinacy` (step (6)), and concludes by Lemma D.3 (step (7)). -/
theorem isPeriodic_of_ambiguityStrip [Fact p.Prime] {B : Finset (ℤ × ℤ)}
    (hB : Sz.Balanced true B) {a b : ℤ} (hamb : Sz.AmbiguityStrip a b)
    (hfit : Sz.ht B ≤ b - a) : IsPeriodic Sz.xi := by
  obtain ⟨v, hv⟩ := Sz.phi_surjective (b - Sz.topIdx B)
  have htop' : Sz.topIdx (B.image (· + v)) = b := by
    rw [Sz.topIdx_add hB.nonempty, hv]; ring
  have hht' : Sz.ht (B.image (· + v)) ≤ b - a := by
    rw [Sz.ht_add hB.nonempty]; exact hfit
  exact Sz.isPeriodic_of_ambiguityStrip_aux (Balanced.translate Sz hB v) htop' hamb hht'


/-! ### §D.5 Proof of Theorem D.1 -/

/-- **(D.2).**  The contrapositive of Lemma D.7, iterated row by row: if `ξ` is not periodic and
`B` is `+`-balanced, then agreement with `ξ` on a strip of width at least `ht(B) - 1` propagates
to the whole upper half-plane. -/
theorem agree_of_agree_strip [Fact p.Prime] {B : Finset (ℤ × ℤ)} (hB : Sz.Balanced true B)
    (hnp : ¬ IsPeriodic Sz.xi) {a b : ℤ} (hab : Sz.ht B - 1 ≤ b - a)
    {x : Config (ZMod p)} (hx : x ∈ orbitClosure Sz.xi)
    (hagree : ∀ v ∈ Sz.strip a b, x v = Sz.xi v) :
    ∀ v : ℤ × ℤ, a ≤ Sz.phi v → x v = Sz.xi v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v0, hv0a, hv0ne⟩ := hcon
  -- `v0` lies strictly above row `b`, since `x` and `ξ` agree on `St[a, b]`.
  have hv0b : b < Sz.phi v0 := by
    by_contra h
    push Not at h
    exact hv0ne (hagree v0 (Sz.mem_strip_iff.mpr ⟨hv0a, h⟩))
  -- The least row above `b` on which `x` and `ξ` disagree, using `Int.exists_least_of_bdd`.
  have hbdd : ∃ c : ℤ, ∀ z : ℤ, (b < z ∧ ∃ v, Sz.phi v = z ∧ x v ≠ Sz.xi v) → c ≤ z :=
    ⟨b + 1, fun z hz => hz.1⟩
  have hinh : ∃ z : ℤ, b < z ∧ ∃ v, Sz.phi v = z ∧ x v ≠ Sz.xi v :=
    ⟨Sz.phi v0, hv0b, v0, rfl, hv0ne⟩
  obtain ⟨t, ⟨htb, v1, hv1phi, hv1ne⟩, hmin⟩ := Int.exists_least_of_bdd hbdd hinh
  -- `a ≤ b + 1`, from `hab` and the non-negativity of `ht B`; hence `a ≤ t`.
  have haB : a ≤ b + 1 := by
    have := Sz.ht_nonneg hB.nonempty
    omega
  have hat : a ≤ t := by omega
  -- `x` agrees with `ξ` on `St[a, t - 1]`: on `St[a, b]` by `hagree`, and above `b` by
  -- minimality of `t`.
  have hagree' : ∀ v ∈ Sz.strip a (t - 1), x v = Sz.xi v := by
    intro v hv
    rw [Sz.mem_strip_iff] at hv
    by_contra hne
    by_cases h : Sz.phi v ≤ b
    · exact hne (hagree v (Sz.mem_strip_iff.mpr ⟨hv.1, h⟩))
    · push Not at h
      have : t ≤ Sz.phi v := hmin _ ⟨h, v, rfl, hne⟩
      omega
  have hamb : Sz.AmbiguityStrip a t := ⟨hat, x, hx, hagree', v1, hv1phi, hv1ne⟩
  have hfit : Sz.ht B ≤ t - a := by omega
  exact hnp (Sz.isPeriodic_of_ambiguityStrip hB hamb hfit)

/-- Covering set for §D.5: a set `D` of representatives of `St[0, Δ-1]` modulo `ℤh₁`, built from
one preimage `w t` per row `t` (via surjectivity of `φ`) and one residue mod `c₁` per row (since
`ℤh₁`-cosets inside a row correspond to `u`-offset residues mod `c₁`). -/
private theorem exists_covering_set [Fact p.Prime] :
    ∃ D : Finset (ℤ × ℤ), ∀ j : ℤ, ∀ v : ℤ × ℤ,
      Sz.phi v ∈ Set.Icc (j * Sz.Delta) ((j + 1) * Sz.Delta - 1) →
      ∃ e ∈ D, ∃ n : ℤ, v = e + j • Sz.h2 + n • Sz.h1 := by
  choose w hw using Sz.phi_surjective
  set Δn : ℕ := Sz.Delta.toNat with hΔn_def
  refine ⟨(Finset.range Δn ×ˢ Finset.range Sz.c₁).image
    (fun q => w (q.1 : ℤ) + (q.2 : ℤ) • Sz.u), fun j v hv => ?_⟩
  simp only [Set.mem_Icc] at hv
  set v' : ℤ × ℤ := v - j • Sz.h2 with hv'_def
  have hphiv' : Sz.phi v' = Sz.phi v - j * Sz.Delta := by
    rw [hv'_def, sub_eq_add_neg, ← neg_smul, Sz.phi_add, Sz.phi_smul,
      show Sz.phi Sz.h2 = Sz.Delta from rfl]
    ring
  have hexp : (j + 1) * Sz.Delta = j * Sz.Delta + Sz.Delta := by ring
  have ht0 : 0 ≤ Sz.phi v' := by rw [hphiv']; omega
  have ht1 : Sz.phi v' < Sz.Delta := by rw [hphiv']; omega
  obtain ⟨s, hs⟩ := Sz.exists_zsmul_of_phi_eq (z := v') (w := w (Sz.phi v')) (hw _).symm
  obtain ⟨n, r, hr0, hr1, hs_eq⟩ :
      ∃ n r : ℤ, 0 ≤ r ∧ r < (Sz.c₁ : ℤ) ∧ s = (Sz.c₁ : ℤ) * n + r :=
    ⟨s / (Sz.c₁ : ℤ), s % (Sz.c₁ : ℤ), Int.emod_nonneg _ (by exact_mod_cast Sz.c₁_pos.ne'),
      Int.emod_lt_of_pos _ (by exact_mod_cast Sz.c₁_pos),
      (Int.mul_ediv_add_emod s (Sz.c₁ : ℤ)).symm⟩
  refine ⟨w (Sz.phi v') + r • Sz.u, ?_, n, ?_⟩
  · refine Finset.mem_image.mpr ⟨((Sz.phi v').toNat, r.toNat), ?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩
      · rw [hΔn_def]; omega
      · omega
    · have h1 : ((Sz.phi v').toNat : ℤ) = Sz.phi v' := Int.toNat_of_nonneg ht0
      have h2 : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
      rw [h1, h2]
  · have hv_eq : v = v' + j • Sz.h2 := by rw [hv'_def]; abel
    have hh1 : Sz.h1 = (Sz.c₁ : ℤ) • Sz.u := rfl
    -- Substitute for `v'` only on the left, so `hs` doesn't also rewrite the `v'` hidden
    -- inside `w (Sz.phi v')` on the right (which would loop back on itself).
    have hvw : v = w (Sz.phi v') + s • Sz.u + j • Sz.h2 := by
      conv_lhs => rw [hv_eq, hs]
    rw [hvw, hs_eq, hh1, smul_smul]
    have hcomb : ((Sz.c₁:ℤ)*n+r) • Sz.u = r • Sz.u + (n*(Sz.c₁:ℤ)) • Sz.u := by
      rw [← add_smul]; congr 1; ring
    rw [hcomb]
    abel

/-- The core of Theorem D.1's proof (§D.5, normalised so `Δ ≥ ht(B) + 1`, `ε = true`): a
`+`-balanced set `B` fitting inside a single row-band of width `Δ` forces `ξ` to be periodic. -/
private theorem xi_isPeriodic_core [Fact p.Prime] {B : Finset (ℤ × ℤ)}
    (hbal : Sz.Balanced true B) (hnp : ¬ IsPeriodic Sz.xi)
    (hfit : Sz.ht B + 1 ≤ Sz.Delta) : False := by
  obtain ⟨D, hcover⟩ := Sz.exists_covering_set
  set N : ℕ := (patterns Sz.xi D).ncard with hN_def
  -- Step (b): since `ξ` is not periodic, `N! h₂` is not a period, giving a witness `v₀`.
  have hh2ne : Sz.h2 ≠ 0 := by
    intro h
    have hD : (0:ℤ) < Sz.Delta := Sz.Delta_pos
    have hDeq : Sz.Delta = Sz.phi Sz.h2 := rfl
    have hz : Sz.phi (0:ℤ×ℤ) = 0 := by
      have h0 := Sz.phi_add (0:ℤ×ℤ) 0
      simp only [add_zero] at h0
      omega
    rw [hDeq, h, hz] at hD
    exact lt_irrefl 0 hD
  have hNfacne : ((N.factorial : ℤ)) • Sz.h2 ≠ 0 := by
    simp only [ne_eq, smul_eq_zero, Nat.cast_eq_zero, Nat.factorial_ne_zero, false_or]
    exact hh2ne
  have hnotper : (N.factorial : ℤ) • Sz.h2 ∉ Per Sz.xi := fun h => hnp ⟨_, h, hNfacne⟩
  rw [mem_Per_iff] at hnotper
  have hv0 : ∃ v0 : ℤ × ℤ, Sz.xi (v0 + (N.factorial : ℤ) • Sz.h2) ≠ Sz.xi v0 := by
    by_contra hc
    push Not at hc
    exact hnotper (funext hc)
  obtain ⟨v0, hv0⟩ := hv0
  -- Choose `k` so that even the highest shift `k + N` still sits at or below `v₀`'s row.
  set k : ℤ := Sz.phi v0 / Sz.Delta - (N : ℤ) with hk_def
  have hb0N : (k + (N : ℤ)) * Sz.Delta ≤ Sz.phi v0 := by
    have hmod : (0:ℤ) ≤ Sz.phi v0 % Sz.Delta := Int.emod_nonneg _ Sz.Delta_pos.ne'
    have hdiv := Int.mul_ediv_add_emod (Sz.phi v0) Sz.Delta
    have hkk : k + (N:ℤ) = Sz.phi v0 / Sz.Delta := by rw [hk_def]; ring
    rw [hkk]
    nlinarith [hdiv, hmod]
  -- Step (c): pigeonhole `N + 1` shifts of the `D`-pattern into the `N`-element set of `D`-patterns.
  have htgt_finite : (patterns Sz.xi D).Finite := patterns_finite Sz.xi D
  have hlt : (patterns Sz.xi D).ncard < ((Finset.range (N+1) : Finset ℕ) : Set ℕ).ncard := by
    rw [Set.ncard_coe_finset, Finset.card_range]
    exact Nat.lt_succ_self N
  have hmaps : ∀ j ∈ ((Finset.range (N+1) : Finset ℕ) : Set ℕ),
      pattern Sz.xi D ((k + (j : ℤ)) • Sz.h2) ∈ patterns Sz.xi D :=
    fun j _ => ⟨(k + (j : ℤ)) • Sz.h2, rfl⟩
  obtain ⟨j0, hj0, j0', hj0', hne, heqpat⟩ :=
    Set.exists_ne_map_eq_of_ncard_lt_of_maps_to hlt hmaps htgt_finite
  simp only [Finset.mem_coe, Finset.mem_range] at hj0 hj0'
  -- normalise so `j0 < j0'`
  obtain ⟨j0, j0', hj0N, hj0'N, hne, heqpat⟩ :
      ∃ j0 j0' : ℕ, j0 < N + 1 ∧ j0' < N + 1 ∧ j0 < j0' ∧
        pattern Sz.xi D ((k + (j0 : ℤ)) • Sz.h2) = pattern Sz.xi D ((k + (j0' : ℤ)) • Sz.h2) := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨j0, j0', hj0, hj0', h, heqpat⟩
    · exact ⟨j0', j0, hj0', hj0, h, heqpat.symm⟩
  set d : ℕ := j0' - j0 with hd_def
  have hd_pos : 0 < d := by omega
  have hd_le : d ≤ N := by omega
  obtain ⟨m, hm⟩ : d ∣ N.factorial := Nat.dvd_factorial hd_pos (by omega)
  -- `T^{d h₂} ξ` agrees with `ξ` on `D` shifted by `(k + j0) h₂`, hence on the whole strip.
  have hbase : ∀ e ∈ D,
      Sz.xi ((k + (j0:ℤ)) • Sz.h2 + e + (d:ℤ) • Sz.h2) = Sz.xi ((k + (j0:ℤ)) • Sz.h2 + e) := by
    intro e he
    have h1 := congrFun heqpat ⟨e, he⟩
    simp only [pattern] at h1
    have h2 : (k + (j0':ℤ)) • Sz.h2 = (k + (j0:ℤ)) • Sz.h2 + (d:ℤ) • Sz.h2 := by
      rw [← add_smul]; congr 1; rw [hd_def]; omega
    rw [h2] at h1
    have h3 : (k + (j0:ℤ)) • Sz.h2 + e + (d:ℤ) • Sz.h2
        = (k + (j0:ℤ)) • Sz.h2 + (d:ℤ) • Sz.h2 + e := by abel
    rw [h3]
    exact h1.symm
  have hstripAgree : ∀ v ∈ Sz.strip ((k+(j0:ℤ))*Sz.Delta) ((k+(j0:ℤ)+1)*Sz.Delta - 1),
      Sz.xi (v + (d:ℤ) • Sz.h2) = Sz.xi v := by
    intro v hv
    rw [Sz.mem_strip_iff] at hv
    obtain ⟨e, he, n, hn⟩ := hcover (k + (j0:ℤ)) v (Set.mem_Icc.mpr hv)
    set V : ℤ × ℤ := e + (k + (j0:ℤ)) • Sz.h2 with hV_def
    have hbaseV : Sz.xi (V + (d:ℤ) • Sz.h2) = Sz.xi V := by
      rw [hV_def, add_comm e ((k+(j0:ℤ))•Sz.h2)]
      exact hbase e he
    have key := Sz.xi_sub_h1_periodic (d:ℤ) n V
    rw [sub_eq_zero.mpr hbaseV] at key
    have hkey : Sz.xi (V + n • Sz.h1 + (d:ℤ) • Sz.h2) = Sz.xi (V + n • Sz.h1) :=
      sub_eq_zero.mp key
    rw [hn]
    exact hkey
  have hab' : Sz.ht B - 1 ≤ ((k+(j0:ℤ)+1)*Sz.Delta - 1) - (k+(j0:ℤ))*Sz.Delta := by
    have : ((k+(j0:ℤ)+1)*Sz.Delta - 1) - (k+(j0:ℤ))*Sz.Delta = Sz.Delta - 1 := by ring
    omega
  have hshift : ∀ v : ℤ × ℤ, (k+(j0:ℤ))*Sz.Delta ≤ Sz.phi v →
      Sz.xi (v + (d:ℤ) • Sz.h2) = Sz.xi v :=
    Sz.agree_of_agree_strip hbal hnp hab'
      (T_mem_orbitClosure Sz.xi ((d:ℤ) • Sz.h2)) hstripAgree
  -- Iterate the shift `m` times to reach `N! h₂` from `v₀`, contradicting `hv0`.
  have hb0 : (k+(j0:ℤ))*Sz.Delta ≤ Sz.phi v0 := by
    have hmono : (k+(j0:ℤ))*Sz.Delta ≤ (k+(N:ℤ))*Sz.Delta :=
      mul_le_mul_of_nonneg_right (by omega) (le_of_lt Sz.Delta_pos)
    omega
  have hiter : ∀ i : ℕ, (k+(j0:ℤ))*Sz.Delta ≤ Sz.phi v0 →
      Sz.xi (v0 + ((i:ℤ)*(d:ℤ)) • Sz.h2) = Sz.xi v0 := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hbound
      have hprev := ih hbound
      have hphi_add : Sz.phi (v0 + ((i:ℤ)*(d:ℤ)) • Sz.h2) = Sz.phi v0 + (i:ℤ)*(d:ℤ) * Sz.Delta := by
        rw [Sz.phi_add, Sz.phi_smul, show Sz.phi Sz.h2 = Sz.Delta from rfl]
      have hge : (k+(j0:ℤ))*Sz.Delta ≤ Sz.phi (v0 + ((i:ℤ)*(d:ℤ)) • Sz.h2) := by
        rw [hphi_add]
        have hnn : (0:ℤ) ≤ (i:ℤ)*(d:ℤ)*Sz.Delta := mul_nonneg (by positivity) (le_of_lt Sz.Delta_pos)
        omega
      have hshifted := hshift (v0 + ((i:ℤ)*(d:ℤ)) • Sz.h2) hge
      have heq : v0 + ((i:ℤ)*(d:ℤ)) • Sz.h2 + (d:ℤ) • Sz.h2
          = v0 + (((i+1:ℕ):ℤ)*(d:ℤ)) • Sz.h2 := by
        rw [add_assoc, ← add_smul]
        congr 2
        push_cast; ring
      rw [heq] at hshifted
      rw [hshifted, hprev]
  have hfinal := hiter m hb0
  have hcast : (m:ℤ)*(d:ℤ) = (N.factorial:ℤ) := by
    have hmd : m*d = N.factorial := by rw [hm]; ring
    exact_mod_cast hmd
  rw [show ((m:ℤ)*(d:ℤ)) • Sz.h2 = (N.factorial:ℤ) • Sz.h2 from by rw [hcast]] at hfinal
  exact hv0 hfinal

/-- **Theorem D.1.**  If `ξ = ξ₁ + ξ₂` has `P_ξ(S) ≤ |S|` for some non-empty finite
lattice-convex `S`, then `ξ` is periodic. -/
theorem xi_isPeriodic [Fact p.Prime] {S : Finset (ℤ × ℤ)} (hne : S.Nonempty)
    (hS : LatticeConvex S) (hP : P Sz.xi S ≤ S.card) : IsPeriodic Sz.xi := by
  classical
  by_contra hnp
  obtain ⟨ε, B, _hBsub, hbal⟩ := Sz.exists_balanced hne hS hP
  -- Rescale `h₂` (replacing it by `c • h₂`) so the new `Δ` fits `B` with a row to spare.
  obtain ⟨c, hcpos, hcbig⟩ : ∃ c : ℕ, 0 < c ∧ Sz.ht B + 1 ≤ (c : ℤ) * Sz.Delta := by
    refine ⟨(Sz.ht B + 1).toNat, ?_, ?_⟩
    · have := Sz.ht_nonneg hbal.nonempty; omega
    · have hnn := Sz.ht_nonneg hbal.nonempty
      have hcast : ((Sz.ht B + 1).toNat : ℤ) = Sz.ht B + 1 := Int.toNat_of_nonneg (by omega)
      have hD1 : (1 : ℤ) ≤ Sz.Delta := Sz.Delta_pos
      calc Sz.ht B + 1 = ((Sz.ht B + 1).toNat : ℤ) * 1 := by rw [hcast, mul_one]
        _ ≤ ((Sz.ht B + 1).toNat : ℤ) * Sz.Delta := mul_le_mul_of_nonneg_left hD1 (by positivity)
  set Sz2 : SzabadosData p :=
    { xi1 := Sz.xi1
      xi2 := Sz.xi2
      u := Sz.u
      c₁ := Sz.c₁
      h2 := (c : ℤ) • Sz.h2
      u_primitive := Sz.u_primitive
      c₁_pos := Sz.c₁_pos
      h1_mem_Per := Sz.h1_mem_Per
      h2_mem_Per := (Per Sz.xi2).zsmul_mem Sz.h2_mem_Per (c : ℤ)
      delta_pos := by
        show 0 < det Sz.u ((c : ℤ) • Sz.h2)
        have hdc : det Sz.u ((c : ℤ) • Sz.h2) = (c : ℤ) * det Sz.u Sz.h2 := by
          simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
        rw [hdc]
        have hcpos' : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hcpos
        have hDsz : (0:ℤ) < det Sz.u Sz.h2 := Sz.delta_pos
        positivity } with hSz2_def
  have hxi2 : Sz2.xi = Sz.xi := rfl
  have hht2 : Sz2.ht B = Sz.ht B := rfl
  have hDelta2 : Sz2.Delta = (c : ℤ) * Sz.Delta := by
    show det Sz.u ((c : ℤ) • Sz.h2) = (c : ℤ) * det Sz.u Sz.h2
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hnp2 : ¬ IsPeriodic Sz2.xi := by rw [hxi2]; exact hnp
  have hbal2 : Sz2.Balanced ε B := ⟨hbal.nonempty, hbal.latticeConvex, hbal.low, hbal.deficit,
    hbal.rows⟩
  have hfit2 : Sz2.ht B + 1 ≤ Sz2.Delta := by rw [hht2, hDelta2]; exact hcbig
  cases ε with
  | true => exact xi_isPeriodic_core Sz2 hbal2 hnp2 hfit2
  | false =>
      have hbal3 : Sz2.neg.Balanced true B := (balanced_neg (Sz := Sz2) (ε := true)).mpr hbal2
      have hnp3 : ¬ IsPeriodic Sz2.neg.xi := by rw [neg_xi]; exact hnp2
      have hfit3 : Sz2.neg.ht B + 1 ≤ Sz2.neg.Delta := by rw [neg_ht, neg_Delta]; exact hfit2
      exact xi_isPeriodic_core Sz2.neg hbal3 hnp3 hfit3

end SzabadosData

/-! ### Theorem D.1 and Corollary D.2 in unnormalised form -/

/-- Every non-zero lattice vector is a positive integer multiple of a primitive vector. -/
private theorem exists_primitive_nsmul_eq {h : ℤ × ℤ} (hh : h ≠ 0) :
    ∃ (v : ℤ × ℤ) (k : ℕ), Primitive v ∧ 0 < k ∧ h = (k : ℤ) • v := by
  set d : ℕ := Int.gcd h.1 h.2 with hddef
  have hd_pos : 0 < d := by
    rw [hddef, Int.gcd_pos_iff]
    by_contra hcon
    push Not at hcon
    exact hh (Prod.ext hcon.1 hcon.2)
  have hdvd1 : (d : ℤ) ∣ h.1 := Int.gcd_dvd_left ..
  have hdvd2 : (d : ℤ) ∣ h.2 := Int.gcd_dvd_right ..
  set v : ℤ × ℤ := (h.1 / d, h.2 / d) with hvdef
  have heq1 : (d : ℤ) * v.1 = h.1 := by rw [hvdef]; exact Int.mul_ediv_cancel' hdvd1
  have heq2 : (d : ℤ) * v.2 = h.2 := by rw [hvdef]; exact Int.mul_ediv_cancel' hdvd2
  have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast hd_pos.ne'
  have hbezout : (d : ℤ) = h.1 * Int.gcdA h.1 h.2 + h.2 * Int.gcdB h.1 h.2 :=
    Int.gcd_eq_gcd_ab h.1 h.2
  have hcoprime : Int.gcdA h.1 h.2 * v.1 + Int.gcdB h.1 h.2 * v.2 = 1 := by
    have hcancel : (d : ℤ) * (Int.gcdA h.1 h.2 * v.1 + Int.gcdB h.1 h.2 * v.2) = (d : ℤ) * 1 := by
      linear_combination Int.gcdA h.1 h.2 * heq1 + Int.gcdB h.1 h.2 * heq2 - hbezout
    exact mul_left_cancel₀ hdne hcancel
  refine ⟨v, d, ⟨Int.gcdA h.1 h.2, Int.gcdB h.1 h.2, hcoprime⟩, hd_pos, ?_⟩
  apply Prod.ext
  · show h.1 = (d : ℤ) * v.1
    exact heq1.symm
  · show h.2 = (d : ℤ) * v.2
    exact heq2.symm

/-- Normalisation: a pair of configurations with non-zero periods `h₁, h₂` pointing in different
directions can be put into the form of `SzabadosData`.  Paper §D.1: take `u` primitive in the
direction of `h₁`, and replace `h₂` by `-h₂` if necessary so that `Δ > 0`. -/
theorem exists_szabadosData {p : ℕ} {xi1 xi2 : Config (ZMod p)} {h1 h2 : ℤ × ℤ}
    (hp1 : h1 ∈ Per xi1) (hp2 : h2 ∈ Per xi2) (hh1 : h1 ≠ 0) (hindep : det h1 h2 ≠ 0) :
    ∃ Sz : SzabadosData p, Sz.xi1 = xi1 ∧ Sz.xi2 = xi2 := by
  obtain ⟨v, k, hvprim, hkpos, hh1eq⟩ := exists_primitive_nsmul_eq hh1
  have hdet_eq : det h1 h2 = (k : ℤ) * det v h2 := by
    rw [hh1eq]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hkne : (k : ℤ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hdvh2_ne : det v h2 ≠ 0 := by
    intro hcon
    exact hindep (by rw [hdet_eq, hcon, mul_zero])
  rcases lt_or_gt_of_ne hdvh2_ne with hlt | hgt
  · exact ⟨⟨xi1, xi2, v, k, -h2, hvprim, hkpos, hh1eq ▸ hp1, (Per xi2).neg_mem hp2, by
      show 0 < det v (-h2)
      have hneg : det v (-h2) = -det v h2 := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
      rw [hneg]; linarith⟩, rfl, rfl⟩
  · exact ⟨⟨xi1, xi2, v, k, h2, hvprim, hkpos, hh1eq ▸ hp1, hp2, hgt⟩, rfl, rfl⟩

/-- **Theorem D.1.**  Let `p` be a prime and let `ξ₁, ξ₂ : ℤ² → 𝔽_p` have periods
`h₁, h₂ ∈ ℤ² \ {0}` respectively, linearly independent over `ℝ`, and put `ξ = ξ₁ + ξ₂`.  If
`P_ξ(S) ≤ |S|` for some non-empty finite lattice-convex `S`, then `ξ` is periodic. -/
theorem isPeriodic_of_add {p : ℕ} [Fact p.Prime] {xi1 xi2 : Config (ZMod p)} {h1 h2 : ℤ × ℤ}
    (hp1 : h1 ∈ Per xi1) (hp2 : h2 ∈ Per xi2) (hh1 : h1 ≠ 0) (hindep : det h1 h2 ≠ 0)
    {S : Finset (ℤ × ℤ)} (hne : S.Nonempty) (hS : LatticeConvex S)
    (hP : P (fun z => xi1 z + xi2 z) S ≤ S.card) :
    IsPeriodic fun z => xi1 z + xi2 z := by
  obtain ⟨Sz, e1, e2⟩ := exists_szabadosData hp1 hp2 hh1 hindep
  have hxi : Sz.xi = fun z => xi1 z + xi2 z := by
    funext z
    simp [SzabadosData.xi, e1, e2]
  rw [← hxi] at hP ⊢
  exact Sz.xi_isPeriodic hne hS hP

/-- A *periodic decomposition* of `ξ` of length `n`: a sum of `n` periodic configurations.
Paper Corollary D.2. -/
def PeriodicDecomp {p : ℕ} (xi : Config (ZMod p)) (n : ℕ) : Prop :=
  ∃ f : Fin n → Config (ZMod p), (∀ i, IsPeriodic (f i)) ∧ ∀ z, xi z = ∑ i, f i z

/-- `ord(ξ) = n`: the length of an `𝔽_p`-minimal periodic decomposition of `ξ`.
Paper Corollary D.2, Remark 8.3. -/
def HasOrder {p : ℕ} (xi : Config (ZMod p)) (n : ℕ) : Prop :=
  PeriodicDecomp xi n ∧ ∀ k, PeriodicDecomp xi k → n ≤ k

/-- **Corollary D.2.**  If `ξ = ξ₁ + ξ₂` is an `𝔽_p`-minimal periodic decomposition of order 2,
then `ξ` does not have low convex complexity.

Order 2 forces `ξ` to be non-periodic — a periodic configuration has a minimal decomposition of
length 1 — and forces the two periods to point in different directions, components with parallel
periods being mergeable into one.  Theorem D.1 then applies. -/
theorem not_lowConvexComplexity_of_hasOrder_two {p : ℕ} [Fact p.Prime] {xi : Config (ZMod p)}
    (h : HasOrder xi 2) : ¬ LowConvexComplexity xi := by
  obtain ⟨⟨f, hfper, hfsum⟩, hmin⟩ := h
  obtain ⟨h1, hh1mem, hh1ne⟩ := hfper 0
  obtain ⟨h2, hh2mem, hh2ne⟩ := hfper 1
  have hxi_eq : xi = fun z => f 0 z + f 1 z := by
    funext z
    rw [hfsum z]
    simp
  have hnp : ¬ IsPeriodic xi := by
    rintro ⟨q, hqmem, hqne⟩
    have hpd1 : PeriodicDecomp xi 1 :=
      ⟨fun _ => xi, fun _ => ⟨q, hqmem, hqne⟩, fun z => by simp⟩
    have h21 := hmin 1 hpd1
    omega
  have hindep : det h1 h2 ≠ 0 := by
    intro hcon
    apply hnp
    obtain ⟨w, k, hwprim, hkpos, hh1eq⟩ := exists_primitive_nsmul_eq hh1ne
    obtain ⟨u', hu'⟩ := hwprim.exists_dual
    have hdw : det h1 h2 = (k : ℤ) * det w h2 := by
      rw [hh1eq]
      simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    have hkne : (k : ℤ) ≠ 0 := by exact_mod_cast hkpos.ne'
    have hdetwh2 : det w h2 = 0 := by
      rw [hdw] at hcon
      rcases mul_eq_zero.mp hcon with h' | h'
      · exact absurd h' hkne
      · exact h'
    have hh2eq : h2 = (det h2 u') • w := by
      have hd := eq_smul_add_smul hu' h2
      rw [hdetwh2, zero_smul, add_zero] at hd
      exact hd
    set m : ℤ := det h2 u' with hmdef
    have hcommon : (k : ℤ) • h2 = m • h1 := by
      rw [hh2eq, hh1eq, smul_smul, smul_smul, mul_comm (k : ℤ) m]
    have hq1 : (k : ℤ) • h2 ∈ Per (f 1) := (Per (f 1)).zsmul_mem hh2mem (k : ℤ)
    have hq2 : m • h1 ∈ Per (f 0) := (Per (f 0)).zsmul_mem hh1mem m
    have hqmem0 : (k : ℤ) • h2 ∈ Per (f 0) := by rw [hcommon]; exact hq2
    have hqne' : (k : ℤ) • h2 ≠ 0 := by
      intro hcon2
      rcases smul_eq_zero.mp hcon2 with h' | h'
      · exact hkne h'
      · exact hh2ne h'
    refine ⟨(k : ℤ) • h2, ?_, hqne'⟩
    rw [hxi_eq, mem_Per_iff]
    funext z
    show f 0 (z + (k : ℤ) • h2) + f 1 (z + (k : ℤ) • h2) = f 0 z + f 1 z
    rw [Per.apply hqmem0 z, Per.apply hq1 z]
  intro hlow
  obtain ⟨S, hSne, hSconv, hSP⟩ := hlow
  apply hnp
  have hP' : P (fun z => f 0 z + f 1 z) S ≤ S.card := by rw [← hxi_eq]; exact hSP
  have hthis := isPeriodic_of_add hh1mem hh2mem hh1ne hindep hSne hSconv hP'
  rw [← hxi_eq] at hthis
  exact hthis

end Nivat
