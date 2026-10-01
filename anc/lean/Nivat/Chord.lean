/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Config
import Nivat.Defs.Complexity
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Concavity of chord length and lattice-point counting

Formalisation of the geometric input needed for condition (iii) of Lemma D.5 of *The Convex
Nivat Conjecture* (Pan), as recorded in the docstring of
`Nivat.SzabadosData.card_row_ge_of_extreme` in `Nivat/AppendixD.lean`: for a lattice-convex set
whose two extreme rows (the lattice points on two parallel supporting lines) each have at least
`n` points, every intermediate row has at least `n - 1` points.  This is the statement that the
length of the parallel chords of a convex set is a concave function of the level at which the
chord is cut.

The proof strategy avoids working with the supremum/infimum of the (possibly non-attained) real
endpoints of each chord: instead of the concavity of the endpoint functions, we only ever take
the convex combination of *two given* chords already known to exist (`exists_chord_of_convex`),
which is a completely elementary consequence of convexity.  The real-valued chord-length bound
is then converted into a genuine lattice point count via `card_Icc_ceil_floor_gt`, and the two
are bridged in the lattice-convex setting by `card_row_ge_of_extreme`, using the unimodular
change of coordinates `eq_smul_add_smul` (and its real analogue `toReal_eq_smul_add_smul`) rather
than reproving that each row of a lattice-convex set is a contiguous run.

This file is deliberately independent of `Nivat/AppendixD.lean` (in particular of
`Nivat.SzabadosData` and everything under its `Sz.*` namespace): it is imported *by*
`AppendixD.lean`, so `card_row_ge_of_extreme` is phrased purely in terms of `LatticeConvex`,
`det`/`pi` and a chosen unimodular dual pair `(v, u)`, with no reference to any `Szabados`-style
combinatorial data.

## Main results

* `Nivat.card_Icc_ceil_floor_gt` — a real interval of length `L` contains more than `L - 1`
  integers.
* `Nivat.card_ge_sub_add_one_of_ordConnected`, `Nivat.sub_max_min_ge` — integer bookkeeping
  lemmas used to package the above.
* `Nivat.exists_chord_of_convex` — the concavity of the chord length: a convex combination of
  two chords of a convex set is (the level of) a chord at least as long as the combination of
  the two given lengths.
* `Nivat.card_row_ge_of_extreme` — the bridge to lattice-convex sets: if two levels of a
  lattice-convex set each carry `n` points on lines parallel to a primitive vector `v`, every
  intermediate level carries at least `n - 1`.
* `Nivat.latticeConvex_sdiff_extremeRow` — deleting an extreme row (all points with `pi v z = hi`,
  where `hi` bounds `pi v` from above on `B`) from a lattice-convex set preserves
  lattice-convexity.

## Status

All of the above are proved in full; no `sorry`.
-/

namespace Nivat

open Finset

/-! ### Lattice points in a real interval -/

/-- A real interval of length `L = b - a` contains more than `L - 1` integers: the integers in
`[a, b]` are exactly `Finset.Icc ⌈a⌉ ⌊b⌋`. -/
theorem card_Icc_ceil_floor_gt {a b : ℝ} (hab : a ≤ b) :
    b - a - 1 < ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) := by
  have hle : ⌈a⌉ ≤ ⌊b⌋ + 1 := (Int.ceil_mono hab).trans (Int.ceil_le_floor_add_one b)
  have heq : ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℤ) = ⌊b⌋ + 1 - ⌈a⌉ := Int.card_Icc_of_le ⌈a⌉ ⌊b⌋ hle
  have h1 : b - 1 < (⌊b⌋ : ℝ) := Int.sub_one_lt_floor b
  have h2 : (⌈a⌉ : ℝ) < a + 1 := Int.ceil_lt_add_one a
  have heqR : ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) = (⌊b⌋ : ℝ) + 1 - (⌈a⌉ : ℝ) := by
    exact_mod_cast heq
  linarith

/-- If a finite integer set `K` is order-convex (contains the whole integer interval between
any two of its elements) and contains `x ≤ y`, then `K.card ≥ y - x + 1`. -/
theorem card_ge_sub_add_one_of_ordConnected {K : Finset ℤ}
    (hconv : ∀ x ∈ K, ∀ y ∈ K, Finset.Icc x y ⊆ K) {x y : ℤ} (hx : x ∈ K) (hy : y ∈ K)
    (hxy : x ≤ y) : y - x + 1 ≤ (K.card : ℤ) := by
  have hsub : Finset.Icc x y ⊆ K := hconv x hx y hy
  have hcard : (Finset.Icc x y).card ≤ K.card := Finset.card_le_card hsub
  have heq : ((Finset.Icc x y).card : ℤ) = y + 1 - x := Int.card_Icc_of_le x y (by omega)
  omega

/-- If `S` is a finite non-empty set of integers with at least `n` elements, its span
`S.max' - S.min'` is at least `n - 1`. -/
theorem sub_max_min_ge {S : Finset ℤ} {n : ℕ} (hcard : n ≤ S.card) (hne : S.Nonempty) :
    (n : ℤ) - 1 ≤ S.max' hne - S.min' hne := by
  obtain ⟨x, hx⟩ := hne
  have hsub : S ⊆ Finset.Icc (S.min' ⟨x, hx⟩) (S.max' ⟨x, hx⟩) :=
    fun y hy => Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hy, Finset.le_max' _ _ hy⟩
  have hle : S.min' ⟨x, hx⟩ ≤ S.max' ⟨x, hx⟩ :=
    (Finset.min'_le _ _ hx).trans (Finset.le_max' _ _ hx)
  have hcard' : S.card ≤ (Finset.Icc (S.min' ⟨x, hx⟩) (S.max' ⟨x, hx⟩)).card :=
    Finset.card_le_card hsub
  have heq : ((Finset.Icc (S.min' ⟨x, hx⟩) (S.max' ⟨x, hx⟩)).card : ℤ) =
      S.max' ⟨x, hx⟩ + 1 - S.min' ⟨x, hx⟩ :=
    Int.card_Icc_of_le (S.min' ⟨x, hx⟩) (S.max' ⟨x, hx⟩) (by omega)
  omega

/-! ### Concavity of the chord length -/

/-- **Concavity of the chord length.**  If `C` is convex and the slices at levels `φ = φ p₁` and
`φ = φ p₂` contain segments `[p₁, q₁]` and `[p₂, q₂]` (each with both endpoints in `C` and equal
`φ`-value, i.e. lying in a single level slice), then for every convex combination
`t = α (φ p₁) + β (φ p₂)` the slice at level `t` contains a segment whose `ψ`-length is at least
the convex combination `α (ψ q₁ - ψ p₁) + β (ψ q₂ - ψ p₂)` of the two given lengths.

This is proved by simply taking the convex combinations `p := α p₁ + β p₂` and `q := α q₁ + β q₂`;
no supremum/infimum of the (possibly non-attained) endpoint functions of `C` is needed. -/
theorem exists_chord_of_convex {C : Set (ℝ × ℝ)} (hC : Convex ℝ C)
    {φ ψ : ℝ × ℝ → ℝ} (hφ : IsLinearMap ℝ φ) (hψ : IsLinearMap ℝ ψ)
    {p₁ q₁ p₂ q₂ : ℝ × ℝ} (hp₁ : p₁ ∈ C) (hq₁ : q₁ ∈ C) (hp₂ : p₂ ∈ C) (hq₂ : q₂ ∈ C)
    (h₁ : φ p₁ = φ q₁) (h₂ : φ p₂ = φ q₂)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    ∃ p q : ℝ × ℝ, p ∈ C ∧ q ∈ C ∧ φ p = φ q ∧
      φ p = α * φ p₁ + β * φ p₂ ∧
      ψ q - ψ p = α * (ψ q₁ - ψ p₁) + β * (ψ q₂ - ψ p₂) := by
  have hp : φ (α • p₁ + β • p₂) = α * φ p₁ + β * φ p₂ := by
    rw [hφ.map_add, hφ.map_smul, hφ.map_smul, smul_eq_mul, smul_eq_mul]
  have hq : φ (α • q₁ + β • q₂) = α * φ q₁ + β * φ q₂ := by
    rw [hφ.map_add, hφ.map_smul, hφ.map_smul, smul_eq_mul, smul_eq_mul]
  have hψp : ψ (α • p₁ + β • p₂) = α * ψ p₁ + β * ψ p₂ := by
    rw [hψ.map_add, hψ.map_smul, hψ.map_smul, smul_eq_mul, smul_eq_mul]
  have hψq : ψ (α • q₁ + β • q₂) = α * ψ q₁ + β * ψ q₂ := by
    rw [hψ.map_add, hψ.map_smul, hψ.map_smul, smul_eq_mul, smul_eq_mul]
  refine ⟨α • p₁ + β • p₂, α • q₁ + β • q₂, hC hp₁ hp₂ hα hβ hαβ, hC hq₁ hq₂ hα hβ hαβ, ?_, hp, ?_⟩
  · rw [hp, hq, h₁, h₂]
  · rw [hψp, hψq]; ring

/-! ### Bridging to lattice-convex sets -/

/-- The real-valued linear form along `u`, agreeing with `det u` on lattice points
(`phiR_toReal`).  This is the real level function whose fibres are the parallel chords of
`Conv B`. -/
def phiR (u : ℤ × ℤ) (w : ℝ × ℝ) : ℝ := (u.1 : ℝ) * w.2 - (u.2 : ℝ) * w.1

/-- The real-valued linear form along `u'`, agreeing with `fun z => det z u'` on lattice points
(`psiR_toReal`).  This is the coordinate along a chord parallel to `u`. -/
def psiR (u' : ℤ × ℤ) (w : ℝ × ℝ) : ℝ := w.1 * (u'.2 : ℝ) - w.2 * (u'.1 : ℝ)

theorem isLinearMap_phiR (u : ℤ × ℤ) : IsLinearMap ℝ (phiR u) where
  map_add x y := by simp only [phiR, Prod.fst_add, Prod.snd_add]; ring
  map_smul c x := by simp only [phiR, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem isLinearMap_psiR (u' : ℤ × ℤ) : IsLinearMap ℝ (psiR u') where
  map_add x y := by simp only [psiR, Prod.fst_add, Prod.snd_add]; ring
  map_smul c x := by simp only [psiR, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem phiR_toReal (u z : ℤ × ℤ) : phiR u (toReal z) = ((det u z : ℤ) : ℝ) := by
  simp only [phiR, toReal, det]; push_cast; ring

theorem psiR_toReal (u' z : ℤ × ℤ) : psiR u' (toReal z) = ((det z u' : ℤ) : ℝ) := by
  simp only [psiR, toReal, det]; push_cast; ring

/-- The real analogue of `eq_smul_add_smul`: in the coordinates of a unimodular basis `(u, u')`,
every real point decomposes as `(ψ-coordinate) • u + (φ-coordinate) • u'`. -/
theorem toReal_eq_smul_add_smul {u u' : ℤ × ℤ} (h : det u u' = 1) (w : ℝ × ℝ) :
    w = (psiR u' w) • toReal u + (phiR u w) • toReal u' := by
  have hdet : (u.1 : ℝ) * (u'.2 : ℝ) - (u.2 : ℝ) * (u'.1 : ℝ) = 1 := by
    have h' := h; simp only [det] at h'; exact_mod_cast h'
  apply Prod.ext <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, toReal,
      psiR, phiR]
  · linear_combination (-w.1) * hdet
  · linear_combination (-w.2) * hdet

/-- `toReal` commutes with the change of coordinates given by a unimodular basis. -/
theorem toReal_zsmul_add_zsmul (u u' : ℤ × ℤ) (s t : ℤ) :
    toReal (s • u + t • u') = (s : ℝ) • toReal u + (t : ℝ) • toReal u' := by
  apply Prod.ext <;>
    simp only [toReal, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    push_cast <;> ring

/-- Two lattice points on the same level of `φ = det u ·` with the same `ψ = det (·) u'`
coordinate coincide: `(φ, ψ)` is a coordinate system on the unimodular basis `(u, u')`. -/
theorem eq_of_phi_psi_eq {u u' : ℤ × ℤ} (h : det u u' = 1) {z₁ z₂ : ℤ × ℤ}
    (hphi : det u z₁ = det u z₂) (hpsi : det z₁ u' = det z₂ u') : z₁ = z₂ := by
  have e1 : z₁ = det z₁ u' • u + det u z₁ • u' := eq_smul_add_smul h z₁
  have e2 : z₂ = det z₂ u' • u + det u z₂ • u' := eq_smul_add_smul h z₂
  rw [e1, e2, hphi, hpsi]

/-- The lattice point of "coordinates" `(s, t)` in the unimodular basis `(u, u')` lies on level
`t` of `φ = det u ·`. -/
theorem phi_zsmul_add_zsmul {u u' : ℤ × ℤ} (h : det u u' = 1) (s t : ℤ) :
    det u (s • u + t • u') = t := pi_smul_add_smul h s t

/-- The lattice point of "coordinates" `(s, t)` in the unimodular basis `(u, u')` has `ψ`-coordinate
`s`. -/
theorem psi_zsmul_add_zsmul {u u' : ℤ × ℤ} (h : det u u' = 1) (s t : ℤ) :
    det (s • u + t • u') u' = s := by
  have h' : (u.1 : ℤ) * u'.2 - u.2 * u'.1 = 1 := h
  simp only [det, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  linear_combination s * h'

/-- **Concavity, bridged to lattice points (paper Lemma D.5 (iii)).**  If `B` is lattice-convex
and two levels `t₁ ≤ t₂` of `π_v z = pi v z` each carry at least `n` points of `B`, then every
intermediate level `t₁ ≤ t ≤ t₂` carries at least `n - 1` points (stated as `n ≤ card + 1` to
avoid truncated subtraction).  Here `u` is any unimodular dual of the primitive direction `v`
(`det v u = 1`); no hypothesis that `v` is primitive, nor any global bound on `pi v` over `B`,
is needed — only `det v u = 1` and the two extreme-row cardinalities are used. -/
theorem card_row_ge_of_extreme {B : Finset (ℤ × ℤ)} (hB : LatticeConvex B)
    {v u : ℤ × ℤ} (hvu : det v u = 1) {t₁ t₂ t : ℤ} {n : ℕ}
    (h₁ : n ≤ (B.filter fun z => pi v z = t₁).card)
    (h₂ : n ≤ (B.filter fun z => pi v z = t₂).card)
    (hle : t₁ ≤ t) (hlet : t ≤ t₂) :
    n ≤ (B.filter fun z => pi v z = t).card + 1 := by
  unfold pi at h₁ h₂ ⊢
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · omega
  -- Extract, from each extreme row, two lattice points realising the maximal `ψ`-span.
  have key : ∀ s : ℤ, n ≤ (B.filter fun z => det v z = s).card →
      ∃ z₁ z₂ : ℤ × ℤ, z₁ ∈ B ∧ z₂ ∈ B ∧ det v z₁ = s ∧ det v z₂ = s ∧
        (n : ℝ) - 1 ≤ ((det z₂ u : ℤ) : ℝ) - ((det z₁ u : ℤ) : ℝ) := by
    intro s hs
    set row := B.filter fun z => det v z = s with hrow
    have hinj : Set.InjOn (fun z => det z u) (row : Set (ℤ × ℤ)) := by
      intro z₁ hz₁ z₂ hz₂ heq
      have e1 : det v z₁ = s := (Finset.mem_filter.mp hz₁).2
      have e2 : det v z₂ = s := (Finset.mem_filter.mp hz₂).2
      exact eq_of_phi_psi_eq hvu (e1.trans e2.symm) heq
    have hScard : (row.image (fun z => det z u)).card = row.card :=
      Finset.card_image_of_injOn hinj
    have hSne : (row.image (fun z => det z u)).Nonempty := by
      have hrne : row.Nonempty := Finset.card_pos.mp (by omega)
      exact hrne.image _
    have hSn : n ≤ (row.image (fun z => det z u)).card := by rw [hScard]; exact hs
    have hspan := sub_max_min_ge hSn hSne
    obtain ⟨z₂, hz₂row, hz₂eq⟩ := Finset.mem_image.mp (Finset.max'_mem _ hSne)
    obtain ⟨z₁, hz₁row, hz₁eq⟩ := Finset.mem_image.mp (Finset.min'_mem _ hSne)
    refine ⟨z₁, z₂, (Finset.mem_filter.mp hz₁row).1, (Finset.mem_filter.mp hz₂row).1,
      (Finset.mem_filter.mp hz₁row).2, (Finset.mem_filter.mp hz₂row).2, ?_⟩
    rw [hz₁eq, hz₂eq]
    exact_mod_cast hspan
  obtain ⟨w₁, w₂, hw₁B, hw₂B, hw₁phi, hw₂phi, hw₁span⟩ := key t₁ h₁
  obtain ⟨w₃, w₄, hw₃B, hw₄B, hw₃phi, hw₄phi, hw₂span⟩ := key t₂ h₂
  set p₁ := toReal w₁; set q₁ := toReal w₂; set p₂ := toReal w₃; set q₂ := toReal w₄
  have hp₁ : p₁ ∈ Conv B := subset_Conv hw₁B
  have hq₁ : q₁ ∈ Conv B := subset_Conv hw₂B
  have hp₂ : p₂ ∈ Conv B := subset_Conv hw₃B
  have hq₂ : q₂ ∈ Conv B := subset_Conv hw₄B
  have hC : Convex ℝ (Conv B) := convex_convexHull ℝ _
  have hphi1 : phiR v p₁ = phiR v q₁ := by
    rw [phiR_toReal, phiR_toReal, hw₁phi, hw₂phi]
  have hphi2 : phiR v p₂ = phiR v q₂ := by
    rw [phiR_toReal, phiR_toReal, hw₃phi, hw₄phi]
  -- Choose the convex coefficients `α, β` realising `t = α t₁ + β t₂`.
  obtain ⟨α, β, hα, hβ, hαβ, hαt⟩ :
      ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ α + β = 1 ∧ α * (t₁ : ℝ) + β * (t₂ : ℝ) = (t : ℝ) := by
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact ⟨1, 0, zero_le_one, le_refl 0, by ring, by rw [← heq]; ring⟩
    · rcases eq_or_lt_of_le hlet with heq2 | hlt2
      · exact ⟨0, 1, le_refl 0, zero_le_one, by ring, by rw [heq2]; ring⟩
      · have hpos : (0:ℝ) < (t₂ : ℝ) - (t₁ : ℝ) := by
          have : (t₁ : ℝ) < (t₂ : ℝ) := by exact_mod_cast hlt.trans hlt2
          linarith
        refine ⟨((t₂ : ℝ) - t) / ((t₂ : ℝ) - t₁), ((t : ℝ) - t₁) / ((t₂ : ℝ) - t₁), ?_, ?_, ?_, ?_⟩
        · apply div_nonneg (by
            have : (t : ℝ) ≤ (t₂ : ℝ) := by exact_mod_cast hlet
            linarith) hpos.le
        · apply div_nonneg (by
            have : (t₁ : ℝ) ≤ (t : ℝ) := by exact_mod_cast hle
            linarith) hpos.le
        · field_simp; ring
        · field_simp; ring
  obtain ⟨p, q, hpC, hqC, hpq, hpval, hψspan⟩ :=
    exists_chord_of_convex hC (isLinearMap_phiR v) (isLinearMap_psiR u) hp₁ hq₁ hp₂ hq₂
      hphi1 hphi2 hα hβ hαβ
  rw [phiR_toReal, phiR_toReal, hw₁phi, hw₃phi, hαt] at hpval
  -- The `ψ`-span of the intermediate chord is at least `n - 1`.
  have hq1eq : psiR u q₁ = ((det w₂ u : ℤ) : ℝ) := psiR_toReal u w₂
  have hp1eq : psiR u p₁ = ((det w₁ u : ℤ) : ℝ) := psiR_toReal u w₁
  have hq2eq : psiR u q₂ = ((det w₄ u : ℤ) : ℝ) := psiR_toReal u w₄
  have hp2eq : psiR u p₂ = ((det w₃ u : ℤ) : ℝ) := psiR_toReal u w₃
  have hspan_ge : (n : ℝ) - 1 ≤ psiR u q - psiR u p := by
    rw [hψspan, hq1eq, hp1eq, hq2eq, hp2eq]
    have m1 : α * ((n : ℝ) - 1) ≤ α * (((det w₂ u : ℤ) : ℝ) - ((det w₁ u : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hw₁span hα
    have m2 : β * ((n : ℝ) - 1) ≤ β * (((det w₄ u : ℤ) : ℝ) - ((det w₃ u : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hw₂span hβ
    have hsum : α * ((n : ℝ) - 1) + β * ((n : ℝ) - 1) = (n : ℝ) - 1 := by
      rw [← add_mul, hαβ, one_mul]
    linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  have hple : psiR u p ≤ psiR u q := by linarith
  -- Every integer between the two `ψ`-coordinates gives a lattice point on the intermediate row.
  have hqval : phiR v q = (t : ℝ) := by rw [← hpq]; exact hpval
  have hpt : p = psiR u p • toReal v + (t : ℝ) • toReal u := by
    rw [← hpval]; exact toReal_eq_smul_add_smul hvu p
  have hqt : q = psiR u q • toReal v + (t : ℝ) • toReal u := by
    rw [← hqval]; exact toReal_eq_smul_add_smul hvu q
  have hmapmem : ∀ s : ℤ, psiR u p ≤ (s : ℝ) → (s : ℝ) ≤ psiR u q →
      s • v + t • u ∈ B.filter fun z => det v z = t := by
    intro s hs1 hs2
    have hmem : (s : ℝ) • toReal v + (t : ℝ) • toReal u ∈ Conv B := by
      rcases eq_or_lt_of_le hple with heqpq | hltpq
      · have hseq : (s : ℝ) = psiR u p :=
          le_antisymm (by rw [heqpq]; exact hs2) hs1
        rw [hseq, ← hpt]; exact hpC
      · have hden : psiR u q - psiR u p > 0 := by linarith
        have hDne : psiR u q - psiR u p ≠ 0 := ne_of_gt hden
        set lam := ((psiR u q : ℝ) - s) / (psiR u q - psiR u p) with hlamdef
        have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hden.le
        have hlam1 : lam ≤ 1 := by rw [div_le_one hden]; linarith
        have hcomb : (s : ℝ) = lam * psiR u p + (1 - lam) * psiR u q := by
          rw [hlamdef]; field_simp; ring
        have heqpt : lam • p + (1 - lam) • q =
            (s : ℝ) • toReal v + (t : ℝ) • toReal u := by
          rw [hpt, hqt, hcomb]
          apply Prod.ext <;>
            simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
            ring
        rw [← heqpt]
        exact hC hpC hqC hlam0 (by linarith) (by ring)
    have hws : toReal (s • v + t • u) ∈ Conv B := by
      rw [toReal_zsmul_add_zsmul]; exact hmem
    have hmemB : s • v + t • u ∈ B := hB _ hws
    exact Finset.mem_filter.mpr ⟨hmemB, phi_zsmul_add_zsmul hvu s t⟩
  have hinj2 : Set.InjOn (fun s : ℤ => s • v + t • u) (Finset.Icc ⌈psiR u p⌉ ⌊psiR u q⌋ : Set ℤ) := by
    intro s₁ _ s₂ _ heq
    have h1 : det (s₁ • v + t • u) u = det (s₂ • v + t • u) u := by
      simp only at heq; rw [heq]
    rwa [psi_zsmul_add_zsmul hvu, psi_zsmul_add_zsmul hvu] at h1
  have hsubmap : ∀ s ∈ Finset.Icc ⌈psiR u p⌉ ⌊psiR u q⌋,
      s • v + t • u ∈ B.filter fun z => det v z = t := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    exact hmapmem s (le_trans (Int.le_ceil _) (by exact_mod_cast hs.1))
      (le_trans (by exact_mod_cast hs.2) (Int.floor_le _))
  have hcardle : (Finset.Icc ⌈psiR u p⌉ ⌊psiR u q⌋).card ≤ (B.filter fun z => det v z = t).card := by
    have him : (Finset.Icc ⌈psiR u p⌉ ⌊psiR u q⌋).image (fun s : ℤ => s • v + t • u) ⊆
        B.filter fun z => det v z = t := by
      intro z hz
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
      exact hsubmap s hs
    calc (Finset.Icc ⌈psiR u p⌉ ⌊psiR u q⌋).card
        = ((Finset.Icc ⌈psiR u p⌉ ⌊psiR u q⌋).image (fun s : ℤ => s • v + t • u)).card :=
          (Finset.card_image_of_injOn hinj2).symm
      _ ≤ (B.filter fun z => det v z = t).card := Finset.card_le_card him
  have hgt := card_Icc_ceil_floor_gt hple
  have : (n : ℝ) - 2 < ((Finset.Icc ⌈psiR u p⌉ ⌊psiR u q⌋).card : ℝ) := by linarith
  have hcast : ((Finset.Icc ⌈psiR u p⌉ ⌊psiR u q⌋).card : ℝ) ≤
      ((B.filter fun z => det v z = t).card : ℝ) := by exact_mod_cast hcardle
  have : (n : ℝ) - 2 < ((B.filter fun z => det v z = t).card : ℝ) := by linarith
  have hfin : (n : ℝ) < ((B.filter fun z => det v z = t).card : ℝ) + 2 := by linarith
  have : n < (B.filter fun z => det v z = t).card + 2 := by exact_mod_cast hfin
  omega

/-! ### Deleting an extreme row -/

/-- **Deleting an extreme row preserves lattice-convexity** (paper, proof of Lemma D.5 (iii)):
if every point of a lattice-convex set `B` has `pi v z ≤ hi`, then removing the top row
`pi v z = hi` leaves a lattice-convex set.  The key point is that
`{w : ℝ × ℝ | phiR v w < hi}` is convex and its lattice points are exactly the retained ones,
so `Conv (B.filter ...)` is trapped between that half-plane and `Conv B`. -/
theorem latticeConvex_sdiff_extremeRow {v : ℤ × ℤ} {B : Finset (ℤ × ℤ)} (hB : LatticeConvex B)
    {hi : ℤ} (hhi : ∀ z ∈ B, pi v z ≤ hi) :
    LatticeConvex (B.filter fun z => pi v z ≠ hi) := by
  intro z hz
  have hzB : z ∈ B := hB z <|
    convexHull_mono (Set.image_mono (by exact_mod_cast Finset.filter_subset _ B)) hz
  have hconv : Convex ℝ {w : ℝ × ℝ | phiR v w < (hi : ℝ)} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [(isLinearMap_phiR v).map_add, (isLinearMap_phiR v).map_smul,
      (isLinearMap_phiR v).map_smul, smul_eq_mul, smul_eq_mul]
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have ha0' : a = 0 := ha0.symm
      have hb1 : b = 1 := by linarith
      rw [ha0', hb1]; simpa using hy
    · have h1 : a * phiR v x < a * hi := mul_lt_mul_of_pos_left hx hapos
      have h2 : b * phiR v y ≤ b * hi := mul_le_mul_of_nonneg_left hy.le hb
      have hsum : a * (hi : ℝ) + b * hi = hi := by rw [← add_mul, hab, one_mul]
      linarith
  have hsub2 : Conv (B.filter fun z => pi v z ≠ hi) ⊆ {w : ℝ × ℝ | phiR v w < (hi : ℝ)} := by
    apply convexHull_min _ hconv
    rintro w ⟨w', hw', rfl⟩
    have hw'lt : pi v w' < hi := lt_of_le_of_ne (hhi w' (Finset.mem_filter.mp hw').1)
      (Finset.mem_filter.mp hw').2
    show phiR v (toReal w') < (hi : ℝ)
    rw [phiR_toReal]; exact_mod_cast hw'lt
  have hlt : phiR v (toReal z) < (hi : ℝ) := hsub2 hz
  refine Finset.mem_filter.mpr ⟨hzB, ?_⟩
  have hltz : det v z < hi := by rw [phiR_toReal] at hlt; exact_mod_cast hlt
  exact ne_of_lt hltz

end Nivat
