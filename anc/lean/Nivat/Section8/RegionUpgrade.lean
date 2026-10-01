/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.HalfPlane

/-!
# §8.1 bridge: upgrading overlap periodicity to full periodicity on a region

Colle's Definition 2.11 asks a *regional period* `h` of `η` on `𝒰` only to satisfy
`η_{g+h} = η_g` for `g ∈ 𝒰 ∩ (𝒰 − h)`, i.e. equality **only where both a point and its
translate lie in the region**.  It does *not* require `𝒰 + h ⊆ 𝒰`.  Our
`Nivat.FullyPeriodicOnWith` does require the containments.

This file supplies the missing bridge, which in the paper is the prose paragraph following
Theorem 8.7 ("Closed convexity puts `h, h'` in `K_R` ... Thus `R + h, R + h' ⊆ R`, and the
overlap identities hold at every point of `R`"):

* `Nivat.mem_recCone_of_ray` — the limit argument: if some forward ray `x₀ + ℝ_{≥0} w` stays in
  `C_R`, then `w ∈ K_R`.  Proof: for `x ∈ C_R` and `s ≥ 1`,
  `(1 − 1/s) x + (1/s)(x₀ + s w) = x + w + (1/s)(x₀ − x) ∈ C_R` by convexity; let `s → ∞` and
  use that `C_R` is closed.
* `Nivat.toReal_mem_recCone_of_nat_ray` — the lattice form: if `z₀ + k h ∈ R` for all `k : ℕ`
  then `h ∈ K_R`.
* `Nivat.add_mem_of_mem_recCone` — `h ∈ K_R` and `R` lattice-convex give `R + h ⊆ R`.
* `Nivat.fullyPeriodicOnWith_of_overlap_of_mem_recCone`,
  `Nivat.fullyPeriodicOn_of_overlap_of_mem_recCone` — the bridge lemma proper: Colle's literal
  (overlap-only) hypotheses plus `h, h' ∈ K_R` give `FullyPeriodicOnWith` / `FullyPeriodicOn`.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open scoped Pointwise

variable {α : Type*}

/-! ### Elementary facts about `C_R` -/

/-- `C_R` is convex. -/
theorem convex_convHullOf (R : Set (ℤ × ℤ)) : Convex ℝ (convHullOf R) :=
  (convex_convexHull ℝ _).closure

/-- `C_R` is closed. -/
theorem isClosed_convHullOf (R : Set (ℤ × ℤ)) : IsClosed (convHullOf R) :=
  isClosed_closure

/-- `R ⊆ C_R`. -/
theorem mem_convHullOf_of_mem {R : Set (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ R) :
    toReal z ∈ convHullOf R :=
  subset_closure (subset_convexHull ℝ _ ⟨z, hz, rfl⟩)

/-! ### The limit argument: a forward ray inside `C_R` lands in `K_R` -/

/-- **The closed-convexity limit argument** (paper §8.1, the paragraph after Theorem 8.7).
If some forward ray `x₀ + ℝ_{≥0} w` is contained in `C_R`, then `w` lies in the recession cone
`K_R = {w : C_R + w ⊆ C_R}`.

Indeed, for `x ∈ C_R` and `s ≥ 1`, convexity gives
`(1 − s⁻¹) • x + s⁻¹ • (x₀ + s • w) = x + w + s⁻¹ • (x₀ − x) ∈ C_R`;
letting `s → ∞` and using that `C_R` is closed yields `x + w ∈ C_R`. -/
theorem mem_recCone_of_ray {R : Set (ℤ × ℤ)} {x₀ w : ℝ × ℝ}
    (hray : ∀ s : ℝ, 0 ≤ s → x₀ + s • w ∈ convHullOf R) : w ∈ recCone R := by
  intro x hx
  have hconv : Convex ℝ (convHullOf R) := convex_convHullOf R
  have hclosed : IsClosed (convHullOf R) := isClosed_convHullOf R
  -- The approximating sequence `x + w + (n+1)⁻¹ • (x₀ - x)`.
  have hmem : ∀ n : ℕ, x + w + ((n : ℝ) + 1)⁻¹ • (x₀ - x) ∈ convHullOf R := by
    intro n
    set s : ℝ := (n : ℝ) + 1 with hsdef
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; linarith
    have hspos : (0 : ℝ) < s := by linarith
    have hsinv_pos : (0 : ℝ) < s⁻¹ := inv_pos.mpr hspos
    have hsinv_le : s⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact hs1
    have hy : x₀ + s • w ∈ convHullOf R := hray s hspos.le
    have hcomb := hconv hx hy (by linarith : (0 : ℝ) ≤ 1 - s⁻¹) hsinv_pos.le (by ring)
    have heq : (1 - s⁻¹) • x + s⁻¹ • (x₀ + s • w) = x + w + s⁻¹ • (x₀ - x) := by
      rw [sub_smul, one_smul, smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt hspos), one_smul,
        smul_sub]
      abel
    rwa [heq] at hcomb
  -- Pass to the limit.
  have h0 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [one_div] using this
  have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • (x₀ - x)) Filter.atTop
      (nhds ((0 : ℝ) • (x₀ - x))) := h0.smul_const (x₀ - x)
  have h2 : Filter.Tendsto (fun n : ℕ => x + w + ((n : ℝ) + 1)⁻¹ • (x₀ - x)) Filter.atTop
      (nhds (x + w)) := by
    have := (tendsto_const_nhds (x := x + w) (f := Filter.atTop (α := ℕ))).add h1
    simpa using this
  exact hclosed.mem_of_tendsto h2 (Filter.Eventually.of_forall hmem)

/-- Lattice form of `Nivat.mem_recCone_of_ray`: if the forward `h`-orbit of some lattice point
of `R` stays in `R`, then `h ∈ K_R`.  (Compare `Nivat.toReal_mem_recCone`, which needs the much
stronger hypothesis `R + h ⊆ R`.) -/
theorem toReal_mem_recCone_of_nat_ray {R : Set (ℤ × ℤ)} {z₀ h : ℤ × ℤ}
    (hray : ∀ k : ℕ, z₀ + (k : ℤ) • h ∈ R) : toReal h ∈ recCone R := by
  have hconv : Convex ℝ (convHullOf R) := convex_convHullOf R
  -- The integer points of the ray lie in `C_R`.
  have hmemR : ∀ k : ℕ, toReal z₀ + (k : ℝ) • toReal h ∈ convHullOf R := by
    intro k
    have hk := mem_convHullOf_of_mem (hray k)
    rw [toReal_add, toReal_zsmul] at hk
    simpa using hk
  refine mem_recCone_of_ray (x₀ := toReal z₀) ?_
  intro s hs
  set n : ℕ := ⌊s⌋₊ with hndef
  have hnle : (n : ℝ) ≤ s := Nat.floor_le hs
  have hlt : s < (n : ℝ) + 1 := Nat.lt_floor_add_one s
  set r : ℝ := s - (n : ℝ) with hrdef
  have hr0 : (0 : ℝ) ≤ r := by rw [hrdef]; linarith
  have hr1 : r ≤ 1 := by rw [hrdef]; linarith
  have hA : toReal z₀ + (n : ℝ) • toReal h ∈ convHullOf R := hmemR n
  have hB : toReal z₀ + ((n : ℝ) + 1) • toReal h ∈ convHullOf R := by
    have := hmemR (n + 1)
    rwa [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring] at this
  have hcomb := hconv hA hB (by linarith : (0 : ℝ) ≤ 1 - r) hr0 (by ring)
  have heq : (1 - r) • (toReal z₀ + (n : ℝ) • toReal h)
      + r • (toReal z₀ + ((n : ℝ) + 1) • toReal h) = toReal z₀ + s • toReal h := by
    have hs' : s = (n : ℝ) + r := by rw [hrdef]; ring
    rw [hs']
    apply Prod.ext <;>
      · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
  rwa [heq] at hcomb

/-! ### `K_R` forces the translation containment -/

/-- **The containment step.**  If `h ∈ K_R` and `R` is a lattice-convex region, then
`R + h ⊆ R`.  This is where the region's lattice-convexity is used: `R = C_R ∩ ℤ²`. -/
theorem add_mem_of_mem_recCone {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {h : ℤ × ℤ} (hh : toReal h ∈ recCone R) {z : ℤ × ℤ} (hz : z ∈ R) : z + h ∈ R := by
  have hzC : toReal z ∈ convHullOf R := mem_convHullOf_of_mem hz
  have hstep : toReal z + toReal h ∈ convHullOf R := hh _ hzC
  rw [eq_preimage_convHullOf hR]
  show toReal (z + h) ∈ convHullOf R
  rwa [toReal_add]

/-- Set form of `Nivat.add_mem_of_mem_recCone`. -/
theorem subset_of_mem_recCone {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {h : ℤ × ℤ} (hh : toReal h ∈ recCone R) : ∀ z ∈ R, z + h ∈ R :=
  fun _ hz => add_mem_of_mem_recCone hR hh hz

/-! ### The bridge lemma -/

/-- **Bridge lemma (with witnesses).**  Colle [Definition 2.11] only requires a regional period
to satisfy `G (z + h) = G z` on the overlap `R ∩ (R − h)`.  Given in addition that `h, h'` lie
in the recession cone `K_R` of a lattice-convex region `R` — which the paper's §8.1 argument
supplies, because Colle's Cases 1 and 2 produce periods parallel to the two non-parallel
unbounded edges of `R`, oriented outwards — the overlap identities upgrade to identities at
every point of `R`, i.e. to `FullyPeriodicOnWith`. -/
theorem fullyPeriodicOnWith_of_overlap_of_mem_recCone
    {G : Config α} {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {h h' : ℤ × ℤ} (hdet : det h h' ≠ 0)
    (hh : toReal h ∈ recCone R) (hh' : toReal h' ∈ recCone R)
    (hper : ∀ z ∈ R, z + h ∈ R → G (z + h) = G z)
    (hper' : ∀ z ∈ R, z + h' ∈ R → G (z + h') = G z) :
    FullyPeriodicOnWith G R h h' := by
  have hsub : ∀ z ∈ R, z + h ∈ R := subset_of_mem_recCone hR hh
  have hsub' : ∀ z ∈ R, z + h' ∈ R := subset_of_mem_recCone hR hh'
  exact ⟨hdet, hsub, hsub', fun z hz => hper z hz (hsub z hz),
    fun z hz => hper' z hz (hsub' z hz)⟩

/-- **Bridge lemma.**  The form consumed by Theorem 8.7: Colle's literal conclusion (a pair of
`ℝ`-independent regional periods in the overlap sense, both lying in `K_R`) yields the
development's `FullyPeriodicOn`. -/
theorem fullyPeriodicOn_of_overlap_of_mem_recCone
    {G : Config α} {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {h h' : ℤ × ℤ} (hdet : det h h' ≠ 0)
    (hh : toReal h ∈ recCone R) (hh' : toReal h' ∈ recCone R)
    (hper : ∀ z ∈ R, z + h ∈ R → G (z + h) = G z)
    (hper' : ∀ z ∈ R, z + h' ∈ R → G (z + h') = G z) :
    FullyPeriodicOn G R :=
  ⟨h, h', fullyPeriodicOnWith_of_overlap_of_mem_recCone hR hdet hh hh' hper hper'⟩

/-- The same bridge, taking the *ray* hypotheses instead of `K_R`-membership: this is the
version closest to what Cases 1 and 2 of Colle's Lemma 4.6 literally provide, namely two
non-parallel periods `h, h'` whose forward orbits from some point of `R` remain in `R` (they are
directed along the two unbounded edges of the region). -/
theorem fullyPeriodicOn_of_overlap_of_nat_ray
    {G : Config α} {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ z₀' h h' : ℤ × ℤ} (hdet : det h h' ≠ 0)
    (hray : ∀ k : ℕ, z₀ + (k : ℤ) • h ∈ R) (hray' : ∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ R)
    (hper : ∀ z ∈ R, z + h ∈ R → G (z + h) = G z)
    (hper' : ∀ z ∈ R, z + h' ∈ R → G (z + h') = G z) :
    FullyPeriodicOn G R :=
  fullyPeriodicOn_of_overlap_of_mem_recCone hR hdet (toReal_mem_recCone_of_nat_ray hray)
    (toReal_mem_recCone_of_nat_ray hray') hper hper'

/-- Converse sanity check: the strong hypothesis implies the weak one, so the bridge lemma is
a genuine strengthening of the input rather than a change of statement.  Together with
`Nivat.mem_interior_recCone` (which extracts `h, h' ∈ K_R` from `FullyPeriodicOnWith`) this
shows that `FullyPeriodicOnWith G R h h'` is *equivalent*, for a lattice-convex `R`, to
`det h h' ≠ 0` together with `h, h' ∈ K_R` and the two overlap identities. -/
theorem fullyPeriodicOnWith_iff_overlap_and_mem_recCone
    {G : Config α} {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R) (hne : R.Nonempty)
    {h h' : ℤ × ℤ} :
    FullyPeriodicOnWith G R h h' ↔
      det h h' ≠ 0 ∧ toReal h ∈ recCone R ∧ toReal h' ∈ recCone R ∧
        (∀ z ∈ R, z + h ∈ R → G (z + h) = G z) ∧
        (∀ z ∈ R, z + h' ∈ R → G (z + h') = G z) := by
  constructor
  · intro hfp
    obtain ⟨hmem, hmem', _, _⟩ := mem_interior_recCone hR hne hfp
    obtain ⟨hdet, _, _, hGh, hGh'⟩ := hfp
    exact ⟨hdet, hmem, hmem', fun z hz _ => hGh z hz, fun z hz _ => hGh' z hz⟩
  · rintro ⟨hdet, hmem, hmem', hper, hper'⟩
    exact fullyPeriodicOnWith_of_overlap_of_mem_recCone hR hdet hmem hmem' hper hper'

end Nivat
