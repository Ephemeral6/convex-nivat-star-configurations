import Nivat.External.Colle.Claim414EllPrime
import Nivat.External.Colle.Lemma41
import Nivat.Section8.HalfPlane

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.Colle41

/-- Step 1: `convHullOf R` is convex. -/
theorem convHullOf_convex (R : Set (ℤ × ℤ)) : Convex ℝ (convHullOf R) :=
  (convex_convexHull ℝ _).closure

/-- Step 2: ray membership transfers to `convHullOf`. -/
theorem ray_mem_convHullOf {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ v : ℤ × ℤ} (hray : RayIn R z₀ v) (k : ℕ) :
    toReal (z₀ + (k:ℤ) • v) ∈ convHullOf R := by
  have hmem := hray k
  rw [eq_preimage_convHullOf hR] at hmem
  exact hmem

/-- Step 3 (continuum ray density): real nonneg multiples of `v` from `z₀` land in `convHullOf R`. -/
theorem real_ray_mem_convHullOf {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ v : ℤ × ℤ} (hray : RayIn R z₀ v) {α : ℝ} (hα : 0 ≤ α) :
    toReal z₀ + α • toReal v ∈ convHullOf R := by
  set n := ⌊α⌋₊ with hn
  set r := α - (n:ℝ) with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith [Nat.floor_le hα]
  have hr1 : r ≤ 1 := by
    rw [hr]
    have := Nat.lt_floor_add_one α
    rw [← hn] at this
    linarith
  have hA : toReal (z₀ + (n:ℤ) • v) ∈ convHullOf R := ray_mem_convHullOf hR hray n
  have hB : toReal (z₀ + ((n+1:ℕ):ℤ) • v) ∈ convHullOf R := ray_mem_convHullOf hR hray (n+1)
  have hconv := (convHullOf_convex R) hA hB (by linarith : (0:ℝ) ≤ 1 - r) hr0 (by ring)
  have heq : (1 - r) • toReal (z₀ + (n:ℤ) • v) + r • toReal (z₀ + ((n+1:ℕ):ℤ) • v)
      = toReal z₀ + α • toReal v := by
    apply Prod.ext <;>
      simp only [toReal, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
        smul_eq_mul, Int.cast_add, Nat.cast_add, Nat.cast_one] <;>
      push_cast <;> nlinarith [hr]
  rwa [heq] at hconv

/-- Step 4: the real translated cone with apex at the midpoint of the two ray basepoints
lies in `convHullOf R`. -/
theorem cone_mem_convHullOf {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ z₀' u u' : ℤ × ℤ} (hu : RayIn R z₀ u) (hu' : RayIn R z₀' u')
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (2:ℝ)⁻¹ • toReal z₀ + (2:ℝ)⁻¹ • toReal z₀' + p • toReal u + q • toReal u'
      ∈ convHullOf R := by
  have hA : toReal z₀ + (2*p) • toReal u ∈ convHullOf R :=
    real_ray_mem_convHullOf hR hu (by linarith)
  have hB : toReal z₀' + (2*q) • toReal u' ∈ convHullOf R :=
    real_ray_mem_convHullOf hR hu' (by linarith)
  have hconv := (convHullOf_convex R) hA hB
    (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹) (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹) (by norm_num)
  have heq : (2:ℝ)⁻¹ • (toReal z₀ + (2*p) • toReal u) + (2:ℝ)⁻¹ • (toReal z₀' + (2*q) • toReal u')
      = (2:ℝ)⁻¹ • toReal z₀ + (2:ℝ)⁻¹ • toReal z₀' + p • toReal u + q • toReal u' := by
    apply Prod.ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul] <;> ring
  rwa [heq] at hconv


/-- Step 5: for `det u u' ≠ 0`, every real point in the OPEN cone (apex at midpoint, `p,q > 0`)
that is additionally a lattice point (i.e. of the form `toReal w` for `w : ℤ×ℤ`) lies in `R`,
via `eq_preimage_convHullOf`. -/
theorem lattice_pt_of_cone_mem {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ z₀' u u' w : ℤ × ℤ} (hu : RayIn R z₀ u) (hu' : RayIn R z₀' u')
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hw : toReal w = (2:ℝ)⁻¹ • toReal z₀ + (2:ℝ)⁻¹ • toReal z₀' + p • toReal u + q • toReal u') :
    w ∈ R := by
  rw [eq_preimage_convHullOf hR]
  show toReal w ∈ convHullOf R
  rw [hw]
  exact cone_mem_convHullOf hR hu hu' hp hq


/-- Step 6: the main theorem — `R` contains a translate of any finite set `W`,
given two rays from `IsLatticeConvexRegion R` with linearly independent directions. -/
theorem exists_translate_mem {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ z₀' u u' : ℤ × ℤ} (hu : RayIn R z₀ u) (hu' : RayIn R z₀' u')
    (hdet : det u u' ≠ 0) (W : Finset (ℤ × ℤ)) :
    ∃ b : ℤ × ℤ, ∀ z ∈ W, b + z ∈ R := by
  classical
  set D : ℝ := (u.1:ℝ) * (u'.2:ℝ) - (u.2:ℝ) * (u'.1:ℝ) with hDdef
  have hD : D ≠ 0 := by
    have : ((det u u' : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hdet
    simpa [hDdef, det] using this
  set c1 : ℝ := (2:ℝ)⁻¹ * (z₀.1:ℝ) + (2:ℝ)⁻¹ * (z₀'.1:ℝ) with hc1
  set c2 : ℝ := (2:ℝ)⁻¹ * (z₀.2:ℝ) + (2:ℝ)⁻¹ * (z₀'.2:ℝ) with hc2
  -- error terms for a point z, not depending on N
  set ep : ℤ × ℤ → ℝ := fun z => (((z.1:ℝ) - c1) * (u'.2:ℝ) - ((z.2:ℝ) - c2) * (u'.1:ℝ)) / D
    with hep
  set eq' : ℤ × ℤ → ℝ := fun z => ((u.1:ℝ) * ((z.2:ℝ) - c2) - (u.2:ℝ) * ((z.1:ℝ) - c1)) / D
    with heq'
  rcases W.eq_empty_or_nonempty with hW | hW
  · exact ⟨0, by simp [hW]⟩
  · -- choose N large enough to dominate all error terms
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ z ∈ W, -(ep z) ≤ (N:ℝ) ∧ -(eq' z) ≤ (N:ℝ) := by
      have hbound : ∃ M : ℝ, ∀ z ∈ W, -(ep z) ≤ M ∧ -(eq' z) ≤ M := by
        refine ⟨(W.sup' hW (fun z => max (-(ep z)) (-(eq' z)))), fun z hz => ?_⟩
        constructor
        · exact le_trans (le_max_left _ _) (Finset.le_sup' (fun z => max (-(ep z)) (-(eq' z))) hz)
        · exact le_trans (le_max_right _ _) (Finset.le_sup' (fun z => max (-(ep z)) (-(eq' z))) hz)
      obtain ⟨M, hM⟩ := hbound
      obtain ⟨N, hN⟩ := exists_nat_ge M
      exact ⟨N, fun z hz => ⟨le_trans (hM z hz).1 hN, le_trans (hM z hz).2 hN⟩⟩
    refine ⟨(N:ℤ) • (u + u'), fun z hz => ?_⟩
    set b : ℤ × ℤ := (N:ℤ) • (u + u') with hbdef
    set w : ℤ × ℤ := b + z with hwdef
    set p : ℝ := (N:ℝ) + ep z with hp
    set q : ℝ := (N:ℝ) + eq' z with hq
    have hp0 : 0 ≤ p := by rw [hp]; linarith [(hN z hz).1]
    have hq0 : 0 ≤ q := by rw [hq]; linarith [(hN z hz).2]
    apply lattice_pt_of_cone_mem hR hu hu' hp0 hq0 (w := w) (p := p) (q := q)
    -- verify the coordinate identity
    have hb1 : (b.1 : ℝ) = (N:ℝ) * ((u.1:ℝ) + (u'.1:ℝ)) := by
      simp [hbdef, Prod.add_def]
    have hb2 : (b.2 : ℝ) = (N:ℝ) * ((u.2:ℝ) + (u'.2:ℝ)) := by
      simp [hbdef, Prod.add_def]
    apply Prod.ext
    · show (w.1:ℝ) = _
      have hw1 : (w.1:ℝ) = (b.1:ℝ) + (z.1:ℝ) := by simp [hwdef, Prod.add_def]
      rw [hw1, hb1]
      simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul, toReal]
      show _ = c1 + p * (u.1:ℝ) + q * (u'.1:ℝ)
      rw [hp, hq, hep, heq']
      field_simp
      ring
    · show (w.2:ℝ) = _
      have hw2 : (w.2:ℝ) = (b.2:ℝ) + (z.2:ℝ) := by simp [hwdef, Prod.add_def]
      rw [hw2, hb2]
      simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul, toReal]
      show _ = c2 + p * (u.2:ℝ) + q * (u'.2:ℝ)
      rw [hp, hq, hep, heq']
      field_simp
      ring

/-- **Ray refinement.**  A lattice-convex region containing the ray `z₀ + ℕ·(n • v)` with
`n > 0` contains the finer ray `z₀ + ℕ·v`.

This is the bridge between the two sign conventions in play around Claim 4.14.  The producers
of a periodic ray hand back a *positive multiple* of the line direction — `lemma41_of_sweep`
(`Lemma41.lean:723`) builds `h' := ((t₀ * q : ℕ) : ℤ) • u'` with `t₀ * q > 0` (`:729`), and the
retired `region_periods_and_rays_of_geom` (`ChainGeom.lean:228`) builds `(N.natAbs : ℤ) • cg.vJ`
— whereas `Claim414.claim414_ellprime` (`Claim414EllPrime.lean:160`) consumes a ray along
`cg.vJ` itself.  Convexity closes the gap, and only for a *positive* multiple: for `n < 0` the
hypothesis describes the `-v` ray and the conclusion is false in general. -/
theorem rayIn_of_rayIn_nsmul {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z₀ v : ℤ × ℤ} {n : ℕ} (hn : 0 < n) (hray : RayIn R z₀ ((n : ℤ) • v)) :
    RayIn R z₀ v := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  intro k
  rw [eq_preimage_convHullOf hR]
  show toReal (z₀ + (k : ℤ) • v) ∈ convHullOf R
  have hmem := real_ray_mem_convHullOf hR hray (α := (k : ℝ) / (n : ℝ)) (by positivity)
  have heq : toReal z₀ + ((k : ℝ) / (n : ℝ)) • toReal ((n : ℤ) • v)
      = toReal (z₀ + (k : ℤ) • v) := by
    rw [toReal_add, toReal_zsmul, toReal_zsmul, smul_smul]
    congr 2
    push_cast
    field_simp
  rwa [heq] at hmem

end Nivat.ColleReg
