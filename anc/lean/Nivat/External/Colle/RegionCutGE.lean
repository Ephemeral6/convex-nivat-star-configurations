/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma41
import Nivat.External.Colle.LatticeEdges
import Nivat.Section8.RegionUpgrade

set_option autoImplicit false

open Nivat

namespace Nivat.LE2

/-! ## Cutting a region by an integral half-plane

`b3_colle2.txt:700`: Lemma 4.1 outputs `𝒦 = ℋ(ℓ_{Q'}) ∩ ℛ`.  This file supplies the two
facts that make that intersection a region again, for the 3-conjunct `Colle41.IsRegion`
used by `case1_sweep`.
-/

/-- Lattice convexity is preserved by intersecting with an integral half-plane:
if `R = C ∩ ℤ²` for a closed convex `C ⊆ ℝ²`, then `R ∩ {z | c ≤ ⟨n, z⟩}` is cut out by
`C` intersected with the corresponding closed half-space. -/
theorem isLatticeConvexRegion_inter_halfPlaneGE
    {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R) (n : ℤ × ℤ) (c : ℤ) :
    IsLatticeConvexRegion (R ∩ halfPlaneGE n c) := by
  obtain ⟨C, hCconv, hCclosed, hReq⟩ := hR
  set f : ℝ × ℝ → ℝ := fun x => (n.1 : ℝ) * x.1 + (n.2 : ℝ) * x.2 with hf
  have hlin : IsLinearMap ℝ f := by
    constructor
    · intro x y; simp only [hf, Prod.fst_add, Prod.snd_add]; ring
    · intro t x; simp only [hf, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hcont : Continuous f := by
    simp only [hf]
    fun_prop
  refine ⟨C ∩ {x : ℝ × ℝ | (c : ℝ) ≤ f x}, hCconv.inter (convex_halfSpace_ge hlin _),
    hCclosed.inter (isClosed_le continuous_const hcont), ?_⟩
  rw [Set.preimage_inter, ← hReq]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_setOf_eq, halfPlaneGE, dot, toReal, hf]
  exact_mod_cast Iff.rfl

private theorem dot_add_nsmul (n q e : ℤ × ℤ) (k : ℕ) :
    dot n (q + (k : ℤ) • e) = dot n q + (k : ℤ) * dot n e := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **The cut lemma for `Colle41.IsRegion`** (`b3_colle2.txt:700`).

`R ∩ ℋ` is again an `(u, u')`-region when the cutting line is parallel to `u`
(`dot n u = 0`, so the `u`-ray runs along the boundary) and points strictly into the
half-plane along `u'` (`0 < dot n u'`, so the `u'`-ray eventually enters and stays).

No base point is assumed: both rays are produced.  The `u'`-ray is pushed into the
half-plane by `0 < dot n u'`, and the `u`-ray is then re-based at that same point, using
that `u` is a recession direction of `R` (`toReal_mem_recCone_of_nat_ray`). -/
theorem isRegion_inter_halfPlaneGE
    {R : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (hR : Colle41.IsRegion R u u')
    (n : ℤ × ℤ) (c : ℤ) (hnu : dot n u = 0) (hnu' : 0 < dot n u') :
    Colle41.IsRegion (R ∩ halfPlaneGE n c) u u' := by
  obtain ⟨hconv, ⟨z₀, hray⟩, ⟨z₀', hray'⟩⟩ := hR
  -- Push the `u'`-ray base into the half-plane.
  set k₀ : ℕ := (c - dot n z₀').toNat with hk₀
  set z₁ : ℤ × ℤ := z₀' + (k₀ : ℤ) • u' with hz₁
  have hk₀_ge : c - dot n z₀' ≤ (k₀ : ℤ) := Int.self_le_toNat _
  have hdot_z₁ : c ≤ dot n z₁ := by
    have h1 : (k₀ : ℤ) * 1 ≤ (k₀ : ℤ) * dot n u' :=
      mul_le_mul_of_nonneg_left hnu' (Int.natCast_nonneg k₀)
    have : c ≤ dot n z₀' + (k₀ : ℤ) := by omega
    calc c ≤ dot n z₀' + (k₀ : ℤ) := this
      _ = dot n z₀' + (k₀ : ℤ) * 1 := by ring
      _ ≤ dot n z₀' + (k₀ : ℤ) * dot n u' := by omega
      _ = dot n z₁ := by rw [hz₁, dot_add_nsmul]
  have hz₁_mem : z₁ ∈ R := by rw [hz₁]; exact hray' k₀
  refine ⟨isLatticeConvexRegion_inter_halfPlaneGE hconv n c, ⟨z₁, ?_⟩, ⟨z₁, ?_⟩⟩
  · -- the `u`-ray, re-based at `z₁`: `u` is a recession direction and `dot n u = 0`
    have hrec : toReal u ∈ recCone R := toReal_mem_recCone_of_nat_ray hray
    have hstep : ∀ k : ℕ, z₁ + (k : ℤ) • u ∈ R := by
      intro k
      induction k with
      | zero => simpa using hz₁_mem
      | succ m ih =>
        have := add_mem_of_mem_recCone hconv hrec ih
        have he : z₁ + (m : ℤ) • u + u = z₁ + ((m + 1 : ℕ) : ℤ) • u := by
          push_cast
          module
        rwa [he] at this
    intro k
    refine ⟨hstep k, ?_⟩
    show c ≤ dot n (z₁ + (k : ℤ) • u)
    rw [dot_add_nsmul, hnu, mul_zero, add_zero]
    exact hdot_z₁
  · -- the `u'`-ray from `z₁`, which only moves further into the half-plane
    intro k
    constructor
    · have he : z₁ + (k : ℤ) • u' = z₀' + ((k₀ + k : ℕ) : ℤ) • u' := by
        rw [hz₁]
        push_cast
        module
      rw [he]
      exact hray' (k₀ + k)
    · show c ≤ dot n (z₁ + (k : ℤ) • u')
      rw [dot_add_nsmul]
      have : 0 ≤ (k : ℤ) * dot n u' :=
        mul_nonneg (Int.natCast_nonneg k) (le_of_lt hnu')
      omega

end Nivat.LE2

