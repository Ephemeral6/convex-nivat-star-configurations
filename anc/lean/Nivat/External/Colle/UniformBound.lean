import Nivat.External.Colle.MaximalEnveloped
import Nivat.External.Colle.EdgeSeparating

/-!
# Uniform bound for Colle's item (iv) family

**Goal**: Prove that the family `{T | EnvOf U T ∧ B ⊆ T ⊆ halfStrip B v ∧ g ∉ T}`
is uniformly bounded, so Zorn's lemma applies to get a maximal element.

**Key results** (from EdgeSeparating.lean, proved with clean axioms):
1. `exists_edge_separating`: Every point outside a finite lattice-convex region with positive
   area is separated by some edge normal
2. `dot_pos_of_separating`: A separating normal automatically satisfies `dot n v > 0`
3. `reach_bound`: This bounds the reach `t` along direction `v`

**This file**: Use those lemmas to prove uniform boundedness by taking max over `n ∈ E U`.
-/

namespace Nivat.ColleBound
open Nivat Nivat.LE2 Nivat.EdgeSeparating

/-! ## Helper lemmas -/

lemma nat_bound_of_mul_lt {t : ℕ} {nv dg db : ℤ} (hnv : 0 < nv)
    (h : (t : ℤ) * nv < dg - db) : (t : ℤ) < (dg - db - 1) / nv + 1 := by
  have h1 : (t : ℤ) * nv ≤ dg - db - 1 := by omega
  have h2 : (t : ℤ) ≤ (dg - db - 1) / nv := Int.le_ediv_of_mul_le hnv h1
  omega

/-! ## Main uniform bound theorem -/

/-- **Uniform bound for item (iv) family.**
Given finite E U, finite B, primitive v, and a forbidden point g in halfStrip B v,
the family {T | EnvOf U T ∧ B ⊆ T ⊆ halfStrip B v ∧ g ∉ T} is uniformly bounded.

**Proof idea**: Each T is separated from g by some n ∈ E T ⊆ E U. Since E U is finite,
we compute the bound for each n ∈ E U and each b ∈ B, then take the maximum.

**Assumptions**: We require that every T in the family satisfies T.Finite and PosArea T.
These will be provided by the caller depending on the specific application context. -/
theorem exists_finite_bound
    {U B : Set (ℤ × ℤ)} {v g : ℤ × ℤ}
    (hU_fin : (E U).Finite)
    (hU_ne : (E U).Nonempty)
    (hB_fin : B.Finite) (hB_ne : B.Nonempty)
    (_hv : Prim v)
    (hg : g ∈ halfStrip B v)
    (hT_finite : ∀ T, EnvOf U T → B ⊆ T → T ⊆ halfStrip B v → g ∉ T → T.Finite)
    (hT_area : ∀ T, EnvOf U T → B ⊆ T → T ⊆ halfStrip B v → g ∉ T → PosArea T)
    : ∃ W : Set (ℤ × ℤ), W.Finite ∧
        ∀ T : Set (ℤ × ℤ), EnvOf U T → B ⊆ T → T ⊆ halfStrip B v → g ∉ T → T ⊆ W := by
  -- Decompose g = b_g + t_g • v
  obtain ⟨b_g, hb_g, t_g, rfl⟩ := hg

  -- For each n ∈ E U and b ∈ B, compute bound on t
  let bound_for (n b : ℤ × ℤ) : ℤ :=
    if 0 < dot n v then
      (dot n (b_g + (t_g : ℤ) • v) - dot n b - 1) / dot n v + 1
    else
      0

  -- Collect all bounds for pairs (n, b) with n ∈ E U, b ∈ B
  let all_bounds : Set ℤ := (fun (p : (ℤ × ℤ) × (ℤ × ℤ)) => bound_for p.1 p.2) '' (E U ×ˢ B)

  -- all_bounds is finite since E U × B is finite
  have hbounds_fin : all_bounds.Finite := by
    apply Set.Finite.image
    exact Set.Finite.prod hU_fin hB_fin

  -- all_bounds is nonempty
  have hbounds_ne : all_bounds.Nonempty := by
    obtain ⟨n0, hn0⟩ := hU_ne
    obtain ⟨b0, hb0⟩ := hB_ne
    use bound_for n0 b0
    use (n0, b0)
    exact ⟨Set.mem_prod.mpr ⟨hn0, hb0⟩, rfl⟩

  -- Take t_max to be the maximum (using sSup on finite nonempty set of ℤ)
  let t_max : ℤ := sSup all_bounds

  -- For finite nonempty sets of ℤ, sSup is bounded above by all elements
  have ht_max_ub : ∀ k ∈ all_bounds, k ≤ t_max := by
    intro k hk
    exact le_csSup hbounds_fin.bddAbove hk

  -- Define W as all points reachable from B within t_max steps along v
  let W : Set (ℤ × ℤ) := {z | ∃ b ∈ B, ∃ t : ℕ, (t : ℤ) < t_max + 1 ∧ z = b + (t : ℤ) • v}

  use W
  constructor

  · -- Prove W is finite
    -- W is contained in the union over b ∈ B of finite sets {b + t•v | t < t_max + 1}
    have key : W = ⋃ b ∈ B, {z | ∃ t : ℕ, (t : ℤ) < t_max + 1 ∧ z = b + (t : ℤ) • v} := by
      ext z
      constructor
      · intro ⟨b, hb, t, ht, hz⟩
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨b, hb, t, ht, hz⟩
      · intro h
        simp only [Set.mem_iUnion, exists_prop] at h
        obtain ⟨b, hb, t, ht, hz⟩ := h
        exact ⟨b, hb, t, ht, hz⟩
    rw [key]
    apply Set.Finite.biUnion hB_fin
    intro b _
    -- For fixed b, {b + t•v | t < t_max + 1} is finite
    let fiber := {z | ∃ t : ℕ, (t : ℤ) < t_max + 1 ∧ z = b + (t : ℤ) • v}
    show fiber.Finite
    -- This is the image of {t : ℕ | (t : ℤ) < t_max + 1} under (b + · • v)
    have eq_image : fiber = (fun t : ℕ => b + (t : ℤ) • v) '' {t : ℕ | (t : ℤ) < t_max + 1} := by
      ext z; simp only [fiber, Set.mem_ofPred_eq, Set.mem_image]; tauto
    rw [eq_image]
    apply Set.Finite.image
    -- {t : ℕ | (t : ℤ) < t_max + 1} is finite
    by_cases h : 0 ≤ t_max
    · -- If t_max ≥ 0, then {t : ℕ | (t : ℤ) < t_max + 1} ⊆ {0, 1, ..., Int.toNat t_max}
      apply Set.Finite.subset (Set.finite_le_nat (Int.toNat t_max))
      intro t ht
      simp only [Set.mem_ofPred_eq] at ht ⊢
      have : (t : ℤ) ≤ t_max := by omega
      calc t = Int.toNat (t : ℤ) := by simp
           _ ≤ Int.toNat t_max := by apply Int.toNat_le_toNat; omega
    · -- If t_max < 0, then {t : ℕ | (t : ℤ) < t_max + 1} = ∅ or very small
      push Not at h
      have : ∀ t : ℕ, (t : ℤ) < t_max + 1 → t = 0 := by
        intro t ht
        by_contra hn
        have : 1 ≤ (t : ℤ) := by omega
        omega
      apply Set.Finite.subset (Set.finite_singleton 0)
      intro t ht
      simp only [Set.mem_ofPred_eq] at ht
      simp [this t ht]

  · -- Prove every T in the family is contained in W
    intro T henv hBT hTstrip hgT z hzT
    -- z ∈ T ⊆ halfStrip B v means z = b + t • v for some b ∈ B, t : ℕ
    obtain ⟨b, hb, t, rfl⟩ := hTstrip hzT

    -- Goal: show z ∈ W, i.e., (t : ℤ) < t_max + 1
    use b, hb, t

    constructor
    · -- Show (t : ℤ) < t_max + 1
      -- Get T.Finite and PosArea T from hypotheses
      have hT_fin : T.Finite := hT_finite T henv hBT hTstrip hgT
      have hT_area : PosArea T := hT_area T henv hBT hTstrip hgT

      -- IsLatticeConvexRegion T from EnvOf structure
      have hT_lc : IsLatticeConvexRegion T := henv.1.latticeConvex

      -- Apply exists_edge_separating to get n ∈ E T separating T from g
      obtain ⟨n, hn_ET, hsep⟩ := exists_edge_separating hT_fin hT_lc hT_area hgT

      -- EnvOf U T implies E T ⊆ E U via WeaklyEnveloped.E_subset
      have hn_EU : n ∈ E U := henv.1.E_subset hn_ET

      -- Apply dot_pos_of_separating
      have hnv_pos : 0 < dot n v := by
        apply dot_pos_of_separating hBT ⟨b_g, hb_g, t_g, rfl⟩ hsep

      -- Apply reach_bound to z = b + t • v
      have hreach : (t : ℤ) * dot n v < dot n (b_g + (t_g : ℤ) • v) - dot n b := by
        apply reach_bound hsep hzT rfl

      -- From hreach and hnv_pos, deduce (t : ℤ) < bound_for n b
      have hbound : (t : ℤ) < bound_for n b := by
        simp only [bound_for]
        rw [if_pos hnv_pos]
        apply nat_bound_of_mul_lt hnv_pos hreach

      -- bound_for n b ∈ all_bounds
      have hbound_in : bound_for n b ∈ all_bounds := by
        use (n, b)
        exact ⟨Set.mem_prod.mpr ⟨hn_EU, hb⟩, rfl⟩

      -- Therefore (t : ℤ) < t_max + 1
      calc (t : ℤ) < bound_for n b := hbound
           _ ≤ t_max := ht_max_ub _ hbound_in
           _ < t_max + 1 := by omega

    · -- z = b + (t : ℤ) • v
      rfl

end Nivat.ColleBound
