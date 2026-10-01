/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.L1StraddleMax
import Nivat.External.Colle.MaximalEnveloped
import Nivat.External.Colle.L3Cover
import Nivat.External.Colle.HalfPlaneShells
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.L1Region

/-!
# L1 Figure 11(B) cover and generator package

**Source**: Collé, arXiv:1909.08195v4, `b3_colle2.txt:848-856` (Figure 11(B)).

This file provides the two pieces needed for Figure 11(B) of Collé's proof:
1. The existence of a generating set `𝒮_φ` with an anchor point `a` (target 1).
2. The cover theorem stating that `overlap Rhi (c•u)` is contained in the
   `genClosure` of the seed `overlap Rlo (c•u) ∪ ray g u' t₀` (target 2).

## Original text (:848-856)

"(see Figure 11(A)). In any case, by using that 𝒮_φ is η-generating, we get that
(T^u η)|_{ℝ^{N+1}_I} = (T^h(T^u η))|_{ℝ^{N+1}_I} (see Figure 11(B)), which contradicts
the maximality of N ∈ ℤ₊ and proves the claim.

(B) Let Ŝ_φ denote a translation of 𝒮_φ. Since Ŝ_φ is η-generating, the knowledge of
a configuration on ℝ^N_I ∪ {g + t v_ℓ' : t ≥ t₀} determines uniquely such a
configuration on ℝ^{N+1}_I."

The generating set 𝒮_φ comes from the periodic decomposition (`:764`), and any
translation of it is still generating. The "determines uniquely" is implemented by
`Nivat.MaxEnv.genClosure` and the propagation by
`Nivat.L3Cover.agree_on_genClosure_of_generatesAt`.

## Consumer

`Nivat.External.Colle.RegionSteps.exists_cutResidualR_of_claim46_ofPieces` at `:1651-1653`
needs `Sφ : Finset (ℤ × ℤ)`, `a : ℤ × ℤ`, and `hgen : Nivat.Colle.GeneratesAt ξ Sφ a`.
The cover `hcover` at `:1670-1677` is the geometric content this file addresses.

-/

set_option autoImplicit false

namespace Nivat.L1CoverPackage

open Nivat Nivat.Colle Nivat.Colle35 Nivat.Colle41 Nivat.MaxEnv Nivat.L1Region Nivat.L1StraddleMax

variable {ξ : Config ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}

/-! ## Target 1: Existence of generating set package

原文：b3_colle2.txt:848-856, especially :856 "Let Ŝ_φ denote a translation of 𝒮_φ.
Since Ŝ_φ is η-generating..."

The generating set 𝒮_φ is part of the decomposition data that comes from
`IsMinimalCounterexample ξ`. The anchor point `a` can be any vertex of 𝒮_φ.
-/

/-- **Figure 11(B) generator package exists.**

Given a `DecompDataZ ξ` (which records the periodic decomposition from `:764`),
we can produce a generating set `𝒮_φ` and an anchor point `a` such that
`GeneratesAt ξ 𝒮_φ a` holds.

原文：b3_colle2.txt:848 "by using that 𝒮_φ is η-generating" and :856
"Since Ŝ_φ is η-generating" (any translation works).

The key fact is `DecompDataZ.isGeneratingSet` (`DecompData.lean:195`), which states
that 𝒮_φ is an η-generating set. This implies `GeneratesAt ξ 𝒮_φ a` for any vertex `a`
by the definition of `IsGeneratingSet` (`Generating.lean:58`).
-/
theorem exists_gen_package (d : Nivat.Colle35.DecompDataZ ξ) :
    ∃ (Sφ : Finset (ℤ × ℤ)) (a : ℤ × ℤ), Nivat.Colle.GeneratesAt ξ Sφ a := by
  -- Use d.toDecompData.Sphi as the generating set
  -- Apply the fact that Sphi is a generating set
  have hgen_set : IsGeneratingSet ξ d.toDecompData.Sphi := d.isGeneratingSet
  -- exists_vertex_of_generating (HalfPlaneShells.lean:55) extracts a generating vertex
  obtain ⟨a, ha, _, hgen_a⟩ := Nivat.Colle.exists_vertex_of_generating hgen_set
  exact ⟨d.toDecompData.Sphi, a, hgen_a⟩

/-! ## Target 2: Cover theorem with explicit row-structure binders

原文：b3_colle2.txt:856 "Let Ŝ_φ denote a translation of 𝒮_φ. Since Ŝ_φ is η-generating,
the knowledge of a configuration on ℝ^N_I ∪ {g + t v_ℓ' : t ≥ t₀} determines uniquely
such a configuration on ℝ^{N+1}_I."

-/

/-- **Overlap lift by arithmetic: monotonicity of overlap with respect to cuts.**

If `z ∈ cut N`, `z + c•vl ∈ cut (N+1)`, and `c > 0`, `dot m vl > 0`, then
`z + c•vl ∈ cut N` (since `dot m (z + c•vl) = dot m z + c·dot m vl ≥ lev N`).

This implies `overlap (cut (N+1)) (c•vl) ∩ cut N = overlap (cut N) (c•vl)`.
-/
theorem overlap_lift_of_pos
    {Rinf : Set (ℤ × ℤ)} {m vl : ℤ × ℤ} {c : ℤ} (lev : ℕ → ℤ) (N : ℕ)
    (hmvl : 0 < Nivat.LE2.dot m vl) (hc : 0 < c)
    (hRinf : ∀ z ∈ Rinf, z + c • vl ∈ Rinf) :
    ∀ z, z ∈ Nivat.L1Region.cut Rinf m lev N →
      z ∈ overlap (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) →
      z ∈ overlap (Nivat.L1Region.cut Rinf m lev N) (c • vl) := by
  intro z hzN hz
  -- hz: z ∈ overlap (cut (N+1)) (c•vl) means z ∈ cut (N+1) ∧ z + c•vl ∈ cut (N+1)
  obtain ⟨hzN1, hzc_N1⟩ := hz
  -- Need: z ∈ cut N ∧ z + c•vl ∈ cut N
  constructor
  · exact hzN
  · -- Need: z + c•vl ∈ cut N
    -- cut N = {z ∈ Rinf | dot m z ≥ lev N}
    -- We have: z ∈ cut N (so dot m z ≥ lev N), and z + c•vl ∈ Rinf (from hRinf)
    -- Need: dot m (z + c•vl) ≥ lev N
    constructor
    · -- z + c•vl ∈ Rinf
      exact hRinf z hzN.1
    · -- dot m (z + c•vl) ≥ lev N
      have hzN_lev : lev N ≤ Nivat.LE2.dot m z := hzN.2
      have hpos : 0 < c * Nivat.LE2.dot m vl := Int.mul_pos hc hmvl
      -- Unfold halfPlaneGE to get set membership
      show z + c • vl ∈ Nivat.LE2.halfPlaneGE m (lev N)
      unfold Nivat.LE2.halfPlaneGE
      -- Now goal is: z + c • vl ∈ {z | lev N ≤ LE2.dot m z}
      show lev N ≤ Nivat.LE2.dot m (z + c • vl)
      -- Use dot_add
      have key := Nivat.LE2.dot_add m z (c • vl)
      rw [key]
      have hdot_smul : Nivat.LE2.dot m (c • vl) = c * Nivat.LE2.dot m vl := by
        cases m with | mk m1 m2 =>
        cases vl with | mk v1 v2 =>
        unfold Nivat.LE2.dot
        simp only [Prod.smul_mk, smul_eq_mul]
        ring
      rw [hdot_smul]
      omega

/-- **Figure 11(B) cover theorem with explicit row-structure binders.**

原文：b3_colle2.txt:856 "Since Ŝ_φ is η-generating, the knowledge of a configuration on
ℝ^N_I ∪ {g + t v_ℓ' : t ≥ t₀} determines uniquely such a configuration on ℝ^{N+1}_I."

This conditional version makes the geometric structure explicit via hypotheses:

1. `base`, `henum_covers` (`:818`): explicit enumeration of gap w-lines
2. `henum_in_cut`, `henum_gap_only`: enumeration is well-formed (gap-only points in cut (N+1))
3. `hstep` (`:856`): Each point is window-covered from the seed union ray
4. `hmvl`, `hc`, `hRinf`: arithmetic inputs for `overlap_lift_of_pos` (replaces `hoverlap_lift`)

**Proof strategy**: Apply `L3Cover.subset_genClosure_of_window_of_covers` with
`enum i j := base i + (j : ℤ) • w`. The overlap lift property is derived arithmetically.
-/
theorem cover_of_fig11B_of_rows
    {Sφ : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {Rinf : Set (ℤ × ℤ)} {w vl : ℤ × ℤ} {c : ℤ}
    {m : ℤ × ℤ}
    (lev : ℕ → ℤ) (N : ℕ)
    (g : ℤ × ℤ) (t₀ : ℤ)
    (hmvl : 0 < Nivat.LE2.dot m vl) (hc : 0 < c)
    (hRinf : ∀ z ∈ Rinf, z + c • vl ∈ Rinf)
    -- Enumeration of base points for w-lines in the gap (`:818`)
    (base : ℕ → ℤ × ℤ)
    (henum_covers : ∀ z ∈ Nivat.L1Region.cut Rinf m lev (N + 1),
      z ∉ Nivat.L1Region.cut Rinf m lev N →
      ∃ i j : ℕ, z = base i + (j : ℤ) • w)
    -- Enumeration is well-formed: all enum points are in cut (N+1)
    (henum_in_cut : ∀ i j : ℕ, base i + (j : ℤ) • w ∈ Nivat.L1Region.cut Rinf m lev (N + 1))
    -- Enumeration only produces gap points (not in cut N)
    (henum_gap_only : ∀ i j : ℕ, base i + (j : ℤ) • w ∉ Nivat.L1Region.cut Rinf m lev N)
    -- Window-step hypothesis (`:856`)
    (hstep : ∀ i j : ℕ,
      base i + (j : ℤ) • w ∈ Nivat.L1Region.cut Rinf m lev (N + 1) →
      base i + (j : ℤ) • w ∉ Nivat.L1Region.cut Rinf m lev N →
      ∀ b ∈ Sφ.erase a,
        b + (base i + (j : ℤ) • w - a) ∈
          overlap (Nivat.L1Region.cut Rinf m lev N) (c • vl) ∪ ray g w t₀ ∨
          ∃ j' : ℕ, j' < j ∧ b + (base i + (j : ℤ) • w - a) = base i + (j' : ℤ) • w) :
    overlap (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) ⊆
      genClosure Sφ a (overlap (Nivat.L1Region.cut Rinf m lev N) (c • vl) ∪ ray g w t₀) := by

  set D := overlap (Nivat.L1Region.cut Rinf m lev N) (c • vl) ∪ ray g w t₀
  set K := overlap (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl)

  -- Step 1: Define enumeration enum i j := base i + (j : ℤ) • w
  set enum : ℕ → ℕ → ℤ × ℤ := fun i j => base i + (j : ℤ) • w

  -- Derive hoverlap_lift from overlap_lift_of_pos
  have hoverlap_lift : ∀ z, z ∈ Nivat.L1Region.cut Rinf m lev N →
      z ∈ overlap (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) →
      z ∈ overlap (Nivat.L1Region.cut Rinf m lev N) (c • vl) :=
    overlap_lift_of_pos lev N hmvl hc hRinf

  -- Step 2: Prove hwindow from hstep
  have hwindow : ∀ i j : ℕ, ∀ z ∈ Sφ.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' : ℕ | j' < j}) := by
    intro i j z hz
    show z + (base i + (j : ℤ) • w - a) ∈
        D ∪ (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' : ℕ | j' < j})
    by_cases hcut : enum i j ∈ Nivat.L1Region.cut Rinf m lev N
    · -- enum i j ∈ cut N, but henum_gap_only says enum i j ∉ cut N
      exfalso
      exact henum_gap_only i j hcut
    · -- enum i j ∉ cut N, so it's in the gap
      have hcutN1 := henum_in_cut i j
      have hstep_ij := hstep i j hcutN1 hcut z hz
      rcases hstep_ij with h1 | ⟨j', hj', heq⟩
      · left; left; exact h1
      · right
        simp only [Set.mem_image, Set.mem_ofPred_eq]
        use j', hj'
        exact heq.symm

  -- Step 3: Prove hcovers from henum_covers
  have hcovers : K ⊆ D ∪ (⋃ i, Set.range (enum i)) := by
    intro z hz
    have hz_cutN1 : z ∈ Nivat.L1Region.cut Rinf m lev (N + 1) := hz.1
    by_cases hzN : z ∈ Nivat.L1Region.cut Rinf m lev N
    · left; left
      exact hoverlap_lift z hzN hz
    · obtain ⟨i, j, heq⟩ := henum_covers z hz_cutN1 hzN
      right
      simp only [Set.mem_iUnion, Set.mem_range]
      use i, j
      exact heq.symm

  -- Step 4: Apply subset_genClosure_of_window_of_covers
  exact Nivat.L3Cover.subset_genClosure_of_window_of_covers hwindow hcovers

/-- **Figure 11(B) cover theorem, enumerated leftwards from the ray (`base i - j•w`).**

原文：同 `cover_of_fig11B_of_rows`（`:856`），但枚举方向相反：team-lead 指出 `hstep` 的机制
（`𝒮_φ` 以 `−w` 端为锚点放置，同边其余点朝 `+w`／朝 ray 方向，已知）要求「更早」是**更大**的
`w`-坐标（靠近 `t₀ ≤ t` 的 ray 尾巴），「更晚」（待推出）是更小的坐标，一路推到行首
`base i`。这里 `base i` 仍是行首（`henum_*` 的形状不变，只是 `enum i j := base i − j•w`），
`hstep` 的「已知」分支现在是 `j' < j`（更接近 ray 的、坐标更大的点）。

证明与 `cover_of_fig11B_of_rows` 相同，仅把 `enum` 的位移方向换号；不复用前者（`ray g w t₀`
的方向必须保持 `w` 不变，不能靠对整条定理代入 `w ↦ -w` 来偷懒，那样连 ray 方向都会翻）。 -/
theorem cover_of_fig11B_of_rows'
    {Sφ : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {Rinf : Set (ℤ × ℤ)} {w vl : ℤ × ℤ} {c : ℤ}
    {m : ℤ × ℤ}
    (lev : ℕ → ℤ) (N : ℕ)
    (g : ℤ × ℤ) (t₀ : ℤ)
    (hmvl : 0 < Nivat.LE2.dot m vl) (hc : 0 < c)
    (hRinf : ∀ z ∈ Rinf, z + c • vl ∈ Rinf)
    -- Enumeration of base points for w-lines in the gap (`:818`), leftward from `base i`.
    (base : ℕ → ℤ × ℤ)
    (henum_covers : ∀ z ∈ Nivat.L1Region.cut Rinf m lev (N + 1),
      z ∉ Nivat.L1Region.cut Rinf m lev N →
      ∃ i j : ℕ, z = base i - (j : ℤ) • w)
    (henum_in_cut : ∀ i j : ℕ, base i - (j : ℤ) • w ∈ Nivat.L1Region.cut Rinf m lev (N + 1))
    (henum_gap_only : ∀ i j : ℕ, base i - (j : ℤ) • w ∉ Nivat.L1Region.cut Rinf m lev N)
    -- Window-step hypothesis (`:856`): "known" fallback now has LARGER `j'` (closer to the ray).
    (hstep : ∀ i j : ℕ,
      base i - (j : ℤ) • w ∈ Nivat.L1Region.cut Rinf m lev (N + 1) →
      base i - (j : ℤ) • w ∉ Nivat.L1Region.cut Rinf m lev N →
      ∀ b ∈ Sφ.erase a,
        b + (base i - (j : ℤ) • w - a) ∈
          overlap (Nivat.L1Region.cut Rinf m lev N) (c • vl) ∪ ray g w t₀ ∨
          ∃ j' : ℕ, j' < j ∧ b + (base i - (j : ℤ) • w - a) = base i - (j' : ℤ) • w) :
    overlap (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) ⊆
      genClosure Sφ a (overlap (Nivat.L1Region.cut Rinf m lev N) (c • vl) ∪ ray g w t₀) := by

  set D := overlap (Nivat.L1Region.cut Rinf m lev N) (c • vl) ∪ ray g w t₀
  set K := overlap (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl)

  set enum : ℕ → ℕ → ℤ × ℤ := fun i j => base i - (j : ℤ) • w

  have hoverlap_lift : ∀ z, z ∈ Nivat.L1Region.cut Rinf m lev N →
      z ∈ overlap (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) →
      z ∈ overlap (Nivat.L1Region.cut Rinf m lev N) (c • vl) :=
    overlap_lift_of_pos lev N hmvl hc hRinf

  have hwindow : ∀ i j : ℕ, ∀ z ∈ Sφ.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' : ℕ | j' < j}) := by
    intro i j z hz
    show z + (base i - (j : ℤ) • w - a) ∈
        D ∪ (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' : ℕ | j' < j})
    by_cases hcut : enum i j ∈ Nivat.L1Region.cut Rinf m lev N
    · exfalso
      exact henum_gap_only i j hcut
    · have hcutN1 := henum_in_cut i j
      have hstep_ij := hstep i j hcutN1 hcut z hz
      rcases hstep_ij with h1 | ⟨j', hj', heq⟩
      · left; left; exact h1
      · right
        simp only [Set.mem_image, Set.mem_ofPred_eq]
        use j', hj'
        exact heq.symm

  have hcovers : K ⊆ D ∪ (⋃ i, Set.range (enum i)) := by
    intro z hz
    have hz_cutN1 : z ∈ Nivat.L1Region.cut Rinf m lev (N + 1) := hz.1
    by_cases hzN : z ∈ Nivat.L1Region.cut Rinf m lev N
    · left; left
      exact hoverlap_lift z hzN hz
    · obtain ⟨i, j, heq⟩ := henum_covers z hz_cutN1 hzN
      right
      simp only [Set.mem_iUnion, Set.mem_range]
      use i, j
      exact heq.symm

  exact Nivat.L3Cover.subset_genClosure_of_window_of_covers hwindow hcovers

end Nivat.L1CoverPackage

#print axioms Nivat.L1CoverPackage.cover_of_fig11B_of_rows'
