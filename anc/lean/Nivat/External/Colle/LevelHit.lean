/-
Lane: LevelHit
Produces `hlevel_of_coneRegion` for `htail_of_levels` (`TailLevels.lean:71`).

原文：b3_colle2.txt:396-398 (Figure 2) — a `(-ℓ, ℓ_i)`-region has two semi-infinite edges.
The edge parallel to `-ℓ` ensures every level above the base is hit.

For `coneRegion B vl u' = B + ℕvl + ℕu'` (`:780` construction), the `-ℓ` direction
is `vl`, so adding integer multiples of `vl` sweeps all levels when `dot m vl = 1`.

Consumer: `TailLevels.htail_of_levels` at `hlevel` parameter.
-/
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.L1Line0

namespace Nivat.LevelHit

open Nivat.LE2 (dot)
open Nivat.ConeRegion (coneRegion)

/-- **Level coverage for `coneRegion`** (Figure 2, `b3_colle2.txt:396-398`).

原文：Figure 2 shows that a `(-ℓ, ℓ_i)`-region has a semi-infinite edge parallel to `-ℓ`,
ensuring all levels above the base are hit.

For `coneRegion B vl u' = B + ℕvl + ℕu'` (`:780`), this translates to:
given any level `b ≥ dot m b₀` (where `b₀ ∈ B`), we can reach it by adding
`(b - dot m b₀)` copies of `vl` (since `dot m vl = 1` by normalization).

**Why this works**:
- Start with base point `b₀ ∈ B`
- Need to reach level `b` where `dot m b₀ ≤ b`
- Take `z₀ := b₀ + (b - dot m b₀) • vl`
- Then `dot m z₀ = dot m b₀ + (b - dot m b₀) * dot m vl = dot m b₀ + (b - dot m b₀) = b`
- Since `b - dot m b₀ ≥ 0`, we have `z₀ ∈ coneRegion B vl u'` by definition

The normalization `dot m vl = 1` is justified: `m` is the cutting plane normal we choose,
and under a unimodular basis with `Primitive vl`, we can take `m := expNormal u' vl`
to get `dot m vl = 1` and `dot m u' = 0` (see `EnvFit.lean:91` `dot_expNormal_add`). -/
theorem hlevel_of_coneRegion
    {B : Set (ℤ × ℤ)} {m vl u' b₀ : ℤ × ℤ}
    (hb₀ : b₀ ∈ B)
    (_hmu' : dot m u' = 0)
    (hmvl : dot m vl = 1)
    (b : ℤ) (hb : dot m b₀ ≤ b) :
    ∃ z₀ ∈ coneRegion B vl u', dot m z₀ = b := by
  -- Construct z₀ := b₀ + (b - dot m b₀) • vl
  let s := b - dot m b₀
  use b₀ + s • vl
  constructor
  · -- Show b₀ + s • vl ∈ coneRegion B vl u'
    rw [Nivat.ConeRegion.mem_coneRegion_iff]
    -- Need: ∃ b' ∈ B, ∃ s' t : ℕ, b₀ + s • vl = b' + s' • vl + t • u'
    use b₀, hb₀
    -- Since s = b - dot m b₀ ≥ 0, we can use s as s' : ℕ
    have hs_nn : 0 ≤ s := by omega
    use s.toNat, 0
    simp only [Int.toNat_of_nonneg hs_nn, Nat.cast_zero, zero_smul, add_zero]
  · -- Show dot m (b₀ + s • vl) = b
    calc dot m (b₀ + s • vl)
        = dot m b₀ + dot m (s • vl) := by
          simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
          ring
      _ = dot m b₀ + s * dot m vl := by
          simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
          ring
      _ = dot m b₀ + s * 1 := by rw [hmvl]
      _ = dot m b₀ + s := by ring
      _ = b := by omega

#print axioms hlevel_of_coneRegion

end Nivat.LevelHit
