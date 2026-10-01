/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Region
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.RegionCut

/-!
# Abstract gap enumeration from structural properties

原文：b3_colle2.txt:818 "the gap 𝓡^{N+1}_I \ 𝓡^N_I consists of finitely many w-lines"

**Goal**: Prove that `henum_covers`, `henum_in_cut`, and `henum_gap_only` follow from
two structural properties of `Rinf`:

1. **Ray closure** `hray : ∀ z ∈ Rinf, z + w ∈ Rinf` — `Rinf` is closed under `+w`
2. **Row starting points** `hbdd : ∀ z ∈ Rinf, ∃ p ∈ Rinf, ∃ j : ℕ, z = p + j•w ∧ p − w ∉ Rinf`
   — each w-row in `Rinf` has a well-defined starting point

These are exactly the properties of a "two half-infinite edges" region (`:386`).

## Key insight: one row per level when m is primitive

When `Prim m` and `dot m w = 0`:
- All points with `dot m z = ℓ` lie on the affine line `{z : dot m z = ℓ}`
- This line's direction is `ker(dot m)`, which equals `ℤ•dir m` when `m` is primitive
- Since `w` also satisfies `dot m w = 0`, we have `w = ±dir m` (both primitive and perpendicular)
- Therefore: **at most one w-row per level**

2026-09-22 (lane-place, cover task): this file previously carried two `sorry`s that tried to
prove "for every index `i < num_levels`, a witness point exists at that level" — that claim is
FALSE in general (a level inside the gap band need not actually be occupied by a point of
`Rinf`; `hray`/`hbdd` say nothing about density). The fix does not need that claim: `base`'s own
definition already case-splits on witness-existence directly (`Classical.choose` under a
`dif`), so `henum_in_cut`/`henum_gap_only` are read straight off whichever witness `base`
actually chose (or the `p_wit` fallback), without ever asking whether `i < num_levels`.
-/

set_option autoImplicit false

namespace Nivat.L1CoverPackage

open Nivat Nivat.LE2 Nivat.L1Region Nivat.ConeRegion Classical

variable {Rinf : Set (ℤ × ℤ)} {m w : ℤ × ℤ} {lev : ℕ → ℤ} {N : ℕ}

/-- `dot m` distributes over `ℤ`-smul in the second argument. -/
theorem dot_zsmul_right (m z : ℤ × ℤ) (k : ℤ) : dot m (k • z) = k * dot m z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-! ## §1. One row per level when m is primitive -/

/-- If `m` is primitive and `dot m w = 0`, then two points on the same level
differ by a multiple of `w`.

原文：b3_colle2.txt:386 "two half-infinite edges" — points on the same
dot-m level lie on a single w-line.

Uses `exists_zsmul_dir_of_mem_face` from RegionCut.lean:173. -/
theorem same_level_iff_on_wline
    (hm : Prim m) (hmw : Nivat.LE2.dot m w = 0) (hw_prim : Prim w)
    {z z' : ℤ × ℤ} (hlev : Nivat.LE2.dot m z = Nivat.LE2.dot m z') :
    ∃ k : ℤ, z' = z + k • w := by
  have hdot : Nivat.LE2.dot m (z' - z) = 0 := by
    rw [Nivat.LE2.dot_sub, hlev]
    ring
  have hdet : det w (z' - z) = 0 :=
    det_eq_zero_of_dot_eq_zero hm.ne_zero hmw hdot
  obtain ⟨k, hk⟩ := exists_smul_of_det_eq_zero hw_prim hdet
  refine ⟨k, ?_⟩
  have hk' : z' - z = k • w := hk
  rw [← hk']; ring

/-- Helper: Iteration of `hray` for natural number steps. -/
lemma add_nsmul_mem (hray : ∀ z ∈ Rinf, z + w ∈ Rinf)
    (p : ℤ × ℤ) (hp : p ∈ Rinf) (j : ℕ) :
    p + (j : ℤ) • w ∈ Rinf := by
  induction j with
  | zero => simpa using hp
  | succ j ih =>
    have heq : p + ((j + 1 : ℕ) : ℤ) • w = (p + (j : ℤ) • w) + w := by push_cast; ring
    rw [heq]
    exact hray _ ih

/-- If `Prim m` and `dot m w = 0`, then each level in `Rinf` has at most one w-row
starting point (a point whose predecessor is not in `Rinf`). -/
theorem at_most_one_row_start_per_level
    (hm : Prim m) (hmw : dot m w = 0) (hw_prim : Prim w)
    (hray : ∀ z ∈ Rinf, z + w ∈ Rinf)
    {p p' : ℤ × ℤ}
    (hp : p ∈ Rinf) (hp_start : p - w ∉ Rinf)
    (hp' : p' ∈ Rinf) (hp'_start : p' - w ∉ Rinf)
    (hlev : dot m p = dot m p') :
    p = p' := by
  obtain ⟨k, hk⟩ := same_level_iff_on_wline hm hmw hw_prim hlev
  by_cases hk_zero : k = 0
  · rw [hk_zero, zero_smul, add_zero] at hk
    exact hk.symm
  · by_cases hk_pos : 0 < k
    · -- k > 0: p' = p + k•w with k ≥ 1, so p' - w = p + (k-1)•w ∈ Rinf, contradicting hp'_start
      have hk_nat : ∃ n : ℕ, 1 ≤ n ∧ k = (n : ℤ) := ⟨k.toNat, by omega, by omega⟩
      obtain ⟨n, hn_ge, hk_eq⟩ := hk_nat
      have hcast : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
      have heq0 : p' - w = p + ((n : ℤ) - 1) • w := by rw [hk, hk_eq]; ring
      have heq : p' - w = p + ((n - 1 : ℕ) : ℤ) • w := by rw [heq0, hcast]
      have hp'_w : p' - w ∈ Rinf := by rw [heq]; exact add_nsmul_mem hray p hp (n - 1)
      exact absurd hp'_w hp'_start
    · -- k < 0: p = p' + (-k)•w with -k ≥ 1, so p - w = p' + ((-k)-1)•w ∈ Rinf, contradicting hp_start
      have hk_nat : ∃ n : ℕ, 1 ≤ n ∧ -k = (n : ℤ) := ⟨(-k).toNat, by omega, by omega⟩
      obtain ⟨n, hn_ge, hkeq⟩ := hk_nat
      have hcast : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
      have hp_eq : p = p' + (-k) • w := by rw [hk]; ring
      have heq0 : p - w = p' + ((n : ℤ) - 1) • w := by rw [hp_eq, hkeq]; ring
      have heq : p - w = p' + ((n - 1 : ℕ) : ℤ) • w := by rw [heq0, hcast]
      have hp_w : p - w ∈ Rinf := by rw [heq]; exact add_nsmul_mem hray p' hp' (n - 1)
      exact absurd hp_w hp_start

/-! ## §2. Enumerating gap levels -/

/-- The levels in the gap `cut (N+1) \ cut N` are exactly those ℓ with
`lev (N+1) ≤ ℓ < lev N`.

原文：b3_colle2.txt:818 — the gap is finitely many levels. -/
theorem gap_levels_finite :
    ∀ z, z ∈ cut Rinf m lev (N + 1) → z ∉ cut Rinf m lev N →
      lev (N + 1) ≤ dot m z ∧ dot m z < lev N := by
  intro z hzN1 hzN
  have hzN1_mem : z ∈ Rinf ∧ z ∈ halfPlaneGE m (lev (N + 1)) := hzN1
  have hzN_nmem : ¬(z ∈ Rinf ∧ z ∈ halfPlaneGE m (lev N)) := hzN
  simp only [halfPlaneGE, Set.mem_ofPred_eq] at hzN1_mem hzN_nmem
  push Not at hzN_nmem
  exact ⟨hzN1_mem.2, hzN_nmem hzN1_mem.1⟩

/-! ## §3. Main theorem: abstract gap enumeration -/

/-- **Abstract gap enumeration theorem.**

原文：b3_colle2.txt:818-856

If `Rinf` satisfies:
1. `hray`: closure under `+w` (ray structure)
2. `hbdd`: each point has a w-row starting point (bounded w-rows)
3. `hm_prim`: `m` is primitive (ensures one row per level)
4. `hmw`: `w` is perpendicular to `m` (rows are level sets)

Then there exists an enumeration `base : ℕ → ℤ × ℤ` such that:
- `henum_covers`: every gap point is `base i + j•w` for some `i, j`
- `henum_in_cut`: all `base i + j•w` are in `cut (N+1)`
- `henum_gap_only`: all `base i + j•w` are not in `cut N` (gap points)
-/
theorem exists_gap_enumeration_of_rows
    (hray : ∀ z ∈ Rinf, z + w ∈ Rinf)
    (hbdd : ∀ z ∈ Rinf, ∃ p ∈ Rinf, ∃ j : ℕ, z = p + (j : ℤ) • w ∧ p - w ∉ Rinf)
    (hm_prim : Prim m)
    (hmw : dot m w = 0)
    (hw_prim : Prim w)
    (hlev_mono : lev (N + 1) < lev N)
    (hgap_nonempty : ∃ z, z ∈ cut Rinf m lev (N + 1) ∧ z ∉ cut Rinf m lev N) :
    ∃ (base : ℕ → ℤ × ℤ),
      (∀ z ∈ cut Rinf m lev (N + 1), z ∉ cut Rinf m lev N →
        ∃ i j : ℕ, z = base i + (j : ℤ) • w) ∧
      (∀ i j : ℕ, base i + (j : ℤ) • w ∈ cut Rinf m lev (N + 1)) ∧
      (∀ i j : ℕ, base i + (j : ℤ) • w ∉ cut Rinf m lev N) := by
  have hdot_off : ∀ (p : ℤ × ℤ) (j : ℕ), dot m (p + (j : ℤ) • w) = dot m p := by
    intro p j
    rw [dot_add, dot_zsmul_right, hmw, mul_zero, add_zero]
  obtain ⟨z_wit, hz_wit_in, hz_wit_out⟩ := hgap_nonempty
  obtain ⟨p_wit, hp_wit_mem, j_wit, hz_wit_eq, hp_wit_start⟩ := hbdd z_wit hz_wit_in.1

  let num_levels := (lev N - lev (N + 1)).toNat
  let level_of (i : ℕ) : ℤ := if i < num_levels then lev (N + 1) + i else lev N - 1

  let base : ℕ → ℤ × ℤ := fun i =>
    let ℓ := level_of i
    if h : ∃ p, p ∈ cut Rinf m lev (N + 1) ∧ p ∉ cut Rinf m lev N ∧ dot m p = ℓ then
      let p := Classical.choose h
      Classical.choose (hbdd p (Classical.choose_spec h).1.1)
    else p_wit

  refine ⟨base, ?_, ?_, ?_⟩

  · -- Coverage: every gap point is enumerated
    intro z hzN1 hzN
    obtain ⟨hlev_lower, hlev_upper⟩ := gap_levels_finite z hzN1 hzN
    obtain ⟨p, hp_mem, j, hz_eq, hp_start⟩ := hbdd z hzN1.1
    have hp_lev : dot m p = dot m z := by rw [hz_eq]; exact (hdot_off p j).symm
    have hlev_in_range : lev (N + 1) ≤ dot m p ∧ dot m p < lev N := by
      rw [hp_lev]; exact ⟨hlev_lower, hlev_upper⟩
    set i := (dot m p - lev (N + 1)).toNat with hi_def
    have hi_cast : (i : ℤ) = dot m p - lev (N + 1) := by
      rw [hi_def]; exact Int.toNat_of_nonneg (by omega)
    have hi_bound : i < num_levels := by
      have hnn : (0:ℤ) ≤ lev N - lev (N + 1) := by omega
      have h1 : (i : ℤ) < ((lev N - lev (N + 1)).toNat : ℤ) := by
        rw [hi_cast, Int.toNat_of_nonneg hnn]; omega
      exact_mod_cast h1
    have hlev_i : level_of i = dot m p := by
      show (if i < num_levels then lev (N + 1) + (i : ℤ) else lev N - 1) = dot m p
      rw [if_pos hi_bound]
      omega
    have hp_notN : p ∉ cut Rinf m lev N := by
      intro hpc
      have hle : lev N ≤ dot m p := hpc.2
      omega
    have hex : ∃ p'', p'' ∈ cut Rinf m lev (N + 1) ∧ p'' ∉ cut Rinf m lev N ∧
        dot m p'' = level_of i :=
      ⟨p, ⟨hp_mem, hlev_in_range.1⟩, hp_notN, by rw [hlev_i]⟩
    set p2 := Classical.choose hex with hp2_def
    have hp2_spec := Classical.choose_spec hex
    set q := Classical.choose (hbdd p2 hp2_spec.1.1) with hq_def
    have hq_spec := Classical.choose_spec (hbdd p2 hp2_spec.1.1)
    obtain ⟨hq_mem, jq, hq_eq, hq_start⟩ := hq_spec
    have hq_lev : dot m q = dot m p2 := by rw [hq_eq, hdot_off]
    have hq_eqp : q = p :=
      at_most_one_row_start_per_level hm_prim hmw hw_prim hray hq_mem hq_start hp_mem hp_start
        (by rw [hq_lev, hp2_spec.2.2, hlev_i])
    have hbase_i_eq : base i = q := by
      show (if h : ∃ p, p ∈ cut Rinf m lev (N + 1) ∧ p ∉ cut Rinf m lev N ∧ dot m p = level_of i
              then Classical.choose (hbdd (Classical.choose h) (Classical.choose_spec h).1.1)
              else p_wit) = q
      rw [dif_pos hex]
    have hbase_i_p : base i = p := by rw [hbase_i_eq, hq_eqp]
    exact ⟨i, j, by rw [hbase_i_p]; exact hz_eq⟩

  · -- Well-formed: all enum points are in cut (N+1)
    intro i j
    simp only [base]
    by_cases hex : ∃ p, p ∈ cut Rinf m lev (N + 1) ∧ p ∉ cut Rinf m lev N ∧ dot m p = level_of i
    · rw [dif_pos hex]
      set p' := Classical.choose hex with hp'_def
      have hp'_spec := Classical.choose_spec hex
      set base_start := Classical.choose (hbdd p' hp'_spec.1.1) with hbs_def
      have hbs_spec := Classical.choose_spec (hbdd p' hp'_spec.1.1)
      obtain ⟨hbs_mem, jbs, hbs_eq, hbs_start⟩ := hbs_spec
      refine ⟨add_nsmul_mem hray base_start hbs_mem j, ?_⟩
      have heq : dot m (base_start + (j : ℤ) • w) = dot m p' := by
        rw [hdot_off, hbs_eq, hdot_off]
      show lev (N + 1) ≤ dot m (base_start + (j : ℤ) • w)
      rw [heq]
      exact hp'_spec.1.2
    · rw [dif_neg hex]
      refine ⟨add_nsmul_mem hray p_wit hp_wit_mem j, ?_⟩
      have heq : dot m (p_wit + (j : ℤ) • w) = dot m z_wit := by
        rw [hdot_off, hz_wit_eq, hdot_off]
      show lev (N + 1) ≤ dot m (p_wit + (j : ℤ) • w)
      rw [heq]
      exact hz_wit_in.2

  · -- Gap-only: all enum points are not in cut N
    intro i j
    simp only [base]
    by_cases hex : ∃ p, p ∈ cut Rinf m lev (N + 1) ∧ p ∉ cut Rinf m lev N ∧ dot m p = level_of i
    · rw [dif_pos hex]
      set p' := Classical.choose hex with hp'_def
      have hp'_spec := Classical.choose_spec hex
      set base_start := Classical.choose (hbdd p' hp'_spec.1.1) with hbs_def
      have hbs_spec := Classical.choose_spec (hbdd p' hp'_spec.1.1)
      obtain ⟨hbs_mem, jbs, hbs_eq, hbs_start⟩ := hbs_spec
      intro hcontra
      have heq : dot m (base_start + (j : ℤ) • w) = dot m p' := by
        rw [hdot_off, hbs_eq, hdot_off]
      have hge : lev N ≤ dot m p' := by rw [← heq]; exact hcontra.2
      exact hp'_spec.2.1 ⟨hp'_spec.1.1, hge⟩
    · rw [dif_neg hex]
      intro hcontra
      have heq : dot m (p_wit + (j : ℤ) • w) = dot m z_wit := by
        rw [hdot_off, hz_wit_eq, hdot_off]
      have hge : lev N ≤ dot m z_wit := by rw [← heq]; exact hcontra.2
      exact hz_wit_out ⟨hz_wit_in.1, hge⟩

end Nivat.L1CoverPackage

#print axioms Nivat.L1CoverPackage.exists_gap_enumeration_of_rows

/-! ## §4. `hbdd` from tower's `hwneg`/`htop` (team-lead 2026-09-22)

Once `RegionSteps.lean` exports `hwneg : dot nℓ w < 0` and
`htop : ∃ top, ∀ z ∈ Rinf, dot nℓ z ≤ top` (tower package, in progress), `hbdd` follows:
going backward along `w` strictly increases `dot nℓ`, so a backward `-w`-ray from any point
of `Rinf` would be unbounded above in `dot nℓ`, contradicting `htop`. Combined with `hray`
(closure under `+w`, free via `RecessionCone.recession_of_ray`), well-ordering on the least
`k` with `z - (k:ℤ)•w ∉ Rinf` gives the row-start point. -/

namespace Nivat.L1CoverPackage

variable {Rinf : Set (ℤ × ℤ)} {w nℓ : ℤ × ℤ}

theorem hbdd_of_bounded
    (hray : ∀ z ∈ Rinf, z + w ∈ Rinf)
    (hwneg : Nivat.LE2.dot nℓ w < 0)
    (htop : ∃ top : ℤ, ∀ z ∈ Rinf, Nivat.LE2.dot nℓ z ≤ top) :
    ∀ z ∈ Rinf, ∃ p ∈ Rinf, ∃ j : ℕ, z = p + (j : ℤ) • w ∧ p - w ∉ Rinf := by
  obtain ⟨top, htop'⟩ := htop
  intro z hz
  by_contra hcon
  push_neg at hcon
  -- If no row-start exists, we can go backward forever, contradicting `htop`.
  have hback : ∀ k : ℕ, z - (k : ℤ) • w ∈ Rinf ∧
      Nivat.LE2.dot nℓ (z - (k : ℤ) • w) = Nivat.LE2.dot nℓ z - (k : ℤ) * Nivat.LE2.dot nℓ w := by
    intro k
    induction k with
    | zero => simpa using hz
    | succ k ih =>
      obtain ⟨ihmem, ihdot⟩ := ih
      have hzk_mem : z - (k : ℤ) • w ∈ Rinf := ihmem
      have heqk : z = (z - (k : ℤ) • w) + (k : ℤ) • w := by ring
      have hmem_next : z - (k : ℤ) • w - w ∈ Rinf := hcon (z - (k : ℤ) • w) hzk_mem k heqk
      refine ⟨?_, ?_⟩
      · have heq : z - (((k : ℕ) + 1 : ℕ) : ℤ) • w = z - (k : ℤ) • w - w := by push_cast; ring
        rw [heq]; exact hmem_next
      · have heq : z - (((k : ℕ) + 1 : ℕ) : ℤ) • w = z - (k : ℤ) • w - w := by push_cast; ring
        rw [heq]
        have hdw : Nivat.LE2.dot nℓ (z - (k : ℤ) • w - w)
            = Nivat.LE2.dot nℓ (z - (k : ℤ) • w) - Nivat.LE2.dot nℓ w := by
          rw [Nivat.LE2.dot_sub]
        rw [hdw, ihdot]; push_cast; ring
  -- Pick k large enough that `dot nℓ (z - k•w) > top`, contradicting `htop'`.
  set K : ℕ := (top - Nivat.LE2.dot nℓ z).toNat + 1 with hK
  obtain ⟨hKmem, hKdot⟩ := hback K
  have hKle : Nivat.LE2.dot nℓ (z - (K : ℤ) • w) ≤ top := htop' _ hKmem
  rw [hKdot] at hKle
  have hKpos : (0:ℤ) ≤ (K:ℤ) := Int.natCast_nonneg _
  have hw1 : Nivat.LE2.dot nℓ w ≤ -1 := by omega
  have hmul : (K : ℤ) * Nivat.LE2.dot nℓ w ≤ (K:ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left hw1 hKpos
  have hKge : top - Nivat.LE2.dot nℓ z < (K : ℤ) := by
    have : (top - Nivat.LE2.dot nℓ z) ≤ ((top - Nivat.LE2.dot nℓ z).toNat : ℤ) :=
      Int.self_le_toNat _
    push_cast [hK]
    omega
  omega

end Nivat.L1CoverPackage

#print axioms Nivat.L1CoverPackage.hbdd_of_bounded

/-! ## §5. Gap band collapses to a single height, from `hconsec`

`hconsec` (team-lead, `CutLevels.exists_lev_consecutive`) only forbids attained heights
STRICTLY between `lev(N+1)` and `lev N`; combined with membership in the gap band
`[lev(N+1), lev N)` itself, this pins the height to `lev(N+1)` exactly. -/

namespace Nivat.L1CoverPackage

variable {Rinf : Set (ℤ × ℤ)} {m w : ℤ × ℤ} {lev : ℕ → ℤ}

theorem gap_height_eq_of_consec
    (hconsec : ∀ n : ℕ, ∀ z ∈ Rinf, Nivat.LE2.dot m z < lev n → Nivat.LE2.dot m z ≤ lev (n + 1))
    {N : ℕ} {z : ℤ × ℤ} (hz : z ∈ Rinf)
    (hlo : lev (N + 1) ≤ Nivat.LE2.dot m z) (hhi : Nivat.LE2.dot m z < lev N) :
    Nivat.LE2.dot m z = lev (N + 1) :=
  le_antisymm (hconsec N z hz hhi) hlo

end Nivat.L1CoverPackage

#print axioms Nivat.L1CoverPackage.gap_height_eq_of_consec
