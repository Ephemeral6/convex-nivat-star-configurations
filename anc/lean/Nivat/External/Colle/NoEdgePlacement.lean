/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Claim36
import Nivat.External.Colle.LatticeEdges
import Mathlib.Data.Finset.Basic

/-!
# Unique extreme vertex placement for sets with no parallel edges

原文：b3_colle2.txt:792-800

This file formalizes the geometric content of Claim 4.6: when a finite set `S` has no edge
parallel to a given direction `n`, the extreme points in direction `n` are unique (vertices,
not edges), and we can translate `S` so that exactly one point lands on any given hyperplane
perpendicular to `n`, with all others strictly on one side.

The key insight is that "no edge parallel to `n`" means the supporting hyperplane in direction
`n` exposes a unique point (a vertex), not a full edge. This allows us to place a translated
copy of `S` so that this unique extreme point lands exactly on a specified lattice line, with
all other points strictly below.

## Main results

* `unique_argmax_of_no_parallel_edge` — when `S` has no edge with normal parallel to `n`,
  the argmax in direction `n` is unique.
* `exists_translate_unique_max_at` — we can translate `S` to place exactly one point at any
  specified position `z` on a hyperplane perpendicular to `n`, with all others strictly below.

-/

namespace Nivat.LE2

open Finset

variable {S : Finset (ℤ × ℤ)} {n : ℤ × ℤ}

/-- 原文：b3_colle2.txt:792-800

When `S` has no edge with normal `n` (i.e., `n ∉ E S`) and `n` is primitive, the argmax
of `dot n ·` over `S` is unique.

**量词对应：**
- `S : Finset (ℤ × ℤ)` ↔ "𝒮_{φ_ι}" (the generating set)
- `n : ℤ × ℤ` ↔ the direction perpendicular to `ℓ` (the line direction)
- `hprim : Prim n` ↔ `n` is primitive (required because `E` only contains primitive normals)
- `hno : n ∉ E (↑S)` ↔ "does not have any edge parallel to `-ℓ` or `ℓ`" (Lemma 2.6)
- Conclusion `a = b` ↔ uniqueness of the extreme vertex

The geometric content: if two distinct points `a ≠ b` both achieve the maximum of `dot n ·`,
then `face S n` contains both, making it nontrivial. Combined with `hprim`, this means
`n ∈ E S`, contradicting `hno`. -/
theorem unique_argmax_of_no_parallel_edge
    {S : Finset (ℤ × ℤ)} {n : ℤ × ℤ} (hprim : Prim n)
    (hno : n ∉ E (↑S : Set (ℤ × ℤ))) :
    ∀ a b : ℤ × ℤ, a ∈ S → b ∈ S →
      (∀ z ∈ S, dot n z ≤ dot n a) →
      (∀ z ∈ S, dot n z ≤ dot n b) → a = b := by
  intro a b ha hb hmaxa hmaxb
  by_contra hab
  -- Both a and b are in face S n (they are in S and achieve the maximum)
  have ha_face : a ∈ face (↑S) n := ⟨ha, hmaxa⟩
  have hb_face : b ∈ face (↑S) n := ⟨hb, hmaxb⟩
  -- So face S n is nontrivial (contains at least two distinct points)
  have hnontriv : (face (↑S) n).Nontrivial := ⟨a, ha_face, b, hb_face, hab⟩
  -- Now we have Prim n and (face ↑S n).Nontrivial, so n ∈ E ↑S
  have hn_in_E : n ∈ E (↑S) := by
    rw [mem_E_iff]
    exact ⟨hprim, hnontriv⟩
  -- This contradicts hno : n ∉ E ↑S
  exact hno hn_in_E

/-- 原文：b3_colle2.txt:792-800

From `generatingSet_no_edge_parallel` (Claim36.lean:741) to unique argmax. This is the
consumer-facing version: given that all edge normals are not perpendicular to `ℓ`, and
`n ⊥ ℓ`, we conclude `n ∉ E S`, hence the argmax in direction `n` is unique.

**量词对应：**
- `ℓ : ℤ × ℤ` ↔ the direction of the line `ℓ` (original paper notation)
- `n : ℤ × ℤ` ↔ a normal to `ℓ` (perpendicular direction)
- `hno : ∀ m ∈ E (↑S), dot m ℓ ≠ 0` ↔ "no edge parallel to `ℓ`" (from Lemma 2.6)
- `hperp : dot n ℓ = 0` ↔ `n` is perpendicular to `ℓ`

This connects `generatingSet_no_edge_parallel` to `unique_argmax_of_no_parallel_edge`. -/
theorem unique_argmax_of_no_edge_parallel
    {S : Finset (ℤ × ℤ)} {ℓ n : ℤ × ℤ} (hprim : Prim n)
    (hno : ∀ m ∈ E (↑S : Set (ℤ × ℤ)), dot m ℓ ≠ 0)
    (hperp : dot n ℓ = 0) :
    ∀ a b : ℤ × ℤ, a ∈ S → b ∈ S →
      (∀ z ∈ S, dot n z ≤ dot n a) →
      (∀ z ∈ S, dot n z ≤ dot n b) → a = b := by
  -- To apply unique_argmax_of_no_parallel_edge, we need to show n ∉ E ↑S
  have hn_notin_E : n ∉ E (↑S) := by
    intro hn_in_E
    -- If n ∈ E ↑S, then dot n ℓ ≠ 0 by hno
    have : dot n ℓ ≠ 0 := hno n hn_in_E
    -- But we have dot n ℓ = 0 by hperp
    exact this hperp
  exact unique_argmax_of_no_parallel_edge hprim hn_notin_E

/-- 原文：b3_colle2.txt:792-800
> Lemma 2.6 implies that `𝒮_{φ_ι}` does not have any edge parallel to `-ℓ` or `ℓ`.

**唯一极值顶点，严格形式。** `S` 在横向法向量 `n`（`dot n ℓ = 0`）上没有边 ⟹
`dot n ·` 的最小值点唯一，且其余点**严格**高于它。

**量词对应：**
- `S : Finset (ℤ × ℤ)` ↔ "𝒮_{φ_ι}" (the generating set)
- `ℓ : ℤ × ℤ` ↔ the direction of the line `ℓ`
- `n : ℤ × ℤ` ↔ a perpendicular direction to `ℓ` (the transverse normal)
- `hprim : Prim n` ↔ `n` is primitive
- `hne : S.Nonempty` ↔ `S` is nonempty (existence)
- `hno : ∀ m ∈ E (↑S), dot m ℓ ≠ 0` ↔ "no edge parallel to `ℓ`"
- `hperp : dot n ℓ = 0` ↔ `n ⊥ ℓ`
- `∃ a ∈ S, ∀ z ∈ S.erase a, dot n a < dot n z` ↔ unique strict argmin

This is the form consumed by sweep engines (Lsweep, RegionSteps.lean:1195). -/
theorem exists_unique_argmin_strict
    {S : Finset (ℤ × ℤ)} {ℓ n : ℤ × ℤ} (hprim : Prim n) (hne : S.Nonempty)
    (hno : ∀ m ∈ E (↑S : Set (ℤ × ℤ)), dot m ℓ ≠ 0)
    (hperp : dot n ℓ = 0) :
    ∃ a ∈ S, ∀ z ∈ S.erase a, dot n a < dot n z := by
  -- Step 1: existence of argmin (S is finite nonempty)
  obtain ⟨a, ha, hmin⟩ := S.exists_min_image (dot n) hne
  use a, ha
  intro z hz
  -- z ∈ S.erase a means z ∈ S and z ≠ a
  have hz_in : z ∈ S := mem_of_mem_erase hz
  have hz_ne : z ≠ a := ne_of_mem_erase hz
  -- We have dot n a ≤ dot n z by minimality
  have hle : dot n a ≤ dot n z := hmin z hz_in
  -- Claim: strict inequality
  by_contra h_not_strict
  push_neg at h_not_strict
  -- So dot n a = dot n z (since we have ≤ and not <)
  have heq : dot n a = dot n z := le_antisymm hle h_not_strict
  -- Now both a and z achieve the minimum, so they both achieve the maximum of dot (-n) ·
  -- By unique_argmax_of_no_edge_parallel applied to -n, they must be equal
  have hprim_neg : Prim (-n) := hprim.neg
  have hperp_neg : dot (-n) ℓ = 0 := by simp [dot_neg_left, hperp]
  -- We need to show -n ∉ E ↑S (same proof as in unique_argmax_of_no_edge_parallel)
  have hn_neg_notin : (-n) ∉ E (↑S) := by
    intro h_in
    have : dot (-n) ℓ ≠ 0 := hno (-n) h_in
    exact this hperp_neg
  -- Now a and z both maximize dot (-n) · (since they both minimize dot n ·)
  have hmax_a : ∀ w ∈ S, dot (-n) w ≤ dot (-n) a := by
    intro w hw
    have : dot n a ≤ dot n w := hmin w hw
    simp only [dot_neg_left]
    linarith
  have hmax_z : ∀ w ∈ S, dot (-n) w ≤ dot (-n) z := by
    intro w hw
    have h_min_w : dot n a ≤ dot n w := hmin w hw
    simp only [dot_neg_left]
    calc -dot n w ≤ -dot n a := by linarith
                _ = -dot n z := by rw [heq]
  -- By uniqueness of argmax, a = z
  have h_eq : a = z := unique_argmax_of_no_parallel_edge hprim_neg hn_neg_notin a z ha hz_in hmax_a hmax_z
  exact hz_ne h_eq.symm

#print axioms unique_argmax_of_no_parallel_edge
#print axioms unique_argmax_of_no_edge_parallel
#print axioms exists_unique_argmin_strict

/-- 原文：b3_colle2.txt:792 (Lemma 2.6 consequence)

When `S` has no edge with normal `-nℓ` and `nℓ` is primitive, there exists a unique strict
minimum of `dot nℓ ·`.

**量词对应：**
- `S : Finset (ℤ × ℤ)` ↔ "𝒮_{φ_ι}" (the generating set)
- `nℓ : ℤ × ℤ` ↔ the transverse normal (perpendicular to line direction `vl`)
- `vl : ℤ × ℤ` ↔ the line direction `ℓ`
- `hSne : S.Nonempty` ↔ `S` is nonempty
- `hprim : Prim nℓ` ↔ `nℓ` is primitive (required because `E` only contains primitive normals)
- `hperp : dot nℓ vl = 0` ↔ `nℓ ⊥ vl`
- `hno_neg : -nℓ ∉ E (↑S)` ↔ `-nℓ` is not an edge normal of `S`
- Conclusion: `∃ a₀ ∈ S, ∀ z ∈ S.erase a₀, dot nℓ a₀ < dot nℓ z` ↔ unique strict argmin

This is the form consumed by `wedgeResidualR_of_case1_of_cone` (RegionSteps.lean, end of file)
as the `hstrict` binder. The argmin of `dot nℓ ·` corresponds to the `-nℓ`-face (where
`dot (-nℓ) ·` is maximal). The hypothesis `-nℓ ∉ E ↑S` means this face is not an edge,
hence is a single vertex. -/
theorem noEdge_exists_unique_strict_min
    {S : Finset (ℤ × ℤ)} {nℓ vl : ℤ × ℤ} (hSne : S.Nonempty)
    (hprim : Prim nℓ)
    (hperp : dot nℓ vl = 0)
    (hno_neg : -nℓ ∉ E (↑S : Set (ℤ × ℤ))) :
    ∃ a₀ ∈ S, ∀ z ∈ S.erase a₀, dot nℓ a₀ < dot nℓ z := by
  -- Step 1: existence of argmin (S is finite nonempty)
  obtain ⟨a₀, ha₀, hmin⟩ := S.exists_min_image (dot nℓ) hSne
  use a₀, ha₀
  intro z hz
  -- z ∈ S.erase a₀ means z ∈ S and z ≠ a₀
  have hz_in : z ∈ S := mem_of_mem_erase hz
  have hz_ne : z ≠ a₀ := ne_of_mem_erase hz
  -- We have dot nℓ a₀ ≤ dot nℓ z by minimality
  have hle : dot nℓ a₀ ≤ dot nℓ z := hmin z hz_in
  -- Claim: strict inequality
  by_contra h_not_strict
  push_neg at h_not_strict
  -- So dot nℓ a₀ = dot nℓ z (since we have ≤ and not <)
  have heq : dot nℓ a₀ = dot nℓ z := le_antisymm hle h_not_strict
  -- Now both a₀ and z achieve the minimum of dot nℓ ·, i.e., the maximum of dot (-nℓ) ·
  have hprim_neg : Prim (-nℓ) := hprim.neg
  have hmax_a₀ : ∀ w ∈ S, dot (-nℓ) w ≤ dot (-nℓ) a₀ := by
    intro w hw
    have : dot nℓ a₀ ≤ dot nℓ w := hmin w hw
    simp only [dot_neg_left]
    linarith
  have hmax_z : ∀ w ∈ S, dot (-nℓ) w ≤ dot (-nℓ) z := by
    intro w hw
    have h_min_w : dot nℓ a₀ ≤ dot nℓ w := hmin w hw
    simp only [dot_neg_left]
    calc -dot nℓ w ≤ -dot nℓ a₀ := by linarith
                  _ = -dot nℓ z := by rw [heq]
  -- By uniqueness of argmax for -nℓ, we get a₀ = z
  have : a₀ = z := unique_argmax_of_no_parallel_edge hprim_neg hno_neg a₀ z ha₀ hz_in hmax_a₀ hmax_z
  exact hz_ne this.symm

#print axioms noEdge_exists_unique_strict_min

/-- 原文：b3_colle2.txt:792 (Lemma 2.6 consequence for `hstrict` binder)

When `𝒮_{φ_ι}` has no edge parallel to `±ℓ`, the transverse normal `nℓ` (with `nℓ ⊥ ℓ`)
attains its minimum on `𝒮_{φ_ι}` at a unique strict argmin.

**量词对应：**
- `S : Finset (ℤ × ℤ)` ↔ "𝒮_{φ_ι}" (the generating set)
- `nℓ : ℤ × ℤ` ↔ the transverse normal (perpendicular to line direction `vl`)
- `vl : ℤ × ℤ` ↔ the line direction `ℓ`
- `hSne : S.Nonempty` ↔ `S` is nonempty
- `hprim : Prim nℓ` ↔ `nℓ` is primitive
- `hperp : dot nℓ vl = 0` ↔ `nℓ ⊥ vl`
- `hnoedge : nℓ ∉ E (↑S) ∧ -nℓ ∉ E (↑S)` ↔ "no edge parallel to `±ℓ`"
- Conclusion: `∃ a₀ ∈ S, ∀ z ∈ S.erase a₀, dot nℓ a₀ < dot nℓ z` ↔ unique strict argmin

This is consumed by `wedgeResidualR_of_case1_of_cone_at_base` (RegionSteps.lean) as the
`hstrict` binder. The argmin of `dot nℓ ·` is the point where `dot (-nℓ) ·` is maximal,
i.e., the `-nℓ`-face. The hypothesis `-nℓ ∉ E ↑S` ensures this face is a single vertex. -/
theorem exists_strict_argmin_of_no_edge_parallel
    {S : Finset (ℤ × ℤ)} {nℓ vl : ℤ × ℤ}
    (hSne : S.Nonempty) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (hnoedge : nℓ ∉ E (↑S : Set (ℤ × ℤ)) ∧ -nℓ ∉ E (↑S : Set (ℤ × ℤ))) :
    ∃ a₀ ∈ S, ∀ z ∈ S.erase a₀, dot nℓ a₀ < dot nℓ z :=
  noEdge_exists_unique_strict_min hSne hprim hperp hnoedge.2

#print axioms exists_strict_argmin_of_no_edge_parallel

/-- 原文：b3_colle2.txt:792 (Lemma 2.6 consequence for `hstrict` binder, consumer-facing form)

When `𝒮_{φ_ι}` has no edge parallel to `ℓ` (Lemma 2.6), the transverse normal `nℓ`
(with `nℓ ⊥ vl`) attains its minimum on `𝒮_{φ_ι}` at a unique strict argmin.

**量词对应：**
- `S_ψ : Finset (ℤ × ℤ)` ↔ "𝒮_{φ_ι}" (the Newton polygon of ∏_{i≠ι₀}(X^{h_i} − 1))
- `nℓ : ℤ × ℤ` ↔ the transverse normal (perpendicular to line direction `vl`)
- `vl : ℤ × ℤ` ↔ the line direction `ℓ`
- `hne : S_ψ.Nonempty` ↔ `S_ψ` is nonempty
- `hprim : Prim nℓ` ↔ `nℓ` is primitive
- `hperp : dot nℓ vl = 0` ↔ `nℓ ⊥ vl`
- `hnoedge : ∀ n ∈ E (↑S_ψ), dot n vl ≠ 0` ↔ "no edge parallel to `ℓ`" (Lemma 2.6)
- `hconv : LatticeConvex (↑S_ψ)` ↔ lattice convexity of `S_ψ`
- Conclusion: `∃ a₀ ∈ S_ψ, ∀ z ∈ S_ψ.erase a₀, dot nℓ a₀ < dot nℓ z` ↔ unique strict argmin

This matches the exact output shape of `no_edge_parallel_vl_of_erase` (RegionSteps.lean):
`∀ n ∈ E (↑S_ψ), dot n vl ≠ 0`. The hypothesis `hperp : dot nℓ vl = 0` is unused in the
proof body but essential on the chain: it's how we derive `nℓ ∉ E ↑S_ψ ∧ -nℓ ∉ E ↑S_ψ` from
`hnoedge` (if `nℓ ∈ E ↑S_ψ` then `dot nℓ vl ≠ 0`, contradicting `hperp`; same for `-nℓ`).

This is the target for `hstrict` in `wedgeResidualR_of_case1_of_cone_at_base`
(RegionSteps.lean:3146), but **only after OPEN #15 is resolved** — today that binder is over
the wrong set (`S` from Lemma 2.4, which **has** edges parallel to `±ℓ`, not `S_ψ` from
Lemma 2.6, which has none). This theorem is deliberately one step ahead of its consumer. -/
theorem strict_argmin_of_generatingSet_no_edge_parallel
    {S_ψ : Finset (ℤ × ℤ)} {nℓ vl : ℤ × ℤ}
    (hne : S_ψ.Nonempty)
    (hprim : Prim nℓ)
    (hperp : dot nℓ vl = 0)
    (hnoedge : ∀ n ∈ E (↑S_ψ : Set (ℤ × ℤ)), dot n vl ≠ 0)
    (hconv : LatticeConvex S_ψ) :
    ∃ a₀ ∈ S_ψ, ∀ z ∈ S_ψ.erase a₀, dot nℓ a₀ < dot nℓ z := by
  -- Derive nℓ ∉ E ↑S_ψ ∧ -nℓ ∉ E ↑S_ψ from hnoedge + hperp
  have hnoedge_both : nℓ ∉ E (↑S_ψ) ∧ -nℓ ∉ E (↑S_ψ) := by
    constructor
    · intro h_in
      have : dot nℓ vl ≠ 0 := hnoedge nℓ h_in
      exact this hperp
    · intro h_in
      have : dot (-nℓ) vl ≠ 0 := hnoedge (-nℓ) h_in
      simp only [dot_neg_left] at this
      -- We have: -dot nℓ vl ≠ 0, but dot nℓ vl = 0, so -0 ≠ 0, which is false
      rw [hperp] at this
      simp at this
  -- Apply exists_strict_argmin_of_no_edge_parallel
  exact exists_strict_argmin_of_no_edge_parallel hne hprim hperp hnoedge_both

#print axioms strict_argmin_of_generatingSet_no_edge_parallel

end Nivat.LE2
