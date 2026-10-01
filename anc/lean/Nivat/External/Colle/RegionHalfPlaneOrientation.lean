/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.RegionEdges

/-!
# Which side?  The orientation of `ℋ` in `IsRegion (ℛ ∩ ℋ) ℓ ℓ'`

Colle, Lemma 4.1 (`scratch/b3_colle2.txt:700`) concludes on the set `ℋ(ℓ_{Q'}) ∩ ℛ`.
For `IsRegion (ℛ ∩ ℋ) n n'` (`LatticeEdges.lean:2221`) to have any chance, the cutting
half-plane must be taken on the correct side of the `n'`-edge.  There are exactly two
candidates, `halfPlaneLE n' c` and `halfPlaneGE n' c = halfPlaneLE (-n') (-c)`
(`LatticeEdges.lean:1757`, `:1761`, `:1764`), and this file decides between them at
kernel level, using the repository's own non-degenerate region `isRegion_quad`
(`LatticeEdges.lean:2391`) as the test target.

**Answer: `halfPlaneLE n' c` — the cut whose outer normal is `n'` itself.**

* `halfPlaneGE n' c` (outer normal `-n'`) is **refuted**: `not_isRegion_inter_halfPlaneGE`.
  It preserves the `n'`-edge but truncates the `n`-edge to a finite set, so `semiInf`
  fails.
* `halfPlaneLE n' c` (outer normal `n'`) **works**: `isRegion_quadLE`.  The `n'`-edge is
  *not* destroyed — it slides down to the cutting level and stays semi-infinite.  This
  is the content of `face_inter_slice` (`RegionEdges.lean:630`): the face in the cut
  direction becomes the whole slice `{z ∈ R : dot n' z = c}`.
-/

namespace Nivat.LE2

open Nivat

/-! ### Name probes (no fabricated lemma names) -/

section Probes
#check @Set.infinite_of_injective_forall_mem
#check @Set.Finite.not_infinite
#check @Set.Infinite.nontrivial
#check @mul_left_cancel₀
#check @isLatticeConvexRegion_inter_halfPlaneLE
#check @isRegion_of_two_semiInf
#check @halfPlaneGE_eq_halfPlaneLE_neg
end Probes

/-! ## 1. The wrong side: outer normal `-n'`, i.e. `halfPlaneGE n' c`

`quad ∩ halfPlaneGE (0,-1) (-1) = {z | 0 ≤ z₁ ∧ 0 ≤ z₂ ≤ 1}` is a width-2 half-strip.
Its `(0,-1)`-edge is still semi-infinite, but its `(-1,0)`-edge has collapsed to the
two points `(0,0)`, `(0,1)`. -/

/-- The bad cut: `quad ∩ {z₂ ≤ 1}`. -/
def quadGE : Set (ℤ × ℤ) := quad ∩ halfPlaneLE ((0 : ℤ), (1 : ℤ)) 1

theorem mem_quadGE {z : ℤ × ℤ} : z ∈ quadGE ↔ 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1 := by
  simp only [quadGE, Set.mem_inter_iff, mem_quad, halfPlaneLE, Set.mem_ofPred_eq, dot_e2]
  tauto

theorem quad_inter_halfPlaneGE :
    quad ∩ halfPlaneGE ((0 : ℤ), (-1 : ℤ)) (-1) = quadGE := by
  ext z
  simp only [Set.mem_inter_iff, mem_quad, halfPlaneGE, Set.mem_ofPred_eq, dot_e2', mem_quadGE]
  omega

/-- **The `n`-edge is truncated.**  Cutting on the `-n'` side leaves only two lattice
points on the edge with outer normal `n = (-1,0)`. -/
theorem face_quadGE_left :
    face quadGE (-1, 0) = {((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))} := by
  ext z
  constructor
  · rintro ⟨hz, hm⟩
    rw [mem_quadGE] at hz
    have hmem : ((0 : ℤ), z.2) ∈ quadGE := by
      rw [mem_quadGE]; exact ⟨le_refl 0, hz.2.1, hz.2.2⟩
    have h := hm _ hmem
    simp only [dot_e1'] at h
    have hz1 : z.1 = 0 := le_antisymm (by omega) hz.1
    rcases (by omega : z.2 = 0 ∨ z.2 = 1) with h' | h'
    · exact Or.inl (Prod.ext hz1 h')
    · exact Or.inr (Prod.ext hz1 h')
  · rintro (rfl | rfl)
    · refine ⟨by rw [mem_quadGE]; exact ⟨le_refl 0, le_refl 0, by norm_num⟩, ?_⟩
      intro y hy
      rw [mem_quadGE] at hy
      simp only [dot_e1']
      omega
    · refine ⟨by rw [mem_quadGE]; exact ⟨le_refl 0, by norm_num, le_refl 1⟩, ?_⟩
      intro y hy
      rw [mem_quadGE] at hy
      simp only [dot_e1']
      omega

theorem not_isSemiInfEdge_quadGE_left : ¬ IsSemiInfEdge quadGE (-1, 0) := by
  rintro ⟨-, hinf⟩
  rw [face_quadGE_left] at hinf
  exact ((Set.finite_singleton _).insert _).not_infinite hinf

/-- **Refutation.**  Cutting an `(n,n')`-region by `halfPlaneGE n' c` — i.e. by a
half-plane whose *outer* normal is `-n'` — does not give an `(n,n')`-region, even when
the intersection is nonempty.  The `n'`-edge survives, but the `n`-edge is truncated to
a finite set. -/
theorem not_isRegion_inter_halfPlaneGE :
    ¬ ∀ (R : Set (ℤ × ℤ)) (n n' : ℤ × ℤ) (c : ℤ),
        IsRegion R n n' → (R ∩ halfPlaneGE n' c).Nonempty →
        IsRegion (R ∩ halfPlaneGE n' c) n n' := by
  intro h
  have hne : (quad ∩ halfPlaneGE ((0 : ℤ), (-1 : ℤ)) (-1)).Nonempty := by
    rw [quad_inter_halfPlaneGE]
    exact ⟨((0 : ℤ), (0 : ℤ)), by rw [mem_quadGE]; norm_num⟩
  have hq := h quad (-1, 0) (0, -1) (-1) isRegion_quad hne
  rw [quad_inter_halfPlaneGE] at hq
  exact not_isSemiInfEdge_quadGE_left hq.semiInf

/-! ## 2. The right side: outer normal `n'`, i.e. `halfPlaneLE n' c`

`quad ∩ halfPlaneLE (0,-1) (-1) = {z | 0 ≤ z₁ ∧ 1 ≤ z₂}`.  Both edges stay
semi-infinite: the `n`-edge because the cut is parallel to `n'`, the `n'`-edge because
it slides down to the cutting level (`face_inter_slice`). -/

/-- The good cut: `quad ∩ {1 ≤ z₂}`. -/
def quadLE : Set (ℤ × ℤ) := quad ∩ halfPlaneLE ((0 : ℤ), (-1 : ℤ)) (-1)

theorem mem_quadLE {z : ℤ × ℤ} : z ∈ quadLE ↔ 0 ≤ z.1 ∧ 1 ≤ z.2 := by
  simp only [quadLE, Set.mem_inter_iff, mem_quad, halfPlaneLE, Set.mem_ofPred_eq, dot_e2']
  omega

/-- In a direction pointing into the recession cone there is no exposed face at all. -/
theorem face_quadLE_eq_empty {m : ℤ × ℤ} (h : 0 < m.1 ∨ 0 < m.2) :
    face quadLE m = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hz, hm⟩
  rw [mem_quadLE] at hz
  rcases h with h | h
  · have hmem : ((z.1 + 1 : ℤ), z.2) ∈ quadLE := by
      rw [mem_quadLE]; exact ⟨show (0 : ℤ) ≤ z.1 + 1 by omega, hz.2⟩
    have hc := hm _ hmem
    simp only [dot] at hc
    nlinarith
  · have hmem : (z.1, (z.2 + 1 : ℤ)) ∈ quadLE := by
      rw [mem_quadLE]; exact ⟨hz.1, show (1 : ℤ) ≤ z.2 + 1 by omega⟩
    have hc := hm _ hmem
    simp only [dot] at hc
    nlinarith

/-- A strictly interior normal exposes the single corner `(0,1)`. -/
theorem face_quadLE_singleton {m : ℤ × ℤ} (h1 : m.1 < 0) (h2 : m.2 < 0) :
    face quadLE m = {((0 : ℤ), (1 : ℤ))} := by
  have hcorner : ((0 : ℤ), (1 : ℤ)) ∈ quadLE := by
    rw [mem_quadLE]; exact ⟨le_refl 0, le_refl 1⟩
  ext z
  constructor
  · rintro ⟨hz, hm⟩
    rw [mem_quadLE] at hz
    have hc := hm _ hcorner
    simp only [dot] at hc
    have e1 : m.1 * z.1 ≤ 0 := by nlinarith
    have e2 : m.2 * z.2 ≤ m.2 := by nlinarith
    have hp1 : m.1 * z.1 = 0 := le_antisymm e1 (by linarith)
    have hz1 : z.1 = 0 := (mul_eq_zero.mp hp1).resolve_left (ne_of_lt h1)
    have hp2 : m.2 * z.2 = m.2 * 1 := by rw [mul_one]; linarith
    have hz2 : z.2 = 1 := mul_left_cancel₀ (ne_of_lt h2) hp2
    exact Set.mem_singleton_iff.mpr (Prod.ext hz1 hz2)
  · rintro hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨hcorner, ?_⟩
    intro y hy
    rw [mem_quadLE] at hy
    simp only [dot]
    nlinarith

theorem face_quadLE_left : face quadLE (-1, 0) = {z : ℤ × ℤ | z.1 = 0 ∧ 1 ≤ z.2} := by
  ext z
  constructor
  · rintro ⟨hz, hm⟩
    rw [mem_quadLE] at hz
    have hmem : ((0 : ℤ), z.2) ∈ quadLE := by
      rw [mem_quadLE]; exact ⟨le_refl 0, hz.2⟩
    have h := hm _ hmem
    simp only [dot_e1'] at h
    exact ⟨le_antisymm (by omega) hz.1, hz.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [mem_quadLE]; exact ⟨by omega, h2⟩, ?_⟩
    intro y hy
    rw [mem_quadLE] at hy
    simp only [dot_e1']
    omega

theorem face_quadLE_bot : face quadLE (0, -1) = {z : ℤ × ℤ | 0 ≤ z.1 ∧ z.2 = 1} := by
  ext z
  constructor
  · rintro ⟨hz, hm⟩
    rw [mem_quadLE] at hz
    have hmem : (z.1, (1 : ℤ)) ∈ quadLE := by
      rw [mem_quadLE]; exact ⟨hz.1, le_refl 1⟩
    have h := hm _ hmem
    simp only [dot_e2'] at h
    exact ⟨hz.1, le_antisymm (by omega) hz.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [mem_quadLE]; exact ⟨h1, by omega⟩, ?_⟩
    intro y hy
    rw [mem_quadLE] at hy
    simp only [dot_e2']
    omega

theorem infinite_face_quadLE_left : (face quadLE (-1, 0)).Infinite := by
  rw [face_quadLE_left]
  exact Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((0 : ℤ), (k : ℤ) + 1))
    (fun a b h => by simpa using h)
    (fun k => ⟨rfl, show (1 : ℤ) ≤ (k : ℤ) + 1 by omega⟩)

theorem infinite_face_quadLE_bot : (face quadLE (0, -1)).Infinite := by
  rw [face_quadLE_bot]
  exact Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((k : ℤ), (1 : ℤ)))
    (fun a b h => by simpa using h)
    (fun k => ⟨show (0 : ℤ) ≤ (k : ℤ) by positivity, rfl⟩)

theorem isSemiInfEdge_quadLE_left : IsSemiInfEdge quadLE (-1, 0) :=
  ⟨⟨by decide, infinite_face_quadLE_left.nontrivial⟩, infinite_face_quadLE_left⟩

theorem isSemiInfEdge_quadLE_bot : IsSemiInfEdge quadLE (0, -1) :=
  ⟨⟨by decide, infinite_face_quadLE_bot.nontrivial⟩, infinite_face_quadLE_bot⟩

theorem semiInfUnique_quadLE (m : ℤ × ℤ) (hm : IsSemiInfEdge quadLE m) :
    m = (-1, 0) ∨ m = (0, -1) := by
  obtain ⟨⟨hprim, hnt⟩, hinf⟩ := hm
  have hg : Int.gcd m.1 m.2 = 1 := hprim
  have hle1 : m.1 ≤ 0 := by
    by_contra hc
    rw [face_quadLE_eq_empty (Or.inl (by omega))] at hnt
    obtain ⟨a, ha, -⟩ := hnt
    exact ha
  have hle2 : m.2 ≤ 0 := by
    by_contra hc
    rw [face_quadLE_eq_empty (Or.inr (by omega))] at hnt
    obtain ⟨a, ha, -⟩ := hnt
    exact ha
  rcases lt_or_eq_of_le hle1 with h1 | h1 <;> rcases lt_or_eq_of_le hle2 with h2 | h2
  · rw [face_quadLE_singleton h1 h2] at hinf
    exact absurd hinf (Set.finite_singleton _).not_infinite
  · rw [h2, Int.gcd_zero_right] at hg
    exact Or.inl (Prod.ext (by omega) h2)
  · rw [h1, Int.gcd_zero_left] at hg
    exact Or.inr (Prod.ext h1 (by omega))
  · rw [h1, h2] at hg
    simp at hg

/-- **The correct orientation, on the repository's own non-degenerate region.**
Cutting `quad` by `halfPlaneLE n' c` (outer normal `n' = (0,-1)`) leaves an
`(n,n')`-region with the *same* pair of normals. -/
theorem isRegion_quadLE : IsRegion quadLE (-1, 0) (0, -1) :=
  isRegion_of_two_semiInf
    (isLatticeConvexRegion_inter_halfPlaneLE _ _ isLatticeConvexRegion_quad)
    isSemiInfEdge_quadLE_left isSemiInfEdge_quadLE_bot (by decide) semiInfUnique_quadLE

/-- Packaged the way the target statement will be phrased. -/
theorem isRegion_quad_inter_halfPlaneLE :
    IsRegion (quad ∩ halfPlaneLE ((0 : ℤ), (-1 : ℤ)) (-1)) (-1, 0) (0, -1) :=
  isRegion_quadLE

end Nivat.LE2

open Nivat.LE2 in
#print axioms Nivat.LE2.not_isRegion_inter_halfPlaneGE
#print axioms Nivat.LE2.not_isSemiInfEdge_quadGE_left
#print axioms Nivat.LE2.face_quadGE_left
#print axioms Nivat.LE2.isRegion_quadLE
#print axioms Nivat.LE2.isRegion_quad_inter_halfPlaneLE
#print axioms Nivat.LE2.semiInfUnique_quadLE
#print axioms Nivat.LE2.isSemiInfEdge_quadLE_left
#print axioms Nivat.LE2.isSemiInfEdge_quadLE_bot
#print axioms Nivat.LE2.face_quadLE_eq_empty
#print axioms Nivat.LE2.face_quadLE_singleton
