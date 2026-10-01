/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
# Transport of the edge set `E(·)` along an equality of convex hulls

This file proves the "carrying" lemma that was missing from the tree:

```
theorem E_congr_of_Conv_eq {S T : Finset (ℤ × ℤ)} (h : Conv S = Conv T) :
    E (↑S : Set (ℤ × ℤ)) = E (↑T : Set (ℤ × ℤ))
```

`Nivat/External/Colle/Claim36.lean`'s Gap 1 carries a hypothesis
`hS_hull : Conv S_ψ = Conv (supp ψ)` but needs a conclusion about `E ↑S_ψ`; this is the
bridge.

## Why it is true (and why the obvious worry is unfounded)

`face R n` is the set of points of `R` maximising `⟨n, ·⟩`, so it depends on `R` and not
only on `Conv R`: for `S = {(0,0),(1,0),(2,0)}` and `T = {(0,0),(2,0)}` we have
`Conv S = Conv T` but `face ↑S (0,1) = ↑S ≠ ↑T = face ↑T (0,1)`.  That refutation is
recorded below as `exists_Conv_eq_face_ne`, so the statement proved here really is at the
strongest level that survives.

What *is* determined by the hull is whether the face has **at least two** points, which is
all `IsEdge` looks at.  The reason is the elementary "face of a hull" lemma
`mem_convexHull_sep_of_rdot_eq`: a point of `convexHull A` lying on a supporting
hyperplane of `A` already lies in the convex hull of the part of `A` on that hyperplane.
Hence if `face ↑S n` is a single point `z₀`, the exposed face of `Conv S` collapses to the
single point `toReal z₀`; and conversely two distinct maximisers in `S` give two distinct
points of the exposed face of the hull.  So

```
(face ↑S n).Nontrivial ↔ (hface (Conv S) (toReal n)).Nontrivial
```

(`nontrivial_face_iff`), whose right-hand side mentions `S` only through `Conv S`.

No Krein–Milman is needed, and **no extra hypothesis is used**: neither finiteness beyond
`Finset`, nor `LatticeConvex`, nor "contains all lattice points of the hull".

## Note on the statement's type

`Nivat.Conv : Finset (ℤ × ℤ) → Set (ℝ × ℝ)` is defined only for `Finset`s
(`Nivat/Defs/Complexity.lean`), so the version of the lemma with `S T : Set (ℤ × ℤ)` does
not typecheck.  The `Finset` form below with the coercion `↑S` is exactly the shape
`Claim36.lean` uses (`E (↑S_ψ : Set (ℤ × ℤ))`).

## Main results

* `Nivat.LE2.rdot`, `Nivat.LE2.hface` — the real pairing and the exposed face of a subset
  of `ℝ²`.
* `Nivat.LE2.mem_convexHull_sep_of_rdot_eq` — the face-of-a-hull lemma.
* `Nivat.LE2.nontrivial_face_iff` — the bridge between `face` over `ℤ²` and `hface` over `ℝ²`.
* `Nivat.LE2.E_congr_of_Conv_eq` — the transport lemma.
* `Nivat.LE2.IsEdge_congr_of_Conv_eq`, `Nivat.LE2.mem_E_congr_of_Conv_eq` — pointwise forms.
* `Nivat.LE2.exists_Conv_eq_face_ne` — `face` itself does **not** transport, so
  `E_congr_of_Conv_eq` cannot be upgraded to a statement about `face`.
-/

namespace Nivat.LE2

open Nivat

/-! ## §1. The real pairing and the exposed face of a planar set -/

/-- The real pairing `⟨n, x⟩ = n₁x₁ + n₂x₂` on `ℝ²`; the `ℝ`-counterpart of `dot`. -/
def rdot (n x : ℝ × ℝ) : ℝ := n.1 * x.1 + n.2 * x.2

theorem rdot_isLinear (n : ℝ × ℝ) : IsLinearMap ℝ (rdot n) where
  map_add x y := by simp only [rdot, Prod.fst_add, Prod.snd_add]; ring
  map_smul a x := by simp only [rdot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem rdot_smul_add (n p q : ℝ × ℝ) (a b : ℝ) :
    rdot n (a • p + b • q) = a * rdot n p + b * rdot n q := by
  simp only [rdot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- `rdot` restricted to the lattice is `dot`. -/
theorem rdot_toReal (n z : ℤ × ℤ) : rdot (toReal n) (toReal z) = (dot n z : ℝ) := by
  simp only [rdot, toReal, dot, Int.cast_add, Int.cast_mul]

/-- The exposed face of a subset `C ⊆ ℝ²` with outer normal `n`: the points of `C`
maximising `⟨n, ·⟩`.  Same convention as `face`. -/
def hface (C : Set (ℝ × ℝ)) (n : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | x ∈ C ∧ ∀ y ∈ C, rdot n y ≤ rdot n x}

theorem mem_hface_iff {C : Set (ℝ × ℝ)} {n x : ℝ × ℝ} :
    x ∈ hface C n ↔ x ∈ C ∧ ∀ y ∈ C, rdot n y ≤ rdot n x := Iff.rfl

/-! ## §2. The face-of-a-hull lemma

If `⟨n, ·⟩ ≤ c` on `A` then every point of `convexHull A` with `⟨n, ·⟩ = c` already lies in
the convex hull of the slice `A ∩ {⟨n, ·⟩ = c}`.  The proof is the standard one: the union
of that hull with the open half plane `{⟨n, ·⟩ < c}` is convex and contains `A`. -/

theorem mem_convexHull_sep_of_rdot_eq {A : Set (ℝ × ℝ)} {n : ℝ × ℝ} {c : ℝ}
    (hle : ∀ a ∈ A, rdot n a ≤ c) {x : ℝ × ℝ}
    (hx : x ∈ convexHull ℝ A) (hxc : rdot n x = c) :
    x ∈ convexHull ℝ {a | a ∈ A ∧ rdot n a = c} := by
  set A₁ : Set (ℝ × ℝ) := {a | a ∈ A ∧ rdot n a = c} with hA₁def
  -- the hull of the slice sits inside the hyperplane
  have hhull_eq : ∀ y ∈ convexHull ℝ A₁, rdot n y = c :=
    convexHull_min (fun a ha => ha.2) (convex_hyperplane (rdot_isLinear n) c)
  -- the witness convex set
  have hB : Convex ℝ (convexHull ℝ A₁ ∪ {y | rdot n y < c}) := by
    rintro p hp q hq a b ha hb hab
    have hsum : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    rcases hp with hp | hp
    · rcases hq with hq | hq
      · exact Or.inl (convex_convexHull ℝ A₁ hp hq ha hb hab)
      · rcases eq_or_lt_of_le hb with hb0 | hb0
        · have hb0' : b = 0 := hb0.symm
          have ha1 : a = 1 := by linarith
          refine Or.inl ?_
          rw [ha1, hb0', one_smul, zero_smul, add_zero]
          exact hp
        · refine Or.inr ?_
          show rdot n (a • p + b • q) < c
          rw [rdot_smul_add, hhull_eq p hp]
          have := mul_lt_mul_of_pos_left hq hb0
          linarith
    · rcases hq with hq | hq
      · rcases eq_or_lt_of_le ha with ha0 | ha0
        · have ha0' : a = 0 := ha0.symm
          have hb1 : b = 1 := by linarith
          refine Or.inl ?_
          rw [ha0', hb1, one_smul, zero_smul, zero_add]
          exact hq
        · refine Or.inr ?_
          show rdot n (a • p + b • q) < c
          rw [rdot_smul_add, hhull_eq q hq]
          have := mul_lt_mul_of_pos_left hp ha0
          linarith
      · exact Or.inr (convex_halfSpace_lt (rdot_isLinear n) c hp hq ha hb hab)
  have hAB : A ⊆ convexHull ℝ A₁ ∪ {y | rdot n y < c} := by
    intro a haA
    rcases lt_or_eq_of_le (hle a haA) with h | h
    · exact Or.inr h
    · exact Or.inl (subset_convexHull ℝ A₁ ⟨haA, h⟩)
  rcases convexHull_min hAB hB hx with h | h
  · exact h
  · exact absurd hxc (ne_of_lt h)

/-! ## §3. The bridge `face` ↔ `hface` -/

/-- `Conv S` lies in the half plane cut out by any support level of `S`. -/
theorem Conv_subset_halfSpace {S : Finset (ℤ × ℤ)} {n : ℤ × ℤ} {c : ℤ}
    (hle : ∀ z ∈ S, dot n z ≤ c) :
    ∀ y ∈ Conv S, rdot (toReal n) y ≤ (c : ℝ) := by
  refine convexHull_min ?_ (convex_halfSpace_le (rdot_isLinear (toReal n)) (c : ℝ))
  rintro _ ⟨z, hz, rfl⟩
  show rdot (toReal n) (toReal z) ≤ (c : ℝ)
  rw [rdot_toReal]
  exact_mod_cast hle z hz

/-- Two distinct maximisers in `S` give two distinct points of the exposed face of `Conv S`. -/
theorem nontrivial_hface_of_nontrivial_face {S : Finset (ℤ × ℤ)} {n : ℤ × ℤ}
    (h : (face (↑S : Set (ℤ × ℤ)) n).Nontrivial) :
    (hface (Conv S) (toReal n)).Nontrivial := by
  obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := h
  have key : ∀ z ∈ face (↑S : Set (ℤ × ℤ)) n, toReal z ∈ hface (Conv S) (toReal n) := by
    rintro z ⟨hzS, hzmax⟩
    refine ⟨subset_Conv hzS, fun y hy => ?_⟩
    rw [rdot_toReal]
    exact Conv_subset_halfSpace (fun w hw => hzmax w hw) y hy
  exact ⟨toReal z₁, key z₁ hz₁, toReal z₂, key z₂ hz₂,
    fun hc => hne (toReal_injective hc)⟩

/-- Conversely, if the maximisers in `S` are a single point then the exposed face of
`Conv S` collapses to that point. -/
theorem subsingleton_hface_of_subsingleton_face {S : Finset (ℤ × ℤ)} {n : ℤ × ℤ}
    (h : (face (↑S : Set (ℤ × ℤ)) n).Subsingleton) :
    (hface (Conv S) (toReal n)).Subsingleton := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · -- `Conv ∅ = ∅`
    have hC : Conv (∅ : Finset (ℤ × ℤ)) = (∅ : Set (ℝ × ℝ)) := by
      simp only [Conv, Finset.coe_empty, Set.image_empty, convexHull_empty]
    intro x hx
    rw [hC] at hx
    exact absurd hx.1 (Set.notMem_empty x)
  · obtain ⟨z₀, hz₀⟩ :=
      face_nonempty (S.finite_toSet) (Finset.coe_nonempty.mpr hSne) n
    set c : ℤ := dot n z₀ with hc
    have hmaxS : ∀ z ∈ S, dot n z ≤ c := fun z hz => hz₀.2 z hz
    -- the slice of `toReal '' S` on the supporting hyperplane is `{toReal z₀}`
    have hslice : {a | a ∈ toReal '' (↑S : Set (ℤ × ℤ)) ∧ rdot (toReal n) a = (c : ℝ)}
        = {toReal z₀} := by
      ext a
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, ha⟩
        rw [rdot_toReal] at ha
        have hzc : dot n z = c := by exact_mod_cast ha
        have : z ∈ face (↑S : Set (ℤ × ℤ)) n := ⟨hz, fun y hy => hzc ▸ hmaxS y hy⟩
        exact congrArg toReal (h this hz₀)
      · rintro rfl
        exact ⟨⟨z₀, hz₀.1, rfl⟩, by rw [rdot_toReal]⟩
    have hcollapse : ∀ x ∈ hface (Conv S) (toReal n), x = toReal z₀ := by
      rintro x ⟨hxC, hxmax⟩
      have hub : rdot (toReal n) x ≤ (c : ℝ) := Conv_subset_halfSpace hmaxS x hxC
      have hlb : (c : ℝ) ≤ rdot (toReal n) x := by
        have := hxmax (toReal z₀) (subset_Conv hz₀.1)
        rwa [rdot_toReal] at this
      have hxc : rdot (toReal n) x = (c : ℝ) := le_antisymm hub hlb
      have hle : ∀ a ∈ toReal '' (↑S : Set (ℤ × ℤ)), rdot (toReal n) a ≤ (c : ℝ) := by
        rintro _ ⟨z, hz, rfl⟩
        rw [rdot_toReal]
        exact_mod_cast hmaxS z hz
      have := mem_convexHull_sep_of_rdot_eq hle hxC hxc
      rw [hslice, convexHull_singleton] at this
      exact this
    intro x hx y hy
    rw [hcollapse x hx, hcollapse y hy]

/-- **The bridge.**  Having an edge in direction `n` is a property of the convex hull:
the lattice face is non-trivial iff the exposed face of the hull is. -/
theorem nontrivial_face_iff (S : Finset (ℤ × ℤ)) (n : ℤ × ℤ) :
    (face (↑S : Set (ℤ × ℤ)) n).Nontrivial ↔ (hface (Conv S) (toReal n)).Nontrivial := by
  constructor
  · exact nontrivial_hface_of_nontrivial_face
  · intro h
    by_contra hcon
    exact (Set.not_nontrivial_iff.mpr
      (subsingleton_hface_of_subsingleton_face (Set.not_nontrivial_iff.mp hcon))) h

/-! ## §4. The transport lemma -/

/-- **Transport of `E(·)` along equality of convex hulls.**  If `S` and `T` have the same
convex hull then they have the same edge normals. -/
theorem E_congr_of_Conv_eq {S T : Finset (ℤ × ℤ)} (h : Conv S = Conv T) :
    E (↑S : Set (ℤ × ℤ)) = E (↑T : Set (ℤ × ℤ)) := by
  ext n
  simp only [mem_E_iff, nontrivial_face_iff, h]

/-- Pointwise form of `E_congr_of_Conv_eq`. -/
theorem IsEdge_congr_of_Conv_eq {S T : Finset (ℤ × ℤ)} (h : Conv S = Conv T) (n : ℤ × ℤ) :
    IsEdge (↑S : Set (ℤ × ℤ)) n ↔ IsEdge (↑T : Set (ℤ × ℤ)) n := by
  simp only [IsEdge, nontrivial_face_iff, h]

/-- Membership form, the shape `Claim36.lean` needs: `n ∉ E ↑S` transports. -/
theorem mem_E_congr_of_Conv_eq {S T : Finset (ℤ × ℤ)} (h : Conv S = Conv T) (n : ℤ × ℤ) :
    n ∈ E (↑S : Set (ℤ × ℤ)) ↔ n ∈ E (↑T : Set (ℤ × ℤ)) := by
  rw [E_congr_of_Conv_eq h]

/-- The face non-triviality is what transports; the *level* of the face need not agree,
but the two support values do. -/
theorem dot_face_eq_of_Conv_eq {S T : Finset (ℤ × ℤ)} (h : Conv S = Conv T) (n : ℤ × ℤ)
    {a b : ℤ × ℤ} (ha : a ∈ face (↑S : Set (ℤ × ℤ)) n) (hb : b ∈ face (↑T : Set (ℤ × ℤ)) n) :
    dot n a = dot n b := by
  have hA : ∀ y ∈ Conv S, rdot (toReal n) y ≤ ((dot n a : ℤ) : ℝ) :=
    Conv_subset_halfSpace (fun z hz => ha.2 z hz)
  have hB : ∀ y ∈ Conv T, rdot (toReal n) y ≤ ((dot n b : ℤ) : ℝ) :=
    Conv_subset_halfSpace (fun z hz => hb.2 z hz)
  have h1 : ((dot n b : ℤ) : ℝ) ≤ ((dot n a : ℤ) : ℝ) := by
    have := hA (toReal b) (h ▸ subset_Conv hb.1)
    rwa [rdot_toReal] at this
  have h2 : ((dot n a : ℤ) : ℝ) ≤ ((dot n b : ℤ) : ℝ) := by
    have := hB (toReal a) (h ▸ subset_Conv ha.1)
    rwa [rdot_toReal] at this
  exact_mod_cast le_antisymm h2 h1

/-! ## §5. Sharpness: `face` itself does not transport

The statement proved above is at the strongest level available: replacing
`(face · n).Nontrivial` by `face · n` makes it false.  Witness: the segment
`{(0,0),(1,0),(2,0)}` versus its two endpoints. -/

private def segS : Finset (ℤ × ℤ) := {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((2 : ℤ), (0 : ℤ))}

private def segT : Finset (ℤ × ℤ) := {((0 : ℤ), (0 : ℤ)), ((2 : ℤ), (0 : ℤ))}

private theorem Conv_segS_eq_segT : Conv segS = Conv segT := by
  have hTS : Conv segT ⊆ Conv segS := by
    refine convexHull_mono ?_
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    simp only [segT, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    simp only [segS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  have hST : Conv segS ⊆ Conv segT := by
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    rintro _ ⟨z, hz, rfl⟩
    have h0 : toReal ((0 : ℤ), (0 : ℤ)) ∈ Conv segT := subset_Conv (by decide)
    have h2 : toReal ((2 : ℤ), (0 : ℤ)) ∈ Conv segT := subset_Conv (by decide)
    simp only [segS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact h0
    · -- `(1,0) = ½·(0,0) + ½·(2,0)`
      have hmid := convex_convexHull ℝ (toReal '' (↑segT : Set (ℤ × ℤ)))
        h0 h2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
      have heq : (1/2 : ℝ) • toReal ((0 : ℤ), (0 : ℤ)) + (1/2 : ℝ) • toReal ((2 : ℤ), (0 : ℤ))
          = toReal ((1 : ℤ), (0 : ℤ)) := by
        simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
        norm_num
      rw [heq] at hmid
      exact hmid
    · exact h2
  exact Set.Subset.antisymm hST hTS

private theorem face_segS_ne_segT :
    face (↑segS : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ))
      ≠ face (↑segT : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ)) := by
  intro hcon
  have hmem : ((1 : ℤ), (0 : ℤ)) ∈ face (↑segS : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ)) := by
    refine ⟨by decide, ?_⟩
    intro y hy
    simp only [segS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> simp [dot]
  rw [hcon] at hmem
  have : ((1 : ℤ), (0 : ℤ)) ∈ (↑segT : Set (ℤ × ℤ)) := hmem.1
  simp only [segT, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at this
  rcases this with h | h <;> exact absurd h (by decide)

/-- `E_congr_of_Conv_eq` cannot be upgraded to `face`: equal convex hulls do **not** force
equal faces.  Hence `Nontrivial` is exactly the amount of information about a face that the
convex hull determines. -/
theorem exists_Conv_eq_face_ne :
    ∃ S T : Finset (ℤ × ℤ), Conv S = Conv T ∧
      ∃ n : ℤ × ℤ, face (↑S : Set (ℤ × ℤ)) n ≠ face (↑T : Set (ℤ × ℤ)) n :=
  ⟨segS, segT, Conv_segS_eq_segT, ((0 : ℤ), (1 : ℤ)), face_segS_ne_segT⟩

/-- ... and the two sets are genuinely different, so the witness is not vacuous. -/
theorem segS_ne_segT : segS ≠ segT := by decide

end Nivat.LE2
