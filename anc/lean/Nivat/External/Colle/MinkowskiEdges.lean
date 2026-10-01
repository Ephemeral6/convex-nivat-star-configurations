/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.Laurent.Basic

/-!
# The Minkowski rule for the lattice edge operator `Nivat.LE2.E`

This file supplies the lattice-level Minkowski additivity rule whose absence is recorded
as the `sorry` reason attached to `generatingSet_no_edge_parallel` in
`Nivat/External/Colle/Claim36.lean`:

> `sorry` reason: needs the lattice-level Minkowski rule `E (A + B) = E A ∪ E B`, which is
> absent from the tree (confirmed by search: 0 hits).

The absence was re-verified for this file (see the *Survey* section below).  Nothing in
this file is imported by anything else; it edits no existing file.

## The operator being studied

Verbatim from `Nivat/External/Colle/LatticeEdges.lean` (`IsEdge`/`E`, at lines 212-217 as
of this writing):

```
/-- `n` is an **edge normal** of `R` if it is primitive and its exposed face contains
at least two lattice points.  `E R` is Colle's `E(R)`. -/
def IsEdge (R : Set (ℤ × ℤ)) (n : ℤ × ℤ) : Prop := Prim n ∧ (face R n).Nontrivial

/-- `E(R)`, the set of edges of `R`, indexed by primitive outer normals. -/
def E (R : Set (ℤ × ℤ)) : Set (ℤ × ℤ) := {n | IsEdge R n}
```

with (`LatticeEdges.lean:160-161`)

```
def face (R : Set (ℤ × ℤ)) (n : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {z | z ∈ R ∧ ∀ y ∈ R, dot n y ≤ dot n z}
```

Note **`E R` is a set of primitive outer NORMALS, not of edge directions.**  That is
stated in the docstring above and in `LatticeEdges.lean:51-52`, and it is the point on
which §6 below turns.

## What is true, and what is false

The naive statement `E (A + B) = E A ∪ E B` is **false** at the generality of
`Set (ℤ × ℤ)`.  The refutation is `E_add_ne` (§3): it is kernel-checked, and the failing
direction is `E A ∪ E B ⊆ E (A + B)`, which breaks as soon as one summand is unbounded in
the relevant direction, because then the corresponding face is *empty*.

The true picture, all proved below:

| statement | hypotheses |
|---|---|
| `face (A + B) n = face A n + face B n` (`face_add`) | **none** |
| `E (A + B) ⊆ E A ∪ E B` (`E_add_subset`) | **none** |
| `n ∈ E A → (face B n).Nonempty → n ∈ E (A + B)` (`mem_E_add_of_mem_E_left`) | as stated |
| `E (A + B) = E A ∪ E B` (`E_add_of_finite`) | `A`, `B` finite and non-empty |

No lattice-convexity hypothesis is needed anywhere; `face_add` holds for arbitrary,
possibly non-convex, possibly infinite subsets of `ℤ²`.  This is *stronger* than what the
Claim 3.6 plan asked for, not weaker.

## Survey (re-verified for this file)

A search of the build graph for any pre-existing lattice-level Minkowski additivity for
`E` or `face` — `E (A + B)`, `face (A + B)`, Minkowski/pointwise sums on `Set (ℤ × ℤ)` —
returns **0 hits**, confirming the claim recorded in `Claim36.lean` (the "genuinely
absent (confirmed by search, 0 hits)" note, and the `sorry` reason).  The
only additivity in the tree is `Nivat/Laurent/Ostrowski.lean:171`
`newt_prod : newt (∏ i ∈ s, f i) = ∑ i ∈ s, newt (f i)`, which lives in `ℝ²` as
`Conv (supp ·)` over `ℂ` and has no transport to `Nivat.LE2.E`.  There is also **no**
lemma anywhere of the form `Conv S = Conv T → E ↑S = E ↑T`; see the Status section.

## Main results

* §1 `face_add` — the Minkowski rule for faces, unconditional.
* §2 `E_add_subset`, `mem_E_add_of_mem_E_left`, `E_add_of_finite` — the edge rule.
* §3 `E_add_ne` — refutation of the naive unrestricted equality.
* §4 `E_segOf`, `E_zono`, `zono_no_edge_parallel` — edges of a lattice zonotope, and the
  corrected form of Claim 3.6's Gap 1.
* §5 non-degeneracy witnesses for every definition introduced here.
* §6 `generatingSet_no_edge_parallel_false`, `generatingSet_no_edge_parallel_false_posArea`
  — `generatingSet_no_edge_parallel` (in `Claim36.lean`) is **false as stated**.

Citations to `Claim36.lean` are by declaration name, not line number: that file is under
concurrent edit and every line number quoted here went stale within the hour.
-/

namespace Nivat.LE2

open Nivat Pointwise

/-! ## §1. The Minkowski rule for faces

This is the engine.  It needs no finiteness, no convexity and no non-emptiness: the
inclusion `⊇` says a sum of maximisers is a maximiser, and `⊆` says that in *any*
decomposition `z = a + b` of a maximiser, both parts are maximisers (test against
`y + b` and `a + y`).
-/

/-- **The exposed face of a Minkowski sum is the Minkowski sum of the exposed faces.**
Unconditional: `A` and `B` are arbitrary subsets of `ℤ²`. -/
theorem face_add (A B : Set (ℤ × ℤ)) (n : ℤ × ℤ) :
    face (A + B) n = face A n + face B n := by
  ext z
  constructor
  · rintro ⟨hz, hmax⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hz
    refine Set.mem_add.mpr ⟨a, ⟨ha, fun y hy => ?_⟩, b, ⟨hb, fun y hy => ?_⟩, rfl⟩
    · have := hmax (y + b) (Set.add_mem_add hy hb)
      rw [dot_add, dot_add] at this
      omega
    · have := hmax (a + y) (Set.add_mem_add ha hy)
      rw [dot_add, dot_add] at this
      omega
  · rintro hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hz
    refine ⟨Set.add_mem_add ha.1 hb.1, fun y hy => ?_⟩
    obtain ⟨c, hc, d, hd, rfl⟩ := Set.mem_add.mp hy
    have h1 := ha.2 c hc
    have h2 := hb.2 d hd
    rw [dot_add, dot_add]
    omega

/-! ## §2. The Minkowski rule for edges -/

/-- A Minkowski sum of two subsingletons is a subsingleton. -/
theorem nontrivial_of_add {S T : Set (ℤ × ℤ)} (h : (S + T).Nontrivial) :
    S.Nontrivial ∨ T.Nontrivial := by
  by_contra hc
  push Not at hc
  obtain ⟨hS, hT⟩ := hc
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := Set.mem_add.mp hy
  exact hxy (by rw [hS ha hc, hT hb hd])

/-- **One inclusion of the Minkowski edge rule holds unconditionally.**  A Minkowski sum
has no edge direction that neither summand has. -/
theorem E_add_subset (A B : Set (ℤ × ℤ)) : E (A + B) ⊆ E A ∪ E B := by
  rintro n ⟨hp, hnt⟩
  rw [face_add] at hnt
  rcases nontrivial_of_add hnt with h | h
  exacts [Or.inl ⟨hp, h⟩, Or.inr ⟨hp, h⟩]

/-- The converse inclusion, pointwise: an edge of `A` survives in `A + B` exactly when `B`
*has* a face in that direction.  This is the hypothesis that the naive statement forgets. -/
theorem mem_E_add_of_mem_E_left {A B : Set (ℤ × ℤ)} {n : ℤ × ℤ} (hn : n ∈ E A)
    (hB : (face B n).Nonempty) : n ∈ E (A + B) := by
  obtain ⟨b, hb⟩ := hB
  obtain ⟨a₁, h₁, a₂, h₂, hne⟩ := hn.2
  refine ⟨hn.1, ?_⟩
  rw [face_add]
  exact ⟨a₁ + b, Set.add_mem_add h₁ hb, a₂ + b, Set.add_mem_add h₂ hb,
    fun h => hne (add_right_cancel h)⟩

/-- **The Minkowski edge rule `E (A + B) = E A ∪ E B`**, for finite non-empty `A`, `B`.

No lattice-convexity is required.  Finiteness and non-emptiness are not decoration: they
are exactly what makes every face non-empty (`LatticeEdges.face_nonempty`), and dropping
them makes the statement false — see `E_add_ne`. -/
theorem E_add_of_finite {A B : Set (ℤ × ℤ)} (hA : A.Finite) (hB : B.Finite)
    (hAne : A.Nonempty) (hBne : B.Nonempty) : E (A + B) = E A ∪ E B := by
  refine Set.Subset.antisymm (E_add_subset A B) ?_
  rintro n (hn | hn)
  · exact mem_E_add_of_mem_E_left hn (face_nonempty hB hBne n)
  · rw [add_comm]
    exact mem_E_add_of_mem_E_left hn (face_nonempty hA hAne n)

/-- `E` of the one-point set `0 = {0}` is empty. -/
theorem E_zero : E (0 : Set (ℤ × ℤ)) = ∅ := by
  ext n
  simp only [Set.mem_empty_iff_false, iff_false, mem_E_iff, not_and]
  intro _
  have hsub : face (0 : Set (ℤ × ℤ)) n ⊆ {(0 : ℤ × ℤ)} := fun z hz => hz.1
  exact fun hnt => Set.not_nontrivial_singleton (hnt.mono hsub)

/-! ## §3. The naive unrestricted equality is FALSE

A refutation is a first-class deliverable here: Claim 3.6's recorded plan asks for
`E (A + B) = E A ∪ E B` with no hypotheses, and that statement is false.

The witness is `A = {0, (1,0)}` (a horizontal segment) and `B = quad`, the quarter plane
`{z | 0 ≤ z.1 ∧ 0 ≤ z.2}` already defined at `LatticeEdges.lean:1108`.  Then
`A + B = quad`, so `(0,1)` is an edge normal of `A` that is *not* an edge normal of the
sum: `quad` is unbounded upwards, so `face quad (0,1) = ∅`.
-/

/-- The lattice segment `{0, v}`. -/
def segOf (v : ℤ × ℤ) : Set (ℤ × ℤ) := {0, v}

theorem dot_zero_right (n : ℤ × ℤ) : dot n 0 = 0 := by simp [dot]

theorem face_segOf_of_dot_eq_zero {v n : ℤ × ℤ} (h : dot n v = 0) :
    face (segOf v) n = segOf v := by
  ext z
  refine ⟨fun hz => hz.1, fun hz => ⟨hz, fun y hy => ?_⟩⟩
  rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> simp [h, dot_zero_right]

/-- **The edge normals of a lattice segment** are exactly the primitive vectors orthogonal
to it.  (The segment has no interior; both of its "sides" expose the whole segment.) -/
theorem E_segOf {v : ℤ × ℤ} (hv : v ≠ 0) : E (segOf v) = {n | Prim n ∧ dot n v = 0} := by
  ext n
  constructor
  · rintro ⟨hp, hnt⟩
    refine ⟨hp, ?_⟩
    by_contra hne
    have hsub : face (segOf v) n ⊆ if 0 < dot n v then {v} else {(0 : ℤ × ℤ)} := by
      rintro z ⟨hz, hmax⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [if_neg (by omega)]
        rcases hz with rfl | rfl
        · rfl
        · exact absurd (hmax 0 (Or.inl rfl)) (by rw [dot_zero_right]; omega)
      · rw [if_pos hgt]
        rcases hz with rfl | rfl
        · exact absurd (hmax v (Or.inr rfl)) (by rw [dot_zero_right]; omega)
        · rfl
    refine absurd (hnt.mono hsub) ?_
    split <;> exact Set.not_nontrivial_singleton
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rw [face_segOf_of_dot_eq_zero h]
    exact ⟨0, Or.inl rfl, v, Or.inr rfl, fun hc => hv hc.symm⟩

theorem finite_segOf (v : ℤ × ℤ) : (segOf v).Finite := (Set.finite_singleton v).insert 0

theorem nonempty_segOf (v : ℤ × ℤ) : (segOf v).Nonempty := ⟨0, Or.inl rfl⟩

theorem mem_E_segOf_up : ((0 : ℤ), (1 : ℤ)) ∈ E (segOf ((1 : ℤ), (0 : ℤ))) := by
  rw [E_segOf (by decide)]
  exact ⟨by decide, by decide⟩

theorem segOf_add_quad : segOf ((1 : ℤ), (0 : ℤ)) + quad = quad := by
  ext z
  constructor
  · rintro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp h
    have h1 : (0 : ℤ) ≤ b.1 := hb.1
    have h2 : (0 : ℤ) ≤ b.2 := hb.2
    rcases ha with rfl | rfl
    · exact ⟨show (0 : ℤ) ≤ 0 + b.1 by omega, show (0 : ℤ) ≤ 0 + b.2 by omega⟩
    · exact ⟨show (0 : ℤ) ≤ 1 + b.1 by omega, show (0 : ℤ) ≤ 0 + b.2 by omega⟩
  · intro hz
    exact Set.mem_add.mpr ⟨0, Or.inl rfl, z, hz, by simp⟩

/-- **REFUTATION.**  `E (A + B) = E A ∪ E B` is false for general subsets of `ℤ²`.

Witness: `A = {0, (1,0)}`, `B = quad`.  `(0,1) ∈ E A` but `(0,1) ∉ E (A + B) = E quad`.
So the plan recorded in the `sorry` reason in `Claim36.lean` cannot be carried out as
literally stated;
the finiteness hypotheses of `E_add_of_finite` are necessary, not cosmetic. -/
theorem E_add_ne :
    E (segOf ((1 : ℤ), (0 : ℤ)) + quad) ≠ E (segOf ((1 : ℤ), (0 : ℤ))) ∪ E quad := by
  intro hEq
  have hmem : ((0 : ℤ), (1 : ℤ)) ∈ E (segOf ((1 : ℤ), (0 : ℤ)) + quad) := by
    rw [hEq]; exact Or.inl mem_E_segOf_up
  rw [segOf_add_quad] at hmem
  rw [mem_E_iff, face_quad_eq_empty (Or.inr (by norm_num))] at hmem
  exact Set.not_nontrivial_empty hmem.2

/-! ## §4. Lattice zonotopes, and the corrected form of Claim 3.6's Gap 1

A Minkowski sum of segments is a *zonotope*.  Its edge normals are exactly the primitive
vectors orthogonal to some generator.  This is the shape Claim 3.6 needs, because the
Newton polygon of `ψ = ∏_{i ≠ m} (X^{h_i} - 1)` is the zonotope generated by the segments
`[0, h_i]`.
-/

theorem finite_zono {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ) :
    (∑ i ∈ s, segOf (h i)).Finite := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact Set.finite_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (finite_segOf (h a)).add ih

theorem nonempty_zono {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ) :
    (∑ i ∈ s, segOf (h i)).Nonempty := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, rfl⟩
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (nonempty_segOf (h a)).add ih

/-- **The edges of a lattice zonotope**: `E (∑ [0, hᵢ]) = ⋃ E [0, hᵢ]`.  Direct
consequence of `E_add_of_finite`. -/
theorem E_zono {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ) :
    E (∑ i ∈ s, segOf (h i)) = ⋃ i ∈ s, E (segOf (h i)) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, E_zero]; simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha,
        E_add_of_finite (finite_segOf (h a)) (finite_zono s h)
          (nonempty_segOf (h a)) (nonempty_zono s h), ih]
      simp only [Finset.set_biUnion_insert]

/-- The edge with outer normal `n` runs in direction `dir n`, and `det (dir n) ℓ` measures
its failure to be parallel to `ℓ`.  So "the edge `n` is parallel to `ℓ`" is `dot n ℓ = 0`. -/
theorem det_dir (n ℓ : ℤ × ℤ) : det (dir n) ℓ = - dot n ℓ := by
  simp only [det, dir, dot]; ring

/-- **The corrected form of Claim 3.6's Gap 1.**

If no generator `h i` of the zonotope is parallel to `ℓ`, then no *edge* of the zonotope
is parallel to `ℓ`.  This is the statement `generatingSet_no_edge_parallel`
(in `Claim36.lean`) is trying to make; see §6 for why what it actually says is false. -/
theorem zono_no_edge_parallel {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ)
    (hne : ∀ i ∈ s, h i ≠ 0) {ℓ : ℤ × ℤ}
    (hpar : ∀ i ∈ s, det (h i) ℓ ≠ 0) {n : ℤ × ℤ}
    (hn : n ∈ E (∑ i ∈ s, segOf (h i))) : det (dir n) ℓ ≠ 0 := by
  rw [E_zono] at hn
  simp only [Set.mem_iUnion] at hn
  obtain ⟨i, hi, hmem⟩ := hn
  rw [E_segOf (hne i hi)] at hmem
  rw [det_dir]
  intro hc
  exact hpar i hi (det_eq_zero_of_dot_eq_zero hmem.1.ne_zero hmem.2 (by omega))

/-! ## §5. Non-degeneracy

This project's most-repeated bug is a definition that is vacuously true for everything or
true for nothing.  The only definition introduced in this file is `segOf`; no new `Prop`
and no new `structure` is introduced (the refutations of §3 and §6 are theorems, not
definitions).  `segOf` gets both a satisfiability witness and a refutation, and the
derived edge sets get a positive computation cross-checked against `LatticeEdges.E_box`.
-/

theorem mem_segOf_zero (v : ℤ × ℤ) : (0 : ℤ × ℤ) ∈ segOf v := Or.inl rfl

theorem mem_segOf_self (v : ℤ × ℤ) : v ∈ segOf v := Or.inr rfl

/-- `segOf` is not everything: `(1,0) ∉ segOf (0,1)`. -/
theorem notMem_segOf : ((1 : ℤ), (0 : ℤ)) ∉ segOf ((0 : ℤ), (1 : ℤ)) := by
  simp [segOf, Prod.ext_iff]

/-- `segOf v` is a genuine two-point set when `v ≠ 0` — not a singleton. -/
theorem segOf_nontrivial {v : ℤ × ℤ} (hv : v ≠ 0) : (segOf v).Nontrivial :=
  ⟨0, mem_segOf_zero v, v, mem_segOf_self v, fun h => hv h.symm⟩

/-- `E (segOf v)` is non-empty for `v ≠ 0` — the edge rule is not producing `∅`. -/
theorem E_segOf_horizontal : E (segOf ((1 : ℤ), (0 : ℤ))) = {((0 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-1 : ℤ))} := by
  rw [E_segOf (by decide)]
  ext n
  constructor
  · rintro ⟨hp, hd⟩
    have h1 : n.1 = 0 := by simpa [dot] using hd
    rcases prim_eq_of_fst_eq_zero hp h1 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl) <;> exact ⟨by decide, by decide⟩

/-- **Cross-check against the existing tree.**  The unit square `sq1 = box (0,0) (1,1)`
(`LatticeEdges.lean:923`) is the zonotope generated by the two unit segments, and the
Minkowski edge rule reproduces exactly the four edges that `LatticeEdges.E_sq1` computes
independently.  So `E_add_of_finite` really does output a four-edge lattice polygon, not a
degenerate set. -/
theorem zono_eq_sq1 : segOf ((1 : ℤ), (0 : ℤ)) + segOf ((0 : ℤ), (1 : ℤ)) = sq1 := by
  ext z
  constructor
  · rintro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp h
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      exact ⟨by decide, by decide, by decide, by decide⟩
  · rintro ⟨h1, h2, h3, h4⟩
    simp only at h1 h2 h3 h4
    refine Set.mem_add.mpr ⟨(z.1, 0), ?_, (0, z.2), ?_, ?_⟩
    · rcases (by omega : z.1 = 0 ∨ z.1 = 1) with h | h
      · exact Or.inl (by rw [h]; rfl)
      · exact Or.inr (show (z.1, (0 : ℤ)) = ((1 : ℤ), (0 : ℤ)) from by rw [h])
    · rcases (by omega : z.2 = 0 ∨ z.2 = 1) with h | h
      · exact Or.inl (by rw [h]; rfl)
      · exact Or.inr (show ((0 : ℤ), z.2) = ((0 : ℤ), (1 : ℤ)) from by rw [h])
    · exact Prod.ext (by simp) (by simp)

theorem E_zono_sq1 :
    E (segOf ((1 : ℤ), (0 : ℤ)) + segOf ((0 : ℤ), (1 : ℤ))) =
      {((1 : ℤ), (0 : ℤ)), ((-1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((0 : ℤ), (-1 : ℤ))} := by
  rw [zono_eq_sq1, E_sq1]

/-- The same four edges, obtained instead from `E_add_of_finite` — the two computations
agree, which is the cross-check. -/
theorem E_zono_sq1' :
    E (segOf ((1 : ℤ), (0 : ℤ)) + segOf ((0 : ℤ), (1 : ℤ))) =
      E (segOf ((1 : ℤ), (0 : ℤ))) ∪ E (segOf ((0 : ℤ), (1 : ℤ))) :=
  E_add_of_finite (finite_segOf _) (finite_segOf _) (nonempty_segOf _) (nonempty_segOf _)

/-! ## §7. Minkowski symmetry technical lemmas -/

/-- For any non-zero integer vector, there exists a primitive orthogonal vector. -/
theorem exists_prim_orthogonal {u : ℤ × ℤ} (hu : u ≠ 0) :
    ∃ v : ℤ × ℤ, Prim v ∧ dot u v = 0 := by
  have hrot_ne : ((-u.2, u.1) : ℤ × ℤ) ≠ 0 := by
    intro h
    apply hu
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
    have h1' : (-u.2 : ℤ) = 0 := h1
    have h2' : (u.1 : ℤ) = 0 := h2
    exact Prod.ext (by omega) (by omega)
  have hg_ne : Int.gcd (-u.2) u.1 ≠ 0 := by
    intro h
    apply hrot_ne
    obtain ⟨h1, h2⟩ := Int.gcd_eq_zero_iff.mp h
    exact Prod.ext h1 h2
  have hg_pos : 0 < Int.gcd (-u.2) u.1 := Nat.pos_of_ne_zero hg_ne
  have hd1 : (↑(Int.gcd (-u.2) u.1) : ℤ) ∣ (-u.2) := Int.gcd_dvd_left (-u.2) u.1
  have hd2 : (↑(Int.gcd (-u.2) u.1) : ℤ) ∣ u.1 := Int.gcd_dvd_right (-u.2) u.1
  refine ⟨((-u.2) / (Int.gcd (-u.2) u.1 : ℤ), u.1 / (Int.gcd (-u.2) u.1 : ℤ)), ?_, ?_⟩
  · exact Int.gcd_div_gcd_div_gcd hg_pos
  · have e1 : (↑(Int.gcd (-u.2) u.1) : ℤ) * ((-u.2) / (Int.gcd (-u.2) u.1 : ℤ)) = -u.2 :=
      Int.mul_ediv_cancel' hd1
    have e2 : (↑(Int.gcd (-u.2) u.1) : ℤ) * (u.1 / (Int.gcd (-u.2) u.1 : ℤ)) = u.1 :=
      Int.mul_ediv_cancel' hd2
    have hgz : (↑(Int.gcd (-u.2) u.1) : ℤ) ≠ 0 := by exact_mod_cast hg_ne
    show dot u ((-u.2) / (Int.gcd (-u.2) u.1 : ℤ), u.1 / (Int.gcd (-u.2) u.1 : ℤ)) = 0
    simp only [dot]
    have key : (↑(Int.gcd (-u.2) u.1) : ℤ) *
        (u.1 * ((-u.2) / (Int.gcd (-u.2) u.1 : ℤ)) + u.2 * (u.1 / (Int.gcd (-u.2) u.1 : ℤ)))
        = 0 := by
      have expand : (↑(Int.gcd (-u.2) u.1) : ℤ) *
          (u.1 * ((-u.2) / (Int.gcd (-u.2) u.1 : ℤ)) + u.2 * (u.1 / (Int.gcd (-u.2) u.1 : ℤ)))
        = u.1 * ((↑(Int.gcd (-u.2) u.1) : ℤ) * ((-u.2) / (Int.gcd (-u.2) u.1 : ℤ)))
          + u.2 * ((↑(Int.gcd (-u.2) u.1) : ℤ) * (u.1 / (Int.gcd (-u.2) u.1 : ℤ))) := by ring
      rw [expand, e1, e2]; ring
    exact (mul_eq_zero.mp key).resolve_left hgz

/-- **Corrected statement 2026-09-16** (the original, with no `n ≠ 0`/`n' ≠ 0` hypotheses, is
FALSE: `n = n' = 0`, `u = (1,0)`, `v = (0,1)` satisfies both orthogonality hypotheses vacuously
and `det u v = 1 ≠ 0`, while `det n n' = 0`).  The old signature had zero call sites anywhere in
the tree, so adding the two non-degeneracy hypotheses is a pure strengthening with no downstream
breakage.

If `n ⊥ u`, `n' ⊥ v`, `n ≠ 0`, `n' ≠ 0`, and `det u v ≠ 0`, then `det n n' ≠ 0`. -/
theorem det_ne_zero_of_orthogonal {n n' u v : ℤ × ℤ}
    (hn_ne : n ≠ 0) (hn'_ne : n' ≠ 0)
    (hn : dot n u = 0) (hn' : dot n' v = 0) (huv : det u v ≠ 0) :
    det n n' ≠ 0 := by
  simp only [dot] at hn hn'
  simp only [det] at huv ⊢
  intro hP
  have key1 : n.1 * n'.1 * (u.1 * v.2 - u.2 * v.1) = 0 := by
    linear_combination n'.1 * v.2 * hn - n.1 * u.2 * hn' + u.2 * v.2 * hP
  have key2 : n.2 * n'.2 * (u.1 * v.2 - u.2 * v.1) = 0 := by
    linear_combination n.2 * u.1 * hn' - n'.2 * v.1 * hn + u.1 * v.1 * hP
  have h11 : n.1 * n'.1 = 0 := (mul_eq_zero.mp key1).resolve_right huv
  have h22 : n.2 * n'.2 = 0 := (mul_eq_zero.mp key2).resolve_right huv
  rcases eq_or_ne n.1 0 with hn1 | hn1
  · have hn2 : n.2 ≠ 0 := fun h2 => hn_ne (Prod.ext hn1 h2)
    have hn'1 : n'.1 = 0 := by
      have h0 : n.2 * n'.1 = 0 := by linear_combination -hP + n'.2 * hn1
      exact (mul_eq_zero.mp h0).resolve_left hn2
    have hn'2 : n'.2 ≠ 0 := fun h2 => hn'_ne (Prod.ext hn'1 h2)
    exact (mul_ne_zero hn2 hn'2) h22
  · have hn'1 : n'.1 = 0 := (mul_eq_zero.mp h11).resolve_left hn1
    have hn'2 : n'.2 = 0 := by
      have h0 : n.1 * n'.2 = 0 := by linear_combination hP + n.2 * hn'1
      exact (mul_eq_zero.mp h0).resolve_left hn1
    exact hn'_ne (Prod.ext hn'1 hn'2)

/-- E is symmetric under Minkowski sum: E A ∪ E B ⊆ E(A + B) when finite and non-empty. -/
theorem E_minkowskiSum_symm {A B : Set (ℤ × ℤ)}
    (hA : A.Finite) (hB : B.Finite) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    E A ∪ E B ⊆ E (A + B) := by
  intro n hn
  rcases hn with hn | hn
  · exact mem_E_add_of_mem_E_left hn (face_nonempty hB hBne n)
  · rw [add_comm]
    exact mem_E_add_of_mem_E_left hn (face_nonempty hA hAne n)

end Nivat.LE2

/-! ## §6. Does this discharge `generatingSet_no_edge_parallel`?  No — that statement is
false.

`Claim36.lean`'s `generatingSet_no_edge_parallel` asks for

```
theorem generatingSet_no_edge_parallel {m : ℕ} (hm : 2 ≤ m) {h : Fin m → ℤ × ℤ}
    (hh_ne : ∀ i, h i ≠ 0)
    (hh_dir : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0)
    {i_m : Fin m} {ℓ_m : ℤ × ℤ} (hℓ_prim : Primitive ℓ_m)
    (hℓ_dir : ∃ c : ℤ, c ≠ 0 ∧ h i_m = c • ℓ_m)
    {S_ψ : Finset (ℤ × ℤ)}
    (hS_hull : Conv S_ψ = Conv (supp (∏ i ∈ Finset.univ.erase i_m, (mono (h i) - 1 :
      LaurentTwo ℤ)))) :
    ℓ_m ∉ E (↑S_ψ : Set (ℤ × ℤ)) ∧ -ℓ_m ∉ E (↑S_ψ : Set (ℤ × ℤ))
```

**This is not provable, because it is false**, and no Minkowski rule can repair it.  The
defect is a units mismatch, not a missing lemma: `E` is a set of primitive outer
**normals** (`LatticeEdges.lean`, the `E`/`IsEdge` docstrings quoted at the head of this
file), whereas `ℓ_m` is a **direction** — it is
the primitive direction of the period vector `h i_m`, by `hℓ_dir : h i_m = c • ℓ_m`.  The
paper's sentence "`S_ψ` has no edge parallel to `±ℓ_m`" therefore translates to

```
∀ n ∈ E ↑S_ψ, det (dir n) ℓ_m ≠ 0      (equivalently, by det_dir:  dot n ℓ_m ≠ 0)
```

and **not** to `ℓ_m ∉ E ↑S_ψ`.  The two differ by a 90° rotation, and `ℓ_m ∉ E ↑S_ψ` is
in general false: `ℓ_m` occurs as a normal of `S_ψ` precisely when some *other* period
`h i`, `i ≠ i_m`, is orthogonal to `ℓ_m` — which the hypothesis `hh_dir` (pairwise
non-parallel) explicitly permits.

Two witnesses are given.  The first is minimal; the second answers the objection that the
first has `Conv S_ψ` of zero area.

The proved replacement is `Nivat.LE2.zono_no_edge_parallel` (§4), which is the corrected
statement for the Newton zonotope.  See the Status section for what still stands between
that and a proof of Gap 1.
-/

namespace Nivat.LE2.Colle36Fit

open Nivat Nivat.LE2

/-! ### §6.1 Witness A: `m = 2` -/

/-- `h₁ = (1,0)`, `h₂ = (0,1)`: non-zero, pairwise non-parallel, as Claim 3.6 requires. -/
def hw2 : Fin 2 → ℤ × ℤ := ![((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))]

theorem hw2_ne : ∀ i, hw2 i ≠ 0 := by decide +kernel

theorem hw2_dir : ∀ i j, i ≠ j → det (hw2 i) (hw2 j) ≠ 0 := by decide +kernel

theorem supp_mono_sub_one {u : ℤ × ℤ} (hu : u ≠ 0) :
    supp (mono u - 1 : LaurentTwo ℤ) = {u, 0} := by
  ext v
  simp only [mem_supp, Finset.mem_insert, Finset.mem_singleton]
  rw [show ((mono u - 1 : LaurentTwo ℤ)).coeff = (Finsupp.single u 1 - Finsupp.single 0 1)
    from rfl]
  simp only [Finsupp.sub_apply, Finsupp.single_apply]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [if_neg (fun hh => hc.1 hh.symm), if_neg (fun hh => hc.2 hh.symm)] at h
    simp at h
  · rintro (rfl | rfl)
    · rw [if_pos rfl, if_neg (fun hh => hu hh.symm)]; norm_num
    · rw [if_neg (fun hh => hu hh), if_pos rfl]; norm_num

theorem prod_hw2 :
    (∏ i ∈ Finset.univ.erase (1 : Fin 2), (mono (hw2 i) - 1 : LaurentTwo ℤ))
      = mono ((1 : ℤ), (0 : ℤ)) - 1 := by
  rw [show Finset.univ.erase (1 : Fin 2) = {0} from by decide]
  rw [Finset.prod_singleton]
  rfl

theorem supp_prod_hw2 :
    supp (∏ i ∈ Finset.univ.erase (1 : Fin 2), (mono (hw2 i) - 1 : LaurentTwo ℤ))
      = {((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))} := by
  rw [prod_hw2, supp_mono_sub_one (by decide)]
  rfl

theorem mem_E_supp_prod_hw2 :
    ((0 : ℤ), (1 : ℤ)) ∈
      E (↑(supp (∏ i ∈ Finset.univ.erase (1 : Fin 2),
        (mono (hw2 i) - 1 : LaurentTwo ℤ))) : Set (ℤ × ℤ)) := by
  rw [supp_prod_hw2]
  refine ⟨by decide, ?_⟩
  have hc : (↑({((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))
      = {((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))} := by
    simp only [Finset.coe_insert, Finset.coe_singleton]
  rw [hc]
  have hface : ∀ z ∈ ({((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)),
      z ∈ face ({((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ)) := by
    rintro z hz
    refine ⟨hz, fun y hy => ?_⟩
    rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> simp [dot]
  exact ⟨((1 : ℤ), (0 : ℤ)), hface _ (Or.inl rfl), ((0 : ℤ), (0 : ℤ)), hface _ (Or.inr rfl),
    by decide⟩

/-- **REFUTATION of `generatingSet_no_edge_parallel` (in `Claim36.lean`)**, stated as the
universal closure of exactly that theorem (implicit binders made explicit; nothing else
changed, nothing weakened, no hypothesis dropped).

Instance: `m = 2`, `h = ((1,0), (0,1))`, `i_m = 1`, `ℓ_m = (0,1)`,
`S_ψ = supp ψ` so that `hS_hull` holds by `rfl`.  Then `ψ = X^{(1,0)} - 1`,
`S_ψ = {(1,0), (0,0)}`, and `ℓ_m = (0,1) ∈ E ↑S_ψ` because `(0,1)` is orthogonal to the
surviving period `h₁ = (1,0)`.  Every hypothesis of the original is discharged, so this is
not a vacuous refutation. -/
theorem generatingSet_no_edge_parallel_false :
    ¬ (∀ (m : ℕ), 2 ≤ m → ∀ (h : Fin m → ℤ × ℤ), (∀ i, h i ≠ 0) →
        (∀ i j, i ≠ j → det (h i) (h j) ≠ 0) →
        ∀ (i_m : Fin m) (ℓ_m : ℤ × ℤ), Primitive ℓ_m →
        (∃ c : ℤ, c ≠ 0 ∧ h i_m = c • ℓ_m) →
        ∀ S_ψ : Finset (ℤ × ℤ),
          Conv S_ψ = Conv (supp (∏ i ∈ Finset.univ.erase i_m,
            (mono (h i) - 1 : LaurentTwo ℤ))) →
          ℓ_m ∉ E (↑S_ψ : Set (ℤ × ℤ)) ∧ -ℓ_m ∉ E (↑S_ψ : Set (ℤ × ℤ))) := by
  intro hall
  have := hall 2 (le_refl 2) hw2 hw2_ne hw2_dir 1 ((0 : ℤ), (1 : ℤ))
    (by rw [← prim_iff_primitive]; decide)
    ⟨1, by norm_num, by simp [hw2]⟩
    (supp (∏ i ∈ Finset.univ.erase (1 : Fin 2), (mono (hw2 i) - 1 : LaurentTwo ℤ))) rfl
  exact this.1 mem_E_supp_prod_hw2

/-! ### §6.2 Witness B: `m = 3`, with `conv(S_ψ)` of positive area

Witness A leaves `S_ψ` a segment, so `conv(S_ψ)` has zero area and one could object that
Colle's `E(·)` ("if `conv(𝒮)` has positive area, an edge of the convex polygon `conv(𝒮)`",
§2.1) is not meant to apply.  It does not matter: with `m = 3` the set `S_ψ` is a genuine
lattice parallelogram of positive area and the statement still fails.
-/

/-- `h₁ = (1,0)`, `h₂ = (1,1)`, `h₃ = (0,1)`: non-zero, pairwise non-parallel. -/
def hw3 : Fin 3 → ℤ × ℤ := ![((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (1 : ℤ)), ((0 : ℤ), (1 : ℤ))]

theorem hw3_ne : ∀ i, hw3 i ≠ 0 := by decide +kernel

theorem hw3_dir : ∀ i j, i ≠ j → det (hw3 i) (hw3 j) ≠ 0 := by decide +kernel

theorem prod_hw3 :
    (∏ i ∈ Finset.univ.erase (2 : Fin 3), (mono (hw3 i) - 1 : LaurentTwo ℤ))
      = (mono ((1 : ℤ), (0 : ℤ)) - 1) * (mono ((1 : ℤ), (1 : ℤ)) - 1) := by
  rw [show Finset.univ.erase (2 : Fin 3) = {0, 1} from by decide]
  rw [Finset.prod_pair (by decide)]
  rfl

theorem expand_psi3 :
    ((mono ((1 : ℤ), (0 : ℤ)) - 1) * (mono ((1 : ℤ), (1 : ℤ)) - 1) : LaurentTwo ℤ)
      = mono ((2 : ℤ), (1 : ℤ)) - mono ((1 : ℤ), (0 : ℤ)) - mono ((1 : ℤ), (1 : ℤ)) + 1 := by
  have h : ((mono ((1 : ℤ), (0 : ℤ)) - 1) * (mono ((1 : ℤ), (1 : ℤ)) - 1) : LaurentTwo ℤ)
      = mono ((1 : ℤ), (0 : ℤ)) * mono ((1 : ℤ), (1 : ℤ)) - mono ((1 : ℤ), (0 : ℤ))
        - mono ((1 : ℤ), (1 : ℤ)) + 1 := by ring
  rw [h, mono_mul_mono]
  norm_num

/-- No cancellation occurs: the support really is the four-point parallelogram. -/
theorem supp_psi3 :
    supp ((mono ((1 : ℤ), (0 : ℤ)) - 1) * (mono ((1 : ℤ), (1 : ℤ)) - 1) : LaurentTwo ℤ)
      = {((2 : ℤ), (1 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (1 : ℤ)), ((0 : ℤ), (0 : ℤ))} := by
  rw [expand_psi3]
  ext v
  simp only [mem_supp, Finset.mem_insert, Finset.mem_singleton]
  rw [show ((mono ((2 : ℤ), (1 : ℤ)) - mono ((1 : ℤ), (0 : ℤ)) - mono ((1 : ℤ), (1 : ℤ)) + 1 :
      LaurentTwo ℤ)).coeff
      = Finsupp.single ((2 : ℤ), (1 : ℤ)) 1 - Finsupp.single ((1 : ℤ), (0 : ℤ)) 1
        - Finsupp.single ((1 : ℤ), (1 : ℤ)) 1 + Finsupp.single 0 1 from rfl]
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [if_neg (fun hh => hc.1 hh.symm), if_neg (fun hh => hc.2.1 hh.symm),
      if_neg (fun hh => hc.2.2.1 hh.symm), if_neg (fun hh => hc.2.2.2 hh.symm)] at h
    simp at h
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num [Prod.ext_iff]

/-- `S_ψ` for witness B, as a set. -/
def par : Set (ℤ × ℤ) :=
  {((2 : ℤ), (1 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (1 : ℤ)), ((0 : ℤ), (0 : ℤ))}

theorem mem_par : ((0 : ℤ), (0 : ℤ)) ∈ par := by simp [par]

theorem notMem_par : ((5 : ℤ), (5 : ℤ)) ∉ par := by
  simp [par, Prod.ext_iff]

theorem coe_supp_psi3 :
    (↑(supp (∏ i ∈ Finset.univ.erase (2 : Fin 3), (mono (hw3 i) - 1 : LaurentTwo ℤ))) :
      Set (ℤ × ℤ)) = par := by
  rw [prod_hw3, supp_psi3]
  simp only [Finset.coe_insert, Finset.coe_singleton, par]

/-- **`conv(par)` has positive area**: it is a genuine lattice parallelogram, not a
segment and not a point.  So Colle's side condition on `E(·)` is met. -/
theorem posArea_par : PosArea par :=
  ⟨((0 : ℤ), (0 : ℤ)), by simp [par], ((1 : ℤ), (0 : ℤ)), by simp [par],
    ((1 : ℤ), (1 : ℤ)), by simp [par], by decide⟩

theorem mem_E_par : ((0 : ℤ), (1 : ℤ)) ∈ E par := by
  refine ⟨by decide, ?_⟩
  have hface : ∀ z ∈ par, z.2 = 1 → z ∈ face par ((0 : ℤ), (1 : ℤ)) := by
    rintro z hz hz1
    refine ⟨hz, fun y hy => ?_⟩
    rw [dot_e2, dot_e2, hz1]
    rcases hy with rfl | rfl | rfl | rfl <;> norm_num
  exact ⟨((2 : ℤ), (1 : ℤ)), hface _ (by simp [par]) rfl,
    ((1 : ℤ), (1 : ℤ)), hface _ (by simp [par]) rfl, by decide⟩

/-- **REFUTATION, positive-area version.**  Same statement as
`generatingSet_no_edge_parallel_false`, now with `m = 3` and `conv(S_ψ)` a parallelogram of
positive area (`posArea_par`), so the refutation is not an artefact of a degenerate `S_ψ`.

Instance: `h = ((1,0), (1,1), (0,1))`, `i_m = 2`, `ℓ_m = (0,1)`,
`ψ = (X^{(1,0)}-1)(X^{(1,1)}-1)`, `S_ψ = supp ψ = {(2,1),(1,0),(1,1),(0,0)}`.
`ℓ_m = (0,1) ∈ E ↑S_ψ` because the surviving period `h₁ = (1,0)` is orthogonal to `ℓ_m`,
so the parallelogram has a horizontal edge whose outer normal is exactly `(0,1)`. -/
theorem generatingSet_no_edge_parallel_false_posArea :
    ¬ (∀ (m : ℕ), 2 ≤ m → ∀ (h : Fin m → ℤ × ℤ), (∀ i, h i ≠ 0) →
        (∀ i j, i ≠ j → det (h i) (h j) ≠ 0) →
        ∀ (i_m : Fin m) (ℓ_m : ℤ × ℤ), Primitive ℓ_m →
        (∃ c : ℤ, c ≠ 0 ∧ h i_m = c • ℓ_m) →
        ∀ S_ψ : Finset (ℤ × ℤ),
          Conv S_ψ = Conv (supp (∏ i ∈ Finset.univ.erase i_m,
            (mono (h i) - 1 : LaurentTwo ℤ))) →
          ℓ_m ∉ E (↑S_ψ : Set (ℤ × ℤ)) ∧ -ℓ_m ∉ E (↑S_ψ : Set (ℤ × ℤ))) := by
  intro hall
  have := hall 3 (by norm_num) hw3 hw3_ne hw3_dir 2 ((0 : ℤ), (1 : ℤ))
    (by rw [← prim_iff_primitive]; decide)
    ⟨1, by norm_num, by simp [hw3]⟩
    (supp (∏ i ∈ Finset.univ.erase (2 : Fin 3), (mono (hw3 i) - 1 : LaurentTwo ℤ))) rfl
  rw [coe_supp_psi3] at this
  exact this.1 mem_E_par

end Nivat.LE2.Colle36Fit

/-! ## Status

### Proved here, no `sorry`, no new `axiom`

* `Nivat.LE2.face_add` — `face (A + B) n = face A n + face B n`, **unconditional**.
* `Nivat.LE2.E_add_subset` — `E (A + B) ⊆ E A ∪ E B`, **unconditional**.
* `Nivat.LE2.mem_E_add_of_mem_E_left` — the converse, pointwise, under `(face B n).Nonempty`.
* `Nivat.LE2.E_add_of_finite` — `E (A + B) = E A ∪ E B` for `A`, `B` finite and non-empty.
* `Nivat.LE2.E_add_ne` — the unrestricted equality is **false** (`A` a segment, `B` the
  quarter plane).
* `Nivat.LE2.E_segOf`, `E_zono`, `zono_no_edge_parallel` — edges of a lattice zonotope.
* `Nivat.LE2.Colle36Fit.generatingSet_no_edge_parallel_false` and
  `…_false_posArea` — `Claim36.lean`'s `generatingSet_no_edge_parallel` is **false as
  stated**, in both the degenerate and
  the positive-area regime.

### Does it discharge `generatingSet_no_edge_parallel`?  No, and it cannot

The `generatingSet_no_edge_parallel` statement in `Claim36.lean` is false (§6): it asks
for `ℓ_m ∉ E ↑S_ψ` where `ℓ_m`
is a *direction* and `E` holds *normals*.  No lemma about Minkowski sums can prove a false
statement.  The statement must first be corrected to

```
∀ n ∈ E (↑S_ψ : Set (ℤ × ℤ)), det (dir n) ℓ_m ≠ 0
```

(equivalently `dot n ℓ_m ≠ 0`, by `Nivat.LE2.det_dir`), which is Colle's "`S_ψ` has no edge
parallel to `±ℓ_m`".  **This file does not edit `Claim36.lean`; correcting it is somebody
else's call.**

### What still stands between `zono_no_edge_parallel` and the corrected Gap 1

`zono_no_edge_parallel` proves the corrected statement for the zonotope
`∑_{i ≠ i_m} segOf (h i)`.  Two bridges are still missing, and neither is a Minkowski
rule, so neither is supplied here:

1. **`supp ψ` is not the Minkowski sum of the `supp (X^{h_i} - 1)`.**  Cancellation is
   real: if `h₁ + h₂ = h₃` then the coefficient at `h₁ + h₂` in
   `(X^{h₁}-1)(X^{h₂}-1)(X^{h₃}-1)` can cancel, so `supp` of the product is a *proper*
   subset of the sum of supports.  This is exactly why `Nivat/Laurent/Ostrowski.lean:171`
   `newt_prod` is stated for the *Newton polygon* `Conv (supp ·)` over `ℂ`, where the
   leading coefficients cannot vanish, rather than for `supp` over `ℤ`.
2. **There is no `Conv S = Conv T → E ↑S = E ↑T` bridge in the tree** (0 hits; see the
   Survey section).  The hypothesis `hS_hull` of Claim 3.6's Gap 1 constrains only the
   *real* convex hull of `S_ψ`, whereas `E` is computed from the *lattice points* of
   `S_ψ`.  The missing lemma is true for finite sets — `conv (face S n) = face (Conv S) n`
   forces `(face S n).Nontrivial ↔ (face T n).Nontrivial` when `Conv S = Conv T` — but it
   is genuinely a piece of convex geometry over `ℝ`, not of lattice Minkowski theory, and
   it is **待跑** (not attempted here).

So the honest summary is: the Minkowski edge rule asked for is delivered, in a stronger
(hypothesis-free for `face`, one-inclusion-free for `E`) form than requested; it is *not*
sufficient for Gap 1, and Gap 1 as currently written is in any case false.

### Update 2026-09-14 — both bridges now exist; Gap 1 is restated and closed

Nothing above is retracted; this section records what has since been supplied elsewhere.

* Bridge 2 ("there is no `Conv S = Conv T → E ↑S = E ↑T` bridge in the tree") **is now in the
  tree**: `Nivat/External/Colle/ConvTransport.lean` `E_congr_of_Conv_eq`, written after the
  survey above was taken.  Its sharpness witness `exists_Conv_eq_face_ne` shows `Nontrivial`
  is exactly the amount of face information a hull determines.
* Bridge 1 ("`supp ψ` is not the Minkowski sum of the `supp (X^{h_i} - 1)`") is correct as
  stated — cancellation is real — but it is not an obstruction at the level of *hulls*, which
  is the level `hS_hull` works at.  `Nivat/External/Colle/NewtonZonotope.lean`
  `Conv_supp_prod_eq_Conv_zonoF` proves `Conv (supp ψ) = Conv (zonotope)` over `ℤ`, by pushing
  `ψ` along the injective ring map `ℤ → ℂ` (which preserves `supp` exactly) and applying the
  existing `Nivat.newt_prod`.  No new Ostrowski proof was needed.
* `Claim36.lean`'s `generatingSet_no_edge_parallel` was accordingly **restated** to
  `∀ n ∈ E ↑S_ψ, dot n ℓ_m ≠ 0` and **proved**, assembling
  `Conv_supp_prod_eq_Conv_zonoF`, `E_congr_of_Conv_eq` and `zono_no_edge_parallel`.  The
  refutations in §6 refer to the *old* statement and are deliberately kept: they are the
  reason the restatement was necessary, and they were re-measured
  `[propext, Classical.choice, Quot.sound]` on 2026-09-14.
-/
