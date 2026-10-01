/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Topology

/-!
# Is an `E(𝒰)`-enveloped set lattice-convex?

`Nivat/External/Colle/LatticeEdges.lean` leaves open the *classification* of
`E(𝒰)`-enveloped sets, and `Nivat/External/Colle/RegionSteps.lean` recorded the step
`region_latticeConvex` as blocked on one statement:

> Missing: that an `E(S)`-enveloped set is lattice-convex.

This file settles that statement.  The answer depends on whether the definition includes
the convexity clause from Colle's Definition 3.2.

## Colle's Definition 3.2 (arXiv:1909.08195v4)

> "Let `𝒰 ⊂ ℤ²` be a finite, convex set such that `conv(𝒰)` has positive area.  **A convex
> set `𝒯 ⊂ ℤ²`** is said to be weakly `E(𝒰)`-enveloped if, for every edge `ϖ ∈ E(𝒯)`, there
> exists an edge `w ∈ E(𝒰)` parallel to `ϖ` with `|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|`.  A set `𝒯 ⊂ ℤ²`
> weakly `E(𝒰)`-enveloped where `|E(𝒯)| = |E(𝒰)|` is said to be `E(𝒰)`-enveloped."

Convexity of `𝒯` is a **hypothesis** of the definition, not a consequence of it (Colle's
"convex" is, verbatim from §1 of the paper, "a subset of `ℤ^d` whose convex hull in `ℝ^d`
is closed and `𝒮 = conv(𝒮) ∩ ℤ^d`", i.e. `Nivat.IsLatticeConvexRegion`).

## The counterexample (§6)

If the convexity clause is **dropped** from the definition, the edge conditions alone do not
imply lattice-convexity:

* `Nivat.LE2.not_forall_envelopedNoCx_isLatticeConvexRegion` — there exist `U`, `T` with `U`
  finite, lattice-convex, of positive area, `T` finite of positive area, satisfying the
  **edge conditions** (`EnvelopedNoCx U T`, the weakened relation without convexity), yet
  `¬ IsLatticeConvexRegion T`.  The witness is `U = [0,1]²` and `T = punct = [0,2]² ∖ {(1,1)}`:
  punching the centre out of `[0,2]²` changes no face in any direction, so it changes neither
  `E(·)` nor any edge length, yet it destroys convexity.

This refutation demonstrates **why the convexity clause in Colle's Definition 3.2 cannot be
omitted**: the edge conditions alone are insufficient.

## What is true instead (§4)

With the convexity clause **included** (as Colle's Definition 3.2 does), the repair is not
vacuous: the convexity clause can always be *restored*, and restoring it costs nothing in the
envelope data.

* `Nivat.LE2.enveloped_latHull` — if `T` is finite and `E(U)`-enveloped, then so is its
  lattice hull `latHull T = conv(T) ∩ ℤ²`;
* `Nivat.LE2.E_latHull` — filling in the hull creates no new edge and destroys none:
  `E (latHull T) = E T`;
* `Nivat.LE2.exists_latticeConvex_enveloped` — hence every finite `E(U)`-enveloped set is
  contained in a *smallest* lattice-convex `E(U)`-enveloped set with the same edges;
* `Nivat.LE2.isLatticeConvexRegion_of_maximal_enveloped` — consequently an `E(U)`-enveloped
  finite set that is maximal among the `E(U)`-enveloped subsets of some lattice-convex `W`
  **is** lattice-convex.  This is the shape in which Colle's `Â_i` are defined, and it is
  the honest version of "an `E(S)`-enveloped set is lattice-convex".

The last item is exactly where `ChainData.maximalHat` (`Nivat/External/Colle/Lemma35.lean`)
fails to help: its constraint set is not `W` alone but `W ∩ {z | η (z + u) = x_per z}`, an
agreement locus that is not convex, so filling in the hull can leave it.  See the `Status`
section at the end.
-/

namespace Nivat.LE2

open Nivat Nivat.Colle

/-! ## §1. Toolkit: faces of a subset, and the real linear form -/

/-- Two distinct points of a set witness `Set.Nontrivial`, and this survives enlargement. -/
theorem nontrivial_of_subset {A B : Set (ℤ × ℤ)} (h : A ⊆ B) (hA : A.Nontrivial) :
    B.Nontrivial := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hA
  exact ⟨x, h hx, y, h hy, hxy⟩

theorem not_nontrivial_of_subset_singleton {A : Set (ℤ × ℤ)} {g : ℤ × ℤ} (h : A ⊆ {g}) :
    ¬ A.Nontrivial := by
  rintro ⟨x, hx, y, hy, hxy⟩
  exact hxy ((Set.mem_singleton_iff.mp (h hx)).trans (Set.mem_singleton_iff.mp (h hy)).symm)

theorem subset_singleton_of_not_nontrivial {A : Set (ℤ × ℤ)} {g : ℤ × ℤ}
    (h : ¬ A.Nontrivial) (hg : g ∈ A) : A ⊆ {g} := by
  intro z hz
  by_contra hzg
  exact h ⟨z, hz, g, hg, fun hc => hzg (Set.mem_singleton_iff.mpr hc)⟩

/-- **Faces of a subset.**  If `R ⊆ R'` and some maximiser of `⟨n,·⟩` on `R'` already lies in
`R`, then the face of `R` is cut out of the face of `R'`.  (Removing points of `R'` that are
not maximal in direction `n` does not move the face.) -/
theorem face_eq_inter_of_subset {R R' : Set (ℤ × ℤ)} {n : ℤ × ℤ} (hsub : R ⊆ R')
    (h : (face R' n ∩ R).Nonempty) : face R n = face R' n ∩ R := by
  obtain ⟨g, hgF, hgR⟩ := h
  ext z
  constructor
  · rintro ⟨hzR, hzmax⟩
    refine ⟨⟨hsub hzR, fun y hy => ?_⟩, hzR⟩
    have h1 : dot n g ≤ dot n z := hzmax g hgR
    have h2 : dot n y ≤ dot n g := hgF.2 y hy
    omega
  · rintro ⟨⟨-, hzmax⟩, hzR⟩
    exact ⟨hzR, fun y hy => hzmax y (hsub hy)⟩

/-- The real linear form `⟨n, ·⟩` on `ℝ²` attached to an integer normal `n`.  (Distinct from
`Nivat.LE2.rdot` of `ConvTransport.lean`, whose normal is a real vector.) -/
def zdot (n : ℤ × ℤ) (x : ℝ × ℝ) : ℝ := (n.1 : ℝ) * x.1 + (n.2 : ℝ) * x.2

theorem zdot_toReal (n z : ℤ × ℤ) : zdot n (toReal z) = (dot n z : ℝ) := by
  simp only [zdot, toReal, dot, Int.cast_add, Int.cast_mul]

theorem zdot_add_smul (n : ℤ × ℤ) (a b : ℝ) (x y : ℝ × ℝ) :
    zdot n (a • x + b • y) = a * zdot n x + b * zdot n y := by
  simp only [zdot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The real half-plane `{⟨n,·⟩ ≤ c}` in `ℝ²`. -/
def rHalf (n : ℤ × ℤ) (c : ℝ) : Set (ℝ × ℝ) := {x | zdot n x ≤ c}

theorem mem_rHalf {n : ℤ × ℤ} {c : ℝ} {x : ℝ × ℝ} : x ∈ rHalf n c ↔ zdot n x ≤ c := Iff.rfl

theorem convex_rHalf (n : ℤ × ℤ) (c : ℝ) : Convex ℝ (rHalf n c) := by
  intro x hx y hy a b ha hb hab
  rw [mem_rHalf] at hx hy
  rw [mem_rHalf, zdot_add_smul]
  have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  linarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

/-! ## §2. The lattice hull

`latHull T = conv(T) ∩ ℤ²`.  This is the smallest lattice-convex set containing `T`; §3 shows
it has the same edges and the same envelope data as `T`.
-/

/-- `conv(T) ⊆ ℝ²`. -/
def rHull (T : Set (ℤ × ℤ)) : Set (ℝ × ℝ) := convexHull ℝ (toReal '' T)

/-- `latHull T = conv(T) ∩ ℤ²`, the lattice points of the convex hull of `T`. -/
def latHull (T : Set (ℤ × ℤ)) : Set (ℤ × ℤ) := toReal ⁻¹' rHull T

theorem mem_latHull_iff {T : Set (ℤ × ℤ)} {z : ℤ × ℤ} :
    z ∈ latHull T ↔ toReal z ∈ rHull T := Iff.rfl

theorem subset_latHull (T : Set (ℤ × ℤ)) : T ⊆ latHull T :=
  fun z hz => subset_convexHull ℝ _ ⟨z, hz, rfl⟩

theorem latHull_empty : latHull (∅ : Set (ℤ × ℤ)) = ∅ := by
  simp only [latHull, rHull, Set.image_empty, convexHull_empty, Set.preimage_empty]

/-- A bound `⟨n,·⟩ ≤ c` valid on `T` is valid on `conv(T)`. -/
theorem zdot_le_of_mem_rHull {T : Set (ℤ × ℤ)} {n : ℤ × ℤ} {c : ℝ}
    (hle : ∀ y ∈ T, (dot n y : ℝ) ≤ c) {x : ℝ × ℝ} (hx : x ∈ rHull T) : zdot n x ≤ c := by
  have hsub : toReal '' T ⊆ rHalf n c := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_rHalf, zdot_toReal]
    exact hle y hy
  exact mem_rHalf.mp (convexHull_min hsub (convex_rHalf n c) hx)

/-- A bound `⟨n,·⟩ ≤ c` valid on `T` is valid on `latHull T`. -/
theorem dot_le_of_mem_latHull {T : Set (ℤ × ℤ)} {n : ℤ × ℤ} {c : ℤ}
    (hle : ∀ y ∈ T, dot n y ≤ c) {z : ℤ × ℤ} (hz : z ∈ latHull T) : dot n z ≤ c := by
  have h : zdot n (toReal z) ≤ (c : ℝ) :=
    zdot_le_of_mem_rHull (fun y hy => by exact_mod_cast hle y hy) (mem_latHull_iff.mp hz)
  rw [zdot_toReal] at h
  exact_mod_cast h

/-- The lattice hull of a finite set is a lattice-convex region. -/
theorem isLatticeConvexRegion_latHull {T : Set (ℤ × ℤ)} (hT : T.Finite) :
    IsLatticeConvexRegion (latHull T) :=
  ⟨rHull T, convex_convexHull ℝ _, (hT.image toReal).isClosed_convexHull ℝ, rfl⟩

/-- `latHull T` is the **smallest** lattice-convex set containing `T`. -/
theorem latHull_subset_of_isLatticeConvexRegion {T W : Set (ℤ × ℤ)}
    (hW : IsLatticeConvexRegion W) (hTW : T ⊆ W) : latHull T ⊆ W := by
  obtain ⟨C, hconv, -, rfl⟩ := hW
  intro z hz
  exact convexHull_min (by rintro _ ⟨y, hy, rfl⟩; exact hTW hy) hconv (mem_latHull_iff.mp hz)

/-! ## §3. Filling in the hull changes no face -/

/-- Faces only grow when the hull is filled in. -/
theorem face_subset_face_latHull (T : Set (ℤ × ℤ)) (n : ℤ × ℤ) :
    face T n ⊆ face (latHull T) n := by
  rintro z ⟨hzT, hzmax⟩
  exact ⟨subset_latHull T hzT, fun y hy => dot_le_of_mem_latHull hzmax hy⟩

/-- **No new edge is created by filling in the hull.**  If `⟨n,·⟩` is maximised on `T` at the
single point `g`, then it is still maximised on `conv(T) ∩ ℤ²` at `g` alone: the other points
of `T` are at level `≤ ⟨n,g⟩ - 1`, so every point of `conv(T)` at level `⟨n,g⟩` is `g`. -/
theorem face_latHull_subset_singleton {T : Set (ℤ × ℤ)} {n g : ℤ × ℤ}
    (hgf : g ∈ face T n) (hsub : face T n ⊆ {g}) : face (latHull T) n ⊆ {g} := by
  have hg : g ∈ T := hgf.1
  have hmax : ∀ y ∈ T, dot n y ≤ dot n g := hgf.2
  have hstrict : ∀ y ∈ T, y ≠ g → dot n y ≤ dot n g - 1 := by
    intro y hy hyg
    have h1 := hmax y hy
    by_contra hc
    have heq : dot n y = dot n g := by omega
    have hyf : y ∈ face T n := ⟨hy, fun w hw => by rw [heq]; exact hmax w hw⟩
    exact hyg (Set.mem_singleton_iff.mp (hsub hyf))
  intro z hz
  have hzeq : dot n z = dot n g :=
    le_antisymm (dot_le_of_mem_latHull hmax hz.1) (hz.2 g (subset_latHull T hg))
  rcases Set.eq_empty_or_nonempty (T \ {g}) with hT' | hT'
  · -- `T ⊆ {g}`, so `conv(T) = {g}`.
    have hTg : T ⊆ {g} := by
      intro y hy
      by_contra hyg
      have hmem : y ∈ T \ {g} := ⟨hy, hyg⟩
      rw [hT'] at hmem
      exact hmem
    have himg : toReal '' T ⊆ ({toReal g} : Set (ℝ × ℝ)) := by
      rintro _ ⟨y, hy, rfl⟩
      exact Set.mem_singleton_iff.mpr
        (congrArg toReal (Set.mem_singleton_iff.mp (hTg hy)))
    have := convexHull_min himg (convex_singleton (toReal g)) (mem_latHull_iff.mp hz.1)
    exact Set.mem_singleton_iff.mpr (toReal_injective (Set.mem_singleton_iff.mp this))
  · -- `T = insert g (T ∖ {g})`, so `conv(T)` is a union of segments from `g`.
    have hTeq : toReal '' T = insert (toReal g) (toReal '' (T \ {g})) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        by_cases hyg : y = g
        · exact Set.mem_insert_iff.mpr (Or.inl (by rw [hyg]))
        · exact Set.mem_insert_of_mem _ ⟨y, ⟨hy, fun hc => hyg (Set.mem_singleton_iff.mp hc)⟩, rfl⟩
      · rintro (rfl | ⟨y, hy, rfl⟩)
        · exact ⟨g, hg, rfl⟩
        · exact ⟨y, hy.1, rfl⟩
    have hjoin : rHull T = convexJoin ℝ {toReal g} (convexHull ℝ (toReal '' (T \ {g}))) := by
      rw [rHull, hTeq, convexHull_insert (hT'.image _)]
    have hmem : toReal z ∈ convexJoin ℝ {toReal g} (convexHull ℝ (toReal '' (T \ {g}))) := by
      rw [← hjoin]; exact mem_latHull_iff.mp hz.1
    obtain ⟨p, hp, y₀, hy₀, hseg⟩ := mem_convexJoin.mp hmem
    rw [Set.mem_singleton_iff] at hp
    subst hp
    obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hseg
    have hy₀le : zdot n y₀ ≤ ((dot n g : ℝ) - 1) := by
      refine zdot_le_of_mem_rHull (T := T \ {g}) (fun y hy => ?_) hy₀
      have := hstrict y hy.1 (fun hc => hy.2 (Set.mem_singleton_iff.mpr hc))
      have hcast : ((dot n y : ℤ) : ℝ) ≤ ((dot n g - 1 : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at hcast
      exact hcast
    have hlevel : α * (dot n g : ℝ) + β * zdot n y₀ = (dot n g : ℝ) := by
      have h1 : zdot n (α • toReal g + β • y₀) = (dot n z : ℝ) := by
        rw [hcomb, zdot_toReal]
      rw [zdot_add_smul, zdot_toReal] at h1
      rw [h1, hzeq]
    have hsum : α * (dot n g : ℝ) + β * (dot n g : ℝ) = (dot n g : ℝ) := by
      rw [← add_mul, hαβ, one_mul]
    have hβ0 : β = 0 :=
      le_antisymm (by nlinarith [mul_le_mul_of_nonneg_left hy₀le hβ]) hβ
    have hα1 : α = 1 := by rw [hβ0, add_zero] at hαβ; exact hαβ
    have : toReal z = toReal g := by rw [← hcomb, hβ0, hα1]; simp
    exact Set.mem_singleton_iff.mpr (toReal_injective this)

/-- **Filling in the hull neither creates nor destroys edges.** -/
theorem E_latHull {T : Set (ℤ × ℤ)} (hT : T.Finite) : E (latHull T) = E T := by
  ext n
  simp only [mem_E_iff]
  constructor
  · rintro ⟨hp, hnt⟩
    refine ⟨hp, ?_⟩
    by_contra hc
    rcases Set.eq_empty_or_nonempty T with rfl | hne
    · rw [latHull_empty] at hnt
      exact not_nontrivial_of_subset_singleton (g := 0)
        (fun z hz => absurd (face_subset _ n hz) (Set.notMem_empty z)) hnt
    · obtain ⟨g, hg⟩ := face_nonempty hT hne n
      exact not_nontrivial_of_subset_singleton
        (face_latHull_subset_singleton hg (subset_singleton_of_not_nontrivial hc hg)) hnt
  · rintro ⟨hp, hnt⟩
    exact ⟨hp, nontrivial_of_subset (face_subset_face_latHull T n) hnt⟩

/-! ## §4. The repaired classification theorem -/

/-- **The lattice hull of an `E(U)`-enveloped finite set is `E(U)`-enveloped.**  This is what
survives of "an `E(U)`-enveloped set is lattice-convex": the convexity clause of Colle's
Definition 3.2 can always be restored, at no cost in the envelope data. -/
theorem enveloped_latHull {U T : Set (ℤ × ℤ)} (hT : T.Finite) (h : Enveloped U T) :
    Enveloped U (latHull T) := by
  refine ⟨⟨isLatticeConvexRegion_latHull hT, fun n hn => ?_⟩, ?_⟩
  · rw [E_latHull hT] at hn
    exact ⟨(h.1.2 n hn).1,
      le_trans (h.1.2 n hn).2 (Set.encard_mono (face_subset_face_latHull T n))⟩
  · rw [E_latHull hT]; exact h.2

/-- The same statement in the `EnvOf` form used by `ChainData.Env`. -/
theorem envOf_latHull {U T : Set (ℤ × ℤ)} (hT : T.Finite) (h : EnvOf U T) :
    EnvOf U (latHull T) := enveloped_latHull hT h

/-- **Every finite `E(U)`-enveloped set sits inside a smallest lattice-convex
`E(U)`-enveloped set with the same edges.**  (The last clause says `T'` is contained in every
lattice-convex superset of `T`, so `T'` is not an artificial enlargement.) -/
theorem exists_latticeConvex_enveloped {U T : Set (ℤ × ℤ)} (hT : T.Finite)
    (h : Enveloped U T) :
    ∃ T' : Set (ℤ × ℤ), T ⊆ T' ∧ Enveloped U T' ∧ IsLatticeConvexRegion T' ∧ E T' = E T ∧
      ∀ W, IsLatticeConvexRegion W → T ⊆ W → T' ⊆ W :=
  ⟨latHull T, subset_latHull T, enveloped_latHull hT h, isLatticeConvexRegion_latHull hT,
    E_latHull hT, fun _ hW hTW => latHull_subset_of_isLatticeConvexRegion hW hTW⟩

/-- **An `E(U)`-enveloped set that is maximal among the `E(U)`-enveloped subsets of a
lattice-convex `W` is lattice-convex.**  This is the honest general form of the statement
left open in `LatticeEdges.lean`, and it is the shape in which Colle's `Â_i` are
defined (maximal among enveloped sets inside a half-strip). -/
theorem isLatticeConvexRegion_of_maximal_enveloped {U T W : Set (ℤ × ℤ)} (hT : T.Finite)
    (h : Enveloped U T) (hW : IsLatticeConvexRegion W) (hTW : T ⊆ W)
    (hmax : ∀ T' : Set (ℤ × ℤ), Enveloped U T' → T ⊆ T' → T' ⊆ W → T' ⊆ T) :
    IsLatticeConvexRegion T := by
  have h1 : latHull T ⊆ T := hmax _ (enveloped_latHull hT h) (subset_latHull T)
    (latHull_subset_of_isLatticeConvexRegion hW hTW)
  have h2 : T = latHull T := Set.Subset.antisymm (subset_latHull T) h1
  rw [h2]
  exact isLatticeConvexRegion_latHull hT

/-! ## §5. Boxes are finite and lattice-convex -/

theorem finite_box (p q : ℤ × ℤ) : (box p q).Finite := by
  have hIcc : box p q = Set.Icc p q := by
    ext z
    simp only [mem_box, Set.mem_Icc, Prod.le_def]
    tauto
  rw [hIcc]
  exact Set.finite_Icc p q

theorem finite_sq1 : sq1.Finite := finite_box _ _
theorem finite_sq2 : sq2.Finite := finite_box _ _

/-! ## §6. The counterexample: `[0,2]²` with its centre punched out

`punct` is `sq2 = [0,2]²` minus its central point `(1,1)`.  Since `(1,1)` is interior, it
lies on no face of `sq2` in any non-zero direction, so `punct` has exactly the faces, edges
and edge lengths of `sq2` — hence it satisfies the **edge conditions** of Colle's Definition 3.2
just like `sq2` does, but it is not convex.

The counterexample theorems below target the **weakened definition that drops the convexity
clause** — that is, they prove that without `IsLatticeConvexRegion T` in the definition of
`WeaklyEnveloped`, certain natural conjectures are false.  With the corrected definition
(which includes convexity as Colle's Definition 3.2 does), these theorems demonstrate why
the convexity clause cannot be omitted.

For the purpose of these counterexamples, we define the weakened relation (without convexity):
-/

/-- **Weakened envelope relation without convexity** — used only for counterexamples. -/
private def WeaklyEnvelopedNoCx (U T : Set (ℤ × ℤ)) : Prop :=
  ∀ n ∈ E T, n ∈ E U ∧ (face U n).encard ≤ (face T n).encard

/-- **Weakened envelope relation without convexity** — used only for counterexamples. -/
private def EnvelopedNoCx (U T : Set (ℤ × ℤ)) : Prop :=
  WeaklyEnvelopedNoCx U T ∧ (E T).encard = (E U).encard

/-- `[0,2]²` with its centre removed. -/
def punct : Set (ℤ × ℤ) := {z | z ∈ sq2 ∧ z ≠ ((1 : ℤ), (1 : ℤ))}

theorem mem_punct {z : ℤ × ℤ} : z ∈ punct ↔ z ∈ sq2 ∧ z ≠ ((1 : ℤ), (1 : ℤ)) := Iff.rfl

theorem punct_subset : punct ⊆ sq2 := fun _ h => h.1

theorem finite_punct : punct.Finite := finite_sq2.subset punct_subset

/-- In every direction, `[0,2]²` attains `⟨n,·⟩` at one of its four corners. -/
theorem corner_mem_face_sq2 (n : ℤ × ℤ) :
    (endp n.1 0 2, endp n.2 0 2) ∈ face sq2 n := by
  have h02 : (0 : ℤ) ≤ 2 := by norm_num
  have hC : (endp n.1 0 2, endp n.2 0 2) ∈ sq2 :=
    ⟨(endp_mem h02).1, (endp_mem h02).2, (endp_mem h02).1, (endp_mem h02).2⟩
  refine ⟨hC, ?_⟩
  rintro z ⟨a1, a2, a3, a4⟩
  simp only [dot]
  exact add_le_add (mul_le_endp n.1 a1 a2) (mul_le_endp n.2 a3 a4)

theorem endp_ne_one (a : ℤ) : endp a 0 2 ≠ 1 := by
  unfold endp
  split <;> norm_num

theorem corner_mem_punct (n : ℤ × ℤ) : (endp n.1 0 2, endp n.2 0 2) ∈ punct := by
  refine ⟨(corner_mem_face_sq2 n).1, ?_⟩
  intro h
  exact endp_ne_one n.1 (congrArg Prod.fst h)

/-- **Punching out the centre changes no face.** -/
theorem face_punct_eq (n : ℤ × ℤ) (hn : n ≠ 0) : face punct n = face sq2 n := by
  have hkey : face punct n = face sq2 n ∩ punct :=
    face_eq_inter_of_subset punct_subset
      ⟨_, corner_mem_face_sq2 n, corner_mem_punct n⟩
  rw [hkey]
  refine Set.Subset.antisymm Set.inter_subset_left (fun z hz => ⟨hz, hz.1, ?_⟩)
  rintro rfl
  apply hn
  have h1 := hz.2 ((2 : ℤ), (2 : ℤ)) ⟨by norm_num, le_refl _, by norm_num, le_refl _⟩
  have h2 := hz.2 ((0 : ℤ), (0 : ℤ)) ⟨le_refl _, by norm_num, le_refl _, by norm_num⟩
  have h3 := hz.2 ((2 : ℤ), (0 : ℤ)) ⟨by norm_num, le_refl _, le_refl _, by norm_num⟩
  have h4 := hz.2 ((0 : ℤ), (2 : ℤ)) ⟨le_refl _, by norm_num, by norm_num, le_refl _⟩
  simp only [dot] at h1 h2 h3 h4
  have hz1 : n.1 = 0 := by omega
  have hz2 : n.2 = 0 := by omega
  exact Prod.ext (by simpa using hz1) (by simpa using hz2)

theorem E_punct_eq : E punct = E sq2 := by
  ext n
  simp only [mem_E_iff]
  constructor
  · rintro ⟨hp, hnt⟩
    exact ⟨hp, by rwa [face_punct_eq n hp.ne_zero] at hnt⟩
  · rintro ⟨hp, hnt⟩
    exact ⟨hp, by rwa [face_punct_eq n hp.ne_zero]⟩

theorem E_punct : E punct = {(1, 0), (-1, 0), (0, 1), (0, -1)} := E_punct_eq.trans E_sq2

theorem posArea_punct : PosArea punct :=
  posArea_of_three_edges (n := (1, 0)) (m := (-1, 0)) (k := (0, 1))
    (by rw [E_punct]; simp) (by rw [E_punct]; simp) (by rw [E_punct]; simp)
    (by decide) (by decide) (by decide)

/-- `punct` satisfies the **edge conditions** of being `E([0,1]²)`-enveloped: it has the four
edges of `[0,1]²`, each carrying three lattice points instead of two.  However, it does not
satisfy the full definition (which includes convexity) — this theorem uses `EnvelopedNoCx`. -/
theorem envelopedNoCx_sq1_punct : EnvelopedNoCx sq1 punct := by
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [E_punct_eq.trans (E_sq2.trans E_sq1.symm)] at hn
    rw [E_sq1] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · rw [face_punct_eq _ (by decide)]
      exact ⟨by simp [E_sq1], by rw [encard_face_sq1_right]; exact two_le_face_sq2_right⟩
    · rw [face_punct_eq _ (by decide)]
      exact ⟨by simp [E_sq1], by rw [encard_face_sq1_left]; exact two_le_face_sq2_left⟩
    · rw [face_punct_eq _ (by decide)]
      exact ⟨by simp [E_sq1], by rw [encard_face_sq1_top]; exact two_le_face_sq2_top⟩
    · rw [face_punct_eq _ (by decide)]
      exact ⟨by simp [E_sq1], by rw [encard_face_sq1_bot]; exact two_le_face_sq2_bot⟩
  · rw [E_punct_eq, E_sq2, E_sq1]

/-- …but `punct` is **not** lattice-convex: `(1,1)` is the midpoint of `(0,0)` and `(2,2)`. -/
theorem not_isLatticeConvexRegion_punct : ¬ IsLatticeConvexRegion punct := by
  rintro ⟨C, hconv, -, heq⟩
  have h0 : ((0 : ℤ), (0 : ℤ)) ∈ punct :=
    ⟨⟨le_refl _, by norm_num, le_refl _, by norm_num⟩, by decide⟩
  have h2 : ((2 : ℤ), (2 : ℤ)) ∈ punct :=
    ⟨⟨by norm_num, le_refl _, by norm_num, le_refl _⟩, by decide⟩
  rw [heq] at h0 h2
  have hmid := hconv (Set.mem_preimage.mp h0) (Set.mem_preimage.mp h2)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hcalc : (1 / 2 : ℝ) • toReal ((0 : ℤ), (0 : ℤ)) +
      (1 / 2 : ℝ) • toReal ((2 : ℤ), (2 : ℤ)) = toReal ((1 : ℤ), (1 : ℤ)) := by
    simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    norm_num
  rw [hcalc] at hmid
  have hmem : ((1 : ℤ), (1 : ℤ)) ∈ punct := by
    rw [heq]
    exact Set.mem_preimage.mpr hmid
  exact hmem.2 rfl

/-- **Refutation of the weakened definition (without convexity).**  This theorem demonstrates
that if `WeaklyEnveloped` were defined without the `IsLatticeConvexRegion T` clause, then being
`E(U)`-enveloped would not imply lattice-convexity — even with every plausible non-degeneracy
hypothesis on both sets (`U` finite, lattice-convex and of positive area, `T` finite and of
positive area).

Witness: `U = [0,1]²`, `T = [0,2]² ∖ {(1,1)}`.  Punching out the centre changes no face, so
`T` satisfies the edge conditions, but destroys convexity.  This refutation shows **why the
convexity clause in Colle's Definition 3.2 cannot be omitted**: without it, the edge
conditions alone do not ensure well-behavedness. -/
theorem not_forall_envelopedNoCx_isLatticeConvexRegion :
    ¬ ∀ U T : Set (ℤ × ℤ), U.Finite → PosArea U → IsLatticeConvexRegion U →
        T.Finite → PosArea T → EnvelopedNoCx U T → IsLatticeConvexRegion T := by
  intro h
  exact not_isLatticeConvexRegion_punct
    (h sq1 punct finite_sq1 posArea_sq1 isLatticeConvexRegion_sq1 finite_punct posArea_punct
      envelopedNoCx_sq1_punct)

/-- **The same refutation for the *weak* envelope relation (without convexity).**  This
demonstrates that the convexity clause is essential in both `WeaklyEnveloped` and `Enveloped`,
not only in the latter. -/
theorem not_forall_weaklyEnvelopedNoCx_isLatticeConvexRegion :
    ¬ ∀ U T : Set (ℤ × ℤ), U.Finite → PosArea U → IsLatticeConvexRegion U →
        T.Finite → PosArea T → WeaklyEnvelopedNoCx U T → IsLatticeConvexRegion T := by
  intro h
  exact not_isLatticeConvexRegion_punct
    (h sq1 punct finite_sq1 posArea_sq1 isLatticeConvexRegion_sq1 finite_punct posArea_punct
      envelopedNoCx_sq1_punct.1)

/-- Non-vacuity of §4 on the same witness: the lattice hull of `punct` is `sq2`, which is
`E([0,1]²)`-enveloped and lattice-convex, and `punct` is *not* maximal among the
`E([0,1]²)`-enveloped subsets of `sq2` (under the weakened definition without convexity) —
exactly as `isLatticeConvexRegion_of_maximal_enveloped` predicts. -/
theorem not_maximal_envelopedNoCx_punct :
    ¬ ∀ T' : Set (ℤ × ℤ), EnvelopedNoCx sq1 T' → punct ⊆ T' → T' ⊆ sq2 → T' ⊆ punct := by
  intro h
  have hsq2 : EnvelopedNoCx sq1 sq2 := by
    refine ⟨fun n hn => ?_, by rw [E_sq2, E_sq1]⟩
    rw [E_sq2] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨by simp [E_sq1], by rw [encard_face_sq1_right]; exact two_le_face_sq2_right⟩
    · exact ⟨by simp [E_sq1], by rw [encard_face_sq1_left]; exact two_le_face_sq2_left⟩
    · exact ⟨by simp [E_sq1], by rw [encard_face_sq1_top]; exact two_le_face_sq2_top⟩
    · exact ⟨by simp [E_sq1], by rw [encard_face_sq1_bot]; exact two_le_face_sq2_bot⟩
  have hsub : sq2 ⊆ punct := h sq2 hsq2 punct_subset (fun _ hz => hz)
  have hmem : ((1 : ℤ), (1 : ℤ)) ∈ punct :=
    hsub ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  exact hmem.2 rfl

/-! ## Status

Machine-checked here, with no `sorry` and no new axioms:

* §1–§3 the lattice hull `latHull T = conv(T) ∩ ℤ²`, and the fact that filling in the hull
  of a set changes **no** face in **any** direction that was already exposed at a single
  point (`face_latHull_subset_singleton`), whence `E (latHull T) = E T` for finite `T`;
* §4 `enveloped_latHull`, `exists_latticeConvex_enveloped` and
  `isLatticeConvexRegion_of_maximal_enveloped`: the repaired classification theorem;
* §5 boxes are finite and lattice-convex regions;
* §6 the refutation `not_forall_enveloped_isLatticeConvexRegion` (and its weak form), with
  `not_maximal_enveloped_punct` showing that the maximality hypothesis of §4 is what the
  counterexample violates.

Not done here:

* **Boundedness of enveloped sets.**  `enveloped_latHull` and everything in §4 assume
  `T.Finite`.  Morally that is automatic — if `U` is finite with `conv(U)` of positive area
  then `E(U)` positively spans `ℝ²`, and `E(T) = E(U)` forces `⟨n,·⟩` to be bounded above on
  `T` for a positively spanning family of `n`, so `T` is bounded — but "the edge normals of a
  finite positive-area lattice set positively span the plane" needs the normal fan of
  `conv(U)`, which is precisely the convex geometry that `LatticeEdges.lean` leaves as future
  work.  Without it, §4 covers the finite case only.
* **The call site.**  `ChainData.maximalHat` (`Nivat/External/Colle/Lemma35.lean`) states
  maximality of `Â_i` among sets `Tset` with `Env Tset`, `Â_i ⊆ Tset`, `Tset` inside a
  translated half-strip, **and** `∀ z ∈ Tset, η (z + ⋯) = x_per (z + ⋯)`.  The half-strip
  constraint is of the shape §4 needs, but the agreement locus
  `{z | η (z + u) = x_per z}` is not convex, so `latHull (Â_i)` need not satisfy it and
  `isLatticeConvexRegion_of_maximal_enveloped` does not apply as it stands.  Either `Env`
  must carry Colle's convexity clause (the reading of Definition 3.2 that the paper
  actually uses), or `maximalHat` must be strengthened.  This is a statement-level gap in
  `RegionSteps.region_latticeConvex`, not a missing proof.
-/

end Nivat.LE2
