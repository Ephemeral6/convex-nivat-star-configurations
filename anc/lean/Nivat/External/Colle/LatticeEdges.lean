/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LowComplexityWindow

/-!
# Edges, vertices, cyclic orientation and envelopes of lattice-convex sets in `ℤ²`

Formalisation of the convex-geometry vocabulary of
Cleber F. Colle, *On periodic decompositions, one-sided nonexpansive directions and
Nivat's conjecture*, arXiv:1909.08195v4, §2.1 and §3.

This is a **base library**.  Nothing here mentions configurations, complexity or
subshifts: it is pure lattice convex geometry.  It exists because Colle's
Lemma 3.5, Claims 3.6/3.7, Lemma 4.1 and Lemma 4.5 all depend on the notions
`E(𝒮)`, `V(𝒮)`, `w ≺ w'`, `E(𝒰)`-enveloped, `H_B(ℓ)`, `St_B(ℓ)` and
`(ℓ,ℓ')`-region, none of which exist in mathlib or in this repository.

## Sign convention (READ THIS)

Colle's half plane (paper, §1, displayed formula after Definition 1.4) is
`ℋ(ℓ) = {g ∈ ℤ² : ⟨g, (-u₂, u₁)⟩ ≥ 0}` where `u` is a vector **parallel** to the
oriented line `ℓ`; so `ℓ`'s *inner* normal is `u` rotated by `+90°`, and a support
line of `𝒮` determined by `ℓ` (Definition 2.1) exposes the face on which the inner
normal is **minimised**.

This file uses the opposite, **outer-normal / maximal-face** convention
```
face R n = {z ∈ R : ∀ y ∈ R, ⟨n, y⟩ ≤ ⟨n, z⟩}
```
because that is the convention already used in this repository by
`Nivat.Colle.support_face_deficit_of_strict_deficit`
(`Nivat/External/Colle/LowComplexityGenerating.lean`, hypothesis `∀ z ∈ S, inner2 w z ≤ c`).
`Nivat/External/Colle/Lemma35.lean`'s `SupportLevel` uses the *other* (Colle's) one,
`c ≤ inner2 w z`.  The dictionary is a single sign flip, recorded here as

* `face_neg`         : `face R (-n) = {z ∈ R : ∀ y ∈ R, ⟨n,z⟩ ≤ ⟨n,y⟩}` (minimal face),
* `face_eq_of_supportLevel` : Colle's `SupportLevel w S c` (`c ≤ ⟨w,·⟩`, attained)
  identifies `face S (-w)`,
* `halfPlaneLE` / `halfPlaneGE` and `halfPlaneGE_eq_halfPlaneLE_neg`.

If `n` is the outer normal of an edge, the *positively oriented* direction vector of
that edge is `dir n = (-n₂, n₁)`, `n` rotated by `+90°` (so that the interior is on
the left, as Colle requires).

## Main definitions

* `Nivat.LE2.dot`, `Nivat.LE2.Prim` — the integer pairing and primitive vectors.
* `Nivat.LE2.face` — the exposed face with outer normal `n`; this is `w ∩ 𝒮` for the
  edge `w` with normal `n`, so `(face R n).encard` is Colle's `|w ∩ 𝒮|`.
* `Nivat.LE2.E`, `Nivat.LE2.V` — the edge normals `E(𝒮)` and the vertices `V(𝒮)`
  (Colle, §2.1).
* `Nivat.LE2.angLT`, `Nivat.LE2.IsSuccEdge` — the counter-clockwise cyclic order on
  edges and Colle's `w_p ≺ w` (§2.1).
* `Nivat.LE2.WeaklyEnveloped`, `Nivat.LE2.Enveloped` — Colle, Definition 3.2.
* `Nivat.LE2.halfStrip`, `Nivat.LE2.strip` — `H_B(ℓ)` and `St_B(ℓ)`, Definition 3.4.
* `Nivat.LE2.IsRegion` — Colle, Definition 3.1, `(ℓ,ℓ')`-regions.

## Status

See the `Status` section at the end of the file for the exact list of what is
proved and what is not.
-/

namespace Nivat.LE2

open Nivat Nivat.Colle

/-! ## §1. The integer pairing and primitive vectors -/

/-- The integer pairing `⟨n, z⟩ = n₁z₁ + n₂z₂`. -/
def dot (n z : ℤ × ℤ) : ℤ := n.1 * z.1 + n.2 * z.2

theorem dot_comm (n z : ℤ × ℤ) : dot n z = dot z n := by simp only [dot]; ring

theorem dot_add (n z w : ℤ × ℤ) : dot n (z + w) = dot n z + dot n w := by
  simp only [dot, Prod.fst_add, Prod.snd_add]; ring

theorem dot_sub (n z w : ℤ × ℤ) : dot n (z - w) = dot n z - dot n w := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring

theorem dot_neg_left (n z : ℤ × ℤ) : dot (-n) z = -dot n z := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

@[simp] theorem dot_zero_left (z : ℤ × ℤ) : dot 0 z = 0 := by simp [dot]

/-- The bridge to the real linear form `inner2` used elsewhere in the repository. -/
theorem inner2_toReal (n z : ℤ × ℤ) : inner2 (toReal n) z = (dot n z : ℝ) := by
  simp only [inner2, toReal, dot, Int.cast_add, Int.cast_mul]
  ring

/-- A lattice vector is *primitive* if its coordinates are coprime. -/
def Prim (n : ℤ × ℤ) : Prop := Int.gcd n.1 n.2 = 1

instance (n : ℤ × ℤ) : Decidable (Prim n) :=
  inferInstanceAs (Decidable (Int.gcd n.1 n.2 = 1))

theorem prim_iff_primitive {n : ℤ × ℤ} : Prim n ↔ Primitive n :=
  Int.isCoprime_iff_gcd_eq_one.symm

theorem Prim.ne_zero {n : ℤ × ℤ} (h : Prim n) : n ≠ 0 := by
  intro h0
  rw [h0] at h
  simp [Prim] at h

theorem Prim.neg {n : ℤ × ℤ} (h : Prim n) : Prim (-n) := by
  simpa [Prim, Int.gcd] using h

/-- Two lattice vectors orthogonal to one and the same non-zero vector are parallel. -/
theorem det_eq_zero_of_dot_eq_zero {n u v : ℤ × ℤ} (hn : n ≠ 0)
    (hu : dot n u = 0) (hv : dot n v = 0) : det u v = 0 := by
  simp only [dot] at hu hv
  have h1 : det u v * n.1 = 0 := by simp only [det]; linear_combination v.2 * hu - u.2 * hv
  have h2 : det u v * n.2 = 0 := by simp only [det]; linear_combination u.1 * hv - v.1 * hu
  rcases mul_eq_zero.mp h1 with h | h
  · exact h
  · rcases mul_eq_zero.mp h2 with h' | h'
    · exact h'
    · exact absurd (show n = (0 : ℤ × ℤ) by simp [Prod.ext_iff, h, h']) hn

/-- A lattice vector parallel to a primitive vector is an integer multiple of it. -/
theorem exists_smul_of_det_eq_zero {n m : ℤ × ℤ} (hn : Prim n) (h : det n m = 0) :
    ∃ a : ℤ, m = (a * n.1, a * n.2) := by
  obtain ⟨x, y, hxy⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hn
  simp only [det] at h
  refine ⟨x * m.1 + y * m.2, Prod.ext ?_ ?_⟩
  · show m.1 = (x * m.1 + y * m.2) * n.1
    linear_combination (-m.1) * hxy - y * h
  · show m.2 = (x * m.1 + y * m.2) * n.2
    linear_combination (-m.2) * hxy + x * h

/-- Two parallel primitive vectors are equal or opposite. -/
theorem eq_or_neg_of_prim_of_det_eq_zero {n m : ℤ × ℤ} (hn : Prim n) (hm : Prim m)
    (h : det n m = 0) : m = n ∨ m = -n := by
  obtain ⟨a, ha⟩ := exists_smul_of_det_eq_zero hn h
  have hgcd : a.natAbs * Int.gcd n.1 n.2 = 1 := by
    have : Int.gcd m.1 m.2 = a.natAbs * Int.gcd n.1 n.2 := by
      rw [ha]; exact Int.gcd_mul_left a n.1 n.2
    rw [← this]; exact hm
  rw [hn, mul_one] at hgcd
  rcases Int.natAbs_eq_iff.mp hgcd with h1 | h1
  · left; rw [ha, h1]; simp
  · right; rw [ha, h1]; simp [Prod.ext_iff]

/-! ## §2. Faces, edges and vertices

Colle, §2.1: *"A point `g ∈ 𝒮` is called a vertex of `𝒮` when `𝒮 \ {g}` is still a
convex set.  If `conv(𝒮)` has positive area, an edge of the convex polygon `conv(𝒮)`
is called an edge of `𝒮`."*

An edge of `conv(𝒮)` for `𝒮 ⊆ ℤ²` always has rational direction, hence a **primitive
integer outer normal**, which determines it.  So we index edges by their primitive
outer normals; the edge itself, as a set of lattice points (Colle's `w ∩ 𝒮`), is the
exposed face `face 𝒮 n`.  This is a definition, not an assumption: everything below
unfolds to arithmetic in `ℤ`.
-/

/-- The exposed face of `R` in the direction of the **outer** normal `n`.  For an edge
normal `n` this is exactly Colle's `w ∩ R`. -/
def face (R : Set (ℤ × ℤ)) (n : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {z | z ∈ R ∧ ∀ y ∈ R, dot n y ≤ dot n z}

theorem mem_face_iff {R : Set (ℤ × ℤ)} {n z : ℤ × ℤ} :
    z ∈ face R n ↔ z ∈ R ∧ ∀ y ∈ R, dot n y ≤ dot n z := Iff.rfl

theorem face_subset (R : Set (ℤ × ℤ)) (n : ℤ × ℤ) : face R n ⊆ R := fun _ h => h.1

/-- The minimal-face description of `face R (-n)`: this is the sign dictionary between
this file's convention and Colle's. -/
theorem face_neg (R : Set (ℤ × ℤ)) (n : ℤ × ℤ) :
    face R (-n) = {z | z ∈ R ∧ ∀ y ∈ R, dot n z ≤ dot n y} := by
  ext z
  simp only [mem_face_iff, dot_neg_left, neg_le_neg_iff, Set.mem_ofPred_eq]

/-- All points of a face have the same pairing with the normal. -/
theorem dot_eq_of_mem_face {R : Set (ℤ × ℤ)} {n a b : ℤ × ℤ}
    (ha : a ∈ face R n) (hb : b ∈ face R n) : dot n a = dot n b :=
  le_antisymm (hb.2 a ha.1) (ha.2 b hb.1)

/-- If `c` is a support level for `R` with outer normal `n` (i.e. `⟨n,·⟩ ≤ c` on `R`,
with equality somewhere), then the face is cut out by `⟨n,·⟩ = c`. -/
theorem face_eq_of_support {R : Set (ℤ × ℤ)} {n : ℤ × ℤ} {c : ℤ}
    (hle : ∀ z ∈ R, dot n z ≤ c) (hmem : ∃ z ∈ R, dot n z = c) :
    face R n = {z | z ∈ R ∧ dot n z = c} := by
  obtain ⟨z₀, hz₀R, hz₀⟩ := hmem
  ext z
  constructor
  · rintro ⟨hzR, hz⟩
    refine ⟨hzR, le_antisymm (hle z hzR) ?_⟩
    rw [← hz₀]; exact hz z₀ hz₀R
  · rintro ⟨hzR, hz⟩
    refine ⟨hzR, fun y hy => ?_⟩
    rw [hz]; exact hle y hy

/-- Colle's `SupportLevel` (the minimal-face convention of `Lemma35.lean`, transcribed)
picks out the face with outer normal `-n`. -/
theorem face_eq_of_supportLevel {R : Set (ℤ × ℤ)} {n : ℤ × ℤ} {c : ℤ}
    (hge : ∀ z ∈ R, c ≤ dot n z) (hmem : ∃ z ∈ R, dot n z = c) :
    face R (-n) = {z | z ∈ R ∧ dot n z = c} := by
  obtain ⟨z₀, hz₀R, hz₀⟩ := hmem
  rw [face_neg]
  ext z
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hzR, hz⟩
    refine ⟨hzR, le_antisymm ?_ (hge z hzR)⟩
    rw [← hz₀]; exact hz z₀ hz₀R
  · rintro ⟨hzR, hz⟩
    refine ⟨hzR, fun y hy => ?_⟩
    rw [hz]; exact hge y hy

/-- `n` is an **edge normal** of `R` if it is primitive and its exposed face contains
at least two lattice points.  `E R` is Colle's `E(R)`. -/
def IsEdge (R : Set (ℤ × ℤ)) (n : ℤ × ℤ) : Prop := Prim n ∧ (face R n).Nontrivial

/-- `E(R)`, the set of edges of `R`, indexed by primitive outer normals. -/
def E (R : Set (ℤ × ℤ)) : Set (ℤ × ℤ) := {n | IsEdge R n}

theorem mem_E_iff {R : Set (ℤ × ℤ)} {n : ℤ × ℤ} :
    n ∈ E R ↔ Prim n ∧ (face R n).Nontrivial := Iff.rfl

/-- `g` is a **vertex** of `R` if some primitive direction exposes exactly `g`.
(Colle's `V(R)`; `vertex_erase` below shows this implies Colle's own formulation.) -/
def IsVtx (R : Set (ℤ × ℤ)) (g : ℤ × ℤ) : Prop := ∃ n, Prim n ∧ face R n = {g}

/-- `V(R)`, the set of vertices of `R`. -/
def V (R : Set (ℤ × ℤ)) : Set (ℤ × ℤ) := {g | IsVtx R g}

theorem V_subset (R : Set (ℤ × ℤ)) : V R ⊆ R := by
  rintro g ⟨n, -, hn⟩
  have : g ∈ face R n := by rw [hn]; rfl
  exact this.1

/-- `conv(R)` has positive area. -/
def PosArea (R : Set (ℤ × ℤ)) : Prop :=
  ∃ a ∈ R, ∃ b ∈ R, ∃ c ∈ R, det (b - a) (c - a) ≠ 0

/-- A set on which some non-zero linear form is constant has zero area. -/
theorem not_posArea_of_dot_const {R : Set (ℤ × ℤ)} {n : ℤ × ℤ} (hn : n ≠ 0)
    (h : ∀ y ∈ R, ∀ z ∈ R, dot n y = dot n z) : ¬ PosArea R := by
  rintro ⟨a, ha, b, hb, c, hc, hdet⟩
  exact hdet (det_eq_zero_of_dot_eq_zero hn
    (by rw [dot_sub, h b hb a ha, sub_self]) (by rw [dot_sub, h c hc a ha, sub_self]))

/-- The oriented direction vector of the edge with outer normal `n`: `n` rotated by
`+90°`, so the interior of `R` lies on its left, as Colle's orientation convention
requires. -/
def dir (n : ℤ × ℤ) : ℤ × ℤ := (-n.2, n.1)

theorem dot_dir (n : ℤ × ℤ) : dot n (dir n) = 0 := by simp only [dot, dir]; ring

/-- **Pairing a normal against another edge's direction is (minus) the determinant.**
The general form of `dot_dir` above, which is the case `a = b`.

This is what converts a *half-plane* statement about `Â_∞` into an *orientation*
statement about the fan of `𝒮_φ`.  Concretely, with `ν_J = -nJ` the outer normal of
`Â_∞`'s `ℓ_J`-edge (`nJ` is the **inner** normal, by
`hhp : hatOf A kk vl i ⊆ halfPlaneGE nJ cJ`, `ofPartsExhaustsInter`'s binder,
`ChainExhaustInter.lean`) and
`w = -(dir ν_{J+1})` the sweep vector of `exists_w_hsweepW`, it turns
`hsweepW : dot nJ w < 0` (same binder table, `ChainExhaustInter.lean`) into
`0 < det ν_J ν_{J+1}`.
⚠ Calling that "the successor relation of `scratch/b3_colle2.txt:424`" is **our** reading, not
the source's: `:424` enumerates the edges of `𝒮_φ` cyclically and never mentions `Â_∞`, `nJ`
or `w`.  What is on-chain is the binder `hsweepW` itself; the det-sign form below is an
equivalent repackaging of that binder and of nothing else.
See `dot_neg_dir_neg_lt_iff` below for that equivalence, packaged. -/
theorem dot_dir_eq_neg_det (a b : ℤ × ℤ) : dot a (dir b) = - det a b := by
  simp only [dot, dir, det]; ring

/-- **The Plücker relation for three normals, rotated by 90°.**

No hypotheses, pure algebra: for any `a b c : ℤ × ℤ`,

    (det a b) • (-(dir c)) = (det a c) • (-(dir b)) + (det b c) • (dir a)

Substituting `a = ν_{J-1}`, `b = ν_J`, `c = ν_{J+1}` gives **`e • w = D • u + d • v_{J-1}`**,
where `e = det ν_{J-1} ν_J`, `d = det ν_J ν_{J+1}`, `D = det ν_{J-1} ν_{J+1}`, and
`w = -(dir ν_{J+1})`, `u = -(dir ν_J)`, `v_{J-1} = dir ν_{J-1}` (`blueprint/NOTATION.md`).

⚠ **This is the correct general form of the `w = u + c • v_{J-1}` that was in use.**  That
shape is equivalent to `D = e` — not to `e ∣ d`, not to `e = 1`.  Both standing rigs happen
to have `D = e = 1`, so the gap is invisible on them.

⚠ **`D` is a two-step determinant and is NOT derivable from the binder table.**
`hsweep` / `hsweepW` (both binders of `ofPartsExhaustsInter`, `ChainExhaustInter.lean`)
give only the two *adjacent*
positivities `0 < e` and `0 < d`, and two adjacent counterclockwise turns can sum past a
half turn.  Kernel-refuted, not merely unproven: writing `ν_{J+1} = α • ν_{J-1} + β • ν_J`
in the basis `{ν_{J-1}, ν_J}` (a basis because `0 < e`), one gets `d = -α * e` and
`D = β * e`, so `hsweepW` pins only `α < 0` and leaves `sign β = sign D` entirely free.
Witness `ν_{J-1} = (1,0)`, `ν_J = (0,1)`, `ν_{J+1} = (-1,-1)`: both adjacent steps turn
counterclockwise (90° then 135°), yet `D = -1 < 0`.  Adding half-plane hypotheses at both
ends does not rescue it either (`nℓ = (-2,-1)` satisfies both and still gives `D = -1`).
The source-side window that *would* supply a sign is the range `ι+1 ≤ J ≤ ι+m-1` at
`scratch/b3_colle2.txt:432`, whose selection criterion (`:424`'s cyclic enumeration plus
`:498`'s minimality) is not yet transcribed.  Any use of `D`'s sign must carry it as an
explicit hypothesis.

Adjacent identity: `dot_dir_eq_neg_det` above. -/
theorem plucker_dir (a b c : ℤ × ℤ) :
    (det a b) • (-(dir c)) = (det a c) • (-(dir b)) + (det b c) • (dir a) := by
  simp only [Prod.ext_iff, det, dir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_neg, Prod.snd_neg, smul_eq_mul]
  constructor <;> ring

/-- **`hsweepW` repackaged as a determinant sign.**

Read `nu` as `ν_J`, the outer normal of `Â_∞`'s `ℓ_J`-edge, and `nu'` as `ν_{J+1}`.
The left-hand side is `dot nJ w < 0` with `nJ = -ν_J` and `w = -(dir ν_{J+1})`;
the right-hand side is the same fact written as a determinant sign.

⚠ **Retracted 2026-09-24 (集成者):** the previous docstring called the right-hand side "the
successor relation of `scratch/b3_colle2.txt:424`" and said it means `ℓ_{J+1}` is the
*counterclockwise successor* of `ℓ_J`.  Source `:424` says no such thing about `Â_∞` — it
enumerates the edges of `𝒮_φ` cyclically, and mentions neither `nJ` nor `w`.  The on-chain
content here is exactly the binder `hsweepW` (`ChainExhaustInter.lean`); "counterclockwise"
is our name for the det sign, definitional, and carries no source claim.

Both quantifiers are universal over `ℤ × ℤ`; nothing is assumed about the fan. -/
theorem dot_neg_dir_neg_lt_iff (nu nu' : ℤ × ℤ) :
    dot (-nu) (-(dir nu')) < 0 ↔ 0 < det nu nu' := by
  have h : dot (-nu) (-(dir nu')) = - det nu nu' := by
    simp only [dot, dir, det, Prod.fst_neg, Prod.snd_neg]; ring
  rw [h]; omega

/-- Two distinct points of one face differ by a vector parallel to `dir n`. -/
theorem dot_sub_eq_zero_of_mem_face {R : Set (ℤ × ℤ)} {n a b : ℤ × ℤ}
    (ha : a ∈ face R n) (hb : b ∈ face R n) : dot n (b - a) = 0 := by
  rw [dot_sub, dot_eq_of_mem_face hb ha, sub_self]

/-- **An edge determines its normal.**  On a set of positive area, distinct primitive
outer normals expose distinct faces. -/
theorem injOn_face {R : Set (ℤ × ℤ)} (hR : PosArea R) : Set.InjOn (face R) (E R) := by
  rintro n ⟨hnp, hn2⟩ m ⟨hmp, -⟩ hfe
  obtain ⟨a, ha, b, hb, hab⟩ := hn2
  have hd : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hn0 : dot (b - a) n = 0 := by
    rw [← dot_comm]; exact dot_sub_eq_zero_of_mem_face ha hb
  have hm0 : dot (b - a) m = 0 := by
    rw [← dot_comm]
    exact dot_sub_eq_zero_of_mem_face (hfe ▸ ha) (hfe ▸ hb)
  have hdet : det n m = 0 := det_eq_zero_of_dot_eq_zero hd hn0 hm0
  rcases eq_or_neg_of_prim_of_det_eq_zero hnp hmp hdet with rfl | rfl
  · rfl
  · exfalso
    have ha' : a ∈ face R (-n) := hfe ▸ ha
    rw [face_neg] at ha'
    simp only [Set.mem_ofPred_eq] at ha'
    refine not_posArea_of_dot_const hnp.ne_zero ?_ hR
    intro y hy z hz
    have h1 := ha.2 y hy
    have h2 := ha'.2 y hy
    have h3 := ha.2 z hz
    have h4 := ha'.2 z hz
    omega

/-! ## §3. Finiteness of the edge set, and faces of finite sets -/

/-- **`|E(𝒮)| < ∞`.**  A finite set of positive area has finitely many edges.  This is
Colle's standing hypothesis "`|E(𝒮)| < ∞`" (§2.1), proved rather than assumed. -/
theorem finite_E {R : Set (ℤ × ℤ)} (hfin : R.Finite) (hR : PosArea R) : (E R).Finite := by
  refine Set.Finite.of_finite_image ?_ (injOn_face hR)
  refine Set.Finite.subset hfin.finite_subsets ?_
  rintro _ ⟨n, -, rfl⟩
  exact face_subset R n

/-- The set of primitive vectors orthogonal to a fixed non-zero vector has at most two
elements: `n` and `-n` for any one witness `n`.  Pure linear algebra, no convexity. -/
theorem finite_prim_orthogonal {d : ℤ × ℤ} (hd : d ≠ 0) :
    {n : ℤ × ℤ | Prim n ∧ dot n d = 0}.Finite := by
  classical
  rcases Set.eq_empty_or_nonempty {n : ℤ × ℤ | Prim n ∧ dot n d = 0} with he | ⟨n₀, hn₀⟩
  · rw [he]; exact Set.finite_empty
  · refine Set.Finite.subset (Set.Finite.insert n₀ (Set.finite_singleton (-n₀))) ?_
    intro m hm
    have hdet : det n₀ m = 0 :=
      det_eq_zero_of_dot_eq_zero hd (by rw [dot_comm]; exact hn₀.2) (by rw [dot_comm]; exact hm.2)
    rcases eq_or_neg_of_prim_of_det_eq_zero hn₀.1 hm.1 hdet with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl h)
    · exact Set.mem_insert_iff.mpr (Or.inr (by simp [h]))

/-- **`|E(R)| < ∞` for any finite `R`, with no `PosArea` hypothesis.**  Unlike `finite_E`,
this covers degenerate (collinear or empty) `R` too: every edge normal `n ∈ E R` is
witnessed by some pair of distinct points `a, b` of the (finite) face, and is then one of
at most two primitive vectors orthogonal to `b - a`; ranging over the finitely many
differences of pairs of points of `R` gives a finite cover.

This is what lets a caller discharge an `E`-equality obligation for an arbitrary finite
index set `S` — in particular `RegionSteps.region_latticeConvex`, where `S : Finset (ℤ × ℤ)`
carries no positive-area guarantee. -/
theorem finite_E_of_finite {R : Set (ℤ × ℤ)} (hfin : R.Finite) : (E R).Finite := by
  classical
  set Diffs : Set (ℤ × ℤ) :=
      {d : ℤ × ℤ | ∃ a ∈ R, ∃ b ∈ R, d = b - a ∧ d ≠ 0} with hDiffsDef
  have hDiffsFin : Diffs.Finite := by
    have hsub : Diffs ⊆ (fun p : (ℤ × ℤ) × (ℤ × ℤ) => p.2 - p.1) '' (R ×ˢ R) := by
      rintro d ⟨a, ha, b, hb, rfl, -⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    exact Set.Finite.subset ((hfin.prod hfin).image _) hsub
  have hE_subset :
      E R ⊆ ⋃ d ∈ Diffs, {n : ℤ × ℤ | Prim n ∧ dot n d = 0} := by
    intro n hn
    obtain ⟨hnp, a, ha, b, hb, hab⟩ := hn
    have hd0 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have hd : dot n (b - a) = 0 := dot_sub_eq_zero_of_mem_face ha hb
    exact Set.mem_biUnion ⟨a, ha.1, b, hb.1, rfl, hd0⟩ ⟨hnp, hd⟩
  refine Set.Finite.subset (Set.Finite.biUnion hDiffsFin ?_) hE_subset
  intro d hd
  obtain ⟨a, ha, b, hb, hdeq, hdne⟩ := hd
  exact finite_prim_orthogonal hdne

/-- A non-empty finite set has a non-empty face in every direction. -/
theorem face_nonempty {R : Set (ℤ × ℤ)} (hfin : R.Finite) (hne : R.Nonempty) (n : ℤ × ℤ) :
    (face R n).Nonempty := by
  classical
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image hfin.toFinset (dot n)
    (by rwa [Set.Finite.toFinset_nonempty])
  exact ⟨b, hfin.mem_toFinset.mp hb, fun y hy => hmax y (hfin.mem_toFinset.mpr hy)⟩

/-! ## §4. Vertices: the bridge to Colle's own formulation

Colle defines a vertex of a convex `𝒮 ⊆ ℤ²` to be a `g ∈ 𝒮` with `𝒮 \ {g}` still
lattice-convex.  We show the exposed vertices of §2 satisfy this. -/

/-- Colle's own formulation of "vertex of `𝒮`" (§2.1). -/
def IsColleVertex (S : Finset (ℤ × ℤ)) (g : ℤ × ℤ) : Prop :=
  g ∈ S ∧ LatticeConvex (S.erase g)

/-- If `n` exposes exactly `g`, then deleting `g` is cutting by a strict half-plane. -/
theorem erase_eq_filter_of_face_eq_singleton {S : Finset (ℤ × ℤ)} {n g : ℤ × ℤ}
    (h : face (↑S : Set (ℤ × ℤ)) n = {g}) :
    S.erase g = S.filter (fun z => inner2 (toReal n) z < ((dot n g : ℤ) : ℝ)) := by
  classical
  have hg : g ∈ face (↑S : Set (ℤ × ℤ)) n := by rw [h]; rfl
  ext z
  simp only [Finset.mem_erase, Finset.mem_filter, inner2_toReal, Int.cast_lt]
  constructor
  · rintro ⟨hzg, hzS⟩
    refine ⟨hzS, ?_⟩
    have h1 : dot n z ≤ dot n g := hg.2 z (Finset.mem_coe.mpr hzS)
    rcases lt_or_eq_of_le h1 with h2 | h2
    · exact h2
    · exfalso
      apply hzg
      have hzf : z ∈ face (↑S : Set (ℤ × ℤ)) n :=
        ⟨Finset.mem_coe.mpr hzS, fun y hy => by rw [h2]; exact hg.2 y hy⟩
      rw [h] at hzf
      exact hzf
  · rintro ⟨hzS, hlt⟩
    exact ⟨by rintro rfl; exact absurd hlt (lt_irrefl _), hzS⟩

/-- **An exposed vertex is a vertex in Colle's sense.**  This is the point of contact
between the two definitions in §2.1. -/
theorem isColleVertex_of_isVtx {S : Finset (ℤ × ℤ)} (hS : LatticeConvex S) {g : ℤ × ℤ}
    (hg : IsVtx (↑S : Set (ℤ × ℤ)) g) : IsColleVertex S g := by
  classical
  obtain ⟨n, -, hn⟩ := hg
  have hgS : g ∈ S := by
    have : g ∈ face (↑S : Set (ℤ × ℤ)) n := by rw [hn]; rfl
    exact Finset.mem_coe.mp this.1
  refine ⟨hgS, ?_⟩
  rw [erase_eq_filter_of_face_eq_singleton hn]
  exact latticeConvex_filter_inner2_lt hS (toReal n) ((dot n g : ℤ) : ℝ)

/-! ## §5. The counter-clockwise cyclic order on edges

Colle, §2.1: *"our standard convention is that the boundary of `conv(𝒮)` is positively
oriented … If `|E(𝒮)| < ∞`, our convention endows each `w ∈ E(𝒮)` with a well-defined
successor edge `w_s` and a well-defined predecessor edge `w_p`.  We use `w_p ≺ w` …"*

The positively oriented boundary visits the edges in increasing order of the angle of
their **outer** normal, so we order primitive vectors by angle measured
counter-clockwise from the positive `x`-axis. -/

/-- `0` for directions with angle in `[0, π)`, `1` for angle in `[π, 2π)`. -/
def half (a : ℤ × ℤ) : ℕ := if 0 < a.2 ∨ (a.2 = 0 ∧ 0 < a.1) then 0 else 1

/-- The within-half key: `-a₁/a₂`, which increases with the angle on each half, with `⊥`
for the two horizontal directions (angles `0` and `π`), which start their halves. -/
noncomputable def angSlope (a : ℤ × ℤ) : WithBot ℚ :=
  if a.2 = 0 then (⊥ : WithBot ℚ) else ((-(a.1 : ℚ) / (a.2 : ℚ) : ℚ) : WithBot ℚ)

/-- The angular key of a direction: a point of a linear order that increases with the
counter-clockwise angle measured from the positive `x`-axis. -/
noncomputable def angKey (a : ℤ × ℤ) : Lex (ℕ × WithBot ℚ) := toLex (half a, angSlope a)

/-- `a` comes strictly before `b` in the counter-clockwise order starting at the positive
`x`-axis. -/
def angLT (a b : ℤ × ℤ) : Prop := angKey a < angKey b

theorem angLT_iff {a b : ℤ × ℤ} :
    angLT a b ↔ half a < half b ∨ (half a = half b ∧ angSlope a < angSlope b) :=
  Prod.Lex.lt_iff

theorem angLT_irrefl (a : ℤ × ℤ) : ¬ angLT a a := lt_irrefl _

theorem angLT_trans {a b c : ℤ × ℤ} : angLT a b → angLT b c → angLT a c := lt_trans

theorem angLT_asymm {a b : ℤ × ℤ} (h : angLT a b) : ¬ angLT b a :=
  fun h' => angLT_irrefl a (angLT_trans h h')

/-- A vector and its negative lie in opposite halves. -/
theorem half_neg_ne {a : ℤ × ℤ} (h : a ≠ 0) : half a ≠ half (-a) := by
  have h' : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (Prod.ext hc.1 hc.2)
  simp only [half, Prod.fst_neg, Prod.snd_neg]
  rcases lt_trichotomy a.2 0 with h2 | h2 | h2
  · rw [if_neg (by omega), if_pos (by omega)]; omega
  · have h1 : a.1 ≠ 0 := by rcases h' with h'' | h''; exacts [h'', absurd h2 h'']
    rcases lt_trichotomy a.1 0 with h3 | h3 | h3
    · rw [if_neg (by omega), if_pos (by omega)]; omega
    · exact absurd h3 h1
    · rw [if_pos (by omega), if_neg (by omega)]; omega
  · rw [if_pos (by omega), if_neg (by omega)]; omega

/-- A primitive vector with zero second coordinate is `(1,0)` or `(-1,0)`. -/
theorem prim_eq_of_snd_eq_zero {n : ℤ × ℤ} (hp : Prim n) (h : n.2 = 0) :
    n = (1, 0) ∨ n = (-1, 0) := by
  have : n.1.natAbs = 1 := by
    have := hp; rw [Prim, h] at this; simpa using this
  rcases Int.natAbs_eq_iff.mp this with h1 | h1
  · left; exact Prod.ext (by simpa using h1) (by simpa using h)
  · right; exact Prod.ext (by simpa using h1) (by simpa using h)

/-- A primitive vector with zero first coordinate is `(0,1)` or `(0,-1)`. -/
theorem prim_eq_of_fst_eq_zero {n : ℤ × ℤ} (hp : Prim n) (h : n.1 = 0) :
    n = (0, 1) ∨ n = (0, -1) := by
  have : n.2.natAbs = 1 := by
    have := hp; rw [Prim, h] at this; simpa using this
  rcases Int.natAbs_eq_iff.mp this with h1 | h1
  · left; exact Prod.ext (by simpa using h) (by simpa using h1)
  · right; exact Prod.ext (by simpa using h) (by simpa using h1)

/-- A primitive vector with equal coordinates is `(1,1)` or `(-1,-1)`. -/
theorem prim_eq_of_coord_eq {n : ℤ × ℤ} (hp : Prim n) (h : n.1 = n.2) :
    n = (1, 1) ∨ n = (-1, -1) := by
  have : n.1.natAbs = 1 := by
    have := hp; rw [Prim, ← h] at this; simpa using this
  rcases Int.natAbs_eq_iff.mp this with h1 | h1
  · left; exact Prod.ext (by simpa using h1) (by rw [← h]; simpa using h1)
  · right; exact Prod.ext (by simpa using h1) (by rw [← h]; simpa using h1)

/-- **The angular key separates directions.**  Two primitive vectors with the same
angular key are equal. -/
theorem angKey_injOn_prim {a b : ℤ × ℤ} (ha : Prim a) (hb : Prim b)
    (h : angKey a = angKey b) : a = b := by
  have h' := congrArg ofLex h
  simp only [angKey, ofLex_toLex, Prod.mk.injEq] at h'
  obtain ⟨hh, hs⟩ := h'
  by_cases ha2 : a.2 = 0
  · by_cases hb2 : b.2 = 0
    · rcases prim_eq_of_snd_eq_zero ha ha2 with rfl | rfl <;>
        rcases prim_eq_of_snd_eq_zero hb hb2 with rfl | rfl <;>
        simp_all [half]
    · exfalso
      rw [angSlope, angSlope, if_pos ha2, if_neg hb2] at hs
      exact (WithBot.bot_ne_coe hs).elim
  · by_cases hb2 : b.2 = 0
    · exfalso
      rw [angSlope, angSlope, if_neg ha2, if_pos hb2] at hs
      exact (WithBot.bot_ne_coe hs.symm).elim
    · rw [angSlope, angSlope, if_neg ha2, if_neg hb2] at hs
      have hq : (-(a.1 : ℚ)) / (a.2 : ℚ) = (-(b.1 : ℚ)) / (b.2 : ℚ) :=
        WithBot.coe_injective hs
      have ha2' : (a.2 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha2
      have hb2' : (b.2 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb2
      have hcross : (-(a.1 : ℚ)) * (b.2 : ℚ) = (-(b.1 : ℚ)) * (a.2 : ℚ) :=
        (div_eq_div_iff ha2' hb2').mp hq
      have hZ : (a.1 : ℚ) * (b.2 : ℚ) = (b.1 : ℚ) * (a.2 : ℚ) := by linear_combination -hcross
      have hZ' : a.1 * b.2 = b.1 * a.2 := by exact_mod_cast hZ
      have hdet : det a b = 0 := by simp only [det]; linear_combination hZ'
      rcases eq_or_neg_of_prim_of_det_eq_zero ha hb hdet with rfl | rfl
      · rfl
      · exact absurd hh (half_neg_ne ha.ne_zero)

/-- **Trichotomy.**  The angular order is total on primitive vectors. -/
theorem angLT_trichotomy {a b : ℤ × ℤ} (ha : Prim a) (hb : Prim b) :
    angLT a b ∨ a = b ∨ angLT b a := by
  rcases lt_trichotomy (angKey a) (angKey b) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (angKey_injOn_prim ha hb h))
  · exact Or.inr (Or.inr h)

/-- **Colle's `n ≺ m`.**  `m` is the successor edge of `n` in the positively oriented
boundary of `R`: going counter-clockwise from `n`, `m` is the next edge normal of `R`
(wrapping around to the first one if `n` is the last). -/
def IsSuccEdge (R : Set (ℤ × ℤ)) (n m : ℤ × ℤ) : Prop :=
  n ∈ E R ∧ m ∈ E R ∧
    ((angLT n m ∧ ∀ k ∈ E R, angLT n k → ¬ angLT k m) ∨
     ((∀ k ∈ E R, ¬ angLT n k) ∧ ∀ k ∈ E R, ¬ angLT k m))

theorem exists_angMin {A : Set (ℤ × ℤ)} (hfin : A.Finite) (hne : A.Nonempty) :
    ∃ m ∈ A, ∀ k ∈ A, ¬ angLT k m := by
  classical
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image hfin.toFinset angKey
    (by rwa [Set.Finite.toFinset_nonempty])
  exact ⟨m, hfin.mem_toFinset.mp hm,
    fun k hk => not_lt.mpr (hmin k (hfin.mem_toFinset.mpr hk))⟩

/-- **Every edge of a set with finitely many edges has a successor.** -/
theorem exists_isSuccEdge {R : Set (ℤ × ℤ)} (hfin : (E R).Finite) {n : ℤ × ℤ}
    (hn : n ∈ E R) : ∃ m, IsSuccEdge R n m := by
  classical
  by_cases hA : {k | k ∈ E R ∧ angLT n k}.Nonempty
  · obtain ⟨m, hm, hmin⟩ := exists_angMin
      (hfin.subset (fun k hk => hk.1)) hA
    exact ⟨m, hn, hm.1, Or.inl ⟨hm.2, fun k hk hnk hkm => hmin k ⟨hk, hnk⟩ hkm⟩⟩
  · obtain ⟨m, hm, hmin⟩ := exists_angMin hfin ⟨n, hn⟩
    refine ⟨m, hn, hm, Or.inr ⟨fun k hk hnk => hA ⟨k, hk, hnk⟩, hmin⟩⟩

/-- **The successor is unique.** -/
theorem isSuccEdge_unique {R : Set (ℤ × ℤ)} {n m m' : ℤ × ℤ}
    (h : IsSuccEdge R n m) (h' : IsSuccEdge R n m') : m = m' := by
  obtain ⟨-, hmE, hm⟩ := h
  obtain ⟨-, hm'E, hm'⟩ := h'
  have key : ¬ angLT m m' ∧ ¬ angLT m' m := by
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hm' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact ⟨fun hc => h2' m hmE h1 hc, fun hc => h2 m' hm'E h1' hc⟩
    · exact absurd h1 (h1' m hmE)
    · exact absurd h1' (h1 m' hm'E)
    · exact ⟨h2' m hmE, h2 m' hm'E⟩
  rcases angLT_trichotomy hmE.1 hm'E.1 with hc | hc | hc
  · exact absurd hc key.1
  · exact hc
  · exact absurd hc key.2

/-- `m` lies strictly between `a` and `b` in the counter-clockwise cyclic order. -/
def CycBtw (a m b : ℤ × ℤ) : Prop :=
  (angLT a b ∧ angLT a m ∧ angLT m b) ∨ (angLT b a ∧ (angLT a m ∨ angLT m b))

/-- **Colle's `w ≺ ⋯ ≺ w'`** (Definition 3.1): following the positive orientation, the
edge `n` comes before the edge `n'`, i.e. every other edge sits between them. -/
def PrecedesAll (R : Set (ℤ × ℤ)) (n n' : ℤ × ℤ) : Prop :=
  n ∈ E R ∧ n' ∈ E R ∧ n ≠ n' ∧ ∀ m ∈ E R, m ≠ n → m ≠ n' → CycBtw n m n'

/-! ## §6. `E(𝒰)`-enveloped sets (Colle, Definition 3.2)

*"Let `𝒰 ⊆ ℤ²` be a finite, convex set such that `conv(𝒰)` has positive area.  A convex
set `𝒯 ⊆ ℤ²` is said to be weakly `E(𝒰)`-enveloped if, for every edge `ϖ ∈ E(𝒯)`, there
exists an edge `w ∈ E(𝒰)` parallel to `ϖ` with `|w ∩ 𝒰| ≤ |ϖ ∩ 𝒯|`.  A set `𝒯 ⊆ ℤ²`
weakly `E(𝒰)`-enveloped where `|E(𝒯)| = |E(𝒰)|` is said to be `E(𝒰)`-enveloped."*

Two *oriented* edges are parallel exactly when they carry the same primitive outer
normal (Colle, §1: "(anti)parallel" refers to the adjacent vectors of the respective
orientations), so "there exists `w ∈ E(𝒰)` parallel to `ϖ`" is literally `n ∈ E 𝒰`
for `n` the normal of `ϖ`.  Counts are taken in `ℕ∞` so that semi-infinite edges are
handled correctly. -/

/-- Translation of a subset of `ℤ²` by `v`. -/
def shift (v : ℤ × ℤ) (R : Set (ℤ × ℤ)) : Set (ℤ × ℤ) := {z | z - v ∈ R}

theorem mem_shift_iff {v : ℤ × ℤ} {R : Set (ℤ × ℤ)} {z : ℤ × ℤ} :
    z ∈ shift v R ↔ z - v ∈ R := Iff.rfl

theorem shift_eq_image (v : ℤ × ℤ) (R : Set (ℤ × ℤ)) :
    shift v R = (fun z => z + v) '' R := by
  ext z
  simp only [mem_shift_iff, Set.mem_image]
  exact ⟨fun h => ⟨z - v, h, by abel⟩, by rintro ⟨x, hx, rfl⟩; simpa using hx⟩

theorem face_shift (v : ℤ × ℤ) (R : Set (ℤ × ℤ)) (n : ℤ × ℤ) :
    face (shift v R) n = shift v (face R n) := by
  ext z
  constructor
  · rintro ⟨hz, hmax⟩
    refine ⟨hz, fun y hy => ?_⟩
    have h := hmax (y + v) (show (y + v) - v ∈ R by simpa using hy)
    have e1 := dot_add n y v
    have e2 := dot_sub n z v
    omega
  · rintro ⟨hz, hmax⟩
    refine ⟨hz, fun y hy => ?_⟩
    have h := hmax (y - v) hy
    have e1 := dot_sub n y v
    have e2 := dot_sub n z v
    omega

theorem shift_nontrivial_iff {v : ℤ × ℤ} {A : Set (ℤ × ℤ)} :
    (shift v A).Nontrivial ↔ A.Nontrivial := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨x - v, hx, y - v, hy, fun h => hxy (sub_left_inj.mp h)⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨x + v, by simpa [mem_shift_iff] using hx, y + v,
      by simpa [mem_shift_iff] using hy, fun h => hxy (add_right_cancel h)⟩

@[simp] theorem E_shift (v : ℤ × ℤ) (R : Set (ℤ × ℤ)) : E (shift v R) = E R := by
  ext n
  simp only [mem_E_iff, face_shift, shift_nontrivial_iff]

theorem encard_shift (v : ℤ × ℤ) (A : Set (ℤ × ℤ)) : (shift v A).encard = A.encard := by
  rw [shift_eq_image]
  exact Set.InjOn.encard_image (fun _ _ _ _ h => add_right_cancel h)

/-- **Colle, Definition 3.2.**  `T` is *weakly `E(U)`-enveloped*. -/
def WeaklyEnveloped (U T : Set (ℤ × ℤ)) : Prop :=
  IsLatticeConvexRegion T ∧ ∀ n ∈ E T, n ∈ E U ∧ (face U n).encard ≤ (face T n).encard

/-- **Colle, Definition 3.2.**  `T` is `E(U)`-enveloped. -/
def Enveloped (U T : Set (ℤ × ℤ)) : Prop :=
  WeaklyEnveloped U T ∧ (E T).encard = (E U).encard

theorem WeaklyEnveloped.E_subset {U T : Set (ℤ × ℤ)} (h : WeaklyEnveloped U T) :
    E T ⊆ E U := fun _ hn => (h.2 _ hn).1

theorem WeaklyEnveloped.latticeConvex {U T : Set (ℤ × ℤ)} (h : WeaklyEnveloped U T) :
    IsLatticeConvexRegion T := h.1

theorem weaklyEnveloped_refl (U : Set (ℤ × ℤ)) (hU : IsLatticeConvexRegion U) :
    WeaklyEnveloped U U :=
  ⟨hU, fun _ hn => ⟨hn, le_refl _⟩⟩

theorem enveloped_refl (U : Set (ℤ × ℤ)) (hU : IsLatticeConvexRegion U) : Enveloped U U :=
  ⟨weaklyEnveloped_refl U hU, rfl⟩

/-- **Translation carries a lattice-convex region to one.**  If `T = toReal ⁻¹' C` with
`C` closed convex, then `shift v T = toReal ⁻¹' {p | p - toReal v ∈ C}`, and translating
a closed convex set keeps it closed and convex. -/
theorem isLatticeConvexRegion_shift_of {T : Set (ℤ × ℤ)} (v : ℤ × ℤ)
    (h : IsLatticeConvexRegion T) : IsLatticeConvexRegion (shift v T) := by
  obtain ⟨C, hCconv, hCclosed, hTeq⟩ := h
  refine ⟨{p : ℝ × ℝ | p - toReal v ∈ C}, ?_, ?_, ?_⟩
  · intro p hp q hq α β hα hβ hsum
    show α • p + β • q - toReal v ∈ C
    have hv : toReal v = α • toReal v + β • toReal v := by
      rw [← add_smul, hsum, one_smul]
    have hstep : α • p + β • q - toReal v
        = α • (p - toReal v) + β • (q - toReal v) := by
      rw [smul_sub, smul_sub]; nth_rewrite 1 [hv]; abel
    rw [hstep]
    exact hCconv hp hq hα hβ hsum
  · exact IsClosed.preimage (continuous_sub_right (toReal v)) hCclosed
  · ext z
    show z ∈ shift v T ↔ toReal z ∈ {p : ℝ × ℝ | p - toReal v ∈ C}
    rw [show (z ∈ shift v T) = (z - v ∈ T) from rfl, hTeq]
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, toReal_sub]

theorem isLatticeConvexRegion_shift_iff {T : Set (ℤ × ℤ)} (v : ℤ × ℤ) :
    IsLatticeConvexRegion (shift v T) ↔ IsLatticeConvexRegion T := by
  refine ⟨fun h => ?_, isLatticeConvexRegion_shift_of v⟩
  have hcancel : shift (-v) (shift v T) = T := by
    ext z; simp [shift, sub_neg_eq_add]
  have hshift := isLatticeConvexRegion_shift_of (-v) h
  rwa [hcancel] at hshift

/-- **Translation preserves lattice-convexity.**  If `T` is lattice-convex, then so is
its translate `shift v T`. -/
theorem isLatticeConvexRegion_shift {T : Set (ℤ × ℤ)} (v : ℤ × ℤ)
    (h : IsLatticeConvexRegion T) : IsLatticeConvexRegion (shift v T) :=
  (isLatticeConvexRegion_shift_iff v).mpr h

/-! ## H-representation of a finite planar lattice set

Landed 2026-09-16, verified in the main repo with `lake env lean`: every theorem below
depends only on `[propext, Classical.choice, Quot.sound]`.

For a finite `T` with `PosArea T`,
`convHullOf T = ⋂ n ∈ E T, {x : ℝ² | ⟪ n, x ⟫ ≤ suppVal T n}`.

The `⊆` direction is routine.  The content is `⊇`, and the crux is `exists_edge_cone`:
every non-zero *real* direction `c` is a non-negative combination of two **edge** normals
`n₁, n₂ ∈ E T` which expose a common point `v` of `T`.  Given that, a point satisfying
all the edge inequalities satisfies every supporting inequality, and Hahn-Banach
separation finishes the job.  `IsFrame`/`isFrame_collinear` covers the degenerate case
where `T` is collinear and `PosArea T` fails.

mathlib has no 2D H-representation, and
`isLatticeConvexRegion_iUnion_of_mono_fixedEdges_finite` below needs one. -/

/-! ### H-rep §1. Elementary algebra of `dot` and `det` -/

theorem det_skew (u w : ℤ × ℤ) : det u w = - det w u := by
  simp only [det]; ring

theorem det_self (u : ℤ × ℤ) : det u u = 0 := by simp only [det]; ring

theorem dot_smul (g : ℤ) (p z : ℤ × ℤ) : dot (g • p) z = g * dot p z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem face_smul {T : Set (ℤ × ℤ)} {g : ℤ} (hg : 0 < g) (p : ℤ × ℤ) :
    face T (g • p) = face T p := by
  ext z
  simp only [mem_face_iff, dot_smul]
  refine and_congr_right fun _ => forall_congr' fun y => imp_congr_right fun _ => ?_
  constructor
  · intro h; exact le_of_mul_le_mul_left h hg
  · intro h; exact mul_le_mul_of_nonneg_left h hg.le

/-! ### H-rep §2. The primitive part of a non-zero lattice vector -/

/-- `primPart z` is `z` divided by the gcd of its coordinates. -/
def primPart (z : ℤ × ℤ) : ℤ × ℤ :=
  (z.1 / (Int.gcd z.1 z.2 : ℤ), z.2 / (Int.gcd z.1 z.2 : ℤ))

theorem primPart_spec {z : ℤ × ℤ} (hz : z ≠ 0) :
    Prim (primPart z) ∧ ∃ g : ℤ, 0 < g ∧ z = g • primPart z := by
  have hg0 : Int.gcd z.1 z.2 ≠ 0 := by
    intro h
    rcases Int.gcd_eq_zero_iff.mp h with ⟨h1, h2⟩
    exact hz (by simp [Prod.ext_iff, h1, h2])
  have hgpos : 0 < Int.gcd z.1 z.2 := Nat.pos_of_ne_zero hg0
  have h1 : (Int.gcd z.1 z.2 : ℤ) * (z.1 / (Int.gcd z.1 z.2 : ℤ)) = z.1 :=
    Int.mul_ediv_cancel' (Int.gcd_dvd_left z.1 z.2)
  have h2 : (Int.gcd z.1 z.2 : ℤ) * (z.2 / (Int.gcd z.1 z.2 : ℤ)) = z.2 :=
    Int.mul_ediv_cancel' (Int.gcd_dvd_right z.1 z.2)
  refine ⟨by simpa [Prim, primPart] using Int.gcd_div_gcd_div_gcd hgpos,
    (Int.gcd z.1 z.2 : ℤ), by exact_mod_cast hgpos, ?_⟩
  simp only [Prod.ext_iff, primPart, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  exact ⟨h1.symm, h2.symm⟩

/-! ### H-rep §3. Support values -/

/-- The support value `max {⟪n, z⟫ : z ∈ T}` of a finite non-empty `T` in the direction `n`
(defined for every `n`, with the usual `sSup` junk value otherwise). -/
noncomputable def suppVal (T : Set (ℤ × ℤ)) (n : ℤ × ℤ) : ℤ := sSup (dot n '' T)

theorem suppVal_eq {T : Set (ℤ × ℤ)} {n v : ℤ × ℤ} (hv : v ∈ face T n) :
    suppVal T n = dot n v :=
  IsGreatest.csSup_eq ⟨⟨v, hv.1, rfl⟩, by rintro _ ⟨z, hz, rfl⟩; exact hv.2 z hz⟩

theorem le_suppVal {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty) {n z : ℤ × ℤ}
    (hz : z ∈ T) : dot n z ≤ suppVal T n := by
  obtain ⟨v, hv⟩ := face_nonempty hfin hne n
  rw [suppVal_eq hv]
  exact hv.2 z hz

theorem exists_suppVal_eq {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty) (n : ℤ × ℤ) :
    ∃ v ∈ T, dot n v = suppVal T n := by
  obtain ⟨v, hv⟩ := face_nonempty hfin hne n
  exact ⟨v, hv.1, (suppVal_eq hv).symm⟩

/-- Support values are monotone in the set. -/
theorem suppVal_mono {T T' : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (hfin' : T'.Finite) (hne' : T'.Nonempty) (hsub : T ⊆ T') (n : ℤ × ℤ) :
    suppVal T n ≤ suppVal T' n := by
  obtain ⟨v, hv, hveq⟩ := exists_suppVal_eq hfin hne n
  rw [← hveq]
  exact le_suppVal hfin' hne' (hsub hv)

/-! ### H-rep §4. Real directions paired with lattice vectors -/

/-- The pairing of a real direction with a lattice vector. -/
def rdotZ (c : ℝ × ℝ) (u : ℤ × ℤ) : ℝ := c.1 * (u.1 : ℝ) + c.2 * (u.2 : ℝ)

/-- The determinant of a real direction against a lattice vector. -/
def rdet (c : ℝ × ℝ) (u : ℤ × ℤ) : ℝ := c.1 * (u.2 : ℝ) - c.2 * (u.1 : ℝ)

theorem rdotZ_sub (c : ℝ × ℝ) (u w : ℤ × ℤ) : rdotZ c (u - w) = rdotZ c u - rdotZ c w := by
  simp only [rdotZ, Prod.fst_sub, Prod.snd_sub]; push_cast; ring

theorem rdotZ_of_int (m : ℤ × ℤ) {c : ℝ × ℝ} {lam : ℝ}
    (hc1 : c.1 = lam * (m.1 : ℝ)) (hc2 : c.2 = lam * (m.2 : ℝ)) (u : ℤ × ℤ) :
    rdotZ c u = lam * (dot m u : ℝ) := by
  simp only [rdotZ, hc1, hc2, dot]; push_cast; ring

theorem rsq_pos {c : ℝ × ℝ} (hc : c ≠ 0) : 0 < c.1 ^ 2 + c.2 ^ 2 := by
  rcases eq_or_ne c.1 0 with h1 | h1
  · rcases eq_or_ne c.2 0 with h2 | h2
    · exact absurd (by simp [Prod.ext_iff, h1, h2] : c = 0) hc
    · positivity
  · positivity

/-! ### H-rep §5. The angular key on an open half plane

For lattice vectors `u` in the open half plane `{rdotZ c · < 0}`, the quantity
`rdet c u / rdotZ c u` is a faithful (order-reversing-free) measure of the angle of `u`. -/

/-- The angular key of the lattice vector `u` seen from the real direction `c`. -/
noncomputable def rkey (c : ℝ × ℝ) (u : ℤ × ℤ) : ℝ := rdet c u / rdotZ c u

theorem rkey_sub_mul {c : ℝ × ℝ} {u w : ℤ × ℤ} (hu : rdotZ c u ≠ 0) (hw : rdotZ c w ≠ 0) :
    (rkey c w - rkey c u) * (rdotZ c w * rdotZ c u)
      = (c.1 ^ 2 + c.2 ^ 2) * (det u w : ℝ) := by
  unfold rkey
  field_simp
  simp only [rdet, rdotZ, det]
  push_cast
  ring

theorem rkey_le_iff {c : ℝ × ℝ} {u w : ℤ × ℤ} (hc : c ≠ 0)
    (hu : rdotZ c u < 0) (hw : rdotZ c w < 0) :
    rkey c u ≤ rkey c w ↔ 0 ≤ det u w := by
  have hP : (0 : ℝ) < rdotZ c w * rdotZ c u := mul_pos_of_neg_of_neg hw hu
  have hC : (0 : ℝ) < c.1 ^ 2 + c.2 ^ 2 := rsq_pos hc
  have hE := rkey_sub_mul hu.ne hw.ne
  constructor
  · intro h
    have h1 : (0 : ℝ) ≤ rkey c w - rkey c u := sub_nonneg.mpr h
    have h2 : (0 : ℝ) ≤ (c.1 ^ 2 + c.2 ^ 2) * (det u w : ℝ) := by
      rw [← hE]; exact mul_nonneg h1 hP.le
    have h3 : (0 : ℝ) ≤ (det u w : ℝ) := by nlinarith
    exact_mod_cast h3
  · intro h
    have h3 : (0 : ℝ) ≤ (det u w : ℝ) := by exact_mod_cast h
    have h2 : (0 : ℝ) ≤ (rkey c w - rkey c u) * (rdotZ c w * rdotZ c u) := by
      rw [hE]; exact mul_nonneg hC.le h3
    nlinarith [h2, hP]

/-! ### H-rep §6. Rotations and the planar cone identity -/

/-- `nrmR w` is `w` rotated by `-90°`: `dot (nrmR w) u = - det w u`. -/
def nrmR (w : ℤ × ℤ) : ℤ × ℤ := (w.2, -w.1)

/-- `nrmL w` is `w` rotated by `+90°`: `dot (nrmL w) u = det w u`. -/
def nrmL (w : ℤ × ℤ) : ℤ × ℤ := (-w.2, w.1)

theorem dot_nrmR (w u : ℤ × ℤ) : dot (nrmR w) u = - det w u := by
  simp only [dot, det, nrmR]; ring

theorem dot_nrmL (w u : ℤ × ℤ) : dot (nrmL w) u = det w u := by
  simp only [dot, det, nrmL]; ring

theorem nrmR_ne_zero {w : ℤ × ℤ} (hw : w ≠ 0) : nrmR w ≠ 0 := by
  intro h
  apply hw
  simp only [nrmR, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at h
  simp [Prod.ext_iff, h.1, h.2]

theorem nrmL_ne_zero {w : ℤ × ℤ} (hw : w ≠ 0) : nrmL w ≠ 0 := by
  intro h
  apply hw
  simp only [nrmL, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at h
  simp [Prod.ext_iff, h.1, h.2]

/-- **The planar cone identity.**  `det w₁ w₂ · c = (-⟪c,w₂⟫)·nrmR w₁ + (-⟪c,w₁⟫)·nrmL w₂`.
This is the dual-cone computation: `nrmR w₁` and `nrmL w₂` generate the dual of the cone
spanned by `w₁` and `w₂`. -/
theorem cone_identity (c : ℝ × ℝ) (w₁ w₂ : ℤ × ℤ) :
    (det w₁ w₂ : ℝ) * c.1
        = (- rdotZ c w₂) * ((nrmR w₁).1 : ℝ) + (- rdotZ c w₁) * ((nrmL w₂).1 : ℝ) ∧
    (det w₁ w₂ : ℝ) * c.2
        = (- rdotZ c w₂) * ((nrmR w₁).2 : ℝ) + (- rdotZ c w₁) * ((nrmL w₂).2 : ℝ) := by
  constructor <;> simp only [det, rdotZ, nrmR, nrmL] <;> push_cast <;> ring

theorem real_div_comb {D A B p q r : ℝ} (hD : 0 < D) (h : D * p = A * q + B * r) :
    p = (A / D) * q + (B / D) * r := by
  have hD' : D ≠ 0 := ne_of_gt hD
  field_simp
  linear_combination h

/-! ### H-rep §7. The cone decomposition (crux) -/

/-- `ConeDecomp T N c`: the real direction `c` is a non-negative combination of two
members `n₁, n₂` of `N`, and some point `v` of `T` maximises all three of
`⟪c,·⟫`, `⟪n₁,·⟫`, `⟪n₂,·⟫` over `T`. -/
def ConeDecomp (T N : Set (ℤ × ℤ)) (c : ℝ × ℝ) : Prop :=
  ∃ n₁ n₂ : ℤ × ℤ, ∃ a b : ℝ, n₁ ∈ N ∧ n₂ ∈ N ∧ 0 ≤ a ∧ 0 ≤ b ∧
    c.1 = a * (n₁.1 : ℝ) + b * (n₂.1 : ℝ) ∧
    c.2 = a * (n₁.2 : ℝ) + b * (n₂.2 : ℝ) ∧
    ∃ v : ℤ × ℤ, (∀ z ∈ T, rdotZ c z ≤ rdotZ c v) ∧ v ∈ face T n₁ ∧ v ∈ face T n₂

/-- `N` is a *frame* for `T` if every non-zero direction has a cone decomposition along `N`.
The edge normals `E T` form a frame when `T` has positive area (`isFrame_E`); for a
collinear `T` one needs the two directions along the line as well (`isFrame_collinear`). -/
def IsFrame (T N : Set (ℤ × ℤ)) : Prop :=
  ∀ c : ℝ × ℝ, c ≠ 0 → ConeDecomp T N c

/-- The degenerate case of the crux: `c` is a positive multiple of an integer vector `m`
whose face already contains two distinct points of `T`. -/
theorem coneDecomp_of_parallel {T : Set (ℤ × ℤ)} {c : ℝ × ℝ} {m : ℤ × ℤ} (hm : m ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hc1 : c.1 = lam * (m.1 : ℝ)) (hc2 : c.2 = lam * (m.2 : ℝ))
    {u v : ℤ × ℤ} (huT : u ∈ T) (hvT : v ∈ T) (huv : u ≠ v)
    (hueq : rdotZ c u = rdotZ c v) (hvle : ∀ z ∈ T, rdotZ c z ≤ rdotZ c v) :
    ConeDecomp T (E T) c := by
  obtain ⟨hp, g, hg, hgeq⟩ := primPart_spec hm
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hm1 : (m.1 : ℤ) = g * (primPart m).1 := by
    conv_lhs => rw [hgeq]
    simp
  have hm2 : (m.2 : ℤ) = g * (primPart m).2 := by
    conv_lhs => rw [hgeq]
    simp
  -- `m` exposes `v`, hence so does `primPart m`
  have hdotle : ∀ z ∈ T, dot m z ≤ dot m v := by
    intro z hz
    have h := hvle z hz
    rw [rdotZ_of_int m hc1 hc2, rdotZ_of_int m hc1 hc2] at h
    have : (dot m z : ℝ) ≤ (dot m v : ℝ) := le_of_mul_le_mul_left h hlam
    exact_mod_cast this
  have hdotu : dot m u = dot m v := by
    rw [rdotZ_of_int m hc1 hc2, rdotZ_of_int m hc1 hc2] at hueq
    have : (dot m u : ℝ) = (dot m v : ℝ) := mul_left_cancel₀ (ne_of_gt hlam) hueq
    exact_mod_cast this
  have hfaceEq : face T m = face T (primPart m) := by
    calc face T m = face T (g • primPart m) := by rw [← hgeq]
      _ = face T (primPart m) := face_smul hg _
  have hvf : v ∈ face T (primPart m) := hfaceEq ▸ ⟨hvT, hdotle⟩
  have huf : u ∈ face T (primPart m) :=
    hfaceEq ▸ ⟨huT, fun y hy => by rw [hdotu]; exact hdotle y hy⟩
  refine ⟨primPart m, primPart m, lam * (g : ℝ), 0, ⟨hp, ⟨u, huf, v, hvf, huv⟩⟩,
    ⟨hp, ⟨u, huf, v, hvf, huv⟩⟩, by positivity, le_refl 0, ?_, ?_, v, hvle, hvf, hvf⟩
  · rw [zero_mul, add_zero, hc1]
    have : ((m.1 : ℤ) : ℝ) = (g : ℝ) * (((primPart m).1 : ℤ) : ℝ) := by exact_mod_cast hm1
    rw [this]; ring
  · rw [zero_mul, add_zero, hc2]
    have : ((m.2 : ℤ) : ℝ) = (g : ℝ) * (((primPart m).2 : ℤ) : ℝ) := by exact_mod_cast hm2
    rw [this]; ring

/-- **Crux.**  For a finite planar lattice set `T` of positive area and *any* non-zero real
direction `c`, there are two edge normals `n₁, n₂ ∈ E T` and non-negative reals `a, b`
with `c = a·n₁ + b·n₂`, such that a single point `v` of `T` maximises all three of
`⟪c,·⟫`, `⟪n₁,·⟫`, `⟪n₂,·⟫` over `T`.

If `c` already exposes an edge this is `coneDecomp_of_parallel`.  The real content is the
case where `c` exposes a single vertex `v`: then `c` lies in the normal cone at `v`, which
is spanned by the normals of the two edges of `T` through `v`.  Those two edges are found
by taking the angular extremes of `{z - v : z ∈ T, z ≠ v}`, a set which lies in the open
half plane `{rdotZ c · < 0}` and is therefore angularly totally ordered by `rkey c`. -/
theorem exists_edge_cone {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (harea : PosArea T) {c : ℝ × ℝ} (hc : c ≠ 0) : ConeDecomp T (E T) c := by
  classical
  have hTne : hfin.toFinset.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, hfin.mem_toFinset.mpr hp⟩
  obtain ⟨v, hvS, hvmax⟩ := hfin.toFinset.exists_max_image (rdotZ c) hTne
  have hvT : v ∈ T := hfin.mem_toFinset.mp hvS
  have hvle : ∀ z ∈ T, rdotZ c z ≤ rdotZ c v := fun z hz => hvmax z (hfin.mem_toFinset.mpr hz)
  by_cases hB : ∃ u ∈ T, u ≠ v ∧ rdotZ c u = rdotZ c v
  · -- `c` already exposes an edge of `T`.
    obtain ⟨u, huT, huv, hueq⟩ := hB
    have hwne : u - v ≠ 0 := sub_ne_zero.mpr huv
    have hperp : rdotZ c (u - v) = 0 := by rw [rdotZ_sub, hueq]; ring
    have hN : (0 : ℝ) < ((u - v).1 : ℝ) ^ 2 + ((u - v).2 : ℝ) ^ 2 := by
      rcases eq_or_ne ((u - v).1) 0 with h1 | h1
      · rcases eq_or_ne ((u - v).2) 0 with h2 | h2
        · exact absurd (by simp [Prod.ext_iff, h1, h2] : u - v = 0) hwne
        · have : ((u - v).2 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h2
          positivity
      · have : ((u - v).1 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h1
        positivity
    set lam : ℝ :=
      (c.1 * (((u - v).2 : ℤ) : ℝ) - c.2 * (((u - v).1 : ℤ) : ℝ))
        / (((u - v).1 : ℝ) ^ 2 + ((u - v).2 : ℝ) ^ 2) with hlamdef
    have hperp' : c.1 * (((u - v).1 : ℤ) : ℝ) + c.2 * (((u - v).2 : ℤ) : ℝ) = 0 := hperp
    have hc1 : c.1 = lam * (((nrmR (u - v)).1 : ℤ) : ℝ) := by
      rw [hlamdef]
      simp only [nrmR]
      field_simp
      linear_combination (((u - v).1 : ℤ) : ℝ) * hperp'
    have hc2 : c.2 = lam * (((nrmR (u - v)).2 : ℤ) : ℝ) := by
      rw [hlamdef]
      simp only [nrmR]
      push_cast
      field_simp
      linear_combination (((u - v).2 : ℤ) : ℝ) * hperp'
    have hlamne : lam ≠ 0 := by
      intro h
      apply hc
      rw [h] at hc1 hc2
      simp only [zero_mul] at hc1 hc2
      simp [Prod.ext_iff, hc1, hc2]
    rcases lt_or_gt_of_ne hlamne with hneg | hpos
    · -- `c` is a positive multiple of `nrmL (u - v)`
      refine coneDecomp_of_parallel (nrmL_ne_zero hwne) (neg_pos.mpr hneg) ?_ ?_
        huT hvT huv hueq hvle
      · rw [hc1]; simp only [nrmR, nrmL]; push_cast; ring
      · rw [hc2]; simp only [nrmR, nrmL]; push_cast; ring
    · exact coneDecomp_of_parallel (nrmR_ne_zero hwne) hpos hc1 hc2 huT hvT huv hueq hvle
  · -- `c` exposes the single vertex `v`; build the two edges of `T` through `v`.
    push Not at hB
    have hlt : ∀ z ∈ T, z ≠ v → rdotZ c (z - v) < 0 := by
      intro z hz hzv
      have h1 : rdotZ c z ≤ rdotZ c v := hvle z hz
      have h2 : rdotZ c z ≠ rdotZ c v := hB z hz hzv
      rw [rdotZ_sub]
      linarith [lt_of_le_of_ne h1 h2]
    set S : Finset (ℤ × ℤ) := hfin.toFinset.erase v with hSdef
    have hmemS : ∀ z, z ∈ S ↔ (z ∈ T ∧ z ≠ v) := by
      intro z
      simp only [hSdef, Finset.mem_erase, hfin.mem_toFinset]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    have hSne : S.Nonempty := by
      rcases Finset.eq_empty_or_nonempty S with h | h
      · exfalso
        obtain ⟨a, ha, b, hb, d, hd, hdet⟩ := harea
        have e : ∀ z ∈ T, z = v := by
          intro z hz
          by_contra hx
          have hzS : z ∈ S := (hmemS z).mpr ⟨hz, hx⟩
          rw [h] at hzS
          exact absurd hzS (Finset.notMem_empty z)
        rw [e a ha, e b hb, e d hd] at hdet
        exact hdet (by simp only [sub_self]; simp [det])
      · exact h
    obtain ⟨z₁, hz₁S, hmin⟩ := S.exists_min_image (fun z => rkey c (z - v)) hSne
    obtain ⟨z₂, hz₂S, hmax⟩ := S.exists_max_image (fun z => rkey c (z - v)) hSne
    have hz₁T : z₁ ∈ T := ((hmemS z₁).mp hz₁S).1
    have hz₁v : z₁ ≠ v := ((hmemS z₁).mp hz₁S).2
    have hz₂T : z₂ ∈ T := ((hmemS z₂).mp hz₂S).1
    have hz₂v : z₂ ≠ v := ((hmemS z₂).mp hz₂S).2
    have hneg : ∀ z ∈ S, rdotZ c (z - v) < 0 := fun z hz =>
      hlt z ((hmemS z).mp hz).1 ((hmemS z).mp hz).2
    have hd1 : ∀ z ∈ S, 0 ≤ det (z₁ - v) (z - v) := fun z hz =>
      (rkey_le_iff hc (hneg z₁ hz₁S) (hneg z hz)).mp (hmin z hz)
    have hd2 : ∀ z ∈ S, det (z₂ - v) (z - v) ≤ 0 := by
      intro z hz
      have h := (rkey_le_iff hc (hneg z hz) (hneg z₂ hz₂S)).mp (hmax z hz)
      rw [det_skew (z₂ - v) (z - v)]
      linarith
    -- the two extreme directions are independent, by positivity of the area
    have hD : 0 < det (z₁ - v) (z₂ - v) := by
      rcases (hd1 z₂ hz₂S).lt_or_eq with h | h
      · exact h
      · exfalso
        have hkeyeq : rkey c (z₂ - v) ≤ rkey c (z₁ - v) :=
          (rkey_le_iff hc (hneg z₂ hz₂S) (hneg z₁ hz₁S)).mpr
            (by rw [det_skew (z₂ - v) (z₁ - v)]; linarith)
        have hconst : ∀ z ∈ S, rkey c (z - v) = rkey c (z₁ - v) :=
          fun z hz => le_antisymm (le_trans (hmax z hz) hkeyeq) (hmin z hz)
        have hallS : ∀ z ∈ S, ∀ z' ∈ S, det (z - v) (z' - v) = 0 := by
          intro z hz z' hz'
          have h1 : (0 : ℤ) ≤ det (z - v) (z' - v) :=
            (rkey_le_iff hc (hneg z hz) (hneg z' hz')).mp
              (by rw [hconst z hz, hconst z' hz'])
          have h2 : (0 : ℤ) ≤ det (z' - v) (z - v) :=
            (rkey_le_iff hc (hneg z' hz') (hneg z hz)).mp
              (by rw [hconst z hz, hconst z' hz'])
          rw [det_skew (z' - v) (z - v)] at h2
          linarith
        have hall : ∀ z ∈ T, ∀ z' ∈ T, det (z - v) (z' - v) = 0 := by
          intro z hz z' hz'
          by_cases hzv : z = v
          · subst hzv; simp [det]
          by_cases hz'v : z' = v
          · subst hz'v; simp [det]
          exact hallS z ((hmemS z).mpr ⟨hz, hzv⟩) z' ((hmemS z').mpr ⟨hz', hz'v⟩)
        obtain ⟨a, ha, b, hb, d, hd, hdet⟩ := harea
        refine hdet ?_
        have e1 := hall b hb a ha
        have e2 := hall b hb d hd
        have e3 := hall a ha d hd
        have e4 := hall a ha a ha
        simp only [det, Prod.fst_sub, Prod.snd_sub] at e1 e2 e3 e4 ⊢
        linear_combination e2 - e1 - e3 + e4
    -- the two edge normals
    have hw₁ne : z₁ - v ≠ 0 := sub_ne_zero.mpr hz₁v
    have hw₂ne : z₂ - v ≠ 0 := sub_ne_zero.mpr hz₂v
    obtain ⟨hp₁, g₁, hg₁, he₁⟩ := primPart_spec (nrmR_ne_zero hw₁ne)
    obtain ⟨hp₂, g₂, hg₂, he₂⟩ := primPart_spec (nrmL_ne_zero hw₂ne)
    set n₁ : ℤ × ℤ := primPart (nrmR (z₁ - v)) with hn₁def
    set n₂ : ℤ × ℤ := primPart (nrmL (z₂ - v)) with hn₂def
    have hfm₁ : ∀ z ∈ T, dot (nrmR (z₁ - v)) z ≤ dot (nrmR (z₁ - v)) v := by
      intro z hz
      by_cases hzv : z = v
      · subst hzv; exact le_refl _
      · have hge := hd1 z ((hmemS z).mpr ⟨hz, hzv⟩)
        have h2 : dot (nrmR (z₁ - v)) (z - v) ≤ 0 := by rw [dot_nrmR]; linarith
        rw [dot_sub] at h2; linarith
    have hzero₁ : dot (nrmR (z₁ - v)) (z₁ - v) = 0 := by rw [dot_nrmR, det_self]; ring
    have hfm₂ : ∀ z ∈ T, dot (nrmL (z₂ - v)) z ≤ dot (nrmL (z₂ - v)) v := by
      intro z hz
      by_cases hzv : z = v
      · subst hzv; exact le_refl _
      · have hle := hd2 z ((hmemS z).mpr ⟨hz, hzv⟩)
        have h2 : dot (nrmL (z₂ - v)) (z - v) ≤ 0 := by rw [dot_nrmL]; linarith
        rw [dot_sub] at h2; linarith
    have hzero₂ : dot (nrmL (z₂ - v)) (z₂ - v) = 0 := by rw [dot_nrmL, det_self]
    have hfaceEq₁ : face T (nrmR (z₁ - v)) = face T n₁ := by
      calc face T (nrmR (z₁ - v)) = face T (g₁ • n₁) := by rw [← he₁]
        _ = face T n₁ := face_smul hg₁ _
    have hfaceEq₂ : face T (nrmL (z₂ - v)) = face T n₂ := by
      calc face T (nrmL (z₂ - v)) = face T (g₂ • n₂) := by rw [← he₂]
        _ = face T n₂ := face_smul hg₂ _
    have hv₁ : v ∈ face T n₁ := hfaceEq₁ ▸ ⟨hvT, hfm₁⟩
    have hv₂ : v ∈ face T n₂ := hfaceEq₂ ▸ ⟨hvT, hfm₂⟩
    have hz₁face : z₁ ∈ face T n₁ := by
      refine hfaceEq₁ ▸ ⟨hz₁T, fun y hy => ?_⟩
      have heq : dot (nrmR (z₁ - v)) z₁ = dot (nrmR (z₁ - v)) v := by
        rw [dot_sub] at hzero₁; linarith
      rw [heq]; exact hfm₁ y hy
    have hz₂face : z₂ ∈ face T n₂ := by
      refine hfaceEq₂ ▸ ⟨hz₂T, fun y hy => ?_⟩
      have heq : dot (nrmL (z₂ - v)) z₂ = dot (nrmL (z₂ - v)) v := by
        rw [dot_sub] at hzero₂; linarith
      rw [heq]; exact hfm₂ y hy
    have hE₁ : n₁ ∈ E T := ⟨hp₁, ⟨z₁, hz₁face, v, hv₁, hz₁v⟩⟩
    have hE₂ : n₂ ∈ E T := ⟨hp₂, ⟨z₂, hz₂face, v, hv₂, hz₂v⟩⟩
    -- the coefficients
    have hA : 0 < - rdotZ c (z₂ - v) := by linarith [hneg z₂ hz₂S]
    have hBpos : 0 < - rdotZ c (z₁ - v) := by linarith [hneg z₁ hz₁S]
    have hg₁R : (0 : ℝ) < (g₁ : ℝ) := by exact_mod_cast hg₁
    have hg₂R : (0 : ℝ) < (g₂ : ℝ) := by exact_mod_cast hg₂
    have hDR : (0 : ℝ) < ((det (z₁ - v) (z₂ - v) : ℤ) : ℝ) := by exact_mod_cast hD
    obtain ⟨hcone1, hcone2⟩ := cone_identity c (z₁ - v) (z₂ - v)
    have hm₁1 : (((nrmR (z₁ - v)).1 : ℤ) : ℝ) = (g₁ : ℝ) * ((n₁.1 : ℤ) : ℝ) := by
      have : ((nrmR (z₁ - v)).1 : ℤ) = g₁ * n₁.1 := by
        conv_lhs => rw [he₁]
        simp
      exact_mod_cast this
    have hm₁2 : (((nrmR (z₁ - v)).2 : ℤ) : ℝ) = (g₁ : ℝ) * ((n₁.2 : ℤ) : ℝ) := by
      have : ((nrmR (z₁ - v)).2 : ℤ) = g₁ * n₁.2 := by
        conv_lhs => rw [he₁]
        simp
      exact_mod_cast this
    have hm₂1 : (((nrmL (z₂ - v)).1 : ℤ) : ℝ) = (g₂ : ℝ) * ((n₂.1 : ℤ) : ℝ) := by
      have : ((nrmL (z₂ - v)).1 : ℤ) = g₂ * n₂.1 := by
        conv_lhs => rw [he₂]
        simp
      exact_mod_cast this
    have hm₂2 : (((nrmL (z₂ - v)).2 : ℤ) : ℝ) = (g₂ : ℝ) * ((n₂.2 : ℤ) : ℝ) := by
      have : ((nrmL (z₂ - v)).2 : ℤ) = g₂ * n₂.2 := by
        conv_lhs => rw [he₂]
        simp
      exact_mod_cast this
    have hI1 : ((det (z₁ - v) (z₂ - v) : ℤ) : ℝ) * c.1
        = ((- rdotZ c (z₂ - v)) * (g₁ : ℝ)) * ((n₁.1 : ℤ) : ℝ)
          + ((- rdotZ c (z₁ - v)) * (g₂ : ℝ)) * ((n₂.1 : ℤ) : ℝ) := by
      rw [hcone1, hm₁1, hm₂1]; ring
    have hI2 : ((det (z₁ - v) (z₂ - v) : ℤ) : ℝ) * c.2
        = ((- rdotZ c (z₂ - v)) * (g₁ : ℝ)) * ((n₁.2 : ℤ) : ℝ)
          + ((- rdotZ c (z₁ - v)) * (g₂ : ℝ)) * ((n₂.2 : ℤ) : ℝ) := by
      rw [hcone2, hm₁2, hm₂2]; ring
    exact ⟨n₁, n₂,
      ((- rdotZ c (z₂ - v)) * (g₁ : ℝ)) / ((det (z₁ - v) (z₂ - v) : ℤ) : ℝ),
      ((- rdotZ c (z₁ - v)) * (g₂ : ℝ)) / ((det (z₁ - v) (z₂ - v) : ℤ) : ℝ),
      hE₁, hE₂,
      div_nonneg (mul_pos hA hg₁R).le hDR.le,
      div_nonneg (mul_pos hBpos hg₂R).le hDR.le,
      real_div_comb hDR hI1, real_div_comb hDR hI2,
      v, hvle, hv₁, hv₂⟩

/-- The edge normals of a positive-area set form a frame. -/
theorem isFrame_E {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty) (harea : PosArea T) :
    IsFrame T (E T) :=
  fun _c hc => exists_edge_cone hfin hne harea hc

/-! ### H-rep §7b. The collinear frame

For a `T` all of whose points lie on a line of direction `w`, the four directions
`w, -w, nrmL w, -nrmL w` form a frame: `±nrmL w` expose all of `T`, and `±w` expose the
two ends of the segment. -/


theorem rdotZ_decomp (c : ℝ × ℝ) {w : ℤ × ℤ} (hw : w ≠ 0) (z : ℤ × ℤ) :
    rdotZ c z = (rdotZ c w / ((w.1 : ℝ) ^ 2 + (w.2 : ℝ) ^ 2)) * (dot w z : ℝ)
      + (rdotZ c (nrmL w) / ((w.1 : ℝ) ^ 2 + (w.2 : ℝ) ^ 2)) * (dot (nrmL w) z : ℝ) := by
  have hN : (0 : ℝ) < (w.1 : ℝ) ^ 2 + (w.2 : ℝ) ^ 2 := by
    rcases eq_or_ne w.1 0 with h1 | h1
    · rcases eq_or_ne w.2 0 with h2 | h2
      · exact absurd (by simp [Prod.ext_iff, h1, h2] : w = 0) hw
      · have : (w.2 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h2
        positivity
    · have : (w.1 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h1
      positivity
  have hN' : (w.1 : ℝ) ^ 2 + (w.2 : ℝ) ^ 2 ≠ 0 := ne_of_gt hN
  simp only [rdotZ, dot, nrmL]
  push_cast
  field_simp
  ring

/-- **The collinear frame.**  If all of `T` lies on a line of direction `w ≠ 0`, then
`{w, -w, nrmL w, -nrmL w}` is a frame for `T`. -/
theorem isFrame_collinear {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    {w : ℤ × ℤ} (hw : w ≠ 0) (hcol : ∀ z ∈ T, ∀ z' ∈ T, det (z - z') w = 0) :
    IsFrame T {w, -w, nrmL w, -nrmL w} := by
  classical
  intro c hc
  have hTne : hfin.toFinset.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, hfin.mem_toFinset.mpr hp⟩
  obtain ⟨v, hvS, hvmax⟩ := hfin.toFinset.exists_max_image (rdotZ c) hTne
  have hvT : v ∈ T := hfin.mem_toFinset.mp hvS
  have hvle : ∀ z ∈ T, rdotZ c z ≤ rdotZ c v := fun z hz => hvmax z (hfin.mem_toFinset.mpr hz)
  set m : ℤ × ℤ := nrmL w with hmdef
  set D : ℝ := (w.1 : ℝ) ^ 2 + (w.2 : ℝ) ^ 2 with hDdef
  set α : ℝ := rdotZ c w / D with hαdef
  set β : ℝ := rdotZ c m / D with hβdef
  -- `⟪m, ·⟫` is constant on `T`
  have hmconst : ∀ z ∈ T, dot m z = dot m v := by
    intro z hz
    have h : dot (nrmL w) (z - v) = 0 := by
      rw [dot_nrmL, det_skew, hcol z hz v hvT]; ring
    rw [dot_sub] at h
    linarith
  have hmface : v ∈ face T m := ⟨hvT, fun z hz => (hmconst z hz).le⟩
  have hmface' : v ∈ face T (-m) := ⟨hvT, fun z hz => by rw [dot_neg_left, dot_neg_left, hmconst z hz]⟩
  have hdec : ∀ z, rdotZ c z = α * (dot w z : ℝ) + β * (dot m z : ℝ) := fun z =>
    rdotZ_decomp c hw z
  have hc1 : c.1 = α * (w.1 : ℝ) + β * (m.1 : ℝ) := by
    have h := hdec (1, 0)
    simp only [rdotZ, dot, Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero] at h
    simpa [hmdef, nrmL] using h
  have hc2 : c.2 = α * (w.2 : ℝ) + β * (m.2 : ℝ) := by
    have h := hdec (0, 1)
    simp only [rdotZ, dot, Int.cast_one, Int.cast_zero, mul_one, mul_zero, zero_add] at h
    simpa [hmdef, nrmL] using h
  -- the `w`-component of the maximiser
  have hαle : ∀ z ∈ T, α * (dot w z : ℝ) ≤ α * (dot w v : ℝ) := by
    intro z hz
    have h := hvle z hz
    rw [hdec z, hdec v, hmconst z hz] at h
    linarith
  have hw1 : ((-w).1 : ℝ) = -(w.1 : ℝ) := by simp
  have hw2 : ((-w).2 : ℝ) = -(w.2 : ℝ) := by simp
  have hm1 : ((-m).1 : ℝ) = -(m.1 : ℝ) := by simp
  have hm2 : ((-m).2 : ℝ) = -(m.2 : ℝ) := by simp
  have hwmem : w ∈ ({w, -w, nrmL w, -nrmL w} : Set (ℤ × ℤ)) := by simp
  have hwmem' : -w ∈ ({w, -w, nrmL w, -nrmL w} : Set (ℤ × ℤ)) := by simp
  have hmmem : m ∈ ({w, -w, nrmL w, -nrmL w} : Set (ℤ × ℤ)) := by simp [hmdef]
  have hmmem' : -m ∈ ({w, -w, nrmL w, -nrmL w} : Set (ℤ × ℤ)) := by simp [hmdef]
  -- choose the `m`-part
  obtain ⟨n₂, b, hn₂, hb, hb1, hb2, hv₂⟩ : ∃ n₂ : ℤ × ℤ, ∃ b : ℝ,
      n₂ ∈ ({w, -w, nrmL w, -nrmL w} : Set (ℤ × ℤ)) ∧ 0 ≤ b ∧
      β * (m.1 : ℝ) = b * (n₂.1 : ℝ) ∧ β * (m.2 : ℝ) = b * (n₂.2 : ℝ) ∧ v ∈ face T n₂ := by
    rcases le_or_gt 0 β with hβ | hβ
    · exact ⟨m, β, hmmem, hβ, rfl, rfl, hmface⟩
    · exact ⟨-m, -β, hmmem', by linarith, by rw [hm1]; ring, by rw [hm2]; ring, hmface'⟩
  -- choose the `w`-part
  rcases lt_trichotomy α 0 with hα | hα | hα
  · refine ⟨-w, n₂, -α, b, hwmem', hn₂, by linarith, hb, ?_, ?_, v, hvle, ?_, hv₂⟩
    · rw [hc1, hb1, hw1]; ring
    · rw [hc2, hb2, hw2]; ring
    · refine ⟨hvT, fun z hz => ?_⟩
      rw [dot_neg_left, dot_neg_left, neg_le_neg_iff]
      have h := hαle z hz
      have : (dot w v : ℝ) ≤ (dot w z : ℝ) := le_of_mul_le_mul_left (by linarith) (neg_pos.mpr hα)
      exact_mod_cast this
  · refine ⟨n₂, n₂, 0, b, hn₂, hn₂, le_refl 0, hb, ?_, ?_, v, hvle, hv₂, hv₂⟩
    · rw [hc1, hb1, hα]; ring
    · rw [hc2, hb2, hα]; ring
  · refine ⟨w, n₂, α, b, hwmem, hn₂, hα.le, hb, ?_, ?_, v, hvle, ?_, hv₂⟩
    · rw [hc1, hb1]
    · rw [hc2, hb2]
    · refine ⟨hvT, fun z hz => ?_⟩
      have : (dot w z : ℝ) ≤ (dot w v : ℝ) := le_of_mul_le_mul_left (hαle z hz) hα
      exact_mod_cast this

/-! ### H-rep §8. The H-representation -/

/-- The closed half plane `{x : ⟪n, x⟫ ≤ c}` of `ℝ²`. -/
def realHalfPlaneLE (n : ℤ × ℤ) (c : ℤ) : Set (ℝ × ℝ) :=
  {x : ℝ × ℝ | (n.1 : ℝ) * x.1 + (n.2 : ℝ) * x.2 ≤ (c : ℝ)}

theorem mem_realHalfPlaneLE {n : ℤ × ℤ} {c : ℤ} {x : ℝ × ℝ} :
    x ∈ realHalfPlaneLE n c ↔ (n.1 : ℝ) * x.1 + (n.2 : ℝ) * x.2 ≤ (c : ℝ) := Iff.rfl

theorem realHalfPlaneLE_isClosed (n : ℤ × ℤ) (c : ℤ) : IsClosed (realHalfPlaneLE n c) :=
  isClosed_le
    ((continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd))
    continuous_const

theorem realHalfPlaneLE_convex (n : ℤ × ℤ) (c : ℤ) : Convex ℝ (realHalfPlaneLE n c) := by
  intro x hx y hy s t hs ht hst
  have hx' : (n.1 : ℝ) * x.1 + (n.2 : ℝ) * x.2 ≤ (c : ℝ) := hx
  have hy' : (n.1 : ℝ) * y.1 + (n.2 : ℝ) * y.2 ≤ (c : ℝ) := hy
  have hsum : s * (c : ℝ) + t * (c : ℝ) = (c : ℝ) := by rw [← add_mul, hst, one_mul]
  show (n.1 : ℝ) * (s • x + t • y).1 + (n.2 : ℝ) * (s • x + t • y).2 ≤ (c : ℝ)
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx' hs, mul_le_mul_of_nonneg_left hy' ht, hsum]

theorem convex_convHullOf (T : Set (ℤ × ℤ)) : Convex ℝ (convHullOf T) :=
  (convex_convexHull ℝ _).closure

theorem isClosed_convHullOf (T : Set (ℤ × ℤ)) : IsClosed (convHullOf T) := isClosed_closure

theorem toReal_mem_convHullOf {T : Set (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ T) :
    toReal z ∈ convHullOf T := subset_closure (subset_convexHull ℝ _ ⟨z, hz, rfl⟩)

theorem dot_cast_toReal (m z : ℤ × ℤ) :
    (m.1 : ℝ) * (toReal z).1 + (m.2 : ℝ) * (toReal z).2 = ((dot m z : ℤ) : ℝ) := by
  simp only [toReal, dot]; push_cast; ring

/-- Every point of `T` satisfies the support constraint in every direction. -/
theorem toReal_mem_realHalfPlaneLE_of_mem {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    {z : ℤ × ℤ} (hz : z ∈ T) (n : ℤ × ℤ) :
    toReal z ∈ realHalfPlaneLE n (suppVal T n) := by
  show (n.1 : ℝ) * (toReal z).1 + (n.2 : ℝ) * (toReal z).2 ≤ ((suppVal T n : ℤ) : ℝ)
  rw [dot_cast_toReal]
  exact_mod_cast le_suppVal hfin hne hz

/-- **The easy direction**, for an arbitrary set `N` of directions: the hull lies in every
supporting half plane. -/
theorem convHullOf_subset_iInter_frame {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (N : Set (ℤ × ℤ)) :
    convHullOf T ⊆ ⋂ n ∈ N, realHalfPlaneLE n (suppVal T n) := by
  refine Set.subset_iInter₂ fun n _ => ?_
  refine closure_minimal (convexHull_min ?_ (realHalfPlaneLE_convex n _))
    (realHalfPlaneLE_isClosed n _)
  rintro _ ⟨z, hz, rfl⟩
  exact toReal_mem_realHalfPlaneLE_of_mem hfin hne hz n

/-- **The hard direction**, for any frame `N`: a point of `ℝ²` satisfying every supporting
inequality indexed by `N` lies in the closed convex hull.  Separate a missing point
(Hahn–Banach), then decompose the separating direction along two members of `N` sharing an
exposed point of `T`. -/
theorem iInter_subset_convHullOf_frame {T N : Set (ℤ × ℤ)} (hne : T.Nonempty)
    (hframe : IsFrame T N) :
    ⋂ n ∈ N, realHalfPlaneLE n (suppVal T n) ⊆ convHullOf T := by
  intro x hx
  by_contra hxK
  obtain ⟨f, u, hfle, hfx⟩ := geometric_hahn_banach_closed_point
    (convex_convHullOf T) (isClosed_convHullOf T) hxK
  obtain ⟨c, hfrep⟩ : ∃ c : ℝ × ℝ, ∀ y : ℝ × ℝ, f y = c.1 * y.1 + c.2 * y.2 := by
    refine ⟨(f (1, 0), f (0, 1)), fun y => ?_⟩
    have hy : y = y.1 • ((1 : ℝ), (0 : ℝ)) + y.2 • ((0 : ℝ), (1 : ℝ)) := by
      simp
    conv_lhs => rw [hy]
    rw [map_add, map_smul, map_smul]
    simp [mul_comm]
  have hsep : ∀ z ∈ T, rdotZ c z < c.1 * x.1 + c.2 * x.2 := by
    intro z hz
    have h1 : c.1 * (toReal z).1 + c.2 * (toReal z).2 < u := by
      rw [← hfrep]; exact hfle _ (toReal_mem_convHullOf hz)
    have h2 : u < c.1 * x.1 + c.2 * x.2 := by rw [← hfrep]; exact hfx
    have h3 : rdotZ c z = c.1 * (toReal z).1 + c.2 * (toReal z).2 := by simp [rdotZ, toReal]
    rw [h3]; linarith
  have hc0 : c ≠ 0 := by
    intro h
    obtain ⟨z, hz⟩ := hne
    have hlt := hsep z hz
    rw [h] at hlt
    simp only [rdotZ, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero] at hlt
    linarith
  obtain ⟨n₁, n₂, a, b, hE₁, hE₂, ha, hb, e1, e2, v, hvle, hv₁, hv₂⟩ := hframe c hc0
  have hvT : v ∈ T := hv₁.1
  have h₁ : (n₁.1 : ℝ) * x.1 + (n₁.2 : ℝ) * x.2 ≤ ((suppVal T n₁ : ℤ) : ℝ) :=
    Set.mem_iInter₂.mp hx n₁ hE₁
  have h₂ : (n₂.1 : ℝ) * x.1 + (n₂.2 : ℝ) * x.2 ≤ ((suppVal T n₂ : ℤ) : ℝ) :=
    Set.mem_iInter₂.mp hx n₂ hE₂
  rw [suppVal_eq hv₁] at h₁
  rw [suppVal_eq hv₂] at h₂
  have hvcomb : rdotZ c v = a * ((dot n₁ v : ℤ) : ℝ) + b * ((dot n₂ v : ℤ) : ℝ) := by
    simp only [rdotZ, dot, e1, e2]
    push_cast
    ring
  have hcontra := hsep v hvT
  rw [hvcomb, e1, e2] at hcontra
  nlinarith [mul_le_mul_of_nonneg_left h₁ ha, mul_le_mul_of_nonneg_left h₂ hb]

/-- **H-representation along any frame.** -/
theorem convHullOf_eq_iInter_frame {T N : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (hframe : IsFrame T N) :
    convHullOf T = ⋂ n ∈ N, realHalfPlaneLE n (suppVal T n) :=
  Set.Subset.antisymm (convHullOf_subset_iInter_frame hfin hne N)
    (iInter_subset_convHullOf_frame hne hframe)

/-- **The easy direction** for the edge normals. -/
theorem convHullOf_subset_iInter {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty) :
    convHullOf T ⊆ ⋂ n ∈ E T, realHalfPlaneLE n (suppVal T n) :=
  convHullOf_subset_iInter_frame hfin hne (E T)

/-- **The hard direction** for the edge normals. -/
theorem iInter_subset_convHullOf {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (harea : PosArea T) :
    ⋂ n ∈ E T, realHalfPlaneLE n (suppVal T n) ⊆ convHullOf T :=
  iInter_subset_convHullOf_frame hne (isFrame_E hfin hne harea)

/-- **H-representation of a planar lattice polygon.**  The closed convex hull of a finite
lattice set of positive area is cut out by the supporting half planes of its edges. -/
theorem convHullOf_eq_iInter_realHalfPlaneLE {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hne : T.Nonempty) (harea : PosArea T) :
    convHullOf T = ⋂ n ∈ E T, realHalfPlaneLE n (suppVal T n) :=
  convHullOf_eq_iInter_frame hfin hne (isFrame_E hfin hne harea)

/-- The same statement, with the half planes written out. -/
theorem convHullOf_eq_iInter_halfPlane {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (harea : PosArea T) :
    convHullOf T
      = ⋂ n ∈ E T,
          {x : ℝ × ℝ | (n.1 : ℝ) * x.1 + (n.2 : ℝ) * x.2 ≤ ((suppVal T n : ℤ) : ℝ)} :=
  convHullOf_eq_iInter_realHalfPlaneLE hfin hne harea

/-- **The lattice `⊇` direction.**  A lattice point obeying every edge inequality of a
lattice-convex region of positive area belongs to it. -/
theorem mem_of_dot_le_suppVal {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (harea : PosArea T) (hlc : IsLatticeConvexRegion T) {z : ℤ × ℤ}
    (h : ∀ n ∈ E T, dot n z ≤ suppVal T n) : z ∈ T := by
  rw [eq_preimage_convHullOf hlc]
  show toReal z ∈ convHullOf T
  refine iInter_subset_convHullOf hfin hne harea (Set.mem_iInter₂.mpr fun m hm => ?_)
  show (m.1 : ℝ) * (toReal z).1 + (m.2 : ℝ) * (toReal z).2 ≤ ((suppVal T m : ℤ) : ℝ)
  rw [dot_cast_toReal]
  exact_mod_cast h m hm

/-- The converse of `mem_of_dot_le_suppVal`: membership gives all the edge
inequalities. -/
theorem dot_le_suppVal_of_mem {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    {z : ℤ × ℤ} (hz : z ∈ T) : ∀ n ∈ E T, dot n z ≤ suppVal T n :=
  fun _n _ => le_suppVal hfin hne hz

/-! ### §10. Monotone unions with a common frame

Support values are **integers**, so a monotone sequence of them that is bounded above is
eventually constant.  This is what makes `⋃ i, convHullOf (T i)` closed for a monotone
family sharing a finite frame: it is the intersection of the half planes of the directions
whose support values stay bounded. -/

theorem convHullOf_subset_realHalfPlaneLE {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hne : T.Nonempty) (n : ℤ × ℤ) : convHullOf T ⊆ realHalfPlaneLE n (suppVal T n) :=
  fun _ hx => Set.mem_iInter₂.mp (convHullOf_subset_iInter_frame hfin hne {n} hx) n rfl

/-- **Closedness of a monotone union of hulls with a common finite frame.** -/
theorem isClosed_iUnion_convHullOf_of_frame {T : ℕ → Set (ℤ × ℤ)} {N : Set (ℤ × ℤ)}
    (hNfin : N.Finite) (hmono : ∀ i j, i ≤ j → T i ⊆ T j)
    (hfin : ∀ i, (T i).Finite) (hne : ∀ i, (T i).Nonempty)
    (hframe : ∀ i, IsFrame (T i) N) :
    IsClosed (⋃ i, convHullOf (T i)) := by
  classical
  have hsmono : ∀ n, ∀ i j, i ≤ j → suppVal (T i) n ≤ suppVal (T j) n := fun n i j hij =>
    suppVal_mono (hfin i) (hne i) (hfin j) (hne j) (hmono i j hij) n
  -- the eventual value of the support in a bounded direction
  have hstab : ∀ n : ℤ × ℤ, ∃ c : ℤ, (∃ M : ℤ, ∀ i, suppVal (T i) n ≤ M) →
      ∃ i₀, ∀ i, i₀ ≤ i → suppVal (T i) n = c := by
    intro n
    by_cases hB : ∃ M : ℤ, ∀ i, suppVal (T i) n ≤ M
    · obtain ⟨M, hM⟩ := hB
      obtain ⟨c, ⟨i₀, hi₀⟩, hgreatest⟩ :=
        Int.exists_greatest_of_bdd (P := fun c => ∃ i, suppVal (T i) n = c)
          ⟨M, fun z ⟨i, hi⟩ => hi ▸ hM i⟩ ⟨_, 0, rfl⟩
      refine ⟨c, fun _ => ⟨i₀, fun i hi => le_antisymm (hgreatest _ ⟨i, rfl⟩) ?_⟩⟩
      rw [← hi₀]; exact hsmono n i₀ i hi
    · exact ⟨0, fun h => absurd h hB⟩
  choose cval hcval using hstab
  set Bdd : Set (ℤ × ℤ) := {n ∈ N | ∃ M : ℤ, ∀ i, suppVal (T i) n ≤ M} with hBdddef
  have hkey : (⋃ i, convHullOf (T i)) = ⋂ n ∈ Bdd, realHalfPlaneLE n (cval n) := by
    apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun i => Set.subset_iInter₂ fun n hn => ?_
      obtain ⟨i₀, hi₀⟩ := hcval n hn.2
      intro x hx
      have hx' : (n.1 : ℝ) * x.1 + (n.2 : ℝ) * x.2 ≤ ((suppVal (T i) n : ℤ) : ℝ) :=
        convHullOf_subset_realHalfPlaneLE (hfin i) (hne i) n hx
      have hle : suppVal (T i) n ≤ cval n := by
        rw [← hi₀ (max i i₀) (le_max_right i i₀)]
        exact hsmono n i _ (le_max_left i i₀)
      show (n.1 : ℝ) * x.1 + (n.2 : ℝ) * x.2 ≤ ((cval n : ℤ) : ℝ)
      exact le_trans hx' (by exact_mod_cast hle)
    · intro x hx
      -- for each `n ∈ N`, an index whose support value dominates `⟪n, x⟫`
      have hidx : ∀ n : ℤ × ℤ, ∃ i : ℕ, n ∈ N →
          (n.1 : ℝ) * x.1 + (n.2 : ℝ) * x.2 ≤ ((suppVal (T i) n : ℤ) : ℝ) := by
        intro n
        by_cases hn : n ∈ N
        · by_cases hB : ∃ M : ℤ, ∀ i, suppVal (T i) n ≤ M
          · obtain ⟨i₀, hi₀⟩ := hcval n hB
            refine ⟨i₀, fun _ => ?_⟩
            rw [hi₀ i₀ le_rfl]
            exact Set.mem_iInter₂.mp hx n ⟨hn, hB⟩
          · push Not at hB
            obtain ⟨i, hi⟩ := hB ⌈(n.1 : ℝ) * x.1 + (n.2 : ℝ) * x.2⌉
            exact ⟨i, fun _ => le_trans (Int.le_ceil _) (by exact_mod_cast hi.le)⟩
        · exact ⟨0, fun h => absurd h hn⟩
      choose idx hidx using hidx
      set I : ℕ := hNfin.toFinset.sup idx with hIdef
      refine Set.mem_iUnion.mpr ⟨I, ?_⟩
      rw [convHullOf_eq_iInter_frame (hfin I) (hne I) (hframe I)]
      refine Set.mem_iInter₂.mpr fun n hn => ?_
      have hle : idx n ≤ I := Finset.le_sup (f := idx) (hNfin.mem_toFinset.mpr hn)
      show (n.1 : ℝ) * x.1 + (n.2 : ℝ) * x.2 ≤ ((suppVal (T I) n : ℤ) : ℝ)
      exact le_trans (hidx n hn) (by exact_mod_cast hsmono n _ _ hle)
  rw [hkey]
  exact isClosed_biInter fun n _ => realHalfPlaneLE_isClosed n _

/-! ### §11. Closing `isLatticeConvexRegion_iUnion_of_mono_fixedEdges_finite` -/

/-- Lattice-convexity of a monotone union of lattice-convex sets follows from closedness of
the union of their hulls (the convexity and the preimage identity are automatic). -/
theorem isLatticeConvexRegion_iUnion_of_isClosed {T : ℕ → Set (ℤ × ℤ)}
    (hmono : ∀ i j, i ≤ j → T i ⊆ T j) (hconv : ∀ i, IsLatticeConvexRegion (T i))
    (hclosed : IsClosed (⋃ i, convHullOf (T i))) :
    IsLatticeConvexRegion (⋃ i, T i) := by
  refine ⟨⋃ i, convHullOf (T i), ?_, hclosed, ?_⟩
  · intro x hx y hy α β hα hβ hsum
    rw [Set.mem_iUnion] at hx hy ⊢
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    have hmonoConv : ∀ m n, m ≤ n → convHullOf (T m) ⊆ convHullOf (T n) := fun m n hmn =>
      closure_mono (convexHull_mono (Set.image_mono (hmono m n hmn)))
    exact ⟨max i j, convex_convHullOf _ (hmonoConv i _ (le_max_left i j) hi)
      (hmonoConv j _ (le_max_right i j) hj) hα hβ hsum⟩
  · ext z
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [eq_preimage_convHullOf (hconv i)] at hi; exact hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [eq_preimage_convHullOf (hconv i)]; exact hi⟩

theorem isLatticeConvexRegion_empty : IsLatticeConvexRegion (∅ : Set (ℤ × ℤ)) :=
  ⟨∅, convex_empty, isClosed_empty, by simp⟩

theorem isLatticeConvexRegion_singleton (a : ℤ × ℤ) :
    IsLatticeConvexRegion ({a} : Set (ℤ × ℤ)) :=
  ⟨{toReal a}, convex_singleton _, isClosed_singleton, by
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact toReal_injective.eq_iff.symm⟩

/-- In the plane, a vector orthogonal to a non-zero `u` is orthogonal to everything
parallel to `u`. -/
theorem dot_eq_zero_of_dot_eq_zero_of_det_eq_zero {n u w : ℤ × ℤ} (hu : u ≠ 0)
    (hnu : dot n u = 0) (huw : det u w = 0) : dot n w = 0 := by
  have h1 : u.1 * dot n w = 0 := by
    simp only [dot, det] at hnu huw ⊢; linear_combination w.1 * hnu + n.2 * huw
  have h2 : u.2 * dot n w = 0 := by
    simp only [dot, det] at hnu huw ⊢; linear_combination w.2 * hnu - n.1 * huw
  rcases mul_eq_zero.mp h1 with h | h
  · rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd (by simp [Prod.ext_iff, h, h'] : u = 0) hu
    · exact h'
  · exact h

/-- Every edge normal of a collinear set is orthogonal to the direction of the line. -/
theorem dot_eq_zero_of_mem_E_of_collinear {T : Set (ℤ × ℤ)} {w : ℤ × ℤ}
    (hcol : ∀ z ∈ T, ∀ z' ∈ T, det (z - z') w = 0) {n : ℤ × ℤ} (hn : n ∈ E T) :
    dot n w = 0 := by
  obtain ⟨-, p, hp, q, hq, hpq⟩ := hn
  exact dot_eq_zero_of_dot_eq_zero_of_det_eq_zero (sub_ne_zero.mpr (Ne.symm hpq))
    (dot_sub_eq_zero_of_mem_face hp hq) (hcol q hq.1 p hp.1)

/-- A set without positive area is collinear along any chord. -/
theorem collinear_of_not_posArea {T : Set (ℤ × ℤ)} (hT : ¬ PosArea T) {a b : ℤ × ℤ}
    (ha : a ∈ T) (hb : b ∈ T) : ∀ z ∈ T, ∀ z' ∈ T, det (z - z') (b - a) = 0 := by
  intro z hz z' hz'
  have h1 : det (z - a) (b - a) = 0 := by
    by_contra h; exact hT ⟨a, ha, z, hz, b, hb, h⟩
  have h2 : det (z' - a) (b - a) = 0 := by
    by_contra h; exact hT ⟨a, ha, z', hz', b, hb, h⟩
  simp only [det, Prod.fst_sub, Prod.snd_sub] at h1 h2 ⊢
  linear_combination h1 - h2

/-- A positive-area set has an edge normal not orthogonal to any given non-zero vector. -/
theorem exists_mem_E_dot_ne_zero {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (harea : PosArea T) {w : ℤ × ℤ} (hw : w ≠ 0) : ∃ n ∈ E T, dot n w ≠ 0 := by
  have hc : toReal w ≠ 0 := by
    intro h
    apply hw
    apply toReal_injective
    rw [h]; simp [toReal, Prod.ext_iff]
  obtain ⟨n₁, n₂, a, b, hE₁, hE₂, -, -, e1, e2, -⟩ := exists_edge_cone hfin hne harea hc
  by_contra hcon
  push Not at hcon
  have h1 := hcon n₁ hE₁
  have h2 := hcon n₂ hE₂
  have hpos := rsq_pos hc
  simp only [toReal] at e1 e2 hpos
  have hcomb : (w.1 : ℝ) ^ 2 + (w.2 : ℝ) ^ 2 = a * (dot n₁ w : ℝ) + b * (dot n₂ w : ℝ) := by
    simp only [dot]; push_cast
    linear_combination (w.1 : ℝ) * e1 + (w.2 : ℝ) * e2
  rw [h1, h2] at hcomb
  simp only [Int.cast_zero, mul_zero, add_zero] at hcomb
  linarith

/-- **Monotone union of lattice-convex sets with fixed edge directions is lattice-convex.**
This is the strengthened form after `isLatticeConvexRegion_iUnion_of_mono` (which was false)
was withdrawn on 2026-09-16; see blueprint/NOTE.md for the triangle counterexample.
the constraint `hedge : ∀ i, E(T i) = E(S)`. The fixed edges prevent the "drift"
that makes the triangle counterexample fail.

This is the key lemma needed for `region_latticeConvex` (A3).

**2026-09-16: this signature is itself FALSE without finiteness.** See
`ConeCounterexample.lean` for the compiled refutation: cones
`T i = ℤ² ∩ {y ≥ (1 + √2/(i+1))|x|}` satisfy all hypotheses but the union
misses `(1,1)`, which any closed convex superset must contain. Every `T i` in that
counterexample is infinite, so the fix is to add `hfin : ∀ i, (T i).Finite` — done
below, renaming to `_finite`. The call site `RegionSteps.lean:825` supplies it via
`(c.shellFinite i 0).subset (c.subShell i 0)`.

**2026-09-16: proved.**  The `sorry` in the closedness step is closed by
`isClosed_iUnion_convHullOf_of_frame` (§10 above).  The cone counterexample cited above is
the exact reason the proof works in ℤ and not in ℝ: there the support values increase
strictly towards `√2`, whereas `suppVal` is an *integer*, so a monotone bounded support
sequence is eventually constant.  Finiteness enters only through that lemma. -/
theorem isLatticeConvexRegion_iUnion_of_mono_fixedEdges_finite
    {T : ℕ → Set (ℤ × ℤ)} {S : Set (ℤ × ℤ)}
    (hmono : ∀ i j, i ≤ j → T i ⊆ T j)
    (hconv : ∀ i, IsLatticeConvexRegion (T i))
    (hfin : ∀ i, (T i).Finite)
    (hedge : ∀ i, E (T i) = E S) :
    IsLatticeConvexRegion (⋃ i, T i) := by
  classical
  by_cases hsub : ∀ i, (T i).Subsingleton
  · -- degenerate: the union is empty or a single point
    have hU : (⋃ i, T i).Subsingleton := by
      intro x hx y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
      exact hsub (max i j) (hmono i _ (le_max_left i j) hi) (hmono j _ (le_max_right i j) hj)
    rcases hU.eq_empty_or_singleton with h | ⟨a, h⟩
    · rw [h]; exact isLatticeConvexRegion_empty
    · rw [h]; exact isLatticeConvexRegion_singleton a
  · obtain ⟨i₀, hi₀⟩ := not_forall.mp hsub
    rw [Set.not_subsingleton_iff] at hi₀
    obtain ⟨a, ha, b, hb, hab⟩ := hi₀
    -- reindex so that `a, b ∈ T' 0`
    set T' : ℕ → Set (ℤ × ℤ) := fun i => T (i₀ + i) with hT'def
    have hmono' : ∀ i j, i ≤ j → T' i ⊆ T' j := fun i j hij =>
      hmono (i₀ + i) (i₀ + j) (by omega)
    have hfin' : ∀ i, (T' i).Finite := fun i => hfin (i₀ + i)
    have hconv' : ∀ i, IsLatticeConvexRegion (T' i) := fun i => hconv (i₀ + i)
    have hedge' : ∀ i, E (T' i) = E S := fun i => hedge (i₀ + i)
    have hab' : ∀ i, a ∈ T' i ∧ b ∈ T' i := fun i =>
      ⟨hmono i₀ (i₀ + i) (by omega) ha, hmono i₀ (i₀ + i) (by omega) hb⟩
    have hne' : ∀ i, (T' i).Nonempty := fun i => ⟨a, (hab' i).1⟩
    have hUeq : (⋃ i, T i) = ⋃ i, T' i := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset fun i =>
          Set.subset_iUnion_of_subset i (hmono i (i₀ + i) (by omega))
      · exact Set.iUnion_subset fun i => Set.subset_iUnion T (i₀ + i)
    rw [hUeq]
    refine isLatticeConvexRegion_iUnion_of_isClosed hmono' hconv' ?_
    by_cases harea : PosArea (T' 0)
    · -- positive area: the edge normals `E S` form a common finite frame
      have hareaI : ∀ i, PosArea (T' i) := fun i => by
        obtain ⟨p, hp, q, hq, r, hr, hd⟩ := harea
        exact ⟨p, hmono' 0 i (Nat.zero_le i) hp, q, hmono' 0 i (Nat.zero_le i) hq,
          r, hmono' 0 i (Nat.zero_le i) hr, hd⟩
      refine isClosed_iUnion_convHullOf_of_frame (N := E S) ?_ hmono' hfin' hne' fun i => ?_
      · rw [← hedge' 0]; exact finite_E_of_finite (hfin' 0)
      · rw [← hedge' i]; exact isFrame_E (hfin' i) (hne' i) (hareaI i)
    · -- collinear: every `T' i` lies on the line through `a` and `b`
      have hw : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
      have hcol : ∀ i, ∀ z ∈ T' i, ∀ z' ∈ T' i, det (z - z') (b - a) = 0 := by
        intro i
        have hno : ¬ PosArea (T' i) := by
          intro hP
          obtain ⟨n, hn, hnw⟩ := exists_mem_E_dot_ne_zero (hfin' i) (hne' i) hP hw
          rw [hedge' i, ← hedge' 0] at hn
          exact hnw (dot_eq_zero_of_mem_E_of_collinear
            (collinear_of_not_posArea harea (hab' 0).1 (hab' 0).2) hn)
        exact collinear_of_not_posArea hno (hab' i).1 (hab' i).2
      exact isClosed_iUnion_convHullOf_of_frame
        (N := {b - a, -(b - a), nrmL (b - a), -nrmL (b - a)})
        (Set.toFinite _) hmono' hfin' hne' fun i => isFrame_collinear (hfin' i) (hne' i) hw (hcol i)

/-- **An `E(U)`-enveloped set has exactly the edge directions of `U`.**  This is the
first non-trivial consequence of Definition 3.2, and the reason the cardinality clause
`|E(𝒯)| = |E(𝒰)|` is there. -/
theorem Enveloped.E_eq {U T : Set (ℤ × ℤ)} (hU : (E U).Finite) (h : Enveloped U T) :
    E T = E U :=
  hU.eq_of_subset_of_encard_le' h.1.E_subset (le_of_eq h.2.symm)

/-- An `E(U)`-enveloped set has at least as many lattice points on *every* edge of `U`
(not merely on its own edges). -/
theorem Enveloped.face_encard_le {U T : Set (ℤ × ℤ)} (hU : (E U).Finite)
    (h : Enveloped U T) {n : ℤ × ℤ} (hn : n ∈ E U) :
    (face U n).encard ≤ (face T n).encard :=
  (h.1.2 n (by rw [h.E_eq hU]; exact hn)).2

theorem Enveloped.trans {U T W : Set (ℤ × ℤ)} (h : Enveloped U T) (h' : Enveloped T W) :
    Enveloped U W :=
  ⟨⟨h'.1.1, fun n hn => ⟨(h.1.2 n (h'.1.2 n hn).1).1,
      le_trans (h.1.2 n (h'.1.2 n hn).1).2 (h'.1.2 n hn).2⟩⟩,
    h'.2.trans h.2⟩

@[simp] theorem weaklyEnveloped_shift_right {U T : Set (ℤ × ℤ)} (v : ℤ × ℤ) :
    WeaklyEnveloped U (shift v T) ↔ WeaklyEnveloped U T := by
  simp only [WeaklyEnveloped, E_shift, face_shift, encard_shift]
  exact and_congr_left fun _ => isLatticeConvexRegion_shift_iff v

@[simp] theorem enveloped_shift_right {U T : Set (ℤ × ℤ)} (v : ℤ × ℤ) :
    Enveloped U (shift v T) ↔ Enveloped U T := by
  simp only [Enveloped, weaklyEnveloped_shift_right, E_shift]

@[simp] theorem enveloped_shift_left {U T : Set (ℤ × ℤ)} (v : ℤ × ℤ) :
    Enveloped (shift v U) T ↔ Enveloped U T := by
  constructor
  · intro ⟨⟨hconv, hedge⟩, hcard⟩
    refine ⟨⟨hconv, ?_⟩, ?_⟩
    · intro n hn
      have := hedge n hn
      simp only [E_shift, face_shift, encard_shift] at this
      exact this
    · rwa [E_shift] at hcard
  · intro ⟨⟨hconv, hedge⟩, hcard⟩
    refine ⟨⟨hconv, ?_⟩, ?_⟩
    · intro n hn
      have := hedge n hn
      simp only [E_shift, face_shift, encard_shift]
      exact this
    · rwa [E_shift]

/-- If `u` is parallel to a non-zero `v` and `m ⟂ v`, then `m ⟂ u`. -/
theorem dot_eq_zero_of_det_eq_zero {u v m : ℤ × ℤ} (hv : v ≠ 0) (h : det u v = 0)
    (hm : dot v m = 0) : dot u m = 0 := by
  simp only [det] at h
  simp only [dot] at hm ⊢
  have h1 : (u.1 * m.1 + u.2 * m.2) * v.1 = 0 := by linear_combination u.1 * hm - m.2 * h
  have h2 : (u.1 * m.1 + u.2 * m.2) * v.2 = 0 := by linear_combination u.2 * hm + m.1 * h
  rcases mul_eq_zero.mp h1 with h' | h'
  · exact h'
  · rcases mul_eq_zero.mp h2 with h'' | h''
    · exact h''
    · exact absurd (show v = (0 : ℤ × ℤ) by simp [Prod.ext_iff, h', h'']) hv

theorem det_sub_right (u v w : ℤ × ℤ) : det u (v - w) = det u v - det u w := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

/-- **Two edges in genuinely different directions force positive area.** -/
theorem posArea_of_edges {R : Set (ℤ × ℤ)} {n m : ℤ × ℤ} (hn : n ∈ E R) (hm : m ∈ E R)
    (hne : m ≠ n) (hne' : m ≠ -n) : PosArea R := by
  by_contra hR
  simp only [PosArea, not_exists, not_and] at hR
  obtain ⟨a, ha, b, hb, hab⟩ := hn.2
  obtain ⟨c, hc, d, hd, hcd⟩ := hm.2
  have hd1 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hz1 : det (b - a) (c - a) = 0 := by
    by_contra hcon; exact hcon (by
      have := hR a ha.1 b hb.1 c hc.1; simpa using this)
  have hz2 : det (b - a) (d - a) = 0 := by
    by_contra hcon; exact hcon (by
      have := hR a ha.1 b hb.1 d hd.1; simpa using this)
  have hz3 : det (b - a) (d - c) = 0 := by
    have : d - c = (d - a) - (c - a) := by abel
    rw [this, det_sub_right, hz1, hz2, sub_zero]
  have hdn : dot (b - a) n = 0 := by
    rw [← dot_comm]; exact dot_sub_eq_zero_of_mem_face ha hb
  have hdm : dot (d - c) m = 0 := by
    rw [← dot_comm]; exact dot_sub_eq_zero_of_mem_face hc hd
  have hdn' : dot (d - c) n = 0 :=
    dot_eq_zero_of_det_eq_zero hd1 (by rw [det_comm, hz3, neg_zero]) hdn
  have hd2 : d - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hcd)
  have hdet : det n m = 0 := det_eq_zero_of_dot_eq_zero hd2 hdn' hdm
  rcases eq_or_neg_of_prim_of_det_eq_zero hn.1 hm.1 hdet with h | h
  · exact hne h
  · exact hne' h

/-- **Three edges force positive area**, so an `E(U)`-enveloped set of a `U` with at
least three edges automatically has positive area. -/
theorem posArea_of_three_edges {R : Set (ℤ × ℤ)} {n m k : ℤ × ℤ} (hn : n ∈ E R)
    (hm : m ∈ E R) (hk : k ∈ E R) (h1 : n ≠ m) (h2 : n ≠ k) (h3 : m ≠ k) : PosArea R := by
  by_cases hc : m = -n
  · exact posArea_of_edges hn hk (Ne.symm h2) (by rw [← hc]; exact Ne.symm h3)
  · exact posArea_of_edges hn hm (Ne.symm h1) hc

/-! ## §7. Half-planes, the line `ℓ^{(-)}`, half-strips and strips -/

/-- The half-plane `{⟨n, ·⟩ ≤ c}` (outer-normal convention of this file). -/
def halfPlaneLE (n : ℤ × ℤ) (c : ℤ) : Set (ℤ × ℤ) := {z | dot n z ≤ c}

/-- **Colle's `ℋ(ℓ)`**: with `n` the inner normal of `ℓ` and `c` its level,
`ℋ(ℓ) = {⟨n, ·⟩ ≥ c}`.  The interior is on the left of `ℓ`. -/
def halfPlaneGE (n : ℤ × ℤ) (c : ℤ) : Set (ℤ × ℤ) := {z | c ≤ dot n z}

/-- The sign dictionary for half-planes. -/
theorem halfPlaneGE_eq_halfPlaneLE_neg (n : ℤ × ℤ) (c : ℤ) :
    halfPlaneGE n c = halfPlaneLE (-n) (-c) := by
  ext z
  simp only [halfPlaneGE, halfPlaneLE, Set.mem_ofPred_eq, dot_neg_left]
  omega

/-- For a primitive `n` the form `⟨n, ·⟩` hits every integer. -/
theorem dot_surjective {n : ℤ × ℤ} (hn : Prim n) : Function.Surjective (dot n) := by
  have hv : Primitive (n.2, -n.1) := (prim_iff_primitive.mp hn).symm.neg_right
  intro c
  obtain ⟨z, hz⟩ := pi_surjective hv c
  refine ⟨z, ?_⟩
  rw [← hz]
  simp only [pi, det, dot]
  ring

/-- **Colle, Notation 3.3.**  For `ℓ = {⟨n,·⟩ = c}` bounding `ℋ(ℓ) = {⟨n,·⟩ ≥ c}` with
`n` primitive, `ℓ^{(-)}` is the lattice line `{⟨n,·⟩ = c - 1}`. -/
def outerLine (n : ℤ × ℤ) (c : ℤ) : Set (ℤ × ℤ) := {z | dot n z = c - 1}

theorem outerLine_nonempty {n : ℤ × ℤ} (hn : Prim n) (c : ℤ) : (outerLine n c).Nonempty :=
  dot_surjective hn (c - 1)

theorem outerLine_disjoint (n : ℤ × ℤ) (c : ℤ) :
    Disjoint (outerLine n c) (halfPlaneGE n c) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  simp only [outerLine, Set.mem_ofPred_eq] at hz
  simp only [halfPlaneGE, Set.mem_ofPred_eq] at hz'
  omega

/-- `ℓ^{(-)}` is the **closest** such line: any parallel lattice line disjoint from
`ℋ(ℓ)` sits at level `≤ c - 1`. -/
theorem outerLine_closest {n : ℤ × ℤ} {c d : ℤ}
    (hdis : Disjoint ({z : ℤ × ℤ | dot n z = d}) (halfPlaneGE n c))
    (hne : ({z : ℤ × ℤ | dot n z = d}).Nonempty) : d ≤ c - 1 := by
  obtain ⟨z, hz⟩ := hne
  simp only [Set.mem_ofPred_eq] at hz
  by_contra h
  exact Set.disjoint_left.mp hdis (by simpa using hz) (by
    simp only [halfPlaneGE, Set.mem_ofPred_eq]; omega)

/-- **Colle, Definition 3.4.**  The half-strip `H_B(ℓ) = {g + t·v : g ∈ B, t ∈ ℤ₊}`.
This is deliberately character-for-character the same definition as
`Nivat.Colle35.halfStrip` (`Nivat/External/Colle/Lemma35.lean`, line 402), so the two
can be identified by `rfl` once the files are joined. -/
def halfStrip (B : Set (ℤ × ℤ)) (v : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {g | ∃ b ∈ B, ∃ t : ℕ, g = b + (t : ℤ) • v}

theorem subset_halfStrip (B : Set (ℤ × ℤ)) (v : ℤ × ℤ) : B ⊆ halfStrip B v :=
  fun b hb => ⟨b, hb, 0, by simp⟩

/-- **Colle, §3** (proof of Claim 3.6).  The strip `St_B(ℓ) := H_B(ℓ) ∪ H_B(-ℓ)`. -/
def strip (B : Set (ℤ × ℤ)) (v : ℤ × ℤ) : Set (ℤ × ℤ) :=
  halfStrip B v ∪ halfStrip B (-v)

theorem halfStrip_subset_strip (B : Set (ℤ × ℤ)) (v : ℤ × ℤ) :
    halfStrip B v ⊆ strip B v := Set.subset_union_left

theorem subset_strip (B : Set (ℤ × ℤ)) (v : ℤ × ℤ) : B ⊆ strip B v :=
  (subset_halfStrip B v).trans (halfStrip_subset_strip B v)

theorem strip_neg (B : Set (ℤ × ℤ)) (v : ℤ × ℤ) : strip B (-v) = strip B v := by
  simp only [strip, neg_neg]
  exact Set.union_comm _ _

/-- The strip is the full two-sided translate family: `St_B(ℓ) = {g + t·v : g ∈ B, t ∈ ℤ}`. -/
theorem strip_eq (B : Set (ℤ × ℤ)) (v : ℤ × ℤ) :
    strip B v = {g | ∃ b ∈ B, ∃ t : ℤ, g = b + t • v} := by
  ext g
  constructor
  · rintro (⟨b, hb, t, rfl⟩ | ⟨b, hb, t, rfl⟩)
    · exact ⟨b, hb, (t : ℤ), rfl⟩
    · exact ⟨b, hb, -(t : ℤ), by rw [neg_smul, smul_neg]⟩
  · rintro ⟨b, hb, t, rfl⟩
    rcases le_or_gt 0 t with ht | ht
    · exact Or.inl ⟨b, hb, t.toNat, by rw [Int.toNat_of_nonneg ht]⟩
    · refine Or.inr ⟨b, hb, (-t).toNat, ?_⟩
      rw [Int.toNat_of_nonneg (by omega), smul_neg, ← neg_smul, neg_neg]

/-! ## §8. Non-degenerate concrete instances: lattice boxes

Everything below is a *check that the definitions are not vacuous*.  The witnesses
are genuine lattice polygons with four edges and positive area; degenerate witnesses
(points, segments, the empty set) are deliberately avoided. -/

/-- The lattice box `[p₁,q₁] × [p₂,q₂]`. -/
def box (p q : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {z | p.1 ≤ z.1 ∧ z.1 ≤ q.1 ∧ p.2 ≤ z.2 ∧ z.2 ≤ q.2}

theorem mem_box {p q z : ℤ × ℤ} :
    z ∈ box p q ↔ p.1 ≤ z.1 ∧ z.1 ≤ q.1 ∧ p.2 ≤ z.2 ∧ z.2 ≤ q.2 := Iff.rfl

@[simp] theorem dot_e1 (z : ℤ × ℤ) : dot (1, 0) z = z.1 := by simp [dot]

@[simp] theorem dot_e1' (z : ℤ × ℤ) : dot (-1, 0) z = -z.1 := by simp [dot]

@[simp] theorem dot_e2 (z : ℤ × ℤ) : dot (0, 1) z = z.2 := by simp [dot]

@[simp] theorem dot_e2' (z : ℤ × ℤ) : dot (0, -1) z = -z.2 := by simp [dot]

/-- The endpoint of `[lo,hi]` that maximises `a * ·`. -/
def endp (a lo hi : ℤ) : ℤ := if 0 < a then hi else lo

theorem endp_mem {a lo hi : ℤ} (h : lo ≤ hi) : lo ≤ endp a lo hi ∧ endp a lo hi ≤ hi := by
  unfold endp; split <;> omega

theorem mul_le_endp (a : ℤ) {lo hi x : ℤ} (h1 : lo ≤ x) (h2 : x ≤ hi) :
    a * x ≤ a * endp a lo hi := by
  unfold endp
  by_cases h : 0 < a
  · rw [if_pos h]; nlinarith
  · rw [if_neg h]
    have ha : a ≤ 0 := by omega
    nlinarith

theorem face_box_right {p q : ℤ × ℤ} (hp : p.1 ≤ q.1) :
    face (box p q) (1, 0) = {z | z.1 = q.1 ∧ p.2 ≤ z.2 ∧ z.2 ≤ q.2} := by
  ext z
  constructor
  · rintro ⟨⟨a1, a2, a3, a4⟩, hm⟩
    have h := hm (q.1, z.2) ⟨hp, le_refl _, a3, a4⟩
    simp only [dot_e1] at h
    exact ⟨le_antisymm a2 h, a3, a4⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨by omega, by omega, h2, h3⟩, ?_⟩
    rintro y ⟨b1, b2, b3, b4⟩
    simp only [dot_e1]
    omega

theorem face_box_left {p q : ℤ × ℤ} (hp : p.1 ≤ q.1) :
    face (box p q) (-1, 0) = {z | z.1 = p.1 ∧ p.2 ≤ z.2 ∧ z.2 ≤ q.2} := by
  ext z
  constructor
  · rintro ⟨⟨a1, a2, a3, a4⟩, hm⟩
    have h := hm (p.1, z.2) ⟨le_refl _, hp, a3, a4⟩
    simp only [dot_e1'] at h
    exact ⟨le_antisymm (by omega) a1, a3, a4⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨by omega, by omega, h2, h3⟩, ?_⟩
    rintro y ⟨b1, b2, b3, b4⟩
    simp only [dot_e1']
    omega

theorem face_box_top {p q : ℤ × ℤ} (hq : p.2 ≤ q.2) :
    face (box p q) (0, 1) = {z | p.1 ≤ z.1 ∧ z.1 ≤ q.1 ∧ z.2 = q.2} := by
  ext z
  constructor
  · rintro ⟨⟨a1, a2, a3, a4⟩, hm⟩
    have h := hm (z.1, q.2) ⟨a1, a2, hq, le_refl _⟩
    simp only [dot_e2] at h
    exact ⟨a1, a2, le_antisymm a4 h⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2, by omega, by omega⟩, ?_⟩
    rintro y ⟨b1, b2, b3, b4⟩
    simp only [dot_e2]
    omega

theorem face_box_bot {p q : ℤ × ℤ} (hq : p.2 ≤ q.2) :
    face (box p q) (0, -1) = {z | p.1 ≤ z.1 ∧ z.1 ≤ q.1 ∧ z.2 = p.2} := by
  ext z
  constructor
  · rintro ⟨⟨a1, a2, a3, a4⟩, hm⟩
    have h := hm (z.1, p.2) ⟨a1, a2, le_refl _, hq⟩
    simp only [dot_e2'] at h
    exact ⟨a1, a2, le_antisymm (by omega) a3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2, by omega, by omega⟩, ?_⟩
    rintro y ⟨b1, b2, b3, b4⟩
    simp only [dot_e2']
    omega

/-- In every direction that is not axis-parallel, the box exposes a single corner —
hence has no edge there. -/
theorem face_box_of_ne_zero {p q : ℤ × ℤ} (hp : p.1 ≤ q.1) (hq : p.2 ≤ q.2) {n : ℤ × ℤ}
    (h1 : n.1 ≠ 0) (h2 : n.2 ≠ 0) :
    face (box p q) n = {(endp n.1 p.1 q.1, endp n.2 p.2 q.2)} := by
  have hC : (endp n.1 p.1 q.1, endp n.2 p.2 q.2) ∈ box p q :=
    ⟨(endp_mem hp).1, (endp_mem hp).2, (endp_mem hq).1, (endp_mem hq).2⟩
  have hmax : ∀ z ∈ box p q, dot n z ≤ dot n (endp n.1 p.1 q.1, endp n.2 p.2 q.2) := by
    rintro z ⟨a1, a2, a3, a4⟩
    simp only [dot]
    exact add_le_add (mul_le_endp n.1 a1 a2) (mul_le_endp n.2 a3 a4)
  ext z
  constructor
  · rintro ⟨hz, hzm⟩
    have hle := hmax z hz
    have hge := hzm _ hC
    obtain ⟨a1, a2, a3, a4⟩ := hz
    have e1 := mul_le_endp n.1 a1 a2
    have e2 := mul_le_endp n.2 a3 a4
    simp only [dot] at hle hge
    have f1 : n.1 * z.1 = n.1 * endp n.1 p.1 q.1 := by linarith
    have f2 : n.2 * z.2 = n.2 * endp n.2 p.2 q.2 := by linarith
    exact Prod.ext (mul_left_cancel₀ h1 f1) (mul_left_cancel₀ h2 f2)
  · rintro rfl
    exact ⟨hC, hmax⟩

/-- **A box with positive area has exactly four edges.** -/
theorem E_box {p q : ℤ × ℤ} (hp : p.1 < q.1) (hq : p.2 < q.2) :
    E (box p q) = {(1, 0), (-1, 0), (0, 1), (0, -1)} := by
  ext n
  constructor
  · rintro ⟨hprim, hnt⟩
    by_cases h1 : n.1 = 0
    · rcases prim_eq_of_fst_eq_zero hprim h1 with rfl | rfl <;> simp
    · by_cases h2 : n.2 = 0
      · rcases prim_eq_of_snd_eq_zero hprim h2 with rfl | rfl <;> simp
      · exfalso
        rw [face_box_of_ne_zero hp.le hq.le h1 h2] at hnt
        exact Set.not_nontrivial_singleton hnt
  · rintro (rfl | rfl | rfl | rfl)
    · refine ⟨by decide, ?_⟩
      rw [face_box_right hp.le]
      exact ⟨(q.1, p.2), ⟨rfl, le_refl _, hq.le⟩, (q.1, q.2), ⟨rfl, hq.le, le_refl _⟩,
        by intro h; rw [Prod.ext_iff] at h; omega⟩
    · refine ⟨by decide, ?_⟩
      rw [face_box_left hp.le]
      exact ⟨(p.1, p.2), ⟨rfl, le_refl _, hq.le⟩, (p.1, q.2), ⟨rfl, hq.le, le_refl _⟩,
        by intro h; rw [Prod.ext_iff] at h; omega⟩
    · refine ⟨by decide, ?_⟩
      rw [face_box_top hq.le]
      exact ⟨(p.1, q.2), ⟨le_refl _, hp.le, rfl⟩, (q.1, q.2), ⟨hp.le, le_refl _, rfl⟩,
        by intro h; rw [Prod.ext_iff] at h; omega⟩
    · refine ⟨by decide, ?_⟩
      rw [face_box_bot hq.le]
      exact ⟨(p.1, p.2), ⟨le_refl _, hp.le, rfl⟩, (q.1, p.2), ⟨hp.le, le_refl _, rfl⟩,
        by intro h; rw [Prod.ext_iff] at h; omega⟩

theorem two_le_encard_of_pair {A : Set (ℤ × ℤ)} {a b : ℤ × ℤ} (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) : 2 ≤ A.encard := by
  rw [← Set.encard_pair hab]
  exact Set.encard_mono (by rintro x (rfl | rfl); exacts [ha, hb])

/-- The unit square `[0,1]²`: four edges, each carrying exactly two lattice points. -/
def sq1 : Set (ℤ × ℤ) := box (0, 0) (1, 1)

/-- The square `[0,2]²`: four edges, each carrying three lattice points. -/
def sq2 : Set (ℤ × ℤ) := box (0, 0) (2, 2)

theorem E_sq1 : E sq1 = {(1, 0), (-1, 0), (0, 1), (0, -1)} := E_box (by norm_num) (by norm_num)

theorem E_sq2 : E sq2 = {(1, 0), (-1, 0), (0, 1), (0, -1)} := E_box (by norm_num) (by norm_num)

/-- `[0,1]²` really is a lattice polygon of positive area: it has four distinct edges. -/
theorem posArea_sq1 : PosArea sq1 :=
  posArea_of_three_edges (n := (1, 0)) (m := (-1, 0)) (k := (0, 1))
    (by rw [E_sq1]; simp) (by rw [E_sq1]; simp) (by rw [E_sq1]; simp)
    (by decide) (by decide) (by decide)

theorem posArea_sq2 : PosArea sq2 :=
  posArea_of_three_edges (n := (1, 0)) (m := (-1, 0)) (k := (0, 1))
    (by rw [E_sq2]; simp) (by rw [E_sq2]; simp) (by rw [E_sq2]; simp)
    (by decide) (by decide) (by decide)

/-- A corner of `[0,1]²` is a vertex in the sense of `IsVtx`. -/
theorem isVtx_sq1 : IsVtx sq1 ((1 : ℤ), (1 : ℤ)) := by
  refine ⟨(1, 1), by decide, ?_⟩
  rw [sq1, face_box_of_ne_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [endp]

theorem encard_face_sq1_right : (face sq1 (1, 0)).encard = 2 := by
  rw [sq1, face_box_right (by norm_num)]
  have : {z : ℤ × ℤ | z.1 = ((1 : ℤ), (1 : ℤ)).1 ∧ ((0 : ℤ), (0 : ℤ)).2 ≤ z.2 ∧
      z.2 ≤ ((1 : ℤ), (1 : ℤ)).2} = {((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (1 : ℤ))} := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩
      have : z.2 = 0 ∨ z.2 = 1 := by simp only at h2 h3; omega
      rcases this with h | h
      · exact Or.inl (Prod.ext h1 h)
      · exact Or.inr (Prod.ext h1 h)
    · rintro (rfl | rfl) <;> exact ⟨rfl, by norm_num, by norm_num⟩
  rw [this]
  exact Set.encard_pair (by decide)

theorem encard_face_sq1_left : (face sq1 (-1, 0)).encard = 2 := by
  rw [sq1, face_box_left (by norm_num)]
  have : {z : ℤ × ℤ | z.1 = ((0 : ℤ), (0 : ℤ)).1 ∧ ((0 : ℤ), (0 : ℤ)).2 ≤ z.2 ∧
      z.2 ≤ ((1 : ℤ), (1 : ℤ)).2} = {((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))} := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩
      have : z.2 = 0 ∨ z.2 = 1 := by simp only at h2 h3; omega
      rcases this with h | h
      · exact Or.inl (Prod.ext h1 h)
      · exact Or.inr (Prod.ext h1 h)
    · rintro (rfl | rfl) <;> exact ⟨rfl, by norm_num, by norm_num⟩
  rw [this]
  exact Set.encard_pair (by decide)

theorem encard_face_sq1_top : (face sq1 (0, 1)).encard = 2 := by
  rw [sq1, face_box_top (by norm_num)]
  have : {z : ℤ × ℤ | ((0 : ℤ), (0 : ℤ)).1 ≤ z.1 ∧ z.1 ≤ ((1 : ℤ), (1 : ℤ)).1 ∧
      z.2 = ((1 : ℤ), (1 : ℤ)).2} = {((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (1 : ℤ))} := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩
      have : z.1 = 0 ∨ z.1 = 1 := by simp only at h1 h2; omega
      rcases this with h | h
      · exact Or.inl (Prod.ext h h3)
      · exact Or.inr (Prod.ext h h3)
    · rintro (rfl | rfl) <;> exact ⟨by norm_num, by norm_num, rfl⟩
  rw [this]
  exact Set.encard_pair (by decide)

theorem encard_face_sq1_bot : (face sq1 (0, -1)).encard = 2 := by
  rw [sq1, face_box_bot (by norm_num)]
  have : {z : ℤ × ℤ | ((0 : ℤ), (0 : ℤ)).1 ≤ z.1 ∧ z.1 ≤ ((1 : ℤ), (1 : ℤ)).1 ∧
      z.2 = ((0 : ℤ), (0 : ℤ)).2} = {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩
      have : z.1 = 0 ∨ z.1 = 1 := by simp only at h1 h2; omega
      rcases this with h | h
      · exact Or.inl (Prod.ext h h3)
      · exact Or.inr (Prod.ext h h3)
    · rintro (rfl | rfl) <;> exact ⟨by norm_num, by norm_num, rfl⟩
  rw [this]
  exact Set.encard_pair (by decide)

theorem two_le_face_sq2_right : 2 ≤ (face sq2 (1, 0)).encard := by
  rw [sq2, face_box_right (by norm_num)]
  exact two_le_encard_of_pair (a := ((2 : ℤ), (0 : ℤ))) (b := ((2 : ℤ), (1 : ℤ)))
    ⟨rfl, by norm_num, by norm_num⟩ ⟨rfl, by norm_num, by norm_num⟩ (by decide)

theorem two_le_face_sq2_left : 2 ≤ (face sq2 (-1, 0)).encard := by
  rw [sq2, face_box_left (by norm_num)]
  exact two_le_encard_of_pair (a := ((0 : ℤ), (0 : ℤ))) (b := ((0 : ℤ), (1 : ℤ)))
    ⟨rfl, by norm_num, by norm_num⟩ ⟨rfl, by norm_num, by norm_num⟩ (by decide)

theorem two_le_face_sq2_top : 2 ≤ (face sq2 (0, 1)).encard := by
  rw [sq2, face_box_top (by norm_num)]
  exact two_le_encard_of_pair (a := ((0 : ℤ), (2 : ℤ))) (b := ((1 : ℤ), (2 : ℤ)))
    ⟨by norm_num, by norm_num, rfl⟩ ⟨by norm_num, by norm_num, rfl⟩ (by decide)

theorem two_le_face_sq2_bot : 2 ≤ (face sq2 (0, -1)).encard := by
  rw [sq2, face_box_bot (by norm_num)]
  exact two_le_encard_of_pair (a := ((0 : ℤ), (0 : ℤ))) (b := ((1 : ℤ), (0 : ℤ)))
    ⟨by norm_num, by norm_num, rfl⟩ ⟨by norm_num, by norm_num, rfl⟩ (by decide)

/-- **Every box is lattice-convex.** -/
theorem isLatticeConvexRegion_box (p q : ℤ × ℤ) : IsLatticeConvexRegion (box p q) := by
  refine ⟨Set.Icc (toReal p) (toReal q), ?_, ?_, ?_⟩
  · intro x hx y hy α β hα hβ hsum
    simp only [Set.mem_Icc, toReal] at hx hy ⊢
    obtain ⟨⟨hxp1, hxp2⟩, ⟨hxq1, hxq2⟩⟩ := hx
    obtain ⟨⟨hyp1, hyp2⟩, ⟨hyq1, hyq2⟩⟩ := hy
    constructor
    · constructor
      · have : α * x.1 + β * y.1 ≥ α * (p.1 : ℝ) + β * (p.1 : ℝ) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hxp1 hα
          · exact mul_le_mul_of_nonneg_left hyp1 hβ
        calc α • x.1 + β • y.1 = α * x.1 + β * y.1 := by rfl
          _ ≥ α * (p.1 : ℝ) + β * (p.1 : ℝ) := this
          _ = (α + β) * (p.1 : ℝ) := by ring
          _ = (p.1 : ℝ) := by rw [hsum]; ring
      · have : α * x.2 + β * y.2 ≥ α * (p.2 : ℝ) + β * (p.2 : ℝ) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hxp2 hα
          · exact mul_le_mul_of_nonneg_left hyp2 hβ
        calc α • x.2 + β • y.2 = α * x.2 + β * y.2 := by rfl
          _ ≥ α * (p.2 : ℝ) + β * (p.2 : ℝ) := this
          _ = (α + β) * (p.2 : ℝ) := by ring
          _ = (p.2 : ℝ) := by rw [hsum]; ring
    · constructor
      · have : α * x.1 + β * y.1 ≤ α * (q.1 : ℝ) + β * (q.1 : ℝ) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hxq1 hα
          · exact mul_le_mul_of_nonneg_left hyq1 hβ
        calc α • x.1 + β • y.1 = α * x.1 + β * y.1 := by rfl
          _ ≤ α * (q.1 : ℝ) + β * (q.1 : ℝ) := this
          _ = (α + β) * (q.1 : ℝ) := by ring
          _ = (q.1 : ℝ) := by rw [hsum]; ring
      · have : α * x.2 + β * y.2 ≤ α * (q.2 : ℝ) + β * (q.2 : ℝ) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hxq2 hα
          · exact mul_le_mul_of_nonneg_left hyq2 hβ
        calc α • x.2 + β • y.2 = α * x.2 + β * y.2 := by rfl
          _ ≤ α * (q.2 : ℝ) + β * (q.2 : ℝ) := this
          _ = (α + β) * (q.2 : ℝ) := by ring
          _ = (q.2 : ℝ) := by rw [hsum]; ring
  · exact isClosed_Icc
  · ext z
    simp only [Set.mem_preimage, toReal, Set.mem_Icc, mem_box]
    constructor
    · intro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨Int.cast_le.mpr h1, Int.cast_le.mpr h3⟩,
             ⟨Int.cast_le.mpr h2, Int.cast_le.mpr h4⟩⟩
    · intro ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
      exact ⟨Int.cast_le.mp h1, Int.cast_le.mp h2,
             Int.cast_le.mp h3, Int.cast_le.mp h4⟩

theorem isLatticeConvexRegion_sq1 : IsLatticeConvexRegion sq1 :=
  isLatticeConvexRegion_box (0, 0) (1, 1)

theorem isLatticeConvexRegion_sq2 : IsLatticeConvexRegion sq2 :=
  isLatticeConvexRegion_box (0, 0) (2, 2)

/-- **Non-degeneracy check for `Enveloped`.**  The square `[0,2]²` is
`E([0,1]²)`-enveloped: both are genuine lattice polygons with four edges and positive
area, and each edge of `[0,1]²` carries `2 ≤ 3` lattice points. -/
theorem enveloped_sq : Enveloped sq1 sq2 := by
  constructor
  · constructor
    · exact isLatticeConvexRegion_sq2
    · intro n hn
      rw [E_sq2] at hn
      have hE : E sq1 = {(1, 0), (-1, 0), (0, 1), (0, -1)} := E_sq1
      rcases hn with rfl | rfl | rfl | rfl
      · exact ⟨by rw [hE]; simp, by rw [encard_face_sq1_right]; exact two_le_face_sq2_right⟩
      · exact ⟨by rw [hE]; simp, by rw [encard_face_sq1_left]; exact two_le_face_sq2_left⟩
      · exact ⟨by rw [hE]; simp, by rw [encard_face_sq1_top]; exact two_le_face_sq2_top⟩
      · exact ⟨by rw [hE]; simp, by rw [encard_face_sq1_bot]; exact two_le_face_sq2_bot⟩
  · rw [E_sq1, E_sq2]

/-- The envelope relation is not trivial in the other direction: `[0,1]²` is **not**
`E([0,2]²)`-enveloped, because its edges are too short. -/
theorem not_enveloped_sq : ¬ Enveloped sq2 sq1 := by
  intro h
  have h1 := (h.1.2 (1, 0) (by rw [E_sq1]; simp)).2
  rw [encard_face_sq1_right] at h1
  have h2 : (face sq2 (1, 0)).encard = 3 := by
    rw [sq2, face_box_right (by norm_num)]
    have : {z : ℤ × ℤ | z.1 = ((2 : ℤ), (2 : ℤ)).1 ∧ ((0 : ℤ), (0 : ℤ)).2 ≤ z.2 ∧
        z.2 ≤ ((2 : ℤ), (2 : ℤ)).2} =
        {((2 : ℤ), (0 : ℤ)), ((2 : ℤ), (1 : ℤ)), ((2 : ℤ), (2 : ℤ))} := by
      ext z
      constructor
      · rintro ⟨ha, hb, hc⟩
        have : z.2 = 0 ∨ z.2 = 1 ∨ z.2 = 2 := by simp only at hb hc; omega
        rcases this with h | h | h
        · exact Or.inl (Prod.ext ha h)
        · exact Or.inr (Or.inl (Prod.ext ha h))
        · exact Or.inr (Or.inr (Prod.ext ha h))
      · rintro (rfl | rfl | rfl) <;> exact ⟨rfl, by norm_num, by norm_num⟩
    rw [this, Set.encard_insert_of_notMem (by decide), Set.encard_pair (by decide)]
    rfl
  rw [h2] at h1
  exact absurd h1 (by decide)

/-! ## §9. Infinite regions and semi-infinite edges (Colle, Definition 3.1)

*"Let `ℓ, ℓ′` be two distinct support lines.  An `(ℓ,ℓ′)`-region is an infinite convex
set `ℛ ⊂ ℤ²` which has exactly two semi-infinite edges `w, w′`, parallel to `ℓ` and
`ℓ′` respectively, such that with respect to the positive orientation of the boundary
of `ℛ` one has `w ≺ ⋯ ≺ w′`."* -/

/-- An edge is **semi-infinite** when it carries infinitely many lattice points. -/
def IsSemiInfEdge (R : Set (ℤ × ℤ)) (n : ℤ × ℤ) : Prop := n ∈ E R ∧ (face R n).Infinite

theorem IsSemiInfEdge.mem_E {R : Set (ℤ × ℤ)} {n : ℤ × ℤ} (h : IsSemiInfEdge R n) :
    n ∈ E R := h.1

/-- **Colle, Definition 3.1.**  `R` is an `(n, n')`-region, where the two support lines
are named by the primitive outer normals `n`, `n'` of their edges. -/
structure IsRegion (R : Set (ℤ × ℤ)) (n n' : ℤ × ℤ) : Prop where
  /-- `R` is the set of lattice points of a closed convex subset of `ℝ²`. -/
  latticeConvex : IsLatticeConvexRegion R
  /-- `R` is infinite. -/
  infinite : R.Infinite
  /-- `conv(R)` has positive area, so `R` is not contained in a line. -/
  posArea : PosArea R
  /-- `R` has finitely many edges. -/
  edgesFinite : (E R).Finite
  /-- `n` is a semi-infinite edge. -/
  semiInf : IsSemiInfEdge R n
  /-- `n'` is a semi-infinite edge. -/
  semiInf' : IsSemiInfEdge R n'
  /-- …and there are no others: *exactly* two semi-infinite edges. -/
  semiInfUnique : ∀ m, IsSemiInfEdge R m → m = n ∨ m = n'
  /-- The two edge normals form a positively oriented basis: `0 < det n n'`
  (paper `scratch/b3_colle2.txt:388`: the `ℓ`-edges precede the `ℓ'`-edges). -/
  detPos : 0 < det n n'
  /-- `w ≺ ⋯ ≺ w'` for the positive orientation. -/
  precedes : PrecedesAll R n n'

theorem IsRegion.ne {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ} (h : IsRegion R n n') : n ≠ n' :=
  h.precedes.2.2.1

/-! ### The quarter plane: a non-degenerate infinite region -/

/-- The quarter plane `{z : 0 ≤ z₁, 0 ≤ z₂}`. -/
def quad : Set (ℤ × ℤ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2}

theorem mem_quad {z : ℤ × ℤ} : z ∈ quad ↔ 0 ≤ z.1 ∧ 0 ≤ z.2 := Iff.rfl

/-- In a direction pointing into the recession cone there is no exposed face at all. -/
theorem face_quad_eq_empty {n : ℤ × ℤ} (h : 0 < n.1 ∨ 0 < n.2) : face quad n = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, hm⟩
  rcases h with h | h
  · have hc := hm (z.1 + 1, z.2) ⟨by omega, h2⟩
    simp only [dot] at hc
    nlinarith
  · have hc := hm (z.1, z.2 + 1) ⟨h1, by omega⟩
    simp only [dot] at hc
    nlinarith

theorem face_quad_left : face quad (-1, 0) = {z | z.1 = 0 ∧ 0 ≤ z.2} := by
  ext z
  constructor
  · rintro ⟨⟨h1, h2⟩, hm⟩
    have h := hm (0, z.2) ⟨le_refl _, h2⟩
    simp only [dot_e1'] at h
    exact ⟨le_antisymm (by omega) h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨by omega, h2⟩, ?_⟩
    rintro y ⟨b1, b2⟩
    simp only [dot_e1']
    omega

theorem face_quad_bot : face quad (0, -1) = {z | 0 ≤ z.1 ∧ z.2 = 0} := by
  ext z
  constructor
  · rintro ⟨⟨h1, h2⟩, hm⟩
    have h := hm (z.1, 0) ⟨h1, le_refl _⟩
    simp only [dot_e2'] at h
    exact ⟨h1, le_antisymm (by omega) h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, by omega⟩, ?_⟩
    rintro y ⟨b1, b2⟩
    simp only [dot_e2']
    omega

theorem face_quad_singleton {n : ℤ × ℤ} (h1 : n.1 < 0) (h2 : n.2 < 0) :
    face quad n = {((0 : ℤ), (0 : ℤ))} := by
  ext z
  constructor
  · rintro ⟨⟨a1, a2⟩, hm⟩
    have h := hm (0, 0) ⟨le_refl _, le_refl _⟩
    simp only [dot] at h
    have e1 : n.1 * z.1 ≤ 0 := by nlinarith
    have e2 : n.2 * z.2 ≤ 0 := by nlinarith
    have f1 : n.1 * z.1 = 0 := by linarith
    have f2 : n.2 * z.2 = 0 := by linarith
    refine Prod.ext ?_ ?_
    · rcases mul_eq_zero.mp f1 with h' | h'
      · omega
      · exact h'
    · rcases mul_eq_zero.mp f2 with h' | h'
      · omega
      · exact h'
  · rintro rfl
    refine ⟨⟨le_refl _, le_refl _⟩, ?_⟩
    rintro y ⟨b1, b2⟩
    simp only [dot]
    nlinarith

/-- **The quarter plane has exactly two edges**, both semi-infinite. -/
theorem E_quad : E quad = {(-1, 0), (0, -1)} := by
  ext n
  constructor
  · rintro ⟨hprim, hnt⟩
    by_cases hpos : 0 < n.1 ∨ 0 < n.2
    · rw [face_quad_eq_empty hpos] at hnt
      exact absurd hnt (by simp)
    · push Not at hpos
      obtain ⟨hp1, hp2⟩ := hpos
      by_cases h1 : n.1 = 0
      · rcases prim_eq_of_fst_eq_zero hprim h1 with rfl | rfl
        · exact absurd hp2 (by norm_num)
        · simp
      · by_cases h2 : n.2 = 0
        · rcases prim_eq_of_snd_eq_zero hprim h2 with rfl | rfl
          · exact absurd hp1 (by norm_num)
          · simp
        · exfalso
          rw [face_quad_singleton (by omega) (by omega)] at hnt
          exact Set.not_nontrivial_singleton hnt
  · rintro (rfl | rfl)
    · refine ⟨by decide, ?_⟩
      rw [face_quad_left]
      exact ⟨(0, 0), ⟨rfl, le_refl _⟩, (0, 1), ⟨rfl, by norm_num⟩, by decide⟩
    · refine ⟨by decide, ?_⟩
      rw [face_quad_bot]
      exact ⟨(0, 0), ⟨le_refl _, rfl⟩, (1, 0), ⟨by norm_num, rfl⟩, by decide⟩

theorem infinite_face_quad_left : (face quad (-1, 0)).Infinite := by
  rw [face_quad_left]
  exact Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((0 : ℤ), (k : ℤ)))
    (fun a b h => by simpa using h) (fun k => ⟨rfl, by positivity⟩)

theorem infinite_face_quad_bot : (face quad (0, -1)).Infinite := by
  rw [face_quad_bot]
  exact Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (((k : ℤ)), (0 : ℤ)))
    (fun a b h => by simpa using h) (fun k => ⟨by positivity, rfl⟩)

theorem infinite_quad : quad.Infinite := infinite_face_quad_left.mono (face_subset _ _)

theorem isLatticeConvexRegion_quad : IsLatticeConvexRegion quad := by
  refine ⟨{x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2}, ?_, ?_, ?_⟩
  · rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ a b ha hb -
    constructor
    · show (0 : ℝ) ≤ a * x.1 + b * y.1
      exact add_nonneg (mul_nonneg ha hx1) (mul_nonneg hb hy1)
    · show (0 : ℝ) ≤ a * x.2 + b * y.2
      exact add_nonneg (mul_nonneg ha hx2) (mul_nonneg hb hy2)
  · exact (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)
  · ext z
    simp only [Set.mem_preimage, toReal]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · show (0 : ℝ) ≤ (z.1 : ℝ)
        exact_mod_cast h1
      · show (0 : ℝ) ≤ (z.2 : ℝ)
        exact_mod_cast h2
    · rintro ⟨h1, h2⟩
      have g1 : (0 : ℝ) ≤ (z.1 : ℝ) := h1
      have g2 : (0 : ℝ) ≤ (z.2 : ℝ) := h2
      exact ⟨by exact_mod_cast g1, by exact_mod_cast g2⟩

/-- The two edges of the quarter plane are in the correct counter-clockwise order:
the left edge (pointing up) precedes the bottom edge (pointing left). -/
theorem angLT_quad : angLT (-1, 0) (0, -1) := by
  rw [angLT_iff]
  refine Or.inr ⟨by norm_num [half], ?_⟩
  rw [angSlope, angSlope, if_pos rfl, if_neg (by norm_num)]
  exact WithBot.bot_lt_coe _

/-- **Non-degeneracy check for `IsRegion`.**  The quarter plane is a genuine
`((-1,0), (0,-1))`-region: infinite, of positive area, with exactly two edges, both
semi-infinite.  It is not a point, a segment, a half-plane or the whole plane. -/
theorem isRegion_quad : IsRegion quad (-1, 0) (0, -1) where
  latticeConvex := isLatticeConvexRegion_quad
  infinite := infinite_quad
  posArea := posArea_of_edges (n := (-1, 0)) (m := (0, -1))
    (by rw [E_quad]; simp) (by rw [E_quad]; simp) (by decide) (by decide)
  edgesFinite := by rw [E_quad]; exact Set.toFinite _
  semiInf := ⟨by rw [E_quad]; simp, infinite_face_quad_left⟩
  semiInf' := ⟨by rw [E_quad]; simp, infinite_face_quad_bot⟩
  semiInfUnique := fun m hm => by
    have h := hm.1
    rw [E_quad] at h
    simpa using h
  detPos := by decide
  precedes := ⟨by rw [E_quad]; simp, by rw [E_quad]; simp, by decide, fun m hm h1 h2 => by
    rw [E_quad] at hm
    rcases hm with rfl | rfl
    · exact absurd rfl h1
    · exact absurd rfl h2⟩

/-! ## §10. Interface to the chain construction (`ChainData`)

`Nivat.Colle35.ChainData` (`Nivat/External/Colle/Lemma35.lean`) carries a field

```
Env : Set (ℤ × ℤ) → Prop
```

that is used only through `envB : ∀ i, Env (B i)`, `envA : ∀ i, Env (A i)` and
`shellEnv : ∃ ε i₀, 0 < ε ∧ ∀ i, i₀ ≤ i → Env (shell i ε)`.  It is an *abstract*
predicate there because the notion "`E(S_φ)`-enveloped" had no definition.  With this
file it becomes concrete:

```
Env := Nivat.LE2.EnvOf (↑S : Set (ℤ × ℤ))
```

where `S` is the generating window.  The lemmas below are the shapes in which
`envB`/`envA`/`shellEnv` are discharged.  (This file deliberately does **not** import
`Lemma35.lean`; the wiring is left to whoever joins the two.) -/

/-- `EnvOf U` is the predicate "`· ` is `E(U)`-enveloped", ready to be plugged into
the `Env` field of `ChainData`. -/
def EnvOf (U : Set (ℤ × ℤ)) : Set (ℤ × ℤ) → Prop := fun T => Enveloped U T

theorem envOf_iff {U T : Set (ℤ × ℤ)} : EnvOf U T ↔ Enveloped U T := Iff.rfl

/-- The usual way an envelope hypothesis is verified: same edge directions, and each
edge at least as long. -/
theorem envOf_of_E_eq {U T : Set (ℤ × ℤ)} (hT : IsLatticeConvexRegion T) (hE : E T = E U)
    (hle : ∀ n ∈ E U, (face U n).encard ≤ (face T n).encard) : EnvOf U T :=
  ⟨⟨hT, fun n hn => ⟨hE ▸ hn, hle n (hE ▸ hn)⟩⟩, by rw [hE]⟩

/-- Envelopes are translation-invariant, which is what makes them usable along a chain
of translates `B i`, `A i`. -/
theorem envOf_shift {U T : Set (ℤ × ℤ)} (v : ℤ × ℤ) (h : EnvOf U T) :
    EnvOf U (shift v T) := (enveloped_shift_right v).mpr h

/-- An `E(U)`-enveloped set of a `U` with three distinct edges cannot be degenerate. -/
theorem posArea_of_envOf {U T : Set (ℤ × ℤ)} {n m k : ℤ × ℤ} (hn : n ∈ E U) (hm : m ∈ E U)
    (hk : k ∈ E U) (h1 : n ≠ m) (h2 : n ≠ k) (h3 : m ≠ k) (hfin : (E U).Finite)
    (h : EnvOf U T) : PosArea T := by
  have hE : E T = E U := Enveloped.E_eq hfin h
  exact posArea_of_three_edges (hE ▸ hn) (hE ▸ hm) (hE ▸ hk) h1 h2 h3

/-! ### Every non-degenerate lattice box is `E(sq1)`-enveloped

`Nivat.ColleReg.envOf_Bchain` proves this for the particular boxes `[0, i+1]²`.  The chain
construction of Colle §3 needs to enlarge an arbitrary finite set to an enveloped set, and
the natural enlargement is its bounding box, which does not start at the origin.  Since
`E_box` and `face_box_*` already take arbitrary corners, the generalisation is mechanical. -/

theorem two_le_face_box_right {p q : ℤ × ℤ} (h1 : p.1 < q.1) (h2 : p.2 < q.2) :
    2 ≤ (face (box p q) (1, 0)).encard := by
  rw [face_box_right (le_of_lt h1)]
  exact two_le_encard_of_pair (a := (q.1, p.2)) (b := (q.1, p.2 + 1))
    ⟨rfl, le_refl _, le_of_lt h2⟩ ⟨rfl, by omega, by omega⟩
    (by intro h; rw [Prod.ext_iff] at h; omega)

theorem two_le_face_box_left {p q : ℤ × ℤ} (h1 : p.1 < q.1) (h2 : p.2 < q.2) :
    2 ≤ (face (box p q) (-1, 0)).encard := by
  rw [face_box_left (le_of_lt h1)]
  exact two_le_encard_of_pair (a := (p.1, p.2)) (b := (p.1, p.2 + 1))
    ⟨rfl, le_refl _, le_of_lt h2⟩ ⟨rfl, by omega, by omega⟩
    (by intro h; rw [Prod.ext_iff] at h; omega)

theorem two_le_face_box_top {p q : ℤ × ℤ} (h1 : p.1 < q.1) (h2 : p.2 < q.2) :
    2 ≤ (face (box p q) (0, 1)).encard := by
  rw [face_box_top (le_of_lt h2)]
  exact two_le_encard_of_pair (a := (p.1, q.2)) (b := (p.1 + 1, q.2))
    ⟨le_refl _, le_of_lt h1, rfl⟩ ⟨by omega, by omega, rfl⟩
    (by intro h; rw [Prod.ext_iff] at h; omega)

theorem two_le_face_box_bot {p q : ℤ × ℤ} (h1 : p.1 < q.1) (h2 : p.2 < q.2) :
    2 ≤ (face (box p q) (0, -1)).encard := by
  rw [face_box_bot (le_of_lt h2)]
  exact two_le_encard_of_pair (a := (p.1, p.2)) (b := (p.1 + 1, p.2))
    ⟨le_refl _, le_of_lt h1, rfl⟩ ⟨by omega, by omega, rfl⟩
    (by intro h; rw [Prod.ext_iff] at h; omega)

/-- **Every non-degenerate lattice box is `E(sq1)`-enveloped.**  Generalises
`Nivat.ColleReg.envOf_Bchain` from `box (0,0) (i+1, i+1)` to arbitrary corners. -/
theorem envOf_sq1_box {p q : ℤ × ℤ} (h1 : p.1 < q.1) (h2 : p.2 < q.2) :
    EnvOf sq1 (box p q) := by
  refine envOf_of_E_eq (isLatticeConvexRegion_box _ _) ?_ ?_
  · rw [E_box h1 h2, E_sq1]
  · intro n hn
    rw [E_sq1] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · rw [encard_face_sq1_right]; exact two_le_face_box_right h1 h2
    · rw [encard_face_sq1_left]; exact two_le_face_box_left h1 h2
    · rw [encard_face_sq1_top]; exact two_le_face_box_top h1 h2
    · rw [encard_face_sq1_bot]; exact two_le_face_box_bot h1 h2

/-! ## Status

Proved here, with no `sorry` and no new axioms:

* §1–§2 the integer pairing, primitive vectors, exposed faces, the sign dictionary
  to Colle's `ℋ(ℓ)`, edges `E(·)` and vertices `V(·)`, and `injOn_face`
  ("an edge determines its normal");
* §3 `finite_E`: a finite set of positive area has finitely many edges;
* §4 the bridge `isColleVertex_of_isVtx` to Colle's own definition of a vertex
  ("`𝒮 ∖ {g}` is still convex");
* §5 the counter-clockwise cyclic order on primitive directions, with trichotomy,
  and successor/predecessor of an edge (existence and uniqueness);
* §6 a concrete definition of *weakly `E(𝒰)`-enveloped* and *`E(𝒰)`-enveloped*
  (Definition 3.2), reflexive and transitive, translation-invariant, with
  `Enveloped.E_eq` and `posArea_of_three_edges`;
* §7 half-planes, `ℓ^{(-)}` (Notation 3.3) with its "closest outside line" property,
  half-strips and strips (Definition 3.4);
* §8 the lattice box: all four faces computed, `E_box`, and the non-degenerate
  envelope `Enveloped sq1 sq2` together with the negative check `not_enveloped_sq`;
* §9 semi-infinite edges and `(ℓ,ℓ')`-regions (Definition 3.1), with the quarter
  plane as a non-degenerate witness;
* §10–§11 the 2D H-representation (absent from Mathlib) and, on top of it,
  `isClosed_iUnion_convHullOf_of_frame` and
  `isLatticeConvexRegion_iUnion_of_mono_fixedEdges_finite`: a monotone union of finite
  lattice-convex sets with fixed edge directions is lattice-convex.  The integrality of
  `suppVal` is what makes this true — a monotone bounded *integer* support sequence is
  eventually constant, which is exactly what fails over `ℝ`.

## Not proved here (2026-09-16, measured — this is a debt register, not a parking lot)

Two of the three items previously listed under this heading are now closed, one here and
one elsewhere; what is left is stated precisely so it cannot be mistaken for more or less
than it is.

* **Closed elsewhere.**  Colle's `Â_∞^{(ε)}` truncations and the distance enumeration
  `0 = d₀ < d₁ < ⋯` are in `Nivat/External/Colle/MaximalEnveloped.lean`: `MaxEnv.shell`,
  `MaxEnv.d`, `d_strictMono`, `exists_d_eq_lineDist`, and
  `exists_mem_halfPlaneGE_lineDist_eq` (the enumeration is *onto* the realised distance
  set, Colle `b3_colle2.txt:442`, needing `Prim n`).
* **Still open.**  For infinite regions: that an `(ℓ,ℓ')`-region has finitely many edges,
  that its edge set is an interval in the cyclic order, and that `E(·)` behaves well under
  intersection with a half-plane.  §9 proves these for the quarter plane only.  Nothing in
  the main line currently depends on them: `RegionSteps.region_latticeConvex` gets
  lattice-convexity of each `Â_i` straight out of `LE2.EnvOf` (which bundles it) and then
  takes the union through §11 above.  So this is a completeness gap in the region theory,
  not a hole under `Nivat.convex_nivat`.  The live obligations are registered in
  `delivery/blueprint/NOTE.md`; the gate, not this comment, is what decides whether they
  are met.
-/

/-! ### H-rep §9. Non-vacuity check on the unit square `[0,1]²`

These are not needed downstream; they exist to witness that the statement is not
vacuous and that both directions compute the expected answer. -/

section UnitSquare

theorem finite_sq1' : sq1.Finite := by
  refine Set.Finite.subset (Set.finite_Icc ((0 : ℤ), (0 : ℤ)) ((1 : ℤ), (1 : ℤ))) ?_
  rintro z ⟨h1, h2, h3, h4⟩
  exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩

theorem nonempty_sq1 : sq1.Nonempty := ⟨(0, 0), by exact ⟨le_refl _, by norm_num, le_refl _, by norm_num⟩⟩

theorem face_sq1_right : ((1 : ℤ), (1 : ℤ)) ∈ face sq1 ((1 : ℤ), (0 : ℤ)) :=
  ⟨⟨by norm_num, le_refl _, by norm_num, le_refl _⟩, fun y hy => by simpa using hy.2.1⟩

theorem face_sq1_left : ((0 : ℤ), (0 : ℤ)) ∈ face sq1 ((-1 : ℤ), (0 : ℤ)) :=
  ⟨⟨le_refl _, by norm_num, le_refl _, by norm_num⟩, fun y hy => by simpa using hy.1⟩

theorem face_sq1_top : ((1 : ℤ), (1 : ℤ)) ∈ face sq1 ((0 : ℤ), (1 : ℤ)) :=
  ⟨⟨by norm_num, le_refl _, by norm_num, le_refl _⟩, fun y hy => by simpa using hy.2.2.2⟩

theorem face_sq1_bot : ((0 : ℤ), (0 : ℤ)) ∈ face sq1 ((0 : ℤ), (-1 : ℤ)) :=
  ⟨⟨le_refl _, by norm_num, le_refl _, by norm_num⟩, fun y hy => by simpa using hy.2.2.1⟩

/-- The centre of the square is in its hull: this exercises the `⊇` direction, hence
the separation argument and the cone decomposition. -/
theorem centre_mem_sq1 : (((1 : ℝ) / 2), ((1 : ℝ) / 2)) ∈ convHullOf sq1 := by
  rw [convHullOf_eq_iInter_realHalfPlaneLE finite_sq1' nonempty_sq1 posArea_sq1]
  refine Set.mem_iInter₂.mpr fun m hm => ?_
  rw [E_sq1] at hm
  rcases hm with h | h | h | h <;> subst h
  · rw [suppVal_eq face_sq1_right]; norm_num [realHalfPlaneLE, dot]
  · rw [suppVal_eq face_sq1_left]; norm_num [realHalfPlaneLE, dot]
  · rw [suppVal_eq face_sq1_top]; norm_num [realHalfPlaneLE, dot]
  · rw [suppVal_eq face_sq1_bot]; norm_num [realHalfPlaneLE, dot]

/-- A point outside is really excluded: this exercises the `⊆` direction. -/
theorem two_zero_not_mem_sq1 : ((2 : ℝ), (0 : ℝ)) ∉ convHullOf sq1 := by
  intro hmem
  rw [convHullOf_eq_iInter_realHalfPlaneLE finite_sq1' nonempty_sq1 posArea_sq1] at hmem
  have h := Set.mem_iInter₂.mp hmem ((1 : ℤ), (0 : ℤ)) (by rw [E_sq1]; simp)
  rw [suppVal_eq face_sq1_right] at h
  norm_num [realHalfPlaneLE, dot] at h

end UnitSquare

end Nivat.LE2
