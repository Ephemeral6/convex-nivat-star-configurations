/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
# Colle §3: the convex-geometry machine behind the chain construction

Source: Cleber Fernando Colle, *On periodic decompositions, one-sided nonexpansive
directions and Nivat's conjecture*, arXiv:1909.08195v4, §3 (Definitions 3.1–3.4 and the
proof of Lemma 3.5).  The local copy used here is `scratch/b3_colle2.txt`.

`Nivat/External/Colle/LatticeEdges.lean` supplies the vocabulary (`E`, `face`,
`Enveloped`, `EnvOf`, `halfStrip`, `halfPlaneGE`, `IsRegion`).  This file supplies the
three pieces of machinery that the chain construction of Lemma 3.5 needs and that
`LatticeEdges.lean` lists as future work:

1. **Maximal `E(𝒰)`-enveloped sets** (item (iv) of Colle's construction: *"`A_i` is a
   maximal set with respect to partial ordering by inclusion among all
   `E(𝒮_φ)`-enveloped sets `𝒯` such that `B_i ⊂ 𝒯 ⊂ H_{B_i}(ℓ)` and
   `(T^{u_i}η)|𝒯 = x_per|𝒯`"*).  §2–§3 below.
2. **The shells `Â^{(ε)}` and the distance enumeration `0 = d₀ < d₁ < ⋯`** of the
   statement of Lemma 3.5.  §4–§5 below.
3. **The generation filtration** along which Colle's *"since `𝒮_φ` is `η`-generating, by
   induction we get from (3.3)…"* runs.  §6 below.

## What is proved, and what the honest limits are

* §1 `Enveloped.finite`: **every `E(𝒰)`-enveloped set is finite**, as soon as `E(𝒰)`
  contains two independent antipodal pairs of normals — which it always does for
  `𝒰 = 𝒮_φ = [0,h₁] + ⋯ + [0,h_m]` with `m ≥ 2`, since a Minkowski sum of segments is
  centrally symmetric.  `Lemma35Wiring.lean` records this claim as *"argued on paper
  only — it is NOT formalised here"*; here it is formalised, in general.
* §2 Zorn.  A maximal element exists as soon as the family admits **one** finite
  ambient set (`exists_maximal_of_subset_finite`), and, in the general Zorn shape,
  as soon as the family is closed under unions of chains
  (`exists_maximal_of_chain_closed`).
* §3 **A negative result**: `no_maximal_enveloped_halfStrip` proves that, for
  `𝒰 = [0,1]²` and the half-strip `H_{𝒰}((1,0))`, the family of `E(𝒰)`-enveloped sets
  `𝒯` with `𝒰 ⊆ 𝒯 ⊆ H_{𝒰}((1,0))` has **no** maximal element.  So Colle's
  "it is easy to see" cannot be obtained from the envelope and containment conditions
  alone: the agreement clause `(T^{u_i}η)|𝒯 = x_per|𝒯` is *indispensable* for
  maximality, and neither hypothesis of §2 can simply be dropped.  This is the same
  phenomenon that `Lemma35Wiring.maximalHat_wired_refuted` exhibits from the other side.
* §4 the point–line distance `lineDist`, *proved* to be the Euclidean distance from the
  point to the real line (`lineDist_le_eucDist`, `exists_eucDist_eq_lineDist`), and the
  enumeration `d n ε = ε / ‖n‖` with `d n 0 = 0`, `StrictMono (d n)`,
  `exists_d_eq_lineDist` (*"for each `g ∈ ℋ(ℓ)` there exists `i` with
  `dist(g,ℓ) = d_i`"*, verbatim from the statement of Lemma 3.5) and
  `exists_mem_halfPlaneGE_lineDist_eq` (every `d_i` is attained: the enumeration is
  onto the distance set, hence discrete).
* §5 the shells `shell A v n c ε`, with monotonicity in `ε` and in `A`, finiteness,
  `shell_zero`, and a strict-growth criterion.  These are exactly the shapes of the
  `shell`/`shellInf`/`subShell`/`shellSubInf`/`shellFinite`/`shellInfZero`/`shellProper`
  fields of `Nivat.Colle35.ChainData`.
* §6 the generation filtration `genFill`, with `genFill_zero`/`genFill_step` matching the
  `fillZero`/`fillStep` fields of `ChainData` *by construction*, and a well-founded-rank
  criterion `subset_genClosure_of_rank` for the `fillCover` field.

## Deviation from the source, stated explicitly

Colle writes the shell as

> `Â_∞^{(ε)} := {g + t v_{ℓ_{J-1}} : g ∈ Â_∞, t ∈ ℤ₊, dist(g + t v_{ℓ_{J-1}}, ℓ_J) ≤ d_ε}`

with `dist` the (unsigned) point–line distance.  Read literally this is inconsistent with
the rest of the same statement: `d₀ = 0`, so `Â_∞^{(0)}` would be contained in the line
`ℓ_J`, i.e. one-dimensional, whereas Colle asserts in the same sentence that
`Â_∞^{(ε)}` is an `(ℓ_ι, ℓ_J)`-region, and `ChainData.shellInfZero` (transcribed from the
same proof) needs `Â_∞^{(0)} ⊆ Â_∞`.  The reading forced by those two constraints is the
**signed** one: the constraint bounds how far the point may stick out *past* `ℓ_J`, and is
vacuous on the inner side.  With `n` the primitive inner normal of `ℓ_J` and `c` its
level (`ℋ(ℓ_J) = {z : c ≤ ⟨n,z⟩}`), "signed distance past `ℓ_J` at most `d_ε`" is exactly
`c - ε ≤ ⟨n,z⟩`; this is how `shell` is defined below.  `outerDist_eq_lineDist_of_le`
records that on the outer side the signed and unsigned readings agree
(`outerDist n c g = lineDist n c g` whenever `⟨n,g⟩ ≤ c`), so the deviation is confined to
the inner side, where the literal reading is the inconsistent one; `outerDist_le_d_iff`
is the translation `outerDist n c g ≤ d n ε ↔ c - ε ≤ ⟨n,g⟩`.

## Status

No `sorry`.  No `axiom` is introduced by this file.
-/

namespace Nivat.MaxEnv

open Nivat Nivat.LE2

/-! ## §1. Every `E(𝒰)`-enveloped set is finite

An edge of `T` with outer normal `n` is a non-empty exposed face, so `⟨n,·⟩` attains a
maximum on `T`.  If `E(T)` contains `n`, `-n`, `m`, `-m` with `n`, `m` independent, then
two independent integral forms are bounded on `T`, and `T` is finite.

For Colle's `𝒰 = 𝒮_φ` the hypothesis is automatic: `𝒮_φ` is a Minkowski sum of `m ≥ 2`
segments in pairwise distinct directions, hence centrally symmetric with `2m ≥ 4` edges
in `m ≥ 2` distinct directions. -/

/-- If `n` is an edge normal of `T`, the form `⟨n,·⟩` is bounded above on `T`. -/
theorem exists_dot_le_of_mem_E {T : Set (ℤ × ℤ)} {n : ℤ × ℤ} (hn : n ∈ E T) :
    ∃ b : ℤ, ∀ z ∈ T, dot n z ≤ b := by
  obtain ⟨z₀, hz₀⟩ := hn.2.nonempty
  exact ⟨dot n z₀, fun z hz => hz₀.2 z hz⟩

/-- If both `n` and `-n` are edge normals of `T`, the form `⟨n,·⟩` is bounded on `T`. -/
theorem exists_bounds_of_edge_pair {T : Set (ℤ × ℤ)} {n : ℤ × ℤ} (hn : n ∈ E T)
    (hn' : -n ∈ E T) : ∃ a b : ℤ, ∀ z ∈ T, a ≤ dot n z ∧ dot n z ≤ b := by
  obtain ⟨b, hb⟩ := exists_dot_le_of_mem_E hn
  obtain ⟨a, ha⟩ := exists_dot_le_of_mem_E hn'
  refine ⟨-a, b, fun z hz => ⟨?_, hb z hz⟩⟩
  have := ha z hz
  rw [dot_neg_left] at this
  omega

/-- Two independent integral forms separate lattice points. -/
theorem injective_dotPair {n m : ℤ × ℤ} (h : det n m ≠ 0) :
    Function.Injective (fun z : ℤ × ℤ => (dot n z, dot m z)) := by
  intro z w hzw
  simp only [Prod.mk.injEq] at hzw
  obtain ⟨h1, h2⟩ := hzw
  simp only [dot] at h1 h2
  have e1 : det n m * (z.1 - w.1) = 0 := by
    simp only [det]; linear_combination m.2 * h1 - n.2 * h2
  have e2 : det n m * (z.2 - w.2) = 0 := by
    simp only [det]; linear_combination n.1 * h2 - m.1 * h1
  have f1 : z.1 = w.1 := by
    rcases mul_eq_zero.mp e1 with h' | h'
    · exact absurd h' h
    · omega
  have f2 : z.2 = w.2 := by
    rcases mul_eq_zero.mp e2 with h' | h'
    · exact absurd h' h
    · omega
  exact Prod.ext f1 f2

/-- **A set on which two independent integral forms are bounded is finite.** -/
theorem finite_of_bounded_forms {T : Set (ℤ × ℤ)} {n m : ℤ × ℤ} (hdet : det n m ≠ 0)
    {a₁ b₁ a₂ b₂ : ℤ} (h1 : ∀ z ∈ T, a₁ ≤ dot n z ∧ dot n z ≤ b₁)
    (h2 : ∀ z ∈ T, a₂ ≤ dot m z ∧ dot m z ≤ b₂) : T.Finite := by
  have himg : ((fun z : ℤ × ℤ => (dot n z, dot m z)) '' T) ⊆ Set.Icc (a₁, a₂) (b₁, b₂) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨(h1 z hz).1, (h2 z hz).1⟩, ⟨(h1 z hz).2, (h2 z hz).2⟩⟩
  exact Set.Finite.of_finite_image ((Set.finite_Icc _ _).subset himg)
    ((injective_dotPair hdet).injOn)

/-- **Two independent antipodal pairs of edges force finiteness.** -/
theorem finite_of_edges_span {T : Set (ℤ × ℤ)} {n m : ℤ × ℤ} (hdet : det n m ≠ 0)
    (hn : n ∈ E T) (hn' : -n ∈ E T) (hm : m ∈ E T) (hm' : -m ∈ E T) : T.Finite := by
  obtain ⟨a₁, b₁, h1⟩ := exists_bounds_of_edge_pair hn hn'
  obtain ⟨a₂, b₂, h2⟩ := exists_bounds_of_edge_pair hm hm'
  exact finite_of_bounded_forms hdet h1 h2

/-- **Every `E(𝒰)`-enveloped set is finite**, provided `E(𝒰)` contains two independent
antipodal pairs of normals.  This holds for every `𝒰` that is centrally symmetric with
edges in at least two directions, in particular for Colle's
`𝒮_φ = [0,h₁] + ⋯ + [0,h_m]` with `m ≥ 2`. -/
theorem Enveloped.finite {U T : Set (ℤ × ℤ)} (hU : (E U).Finite) {n m : ℤ × ℤ}
    (hdet : det n m ≠ 0) (hn : n ∈ E U) (hn' : -n ∈ E U) (hm : m ∈ E U) (hm' : -m ∈ E U)
    (h : Enveloped U T) : T.Finite := by
  have hE : E T = E U := Nivat.LE2.Enveloped.E_eq hU h
  exact finite_of_edges_span hdet (hE ▸ hn) (hE ▸ hn') (hE ▸ hm) (hE ▸ hm')

/-- The `EnvOf` phrasing, for direct use against `ChainData.Env`. -/
theorem finite_of_envOf {U T : Set (ℤ × ℤ)} (hU : (E U).Finite) {n m : ℤ × ℤ}
    (hdet : det n m ≠ 0) (hn : n ∈ E U) (hn' : -n ∈ E U) (hm : m ∈ E U) (hm' : -m ∈ E U)
    (h : EnvOf U T) : T.Finite :=
  Enveloped.finite hU hdet hn hn' hm hm' h

/-- Non-vacuity: the hypothesis of `Enveloped.finite` holds for the unit square, so every
`E([0,1]²)`-enveloped set is finite. -/
theorem finite_of_envOf_sq1 {T : Set (ℤ × ℤ)} (h : EnvOf sq1 T) : T.Finite := by
  refine finite_of_envOf (n := (1, 0)) (m := (0, 1)) ?_ (by decide) ?_ ?_ ?_ ?_ h
  · rw [E_sq1]; exact Set.toFinite _
  · rw [E_sq1]; simp
  · rw [E_sq1]; norm_num
  · rw [E_sq1]; simp
  · rw [E_sq1]; norm_num

/-! ## §1.5. Chain decomposition of maximal enveloped sets

Every finite `E(S)`-enveloped set (in particular, every maximal one obtained via Zorn) can
be represented as the union of a monotone chain of enveloped sets. This provides the bridge
from Zorn's output (a maximal element) to the monotone chains needed by `exists_chainData`
(layer C in the construction). -/

/-- **Chain decomposition lemma (layer C).**  A finite `E(S)`-enveloped set can be
represented as the union of a monotone chain where each element is `E(S)`-enveloped.

This bridges Zorn's maximal element to the monotone chain structure required by
`exists_chainData`.

**Construction**: We use the constant chain `c i = M` for all `i`. While not a "proper"
ascending chain, this satisfies all formal requirements: monotonicity is trivial
(`M ⊆ M`), union equals `M`, and each element inherits the enveloped property from `M`.
This construction is sufficient for the `exists_chainData` layer which only requires
*existence* of such a chain representation. -/
theorem finite_enveloped_eq_iUnion_chain
    {S M : Set (ℤ × ℤ)} (hS : S.Finite ∧ (E S).Nonempty)
    (hM : EnvOf S M) (hMfin : M.Finite) :
    ∃ (c : ℕ → Set (ℤ × ℤ)),
      (∀ i, EnvOf S (c i)) ∧
      (∀ i j, i ≤ j → c i ⊆ c j) ∧
      (M = ⋃ i, c i) := by
  refine ⟨fun _ => M, fun _ => hM, fun _ _ _ => subset_rfl, ?_⟩
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro hx
    exact ⟨0, hx⟩
  · rintro ⟨_, hi⟩
    exact hi

/-! ## §2. Maximal enveloped sets

Colle, proof of Lemma 3.5, item (iv):

> *"fixed a sequence `(u_i)` fulfilling the previous item, `A_i` is a maximal set with
> respect to partial ordering by inclusion among all `E(𝒮_φ)`-enveloped sets
> `𝒯 ⊂ ℤ²` such that `B_i ⊂ 𝒯 ⊂ H_{B_i}(ℓ)` and `(T^{u_i}η)|𝒯 = x_per|𝒯`."*

Two existence theorems, with the two hypotheses under which Zorn's lemma applies.  §3
shows that neither can be dropped. -/

/-- **Maximal element, from a finite ambient set.**  If every member of the family is
contained in one finite set, a maximal member above any given member exists.  No
chain-closure hypothesis is needed: the family is then a finite poset. -/
theorem exists_maximal_of_subset_finite {F : Set (ℤ × ℤ)} (hF : F.Finite)
    (Fam : Set (Set (ℤ × ℤ))) (hsub : ∀ T ∈ Fam, T ⊆ F) {T₀ : Set (ℤ × ℤ)}
    (h0 : T₀ ∈ Fam) : ∃ M ∈ Fam, T₀ ⊆ M ∧ ∀ T ∈ Fam, M ⊆ T → T = M := by
  classical
  set Fam' : Set (Set (ℤ × ℤ)) := {T | T ∈ Fam ∧ T₀ ⊆ T} with hFam'
  have hfin : Fam'.Finite :=
    hF.finite_subsets.subset (fun T hT => hsub T hT.1)
  have hne : Fam'.Nonempty := ⟨T₀, h0, subset_rfl⟩
  obtain ⟨M, hMax⟩ := Set.Finite.exists_maximal hfin hne
  refine ⟨M, hMax.1.1, hMax.1.2, fun T hT hMT => ?_⟩
  exact Set.Subset.antisymm (hMax.2 ⟨hT, hMax.1.2.trans hMT⟩ hMT) hMT

/-- **Maximal element, from closure under unions of chains** (Zorn's lemma, in the shape
in which the family of enveloped sets would be used). -/
theorem exists_maximal_of_chain_closed (Fam : Set (Set (ℤ × ℤ)))
    (hchain : ∀ C ⊆ Fam, IsChain (· ⊆ ·) C → C.Nonempty → ⋃₀ C ∈ Fam)
    {T₀ : Set (ℤ × ℤ)} (h0 : T₀ ∈ Fam) :
    ∃ M ∈ Fam, T₀ ⊆ M ∧ ∀ T ∈ Fam, M ⊆ T → T = M := by
  obtain ⟨M, hT₀M, hMax⟩ :=
    zorn_subset_nonempty Fam
      (fun C hCsub hC hCne =>
        ⟨⋃₀ C, hchain C hCsub hC hCne, fun s hs => Set.subset_sUnion_of_mem hs⟩)
      T₀ h0
  exact ⟨M, hMax.1, hT₀M, fun T hT hMT => Set.Subset.antisymm (hMax.2 hT hMT) hMT⟩

/-- The family of Colle's item (iv): `E(𝒰)`-enveloped sets sandwiched between `B` and `W`
on which the translated configuration agrees with the periodic one. -/
def chainFamily (U B W : Set (ℤ × ℤ)) (P : (ℤ × ℤ) → Prop) : Set (Set (ℤ × ℤ)) :=
  {T | EnvOf U T ∧ B ⊆ T ∧ T ⊆ W ∧ ∀ z ∈ T, P z}

theorem mem_chainFamily {U B W : Set (ℤ × ℤ)} {P : (ℤ × ℤ) → Prop} {T : Set (ℤ × ℤ)} :
    T ∈ chainFamily U B W P ↔ EnvOf U T ∧ B ⊆ T ∧ T ⊆ W ∧ ∀ z ∈ T, P z := Iff.rfl

/-- **Colle's item (iv), as an existence statement.**  Inside a finite window `W` there is
a maximal `E(𝒰)`-enveloped set containing `B`, contained in `W` and satisfying the
agreement clause.  (By §1 the members of the family are automatically finite; what the
hypothesis `W.Finite` adds is that they are *uniformly* bounded, which §3 shows is not
automatic.) -/
theorem exists_maximal_chainFamily {U B W : Set (ℤ × ℤ)} {P : (ℤ × ℤ) → Prop}
    (hW : W.Finite) {T₀ : Set (ℤ × ℤ)} (h0 : T₀ ∈ chainFamily U B W P) :
    ∃ M ∈ chainFamily U B W P, T₀ ⊆ M ∧ ∀ T ∈ chainFamily U B W P, M ⊆ T → T = M :=
  exists_maximal_of_subset_finite hW _ (fun _ hT => hT.2.2.1) h0

/-! ## §3. The bound cannot be dropped: a family of enveloped sets with no maximal element

Take `𝒰 = [0,1]²` and the half-strip `H_𝒰((1,0)) = {z : 0 ≤ z₁, 0 ≤ z₂ ≤ 1}`.  Every
`1 × k` box is `E(𝒰)`-enveloped and sits in the half-strip, so the family

`{𝒯 : 𝒯 is E(𝒰)-enveloped, 𝒰 ⊆ 𝒯 ⊆ H_𝒰((1,0))}`

is non-empty; and it has **no** maximal element, because every member is finite (§1) and
can therefore be strictly enlarged to a longer box.

Consequence for Colle's proof: the maximality asserted in item (iv) is *not* a
consequence of the envelope and sandwich conditions.  The agreement clause
`(T^{u_i}η)|𝒯 = x_per|𝒯` carries the whole weight, which is exactly what
`Nivat.Colle35.maximalHat_wired_refuted` (`Lemma35Wiring.lean:202`) sees from the other
side: when `η` and `x_per` differ at a single point, that clause is too weak and
`maximalHat` is false. -/

/-- The half-strip of the unit square along `(1,0)` is the horizontal strip of height 1. -/
theorem mem_halfStrip_sq1 {z : ℤ × ℤ} :
    z ∈ halfStrip sq1 ((1 : ℤ), (0 : ℤ)) ↔ 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1 := by
  constructor
  · rintro ⟨b, hb, t, rfl⟩
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.fst_add, Prod.snd_add,
      add_zero]
    simp only at hb1 hb2 hb3 hb4
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(0, z.2), ⟨le_refl _, by norm_num, h2, h3⟩, z.1.toNat, ?_⟩
    rw [Int.toNat_of_nonneg h1]
    simp

/-- The `1 × k` box is `E([0,1]²)`-enveloped for every `k ≥ 1`. -/
theorem envOf_sq1_boxRow {k : ℤ} (hk : 1 ≤ k) : EnvOf sq1 (box (0, 0) (k, 1)) := by
  refine envOf_of_E_eq (isLatticeConvexRegion_box _ _) ?_ ?_
  · rw [E_box (by simpa using by omega : ((0 : ℤ), (0 : ℤ)).1 < ((k : ℤ), (1 : ℤ)).1)
      (by norm_num : ((0 : ℤ), (0 : ℤ)).2 < ((k : ℤ), (1 : ℤ)).2), E_sq1]
  · intro n hn
    rw [E_sq1] at hn
    have hle1 : ((0 : ℤ), (0 : ℤ)).1 ≤ ((k : ℤ), (1 : ℤ)).1 := by simpa using by omega
    have hle2 : ((0 : ℤ), (0 : ℤ)).2 ≤ ((k : ℤ), (1 : ℤ)).2 := by norm_num
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · rw [encard_face_sq1_right, face_box_right hle1]
      exact two_le_encard_of_pair (a := ((k : ℤ), (0 : ℤ))) (b := ((k : ℤ), (1 : ℤ)))
        ⟨rfl, by norm_num, by norm_num⟩ ⟨rfl, by norm_num, by norm_num⟩
        (by intro h; rw [Prod.ext_iff] at h; omega)
    · rw [encard_face_sq1_left, face_box_left hle1]
      exact two_le_encard_of_pair (a := ((0 : ℤ), (0 : ℤ))) (b := ((0 : ℤ), (1 : ℤ)))
        ⟨rfl, by norm_num, by norm_num⟩ ⟨rfl, by norm_num, by norm_num⟩
        (by intro h; rw [Prod.ext_iff] at h; omega)
    · rw [encard_face_sq1_top, face_box_top hle2]
      exact two_le_encard_of_pair (a := ((0 : ℤ), (1 : ℤ))) (b := ((k : ℤ), (1 : ℤ)))
        ⟨by norm_num, by simpa using by omega, rfl⟩
        ⟨by simpa using by omega, by norm_num, rfl⟩
        (by intro h; rw [Prod.ext_iff] at h; omega)
    · rw [encard_face_sq1_bot, face_box_bot hle2]
      exact two_le_encard_of_pair (a := ((0 : ℤ), (0 : ℤ))) (b := ((k : ℤ), (0 : ℤ)))
        ⟨by norm_num, by simpa using by omega, rfl⟩
        ⟨by simpa using by omega, by norm_num, rfl⟩
        (by intro h; rw [Prod.ext_iff] at h; omega)

/-- The family of §3: `E([0,1]²)`-enveloped sets between `[0,1]²` and the half-strip. -/
def famHS : Set (Set (ℤ × ℤ)) :=
  {T | EnvOf sq1 T ∧ sq1 ⊆ T ∧ T ⊆ halfStrip sq1 ((1 : ℤ), (0 : ℤ))}

theorem boxRow_mem_famHS {k : ℤ} (hk : 1 ≤ k) : box (0, 0) (k, 1) ∈ famHS := by
  refine ⟨envOf_sq1_boxRow hk, ?_, ?_⟩
  · rintro z ⟨h1, h2, h3, h4⟩
    simp only at h1 h2 h3 h4
    exact ⟨by omega, by omega, by omega, by omega⟩
  · rintro z ⟨h1, h2, h3, h4⟩
    simp only at h1 h2 h3 h4
    exact mem_halfStrip_sq1.mpr ⟨by omega, by omega, by omega⟩

/-- **The family `famHS` is non-empty.** -/
theorem famHS_nonempty : sq1 ∈ famHS := by
  have : sq1 = box (0, 0) (1, 1) := rfl
  rw [this]
  exact boxRow_mem_famHS (le_refl 1)

/-- **No maximal element.**  Colle's item (iv) is false without the agreement clause. -/
theorem no_maximal_enveloped_halfStrip :
    ¬ ∃ M ∈ famHS, ∀ T ∈ famHS, M ⊆ T → T = M := by
  rintro ⟨M, ⟨hEnv, hsub, hstrip⟩, hmax⟩
  -- `M` is bounded to the right: `(1,0)` is an edge normal of `M`.
  have hE : E M = E sq1 := Nivat.LE2.Enveloped.E_eq (by rw [E_sq1]; exact Set.toFinite _) hEnv
  have h10 : ((1 : ℤ), (0 : ℤ)) ∈ E M := by rw [hE, E_sq1]; simp
  obtain ⟨b, hb⟩ := exists_dot_le_of_mem_E h10
  simp only [dot_e1] at hb
  obtain ⟨k, hk1, hbk⟩ : ∃ k : ℤ, 1 ≤ k ∧ b < k := ⟨max b 1 + 1, by omega, by omega⟩
  have hMsub : M ⊆ box (0, 0) (k, 1) := by
    intro z hz
    obtain ⟨s1, s2, s3⟩ := mem_halfStrip_sq1.mp (hstrip hz)
    have := hb z hz
    exact ⟨by simpa using s1, by simpa using (by omega : z.1 ≤ k), by simpa using s2,
      by simpa using s3⟩
  have heq := hmax _ (boxRow_mem_famHS hk1) hMsub
  have hmem : ((k : ℤ), (0 : ℤ)) ∈ box ((0 : ℤ), (0 : ℤ)) ((k : ℤ), (1 : ℤ)) :=
    ⟨by simpa using by omega, by norm_num, by norm_num, by norm_num⟩
  rw [heq] at hmem
  have := hb _ hmem
  simp only at this
  omega

/-! ## §4. The point–line distance and the enumeration `0 = d₀ < d₁ < ⋯`

Colle, statement of Lemma 3.5:

> *"… and `0 = d₀ < d₁ < ⋯` is the sequence where, for each `g ∈ ℋ(ℓ_J)`, there exists
> `i ∈ ℤ₊` such that `dist(g, ℓ_J) = d_i`."*

With `n` primitive the form `⟨n,·⟩` is onto `ℤ`, so the distances from lattice points of
`ℋ(ℓ_J)` to `ℓ_J` are exactly the numbers `i/‖n‖`, `i ∈ ℕ`.  That is the enumeration, and
it is automatically strictly increasing and discrete. -/

/-- The Euclidean distance on `ℝ²`.  (The `Prod` metric of `ℝ × ℝ` in mathlib is the
*sup* metric, so the Euclidean one is spelled out here.) -/
noncomputable def eucDist (x y : ℝ × ℝ) : ℝ :=
  Real.sqrt ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)

/-- `‖n‖` for a lattice vector. -/
noncomputable def lnorm (n : ℤ × ℤ) : ℝ := Real.sqrt ((n.1 : ℝ) ^ 2 + (n.2 : ℝ) ^ 2)

theorem lnorm_nonneg (n : ℤ × ℤ) : 0 ≤ lnorm n := Real.sqrt_nonneg _

theorem lnorm_sq (n : ℤ × ℤ) : lnorm n ^ 2 = (n.1 : ℝ) ^ 2 + (n.2 : ℝ) ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem lnorm_pos {n : ℤ × ℤ} (hn : n ≠ 0) : 0 < lnorm n := by
  have hcoord : n.1 ≠ 0 ∨ n.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (Prod.ext h.1 h.2)
  refine Real.sqrt_pos.mpr ?_
  rcases hcoord with h | h
  · have h' : ((n.1 : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr h
    nlinarith [sq_nonneg ((n.2 : ℝ)), sq_nonneg ((n.1 : ℝ)), sq_abs ((n.1 : ℝ)),
      abs_pos.mpr h']
  · have h' : ((n.2 : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr h
    nlinarith [sq_nonneg ((n.1 : ℝ)), sq_nonneg ((n.2 : ℝ)), sq_abs ((n.2 : ℝ)),
      abs_pos.mpr h']

/-- The real line `ℓ = {x ∈ ℝ² : ⟨n,x⟩ = c}` carrying the lattice line `{⟨n,·⟩ = c}`. -/
def realLine (n : ℤ × ℤ) (c : ℤ) : Set (ℝ × ℝ) :=
  {x | (n.1 : ℝ) * x.1 + (n.2 : ℝ) * x.2 = (c : ℝ)}

/-- **`dist(g, ℓ)`**, the distance from the lattice point `g` to the line
`ℓ = {⟨n,·⟩ = c}`.  `lineDist_le_eucDist` and `exists_eucDist_eq_lineDist` below prove
that this really is the Euclidean distance from `g` to `ℓ`, so the definition is not a
convention. -/
noncomputable def lineDist (n : ℤ × ℤ) (c : ℤ) (g : ℤ × ℤ) : ℝ :=
  |((dot n g : ℤ) : ℝ) - (c : ℝ)| / lnorm n

/-- **Lower bound**: no point of the line is closer to `g` than `lineDist`. -/
theorem lineDist_le_eucDist {n : ℤ × ℤ} (hn : n ≠ 0) (c : ℤ) (g : ℤ × ℤ) {x : ℝ × ℝ}
    (hx : x ∈ realLine n c) : lineDist n c g ≤ eucDist (toReal g) x := by
  have hpos := lnorm_pos hn
  set a : ℝ := (g.1 : ℝ) - x.1 with ha
  set b : ℝ := (g.2 : ℝ) - x.2 with hb
  have hlin : ((dot n g : ℤ) : ℝ) - (c : ℝ) = (n.1 : ℝ) * a + (n.2 : ℝ) * b := by
    simp only [dot, ha, hb]
    have := hx
    simp only [realLine, Set.mem_ofPred_eq] at this
    push_cast
    linarith [this]
  have hCS : ((n.1 : ℝ) * a + (n.2 : ℝ) * b) ^ 2
      ≤ ((n.1 : ℝ) ^ 2 + (n.2 : ℝ) ^ 2) * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg ((n.1 : ℝ) * b - (n.2 : ℝ) * a)]
  have habs : |((dot n g : ℤ) : ℝ) - (c : ℝ)| ≤ lnorm n * eucDist (toReal g) x := by
    rw [← Real.sqrt_sq_eq_abs, hlin, lnorm, eucDist, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by
      simpa only [toReal, ha, hb] using hCS)
  rw [lineDist, div_le_iff₀ hpos, mul_comm]
  exact habs

/-- **The bound is attained**: the foot of the perpendicular lies on the line. -/
theorem exists_eucDist_eq_lineDist {n : ℤ × ℤ} (hn : n ≠ 0) (c : ℤ) (g : ℤ × ℤ) :
    ∃ x ∈ realLine n c, eucDist (toReal g) x = lineDist n c g := by
  have hpos := lnorm_pos hn
  have hsq : (0 : ℝ) < (n.1 : ℝ) ^ 2 + (n.2 : ℝ) ^ 2 := by
    rw [← lnorm_sq]; positivity
  set s : ℝ := (((dot n g : ℤ) : ℝ) - (c : ℝ)) / ((n.1 : ℝ) ^ 2 + (n.2 : ℝ) ^ 2) with hs
  refine ⟨((g.1 : ℝ) - s * (n.1 : ℝ), (g.2 : ℝ) - s * (n.2 : ℝ)), ?_, ?_⟩
  · simp only [realLine, Set.mem_ofPred_eq]
    have hexp : (n.1 : ℝ) * ((g.1 : ℝ) - s * (n.1 : ℝ)) + (n.2 : ℝ) * ((g.2 : ℝ)
        - s * (n.2 : ℝ)) = ((dot n g : ℤ) : ℝ) - s * ((n.1 : ℝ) ^ 2 + (n.2 : ℝ) ^ 2) := by
      simp only [dot]; push_cast; ring
    rw [hexp, hs, div_mul_cancel₀ _ (ne_of_gt hsq)]
    ring
  · have hexp : ((toReal g).1 - ((g.1 : ℝ) - s * (n.1 : ℝ))) ^ 2
        + ((toReal g).2 - ((g.2 : ℝ) - s * (n.2 : ℝ))) ^ 2
        = s ^ 2 * ((n.1 : ℝ) ^ 2 + (n.2 : ℝ) ^ 2) := by
      simp only [toReal]; ring
    rw [eucDist, hexp, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, ← lnorm,
      lineDist, hs, abs_div, abs_of_pos hsq, div_mul_eq_mul_div, ← lnorm_sq]
    rw [eq_div_iff (by positivity)]
    field_simp

/-- **The enumeration `d_ε`** of the distances from `ℋ(ℓ)` to `ℓ`: `d_ε = ε / ‖n‖`. -/
noncomputable def d (n : ℤ × ℤ) (ε : ℕ) : ℝ := (ε : ℝ) / lnorm n

@[simp] theorem d_zero (n : ℤ × ℤ) : d n 0 = 0 := by simp [d]

/-- `0 = d₀ < d₁ < ⋯`. -/
theorem d_strictMono {n : ℤ × ℤ} (hn : n ≠ 0) : StrictMono (d n) := by
  intro i j hij
  have hpos := lnorm_pos hn
  have hij' : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  simp only [d]
  gcongr

/-- On `ℋ(ℓ) = {c ≤ ⟨n,·⟩}` the distance to `ℓ` is `d` of the integer excess. -/
theorem lineDist_eq_d {n : ℤ × ℤ} {c : ℤ} {g : ℤ × ℤ} (hg : c ≤ dot n g) :
    lineDist n c g = d n (dot n g - c).toNat := by
  have hc : ((c : ℤ) : ℝ) ≤ ((dot n g : ℤ) : ℝ) := by exact_mod_cast hg
  have h2 : (((dot n g - c).toNat : ℕ) : ℤ) = dot n g - c := Int.toNat_of_nonneg (by omega)
  rw [lineDist, d, abs_of_nonneg (by linarith)]
  congr 1
  have hcast : (((dot n g - c).toNat : ℕ) : ℝ) = (((dot n g - c : ℤ)) : ℝ) := by
    exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) h2
  rw [hcast]
  push_cast
  ring

/-- **Colle's enumeration property**: every lattice point of `ℋ(ℓ)` is at distance `d_i`
from `ℓ` for some `i`. -/
theorem exists_d_eq_lineDist {n : ℤ × ℤ} {c : ℤ} {g : ℤ × ℤ}
    (hg : g ∈ halfPlaneGE n c) : ∃ i : ℕ, lineDist n c g = d n i :=
  ⟨(dot n g - c).toNat, lineDist_eq_d hg⟩

/-- **The enumeration is onto the distance set** (so it is the *discrete* enumeration
Colle describes, not merely an upper family): every `d_i` is realised in `ℋ(ℓ)`. -/
theorem exists_mem_halfPlaneGE_lineDist_eq {n : ℤ × ℤ} (hn : Prim n) (c : ℤ) (i : ℕ) :
    ∃ g ∈ halfPlaneGE n c, lineDist n c g = d n i := by
  obtain ⟨g, hgeq⟩ := dot_surjective hn (c + i)
  have hmem : g ∈ halfPlaneGE n c := by
    simp only [halfPlaneGE, Set.mem_ofPred_eq, hgeq]
    omega
  refine ⟨g, hmem, ?_⟩
  rw [lineDist_eq_d (by simp only [hgeq]; omega), hgeq]
  congr 1
  omega

/-! ### The signed reading used by the shells

See the module docstring: the literal unsigned reading of Colle's shell constraint is
inconsistent with `d₀ = 0` and `Â_∞^{(0)} ⊆ Â_∞`.  `outerDist` is the signed distance,
positive strictly outside `ℋ(ℓ)`, and `outerDist_eq_lineDist_of_le` records that the two
readings agree exactly where the constraint bites. -/

/-- Signed distance to `ℓ`, positive on the far side of `ℋ(ℓ) = {c ≤ ⟨n,·⟩}`. -/
noncomputable def outerDist (n : ℤ × ℤ) (c : ℤ) (g : ℤ × ℤ) : ℝ :=
  (((c - dot n g : ℤ)) : ℝ) / lnorm n

theorem outerDist_eq_lineDist_of_le {n : ℤ × ℤ} {c : ℤ} {g : ℤ × ℤ} (h : dot n g ≤ c) :
    outerDist n c g = lineDist n c g := by
  rw [outerDist, lineDist, abs_of_nonpos (by
    have : ((dot n g : ℤ) : ℝ) ≤ ((c : ℤ) : ℝ) := by exact_mod_cast h
    linarith)]
  congr 1
  push_cast
  ring

/-- **The integer form of the shell constraint.**  `outerDist ≤ d_ε` is the integer
inequality `c - ε ≤ ⟨n,z⟩`. -/
theorem outerDist_le_d_iff {n : ℤ × ℤ} (hn : n ≠ 0) (c : ℤ) (g : ℤ × ℤ) (ε : ℕ) :
    outerDist n c g ≤ d n ε ↔ c - (ε : ℤ) ≤ dot n g := by
  have hpos := lnorm_pos hn
  rw [outerDist, d, div_le_div_iff_of_pos_right hpos]
  constructor
  · intro h
    have h' : ((c - dot n g : ℤ) : ℝ) ≤ (((ε : ℤ)) : ℝ) := by push_cast at h ⊢; linarith
    have := (Int.cast_le (R := ℝ)).mp h'
    omega
  · intro h
    have h' : ((c - dot n g : ℤ) : ℝ) ≤ (((ε : ℤ)) : ℝ) := by
      exact_mod_cast (by omega : (c - dot n g : ℤ) ≤ (ε : ℤ))
    push_cast at h' ⊢
    linarith

/-! ## §5. The shells `Â^{(ε)}`

Colle, statement of Lemma 3.5:

> `Â_∞^{(ε)} := {g + t v_{ℓ_{J-1}} : g ∈ Â_∞, t ∈ ℤ₊, dist(g + t v_{ℓ_{J-1}}, ℓ_J) ≤ d_ε}`

with the signed reading of §4, i.e. `c - ε ≤ ⟨n, ·⟩` for `n` the primitive inner normal
of `ℓ_J` at level `c`.  The lemmas below are exactly the shapes of the `shell`,
`shellInf`, `subShell`, `shellSubInf`, `shellFinite`, `shellInfZero` and `shellProper`
fields of `Nivat.Colle35.ChainData`. -/

/-- **Colle's `Â^{(ε)}`**: the set `A` swept along `v` and cut off `ε` lattice levels
past the line `ℓ_J = {⟨n,·⟩ = c}`. -/
def shell (A : Set (ℤ × ℤ)) (v n : ℤ × ℤ) (c : ℤ) (ε : ℕ) : Set (ℤ × ℤ) :=
  {z | ∃ g ∈ A, ∃ t : ℕ, z = g + (t : ℤ) • v ∧ c - (ε : ℤ) ≤ dot n z}

theorem mem_shell {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} {ε : ℕ} {z : ℤ × ℤ} :
    z ∈ shell A v n c ε ↔ ∃ g ∈ A, ∃ t : ℕ, z = g + (t : ℤ) • v ∧ c - (ε : ℤ) ≤ dot n z :=
  Iff.rfl

/-- The shell condition, in Colle's own metric form. -/
theorem mem_shell_iff_dist {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} (hn : n ≠ 0) {c : ℤ} {ε : ℕ}
    {z : ℤ × ℤ} :
    z ∈ shell A v n c ε ↔
      ∃ g ∈ A, ∃ t : ℕ, z = g + (t : ℤ) • v ∧ outerDist n c z ≤ d n ε := by
  simp only [mem_shell, outerDist_le_d_iff hn]

/-- `Â^{(ε)} ⊆ Â^{(ε')}` for `ε ≤ ε'`. -/
theorem shell_mono_eps {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} {ε ε' : ℕ} (h : ε ≤ ε') :
    shell A v n c ε ⊆ shell A v n c ε' := by
  rintro z ⟨g, hg, t, rfl, hz⟩
  exact ⟨g, hg, t, rfl, by omega⟩

/-- **`ChainData.shellSubInf`**: `Â_i^{(ε)} ⊆ Â_∞^{(ε)}`. -/
theorem shell_mono_set {A A' : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} {ε : ℕ} (h : A ⊆ A') :
    shell A v n c ε ⊆ shell A' v n c ε := by
  rintro z ⟨g, hg, t, rfl, hz⟩
  exact ⟨g, h hg, t, rfl, hz⟩

/-- **`ChainData.subShell`**: `Â ⊆ Â^{(ε)}` whenever `Â ⊆ ℋ(ℓ_J)`. -/
theorem subset_shell {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} (ε : ℕ)
    (hA : A ⊆ halfPlaneGE n c) : A ⊆ shell A v n c ε := by
  intro g hg
  exact ⟨g, hg, 0, by simp, by have := hA hg; simp only [halfPlaneGE,
    Set.mem_ofPred_eq] at this; omega⟩

theorem shell_subset_halfPlaneGE {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} {ε : ℕ} :
    shell A v n c ε ⊆ halfPlaneGE n (c - (ε : ℤ)) := by
  rintro z ⟨g, hg, t, rfl, hz⟩
  exact hz

/-- `A` is *swept-closed* for `v` past `ℓ_J`: sliding a point of `A` along `v` never
leaves `A` as long as one stays inside `ℋ(ℓ_J)`.  This holds for Colle's `Â_∞`, whose
support line in the direction `ℓ_J` is exactly `{⟨n,·⟩ = c}` and whose recession cone
contains `v_{ℓ_{J-1}}` on that side. -/
def SweptClosed (A : Set (ℤ × ℤ)) (v n : ℤ × ℤ) (c : ℤ) : Prop :=
  ∀ g ∈ A, ∀ t : ℕ, c ≤ dot n (g + (t : ℤ) • v) → g + (t : ℤ) • v ∈ A

/-- **`ChainData.shellInfZero`**: `Â^{(0)} = Â`, since `d₀ = 0`. -/
theorem shell_zero {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} (hA : A ⊆ halfPlaneGE n c)
    (hsw : SweptClosed A v n c) : shell A v n c 0 = A := by
  apply Set.Subset.antisymm
  · rintro z ⟨g, hg, t, rfl, hz⟩
    exact hsw g hg t (by simpa using hz)
  · exact subset_shell 0 hA

/-- **`ChainData.shellFinite`**: a shell of a finite set is finite, provided the sweeping
direction genuinely points out of `ℋ(ℓ_J)`. -/
theorem shell_finite {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} {ε : ℕ} (hA : A.Finite)
    (hv : dot n v < 0) : (shell A v n c ε).Finite := by
  classical
  rcases Set.eq_empty_or_nonempty A with rfl | hne
  · refine Set.Finite.subset (Set.finite_empty) ?_
    rintro z ⟨g, hg, -⟩
    exact absurd hg (Set.notMem_empty g)
  obtain ⟨b, hb⟩ : ∃ b : ℤ, ∀ g ∈ A, dot n g ≤ b := by
    have himg : ((fun g => dot n g) '' A).Finite := hA.image _
    obtain ⟨b, hb⟩ := himg.bddAbove
    exact ⟨b, fun g hg => hb ⟨g, hg, rfl⟩⟩
  set N : ℕ := (b - c + (ε : ℤ)).toNat with hN
  have hsub : shell A v n c ε ⊆
      (fun p : (ℤ × ℤ) × ℕ => p.1 + (p.2 : ℤ) • v) '' (A ×ˢ Set.Iic N) := by
    rintro z ⟨g, hg, t, rfl, hz⟩
    refine ⟨(g, t), ⟨hg, ?_⟩, rfl⟩
    have hdot : dot n (g + (t : ℤ) • v) = dot n g + (t : ℤ) * dot n v := by
      simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      ring
    rw [hdot] at hz
    have hbg := hb g hg
    have ht : (t : ℤ) ≤ b - c + (ε : ℤ) := by nlinarith [Int.natCast_nonneg t]
    simp only [Set.mem_Iic, hN]
    omega
  exact Set.Finite.subset (Set.Finite.image _ (hA.prod (Set.finite_Iic N))) hsub

/-- **`ChainData.shellProper`**: a shell that reaches a point outside `Â` is strictly
larger than `Â`. -/
theorem not_shell_subset {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} {ε : ℕ} {g : ℤ × ℤ}
    {t : ℕ} (hg : g ∈ A) (hout : g + (t : ℤ) • v ∉ A)
    (hlev : c - (ε : ℤ) ≤ dot n (g + (t : ℤ) • v)) : ¬ shell A v n c ε ⊆ A := by
  intro h
  exact hout (h ⟨g, hg, t, rfl, hlev⟩)

/-! ## §6. The generation filtration

Colle, last paragraph of the proof of Lemma 3.5:

> *"Since `𝒮_φ` is `η`-generating, by induction we get from (3.3) that
> `ϑ_i|Â_i^{(ε)} = x̂_per|Â_i^{(ε)}`, which contradicts the maximality of `Â_i`."*

The induction runs along a filtration of `Â_i^{(ε)}` in which every new site is the
distinguished point `gen` of a translate of the window `S` all of whose other points are
already filled.  `genFill` is that filtration, defined once and for all; it satisfies the
`fillZero` and `fillStep` fields of `Nivat.Colle35.ChainData` *by construction*, and
`subset_genClosure_of_rank` is the criterion under which `fillCover` holds. -/

/-- **The generation filtration.**  `genFill S gen X n` is the set of sites reachable from
`X` in at most `n` one-step generations by translates of the window `S` with distinguished
point `gen`. -/
def genFill (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) (X : Set (ℤ × ℤ)) : ℕ → Set (ℤ × ℤ)
  | 0 => X
  | n + 1 => genFill S gen X n ∪
      {z | ∃ t : ℤ × ℤ, z = gen + t ∧ ∀ b ∈ S.erase gen, b + t ∈ genFill S gen X n}

@[simp] theorem genFill_zero (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) (X : Set (ℤ × ℤ)) :
    genFill S gen X 0 = X := rfl

theorem genFill_succ (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) (X : Set (ℤ × ℤ)) (n : ℕ) :
    genFill S gen X (n + 1) = genFill S gen X n ∪
      {z | ∃ t : ℤ × ℤ, z = gen + t ∧ ∀ b ∈ S.erase gen, b + t ∈ genFill S gen X n} := rfl

/-- **`ChainData.fillStep`, by construction.** -/
theorem genFill_step (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) (X : Set (ℤ × ℤ)) (n : ℕ)
    (z : ℤ × ℤ) (hz : z ∈ genFill S gen X (n + 1)) :
    z ∈ genFill S gen X n ∨
      ∃ t : ℤ × ℤ, z = gen + t ∧ ∀ b ∈ S.erase gen, b + t ∈ genFill S gen X n := hz

theorem genFill_mono (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) (X : Set (ℤ × ℤ)) :
    Monotone (genFill S gen X) :=
  monotone_nat_of_le_succ fun n => by
    rw [genFill_succ]; exact Set.subset_union_left

/-- The set generated from `X` by the window `S`. -/
def genClosure (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) (X : Set (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  ⋃ n, genFill S gen X n

theorem subset_genClosure (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) (X : Set (ℤ × ℤ)) :
    X ⊆ genClosure S gen X := fun _ hz => Set.mem_iUnion.mpr ⟨0, hz⟩

/-- **The closure is closed under one generation step.**  This is where the finiteness of
the window `S` is used: a single `n` works for all of `S ∖ {gen}` at once. -/
theorem genClosure_step {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} {X : Set (ℤ × ℤ)} {t : ℤ × ℤ}
    (h : ∀ b ∈ S.erase gen, b + t ∈ genClosure S gen X) :
    gen + t ∈ genClosure S gen X := by
  classical
  have key : ∀ b ∈ S.erase gen, ∃ n, b + t ∈ genFill S gen X n :=
    fun b hb => Set.mem_iUnion.mp (h b hb)
  set F : ℤ × ℤ → ℕ :=
    fun b => if hb : ∃ n, b + t ∈ genFill S gen X n then Nat.find hb else 0 with hFdef
  have hF : ∀ b ∈ S.erase gen, b + t ∈ genFill S gen X (F b) := by
    intro b hb
    have hex := key b hb
    simp only [hFdef, dif_pos hex]
    exact Nat.find_spec hex
  refine Set.mem_iUnion.mpr ⟨(S.erase gen).sup F + 1, Or.inr ⟨t, rfl, fun b hb => ?_⟩⟩
  exact genFill_mono S gen X (Finset.le_sup hb) (hF b hb)

/-- **`ChainData.fillCover`, by well-founded rank.**  If every site of `Y` is either
already in `X` or is the distinguished point of a window translate whose other points are
in `X` or lower-ranked sites of `Y`, then `Y` is generated from `X`. -/
theorem subset_genClosure_of_rank {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} {X Y : Set (ℤ × ℤ)}
    (ρ : ℤ × ℤ → ℕ)
    (hstep : ∀ z ∈ Y, z ∈ X ∨ ∃ t : ℤ × ℤ, z = gen + t ∧
      ∀ b ∈ S.erase gen, b + t ∈ X ∨ (b + t ∈ Y ∧ ρ (b + t) < ρ z)) :
    Y ⊆ genClosure S gen X := by
  have key : ∀ m : ℕ, ∀ z ∈ Y, ρ z = m → z ∈ genClosure S gen X := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro z hz hrz
      rcases hstep z hz with hx | ⟨t, rfl, hb⟩
      · exact subset_genClosure S gen X hx
      · refine genClosure_step (fun b hbmem => ?_)
        rcases hb b hbmem with h1 | ⟨h2, h3⟩
        · exact subset_genClosure S gen X h1
        · exact ih (ρ (b + t)) (by omega) _ h2 rfl
  exact fun z hz => key (ρ z) z hz rfl

/-- Non-vacuity: one generation step really does add a point. -/
theorem genClosure_nontrivial :
    ((1 : ℤ), (0 : ℤ)) ∈
      genClosure ({(0, 0), (1, 0)} : Finset (ℤ × ℤ)) ((1 : ℤ), (0 : ℤ))
        ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ∧
    ((1 : ℤ), (0 : ℤ)) ∉ ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) := by
  constructor
  · refine Set.mem_iUnion.mpr ⟨1, Or.inr ⟨(0, 0), by simp, fun b hb => ?_⟩⟩
    have : b = ((0 : ℤ), (0 : ℤ)) := by
      have := Finset.mem_erase.mp hb
      have h2 := this.2
      simp only [Finset.mem_insert, Finset.mem_singleton] at h2
      rcases h2 with h | h
      · exact h
      · exact absurd h this.1
    subst this
    simp
  · simp only [Set.mem_singleton_iff, Prod.ext_iff]
    norm_num

/-! ## §7. What this file does **not** do

* It does not construct Colle's chain `B' ⊂ B₁ ⊂ A₁ ⊂ ⋯`, and it does not prove
  `Nivat.Colle35.exists_chainData`.  Those need the dynamical input (the generating set,
  the failure of agreement on the half-strip) on top of the geometry here.
* `SweptClosed` is a hypothesis on `Â`, not a theorem: it says the region is stable under
  sliding along `v` inside `ℋ(ℓ_J)`.  Proving it for the `Â_∞` produced by the chain
  construction is part of that construction, not of this file.
* The `IsRegion` classification results left open in `LatticeEdges.lean` (an
  `(ℓ,ℓ')`-region has finitely many edges; its edge set is an interval in the cyclic
  order) are still open here.  In particular this file does **not** prove that
  `shell A v n c ε` is again an `(ℓ_ι, ℓ_J)`-region, which Colle asserts at
  `b3_colle2.txt:442`.  Nothing in the main line consumes that assertion: the shells are
  used only set-theoretically, through `reach` and the generation filtration.
-/

end Nivat.MaxEnv
