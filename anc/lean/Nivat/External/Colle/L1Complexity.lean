/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Data
import Nivat.AppendixD

/-!
# `L1Complexity`: conjunct 7 of leaf L1 (`L1Data.hPQ`) from the Lemma 2.4 deficit

`L1Data.hPQ` (`L1Data.lean:107`) is

    P ξ S₁ ≤ P ξ Q + pw,   Q = S₁.filter fun z => inner2 n z < cmax

i.e. *cutting the `n`-maximal face off the generating window costs at most `pw` patterns*.

This file proves it, with `pw := (Nivat.R2.face S₁ n cmax).card - 1`, from two inputs that
`case1_claim46_and_selection` (`RegionSteps.lean:866`) already has in its hypotheses:

* `hdef` (`RegionSteps.lean:873-879`) — the Lemma 2.4 boundary deficit for the *untranslated*
  generating set `S`, exported by `Nivat.R2.exists_generatingSet_biOriented`;
* the fact that `S₁` is Collé's `𝒯`, **a translate of `𝒮`** (`b3_colle2.txt:824`).

The whole content is that both sides of the deficit are translation invariant, so the bound
for `S` transports to `S₁` verbatim.  The transport uses `Nivat.P_translate`
(`AppendixD.lean:123`) plus the two commutation lemmas proved here
(`filter_lt_image_add`, `face_image_add`), and the natural-number arithmetic is the same
`Nat.sub_le_iff_le_add` step as `Nivat.ColleReg.deficit_to_lemma41_shape`
(`RegionSteps.lean:393`) — that lemma does the conversion at the **minimal** face of an
untranslated `S`, which is the shape Lemma 4.1 consumes directly; `hPQ` needs the **maximal**
face (`R2Orientation.lean:92`'s sign convention) of a **translate**, so neither half of it is
reusable as stated.

## Scope — read before citing

* This is a proof of **conjunct 7 only**, and it is conditional on the translate hypothesis.
  `L1Data` (`L1Data.lean:64`) carries **neither** `hdef` **nor** any field saying `S₁` is a
  translate of `S`, so `hPQ` is *not* derivable from the other thirteen `L1Data` fields.
  `not_hPQ_of_no_deficit` below is the kernel-checked witness of that: a lattice-convex `S₁`
  satisfying every conjunct of `L1Data.hQ_edge` (with a `u'` that is primitive and normal to
  `n`) for which `hPQ` **fails** at Collé's own `pw = |face| - 1`.  Whoever builds the `L1Data`
  must therefore thread `hdef` and the translate through; it cannot be recovered later.
* Nothing here says the `n` of `hQ_edge` is a good normal, that the face is an *edge*
  (`2 ≤ card`, i.e. `0 < pw`), or that conjunct 8's run exists.  Those are
  `Nivat.ColleReg.L1Data.pw_pos_of_two_le_face_card` (`L1Fields.lean:328`) and the open
  question recorded in `LEAF-L1.md`; `hPQ` is *weaker* as `pw` grows, so it is the one
  `pw`-conjunct that never obstructs.
-/

namespace Nivat.L1Complexity

open Nivat

variable {ξ : Config ℤ}

/-! ## Translating a window shifts the cut level

Both the strict-inequality filter and the face commute with `· + v` at the cost of moving the
level by `inner2 n v`.  These are the only geometric facts in the file.
-/

/-- **The cut commutes with translation.**  `(S + v)` cut at `cmax` is the translate of `S`
cut at `cmax - ⟨n, v⟩`. -/
theorem filter_lt_image_add (S : Finset (ℤ × ℤ)) (n : ℝ × ℝ) (v : ℤ × ℤ) (c : ℝ) :
    ((S.image (· + v)).filter fun z => inner2 n z < c)
      = (S.filter fun z => inner2 n z < c - inner2 n v).image (· + v) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hlt⟩
    rw [inner2_add] at hlt
    exact ⟨w, ⟨hw, by linarith⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hlt⟩, rfl⟩
    refine ⟨⟨w, hw, rfl⟩, ?_⟩
    rw [inner2_add]
    linarith

/-- **The exposed face commutes with translation.** -/
theorem face_image_add (S : Finset (ℤ × ℤ)) (n : ℝ × ℝ) (v : ℤ × ℤ) (c : ℝ) :
    Nivat.R2.face (S.image (· + v)) n c
      = (Nivat.R2.face S n (c - inner2 n v)).image (· + v) := by
  ext z
  simp only [Nivat.R2.face, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, heq⟩
    rw [inner2_add] at heq
    exact ⟨w, ⟨hw, by linarith⟩, rfl⟩
  · rintro ⟨w, ⟨hw, heq⟩, rfl⟩
    refine ⟨⟨w, hw, rfl⟩, ?_⟩
    rw [inner2_add]
    linarith

/-- The translated face has the same cardinality: `· + v` is injective. -/
theorem face_card_image_add (S : Finset (ℤ × ℤ)) (n : ℝ × ℝ) (v : ℤ × ℤ) (c : ℝ) :
    (Nivat.R2.face (S.image (· + v)) n c).card
      = (Nivat.R2.face S n (c - inner2 n v)).card := by
  rw [face_image_add, Finset.card_image_of_injective _ (add_left_injective v)]

/-! ## Conjunct 7 -/

/-- **`L1Data.hPQ` for a translated generating window** (`L1Data.lean:107`, conjunct 7 of
`case1_claim46_and_selection`, `RegionSteps.lean:942`).

`hdef` is the Lemma 2.4 boundary deficit exactly as `case1_claim46_and_selection` receives it
(`RegionSteps.lean:873-879`); `hle` and `hface` are two of the five conjuncts of
`L1Data.hQ_edge` (`L1Data.lean:98-99`), so the leaf pays nothing extra for them.  The witness
produced for `pw` is Collé's own `p' = |𝒮 ∩ ℓ'_𝒮| − 1` (`b3_colle2.txt:645`) read on `𝒯`.

The minimal-face premises of `hdef` are discharged internally by `Finset.exists_min_image`,
as in `Nivat.ColleReg.deficit_to_lemma41_shape` (`RegionSteps.lean:406`); only the
maximal-face conjunct of `hdef` is used. -/
theorem hPQ_of_translate_deficit {S S₁ : Finset (ℤ × ℤ)} {n : ℝ × ℝ} {cmax : ℝ} {v : ℤ × ℤ}
    (hS₁ : S₁ = S.image (· + v))
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
      (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face S n cmax).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face S n cmin).card - 1)
    (hle : ∀ z ∈ S₁, inner2 n z ≤ cmax)
    (hface : (Nivat.R2.face S₁ n cmax).Nonempty) :
    P ξ S₁ ≤ P ξ (S₁.filter fun z => inner2 n z < cmax)
      + ((Nivat.R2.face S₁ n cmax).card - 1) := by
  subst hS₁
  set c' : ℝ := cmax - inner2 n v with hc'
  -- the bound transported to `S`
  have hle' : ∀ z ∈ S, inner2 n z ≤ c' := by
    intro z hz
    have h := hle (z + v) (Finset.mem_image_of_mem _ hz)
    rw [inner2_add] at h
    rw [hc']
    linarith
  have hfaceS : (Nivat.R2.face S n c').Nonempty := by
    rw [face_image_add] at hface
    obtain ⟨z, hz⟩ := hface
    obtain ⟨w, hw, -⟩ := Finset.mem_image.mp hz
    exact ⟨w, hw⟩
  have hSne : S.Nonempty := hfaceS.mono (Nivat.R2.face_subset _ _ _)
  obtain ⟨zmin, hzminS, hzmin⟩ := S.exists_min_image (fun z => inner2 n z) hSne
  have hminface : (Nivat.R2.face S n (inner2 n zmin)).Nonempty :=
    ⟨zmin, Finset.mem_filter.mpr ⟨hzminS, rfl⟩⟩
  have h := (hdef n c' (inner2 n zmin) hle' hfaceS hzmin hminface).1
  rw [filter_lt_image_add, face_card_image_add, P_translate, P_translate, ← hc']
  omega

/-- **`L1Data.hPQ` at the structure's own interface** (`L1Data.lean:107`), where `Q` is an
opaque field and `hQ` is the last conjunct of `L1Data.hQ_edge` (`L1Data.lean:100`).

This is the form a builder of `L1Data` can hand over directly, with
`pw := (Nivat.R2.face S₁ n cmax).card - 1`.  It is also literally the `hPQ` argument of
`Nivat.ColleReg.L1Data.ofEdgeRun` (`L1Fields.lean:167`) at that `pw`, since `ofEdgeRun`
derives `Q` as the same filter. -/
theorem hPQ_of_hQ_edge {S S₁ Q : Finset (ℤ × ℤ)} {n : ℝ × ℝ} {cmax : ℝ} {v : ℤ × ℤ}
    (hS₁ : S₁ = S.image (· + v))
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
      (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face S n cmax).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face S n cmin).card - 1)
    (hle : ∀ z ∈ S₁, inner2 n z ≤ cmax)
    (hface : (Nivat.R2.face S₁ n cmax).Nonempty)
    (hQ : Q = S₁.filter fun z => inner2 n z < cmax) :
    P ξ S₁ ≤ P ξ Q + ((Nivat.R2.face S₁ n cmax).card - 1) := by
  subst hQ
  exact hPQ_of_translate_deficit hS₁ hdef hle hface

/-! ## `hdef` is load-bearing: `hPQ` is false without it

`L1Data` carries no complexity hypothesis at all, so it is worth recording in the kernel that
conjunct 7 is not a consequence of the geometry in `L1Data.hQ_edge`.

The witness is the L-shaped window `S₁ = {(0,0), (1,0), (0,1)}` with `n = (0,1)` (so
`inner2 n z = z.2`), `cmax = 1`, `u' = (1,0)`.  Every conjunct of `hQ_edge` holds — `n ≠ 0`,
`inner2 n u' = 0`, `1` bounds the level, the face `{(0,1)}` is non-empty — and `S₁` is even
lattice-convex; but the face is a **vertex**, so Collé's `pw = |face| - 1` is `0`, while the
configuration `ξ z = if z.2 = 0 then 1 else 0` has three patterns on `S₁` and only two on the
cut `Q = {(0,0), (1,0)}`.

This does **not** contradict the theorem above: `ξ` here has no generating set with the
Lemma 2.4 deficit at this normal (it is periodic, hence not a minimal counterexample), which
is exactly what `hdef` would have supplied.  Scope, per `PROTOCOL.md` §11: what is refuted is
"conjunct 7 follows from conjuncts 1–6 of `L1Data` plus lattice convexity", a statement
nobody in the repo asserts but which the absence of a deficit field in `L1Data` invites.
-/

/-- The refuting configuration: the indicator of the horizontal axis `z.2 = 0`. -/
def rowConfig : Config ℤ := fun z => if z.2 = 0 then 1 else 0

/-- The refuting window: an L-shaped triomino. -/
def Lwin : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (0, 1)}

/-- The vertical normal. -/
def nvert : ℝ × ℝ := (0, 1)

theorem inner2_nvert (z : ℤ × ℤ) : inner2 nvert z = (z.2 : ℝ) := by
  simp [inner2, nvert]

theorem mem_Lwin {z : ℤ × ℤ} : z ∈ Lwin ↔ z = (0, 0) ∨ z = (1, 0) ∨ z = (0, 1) := by
  simp [Lwin]

/-- The cut of `Lwin` below level `1` is its bottom row. -/
theorem Lwin_cut : (Lwin.filter fun z => inner2 nvert z < 1) = {(0, 0), (1, 0)} := by
  ext z
  simp only [Finset.mem_filter, mem_Lwin, inner2_nvert, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h | h | h, hlt⟩ <;> subst h
    · exact Or.inl rfl
    · exact Or.inr rfl
    · norm_num at hlt
  · rintro (h | h) <;> subst h <;> refine ⟨by tauto, by norm_num⟩

/-- The face of `Lwin` at level `1` is the single vertex `(0,1)`. -/
theorem Lwin_face : Nivat.R2.face Lwin nvert 1 = {(0, 1)} := by
  ext z
  simp only [Nivat.R2.face, Finset.mem_filter, mem_Lwin, inner2_nvert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h | h | h, heq⟩ <;> subst h
    · norm_num at heq
    · norm_num at heq
    · rfl
  · rintro rfl
    exact ⟨by tauto, by norm_num⟩

/-- `Lwin` is lattice-convex: it is `{p : 0 ≤ p.1, 0 ≤ p.2, p.1 + p.2 ≤ 1} ∩ ℤ²`. -/
theorem latticeConvex_Lwin : Nivat.LatticeConvex Lwin := by
  set regA : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1} with hregA
  set regB : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.2} with hregB
  set regC : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 + p.2 ≤ 1} with hregC
  set region : Set (ℝ × ℝ) := regA ∩ (regB ∩ regC) with hregion
  have hconv : Convex ℝ region := by
    have h1 : Convex ℝ regA :=
      convex_halfSpace_ge (f := fun p : ℝ × ℝ => p.1) (LinearMap.fst ℝ ℝ ℝ).isLinear 0
    have h2 : Convex ℝ regB :=
      convex_halfSpace_ge (f := fun p : ℝ × ℝ => p.2) (LinearMap.snd ℝ ℝ ℝ).isLinear 0
    have h3 : Convex ℝ regC :=
      convex_halfSpace_le (f := fun p : ℝ × ℝ => p.1 + p.2)
        (((LinearMap.fst ℝ ℝ ℝ) + (LinearMap.snd ℝ ℝ ℝ))).isLinear 1
    exact h1.inter (h2.inter h3)
  have hsub : Conv Lwin ⊆ region := by
    refine convexHull_min ?_ hconv
    rintro _ ⟨w, hw, rfl⟩
    simp only [Lwin, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_⟩ <;>
        simp only [hregA, hregB, hregC, Set.mem_ofPred_eq, toReal] <;> norm_num
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hsub hz
  simp only [hregA, hregB, hregC, Set.mem_ofPred_eq, toReal] at h1 h2 h3
  have i1 : (0 : ℤ) ≤ z.1 := by exact_mod_cast h1
  have i2 : (0 : ℤ) ≤ z.2 := by exact_mod_cast h2
  have i3 : z.1 + z.2 ≤ (1 : ℤ) := by exact_mod_cast h3
  refine mem_Lwin.mpr ?_
  have : (z.1 = 0 ∧ z.2 = 0) ∨ (z.1 = 1 ∧ z.2 = 0) ∨ (z.1 = 0 ∧ z.2 = 1) := by omega
  rcases this with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl (Prod.ext hx hy)
  · exact Or.inr (Or.inl (Prod.ext hx hy))
  · exact Or.inr (Or.inr (Prod.ext hx hy))

theorem primitive_e1 : Primitive ((1 : ℤ), (0 : ℤ)) := isCoprime_one_left

theorem range_rowConfig_finite : (Set.range rowConfig).Finite := by
  refine Set.Finite.subset ((Set.finite_singleton (0 : ℤ)).insert 1) ?_
  rintro _ ⟨z, rfl⟩
  by_cases h : z.2 = 0 <;> simp [rowConfig, h]

/-- The bottom row sees only two patterns: along it `rowConfig` is constant. -/
theorem P_Lwin_cut_le : P rowConfig ({(0, 0), (1, 0)} : Finset (ℤ × ℤ)) ≤ 2 := by
  set Qc : Finset (ℤ × ℤ) := {(0, 0), (1, 0)} with hQc
  have hq2 : ∀ q ∈ Qc, q.2 = 0 := by
    intro q hq
    simp only [hQc, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with h | h <;> subst h <;> rfl
  have hsub : patterns rowConfig Qc ⊆
      {(fun _ => 1 : ↥Qc → ℤ), (fun _ => 0 : ↥Qc → ℤ)} := by
    rintro _ ⟨u, rfl⟩
    by_cases h : u.2 = 0
    · refine Or.inl ?_
      funext q
      have hq0 : ((q : ℤ × ℤ)).2 = 0 := hq2 (q : ℤ × ℤ) q.2
      simp [pattern, rowConfig, Prod.snd_add, hq0, h]
    · refine Or.inr ?_
      funext q
      have hq0 : ((q : ℤ × ℤ)).2 = 0 := hq2 (q : ℤ × ℤ) q.2
      simp [pattern, rowConfig, Prod.snd_add, hq0, h]
  calc P rowConfig Qc ≤ ({(fun _ => 1 : ↥Qc → ℤ), (fun _ => 0 : ↥Qc → ℤ)} : Set _).ncard :=
        Set.ncard_le_ncard hsub ((Set.finite_singleton _).insert _)
    _ ≤ ({(fun _ => 0 : ↥Qc → ℤ)} : Set _).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

/-- The L-shaped window sees three patterns: the two rows can be occupied separately. -/
theorem three_le_P_Lwin : 3 ≤ P rowConfig Lwin := by
  have h00 : ((0, 0) : ℤ × ℤ) ∈ Lwin := mem_Lwin.mpr (Or.inl rfl)
  have h01 : ((0, 1) : ℤ × ℤ) ∈ Lwin := mem_Lwin.mpr (Or.inr (Or.inr rfl))
  set a : ↥Lwin := ⟨(0, 0), h00⟩ with ha
  set b : ↥Lwin := ⟨(0, 1), h01⟩ with hb
  set p1 := pattern rowConfig Lwin (0, 0) with hp1
  set p2 := pattern rowConfig Lwin (0, -1) with hp2
  set p3 := pattern rowConfig Lwin (0, 5) with hp3
  have e1a : p1 a = 1 := by simp [hp1, ha, pattern, rowConfig]
  have e2a : p2 a = 0 := by norm_num [hp2, ha, pattern, rowConfig]
  have e3a : p3 a = 0 := by norm_num [hp3, ha, pattern, rowConfig]
  have e2b : p2 b = 1 := by norm_num [hp2, hb, pattern, rowConfig]
  have e3b : p3 b = 0 := by norm_num [hp3, hb, pattern, rowConfig]
  have h12 : p1 ≠ p2 := fun h => by rw [h, e2a] at e1a; exact zero_ne_one e1a
  have h13 : p1 ≠ p3 := fun h => by rw [h, e3a] at e1a; exact zero_ne_one e1a
  have h23 : p2 ≠ p3 := fun h => by rw [h, e3b] at e2b; exact zero_ne_one e2b
  have hcard : ({p1, p2, p3} : Set (↥Lwin → ℤ)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨p1, p2, p3, h12, h13, h23, rfl⟩
  have hsub : ({p1, p2, p3} : Set (↥Lwin → ℤ)) ⊆ patterns rowConfig Lwin := by
    rintro f (rfl | rfl | rfl)
    · exact ⟨(0, 0), rfl⟩
    · exact ⟨(0, -1), rfl⟩
    · exact ⟨(0, 5), rfl⟩
  have := Set.ncard_le_ncard hsub (patterns_finite_of_range_finite range_rowConfig_finite Lwin)
  rwa [hcard] at this

/-- **Conjunct 7 does not follow from the geometry of conjuncts 4–6 plus lattice convexity.**

Every hypothesis of `L1Data.hQ_edge` (`L1Data.lean:95-100`) is met — `n ≠ 0`,
`inner2 n u' = 0`, the level bound, a non-empty face — together with `Primitive u'`
(conjunct 6) and `LatticeConvex S₁` (which conjunct 1 supplies); yet `hPQ` fails at Collé's
own width `pw = |face| - 1`.

The face here is a **vertex**, so `pw = 0`; the obstruction is that `rowConfig` has no
generating set with the Lemma 2.4 deficit at this normal, which is precisely the input
`hPQ_of_translate_deficit` takes as `hdef`.  See the section docstring for scope. -/
theorem not_hPQ_of_no_deficit :
    ∃ (ξ : Config ℤ) (S₁ : Finset (ℤ × ℤ)) (n : ℝ × ℝ) (cmax : ℝ) (u' : ℤ × ℤ),
      n ≠ 0 ∧
      inner2 n u' = 0 ∧
      Primitive u' ∧
      Nivat.LatticeConvex S₁ ∧
      (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧
      ¬ (P ξ S₁ ≤ P ξ (S₁.filter fun z => inner2 n z < cmax)
          + ((Nivat.R2.face S₁ n cmax).card - 1)) := by
  refine ⟨rowConfig, Lwin, nvert, 1, (1, 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [nvert, Prod.ext_iff]
  · simp [inner2, nvert]
  · exact primitive_e1
  · exact latticeConvex_Lwin
  · intro z hz
    rw [inner2_nvert]
    rcases mem_Lwin.mp hz with h | h | h <;> subst h <;> norm_num
  · exact ⟨(0, 1), by rw [Lwin_face]; exact Finset.mem_singleton_self _⟩
  · rw [Lwin_cut, Lwin_face, Finset.card_singleton]
    have h1 := three_le_P_Lwin
    have h2 := P_Lwin_cut_le
    omega

end Nivat.L1Complexity
