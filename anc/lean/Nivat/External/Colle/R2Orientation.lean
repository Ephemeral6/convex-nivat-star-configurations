import Nivat.External.Colle.Interfaces

/-!
# The orientation gap of route R2

Route R2 tries to replace Colle's Lemma 3.5 by the chain

  `ℓ ∈ ONED ξ` → Colle Lemma 2.4 → Colle Prop. 2.10 → Colle Prop. 2.12 → `±ℓ ∈ ONED ξ`.

Colle's Proposition 2.10 (arXiv:1909.08195v4, l. 359) carries, besides the Lemma 2.4
deficit bound, the extra hypothesis

  `|S ∩ ℓ_S| ≤ |S ∩ −ℓ_S|`,

which an unoriented line satisfies for at most one of its two orientations.  This file
records what is *provable* about that hypothesis in the present vocabulary, and states
precisely what is not.

## What is proved here

* `face_neg_level`, `upperBound_neg_iff` — the sign-convention certification.  The repo's
  supporting-face convention (`∀ z ∈ S, inner2 w z ≤ c`, i.e. the **maximal** face for `w`)
  is related to Colle's (`S ⊂ H(ℓ_S)`, i.e. the **minimal** face for the left normal
  `n_ℓ`) by `w = -n_ℓ`.  Under that dictionary `S ∩ ℓ_S` is the `w`-maximal face and
  `S ∩ −ℓ_S` is the `(-w)`-maximal face.
* `exists_generatingSet_biOriented` — a single generating set satisfies the Lemma 2.4
  deficit bound simultaneously at **both** orientations of every line.  Equivalently:
  conditions (ii) and (iii) of the Cyr–Kra notion of an `ℓ`-balanced set (Def. 4.5 of
  arXiv:1208.4090) are orientation-free at low convex complexity.  Only condition (i),
  the balance condition `Balanced` below, is orientation-dependent — that is the gap.
* `two_le_face_card_of_mem_ONED` — Colle Lemma 2.3 in face-cardinality form: the face of a
  generating set exposed by a *one-sided nonexpansive* normal is never a single vertex.
  So the gap only ever bites on edges, never on vertices.
* `neg_notMem_ONED_of_lower_face_card_le_one` — **the hard obstruction.**  If the face of a
  generating set opposite to `w` is a single lattice point (the extreme failure of Colle's
  hypothesis), then `-w ∉ ONED ξ`, i.e. the conclusion route R2 is trying to reach at this
  line is *false*.  The hypothesis is therefore not a removable artefact of Colle's
  write-up; attack route (d) is answered in the negative.
* `two_le_both_faces_of_biONED` — if both orientations are already nonexpansive, both
  faces are edges; Colle's hypothesis is a genuine extra constraint on the pair.
* `balanced_of_card_le_one` — the balance condition is vacuous on vertices.
* `face_card_eq_of_centrallySymmetric` — a centrally symmetric window has equal opposite
  faces, hence satisfies Colle's hypothesis at *both* orientations.  This is the exact
  content of attack route (c); see the audit note for why the symmetrisation cannot be
  carried out (the minimal-descent generating set has zero discrepancy budget left).

## What is NOT proved here

`BalancedGeneratingGoal` states the missing step: for the given `ONED` orientation, a
generating set that is *balanced* for it.  It is a `def` used by nothing; no `axiom`,
no `sorry`, and no theorem of this file assumes it.  In Cyr–Kra it is their Lemma 4.7,
and they state verbatim (arXiv:1208.4090, just before Lemma 4.7) that

  "Showing the existence of an `ℓ`-balanced set for `η` is the **second use of the
   stronger hypothesis on complexity**",

that hypothesis being `P_η(R_{n,k}) ≤ nk/2`.  At `P_η(S) ≤ |S|` it is open.
-/

namespace Nivat.R2

open Nivat.Colle

/-! ### Elementary `inner2` algebra -/

theorem inner2_neg_left (w : ℝ × ℝ) (z : ℤ × ℤ) : inner2 (-w) z = -inner2 w z := by
  simp only [inner2, Prod.fst_neg, Prod.snd_neg]
  ring

theorem inner2_sub (w : ℝ × ℝ) (m z : ℤ × ℤ) :
    inner2 w (m - z) = inner2 w m - inner2 w z := by
  simp only [inner2, Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

/-! ### Faces -/

/-- The face of `S` exposed by the normal `w` at level `c`.  When `c` is the maximum of
`inner2 w` on `S` this is the supporting face of `S` in direction `w`. -/
noncomputable def face (S : Finset (ℤ × ℤ)) (w : ℝ × ℝ) (c : ℝ) : Finset (ℤ × ℤ) :=
  S.filter fun z => inner2 w z = c

theorem mem_face {S : Finset (ℤ × ℤ)} {w : ℝ × ℝ} {c : ℝ} {z : ℤ × ℤ} :
    z ∈ face S w c ↔ z ∈ S ∧ inner2 w z = c := Finset.mem_filter

theorem face_subset (S : Finset (ℤ × ℤ)) (w : ℝ × ℝ) (c : ℝ) : face S w c ⊆ S :=
  Finset.filter_subset _ _

/-! ### Sign-convention certification

Colle's half plane is `H(ℓ) = {g : ⟨g, n_ℓ⟩ ≥ 0}` with `n_ℓ` the left normal of the
oriented line `ℓ`, and `ℓ_S` is the parallel line with `S ⊂ H(ℓ_S)`; so `S ∩ ℓ_S` is the
face of `S` *minimising* `⟨·, n_ℓ⟩`.  This repo's `sideOf w = {z : inner2 w z ≤ 0}`, so
`w ∈ ONED ξ` corresponds to `ℓ ∈ nexpd(η)` with `w = -n_ℓ`, and the minimal face for
`n_ℓ` is the **maximal** face for `w`, which is the convention of
`Nivat.Colle.exists_generatingSet_with_boundary_deficit`.  The next two lemmas are the
machine-checked form of that translation. -/

/-- The face exposed by `-w` at level `-c` is the face exposed by `w` at level `c`.
Consequently the `(-w)`-maximal face of `S` is its `w`-minimal face — Colle's
`S ∩ −ℓ_S` in the repo's maximal-face convention. -/
theorem face_neg_level (S : Finset (ℤ × ℤ)) (w : ℝ × ℝ) (c : ℝ) :
    face S (-w) (-c) = face S w c := by
  refine Finset.filter_congr fun z _ => ?_
  rw [inner2_neg_left]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- `-c` bounds `inner2 (-w)` from above on `S` exactly when `c` bounds `inner2 w` from
below on `S`. -/
theorem upperBound_neg_iff {S : Finset (ℤ × ℤ)} {w : ℝ × ℝ} {c : ℝ} :
    (∀ z ∈ S, inner2 (-w) z ≤ -c) ↔ ∀ z ∈ S, c ≤ inner2 w z := by
  constructor
  · intro h z hz
    have := h z hz
    rw [inner2_neg_left] at this
    linarith
  · intro h z hz
    have := h z hz
    rw [inner2_neg_left]
    linarith

theorem filter_lt_neg (S : Finset (ℤ × ℤ)) (w : ℝ × ℝ) (c : ℝ) :
    (S.filter fun z => inner2 (-w) z < -c) = S.filter fun z => c < inner2 w z := by
  refine Finset.filter_congr fun z _ => ?_
  rw [inner2_neg_left]
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ### Both orientations carry the Lemma 2.4 deficit bound

The deficit bound of `Nivat.Colle.exists_generatingSet_with_boundary_deficit` is stated
for *every* normal, so instantiating it at `w` and at `-w` gives the bound at both
supporting faces of the same line at once.  In Cyr–Kra's terminology this says that
conditions (ii) and (iii) of an `ℓ`-balanced set (Def. 4.5, arXiv:1208.4090) hold for
both orientations of every line as soon as the configuration has low convex complexity:
(ii) because every vertex of a generating set is generated, (iii) because that is exactly
the deficit bound below.  The orientation-sensitive condition is (i) alone. -/
theorem exists_generatingSet_biOriented {A : Type*} {ξ : Config A}
    (hfin : (Set.range ξ).Finite) (hlow : LowConvexComplexity ξ) :
    ∃ S : Finset (ℤ × ℤ), IsGeneratingSet ξ S ∧ P ξ S ≤ S.card ∧
      ∀ (w : ℝ × ℝ) (cmax cmin : ℝ),
        (∀ z ∈ S, inner2 w z ≤ cmax) → (face S w cmax).Nonempty →
        (∀ z ∈ S, cmin ≤ inner2 w z) → (face S w cmin).Nonempty →
          P ξ S - P ξ (S.filter fun z => inner2 w z < cmax) ≤ (face S w cmax).card - 1 ∧
          P ξ S - P ξ (S.filter fun z => cmin < inner2 w z) ≤ (face S w cmin).card - 1 := by
  obtain ⟨S, hgen, hlowS, hdef⟩ := exists_generatingSet_with_boundary_deficit hfin hlow
  refine ⟨S, hgen, hlowS, ?_⟩
  intro w cmax cmin hmax hmaxne hmin hminne
  refine ⟨hdef w cmax hmax hmaxne, ?_⟩
  have hbound : ∀ z ∈ S, inner2 (-w) z ≤ -cmin := upperBound_neg_iff.mpr hmin
  have hne : (S.filter fun z => inner2 (-w) z = -cmin).Nonempty := by
    rw [show (S.filter fun z => inner2 (-w) z = -cmin) = face S w cmin from
      face_neg_level S w cmin]
    exact hminne
  have h := hdef (-w) (-cmin) hbound hne
  rw [filter_lt_neg S w cmin,
    show (S.filter fun z => inner2 (-w) z = -cmin) = face S w cmin from
      face_neg_level S w cmin] at h
  exact h

/-! ### Colle Lemma 2.3 in face-cardinality form

If the supporting face of a generating set in direction `w` is a single lattice point,
then `w` is *not* a one-sided nonexpansive direction.  Contrapositively, for every
`w ∈ ONED ξ` the exposed face has at least two points, i.e. it is an edge.  This bounds
how badly the orientation hypothesis can fail: the side that sits in `ONED` always
carries an edge. -/
theorem two_le_face_card_of_mem_ONED {A : Type*} {ξ : Config A} {S : Finset (ℤ × ℤ)}
    (hgen : IsGeneratingSet ξ S) {w : ℝ × ℝ} {c : ℝ} (hmax : ∀ z ∈ S, inner2 w z ≤ c)
    (hface : (face S w c).Nonempty) (hw : w ∈ ONED ξ) : 2 ≤ (face S w c).card := by
  classical
  by_contra hlt
  push Not at hlt
  have hcard : (face S w c).card = 1 := by
    have := Finset.card_pos.mpr hface
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have haS : a ∈ S := face_subset S w c (ha ▸ Finset.mem_singleton_self a)
  have hac : inner2 w a = c := (mem_face.mp (ha ▸ Finset.mem_singleton_self a)).2
  -- with a singleton face, deleting the exposed point is a strict half-plane cut
  have herase : S.erase a = S.filter fun z => inner2 w z < c := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hza, hzS⟩
      refine ⟨hzS, lt_of_le_of_ne (hmax z hzS) ?_⟩
      intro heq
      exact hza (Finset.mem_singleton.mp (ha ▸ mem_face.mpr ⟨hzS, heq⟩))
    · rintro ⟨hzS, hlt'⟩
      exact ⟨fun h => absurd (h ▸ hlt') (by rw [hac]; exact lt_irrefl c), hzS⟩
  have hdel : LatticeConvex (S.erase a) := by
    rw [herase]
    exact latticeConvex_filter_inner2_lt hgen.2.1 w c
  have hgenA : GeneratesAt ξ S a := hgen.2.2 a haS hdel
  refine not_mem_ONED_of_generatesAt hgenA (w := w) ?_ hw
  intro b hb
  rw [hac]
  rw [herase] at hb
  exact (Finset.mem_filter.mp hb).2

/-! ### The hard obstruction: the extreme failure case refutes R2's own target

Colle's hypothesis `|S ∩ ℓ_S| ≤ |S ∩ −ℓ_S|` fails most brutally when the opposite face
`S ∩ −ℓ_S` is a single lattice point.  The next two theorems show that in *exactly* that
situation the conclusion R2 wants at this line is false: a singleton opposite face makes
the opposite orientation non-nonexpansive, by Colle Lemma 2.3.

So the hypothesis is not a removable artefact of Colle's write-up.  Any hypothesis-free
version of Prop. 2.10 would have to produce, in the singleton case, a *doubly* periodic
element of the orbit closure — since the one-sidedly periodic conclusion it would
otherwise yield is refuted here.  Attack route (a) ("just get both orientations") is
therefore circular in a precise sense, and attack route (d) ("the hypothesis is not
really needed") is answered in the negative. -/

/-- If the face of a generating set exposed by `-w` is a single lattice point, then `-w`
is not a one-sided nonexpansive direction.  Contrapositive of Colle Lemma 2.3. -/
theorem neg_notMem_ONED_of_face_card_le_one {A : Type*} {ξ : Config A}
    {S : Finset (ℤ × ℤ)} (hgen : IsGeneratingSet ξ S) {w : ℝ × ℝ} {c' : ℝ}
    (hmax : ∀ z ∈ S, inner2 (-w) z ≤ c') (hface : (face S (-w) c').Nonempty)
    (hcard : (face S (-w) c').card ≤ 1) : -w ∉ ONED ξ := by
  intro hw
  have h2 := two_le_face_card_of_mem_ONED hgen hmax hface hw
  omega

/-- The same statement in the repo's single-normal convention: if the **lower** face of a
generating window `S` for the normal `w` is a single lattice point — the extreme failure
of Colle's face-cardinality hypothesis — then `-w ∉ ONED ξ`.

This is the obstruction in its usable form.  Route R2 feeds a known `w ∈ ONED ξ` into
Colle Prop. 2.10 in order to obtain `-w ∈ ONED ξ`; whenever the generating set supplied
by Lemma 2.4 has a vertex as its `w`-lower face, that target is *false*, so no amount of
reworking Prop. 2.10's proof can dispense with the hypothesis.  The gap is real. -/
theorem neg_notMem_ONED_of_lower_face_card_le_one {A : Type*} {ξ : Config A}
    {S : Finset (ℤ × ℤ)} (hgen : IsGeneratingSet ξ S) {w : ℝ × ℝ} {cmin : ℝ}
    (hmin : ∀ z ∈ S, cmin ≤ inner2 w z) (hface : (face S w cmin).Nonempty)
    (hcard : (face S w cmin).card ≤ 1) : -w ∉ ONED ξ := by
  have hface' : (face S (-w) (-cmin)).Nonempty := by
    rw [face_neg_level]; exact hface
  have hcard' : (face S (-w) (-cmin)).card ≤ 1 := by
    rw [face_neg_level]; exact hcard
  exact neg_notMem_ONED_of_face_card_le_one hgen
    (upperBound_neg_iff.mpr hmin) hface' hcard'

/-- Consequently, if *both* orientations of a line are one-sided nonexpansive then both
supporting faces of any generating set are edges.  Colle's hypothesis then compares two
numbers that are both at least `2`; it is a genuine extra constraint on the pair, not a
consequence of `ONED` membership. -/
theorem two_le_both_faces_of_biONED {A : Type*} {ξ : Config A}
    {S : Finset (ℤ × ℤ)} (hgen : IsGeneratingSet ξ S) {w : ℝ × ℝ} {cmax cmin : ℝ}
    (hmax : ∀ z ∈ S, inner2 w z ≤ cmax) (hmaxne : (face S w cmax).Nonempty)
    (hmin : ∀ z ∈ S, cmin ≤ inner2 w z) (hminne : (face S w cmin).Nonempty)
    (hw : w ∈ ONED ξ) (hw' : -w ∈ ONED ξ) :
    2 ≤ (face S w cmax).card ∧ 2 ≤ (face S w cmin).card := by
  refine ⟨two_le_face_card_of_mem_ONED hgen hmax hmaxne hw, ?_⟩
  by_contra h
  push Not at h
  exact neg_notMem_ONED_of_lower_face_card_le_one hgen hmin hminne (by omega) hw'

/-! ### The balance condition (Cyr–Kra Definition 4.5(i)) -/
/-- `Balanced S w c` is condition (i) of the Cyr–Kra notion of an `ℓ`-balanced set:
every line parallel to the exposed face — i.e. every non-empty level set of `inner2 w`
on `S` — carries at least `|face| - 1` lattice points of `S`.

This is what the proof of Cyr–Kra Lemma 2.24 (= the substance of Colle Prop. 2.10)
actually consumes: it is used exactly once, to place the auxiliary set `R` of the bottom
`|w₁ ∩ S| - 1` points of each column inside `S`, which is what makes the Morse–Hedlund
count on a window of that width legitimate. -/
def Balanced (S : Finset (ℤ × ℤ)) (w : ℝ × ℝ) (c : ℝ) : Prop :=
  ∀ t : ℝ, (face S w t).Nonempty → (face S w c).card - 1 ≤ (face S w t).card

/-- The balance condition is vacuous when the exposed face is a vertex.  Together with
`two_le_face_card_of_mem_ONED` this localises the whole gap to exposed *edges*. -/
theorem balanced_of_card_le_one {S : Finset (ℤ × ℤ)} {w : ℝ × ℝ} {c : ℝ}
    (h : (face S w c).card ≤ 1) : Balanced S w c := by
  intro t _
  omega

/-! ### Attack route (c): central symmetry

A centrally symmetric window has opposite faces of equal cardinality, hence satisfies
Colle's hypothesis `|S ∩ ℓ_S| ≤ |S ∩ −ℓ_S|` at *both* orientations of every line.  This
lemma is the provable half of route (c).  The unprovable half — that a centrally
symmetric window can also be made to carry the Lemma 2.4 deficit bound — is discussed in
`audit-2026-09-13/r2-orientation-gap.md`; it fails because the generating set of
Lemma 2.4 is produced by a minimal descent that leaves no discrepancy budget for
enlarging the window. -/
def CentrallySymmetric (S : Finset (ℤ × ℤ)) : Prop :=
  ∃ m : ℤ × ℤ, ∀ z : ℤ × ℤ, z ∈ S ↔ m - z ∈ S

/-- In a centrally symmetric window the two supporting faces of any line have the same
number of lattice points. -/
theorem face_card_eq_of_centrallySymmetric {S : Finset (ℤ × ℤ)}
    (hsym : CentrallySymmetric S) {w : ℝ × ℝ} {cmax cmin : ℝ}
    (hmax : ∀ z ∈ S, inner2 w z ≤ cmax) (hmin : ∀ z ∈ S, cmin ≤ inner2 w z)
    (hmaxne : (face S w cmax).Nonempty) (hminne : (face S w cmin).Nonempty) :
    (face S w cmax).card = (face S w cmin).card := by
  classical
  obtain ⟨m, hm⟩ := hsym
  obtain ⟨z₀, hz₀⟩ := hminne
  obtain ⟨z₁, hz₁⟩ := hmaxne
  obtain ⟨hz₀S, hz₀c⟩ := mem_face.mp hz₀
  obtain ⟨hz₁S, hz₁c⟩ := mem_face.mp hz₁
  -- the centre pairs the two extreme levels
  have hsum : inner2 w m = cmax + cmin := by
    have h₀ : inner2 w (m - z₀) ≤ cmax := hmax _ ((hm z₀).mp hz₀S)
    have h₁ : cmin ≤ inner2 w (m - z₁) := hmin _ ((hm z₁).mp hz₁S)
    rw [inner2_sub, hz₀c] at h₀
    rw [inner2_sub, hz₁c] at h₁
    linarith
  refine Finset.card_bij' (fun z _ => m - z) (fun z _ => m - z) ?_ ?_ ?_ ?_
  · intro z hz
    obtain ⟨hzS, hzc⟩ := mem_face.mp hz
    refine mem_face.mpr ⟨(hm z).mp hzS, ?_⟩
    rw [inner2_sub, hsum, hzc]
    ring
  · intro z hz
    obtain ⟨hzS, hzc⟩ := mem_face.mp hz
    refine mem_face.mpr ⟨(hm z).mp hzS, ?_⟩
    rw [inner2_sub, hsum, hzc]
    ring
  · intro z _
    abel
  · intro z _
    abel

/-! ### The open sub-problem

`BalancedGeneratingGoal ξ` is the statement R2 needs and that this file does **not**
prove: for the orientation that is known to lie in `ONED ξ`, a generating set that is
balanced for that orientation and carries the deficit bound there.  It is Cyr–Kra's
Lemma 4.7 conclusion.  Their proof of Lemma 4.7 cuts a low-discrepancy rectangle in half
along a line parallel to `ℓ`, so that the resulting window's `(-ℓ)`-face is a full chord
and is automatically at least as long as its `ℓ`-face; the halving costs `|R_{n,k}|/2`
points of discrepancy, which is affordable only under `P_η(R_{n,k}) ≤ nk/2`.

Nothing in this file uses this definition; it is recorded so that the next agent has a
formal target rather than prose. -/
def BalancedGeneratingGoal {A : Type*} (ξ : Config A) : Prop :=
  ∀ w : ℝ × ℝ, w ∈ ONED ξ → ∃ (S : Finset (ℤ × ℤ)) (c : ℝ),
    IsGeneratingSet ξ S ∧ (∀ z ∈ S, inner2 w z ≤ c) ∧ (face S w c).Nonempty ∧
      Balanced S w c ∧
      P ξ S - P ξ (S.filter fun z => inner2 w z < c) ≤ (face S w c).card - 1

end Nivat.R2
