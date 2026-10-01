/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Data
import Nivat.External.Colle.L1Complexity

/-!
# `L1Fields`: the `L1Data` fields that are *not* independent obligations

`L1Data` (`L1Data.lean:64`) lists fifteen obligations, one per conjunct of
`case1_claim46_and_selection`'s conclusion.  Two of them are not independent of the others,
and this file proves that inside the kernel rather than asserting it in prose:

* **`hQS` (conjunct 3, `Q ⊆ S₁`) is free from `hQ_edge` (conjunct 4).**  Conjunct 4 already
  *defines* `Q` as a filter of `S₁`; `subset_of_hQ_edge` extracts the inclusion.
* **`hBQ` (conjunct 8, the `pw`-long run) reduces to two endpoints,** once `B` is taken to be
  a single point.  `inner2 n u' = 0` (part of conjunct 4) makes the `n`-level constant along
  `u'`, so membership in `Q` along the walk is *free* given membership in `S₁`, and membership
  in `S₁` is lattice-convex betweenness between the two endpoints.

The smart constructor `L1Data.ofEdgeRun` packages both: it builds an `L1Data` from the cut
data `(n, cmax)` and one run start `z₀`, with `Q` and `B` *derived* rather than supplied.

## Scope — read before citing anything here

* This is **not** a proof of leaf L1, and not a step of Collé's argument.  Every genuinely
  geometric obligation of `L1Data` (`hPQ`, `hRper`, `hR_region`, `hRR'`, `hnonper`, `hline`,
  `hstraddle`, `hbase`) is passed straight through `ofEdgeRun` untouched.
* What the constructor *does* change is the shape of conjunct 8's obligation: instead of a
  run condition quantified over an unspecified `B`, the caller owes `z₀ ∈ S₁`,
  `z₀ + ((pw : ℤ) - 1) • u' ∈ S₁`, and `inner2 n z₀ < cmax`.  Whether a real `𝒮₁` supplies
  those two endpoints is **open** and is exactly the geometric question recorded in
  `LEAF-L1.md` ("943 的焦点问题"): is the row immediately below the cut at least as wide as
  the cut itself?  `Nivat.L3Run943.no_nonempty_B_run_943` (`tmp/L3run943.lean`, not landed)
  shows lattice convexity alone does **not** answer it.

  ⚠ **Status changed 2026-09-18 (`PROTOCOL.md` §14).**  The question above is answered, but
  by *changing it*, not by settling it as posed.  The row below the top cut can indeed be too
  short — that is what `no_nonempty_B_run_943` shows — but conjunct 4 does not require the cut
  to be taken at the top: `-n` at level `-cmin` is the same conjunct.
  `exists_side_with_run_of_latticeConvex` proves that at **one of the two ends** the run
  exists, from lattice convexity alone.  ⚠ It does not choose the end for conjuncts 14, 15
  and 16; see its own scope note.
* `singleton_subset_cut` discharges, for a singleton `B`, the obligation `∀ g ∈ B, g ∈ Q`
  that `SweptSeed.lean:296`'s `halfStripFrom_subset_R` consumes (the surviving content of
  `OPEN.md` #5 after that entry's 2026-09-18 revocation).  It is *only* the singleton case.
* ⚠ **Retracted 2026-09-19, kept in place per `PROTOCOL.md` §14 (was: "Taking `B` to be a
  singleton is not free either: `hbase_singleton_iff` states the price in the kernel — conjunct
  16 loses all choice and becomes a demand on the one point `z₀`").**  `L1Data.hbase` weakened
  the same day to `B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R` — the `b` in the second half is no
  longer required to lie in `B`, so the two halves decouple.  For `B := {z₀}` the first half is
  `Finset.singleton_nonempty`, free, and the second half never mentions `z₀`.  **A singleton
  baseline now costs nothing extra on conjunct 16**; `hbase_singleton_iff` below records the
  (now trivial) equivalence instead of the retracted "price".

The underlying run argument is `Nivat.L3Run943.run943_of_run` (`tmp/L3run943.lean`, receipt,
not landed).  It is restated here at the right interface level: that receipt concludes `∃ B`,
whereas `L1Data.B` is a field shared by conjuncts 8 and 16, so an `∃ B` statement cannot
discharge conjunct 8 on its own.
-/

namespace Nivat.ColleReg

open Nivat Nivat.Colle35

namespace L1Data

variable {S₁ Q : Finset (ℤ × ℤ)} {n : ℝ × ℝ} {cmax cmin : ℝ} {u' z₀ : ℤ × ℤ} {pw : ℕ}

/-! ## Conjunct 3 is implied by conjunct 4 -/

/-- **`hQS` is not an independent obligation.**  Conjunct 4 (`L1Data.hQ_edge`) ends with
`Q = S₁.filter _`, which already gives conjunct 3 (`L1Data.hQS`). -/
theorem subset_of_hQ_edge
    (h : ∃ (n : ℝ × ℝ) (cmax : ℝ),
      n ≠ 0 ∧
      inner2 n u' = 0 ∧
      (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧
      Q = S₁.filter fun z => inner2 n z < cmax) :
    Q ⊆ S₁ := by
  obtain ⟨_, _, _, _, _, _, hQ⟩ := h
  rw [hQ]
  exact Finset.filter_subset _ _

/-! ## Conjunct 8 for a singleton `B`

The key is that `inner2 n u' = 0` (conjunct 4) makes the `n`-level constant along `u'`, so the
filter condition is inherited from the start point and only the `S₁`-membership is real work.
-/

/-- **Every intermediate point of a `u'`-run lies below the cut and inside `S₁`.**  The two
endpoints `z₀` and `z₀ + ((pw : ℤ) - 1) • u'` pin the walk inside `S₁` by lattice-convex
betweenness (`Nivat.Claim47.latticeConvex_between`, `Claim47Core.lean:248`); the cut condition
is inherited from `hlo` because `u'` does not move the `n`-level. -/
theorem mem_cut_of_endpoints (hS₁ : Nivat.LatticeConvex S₁) (hnu' : inner2 n u' = 0)
    (hlo : inner2 n z₀ < cmax) (h0 : z₀ ∈ S₁) (hL : z₀ + ((pw : ℤ) - 1) • u' ∈ S₁)
    {i : ℕ} (hi : i < pw) :
    z₀ + (i : ℤ) • u' ∈ S₁.filter fun z => inner2 n z < cmax := by
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · have ha : z₀ + (0 : ℤ) • u' ∈ S₁ := by simpa using h0
    have hm1 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
    have hm2 : (i : ℤ) ≤ (pw : ℤ) - 1 := by omega
    exact Nivat.Claim47.latticeConvex_between hS₁ ha hL hm1 hm2
  · rw [inner2_add, inner2_zsmul, hnu', mul_zero, add_zero]
    exact hlo

/-- **Conjunct 8 (`L1Data.hBQ`) for `B := {z₀}`**, stated at the interface level `L1Data`
needs: the `B` here is a concrete `Finset`, so this can be handed to the structure directly.
(The receipt `Nivat.L3Run943.run943_of_run` concludes `∃ B` instead, which cannot be: `B` is
shared with conjunct 16.) -/
theorem run_singleton (hS₁ : Nivat.LatticeConvex S₁) (hnu' : inner2 n u' = 0)
    (hlo : inner2 n z₀ < cmax) (h0 : z₀ ∈ S₁) (hL : z₀ + ((pw : ℤ) - 1) • u' ∈ S₁) :
    ∀ g ∈ ({z₀} : Finset (ℤ × ℤ)), ∀ i : ℕ, i < pw →
      g + (i : ℤ) • u' ∈ S₁.filter fun z => inner2 n z < cmax := by
  intro g hg i hi
  rw [Finset.mem_singleton] at hg
  subst hg
  exact mem_cut_of_endpoints hS₁ hnu' hlo h0 hL hi

/-- **`∀ g ∈ B, g ∈ Q` for `B := {z₀}`.**  This is the hypothesis
`Nivat.Colle43.halfStripFrom_subset_R` (`SweptSeed.lean:296`) consumes in place of the
retired `0 < pw`, restricted to a singleton baseline. -/
theorem singleton_subset_cut (hlo : inner2 n z₀ < cmax) (h0 : z₀ ∈ S₁) :
    ∀ g ∈ ({z₀} : Finset (ℤ × ℤ)), g ∈ S₁.filter fun z => inner2 n z < cmax := by
  intro g hg
  rw [Finset.mem_singleton] at hg
  subst hg
  exact Finset.mem_filter.mpr ⟨h0, hlo⟩

/-- **The (former) price of a singleton `B`, now dissolved.**  `L1Data.hbase` (conjunct 16)
weakened 2026-09-19 to `B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R`: no on-chain consumer ever
destructured the "same `b`" coupling between the nonemptiness half and the existential half, so
the two were split.  For `B := {z₀}` the first half is `Finset.singleton_nonempty z₀`, always
true, and the second half no longer mentions `z₀` at all.  **This retracts the previous reading
here** (kept per `PROTOCOL.md` §14, see the module docstring): a singleton baseline is exactly
as free on conjunct 16 as any other `B`, because the weak form never asks the witness `b` to be
the point `z₀` singled out by `B`. -/
theorem hbase_singleton_iff {R : Set (ℤ × ℤ)} :
    (({z₀} : Finset (ℤ × ℤ)).Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R) ↔
      ∃ b, ∀ z ∈ S₁, b + z ∈ R :=
  and_iff_right (Finset.singleton_nonempty z₀)

/-! ## `LatticeConvex S₁` is free

`IsGeneratingSet` (`Generating.lean:58-60`) is a three-fold conjunction whose middle component
is exactly lattice convexity, so the constructor below does not have to ask for it.
-/

/-- Conjunct 1 already carries `LatticeConvex S₁`. -/
theorem latticeConvex_of_isGeneratingSet {ξ : Config ℤ}
    (h : Nivat.Colle.IsGeneratingSet ξ S₁) : Nivat.LatticeConvex S₁ :=
  h.2.1

/-! ## The smart constructor -/

/-- **Build an `L1Data` from the cut data and one run start.**

`Q` and `B` are *derived* (`Q := S₁.filter (inner2 n · < cmax)`, `B := {z₀}`), and with them
conjuncts 3, 4 and 8 disappear as separate obligations: conjunct 4 holds by `rfl`, conjunct 3
by `subset_of_hQ_edge`, conjunct 8 by `run_singleton`.  `LatticeConvex S₁` is taken from
`hS₁gen` rather than asked for.

Everything else is passed through verbatim.  `hbase` is built from the run start `z₀`
(`hbase_singleton_iff`), but since `L1Data.hbase`'s 2026-09-19 weakening decouples its two
halves, this is no longer "all conjunct 16 slack spent on `z₀`" — see the retraction in the
module docstring above.

`noncomputable` because `Q` is a `Finset.filter` over a real inequality (`Real.decidableLT`);
this is a data-only artefact of the cut and has no proof content. -/
noncomputable def ofEdgeRun {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}
    (e u u' : ℤ × ℤ) (τ : ℤ) (pw : ℕ) (R R' : Set (ℤ × ℤ)) (c : ℤ) (S₁ : Finset (ℤ × ℤ))
    (n : ℝ × ℝ) (cmax : ℝ) (z₀ : ℤ × ℤ)
    (hS₁gen : Nivat.Colle.IsGeneratingSet ξ S₁)
    (hn0 : n ≠ 0)
    (hnu' : inner2 n u' = 0)
    (hle : ∀ z ∈ S₁, inner2 n z ≤ cmax)
    (hface : (Nivat.R2.face S₁ n cmax).Nonempty)
    (hlo : inner2 n z₀ < cmax)
    (h0 : z₀ ∈ S₁)
    (hL : z₀ + ((pw : ℤ) - 1) • u' ∈ S₁)
    (hdet : det u u' ≠ 0)
    (hu'_prim : Primitive u')
    (hPQ : P ξ S₁ ≤ P ξ (S₁.filter fun z => inner2 n z < cmax) + pw)
    (hc : c ≠ 0)
    (hRper : Colle41.PeriodOn (T e ξ) R (c • u))
    (hR_region : Colle41.IsRegion R u u')
    (hRR' : R ⊂ R')
    (hnonper : ¬ Colle41.PeriodOn (T e ξ) R' (c • u))
    (hline : ∀ t : ℤ, τ ≤ t → ∀ z ∈ S₁.filter (fun z => inner2 n z < cmax),
      t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R)
    (hstraddle : ∀ g ∈ S₁, g ∉ S₁.filter (fun z => inner2 n z < cmax) → ∀ t₀ : ℤ, τ ≤ t₀ →
      Colle41.PeriodOn (T e ξ) R (c • u) →
      (∀ t : ℤ, t₀ ≤ t → (T e ξ) (t • u' + g + c • u) = (T e ξ) (t • u' + g)) →
      Colle41.PeriodOn (T e ξ) R' (c • u))
    (hbase : ∀ z ∈ S₁, z₀ + z ∈ R) :
    L1Data ξ S where
  e := e
  u := u
  u' := u'
  Q := S₁.filter fun z => inner2 n z < cmax
  τ := τ
  pw := pw
  B := {z₀}
  R := R
  R' := R'
  c := c
  S₁ := S₁
  hS₁gen := hS₁gen
  hQS := Finset.filter_subset _ _
  hQ_edge := ⟨n, cmax, hn0, hnu', hle, hface, rfl⟩
  hdet := hdet
  hu'_prim := hu'_prim
  hPQ := hPQ
  hBQ := run_singleton (latticeConvex_of_isGeneratingSet hS₁gen) hnu' hlo h0 hL
  hc := hc
  hRper := hRper
  hR_region := hR_region
  hRR' := hRR'
  hnonper := hnonper
  hline := hline
  hstraddle := hstraddle
  hbase := hbase_singleton_iff.mpr ⟨z₀, hbase⟩

/-! ## `0 < pw` costs exactly `B ⊆ Q`

`pw` occurs in exactly two fields of `L1Data`, with **opposite monotonicity**:

* `hPQ : P ξ S₁ ≤ P ξ Q + pw` gets *weaker* as `pw` grows;
* `hBQ : ∀ g ∈ B, ∀ i < pw, g + i • u' ∈ Q` gets *stronger* as `pw` grows.

So raising `pw` from `0` to `1` is free on `hPQ` and costs `hBQ` exactly one new instance,
namely `i = 0`, which is `B ⊆ Q`.  That is the whole content of `withPosPw` below, and it
routes around the geometry: `0 < pw` needs **no** face-cardinality bound and therefore **no**
`n ∈ ONED ξ`.

`subset_Q_of_pw_pos` is the converse (it is `Nivat.Colle43.subset_Q_of_hline`,
`SweptSeed.lean:320`, re-stated on the bundled structure), and `pw_pos_iff_subset_Q` puts the
two together: over `L1Data`, having a positive `pw` and having `B ⊆ Q` are the same
information.

⚠ This does **not** produce the paper's `p' = |𝒮 ∩ ℓ'_𝒮| − 1`.  It says that if L1 ever hands
over an `L1Data` at all, positivity of `pw` is not an extra obstacle.  The route through the
face cardinality remains available and is wired up in `pw_pos_of_two_le_face_card` below, for
the case where a caller *wants* the paper's witness.

⚠ **2026-09-18, status changed — `withPosPw` and the face route are mutually exclusive.**
`Nivat.L1Complexity.hPQ_of_hQ_edge` (`L1Complexity.lean`) closes conjunct 7 outright, but it
does so by *pinning* `pw := (Nivat.R2.face S₁ n cmax).card - 1`.  `withPosPw` needs `pw` to be
free (it replaces it by `max pw 1`), so a caller that takes conjunct 7 from
`hPQ_of_hQ_edge` **cannot** also use `withPosPw`.  Nothing above is retracted — `withPosPw` is
still correct and still the cheapest route whenever conjunct 7 is discharged some other way —
but the *default* route is now the pinned one, and for it `0 < pw` is
`pw_pos_of_two_le_face_card`, not `withPosPw`.
-/

variable {ξ : Config ℤ} {S : Finset (ℤ × ℤ)}

/-- **`0 < pw` follows from `B ⊆ Q`.**  Replaces `pw` by `max pw 1`, leaving every other
field — in particular `B`, `Q`, `S₁`, `u'` and `R` — definitionally unchanged.

`hPQ` survives because it is monotone in `pw`; `hBQ` survives because the only new instance
is `i = 0`, supplied by `hB`. -/
def withPosPw (L : L1Data ξ S) (hB : ∀ g ∈ L.B, g ∈ L.Q) : L1Data ξ S :=
  { L with
    pw := max L.pw 1
    hPQ := le_trans L.hPQ (Nat.add_le_add_left (le_max_left _ _) _)
    hBQ := by
      intro g hg i hi
      rcases Nat.lt_or_ge i L.pw with h | h
      · exact L.hBQ g hg i h
      · have hi0 : i = 0 := by omega
        subst hi0
        simpa using hB g hg }

@[simp] theorem withPosPw_pw (L : L1Data ξ S) (hB : ∀ g ∈ L.B, g ∈ L.Q) :
    (L.withPosPw hB).pw = max L.pw 1 := rfl

@[simp] theorem withPosPw_B (L : L1Data ξ S) (hB : ∀ g ∈ L.B, g ∈ L.Q) :
    (L.withPosPw hB).B = L.B := rfl

@[simp] theorem withPosPw_Q (L : L1Data ξ S) (hB : ∀ g ∈ L.B, g ∈ L.Q) :
    (L.withPosPw hB).Q = L.Q := rfl

@[simp] theorem withPosPw_S₁ (L : L1Data ξ S) (hB : ∀ g ∈ L.B, g ∈ L.Q) :
    (L.withPosPw hB).S₁ = L.S₁ := rfl

@[simp] theorem withPosPw_u' (L : L1Data ξ S) (hB : ∀ g ∈ L.B, g ∈ L.Q) :
    (L.withPosPw hB).u' = L.u' := rfl

@[simp] theorem withPosPw_R (L : L1Data ξ S) (hB : ∀ g ∈ L.B, g ∈ L.Q) :
    (L.withPosPw hB).R = L.R := rfl

/-- The point of `withPosPw`. -/
theorem withPosPw_pw_pos (L : L1Data ξ S) (hB : ∀ g ∈ L.B, g ∈ L.Q) :
    0 < (L.withPosPw hB).pw := by
  rw [withPosPw_pw]
  omega

/-- The converse: a positive `pw` gives `B ⊆ Q` back, by reading `hBQ` at `i = 0`.  This is
`Nivat.Colle43.subset_Q_of_hline` (`SweptSeed.lean:320`) on the bundled structure. -/
theorem subset_Q_of_pw_pos (L : L1Data ξ S) (h : 0 < L.pw) : ∀ g ∈ L.B, g ∈ L.Q := by
  intro g hg
  simpa using L.hBQ g hg 0 h

/-- **`0 < pw` and `B ⊆ Q` carry the same information over `L1Data`.**

Left to right is `subset_Q_of_pw_pos` transported along the field equalities; right to left is
`withPosPw`, which keeps `B`, `Q`, `S₁`, `u'` and `R` fixed.

⚠ The left-hand side is an existential over a *possibly different* `L1Data`: `pw` genuinely
changes.  It does not say `0 < L.pw` for the given `L`, which is false in general. -/
theorem pw_pos_iff_subset_Q (L : L1Data ξ S) :
    (∃ L' : L1Data ξ S, 0 < L'.pw ∧ L'.B = L.B ∧ L'.Q = L.Q) ↔ (∀ g ∈ L.B, g ∈ L.Q) := by
  constructor
  · rintro ⟨L', hpos, hB, hQ⟩
    intro g hg
    have := subset_Q_of_pw_pos L' hpos g (by rw [hB]; exact hg)
    rwa [hQ] at this
  · intro hB
    exact ⟨L.withPosPw hB, withPosPw_pw_pos L hB, rfl, rfl⟩

/-! ## The face route — **now the default route** (status changed 2026-09-18)

If a caller does want Collé's own witness `p' = |𝒮 ∩ ℓ'_𝒮| − 1` (`b3_colle2.txt:645`), the
two facts it needs are below.  `sdiff_eq_face` identifies `S₁ ∖ Q` with the exposed face, so
that `(Nivat.R2.face S₁ n cmax).card` is the right quantity; `pw_pos_of_two_le_face_card` is
the one-line consequence of a face-cardinality bound.

**The missing input is `2 ≤ (Nivat.R2.face S₁ n cmax).card`.**  It is supplied by
`Nivat.R2.two_le_face_card_of_mem_ONED` (`R2Orientation.lean:171`) from `n ∈ Nivat.ONED ξ`
(together with `hS₁gen`, `hle` and `hface`, all of which `L1Data` already carries), and that
membership is **not** available at this point of Collé's argument: `ℓ' ∈ nexpd(η)` is the
*conclusion* of Claim 4.9 (`b3_colle2.txt:870`), proved from the region `K` that Lemma 4.1
produces at `:860`.  See `LEAF-L1.md`, "⚠ `n ∈ ONED ξ` 不可用".  `withPosPw` above exists
precisely so that this circularity does not have to be resolved.

⚠ **Status change (nothing above retracted, cf. `PROTOCOL.md` §14).**  Two things moved:

1. **This is no longer the fallback route, it is the default one.**
   `Nivat.L1Complexity.hPQ_of_hQ_edge` (`L1Complexity.lean`) discharges conjunct 7 at
   `pw := (Nivat.R2.face S₁ n cmax).card - 1`, and `Nivat.L1Complexity.not_hPQ_of_no_deficit`
   shows conjunct 7 is *not* derivable from `hQ_edge` + `LatticeConvex` + `Primitive u'`
   alone.  So `pw` is pinned to the face cardinality and there is no longer a choice.
2. **The input it needs is `hdef`, not `n ∈ Nivat.ONED ξ`.**  `hdef`
   (`RegionSteps.lean:874-879`) is a section hypothesis of `case1_claim46_and_selection`, so
   the leaf carries it already.  The circularity diagnosed above is real but is now
   *irrelevant to this route* — nobody has to go through `ONED` to get conjunct 7.  Paragraph
   two above stays on record because it is still the correct verdict about `ONED`, which is
   what `pw_pos_of_two_le_face_card` would need if `2 ≤ card` were wanted on its own.
3. **Conjunct 7 is not an independent obligation at all** (added 2026-09-18).  `conj7_of_conj4`
   below derives it from conjunct 4 together with `hdef` and the translate hypothesis, both of
   which the leaf has for free.  Under that pinning, `L1Data`'s `0 < pw` reduces to
   `2 ≤ (Nivat.R2.face S₁ n cmax).card` and nothing else — that is exactly
   `pw_pos_of_two_le_face_card` below, so the `0 < pw` debt recorded in `LEAF-L1.md` is now a
   statement about `S₁` alone rather than about `ONED`.  ⚠ It is **not** discharged: nothing in
   this file proves the maximising face has two points.  `withPosPw` remains the only route
   that gets `0 < pw` without it, and it is unavailable here (see the warning above).
-/

/-- **`S₁ ∖ Q` is the exposed face.**  Given that `cmax` bounds `inner2 n` on `S₁`, failing
the strict inequality means attaining it. -/
theorem sdiff_eq_face (hle : ∀ z ∈ S₁, inner2 n z ≤ cmax) :
    S₁ \ (S₁.filter fun z => inner2 n z < cmax) = Nivat.R2.face S₁ n cmax := by
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_filter, Nivat.R2.mem_face, not_and, not_lt]
  constructor
  · rintro ⟨hz, hnot⟩
    exact ⟨hz, le_antisymm (hle z hz) (hnot hz)⟩
  · rintro ⟨hz, heq⟩
    exact ⟨hz, fun _ => le_of_eq heq.symm⟩

/-- **Collé's witness is positive exactly when the face is an edge.**  With
`pw := (Nivat.R2.face S₁ n cmax).card - 1`, positivity is the face-cardinality bound and
nothing else. -/
theorem pw_pos_of_two_le_face_card (h : 2 ≤ (Nivat.R2.face S₁ n cmax).card) :
    0 < (Nivat.R2.face S₁ n cmax).card - 1 := by omega

/-! ## Conjunct 8 at the pinned `pw`: cut at whichever end is cheaper

With `pw` pinned to `(Nivat.R2.face S₁ n cmax).card - 1`, conjunct 8 at `B = {z₀}` asks for a
`u'`-run of length `|face| - 1` lying **strictly below** the cut.  The obstruction recorded at
the top of this file — `Nivat.L3Run943.no_nonempty_B_run_943` (`tmp/L3run943.lean`), the
lattice triangle whose row below the cut is a single point — is real, and lattice convexity
alone does not remove it.

**But the cut does not have to be taken at the top.**  Conjunct 4 constrains `n` only by
`n ≠ 0` and `inner2 n u' = 0`, and `-n` satisfies both exactly when `n` does.  Cutting with
`-n` at level `-cmin` is *literally the same conjunct*, with `face S₁ (-n) (-cmin) =
face S₁ n cmin` (`Nivat.R2.face_neg_level`, `R2Orientation.lean:102`) and
`S₁.filter (inner2 (-n) · < -cmin) = S₁.filter (cmin < inner2 n ·)`
(`Nivat.R2.filter_lt_neg`, `R2Orientation.lean:124`).  `hdef` (`RegionSteps.lean:874-879`)
supplies the complexity deficit for **both** ends — that is exactly what its second conjunct,
the `cmin` half, is for.

Once both ends are available the run obligation is discharged by counting, with no geometry at
all: the run needed for the top cut has length `|face cmax| - 1`, and the **bottom face itself**
is a row strictly below the top; symmetrically for the other end.  Since
`a - 1 ≤ b ∨ b - 1 ≤ a` holds for all naturals (`card_pigeonhole`), at least one of the two
cuts finds its run inside the opposite face.

On the triangle of `no_nonempty_B_run_943`: the top face has 3 points and the bottom face 1,
so the top cut fails, but the bottom cut has `pw = 1 - 1 = 0` and conjunct 8 is vacuous.  The
refutation there is therefore a refutation of *cutting at the top*, not of conjunct 8.

⚠ **What is still owed** — *nothing, as of 2026-09-18 (status changed, cf. `PROTOCOL.md` §14).*
The paragraph above was written while `FaceIsRun` was a hypothesis.  It is now the theorem
`faceIsRun` below, and the hypothesis-free form of the dichotomy is
`exists_side_with_run_of_latticeConvex`.
-/

/-- **A face is a contiguous `u'`-run of its own cardinality**, anchored at some `z₀`.

This is the one geometric input the dichotomy below needs.

⚠ **Status changed 2026-09-18 (cf. `PROTOCOL.md` §14): it is no longer a hypothesis.**  The
paragraphs that follow were written when it was one, and they are kept because their verdict on
the two *existing* proofs is still correct — neither is usable, and `faceIsRun` below does not
use either.  What they got wrong is the conclusion drawn from that: the bridge they describe as
missing **was already in the tree** as `Nivat.Colle.det_eq_zero_of_inner2_eq_zero`
(`HalfPlanePeriodicity.lean:18`), and with it `faceIsRun` proves this predicate outright from
lattice convexity.

* `Nivat.L1Width.exists_ell_face_run` (`tmp/L1_width_certified.lean:119`, **not landed**)
  proves exactly this shape, but indexes levels by `det vl z : ℤ` rather than by
  `inner2 n z : ℝ`.  Bridging the two needs the fact that on `{z : inner2 n z}` and
  `{z : det u' z}` are proportional as real functionals (both vanish on `u' ≠ 0`, and the
  space of such functionals on `ℝ²` is one-dimensional).
* `mem_face_run` (`Prop210.lean:1612`) is the contiguity half, also in `det` levels, and is
  `private`.

It is still stated as a named predicate rather than inlined, so that
`run_below_of_faceIsRun` and `exists_side_with_run` stay readable and so that a caller who has
the run for some other reason can use them without `LatticeConvex`. -/
def FaceIsRun (S₁ : Finset (ℤ × ℤ)) (n : ℝ × ℝ) (c : ℝ) (u' : ℤ × ℤ) : Prop :=
  ∃ z₀, z₀ ∈ Nivat.R2.face S₁ n c ∧
    ∀ i : ℕ, i < (Nivat.R2.face S₁ n c).card → z₀ + (i : ℤ) • u' ∈ Nivat.R2.face S₁ n c

/-- **`FaceIsRun` is inhabited, and the triangle's cheap end is an instance.**  A face with at
most one point is a run for any `u'` whatsoever: the only index is `i = 0`.

This is what makes the dichotomy fire on `Nivat.L3Run943.no_nonempty_B_run_943`'s triangle —
its bottom face is the single point `(0,0)`, so `FaceIsRun` holds there for free and the
`cmin` branch of `exists_side_with_run` applies with `pw = 0`.  It also certifies that
`FaceIsRun` is not a vacuous hypothesis. -/
theorem faceIsRun_of_card_le_one (hne : (Nivat.R2.face S₁ n cmax).Nonempty)
    (h : (Nivat.R2.face S₁ n cmax).card ≤ 1) : FaceIsRun S₁ n cmax u' := by
  obtain ⟨z₀, hz₀⟩ := hne
  refine ⟨z₀, hz₀, ?_⟩
  intro i hi
  have : i = 0 := by omega
  subst this
  simpa using hz₀

/-- **The counting step.**  Of any two naturals, one is at least the other minus one.  Named
because it is the entire content of the two-sided dichotomy: the face at one end is always
long enough to carry the run demanded by the cut at the other end. -/
theorem card_pigeonhole (a b : ℕ) : a - 1 ≤ b ∨ b - 1 ≤ a := by omega

/-- **Conjunct 8 from the opposite face.**  If the `cmin`-face is a `u'`-run at least
`(face S₁ n cmax).card - 1` long, it supplies the whole run demanded by the `cmax`-cut, and it
does so strictly below the cut because its level is `cmin < cmax`.

No lattice convexity is used: `FaceIsRun` already carries the contiguity, and membership in
`Q` is immediate from the level. -/
theorem run_below_of_faceIsRun (hlt : cmin < cmax)
    (hrun : FaceIsRun S₁ n cmin u')
    (hcard : (Nivat.R2.face S₁ n cmax).card - 1 ≤ (Nivat.R2.face S₁ n cmin).card) :
    ∃ z₀, z₀ ∈ S₁ ∧ inner2 n z₀ < cmax ∧
      ∀ i : ℕ, i < (Nivat.R2.face S₁ n cmax).card - 1 →
        z₀ + (i : ℤ) • u' ∈ S₁.filter fun z => inner2 n z < cmax := by
  obtain ⟨z₀, hz₀, hrun'⟩ := hrun
  rw [Nivat.R2.mem_face] at hz₀
  refine ⟨z₀, hz₀.1, by rw [hz₀.2]; exact hlt, ?_⟩
  intro i hi
  have hmem := hrun' i (lt_of_lt_of_le hi hcard)
  rw [Nivat.R2.mem_face] at hmem
  exact Finset.mem_filter.mpr ⟨hmem.1, by rw [hmem.2]; exact hlt⟩

/-- **The two-sided dichotomy: conjunct 8 is satisfiable at one of the two cuts.**

Both disjuncts are instances of the *same* conjunct-4 shape, the second one with the normal
`-n` and the level `-cmin` (legitimate because conjunct 4 asks only `n ≠ 0` and
`inner2 n u' = 0`, both stable under negation).  `hdef` (`RegionSteps.lean:874-879`) carries
the matching complexity deficit for both, which is what its `cmin` half is for.

⚠ Scope: this says conjunct 8 *can be met at one end*.  It does not choose the end for the
rest of `L1Data` — **conjuncts 14, 15 and 16** have to be met at the **same** end, and this
theorem says nothing about whether they can be.  In particular the `-n` branch flips which
points of `S₁` land in `Q`, so conjuncts 14 and 15 are different statements there.  Conjunct 7
is *not* at risk: `hdef` carries both halves.

⚠ Conjuncts are referred to by **number** here, not by field name: `L1Data`'s field names and
the destructuring names at `RegionSteps.lean:1155-1157` disagree, and one pair is crossed —
the field `hline` is conjunct 14 while the call site's `hline` is conjunct 8 (`hBQ`).  Table in
`NOTATION.md`. -/
theorem exists_side_with_run (hlt : cmin < cmax)
    (hmax : FaceIsRun S₁ n cmax u') (hmin : FaceIsRun S₁ n cmin u') :
    (∃ z₀, z₀ ∈ S₁ ∧ inner2 n z₀ < cmax ∧
        ∀ i : ℕ, i < (Nivat.R2.face S₁ n cmax).card - 1 →
          z₀ + (i : ℤ) • u' ∈ S₁.filter fun z => inner2 n z < cmax) ∨
    (∃ z₀, z₀ ∈ S₁ ∧ inner2 (-n) z₀ < -cmin ∧
        ∀ i : ℕ, i < (Nivat.R2.face S₁ (-n) (-cmin)).card - 1 →
          z₀ + (i : ℤ) • u' ∈ S₁.filter fun z => inner2 (-n) z < -cmin) := by
  rcases card_pigeonhole (Nivat.R2.face S₁ n cmax).card (Nivat.R2.face S₁ n cmin).card with
    h | h
  · exact Or.inl (run_below_of_faceIsRun hlt hmin h)
  · refine Or.inr (run_below_of_faceIsRun (cmin := -cmax) (by linarith) ?_ ?_)
    · simpa only [FaceIsRun, Nivat.R2.face_neg_level] using hmax
    · simpa only [Nivat.R2.face_neg_level] using h

/-! ## `FaceIsRun` discharged: the real-normal ↔ `det`-level bridge

The hypothesis `FaceIsRun` carried above is now a theorem.  The missing step was never the
lattice geometry — `Nivat.Claim47.latticeConvex_between` (`Claim47Core.lean:248`) already
supplies contiguity — but the translation between the **real** level function `inner2 n ·` and
the **integer** one `det u' ·`, which is what kept `Nivat.L1Width.exists_ell_face_run`
(`tmp/L1_width_certified.lean:119`) and `mem_face_run` (`Prop210.lean:1612`) out of reach.

That bridge is `Nivat.Colle.det_eq_zero_of_inner2_eq_zero` (`HalfPlanePeriodicity.lean:18`):
two lattice vectors annihilated by the same non-zero real normal are `det`-parallel.  It is
already in `L1Data`'s import closure, so nothing new is needed to use it.

⚠ **§20 record (2026-09-18).**  This file briefly carried its own copy of that lemma, under
the same name and with the same proof, before a module-level orphan scan found the original.
The duplicate is deleted.  The reason the scan missed it the first time is worth keeping: the
search had been run for the *conclusion* shape `det _ _ = 0` inside the `L1*` and `R2*` files
and against Collé's face vocabulary, and the original lives in a Proposition 2.12 file about
half-plane period extension, with no face or `L1` vocabulary anywhere near it.

`Prop210.lean:389` additionally carries the full proportionality statement
(`exists_ratio_of_inner2_eq_zero`: `inner2 w · = μ * det v ·` with `μ ≠ 0`), which is strictly
stronger, but it is `private`.  The face argument only needs the vanishing direction, so the
public lemma suffices and no de-privatisation is required.

`n ≠ 0` is load-bearing in it — with `n = 0` every level is `0` and the face is all of `S₁`,
which is exactly the degenerate branch conjunct 4's `n ≠ 0` exists to exclude
(`L1Data.lean:100-101`).
-/

/-- **`FaceIsRun` is a theorem for lattice-convex windows.**

The face `{z ∈ S₁ : ⟨n, z⟩ = cmax}` is a contiguous `u'`-run of its own cardinality, anchored
at its minimal point.  Three steps:

* every face point lies on the `u'`-line through a fixed face point `w`
  (`Nivat.Colle.det_eq_zero_of_inner2_eq_zero`, `HalfPlanePeriodicity.lean:18`, plus
  `Nivat.eq_smul_add_smul`, `Defs/Config.lean:172`);
* the set of indices is an interval, because `Nivat.Claim47.latticeConvex_between`
  (`Claim47Core.lean:248`) fills in between the extreme two and `inner2 n u' = 0` keeps the
  level constant, so the interpolated points are back in the face;
* the index map is injective on the face, so the face's cardinality is the index set's, which
  is bounded by the length of the interval (`Int.card_Icc`).

⚠ `mem_face_run` (`Prop210.lean:1612`) is **not** re-proved here and is not needed.  It is a
`det`-coordinate repackaging of `Nivat.Claim47.latticeConvex_between`, which is public and is
the primitive fact; step two above calls that directly.  So no de-privatisation is required.

This removes the last hypothesis of `exists_side_with_run`; see
`exists_side_with_run_of_latticeConvex`. -/
theorem faceIsRun (hS : Nivat.LatticeConvex S₁) (hu'p : Primitive u') (hn : n ≠ 0)
    (hnu' : inner2 n u' = 0) (hne : (Nivat.R2.face S₁ n cmax).Nonempty) :
    FaceIsRun S₁ n cmax u' := by
  classical
  show ∃ z₀, z₀ ∈ Nivat.R2.face S₁ n cmax ∧
    ∀ i : ℕ, i < (Nivat.R2.face S₁ n cmax).card →
      z₀ + (i : ℤ) • u' ∈ Nivat.R2.face S₁ n cmax
  obtain ⟨t, ht⟩ := hu'p.exists_dual
  set F : Finset (ℤ × ℤ) := Nivat.R2.face S₁ n cmax with hFdef
  obtain ⟨w, hwF⟩ := hne
  have hw : w ∈ S₁ ∧ inner2 n w = cmax := Nivat.R2.mem_face.mp hwF
  set f : ℤ × ℤ → ℤ := fun z => det z t - det w t with hfdef
  have honLine : ∀ z ∈ F, z = w + (f z) • u' := by
    intro z hz
    have hzf : z ∈ S₁ ∧ inner2 n z = cmax := Nivat.R2.mem_face.mp hz
    have h : inner2 n (z - w) + inner2 n w = inner2 n z := by
      rw [← inner2_add]; congr 1; abel
    have h0 : inner2 n (z - w) = 0 := by rw [hzf.2, hw.2] at h; linarith
    have hdet0 : det u' (z - w) = 0 :=
      Nivat.Colle.det_eq_zero_of_inner2_eq_zero hn hnu' h0
    have heq := eq_smul_add_smul ht (z - w)
    rw [hdet0, zero_smul, add_zero] at heq
    have hfe : det (z - w) t = f z := by
      simp only [hfdef, det, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hfe] at heq
    rw [← heq]; abel
  have hmem : ∀ m : ℤ, w + m • u' ∈ S₁ → w + m • u' ∈ F := by
    intro m hmS
    rw [hFdef, Nivat.R2.mem_face]
    refine ⟨hmS, ?_⟩
    rw [inner2_add, inner2_zsmul, hnu', mul_zero, add_zero, hw.2]
  set M : Finset ℤ := F.image f with hMdef
  have hwM : (0 : ℤ) ∈ M := by
    refine Finset.mem_image.mpr ⟨w, hwF, ?_⟩
    simp [hfdef]
  have hMne : M.Nonempty := ⟨0, hwM⟩
  set mlo : ℤ := M.min' hMne with hmlo
  set mhi : ℤ := M.max' hMne with hmhi
  have hptF : ∀ m ∈ M, w + m • u' ∈ F := by
    intro m hm
    obtain ⟨z, hz, hzm⟩ := Finset.mem_image.mp hm
    rw [← hzm, ← honLine z hz]
    exact hz
  have hloF : w + mlo • u' ∈ F := hptF _ (Finset.min'_mem _ _)
  have hhiF : w + mhi • u' ∈ F := hptF _ (Finset.max'_mem _ _)
  have hinterval : ∀ m : ℤ, mlo ≤ m → m ≤ mhi → w + m • u' ∈ F := by
    intro m h1 h2
    refine hmem m (Nivat.Claim47.latticeConvex_between hS ?_ ?_ h1 h2)
    · exact Nivat.R2.face_subset _ _ _ hloF
    · exact Nivat.R2.face_subset _ _ _ hhiF
  have hinj : Set.InjOn f ↑F := by
    intro z hz z' hz' heq
    rw [honLine z (Finset.mem_coe.mp hz), honLine z' (Finset.mem_coe.mp hz'), heq]
  have hcard : M.card = F.card := Finset.card_image_of_injOn hinj
  have hsub : M ⊆ Finset.Icc mlo mhi := fun m hm =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hm, Finset.le_max' _ _ hm⟩
  have hcard2 : F.card ≤ (mhi + 1 - mlo).toNat := by
    rw [← hcard]
    calc M.card ≤ (Finset.Icc mlo mhi).card := Finset.card_le_card hsub
      _ = (mhi + 1 - mlo).toNat := Int.card_Icc _ _
  refine ⟨w + mlo • u', hloF, ?_⟩
  intro i hi
  have hi' : (i : ℤ) < mhi + 1 - mlo := by
    have h := lt_of_lt_of_le hi hcard2
    omega
  have hgoal := hinterval (mlo + (i : ℤ)) (by omega) (by omega)
  have hrw : w + (mlo + (i : ℤ)) • u' = w + mlo • u' + (i : ℤ) • u' := by
    rw [add_smul]; abel
  rwa [hrw] at hgoal

/-- **The two-sided dichotomy with no `FaceIsRun` hypothesis left.**

Same conclusion as `exists_side_with_run`, with both `FaceIsRun` premises discharged by
`faceIsRun`.  Every remaining hypothesis is already carried by `L1Data`: `LatticeConvex S₁`
comes from conjunct 1 (`latticeConvex_of_isGeneratingSet`), `Primitive u'` is conjunct 6, and
`n ≠ 0` and `inner2 n u' = 0` are the first two components of conjunct 4.  The two
`Nonempty`s and `cmin < cmax` are supplied by `exists_min_face` below.

⚠ The scope warning on `exists_side_with_run` still applies verbatim: this picks an end for
conjunct 8 only, not for conjuncts 14, 15 and 16. -/
theorem exists_side_with_run_of_latticeConvex (hS : Nivat.LatticeConvex S₁)
    (hu'p : Primitive u') (hn : n ≠ 0) (hnu' : inner2 n u' = 0) (hlt : cmin < cmax)
    (hmaxne : (Nivat.R2.face S₁ n cmax).Nonempty)
    (hminne : (Nivat.R2.face S₁ n cmin).Nonempty) :
    (∃ z₀, z₀ ∈ S₁ ∧ inner2 n z₀ < cmax ∧
        ∀ i : ℕ, i < (Nivat.R2.face S₁ n cmax).card - 1 →
          z₀ + (i : ℤ) • u' ∈ S₁.filter fun z => inner2 n z < cmax) ∨
    (∃ z₀, z₀ ∈ S₁ ∧ inner2 (-n) z₀ < -cmin ∧
        ∀ i : ℕ, i < (Nivat.R2.face S₁ (-n) (-cmin)).card - 1 →
          z₀ + (i : ℤ) • u' ∈ S₁.filter fun z => inner2 (-n) z < -cmin) :=
  exists_side_with_run hlt (faceIsRun hS hu'p hn hnu' hmaxne) (faceIsRun hS hu'p hn hnu' hminne)

/-- **The bottom level exists.**  A non-empty window has a minimising face for any normal, and
that level is strictly below `cmax` as soon as some point of `S₁` is strictly below `cmax` —
i.e. as soon as the cut `Q` is non-empty, which is the only case conjunct 8 has content in.

This is the same `Finset.exists_min_image` step `Nivat.L1Complexity.hPQ_of_translate_deficit`
(`L1Complexity.lean:139`) uses to discharge `hdef`'s minimal-face premises. -/
theorem exists_min_face (hQne : (S₁.filter fun z => inner2 n z < cmax).Nonempty) :
    ∃ cmin : ℝ, (∀ z ∈ S₁, cmin ≤ inner2 n z) ∧
      (Nivat.R2.face S₁ n cmin).Nonempty ∧ cmin < cmax := by
  classical
  obtain ⟨z₁, hz₁⟩ := hQne
  rw [Finset.mem_filter] at hz₁
  obtain ⟨zmin, hzminS, hzmin⟩ := S₁.exists_min_image (fun z => inner2 n z) ⟨z₁, hz₁.1⟩
  refine ⟨inner2 n zmin, hzmin, ⟨zmin, Nivat.R2.mem_face.mpr ⟨hzminS, rfl⟩⟩, ?_⟩
  exact lt_of_le_of_lt (hzmin z₁ hz₁.1) hz₁.2

/-! ## Conjunct 7 from conjunct 4 — and why the `∃ pw` form of it proves nothing

The integrator's receipt (`tmp/vSeamL1.lean`, `tmp/vSeamL1b.lean`) observes that `hQ_edge`
carries three of the five inputs of `Nivat.L1Complexity.hPQ_of_hQ_edge`, and that the other two
(`hdef`, and `S₁` being a translate of `S`) are free at the call site — `hdef` is a binder of
`case1_claim46_and_selection` (`RegionSteps.lean:874-879`) and `S₁` is existentially quantified
in its conclusion (`RegionSteps.lean:882-883`).  That observation is correct and is landed
below as `conj7_of_conj4`.

⚠ **But the `∃ pw` phrasing of it is a tautology and must not be quoted as the receipt.**
`exists_pw_trivial` proves `∃ pw, P ξ S₁ ≤ P ξ Q + pw` for *arbitrary* `ξ`, `S₁`, `Q`, with no
hypotheses at all: take `pw := P ξ S₁`.  `pw` is a **shared** field — conjunct 8 (`hBQ`)
demands a run of length `pw` — so an existential that lets `pw` float carries none of the
content.  `conj7_of_conj4` therefore returns the *same* `n` and `cmax` that `hQ_edge` supplies,
together with the bound at the **pinned** width `(Nivat.R2.face S₁ n cmax).card - 1`, so that
conjunct 8 is obliged at exactly that width.
-/

/-- **The `∃ pw` form of conjunct 7 is vacuous.**  No hypotheses; `pw := P ξ S₁` works.
Landed as a guard rail, not as a result. -/
theorem exists_pw_trivial (ξ : Config ℤ) (S₁ Q : Finset (ℤ × ℤ)) :
    ∃ pw : ℕ, P ξ S₁ ≤ P ξ Q + pw :=
  ⟨P ξ S₁, Nat.le_add_left _ _⟩

/-- **Conjunct 4 plus `hdef` plus the translate gives conjunct 7, at a pinned width.**

The conclusion repeats conjunct 4 verbatim so that the `n` and `cmax` witnessing it are the
*same* ones the width is measured against; this is what `exists_pw_trivial` shows is essential.

All three of `hle`, `hface`, `hQ` are unpacked from `hQ_edge`, so the leaf pays nothing extra
for them: the only genuinely new inputs are `hdef` (a binder of `case1_claim46_and_selection`)
and `hS₁` (free, since `S₁` is existentially quantified in that theorem's conclusion). -/
theorem conj7_of_conj4 {ξ : Config ℤ} {S S₁ Q : Finset (ℤ × ℤ)} {u' v : ℤ × ℤ}
    (hS₁ : S₁ = Finset.image (fun x => x + v) S)
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
      (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face S n cmax).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face S n cmin).card - 1)
    (hQ_edge : ∃ (n : ℝ × ℝ) (cmax : ℝ),
      n ≠ 0 ∧
      inner2 n u' = 0 ∧
      (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧
      Q = S₁.filter fun z => inner2 n z < cmax) :
    ∃ (n : ℝ × ℝ) (cmax : ℝ),
      n ≠ 0 ∧
      inner2 n u' = 0 ∧
      (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧
      (Q = S₁.filter fun z => inner2 n z < cmax) ∧
      P ξ S₁ ≤ P ξ Q + ((Nivat.R2.face S₁ n cmax).card - 1) := by
  obtain ⟨n, cmax, hn0, hnu', hle, hface, hQ⟩ := hQ_edge
  exact ⟨n, cmax, hn0, hnu', hle, hface, hQ,
    Nivat.L1Complexity.hPQ_of_hQ_edge hS₁ hdef hle hface hQ⟩

/-! ## The singleton-face branch: `pw = 0`

Collé splits Claim 4.7 on whether the edge `𝒯 ∩ ℓ'_𝒯` is a single point (`b3_colle2.txt:838-840`).
At the pinned width `pw = |face| - 1` that branch is `pw = 0`.  This section settles what
happens there, in both directions the integrator asked about.

**The structural fact.**  `pw` occurs in exactly **two** of `L1Data`'s fifteen obligations:
`hPQ` (conjunct 7, `L1Data.lean:114`) and `hBQ` (conjunct 8, `L1Data.lean:116`).  The other
thirteen do not mention it.  So "does the `pw = 0` branch go through" is entirely a question
about those two fields plus their consumers, and nothing else in the structure is at risk.

**Upstream (constructibility).**  At `pw = 0` conjunct 8 is vacuous for *every* `B` and `Q` —
`conj8_of_face_card_le_one`, no geometry used — and conjunct 7 is still delivered by
`Nivat.L1Complexity.hPQ_of_hQ_edge`, which has no cardinality side condition.  So the singleton
branch is **strictly easier** than `2 ≤ |face|`, not harder: it discharges conjunct 8 outright
and pays the same price for conjunct 7.  `conj7_and_conj8_of_singleton_face` lands both at once.

⚠ **Conjunct 7 at `pw = 0` is not free from geometry.**
`Nivat.L1Complexity.not_hPQ_of_no_deficit` (`L1Complexity.lean:332`) is already a `pw = 0`
witness — its face is a vertex, so the pinned width there *is* `0` — and it shows conjunct 7
failing while every conjunct of `hQ_edge`, `Primitive u'` and `LatticeConvex S₁` all hold.
What that refutation isolates is the absence of `hdef`, not the singleton face.  With `hdef` in
hand (and it is a binder of `case1_claim46_and_selection`, `RegionSteps.lean:874-879`) conjunct
7 comes out at `pw = 0` exactly as it does at any other width.

**Downstream (sufficiency).**  Measured on the three consumers of `region_case1`'s
destructuring (`tmp/L1fields_pw0.lean`, `check1.sh` EXIT=0, my own `#check` output):

* `Nivat.ColleReg.case1_claim47_semiAmbiguous` — its type mentions **neither** `pw` nor
  conjuncts 7/8 nor `B` at all, so `pw = 0` cannot reach it.
* `Nivat.Colle41.lemma41_of_sweep` and `Nivat.Colle41.lemma41_colle_region_shape` — both bind
  `{p : ℕ}` with **no** positivity hypothesis, and both are axiom-clean
  (`[propext, Classical.choice, Quot.sound]`).  `lemma41_region_shape_of_pw_zero` below is the
  compiled instantiation at `p := 0`: Lemma 4.1's conclusion, with the conjunct-8 hypothesis
  **deleted from the statement** rather than assumed.
* `Nivat.ColleReg.case1_sweep` (leaf L3, still a `sorry`) — binds `{pw : ℕ}` with no positivity
  either, so `pw = 0` typechecks into it.  Whether its *proof* survives cannot be measured
  while it is a `sorry`; what changes there is recorded on
  `lemma41_region_shape_of_pw_zero` and is L3's to weigh, not this file's.

**Verdict on `2 ≤ |face|`.**  It is not an obligation of `L1Data` (there is no positivity field
on `pw`), and at the pinned width the singleton branch discharges conjunct 8 for free while
reaching Lemma 4.1 unchanged.  So it is not a debt of L1.  The `withPosPw` route above
(`:251`) stays landed under PROTOCOL §14 as the record of the earlier reading, but it is not
needed and is incompatible with the pinned width.
-/

/-- **Conjunct 8 at the pinned width is vacuous on a singleton face.**

No geometry, no hypothesis on `Q`, `B` or `u'`: `i < (face).card - 1` is `i < 0` in ℕ.  This is
why the singleton branch costs nothing — conjunct 8 is the only place `pw` is *consumed* as a
lower bound. -/
theorem conj8_of_face_card_le_one (hcard : (Nivat.R2.face S₁ n cmax).card ≤ 1)
    (B Q : Finset (ℤ × ℤ)) (u' : ℤ × ℤ) :
    ∀ g ∈ B, ∀ i : ℕ, i < (Nivat.R2.face S₁ n cmax).card - 1 → g + (i : ℤ) • u' ∈ Q := by
  intro _ _ i hi
  exact absurd hi (by omega)

/-- The pinned width is zero exactly on a singleton (or empty) face.  Stated so the ℕ-truncated
subtraction is converted once, in a named place, rather than by an `omega` at each use. -/
theorem pinned_pw_eq_zero_iff :
    (Nivat.R2.face S₁ n cmax).card - 1 = 0 ↔ (Nivat.R2.face S₁ n cmax).card ≤ 1 :=
  Nat.sub_eq_zero_iff_le

/-- **The singleton branch discharges conjuncts 7 and 8 together, at `pw = 0`.**

The inputs are exactly those of `conj7_of_conj4` with `hQ_edge` already unpacked, plus
`hcard`.  `B` is arbitrary — conjunct 8 does not constrain it here. -/
theorem conj7_and_conj8_of_singleton_face {ξ : Config ℤ} {S S₁ Q : Finset (ℤ × ℤ)}
    {n : ℝ × ℝ} {cmax : ℝ} {u' v : ℤ × ℤ}
    (hS₁ : S₁ = Finset.image (fun x => x + v) S)
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
      (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face S n cmax).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face S n cmin).card - 1)
    (hle : ∀ z ∈ S₁, inner2 n z ≤ cmax)
    (hface : (Nivat.R2.face S₁ n cmax).Nonempty)
    (hQ : Q = S₁.filter fun z => inner2 n z < cmax)
    (hcard : (Nivat.R2.face S₁ n cmax).card ≤ 1)
    (B : Finset (ℤ × ℤ)) :
    P ξ S₁ ≤ P ξ Q ∧ (∀ g ∈ B, ∀ i : ℕ, i < 0 → g + (i : ℤ) • u' ∈ Q) := by
  refine ⟨?_, fun _ _ i hi => absurd hi (by omega)⟩
  have h := Nivat.L1Complexity.hPQ_of_hQ_edge hS₁ hdef hle hface hQ
  omega

/-- **Lemma 4.1 survives `pw = 0`: the conjunct-8 hypothesis is not merely vacuous, it is
absent from the statement.**

This is `Nivat.Colle41.lemma41_colle_region_shape` at `p := 0`.  Two things change against the
general form, and both are recorded here because they are what leaf L3 has to weigh:

* the `B`-line hypothesis (conjunct 8) is **gone** — nothing relates `B` to `Q` any more;
* the sweep hypothesis's antecedent is `τ ≤ t` instead of `τ + (pw : ℤ) ≤ t`, i.e. it must be
  supplied for **more** `t`, which makes `hsweep` a *stronger* assumption to discharge.

So `pw = 0` is not free downstream: it trades conjunct 8 away for a wider sweep range.  It
does not, however, break anything — the conclusion is the conclusion of Lemma 4.1 verbatim. -/
theorem lemma41_region_shape_of_pw_zero {A : Type*} {η x : Config A}
    (hfinη : (Set.range η).Finite) (hx : x ∈ orbitClosure η)
    {S Q : Finset (ℤ × ℤ)} (hQS : Q ⊆ S) {u u' : ℤ × ℤ} {τ : ℤ}
    (hdet : det u u' ≠ 0)
    (hdef : P η S ≤ P η Q)
    {B : Finset (ℤ × ℤ)}
    (hamb : Colle41.SemiAmbiguousAlong η x S Q u' τ)
    {R : Set (ℤ × ℤ)} {c : ℤ} (hc : c ≠ 0) (hRper : Colle41.PeriodOn x R (c • u))
    (hsweep : ∀ q : ℕ, 0 < q →
        (∀ g ∈ B, ∀ t : ℤ, τ ≤ t → x (g + (t + (q : ℤ)) • u') = x (g + t • u')) →
        ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ Colle41.IsRegion K u u' ∧ K.Nonempty ∧
          ∃ t₀ : ℕ, 0 < t₀ ∧ Colle41.PeriodOn x K (((t₀ * q : ℕ) : ℤ) • u')) :
    ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsLatticeConvexRegion K ∧ K.Nonempty ∧
      ∃ h h' z₀ z₀' : ℤ × ℤ, det h h' ≠ 0 ∧
        (∀ k : ℕ, z₀ + (k : ℤ) • h ∈ K) ∧ (∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ K) ∧
        (∀ z ∈ K, z + h ∈ K → x (z + h) = x z) ∧
        (∀ z ∈ K, z + h' ∈ K → x (z + h') = x z) := by
  refine Colle41.lemma41_colle_region_shape (p := 0) (B := B) hfinη hx hQS hdet ?_ ?_ hamb hc
    hRper ?_
  · simpa using hdef
  · intro _ _ i hi
    exact absurd hi (by omega)
  · intro q hq hq'
    refine hsweep q hq ?_
    intro g hg t ht
    exact hq' g hg t (by simpa using ht)

end L1Data

end Nivat.ColleReg
