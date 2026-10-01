/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Data
import Nivat.External.Colle.RegionCutGE
import Nivat.External.Colle.Interfaces
import Nivat.External.Colle.OrderThree

/-!
# `L1Region`: conjuncts 10–14 and 16 of leaf L1 from the maximality of `N`

`L1Data` (`L1Data.lean:71`) carries four fields that all refer to one choice in Collé's
argument — the **greatest** index `N` with `(T^u η)|𝓡^N_I` of period `h = c·u`
(`b3_colle2.txt:816-818`):

* `hRper`    (conjunct 10, `L1Data.lean:120`) — `PeriodOn (T e ξ) R (c • u)`;
* `hR_region` (conjunct 11, `L1Data.lean:122`) — `IsRegion R u u'`;
* `hRR'`     (conjunct 12, `L1Data.lean:124`) — `R ⊂ R'`;
* `hnonper`  (conjunct 13, `L1Data.lean:126`) — `¬ PeriodOn (T e ξ) R' (c • u)`.

This file turns all four into the output of a single input: an increasing family of regions
whose union is **not** `c·u`-periodic while its first member is.  That is exactly Collé's
own setup (`b3_colle2.txt:816`, `⋃_{n=0}^∞ 𝓡^n_I = 𝓡_{I-1}`), and it is the smart-constructor
move of `CLAUDE.md` hard rule 4.

Conjuncts 14 and 16 mention the *same* `R`, so closing 10–13 in isolation would leave a
coupling: a producer still has to make one family serve all of them.  §5 closes that for 14
and 16, which are stable under enlarging `R`, and shows by counterexample that **conjunct 15
is not** — it stays tied to whichever index the maximality argument selects.

§8 removes `union_not` from the list of things a producer must supply at this level: it is a
field of Collé's *outer* chain `𝓡_{ι-1} ⊂ ⋯ ⊂ 𝓡_{ι-m+1}`, and the selection step turns out
to be a self-map on `RegionFamily`.  What a producer still owes is the chain itself.

## The one real lemma

`periodOn_iUnion_of_monotone` (§1).  `Colle41.PeriodOn` (`Lemma41.lean:659`) is an
*overlap-only* condition — `∀ z ∈ U, z + h ∈ U → x (z + h) = x z` — and that is precisely
what makes it pass to a **directed** union: `z` and `z + h` each land in some member, and a
monotone family puts them both in the later one.  (For a non-directed union this fails: two
members can each miss the overlap that their union creates.)

Everything else is bookkeeping on top of it: the complement of the periodic indices is
upward-closed and nonempty, so `Nat.find` on it lands at `N + 1`.

## What this does *not* supply

The input `¬ PeriodOn x (⋃ n, R n) (c • u)` (`RegionFamily.union_not`) is **not proved here.**
§7 reduces it to Proposition 2.12 (`Interfaces.lean:45`) plus two inputs this file does not
produce: a finite periodic decomposition of `T e ξ`, and a half-plane inside the union.  No
lemma of the form `IsMinimalCounterexample ξ → _` is proved anywhere in this file — per
`PROTOCOL.md`'s two readings of `IsMinimalCounterexample`, such a lemma would be worth
nothing.

## Non-vacuity

`RegionFamily` is inhabited: `witness` (§4) is an explicit family of half-planes in `ℤ²`
together with a configuration for which the maximal index is `4`.  Without it the constructor
below would be a statement about an empty structure (`PROTOCOL.md` §9).  The same witness is
reused in §5.2 to refute the transport of conjunct 15.
-/

set_option autoImplicit false

namespace Nivat.L1Region

open Nivat Nivat.Colle41 Nivat.LE2

/-! ## §1  `PeriodOn` passes to directed unions

This is the only place where the overlap-only shape of Definition 2.11 is used, and it is
used essentially.
-/

/-- **A monotone family's union inherits `PeriodOn` from its members.**

`PeriodOn x U h` only constrains `z` with *both* `z` and `z + h` in `U`.  In a union those
two points may come from different members; monotonicity puts them in the larger of the two,
where the hypothesis applies. -/
theorem periodOn_iUnion_of_monotone {A : Type*} {x : Config A} {Rf : ℕ → Set (ℤ × ℤ)}
    {h : ℤ × ℤ} (hmono : Monotone Rf) (hper : ∀ n, PeriodOn x (Rf n) h) :
    PeriodOn x (⋃ n, Rf n) h := by
  intro z hz hzh
  obtain ⟨a, hz⟩ := Set.mem_iUnion.mp hz
  obtain ⟨b, hzh⟩ := Set.mem_iUnion.mp hzh
  exact hper (max a b) z (hmono (le_max_left a b) hz) (hmono (le_max_right a b) hzh)

/-- The contrapositive: a non-periodic union has a non-periodic member. -/
theorem exists_not_periodOn_of_not_iUnion {A : Type*} {x : Config A} {Rf : ℕ → Set (ℤ × ℤ)}
    {h : ℤ × ℤ} (hmono : Monotone Rf) (hnot : ¬ PeriodOn x (⋃ n, Rf n) h) :
    ∃ n, ¬ PeriodOn x (Rf n) h := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  exact hnot (periodOn_iUnion_of_monotone hmono hc)

/-- **The maximal index `N` exists** (`b3_colle2.txt:818`, "the greatest integer `N ∈ ℤ₊`
such that `(T^u η)|𝓡^N_I` is periodic of period `h`").

Periodicity is inherited downwards along the family (`PeriodOn.mono`), so the set of indices
where it *fails* is upward-closed; it is nonempty by `exists_not_periodOn_of_not_iUnion` and
misses `0` by `h0`, hence its least element is a successor `N + 1`. -/
theorem exists_greatest_periodOn {A : Type*} {x : Config A} {Rf : ℕ → Set (ℤ × ℤ)}
    {h : ℤ × ℤ} (hmono : Monotone Rf) (h0 : PeriodOn x (Rf 0) h)
    (hnot : ¬ PeriodOn x (⋃ n, Rf n) h) :
    ∃ N : ℕ, PeriodOn x (Rf N) h ∧ ¬ PeriodOn x (Rf (N + 1)) h := by
  classical
  have hex : ∃ n, ¬ PeriodOn x (Rf n) h := exists_not_periodOn_of_not_iUnion hmono hnot
  have hspec : ¬ PeriodOn x (Rf (Nat.find hex)) h := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hp
    · exact absurd h0 (by rw [← hz]; exact hspec)
    · exact hp
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · exact not_not.mp (Nat.find_min hex (m := Nat.find hex - 1) (by omega))
  · have he : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [he]
    exact hspec

/-! ## §2  The smart constructor

One structure, four outputs.  Building a `RegionFamily` is strictly weaker than producing the
four conjuncts by hand: the index `N` no longer has to be named.
-/

/-- **Collé's nested family `𝓡^0_I ⊂ 𝓡^1_I ⊂ ⋯`** (`b3_colle2.txt:816`), as the single input
from which `L1Data`'s conjuncts 10–13 follow.

Fields `grow` and `isRegion` are the geometry of the slicing (supplied by `ofCut` below for
half-plane cuts); `base` and `union_not` are the two periodicity facts that pin `N` between
them.  `union_not` is the one carrying genuine content — see the module docstring. -/
structure RegionFamily (x : Config ℤ) (u u' : ℤ × ℤ) (c : ℤ) where
  /-- `R n = 𝓡^n_I`. -/
  R : ℕ → Set (ℤ × ℤ)
  /-- The family is strictly increasing; this is what makes conjunct 12 (`R ⊂ R'`) strict. -/
  grow : ∀ n, R n ⊂ R (n + 1)
  /-- Every member is an `(u, u')`-region — conjunct 11 for whichever index is selected. -/
  isRegion : ∀ n, Colle41.IsRegion (R n) u u'
  /-- `𝓡^0_I` is `c·u`-periodic. -/
  base : Colle41.PeriodOn x (R 0) (c • u)
  /-- The union `𝓡_{I-1}` is not.  **Not proved anywhere in this file** — see the module
  docstring: this is Proposition 2.12 against minimality of the counterexample. -/
  union_not : ¬ Colle41.PeriodOn x (⋃ n, R n) (c • u)

namespace RegionFamily

variable {x : Config ℤ} {u u' : ℤ × ℤ} {c : ℤ}

theorem monotone (F : RegionFamily x u u' c) : Monotone F.R :=
  monotone_nat_of_le_succ fun n => (F.grow n).subset

/-- **Conjuncts 10–13 of `L1Data`, in one step.**

The statement is a verbatim copy of `L1Data.hRper`, `hR_region`, `hRR'`, `hnonper`
(`L1Data.lean:120-126`) with `R`, `R'` existentially quantified, which is how
`case1_claim46_and_selection` supplies them (`RegionSteps.lean:882-883`: the producer picks
the witnesses). -/
theorem exists_index (F : RegionFamily x u u' c) :
    ∃ R R' : Set (ℤ × ℤ),
      Colle41.PeriodOn x R (c • u) ∧
      Colle41.IsRegion R u u' ∧
      R ⊂ R' ∧
      ¬ Colle41.PeriodOn x R' (c • u) := by
  obtain ⟨N, hN, hN'⟩ := exists_greatest_periodOn F.monotone F.base F.union_not
  exact ⟨F.R N, F.R (N + 1), hN, F.isRegion N, F.grow N, hN'⟩

end RegionFamily

/-- `exists_index` at the exact configuration `L1Data` uses, `ξ' = T e ξ`
(`L1Data.lean:120`, `b3_colle2.txt:778`). -/
theorem exists_conjuncts_10_13 {ξ : Config ℤ} {e u u' : ℤ × ℤ} {c : ℤ}
    (F : RegionFamily (T e ξ) u u' c) :
    ∃ R R' : Set (ℤ × ℤ),
      Colle41.PeriodOn (T e ξ) R (c • u) ∧
      Colle41.IsRegion R u u' ∧
      R ⊂ R' ∧
      ¬ Colle41.PeriodOn (T e ξ) R' (c • u) :=
  F.exists_index

/-! ## §3  Building the family by half-plane cuts

Collé's `𝓡^n_I` is `𝓡_{I-1}` sliced by `dist(·, ℓ'_{𝓡_I}) ≤ d_n` (`b3_colle2.txt:816`), i.e.
an intersection with a half-plane whose boundary is parallel to `ℓ' `— so parallel to `u'`,
**not** to `u`.  `LE2.isRegion_inter_halfPlaneGE` (`RegionCutGE.lean:58`) cuts parallel to its
first ray direction, so it is applied here with the two directions swapped; `isRegion_symm`
records that `Colle41.IsRegion` is symmetric in them.
-/

/-- `Colle41.IsRegion` (`Lemma41.lean:688`) is a conjunction of "carries a `u`-ray" and
"carries a `u'`-ray", so it is symmetric in the two directions.  (`LE2.IsRegion`,
`LatticeEdges.lean:2221`, is **not** — it has a `detPos` field.  The two must not be
confused.) -/
theorem isRegion_symm {K : Set (ℤ × ℤ)} {u u' : ℤ × ℤ} (h : Colle41.IsRegion K u u') :
    Colle41.IsRegion K u' u :=
  ⟨h.1, h.2.2, h.2.1⟩

/-- The sliced family: `R∞` cut at a level `lev n` measured by the normal `m`. -/
def cut (Rinf : Set (ℤ × ℤ)) (m : ℤ × ℤ) (lev : ℕ → ℤ) (n : ℕ) : Set (ℤ × ℤ) :=
  Rinf ∩ halfPlaneGE m (lev n)

/-- Each slice is again an `(u, u')`-region, provided the cutting line runs along `u'` and
the `u`-ray points into the half-plane. -/
theorem isRegion_cut {Rinf : Set (ℤ × ℤ)} {u u' m : ℤ × ℤ} (hR : Colle41.IsRegion Rinf u u')
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u) (lev : ℕ → ℤ) (n : ℕ) :
    Colle41.IsRegion (cut Rinf m lev n) u u' :=
  isRegion_symm (isRegion_inter_halfPlaneGE (isRegion_symm hR) m (lev n) hmu' hmu)

/-- Lowering the cut level enlarges the slice. -/
theorem cut_mono {Rinf : Set (ℤ × ℤ)} {m : ℤ × ℤ} {lev : ℕ → ℤ} (hlev : Antitone lev) :
    Monotone (cut Rinf m lev) := by
  intro a b hab z hz
  exact ⟨hz.1, le_trans (hlev hab) hz.2⟩

/-- **`⋃_n 𝓡^n_I = 𝓡_{I-1}`** (`b3_colle2.txt:816`): the levels exhaust `ℤ` downwards, so
every point of `Rinf` is eventually caught. -/
theorem iUnion_cut {Rinf : Set (ℤ × ℤ)} {m : ℤ × ℤ} {lev : ℕ → ℤ}
    (hlev : ∀ b : ℤ, ∃ n, lev n ≤ b) :
    (⋃ n, cut Rinf m lev n) = Rinf := by
  ext z
  constructor
  · rintro hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    exact hn.1
  · intro hz
    obtain ⟨n, hn⟩ := hlev (dot m z)
    exact Set.mem_iUnion.mpr ⟨n, hz, hn⟩

/-- Strictness of `𝓡^n_I ⊂ 𝓡^{n+1}_I`.  In the paper this is built into the choice of the
`d_n`: they enumerate the distances that are actually **attained**
(`b3_colle2.txt:816`), so each step genuinely adds a point. -/
theorem cut_ssubset {Rinf : Set (ℤ × ℤ)} {m : ℤ × ℤ} {lev : ℕ → ℤ} (hlev : Antitone lev)
    (hgap : ∀ n, ∃ z ∈ Rinf, lev (n + 1) ≤ dot m z ∧ dot m z < lev n) (n : ℕ) :
    cut Rinf m lev n ⊂ cut Rinf m lev (n + 1) := by
  obtain ⟨z, hzR, hz1, hz2⟩ := hgap n
  refine ⟨cut_mono hlev (Nat.le_succ n), ?_⟩
  intro hsub
  exact absurd (hsub ⟨hzR, hz1⟩).2 (not_le.mpr hz2)

/-- **A `RegionFamily` from a half-plane slicing.**  This is the shape of Collé's own
construction; the two periodicity inputs are still the caller's. -/
def ofCut {x : Config ℤ} {Rinf : Set (ℤ × ℤ)} {u u' m : ℤ × ℤ} {c : ℤ} {lev : ℕ → ℤ}
    (hR : Colle41.IsRegion Rinf u u')
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u)
    (hlev : Antitone lev)
    (hexh : ∀ b : ℤ, ∃ n, lev n ≤ b)
    (hgap : ∀ n, ∃ z ∈ Rinf, lev (n + 1) ≤ dot m z ∧ dot m z < lev n)
    (hbase : Colle41.PeriodOn x (cut Rinf m lev 0) (c • u))
    (hinf : ¬ Colle41.PeriodOn x Rinf (c • u)) :
    RegionFamily x u u' c where
  R := cut Rinf m lev
  grow := cut_ssubset hlev hgap
  isRegion := isRegion_cut hR hmu' hmu lev
  base := hbase
  union_not := by rw [iUnion_cut hexh]; exact hinf

/-! ## §4  Non-vacuity

An explicit `RegionFamily`, so that §2 is not a theorem about an empty structure.

`Rinf` is all of `ℤ²`, the slices are the half-planes `{z | -n ≤ z.1}`, and the configuration
is the indicator of the single point `(-5, 0)`.  The horizontal shift `(1, 0)` is a period of
every slice that misses `(-5, 0)` — vacuously, the configuration is constant `0` there — and
fails on every slice that contains it.  So the maximal index is `4`.
-/

/-- The ambient region for the witness. -/
theorem isRegion_univ (u u' : ℤ × ℤ) : Colle41.IsRegion (Set.univ : Set (ℤ × ℤ)) u u' :=
  ⟨isLatticeConvexRegion_univ, ⟨0, fun _ => Set.mem_univ _⟩, ⟨0, fun _ => Set.mem_univ _⟩⟩

/-- Indicator of `(-5, 0)`. -/
def wx : Config ℤ := fun z => if z = ((-5 : ℤ), (0 : ℤ)) then 1 else 0

/-- Cut levels `0, -1, -2, …`. -/
def wlev : ℕ → ℤ := fun n => -(n : ℤ)

theorem wlev_antitone : Antitone wlev := by
  intro a b hab
  simp only [wlev, neg_le_neg_iff, Nat.cast_le]
  exact hab

theorem wlev_exhaustive (b : ℤ) : ∃ n, wlev n ≤ b := by
  refine ⟨(-b).toNat, ?_⟩
  simp only [wlev]
  omega

theorem w_mem_cut_iff (n : ℕ) (z : ℤ × ℤ) :
    z ∈ cut Set.univ ((1 : ℤ), (0 : ℤ)) wlev n ↔ -(n : ℤ) ≤ z.1 := by
  simp only [cut, Set.mem_inter_iff, Set.mem_univ, true_and, halfPlaneGE, dot, wlev,
    Set.mem_ofPred_eq]
  omega

theorem wgap (n : ℕ) :
    ∃ z ∈ (Set.univ : Set (ℤ × ℤ)),
      wlev (n + 1) ≤ dot ((1 : ℤ), (0 : ℤ)) z ∧ dot ((1 : ℤ), (0 : ℤ)) z < wlev n := by
  refine ⟨(-(n : ℤ) - 1, 0), Set.mem_univ _, ?_, ?_⟩ <;>
    · simp only [dot, wlev]
      push_cast
      omega

theorem wbase : Colle41.PeriodOn wx (cut Set.univ ((1 : ℤ), (0 : ℤ)) wlev 0) ((1 : ℤ) • (1, 0)) := by
  intro z hz _
  rw [w_mem_cut_iff] at hz
  have h1 : z ≠ ((-5 : ℤ), (0 : ℤ)) := by
    intro h
    rw [h] at hz
    norm_num at hz
  have h2 : z + (1 : ℤ) • ((1 : ℤ), (0 : ℤ)) ≠ ((-5 : ℤ), (0 : ℤ)) := by
    intro h
    have := congrArg Prod.fst h
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this
    omega
  simp only [wx, one_smul] at h1 h2 ⊢
  rw [if_neg h1, if_neg h2]

theorem wnot : ¬ Colle41.PeriodOn wx (Set.univ : Set (ℤ × ℤ)) ((1 : ℤ) • (1, 0)) := by
  intro h
  have := h ((-5 : ℤ), (0 : ℤ)) (Set.mem_univ _) (Set.mem_univ _)
  simp only [wx, one_smul] at this
  norm_num at this

/-- **`RegionFamily` is inhabited.** -/
def witness : RegionFamily wx ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) 1 :=
  ofCut (Rinf := Set.univ) (m := ((1 : ℤ), (0 : ℤ))) (lev := wlev)
    (isRegion_univ _ _)
    (by simp [dot])
    (by simp [dot])
    wlev_antitone
    wlev_exhaustive
    wgap
    wbase
    wnot

/-- The witness really does select an index, so `exists_index` is not vacuous. -/
theorem witness_exists_index :
    ∃ R R' : Set (ℤ × ℤ),
      Colle41.PeriodOn wx R ((1 : ℤ) • ((1 : ℤ), (0 : ℤ))) ∧
      Colle41.IsRegion R ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) ∧
      R ⊂ R' ∧
      ¬ Colle41.PeriodOn wx R' ((1 : ℤ) • ((1 : ℤ), (0 : ℤ))) :=
  witness.exists_index

/-! ## §5  Which of the remaining conjuncts ride along with the selected index

`exists_index` picks `R := F.R N` for an `N` it does not name, so a conjunct that also
mentions `R` can only be delivered alongside it if it is **stable under enlarging `R`** — then
assuming it at level `0` gives it at every level, `N` included.

* **Conjunct 14** (`L1Data.lean:128`) and **conjunct 16** (`L1Data.lean:136`) are of that
  shape: both assert membership *in* `R`, positively.  They ride along (§5.1).
* **Conjunct 15** (`L1Data.lean:131`) is **not**, and this is proved rather than argued:
  `straddle_zero` and `not_straddle_four` below are two compiled statements about the same
  family showing it holds at levels `0 → 1` and fails at levels `4 → 5` (§5.2).

The level-`0` hypotheses are the *strongest* member of their family, not the weakest: by
monotonicity "at level `0`" and "at every level" are equivalent, and both are strictly
stronger than "at level `N`".  Since `N` is not known before the maximality argument runs,
level `0` is the only level a producer can name in advance.  Weakening to "at *some* level"
is **not** available — the maximality argument pins `R` to level `N` exactly.
-/

namespace RegionFamily

variable {x : Config ℤ} {u u' : ℤ × ℤ} {c : ℤ}

/-- A positively-stated membership condition assumed at level `0` holds at every level. -/
theorem line_of_line_zero (F : RegionFamily x u u' c) {τ : ℤ} {Q : Finset (ℤ × ℤ)}
    (h0 : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ F.R 0 ∧ t • u' + z + c • u ∈ F.R 0)
    (n : ℕ) :
    ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ F.R n ∧ t • u' + z + c • u ∈ F.R n := by
  intro t ht z hz
  exact ⟨F.monotone (Nat.zero_le n) (h0 t ht z hz).1,
    F.monotone (Nat.zero_le n) (h0 t ht z hz).2⟩

theorem base_of_base_zero (F : RegionFamily x u u' c) {B S₁ : Finset (ℤ × ℤ)}
    (h0 : ∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ F.R 0) (n : ℕ) :
    ∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ F.R n := by
  obtain ⟨b, hb, h⟩ := h0
  exact ⟨b, hb, fun z hz => F.monotone (Nat.zero_le n) (h z hz)⟩

end RegionFamily

/-- **Conjuncts 10, 11, 12, 13, 14 and 16 of `L1Data`, from one `RegionFamily`.**

Six of the seven `R`-coupled conjuncts come out together, on the *same* `R` and `R'`.  The
two extra hypotheses are conjuncts 14 and 16 stated on `F.R 0`; the maximality argument then
transports them to the selected level.  Conjunct 15 is deliberately absent — see §5.2.

Compare `exists_conjuncts_10_13`, which is this with the last two conjuncts and their
hypotheses dropped. -/
theorem exists_conjuncts_10_14_16 {ξ : Config ℤ} {e u u' : ℤ × ℤ} {c τ : ℤ}
    {Q B S₁ : Finset (ℤ × ℤ)} (F : RegionFamily (T e ξ) u u' c)
    (hline0 : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ F.R 0 ∧ t • u' + z + c • u ∈ F.R 0)
    (hbase0 : ∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ F.R 0) :
    ∃ R R' : Set (ℤ × ℤ),
      Colle41.PeriodOn (T e ξ) R (c • u) ∧
      Colle41.IsRegion R u u' ∧
      R ⊂ R' ∧
      ¬ Colle41.PeriodOn (T e ξ) R' (c • u) ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) ∧
      (∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R) := by
  obtain ⟨N, hN, hN'⟩ := exists_greatest_periodOn F.monotone F.base F.union_not
  exact ⟨F.R N, F.R (N + 1), hN, F.isRegion N, F.grow N, hN',
    F.line_of_line_zero hline0 N, F.base_of_base_zero hbase0 N⟩

/-! ### §5.2  Conjunct 15 does not ride along

Conjunct 15 has `R` in a *hypothesis* and `R'` in its *conclusion*, so enlarging the pair
moves the two ends in opposite directions and no transport is available.  Rather than assert
that, the two theorems below exhibit it on the witness family of §4.
-/

/-- The shape of conjunct 15 (`L1Data.lean:131`) at one pair of levels. -/
def Straddle (x : Config ℤ) (Rlo Rhi : Set (ℤ × ℤ)) (S₁ Q : Finset (ℤ × ℤ))
    (u u' : ℤ × ℤ) (c τ : ℤ) : Prop :=
  ∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ →
    Colle41.PeriodOn x Rlo (c • u) →
    (∀ t : ℤ, t₀ ≤ t → x (t • u' + g + c • u) = x (t • u' + g)) →
    Colle41.PeriodOn x Rhi (c • u)

/-- On the witness family, `wx` is `(1,0)`-periodic on every slice up to level `4`: the only
point where `wx` is nonzero is `(-5, 0)`, which no such slice contains. -/
theorem w_periodOn_of_le {n : ℕ} (hn : n ≤ 4) :
    Colle41.PeriodOn wx (cut Set.univ ((1 : ℤ), (0 : ℤ)) wlev n) ((1 : ℤ) • (1, 0)) := by
  intro z hz _
  rw [w_mem_cut_iff] at hz
  have hn' : (n : ℤ) ≤ 4 := by exact_mod_cast hn
  have h1 : z ≠ ((-5 : ℤ), (0 : ℤ)) := by
    intro h; rw [h] at hz; norm_num at hz; omega
  have h2 : z + (1 : ℤ) • ((1 : ℤ), (0 : ℤ)) ≠ ((-5 : ℤ), (0 : ℤ)) := by
    intro h
    have := congrArg Prod.fst h
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this
    omega
  simp only [wx, one_smul] at h1 h2 ⊢
  rw [if_neg h1, if_neg h2]

/-- Level `5` is where it fails: the slice contains both `(-5, 0)` and `(-4, 0)`. -/
theorem w_not_periodOn_five :
    ¬ Colle41.PeriodOn wx (cut Set.univ ((1 : ℤ), (0 : ℤ)) wlev 5) ((1 : ℤ) • (1, 0)) := by
  intro h
  have hmem : ((-5 : ℤ), (0 : ℤ)) ∈ cut Set.univ ((1 : ℤ), (0 : ℤ)) wlev 5 := by
    rw [w_mem_cut_iff]; norm_num
  have hmem' : ((-5 : ℤ), (0 : ℤ)) + (1 : ℤ) • ((1 : ℤ), (0 : ℤ))
      ∈ cut Set.univ ((1 : ℤ), (0 : ℤ)) wlev 5 := by
    rw [w_mem_cut_iff]; norm_num
  have := h _ hmem hmem'
  simp only [wx, one_smul] at this
  norm_num at this

/-- Conjunct 15's shape **holds** at levels `0 → 1`: its conclusion is true outright there. -/
theorem straddle_zero :
    Straddle wx (witness.R 0) (witness.R 1) {((0 : ℤ), (0 : ℤ))} ∅
      ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) 1 0 :=
  fun _ _ _ _ _ _ _ => w_periodOn_of_le (by norm_num)

/-- …and **fails** at levels `4 → 5`, with every hypothesis discharged.

So "conjunct 15 at level `0`" does not imply "conjunct 15 at level `N`", and conjunct 15
cannot be added to `exists_conjuncts_10_14_16` by the transport of §5.1.  It remains coupled
to whichever index the maximality argument selects. -/
theorem not_straddle_four :
    ¬ Straddle wx (witness.R 4) (witness.R 5) {((0 : ℤ), (0 : ℤ))} ∅
        ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ)) 1 0 := by
  intro h
  refine w_not_periodOn_five (h ((0 : ℤ), (0 : ℤ)) (Finset.mem_singleton_self _)
    (Finset.notMem_empty _) 0 le_rfl (w_periodOn_of_le (by norm_num)) ?_)
  intro t _
  simp only [wx, one_smul]
  norm_num [Prod.ext_iff]

/-! ## §6  The cutting normal exists whenever conjunct 5 holds

`ofCut` needs an `m` with `dot m u = 0` and `0 < dot m u'`.  Conjunct 5
(`hdet : det u u' ≠ 0`, `L1Data.lean:109`) supplies it, and the sign is fixable in both
directions — so this is **not** an extra obligation on L1.

The computation is exact: with `det u v = u.1 * v.2 - u.2 * v.1` (`Nivat/Defs/Config.lean:43`)
and `dot n z = n.1 * z.1 + n.2 * z.2` (`LatticeEdges.lean:72`), the perpendicular of `u`
pairs with `u'` to give `det u u'` *on the nose*.
-/

theorem dot_perp_self (u : ℤ × ℤ) : dot (-u.2, u.1) u = 0 := by
  simp only [dot]; ring

/-- The perpendicular of `u` tested against `u'` **is** `det u u'`. -/
theorem dot_perp_eq_det (u u' : ℤ × ℤ) : dot (-u.2, u.1) u' = det u u' := by
  simp only [dot, det]; ring

/-- **Conjunct 5 supplies `ofCut`'s cutting normal.**  Both signs of `det u u'` are handled:
`det u u' > 0` takes the perpendicular, `det u u' < 0` takes its negative. -/
theorem exists_cut_normal {u u' : ℤ × ℤ} (h : det u u' ≠ 0) :
    ∃ m : ℤ × ℤ, dot m u = 0 ∧ 0 < dot m u' := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · refine ⟨(u.2, -u.1), by simp only [dot]; ring, ?_⟩
    have : dot (u.2, -u.1) u' = -det u u' := by simp only [dot, det]; ring
    rw [this]
    omega
  · exact ⟨(-u.2, u.1), dot_perp_self u, by rw [dot_perp_eq_det]; exact hgt⟩

/-! ## §7  A producer for `union_not`

`union_not` is the one field of `RegionFamily` this file leaves as a hypothesis.  It does
have a producer in sight, and the reduction is landed below rather than described.

Collé's own argument (`b3_colle2.txt:806`) is: a period on `ℋ(ℓ_{ι-m})` would make `T^u η`
periodic by **Proposition 2.12**, contradicting the counterexample.  The repository's
Proposition 2.12 is `Nivat.Colle.exists_parallel_period_of_overlap_halfPlane`
(`Interfaces.lean:45`, axiom-clean), and its `hlocal` hypothesis is *literally* `PeriodOn` on
a half-plane, unfolded.  So the reduction is mechanical once two things are supplied:

1. **`PeriodicDecompZ (T e ξ) nd`** — the finite periodic decomposition.  ⚠ **Superseded by
   §8.1**: this paragraph said "not free; this file does not produce it", and that was wrong.
   Leaf L1's binder `d : DecompDataZ ξ` supplies it through `periodicDecompZ_T_of_decompDataZ`.
2. **`hcover`** — the union contains a half-plane tangent to `c • u`.  ⚠ **Aimed one level too
   low**; see §8.  At the inner level the union is `𝓡_{I-1}`, a *region*, which need not
   contain a half-plane; at the outer level it is `ℋ(ℓ_{ι-m})`, where Collé actually invokes
   Proposition 2.12 and where the inclusion holds by construction.

Both corrections are in §8; this paragraph is kept rather than rewritten, per PROTOCOL §14,
so the misreading stays on the record.

Neither is manufactured here.  What is landed is that *given* those two, `union_not` follows
from `¬ IsPeriodic ξ` alone — so `union_not` is **not** irreducible L1 content; it is
Proposition 2.12 plus a covering statement about the region chain.
-/

/-- **`union_not` from Proposition 2.12.**  If the union covers a half-plane on which `c • u`
is a tangent direction, a period there lifts to a global period of `T e ξ`
(`Interfaces.lean:45`) and hence of `ξ` (`PeriodTransport.lean:24`). -/
theorem union_not_of_halfPlane_cover {ξ : Config ℤ} {e u : ℤ × ℤ} {c : ℤ} {nd : ℕ}
    {Rf : ℕ → Set (ℤ × ℤ)} {w : ℝ × ℝ} {lvl : ℝ}
    (hdec : Nivat.PeriodicDecompZ (T e ξ) nd)
    (hw : w ≠ 0) (hcu : c • u ≠ 0) (hwu : inner2 w (c • u) = 0)
    (hcover : {z : ℤ × ℤ | lvl ≤ inner2 w z} ⊆ ⋃ k, Rf k)
    (hnp : ¬ Nivat.IsPeriodic ξ) :
    ¬ Colle41.PeriodOn (T e ξ) (⋃ k, Rf k) (c • u) := by
  intro hper
  obtain ⟨v, hv, hv0, -⟩ :=
    Nivat.Colle.exists_parallel_period_of_overlap_halfPlane hdec hw hcu hwu
      (fun z hz hz' => hper z (hcover hz) (hcover hz'))
  exact Nivat.CosetPigeonhole.not_isPeriodic_T_of_not_isPeriodic e hnp ⟨v, hv, hv0⟩

/-! ## §8  `union_not` is discharged by the **outer** chain, not by Proposition 2.12

§7 above asks for a half-plane inside `⋃_n 𝓡^n_I = 𝓡_{I-1}`.  Re-reading the source shows
that hypothesis is aimed one level too low, and that the honest producer is cheaper.

`b3_colle2.txt:806`, verbatim:

> Note that `(T^u η)|ℋ(ℓ_{ι-m})` does not have a period parallel to `ℓ_{ι-m}` or `ℓ = ℓ_ι`,
> since otherwise **Proposition 2.12** would implies that `T^u η` is periodic.  Hence, as
> `𝓡_{ι-1} ⊂ 𝓡_{ι-2} ⊂ ⋯ ⊂ 𝓡_{ι-m+1}`, we may consider the **smallest** integer
> `ι-m+1 ≤ I ≤ ι-1` such that `(T^u η)|𝓡_I` is periodic of period `h`.

Two things follow that §7's framing missed:

1. **Proposition 2.12 is applied to `ℋ(ℓ_{ι-m})`, a genuine half-plane**, at the *top* of the
   outer chain `𝓡_{ι-1} ⊂ ⋯ ⊂ 𝓡_{ι-m+1}` — not to `𝓡_{I-1}`.  So §7's `hcover` is the right
   hypothesis at the wrong level: at the outer level the union **is** the half-plane and the
   inclusion is by construction, while at the inner level `𝓡_{I-1}` is a region, and a region
   need not contain a half-plane (`Colle41.IsRegion` gives two rays and lattice convexity,
   which span a cone, not a half-plane).

2. **`¬ PeriodOn (T^u η) 𝓡_{I-1} h` — that is, `union_not` for the inner family — is exactly
   the minimality of `I`.**  Reindex the outer chain as `C k := 𝓡_{ι-1-k}`, so `C` is
   increasing, `C 0 = 𝓡_{ι-1}` is `h`-periodic by Claim 4.6, and "`I` smallest with `𝓡_I`
   periodic" is "`K` greatest with `C K` periodic".  Then `𝓡_{I-1} = C (K+1)`, and
   `¬ PeriodOn x (C (K+1)) h` is the *second* output of `exists_greatest_periodOn` (§1).

So the same §1 lemma runs **twice**: once on the outer chain to select `I` and hand over
`union_not`, once on the inner slices to select `N`.  `RegionFamily.union_not` is therefore
not a debt of L1's inner family at all; it is a field of the outer chain, one level up.

**The two levels are the same object.**  An outer chain and an inner family are both "an
increasing family of `(u, u')`-regions, periodic at the bottom, not periodic in the union",
which is exactly `RegionFamily` (§2).  So no second structure is introduced: the selection
step is a **self-map** on `RegionFamily` (`sliceNext` below), taking the outer chain to the
inner family by slicing its `R (K+1) = 𝓡_{I-1}`.  One consequence worth stating: §4's
`witness` establishes non-vacuity for *both* levels at once, so this section adds no new
vacuity obligation.
-/

namespace RegionFamily

variable {x : Config ℤ} {u u' : ℤ × ℤ} {c : ℤ}

/-- **The index `I`** (`b3_colle2.txt:812`), in the reindexing `R k = 𝓡_{ι-1-k}`: the greatest
`K` with `R K` periodic, so that `R K = 𝓡_I` and `R (K+1) = 𝓡_{I-1}`.

This is `exists_greatest_periodOn` read at the outer level.  Its second component is exactly
`union_not` for the inner family — see `sliceNext`. -/
theorem exists_index_I (F : RegionFamily x u u' c) :
    ∃ K : ℕ, Colle41.PeriodOn x (F.R K) (c • u) ∧
      ¬ Colle41.PeriodOn x (F.R (K + 1)) (c • u) :=
  exists_greatest_periodOn F.monotone F.base F.union_not

/-- **The selection step, as a self-map on `RegionFamily`.**

`Rinf := F.R (K+1) = 𝓡_{I-1}`, sliced as in §3.  Every hypothesis here is slicing data
(§3's `ofCut` inputs); the one periodicity input that `RegionFamily` cannot produce on its
own — `union_not` — is `hK`, and `exists_index_I` produces it from the level above. -/
def sliceNext (F : RegionFamily x u u' c) {m : ℤ × ℤ} {lev : ℕ → ℤ} (K : ℕ)
    (hK : ¬ Colle41.PeriodOn x (F.R (K + 1)) (c • u))
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u)
    (hlev : Antitone lev) (hexh : ∀ b : ℤ, ∃ n, lev n ≤ b)
    (hgap : ∀ n, ∃ z ∈ F.R (K + 1), lev (n + 1) ≤ dot m z ∧ dot m z < lev n)
    (hbase : Colle41.PeriodOn x (cut (F.R (K + 1)) m lev 0) (c • u)) :
    RegionFamily x u u' c :=
  ofCut (F.isRegion (K + 1)) hmu' hmu hlev hexh hgap hbase hK

end RegionFamily

/-- **Conjuncts 10–14 and 16 from the outer chain, with no `union_not` hypothesis left.**

This is §5's `exists_conjuncts_10_14_16` with the inner family's `union_not` replaced by the
outer chain's, via `exists_index_I`.  The slicing hypotheses are quantified over **all**
indices `K`, because the index the maximality argument selects is not known in advance; in
the paper the `d_n` are defined after `I` is chosen (`:814` picks `I`, `b3_colle2.txt:816`
defines the `d_n`), so a producer
supplies them uniformly. -/
theorem exists_conjuncts_10_14_16_of_chain {ξ : Config ℤ} {e u u' : ℤ × ℤ} {c τ : ℤ}
    {m : ℤ × ℤ} {lev : ℕ → ℤ} {Q B S₁ : Finset (ℤ × ℤ)}
    (F : RegionFamily (T e ξ) u u' c)
    (hmu' : dot m u' = 0) (hmu : 0 < dot m u)
    (hlev : Antitone lev) (hexh : ∀ b : ℤ, ∃ n, lev n ≤ b)
    (hgap : ∀ K n : ℕ, ∃ z ∈ F.R (K + 1), lev (n + 1) ≤ dot m z ∧ dot m z < lev n)
    (hbase : ∀ K : ℕ, Colle41.PeriodOn (T e ξ) (cut (F.R (K + 1)) m lev 0) (c • u))
    (hline0 : ∀ K : ℕ, ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
      t • u' + z ∈ cut (F.R (K + 1)) m lev 0 ∧
        t • u' + z + c • u ∈ cut (F.R (K + 1)) m lev 0)
    (hbase0 : ∀ K : ℕ, ∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ cut (F.R (K + 1)) m lev 0) :
    ∃ R R' : Set (ℤ × ℤ),
      Colle41.PeriodOn (T e ξ) R (c • u) ∧
      Colle41.IsRegion R u u' ∧
      R ⊂ R' ∧
      ¬ Colle41.PeriodOn (T e ξ) R' (c • u) ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) ∧
      (∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R) := by
  obtain ⟨K, -, hK⟩ := F.exists_index_I
  exact exists_conjuncts_10_14_16
    (F.sliceNext K hK hmu' hmu hlev hexh (hgap K) (hbase K)) (hline0 K) (hbase0 K)

/-! ### §8.1  The outer chain's own `union_not`, from Proposition 2.12

Now §7 is applied where the paper applies it.  Two inputs remain, and their status is
different from what §7 recorded:

* `hdec : PeriodicDecompZ (T e ξ) nd` — **reachable from leaf L1's binders.**  L1 takes
  `d : DecompDataZ ξ` (`RegionSteps.lean:866`), `periodicDecompZ_of_decompDataZ`
  (`OrderThree.lean:282`) turns it into `PeriodicDecompZ ξ d.toDecompData.m`, and
  `periodicDecompZ_T` below transports that along `T e`.  See
  `periodicDecompZ_T_of_decompDataZ`.
* `hcover` — at this level the union is `ℋ(ℓ_{ι-m})` itself, so the inclusion is an equality
  by construction.  It is still **unchecked**, because the chain `𝓡_i` does not exist in
  Lean; what changed is that it is no longer being asked of a region.
-/

/-- Periodic decompositions transport along translations: `T e` commutes with the sum and
carries each periodic component to a periodic component
(`PeriodTransport.lean:15`, `mem_Per_T_of_mem_Per`). -/
theorem periodicDecompZ_T {ξ : Config ℤ} {n : ℕ} (e : ℤ × ℤ)
    (hdec : Nivat.PeriodicDecompZ ξ n) : Nivat.PeriodicDecompZ (T e ξ) n := by
  obtain ⟨f, hfp, hsum⟩ := hdec
  refine ⟨fun i => T e (f i), fun i => ?_, fun z => ?_⟩
  · obtain ⟨w, hw, hw0⟩ := hfp i
    exact ⟨w, Nivat.CosetPigeonhole.mem_Per_T_of_mem_Per e hw, hw0⟩
  · simpa only [T] using hsum (z + e)

/-- **Leaf L1's binder `d : DecompDataZ ξ` supplies `union_not_of_halfPlane_cover`'s first
argument.**  So the producer is reachable: the decomposition is not a new debt. -/
theorem periodicDecompZ_T_of_decompDataZ {ξ : Config ℤ} (d : Nivat.Colle35.DecompDataZ ξ)
    (e : ℤ × ℤ) : Nivat.PeriodicDecompZ (T e ξ) d.toDecompData.m :=
  periodicDecompZ_T e (Nivat.OrderThree.periodicDecompZ_of_decompDataZ d)

/-- **A `RegionFamily` at the outer level whose `union_not` is proved, not assumed** —
Collé's `ℋ(ℓ_{ι-m})` remark (`b3_colle2.txt:806`) in the kernel.

The decomposition argument is `d : DecompDataZ ξ`, exactly the binder leaf L1 already takes
(`RegionSteps.lean:866`); `hnp` is the non-periodicity of `ξ`.  What remains for a producer
is the chain `C` itself together with `hcover`. -/
def ofHalfPlane {ξ : Config ℤ} {e u u' : ℤ × ℤ} {c : ℤ}
    {C : ℕ → Set (ℤ × ℤ)} {w : ℝ × ℝ} {lvl : ℝ}
    (d : Nivat.Colle35.DecompDataZ ξ)
    (grow : ∀ k, C k ⊂ C (k + 1))
    (isRegion : ∀ k, Colle41.IsRegion (C k) u u')
    (base : Colle41.PeriodOn (T e ξ) (C 0) (c • u))
    (hw : w ≠ 0) (hcu : c • u ≠ 0) (hwu : inner2 w (c • u) = 0)
    (hcover : {z : ℤ × ℤ | lvl ≤ inner2 w z} ⊆ ⋃ k, C k)
    (hnp : ¬ Nivat.IsPeriodic ξ) :
    RegionFamily (T e ξ) u u' c where
  R := C
  grow := grow
  isRegion := isRegion
  base := base
  union_not :=
    union_not_of_halfPlane_cover (periodicDecompZ_T_of_decompDataZ d e) hw hcu hwu hcover hnp

/-! ### §8.2  `ofHalfPlane`'s remaining scalar hypotheses, from L1's own conjuncts

`ofHalfPlane` takes `hcu : c • u ≠ 0`.  That is not a new obligation: conjunct 5
(`det u u' ≠ 0`, `L1Data.lean:109`) and conjunct 9 (`c ≠ 0`, `L1Data.lean:118`) give it.

The other scalar input, `hnp : ¬ IsPeriodic ξ`, is the third component of `IsCounterexample`
(`Section8/ExternalDefs.lean:48`), so leaf L1's binder `hξ : IsMinimalCounterexample ξ`
supplies it as `hξ.1.2.2.1`.  No lemma is landed for that projection: a statement of the form
`IsMinimalCounterexample ξ → _` proves nothing about whether such a `ξ` exists, and this file
does not treat field access as content.
-/

/-- Conjunct 5 forces `u ≠ 0`: `det 0 u' = 0` for every `u'`. -/
theorem ne_zero_of_det_ne_zero {u u' : ℤ × ℤ} (h : det u u' ≠ 0) : u ≠ 0 := by
  intro h0
  apply h
  simp only [h0, det, Prod.fst_zero, Prod.snd_zero, zero_mul, sub_zero]

/-- **`ofHalfPlane`'s `hcu` from conjuncts 5 and 9.** -/
theorem smul_ne_zero_of_det_ne_zero {u u' : ℤ × ℤ} {c : ℤ} (hdet : det u u' ≠ 0) (hc : c ≠ 0) :
    c • u ≠ 0 :=
  zsmul_ne_zero_of_ne_zero hc (ne_zero_of_det_ne_zero hdet)

end Nivat.L1Region

section Receipts
/-! Standing `#print axioms` receipts.  Deletable as a block: everything between
`section Receipts` and `end Receipts` is measurement, not content. -/

#print axioms Nivat.L1Region.periodOn_iUnion_of_monotone
#print axioms Nivat.L1Region.exists_greatest_periodOn
#print axioms Nivat.L1Region.RegionFamily.exists_index
#print axioms Nivat.L1Region.exists_conjuncts_10_13
#print axioms Nivat.L1Region.ofCut
#print axioms Nivat.L1Region.witness_exists_index
#print axioms Nivat.L1Region.exists_conjuncts_10_14_16
#print axioms Nivat.L1Region.not_straddle_four
#print axioms Nivat.L1Region.exists_cut_normal
#print axioms Nivat.L1Region.union_not_of_halfPlane_cover
#print axioms Nivat.L1Region.RegionFamily.exists_index_I
#print axioms Nivat.L1Region.RegionFamily.sliceNext
#print axioms Nivat.L1Region.exists_conjuncts_10_14_16_of_chain
#print axioms Nivat.L1Region.periodicDecompZ_T
#print axioms Nivat.L1Region.periodicDecompZ_T_of_decompDataZ
#print axioms Nivat.L1Region.ofHalfPlane
#print axioms Nivat.L1Region.smul_ne_zero_of_det_ne_zero

end Receipts
