/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.Lemma41

/-!
# `L1Prim` — half-plane nesting forces parallel normals

One sentence has been carrying a lot of weight in the `base`-reuse discussion, and until this
file it was only prose:

> two half-planes with **non-parallel** normals never contain one another (each has a point
> outside the other).

That sentence is the reason `base : PeriodOn x (halfPlaneGE m lev₀) (c • u)`
(`HalfPlaneFamily.lean:188`) cannot be recycled across a change of cutting normal `m`: a period
proved on one half-plane transports to another only along an inclusion of the underlying sets,
and this file shows the inclusion simply does not exist unless the normals are parallel.

## What is proved

The core is the **witness** form, matching the parenthetical of the sentence above:

* `exists_mem_not_mem_of_det_ne_zero` — if `det m₁ m₂ ≠ 0` then there is an explicit
  `z ∈ halfPlaneGE m₁ c₁` with `z ∉ halfPlaneGE m₂ c₂`.  The witness is `z₀ + t • (-m₁.2, m₁.1)`:
  sliding along `m₁`'s own perpendicular keeps `dot m₁` constant (so the point never leaves the
  first half-plane) while moving `dot m₂` by `t * det m₁ m₂` per step (so it is driven below
  `c₂` once `det ≠ 0`).

From it, in decreasing order of strength:

* `not_halfPlaneGE_subset_of_det_ne_zero` — the sentence itself.
* `not_halfPlaneGE_subset_of_det_ne_zero'` — the "**each** has a point outside the other"
  reading: both inclusions fail simultaneously.
* `det_eq_zero_of_halfPlaneGE_subset` — the contrapositive, in the shape a consumer that
  *has* an inclusion will want: nesting forces `det m₁ m₂ = 0`.

## Two facts found while proving it (both recorded as theorems, not prose)

1. **No extra hypothesis is needed.**  `det m₁ m₂ = 0` holds with no `m₁ ≠ 0`, no `Prim`, no
   nonemptiness side condition: the degenerate normal `m₁ = 0` makes `det m₁ m₂ = 0` outright,
   so it needs no separate treatment.  The lattice-versus-real-plane worry does not bite here
   because the sliding direction `(-m₁.2, m₁.1)` is itself a lattice vector.

2. **The conclusion cannot be strengthened to "`m₂` is a positive multiple of `m₁`".**
   `halfPlaneGE (2,0) 0 ⊆ halfPlaneGE (1,0) 0` holds (`halfPlaneGE_two_subset_one`) and `(1,0)`
   is not `k • (2,0)` for any `k`, so `not_forall_exists_smul_of_halfPlaneGE_subset` refutes
   that shape.  A *divisor* of the normal is admissible; only the **direction** is pinned.
   `dot_pos_of_halfPlaneGE_subset` states exactly how much direction information survives:
   `0 < dot m₁ m₂`, which is what rules out the anti-parallel case `m₂ = -m₁` that
   `det m₁ m₂ = 0` on its own permits.

## Provenance note (§20)

`(-m.2, m.1)` is `Nivat.ColleReg.perp` (`Claim47Core.lean:45`) and its primitivity is
`Nivat.ColleReg.primitive_perp` (`Claim47Core.lean:67`).  Neither is re-proved here; the literal
pair is used inline rather than importing `Claim47Core`, which would pull in `KariMoutot`,
`Generating`, `Lemma41` and `OrbitClosureBasics` for one two-field definition.
-/

set_option autoImplicit false

namespace Nivat.L1Prim

open Nivat Nivat.LE2

/-! ## §1. The sliding direction

`(-m.2, m.1)` is annihilated by `dot m` and pairs with any other normal exactly by the
determinant.  These two equalities are the whole geometric content; everything below is
arithmetic on them. -/

theorem dot_perp_self (m : ℤ × ℤ) : dot m (-m.2, m.1) = 0 := by
  simp only [dot]; ring

theorem dot_perp_det (m₁ m₂ : ℤ × ℤ) : dot m₂ (-m₁.2, m₁.1) = det m₁ m₂ := by
  simp only [dot, det]; ring

/-- A nonzero normal pairs positively with itself. -/
theorem dot_self_pos {m : ℤ × ℤ} (hm : m ≠ 0) : 0 < dot m m := by
  have h : m.1 ≠ 0 ∨ m.2 ≠ 0 := by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact hm (Prod.ext hc.1 hc.2)
  simp only [dot]
  rcases h with h | h
  · have h1 : 0 < m.1 * m.1 := mul_self_pos.mpr h
    nlinarith [mul_self_nonneg m.2]
  · have h1 : 0 < m.2 * m.2 := mul_self_pos.mpr h
    nlinarith [mul_self_nonneg m.1]

/-- A half-plane with a nonzero normal is nonempty: walk far enough along the normal itself. -/
theorem halfPlaneGE_nonempty {m : ℤ × ℤ} (hm : m ≠ 0) (c : ℤ) :
    (halfPlaneGE m c).Nonempty := by
  have hd : 0 < dot m m := dot_self_pos hm
  obtain ⟨N, hN0, hNc⟩ : ∃ N : ℤ, 0 ≤ N ∧ c ≤ N := ⟨max c 0, le_max_right _ _, le_max_left _ _⟩
  refine ⟨(N * m.1, N * m.2), ?_⟩
  show c ≤ dot m (N * m.1, N * m.2)
  have hrw : dot m (N * m.1, N * m.2) = N * dot m m := by simp only [dot]; ring
  rw [hrw]
  nlinarith [mul_nonneg hN0 (by linarith : (0 : ℤ) ≤ dot m m - 1)]

/-! ## §2. The witness

The heart of the file.  No hypothesis beyond `det m₁ m₂ ≠ 0` — in particular `m₁ ≠ 0` is a
consequence, not an assumption. -/

/-- **Each half-plane has a point outside the other, whenever the normals are not parallel.**
The witness slides from an arbitrary point of `halfPlaneGE m₁ c₁` along `(-m₁.2, m₁.1)`, which
leaves `dot m₁` fixed and decreases `dot m₂` without bound. -/
theorem exists_mem_not_mem_of_det_ne_zero {m₁ m₂ : ℤ × ℤ} (hd : det m₁ m₂ ≠ 0) (c₁ c₂ : ℤ) :
    ∃ z, z ∈ halfPlaneGE m₁ c₁ ∧ z ∉ halfPlaneGE m₂ c₂ := by
  have hm : m₁ ≠ 0 := by
    intro h
    apply hd
    rw [h]
    simp [det]
  obtain ⟨z₀, hz₀mem⟩ := halfPlaneGE_nonempty hm c₁
  have hz₀ : c₁ ≤ dot m₁ z₀ := hz₀mem
  -- `d * d ≥ 1` is the only place `det ≠ 0` is consumed quantitatively.
  have hdd : 1 ≤ det m₁ m₂ * det m₁ m₂ := by
    rcases lt_or_gt_of_ne hd with hlt | hgt <;> nlinarith
  -- how far below `c₂` we must push, plus one step of slack
  obtain ⟨K, hK1, hslack⟩ : ∃ K : ℤ, 1 ≤ K ∧ dot m₂ z₀ - c₂ + 1 ≤ K :=
    ⟨max (dot m₂ z₀ - c₂ + 1) 1, le_max_right _ _, le_max_left _ _⟩
  have hstep : K ≤ K * (det m₁ m₂ * det m₁ m₂) := by nlinarith
  set t : ℤ := -(K * det m₁ m₂) with htdef
  refine ⟨(z₀.1 + t * (-m₁.2), z₀.2 + t * m₁.1), ?_, ?_⟩
  · show c₁ ≤ dot m₁ (z₀.1 + t * (-m₁.2), z₀.2 + t * m₁.1)
    have hrw : dot m₁ (z₀.1 + t * (-m₁.2), z₀.2 + t * m₁.1) = dot m₁ z₀ := by
      simp only [dot]; ring
    rw [hrw]
    exact hz₀
  · show ¬ (c₂ ≤ dot m₂ (z₀.1 + t * (-m₁.2), z₀.2 + t * m₁.1))
    have hrw : dot m₂ (z₀.1 + t * (-m₁.2), z₀.2 + t * m₁.1)
        = dot m₂ z₀ - K * (det m₁ m₂ * det m₁ m₂) := by
      simp only [dot, htdef, det]; ring
    rw [hrw]
    intro hc
    linarith

/-- **The prose sentence, as a kernel fact.**  Non-parallel normals ⟹ no inclusion. -/
theorem not_halfPlaneGE_subset_of_det_ne_zero {m₁ m₂ : ℤ × ℤ} (hd : det m₁ m₂ ≠ 0) (c₁ c₂ : ℤ) :
    ¬ halfPlaneGE m₁ c₁ ⊆ halfPlaneGE m₂ c₂ := by
  intro hsub
  obtain ⟨z, hz1, hz2⟩ := exists_mem_not_mem_of_det_ne_zero hd c₁ c₂
  exact hz2 (hsub hz1)

/-- The "**each** has a point outside the other" reading: both inclusions fail at once.  The
second uses `det m₂ m₁ = -det m₁ m₂ ≠ 0`. -/
theorem not_halfPlaneGE_subset_of_det_ne_zero' {m₁ m₂ : ℤ × ℤ} (hd : det m₁ m₂ ≠ 0) (c₁ c₂ : ℤ) :
    ¬ halfPlaneGE m₁ c₁ ⊆ halfPlaneGE m₂ c₂ ∧ ¬ halfPlaneGE m₂ c₂ ⊆ halfPlaneGE m₁ c₁ := by
  refine ⟨not_halfPlaneGE_subset_of_det_ne_zero hd c₁ c₂, ?_⟩
  refine not_halfPlaneGE_subset_of_det_ne_zero ?_ c₂ c₁
  rw [det_comm]
  simpa using hd

/-! ## §3. The contrapositive, for a consumer that already has an inclusion -/

/-- **Nesting forces parallel normals.**  No side condition: `m₁ = 0` makes the conclusion
true outright, and `m₂ = 0` is likewise absorbed. -/
theorem det_eq_zero_of_halfPlaneGE_subset {m₁ m₂ : ℤ × ℤ} {c₁ c₂ : ℤ}
    (h : halfPlaneGE m₁ c₁ ⊆ halfPlaneGE m₂ c₂) : det m₁ m₂ = 0 := by
  by_contra hd
  exact not_halfPlaneGE_subset_of_det_ne_zero hd c₁ c₂ h

/-! ## §4. How much more than parallelism survives

Parallelism alone is not the whole story — the *direction* is pinned too, so the anti-parallel
case `m₂ = -m₁` is excluded.  But a positive scalar multiple is **not** forced: see §5. -/

/-- Nesting also forces the two normals to point to the same side: `0 < dot m₁ m₂`.  This is
what rules out `m₂ = -m₁`, which `det m₁ m₂ = 0` alone permits. -/
theorem dot_pos_of_halfPlaneGE_subset {m₁ m₂ : ℤ × ℤ} {c₁ c₂ : ℤ} (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0)
    (h : halfPlaneGE m₁ c₁ ⊆ halfPlaneGE m₂ c₂) : 0 < dot m₁ m₂ := by
  have hdet : det m₁ m₂ = 0 := det_eq_zero_of_halfPlaneGE_subset h
  -- First: parallel and orthogonal at once forces `m₂ = 0`, so `dot m₁ m₂ ≠ 0`.
  have hne : dot m₁ m₂ ≠ 0 := by
    intro h0
    apply hm₂
    simp only [dot] at h0
    simp only [det] at hdet
    have hpos : 0 < m₁.1 * m₁.1 + m₁.2 * m₁.2 := by
      have := dot_self_pos hm₁
      simpa [dot] using this
    have h1 : m₂.1 * (m₁.1 * m₁.1 + m₁.2 * m₁.2) = 0 := by
      linear_combination m₁.1 * h0 - m₁.2 * hdet
    have h2 : m₂.2 * (m₁.1 * m₁.1 + m₁.2 * m₁.2) = 0 := by
      linear_combination m₁.2 * h0 + m₁.1 * hdet
    have e1 : m₂.1 = 0 := by
      rcases mul_eq_zero.mp h1 with hx | hx
      · exact hx
      · exfalso; linarith
    have e2 : m₂.2 = 0 := by
      rcases mul_eq_zero.mp h2 with hx | hx
      · exact hx
      · exfalso; linarith
    exact Prod.ext e1 e2
  -- Second: if it were negative, walking along `m₁` itself escapes `halfPlaneGE m₂ c₂`.
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exfalso
    have hd1 : 0 < dot m₁ m₁ := dot_self_pos hm₁
    have hneg : dot m₁ m₂ ≤ -1 := by linarith
    obtain ⟨z₀, hz₀mem⟩ := halfPlaneGE_nonempty hm₁ c₁
    have hz₀ : c₁ ≤ dot m₁ z₀ := hz₀mem
    obtain ⟨j, hj0, hjslack⟩ : ∃ j : ℤ, 0 ≤ j ∧ dot m₂ z₀ - c₂ + 1 ≤ j :=
      ⟨max (dot m₂ z₀ - c₂ + 1) 0, le_max_right _ _, le_max_left _ _⟩
    have hmem : (z₀.1 + j * m₁.1, z₀.2 + j * m₁.2) ∈ halfPlaneGE m₁ c₁ := by
      show c₁ ≤ dot m₁ (z₀.1 + j * m₁.1, z₀.2 + j * m₁.2)
      have hrw : dot m₁ (z₀.1 + j * m₁.1, z₀.2 + j * m₁.2) = dot m₁ z₀ + j * dot m₁ m₁ := by
        simp only [dot]; ring
      rw [hrw]
      nlinarith [mul_nonneg hj0 (le_of_lt hd1)]
    have hout : c₂ ≤ dot m₂ (z₀.1 + j * m₁.1, z₀.2 + j * m₁.2) := h hmem
    have hrw2 : dot m₂ (z₀.1 + j * m₁.1, z₀.2 + j * m₁.2) = dot m₂ z₀ + j * dot m₁ m₂ := by
      simp only [dot]; ring
    rw [hrw2] at hout
    nlinarith [mul_nonneg hj0 (by linarith : (0 : ℤ) ≤ -1 - dot m₁ m₂)]
  · exact hgt

/-! ## §5. The strengthening that is **false**

Recorded so nobody later upgrades `det_eq_zero_of_halfPlaneGE_subset`'s conclusion to
"`m₂ = k • m₁` for some `k > 0`".  A normal may shrink to a divisor of itself under nesting. -/

theorem halfPlaneGE_two_subset_one :
    halfPlaneGE ((2 : ℤ), (0 : ℤ)) 0 ⊆ halfPlaneGE ((1 : ℤ), (0 : ℤ)) 0 := by
  intro z hz
  have hz' : (0 : ℤ) ≤ dot ((2 : ℤ), (0 : ℤ)) z := hz
  show (0 : ℤ) ≤ dot ((1 : ℤ), (0 : ℤ)) z
  simp only [dot] at hz' ⊢
  omega

/-- **Refutation of the scalar-multiple shape.**  Nesting does not force `m₂` to be a positive
multiple of `m₁`: `(2,0)`'s half-plane sits inside `(1,0)`'s, and `(1,0)` is not `k • (2,0)`.
So `det m₁ m₂ = 0` (plus `0 < dot m₁ m₂`) is the sharp conclusion. -/
theorem not_forall_exists_smul_of_halfPlaneGE_subset :
    ¬ ∀ (m₁ m₂ : ℤ × ℤ) (c₁ c₂ : ℤ), halfPlaneGE m₁ c₁ ⊆ halfPlaneGE m₂ c₂ →
      ∃ k : ℤ, 0 < k ∧ m₂ = k • m₁ := by
  intro hall
  obtain ⟨k, -, hk⟩ := hall ((2 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) 0 0 halfPlaneGE_two_subset_one
  have h1 : (1 : ℤ) = k * 2 := congrArg Prod.fst hk
  omega

/-! ## §6. Claim 4.6's inductive step — three naive forms, all false

Lane Aface, 2026-09-19, refutation side of Claim 4.6 (`b3_colle2.txt:780-800`), AnfpL leading
the positive side.  Collé's induction extends periodicity outward one lattice line at a time:

> we may extend the periodicity from `(T^u(η−η̄))|H_B(ℓ)` to `(T^u(η−η̄))|H_B(ℓ) ∪ A₁`, where
> `A₁ := 𝓡_{ι−1} ∩ l₁` … Proceeding this way, we get by induction that `(T^u η)|𝓡_{ι−1}` is
> periodic with period parallel to `ℓ`.  (`b3_colle2.txt:793-800`)

"Proceeding this way" is one sentence covering the whole induction.  Before anyone formalises
it, this section asks what the *step* is, by writing down the forms someone would naturally
write and killing them.  All four witnesses are explicit configurations on `ℤ × ℤ`.

### Witness legality

These refute **general-purpose statements about `Colle41.PeriodOn`** (`Lemma41.lean:659`,
Definition 2.11) — set-and-configuration statements with **no Collé-definition preconditions at
all**: no `IsMinimalCounterexample`, no generating set, no enveloped `B`, no region.  There is
therefore nothing a witness could fail to satisfy; `xcol`/`xshift` are total configurations and
`Ucol`/`Vcol` are literal `setOf`s.  This is the easy end of the legality checklist
(`nivat-refutation`), and it is stated explicitly because the *hard* end is where this project
has previously shipped illegal witnesses (`EnvelopedConvex.lean:483`).

### 🔴 What these do and do not refute

They refute **our own weakened readings of the step**, not Collé's Claim 4.6.  Per the skill's
rule, the conclusion is therefore *"the induction has to carry more information"*, **not**
*"the paper is wrong"*.  Specifically, §6.4 identifies the information: the accumulated region
must be **`h`-invariant** (a union of complete `ℓ`-lines).  That is true of Collé's chain by
construction — `H_B(ℓ)` is a half-strip bounded by `ℓ`-parallel lines and each `A_i` is a full
line `l_i` — and it is exactly the hypothesis that disappears if one formalises the step as
"the new points are determined by the old ones". -/

/-- The counting configuration `x (a, b) = a`, and the period `(1,0)` transverse to the columns
below.  Every refutation in §6.1-§6.3 uses this pair. -/
private def xcol : Config ℤ := fun z => z.1

private def Ucol : Set (ℤ × ℤ) := {z | z.1 = 0}

private def Vcol : Set (ℤ × ℤ) := {z | z.1 = 0 ∨ z.1 = 1}

/-- `Ucol` is `(1,0)`-periodic **vacuously**: no `z` has both `z` and `z + (1,0)` in a single
column.  This is the whole engine of §6.1-§6.3 — `PeriodOn` is an *overlap-only* predicate
(`L1Region.lean:77`), so a region too thin to contain an `h`-step constrains nothing. -/
theorem periodOn_Ucol : Colle41.PeriodOn xcol Ucol ((1 : ℤ), (0 : ℤ)) := by
  intro z hz hzh
  exfalso
  have h1 : z.1 = 0 := hz
  have h2 : (z + ((1 : ℤ), (0 : ℤ))).1 = 0 := hzh
  simp only [Prod.fst_add] at h2
  omega

theorem not_periodOn_Vcol : ¬ Colle41.PeriodOn xcol Vcol ((1 : ℤ), (0 : ℤ)) := by
  intro hp
  have hz : ((0 : ℤ), (0 : ℤ)) ∈ Vcol := Or.inl rfl
  have hzh : ((0 : ℤ), (0 : ℤ)) + ((1 : ℤ), (0 : ℤ)) ∈ Vcol := Or.inr rfl
  have := hp _ hz hzh
  simp only [xcol] at this
  exact absurd this (by decide)

theorem Ucol_subset_Vcol : Ucol ⊆ Vcol := fun _ hz => Or.inl hz

/-! ### §6.1  Overlap alone does not propagate -/

/-- **Naive step 1.**  "The next region overlaps the current one, so periodicity carries over."
False. -/
theorem not_forall_periodOn_of_overlap :
    ¬ ∀ (x : Config ℤ) (U V : Set (ℤ × ℤ)) (h : ℤ × ℤ),
      Colle41.PeriodOn x U h → U ⊆ V → (U ∩ V).Nonempty → Colle41.PeriodOn x V h := by
  intro hall
  exact not_periodOn_Vcol
    (hall xcol Ucol Vcol ((1 : ℤ), (0 : ℤ)) periodOn_Ucol Ucol_subset_Vcol
      ⟨((0 : ℤ), (0 : ℤ)), rfl, Or.inl rfl⟩)

/-! ### §6.2  Even an exact `U ∪ (U + h)` cover does not propagate

This is the sharpest form of "adjacent layers overlap": the new region is *nothing but* the old
one together with its own `h`-translate.  Still false — and this is the useful one, because it
shows the failure is not about the new region being large. -/

theorem Vcol_eq_union_shift :
    Vcol = Ucol ∪ (fun z => z + ((1 : ℤ), (0 : ℤ))) '' Ucol := by
  ext z
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ⟨(0, z.2), rfl, ?_⟩
      have : z.1 = 1 := h
      exact Prod.ext (by simpa using this.symm) (by simp)
  · rintro (h | ⟨w, hw, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ?_
      have : w.1 = 0 := hw
      show (w + ((1 : ℤ), (0 : ℤ))).1 = 1
      simp only [Prod.fst_add]
      omega

/-- **Naive step 2 — the sharp one.**  "The new region is the old region together with its
`h`-shift, so periodicity carries over."  **False.**

The reason is structural, not accidental: `PeriodOn x U h` says nothing whatsoever when `U` is
too thin to contain a single `h`-step, and `U ∪ (U + h)` is then exactly thick enough to create
one brand-new constraint that `U` never had to satisfy.  Any formalisation of Collé's step that
reduces to "cover the new layer by shifts of the old" is unsound. -/
theorem not_forall_periodOn_of_eq_union_shift :
    ¬ ∀ (x : Config ℤ) (U V : Set (ℤ × ℤ)) (h : ℤ × ℤ),
      Colle41.PeriodOn x U h → V = U ∪ (fun z => z + h) '' U → Colle41.PeriodOn x V h := by
  intro hall
  exact not_periodOn_Vcol
    (hall xcol Ucol Vcol ((1 : ℤ), (0 : ℤ)) periodOn_Ucol Vcol_eq_union_shift)

/-! ### §6.3  Union closure needs monotonicity — a guard on `periodOn_iUnion_of_monotone`

`Nivat.L1Region.periodOn_iUnion_of_monotone` (`L1Region.lean:80`) is already proved and is what
AnfpL's scaffolding half (a) would use to pass from the layers to `wedgeFull`.  Its `hmono` is
**not** decoration: without it the statement is false, by the same thin-region mechanism. -/

private def RfCol : ℕ → Set (ℤ × ℤ) := fun n => {z | z.1 = (n : ℤ)}

theorem periodOn_RfCol (n : ℕ) : Colle41.PeriodOn xcol (RfCol n) ((1 : ℤ), (0 : ℤ)) := by
  intro z hz hzh
  exfalso
  have h1 : z.1 = (n : ℤ) := hz
  have h2 : (z + ((1 : ℤ), (0 : ℤ))).1 = (n : ℤ) := hzh
  simp only [Prod.fst_add] at h2
  omega

/-- **Naive step 3.**  "Each layer is periodic, so the union is."  **False without
monotonicity** — the two endpoints of an `h`-step may sit in different layers, where no
hypothesis relates them.  `periodOn_iUnion_of_monotone`'s own docstring names this mechanism;
this theorem is the receipt that it is a real obstruction and not a proof-convenience. -/
theorem not_forall_periodOn_iUnion :
    ¬ ∀ (x : Config ℤ) (Rf : ℕ → Set (ℤ × ℤ)) (h : ℤ × ℤ),
      (∀ n, Colle41.PeriodOn x (Rf n) h) → Colle41.PeriodOn x (⋃ n, Rf n) h := by
  intro hall
  have hp := hall xcol RfCol ((1 : ℤ), (0 : ℤ)) periodOn_RfCol
  have hz : ((0 : ℤ), (0 : ℤ)) ∈ ⋃ n, RfCol n :=
    Set.mem_iUnion.mpr ⟨0, by show (0 : ℤ) = ((0 : ℕ) : ℤ); simp⟩
  have hzh : ((0 : ℤ), (0 : ℤ)) + ((1 : ℤ), (0 : ℤ)) ∈ ⋃ n, RfCol n :=
    Set.mem_iUnion.mpr ⟨1, by show (0 : ℤ) + 1 = ((1 : ℕ) : ℤ); simp⟩
  have := hp _ hz hzh
  simp only [xcol] at this
  exact absurd this (by decide)

/-! ### §6.4  The real content: determination is **not** enough — `h`-invariance is

Collé's justification for the step is that `𝒮_{φι}` is a generating set for `η − η̄_{ι₀}` with
**no edge parallel to `ℓ` or `−ℓ`**, so the value at each new point is determined by values at
already-known points (`b3_colle2.txt:791-795`, Figure 10: *"the knowledge of `T^u η` on
`H_B(ℓ)` determines uniquely `T^u η` on `A₁`"*).

The naive formalisation of that is: *each new point copies a known point by a fixed offset*
(fixed = translation-equivariant, which is what a generating set gives).  **That is still not
enough**, and `not_forall_periodOn_of_determined` below is the witness.

`periodOn_of_copy_of_invariant` isolates precisely what closes the gap: the old region must be
**`h`-invariant**.  With it the step is four lines and entirely free of geometry; without it,
false.  In Collé's chain the invariance holds because `h ∥ ℓ` and every region in the chain is a
union of complete `ℓ`-lines — so the content that must survive into the Lean induction is the
*`ℓ`-line structure of the regions*, not the determination. -/

/-- **The step, once `h`-invariance is supplied.**  Free: no geometry, no generating set, no
lattice convexity.  `hwin`/`hcopy` are the determination; `hinv` is what §6.4's refutation shows
cannot be dropped.

The proof is the three-case split on which of `z`, `z + h` is new; `hinv` is what makes the
mixed case (`z` old, `z + h` new) vacuous.

⚠ Note `U ⊆ V` is **not** a hypothesis: it turned out to be unused, so it is dropped rather than
carried as decoration.  (The refutation below *does* assume it — assuming more there makes the
refutation stronger, not weaker.) -/
theorem periodOn_of_copy_of_invariant {A : Type*} {x : Config A} {U V : Set (ℤ × ℤ)}
    {h w : ℤ × ℤ}
    (hinv : ∀ z : ℤ × ℤ, z + h ∈ U ↔ z ∈ U)
    (hper : Colle41.PeriodOn x U h)
    (hwin : ∀ z ∈ V, z ∉ U → z + w ∈ U)
    (hcopy : ∀ z ∈ V, z ∉ U → x z = x (z + w)) :
    Colle41.PeriodOn x V h := by
  intro z hz hzh
  by_cases hzU : z ∈ U
  · -- `z` old; by `hinv` so is `z + h`, and `hper` applies directly.
    exact hper z hzU ((hinv z).mpr hzU)
  · -- `z` new; by `hinv` so is `z + h`, and both copy into `U` one `h`-step apart.
    have hzhU : z + h ∉ U := fun hc => hzU ((hinv z).mp hc)
    have h1 : x z = x (z + w) := hcopy z hz hzU
    have h2 : x (z + h) = x (z + h + w) := hcopy (z + h) hzh hzhU
    have hmem : z + w ∈ U := hwin z hz hzU
    have hmem' : z + w + h ∈ U := by
      have heq : z + h + w = z + w + h := by abel
      have hx := hwin (z + h) hzh hzhU
      rwa [heq] at hx
    have h3 : x (z + w + h) = x (z + w) := hper (z + w) hmem hmem'
    have heq : z + h + w = z + w + h := by abel
    rw [h2, heq, h3, h1]

/-- The configuration for §6.4: column `0` carries `b`, column `1` carries `b + 1`.  Each point
of column `1` copies a point of column `0` under the **fixed** offset `(-1, 1)`, so
determination holds — yet the `(1,0)`-step from column `0` to column `1` changes the value. -/
private def xshift : Config ℤ := fun z => if z.1 = 1 then z.2 + 1 else z.2

/-- **Naive step 4 — the informative one.**  "Every new point is determined from the known
region by a fixed offset, so periodicity extends."  **False.**

`Ucol` is `(1,0)`-periodic, `Vcol` is covered, every new point copies an old one under the
fixed offset `(-1,1)` — and periodicity still fails.  What is missing is exactly `hinv` of
`periodOn_of_copy_of_invariant`: `Ucol` is a single column, and `(-1,0) + (1,0) ∈ Ucol` while
`(-1,0) ∉ Ucol`, so it is **not** `(1,0)`-invariant.

**Consequence for the induction (AnfpL):** carrying "the new layer is determined by the old
one" through the induction is insufficient, no matter how the determination is packaged.  The
invariant that has to be carried is that every region in the chain is a **union of complete
`h`-lines** (`h ∥ ℓ`), which for Collé's chain is true by construction of `H_B(ℓ)` and the
`A_i`, and is the thing a Lean formalisation will silently drop. -/
theorem not_forall_periodOn_of_determined :
    ¬ ∀ (x : Config ℤ) (U V : Set (ℤ × ℤ)) (h w : ℤ × ℤ),
      U ⊆ V → Colle41.PeriodOn x U h →
      (∀ z ∈ V, z ∉ U → z + w ∈ U) →
      (∀ z ∈ V, z ∉ U → x z = x (z + w)) →
      Colle41.PeriodOn x V h := by
  intro hall
  have hperU : Colle41.PeriodOn xshift Ucol ((1 : ℤ), (0 : ℤ)) := by
    intro z hz hzh
    exfalso
    have h1 : z.1 = 0 := hz
    have h2 : (z + ((1 : ℤ), (0 : ℤ))).1 = 0 := hzh
    simp only [Prod.fst_add] at h2
    omega
  have hwin : ∀ z ∈ Vcol, z ∉ Ucol → z + ((-1 : ℤ), (1 : ℤ)) ∈ Ucol := by
    intro z hz hzU
    have h1 : z.1 = 1 := Or.resolve_left hz hzU
    show (z + ((-1 : ℤ), (1 : ℤ))).1 = 0
    simp only [Prod.fst_add]
    omega
  have hcopy : ∀ z ∈ Vcol, z ∉ Ucol → xshift z = xshift (z + ((-1 : ℤ), (1 : ℤ))) := by
    intro z hz hzU
    have h1 : z.1 = 1 := Or.resolve_left hz hzU
    have h2 : (z + ((-1 : ℤ), (1 : ℤ))).1 = 0 := by simp only [Prod.fst_add]; omega
    simp only [xshift, h1, h2]
    norm_num
  have hp := hall xshift Ucol Vcol ((1 : ℤ), (0 : ℤ)) ((-1 : ℤ), (1 : ℤ))
    Ucol_subset_Vcol hperU hwin hcopy
  have hz : ((0 : ℤ), (0 : ℤ)) ∈ Vcol := Or.inl rfl
  have hzh : ((0 : ℤ), (0 : ℤ)) + ((1 : ℤ), (0 : ℤ)) ∈ Vcol := Or.inr rfl
  have := hp _ hz hzh
  simp only [xshift] at this
  norm_num at this

/-- `Ucol` is not `(1,0)`-invariant — the hypothesis whose absence §6.4 exploits, named so the
refutation cannot be misread as an argument against `periodOn_of_copy_of_invariant`. -/
theorem Ucol_not_invariant :
    ¬ ∀ z : ℤ × ℤ, z + ((1 : ℤ), (0 : ℤ)) ∈ Ucol ↔ z ∈ Ucol := by
  intro hall
  have h := (hall ((-1 : ℤ), (0 : ℤ))).mp (by show ((-1 : ℤ) + 1) = 0; omega)
  have : (-1 : ℤ) = 0 := h
  exact absurd this (by decide)

/-! ## §7  `c ≠ 0` is free from `hinf` — the "eighth residual" retracted

In the `tmp/Aface_l1_skeleton.lean` receipt I reported `c0 : c ≠ 0` (`L1Claim.lean:116`) as an
*eighth, unowned* residual of the L1 composite, on the ground that `ofWedge` explicitly declines
to supply it (`L1RegionBuild.lean:149-150`: "nothing here names `c`").  **Cclaim pointed out
that it is not a residual at all: it falls out of `hinf`.**  §7 is the kernel receipt for their
argument, stated at full generality (no `wedgeFull`, no geometry, so it costs nothing and
imports nothing new).

Mechanism: a zero period is vacuous for *every* configuration and *every* set, because
`PeriodOn` (Definition 2.11, `Lemma41.lean:659`) asks `x (z + h) = x z` and `h = 0` makes that
`rfl`.  So any hypothesis of the form `¬ PeriodOn x U (c • v)` — and `hinf` is exactly that —
already carries `c ≠ 0`.

⚠ Scope: this is the *only* thing `hinf` gives away for free in that direction.  It does **not**
bound `c`, fix its sign, or relate it to `vl`; §7 is not a route to weakening `hinf`. -/

/-- A zero period holds on every set, for every configuration: `PeriodOn`'s conclusion at
`h = 0` is `x (z + 0) = x z`. -/
theorem periodOn_zero {A : Type*} (x : Config A) (U : Set (ℤ × ℤ)) :
    Colle41.PeriodOn x U 0 := by
  intro z _ _
  rw [add_zero]

/-- **`c0` is free.**  Any `¬ PeriodOn x U (c • v)` forces `c ≠ 0`.  Instantiated at
`U := wedgeFull …`, `v := vl`, this is `ofWedge`'s `hinf` discharging `_of_family`'s `c0`, so the
L1 composite's residual list stays at seven. -/
theorem ne_zero_of_not_periodOn_smul {A : Type*} {x : Config A} {U : Set (ℤ × ℤ)} {v : ℤ × ℤ}
    {c : ℤ} (h : ¬ Colle41.PeriodOn x U (c • v)) : c ≠ 0 := by
  rintro rfl
  exact h (by rw [zero_smul]; exact periodOn_zero x U)

/-- Non-vacuity guard for §7: hypotheses of the shape `¬ PeriodOn x U (c • v)` are satisfiable,
so `ne_zero_of_not_periodOn_smul` is not being applied to an empty class.  Witness reused from
§6.1 (`xcol`, `Vcol`, `c = 1`, `v = (1,0)`). -/
theorem exists_not_periodOn_smul :
    ∃ (x : Config ℤ) (U : Set (ℤ × ℤ)) (c : ℤ) (v : ℤ × ℤ),
      ¬ Colle41.PeriodOn x U (c • v) :=
  ⟨xcol, Vcol, 1, ((1 : ℤ), (0 : ℤ)), by rw [one_smul]; exact not_periodOn_Vcol⟩

/-! ## §8  `hinv` is unavailable on a cut half-plane — for the *same* reason `c0` is free

§6.4 isolated `hinv : ∀ z, z + h ∈ U ↔ z ∈ U` as the hypothesis that turns "determined by a
copy" into genuine periodicity.  §8 answers the obvious follow-up — *is `hinv` available on the
regions leaf L1 actually uses?* — and the answer is **no, never**, by a one-line computation
that reuses §7.

Mechanism.  A half-plane `halfPlaneGE n k` is `h`-invariant (in the iff sense `hinv` asks for)
**iff** `dot n h = 0`.  The L1 chain's cut normal satisfies `dot (expNormal u' vl) vl = 1`
(`dot_expNormal_vl`, `L1RegionBuild.lean:288`, under `hunimod`), so translating by the period
`h = c • vl` shifts the cut level by exactly `c`.  Hence `hinv` on that cut holds **iff `c = 0`**
— and `c = 0` is precisely what `hinf` forbids (§7).  So the hypothesis that makes `c0` free is
the same hypothesis that makes `hinv` unattainable: they cannot both be had.

⚠ **Read this as a scope limit on §6.4, not as a refutation of anyone's scaffolding.**  It says
`periodOn_of_copy_of_invariant` cannot be applied off the shelf to a `halfPlaneGE`-cut region
with a transverse period; it does **not** say the specialised single-step obligation is false.
What survives is the *one-sided* closure `halfPlaneGE_forward_of_dot_nonneg` below — the cut is
closed under `+h` in one direction whenever `0 ≤ dot n h` — and a propagation argument that only
ever needs that direction is untouched by §6.4's counterexamples.

§20 note: `dot_smul_right` already exists twice in the tree (`EnvBound.lean:29`,
`L1RegionBuild.lean:324`), but neither module is reachable from this file's two imports, so it is
restated privately here rather than by pulling in a new import. -/

private theorem dot_smul_right' (n : ℤ × ℤ) (g : ℤ) (v : ℤ × ℤ) : dot n (g • v) = g * dot n v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The easy direction: a half-plane is `h`-invariant when `h` runs along its boundary. -/
theorem halfPlaneGE_invariant_of_dot_eq_zero {n h : ℤ × ℤ} (h0 : dot n h = 0) (k : ℤ)
    (z : ℤ × ℤ) : z + h ∈ halfPlaneGE n k ↔ z ∈ halfPlaneGE n k := by
  show k ≤ dot n (z + h) ↔ k ≤ dot n z
  rw [dot_add, h0, add_zero]

/-- **What survives when `hinv` does not**: one-sided closure.  A half-plane is closed under
`+ h` (forward only) as soon as `0 ≤ dot n h`, with no invariance and no primitivity. -/
theorem halfPlaneGE_forward_of_dot_nonneg {n h : ℤ × ℤ} (h0 : 0 ≤ dot n h) (k : ℤ)
    {z : ℤ × ℤ} (hz : z ∈ halfPlaneGE n k) : z + h ∈ halfPlaneGE n k := by
  have hz' : k ≤ dot n z := hz
  show k ≤ dot n (z + h)
  rw [dot_add]
  omega

/-- **The obstruction.**  If some lattice vector `v` has `dot n v = 1` — i.e. `n`'s levels are
*all* of `ℤ` along `v`, which is exactly what `dot_expNormal_vl` gives the L1 cut under
`hunimod` — then no nonzero multiple `c • v` is a symmetry of `halfPlaneGE n k`.  Witnesses are
explicit: `k • v` for `c < 0`, `(k-1) • v` for `c > 0`. -/
theorem not_invariant_of_dot_eq_one {n v : ℤ × ℤ} (hv : dot n v = 1) {c : ℤ} (hc : c ≠ 0)
    (k : ℤ) : ¬ ∀ z : ℤ × ℤ, z + c • v ∈ halfPlaneGE n k ↔ z ∈ halfPlaneGE n k := by
  intro hall
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have h1 : (k • v : ℤ × ℤ) ∈ halfPlaneGE n k := by
      show k ≤ dot n (k • v)
      rw [dot_smul_right', hv]
      omega
    have h2 : k ≤ dot n (k • v + c • v) := (hall (k • v)).mpr h1
    rw [dot_add, dot_smul_right', dot_smul_right', hv] at h2
    omega
  · have h1 : ((k - 1) • v : ℤ × ℤ) + c • v ∈ halfPlaneGE n k := by
      show k ≤ dot n ((k - 1) • v + c • v)
      rw [dot_add, dot_smul_right', dot_smul_right', hv]
      omega
    have h2 : k ≤ dot n ((k - 1) • v) := (hall ((k - 1) • v)).mp h1
    rw [dot_smul_right', hv] at h2
    omega

/-- **The punchline, in the shape leaf L1 presents it.**  `hinf` (the hypothesis that makes
`c0 : c ≠ 0` free, §7) is by itself enough to rule out `hinv` on any cut half-plane whose normal
pairs to `1` with the period direction.  Nothing here mentions `wedgeFull`, `expNormal` or
`ChainDataGeom`: the two facts are incompatible at the level of `dot` alone. -/
theorem not_invariant_of_not_periodOn_smul {A : Type*} {x : Config A} {U : Set (ℤ × ℤ)}
    {n v : ℤ × ℤ} (hv : dot n v = 1) {c : ℤ}
    (hinf : ¬ Colle41.PeriodOn x U (c • v)) (k : ℤ) :
    ¬ ∀ z : ℤ × ℤ, z + c • v ∈ halfPlaneGE n k ↔ z ∈ halfPlaneGE n k :=
  not_invariant_of_dot_eq_one hv (ne_zero_of_not_periodOn_smul hinf) k

/-! ## §9  The maximal periodic index is unique

Landed at Cclaim's request: `L1Claim.exists_L1MaxBResidual_of_wedgeAt` cites this in its
docstring, and a landed file should not have to point at a `tmp/` receipt.  Moved verbatim from
`tmp/Aface_l1_skeleton.lean`.

`exists_L1MaxBResidual_of_family` quantifies its residual `∀ N, PeriodOn (F.R N) h →
¬ PeriodOn (F.R (N+1)) h → …`, while `_of_tail` takes a single `N` as an argument.  This lemma
is why the two are **equivalent** obligations and not one stronger than the other: `PeriodOn` is
antitone in its set (`PeriodOn.mono`, `Lemma41.lean:662`) and the family is monotone, so
`{n | PeriodOn (Rf n) h}` is downward closed and there is at most one `N` at which it breaks.
The `∀ N` therefore ranges over a set with at most one element — **nobody owes more than one
index.**  (I first read the `∀ N` as a strengthening and was wrong; this is the receipt.) -/

theorem maximal_index_unique {A : Type*} {x : Config A} {Rf : ℕ → Set (ℤ × ℤ)} {h : ℤ × ℤ}
    (hmono : Monotone Rf) {N M : ℕ}
    (hN : Colle41.PeriodOn x (Rf N) h) (hN1 : ¬ Colle41.PeriodOn x (Rf (N + 1)) h)
    (hM : Colle41.PeriodOn x (Rf M) h) (hM1 : ¬ Colle41.PeriodOn x (Rf (M + 1)) h) :
    N = M := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hN1 (Colle41.PeriodOn.mono (hmono (by omega : N + 1 ≤ M)) hM)
  · exact hM1 (Colle41.PeriodOn.mono (hmono (by omega : M + 1 ≤ N)) hN)

end Nivat.L1Prim

#print axioms Nivat.L1Prim.dot_perp_self
#print axioms Nivat.L1Prim.dot_perp_det
#print axioms Nivat.L1Prim.dot_self_pos
#print axioms Nivat.L1Prim.halfPlaneGE_nonempty
#print axioms Nivat.L1Prim.exists_mem_not_mem_of_det_ne_zero
#print axioms Nivat.L1Prim.not_halfPlaneGE_subset_of_det_ne_zero
#print axioms Nivat.L1Prim.not_halfPlaneGE_subset_of_det_ne_zero'
#print axioms Nivat.L1Prim.det_eq_zero_of_halfPlaneGE_subset
#print axioms Nivat.L1Prim.dot_pos_of_halfPlaneGE_subset
#print axioms Nivat.L1Prim.halfPlaneGE_two_subset_one
#print axioms Nivat.L1Prim.not_forall_exists_smul_of_halfPlaneGE_subset

#print axioms Nivat.L1Prim.periodOn_Ucol
#print axioms Nivat.L1Prim.not_periodOn_Vcol
#print axioms Nivat.L1Prim.not_forall_periodOn_of_overlap
#print axioms Nivat.L1Prim.Vcol_eq_union_shift
#print axioms Nivat.L1Prim.not_forall_periodOn_of_eq_union_shift
#print axioms Nivat.L1Prim.periodOn_RfCol
#print axioms Nivat.L1Prim.not_forall_periodOn_iUnion
#print axioms Nivat.L1Prim.periodOn_of_copy_of_invariant
#print axioms Nivat.L1Prim.not_forall_periodOn_of_determined
#print axioms Nivat.L1Prim.Ucol_not_invariant

#print axioms Nivat.L1Prim.periodOn_zero
#print axioms Nivat.L1Prim.ne_zero_of_not_periodOn_smul
#print axioms Nivat.L1Prim.exists_not_periodOn_smul

#print axioms Nivat.L1Prim.halfPlaneGE_invariant_of_dot_eq_zero
#print axioms Nivat.L1Prim.halfPlaneGE_forward_of_dot_nonneg
#print axioms Nivat.L1Prim.not_invariant_of_dot_eq_one
#print axioms Nivat.L1Prim.not_invariant_of_not_periodOn_smul

#print axioms Nivat.L1Prim.maximal_index_unique
