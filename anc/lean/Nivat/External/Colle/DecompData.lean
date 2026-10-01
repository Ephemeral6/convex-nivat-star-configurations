/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma35
import Nivat.Laurent.Basic
import Nivat.Defs.Complexity
import Nivat.External.Colle.Generating
import Nivat.External.Colle.AlphabetReduction
import Nivat.External.Colle.NewtonZonotope
import Nivat.Section8.ExternalDefs

/-!
# Decomposition data supplement for ChainData

**Source**: Collé, arXiv:1909.08195v4, line 764 (scratch/b3_colle2.txt:764).

This file adds the periodic decomposition data that the paper's construction of S_φ
requires, following the "add, don't replace" protocol. The original `ChainData` structure
takes `S : Finset (ℤ × ℤ)` as a bare parameter without recording that it is the convex hull
of the support of `φ(X) = ∏(X^{h_i} - 1)`, where the `h_i` are periods of a ℤ-minimal
decomposition with pairwise-distinct directions.

## Key constraint: `h_dir`

The field `h_dir : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0` encodes "the h_i have pairwise
distinct directions", which is what allows the paper's argument at :890/:896 to obtain a
second normal direction `ℓ' = ℓ_J` that is non-parallel to the first.

Without this field, the type system cannot guarantee that a second direction exists.

## The producer (2026-09-17)

`DecompDataZ.of_minimalCounterexample` builds a `DecompDataZ ξ` from
`IsMinimalCounterexample ξ`, so that `Case1`/`Case2` (`RegionSteps.lean:312-327`) can be stated
over `E(𝒮_φ)` as the paper does (`b3_colle2.txt:756-758`) instead of over the Lemma 2.4 set.
See the section docstring below for which field comes from where.
-/

namespace Nivat.Colle35

open Nivat Nivat.Colle

variable {α : Type*}

/-- **Collé :764, verbatim.**

"Let η = η₁ + ⋯ + η_m be a ℤ-minimal periodic decomposition (see Theorem 1.10),
h_i ∈ ℤ² a period for η_i, with 1 ≤ i ≤ m, and set φ(X) := (X^{h₁}−1)⋯(X^{h_m}−1)."

All conditions from the paper are transcribed into fields:
- `m ≥ 2` (needed for the argument)
- `η = ∑ i, eta i` (the decomposition)
- `h i ≠ 0` (periods are nonzero)
- `h i ∈ Per (eta i)` (h_i is a period of η_i)
- `det (h i) (h j) ≠ 0` for `i ≠ j` (pairwise distinct directions)
- `Sphi` is the convex hull of `supp(∏ (X^{h_i} - 1))`

**On minimality (source-checked 2026-09-17, every quote verified verbatim by the
integrator, not relayed).**  `:168` defines a ℤ-minimal periodic decomposition as one with
the smallest number of components:

> "If `m ≤ n` for every `R`-periodic decomposition `η = ϑ₁ + ⋯ + ϑ_n`, we call
> `η = η₁ + ⋯ + η_m` a `R`-minimal periodic decomposition."

`:170` is where minimality is *spent*:

> "If `η` is a non-periodic configuration and `η = η₁ + ⋯ + η_m` is a `R`-minimal periodic
> decomposition, then any two periods for `η_i` and `η_j`, with `i ≠ j`, are in distinct
> directions."

So minimality's only role is to produce `h_dir`; §3/§4 never invoke the `m ≤ n` definition
again.  What they do invoke, repeatedly and explicitly, is pairwise-distinct directions —
`:160` and `:164` (Theorem 1.10, both parts), `:424` (the hypothesis of **Lemma 3.5
itself**: "where `h₁, …, h_m ∈ ℤ²`, with `m ≥ 2`, are vectors in pairwise distinct
directions"), `:567` and `:792` (used to exclude edges parallel to a given direction).

`:424` is why this structure exists: `ChainData` transcribes Lemma 3.5 but dropped that
hypothesis, so downstream code could not reach the second edge direction `ℓ_J` at all.

We therefore record `h_dir` as a field rather than minimality itself.  That is the safe
direction: it makes the structure *harder* to construct (a producer must either take a
minimal decomposition and apply `:170`, or prove `h_dir` directly) and impossible to use
without it.  Recording minimality instead would leave `h_dir` as a proof obligation that
the type system does not force — the exact failure mode that produced this file. -/
structure DecompData [AddCommMonoid α] (η : Config α) where
  /-- Number of components in the decomposition. -/
  m : ℕ
  /-- At least 2 components (needed for the argument). -/
  hm : 2 ≤ m
  /-- The components `η_i` of the decomposition. -/
  eta : Fin m → Config α
  /-- The periods `h_i`, one for each component. -/
  h : Fin m → ℤ × ℤ
  /-- `η = ∑ i, η_i`. -/
  sum_eq : ∀ z, η z = ∑ i, eta i z
  /-- Each period is nonzero. -/
  h_ne : ∀ i, h i ≠ 0
  /-- `h_i` is a period of `η_i`. -/
  h_period : ∀ i, h i ∈ Per (eta i)
  /-- **Pairwise distinct directions**: `det(h_i, h_j) ≠ 0` for `i ≠ j`.

  This is the key constraint that allows the paper to obtain a second normal direction
  `ℓ' = ℓ_J` non-parallel to `ℓ = ℓ_I` (paper :890/:896). -/
  h_dir : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0
  /-- The zonotope `S_φ`, as a finite set. -/
  Sphi : Finset (ℤ × ℤ)
  /-- `S_φ` is the convex hull of the support of `φ(X) = ∏(X^{h_i} - 1)`. -/
  Sphi_eq : Conv Sphi = Conv (supp (∏ i : Fin m, (mono (h i) - 1 : LaurentTwo ℤ)))

/-- **ChainData with decomposition data.**

This structure extends `ChainData` with the periodic decomposition data from the paper's
setup.

**Agreement field deleted 2026-09-17.**  This structure used to carry a field asserting
`decomp.Sphi = S`, tying the `S` index of `ChainData` to `S_φ` by fiat.  That is
an obligation on every producer to prove that the `S` handed in — in the assembly, the
Lemma 2.4 generating set of `exists_preamble` — *equals* `S_φ`, which Collé never claims
(`:286-292` and `:298` define two different sets); an unprovable field makes the structure
uninhabitable.  The pairing is now expressed where it belongs, at the type: the assembly
(`ColleRegion.lean`) and `RegionSteps.exists_chainData` instantiate `ChainData`'s `S` with
`d.Sphi` for `d : DecompDataZ ξ` directly.  This structure has no consumer in the tree; it is
kept only so that nothing that mentions it by name breaks. -/
structure ChainDataWithDecomp [AddCommMonoid α] (η xper : Config α) (vl : ℤ × ℤ)
    (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) extends
    ChainData η xper vl S gen where
  /-- The periodic decomposition data. -/
  decomp : DecompData η

/-- **Forgetting bridge**: a `ChainDataWithDecomp` is a `ChainData`. -/
theorem ChainDataWithDecomp.toChainData_fst [AddCommMonoid α] {η xper : Config α}
    {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (c : ChainDataWithDecomp η xper vl S gen) :
    c.toChainData = c.1 := rfl


/-! ## The annihilator layer

`DecompData` records the decomposition and the zonotope `S_φ`, but not the fact that
`φ(X)` annihilates `η` — which is what turns `S_φ` into an `η`-generating set.  That fact
only typechecks over `ℤ` (`act` maps `Config R → Config R` for the *same* `R`), and `ℤ` is
where Collé works, so it lives in a separate extending structure rather than in
`DecompData` itself.
-/

/-- **`DecompData` over `ℤ`, with Lemma 3.5's annihilator hypothesis.**

`b3_colle2.txt:424`, verbatim: *"Let `η ∈ A^(ℤ²)` be a configuration with
`φ(X) = (X^{h₁}−1)⋯(X^{h_m}−1) ∈ ann_R(η)`"*.

`Sphi_supp` and `Sphi_conv` are the two remaining premises of
`Nivat.Colle.isGeneratingSet_of_annihilator` (`Generating.lean:65`); `Sphi_eq` supplies its
hull premise and `Sphi_nonempty` is derived, not assumed. -/
structure DecompDataZ (η : Config ℤ) extends DecompData η where
  /-- `φ(X) ∈ ann_R(η)` (`:424`). -/
  ann : act (∏ i : Fin toDecompData.m, (mono (toDecompData.h i) - 1 : LaurentTwo ℤ)) η = 0
  /-- `supp φ ⊆ S_φ`. -/
  Sphi_supp : supp (∏ i : Fin toDecompData.m,
    (mono (toDecompData.h i) - 1 : LaurentTwo ℤ)) ⊆ toDecompData.Sphi
  /-- `S_φ` is lattice-convex (it is a zonotope). -/
  Sphi_conv : LatticeConvex toDecompData.Sphi

/-- Each factor `X^{h_i} - 1` of `φ` is nonzero, because `h_i ≠ 0`. -/
theorem DecompData.factor_ne_zero [AddCommMonoid α] {η : Config α} (D : DecompData η)
    (i : Fin D.m) : (mono (D.h i) - 1 : LaurentTwo ℤ) ≠ 0 := by
  intro hz
  rw [sub_eq_zero] at hz
  have hco := congrArg (fun f : LaurentTwo ℤ => f.coeff (D.h i)) hz
  rw [← mono_zero] at hco
  simp only [coeff_mono, Finsupp.single_eq_same] at hco
  rw [Finsupp.single_apply, if_neg (Ne.symm (D.h_ne i))] at hco
  exact one_ne_zero hco

/-- `φ = ∏ (X^{h_i} - 1)` is nonzero: `LaurentTwo ℤ` has no zero divisors. -/
theorem DecompData.phi_ne_zero [AddCommMonoid α] {η : Config α} (D : DecompData η) :
    (∏ i : Fin D.m, (mono (D.h i) - 1 : LaurentTwo ℤ)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => D.factor_ne_zero i

/-- `S_φ` is nonempty — derived from `φ ≠ 0`, not assumed. -/
theorem DecompDataZ.Sphi_nonempty {η : Config ℤ} (D : DecompDataZ η) :
    D.toDecompData.Sphi.Nonempty := by
  have hsupp : (supp (∏ i : Fin D.toDecompData.m,
      (mono (D.toDecompData.h i) - 1 : LaurentTwo ℤ))).Nonempty := by
    refine Finsupp.support_nonempty_iff.mpr fun hc => ?_
    exact D.toDecompData.phi_ne_zero (AddMonoidAlgebra.coeff_eq_zero.mp hc)
  obtain ⟨z, hz⟩ := hsupp
  exact ⟨z, D.Sphi_supp hz⟩

/-- **`S_φ` is an `η`-generating set.**

This is the standing hypothesis Collé uses at `:597` (*"Since `S_φ` is an `η`-generating
set…"*) and throughout §3–§4.  Every premise of
`Nivat.Colle.isGeneratingSet_of_annihilator` is a field of `DecompDataZ`, except
nonemptiness, which is derived above. -/
theorem DecompDataZ.isGeneratingSet {η : Config ℤ} (D : DecompDataZ η) :
    IsGeneratingSet η D.toDecompData.Sphi :=
  isGeneratingSet_of_annihilator D.ann D.Sphi_nonempty D.Sphi_conv D.Sphi_supp
    D.toDecompData.Sphi_eq

/-! ## The producer: a `DecompDataZ ξ` from a minimal counterexample

`b3_colle2.txt:764`, verbatim: *"Let `η = η₁ + ⋯ + η_m` be a `ℤ`-minimal periodic
decomposition (see Theorem 1.10), `h_i ∈ ℤ²` a period for `η_i`, with `1 ≤ i ≤ m`, and set
`φ(X) := (X^{h₁}−1)⋯(X^{h_m}−1)`."*

`IsMinimalCounterexample ξ` (`Section8/ExternalDefs.lean:52`) carries exactly such a
decomposition (`HasOrderZ`), so every field of `DecompDataZ ξ` is obtained from it:

* `eta`, `h`, `sum_eq`, `h_ne`, `h_period` — the decomposition itself, one period chosen per
  component (`choose`);
* `hm : 2 ≤ m` — `m = 0` contradicts `0 < ξ z`, `m = 1` contradicts `¬ IsPeriodic ξ`;
* `h_dir` — `:170`: two components with parallel periods have a common non-zero period
  (`Nivat.Colle.exists_common_multiple_of_det_eq_zero`) and merge into one
  (`mergeAt` / `sum_mergeAt`), shortening the decomposition against minimality;
* `Sphi`, `Sphi_eq`, `Sphi_supp`, `Sphi_conv` — `Nivat.Colle.exists_latticeConvex_completion`
  applied to `supp φ`;
* `ann` — `AlphabetReduction.act_prod_eq_zero_of_mem_Per` on `ξ = ∑ i, eta i`.

`mem_Per_add`, `mergeAt` and `sum_mergeAt` restate `private` items of
`Section8/External.lean:159-221`, which cannot be imported here: that file is downstream of
`ColleRegion` (it is where `colle_region` is an axiom to be discharged). -/

/-- A common period of two configurations is a period of their sum. -/
theorem mem_Per_add {α : Type*} [Add α] {a b : Config α} {u : ℤ × ℤ}
    (ha : u ∈ Per a) (hb : u ∈ Per b) : u ∈ Per (a + b) := by
  rw [mem_Per_iff]
  funext z
  show a (z + u) + b (z + u) = a z + b z
  rw [Per.apply ha z, Per.apply hb z]

/-- **`:170`, the merging step.**  Two parallel non-zero periods have a common non-zero
multiple, so two components with parallel periods add to a periodic configuration. -/
theorem isPeriodic_add_of_det_eq_zero {α : Type*} [Add α] {a b : Config α} {u v : ℤ × ℤ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hdet : det u v = 0) (hau : u ∈ Per a) (hbv : v ∈ Per b) :
    IsPeriodic (a + b) := by
  obtain ⟨k, l, hk, hkl⟩ := exists_common_multiple_of_det_eq_zero hu hv hdet
  refine ⟨k • u, mem_Per_add (AddSubgroup.zsmul_mem _ hau k)
    (hkl ▸ AddSubgroup.zsmul_mem _ hbv l), ?_⟩
  intro h0
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact hk h1
  · exact hu h1

/-- Fold the `i`-th component of a family into the `j`-th one and delete the index `i`. -/
def mergeAt {α : Type*} [Add α] {m : ℕ} (G : Fin (m + 1) → Config α)
    (i j : Fin (m + 1)) : Fin m → Config α :=
  fun k => if i.succAbove k = j then G j + G i else G (i.succAbove k)

/-- Merging preserves the pointwise sum. -/
theorem sum_mergeAt {α : Type*} [AddCommGroup α] {m : ℕ} (G : Fin (m + 1) → Config α)
    {i j : Fin (m + 1)} (hij : j ≠ i) (z : ℤ × ℤ) :
    ∑ k : Fin m, mergeAt G i j k z = ∑ k, G k z := by
  classical
  set V : Fin (m + 1) → α := fun l => if l = j then G j z + G i z else G l z with hVdef
  have hV : ∀ l, V l = G l z + (if l = j then G i z else 0) := by
    intro l
    rw [hVdef]
    by_cases hl : l = j
    · subst hl; simp
    · simp [hl]
  have htot : ∑ l, V l = (∑ l, G l z) + G i z := by
    rw [Finset.sum_congr rfl fun l _ => hV l, Finset.sum_add_distrib]
    congr 1
    simp
  have hVi : V i = G i z := by rw [hVdef]; simp only [if_neg (Ne.symm hij)]
  have hmerge : ∀ k : Fin m, mergeAt G i j k z = V (i.succAbove k) := by
    intro k
    simp only [mergeAt, hVdef]
    by_cases hk : i.succAbove k = j <;> simp [hk]
  have hsplit := Fin.sum_univ_succAbove V i
  rw [htot, hVi] at hsplit
  rw [Finset.sum_congr rfl fun k _ => hmerge k]
  exact add_left_cancel (a := G i z) (by rw [← hsplit]; abel)

/-- **`DecompDataZ ξ` exists for every minimal counterexample** (`b3_colle2.txt:764`, with
`:170` supplying `h_dir`).  Stated as `Nonempty` because `DecompDataZ ξ` carries data;
consumers `obtain ⟨d⟩ := DecompDataZ.of_minimalCounterexample hξ`. -/
theorem DecompDataZ.of_minimalCounterexample {ξ : Config ℤ} (hξ : IsMinimalCounterexample ξ) :
    Nonempty (DecompDataZ ξ) := by
  classical
  obtain ⟨⟨-, hpos, hnp, -⟩, n, ⟨⟨f, hfper, hfsum⟩, hmin⟩, -⟩ := hξ
  choose h hhper hhne using hfper
  -- `2 ≤ m`: no components contradicts `0 < ξ 0`; one component makes `ξ` periodic.
  have hn2 : 2 ≤ n := by
    by_contra hlt
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · have h0 := hpos 0
      rw [hfsum 0, Fin.sum_univ_zero] at h0
      exact lt_irrefl _ h0
    · have hξf : ξ = f 0 := funext fun z => by rw [hfsum z, Fin.sum_univ_one]
      exact hnp (hξf ▸ ⟨h 0, hhper 0, hhne 0⟩)
  -- `:170`: parallel periods in two components merge, contradicting minimality.
  have hdir : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0 := by
    intro i j hij hdet
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hmerged : IsPeriodic (f j + f i) :=
      isPeriodic_add_of_det_eq_zero (hhne j) (hhne i)
        (by rw [det_comm, hdet, neg_zero]) (hhper j) (hhper i)
    have hDm : PeriodicDecompZ ξ m := by
      refine ⟨mergeAt f i j, fun k => ?_,
        fun z => (hfsum z).trans (sum_mergeAt f (Ne.symm hij) z).symm⟩
      simp only [mergeAt]
      by_cases hk : i.succAbove k = j
      · rw [if_pos hk]; exact hmerged
      · rw [if_neg hk]; exact ⟨h (i.succAbove k), hhper _, hhne _⟩
    exact absurd (hmin m hDm) (by omega)
  -- `φ ∈ ann_ℤ(ξ)` (`:424`).
  have hann : act (∏ i : Fin n, (mono (h i) - 1 : LaurentTwo ℤ)) ξ = 0 := by
    have hξ_eq : ξ = ∑ i : Fin n, f i := funext fun z => by rw [hfsum z, Finset.sum_apply]
    rw [hξ_eq]
    exact AlphabetReduction.act_prod_eq_zero_of_mem_Per Finset.univ h f fun i _ => hhper i
  -- `S_φ := conv(supp φ) ∩ ℤ²` (`:298`).
  obtain ⟨Sphi, hsupp, hconv, hhull⟩ :=
    exists_latticeConvex_completion (supp (∏ i : Fin n, (mono (h i) - 1 : LaurentTwo ℤ)))
  exact ⟨{ m := n, hm := hn2, eta := f, h := h, sum_eq := hfsum, h_ne := hhne,
           h_period := hhper, h_dir := hdir, Sphi := Sphi, Sphi_eq := hhull,
           ann := hann, Sphi_supp := hsupp, Sphi_conv := hconv }⟩

/-! ## `𝒮_{φ_ι} ⊆ 𝒮_φ`

⚠ **This obligation is owed by the Lean side, not by Collé.**  The paper never compares
these two sets; the comparison is forced on us because Def 3.2's envelopment hangs on
`𝒮_φ` while Claim 4.6's forcing window is `𝒮_{φ_ι}`.

The obvious route `supp φ_ι ⊆ supp φ` is **false** (multiplying by `(X^{h_{ι₀}} − 1)` can
cancel terms; supports are not monotone in factors).  The real route goes through convex
hulls, where Ostrowski gives an equality
(`Conv_supp_prod_eq_Conv_zonoF`, `NewtonZonotope.lean:181`). -/

section SubsetSphi

open Nivat.LE2 Pointwise

/-- Dropping a generator shrinks the zonotope, because every segment contains `0`. -/
theorem zonoF_erase_subset {ι : Type*} [DecidableEq ι] [Fintype ι] (h : ι → ℤ × ℤ) (i₀ : ι) :
    zonoF ((Finset.univ : Finset ι).erase i₀) h ⊆ zonoF (Finset.univ : Finset ι) h := by
  classical
  intro x hx
  have hsplit : zonoF (Finset.univ : Finset ι) h
      = ({0, h i₀} : Finset (ℤ × ℤ)) + zonoF ((Finset.univ : Finset ι).erase i₀) h := by
    rw [zonoF, zonoF, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  have hmem : (0 : ℤ × ℤ) + x
      ∈ ({0, h i₀} : Finset (ℤ × ℤ)) + zonoF ((Finset.univ : Finset ι).erase i₀) h :=
    Finset.add_mem_add (by simp) hx
  rw [hsplit]
  simpa using hmem

/-- **`Conv 𝒮_{φ_ι} ⊆ Conv 𝒮_φ`**, by Ostrowski on both sides. -/
theorem conv_subset_conv_Sphi {ξ : Config ℤ} (d : DecompDataZ ξ)
    (i₀ : Fin d.toDecompData.m) {Sι : Finset (ℤ × ℤ)}
    (hhull : Conv Sι
      = Conv (supp (∏ i ∈ (Finset.univ : Finset (Fin d.toDecompData.m)).erase i₀,
          (mono (d.toDecompData.h i) - 1 : LaurentTwo ℤ)))) :
    Conv Sι ⊆ Conv d.toDecompData.Sphi := by
  classical
  rw [hhull,
    Conv_supp_prod_eq_Conv_zonoF _ d.toDecompData.h (fun i _ => d.toDecompData.h_ne i),
    d.toDecompData.Sphi_eq,
    Conv_supp_prod_eq_Conv_zonoF _ d.toDecompData.h (fun i _ => d.toDecompData.h_ne i)]
  refine convexHull_mono (Set.image_mono ?_)
  intro x hx
  exact Finset.mem_coe.mpr (zonoF_erase_subset d.toDecompData.h i₀ (Finset.mem_coe.mp hx))

/-- **`𝒮_{φ_ι} ⊆ 𝒮_φ`.**  The hull inclusion upgrades to a set inclusion because `𝒮_φ` is
lattice-convex (`DecompDataZ.Sphi_conv`). -/
theorem subset_Sphi {ξ : Config ℤ} (d : DecompDataZ ξ) (i₀ : Fin d.toDecompData.m)
    {Sι : Finset (ℤ × ℤ)}
    (hhull : Conv Sι
      = Conv (supp (∏ i ∈ (Finset.univ : Finset (Fin d.toDecompData.m)).erase i₀,
          (mono (d.toDecompData.h i) - 1 : LaurentTwo ℤ)))) :
    Sι ⊆ d.toDecompData.Sphi :=
  fun _ hz => d.Sphi_conv _ (conv_subset_conv_Sphi d i₀ hhull (subset_Conv hz))

/-! ### `E ↑Sphi` is closed under negation of the normal

Landed from `tmp/AnfpL_Sphi_neg_symm.lean` (AnfpL lane).  Pure composition of lemmas already
in the tree: `E_segOf` / `E_zono` (`MinkowskiEdges.lean:204,292`),
`Conv_supp_prod_eq_Conv_zonoF` (`NewtonZonotope.lean:181`), `E_congr_of_Conv_eq`
(`ConvTransport.lean:233`).  No new geometry, no new field. -/

/-- `E (segOf v)` is symmetric under `n ↦ -n`: both `Prim` and `dot · v = 0` are. -/
theorem segOf_negSymm (v : ℤ × ℤ) (hv : v ≠ 0) (n : ℤ × ℤ) :
    n ∈ E (segOf v) ↔ -n ∈ E (segOf v) := by
  rw [E_segOf hv]
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨hp.neg, ?_⟩
    show dot (-n) v = 0
    simp only [dot, Prod.fst_neg, Prod.snd_neg]
    have : dot n v = 0 := hd
    simp only [dot] at this
    linarith
  · rintro ⟨hp, hd⟩
    have hp' : Prim n := by simpa using hp.neg
    refine ⟨hp', ?_⟩
    have hd' : dot (-n) v = 0 := hd
    simp only [dot, Prod.fst_neg, Prod.snd_neg] at hd'
    show dot n v = 0
    simp only [dot]
    linarith

/-- Hence `E` of a zonotope is symmetric under negation: a union of symmetric sets. -/
theorem zono_negSymm {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℤ × ℤ)
    (hne : ∀ i ∈ s, h i ≠ 0) (n : ℤ × ℤ) :
    n ∈ E (∑ i ∈ s, segOf (h i)) ↔ -n ∈ E (∑ i ∈ s, segOf (h i)) := by
  rw [E_zono]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi, hmem⟩; exact ⟨i, hi, (segOf_negSymm (h i) (hne i hi) n).mp hmem⟩
  · rintro ⟨i, hi, hmem⟩; exact ⟨i, hi, (segOf_negSymm (h i) (hne i hi) n).mpr hmem⟩

/-- **`E ↑d.Sphi` is closed under negation of the normal**, for *any* `DecompData`,
unconditionally — only the field `h_ne` is used.

Consequence for the `nJ` obligation of `exists_chainData`: a construction only ever has to
produce `nJ ∈ E ↑d.Sphi`; the antipodal membership `-nJ ∈ E ↑d.Sphi` follows for free. -/
theorem Sphi_negSymm {α : Type*} [AddCommMonoid α] {η : Config α} (d : DecompData η)
    (n : ℤ × ℤ) :
    n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) ↔ -n ∈ E (↑d.Sphi : Set (ℤ × ℤ)) := by
  have hconv : Conv d.Sphi = Conv (zonoF Finset.univ d.h) := by
    rw [d.Sphi_eq, Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun i _ => d.h_ne i)]
  have hE : E (↑d.Sphi : Set (ℤ × ℤ)) = E (↑(zonoF Finset.univ d.h) : Set (ℤ × ℤ)) :=
    E_congr_of_Conv_eq hconv
  rw [hE, coe_zonoF]
  exact zono_negSymm Finset.univ d.h (fun i _ => d.h_ne i) n

end SubsetSphi

end Nivat.Colle35
