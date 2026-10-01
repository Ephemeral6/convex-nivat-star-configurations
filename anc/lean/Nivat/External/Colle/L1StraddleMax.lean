/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Assemble
import Nivat.External.Colle.L3Cover

/-!
# `MaxBResidual.straddle` at the maximal index: what it says, and Collé's route to it

Lane Cconv's file (exclusive, 2026-09-19).  Target: the `straddle` field of
`Nivat.ColleReg.L1Data.MaxBResidual` (`L1Assemble.lean:962`), conjunct 15 of leaf L1 asserted at
the maximal indices only —

    straddle : ∀ N, PeriodOn (T e ξ) (F.R N) (c • u) → ¬ PeriodOn (T e ξ) (F.R (N+1)) (c • u) →
      Straddle (T e ξ) (F.R N) (F.R (N+1)) S₁ (derivedQ ε u' S₁) u u' c τ

with `Nivat.L1Region.Straddle` (`L1Region.lean:412`) the shape of `L1Data.hstraddle`
(`L1Data.lean:132`) at one pair of levels.

## §1  At a maximal index, `Straddle` is a negation

`Straddle x Rlo Rhi …` has `PeriodOn x Rlo (c•u)` among its *premises* and `PeriodOn x Rhi (c•u)`
as its *conclusion*.  At a maximal index the premise is given and the conclusion is false, so the
implication collapses: `straddle_iff_of_max` proves that there `Straddle` is **equivalent** to

    ∀ g ∈ S₁, g ∉ Q → ∀ t₀ ≥ τ, ∃ t ≥ t₀, x (t•u' + g + c•u) ≠ x (t•u' + g)

— *no edge point of the window is eventually `c•u`-periodic along its `u'`-ray*.  That is exactly
the statement `Nivat.L1Straddle.not_eventually_period_of_straddle` (`L1Straddle.lean:252`)
extracts from conjuncts 10/13/15, and it is the only thing the on-chain consumer
`case1_claim47_semiAmbiguous` (`RegionSteps.lean`) ever does with conjunct 15.  So what leaf L1
owes under the name `straddle` is this negation; the `PeriodOn … Rhi` conclusion is a device for
proving it by contradiction, which is how Collé does it (`b3_colle2.txt:826-852`).

## §2  Collé's proof, Figure 11(B), as a reduction

`b3_colle2.txt:848-852`: "*by using that `𝒮_φ` is `η`-generating, we get that
`(T^u η)|𝓡^{N+1}_I = (T^h(T^u η))|𝓡^{N+1}_I` (see Figure 11(B)), which contradicts the maximality
of `N`*".  Figure 11(B): "*the knowledge of a configuration on
`𝓡^N_I ∪ {g + t v_ℓ' : t ≥ t₀}` determines uniquely such a configuration on `𝓡^{N+1}_I`*".

That "determines uniquely" is `Nivat.MaxEnv.genClosure` (`MaximalEnveloped.lean:694`), and the
propagation of agreement along it is `Nivat.L3Cover.agree_on_genClosure_of_generatesAt`
(`L3Cover.lean:79`).  `straddle_of_cover` below is therefore one application of that lemma: given
a generating point `a` of the window `𝒮_φ` and the **cover**

    overlap Rhi (c•u) ⊆ genClosure 𝒮_φ a (overlap Rlo (c•u) ∪ ray g u' t₀)

(`overlap R h := {z ∈ R | z + h ∈ R}` is the part of `R` that `PeriodOn` actually constrains,
`ray g u' t₀ := {t•u' + g | t ≥ t₀}` the edge point's forward ray), `Straddle` follows.  Note the
window in the cover is `𝒮_φ`, Collé's `Ŝ_φ` of Figure 11(B), **not** `𝒯 = S₁` — the two moves of
Claim 4.7 use different windows (`ray_period_of_window_period`, `Claim47Core.lean:525`, uses `𝒯`
for Figure 11(A)).

## §3  Wiring into `MaxBResidual`

`MaxBResidual.ofTailCover` is `MaxBResidual.ofTail` (`L1Assemble.lean:2090`) with its `straddle`
argument replaced by the cover; `MaxBResidual.not_eventually` reads the field back in the §1
shape.  Both go through the real structure — no hand transcription of the target type appears
in this file, so a drift in `MaxBResidual.straddle` or in `Straddle` is a compile error here,
not a lookalike (the failure mode of `RunSide.ExistsCase2RunStatement`).

## What is **not** proved here

The cover.  It is the geometric content of Figure 11(B) and depends on the shape of `F`
(which lattice line `F.R (N+1) ∖ F.R N` is, and that the edge ray lies on it); `F` is abstract
in `MaxBResidual` and is produced by lane L1B (`L1RegionBuild.lean`, `chainFull`).  No lemma in
this file has a hypothesis of the form `IsMinimalCounterexample ξ → _`.  Reading, not kernel
fact (§15): with `F := chainFull …` the difference `F.R (N+1) ∖ F.R N` is a single `u'`-line
(`expLevel` descends by one), so the cover is a row sweep along that line from the ray backwards.
(2026-09-19 correction: an earlier version of this paragraph cited an L3 lemma
`row_sweep_of_run`; no such declaration exists in `Nivat/` (L3band, grep-measured).  The
`genClosure`-inclusion shape is `Nivat.L3Cover.subset_genClosure_of_window_of_covers`
(`L3Cover.lean:198`) / `Nivat.MaxEnv.subset_genClosure_of_rank` (`MaximalEnveloped.lean:721`);
the cover itself is now proved on `chainFull` in `L1StraddleWedge.lean`, `cover_line`.)
-/

set_option autoImplicit false

namespace Nivat.L1StraddleMax

open Nivat Nivat.Colle Nivat.Colle41 Nivat.MaxEnv Nivat.L1Region

variable {x : Config ℤ} {Rlo Rhi : Set (ℤ × ℤ)} {S₁ Q : Finset (ℤ × ℤ)} {u u' : ℤ × ℤ}
  {c τ : ℤ}

/-! ## §1  `Straddle` at a maximal index is a negation -/

/-- **At a maximal index, `Straddle` is exactly "no edge ray is eventually periodic".**

`hlo` is the given periodicity at `N`, `hhi` its failure at `N + 1` — the two outputs of
`Nivat.L1Region.exists_greatest_periodOn` (`L1Region.lean:102`).  Under them the third premise
of `Straddle` is discharged and its conclusion is refuted, leaving the fourth premise negated.
This is the content `MaxBResidual.straddle` actually carries. -/
theorem straddle_iff_of_max (hlo : PeriodOn x Rlo (c • u)) (hhi : ¬ PeriodOn x Rhi (c • u)) :
    Straddle x Rlo Rhi S₁ Q u u' c τ ↔
      ∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ →
        ∃ t : ℤ, t₀ ≤ t ∧ x (t • u' + g + c • u) ≠ x (t • u' + g) := by
  constructor
  · intro h g hg hgQ t₀ ht₀
    by_contra hcon
    push Not at hcon
    exact hhi (h g hg hgQ t₀ ht₀ hlo hcon)
  · intro h g hg hgQ t₀ ht₀ _ hray
    obtain ⟨t, ht, hne⟩ := h g hg hgQ t₀ ht₀
    exact absurd (hray t ht) hne

/-! ## §2  Figure 11(B): `Straddle` from a `genClosure` cover -/

/-- The part of `R` that `PeriodOn x R h` constrains: `z` with both `z` and `z + h` in `R`
(`Lemma41.lean:659`, an overlap-only condition). -/
def overlap (R : Set (ℤ × ℤ)) (h : ℤ × ℤ) : Set (ℤ × ℤ) := {z | z ∈ R ∧ z + h ∈ R}

/-- The forward `u'`-ray through `g` from parameter `t₀` on — the set on which `Straddle`'s
fourth premise gives agreement (`b3_colle2.txt:846`, `{g + t v_ℓ' : t ≥ t₀}`). -/
def ray (g u' : ℤ × ℤ) (t₀ : ℤ) : Set (ℤ × ℤ) := {z | ∃ t : ℤ, t₀ ≤ t ∧ z = t • u' + g}

theorem mem_overlap {R : Set (ℤ × ℤ)} {h z : ℤ × ℤ} :
    z ∈ overlap R h ↔ z ∈ R ∧ z + h ∈ R := Iff.rfl

theorem mem_ray {g u' : ℤ × ℤ} {t₀ : ℤ} {z : ℤ × ℤ} :
    z ∈ ray g u' t₀ ↔ ∃ t : ℤ, t₀ ≤ t ∧ z = t • u' + g := Iff.rfl

/-- **`Straddle` from a `genClosure` cover** (Collé, Figure 11(B), `b3_colle2.txt:848-856`).

`x` agrees with `T (c•u) x` on `overlap Rlo (c•u)` (the third premise of `Straddle`) and on the
ray (the fourth); `agree_on_genClosure_of_generatesAt` propagates the agreement to the
`genClosure`, and `hcover` says that reaches every point `PeriodOn x Rhi (c•u)` asks about.

`hgen` is `GeneratesAt ξ 𝒮_φ a` for Collé's `𝒮_φ` and one of its generating vertices; the
window is translated freely inside `genClosure`, which is the "`Ŝ_φ` a translation of `𝒮_φ`"
of Figure 11(B).  `hcover` is the one hypothesis with content; see the module docstring. -/
theorem straddle_of_cover {ξ : Config ℤ} (hx : x ∈ orbitClosure ξ)
    {Sφ : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt ξ Sφ a)
    (hcover : ∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ →
      overlap Rhi (c • u) ⊆ genClosure Sφ a (overlap Rlo (c • u) ∪ ray g u' t₀)) :
    Straddle x Rlo Rhi S₁ Q u u' c τ := by
  intro g hg hgQ t₀ ht₀ hlo hray
  have hD : ∀ z ∈ overlap Rlo (c • u) ∪ ray g u' t₀, x z = T (c • u) x z := by
    rintro z (⟨hz, hz'⟩ | ⟨t, ht, rfl⟩)
    · exact (hlo z hz hz').symm
    · exact (hray t ht).symm
  intro z hz hz'
  have h := Nivat.L3Cover.agree_on_genClosure_of_generatesAt hx
    (T_mem_of_mem_orbitClosure hx (c • u)) hgen hD z (hcover g hg hgQ t₀ ht₀ ⟨hz, hz'⟩)
  exact h.symm

/-- The cover only ever has to be checked at maximal indices: `MaxBResidual.straddle`'s
quantifier shape, from a cover with the same guards. -/
theorem straddle_all_of_cover {ξ : Config ℤ} {e : ℤ × ℤ}
    (F : RegionFamily (T e ξ) u u' c)
    {Sφ : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt ξ Sφ a)
    (hcover : ∀ N : ℕ, PeriodOn (T e ξ) (F.R N) (c • u) →
      ¬ PeriodOn (T e ξ) (F.R (N + 1)) (c • u) →
      ∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ →
        overlap (F.R (N + 1)) (c • u) ⊆
          genClosure Sφ a (overlap (F.R N) (c • u) ∪ ray g u' t₀)) :
    ∀ N : ℕ, PeriodOn (T e ξ) (F.R N) (c • u) → ¬ PeriodOn (T e ξ) (F.R (N + 1)) (c • u) →
      Straddle (T e ξ) (F.R N) (F.R (N + 1)) S₁ Q u u' c τ :=
  fun N hN hN1 => straddle_of_cover (T_mem_orbitClosure ξ e) hgen (hcover N hN hN1)

end Nivat.L1StraddleMax

/-! ## §3  Wiring into `MaxBResidual`, both directions -/

namespace Nivat.ColleReg.L1Data

open Nivat Nivat.Colle Nivat.Colle41 Nivat.MaxEnv Nivat.L1StraddleMax

/-- **`MaxBResidual` on the tail, with the straddle replaced by Figure 11(B)'s cover.**
`MaxBResidual.ofTail` (`L1Assemble.lean:2090`) with `straddle := straddle_of_cover …`.  This is
the producer-side guard: the output of §2 is consumed by the real structure. -/
theorem MaxBResidual.ofTailCover {ξ : Config ℤ} {e : ℤ × ℤ} (ε : Bool) {u u' : ℤ × ℤ}
    {c τ : ℤ} {S₁ : Finset (ℤ × ℤ)} (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c) (N : ℕ)
    (hN : PeriodOn (T e ξ) (F.R N) (c • u))
    (hN1 : ¬ PeriodOn (T e ξ) (F.R (N + 1)) (c • u))
    (det' : det u u' ≠ 0) (prim : Primitive u') (c0 : c ≠ 0)
    (line : ∀ z ∈ derivedQ ε u' S₁, τ • u' + z ∈ F.R N ∧ τ • u' + z + c • u ∈ F.R N)
    (base : (maxB (derivedQ ε u' S₁) u' ((topFace ε u' S₁).card - 1)).Nonempty ∧
      ∃ b, ∀ z ∈ S₁, b + z ∈ F.R N)
    {Sφ : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt ξ Sφ a)
    (hcover : ∀ g ∈ S₁, g ∉ derivedQ ε u' S₁ → ∀ t₀ : ℤ, τ ≤ t₀ →
      overlap (F.R (N + 1)) (c • u) ⊆
        genClosure Sφ a (overlap (F.R N) (c • u) ∪ ray g u' t₀)) :
    MaxBResidual ε u u' c τ S₁ (F.tail N hN) :=
  MaxBResidual.ofTail ε F N hN hN1 det' prim c0 line base
    (straddle_of_cover (T_mem_orbitClosure ξ e) hgen hcover)

/-- **What the `straddle` field says, read off the real structure.**  At every maximal index, no
edge point of `S₁` is eventually `c•u`-periodic along its `u'`-ray.  Consumer-side guard: this
is `straddle_iff_of_max` applied to `H.straddle`, so it tracks the field's actual type. -/
theorem MaxBResidual.not_eventually {ξ : Config ℤ} {e : ℤ × ℤ} {ε : Bool} {u u' : ℤ × ℤ}
    {c τ : ℤ} {S₁ : Finset (ℤ × ℤ)} {F : Nivat.L1Region.RegionFamily (T e ξ) u u' c}
    (H : MaxBResidual ε u u' c τ S₁ F) (N : ℕ)
    (hN : PeriodOn (T e ξ) (F.R N) (c • u))
    (hN1 : ¬ PeriodOn (T e ξ) (F.R (N + 1)) (c • u)) :
    ∀ g ∈ S₁, g ∉ derivedQ ε u' S₁ → ∀ t₀ : ℤ, τ ≤ t₀ →
      ∃ t : ℤ, t₀ ≤ t ∧ T e ξ (t • u' + g + c • u) ≠ T e ξ (t • u' + g) :=
  (straddle_iff_of_max hN hN1).mp (H.straddle N hN hN1)

end Nivat.ColleReg.L1Data

section Receipts
/-! Standing `#print axioms` receipts.  Deletable as a block. -/

#print axioms Nivat.L1StraddleMax.straddle_iff_of_max
#print axioms Nivat.L1StraddleMax.straddle_of_cover
#print axioms Nivat.L1StraddleMax.straddle_all_of_cover
#print axioms Nivat.ColleReg.L1Data.MaxBResidual.ofTailCover
#print axioms Nivat.ColleReg.L1Data.MaxBResidual.not_eventually
#check @Nivat.ColleReg.L1Data.MaxBResidual.ofTailCover

end Receipts
