/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.KS.Nullstellensatz
import Nivat.External.KS.Lemma3
import Nivat.External.KS.Lemma4

/-!
# Kari–Szabados, Theorem 3.1: synthesis

Assembly of Theorem 3.1 of J. Kari and M. Szabados, *An algebraic geometric approach to Nivat's
conjecture* (arXiv:1605.05929v1; Inform. and Comput. **271** (2020), 104481) out of the three
pieces already formalised in this repository, specialised to `d = 2`:

* `Nivat.External.KS.Lemma3` (namespace `Nivat.KS3`) — source Lemma 3,
* `Nivat.External.KS.Lemma4` (namespace `Nivat.KS4`) — source Lemma 4,
* `Nivat.External.KS.Nullstellensatz` (namespace `Nivat.KS`) — Hilbert's Nullstellensatz for
  `ℂ[X₁^±, X₂^±]`.

## The source, verbatim

Downloaded from `https://ar5iv.labs.arxiv.org/html/1605.05929` on 2026-09-13 and read as plain
text with LaTeX alt-text (`scratch/a4_ks.txt`):

> **Theorem 3.1.**  Let `c` be a finitary integral configuration and `f = ∑ a_v X^v` a
> non-trivial integral polynomial annihilator.  Let `r` be the integer from 3 and
> `v₀ ∈ supp(f)` arbitrary.  Then the Laurent polynomial
>
>     ∏_{v ∈ supp(f), v ≠ v₀} (X^{rv} − X^{rv₀})
>
> annihilates the configuration.
>
> *Proof.*  Denote `g(X)` the polynomial in the statement.  By 4, `x₁ ⋯ x_d · g(X)` vanishes on
> all common roots of `Ann(c)`, therefore by Hilbert's nullstellensatz
> `x₁ ⋯ x_d · g(X) ∈ √(Ann(c))`.  There exists an integer `m` such that
> `x₁^m ⋯ x_d^m · g^m(X) ∈ Ann(c)`.  Then also `g^m(X)` is an annihilator and the proof is
> finished by 6. ∎

and, for the record, the two lemmas the last sentence appeals to:

> **Lemma 5.**  Let `c ∈ ℂ[[x^{±1}]]` be a finitary one-dimensional configuration annihilated by
> `f^m` for a non-trivial polynomial `f` and `m ∈ ℕ`.  Then it is also annihilated by `f`.
>
> **Lemma 6.**  Let `c` be a finitary configuration and `f₁, …, f_k` line Laurent polynomials
> such that `f₁^{m₁} ⋯ f_k^{m_k}` annihilates `c`.  Then also `f₁ ⋯ f_k` annihilates it.

and the consumer:

> **Corollary 1.**  Let `c` be a finitary integral configuration with a non-trivial annihilator.
> Then there exist vectors `v₁, …, v_m ∈ ℤ^d` in pairwise distinct directions such that the
> Laurent polynomial `(X^{v₁} − 1) ⋯ (X^{v_m} − 1)` annihilates `c`.
>
> *Proof.*  By 2, `c` has an integral annihilating polynomial, and therefore also an annihilating
> polynomial as in Theorem 3.1.  Divide it by `X^{(|supp(f)|−1) r v₀}` to obtain an annihilator
> of the form `∏ (X^{uᵢ} − 1)`.  To finish the proof observe that `(X^{au} − 1)(X^{bu} − 1)`
> divides `(X^{abu} − 1)²`, and therefore any two factors `(X^{au} − 1)(X^{bu} − 1)` can be by 6
> replaced by a single factor `(X^{abu} − 1)`. ∎

## What is proved here, and what is deliberately *not*

The **last step of the source's proof — Lemma 6 — is not formalised and is not used.**  What is
proved is everything up to and including the Nullstellensatz application, i.e.

* `Nivat.KS31.exists_pow_bigProd_ann` — *some positive power* of
  `g = ∏_{v ∈ supp(f), v ≠ v₀} (X^{rv} − X^{rv₀})` annihilates `ξ`.

This is strictly weaker than source Theorem 3.1, which asserts that `g` itself annihilates.  The
missing implication `g^m ∈ Ann(c) ⟹ g ∈ Ann(c)` is exactly source Lemmas 5/6.

**Why this is nonetheless enough for the downstream consumer.**  The only consumer of
Theorem 3.1 in this development is Corollary 1, in the shape
`Nivat.KSC.exists_prodList_ann`, which only asks for *some* annihilating product of difference
polynomials `∏ᵢ (X^{uᵢ} − 1)` with `uᵢ ≠ 0`, with no bound on the number of factors and no
condition on their directions.  Dividing out monomials turns `g^m` into
`∏ᵢ (X^{uᵢ} − 1)^m`, which *is* such a product (with each factor repeated `m` times).  The
repetitions are then removed downstream by `Nivat.KSC.exists_pairwise_of_prodList`, whose engine
`Nivat.KSC.per_of_bounded` merges two parallel factors `(X^{au} − 1)(X^{bu} − 1)` into one — and
a repeated factor is a fortiori a parallel pair.  So the work source Lemma 6 does in the source's
own proof of Corollary 1 ("any two factors … can be by 6 replaced by a single factor") is done in
this development by `per_of_bounded`, and Lemma 6 is not needed a second time inside
Theorem 3.1.  See `Nivat.KS31.exists_prodList_ann` below, which is the full conclusion of
`Nivat.KSC.exists_prodList_ann`.

## The three interface bridges

The three imported files do not share conventions; the reconciliations are all proved here, none
is assumed.

1. **Two `scaleExp`s.**  `Nivat.KS3.scaleExp n` is `Finsupp.mapDomain (n • ·)` on exponents
   (`nsmul` on `ℤ × ℤ`), while `Nivat.KS4.scaleExp n` is
   `Finsupp.mapDomain (Nivat.KS4.scalePt n)` with `scalePt n v = ((n : ℤ) * v.1, (n : ℤ) * v.2)`.
   Reconciled by `Nivat.KS31.ks3_scaleExp_eq_ks4` (**proved**, for an arbitrary commutative
   coefficient ring).
2. **Two evaluations.**  `Nivat.KS.evalHom Z : ℂ[X₁^±, X₂^±] →ₐ[ℂ] ℂ` for `Z : ℂˣ × ℂˣ` versus
   `Nivat.KS4.eval φ W : R[X₁^±, X₂^±] → ℂ` for `W : ℂ × ℂ` and `φ : R →+* ℂ`.  Reconciled by
   `Nivat.KS31.eval_eq_evalHom` (**proved**): for `R = ℤ`, `φ = Int.castRingHom ℂ`,
   `W = ((Z.1 : ℂ), (Z.2 : ℂ))`, one has `KS4.eval φ W g = KS.evalHom Z (cx g)` where `cx` is
   coefficientwise complexification.
3. **Integral versus complex configurations.**  The Nullstellensatz file works with
   `Config ℂ`, Lemmas 3/4 with `Config ℤ`.  Reconciled by `Nivat.KS31.act_cx_eq_zero_iff`
   (**proved, an iff, both directions**): for integral `h` and `ξ`,
   `act (cx h) (cxConfig ξ) = 0 ↔ act h ξ = 0`, because
   `act (cx h) (cxConfig ξ) z = ((act h ξ z : ℤ) : ℂ)` and `Int.cast` is injective.

   Note the scope: this is the statement about *integral* `h` only, in both directions, and that
   is all the argument uses.  The genuinely delicate statement — that a *complex* annihilator of
   `cxConfig ξ` forces an integral one, i.e. source Lemma 2 — is **not** needed and **not**
   proved here: the hypothesis of `Nivat.KSC.exists_prodList_ann` already supplies an integral
   annihilator, and the ℂ-side is only ever used as a target (`Ann_ℤ(ξ) ⊆ Ann_ℂ(cxConfig ξ)`,
   the easy inclusion, is what feeds Lemma 4's `hroot`; the reverse inclusion is used only for
   the *conclusion* `act (cx (g^m)) (cxConfig ξ) = 0 → act (g^m) ξ = 0`, which is the easy
   pointwise cast computation above, not Lemma 2).

## What is assumed

Nothing beyond the imported, `sorry`-free files `Nivat.External.KS.Lemma3`,
`Nivat.External.KS.Lemma4`, `Nivat.External.KS.Nullstellensatz` and `Nivat.Laurent.Basic`.  There
are no `axiom`s, no `sorry`s, and no hypotheses in the main results beyond those of the source:
`(Set.range ξ).Finite` ("finitary"), and the existence of a non-zero integral annihilator.

Source Lemma 2 is **not** used (and not available): the ℂ-to-ℤ passage it performs is avoided as
explained above.  Source Lemmas 5 and 6 are **not** used.

## Non-vacuity checks performed

* The hypotheses are satisfiable, so the statement is not vacuous: `ξ = 0` is finitary and `f = 1`
  is a non-zero annihilator (conclusion: `L = []`), and, less degenerately, any finitary `ξ` with
  a period `u ≠ 0` has the non-zero annihilator `X^u − 1` (conclusion: `L = [u]`, by
  `Nivat.act_mono_sub_one_eq_zero_iff`).
* The conclusion is not trivially true: the hypothesis `∃ f ≠ 0, act f ξ = 0` is a real
  restriction on a finitary `ξ` — it is the hypothesis `Nivat.HasNonzeroAnn ξ` of source
  Theorem 8.4(b), which source Lemma 1 derives from low complexity and which fails for
  high-complexity finitary configurations.  (No Lean witness of failure is produced here; this
  remark is not relied on by anything.)  And even the degenerate output `L = []` is not a
  vacuous conclusion: `prodList [] = 1` and `act 1 ξ = ξ`, so `L = []` asserts `ξ = 0`.
* `r = 0` cannot occur: `Nivat.KS3.exists_scaling_ann` delivers `0 < r`.  This is what makes
  `KS4.scalePt r (v − v₀) ≠ 0` for `v ≠ v₀` (`Nivat.KS31.scalePt_ne_zero`), i.e. what makes the
  produced list consist of non-zero vectors.
* `m = 0` cannot occur: `Nivat.KS.exists_pow_mem_annIdeal` delivers `0 < m`.  Had `m = 0` been
  allowed, `g^0 = 1` and the conclusion would degenerate to `ξ = 0`; the proof below does not
  need `0 < m` (with `m = 0` the produced list is `[]` and the conclusion `act 1 ξ = 0` is
  exactly what `g^0 ∈ Ann` says), but `0 < m` is available and is passed on.
* `|supp f| = 1` is *not* a special case and is not special-cased.  Then
  `(supp f).erase v₀ = ∅`, `g = 1`, and `Nivat.KS4.prod_eq_zero_of_common_root` asserts that the
  empty product `1` is `0` at every common root of `Ann(ξ)` — i.e. it asserts that there are no
  common roots.  The Nullstellensatz then gives `1 ∈ Ann(cxConfig ξ)`, i.e. `ξ = 0`, and the
  produced list is `[]` with `act (prodList []) ξ = act 1 ξ = ξ = 0`.  Consistent.
* `f = 0` is excluded by hypothesis, and is genuinely needed: `supp f` must be non-empty to
  supply `v₀`.

## Status

**Complete; no `sorry`.**  Everything lives in the namespace `Nivat.KS31`.
-/

namespace Nivat.KS31

open Finset

/-! ### Bridge 1: the two `scaleExp` conventions agree -/

/-- `(n : ℕ) • v = KS4.scalePt n v` on `ℤ × ℤ`. -/
theorem nsmul_eq_scalePt (n : ℕ) (v : ℤ × ℤ) : n • v = KS4.scalePt n v := by
  refine Prod.ext ?_ ?_
  · rw [Prod.smul_fst]
    exact nsmul_eq_mul n v.1
  · rw [Prod.smul_snd]
    exact nsmul_eq_mul n v.2

/-- **Bridge 1.**  The `X ↦ X^n` substitution of `Nivat.External.KS.Lemma3` (`nsmul` on
exponents) and that of `Nivat.External.KS.Lemma4` (`KS4.scalePt`) are the same map. -/
theorem ks3_scaleExp_eq_ks4 {R : Type*} [CommRing R] (n : ℕ) (f : LaurentTwo R) :
    KS3.scaleExp n f = KS4.scaleExp n f := by
  have hfun : (fun v : ℤ × ℤ => n • v) = KS4.scalePt n := funext (nsmul_eq_scalePt n)
  apply AddMonoidAlgebra.coeff_injective
  rw [KS3.coeff_scaleExp, KS4.scaleExp, AddMonoidAlgebra.coeff_ofCoeff, hfun]

/-! ### Bridge 3: complexification of integral data -/

/-- Coefficientwise complexification `ℤ[X₁^±, X₂^±] → ℂ[X₁^±, X₂^±]`. -/
noncomputable def cx : LaurentTwo ℤ →+* LaurentTwo ℂ :=
  AddMonoidAlgebra.mapRingHom (ℤ × ℤ) (Int.castRingHom ℂ)

/-- The complexification of an integral configuration. -/
def cxConfig (ξ : Config ℤ) : Config ℂ := fun z => (ξ z : ℂ)

@[simp] theorem cxConfig_apply (ξ : Config ℤ) (z : ℤ × ℤ) : cxConfig ξ z = (ξ z : ℂ) := rfl

@[simp] theorem coeff_cx (f : LaurentTwo ℤ) (u : ℤ × ℤ) :
    (cx f).coeff u = ((f.coeff u : ℤ) : ℂ) := by
  simp [cx]

@[simp] theorem cx_mono (u : ℤ × ℤ) : cx (mono u) = (mono u : LaurentTwo ℂ) := by
  rw [cx, mono, AddMonoidAlgebra.mapRingHom_single]
  simp [mono]

theorem support_cx (f : LaurentTwo ℤ) : (cx f).coeff.support = f.coeff.support := by
  ext u
  simp only [Finsupp.mem_support_iff, coeff_cx, ne_eq, Int.cast_eq_zero]

/-- The pointwise computation behind bridge 3. -/
theorem act_cx (f : LaurentTwo ℤ) (ξ : Config ℤ) (z : ℤ × ℤ) :
    act (cx f) (cxConfig ξ) z = ((act f ξ z : ℤ) : ℂ) := by
  classical
  rw [act_apply, act_apply, Finsupp.sum, Finsupp.sum, support_cx, Int.cast_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [coeff_cx, cxConfig_apply, Int.cast_mul]

/-- **Bridge 3.**  For *integral* `h` and `ξ`, `h` annihilates `ξ` over `ℤ` if and only if its
complexification annihilates the complexified configuration.  Both directions are the same
pointwise cast computation; injectivity of `Int.cast : ℤ → ℂ` gives the non-trivial one. -/
theorem act_cx_eq_zero_iff (h : LaurentTwo ℤ) (ξ : Config ℤ) :
    act (cx h) (cxConfig ξ) = 0 ↔ act h ξ = 0 := by
  constructor
  · intro hz
    funext z
    have h2 := congrFun hz z
    rw [act_cx] at h2
    simp only [Pi.zero_apply] at h2 ⊢
    exact_mod_cast h2
  · intro hz
    funext z
    rw [act_cx, hz]
    simp

/-! ### Bridge 2: the two evaluations agree -/

/-- The point of `ℂ × ℂ` underlying a point of the torus, in the shape Lemma 4 wants. -/
noncomputable def toPt (Z : ℂˣ × ℂˣ) : ℂ × ℂ := ((Z.1 : ℂ), (Z.2 : ℂ))

@[simp] theorem toPt_fst (Z : ℂˣ × ℂˣ) : (toPt Z).1 = (Z.1 : ℂ) := rfl
@[simp] theorem toPt_snd (Z : ℂˣ × ℂˣ) : (toPt Z).2 = (Z.2 : ℂ) := rfl

theorem monoEval_toPt (Z : ℂˣ × ℂˣ) (v : ℤ × ℤ) :
    KS4.monoEval (toPt Z) v = (Z.1 : ℂ) ^ v.1 * (Z.2 : ℂ) ^ v.2 := rfl

/-- `Nivat.KS.evalHom` written as a sum over the support. -/
theorem evalHom_eq_finsuppSum (Z : ℂˣ × ℂˣ) (h : LaurentTwo ℂ) :
    KS.evalHom Z h = h.coeff.sum fun v c => c * ((Z.1 : ℂ) ^ v.1 * (Z.2 : ℂ) ^ v.2) := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single h]
  rw [map_finsuppSum]
  exact Finsupp.sum_congr fun v _ => KS.evalHom_single Z v _

/-- **Bridge 2.**  Lemma 4's evaluation of an *integral* Laurent polynomial along
`Int.castRingHom ℂ` at the point `toPt Z` agrees with the Nullstellensatz file's evaluation of
its complexification at `Z`. -/
theorem eval_eq_evalHom (Z : ℂˣ × ℂˣ) (g : LaurentTwo ℤ) :
    KS4.eval (Int.castRingHom ℂ) (toPt Z) g = KS.evalHom Z (cx g) := by
  classical
  rw [evalHom_eq_finsuppSum, KS4.eval, Finsupp.sum, Finsupp.sum, support_cx]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [coeff_cx, monoEval_toPt]
  simp

/-! ### Elementary facts about `KS4.scalePt` and monomials -/

theorem scalePt_sub (n : ℕ) (v w : ℤ × ℤ) :
    KS4.scalePt n v - KS4.scalePt n w = KS4.scalePt n (v - w) := by
  refine Prod.ext ?_ ?_ <;>
    simp only [KS4.scalePt, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem scalePt_ne_zero {n : ℕ} (hn : n ≠ 0) {w : ℤ × ℤ} (hw : w ≠ 0) :
    KS4.scalePt n w ≠ 0 := by
  intro hcon
  refine hw (KS4.scalePt_injective hn ?_)
  rw [hcon]
  refine Prod.ext ?_ ?_ <;> simp [KS4.scalePt]

theorem isUnit_mono {R : Type*} [CommRing R] (u : ℤ × ℤ) : IsUnit (mono u : LaurentTwo R) :=
  isUnit_iff_exists_inv.mpr ⟨mono (-u), by rw [mono_mul_mono, add_neg_cancel, mono_zero]⟩

/-- A unit factor may be stripped from an annihilator. -/
theorem act_eq_zero_of_isUnit_mul {U P : LaurentTwo ℤ} (hU : IsUnit U) {ξ : Config ℤ}
    (h : act (U * P) ξ = 0) : act P ξ = 0 := by
  obtain ⟨u, rfl⟩ := hU
  have h2 : act ((↑u⁻¹ : LaurentTwo ℤ) * ((↑u : LaurentTwo ℤ) * P)) ξ = 0 := by
    rw [act_mul, h, act_zero_right]
  rwa [← mul_assoc, Units.inv_mul, one_mul] at h2

/-! ### Products of difference polynomials indexed by a list

Defined exactly as `Nivat.KSC.prodList`, so that the two are interchangeable. -/

/-- `∏_{u ∈ L} (X^u − 1)`. -/
noncomputable def prodList (L : List (ℤ × ℤ)) : LaurentTwo ℤ := (L.map fun u => mono u - 1).prod

@[simp] theorem prodList_nil : prodList [] = 1 := rfl

theorem prodList_append (L M : List (ℤ × ℤ)) :
    prodList (L ++ M) = prodList L * prodList M := by
  rw [prodList, prodList, prodList, List.map_append, List.prod_append]

/-- A power of a `prodList` is again a `prodList`, over a list with the same entries. -/
theorem exists_prodList_pow (L : List (ℤ × ℤ)) (m : ℕ) :
    ∃ L' : List (ℤ × ℤ), (∀ u ∈ L', u ∈ L) ∧ prodList L' = prodList L ^ m := by
  induction m with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ m ih =>
      obtain ⟨L', hmem, hprod⟩ := ih
      refine ⟨L ++ L', ?_, ?_⟩
      · intro u hu
        rcases List.mem_append.mp hu with h | h
        · exact h
        · exact hmem u h
      · rw [prodList_append, hprod]; ring

/-! ### The polynomial of Theorem 3.1 and its monomial normalisation -/

/-- The Laurent polynomial `∏_{v ∈ supp(f), v ≠ v₀} (X^{rv} − X^{rv₀})` of source
Theorem 3.1. -/
noncomputable def bigProd (r : ℕ) (f : LaurentTwo ℤ) (v₀ : ℤ × ℤ) : LaurentTwo ℤ :=
  ∏ v ∈ (supp f).erase v₀, (mono (KS4.scalePt r v) - mono (KS4.scalePt r v₀))

/-- The list `[r(v − v₀) : v ∈ supp(f), v ≠ v₀]` of source Corollary 1. -/
noncomputable def shiftList (r : ℕ) (f : LaurentTwo ℤ) (v₀ : ℤ × ℤ) : List (ℤ × ℤ) :=
  ((supp f).erase v₀).toList.map fun v => KS4.scalePt r (v - v₀)

theorem mem_shiftList {r : ℕ} {f : LaurentTwo ℤ} {v₀ u : ℤ × ℤ} (hu : u ∈ shiftList r f v₀) :
    ∃ v ∈ (supp f).erase v₀, u = KS4.scalePt r (v - v₀) := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  exact ⟨v, Finset.mem_toList.mp hv, rfl⟩

theorem mono_sub_mono (a b : ℤ × ℤ) :
    (mono b - mono a : LaurentTwo ℤ) = mono a * (mono (b - a) - 1) := by
  rw [mul_sub, mono_mul_mono, mul_one, show a + (b - a) = b from by abel]

/-- **The monomial division of source Corollary 1**: `∏_{v ≠ v₀} (X^{rv} − X^{rv₀})` equals a
monomial times `∏_{v ≠ v₀} (X^{r(v−v₀)} − 1)`. -/
theorem bigProd_eq (r : ℕ) (f : LaurentTwo ℤ) (v₀ : ℤ × ℤ) :
    bigProd r f v₀
      = (mono (KS4.scalePt r v₀) : LaurentTwo ℤ) ^ ((supp f).erase v₀).card
        * prodList (shiftList r f v₀) := by
  classical
  have hfac : ∀ v ∈ (supp f).erase v₀,
      (mono (KS4.scalePt r v) - mono (KS4.scalePt r v₀) : LaurentTwo ℤ)
        = mono (KS4.scalePt r v₀) * (mono (KS4.scalePt r (v - v₀)) - 1) := by
    intro v _
    rw [mono_sub_mono, scalePt_sub]
  rw [bigProd, Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const]
  congr 1
  rw [shiftList, prodList, List.map_map]
  exact (Finset.prod_map_toList _ _).symm

/-! ### Theorem 3.1 up to a power -/

/-- **Source Theorem 3.1, up to a power.**  Let `ξ` be a finitary integral configuration, `f` a
non-zero integral annihilator, `r` the integer of source Lemma 3 and `v₀ ∈ supp(f)`.  Then some
positive power of `g = ∏_{v ∈ supp(f), v ≠ v₀} (X^{rv} − X^{rv₀})` annihilates `ξ`.

The source asserts that `g` itself annihilates; the passage from `g^m` to `g` is source Lemma 6,
which is **not** formalised — see the module docstring for why it is not needed downstream. -/
theorem exists_pow_bigProd_ann {ξ : Config ℤ} (hA : (Set.range ξ).Finite)
    {f : LaurentTwo ℤ} (hf : f ≠ 0) (hann : act f ξ = 0) {v₀ : ℤ × ℤ} (hv₀ : v₀ ∈ supp f) :
    ∃ r m : ℕ, 0 < r ∧ 0 < m ∧ act (bigProd r f v₀ ^ m) ξ = 0 := by
  classical
  -- source Lemma 3, translated to the `KS4.scaleExp` convention (bridge 1)
  obtain ⟨r, hr, hscale3⟩ := KS3.exists_scaling_ann_of_finite hA hf hann
  have hscale : ∀ n : ℕ, 0 < n → Nat.Coprime n r → act (KS4.scaleExp n f) ξ = 0 := by
    intro n hn hc
    rw [← ks3_scaleExp_eq_ks4]
    exact hscale3 n hn hc
  -- source Lemma 4 (bridges 2 and 3), giving vanishing on the torus zero locus of `Ann(c)`
  have hvan : ∀ Z : ℂˣ × ℂˣ,
      (∀ g : LaurentTwo ℂ, act g (cxConfig ξ) = 0 → KS.evalHom Z g = 0) →
        KS.evalHom Z (cx (bigProd r f v₀)) = 0 := by
    intro Z hZ
    have hroot : ∀ g : LaurentTwo ℤ, act g ξ = 0 →
        KS4.eval (Int.castRingHom ℂ) (toPt Z) g = 0 := by
      intro g hg
      rw [eval_eq_evalHom]
      exact hZ _ ((act_cx_eq_zero_iff g ξ).mpr hg)
    have hprod := KS4.prod_eq_zero_of_common_root (Int.castRingHom ℂ)
      (fun a b hab => Int.cast_injective hab) (Z := toPt Z) (r := r)
      (Units.ne_zero Z.1) (Units.ne_zero Z.2) hroot hscale hv₀
    -- rewrite `evalHom Z (cx g)` as the product appearing in Lemma 4
    rw [bigProd, map_prod, map_prod]
    refine (Finset.prod_congr rfl ?_).trans hprod
    intro v _
    rw [map_sub, map_sub, cx_mono, cx_mono, KS.evalHom_mono, KS.evalHom_mono, monoEval_toPt,
      monoEval_toPt]
  -- Hilbert's Nullstellensatz
  obtain ⟨m, hm, hmem⟩ :=
    KS.exists_pow_mem_annIdeal (c := cxConfig ξ) (f := cx (bigProd r f v₀)) hvan
  -- back to `ℤ` (bridge 3, easy direction)
  refine ⟨r, m, hr, hm, ?_⟩
  rw [← act_cx_eq_zero_iff, map_pow]
  exact hmem

/-! ### The conclusion of `Nivat.KSC.exists_prodList_ann` -/

/-- **Source Corollary 1, first half.**  A finitary integral configuration with a non-zero
integral annihilator has an annihilator of the form `∏ᵢ (X^{uᵢ} − 1)` with all `uᵢ ≠ 0`.

This is exactly the statement of `Nivat.KSC.exists_prodList_ann` (with `prodList` defined
identically); the pairwise-non-parallel refinement is `Nivat.KSC.exists_pairwise_of_prodList`. -/
theorem exists_prodList_ann {ξ : Config ℤ} (hA : (Set.range ξ).Finite)
    (hann : ∃ f : LaurentTwo ℤ, f ≠ 0 ∧ act f ξ = 0) :
    ∃ L : List (ℤ × ℤ), (∀ u ∈ L, u ≠ 0) ∧ act (prodList L) ξ = 0 := by
  classical
  obtain ⟨f, hf, hfann⟩ := hann
  -- `supp f` is non-empty, so `v₀` exists
  have hcoeff : f.coeff ≠ 0 := by
    intro hc
    exact hf (AddMonoidAlgebra.coeff_injective (by rw [hc, AddMonoidAlgebra.coeff_zero]))
  obtain ⟨v₀, hv₀⟩ := Finsupp.support_nonempty_iff.mpr hcoeff
  obtain ⟨r, m, hr, _hm, hpow⟩ := exists_pow_bigProd_ann hA hf hfann (v₀ := v₀) hv₀
  -- strip the monomial and the power
  obtain ⟨L, hLmem, hLprod⟩ := exists_prodList_pow (shiftList r f v₀) m
  refine ⟨L, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := mem_shiftList (hLmem u hu)
    exact scalePt_ne_zero hr.ne' (sub_ne_zero.mpr (Finset.ne_of_mem_erase hv))
  · refine act_eq_zero_of_isUnit_mul
      (U := ((mono (KS4.scalePt r v₀) : LaurentTwo ℤ) ^ ((supp f).erase v₀).card) ^ m)
      (((isUnit_mono _).pow _).pow m) ?_
    rw [hLprod, ← mul_pow, ← bigProd_eq]
    exact hpow

end Nivat.KS31
