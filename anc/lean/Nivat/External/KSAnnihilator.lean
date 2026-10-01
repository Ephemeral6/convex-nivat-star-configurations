/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Dichotomy
import Nivat.Defs.Complexity
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Kari–Szabados, Lemma 1: low complexity gives a non-zero integral annihilator

Formalisation of Lemma 1 of J. Kari and M. Szabados, *An algebraic geometric approach to
Nivat's conjecture* (arXiv:1605.05929; Inform. and Comput. 271 (2020)), specialised to
`d = 2` and to integral configurations of finite range, with an **integral** annihilator as
conclusion.  This is part (a) of `Nivat.kari_szabados` (Theorem 8.4(a) of the paper being
formalised).

## The argument (source, Lemma 1, verbatim structure)

> Denote `D = {u₁, …, uₙ}` and consider the set `{(1, c_{u₁+v}, …, c_{uₙ+v}) | v ∈ ℤᵈ}`.  It is
> a set of complex vectors of dimension `n+1`, and because `c` has low complexity there is at
> most `n` of them.  Therefore there exists a common non-zero orthogonal vector
> `(a₀, …, aₙ)`.  Let `g(X) = a₁X^{-u₁} + ⋯ + aₙX^{-uₙ} ≠ 0`; then the coefficient of `gc` at
> position `v` is `a₁c_{u₁+v} + ⋯ + aₙc_{uₙ+v} = -a₀`, that is, `gc` is a constant
> configuration.  Now it suffices to set `f = (X^v - 1) g` for an arbitrary non-zero `v`.

The source works over `ℂ`; the paper remarks (just before its Lemma 2) that "a small
modification of Lemma 1" gives an integral annihilator for integral configurations.  That
modification is carried out here: the vectors `(1, ξ(u₁+v), …, ξ(uₙ+v))` are integral, so
the linear dependence is taken over `ℤ` directly (`LinearIndependent.fintype_card_le_finrank`
holds over `ℤ`, which satisfies the strong rank condition), and no passage through `ℂ` or
through the source's Lemma 2 is needed.

In the notation of `Nivat.act` (where `(act f g)(z) = ∑_u c_u g(z+u)`), the polynomial `g` of
the source is `q = ∑_{s ∈ S} a_s T^s`, and the final annihilator is `(T^{(1,0)} - 1) * q`.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open Finset

/-- **Kari–Szabados, Lemma 1** (integral form).  If `ξ : ℤ² → ℤ` takes finitely many values
and `P_ξ(S) ≤ |S|` for some non-empty finite window `S`, then `ξ` has a non-zero annihilator
in `ℤ[T₁^±, T₂^±]`. -/
theorem hasNonzeroAnn_of_low_complexity' {ξ : Config ℤ} (hA : (Set.range ξ).Finite)
    {S : Finset (ℤ × ℤ)} (_hne : S.Nonempty) (hP : P ξ S ≤ S.card) :
    ∃ f : LaurentTwo ℤ, f ≠ 0 ∧ act f ξ = 0 := by
  classical
  have hfin : (patterns ξ S).Finite := patterns_finite_of_range_finite hA S
  have : Fintype ↥(patterns ξ S) := hfin.fintype
  have hcard : Fintype.card ↥(patterns ξ S) = P ξ S := by
    rw [P, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  -- the `|S| + 1` integer-valued functions `1` and `ρ ↦ ρ(s)` on the finite set of patterns:
  -- these are the coordinates of the source's vectors `(1, c_{u₁+v}, …, c_{uₙ+v})`
  set gfam : Option { x // x ∈ S } → (↥(patterns ξ S) → ℤ) := fun i ρ =>
    i.elim 1 fun s => ρ.1 s
  have hgnone : ∀ ρ, gfam none ρ = 1 := fun _ => rfl
  have hgsome : ∀ (s : { x // x ∈ S }) (y : ℤ × ℤ) (h : pattern ξ S y ∈ patterns ξ S),
      gfam (some s) ⟨pattern ξ S y, h⟩ = ξ (y + (s : ℤ × ℤ)) := fun _ _ _ => rfl
  -- `|S| + 1` vectors in a free `ℤ`-module of rank `P_ξ(S) ≤ |S|` are linearly dependent
  have hdep : ¬ LinearIndependent ℤ gfam := by
    intro hli
    have hcle := hli.fintype_card_le_finrank
    rw [Module.finrank_pi ℤ, hcard, Fintype.card_option, Fintype.card_coe] at hcle
    omega
  obtain ⟨cc, hrel, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  -- the relation, read at the pattern anchored at `z`: `a₀ + ∑_s a_s ξ(z + s) = 0`
  have heval : ∀ z : ℤ × ℤ,
      cc none + ∑ s : { x // x ∈ S }, cc (some s) * ξ (z + (s : ℤ × ℤ)) = 0 := by
    intro z
    have hmem : pattern ξ S z ∈ patterns ξ S := ⟨z, rfl⟩
    have hr := congrFun hrel ⟨pattern ξ S z, hmem⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hr
    rw [Fintype.sum_option, hgnone, mul_one] at hr
    simpa only [hgsome] using hr
  -- the Laurent polynomial `q = ∑_{s ∈ S} a_s T^s` (the source's `g`)
  set cf : ℤ × ℤ → ℤ := fun t => if ht : t ∈ S then cc (some ⟨t, ht⟩) else 0 with hcf
  have hcfsupp : ∀ t : ℤ × ℤ, cf t ≠ 0 → t ∈ S := by
    intro t ht
    by_contra hn
    exact ht (by simp [hcf, hn])
  set q : LaurentTwo ℤ := AddMonoidAlgebra.ofCoeff (Finsupp.onFinset S cf hcfsupp) with hq
  have hactq : ∀ (g : Config ℤ) (z : ℤ × ℤ), act q g z = ∑ t ∈ S, cf t * g (z + t) := by
    intro g z
    rw [act_apply]
    rw [show q.coeff = Finsupp.onFinset S cf hcfsupp from rfl,
      Finsupp.sum_of_support_subset _ Finsupp.support_onFinset_subset _ (by intro i _; ring)]
    simp [Finsupp.onFinset_apply]
  -- `q ξ` is the constant configuration `-a₀`
  have hconst : ∀ z : ℤ × ℤ, act q ξ z = -cc none := by
    intro z
    rw [hactq]
    have hsum : ∑ t ∈ S, cf t * ξ (z + t)
        = ∑ s : { x // x ∈ S }, cc (some s) * ξ (z + (s : ℤ × ℤ)) := by
      rw [← Finset.sum_attach S fun t => cf t * ξ (z + t)]
      exact Finset.sum_congr rfl fun s _ => by simp [hcf, s.2]
    rw [hsum]
    linear_combination heval z
  -- `q ≠ 0`: if all `a_s` vanished then `a₀ = 0` too, contradicting non-triviality
  have hqne : q ≠ 0 := by
    intro h0
    have hall : ∀ s : { x // x ∈ S }, cc (some s) = 0 := by
      intro s
      have hcz : q.coeff (s : ℤ × ℤ) = 0 := by rw [h0]; simp
      rw [show q.coeff = Finsupp.onFinset S cf hcfsupp from rfl, Finsupp.onFinset_apply] at hcz
      simpa [hcf, s.2] using hcz
    have hnone : cc none = 0 := by
      have hz := heval 0
      simp only [hall, zero_mul, Finset.sum_const_zero, add_zero] at hz
      exact hz
    rcases i₀ with _ | s
    · exact hi₀ hnone
    · exact hi₀ (hall s)
  -- `f = (T^{(1,0)} - 1) q` is non-zero (the ring is a domain) and kills `ξ`
  refine ⟨(mono (1, 0) - 1) * q, mul_ne_zero (mono_sub_one_ne_zero (by decide)) hqne, ?_⟩
  rw [act_mul, show act q ξ = fun _ => -cc none from funext hconst, act_sub_left, act_mono,
    act_one]
  funext z
  simp

end Nivat
