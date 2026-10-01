/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Laurent.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Kari–Szabados, Lemma 8: periodic decomposition

Formalisation of Lemma 8 of J. Kari and M. Szabados, *An algebraic geometric approach to
Nivat's conjecture* (arXiv:1605.05929; Inform. and Comput. **271** (2020), 104481),
specialised to `d = 2` and to the line Laurent polynomials `fᵢ = X^{hᵢ} - 1`.  This is the
content of the axiom `Nivat.kari_szabados_decomp` (the second half of Theorem 8.4(b) of the
paper being formalised):

> Let `f₁, …, f_m` be line Laurent polynomials in pairwise distinct directions and `c` a
> configuration annihilated by their product.  Then there exist configurations `c₁, …, c_m`
> such that `fᵢ` annihilates `cᵢ` and `c = c₁ + ⋯ + c_m`.

For `fᵢ = X^{hᵢ} - 1` the support is `{0, hᵢ}`, so `fᵢ` is a line Laurent polynomial as soon
as `hᵢ ≠ 0`, its direction is `⟨hᵢ⟩ ⊆ ℚ²`, and "pairwise distinct directions" is exactly
`det (hᵢ) (hⱼ) ≠ 0` for `i ≠ j`.  "`fᵢ` annihilates `cᵢ`" is `hᵢ ∈ Per cᵢ`
(`Nivat.act_mono_sub_one_eq_zero_iff`).

## The argument

The source proves Lemma 8 by induction on `m`, using its Lemma 7 (the *division lemma*):

> Let `f, g` be line Laurent polynomials in distinct directions and `c` a configuration
> annihilated by `g`.  Then there exists a configuration `c'` such that `f c' = c` and `c'` is
> also annihilated by `g`.

Lemma 7 is proved by solving, in a basis adapted to the direction of `f`, the linear
recurrence `(3)`

  `a_n c'_{[a-n,b]} + ⋯ + a_1 c'_{[a-1,b]} + a_0 c'_{[a,b]} = c_{[a,b]}`

with the boundary condition `c'_{[a,b]} = 0` for `0 ≤ a < n`; this determines `c'` uniquely,
forwards for `a ≥ n` and backwards for `a < 0`.  The source states Lemma 7 over `ℂ`; it is
the *proof of its Theorem 3.2* (not Example 4, which is about the impossibility of a
**finitary** decomposition) that records that for `f = X^{h} - 1` the recurrence has
`a_n = 1` and constant term `a_0 = -1`, so the forward and backward solutions stay integral.

Here that whole package is carried out at once, and directly over `ℤ`, in the shape actually
needed.  For `f = X^q - 1` recurrence `(3)` degenerates to a *telescoping* recurrence
`c'(z + q) - c'(z) = c(z)`, and the role of "the basis adapted to the direction of `f`"
together with the boundary condition is played by:

* `Nivat.KS.antidiff`, the two-sided antidifference of a sequence `ℤ → ℤ` vanishing at `0`
  (`Nivat.KS.antidiff_add_one`).  It is integral because the recurrence is monic with
  constant term `-1`; this is the only place integrality enters;
* the linear form `z ↦ det p z`, which is constant along `p` and increases by `det p q ≠ 0`
  along `q` (`Nivat.KS.kcoord_add_p`, `Nivat.KS.kcoord_add_q`).  Its floor-division by
  `det p q` selects, on each `⟨q⟩`-orbit, a base point `Nivat.KS.basept` lying in a
  fundamental domain, and the base point is `p`-equivariant.  Hence the solution
  `Nivat.KS.solve` inherits the period `p` (`Nivat.KS.solve_mem_Per`), which is the
  "`c'` is also annihilated by `g`" half of Lemma 7.

The induction of Lemma 8 is then `Nivat.KS.decomp_aux`: split off `p = h 0`, observe that
`c = ∏_{i ≥ 1}(X^{hᵢ} - 1) η` has period `p`, use `Nivat.KS.exists_preimage_prod` (Lemma 7
iterated over `i ≥ 1`) to lift `c` back to a `p`-periodic `η₀` with
`∏_{i ≥ 1}(X^{hᵢ} - 1) η₀ = c`, and apply the induction hypothesis to `η - η₀`.

## Deviations from the source, and what is *not* needed

* No finiteness of the range of `η` is assumed, and none is needed: Lemma 8 has no finitary
  hypothesis.  (Example 4 of the source shows the components genuinely need not be finitary
  even when `η` is, which is why the conclusion is about `Config ℤ` and not about a finite
  alphabet.)
* The hypothesis `∀ i, h i ≠ 0` of `Nivat.kari_szabados_decomp` is *not* used: it is kept in
  `Nivat.kari_szabados_decomp'` only so that the statement matches the axiom verbatim.
  (For `h i = 0` the factor `X^{h i} - 1` is `0`, the hypothesis `act (∏ …) η = 0` is vacuous,
  and the conclusion still holds because `0 ∈ Per c` always.)

## Main results

* `Nivat.KS.exists_solve` — Lemma 7 for `f = X^q - 1`, over `ℤ`.
* `Nivat.KS.exists_preimage_prod` — Lemma 7 iterated over a finite family.
* `Nivat.kari_szabados_decomp'` — Lemma 8, verbatim in the shape of the axiom
  `Nivat.kari_szabados_decomp` (note `prodShift h` is by definition `∏ i, (mono (h i) - 1)`).

## Status

Complete; no `sorry`.
-/

namespace Nivat.KS

open Finset

/-! ### The two-sided antidifference on `ℤ`

`antidiff a` is the unique `S : ℤ → ℤ` with `S 0 = 0` and `S (n + 1) - S n = a n`; it is the
solution of the degenerate case of the source's recurrence `(3)` (monic, constant term `-1`)
with the source's boundary condition, and it is manifestly integral. -/

/-- The two-sided antidifference of `a : ℤ → ℤ`: `antidiff a n = ∑_{0 ≤ j < n} a j` for
`n ≥ 0`, and `antidiff a n = -∑_{n ≤ j < 0} a j` for `n < 0`. -/
def antidiff (a : ℤ → ℤ) (n : ℤ) : ℤ :=
  (∑ j ∈ Finset.range n.toNat, a (j : ℤ)) - ∑ j ∈ Finset.range (-n).toNat, a (-(j : ℤ) - 1)

@[simp] theorem antidiff_zero (a : ℤ → ℤ) : antidiff a 0 = 0 := by simp [antidiff]

/-- The defining recurrence: `antidiff a` has forward difference `a`. -/
theorem antidiff_add_one (a : ℤ → ℤ) (n : ℤ) : antidiff a (n + 1) = antidiff a n + a n := by
  by_cases hn : 0 ≤ n
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, by omega⟩
    have h1 : ((N : ℤ) + 1).toNat = N + 1 := by omega
    have h2 : ((N : ℤ)).toNat = N := by omega
    have h3 : (-((N : ℤ) + 1)).toNat = 0 := by omega
    have h4 : (-(N : ℤ)).toNat = 0 := by omega
    simp only [antidiff, h1, h2, h3, h4, Finset.range_zero, Finset.sum_empty, sub_zero,
      Finset.sum_range_succ]
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, n = -(M : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    have h1 : (-(M : ℤ) - 1 + 1).toNat = 0 := by omega
    have h2 : (-(M : ℤ) - 1).toNat = 0 := by omega
    have h3 : (-(-(M : ℤ) - 1 + 1)).toNat = M := by omega
    have h4 : (-(-(M : ℤ) - 1)).toNat = M + 1 := by omega
    simp only [antidiff, h1, h2, h3, h4, Finset.range_zero, Finset.sum_empty, zero_sub,
      Finset.sum_range_succ]
    ring

/-! ### Lemma 7 for `f = X^q - 1`

Fix `p q : ℤ × ℤ` with `det p q ≠ 0` (the source's "distinct directions").  The linear form
`z ↦ det p z` is `p`-invariant and increases by `det p q` along `q`. -/

variable (p q : ℤ × ℤ)

theorem det_add_right (u w : ℤ × ℤ) : det p (u + w) = det p u + det p w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

/-- The index of `z` along the `q`-orbit: the floor-division of the `p`-form by `det p q`. -/
def kcoord (z : ℤ × ℤ) : ℤ := det p z / det p q

/-- The base point of the `q`-orbit of `z`: the representative with `p`-form in `[0, |det p q|)`. -/
def basept (z : ℤ × ℤ) : ℤ × ℤ := z - (kcoord p q z) • q

variable {p q}

theorem kcoord_add_q (hd : det p q ≠ 0) (z : ℤ × ℤ) :
    kcoord p q (z + q) = kcoord p q z + 1 := by
  have h : det p (z + q) = det p z + 1 * det p q := by
    rw [det_add_right]; ring
  rw [kcoord, kcoord, h, Int.add_mul_ediv_right _ _ hd]

theorem kcoord_add_p (z : ℤ × ℤ) : kcoord p q (z + p) = kcoord p q z := by
  rw [kcoord, kcoord, det_add_right, det_self, add_zero]

theorem basept_add_q (hd : det p q ≠ 0) (z : ℤ × ℤ) :
    basept p q (z + q) = basept p q z := by
  rw [basept, basept, kcoord_add_q hd, add_smul, one_smul]
  abel

theorem basept_add_p (z : ℤ × ℤ) : basept p q (z + p) = basept p q z + p := by
  rw [basept, basept, kcoord_add_p]
  abel

theorem basept_add_kcoord_smul (z : ℤ × ℤ) : basept p q z + (kcoord p q z) • q = z := by
  rw [basept]; abel

/-- The solution of the (degenerate) recurrence `(3)` of the source: on each `⟨q⟩`-orbit,
telescope the values of `c` starting from the base point of the orbit. -/
def solve (p q : ℤ × ℤ) (c : Config ℤ) : Config ℤ :=
  fun z => antidiff (fun j => c (basept p q z + j • q)) (kcoord p q z)

/-- **Lemma 7 (source), second half**: the solution keeps the period `p`. -/
theorem solve_mem_Per {c : Config ℤ} (hp : p ∈ Per c) : p ∈ Per (solve p q c) := by
  rw [mem_Per_iff]
  funext z
  rw [T_apply]
  simp only [solve, basept_add_p, kcoord_add_p]
  congr 1
  funext j
  rw [show basept p q z + p + j • q = basept p q z + j • q + p by abel]
  exact Per.apply hp _

/-- **Lemma 7 (source), first half**: the solution really is a preimage under `X^q - 1`. -/
theorem act_solve (hd : det p q ≠ 0) (c : Config ℤ) :
    act (mono q - 1 : LaurentTwo ℤ) (solve p q c) = c := by
  rw [act_sub_left, act_mono, act_one]
  funext z
  rw [Pi.sub_apply, T_apply]
  simp only [solve, basept_add_q hd, kcoord_add_q hd, antidiff_add_one]
  rw [basept_add_kcoord_smul]
  ring

/-- **Lemma 7** of Kari–Szabados, specialised to `f = X^q - 1` and `g` any Laurent polynomial
annihilating `c` and having `p` as an associated period.  Stated in the only form needed: if
`c` has period `p` and `q` is not parallel to `p`, then `c = (X^q - 1) c'` for some `c'` that
still has period `p`. -/
theorem exists_solve (hd : det p q ≠ 0) {c : Config ℤ} (hp : p ∈ Per c) :
    ∃ c' : Config ℤ, p ∈ Per c' ∧ act (mono q - 1 : LaurentTwo ℤ) c' = c :=
  ⟨solve p q c, solve_mem_Per hp, act_solve hd c⟩

/-- Lemma 7 iterated: a `p`-periodic configuration is `∏_{i ∈ s} (X^{H i} - 1)` applied to
some `p`-periodic configuration, as soon as every `H i` is non-parallel to `p`. -/
theorem exists_preimage_prod {ι : Type*} [DecidableEq ι] {p : ℤ × ℤ} {H : ι → ℤ × ℤ}
    (hd : ∀ i, det p (H i) ≠ 0) {c : Config ℤ} (hp : p ∈ Per c) (s : Finset ι) :
    ∃ c' : Config ℤ, p ∈ Per c' ∧
      act (∏ i ∈ s, (mono (H i) - 1) : LaurentTwo ℤ) c' = c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, hp, by simp⟩
  | insert a s ha ih =>
      obtain ⟨c₁, hc₁p, hc₁⟩ := ih
      obtain ⟨c', hc'p, hc'⟩ := exists_solve (hd a) hc₁p
      refine ⟨c', hc'p, ?_⟩
      rw [Finset.prod_insert ha, mul_comm, act_mul, hc', hc₁]

/-! ### Lemma 8 -/

/-- **Lemma 8** of Kari–Szabados, specialised to `fᵢ = X^{hᵢ} - 1`, by induction on the number
of factors. -/
theorem decomp_aux : ∀ (n : ℕ) (h : Fin n → ℤ × ℤ),
    (Pairwise fun i j => det (h i) (h j) ≠ 0) → ∀ η : Config ℤ,
    act (∏ i, (mono (h i) - 1) : LaurentTwo ℤ) η = 0 →
    ∃ f : Fin n → Config ℤ, (∀ i, h i ∈ Per (f i)) ∧ ∀ z, η z = ∑ i, f i z := by
  intro n
  induction n with
  | zero =>
      intro h _ η hann
      have h1 : (∏ i, (mono (h i) - 1) : LaurentTwo ℤ) = 1 := by simp
      rw [h1, act_one] at hann
      refine ⟨fun i => i.elim0, fun i => i.elim0, fun z => ?_⟩
      rw [hann]
      simp
  | succ n ih =>
      intro h hnp η hann
      -- split off the first factor
      have hsplit : (∏ i, (mono (h i) - 1) : LaurentTwo ℤ)
          = (mono (h 0) - 1) * ∏ i : Fin n, (mono (h i.succ) - 1) := Fin.prod_univ_succ _
      have hd : ∀ i : Fin n, det (h 0) (h i.succ) ≠ 0 := fun i =>
        hnp (Ne.symm (Fin.succ_ne_zero i))
      -- `c`, the image of `η` under the remaining factors, has period `h 0`
      have hcp : h 0 ∈ Per (act (∏ i : Fin n, (mono (h i.succ) - 1) : LaurentTwo ℤ) η) := by
        rw [← act_mono_sub_one_eq_zero_iff, ← act_mul, ← hsplit]
        exact hann
      obtain ⟨η₀, hη₀p, hη₀⟩ := exists_preimage_prod hd hcp Finset.univ
      have hzero : act (∏ i : Fin n, (mono (h i.succ) - 1) : LaurentTwo ℤ) (η - η₀) = 0 := by
        rw [act_sub_right, hη₀, sub_self]
      have hnp' : Pairwise fun i j : Fin n => det (h i.succ) (h j.succ) ≠ 0 := by
        intro i j hij
        exact hnp fun hcon => hij (Fin.succ_injective n hcon)
      obtain ⟨f', hf'p, hf'sum⟩ := ih (fun i => h i.succ) hnp' (η - η₀) hzero
      refine ⟨Fin.cons η₀ f', ?_, ?_⟩
      · intro i
        induction i using Fin.cases with
        | zero => simpa using hη₀p
        | succ i => simpa using hf'p i
      · intro z
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have h2 := hf'sum z
        simp only [Pi.sub_apply] at h2
        rw [← h2]
        ring

end Nivat.KS

namespace Nivat

/-- **Kari–Szabados, Lemma 8** (specialised form).  Every `η : ℤ² → ℤ` annihilated by
`Δ = ∏ᵢ (X^{hᵢ} - 1)`, with the `hᵢ` pairwise non-parallel, decomposes as `η = ∑ᵢ ηᵢ` with
`ηᵢ` of period `hᵢ`.

This is exactly the statement of the axiom `Nivat.kari_szabados_decomp`; note that
`Nivat.prodShift h` is by definition `∏ i, (mono (h i) - 1)`, so this theorem can replace that
axiom directly.  The hypothesis `hne : ∀ i, h i ≠ 0` is unused (see the module docstring); it
is kept so that the signature matches the axiom verbatim. -/
theorem kari_szabados_decomp' {n : ℕ} {h : Fin n → ℤ × ℤ} (_hne : ∀ i, h i ≠ 0)
    (hnp : Pairwise fun i j => det (h i) (h j) ≠ 0) {η : Config ℤ}
    (hann : act (∏ i, (mono (h i) - 1) : LaurentTwo ℤ) η = 0) :
    ∃ f : Fin n → Config ℤ, (∀ i, h i ∈ Per (f i)) ∧ ∀ z, η z = ∑ i, f i z :=
  KS.decomp_aux n h hnp η hann

end Nivat
