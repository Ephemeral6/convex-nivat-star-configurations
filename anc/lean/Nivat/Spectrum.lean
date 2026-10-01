/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Dichotomy
import Nivat.Laurent.Newton
import Nivat.Laurent.Ostrowski
import Nivat.Laurent.UFD
import Nivat.Lattice.Zonotope
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# §2. The spectrum, the annihilator `A`, and the dimension budget

Formalisation of §2 of *The Convex Nivat Conjecture* (Pan).

Under the standing hypothesis (1.1) the whole configuration is annihilated by a *canonical*
Laurent polynomial `A(T) = ∏ᵢ Aᵢ(T^{vᵢ})`, whose Newton polygon is the zonotope
`Z = ∑ᵢ [0, dᵢ vᵢ]`.  The route is:

* §2.1 the one-sided limits `σᵢ^ε` and the doubly periodic fields `Gᵢ^{ε,δ}` in the orbit
  closure;
* §2.2 spectral projections along the period `Hᵢ = κᵢ vᵢ`, the exceptional difference fields
  `dᵢ,ε,δ,a` and their spectra `Λᵢ ≠ ∅`;
* §2.3 an integer encoding `w : 𝔽_p ↪ ℤ` preserving every spectrum;
* §2.4 one-sided vanishing forces divisibility by `T^{vᵢ} - λ`;
* §2.5 assembling the prime factors: any `f` with `f(T) ψ` constant is divisible by `A`;
* §2.6 the dimension budget `dim U_S ≥ |S| - |R_Z(S)| + 1`.

## Main definitions

* `Nivat.specProj` — the spectral projection `P_λ`.
* `Nivat.Occurs` — "`λ` occurs in `d`".
* `Nivat.StarConfig.sigma`, `Nivat.StarConfig.Gfield` — the fields of §2.1.
* `Nivat.StarConfig.Lam`, `Nivat.StarConfig.Afac`, `Nivat.StarConfig.Aop` — `Λᵢ`, `Aᵢ(T^{vᵢ})`,
  `A(T)`.
* `Nivat.StarConfig.Zono` — the zonotope `Z = Newt(A)`.
* `Nivat.StarConfig.enc`, `Nivat.StarConfig.psi` — the encoding `w` and `ψ = w(θ)`.
* `Nivat.StarConfig.US` — the space of affine relations `U_S`.

## Main results

* `Nivat.act_specProj_apply` — **Lemma 2.0**.
* `Nivat.StarConfig.Lam_nonempty` — **Lemma 2.1**.
* `Nivat.StarConfig.exists_enc` — **Lemma 2.2**.
* `Nivat.linFactor_dvd` — **Lemma 2.3**.
* `Nivat.StarConfig.Aop_dvd` — **Lemma 2.4**.
* `Nivat.StarConfig.card_add_one_le_finrank_US_add_ncard_RZ` — **Lemma 2.5**.
* `Nivat.StarConfig.P_ge_of_RZ_eq_empty` — **Remark 2.6**.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open Finset

open scoped Pointwise

/-! ### §2.2 Spectral projections

Throughout, `(v, u)` is a unimodular basis (`det v u = 1`), `κ ≥ 1`, and `d` is a complex
configuration with period `κ v`.  A point is written `z = s v + t u`; `{t = const}` is a
*transverse row*. -/

/-- The `κ`-th roots of unity in `ℂ`, as a `Finset`. -/
noncomputable def rootsFinset (κ : ℕ) : Finset ℂ := Polynomial.nthRootsFinset κ (1 : ℂ)

theorem mem_rootsFinset {κ : ℕ} (hκ : 0 < κ) {lam : ℂ} :
    lam ∈ rootsFinset κ ↔ lam ^ κ = 1 :=
  Polynomial.mem_nthRootsFinset hκ 1

theorem card_rootsFinset {κ : ℕ} (hκ : 0 < κ) : (rootsFinset κ).card = κ :=
  (Complex.isPrimitiveRoot_exp κ hκ.ne').card_nthRootsFinset

theorem ne_zero_of_mem_rootsFinset {κ : ℕ} {lam : ℂ} (h : lam ∈ rootsFinset κ) : lam ≠ 0 :=
  Polynomial.ne_zero_of_mem_nthRootsFinset one_ne_zero h

/-- A primitive `κ`-th root of unity lies in `rootsFinset κ`. -/
theorem exists_primitiveRoot_mem {κ : ℕ} (hκ : 0 < κ) :
    ∃ ζ ∈ rootsFinset κ, ∀ k : ℕ, 0 < k → k < κ → ζ ^ k ≠ 1 := by
  refine ⟨_, (mem_rootsFinset hκ).mpr (Complex.isPrimitiveRoot_exp κ hκ.ne').pow_eq_one,
    fun k hk0 hkκ => (Complex.isPrimitiveRoot_exp κ hκ.ne').pow_ne_one_of_pos_of_lt hk0.ne' hkκ⟩

/-- Multiplication by a `κ`-th root of unity permutes `rootsFinset κ`. -/
theorem image_mul_rootsFinset {κ : ℕ} (hκ : 0 < κ) {ζ : ℂ} (hζ : ζ ∈ rootsFinset κ) :
    (rootsFinset κ).image (fun lam => ζ * lam) = rootsFinset κ := by
  classical
  refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · obtain ⟨lam, hlam, rfl⟩ := Finset.mem_image.mp hx
    rw [mem_rootsFinset hκ, mul_pow, (mem_rootsFinset hκ).mp hζ,
      (mem_rootsFinset hκ).mp hlam, one_mul]
  · rw [Finset.card_image_of_injective _ (mul_right_injective₀ (ne_zero_of_mem_rootsFinset hζ))]

/-- The power sums of the `κ`-th roots of unity vanish in the range `0 < k < κ`.  (Stated for
`λ⁻¹`, which is the form needed by the spectral projections.) -/
theorem sum_inv_pow_rootsFinset {κ k : ℕ} (hk0 : 0 < k) (hkκ : k < κ) :
    ∑ lam ∈ rootsFinset κ, lam⁻¹ ^ k = 0 := by
  classical
  have hκ : 0 < κ := hk0.trans hkκ
  obtain ⟨ζ, hζmem, hζprim⟩ := exists_primitiveRoot_mem hκ
  have hζ0 : ζ ≠ 0 := ne_zero_of_mem_rootsFinset hζmem
  have hζk : (ζ⁻¹) ^ k ≠ 1 := by
    rw [inv_pow]
    intro h
    exact hζprim k hk0 hkκ (by rw [← inv_inv (ζ ^ k), h, inv_one])
  have hT : ∑ lam ∈ rootsFinset κ, lam⁻¹ ^ k
      = (ζ⁻¹) ^ k * ∑ lam ∈ rootsFinset κ, lam⁻¹ ^ k := by
    conv_lhs => rw [← image_mul_rootsFinset hκ hζmem]
    rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hζ0 h), Finset.mul_sum]
    exact Finset.sum_congr rfl fun lam _ => by rw [mul_inv, mul_pow]
  have hz : ((ζ⁻¹) ^ k - 1) * ∑ lam ∈ rootsFinset κ, lam⁻¹ ^ k = 0 := by
    linear_combination -hT
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd (by linear_combination h) hζk
  · exact h

/-- The spectral projection `P_λ = κ⁻¹ ∑_{k < κ} λ^{-k} T^{k v}`.  Paper Lemma 2.0. -/
noncomputable def specProj (κ : ℕ) (v : ℤ × ℤ) (lam : ℂ) : LaurentTwo ℂ :=
  ∑ k ∈ Finset.range κ, AddMonoidAlgebra.single ((k : ℤ) • v) ((κ : ℂ)⁻¹ * lam⁻¹ ^ k)

/-- The `λ`-component of the transverse row `t`:
`d_t(λ) = κ⁻¹ ∑_{k < κ} λ^{-k} d(k v + t u)`.  Paper Lemma 2.0. -/
noncomputable def rowCoeff (κ : ℕ) (v u : ℤ × ℤ) (d : Config ℂ) (lam : ℂ) (t : ℤ) : ℂ :=
  (κ : ℂ)⁻¹ * ∑ k ∈ Finset.range κ, lam⁻¹ ^ k * d ((k : ℤ) • v + t • u)

/-! #### The action of a finite sum of monomials -/

/-- The action of a single monomial `c T^a`. -/
theorem act_single {R : Type*} [CommRing R] (a : ℤ × ℤ) (c : R) (g : Config R) (z : ℤ × ℤ) :
    act (AddMonoidAlgebra.single a c) g z = c * g (z + a) := by
  rw [act_apply, AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]

/-- `act` is additive in the operator, pointwise over a finite sum. -/
theorem act_sum_apply {R ι : Type*} [CommRing R] (s : Finset ι) (F : ι → LaurentTwo R)
    (g : Config R) (z : ℤ × ℤ) : act (∑ i ∈ s, F i) g z = ∑ i ∈ s, act (F i) g z := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, act_add_left, Finset.sum_cons]
    show act (F a) g z + act (∑ i ∈ s, F i) g z = act (F a) g z + ∑ i ∈ s, act (F i) g z
    rw [ih]

/-- `act` is additive in the configuration, over a finite sum. -/
theorem act_sum_right {R ι : Type*} [CommRing R] (f : LaurentTwo R) (s : Finset ι)
    (g : ι → Config R) : act f (∑ i ∈ s, g i) = ∑ i ∈ s, act f (g i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, act_add_right, ih, Finset.sum_cons]

/-- The spectral projection, evaluated. -/
theorem act_specProj_eq (κ : ℕ) (v : ℤ × ℤ) (lam : ℂ) (d : Config ℂ) (z : ℤ × ℤ) :
    act (specProj κ v lam) d z
      = (κ : ℂ)⁻¹ * ∑ k ∈ Finset.range κ, lam⁻¹ ^ k * d (z + (k : ℤ) • v) := by
  rw [specProj, act_sum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [act_single, mul_assoc]

/-- Shifting the window of a `κ`-periodic sum over `ℤ` does not change it. -/
theorem sum_range_shift_of_periodic {κ : ℕ} {G : ℤ → ℂ} (hG : ∀ j : ℤ, G (j + κ) = G j) (s : ℤ) :
    ∑ k ∈ Finset.range κ, G (s + k) = ∑ k ∈ Finset.range κ, G k := by
  have step : ∀ a : ℤ,
      ∑ k ∈ Finset.range κ, G (a + 1 + k) = ∑ k ∈ Finset.range κ, G (a + k) := by
    intro a
    have h1 := Finset.sum_range_succ (fun k : ℕ => G (a + k)) κ
    have h2 := Finset.sum_range_succ' (fun k : ℕ => G (a + k)) κ
    have h3 : ∑ k ∈ Finset.range κ, G (a + ((k : ℤ) + 1)) = ∑ k ∈ Finset.range κ, G (a + 1 + k) :=
      Finset.sum_congr rfl fun k _ => by rw [show a + ((k : ℤ) + 1) = a + 1 + k from by ring]
    rw [h1] at h2
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at h2
    rw [hG a, h3] at h2
    exact (add_right_cancel h2).symm
  induction s using Int.induction_on with
  | zero => simp
  | succ n ih => rw [step (n : ℤ)]; exact ih
  | pred n ih =>
    have h := step (-(n : ℤ) - 1)
    rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) from by ring] at h
    rw [← h]; exact ih

/-- The key shift identity behind Lemma 2.0: translating by `w v` multiplies `P_λ d` by `λ^w`. -/
theorem act_specProj_shift {κ : ℕ} (hκ : 0 < κ) {v : ℤ × ℤ} {d : Config ℂ}
    (hd : T ((κ : ℤ) • v) d = d) {lam : ℂ} (hlam : lam ∈ rootsFinset κ) (z : ℤ × ℤ) (w : ℤ) :
    act (specProj κ v lam) d (z + w • v) = lam ^ w * act (specProj κ v lam) d z := by
  have hlam0 : lam ≠ 0 := ne_zero_of_mem_rootsFinset hlam
  have hinv0 : lam⁻¹ ≠ 0 := inv_ne_zero hlam0
  have hinvκ : lam⁻¹ ^ (κ : ℤ) = 1 := by
    rw [zpow_natCast, inv_pow, (mem_rootsFinset hκ).mp hlam, inv_one]
  have hss : lam ^ w * lam⁻¹ ^ w = 1 := by rw [← mul_zpow, mul_inv_cancel₀ hlam0, one_zpow]
  set G : ℤ → ℂ := fun j => lam⁻¹ ^ j * d (z + j • v) with hGdef
  have hGper : ∀ j : ℤ, G (j + κ) = G j := by
    intro j
    have h1 : lam⁻¹ ^ (j + (κ : ℤ)) = lam⁻¹ ^ j := by rw [zpow_add₀ hinv0, hinvκ, mul_one]
    have h2 : d (z + (j + (κ : ℤ)) • v) = d (z + j • v) := by
      rw [show z + (j + (κ : ℤ)) • v = (z + j • v) + (κ : ℤ) • v from by rw [add_smul]; abel]
      exact congrFun hd _
    show lam⁻¹ ^ (j + (κ : ℤ)) * d (z + (j + (κ : ℤ)) • v) = lam⁻¹ ^ j * d (z + j • v)
    rw [h1, h2]
  have hL : ∑ k ∈ Finset.range κ, lam⁻¹ ^ k * d (z + w • v + (k : ℤ) • v)
      = lam ^ w * ∑ k ∈ Finset.range κ, G (w + k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show lam⁻¹ ^ k * d (z + w • v + (k : ℤ) • v)
      = lam ^ w * (lam⁻¹ ^ (w + (k : ℤ)) * d (z + (w + (k : ℤ)) • v))
    rw [zpow_add₀ hinv0, zpow_natCast, add_smul,
      show z + (w • v + (k : ℤ) • v) = z + w • v + (k : ℤ) • v from by abel,
      ← mul_assoc, ← mul_assoc, hss, one_mul]
  have hR : ∑ k ∈ Finset.range κ, lam⁻¹ ^ k * d (z + (k : ℤ) • v)
      = ∑ k ∈ Finset.range κ, G (k : ℤ) :=
    Finset.sum_congr rfl fun k _ => by
      show lam⁻¹ ^ k * d (z + (k : ℤ) • v) = lam⁻¹ ^ (k : ℤ) * d (z + (k : ℤ) • v)
      rw [zpow_natCast]
  rw [act_specProj_eq, act_specProj_eq, hL, hR, sum_range_shift_of_periodic hGper w]
  ring

/-- **Lemma 2.0 (1).**  `(P_λ d)(s v + t u) = λ^s d_t(λ)`. -/
theorem act_specProj_apply {κ : ℕ} (hκ : 0 < κ) {v u : ℤ × ℤ} (_hdet : det v u = 1)
    {d : Config ℂ} (hd : T ((κ : ℤ) • v) d = d) {lam : ℂ} (hlam : lam ∈ rootsFinset κ)
    (s t : ℤ) :
    act (specProj κ v lam) d (s • v + t • u) = lam ^ s * rowCoeff κ v u d lam t := by
  rw [show s • v + t • u = t • u + s • v from add_comm _ _,
    act_specProj_shift hκ hd hlam (t • u) s, act_specProj_eq, rowCoeff]
  congr 2
  exact Finset.sum_congr rfl fun k _ => by rw [add_comm (t • u) ((k : ℤ) • v)]

/-- **Lemma 2.0 (1), completeness.**  `∑_λ P_λ d = d`. -/
theorem sum_act_specProj {κ : ℕ} (hκ : 0 < κ) {v : ℤ × ℤ} {d : Config ℂ}
    (_hd : T ((κ : ℤ) • v) d = d) :
    ∑ lam ∈ rootsFinset κ, act (specProj κ v lam) d = d := by
  funext z
  have hcard : (((rootsFinset κ).card : ℕ) : ℂ) = (κ : ℂ) := by rw [card_rootsFinset hκ]
  have hκ0 : (κ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hκ.ne'
  have key : ∀ k ∈ Finset.range κ,
      (∑ lam ∈ rootsFinset κ, lam⁻¹ ^ k) * d (z + (k : ℤ) • v)
        = if k = 0 then (κ : ℂ) * d z else 0 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [hcard]
    · rw [if_neg hk0.ne', sum_inv_pow_rootsFinset hk0 (Finset.mem_range.mp hk), zero_mul]
  calc (∑ lam ∈ rootsFinset κ, act (specProj κ v lam) d) z
      = ∑ lam ∈ rootsFinset κ, act (specProj κ v lam) d z := Finset.sum_apply _ _ _
    _ = ∑ lam ∈ rootsFinset κ,
          (κ : ℂ)⁻¹ * ∑ k ∈ Finset.range κ, lam⁻¹ ^ k * d (z + (k : ℤ) • v) :=
        Finset.sum_congr rfl fun lam _ => act_specProj_eq κ v lam d z
    _ = (κ : ℂ)⁻¹ * ∑ lam ∈ rootsFinset κ, ∑ k ∈ Finset.range κ,
          lam⁻¹ ^ k * d (z + (k : ℤ) • v) := by rw [Finset.mul_sum]
    _ = (κ : ℂ)⁻¹ * ∑ k ∈ Finset.range κ, ∑ lam ∈ rootsFinset κ,
          lam⁻¹ ^ k * d (z + (k : ℤ) • v) := by rw [Finset.sum_comm]
    _ = (κ : ℂ)⁻¹ * ∑ k ∈ Finset.range κ,
          (∑ lam ∈ rootsFinset κ, lam⁻¹ ^ k) * d (z + (k : ℤ) • v) := by
        congr 1
        exact Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm
    _ = (κ : ℂ)⁻¹ * ∑ k ∈ Finset.range κ, if k = 0 then (κ : ℂ) * d z else 0 := by
        rw [Finset.sum_congr rfl key]
    _ = (κ : ℂ)⁻¹ * ((κ : ℂ) * d z) := by
        congr 1
        rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hκ)
          (fun b _ hb => if_neg hb), if_pos rfl]
    _ = d z := by field_simp

/-- **Lemma 2.0 (2).**  `T^v P_λ d = λ P_λ d`. -/
theorem T_act_specProj {κ : ℕ} (hκ : 0 < κ) {v : ℤ × ℤ} {d : Config ℂ}
    (hd : T ((κ : ℤ) • v) d = d) {lam : ℂ} (hlam : lam ∈ rootsFinset κ) :
    T v (act (specProj κ v lam) d) = lam • act (specProj κ v lam) d := by
  funext z
  show act (specProj κ v lam) d (z + v) = lam • act (specProj κ v lam) d z
  rw [show z + v = z + (1 : ℤ) • v from by rw [one_smul],
    act_specProj_shift hκ hd hlam z 1, zpow_one, smul_eq_mul]

/-- **Lemma 2.0 (3).**  `P_λ` is a Laurent polynomial, hence commutes with every `f(T)`. -/
theorem act_specProj_comm (κ : ℕ) (v : ℤ × ℤ) (lam : ℂ) (f : LaurentTwo ℂ) (d : Config ℂ) :
    act (specProj κ v lam) (act f d) = act f (act (specProj κ v lam) d) := by
  rw [← act_mul, ← act_mul, mul_comm]

/-- The one-variable Laurent polynomial `f(λ, Y) = ∑_β f_β Y^β`, where `f_β = ∑_α f_{α v + β u} λ^α`,
obtained from `f` by the unimodular change of basis `X = T^v`, `Y = T^u` followed by
evaluation `X = λ`.  Paper Lemma 2.0 (4). -/
noncomputable def uniPart (f : LaurentTwo ℂ) (v u : ℤ × ℤ) (lam : ℂ) : ℤ →₀ ℂ :=
  f.coeff.sum fun z a => Finsupp.single (det v z) (a * lam ^ (det z u))

/-- **Lemma 2.0 (4).**  `(f(T) P_λ d)(s v + t u) = λ^s ∑_β f_β d_{t+β}(λ)`. -/
theorem act_act_specProj {κ : ℕ} (hκ : 0 < κ) {v u : ℤ × ℤ} (hdet : det v u = 1)
    (f : LaurentTwo ℂ) {d : Config ℂ} (hd : T ((κ : ℤ) • v) d = d)
    {lam : ℂ} (hlam : lam ∈ rootsFinset κ) (s t : ℤ) :
    act f (act (specProj κ v lam) d) (s • v + t • u)
      = lam ^ s * (uniPart f v u lam).sum fun b g => g * rowCoeff κ v u d lam (t + b) := by
  classical
  have hlam0 : lam ≠ 0 := ne_zero_of_mem_rootsFinset hlam
  -- Expand the one-variable sum over `β` back into a sum over the support of `f`.
  have hU : ((uniPart f v u lam).sum fun b g => g * rowCoeff κ v u d lam (t + b))
      = f.coeff.sum fun w cw =>
          cw * lam ^ (det w u) * rowCoeff κ v u d lam (t + det v w) := by
    rw [uniPart, Finsupp.sum_sum_index (fun a => by ring) (fun a b₁ b₂ => by ring)]
    exact Finsupp.sum_congr fun w _ => Finsupp.sum_single_index (by ring)
  rw [hU, act_apply, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun w _ => ?_
  have hw : s • v + t • u + w = (s + det w u) • v + (t + det v w) • u := by
    conv_lhs => rw [eq_smul_add_smul hdet w]
    rw [add_smul, add_smul]
    abel
  rw [hw, act_specProj_apply hκ hdet hd hlam, zpow_add₀ hlam0]
  ring

/-- `λ` **occurs** in `d` if `P_λ d ≠ 0`, equivalently if `d_t(λ) ≠ 0` for some row `t`.
Paper §2.2. -/
def Occurs (κ : ℕ) (v : ℤ × ℤ) (lam : ℂ) (d : Config ℂ) : Prop :=
  act (specProj κ v lam) d ≠ 0

theorem occurs_iff_exists_row {κ : ℕ} (hκ : 0 < κ) {v u : ℤ × ℤ} (hdet : det v u = 1)
    {d : Config ℂ} (hd : T ((κ : ℤ) • v) d = d) {lam : ℂ} (hlam : lam ∈ rootsFinset κ) :
    Occurs κ v lam d ↔ ∃ t : ℤ, rowCoeff κ v u d lam t ≠ 0 := by
  constructor
  · intro h
    replace h : act (specProj κ v lam) d ≠ 0 := h
    obtain ⟨z, hz⟩ := Function.ne_iff.mp h
    rw [Pi.zero_apply] at hz
    refine ⟨det v z, fun hrow => hz ?_⟩
    rw [eq_smul_add_smul hdet z, act_specProj_apply hκ hdet hd hlam, hrow, mul_zero]
  · rintro ⟨t, ht⟩
    show act (specProj κ v lam) d ≠ 0
    intro hzero
    refine ht ?_
    have h0 := act_specProj_apply hκ hdet hd hlam 0 t
    rw [hzero, Pi.zero_apply, zpow_zero, one_mul] at h0
    exact h0.symm

/-- The linear factor `T^v - λ`.  Paper §2.2, (2.1). -/
noncomputable def linFactor (v : ℤ × ℤ) (lam : ℂ) : LaurentTwo ℂ :=
  mono v - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam

/-- `T^v - λ ≠ 0`.  The hypothesis `v ≠ 0` is needed: `T^0 - 1 = 0`. -/
theorem linFactor_ne_zero {v : ℤ × ℤ} (hv : v ≠ 0) (lam : ℂ) : linFactor v lam ≠ 0 := by
  intro h
  have hc : (linFactor v lam).coeff v = 1 := by
    rw [linFactor]
    simp [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_single, Ne.symm hv]
  rw [h] at hc
  simp at hc

/-- A `λ`-eigenvector of `T^v` is killed by `T^v - λ`. -/
theorem act_linFactor_eq_zero {v : ℤ × ℤ} {lam : ℂ} {e : Config ℂ} (h : T v e = lam • e) :
    act (linFactor v lam) e = 0 := by
  have hz : ∀ z, e (z + v) = lam * e z := fun z => by
    have hh := congrFun h z
    rwa [T_apply, Pi.smul_apply, smul_eq_mul] at hh
  funext z
  show act (mono v - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam) e z = 0
  rw [act_sub_left, Pi.sub_apply, act_mono, T_apply, act_single, add_zero, hz z, sub_self]

/-- The support of `T^v - λ` is `{0, v}`, for `v ≠ 0` and `λ ≠ 0`. -/
theorem supp_linFactor {v : ℤ × ℤ} (hv : v ≠ 0) {lam : ℂ} (hlam : lam ≠ 0) :
    supp (linFactor v lam) = {0, v} := by
  classical
  have hkey : ∀ w : ℤ × ℤ, (linFactor v lam).coeff w
      = (if v = w then (1 : ℂ) else 0) - (if (0 : ℤ × ℤ) = w then lam else 0) := by
    intro w
    show (AddMonoidAlgebra.coeff (mono v - AddMonoidAlgebra.single (0 : ℤ × ℤ) lam)) w = _
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_mono,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
  ext w
  rw [mem_supp, hkey]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_cases h0 : (0 : ℤ × ℤ) = w
  · subst h0
    simp [hv, hlam]
  · by_cases hvw : v = w
    · subst hvw
      simp [h0]
    · simp [h0, hvw, Ne.symm h0, Ne.symm hvw]

/-- `Newt(T^v - λ) = [0, v]` when `v ≠ 0` and `λ ≠ 0`.  Used for (2.3). -/
theorem newt_linFactor {v : ℤ × ℤ} (hv : v ≠ 0) {lam : ℂ} (hlam : lam ≠ 0) :
    newt (linFactor v lam) = segment ℝ 0 (toReal v) := by
  classical
  rw [newt_eq_conv, supp_linFactor hv hlam, Conv, Finset.coe_insert, Finset.coe_singleton,
    Set.image_pair, show toReal (0 : ℤ × ℤ) = (0 : ℝ × ℝ) from by simp [toReal],
    convexHull_pair]

/-! #### Minkowski sums of collinear segments

The Newton polygon of `Aᵢ` is a Minkowski sum of `dᵢ` copies of `[0, vᵢ]`, which is the segment
`[0, dᵢ vᵢ]`.  Mathlib has no such lemma, so it is proved here from the definition of
`segment`. -/

/-- Membership in the segment `[0, c w]` along a fixed direction `w`, for `c ≥ 0`. -/
theorem mem_segment_smul_iff {w : ℝ × ℝ} {c : ℝ} (hc : 0 ≤ c) {x : ℝ × ℝ} :
    x ∈ segment ℝ 0 (c • w) ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ c ∧ x = t • w := by
  constructor
  · rintro ⟨α, β, hα, hβ, hαβ, rfl⟩
    refine ⟨β * c, mul_nonneg hβ hc, ?_, ?_⟩
    · have h1 : β = 1 - α := by linarith
      rw [h1, sub_mul, one_mul]
      linarith [mul_nonneg hα hc]
    · rw [smul_zero, zero_add, smul_smul]
  · rintro ⟨t, ht0, htc, rfl⟩
    rcases hc.eq_or_lt with rfl | hcpos
    · have hzero : t = 0 := le_antisymm htc ht0
      exact ⟨1, 0, zero_le_one, le_refl 0, by ring, by simp [hzero]⟩
    · refine ⟨1 - t / c, t / c, sub_nonneg.mpr ((div_le_one hcpos).mpr htc),
        div_nonneg ht0 hcpos.le, by ring, ?_⟩
      rw [smul_zero, zero_add, smul_smul]
      congr 1
      field_simp

/-- Minkowski sum of two collinear segments based at the origin. -/
theorem segment_smul_add {w : ℝ × ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    segment ℝ 0 (a • w) + segment ℝ 0 (b • w) = segment ℝ 0 ((a + b) • w) := by
  ext x
  constructor
  · rintro ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    obtain ⟨t₁, ht₁0, ht₁a, rfl⟩ := (mem_segment_smul_iff ha).mp hx₁
    obtain ⟨t₂, ht₂0, ht₂b, rfl⟩ := (mem_segment_smul_iff hb).mp hx₂
    exact (mem_segment_smul_iff (add_nonneg ha hb)).mpr
      ⟨t₁ + t₂, by linarith, by linarith, (add_smul t₁ t₂ w).symm⟩
  · intro hx
    obtain ⟨t, ht0, htab, rfl⟩ := (mem_segment_smul_iff (add_nonneg ha hb)).mp hx
    have h1 : (min t a) • w ∈ segment ℝ 0 (a • w) :=
      (mem_segment_smul_iff ha).mpr ⟨min t a, le_min ht0 ha, min_le_right _ _, rfl⟩
    have h2 : (t - min t a) • w ∈ segment ℝ 0 (b • w) := by
      refine (mem_segment_smul_iff hb).mpr ⟨t - min t a, by simp [sub_nonneg], ?_, rfl⟩
      rcases le_total t a with h | h
      · rw [min_eq_left h]; simpa using hb
      · rw [min_eq_right h]; linarith
    have hsum := Set.add_mem_add h1 h2
    rwa [← add_smul, show min t a + (t - min t a) = t from by ring] at hsum

/-- The Minkowski sum of `|s|` copies of `[0, w]` is `[0, |s| w]`. -/
theorem sum_const_segment {ι : Type*} (s : Finset ι) (w : ℝ × ℝ) :
    ∑ _j ∈ s, segment ℝ 0 w = segment ℝ 0 ((s.card : ℝ) • w) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_smul, segment_same,
      Set.singleton_zero]
  | cons j s hj ih =>
    rw [Finset.sum_cons, ih, show segment ℝ 0 w = segment ℝ 0 ((1 : ℝ) • w) from by rw [one_smul],
      segment_smul_add zero_le_one (Nat.cast_nonneg _), Finset.card_cons]
    congr 1
    push_cast
    ring_nf

/-- `toReal` intertwines the `ℤ`-action on the lattice with the `ℝ`-action on the plane. -/
theorem toReal_natCast_smul (d : ℕ) (v : ℤ × ℤ) :
    toReal ((d : ℤ) • v) = (d : ℝ) • toReal v := by
  refine Prod.ext ?_ ?_ <;> simp [toReal]

/-! #### Divisibility by a linear factor

Three ingredients feed **Lemma 2.3**: the geometric-series identity making `T^v - λ` divide
`T^{s v} - λ^s`, the resulting criterion "all `λ`-slices of `f` vanish ⟹ `(T^v - λ) ∣ f`", and a
purely combinatorial extremal argument. -/

/-- `f` is the sum of its monomials. -/
theorem sum_single_coeff (f : LaurentTwo ℂ) :
    (f.coeff.sum fun z c => (AddMonoidAlgebra.single z c : LaurentTwo ℂ)) = f := by
  apply AddMonoidAlgebra.coeff_injective
  rw [AddMonoidAlgebra.coeff_finsuppSum]
  simp only [AddMonoidAlgebra.coeff_single]
  exact Finsupp.sum_single f.coeff

/-- `T^v - λ` divides `T^{k v} - λ^k` for every natural `k` (geometric series). -/
theorem linFactor_dvd_mono_sub_pow (v : ℤ × ℤ) (lam : ℂ) (k : ℕ) :
    linFactor v lam ∣ mono ((k : ℤ) • v) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ k) := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, zero_smul, pow_zero, mono_zero, ← AddMonoidAlgebra.one_def, sub_self]
    exact dvd_zero _
  | succ k ih =>
    have e1 : (mono v : LaurentTwo ℂ) * mono ((k : ℤ) • v) = mono (((k + 1 : ℕ) : ℤ) • v) := by
      rw [mono_mul_mono]
      congr 1
      push_cast
      rw [add_smul, one_smul]
      abel
    have e2 : (mono v : LaurentTwo ℂ) * AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ k)
        = AddMonoidAlgebra.single v (lam ^ k) := by
      rw [mono, AddMonoidAlgebra.single_mul_single, add_zero, one_mul]
    have e3 : (AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ k) : LaurentTwo ℂ) * mono v
        = AddMonoidAlgebra.single v (lam ^ k) := by
      rw [mono, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    have e4 : (AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ k) : LaurentTwo ℂ)
          * AddMonoidAlgebra.single (0 : ℤ × ℤ) lam
        = AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ (k + 1)) := by
      rw [AddMonoidAlgebra.single_mul_single, add_zero, ← pow_succ]
    have hstep : mono (((k + 1 : ℕ) : ℤ) • v)
          - AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ (k + 1))
        = mono v * (mono ((k : ℤ) • v) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ k))
          + AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ k) * linFactor v lam := by
      rw [mul_sub, linFactor, mul_sub, e1, e2, e3, e4]
      abel
    rw [hstep]
    exact dvd_add (ih.mul_left _) (dvd_mul_left _ _)

/-- `T^v - λ` divides `T^{s v} - λ^s` for every integer `s`, when `λ ≠ 0`. -/
theorem linFactor_dvd_mono_sub_zpow {v : ℤ × ℤ} {lam : ℂ} (hlam : lam ≠ 0) (s : ℤ) :
    linFactor v lam ∣ mono (s • v) - AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ s) := by
  have hcancel : ∀ {a b w : LaurentTwo ℂ}, IsUnit w → a ∣ w * b → a ∣ b := by
    rintro a b w hw h
    obtain ⟨W, rfl⟩ := hw
    have hb : b = (↑W⁻¹ : LaurentTwo ℂ) * ((W : LaurentTwo ℂ) * b) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [hb]
    exact h.mul_left _
  rcases le_or_gt 0 s with hs | hs
  · lift s to ℕ using hs with k
    rw [zpow_natCast]
    exact linFactor_dvd_mono_sub_pow v lam k
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, s = -(k : ℤ) := ⟨s.natAbs, by omega⟩
    have hcc : lam ^ k * lam ^ (-(k : ℤ)) = 1 := by
      rw [← zpow_natCast lam k, ← zpow_add₀ hlam, add_neg_cancel, zpow_zero]
    have hmm : (mono ((k : ℤ) • v) : LaurentTwo ℂ) * mono ((-(k : ℤ)) • v) = 1 := by
      rw [mono_mul_mono, ← add_smul, add_neg_cancel, zero_smul, mono_zero]
    refine hcancel ((isUnit_mono ((k : ℤ) • v)).mul (isUnit_single 0 (pow_ne_zero k hlam))) ?_
    have ht1 : (mono ((k : ℤ) • v) : LaurentTwo ℂ)
          * AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ k) * mono ((-(k : ℤ)) • v)
        = AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ k) := by
      rw [mul_right_comm, hmm, one_mul]
    have ht2 : (mono ((k : ℤ) • v) : LaurentTwo ℂ)
          * AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ k)
          * AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ (-(k : ℤ)))
        = mono ((k : ℤ) • v) := by
      rw [mul_assoc, AddMonoidAlgebra.single_mul_single, add_zero, hcc,
        ← AddMonoidAlgebra.one_def, mul_one]
    rw [mul_sub, ht1, ht2, ← neg_sub]
    exact dvd_neg.mpr (linFactor_dvd_mono_sub_pow v lam k)

/-- The additive map `ℂ[Y^±] → ℂ[T₁^±, T₂^±]`, `Y^β ↦ T^{β u}`, on monomials. -/
theorem liftSingle_apply (u : ℤ × ℤ) (b : ℤ) (c : ℂ) :
    (Finsupp.liftAddHom fun b : ℤ => AddMonoidAlgebra.singleAddHom (R := ℂ) (b • u))
        (Finsupp.single b c)
      = AddMonoidAlgebra.single (b • u) c :=
  Finsupp.liftAddHom_apply_single _ b c

/-- If every `λ`-slice of `f` vanishes, i.e. `f(λ, Y) = 0`, then `(T^v - λ) ∣ f`.
This is the algebraic half of Lemma 2.3. -/
theorem linFactor_dvd_of_uniPart_eq_zero {v u : ℤ × ℤ} (hdet : det v u = 1) {lam : ℂ}
    (hlam : lam ≠ 0) {f : LaurentTwo ℂ} (h : uniPart f v u lam = 0) :
    linFactor v lam ∣ f := by
  classical
  -- Push `f(λ, Y) = 0` forward along `Y^β ↦ T^{β u}`.
  have hzero : (f.coeff.sum fun z c =>
      (AddMonoidAlgebra.single ((det v z) • u) (c * lam ^ (det z u)) : LaurentTwo ℂ)) = 0 := by
    have hh := congrArg
      (Finsupp.liftAddHom fun b : ℤ => AddMonoidAlgebra.singleAddHom (R := ℂ) (b • u)) h
    rw [map_zero, uniPart, map_finsuppSum] at hh
    simpa only [liftSingle_apply] using hh
  have hsplit : f = f.coeff.sum fun z c =>
      ((AddMonoidAlgebra.single z c : LaurentTwo ℂ)
        - AddMonoidAlgebra.single ((det v z) • u) (c * lam ^ (det z u))) := by
    rw [Finsupp.sum_sub, hzero, sub_zero, sum_single_coeff]
  rw [hsplit, Finsupp.sum]
  refine Finset.dvd_sum fun z _ => ?_
  have hz2 : (det v z) • u + (det z u) • v = z := by
    conv_rhs => rw [eq_smul_add_smul hdet z]
    abel
  have e1 : (AddMonoidAlgebra.single ((det v z) • u) (f.coeff z) : LaurentTwo ℂ)
        * mono ((det z u) • v) = AddMonoidAlgebra.single z (f.coeff z) := by
    rw [mono, AddMonoidAlgebra.single_mul_single, mul_one, hz2]
  have e2 : (AddMonoidAlgebra.single ((det v z) • u) (f.coeff z) : LaurentTwo ℂ)
        * AddMonoidAlgebra.single (0 : ℤ × ℤ) (lam ^ (det z u))
      = AddMonoidAlgebra.single ((det v z) • u) (f.coeff z * lam ^ (det z u)) := by
    rw [AddMonoidAlgebra.single_mul_single, add_zero]
  rw [← e1, ← e2, ← mul_sub]
  exact (linFactor_dvd_mono_sub_zpow hlam (det z u)).mul_left _

/-- The combinatorial heart of Lemma 2.3: a convolution relation `∑_β q_β R(t + β) = 0` valid for
every `t`, with `R` not identically zero but vanishing on a half-line, forces `q = 0`.  Evaluate
at the extreme point of the support of `R` against the opposite extreme of `supp q`. -/
theorem eq_zero_of_conv_eq_zero {q : ℤ →₀ ℂ} {R : ℤ → ℂ} (hR : ∃ t, R t ≠ 0)
    (hbdd : (∃ c : ℤ, ∀ t : ℤ, c < t → R t = 0) ∨ (∃ c : ℤ, ∀ t : ℤ, t < c → R t = 0))
    (hrel : ∀ t : ℤ, (q.sum fun b g => g * R (t + b)) = 0) : q = 0 := by
  classical
  by_contra hq
  have hne : q.support.Nonempty := Finsupp.support_nonempty_iff.mpr hq
  rcases hbdd with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨t₀, ht₀, hmax⟩ := Int.exists_greatest_of_bdd
      ⟨c, fun z hz => not_lt.mp fun hlt => hz (hc z hlt)⟩ hR
    have hb₀mem : q.support.min' hne ∈ q.support := q.support.min'_mem hne
    have hother : ∀ b ∈ q.support, b ≠ q.support.min' hne →
        q b * R (t₀ - q.support.min' hne + b) = 0 := by
      intro b hb hbne
      have hlt : q.support.min' hne < b :=
        lt_of_le_of_ne (q.support.min'_le b hb) (Ne.symm hbne)
      have hzero : R (t₀ - q.support.min' hne + b) = 0 := by
        by_contra hne0
        have := hmax _ hne0
        omega
      rw [hzero, mul_zero]
    have key := hrel (t₀ - q.support.min' hne)
    rw [Finsupp.sum, Finset.sum_eq_single_of_mem _ hb₀mem hother,
      show t₀ - q.support.min' hne + q.support.min' hne = t₀ from by ring] at key
    exact (mul_ne_zero (Finsupp.mem_support_iff.mp hb₀mem) ht₀) key
  · obtain ⟨t₀, ht₀, hmin⟩ := Int.exists_least_of_bdd
      ⟨c, fun z hz => not_lt.mp fun hlt => hz (hc z hlt)⟩ hR
    have hb₀mem : q.support.max' hne ∈ q.support := q.support.max'_mem hne
    have hother : ∀ b ∈ q.support, b ≠ q.support.max' hne →
        q b * R (t₀ - q.support.max' hne + b) = 0 := by
      intro b hb hbne
      have hlt : b < q.support.max' hne :=
        lt_of_le_of_ne (q.support.le_max' b hb) hbne
      have hzero : R (t₀ - q.support.max' hne + b) = 0 := by
        by_contra hne0
        have := hmin _ hne0
        omega
      rw [hzero, mul_zero]
    have key := hrel (t₀ - q.support.max' hne)
    rw [Finsupp.sum, Finset.sum_eq_single_of_mem _ hb₀mem hother,
      show t₀ - q.support.max' hne + q.support.max' hne = t₀ from by ring] at key
    exact (mul_ne_zero (Finsupp.mem_support_iff.mp hb₀mem) ht₀) key

/-! ### §2.4 One-sided vanishing -/

/-- **Lemma 2.3.**  Let `d` have period `κ v`, vanish on a half-plane `{π_v > c}` or
`{π_v < c}`, and let `λ` occur in `d`.  If `f(T) d = 0` then `(T^v - λ) ∣ f`. -/
theorem linFactor_dvd {κ : ℕ} (hκ : 0 < κ) {v u : ℤ × ℤ} (hdet : det v u = 1)
    {d : Config ℂ} (hd : T ((κ : ℤ) • v) d = d)
    (hvan : (∃ c : ℤ, ∀ z, c < pi v z → d z = 0) ∨ (∃ c : ℤ, ∀ z, pi v z < c → d z = 0))
    {lam : ℂ} (hlam : lam ∈ rootsFinset κ) (hocc : Occurs κ v lam d)
    {f : LaurentTwo ℂ} (hf : act f d = 0) :
    linFactor v lam ∣ f := by
  classical
  refine linFactor_dvd_of_uniPart_eq_zero hdet (ne_zero_of_mem_rootsFinset hlam) ?_
  -- `f(T)` kills every spectral component of `d`, because `P_λ` is itself a Laurent polynomial.
  have hz : act f (act (specProj κ v lam) d) = 0 := by
    rw [← act_specProj_comm, hf, act_zero_right]
  have hrel : ∀ t : ℤ, ((uniPart f v u lam).sum
      fun b g => g * rowCoeff κ v u d lam (t + b)) = 0 := by
    intro t
    have h0 := congrFun hz ((0 : ℤ) • v + t • u)
    rw [act_act_specProj hκ hdet f hd hlam 0 t, zpow_zero, one_mul, Pi.zero_apply] at h0
    exact h0
  -- The row `t` of `P_λ d` lies inside the line `{π_v = t}`, so one-sided vanishing of `d`
  -- becomes one-sided vanishing of `t ↦ d_t(λ)`.
  have hbdd : (∃ c : ℤ, ∀ t : ℤ, c < t → rowCoeff κ v u d lam t = 0)
      ∨ (∃ c : ℤ, ∀ t : ℤ, t < c → rowCoeff κ v u d lam t = 0) := by
    rcases hvan with ⟨c, hc⟩ | ⟨c, hc⟩
    · refine Or.inl ⟨c, fun t ht => ?_⟩
      rw [rowCoeff]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => ?_)
      rw [hc _ (by rw [pi_smul_add_smul hdet]; exact ht), mul_zero]
    · refine Or.inr ⟨c, fun t ht => ?_⟩
      rw [rowCoeff]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => ?_)
      rw [hc _ (by rw [pi_smul_add_smul hdet]; exact ht), mul_zero]
  exact eq_zero_of_conv_eq_zero ((occurs_iff_exists_row hκ hdet hd hlam).mp hocc) hbdd hrel

/-- `T^v - λ` is prime for `λ ≠ 0` and `v` primitive: modulo it,
`ℂ[X^±, Y^±]/(X - λ) ≅ ℂ[Y^±]` is a domain.  Paper Lemma 2.4 (d). -/
theorem prime_linFactor {v : ℤ × ℤ} (hv : Primitive v) {lam : ℂ} (hlam : lam ≠ 0) :
    Prime (linFactor v lam) :=
  prime_mono_sub_const hv hlam

/-- Linear factors from non-parallel directions are non-associate.  Paper Lemma 2.4 (d). -/
theorem not_associated_linFactor_of_det_ne_zero {v w : ℤ × ℤ} (h : det v w ≠ 0)
    {lam mu : ℂ} (hlam : lam ≠ 0) (hmu : mu ≠ 0) :
    ¬ Associated (linFactor v lam) (linFactor w mu) :=
  not_associated_of_det_ne_zero h hlam hmu

/-- Distinct linear factors from the same direction are non-associate.  Paper Lemma 2.4 (d). -/
theorem not_associated_linFactor_of_ne {v : ℤ × ℤ} (hv : v ≠ 0) {lam mu : ℂ} (hlam : lam ≠ 0)
    (hmu : mu ≠ 0) (h : lam ≠ mu) : ¬ Associated (linFactor v lam) (linFactor v mu) :=
  not_associated_of_ne hv hlam hmu h

/-! #### Colour indicators: congruence and periodicity -/

/-- `I_a` takes the value `1` at points of colour `a`. -/
theorem ind_eq_one {α : Type*} {θ : Config α} {a : α} {z : ℤ × ℤ} (h : θ z = a) :
    ind θ a z = 1 := if_pos h

/-- Two configurations agreeing at `z` have the same indicators at `z`. -/
theorem ind_congr {α : Type*} {θ₁ θ₂ : Config α} (a : α) {z : ℤ × ℤ} (h : θ₁ z = θ₂ z) :
    ind θ₁ a z = ind θ₂ a z := by
  by_cases hb : θ₂ z = a
  · rw [ind_eq_one (h.trans hb), ind_eq_one hb]
  · rw [ind_eq_zero fun hc => hb (h.symm.trans hc), ind_eq_zero hb]

/-- Every period of `θ` is a period of each of its colour indicators. -/
theorem mem_Per_ind {α : Type*} {θ : Config α} {u : ℤ × ℤ} (hu : u ∈ Per θ) (a : α) :
    u ∈ Per (ind θ a) := by
  rw [mem_Per_iff]
  funext z
  show ind θ a (z + u) = ind θ a z
  have h : θ (z + u) = θ z := Per.apply hu z
  by_cases hb : θ z = a
  · rw [ind_eq_one (h.trans hb), ind_eq_one hb]
  · rw [ind_eq_zero fun hc => hb (h.symm.trans hc), ind_eq_zero hb]

/-- `∑_a w(a) I_a(z) = w(θ z)`: the indicators resolve any function of the colour. -/
theorem sum_mul_ind {α : Type*} [Fintype α] (w : α → ℂ) (θ : Config α) (z : ℤ × ℤ) :
    ∑ a : α, w a * ind θ a z = w (θ z) := by
  classical
  rw [Finset.sum_eq_single_of_mem (θ z) (Finset.mem_univ _)
    (fun b _ hb => by rw [ind_eq_zero (Ne.symm hb), mul_zero]), ind_self, mul_one]

/-! #### Linearity and genericity

Two auxiliary facts feeding the encoding of **Lemma 2.2**: a Laurent operator is linear in the
configuration, and a finite family of non-trivial linear functionals on `ℂ^α` can be avoided
simultaneously along a curve of Vandermonde type `t ↦ (t^{e a})_a`. -/

/-- `f(T)` is linear in the configuration. -/
theorem act_sum_scalar {R ι : Type*} [CommRing R] [Fintype ι] (f : LaurentTwo R) (c : ι → R)
    (g : ι → Config R) (z : ℤ × ℤ) :
    act f (fun y => ∑ a, c a * g a y) z = ∑ a, c a * act f (g a) z := by
  simp only [act_apply, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun u _ => by ring

/-- A genericity statement of Vandermonde type.  Given finitely many non-trivial linear
functionals `c x` on `ℂ^α` and pairwise distinct exponents `e a`, some natural number `t ≥ 2`
makes every `∑_a t^{e a} c x a` non-zero: each of these numbers is the value at `t` of a non-zero
one-variable polynomial, and a non-zero polynomial has only finitely many roots. -/
theorem exists_two_le_forall_sum_pow_ne_zero {α ι : Type*} [Fintype α] {e : α → ℕ}
    (he : Function.Injective e) (s : Finset ι) (c : ι → α → ℂ)
    (hc : ∀ x ∈ s, ∃ a, c x a ≠ 0) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ x ∈ s, (∑ a, ((t : ℂ) ^ e a) * c x a) ≠ 0 := by
  classical
  -- Package the functionals as one-variable polynomials `Q x = ∑_a c x a X^{e a}`.
  obtain ⟨Q, heval, hcoeff⟩ : ∃ Q : ι → Polynomial ℂ,
      (∀ (x : ι) (n : ℕ), (Q x).eval (n : ℂ) = ∑ a, ((n : ℂ) ^ e a) * c x a) ∧
      (∀ (x : ι) (a : α), (Q x).coeff (e a) = c x a) := by
    refine ⟨fun x => ∑ a, Polynomial.C (c x a) * Polynomial.X ^ e a, ?_, ?_⟩
    · intro x n
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    · intro x a
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)
        fun b _ hb => by rw [if_neg fun h => hb (he h).symm, mul_zero]]
      simp
  have hQne : ∀ x ∈ s, Q x ≠ 0 := by
    intro x hx h0
    obtain ⟨a₀, ha₀⟩ := hc x hx
    exact ha₀ (by rw [← hcoeff x a₀, h0, Polynomial.coeff_zero])
  -- Only finitely many natural numbers are roots of the product.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n : ℕ, (∏ x ∈ s, Q x).eval (n : ℂ) = 0 → n ≤ M := by
    have hfin : {w : ℂ | (∏ x ∈ s, Q x).IsRoot w}.Finite :=
      Polynomial.finite_setOfPred_isRoot (Finset.prod_ne_zero_iff.mpr hQne)
    refine ⟨(hfin.toFinset.preimage (fun n : ℕ => (n : ℂ))
      (Set.injOn_of_injective Nat.cast_injective)).sup id, fun n hn => ?_⟩
    refine Finset.le_sup (f := id) ?_
    rw [Finset.mem_preimage, Set.Finite.mem_toFinset]
    exact hn
  refine ⟨max 2 (M + 1), le_max_left _ _, fun x hx hzero => ?_⟩
  have hbad : (∏ b ∈ s, Q b).eval ((max 2 (M + 1) : ℕ) : ℂ) = 0 := by
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hx (by rw [heval]; exact hzero)
  have h1 := hM _ hbad
  have h2 : M + 1 ≤ max 2 (M + 1) := le_max_right _ _
  omega

/-! ### Laurent polynomials supported in a finite window

An affine relation `∑_{s ∈ S} c_s ψ(u + s) = c₀` of §2.6 is recorded by the Laurent polynomial
`f = ∑_{s ∈ S} c_s T^s`.  Packaging `c ↦ f` as a *linear* map makes linear combinations of
relations correspond to linear combinations of polynomials, which is what the dimension count
in Lemma 2.5 needs. -/

/-- `c ↦ ∑_{s ∈ W} c_s T^s`, linear in the coefficient vector `c`.  Paper §2.6. -/
noncomputable def windowPoly (R : Type*) [CommRing R] (W : Finset (ℤ × ℤ)) :
    ({ x // x ∈ W } → R) →ₗ[R] LaurentTwo R :=
  Fintype.linearCombination R fun s : { x // x ∈ W } => mono (s : ℤ × ℤ)

theorem windowPoly_apply {R : Type*} [CommRing R] (W : Finset (ℤ × ℤ))
    (c : { x // x ∈ W } → R) :
    windowPoly R W c = ∑ s : { x // x ∈ W }, AddMonoidAlgebra.single (s : ℤ × ℤ) (c s) := by
  rw [windowPoly, Fintype.linearCombination_apply]
  exact Finset.sum_congr rfl fun s _ => by simp [mono]

@[simp] theorem coeff_windowPoly {R : Type*} [CommRing R] (W : Finset (ℤ × ℤ))
    (c : { x // x ∈ W } → R) (s : { x // x ∈ W }) :
    (windowPoly R W c).coeff (s : ℤ × ℤ) = c s := by
  classical
  rw [windowPoly_apply, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single s]
  · rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · intro t _ hts
    have hne : (t : ℤ × ℤ) ≠ (s : ℤ × ℤ) := fun h => hts (Subtype.ext h)
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hne.symm]
  · intro h; exact absurd (Finset.mem_univ s) h

theorem coeff_windowPoly_of_notMem {R : Type*} [CommRing R] {W : Finset (ℤ × ℤ)}
    (c : { x // x ∈ W } → R) {t : ℤ × ℤ} (ht : t ∉ W) : (windowPoly R W c).coeff t = 0 := by
  classical
  rw [windowPoly_apply, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hne : (s : ℤ × ℤ) ≠ t := fun h => ht (h ▸ s.2)
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hne.symm]

theorem supp_windowPoly_subset {R : Type*} [CommRing R] (W : Finset (ℤ × ℤ))
    (c : { x // x ∈ W } → R) : supp (windowPoly R W c) ⊆ W := by
  intro t ht
  by_contra h
  exact (mem_supp.mp ht) (coeff_windowPoly_of_notMem c h)

theorem act_windowPoly {R : Type*} [CommRing R] (W : Finset (ℤ × ℤ))
    (c : { x // x ∈ W } → R) (g : Config R) (z : ℤ × ℤ) :
    act (windowPoly R W c) g z = ∑ s : { x // x ∈ W }, c s * g (z + (s : ℤ × ℤ)) := by
  rw [windowPoly_apply, act_sum_apply]
  exact Finset.sum_congr rfl fun s _ => act_single _ _ _ _

/-- `Conv` is monotone.  Paper §0.2. -/
theorem Conv_mono {W W' : Finset (ℤ × ℤ)} (h : W ⊆ W') : Conv W ⊆ Conv W' :=
  convexHull_mono (Set.image_mono (Finset.coe_subset.mpr h))

namespace StarConfig

variable {p m : ℕ} [Fact p.Prime] (S : StarConfig p m)

/-! ### §2.1 One-sided limits and the doubly periodic fields `Gᵢ^{ε,δ}`

`ε : Bool` encodes the sign `±` (`true = +`) and `δ : Bool` the tail `L`/`R`
(`true = R`). -/

/-- The tail of component `j` selected by the limit `σᵢ^ε`.  Paper (2.0): for `ε = +` it is
`R j` when `π_j(v i) > 0` and `L j` when `π_j(v i) < 0`; for `ε = -` the opposite. -/
def tailSel (i j : Fin m) (ε : Bool) : Config (ZMod p) :=
  if decide (0 < pi (S.v j) (S.v i)) = ε then S.R j else S.L j

/-- The doubly periodic background `Bᵢ^ε = ∑_{j ≠ i} τ_j`.  Paper §2.1. -/
def bg (i : Fin m) (ε : Bool) : Config (ZMod p) :=
  fun z => ∑ j ∈ univ.erase i, S.tailSel i j ε z

/-- The one-sided limit `σᵢ^ε = Fᵢ + Bᵢ^ε = lim_{n → ±∞} T^{n Hᵢ} θ`.  Paper §2.1. -/
def sigma (i : Fin m) (ε : Bool) : Config (ZMod p) :=
  fun z => S.F i z + S.bg i ε z

/-- The doubly periodic field `Gᵢ^{ε,δ} = τᵢ^δ + Bᵢ^ε`, where `τᵢ^δ` is `L i` (`δ = false`)
or `R i` (`δ = true`).  Paper §2.1. -/
def Gfield (i : Fin m) (ε δ : Bool) : Config (ZMod p) :=
  fun z => (if δ then S.R i z else S.L i z) + S.bg i ε z

omit [Fact p.Prime] in
theorem tailSel_eq_R (i j : Fin m) (ε : Bool)
    (h : decide (0 < pi (S.v j) (S.v i)) = ε) : S.tailSel i j ε = S.R j := by
  rw [tailSel, if_pos h]

omit [Fact p.Prime] in
theorem tailSel_eq_L (i j : Fin m) (ε : Bool)
    (h : decide (0 < pi (S.v j) (S.v i)) ≠ ε) : S.tailSel i j ε = S.L j := by
  rw [tailSel, if_neg h]

omit [Fact p.Prime] in
/-- Every element of `Γ` is a period of each selected tail. -/
theorem mem_Per_tailSel {u : ℤ × ℤ} (hu : u ∈ S.Gamma) (i j : Fin m) (ε : Bool) :
    u ∈ Per (S.tailSel i j ε) := by
  rw [tailSel]
  split
  · exact (S.mem_Gamma_iff.mp hu j).2
  · exact (S.mem_Gamma_iff.mp hu j).1

omit [Fact p.Prime] in
/-- Every element of `Γ` is a period of the background `Bᵢ^ε`. -/
theorem mem_Per_bg {u : ℤ × ℤ} (hu : u ∈ S.Gamma) (i : Fin m) (ε : Bool) :
    u ∈ Per (S.bg i ε) := by
  rw [mem_Per_iff]
  funext z
  show ∑ j ∈ univ.erase i, S.tailSel i j ε (z + u) = ∑ j ∈ univ.erase i, S.tailSel i j ε z
  exact Finset.sum_congr rfl fun j _ => Per.apply (S.mem_Per_tailSel hu i j ε) z

omit [Fact p.Prime] in
/-- Every element of `Γ` is a period of `Gᵢ^{ε,δ}`. -/
theorem mem_Per_Gfield {u : ℤ × ℤ} (hu : u ∈ S.Gamma) (i : Fin m) (ε δ : Bool) :
    u ∈ Per (S.Gfield i ε δ) := by
  rw [mem_Per_iff]
  funext z
  have hb : S.bg i ε (z + u) = S.bg i ε z := Per.apply (S.mem_Per_bg hu i ε) z
  have ht : (if δ then S.R i (z + u) else S.L i (z + u))
      = (if δ then S.R i z else S.L i z) := by
    cases δ with
    | false => simpa using Per.apply (S.mem_Gamma_iff.mp hu i).1 z
    | true => simpa using Per.apply (S.mem_Gamma_iff.mp hu i).2 z
  show (if δ then S.R i (z + u) else S.L i (z + u)) + S.bg i ε (z + u)
      = (if δ then S.R i z else S.L i z) + S.bg i ε z
  rw [ht, hb]

omit [Fact p.Prime] in
/-- A field admitting all of `Γ` as periods is doubly periodic, because `Γ` contains `N · ℤ²`
for some `N ≠ 0`. -/
theorem doublyPeriodic_of_Gamma_le {f : Config (ZMod p)} (h : ∀ u ∈ S.Gamma, u ∈ Per f) :
    DoublyPeriodic f := by
  obtain ⟨N, hN, hmem⟩ := S.exists_smul_mem_Gamma
  have hdet : det (N • ((1 : ℤ), (0 : ℤ))) (N • ((0 : ℤ), (1 : ℤ))) = N * N := by
    simp [det, Prod.smul_def]
  exact ⟨_, h _ (hmem ((1 : ℤ), (0 : ℤ))), _, h _ (hmem ((0 : ℤ), (1 : ℤ))),
    by rw [hdet]; exact mul_ne_zero hN hN⟩

omit [Fact p.Prime] in
theorem bg_doublyPeriodic (i : Fin m) (ε : Bool) : DoublyPeriodic (S.bg i ε) :=
  S.doublyPeriodic_of_Gamma_le fun _ hu => S.mem_Per_bg hu i ε

omit [Fact p.Prime] in
theorem Gfield_doublyPeriodic (i : Fin m) (ε δ : Bool) : DoublyPeriodic (S.Gfield i ε δ) :=
  S.doublyPeriodic_of_Gamma_le fun _ hu => S.mem_Per_Gfield hu i ε δ

omit [Fact p.Prime] in
/-- `σᵢ^ε` is the limit of `T^{n Hᵢ} θ`: on any finite window it agrees with a translate of
`θ` by an **integer multiple of `Hᵢ`**.  Paper §2.1; the refinement to multiples of `Hᵢ` is
what (4.1) needs, since `fᵢ` is only known to be `Hᵢ`-periodic. -/
theorem exists_zsmul_H_sigma (i : Fin m) (ε : Bool) (W : Finset (ℤ × ℤ)) :
    ∃ t : ℤ, ∀ w ∈ W, S.sigma i ε w = S.θ (t • S.H i + w) := by
  classical
  -- A sign `s` such that translating by `s · n · Hᵢ` pushes every other component `j`
  -- into the tail selected by `tailSel i j ε`.
  obtain ⟨s, hsgn⟩ : ∃ s : ℤ, ∀ j : Fin m, j ≠ i →
      (1 ≤ s * pi (S.v j) (S.v i) ∧ S.tailSel i j ε = S.R j) ∨
      (s * pi (S.v j) (S.v i) ≤ -1 ∧ S.tailSel i j ε = S.L j) := by
    cases ε with
    | true =>
      refine ⟨1, fun j hji => ?_⟩
      have hd : pi (S.v j) (S.v i) ≠ 0 := S.nonparallel j i hji
      rcases lt_or_gt_of_ne hd with hlt | hgt
      · have hnp : ¬ (0 < pi (S.v j) (S.v i)) := by omega
        exact Or.inr ⟨by omega,
          S.tailSel_eq_L i j true (by rw [decide_eq_false hnp]; simp)⟩
      · exact Or.inl ⟨by omega, S.tailSel_eq_R i j true (decide_eq_true hgt)⟩
    | false =>
      refine ⟨-1, fun j hji => ?_⟩
      have hd : pi (S.v j) (S.v i) ≠ 0 := S.nonparallel j i hji
      rcases lt_or_gt_of_ne hd with hlt | hgt
      · have hnp : ¬ (0 < pi (S.v j) (S.v i)) := by omega
        exact Or.inl ⟨by omega, S.tailSel_eq_R i j false (decide_eq_false hnp)⟩
      · exact Or.inr ⟨by omega,
          S.tailSel_eq_L i j false (by rw [decide_eq_true hgt]; simp)⟩
  -- A bound `B` dominating all the thresholds `ℓ_j, r_j` and all the window coordinates.
  obtain ⟨B, hB0, hrj, hellj, hwj⟩ : ∃ B : ℤ, 0 ≤ B ∧ (∀ j : Fin m, S.r j ≤ B) ∧
      (∀ j : Fin m, -B ≤ S.ell j) ∧ (∀ (j : Fin m), ∀ t ∈ W, |pi (S.v j) t| ≤ B) := by
    have hz1 : (0:ℤ) ≤ ∑ k : Fin m, (|S.r k| + |S.ell k|) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hz2 : (0:ℤ) ≤ ∑ k : Fin m, ∑ t ∈ W, |pi (S.v k) t| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨(∑ k : Fin m, (|S.r k| + |S.ell k|)) + ∑ k : Fin m, ∑ t ∈ W, |pi (S.v k) t|,
      by linarith, fun j => ?_, fun j => ?_, fun j t ht => ?_⟩
    · have h1 : |S.r j| + |S.ell j| ≤ ∑ k : Fin m, (|S.r k| + |S.ell k|) :=
        Finset.single_le_sum (f := fun k : Fin m => |S.r k| + |S.ell k|)
          (fun k _ => by positivity) (Finset.mem_univ j)
      have h2 := le_abs_self (S.r j)
      have h3 := abs_nonneg (S.ell j)
      linarith
    · have h1 : |S.r j| + |S.ell j| ≤ ∑ k : Fin m, (|S.r k| + |S.ell k|) :=
        Finset.single_le_sum (f := fun k : Fin m => |S.r k| + |S.ell k|)
          (fun k _ => by positivity) (Finset.mem_univ j)
      have h2 := neg_abs_le (S.ell j)
      have h3 := abs_nonneg (S.r j)
      linarith
    · have h1 : |pi (S.v j) t| ≤ ∑ t' ∈ W, |pi (S.v j) t'| :=
        Finset.single_le_sum (f := fun t' => |pi (S.v j) t'|) (fun _ _ => abs_nonneg _) ht
      have h2 : (∑ t' ∈ W, |pi (S.v j) t'|) ≤ ∑ k : Fin m, ∑ t' ∈ W, |pi (S.v k) t'| :=
        Finset.single_le_sum (f := fun k : Fin m => ∑ t' ∈ W, |pi (S.v k) t'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      linarith
  set n : ℤ := 2 * B + 1 with hn
  have hn0 : (0:ℤ) ≤ n := by rw [hn]; linarith
  refine ⟨s * n, fun w hw => ?_⟩
  have hcomm : (s * n) • S.H i + w = w + (s * n) • S.H i := add_comm _ _
  have hFi : S.F i ((s * n) • S.H i + w) = S.F i w := by
    rw [hcomm]
    exact Per.apply (AddSubgroup.zsmul_mem _ (S.H_mem_Per_F i) (s * n)) w
  have hkey : ∀ j ∈ univ.erase i, S.F j ((s * n) • S.H i + w) = S.tailSel i j ε w := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hκ : (1:ℤ) ≤ (S.kappa i : ℤ) := by exact_mod_cast S.kappa_pos i
    have hcj : pi (S.v j) (S.H i) = (S.kappa i : ℤ) * pi (S.v j) (S.v i) := by
      rw [H_eq, pi_smul]
    have hupi : pi (S.v j) ((s * n) • S.H i + w)
        = n * (s * pi (S.v j) (S.H i)) + pi (S.v j) w := by
      rw [pi_add, pi_smul]; ring
    have hw1 : -B ≤ pi (S.v j) w := by
      have h := neg_abs_le (pi (S.v j) w); have h' := hwj j w hw; linarith
    have hw2 : pi (S.v j) w ≤ B := by
      have h := le_abs_self (pi (S.v j) w); have h' := hwj j w hw; linarith
    have hR : 1 ≤ s * pi (S.v j) (S.H i) → S.F j ((s * n) • S.H i + w) = S.R j w := by
      intro hpos
      have h1 : n ≤ n * (s * pi (S.v j) (S.H i)) := le_mul_of_one_le_right hn0 hpos
      have hbig : S.r j < pi (S.v j) ((s * n) • S.H i + w) := by
        rw [hupi]; have := hrj j; linarith
      rw [S.S3_R j _ hbig, hcomm]
      exact Per.apply (AddSubgroup.zsmul_mem _ (S.H_mem_Per_R i j) (s * n)) w
    have hL : s * pi (S.v j) (S.H i) ≤ -1 → S.F j ((s * n) • S.H i + w) = S.L j w := by
      intro hneg
      have h1 : n * (s * pi (S.v j) (S.H i)) ≤ -n := by
        have h := mul_le_mul_of_nonneg_left hneg hn0; linarith
      have hsmall : pi (S.v j) ((s * n) • S.H i + w) < S.ell j := by
        rw [hupi]; have := hellj j; linarith
      rw [S.S3_L j _ hsmall, hcomm]
      exact Per.apply (AddSubgroup.zsmul_mem _ (S.H_mem_Per_L i j) (s * n)) w
    rcases hsgn j hji with ⟨hpos, htail⟩ | ⟨hneg, htail⟩
    · rw [hR (by rw [hcj]; nlinarith), htail]
    · rw [hL (by rw [hcj]; nlinarith), htail]
  show S.F i w + S.bg i ε w = S.θ ((s * n) • S.H i + w)
  rw [θ_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hFi]
  exact congrArg _ (Finset.sum_congr rfl hkey).symm

omit [Fact p.Prime] in
/-- `σᵢ^ε` is the limit of `T^{n Hᵢ} θ`, hence lies in the orbit closure.  Paper §2.1. -/
theorem sigma_mem_orbitClosure (i : Fin m) (ε : Bool) : S.sigma i ε ∈ orbitClosure S.θ :=
  fun W =>
    let h := S.exists_zsmul_H_sigma i ε W
    ⟨h.choose • S.H i, h.choose_spec⟩

omit [Fact p.Prime] in
/-- `Gᵢ^{ε,δ}` lies in the orbit closure: translate `σᵢ^ε` far along `±uᵢ`.  Paper §2.1. -/
theorem Gfield_mem_orbitClosure (i : Fin m) (ε δ : Bool) :
    S.Gfield i ε δ ∈ orbitClosure S.θ := by
  classical
  refine orbitClosure_closed fun W => ?_
  -- `d ∈ Γ` with `πᵢ(d) ≥ 1`: a `Γ`-multiple of a dual vector to `vᵢ`.
  obtain ⟨ui, hui⟩ := (S.primitive i).exists_dual
  obtain ⟨N, hN, hNmem⟩ := S.exists_smul_mem_Gamma
  set d : ℤ × ℤ := (N.natAbs : ℤ) • ui with hd
  have hdmem : d ∈ S.Gamma := by
    rcases Int.natAbs_eq N with h | h
    · rw [hd, ← h]; exact hNmem ui
    · rw [hd, show ((N.natAbs : ℤ)) = -N by omega, neg_smul]
      exact AddSubgroup.neg_mem _ (hNmem ui)
  have hdpi : pi (S.v i) d = (N.natAbs : ℤ) := by
    rw [hd, pi_smul, show pi (S.v i) ui = 1 from hui, mul_one]
  have hdpos : (1:ℤ) ≤ pi (S.v i) d := by
    rw [hdpi]; exact_mod_cast Int.natAbs_pos.mpr hN
  -- A bound `B` dominating `ℓᵢ`, `rᵢ` and the window coordinates.
  obtain ⟨B, hB0, hri, helli, hwi⟩ : ∃ B : ℤ, 0 ≤ B ∧ S.r i ≤ B ∧ -B ≤ S.ell i ∧
      ∀ t ∈ W, |pi (S.v i) t| ≤ B := by
    have hs : (0:ℤ) ≤ ∑ t ∈ W, |pi (S.v i) t| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨|S.r i| + |S.ell i| + ∑ t ∈ W, |pi (S.v i) t|, by positivity, ?_, ?_, fun t ht => ?_⟩
    · have h1 := le_abs_self (S.r i); have h2 := abs_nonneg (S.ell i); linarith
    · have h1 := neg_abs_le (S.ell i); have h2 := abs_nonneg (S.r i); linarith
    · have h1 := Finset.single_le_sum (f := fun t' => |pi (S.v i) t'|)
        (fun _ _ => abs_nonneg _) ht
      have h2 := abs_nonneg (S.r i); have h3 := abs_nonneg (S.ell i); linarith
  -- Translating by `k • d` pushes the whole window into the `δ`-tail of component `i`.
  obtain ⟨k, hkBig⟩ : ∃ k : ℤ, ∀ t : ℤ × ℤ, |pi (S.v i) t| ≤ B →
      (if δ then S.R i (t + k • d) else S.L i (t + k • d)) = S.F i (t + k • d) := by
    have h1 : (2 * B + 1 : ℤ) ≤ (2 * B + 1) * pi (S.v i) d :=
      le_mul_of_one_le_right (by linarith) hdpos
    cases δ with
    | true =>
      refine ⟨2 * B + 1, fun t ht => ?_⟩
      have ht1 : -B ≤ pi (S.v i) t := by have := neg_abs_le (pi (S.v i) t); linarith
      have hbig : S.r i < pi (S.v i) (t + (2 * B + 1 : ℤ) • d) := by
        rw [pi_add, pi_smul]; linarith
      simpa using (S.S3_R i _ hbig).symm
    | false =>
      refine ⟨-(2 * B + 1), fun t ht => ?_⟩
      have ht2 : pi (S.v i) t ≤ B := by have := le_abs_self (pi (S.v i) t); linarith
      have hsmall : pi (S.v i) (t + (-(2 * B + 1) : ℤ) • d) < S.ell i := by
        rw [pi_add, pi_smul]; linarith
      simpa using (S.S3_L i _ hsmall).symm
  refine ⟨T (k • d) (S.sigma i ε),
    T_mem_of_mem_orbitClosure (S.sigma_mem_orbitClosure i ε) _, fun w hw => ?_⟩
  have hkd : k • d ∈ S.Gamma := AddSubgroup.zsmul_mem _ hdmem k
  have hbgw : S.bg i ε (w + k • d) = S.bg i ε w := Per.apply (S.mem_Per_bg hkd i ε) w
  have htail : (if δ then S.R i w else S.L i w)
      = (if δ then S.R i (w + k • d) else S.L i (w + k • d)) := by
    cases δ with
    | false => simpa using (Per.apply (S.mem_Gamma_iff.mp hkd i).1 w).symm
    | true => simpa using (Per.apply (S.mem_Gamma_iff.mp hkd i).2 w).symm
  show (if δ then S.R i w else S.L i w) + S.bg i ε w
      = S.F i (w + k • d) + S.bg i ε (w + k • d)
  rw [hbgw, htail, hkBig w (hwi w hw)]

omit [Fact p.Prime] in
/-- `σᵢ^ε = Gᵢ^{ε,L}` on `{πᵢ < ℓᵢ}`.  Paper §2.1, by (S3). -/
theorem sigma_eq_Gfield_left (i : Fin m) (ε : Bool) {z : ℤ × ℤ} (hz : pi (S.v i) z < S.ell i) :
    S.sigma i ε z = S.Gfield i ε false z := by
  show S.F i z + S.bg i ε z = (if (false : Bool) then S.R i z else S.L i z) + S.bg i ε z
  rw [S.S3_L i z hz]
  simp

omit [Fact p.Prime] in
/-- `σᵢ^ε = Gᵢ^{ε,R}` on `{πᵢ > rᵢ}`.  Paper §2.1, by (S3). -/
theorem sigma_eq_Gfield_right (i : Fin m) (ε : Bool) {z : ℤ × ℤ} (hz : S.r i < pi (S.v i) z) :
    S.sigma i ε z = S.Gfield i ε true z := by
  show S.F i z + S.bg i ε z = (if (true : Bool) then S.R i z else S.L i z) + S.bg i ε z
  rw [S.S3_R i z hz]
  simp

omit [Fact p.Prime] in
/-- `Hᵢ` preserves `σᵢ^ε`.  Paper §2.1. -/
theorem H_mem_Per_sigma (i : Fin m) (ε : Bool) : S.H i ∈ Per (S.sigma i ε) := by
  rw [mem_Per_iff]
  funext z
  show S.F i (z + S.H i) + S.bg i ε (z + S.H i) = S.F i z + S.bg i ε z
  rw [Per.apply (S.H_mem_Per_F i) z, Per.apply (S.mem_Per_bg (S.H_mem_Gamma i) i ε) z]

omit [Fact p.Prime] in
/-- Every `H_j` preserves `Gᵢ^{ε,δ}`, the latter being a sum of tails.  Paper §2.1. -/
theorem H_mem_Per_Gfield (i j : Fin m) (ε δ : Bool) : S.H j ∈ Per (S.Gfield i ε δ) :=
  S.mem_Per_Gfield (S.H_mem_Gamma j) i ε δ

/-! ### §2.2 The exceptional difference fields and the spectra `Λᵢ` -/

/-- The exceptional difference field
`dᵢ,ε,δ,a(z) = ⟦σᵢ^ε(z) = a⟧ - ⟦Gᵢ^{ε,δ}(z) = a⟧ ∈ {-1, 0, 1}`.  Paper §2.2. -/
noncomputable def diffField (i : Fin m) (ε δ : Bool) (a : ZMod p) : Config ℂ :=
  ind (S.sigma i ε) a - ind (S.Gfield i ε δ) a

omit [Fact p.Prime] in
/-- **(P1).**  `dᵢ,ε,R,a ≡ 0` on `{πᵢ > rᵢ}`. -/
theorem diffField_eq_zero_right (i : Fin m) (ε : Bool) (a : ZMod p) {z : ℤ × ℤ}
    (hz : S.r i < pi (S.v i) z) : S.diffField i ε true a z = 0 := by
  show ind (S.sigma i ε) a z - ind (S.Gfield i ε true) a z = 0
  rw [ind_congr a (S.sigma_eq_Gfield_right i ε hz), sub_self]

omit [Fact p.Prime] in
/-- **(P1).**  `dᵢ,ε,L,a ≡ 0` on `{πᵢ < ℓᵢ}`. -/
theorem diffField_eq_zero_left (i : Fin m) (ε : Bool) (a : ZMod p) {z : ℤ × ℤ}
    (hz : pi (S.v i) z < S.ell i) : S.diffField i ε false a z = 0 := by
  show ind (S.sigma i ε) a z - ind (S.Gfield i ε false) a z = 0
  rw [ind_congr a (S.sigma_eq_Gfield_left i ε hz), sub_self]

omit [Fact p.Prime] in
/-- **(P2).**  `T^{Hᵢ} dᵢ,ε,δ,a = dᵢ,ε,δ,a`. -/
theorem T_H_diffField (i : Fin m) (ε δ : Bool) (a : ZMod p) :
    T ((S.kappa i : ℤ) • S.v i) (S.diffField i ε δ a) = S.diffField i ε δ a := by
  funext z
  show ind (S.sigma i ε) a (z + S.H i) - ind (S.Gfield i ε δ) a (z + S.H i)
      = ind (S.sigma i ε) a z - ind (S.Gfield i ε δ) a z
  rw [Per.apply (mem_Per_ind (S.H_mem_Per_sigma i ε) a) z,
    Per.apply (mem_Per_ind (S.H_mem_Per_Gfield i i ε δ) a) z]

open Classical in
/-- The exceptional spectrum
`Λᵢ = {λ : λ^{κᵢ} = 1 and λ occurs in some dᵢ,ε,δ,a}`.  Paper §2.2. -/
noncomputable def Lam (i : Fin m) : Finset ℂ :=
  (rootsFinset (S.kappa i)).filter fun lam =>
    ∃ ε δ, ∃ a : ZMod p, Occurs (S.kappa i) (S.v i) lam (S.diffField i ε δ a)

theorem mem_Lam_iff {i : Fin m} {lam : ℂ} :
    lam ∈ S.Lam i ↔ lam ∈ rootsFinset (S.kappa i) ∧
      ∃ ε δ, ∃ a : ZMod p, Occurs (S.kappa i) (S.v i) lam (S.diffField i ε δ a) := by
  classical
  rw [Lam, Finset.mem_filter]

/-- **Lemma 2.1.**  `Λᵢ ≠ ∅`: otherwise every `dᵢ,ε,δ,a` vanishes identically, giving
`Fᵢ = Rᵢ` and contradicting (S2). -/
theorem Lam_nonempty (i : Fin m) : (S.Lam i).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  -- If `Λᵢ = ∅` then no `λ` occurs, so every difference field is the sum of its (vanishing)
  -- spectral components.
  have hzero : ∀ (ε δ : Bool) (a : ZMod p), S.diffField i ε δ a = 0 := by
    intro ε δ a
    rw [← sum_act_specProj (S.kappa_pos i) (S.T_H_diffField i ε δ a)]
    refine Finset.sum_eq_zero fun mu hmu => ?_
    by_contra hne
    have hmem : mu ∈ S.Lam i := S.mem_Lam_iff.mpr ⟨hmu, ε, δ, a, hne⟩
    rw [hempty] at hmem
    exact absurd hmem (Finset.notMem_empty mu)
  -- Vanishing of every colour indicator difference forces `σᵢ^+ = Gᵢ^{+,R}` pointwise.
  have hsig : ∀ z, S.sigma i true z = S.Gfield i true true z := by
    intro z
    by_contra hne
    have h : S.diffField i true true (S.Gfield i true true z) z = 0 := by
      rw [hzero true true (S.Gfield i true true z)]; rfl
    rw [show S.diffField i true true (S.Gfield i true true z) z
          = ind (S.sigma i true) (S.Gfield i true true z) z
            - ind (S.Gfield i true true) (S.Gfield i true true z) z from rfl,
      ind_self, ind_eq_zero hne, zero_sub, neg_eq_zero] at h
    exact one_ne_zero h
  -- Cancelling the common background gives `Fᵢ = Rᵢ`, which is doubly periodic by (S3).
  have hFR : S.F i = S.R i := by
    funext z
    exact add_right_cancel (hsig z)
  exact S.S2 i (by rw [hFR]; exact S.S3_R_periodic i)

/-- `dᵢ = deg Aᵢ = |Λᵢ| ≥ 1`.  Paper (2.1). -/
noncomputable def specDeg (i : Fin m) : ℕ := (S.Lam i).card

theorem specDeg_pos (i : Fin m) : 0 < S.specDeg i :=
  Finset.card_pos.mpr (S.Lam_nonempty i)

/-- `Aᵢ(T^{vᵢ}) = ∏_{λ ∈ Λᵢ} (T^{vᵢ} - λ)`.  Paper (2.1). -/
noncomputable def Afac (i : Fin m) : LaurentTwo ℂ := ∏ lam ∈ S.Lam i, linFactor (S.v i) lam

/-- `A(T) = ∏ᵢ Aᵢ(T^{vᵢ})`.  Paper (2.2). -/
noncomputable def Aop : LaurentTwo ℂ := ∏ i, S.Afac i

/-- The zonotope `Z = ∑ᵢ [0, dᵢ vᵢ]`.  Paper (2.2). -/
noncomputable def Zono : Set (ℝ × ℝ) := zonotope S.specDeg S.v

theorem Afac_ne_zero (i : Fin m) : S.Afac i ≠ 0 := by
  rw [Afac, Finset.prod_ne_zero_iff]
  exact fun lam _ => linFactor_ne_zero (S.primitive i).ne_zero lam

theorem Aop_ne_zero : S.Aop ≠ 0 := by
  rw [Aop, Finset.prod_ne_zero_iff]
  exact fun i _ => S.Afac_ne_zero i

/-- **(P3).**  `Aᵢ(T^{vᵢ}) dᵢ,ε,δ,a = 0`. -/
theorem act_Afac_diffField (i : Fin m) (ε δ : Bool) (a : ZMod p) :
    act (S.Afac i) (S.diffField i ε δ a) = 0 := by
  classical
  have hκ : 0 < S.kappa i := S.kappa_pos i
  have hd : T ((S.kappa i : ℤ) • S.v i) (S.diffField i ε δ a) = S.diffField i ε δ a :=
    S.T_H_diffField i ε δ a
  -- Components outside `Λᵢ` vanish by the definition of `Λᵢ`.
  have hout : ∀ mu ∈ rootsFinset (S.kappa i), mu ∉ S.Lam i →
      act (specProj (S.kappa i) (S.v i) mu) (S.diffField i ε δ a) = 0 := by
    intro mu hmu hnot
    by_contra hne
    exact hnot (S.mem_Lam_iff.mpr ⟨hmu, ε, δ, a, hne⟩)
  -- Components inside `Λᵢ` are killed by their own linear factor of `Aᵢ`.
  have hin : ∀ mu ∈ S.Lam i,
      act (S.Afac i) (act (specProj (S.kappa i) (S.v i) mu) (S.diffField i ε δ a)) = 0 := by
    intro mu hmu
    have h0 : act (linFactor (S.v i) mu)
        (act (specProj (S.kappa i) (S.v i) mu) (S.diffField i ε δ a)) = 0 :=
      act_linFactor_eq_zero (T_act_specProj hκ hd (S.mem_Lam_iff.mp hmu).1)
    rw [Afac, ← Finset.prod_erase_mul _ _ hmu, act_mul, h0, act_zero_right]
  rw [← sum_act_specProj hκ hd, act_sum_right]
  refine Finset.sum_eq_zero fun mu hmu => ?_
  by_cases hL : mu ∈ S.Lam i
  · exact hin mu hL
  · rw [hout mu hmu hL, act_zero_right]

/-- **(2.3).**  `Newt(Aᵢ(T^{vᵢ})) = [0, dᵢ vᵢ]`, since `Aᵢ` is monic with `Aᵢ(0) ≠ 0`. -/
theorem newt_Afac (i : Fin m) : newt (S.Afac i) = latSegment (S.specDeg i) (S.v i) := by
  classical
  have hstep : ∀ lam ∈ S.Lam i, newt (linFactor (S.v i) lam) = segment ℝ 0 (toReal (S.v i)) :=
    fun lam hlam => newt_linFactor (S.primitive i).ne_zero
      (ne_zero_of_mem_rootsFinset (S.mem_Lam_iff.mp hlam).1)
  rw [Afac, newt_prod _ _ (fun lam _ => linFactor_ne_zero (S.primitive i).ne_zero lam),
    Finset.sum_congr rfl hstep, sum_const_segment, latSegment, specDeg,
    toReal_natCast_smul]

/-- **(2.3).**  `Newt(A) = ∑ᵢ [0, dᵢ vᵢ] = Z`, by Minkowski additivity of Newton polygons
(Ostrowski). -/
theorem newt_Aop : newt S.Aop = S.Zono := by
  rw [Aop, newt_prod _ _ (fun i _ => S.Afac_ne_zero i), Zono, zonotope]
  exact Finset.sum_congr rfl fun i _ => S.newt_Afac i

/-!
**Remark 2.1 (Galois stability of `Λᵢ`).**  Each `dᵢ,ε,δ,a` is integer-valued, so `Λᵢ` is a
union of Galois orbits, `Aᵢ` is a product of distinct cyclotomic polynomials, and
`A ∈ ℤ[T^±]`.  Nothing below depends on this — Lemma 2.5 handles the coefficient field by
invariance of rank under field extension — so it is recorded here only as a remark.
-/

/-! ### §2.3 A spectrum-preserving encoding -/

/-- The scalar difference field `δᵢ,ε,δ = w(σᵢ^ε) - w(Gᵢ^{ε,δ}) = ∑_a w(a) dᵢ,ε,δ,a`.
Paper Lemma 2.2. -/
noncomputable def scalarDiff (w : ZMod p → ℤ) (i : Fin m) (ε δ : Bool) : Config ℂ :=
  fun z => (w (S.sigma i ε z) : ℂ) - (w (S.Gfield i ε δ z) : ℂ)

theorem scalarDiff_eq_sum (w : ZMod p → ℤ) (i : Fin m) (ε δ : Bool) :
    S.scalarDiff w i ε δ = fun z => ∑ a : ZMod p, (w a : ℂ) * S.diffField i ε δ a z := by
  funext z
  show (w (S.sigma i ε z) : ℂ) - (w (S.Gfield i ε δ z) : ℂ)
      = ∑ a : ZMod p, (w a : ℂ) * (ind (S.sigma i ε) a z - ind (S.Gfield i ε δ) a z)
  rw [Finset.sum_congr rfl fun a _ => mul_sub ((w a : ℂ)) _ _, Finset.sum_sub_distrib,
    sum_mul_ind (fun a => (w a : ℂ)) (S.sigma i ε) z,
    sum_mul_ind (fun a => (w a : ℂ)) (S.Gfield i ε δ) z]

omit [Fact p.Prime] in
/-- `Hᵢ` preserves the scalar difference field, being a period of both `σᵢ^ε` and `Gᵢ^{ε,δ}`. -/
theorem T_H_scalarDiff (w : ZMod p → ℤ) (i : Fin m) (ε δ : Bool) :
    T ((S.kappa i : ℤ) • S.v i) (S.scalarDiff w i ε δ) = S.scalarDiff w i ε δ := by
  funext z
  show (w (S.sigma i ε (z + S.H i)) : ℂ) - (w (S.Gfield i ε δ (z + S.H i)) : ℂ)
      = (w (S.sigma i ε z) : ℂ) - (w (S.Gfield i ε δ z) : ℂ)
  rw [Per.apply (S.H_mem_Per_sigma i ε) z, Per.apply (S.H_mem_Per_Gfield i i ε δ) z]

omit [Fact p.Prime] in
/-- The scalar difference field with the right tail vanishes on `{πᵢ > rᵢ}`. -/
theorem scalarDiff_eq_zero_right (w : ZMod p → ℤ) (i : Fin m) (ε : Bool) {z : ℤ × ℤ}
    (hz : S.r i < pi (S.v i) z) : S.scalarDiff w i ε true z = 0 := by
  show (w (S.sigma i ε z) : ℂ) - (w (S.Gfield i ε true z) : ℂ) = 0
  rw [S.sigma_eq_Gfield_right i ε hz, sub_self]

omit [Fact p.Prime] in
/-- The scalar difference field with the left tail vanishes on `{πᵢ < ℓᵢ}`. -/
theorem scalarDiff_eq_zero_left (w : ZMod p → ℤ) (i : Fin m) (ε : Bool) {z : ℤ × ℤ}
    (hz : pi (S.v i) z < S.ell i) : S.scalarDiff w i ε false z = 0 := by
  show (w (S.sigma i ε z) : ℂ) - (w (S.Gfield i ε false z) : ℂ) = 0
  rw [S.sigma_eq_Gfield_left i ε hz, sub_self]

/-- The `λ`-component of the scalar difference field is the `w`-weighted combination of the
`λ`-components of the exceptional difference fields. -/
theorem act_specProj_scalarDiff (w : ZMod p → ℤ) (i : Fin m) (ε δ : Bool) (lam : ℂ)
    (z : ℤ × ℤ) :
    act (specProj (S.kappa i) (S.v i) lam) (S.scalarDiff w i ε δ) z
      = ∑ a : ZMod p, (w a : ℂ)
          * act (specProj (S.kappa i) (S.v i) lam) (S.diffField i ε δ a) z := by
  rw [S.scalarDiff_eq_sum]
  exact act_sum_scalar (specProj (S.kappa i) (S.v i) lam) (fun a => (w a : ℂ))
    (fun a => S.diffField i ε δ a) z

/-- **Lemma 2.2.**  There is an injection `w : 𝔽_p → ℤ` such that for every `i` and every
`λ ∈ Λᵢ`, the scalar difference field still has `λ` occurring in it, for some pair `(ε, δ)`. -/
theorem exists_enc : ∃ w : ZMod p → ℤ, Function.Injective w ∧
    ∀ i : Fin m, ∀ lam ∈ S.Lam i, ∃ ε δ,
      Occurs (S.kappa i) (S.v i) lam (S.scalarDiff w i ε δ) := by
  classical
  -- For every pair `(i, λ)` with `λ ∈ Λᵢ`, fix a tail choice `(ε, δ)` and a point `z₀` at which
  -- the `λ`-part of some colour component `dᵢ,ε,δ,a` is non-zero.
  have hpick : ∀ x : (_ : Fin m) × ℂ, ∃ y : Bool × Bool × (ℤ × ℤ), x.2 ∈ S.Lam x.1 →
      ∃ a : ZMod p, act (specProj (S.kappa x.1) (S.v x.1) x.2)
        (S.diffField x.1 y.1 y.2.1 a) y.2.2 ≠ 0 := by
    intro x
    by_cases hx : x.2 ∈ S.Lam x.1
    · obtain ⟨-, ε, δ, a, hocc⟩ := S.mem_Lam_iff.mp hx
      replace hocc : act (specProj (S.kappa x.1) (S.v x.1) x.2)
        (S.diffField x.1 ε δ a) ≠ 0 := hocc
      obtain ⟨z₀, hz₀⟩ := Function.ne_iff.mp hocc
      exact ⟨(ε, δ, z₀), fun _ => ⟨a, by simpa using hz₀⟩⟩
    · exact ⟨(true, true, 0), fun h => absurd h hx⟩
  choose pick hpick using hpick
  -- Each pair contributes one non-trivial linear functional in the unknown encoding; pick `t ≥ 2`
  -- with `w(a) = t^{val a}` off all the resulting hyperplanes.
  obtain ⟨t, ht2, ht⟩ := exists_two_le_forall_sum_pow_ne_zero (ZMod.val_injective p)
    (Finset.univ.sigma S.Lam)
    (fun x a => act (specProj (S.kappa x.1) (S.v x.1) x.2)
      (S.diffField x.1 (pick x).1 (pick x).2.1 a) (pick x).2.2)
    (by
      rintro ⟨i, lam⟩ hx
      exact hpick ⟨i, lam⟩ (Finset.mem_sigma.mp hx).2)
  refine ⟨fun a => ((t ^ ZMod.val a : ℕ) : ℤ), fun a b hab => ?_, fun i lam hlam => ?_⟩
  · exact ZMod.val_injective p (Nat.pow_right_injective ht2 (Nat.cast_injective hab))
  · have hocc : act (specProj (S.kappa i) (S.v i) lam)
        (S.scalarDiff (fun a => ((t ^ ZMod.val a : ℕ) : ℤ)) i
          (pick ⟨i, lam⟩).1 (pick ⟨i, lam⟩).2.1) ≠ 0 := by
      intro hzero
      refine ht ⟨i, lam⟩ (Finset.mem_sigma.mpr ⟨Finset.mem_univ i, hlam⟩) ?_
      have hval := congrFun hzero (pick ⟨i, lam⟩).2.2
      rw [Pi.zero_apply, S.act_specProj_scalarDiff] at hval
      refine Eq.trans ?_ hval
      exact Finset.sum_congr rfl fun a _ => by push_cast; ring
    exact ⟨(pick ⟨i, lam⟩).1, (pick ⟨i, lam⟩).2.1, hocc⟩

/-- A fixed choice of encoding as supplied by Lemma 2.2.  Paper §2.3: "Fix such a `w`". -/
noncomputable def enc : ZMod p → ℤ := S.exists_enc.choose

theorem enc_injective : Function.Injective S.enc := S.exists_enc.choose_spec.1

theorem enc_occurs (i : Fin m) {lam : ℂ} (hlam : lam ∈ S.Lam i) :
    ∃ ε δ, Occurs (S.kappa i) (S.v i) lam (S.scalarDiff S.enc i ε δ) :=
  S.exists_enc.choose_spec.2 i lam hlam

/-- `ψ = w(θ) : ℤ² → ℤ ⊆ ℂ`.  Paper §2.3. -/
noncomputable def psi : Config ℂ := fun z => (S.enc (S.θ z) : ℂ)

/-- By (1.1), `D ψ = 0`.  Paper §2.3. -/
theorem act_Dop_psi (h11 : S.CaseTwo) : act S.Dop S.psi = 0 :=
  S.Dop_encoding_eq_zero h11 S.enc

/-! ### §2.5 Divisibility -/

/-- Step (a) of the proof of Lemma 2.4: `z ↦ (f(T) w(x))(z) - c` is a local function of `x`
with window `supp f`, so a relation valid for `θ` is valid throughout the orbit closure. -/
theorem act_enc_eq_const_of_mem_orbitClosure {f : LaurentTwo ℂ} {c : ℂ}
    (hc : act f S.psi = fun _ => c) {x : Config (ZMod p)} (hx : x ∈ orbitClosure S.θ) :
    act f (fun z => (S.enc (x z) : ℂ)) = fun _ => c := by
  classical
  set W : Finset (ℤ × ℤ) := supp f with hW
  set F : (W → ZMod p) → ℂ :=
    fun g => (∑ u : W, f.coeff (u : ℤ × ℤ) * (S.enc (g u) : ℂ)) - c with hFdef
  have hkey : ∀ (y : Config (ZMod p)) (z : ℤ × ℤ),
      F (pattern y W z) = act f (fun w => (S.enc (y w) : ℂ)) z - c := by
    intro y z
    show (∑ u : W, f.coeff (u : ℤ × ℤ) * (S.enc (y (z + (u : ℤ × ℤ))) : ℂ)) - c = _
    congr 1
    rw [act_apply, Finsupp.sum]
    exact Finset.sum_coe_sort W fun u => f.coeff u * (S.enc (y (z + u)) : ℂ)
  have h0 : ∀ z, F (pattern S.θ W z) = 0 := by
    intro z
    rw [hkey]
    show act f S.psi z - c = 0
    rw [hc, sub_self]
  funext z
  exact sub_eq_zero.mp ((hkey x z) ▸ IsLocal.eq_zero_of_mem_orbitClosure h0 hx z)

/-- Step (b) of the proof of Lemma 2.4: the relation passes to the orbit closure and
subtracting two members kills the constant. -/
theorem act_scalarDiff_eq_zero {f : LaurentTwo ℂ} {c : ℂ} (hc : act f S.psi = fun _ => c)
    (i : Fin m) (ε δ : Bool) : act f (S.scalarDiff S.enc i ε δ) = 0 := by
  have h1 := S.act_enc_eq_const_of_mem_orbitClosure hc (S.sigma_mem_orbitClosure i ε)
  have h2 := S.act_enc_eq_const_of_mem_orbitClosure hc (S.Gfield_mem_orbitClosure i ε δ)
  have hsub : S.scalarDiff S.enc i ε δ
      = (fun z => (S.enc (S.sigma i ε z) : ℂ)) - (fun z => (S.enc (S.Gfield i ε δ z) : ℂ)) :=
    rfl
  rw [hsub, act_sub_right, h1, h2, sub_self]

/-- **Lemma 2.4.**  Let `f` be a non-zero Laurent polynomial with `f(T) ψ` constant.
Then `A ∣ f`. -/
theorem Aop_dvd {f : LaurentTwo ℂ} (_hf : f ≠ 0) {c : ℂ}
    (hc : act f S.psi = fun _ => c) : S.Aop ∣ f := by
  classical
  -- (a)–(c).  Every linear factor of `A` divides `f`, by Lemma 2.3 applied to the scalar
  -- difference field, which is `κᵢ vᵢ`-periodic and vanishes on one side of the strip.
  have hdvd : ∀ i : Fin m, ∀ lam ∈ S.Lam i, linFactor (S.v i) lam ∣ f := by
    intro i lam hlam
    obtain ⟨ui, hui⟩ := (S.primitive i).exists_dual
    obtain ⟨ε, δ, hocc⟩ := S.enc_occurs i hlam
    refine linFactor_dvd (S.kappa_pos i) hui (S.T_H_scalarDiff S.enc i ε δ) ?_
      (S.mem_Lam_iff.mp hlam).1 hocc (S.act_scalarDiff_eq_zero hc i ε δ)
    cases δ with
    | true => exact Or.inl ⟨S.r i, fun z hz => S.scalarDiff_eq_zero_right S.enc i ε hz⟩
    | false => exact Or.inr ⟨S.ell i, fun z hz => S.scalarDiff_eq_zero_left S.enc i ε hz⟩
  -- (d).  The factors are pairwise non-associate primes, so their product divides `f`.
  have hAop : S.Aop = ∏ x ∈ Finset.univ.sigma S.Lam, linFactor (S.v x.1) x.2 := by
    rw [Aop, Finset.prod_sigma]
    exact Finset.prod_congr rfl fun i _ => rfl
  rw [hAop]
  refine prod_dvd_of_pairwise_not_associated _ _ ?_ ?_ ?_
  · rintro ⟨i, lam⟩ hx
    rw [Finset.mem_sigma] at hx
    exact prime_linFactor (S.primitive i) (ne_zero_of_mem_rootsFinset (S.mem_Lam_iff.mp hx.2).1)
  · rintro ⟨i, lam⟩ hx ⟨j, mu⟩ hy hxy
    rw [Finset.mem_sigma] at hx hy
    have hlam0 := ne_zero_of_mem_rootsFinset (S.mem_Lam_iff.mp hx.2).1
    have hmu0 := ne_zero_of_mem_rootsFinset (S.mem_Lam_iff.mp hy.2).1
    by_cases hij : i = j
    · subst hij
      exact not_associated_linFactor_of_ne (S.primitive i).ne_zero hlam0 hmu0
        fun h => hxy (congrArg (Sigma.mk i) h)
    · exact not_associated_linFactor_of_det_ne_zero (S.nonparallel i j hij) hlam0 hmu0
  · rintro ⟨i, lam⟩ hx
    rw [Finset.mem_sigma] at hx
    exact hdvd i lam hx.2

/-! ### §2.6 The dimension budget for affine relations -/

/-- `U_S = span_ℚ {1, ψ(· + s) : s ∈ S}`, a space of functions of the anchor `u ∈ ℤ²`.
Paper §2.6. -/
noncomputable def US (W : Finset (ℤ × ℤ)) : Submodule ℚ ((ℤ × ℤ) → ℚ) :=
  Submodule.span ℚ
    (insert (fun _ => (1 : ℚ))
      ((fun s => fun u : ℤ × ℤ => (S.enc (S.θ (u + s)) : ℚ)) '' (W : Set (ℤ × ℤ))))

set_option maxHeartbeats 800000 in
/-- **Lemma 2.5.**  `dim_ℚ U_S ≥ |S| - |R_Z(S)| + 1`, stated without truncated subtraction. -/
theorem card_add_one_le_finrank_US_add_ncard_RZ (W : Finset (ℤ × ℤ)) :
    W.card + 1 ≤ Module.finrank ℚ (S.US W) + (RZ S.Zono W).ncard := by
  classical
  -- The `|S| + 1` generators of `U_S`, indexed by `Option S`: the constant `1` (at `none`)
  -- and the translates `ψ(· + s)` (at `some s`).
  obtain ⟨gen, hgen⟩ : ∃ gen : Option { x // x ∈ W } → ((ℤ × ℤ) → ℚ),
      gen = fun i => i.elim (fun _ => (1 : ℚ))
        (fun s u => ((S.enc (S.θ (u + (s : ℤ × ℤ))) : ℤ) : ℚ)) := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Option { x // x ∈ W } → ℚ) →ₗ[ℚ] ((ℤ × ℤ) → ℚ),
      Φ = Fintype.linearCombination ℚ gen := ⟨_, rfl⟩
  -- `U_S` is the range of `Φ`; the space `R` of affine relations is its kernel.
  have hrangeSet : Set.range gen = insert (fun _ => (1 : ℚ))
      ((fun s => fun u : ℤ × ℤ => ((S.enc (S.θ (u + s)) : ℤ) : ℚ)) '' (W : Set (ℤ × ℤ))) := by
    rw [hgen]
    ext h
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | none => exact Set.mem_insert _ _
      | some s => exact Set.mem_insert_of_mem _ ⟨(s : ℤ × ℤ), Finset.mem_coe.mpr s.2, rfl⟩
    · rintro (rfl | ⟨s, hs, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨s, Finset.mem_coe.mp hs⟩, rfl⟩
  have hrange : LinearMap.range Φ = S.US W := by
    rw [hΦ, Fintype.range_linearCombination, hrangeSet, US]
  -- Rank–nullity: `dim U_S = (|S| + 1) - dim R`.
  have hrk : Module.finrank ℚ (S.US W) + Module.finrank ℚ ↥(LinearMap.ker Φ) = W.card + 1 := by
    rw [← hrange, LinearMap.finrank_range_add_finrank_ker Φ,
      Module.finrank_fintype_fun_eq_card, Fintype.card_option, Fintype.card_coe]
  -- A relation, spelled out at the anchor `z`.
  have hrel : ∀ c : Option { x // x ∈ W } → ℚ, Φ c = 0 → ∀ z : ℤ × ℤ,
      ∑ s : { x // x ∈ W }, c (some s) * ((S.enc (S.θ (z + (s : ℤ × ℤ))) : ℤ) : ℚ)
        = -c none := by
    intro c hc z
    have hz : (∑ i : Option { x // x ∈ W }, c i • gen i) z = 0 := by
      have h := congrFun hc z
      rw [hΦ, Fintype.linearCombination_apply] at h
      simpa using h
    rw [Finset.sum_apply, Fintype.sum_option] at hz
    simp only [hgen, Option.elim, Pi.smul_apply, smul_eq_mul, mul_one] at hz
    linarith
  -- Forgetting the `c₀`-coordinate is injective on `R`, so `R` is carried by the `S`-block.
  obtain ⟨u, kc, hu_li, hu_rel⟩ :
      ∃ (u : Fin (Module.finrank ℚ ↥(LinearMap.ker Φ)) → ({ x // x ∈ W } → ℚ))
        (kc : Fin (Module.finrank ℚ ↥(LinearMap.ker Φ)) → ℚ),
        LinearIndependent ℚ u ∧ ∀ j (z : ℤ × ℤ),
          ∑ s : { x // x ∈ W }, u j s * ((S.enc (S.θ (z + (s : ℤ × ℤ))) : ℤ) : ℚ) = kc j := by
    have hπ : LinearMap.ker
        ((LinearMap.funLeft ℚ ℚ (some : { x // x ∈ W } → Option { x // x ∈ W })).domRestrict
          (LinearMap.ker Φ)) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro ⟨c, hc⟩ hx
      have hs : ∀ s : { x // x ∈ W }, c (some s) = 0 := fun s => by
        simpa using congrFun (LinearMap.mem_ker.mp hx) s
      have h0 : c none = 0 := by
        have h := hrel c hc 0
        rw [Finset.sum_congr rfl fun s _ => by rw [hs s, zero_mul], Finset.sum_const_zero] at h
        exact neg_eq_zero.mp h.symm
      refine Subtype.ext (funext fun i => ?_)
      cases i with
      | none => simpa using h0
      | some s => simpa using hs s
    refine ⟨fun j s =>
        ((Module.finBasis ℚ ↥(LinearMap.ker Φ) j : ↥(LinearMap.ker Φ)) :
          Option { x // x ∈ W } → ℚ) (some s),
      fun j => -(((Module.finBasis ℚ ↥(LinearMap.ker Φ) j : ↥(LinearMap.ker Φ)) :
          Option { x // x ∈ W } → ℚ) none),
      ?_, fun j z => hrel _ (Module.finBasis ℚ ↥(LinearMap.ker Φ) j).2 z⟩
    exact (Module.finBasis ℚ ↥(LinearMap.ker Φ)).linearIndependent.map' _ hπ
  -- Base change `ℚ → ℂ` preserves the dimension of the solution space.
  have huc_li : LinearIndependent ℂ
      (fun j => fun s : { x // x ∈ W } => ((u j s : ℚ) : ℂ)) := by
    have h : LinearIndependent ℂ (fun j => (algebraMap ℚ ℂ) ∘ u j) :=
      linearIndependent_algebraMap_comp_iff.mpr hu_li
    simpa [Function.comp_def, eq_ratCast] using h
  -- `f = ∑_s c_s T^s`, the Laurent polynomial attached to a relation.
  obtain ⟨F, hFdef⟩ : ∃ F : Fin (Module.finrank ℚ ↥(LinearMap.ker Φ)) → LaurentTwo ℂ,
      ∀ j, F j = windowPoly ℂ W (fun s => ((u j s : ℚ) : ℂ)) := ⟨_, fun _ => rfl⟩
  have hF_li : LinearIndependent ℂ F := by
    rw [Fintype.linearIndependent_iff]
    intro a hzero
    have hsum : ∑ j, a j • F j
        = windowPoly ℂ W (fun s => ∑ j, a j * ((u j s : ℚ) : ℂ)) := by
      have h1 : ∀ j, a j • F j
          = windowPoly ℂ W (a j • fun s : { x // x ∈ W } => ((u j s : ℚ) : ℂ)) := by
        intro j; rw [hFdef, map_smul]
      rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => h1 j, ← map_sum]
      congr 1
      funext s
      rw [Finset.sum_apply]
      rfl
    rw [hsum] at hzero
    have hc : ∀ s : { x // x ∈ W }, ∑ j, a j * ((u j s : ℚ) : ℂ) = 0 := by
      intro s
      have h := coeff_windowPoly W (fun t => ∑ j, a j * ((u j t : ℚ) : ℂ)) s
      rw [hzero] at h
      simpa using h.symm
    refine Fintype.linearIndependent_iff.mp huc_li a (funext fun s => ?_)
    rw [Finset.sum_apply]
    simpa using hc s
  -- `f(T) ψ` is constant, so Lemma 2.4 gives `f = A g`.
  have hFne : ∀ j, F j ≠ 0 := fun j => hF_li.ne_zero j
  have hFpsi : ∀ j, act (F j) S.psi = fun _ => ((kc j : ℚ) : ℂ) := by
    intro j
    funext z
    rw [hFdef, act_windowPoly]
    have h := congrArg (fun q : ℚ => (q : ℂ)) (hu_rel j z)
    push_cast at h
    rw [← h]
    rfl
  choose G hG using fun j => S.Aop_dvd (hFne j) (hFpsi j)
  have hGne : ∀ j, G j ≠ 0 := fun j h => hFne j (by rw [hG j, h, mul_zero])
  -- `Newt(f) = Z + Newt(g) ⊆ Conv(S)` puts the support of `g` inside `R_Z(S)`.
  have hGsupp : ∀ j, ∀ r ∈ supp (G j), r ∈ RZ S.Zono W := by
    intro j r hr
    rw [mem_RZ_iff]
    intro x hx
    have h1 : toReal r + x ∈ newt (S.Aop * G j) :=
      add_newt_subset_newt_mul S.Aop_ne_zero (hGne j) hr (by rw [S.newt_Aop]; exact hx)
    rw [← hG j, newt_eq_conv] at h1
    refine Conv_mono ?_ h1
    rw [hFdef]
    exact supp_windowPoly_subset W _
  -- `(c₀, f) ↦ g` is injective, so `dim R ≤ |R_Z(S)|`.
  have hRZfin : (RZ S.Zono W).Finite := RZ_finite S.Zono (zero_mem_zonotope _ _) W
  have : Fintype ↥(RZ S.Zono W) := hRZfin.fintype
  have hcard : Fintype.card ↥(RZ S.Zono W) = (RZ S.Zono W).ncard := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have hGc_li : LinearIndependent ℂ
      (fun j => fun r : ↥(RZ S.Zono W) => (G j).coeff (r : ℤ × ℤ)) := by
    rw [Fintype.linearIndependent_iff]
    intro a hzero
    have hcoeffsum : ∀ t : ℤ × ℤ, (∑ j, a j • G j).coeff t = ∑ j, a j * (G j).coeff t := by
      intro t
      rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
      exact Finset.sum_congr rfl fun j _ => by
        rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    have hH : ∑ j, a j • G j = 0 := by
      refine AddMonoidAlgebra.coeff_eq_zero.mp (Finsupp.ext fun t => ?_)
      rw [hcoeffsum t]
      by_cases ht : t ∈ RZ S.Zono W
      · simpa using congrFun hzero ⟨t, ht⟩
      · refine (Finset.sum_eq_zero fun j _ => ?_).trans (by simp)
        have h0 : (G j).coeff t = 0 := by
          by_contra hne
          exact ht (hGsupp j t (mem_supp.mpr hne))
        rw [h0, mul_zero]
    have hFzero : ∑ j, a j • F j = 0 := by
      have hmul : ∑ j, a j • F j = S.Aop * ∑ j, a j • G j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [hG j, mul_smul_comm]
      rw [hmul, hH, mul_zero]
    exact Fintype.linearIndependent_iff.mp hF_li a hFzero
  have hNle : Module.finrank ℚ ↥(LinearMap.ker Φ) ≤ (RZ S.Zono W).ncard := by
    have h := hGc_li.fintype_card_le_finrank
    rwa [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, hcard] at h
  omega

/-- `U_S` is a space of functions on the finite set of patterns, so its dimension is at most
the complexity.  Paper Remark 2.6. -/
theorem finrank_US_le_P (W : Finset (ℤ × ℤ)) :
    Module.finrank ℚ (S.US W) ≤ P S.θ W := by
  classical
  have : Fintype ↥(patterns S.θ W) := (patterns_finite S.θ W).fintype
  have hcard : Fintype.card ↥(patterns S.θ W) = P S.θ W := by
    rw [P, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  -- Every generator of `U_S`, hence every element of it, depends on the anchor `u` only
  -- through the pattern `θ|_{u + W}`.
  have hfac : ∀ h ∈ S.US W, ∀ u u' : ℤ × ℤ,
      pattern S.θ W u = pattern S.θ W u' → h u = h u' := by
    intro h hh
    rw [US] at hh
    induction hh using Submodule.span_induction with
    | mem g hg =>
        rcases hg with rfl | ⟨s, hs, rfl⟩
        · intro _ _ _; rfl
        · intro u u' huu
          show ((S.enc (S.θ (u + s)) : ℤ) : ℚ) = ((S.enc (S.θ (u' + s)) : ℤ) : ℚ)
          have hq : S.θ (u + s) = S.θ (u' + s) := congrFun huu ⟨s, Finset.mem_coe.mp hs⟩
          rw [hq]
    | zero => intro _ _ _; rfl
    | add a b _ _ ha hb =>
        intro u u' huu
        show a u + b u = a u' + b u'
        rw [ha u u' huu, hb u u' huu]
    | smul c a _ ha =>
        intro u u' huu
        show c * a u = c * a u'
        rw [ha u u' huu]
  -- Pick one anchor realising each pattern; restriction to those anchors is injective on `U_S`.
  have hex : ∀ π : ↥(patterns S.θ W), ∃ u : ℤ × ℤ, pattern S.θ W u = ↑π := fun π => π.2
  choose rho hrho using hex
  have hle : Module.finrank ℚ ↥(S.US W) ≤ Module.finrank ℚ (↥(patterns S.θ W) → ℚ) := by
    refine LinearMap.finrank_le_finrank_of_injective
      (f := (⟨⟨fun x : ↥(S.US W) => fun π => (x : (ℤ × ℤ) → ℚ) (rho π), fun _ _ => rfl⟩,
        fun _ _ => rfl⟩ : ↥(S.US W) →ₗ[ℚ] (↥(patterns S.θ W) → ℚ))) ?_
    intro x y hxy
    refine Subtype.ext (funext fun u => ?_)
    have hmem : pattern S.θ W u ∈ patterns S.θ W := ⟨u, rfl⟩
    have h1 : (x : (ℤ × ℤ) → ℚ) (rho ⟨_, hmem⟩) = (y : (ℤ × ℤ) → ℚ) (rho ⟨_, hmem⟩) :=
      congrFun hxy ⟨_, hmem⟩
    rw [← hfac _ x.2 (rho ⟨_, hmem⟩) u (hrho ⟨_, hmem⟩),
      ← hfac _ y.2 (rho ⟨_, hmem⟩) u (hrho ⟨_, hmem⟩), h1]
  rwa [Module.finrank_fintype_fun_eq_card, hcard] at hle

/-- **Remark 2.6.**  If `R_Z(S) = ∅` then the main theorem already holds for `S`.  This case
covers point and segment windows, since `Z` is two-dimensional (`m ≥ 2` and `v₁ ∦ v₂`). -/
theorem P_ge_of_RZ_eq_empty {W : Finset (ℤ × ℤ)} (h : RZ S.Zono W = ∅) :
    W.card + 1 ≤ P S.θ W := by
  have h1 := S.card_add_one_le_finrank_US_add_ncard_RZ W
  rw [h, Set.ncard_empty, add_zero] at h1
  exact h1.trans (S.finrank_US_le_P W)

/-- **Remark 2.6.**  By lattice-convexity, `r ∈ R_Z(S)` implies `(r + Z) ∩ ℤ² ⊆ S`. -/
theorem mem_of_mem_RZ_Zono {W : Finset (ℤ × ℤ)} (hW : LatticeConvex W) {r : ℤ × ℤ}
    (hr : r ∈ RZ S.Zono W) {q : ℤ × ℤ} (hq : q ∈ latticePts S.Zono) : r + q ∈ W :=
  mem_of_mem_RZ hW hr hq

end StarConfig

end Nivat
