/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Laurent.Basic

/-!
# Multiplying a monomial into a sum of monomials

Pure `AddMonoidAlgebra` bookkeeping needed for **Proposition 5.3**
(`Nivat.StarConfig.exists_witness`, `Nivat/BiRecursion.lean`).  Stated generically here, with no
reference to `StarConfig`, `aElt`, `cElt`, `Jhat`, `FF`, `cToFF` or `Xmono`, so that this file does
**not** import `Nivat.BiRecursion` — that file is expected to import this one, and importing it
back would create a cycle.

Context (not needed to state or prove the lemmas below, only to see why they are the missing
piece): `Nivat.StarConfig.aElt` and `.cElt` are each, after unfolding their definitions
(`toFF`/`subXY`), a `Finsupp.sum` of *shifted, rescaled* monomials — `f.coeff.sum fun s A =>
single (h s) (v s A)` for an index shift `h` (`h = id` for `aElt` once `toFF` is rewritten via
`AddMonoidAlgebra.sum_coeff_single`/`Finsupp.sum_mapRange_index`; `h = Neg.neg` for `cElt`, whose
definition already has exactly this shape) and a value function `v`
(`v s A = cToFF A` for `aElt`, `v s A = cToFF A * Xmono s` for `cElt`).  `mono_mul_sum_single`
below computes `mono d * (that sum)` termwise, reducing the whole computation to the one-line
identity `mono_mul_single`.

## Main results

* `Nivat.mono_mul_single` — `mono d * single u c = c • mono (d + u)`.
* `Nivat.mono_mul_sum_single` — distributes `mono d *` over a `Finsupp.sum` of shifted, rescaled
  monomials.

## Status

Complete; no `sorry`.
-/

namespace Nivat

variable {R : Type*}

/-- The atomic identity behind both `aElt`'s and `cElt`'s bookkeeping: multiplying the monomial
`T^d` into a single term `c · T^u` shifts the exponent by `d` and leaves the coefficient
untouched. -/
theorem mono_mul_single [CommRing R] (d u : ℤ × ℤ) (c : R) :
    (mono d : LaurentTwo R) * AddMonoidAlgebra.single u c = c • mono (d + u) := by
  simp [mono, AddMonoidAlgebra.single_mul_single, smul_eq_mul]

/-- Distributing `mono d *` over a `Finsupp.sum` of shifted, rescaled monomials.  Instantiated
with `h := id`, this gives the shape of `mono d * S.aElt` (after unfolding `toFF`); instantiated
with `h := Neg.neg`, it is literally the shape of `mono d * S.cElt` (`subXY`'s definition already
has this form, with no further unfolding needed). -/
theorem mono_mul_sum_single {R' : Type*} [CommRing R'] [Zero R] {ι : Type*}
    (d : ℤ × ℤ) (t : ι →₀ R) (h : ι → ℤ × ℤ) (v : ι → R → R') :
    (mono d : LaurentTwo R') * (t.sum fun s c => AddMonoidAlgebra.single (h s) (v s c))
      = t.sum fun s c => v s c • mono (d + h s) := by
  rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => mono_mul_single d (h s) (v s (t s))

end Nivat
