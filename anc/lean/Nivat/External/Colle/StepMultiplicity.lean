import Nivat.Lattice.Primitive
import Nivat.External.Colle.DecompData

set_option autoImplicit false

namespace Nivat.CosetPigeonhole

open Nivat

/-- The bridge team-lead asked for: if `u'` is primitive and `h` is a nonzero vector
parallel to `u'` (`det u' h = 0`), then `h = ±(k • u')` for some `k ≥ 1`.  This is the
missing "`k` from where" step: `h = c • u'` from `eq_zsmul_of_det_eq_zero`, `c ≠ 0` from
`h ≠ 0`, then split on the sign of `c` and take `k := c.natAbs`. -/
theorem step_multiplicity {u' : ℤ × ℤ} (hprim : Primitive u')
    {h : ℤ × ℤ} (hh_ne : h ≠ 0) (hpar : det u' h = 0) :
    ∃ k : ℕ, 0 < k ∧ (h = (k : ℤ) • u' ∨ h = -((k : ℤ) • u')) := by
  obtain ⟨c, hc⟩ := eq_zsmul_of_det_eq_zero hprim hpar
  have hc_ne : c ≠ 0 := by
    rintro rfl
    apply hh_ne
    rw [hc, zero_smul]
  set k := c.natAbs with hk_def
  refine ⟨k, Int.natAbs_pos.mpr hc_ne, ?_⟩
  rcases Int.natAbs_eq c with hcpos | hcneg
  · left
    rw [hc, hcpos]
  · right
    rw [hc, hcneg, neg_smul]


end Nivat.CosetPigeonhole
