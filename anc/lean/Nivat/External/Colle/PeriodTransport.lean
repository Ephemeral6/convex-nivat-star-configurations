import Nivat.Defs.Orbit

set_option autoImplicit false

namespace Nivat.CosetPigeonhole

open Nivat

/-- Team-lead's step 2, reconnaissance part (a): `¬ IsPeriodic ξ'` for `ξ' = T u ξ` is a
one-line consequence of translation-invariance of periods.  This is the generic-`α` version
of the `private`, `ZMod p`-specialised `Nivat.Section8.SecondHalfPlane.mem_Per_T_of_mem_Per`
(`Section8/SecondHalfPlane.lean:1089`) — same proof, no new content, just not exported for
`Config ℤ`. -/
theorem mem_Per_T_of_mem_Per {α : Type*} {f : Config α} (e : ℤ × ℤ) {w : ℤ × ℤ}
    (hw : w ∈ Per f) : w ∈ Per (T e f) := by
  rw [mem_Per_iff]
  have h1 : T (w + e) f = T e f := by
    rw [add_comm w e, T_add e w f, mem_Per_iff.mp hw]
  calc T w (T e f) = T (w + e) f := (T_add w e f).symm
    _ = T e f := h1

/-- Converse direction, needed to go from `¬ IsPeriodic ξ` to `¬ IsPeriodic (T u ξ)`:
if `T e f` had a nonzero period `w`, translating back by `-e` shows `f` does too. -/
theorem not_isPeriodic_T_of_not_isPeriodic {α : Type*} {f : Config α} (e : ℤ × ℤ)
    (hf : ¬ IsPeriodic f) : ¬ IsPeriodic (T e f) := by
  rintro ⟨w, hw, hw_ne⟩
  apply hf
  refine ⟨w, ?_, hw_ne⟩
  have hmem := mem_Per_T_of_mem_Per (-e) hw
  have heq : T (-e) (T e f) = f := by
    rw [← T_add, neg_add_cancel, T_zero]
  rwa [heq] at hmem


end Nivat.CosetPigeonhole
