/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.FillCoverWitness

/-!
# `hwedgeF` — kernel numeric instance (lane-hole3-cone, 2026-09-25)

Target: the `hwedgeF` binder of `Nivat.ShellMink.shellEnv_of_faceSeg_hD`
(`tmp/wip/lane-leafa-shell-shellenv.lean:5211`, not yet landed):

```
(hwedgeF : ∀ i, i₀ ≤ i → ∀ n ∈ E (↑S : Set (ℤ × ℤ)),
  0 < dot n w → 0 < dot n vJ1 →
  (face (↑S : Set (ℤ × ℤ)) n).encard ≤
    (face (Nivat.LaneCdSite.shellT A kk vl vJ1 nJ w cJ ε i) n).encard)
```

instantiated on gen's non-degenerate rig (`FillCoverWitness.lean` §5): `S := hexF`, `A := Ai`,
`kk ≡ 0`, `vl := vJ1 := (0,-1)`, `nJ := (0,1)`, `cJ := 0`, `w := (-1,-1)`
(`det vl w = -1 ≠ 0` — team-lead's original `det vl w ≠ 0` requirement was withdrawn per
`LANDING.md` round 230 §5c since gen refuted the general implication, but this rig happens to
satisfy it anyway). The `:518` object `Nivat.LaneCdSite.shellT` specialises here to
`Nivat.FillCoverWit.sh518` (`shellInter_shell_eq` already identifies them,
`sh518_eq : sh518 i ε = hexShape (2*i) (2*i) i i ε`).

**Denominator (PROTOCOL §84): 6 of 6 members of `E hexF` kernel-checked** (`wedge_only_J` below,
via `E_hexF_eq : E (↑hexF) = hexE` + `Nivat.ShellSweep.E_hexA_eq`/`coe_hexF`): only
`n = J := (0,-1) = -nJ` satisfies `0 < dot n w ∧ 0 < dot n vJ1` — `(1,-1)` fails `0 < dot n w`
(`= 0`), the other four fail `0 < dot n vJ1`. This closes debt item (1) from the original report
(previously hand-checked only). The two numeric `hwedgeF` instances below are still checked at a
**single normal `n := J`** and **two concrete `i`** (not a universal proof over `i`).

**Numeric instances, `ε := 1` fixed throughout:**
- `i = 1` (below the threshold `i₀ = ε + 1 = 2`): `hwedgeF`'s conclusion **fails**
  (`hwedgeF_fails_at_i1`) — confirms the guard `i₀ ≤ i` in the binder is load-bearing here, not
  decoration.
- `i = 2` (at the threshold): `hwedgeF`'s conclusion **holds, with equality**
  (`hwedgeF_holds_at_i2`).

This is evidence for `i₀ := ε + 1` as a working threshold on this rig, not a general proof.
-/

set_option autoImplicit false

namespace Nivat.ConeWedgeFCheck

open Nivat Nivat.LE2 Nivat.FillCoverWit Nivat.ShellSweep

/-- The one normal that lands in the wedge on this rig. -/
def J : ℤ × ℤ := ((0 : ℤ), (-1 : ℤ))

/-- `E hexF = hexE`, the six outer normals of the (nondegenerate) hexagon. -/
theorem E_hexF_eq : Nivat.LE2.E (↑hexF : Set (ℤ × ℤ)) = Nivat.ShellSweep.hexE := by
  rw [Nivat.FillCoverWit.coe_hexF]; exact Nivat.ShellSweep.E_hexA_eq

/-- **Closes debt item (1)** (previously hand-checked only): of all six members of `E hexF`,
`J` is the *only* one landing in the wedge `0 < dot n w ∧ 0 < dot n vJ1`. Denominator 6/6. -/
theorem wedge_only_J {n : ℤ × ℤ} (hn : n ∈ Nivat.LE2.E (↑hexF : Set (ℤ × ℤ)))
    (hw : 0 < dot n ((-1 : ℤ), (-1 : ℤ))) (hv : 0 < dot n ((0 : ℤ), (-1 : ℤ))) : n = J := by
  rw [E_hexF_eq] at hn
  simp only [Nivat.ShellSweep.hexE, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  simp only [dot] at hw hv
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [J] <;> omega

theorem J_mem_wedge :
    0 < dot J ((-1 : ℤ), (-1 : ℤ)) ∧ 0 < dot J ((0 : ℤ), (-1 : ℤ)) := by
  constructor <;> simp [dot, J]

theorem face_hexF_J :
    Nivat.LE2.face (↑hexF : Set (ℤ × ℤ)) J = {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))} := by
  have hle : ∀ z ∈ (↑hexF : Set (ℤ × ℤ)), dot J z ≤ (0 : ℤ) := by
    intro z hz
    simp only [hexF, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [dot, J]
  have hmem : ∃ z ∈ (↑hexF : Set (ℤ × ℤ)), dot J z = (0 : ℤ) :=
    ⟨((0 : ℤ), (0 : ℤ)), by simp [hexF], by simp [dot, J]⟩
  rw [Nivat.LE2.face_eq_of_support hle hmem]
  ext ⟨x, y⟩
  simp only [hexF, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_ofPred_eq, dot, J, Prod.mk.injEq]
  constructor
  · rintro ⟨hmem', hxy⟩
    rcases hmem' with h | h | h | h | h | h | h <;>
      (obtain ⟨rfl, rfl⟩ := h; omega)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

theorem encard_face_hexF_J : (Nivat.LE2.face (↑hexF : Set (ℤ × ℤ)) J).encard = 2 := by
  rw [face_hexF_J]; exact Set.encard_pair (by decide)

/-- `i = 1`, `ε = 1`: below the threshold. -/
theorem face_sh518_J_i1 :
    Nivat.LE2.face (sh518 1 1) J = {((0 : ℤ), (-1 : ℤ))} := by
  have hle : ∀ z ∈ sh518 1 1, dot J z ≤ (1 : ℤ) := by
    intro z hz
    rw [sh518_eq] at hz
    obtain ⟨x, y⟩ := z
    simp only [mem_hexShape] at hz
    simp only [dot, J]
    omega
  have hmem : ∃ z ∈ sh518 1 1, dot J z = (1 : ℤ) :=
    ⟨((0 : ℤ), (-1 : ℤ)), by rw [sh518_eq]; simp only [mem_hexShape]; omega, by simp [dot, J]⟩
  rw [Nivat.LE2.face_eq_of_support hle hmem]
  ext ⟨x, y⟩
  rw [sh518_eq]
  simp only [mem_hexShape, Set.mem_ofPred_eq, dot, J, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩; omega
  · rintro ⟨rfl, rfl⟩; norm_num

theorem encard_face_sh518_J_i1 : (Nivat.LE2.face (sh518 1 1) J).encard = 1 := by
  rw [face_sh518_J_i1]; exact Set.encard_singleton _

theorem hwedgeF_fails_at_i1 :
    ¬ (Nivat.LE2.face (↑hexF : Set (ℤ × ℤ)) J).encard ≤
        (Nivat.LE2.face (sh518 1 1) J).encard := by
  rw [encard_face_hexF_J, encard_face_sh518_J_i1]; decide

/-- `i = 2`, `ε = 1`: at the threshold, equality. -/
theorem face_sh518_J_i2 :
    Nivat.LE2.face (sh518 2 1) J = {((0 : ℤ), (-1 : ℤ)), ((1 : ℤ), (-1 : ℤ))} := by
  have hle : ∀ z ∈ sh518 2 1, dot J z ≤ (1 : ℤ) := by
    intro z hz
    rw [sh518_eq] at hz
    obtain ⟨x, y⟩ := z
    simp only [mem_hexShape] at hz
    simp only [dot, J]
    omega
  have hmem : ∃ z ∈ sh518 2 1, dot J z = (1 : ℤ) :=
    ⟨((0 : ℤ), (-1 : ℤ)), by rw [sh518_eq]; simp only [mem_hexShape]; omega, by simp [dot, J]⟩
  rw [Nivat.LE2.face_eq_of_support hle hmem]
  ext ⟨x, y⟩
  rw [sh518_eq]
  simp only [mem_hexShape, Set.mem_ofPred_eq, dot, J, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩; omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

theorem encard_face_sh518_J_i2 : (Nivat.LE2.face (sh518 2 1) J).encard = 2 := by
  rw [face_sh518_J_i2]; exact Set.encard_pair (by decide)

theorem hwedgeF_holds_at_i2 :
    (Nivat.LE2.face (↑hexF : Set (ℤ × ℤ)) J).encard ≤
      (Nivat.LE2.face (sh518 2 1) J).encard := by
  rw [encard_face_hexF_J, encard_face_sh518_J_i2]

/-- **General `i, ε`** (not just `ε = 1`, `i ∈ {1,2}`): for `ε + 1 ≤ i` the bottom face of
`sh518 i ε` w.r.t. `J` contains `(0,-ε)` and `(1,-ε)`, hence has `encard ≥ 2`
(exact value `i - ε + 1`; only `≥ 2` is needed). -/
theorem two_le_encard_face_sh518_J {i ε : ℕ} (h : ε + 1 ≤ i) :
    2 ≤ (Nivat.LE2.face (sh518 i ε) J).encard := by
  have hle : ∀ z ∈ sh518 i ε, dot J z ≤ (ε : ℤ) := by
    intro z hz
    rw [sh518_eq] at hz
    obtain ⟨x, y⟩ := z
    simp only [mem_hexShape] at hz
    simp only [dot, J]
    omega
  have hmem : ∃ z ∈ sh518 i ε, dot J z = (ε : ℤ) :=
    ⟨((0 : ℤ), -(ε : ℤ)), by rw [sh518_eq]; simp only [mem_hexShape]; omega, by simp [dot, J]⟩
  rw [Nivat.LE2.face_eq_of_support hle hmem]
  have hsub : ({((0 : ℤ), -(ε : ℤ)), ((1 : ℤ), -(ε : ℤ))} : Set (ℤ × ℤ)) ⊆
      {z | z ∈ sh518 i ε ∧ dot J z = (ε : ℤ)} := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;>
      refine ⟨?_, by simp [dot, J]⟩ <;> rw [sh518_eq] <;> simp only [mem_hexShape] <;> omega
  calc (2 : ℕ∞) = ({((0 : ℤ), -(ε : ℤ)), ((1 : ℤ), -(ε : ℤ))} : Set (ℤ × ℤ)).encard :=
        (Set.encard_pair (by simp [Prod.ext_iff])).symm
    _ ≤ _ := Set.encard_le_encard hsub

/-- **`hwedgeF` on the rig, all `i, ε` with `ε + 1 ≤ i`**: i.e. `i₀ := ε + 1` works for every
`i ≥ i₀`, not a single point (lane-leafa-shell: `i₀` is shared with `hlcT`/`hattain`, so the
guarantee must be `∀ i ≥ ε+1`). Together with `hwedgeF_fails_at_i1` (`ε = 1`, `i = 1 < ε+1`),
`ε + 1` is the exact threshold at `ε = 1`. -/
theorem hwedgeF_rig {i ε : ℕ} (h : ε + 1 ≤ i) :
    ∀ n ∈ Nivat.LE2.E (↑hexF : Set (ℤ × ℤ)),
      0 < dot n ((-1 : ℤ), (-1 : ℤ)) → 0 < dot n ((0 : ℤ), (-1 : ℤ)) →
      (Nivat.LE2.face (↑hexF : Set (ℤ × ℤ)) n).encard ≤
        (Nivat.LE2.face (sh518 i ε) n).encard := by
  intro n hn hw hv
  have hnJ := wedge_only_J hn hw hv
  subst hnJ
  rw [encard_face_hexF_J]
  exact two_le_encard_face_sh518_J h

end Nivat.ConeWedgeFCheck

#print axioms Nivat.ConeWedgeFCheck.two_le_encard_face_sh518_J
#print axioms Nivat.ConeWedgeFCheck.hwedgeF_rig
#print axioms Nivat.ConeWedgeFCheck.E_hexF_eq
#print axioms Nivat.ConeWedgeFCheck.wedge_only_J
#print axioms Nivat.ConeWedgeFCheck.J_mem_wedge
#print axioms Nivat.ConeWedgeFCheck.face_hexF_J
#print axioms Nivat.ConeWedgeFCheck.encard_face_hexF_J
#print axioms Nivat.ConeWedgeFCheck.face_sh518_J_i1
#print axioms Nivat.ConeWedgeFCheck.encard_face_sh518_J_i1
#print axioms Nivat.ConeWedgeFCheck.hwedgeF_fails_at_i1
#print axioms Nivat.ConeWedgeFCheck.face_sh518_J_i2
#print axioms Nivat.ConeWedgeFCheck.encard_face_sh518_J_i2
#print axioms Nivat.ConeWedgeFCheck.hwedgeF_holds_at_i2
