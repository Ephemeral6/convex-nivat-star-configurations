/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ANormal
import Nivat.External.Colle.ShellLine
import Nivat.External.Colle.BottomReachMin
import Nivat.External.Colle.BottomRoom

set_option autoImplicit false

/-!
# `hline0` and the reach-minimal base point (`bottom`'s conjuncts 1, 2 and 4)

`exists_reachMin` is lane-chaindata-lead's proof (`tmp/wip/lane-chaindata-bottom.lean` §4, also
copied into `tmp/wip/LeafAAssemble.lean`), landed here under its own namespace.  It produces
`z₀` on the level line `⟪nJ,·⟫ = c` of `reachSet T vJ1` together with the reach-minimality
`hline0` (the only premise `BottomReachMin.bottom_of_reachMin` needs for `bottom`'s 4th conjunct,
via `mem_shell_succ_iff`).  Source: `b3_colle2.txt:518-520`.  Lower boundedness of the
`vJ`-parameter is the wedge bound `hsupp_prev`, transported along `vJ1` because
`⟪n_prev, vJ1⟫ = 0`.
-/

namespace Nivat.NlmaxReachMin

open Nivat Nivat.LE2 Nivat.MaxEnv

private theorem dotZ (m : ℤ × ℤ) (k : ℤ) (z : ℤ × ℤ) : dot m (k • z) = k * dot m z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- Two lattice points at the same `nJ`-level differ by an integer multiple of a primitive
`vJ ⟂ nJ`. -/
theorem exists_zsmul_of_dot_eq {nJ vJ : ℤ × ℤ} (hnJprim : Prim nJ) (hvJprim : Prim vJ)
    (hnJvJ : dot nJ vJ = 0) {x y : ℤ × ℤ} (h : dot nJ x = dot nJ y) :
    ∃ t : ℤ, y = x + t • vJ := by
  have hd0 : dot nJ (y - x) = 0 := by rw [dot_sub, h]; ring
  have hdet : det vJ (y - x) = 0 := det_eq_zero_of_dot_eq_zero hnJprim.ne_zero hnJvJ hd0
  obtain ⟨t, ht⟩ := exists_smul_of_det_eq_zero hvJprim hdet
  refine ⟨t, ?_⟩
  have hsm : y - x = t • vJ := by
    rw [ht]; ext <;> simp
  rw [sub_eq_iff_eq_add'] at hsm
  exact hsm


/-- **The replacement witness.**  `z₀` is the `vJ`-least point of `reachSet T vJ1` on the level
line `{⟪nJ,·⟫ = c}`.  Boundedness below of the `vJ`-parameter — the only thing that could fail —
is the wedge bound: `⟪n_prev,·⟫` is constant along `vJ1` (`hnpvJ1`), so `hsupp_prev` transports
from `T` to `reachSet T vJ1` unchanged, and `⟪n_prev,vJ⟫ < 0` turns it into a lower bound on the
parameter.

Compare `LeafABottom.exists_z0`, which maximises `⟪n_prev,·⟫` over the *whole* level line: that
witness satisfies the third conjunct but not the second, which is the gap this closes. -/
theorem exists_reachMin {T : Set (ℤ × ℤ)} {nJ n_prev vJ vJ1 g_J : ℤ × ℤ} {c : ℤ}
    (hnJprim : Prim nJ) (hvJprim : Prim vJ) (hnJvJ : dot nJ vJ = 0)
    (hnpvJ1 : dot n_prev vJ1 = 0) (hnpvJ : dot n_prev vJ < 0)
    (hsupp_prev : ∀ z ∈ T, dot n_prev z ≤ dot n_prev g_J)
    (hne : ∃ z ∈ reachSet T vJ1, dot nJ z = c) :
    ∃ z₀ : ℤ × ℤ, dot nJ z₀ = c ∧ z₀ ∈ reachSet T vJ1 ∧
      ∀ z ∈ reachSet T vJ1, dot nJ z = c → ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • vJ := by
  obtain ⟨x0, hx0mem, hx0lev⟩ := hne
  -- `⟪n_prev,·⟫` on the swept set is bounded by `⟪n_prev, g_J⟫`.
  have hbound : ∀ z ∈ reachSet T vJ1, dot n_prev z ≤ dot n_prev g_J := by
    rintro z ⟨g, hg, s, rfl⟩
    rw [dot_add, dotZ, hnpvJ1, mul_zero, add_zero]
    exact hsupp_prev g hg
  set P : ℤ → Prop := fun k => x0 + k • vJ ∈ reachSet T vJ1 with hP
  have hinh : ∃ k : ℤ, P k :=
    ⟨0, by show x0 + (0 : ℤ) • vJ ∈ reachSet T vJ1; simpa using hx0mem⟩
  set C : ℤ := dot n_prev g_J - dot n_prev x0 with hC
  have hkey : ∀ k : ℤ, P k → k * dot n_prev vJ ≤ C := by
    intro k hk
    have := hbound _ hk
    rw [dot_add, dotZ] at this
    omega
  have hm1 : (1 : ℤ) ≤ -dot n_prev vJ := by omega
  have hCle : C ≤ (C.natAbs : ℤ) := Int.le_natAbs
  have hCge : -(C.natAbs : ℤ) ≤ C := by
    have := Int.le_natAbs (a := -C)
    simp only [Int.natAbs_neg] at this
    linarith
  have hbdd : ∃ b : ℤ, ∀ k : ℤ, P k → b ≤ k := by
    refine ⟨-(C.natAbs : ℤ) - 1, fun k hk => ?_⟩
    have hkle := hkey k hk
    by_contra hlt
    have hlt' : k < -(C.natAbs : ℤ) - 1 := lt_of_not_ge hlt
    have hnk : (C.natAbs : ℤ) + 2 ≤ -k := by omega
    have hmul : (1 : ℤ) * ((C.natAbs : ℤ) + 2) ≤ (-dot n_prev vJ) * (-k) :=
      mul_le_mul hm1 hnk (by positivity) (by linarith)
    have heq : (-dot n_prev vJ) * (-k) = k * dot n_prev vJ := by ring
    linarith [hmul, hCle, hkle, heq]
  obtain ⟨k0, hk0P, hk0min⟩ := Int.exists_least_of_bdd hbdd hinh
  refine ⟨x0 + k0 • vJ, ?_, hk0P, ?_⟩
  · rw [dot_add, dotZ, hnJvJ, mul_zero, add_zero, hx0lev]
  · intro z hz hzlev
    obtain ⟨s, hs⟩ := exists_zsmul_of_dot_eq hnJprim hvJprim hnJvJ (hx0lev.trans hzlev.symm)
    have hPs : P s := by rw [hP]; simp only []; rw [← hs]; exact hz
    refine ⟨s - k0, by have := hk0min s hPs; omega, ?_⟩
    rw [hs, add_assoc, ← add_smul]
    congr 2
    ring

/-- **Wedge premises of `exists_reachMin`, instantiated on the `ℓ_ι`-side data.**
`n_prev := -(det p vJ • (-p.2, p.1))`.  `hpar : det p vJ1 = 0` is the collinear `J = ι+1`
configuration (`p = -c • vl`, `vJ1 = vl`); `hlow`/`hatt` are the fields `ahat_halfPlane_L` /
`ahat_attained_L` (`ChainPartsFeed.lean`, source `b3_colle2.txt:506`).  Then
`⟪n_prev, vJ1⟫ = 0`, `⟪n_prev, vJ⟫ = -(det p vJ)^2 < 0`, and `g_J` is the attained point. -/
theorem exists_reachMin_of_L {T : Set (ℤ × ℤ)} {nJ vJ vJ1 p : ℤ × ℤ} {cL c : ℤ}
    (hnJprim : Prim nJ) (hvJprim : Prim vJ) (hnJvJ : dot nJ vJ = 0)
    (hpar : det p vJ1 = 0) (hdet : det p vJ ≠ 0)
    (hlow : ∀ g ∈ T, cL ≤ dot (det p vJ • (-p.2, p.1)) g)
    (hatt : ∃ g ∈ T, dot (det p vJ • (-p.2, p.1)) g = cL)
    (hne : ∃ z ∈ reachSet T vJ1, dot nJ z = c) :
    ∃ z₀ : ℤ × ℤ, dot nJ z₀ = c ∧ z₀ ∈ reachSet T vJ1 ∧
      ∀ z ∈ reachSet T vJ1, dot nJ z = c → ∃ k : ℤ, 0 ≤ k ∧ z = z₀ + k • vJ := by
  obtain ⟨gJ, hgJ, hgJeq⟩ := hatt
  have hd : ∀ z : ℤ × ℤ, dot (-(det p vJ • (-p.2, p.1))) z = -(det p vJ * (p.1 * z.2 - p.2 * z.1)) := by
    intro z; simp only [dot, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  refine exists_reachMin (n_prev := -(det p vJ • (-p.2, p.1))) (g_J := gJ) hnJprim hvJprim hnJvJ ?_ ?_ ?_ hne
  · rw [hd]; unfold det at hpar; rw [show p.1 * vJ1.2 - p.2 * vJ1.1 = 0 from hpar]; ring
  · rw [hd]; unfold det at hdet ⊢; nlinarith [sq_pos_of_ne_zero hdet]
  · intro z hz
    have := hlow z hz
    have h2 : dot (-(det p vJ • (-p.2, p.1))) z = -dot (det p vJ • (-p.2, p.1)) z := by
      simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring
    have h3 : dot (-(det p vJ • (-p.2, p.1))) gJ = -dot (det p vJ • (-p.2, p.1)) gJ := by
      simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring
    rw [h2, h3]; linarith

end Nivat.NlmaxReachMin

#print axioms Nivat.NlmaxReachMin.exists_reachMin
#print axioms Nivat.NlmaxReachMin.exists_reachMin_of_L
