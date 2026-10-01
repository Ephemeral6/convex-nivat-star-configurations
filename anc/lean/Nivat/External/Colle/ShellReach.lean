/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.MaximalEnveloped

/-!
# Sliding inside the shells `Â_∞^{(ε)}`

Collé's shell is defined at `scratch/b3_colle2.txt:440`, verbatim:

> `Â_∞^{(ε)} := {g + t·v_{ℓ_{J-1}} : g ∈ Â_∞, t ∈ ℤ₊, dist(g + t·v_{ℓ_{J-1}}, ℓ_J) ≤ d_ε}`

`Nivat.MaxEnv.shell` (`MaximalEnveloped.lean:563`) is the faithful transcription, with
`MaxEnv.mem_shell_iff_dist` (`:571`) recovering Collé's metric form.

This file supplies the *sliding* property that `Nivat.Colle37.claim37` consumes as its
`RegionLayers.reach` field: a point of the outer shell `Â_∞^{(ε+1)}` can be pushed into the
inner shell `Â_∞^{(ε)}` by a bounded translation along any direction parallel to the period
`p`.

The geometric input is that `Â_∞` is an `(ℓ, ℓ_J)`-region:

* `hrec` — its recession cone contains `p` (the semi-infinite edge parallel to `ℓ`);
* `hhalf` — `ℓ_J` is a support line, so `Â_∞ ⊆ halfPlaneGE n_J c`;
* `hdot` — `p` is not parallel to `ℓ_J`.

`pos_dot_of_rec` turns `hdot` into the *signed* statement `0 < dot n_J p`: a recession
direction cannot decrease a bounded-below linear functional.

## Main results

* `pos_dot_of_rec` — one-sided recession plus a lower bound forces `0 < dot n p`.
* `reach_of_shell` — the `RegionLayers.reach` obligation, for every `q` parallel to `p`.
-/

namespace Nivat.MaxEnv

open Nivat Nivat.LE2

/-- **A recession direction cannot decrease a functional that is bounded below.**

If `Ainf` is nonempty, closed under `· + p`, and contained in `{g | c ≤ dot n g}`, then
`dot n p` cannot be negative; combined with `dot n p ≠ 0` this gives `0 < dot n p`. -/
theorem pos_dot_of_rec {Ainf : Set (ℤ × ℤ)} {n p : ℤ × ℤ} {c : ℤ}
    (hne : Ainf.Nonempty)
    (hrec : ∀ g ∈ Ainf, g + p ∈ Ainf)
    (hhalf : ∀ g ∈ Ainf, c ≤ dot n g)
    (hdot : dot n p ≠ 0) :
    0 < dot n p := by
  obtain ⟨g₀, hg₀⟩ := hne
  by_contra h_neg
  push Not at h_neg
  -- Forward iteration stays inside `Ainf`.
  have key : ∀ m : ℕ, g₀ + (m : ℤ) • p ∈ Ainf := by
    intro m
    induction m with
    | zero => simpa
    | succ k ih =>
      have hstep : g₀ + ((k + 1 : ℕ) : ℤ) • p = (g₀ + ((k : ℕ) : ℤ) • p) + p := by
        push_cast; rw [add_smul, one_smul, add_assoc]
      rw [hstep]; exact hrec _ ih
  -- Each step drops `dot n` by `|dot n p| ≥ 1`.
  have decrease : ∀ m : ℕ, dot n (g₀ + (m : ℤ) • p) = dot n g₀ + (m : ℤ) * dot n p := by
    intro m
    have expand : g₀ + (m : ℤ) • p = (g₀.1 + (m : ℤ) * p.1, g₀.2 + (m : ℤ) * p.2) := by
      ext <;> simp
    simp only [expand, dot]; ring
  -- Choose `m` large enough to break the lower bound.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, dot n (g₀ + (m : ℤ) • p) < c := by
    have hle : dot n p ≤ -1 := by omega
    refine ⟨(dot n g₀ - c + 1).toNat, ?_⟩
    rw [decrease]
    set m : ℤ := ((dot n g₀ - c + 1).toNat : ℤ) with hmdef
    have hmge : dot n g₀ - c + 1 ≤ m := Int.self_le_toNat _
    have hm0 : (0 : ℤ) ≤ m := by rw [hmdef]; positivity
    nlinarith
  exact absurd (hhalf _ (key m)) (by omega)

/-- Iterating the recession property. -/
private theorem mem_of_rec_nat {Ainf : Set (ℤ × ℤ)} {p : ℤ × ℤ}
    (hrec : ∀ g ∈ Ainf, g + p ∈ Ainf) :
    ∀ (m : ℕ) {g : ℤ × ℤ}, g ∈ Ainf → g + (m : ℤ) • p ∈ Ainf := by
  intro m
  induction m with
  | zero => intro g hg; simpa
  | succ k ih =>
    intro g hg
    have hstep : g + ((k + 1 : ℕ) : ℤ) • p = (g + ((k : ℕ) : ℤ) • p) + p := by
      push_cast; rw [add_smul, one_smul, add_assoc]
    rw [hstep]; exact hrec _ (ih hg)

/-- **The `RegionLayers.reach` obligation for Collé's shells.**

Every point of `Â_∞^{(ε+1)}` is carried into `Â_∞^{(ε)}` by `± q`, for any `q` parallel to
the recession direction `p`.  The displacement bound is `max |q.1| |q.2|`, since the
multiplier is `±1`.

The geometric hypotheses are exactly the `(ℓ, ℓ_J)`-region structure of `Â_∞`; see the
module docstring. -/
theorem reach_of_shell {Ainf : Set (ℤ × ℤ)} {vJ1 n p : ℤ × ℤ} {c : ℤ} (ε : ℕ)
    (hne : Ainf.Nonempty)
    (hrec : ∀ g ∈ Ainf, g + p ∈ Ainf)
    (hhalf : ∀ g ∈ Ainf, c ≤ dot n g)
    (hdot : dot n p ≠ 0)
    {q : ℤ × ℤ} (hq : q ≠ 0) (hqp : ∃ a : ℤ, q = a • p) :
    ∃ N : ℕ, ∀ z ∈ shell Ainf vJ1 n c (ε + 1), ∃ k : ℤ,
      |k * q.1| ≤ (N : ℤ) ∧ |k * q.2| ≤ (N : ℤ) ∧
      z + k • q ∈ shell Ainf vJ1 n c ε := by
  have hpos : 0 < dot n p := pos_dot_of_rec hne hrec hhalf hdot
  obtain ⟨a, haq⟩ := hqp
  -- `a ≠ 0`, else `q = 0`.
  have ha : a ≠ 0 := by rintro rfl; exact hq (by rw [haq]; simp)
  -- `k := sign a`, so that `k • q = |a| • p`.
  set k : ℤ := if 0 < a then 1 else -1 with hk
  have hka : k * a = |a| := by
    rcases lt_trichotomy a 0 with h | h | h
    · rw [hk, if_neg (by omega), abs_of_neg h]; ring
    · exact absurd h ha
    · rw [hk, if_pos h, abs_of_pos h]; ring
  have hkabs : |k| = 1 := by
    rcases lt_trichotomy a 0 with h | h | h
    · rw [hk, if_neg (by omega)]; decide
    · exact absurd h ha
    · rw [hk, if_pos h]; decide
  -- The natural number `|a| ≥ 1`.
  set M : ℕ := a.natAbs with hM
  have hMpos : 1 ≤ (M : ℤ) := by
    have : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
    omega
  have hMabs : (M : ℤ) = |a| := (Int.abs_eq_natAbs a).symm
  refine ⟨max q.1.natAbs q.2.natAbs, ?_⟩
  intro z hz
  rw [mem_shell] at hz
  obtain ⟨g, hg, t, rfl, hzouter⟩ := hz
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [abs_mul, hkabs, one_mul, Int.abs_eq_natAbs]
    exact_mod_cast Nat.le_max_left _ _
  · rw [abs_mul, hkabs, one_mul, Int.abs_eq_natAbs]
    exact_mod_cast Nat.le_max_right _ _
  · -- `k • q = M • p`
    have hsmul : k • q = (M : ℤ) • p := by
      rw [haq, smul_smul, hka, hMabs]
    rw [mem_shell]
    refine ⟨g + (M : ℤ) • p, mem_of_rec_nat hrec M hg, t, ?_, ?_⟩
    · rw [hsmul]; abel
    · -- `dot n` increases by at least `M * dot n p ≥ 1`.
      have hexp : dot n (g + (t : ℤ) • vJ1 + k • q)
          = dot n (g + (t : ℤ) • vJ1) + (M : ℤ) * dot n p := by
        rw [hsmul]
        simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul]
        ring
      have hgrow : (1 : ℤ) ≤ (M : ℤ) * dot n p := by nlinarith
      rw [hexp]
      have hout : c - ((ε : ℤ) + 1) ≤ dot n (g + (t : ℤ) • vJ1) := by
        have := hzouter; push_cast at this ⊢; omega
      omega

end Nivat.MaxEnv
