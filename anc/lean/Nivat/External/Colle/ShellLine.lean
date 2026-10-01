/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.MaximalEnveloped

/-!
# The layer structure of Collé's shells `Â_∞^{(ε)}`

Two unconditional facts about `Nivat.MaxEnv.shell` (`MaximalEnveloped.lean:563`), the
faithful transcription of `b3_colle2.txt:440`:

> `Â_∞^{(ε)} := {g + t·v_{ℓ_{J-1}} : g ∈ Â_∞, t ∈ ℤ₊, dist(g + t·v_{ℓ_{J-1}}, ℓ_J) ≤ d_ε}`

* the shell splits as `reachSet ∩ {c - ε ≤ ⟪n, ·⟫}` — the `ε`-dependence is *only* in the
  half-plane bound;
* consequently `Â_∞^{(ε+1)} ∖ Â_∞^{(ε)}` is the **single lattice line** `⟪n, ·⟫ = c - ε - 1`
  intersected with `reachSet`, not a two-dimensional annulus.

The second fact is what `Nivat.Colle37.RegionLayers.gen` needs: the enlargement in Collé's
closing sentence of Claim 3.7 (`:597`) is a one-dimensional induction along that line.  The
induction itself is `Nivat.Colle37.genClosure_ray` (`ShellGen.lean`).

## Main results

* `reachSet`, `shell_eq_reach_inter`
* `mem_shell_succ_iff` — the layer/line split.
-/

namespace Nivat.MaxEnv

open Nivat Nivat.LE2

/-- The set swept out of `A` by non-negative translations along `v`; the `ε`-independent
part of `shell`. -/
def reachSet (A : Set (ℤ × ℤ)) (v : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {z | ∃ g ∈ A, ∃ t : ℕ, z = g + (t : ℤ) • v}

theorem mem_reachSet {A : Set (ℤ × ℤ)} {v z : ℤ × ℤ} :
    z ∈ reachSet A v ↔ ∃ g ∈ A, ∃ t : ℕ, z = g + (t : ℤ) • v := Iff.rfl

/-- **The shell is a half-plane slice of one fixed swept set.**  Only the bound moves with
`ε`. -/
theorem shell_eq_reach_inter (A : Set (ℤ × ℤ)) (v n : ℤ × ℤ) (c : ℤ) (ε : ℕ) :
    shell A v n c ε = reachSet A v ∩ {z | c - (ε : ℤ) ≤ dot n z} := by
  ext z
  constructor
  · rintro ⟨g, hg, t, rfl, hd⟩; exact ⟨⟨g, hg, t, rfl⟩, hd⟩
  · rintro ⟨⟨g, hg, t, rfl⟩, hd⟩; exact ⟨g, hg, t, rfl, hd⟩

/-- **`Â_∞^{(ε+1)}` is `Â_∞^{(ε)}` plus one lattice line.**

The new sites are exactly the swept points at distance `ε + 1` from `ℓ_J`, i.e. the single
line `⟪n, ·⟫ = c - ε - 1`. -/
theorem mem_shell_succ_iff {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} {ε : ℕ} {z : ℤ × ℤ} :
    z ∈ shell A v n c (ε + 1) ↔
      z ∈ shell A v n c ε ∨ (z ∈ reachSet A v ∧ dot n z = c - (ε : ℤ) - 1) := by
  rw [shell_eq_reach_inter, shell_eq_reach_inter]
  constructor
  · rintro ⟨hr, hd⟩
    simp only [Set.mem_ofPred_eq] at hd
    push_cast at hd
    rcases lt_or_ge (dot n z) (c - (ε : ℤ)) with hlt | hge
    · exact Or.inr ⟨hr, by omega⟩
    · exact Or.inl ⟨hr, hge⟩
  · rintro (⟨hr, hd⟩ | ⟨hr, hd⟩) <;> refine ⟨hr, ?_⟩ <;>
      simp only [Set.mem_ofPred_eq] at * <;> push_cast <;> omega

/-! ### Where the sweep goes next

The forcing order of Collé `:597` — the sites of the new line are numbered by an integer
parameter, a bounded block of them is already known (it meets the window `Q + t·v_ℓ`), and
one application of the generating set forces a site from its `r` neighbours along the line,
where `r + 1` is the number of lattice points on the `ℓ_J`-edge of `S_φ` — is carried out in
`ShellGen.lean` (`Nivat.Colle37.genClosure_ray`).  It needs the sweep to run in **both**
directions out of that block, because the window is bounded while the `ℓ_J`-edge of the
region is a half-line. -/

end Nivat.MaxEnv
