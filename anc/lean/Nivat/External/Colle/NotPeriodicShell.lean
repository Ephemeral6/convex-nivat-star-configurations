/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Claim37
import Nivat.External.Colle.ChainShell

/-!
# Claim 3.7 for a chain whose shells carry Collé's formula

`Nivat.ColleReg.region_not_periodic` (`RegionSteps.lean:1009`) was, until 2026-09-17, stated
over a bare `ChainData`, where `shellInf` is opaque; see `ChainShell.lean` for why its `reach`
obligation cannot be met there.  It now takes a `ChainDataGeom` and is
`ChainGeom.lean`'s `region_not_periodic_of_geom`, which bundles the explicit inputs listed
below into structure fields and calls this file's `region_not_periodic_of_shell`.

This file discharges the same conclusion over a `ChainDataWithShell`, with the two
remaining inputs left explicit:

* `hrec` / `hdot` — `p` is a recession direction of `Â_∞` not parallel to `ℓ_J`; these are
  region structure, and they feed `ChainDataWithShell.reach`.
* `hgen_layers` — Collé `:597`: *"Since `S_φ` is an `η`-generating set, we may enlarge the
  set where `ϑ` and `x̂_per` coincide so that `ϑ|Â^{(ε+1)}_∞ = x̂_per|Â^{(ε+1)}_∞`."*

Nothing here is `sorry`ed: the statement is exactly as strong as its hypotheses.
-/

namespace Nivat.ColleReg

open Nivat Nivat.Colle Nivat.Colle35 Nivat.Colle37 Nivat.LE2

/-- A period of `f` is a period of every translate of `f`. -/
theorem per_translate {α : Type*} {f : Config α} {u v : ℤ × ℤ} (h : v ∈ Per f) :
    v ∈ Per (T u f) := by
  rw [mem_Per_iff] at h ⊢
  funext z
  simp only [T]
  rw [show z + v + u = (z + u) + v by abel]
  exact congrFun h (z + u)

/-- **Claim 3.7 over a `ChainDataWithShell`.**

The conclusion is Collé's — *the forward orbit of `ϑ` along `v_{ℓ'}` has no fully periodic
accumulation point* (`b3_colle2.txt:593`) — not the strictly stronger `¬ IsPeriodic ϑ`,
which is refuted in the tree (`Step_NotPeriodic.lean:430`); see
`blueprint/FROZEN.md:93-96`.

`vJ` is the paper's `v_{ℓ'} = v_{ℓ_J}` (`:593`: *"we will write `ℓ' = ℓ_J`"*), the direction
of both the orbit and the sliding window `Q + t₀·v_{ℓ'}` of `:597`.  It is a **separate**
parameter from `vl = v_{ℓ_ι}`, which only normalises `x̂_per := T^{k·v_ℓ} x_per`; Lemma 3.5
gives `ι + 1 ≤ J ≤ ι + m - 1` (`:424`), so `ℓ_J ≠ ±ℓ_ι` and the two directions genuinely
differ.  See `blueprint/NOTE.md`, entry "Claim 3.7 的轨道方向 — 2026-09-17". -/
theorem region_not_periodic_of_shell
    {ξ xper ϑ : Config ℤ} {vl vJ p : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (c : ChainDataWithShell ξ xper vl S gen) {K ε : ℕ}
    (hp_ne : p ≠ 0) (hp_per : p ∈ Per xper)
    (hxper_mem : xper ∈ orbitClosure ξ)
    (hϑ_mem : ϑ ∈ orbitClosure ξ)
    (hrec : ∀ g ∈ ⋃ i, c.toChainData.Ahat i, g + p ∈ ⋃ i, c.toChainData.Ahat i)
    (hdot : dot c.nJ p ≠ 0)
    (hshell : ∀ z ∈ c.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z)
    (hshell_not :
      ¬ (∀ z ∈ c.toChainData.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z))
    (hgen_layers : ∃ i M : ℕ, ∀ t : ℕ, M ≤ t →
      ∀ z ∈ c.toChainData.shellInf (ε + 1), GenClosure S (c.toChainData.shellInf ε ∪
        (c.toChainData.shellInf (ε + 1) ∩ winS i ((t : ℤ) • vJ))) z)
    (hS : IsGeneratingSet ξ S) :
    ¬ ∃ y : Config ℤ, Colle45.IsFullyPeriodic y ∧
      ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧
        ∀ z ∈ W, y z = T ((t : ℤ) • vJ) ϑ z := by
  let R : RegionLayers := {
    A := c.toChainData.shellInf, ε := ε, Sphi := S, v_m := p, v := vJ
    v_m_ne := hp_ne
    reach := c.reach ε hrec hdot
    gen := hgen_layers }
  refine claim37 R hS ?_ ?_ hϑ_mem hshell ?_
  · exact ⟨1, one_ne_zero, by simp only [one_smul]; exact per_translate hp_per⟩
  · exact T_mem_of_mem_orbitClosure hxper_mem ((K : ℤ) • vl)
  · push Not at hshell_not; exact hshell_not

end Nivat.ColleReg
