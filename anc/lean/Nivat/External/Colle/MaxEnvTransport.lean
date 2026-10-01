/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainMax
import Nivat.External.Colle.LatticeEdges

/-!
# Transporting `-n_J ∈ E ↑S` across `IsMaxEnvIn` (lane-hole3-nlmax)

Consumer: `Nivat.LaneLeafAGenDepth.belowFail_subset_reach_of_faceLen_hat`
(`tmp/wip/lane-leafa-gen-fillcover-depth.lean:4669-4685`), one of whose four hypotheses is
`hνA : -n_J ∈ E (A i₀)`.

**Correction (lane-leafa-gen, round 2026-09-25):** `hνA` already has a producer —
`Nivat.LaneLeafAGenDepth.mem_E_of_enveloped` (`lane-leafa-gen-fillcover-depth.lean:4788-4792`),
which derives it from `Enveloped (↑S) (A i₀)` + `-n_J ∈ E ↑S` via `Enveloped.E_eq`, and is
already the route the call site uses (`belowFail_subset_reach_of_faceLen_env`, `:4805-4824`).
What this file actually supplies, not previously present, is the one step upstream of that:
projecting `IsMaxEnvIn Env C A`'s first conjunct plus `hEnv : Env = EnvOf ↑S` down to
`Enveloped ↑S A` — the shape the real call site (`maxA i₀ : IsMaxEnvIn Env … (A i₀)`) actually
holds, sparing it a manual `hmax.1` unfold. `negNJ_mem_E_A_of_maxA`'s proof body from
`rw [hEnv] at hEnvA` onward is, verbatim, `mem_E_of_enveloped`'s proof.

`-n_J ∈ E (↑S : Set (ℤ × ℤ))` is established at the real call site by
`ChainDataGeom.a_ne_a'_iff_negNJ_mem_E` / `DecompData.neg_mem_E_Sphi_of_dot_eq_zero`
(`FaceDistinct.lean:125,159`), so it is threaded through here as a hypothesis, not reproved.
`Env (A i₀)` is the first conjunct of `IsMaxEnvIn Env C (A i₀)` (`maxA i₀`, `ChainMax.lean:62`,
`Env A ∧ A ⊆ C ∧ …`) — free, no maximality needed, the same "which conjunct" discipline as
`AhatHeight.lean`'s `hstrip` (there conjunct 2, here conjunct 1). `Env = EnvOf ↑S` (`hEnv`,
`ChainExhaustInter.lean:179`) pins `Env (A i₀)` to `Enveloped ↑S (A i₀)` via `envOf_iff`
(`LatticeEdges.lean:2509`, `Iff.rfl`).

The proof is one `Enveloped.E_eq` (`LatticeEdges.lean:1731`), the pattern used at ~40 other
mainline call sites (`AbsorbEnv.lean`, `TowerConstruct.lean`, `ShellSubStrip.lean`, …):
`Enveloped U T` with `(E U).Finite` forces `E T = E U`, so membership transports from `U = ↑S`
to `T = A i₀` verbatim.

Numeric sanity check (硬规矩 6): taking `A i₀ := ↑S` itself (`U = T`), `enveloped_refl`
(`LatticeEdges.lean:715`) gives `Enveloped ↑S ↑S`, and the conclusion `-n_J ∈ E ↑S → -n_J ∈ E ↑S`
confirms the direction of `Enveloped.E_eq` used below (`E T = E U`, letting membership flow from
the *known* side `↑S` to the *asked* side `A i₀`, not the reverse) — a genuine non-degenerate
instance needs an explicit small `S`/`A i₀` pair with `Enveloped ↑S (A i₀)` witnessed, which is
call-site data this file does not carry.
-/

set_option autoImplicit false

namespace Nivat.LaneHole3Nlmax

open Nivat Nivat.LE2 Nivat.Colle35

/-- **`-n_J ∈ E (A i₀)`, from `maxA i₀` and `-n_J ∈ E ↑S`.**  Projects `IsMaxEnvIn Env C A`'s
first conjunct plus `hEnv : Env = EnvOf ↑S` down to `Enveloped ↑S A`, then transports membership
by `Enveloped.E_eq` — the same final step as `mem_E_of_enveloped`
(`tmp/wip/lane-leafa-gen-fillcover-depth.lean:4788-4792`), but starting one step further back so
call sites holding `IsMaxEnvIn` (not already-unpacked `Enveloped`) don't have to unfold `hmax.1`
by hand. -/
theorem negNJ_mem_E_A_of_maxA {S : Finset (ℤ × ℤ)} {Env : Set (ℤ × ℤ) → Prop}
    {C A : Set (ℤ × ℤ)} {nJ : ℤ × ℤ}
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (hmax : IsMaxEnvIn Env C A)
    (hnegm : -nJ ∈ E (↑S : Set (ℤ × ℤ))) :
    -nJ ∈ E A := by
  have hEnvA : Env A := hmax.1
  rw [hEnv] at hEnvA
  have henv' : Enveloped (↑S : Set (ℤ × ℤ)) A := hEnvA
  have hSfin : (↑S : Set (ℤ × ℤ)).Finite := S.finite_toSet
  have hEeq : E A = E (↑S : Set (ℤ × ℤ)) :=
    Enveloped.E_eq (finite_E_of_finite hSfin) henv'
  rw [hEeq]
  exact hnegm

end Nivat.LaneHole3Nlmax

#print axioms Nivat.LaneHole3Nlmax.negNJ_mem_E_A_of_maxA
