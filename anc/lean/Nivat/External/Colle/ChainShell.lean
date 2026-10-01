/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.ShellReach
import Nivat.External.Colle.ShellGeom

/-!
# `ChainData` supplemented with Collé's definition of the shells

`ChainData.shellInf` (`Lemma35.lean:712`) is an opaque `ℕ → Set (ℤ × ℤ)` constrained only by
three containment fields (`shellSubInf`, `shellInfZero`, `shellSubStrip`).  The paper gives
it by a formula — `scratch/b3_colle2.txt:440`, verbatim:

> `Â_∞^{(ε)} := {g + t·v_{ℓ_{J-1}} : g ∈ Â_∞, t ∈ ℤ₊, dist(g + t·v_{ℓ_{J-1}}, ℓ_J) ≤ d_ε}`

(the same display recurs at `:458` for the mirrored item (ii)).  Dropping that formula makes
`Nivat.Colle37.claim37`'s `RegionLayers.reach` obligation *unprovable* from `ChainData`:
the non-vacuity witness `Lemma35.nonempty_chainData` has `shellInf 0 = {0}` and
`shellInf 1 = {0, (1,0)}`, and no translation carries `(1,0)` into `{0}`.

Following CLAUDE.md 「定义修法：加强，不替换」 this file adds a structure extending
`ChainData` with the formula, and derives `reach` from it.  `ChainData` is untouched, so
`Lemma35.lean`'s 19 obligations and `lemma35` itself are unaffected.

## Main results

* `ChainDataWithShell` — `ChainData` plus `shellInf_eq`, the `:440` formula.
* `ChainDataWithShell.reach` — the `RegionLayers.reach` field of `Nivat.Colle37.claim37`.
* `ChainDataWithShell.gen` — the `RegionLayers.gen` field, from `ShellGeom.gen_of_shell`.
-/

namespace Nivat.Colle35

open Nivat Nivat.LE2 Nivat.MaxEnv

variable {α : Type*}

/-- **`ChainData` with Collé's shell formula (`b3_colle2.txt:440`).**

The three new data fields are the paper's `v_{ℓ_{J-1}}` (the sliding direction), the normal
`n_J` of the line `ℓ_J`, and the support value `c_J` — so that `dist(·, ℓ_J) ≤ d_ε` becomes
`c_J - ε ≤ dot n_J ·`, which is what `MaxEnv.mem_shell_iff_dist`
(`MaximalEnveloped.lean:571`) certifies as the same condition.

`ahat_halfPlane` records that `ℓ_J` is a support line of `Â_∞`, and `ahat_nonempty` that
`Â_∞ ≠ ∅`.  Both are part of `Â_∞` being an `(ℓ, ℓ_J)`-region (`:506`: "Actually, `Â_∞` is
an `(ℓ, ℓ_J)`-region"), so a producer that already built the region gets them for free. -/
structure ChainDataWithShell (η xper : Config α) (vl : ℤ × ℤ)
    (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) extends ChainData η xper vl S gen where
  /-- Collé's `v_{ℓ_{J-1}}`: the direction along which the shell is swept. -/
  vJ1 : ℤ × ℤ
  /-- The normal of the second edge line `ℓ_J`. -/
  nJ : ℤ × ℤ
  /-- The support value of `ℓ_J` on `Â_∞`. -/
  cJ : ℤ
  /-- **`b3_colle2.txt:440`**, transcribed through `MaxEnv.shell`. -/
  shellInf_eq : ∀ ε : ℕ,
    toChainData.shellInf ε = MaxEnv.shell (⋃ i, toChainData.Ahat i) vJ1 nJ cJ ε
  /-- `Â_∞` is nonempty. -/
  ahat_nonempty : (⋃ i, toChainData.Ahat i).Nonempty
  /-- `ℓ_J` supports `Â_∞`: `Â_∞ ⊆ halfPlaneGE n_J c_J`. -/
  ahat_halfPlane : ∀ g ∈ ⋃ i, toChainData.Ahat i, cJ ≤ dot nJ g

/-- **The `RegionLayers.reach` obligation, discharged from the shell formula.**

Given that `p` is a recession direction of `Â_∞` (the semi-infinite edge parallel to `ℓ`)
and is not parallel to `ℓ_J`, every point of `Â_∞^{(ε+1)}` is pushed into `Â_∞^{(ε)}` by a
translation of size at most `max |q.1| |q.2|`, for any `q` parallel to `p`.

This is exactly the field `Nivat.Colle37.RegionLayers.reach` consumed by `claim37`. -/
theorem ChainDataWithShell.reach {η xper : Config α} {vl : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataWithShell η xper vl S gen)
    {p : ℤ × ℤ} (ε : ℕ)
    (hrec : ∀ g ∈ ⋃ i, c.toChainData.Ahat i, g + p ∈ ⋃ i, c.toChainData.Ahat i)
    (hdot : dot c.nJ p ≠ 0) :
    ∀ q : ℤ × ℤ, q ≠ 0 → (∃ a : ℤ, q = a • p) →
      ∃ N : ℕ, ∀ z ∈ c.toChainData.shellInf (ε + 1), ∃ k : ℤ,
        |k * q.1| ≤ (N : ℤ) ∧ |k * q.2| ≤ (N : ℤ) ∧
        z + k • q ∈ c.toChainData.shellInf ε := by
  intro q hq hqp
  have hkey := MaxEnv.reach_of_shell (Ainf := ⋃ i, c.toChainData.Ahat i)
    (vJ1 := c.vJ1) (n := c.nJ) (p := p) (c := c.cJ) ε
    c.ahat_nonempty hrec c.ahat_halfPlane hdot hq hqp
  simpa only [c.shellInf_eq] using hkey

open Nivat.Colle37 Nivat.Colle37Geom

/-- **The `RegionLayers.gen` obligation, discharged from the shell formula.**

Collé `:597`: *"Since `S_φ` is an `η`-generating set, we may enlarge the set where `ϑ` and
`x̂_per` coincide."*  `ShellGeom.gen_of_shell` carries out that enlargement — the sweep along
the bottom line of `Â_∞^{(ε+1)}` — so all that is left here is the rewrite through
`shellInf_eq`.

`vJ` is the paper's `v_{ℓ'} = v_{ℓ_J}` (`:593`), the direction of the sliding window, which
is also the direction of the semi-infinite `ℓ_J`-edge of the region and hence of the line
being swept.  It is *not* `vl = v_{ℓ_ι}`; see `blueprint/NOTE.md`, entry
"Claim 3.7 的轨道方向 — 2026-09-17".

The surviving hypotheses are geometry, split in two groups:

* `hS`, `ha`, `ha'`, `hlex`, `hlex'`, `hedge`, `hedge'`, `hdn` — that the `ℓ_J`-parallel edge
  of the zonotope `S_φ` is its `⟪n_J, ·⟫`-minimal face, with endpoints `a, a'` and lattice
  points `a, a + v_J, …, a + r·v_J = a'`;
* `hdz`, `hline`, `hstab`, `hsplit` — that the bottom line of `Â_∞^{(ε+1)}` is the
  half-line `{z₀ + k·v_J : k ≥ L}`, and that `Â_∞` absorbs the translations `b - a` for
  `b ∈ S_φ`, i.e. `S_φ - a` lies in the recession cone of the `(ℓ_ι, ℓ_J)`-region
  `Â_∞^{(ε+1)}` (`b3_colle2.txt:440` asserts the shell *is* such a region).  The mirror
  hypothesis `hstab'` at `a'` was deleted 2026-09-19 — `gen_of_shell` derives it
  (`ShellGeom.lean`, module docstring). -/
theorem ChainDataWithShell.gen {η xper : Config α} {vl : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cd : ChainDataWithShell η xper vl S gen)
    {vJ a a' z₀ : ℤ × ℤ} {r : ℕ} {L : ℤ} (ε : ℕ)
    (hS : LatticeConvex S) (ha : a ∈ S) (ha' : a' ∈ S)
    (hlex : ∀ b ∈ S.erase a,
      dot (-cd.nJ) b < dot (-cd.nJ) a ∨
        (dot (-cd.nJ) b = dot (-cd.nJ) a ∧ dot (-vJ) b < dot (-vJ) a))
    (hlex' : ∀ b ∈ S.erase a',
      dot (-cd.nJ) b < dot (-cd.nJ) a' ∨
        (dot (-cd.nJ) b = dot (-cd.nJ) a' ∧ dot vJ b < dot vJ a'))
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot cd.nJ (b - a))
    (hedge' : ∀ b ∈ S.erase a',
      (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a' - (j : ℤ) • vJ) ∨ 1 ≤ dot cd.nJ (b - a'))
    (hdn : dot cd.nJ vJ = 0) (hdz : dot cd.nJ z₀ = cd.cJ - (ε : ℤ) - 1)
    (hline : ∀ k : ℤ, L ≤ k →
      z₀ + k • vJ ∈ reachSet (⋃ i, cd.toChainData.Ahat i) cd.vJ1)
    (hstab : ∀ b ∈ S, 1 ≤ dot cd.nJ (b - a) → ∀ k : ℤ, L ≤ k →
      z₀ + k • vJ + (b - a) ∈ reachSet (⋃ i, cd.toChainData.Ahat i) cd.vJ1)
    (hsplit : ∀ z ∈ cd.toChainData.shellInf (ε + 1),
      z ∈ cd.toChainData.shellInf ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ) :
    ∃ i M : ℕ, ∀ t : ℕ, M ≤ t → ∀ z ∈ cd.toChainData.shellInf (ε + 1),
      GenClosure S (cd.toChainData.shellInf ε ∪
        (cd.toChainData.shellInf (ε + 1) ∩ winS i ((t : ℤ) • vJ))) z := by
  have h1 := cd.shellInf_eq ε
  have h2 := cd.shellInf_eq (ε + 1)
  rw [h1, h2]
  refine gen_of_shell (r := r) (L := L) hS ha ha' hlex hlex' hedge hedge' hdn hdz
    hline hstab ?_
  rw [← h1, ← h2]
  exact hsplit

end Nivat.Colle35
