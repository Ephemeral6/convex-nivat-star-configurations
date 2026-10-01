/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.SweepBase

/-!
# `hstepIn` reduced to a level-occupancy statement

原文：b3_colle2.txt:777, :402, :414, Figure 10 at :798

`TowerBuild.periodOn_coneRegion_of_lines` (`TowerBuild.lean:236`) carries an unproved binder

```
hstepIn : ∀ z ∈ halfStrip B vl, cz ≤ dot nℓ (z + u') → z + u' ∈ halfStrip B vl
```

which is Figure 10's assertion at `:798` that the `ℓ_{ι-1}` edge of `𝓡_{ι-1}` continues `B`'s
own.  This file does **not** prove it.  What it does is remove the guesswork about what has to
be proved, by isolating the one arithmetic fact that makes `hstepIn` tick:

**`dot nℓ` is constant along `vl`-rays** (`hperp : dot nℓ vl = 0`, `:796` — the lines are
parallel to `ℓ`), so the `nℓ`-levels occupied by `halfStrip B vl` are *exactly* the levels
occupied by `B` (`dot_eq_of_mem_halfStrip`).  Since one `u'`-step drops exactly one level
(`hstep : dot nℓ u' = -1`, `:804` "proceeding this way"), `hstepIn` **forces** `B` to occupy
every level from its own top down to the cut level `cz`, with no gaps
(`exists_level_pred_of_stepIn`, `exists_level_of_stepIn`).

Contrapositively, a single missing level below an occupied one refutes `hstepIn`
(`not_stepIn_of_level_gap`).  This is sharper than "needs geometric reasoning": it says the
whole content of `hstepIn` above the `vl`-bookkeeping is **level occupancy of `B`**, which is
exactly Collé item (i)/(ii) territory (`:472`, `:474`: `B_i ⊇ [-i+1, i-1]² ∩ ℋ(ℓ^{(-)})`
forces occupancy).  Lattice convexity alone does **not** give it — `{(0,0), (1,2)}` is lattice
convex (gcd(1,2)=1, no interior lattice point) and skips level 1 under `nℓ = (0,1)`.

⚠ **This file is a necessary-condition analysis, not a producer.**  `hstepIn` still has no
producer tree-wide; `TowerBuild.lean:242` still takes it as a binder.
-/

set_option autoImplicit false

namespace Nivat.ConeStepIn

open Nivat Nivat.LE2 Nivat.ConeRegion

/-- **`dot nℓ` on the half-strip is `dot nℓ` on `B`** (`b3_colle2.txt:414`, `:796`).

原文：b3_colle2.txt:414 — `H_B(ℓ) := {g + t·v⃗_ℓ ∈ ℤ² : g ∈ B, t ∈ ℤ₊}`
原文：b3_colle2.txt:796 — the lines `l_i` are parallel to `ℓ`, i.e. `⟪n_ℓ, v⃗_ℓ⟫ = 0`

Quantifiers:
- `hperp : dot nℓ vl = 0` — `nℓ` is the transverse normal (`:796`)
- `hz : z ∈ halfStrip B vl` — a point of `H_B(ℓ)` (`:414`)
- Conclusion: `z` sits at the level of one of `B`'s own points — sweeping by `v⃗_ℓ` never
  changes the `nℓ`-level, which is the whole reason the induction at `:795-802` can run
  line by line. -/
theorem dot_eq_of_mem_halfStrip {B : Set (ℤ × ℤ)} {vl nℓ z : ℤ × ℤ}
    (hperp : dot nℓ vl = 0) (hz : z ∈ Nivat.LE2.halfStrip B vl) :
    ∃ b ∈ B, dot nℓ z = dot nℓ b := by
  obtain ⟨b, hb, t, rfl⟩ := hz
  refine ⟨b, hb, ?_⟩
  have h : dot nℓ ((t : ℤ) • vl) = (t : ℤ) * dot nℓ vl := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [dot_add, h, hperp, mul_zero, add_zero]

/-- **`hstepIn` forces `B` to occupy the next level down** (`b3_colle2.txt:798`, `:804`).

原文：b3_colle2.txt:798 — Figure 10: the `ℓ_{ι-1}` edge of `𝓡_{ι-1}` continues `B`'s own
原文：b3_colle2.txt:804 — "proceeding this way", one `u'`-step per line

Quantifiers:
- `hperp : dot nℓ vl = 0` — transverse normal (`:796`)
- `hstep : dot nℓ u' = -1` — one `u'`-step drops exactly one lattice line (`:804`)
- `hstepIn` — the binder of `TowerBuild.periodOn_coneRegion_of_lines` (`TowerBuild.lean:242`)
- `hb : b ∈ B`, `hcz : cz ≤ dot nℓ b - 1` — `b` is at least one level above the cut `cz` (`:472`)
- Conclusion: `B` has a point exactly one level below `b`.

Proof: `b` itself lies in `H_B(ℓ)` (take `t = 0`), the step `b + u'` lands at level
`dot nℓ b - 1 ≥ cz`, so `hstepIn` puts it back in `H_B(ℓ)`, and `dot_eq_of_mem_halfStrip`
reads off a point of `B` at that level. -/
theorem exists_level_pred_of_stepIn {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0) (hstep : dot nℓ u' = -1)
    (hstepIn : ∀ z ∈ Nivat.LE2.halfStrip B vl,
      cz ≤ dot nℓ (z + u') → z + u' ∈ Nivat.LE2.halfStrip B vl)
    {b : ℤ × ℤ} (hb : b ∈ B) (hcz : cz ≤ dot nℓ b - 1) :
    ∃ b' ∈ B, dot nℓ b' = dot nℓ b - 1 := by
  have hbmem : b ∈ Nivat.LE2.halfStrip B vl := ⟨b, hb, 0, by simp⟩
  have hlev : dot nℓ (b + u') = dot nℓ b - 1 := by rw [dot_add, hstep]; ring
  have hstepmem : b + u' ∈ Nivat.LE2.halfStrip B vl := hstepIn b hbmem (by rw [hlev]; omega)
  obtain ⟨b', hb', hb'eq⟩ := dot_eq_of_mem_halfStrip hperp hstepmem
  exact ⟨b', hb', by rw [← hb'eq, hlev]⟩

/-- **A single missing level refutes `hstepIn`** (contrapositive of `exists_level_pred_of_stepIn`).

原文：b3_colle2.txt:472, :474 — item (i)/(ii): `B_i ⊇ [-i+1, i-1]² ∩ ℋ(ℓ^{(-)})`

This is the operational form.  It says: to discharge `hstepIn` you must first establish that
`B` has no `nℓ`-level gaps above `cz`.  **Lattice convexity of `B` is not enough** — take
`nℓ = (0,1)`, `B = {(0,0), (1,2)}`: it is lattice convex (the segment carries no interior
lattice point because `gcd(1,2) = 1`) yet level `1` is empty, so `hstepIn` fails for it at
any `cz ≤ 1`.  The occupancy has to come from Collé's item (ii) at `:474`, which is precisely
the hypothesis that makes `B_i` grow in every direction. -/
theorem not_stepIn_of_level_gap {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0) (hstep : dot nℓ u' = -1)
    {b : ℤ × ℤ} (hb : b ∈ B) (hcz : cz ≤ dot nℓ b - 1)
    (hgap : ∀ b' ∈ B, dot nℓ b' ≠ dot nℓ b - 1) :
    ¬ (∀ z ∈ Nivat.LE2.halfStrip B vl,
        cz ≤ dot nℓ (z + u') → z + u' ∈ Nivat.LE2.halfStrip B vl) := by
  intro hstepIn
  obtain ⟨b', hb', hb'eq⟩ := exists_level_pred_of_stepIn hperp hstep hstepIn hb hcz
  exact hgap b' hb' hb'eq

/-- **Iterated form: `hstepIn` fills every level from `b` down to `cz`** (`:472`, `:804`).

原文：b3_colle2.txt:804 — "proceeding this way, we get by induction that …"

The induction of the paper walks one line down at a time; this lemma is the statement that
the walk never falls off `B`.  Given a point `b ∈ B` and any level `c` with `cz ≤ c ≤ dot nℓ b`,
`B` has a point at level `c`. -/
theorem exists_level_of_stepIn {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : dot nℓ vl = 0) (hstep : dot nℓ u' = -1)
    (hstepIn : ∀ z ∈ Nivat.LE2.halfStrip B vl,
      cz ≤ dot nℓ (z + u') → z + u' ∈ Nivat.LE2.halfStrip B vl)
    {b : ℤ × ℤ} (hb : b ∈ B) :
    ∀ k : ℕ, cz ≤ dot nℓ b - (k : ℤ) → ∃ b' ∈ B, dot nℓ b' = dot nℓ b - (k : ℤ) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨b, hb, by simp⟩
  | succ n ih =>
      intro hle
      have hle' : cz ≤ dot nℓ b - (n : ℤ) := by push_cast at hle ⊢; omega
      obtain ⟨b', hb', hb'eq⟩ := ih hle'
      have hcz' : cz ≤ dot nℓ b' - 1 := by rw [hb'eq]; push_cast at hle ⊢; omega
      obtain ⟨b'', hb'', hb''eq⟩ := exists_level_pred_of_stepIn hperp hstep hstepIn hb' hcz'
      refine ⟨b'', hb'', ?_⟩
      rw [hb''eq, hb'eq]; push_cast; ring

#print axioms dot_eq_of_mem_halfStrip
#print axioms exists_level_pred_of_stepIn
#print axioms not_stepIn_of_level_gap
#print axioms exists_level_of_stepIn

end Nivat.ConeStepIn
