/-
Copyright (c) 2026 Nivat formalisation project.
-/
import Nivat.External.Colle.ANormal
import Nivat.External.Colle.Claim47Core

/-!
# `hsweep` (`ChainDataGeomParts.hsweep : dot nJ vJ1 < 0`) — is the ledger lead right?

Dispatch: leaf A's `ChainDataGeomParts` (`ChainPartsFeed.lean:275-330`) has 24 obligations;
Aparts classified 15 of the 17 owed ones as blocked behind Collé item (ii) / the base
recursion `B (i+1) := A i`.  Of the remaining two, `nfp_L` is being landed elsewhere; this file
attacks the other, `hsweep : dot nJ vJ1 < 0`, a bare placement inequality on the two *data*
fields `nJ vJ1 : ℤ × ℤ` with no `A`/`B` anywhere in its statement.

`blueprint/LEAF-A.md:1481` records a lead: "leaf C's `hsweep` is closable by instantiating
`case1_sweep`".  Step 1 below checks that lead **as types, not as prose**, against the actual
field.  It does not meet.

## Step 1: the ledger's `hsweep` is a different proposition (name collision, not the same field)

`ChainDataGeomParts.hsweep` (`ChainPartsFeed.lean`) has type

    dot nJ vJ1 < 0

a bare `Prop`, no binders, no quantifiers: a decidable fact about two fixed vectors.

`RegionSteps.lean:1704 case1_sweep`'s conclusion — and `RegionClaim411.lean:367
region_of_claim411_of_sweep`'s own locally-named `hsweep` binder, which is what
`LEAF-A.md:1481` actually cites (matching `case1_sweep`'s conclusion verbatim) — has type

    ∀ q : ℕ, 0 < q →
      (∀ g ∈ B, ∀ t : ℤ, τ + (pw : ℤ) ≤ t → ϑ (g + (t + (q:ℤ)) • cg.vJ) = ϑ (g + t • cg.vJ)) →
      ∃ K : Set (ℤ × ℤ), K ⊆ cg.toChainData.shellInf ε ∧ Colle41.IsRegion K p cg.vJ ∧
        K.Nonempty ∧ ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn ϑ K (((t₀ * q : ℕ) : ℤ) • cg.vJ)

a `∀ q, 0 < q → (…) → ∃ K, …` periodicity-implies-region-with-period statement.  These are not
two differently-parametrised instances of one shape; they are categorically different logical
shapes (one is quantifier-free, the other is a nested `∀/∃` implication with an existential
witness of a whole region).  **`LEAF-A.md:1481`'s lead is entirely about `RegionClaim411.lean`'s
`hsweep` (leaf C), not about `ChainDataGeomParts.hsweep` (leaf A).**  The two obligations share
an English name and nothing else — an instance of the "one物多名" trap catalogued in
`NOTATION.md`.  So step 1's verdict is: **they don't meet**, and the reason is that they were
never the same obligation to begin with.

## Step 3: what does produce `dot nJ vJ1 < 0`?

Two candidate routes, with different verdicts.

**Route A — `ChainDataGeom.dot_nJ_vJ1_neg` (`ANormal.lean:747`).**  This is a genuine on-tree
theorem with exactly the right conclusion, `dot cg.nJ cg.vJ1 < 0`, for `cg : ChainDataGeom η xper
vl p S gen`.  Its proof, read in full at `ANormal.lean:749-765`, obtains its two key facts from
`cg.bottom 0` (`ChainGeom.lean`'s `bottom` field, which quantifies over `⋃ i, hatOf A kk vl i` —
Collé's `Â_∞`) and from `cg.ahat_halfPlane`.  **`bottom` is itself one of the 17 owed, recursion-
blocked obligations of `ChainDataGeomParts`** (it is a "region obligation" stated over the same
`A`-indexed union that Aenvfix's counterexample and `ItemII.lean:396 not_itemII_of_chain` say the
finite-seed recursion cannot produce).  So Route A, read honestly, **secretly needs the
recursion**: it is not a free-standing producer of `hsweep`, it is a corollary of already having
a complete `ChainDataGeom`, `bottom` included.  Citing it as "the" producer of `hsweep` would
smuggle item (ii) back in under a different obligation's name — exactly the miscalibration the
dispatch asked to watch for.

**Route B — `nJ` and `vJ1` are free *data* fields, not derived ones.**  Unlike `bottom`,
`ChainDataGeomParts.nJ : ℤ × ℤ` and `.vJ1 : ℤ × ℤ` are declared as *data*, not as obligations: an
assembler is free to choose their values before discharging `hsweep`.  Read this way `hsweep` is
not a theorem to prove about *the* `nJ`/`vJ1` of some already-built chain — it is a placement
condition on a choice the assembler makes.  Every complete inhabitant currently on the tree
already discharges it exactly this way, by concrete computation on a chosen pair, never via
Route A: `Nivat.ShellConvex.cgc_dot_nJ_vJ1 : dot cgc.nJ cgc.vJ1 = -2` (`ShellConvex.lean:867`),
`Nivat.ShellMink.chainBShellNeg_dot_nJ_vJ1_neg : dot chainBShellNeg.nJ chainBShellNeg.vJ1 = -1`
(`ShellMink.lean:886`), and `Nivat.ColleStep.PeriodsRays2.cgw` (`Step_PeriodsRays2.lean:233`,
`nJ = (0,1)`, `vJ1 = (0,-1)`) all instantiate `dot_nJ_vJ := by simp […]`-style and separately
verify the sign by `simp`/`decide` on concrete numerals — not by invoking `dot_nJ_vJ1_neg`.

`exists_hsweep_witness` below is the general fact those ad-hoc computations are all instances
of: for **any** nonzero `vJ1`, taking `nJ := -vJ1` discharges `hsweep` unconditionally, by
`dot_self_pos` alone — no `bottom`, no `A`, no `B`.  (This is *not* claimed to be the `nJ` a real
assembly needs — `nJ` is separately constrained by `dot_nJ_vJ = 0`, `nJ_prim`, `dot_nJ_p ≠ 0`;
those are the *other* placement obligations `NOTATION.md`'s `n_L` vs `nJ` entry already flags as
un-merged with this one.  What this lemma shows is only that `hsweep` in isolation imposes no
obstruction: it is satisfiable for every nonzero sweep direction, freely, with no recursion
input at all.)

## Calibration (do not oversell)

`hsweep`, taken alone, was never blocking anything: it is a decidable fact about a free choice,
solved below unconditionally.  The two-loose-ends count in the dispatch shrinks from 2 to 1
(`nfp_L` remains, landed elsewhere).  **This does not touch item (ii) or the recursion.**  What
it does establish is the intended calibration fact itself: of leaf A's 17 owed fields, the
residual after this file is *purely* recursion-blocked fields (`bottom` among them) — `hsweep`
is not, and never required, a special argument beyond the one landed here.  Route A above stays
on the tree unmodified; it is correctly stated, just not the right citation for a recursion-free
closure of `hsweep`.
-/

set_option autoImplicit false

namespace Nivat.HsweepFeed

open Nivat
open Nivat.LE2 (dot)

/-- **`hsweep` is unconditionally satisfiable, for any nonzero sweep direction, with no
recursion input.**  Taking `nJ := -vJ1` gives `dot nJ vJ1 = -dot vJ1 vJ1 < 0` by
`Nivat.ColleReg.dot_self_pos` alone.  This is the general fact underlying every concrete
`dot_nJ_vJ1`-style computation already on the tree (`ShellConvex.lean:867`,
`ShellMink.lean:886`, `Step_PeriodsRays2.lean:233`), none of which invoke
`ChainDataGeom.dot_nJ_vJ1_neg` (`ANormal.lean:747`) — that theorem is available but, as the file
docstring above records, its proof consumes `cg.bottom`, a recursion-blocked field, so it is not
a recursion-free route to this fact. -/
theorem exists_hsweep_witness {vJ1 : ℤ × ℤ} (hvJ1 : vJ1 ≠ 0) :
    ∃ nJ : ℤ × ℤ, dot nJ vJ1 < 0 :=
  ⟨-vJ1, by
    have hpos : 0 < dot vJ1 vJ1 := Nivat.ColleReg.dot_self_pos hvJ1
    rw [Nivat.LE2.dot_neg_left]
    linarith⟩

/-- Concrete instance, matching the shape of the tree's existing complete inhabitants
(`nJ = (0,1)`, `vJ1 = (0,-1)`, `Step_PeriodsRays2.lean:233`) — the witness
`exists_hsweep_witness` produces at `vJ1 := (0,-1)` is literally `nJ := -(0,-1) = (0,1)`. -/
theorem hsweep_concrete_witness : dot ((0, 1) : ℤ × ℤ) (0, -1) < 0 := by
  decide

section AxiomReceipts

#print axioms Nivat.HsweepFeed.exists_hsweep_witness
#print axioms Nivat.HsweepFeed.hsweep_concrete_witness

end AxiomReceipts

end Nivat.HsweepFeed
