/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1SweepBridge
import Nivat.External.Colle.HbaseFlatSeed

/-!
# Lane Aparts: auditing the two `wedgeResidualR` survivors

Four of the six `wedgeResidualR` producers on the chain are now refuted
(`L1SweepBridge.lean` §21/§23: `_of_hwin` (`:341`), `_of_hwinHole` (`:503`), `_of_hwinHoleE`
(`:654`), `_of_hwinHoleZ` (`:873`), all vacuous at `S = d.Sphi` via
`not_hwin_hole_arg_of_case1`/`not_hwinHole_of_case1`/`not_hwinHoleE_of_case1`/
`not_hwinHoleZ_of_case1`). Two survive: `wedgeResidualR_of_case1_holes` (`:111`) and
`wedgeResidualR_of_hwin_corner_place` (`:235`). Task: map their live gaps, and specifically test
whether either collapses into the refuted `HwinHole`/`HwinHoleE`/`HwinHoleZ` family before
looking for anything else.

## 1. What each survivor's hypotheses are, and where they're discharged

Both share the same `hξ d hSgen hcase1 hvl_prim hp_mem hp_ne hdet_vl hunimod` prefix, all of
which `exists_hD_of_case1`/`exists_vertex_of_generating` discharge from `RegionSteps`' own
hypotheses (unchanged from the four refuted producers — not re-audited here).

* **`wedgeResidualR_of_case1_holes` (`:111`)**: the *entire* remaining content is the explicit
  `holes` binder (`:119-144`), an unproven hypothesis parameter:
  `∀ B u c a, a ∈ S → LatticeConvex (S.erase a) → 0 < c → (halfStrip periodicity) →`
  `∃ b₀ ∈ B, HOLE1(hwin, at the plain u', no shear, no extremality) ∧ HOLE2(hcover, Fig. 11(B))`.
  Consumed once, at the call site (`:151`), against exactly the `B u c a` that `exists_hD_of_case1`
  and `exists_vertex_of_generating` hand out. No other consumer exists on the tree — `holes` is
  never supplied, so this theorem currently has no way to fire.

* **`wedgeResidualR_of_hwin_corner_place` (`:235`)**: same `holes` shape but with HOLE2 split into
  `hcorner` (top-level binder, `:245-246`, now Lstrad's territory — see below) and a `holes`
  binder (`:247-266`) whose second conjunct is `place` (`hmin`/`hattain` at whatever `N` the
  caller reaches), not the opaque `hcover` containment. `holes` here also gains `B.Finite`
  (`:251`) as a premise, discharged for free at the call site (`:273-274`,
  `HbaseFlatSeed.finite_of_envOf_Sphi`). `hcorner`'s producer: per the dispatch, Lstrad's
  `HbaseBridge.exists_shear_hlt_and_doubly_lower_detMax` (not re-verified here, out of scope —
  read-only file). `place`'s producer: `MaxIndexProbe.exists_N₀_hmin_hattain`, already cited in
  the module docstring (`:182-183`) and consumed inline (`L1SweepBridge.lean:289`, via `hplace`).
  **What is left unproven in this survivor is exactly `holes`'s HOLE1 — the same `hwin`-shape as
  in the other survivor**, now with `B.Finite` added but still no `K`, no extremality.

So both survivors reduce to the *same* live gap: `holes`'s HOLE1, an `hwin` fact at the plain
(unsheared) `u'`, for whatever vertex `a` `LatticeConvex (S.erase a)` hands out — no shear
quantifier, no extremality hypothesis on `a`, and (for the first survivor) no finiteness or
envelope constraint on `B` either.

## 2. Does HOLE1 collapse into the refuted `HwinHole`/`HwinHoleE`/`HwinHoleZ` family?

**No — checked by binder comparison, not by name.** `HwinHole ξ S vl` (`L1SweepBridge.lean:487`)
is `∃ u', hunimod ∧ ∀ B u c a K, [ha, hconvS, hc, B.Finite, hamin-at-(u'-K•vl), hD] →`
`∃ b₀ ∈ B, hwin-at-(u'-K•vl)`. Three structural differences from `holes`'s HOLE1, each one of
them load-bearing in the refutation that killed `HwinHole`:

1. **`∀ K` is absent from `holes`.** `not_hwinHoleZ_of_case1`'s proof (§21/§22,
   `L1SweepBridge.lean:1770-1779`) derives its contradiction from `K` being forced arbitrarily
   large (`hKpos : 2*Mn + 2 ≤ K`) and then applying `hamin`/`hK` *at that same unbounded `K`* to
   get a numeric contradiction (`nlinarith`). A statement with no `∀ K` — one fixed instance, the
   unsheared `u'` — gives the refutation nothing to unbound.
2. **`hamin` (the extremality premise `∀ b ∈ S, dot (expNormal (u'-K•vl) vl) a ≤ dot (…) b`) is
   absent from `holes`.** The same contradiction derivation uses `hamin` directly at line 1771
   (`hcmp := hamin z hz`). Without it as a hypothesis, `holes`'s HOLE1 is neither implied by nor
   equivalent to `HwinHole`'s inner statement at any fixed `K` — it is a different obligation
   (fewer hypotheses feeding the same conclusion shape), not a weaker rung on the same ladder.
3. Consequently `holes`'s HOLE1 is not `HwinHole`/`HwinHoleE`/`HwinHoleZ` specialized at `K = 0`
   either: specializing the refuted family at one `K` still keeps `hamin` as a hypothesis, which
   `holes` does not have. No substitution or specialization of the refuted `Prop`s produces
   `holes`'s exact statement.

I did not find (nor did I expect, given points 1–2) an `Iff.rfl` or an `exact` term connecting
`holes`'s HOLE1 to any member of the refuted family — the binder lists differ in ways that are
exactly the ones the refutation's proof term uses, so no such term should exist. **Verdict:
neither survivor collapses into the refuted family.** `PROTOCOL.md` §23 applies in reverse here:
the absence of a collapse is as important a fact as a collapse would have been, and it rests on
reading the *proof*, not just the *statement*, of `not_hwinHoleZ_of_case1`.

## 3. Does HOLE1 have any producer at all?

**Conclusion-shape search**: `grep -n "hwin\|halfStrip.*Set.range\|Set.range.*halfStrip"` across
`Nivat/External/Colle/*.lean`, filtered to declarations whose *conclusion* directly produces
`∃ b₀ ∈ B, ∀ i j z, z + (enum i j - a) ∈ halfStrip … ∪ …` **without an outer `∀ K` and without an
`hamin` hypothesis** (the two features that distinguish `holes`'s HOLE1 from every member of the
refuted ladder). One family of declarations matches this shape exactly:
`HbaseFlatSeed.not_hwin_seed_forall` / `not_exists_enum_hwin_seed` / `not_hwin_seed`
(`HbaseFlatSeed.lean:1097/1121/1142`) — **not producers, refutations**, but refutations of the
*identical* unsheared, no-extremality `hwin` shape `holes`'s HOLE1 asks for, at the concrete
witness `S = {(0,0),(1,0),(2,0)}`, `a = (0,0)`, `B = {(0,0)}`, `vl = (0,1)`: no enumeration at
all — universally quantified, so `coverEnum` is not a special case being dodged — can satisfy it.

**This is not yet a refutation of `holes` on the chain, and I want to say precisely why not,
rather than overclaim.** `not_hwin_seed_forall` refutes the *abstract* `Prop` at a hand-picked
`(S, B, a, vl)` triple with no accompanying `ξ`, `u`, `c`, or `hD` (halfStrip-periodicity) witness
— it never shows this triple is *reachable* as the actual `(B, u, c, a)` that `exists_hD_of_case1`
and `exists_vertex_of_generating` hand out for some genuine `Case1 ξ xper d.Sphi vl` instance.
`HbaseFlatSeed.envOf_holds_and_hwin_seed_refuted` (`:1305`) ran into exactly this limit already,
for the closely related `HwinHoleE`-shaped hole, and its own docstring says so explicitly
(`:1292-1296`): "This does not kill `hwin` for the real chain... the gap is a missing lemma tying
`S` to `Sphi`, not a proof obligation dischargeable from `EnvOf` alone." The same caveat applies
here, doubly, since `holes`'s HOLE1 has *no* `EnvOf`/`B.Finite` constraint at all (for
`wedgeResidualR_of_case1_holes`) or only `B.Finite` without `EnvOf` (for
`wedgeResidualR_of_hwin_corner_place`, `:251`), so the toy witness's `B = {(0,0)}` is not even
screened out by those premises — it would need to be excluded by `LatticeConvex (S.erase a)`,
`0 < c`, or `hD` instead, none of which I traced against a real `ξ`. **I did not find, and am not
claiming, a chain-level counterexample; I found that the abstract shape of the gap is identical to
one already on file, and the same embedding question (does this toy data arise from a real
`DecompDataZ`/`Case1` instance) is open for both.**

Beyond this refutation family, the shape search found no *positive* producer of `holes`'s HOLE1
anywhere in the tree — every other declaration matching `hwin`'s conclusion shape either carries
the `∀ K`/`hamin` structure of the refuted ladder, or is itself an explicit unproven hypothesis
parameter (as `holes` itself is), never a closed proof term.

## Summary

Both survivors reduce to the same single live gap (`holes`'s HOLE1: `hwin` at the plain `u'`, no
shear, no extremality). It is a distinct proposition from the refuted `HwinHole` ladder — checked
by comparing proof terms, not just statements — so §21/§23's refutation does not extend to either
survivor as the dispatch worried it might. It has no positive producer on the tree. The closest
thing on file is a refutation of the identical abstract shape at a hand-picked witness
(`HbaseFlatSeed.not_hwin_seed_forall`), whose applicability to the actual chain is blocked on the
same unresolved "does this witness arise from a real `Case1` instance" question that already
stalled a structurally identical attempt against `HwinHoleE`.

## 4. The watershed question: can the toy witness embed into a real `d.Sphi`?

**Team-lead's conjecture (2026-09-20)**: the toy witness `S = {(0,0),(1,0),(2,0)}` is
**collinear** (three points on a line, 1-dimensional), while `d.Sphi` from a `Case1`-satisfying
`DecompDataZ` must be **2-dimensional** because it's a zonotope with `2 ≤ d.m` and pairwise
non-parallel periods — so the toy witness **cannot embed** into any real `d.Sphi`, and the
refutation is blocked on an impossible precondition.

**Status: the conjecture is correct in direction but not yet kernel-verified.** The structural
facts supporting it:

1. **`d.Sphi` is a zonotope over non-parallel periods.** `DecompData.Sphi_eq` (`:108`) states
   `Conv d.Sphi = Conv (supp (∏ i : Fin d.m, (mono (d.h i) - 1)))`, and `h_dir` (`:104`) requires
   `∀ i j, i ≠ j → det (d.h i) (d.h j) ≠ 0` (pairwise non-parallel). Combined with `hm : 2 ≤ d.m`
   (`:89`), this means `d.Sphi` is the convex hull of the support of a product of at least two
   Laurent monomials with non-parallel exponent vectors — a zonotope spanned by at least two
   linearly independent directions.

2. **The toy witness is 1-dimensional.** `S = {(0,0),(1,0),(2,0)}` lies on the line `{(x,0) : x ∈ ℤ}`,
   so `Conv S ⊆ {(x,0) : x ∈ ℝ}` (a line segment), and `S` itself has affine dimension 1.

3. **A 1-dimensional set cannot embed into the interior of a 2-dimensional one.** If `S ⊆ d.Sphi`
   and both are convex, then `Conv S ⊆ Conv (d.Sphi)`, so a line segment would sit inside a
   2-dimensional zonotope — possible only if `S` lies on the boundary, never spanning the interior.
   But more directly: **a zonotope generated by `m ≥ 2` non-parallel vectors in ℤ² contains points
   not on any line through the origin** (e.g., `h₁ + h₂` for `det(h₁, h₂) ≠ 0`), while any subset
   of a line through the origin is collinear. So if `d.Sphi` is such a zonotope, it cannot equal
   or be a subset of any collinear set — in particular, it cannot equal `{(0,0),(1,0),(2,0)}`.

**What is missing for a kernel receipt**: the above is a **reading of the definitions**, not a
compiled theorem. To turn it into a chain-level refutation of `∃ enum, hwin` at `d.Sphi`, one
would need:

* A lemma `not_collinear_Sphi_of_hm_and_hdir : ∀ (d : DecompData η), 2 ≤ d.m → (∀ i j, i ≠ j →
  det (d.h i) (d.h j) ≠ 0) → ¬ (∃ u : ℤ × ℤ, u ≠ 0 ∧ ∀ z ∈ d.Sphi, ∃ t : ℤ, z = t • u)`, stating
  that `d.Sphi` is not contained in any line through the origin.
* A specialization showing `{(0,0),(1,0),(2,0)} ⊆ {(t,0) : t ∈ ℤ}` (the `x`-axis), hence collinear
  along `(1,0)`.
* A bridge from "the `S` in `not_hwin_seed_forall` is collinear" plus "every `d.Sphi` is
  non-collinear" to "no `d.Sphi` can equal that `S`", and hence `not_hwin_seed_forall`'s
  refutation cannot fire at any real `Case1` instance.

None of these three pieces currently exists in the tree as a named, kernel-verified theorem. The
first (non-collinearity of `d.Sphi`) is the load-bearing one — it's a statement about the
zonotope's dimension, not about `hwin`, so it belongs in `DecompData.lean` or a geometry file, not
here. The second and third are one-liners given the first. **Without the first, the watershed
question remains open**: we have a toy refutation of the abstract `hwin` shape, and a plausible
geometric argument that the toy witness is unreachable, but no kernel receipt that the two connect.

**Consequence if the conjecture holds (and is proved)**: `∃ enum, hwin(enum)` at the real `d.Sphi`
would be **undecided** — the toy refutation doesn't apply (wrong `S`), and no other refutation or
proof exists. Both `wedgeResidualR` survivors remain gated on this unproven `hwin` obligation, with
no known attack beyond "try to prove `hwin` directly at a concrete `d.Sphi` instance, or find a
2-dimensional counterexample." The L1 encoding is not dead (as it would be if the toy refutation
applied), but it's stalled on a gap with no clear closure path.
-/

set_option autoImplicit false

open Nivat Nivat.LE2 Nivat.L1SweepBridge Nivat.HbaseFlatSeed

-- Confirm every claim above fresh this window: the two survivors' exact types, the refuted
-- family's exact types, and the refutation-shape witness's exact type.

#check @Nivat.L1SweepBridge.wedgeResidualR_of_case1_holes
#check @Nivat.L1SweepBridge.wedgeResidualR_of_hwin_corner_place
#check @Nivat.L1SweepBridge.HwinHole
#check @Nivat.L1SweepBridge.HwinHoleE
#check @Nivat.L1SweepBridge.HwinHoleZ
#check @Nivat.L1SweepBridge.not_hwin_hole_arg_of_case1
#check @Nivat.L1SweepBridge.not_hwinHole_of_case1
#check @Nivat.HbaseFlatSeed.not_hwin_seed_forall
#check @Nivat.HbaseFlatSeed.not_exists_enum_hwin_seed
#check @Nivat.HbaseFlatSeed.envOf_holds_and_hwin_seed_refuted
