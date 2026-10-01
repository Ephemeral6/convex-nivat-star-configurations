/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.Generating
import Nivat.External.Colle.HbaseBridge
import Nivat.External.Colle.Claim36
import Nivat.External.Colle.MinkowskiEdges
import Nivat.External.Colle.L3Band
import Nivat.External.Colle.NewtonZonotope

/-!
# From "no edge with normal `n₀`" to a generating vertex

`Nivat.HbaseBridge.hbase_of_sweep_self`'s first residual is
`hgen : Nivat.Colle.GeneratesAt ξ S a`, and `Nivat.Colle.IsGeneratingSet` (`Generating.lean:58`)
only hands out `GeneratesAt` at sites `a` where `LatticeConvex (S.erase a)` — i.e. at
*vertices* of `S` (`Nivat.LE2.IsColleVertex`, `LatticeEdges.lean:352`), not at an arbitrary
point of `S`.  This file supplies the missing existence step: given a direction `n₀` at which
`S` has **no edge**, `S` has a vertex whose exposed face in direction `n₀` is that single point,
and that vertex generates.

## The five-step chain (all facts below are already on-chain; this file only assembles them)

1. `Nivat.LE2.face_nonempty` (`LatticeEdges.lean:339`) — for a finite nonempty `R`, `face R n`
   is nonempty for *every* `n`, unconditionally.
2. `¬ IsEdge (↑S) n₀` together with `Prim n₀` forces `face (↑S) n₀` to fail `Set.Nontrivial`,
   i.e. every two of its points coincide.
3. Nonempty + no two points distinct ⟹ `face (↑S) n₀ = {g}` for the witness `g` from step 1,
   i.e. `Nivat.LE2.IsVtx (↑S) g`.
4. `Nivat.LE2.isColleVertex_of_isVtx` (`LatticeEdges.lean:380`) turns `IsVtx (↑S) g` (with
   `LatticeConvex S`) into `IsColleVertex S g`, i.e. `g ∈ S ∧ LatticeConvex (S.erase g)`.
5. Feed the second half into `IsGeneratingSet`'s third conjunct to get `GeneratesAt ξ S g`.

The whole chain never inspects `ξ` — it is pure lattice convex geometry, exactly like
`LatticeEdges.lean` itself.  Where `n₀` comes from (Lemma 2.6's output, in the ℤ-coefficient
or `ZMod p` case) is a separate, not-yet-formalised question; this file is agnostic to it.

## Delivery shape (binding, per team agreement 2026-09-19)

`claim43_periodOn_of_sweep` (`Claim43.lean:435`) binds `S`/`a` *before* `D`/`enum`, and its
`hwin` hypothesis is stated in terms of `S.erase a`.  So `enum` may depend on the chosen vertex
`a`, but `a` itself must never depend on `enum`/`D`.  Consequently every theorem below that
produces a vertex exposes it as an **existential** — `∃ a, ...` — never a pre-committed value;
consumers must `obtain ⟨a, ha⟩` first and build their own `enum`/`D` inside that scope.
-/

set_option autoImplicit false

namespace Nivat.VertexFromEdge

open Nivat Nivat.LE2 Nivat.Colle

/-! ## §1  No edge with normal `n₀` ⟹ a vertex -/

/-- **Step 1–3 of the chain.**  If `S` is finite and nonempty and has no edge with (primitive)
normal `n₀`, then `S` has a vertex — a point `g` whose exposed face in direction `n₀` is exactly
`{g}`.  Delivered as an existential: nothing here can name `g` ahead of receiving this proof. -/
theorem isVtx_of_not_isEdge {S : Finset (ℤ × ℤ)} (hne : S.Nonempty) {n₀ : ℤ × ℤ}
    (hprim : Prim n₀) (hno : ¬ IsEdge (↑S : Set (ℤ × ℤ)) n₀) :
    ∃ g, IsVtx (↑S : Set (ℤ × ℤ)) g := by
  have hfin : (↑S : Set (ℤ × ℤ)).Finite := S.finite_toSet
  have hSne : (↑S : Set (ℤ × ℤ)).Nonempty := by simpa using hne
  obtain ⟨g, hg⟩ := face_nonempty hfin hSne n₀
  have hsingle : ∀ z ∈ face (↑S : Set (ℤ × ℤ)) n₀, z = g := by
    intro z hz
    by_contra hzne
    exact hno ⟨hprim, ⟨z, hz, g, hg, hzne⟩⟩
  have heq : face (↑S : Set (ℤ × ℤ)) n₀ = {g} := by
    ext z
    simp only [Set.mem_singleton_iff]
    exact ⟨hsingle z, fun h => h ▸ hg⟩
  exact ⟨g, n₀, hprim, heq⟩

/-! ## §2  A vertex generates -/

/-- **Step 4–5 of the chain, the deliverable.**  If `S` is a Collé generating set for `ξ`
(`IsGeneratingSet`, `Generating.lean:58`) and `S` has no edge with normal `n₀`, then `S` has a
site that `GeneratesAt ξ`.  This is exactly `HbaseBridge.hbase_of_sweep_self`'s `hgen` slot,
demonstrated by feeding it in `§3` below. -/
theorem exists_generatesAt_of_not_isEdge {A : Type*} {ξ : Config A} {S : Finset (ℤ × ℤ)}
    (hSgen : IsGeneratingSet ξ S) {n₀ : ℤ × ℤ} (hprim : Prim n₀)
    (hno : ¬ IsEdge (↑S : Set (ℤ × ℤ)) n₀) :
    ∃ a, GeneratesAt ξ S a := by
  obtain ⟨hne, hconv, hgen⟩ := hSgen
  obtain ⟨g, hvtx⟩ := isVtx_of_not_isEdge hne hprim hno
  have hcv : IsColleVertex S g := isColleVertex_of_isVtx hconv hvtx
  exact ⟨g, hgen g hcv.1 hcv.2⟩

/-! ## §3  Kernel check that this is `HbaseBridge`'s `hgen` slot, not merely "equivalent" to it

Per protocol §27, "this is the same slot" is only evidence once the elaborator has checked a
term that plugs one into the other.  Below, `exists_generatesAt_of_not_isEdge`'s output is
`obtain`-ed for its witness `a`, and that witness plus the caller's `D`/`enum`/`hK` (with `hwin`
built *after* `a` is in scope, honouring the binding order above) are fed directly into
`Nivat.HbaseBridge.hbase_of_sweep_self`.  If the shapes had drifted this would fail to
elaborate. -/

open Nivat.Colle41 Nivat.ColleReg in
/-- `hbase_of_sweep_self`'s residual `hgen`, discharged from "no edge with normal `n₀`" instead
of being assumed outright.  The caller still supplies `hwin` themselves, but only after
receiving the vertex `a` — `hwin_fn` is a function of `a`, exactly as the binding order of
`claim43_periodOn_of_sweep` requires.  `_hc0 : c ≠ 0` is threaded through unused: Cclaim's
2026-09-19 15:01 measurement turned it from a consequence of `hinf` into a binder upstream of
`ofWedgeAt`'s assembly, so this signature carries it too rather than silently dropping it
(Cprobe: `c`'s sign is free, `p ↦ -p` is cost-free, so callers may WLOG `0 < c`). -/
theorem hbase_of_sweep_of_not_isEdge {ξ : Config ℤ} {e : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hSgen : IsGeneratingSet ξ S) {n₀ : ℤ × ℤ} (hprim : Prim n₀)
    (hno : ¬ IsEdge (↑S : Set (ℤ × ℤ)) n₀)
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {c : ℤ} (_hc0 : c ≠ 0)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin_fn : ∀ a : ℤ × ℤ, a ∈ S →
      ∀ i j : ℕ, ∀ z ∈ S.erase a,
        z + (enum i j - a) ∈
          D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ 0) (c • vl) := by
  obtain ⟨a, ha⟩ := exists_generatesAt_of_not_isEdge hSgen hprim hno
  exact Nivat.HbaseBridge.hbase_of_sweep_self ha hD enum (hwin_fn a ha.1) hK

/-! ## §4  Where `n₀` comes from: `Claim36.generatingSet_no_edge_parallel`, not `lemma26_int`

`Nivat.L1Base.lemma26_int` (`L1Base.lean:253`) concludes `∃ i, dot ℓ (h i) = 0` — an existential
over *which period direction* `h i` is orthogonal to a `NonExpansiveLine` direction `ℓ`.  That is
a different object from `IsEdge (↑S) n₀`: `h i` ranges over annihilator periods, not over edge
normals of the finset `S`, and the conclusion's polarity is positive ("some `h i` is ⊥ `ℓ`"), not
the negative "`n₀` is not an edge normal" that `isVtx_of_not_isEdge` needs.  `lemma26_int` does
not discharge `hno`, for a structural reason, not a coefficient-ring reason.

What *does* discharge it is `Nivat.Colle36.generatingSet_no_edge_parallel` (`Claim36.lean:741`),
entirely over `ℤ`: it says every edge normal `n` of a zonotope-hull finset `S` has
`dot n ℓ_m ≠ 0`.  Contrapositive: any primitive `n₀` with `dot n₀ ℓ_m = 0` (e.g. the
`exists_prim_orthogonal` witness, `MinkowskiEdges.lean:397`) is not an edge normal of `S`. -/

open Nivat.LE2 in
/-- **The connecting term (protocol §27): fed through the elaborator, not merely asserted.**
Given the zonotope-hull hypothesis `Claim36.generatingSet_no_edge_parallel` needs, any primitive
`n₀` orthogonal to `ℓ_m` supplies `hno`, hence a vertex — with no `lemma26_int` and no `ZMod p`
anywhere in the chain. -/
theorem not_isEdge_of_hull_eq_conv_supp_prod {m : ℕ} (hm : 2 ≤ m) {h : Fin m → ℤ × ℤ}
    (hh_ne : ∀ i, h i ≠ 0) (hh_dir : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0)
    {i_m : Fin m} {ℓ_m : ℤ × ℤ} (hℓ_prim : Primitive ℓ_m)
    (hℓ_dir : ∃ c : ℤ, c ≠ 0 ∧ h i_m = c • ℓ_m)
    {S : Finset (ℤ × ℤ)}
    (hS_hull : Conv S = Conv (supp (∏ i ∈ Finset.univ.erase i_m, (mono (h i) - 1 :
      LaurentTwo ℤ))))
    {n₀ : ℤ × ℤ} (_hprim : Prim n₀) (hperp : dot n₀ ℓ_m = 0) :
    ¬ IsEdge (↑S : Set (ℤ × ℤ)) n₀ := fun hedge =>
  Nivat.Colle36.generatingSet_no_edge_parallel hm hh_ne hh_dir hℓ_prim hℓ_dir hS_hull n₀
    (mem_E_iff.mpr hedge) hperp

open Nivat.LE2 in
/-- Composed with `isVtx_of_not_isEdge`: the zonotope-hull hypothesis alone (no `lemma26_int`,
no `ZMod p`) already yields a vertex of `S`. -/
theorem exists_isVtx_of_hull_eq_conv_supp_prod {m : ℕ} (hm : 2 ≤ m) {h : Fin m → ℤ × ℤ}
    (hh_ne : ∀ i, h i ≠ 0) (hh_dir : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0)
    {i_m : Fin m} {ℓ_m : ℤ × ℤ} (hℓ_prim : Primitive ℓ_m)
    (hℓ_dir : ∃ c : ℤ, c ≠ 0 ∧ h i_m = c • ℓ_m)
    {S : Finset (ℤ × ℤ)} (hne : S.Nonempty)
    (hS_hull : Conv S = Conv (supp (∏ i ∈ Finset.univ.erase i_m, (mono (h i) - 1 :
      LaurentTwo ℤ))))
    {n₀ : ℤ × ℤ} (hprim : Prim n₀) (hperp : dot n₀ ℓ_m = 0) :
    ∃ g, IsVtx (↑S : Set (ℤ × ℤ)) g :=
  isVtx_of_not_isEdge hne hprim
    (not_isEdge_of_hull_eq_conv_supp_prod hm hh_ne hh_dir hℓ_prim hℓ_dir hS_hull hprim hperp)

/-! ## §5  `hgen` closed: the `¬ IsEdge` premise is now discharged, not assumed

The two theorems below are what team-lead asked for by name: feed
`generatingSet_no_edge_parallel`'s conclusion through the elaborator into
`exists_generatesAt_of_not_isEdge`'s `hno` slot directly, so `hgen`'s existential is backed by a
producer instead of an unproven premise.  Nothing here inspects `ξ` beyond `IsGeneratingSet`
(no `lemma26_int`, no `ZMod p`); `hS_hull` is the one hypothesis nobody has discharged yet for a
concrete `𝒮_φ` (flagged to L3win/team-lead separately). -/

open Nivat.LE2 in
/-- `hgen`, closed: given the zonotope-hull hypothesis and a generating set `S`, produce a site
that actually `GeneratesAt ξ`. -/
theorem exists_generatesAt_of_perp {A : Type*} {ξ : Config A} {m : ℕ} (hm : 2 ≤ m)
    {h : Fin m → ℤ × ℤ} (hh_ne : ∀ i, h i ≠ 0)
    (hh_dir : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0)
    {i_m : Fin m} {ℓ_m : ℤ × ℤ} (hℓ_prim : Primitive ℓ_m)
    (hℓ_dir : ∃ c : ℤ, c ≠ 0 ∧ h i_m = c • ℓ_m)
    {S : Finset (ℤ × ℤ)} (hSgen : IsGeneratingSet ξ S)
    (hS_hull : Conv S = Conv (supp (∏ i ∈ Finset.univ.erase i_m, (mono (h i) - 1 :
      LaurentTwo ℤ))))
    {n₀ : ℤ × ℤ} (hprim : Prim n₀) (hperp : dot n₀ ℓ_m = 0) :
    ∃ a, GeneratesAt ξ S a :=
  exists_generatesAt_of_not_isEdge hSgen hprim
    (not_isEdge_of_hull_eq_conv_supp_prod hm hh_ne hh_dir hℓ_prim hℓ_dir hS_hull hprim hperp)

open Nivat.Colle41 Nivat.ColleReg in
/-- The full pipeline, `hbase_of_sweep_of_not_isEdge` specialised so its `hno` is itself
discharged by `generatingSet_no_edge_parallel`: no premise left un-produced except `hS_hull`. -/
theorem hbase_of_sweep_of_perp {ξ : Config ℤ} {e : ℤ × ℤ} {m : ℕ} (hm : 2 ≤ m)
    {h : Fin m → ℤ × ℤ} (hh_ne : ∀ i, h i ≠ 0)
    (hh_dir : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0)
    {i_m : Fin m} {ℓ_m : ℤ × ℤ} (hℓ_prim : Primitive ℓ_m)
    (hℓ_dir : ∃ c : ℤ, c ≠ 0 ∧ h i_m = c • ℓ_m)
    {S : Finset (ℤ × ℤ)} (hSgen : IsGeneratingSet ξ S)
    (hS_hull : Conv S = Conv (supp (∏ i ∈ Finset.univ.erase i_m, (mono (h i) - 1 :
      LaurentTwo ℤ))))
    {n₀ : ℤ × ℤ} (hprim : Prim n₀) (hperp : dot n₀ ℓ_m = 0)
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {c : ℤ} (hc0 : c ≠ 0)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin_fn : ∀ a : ℤ × ℤ, a ∈ S →
      ∀ i j : ℕ, ∀ z ∈ S.erase a,
        z + (enum i j - a) ∈
          D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ 0) (c • vl) :=
  hbase_of_sweep_of_not_isEdge hSgen hprim
    (not_isEdge_of_hull_eq_conv_supp_prod hm hh_ne hh_dir hℓ_prim hℓ_dir hS_hull hprim hperp)
    hc0 hD enum hwin_fn hK

/-! ## §6  `hS_hull` is unsatisfiable for the on-chain `S`; `¬ IsEdge` was never needed

**读法, kernel-checkable citations, not yet re-`#check`-ed by me this round — re-verify before
relying on the identifiers below.**  Team-lead's 2026-09-19 measurement: the `S` that is actually
on-chain at `RegionSteps.lean:1122/1182/1220/1759` (`Case1 ξ xper d.Sphi vl`) is `d.Sphi`
(`DecompDataZ.Sphi_eq`, `DecompData.lean:108`), built from the **full** product `∏ i : Fin m`
(`i_m` *included*).  `not_isEdge_of_hull_eq_conv_supp_prod`'s `hS_hull` instead needs the hull of
the product with `i_m` **erased** (Collé's `𝒮_ψ`, matching `Claim36.lean:741`'s own hypothesis).
Since `hℓ_dir : h i_m = c • ℓ_m`, the *full* zonotope has an edge parallel to `ℓ_m`, so `d.Sphi`
*does* have an edge with normal `n₀` — `hno` is false at `S := d.Sphi`, not merely unproven.
Baseline: `b3_colle2.txt:563-571`, Claim 3.6 is stated for `η − η̄_m` over `ℤ_p`, i.e. for `𝒮_ψ`
with the factor erased, which is why `§1`–`§5` above (`generatingSet_no_edge_parallel`'s route)
does not apply to the on-chain `S` — the paragraph these were transcribed from erases the factor
for a *different* sub-configuration than the one `Sphi_eq` builds.

None of `§1`–`§5` is retracted (`PROTOCOL.md` §14): the theorems are true as stated, and
`generatingSet_no_edge_parallel` may still be wanted elsewhere (e.g. directly for `Claim36`'s own
consumers). They are simply not the route to `hgen` for `d.Sphi`.

The route below needs no edge/zonotope/`ℓ_m` data at all: **every nonempty finite `S ⊆ ℤ²` has
some `IsVtx (↑S) g`**, via a normal `n := (1, N)` with `N` large enough that `dot n` is injective
on `S` (a generic linear functional separates any finite point set). -/

/-- **The general vertex-exposure step.** All that ever gets used of a "generic" normal is that
`dot n` is injective on `S` (plus `Prim n`, which `IsVtx` itself demands) — the specific witness
`(1, N)` below is just one way to build such an `n`.  Factored out per team-lead's 2026-09-19
17:2x request, so any other generic-normal producer (e.g. `HbaseBridge.exists_generic_normal`)
can be fed in directly without redoing the argmax argument. -/
theorem exists_isVtx_of_injOn {S : Finset (ℤ × ℤ)} (hne : S.Nonempty) {n : ℤ × ℤ}
    (hprim : Prim n) (hinj : Set.InjOn (dot n) (↑S : Set (ℤ × ℤ))) :
    ∃ g, IsVtx (↑S : Set (ℤ × ℤ)) g := by
  classical
  obtain ⟨g, hgS, hgmax⟩ := S.exists_mem_eq_sup' hne (fun z => dot n z)
  have hgmax' : ∀ z ∈ S, dot n z ≤ dot n g := by
    intro z hz
    have hle := Finset.le_sup' (fun z => dot n z) hz
    rw [hgmax] at hle
    exact hle
  have hface : face (↑S : Set (ℤ × ℤ)) n = {g} := by
    ext z
    simp only [mem_face_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzS, hzmax⟩
      have heq : dot n z = dot n g := le_antisymm (hgmax' z hzS) (hzmax g hgS)
      exact hinj hzS (Finset.mem_coe.mpr hgS) heq
    · rintro rfl
      exact ⟨Finset.mem_coe.mpr hgS, fun y hy => hgmax' y (Finset.mem_coe.mp hy)⟩
  exact ⟨g, n, hprim, hface⟩

/-- **The unconditional vertex-existence step.** No edge hypothesis, no zonotope, no `ℓ_m`: any
nonempty finite lattice set has a vertex, via a "generic" primitive normal `(1, N)` for `N`
strictly larger than the spread of `x`-coordinates in `S`.  Now just `exists_isVtx_of_injOn` fed
an explicit `InjOn` witness. -/
theorem exists_isVtx_of_finite {S : Finset (ℤ × ℤ)} (hne : S.Nonempty) :
    ∃ g, IsVtx (↑S : Set (ℤ × ℤ)) g := by
  classical
  set N : ℤ := 1 + S.sup' hne (fun z => z.1) - S.inf' hne (fun z => z.1) with hNdef
  have hspread : S.inf' hne (fun z => z.1) ≤ S.sup' hne (fun z => z.1) := by
    obtain ⟨z, hz⟩ := hne
    exact (Finset.inf'_le _ hz).trans (Finset.le_sup' _ hz)
  have hNpos : 0 < N := by omega
  have hbound : ∀ z ∈ S, ∀ z' ∈ S, z.1 - z'.1 < N := by
    intro z hz z' hz'
    have h1 : z.1 ≤ S.sup' hne (fun w => w.1) := Finset.le_sup' _ hz
    have h2 : S.inf' hne (fun w => w.1) ≤ z'.1 := Finset.inf'_le _ hz'
    omega
  set n : ℤ × ℤ := (1, N) with hndef
  have hprim : Prim n := by
    show Int.gcd n.1 n.2 = 1
    simp [hndef]
  have hinj : Set.InjOn (dot n) (↑S : Set (ℤ × ℤ)) := by
    intro z hz z' hz' heq
    simp only [Finset.mem_coe] at hz hz'
    have heq' : z.1 + N * z.2 = z'.1 + N * z'.2 := by
      have hzn : dot n z = z.1 + N * z.2 := by simp [dot, hndef]
      have hzn' : dot n z' = z'.1 + N * z'.2 := by simp [dot, hndef]
      rw [hzn, hzn'] at heq
      exact heq
    have hb1 : z.1 - z'.1 < N := hbound z hz z' hz'
    have hb2 : z'.1 - z.1 < N := hbound z' hz' z hz
    have hk : z.1 - z'.1 = N * (z'.2 - z.2) := by
      have hexpand : N * (z'.2 - z.2) = N * z'.2 - N * z.2 := by ring
      rw [hexpand]; linarith [heq']
    have hk0 : z'.2 - z.2 = 0 := by
      by_contra hcon
      rcases lt_or_gt_of_ne hcon with hlt | hgt
      · have hle : z'.2 - z.2 ≤ -1 := by omega
        nlinarith [mul_le_mul_of_nonneg_left hle hNpos.le]
      · have hge : 1 ≤ z'.2 - z.2 := by omega
        nlinarith [mul_le_mul_of_nonneg_left hge hNpos.le]
    have hz1 : z.1 = z'.1 := by rw [hk0, mul_zero] at hk; omega
    have hz2 : z.2 = z'.2 := by omega
    exact Prod.ext hz1 hz2
  exact exists_isVtx_of_injOn hne hprim hinj

open Nivat.LE2 in
/-- `hgen`, closed unconditionally: `IsGeneratingSet` alone (no edge/zonotope data) already
produces a generating site. -/
theorem exists_generatesAt_of_isGeneratingSet {A : Type*} {ξ : Config A} {S : Finset (ℤ × ℤ)}
    (hSgen : IsGeneratingSet ξ S) : ∃ a, GeneratesAt ξ S a := by
  obtain ⟨hne, hconv, hgen⟩ := hSgen
  obtain ⟨g, hvtx⟩ := exists_isVtx_of_finite hne
  have hcv : IsColleVertex S g := isColleVertex_of_isVtx hconv hvtx
  exact ⟨g, hgen g hcv.1 hcv.2⟩

open Nivat.Colle41 Nivat.ColleReg in
/-- The full pipeline, unconditional: no `hno`/`hprim` binders at all. -/
theorem hbase_of_sweep_of_generatingSet {ξ : Config ℤ} {e : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hSgen : IsGeneratingSet ξ S)
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {c : ℤ} (_hc0 : c ≠ 0)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin_fn : ∀ a : ℤ × ℤ, a ∈ S →
      ∀ i j : ℕ, ∀ z ∈ S.erase a,
        z + (enum i j - a) ∈
          D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ 0) (c • vl) := by
  obtain ⟨a, ha⟩ := exists_generatesAt_of_isGeneratingSet hSgen
  exact Nivat.HbaseBridge.hbase_of_sweep_self ha hD enum (hwin_fn a ha.1) hK

/-! ## §7  `Set.InjOn (dot n) ↑S` for Aface's `n`, from the `expDual`-spread

Team-lead's 2026-09-19 17:3x closure of the open item flagged after §6: Aface's row-order normal
`n := c • expNormal u' vl + expNormal vl u'` (`HbaseBridge.lean:869-875`,
`exists_generic_normal`) is, up to the swap identity `expNormal vl u' = expDual u' vl` below, the
**lex functional** for the coordinate pair `(expNormal u' vl, expDual u' vl)` — exactly
`Nivat.L3Band.expFrame`'s frame (`L3Band.lean:3526-3549`, `decomp`/`ext_dots` kernel-clean).  The
argument is `exists_isVtx_of_finite`'s `(1, N)` proof (`§6` above) with `N ↦ c`,
`z.1 ↦ dot (expDual u' vl) z`, `z.2 ↦ dot (expNormal u' vl) z`, and the final `Prod.ext` replaced
by `LevelFrame.ext_dots`. -/

-- The swap identity `expNormal vl u' = expDual u' vl` is already on-chain as
-- `Nivat.L3Band.expNormal_swap_eq_expDual` (`L3Band.lean:3846`); no local copy needed.

open Nivat.ColleReg Nivat.L3Band in
/-- **The missing instantiation, closed.**  `Set.InjOn (dot n) ↑S` for Aface's `n`, for *any*
finite `S` (including the on-chain `d.Sphi`), provided `c` exceeds the `expDual`-spread of `S` —
a numeric side-condition on `c`, not a property of `S`'s internals. -/
theorem injOn_dot_of_c_gt_dualSpread {u' vl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {S : Finset (ℤ × ℤ)} {c : ℤ}
    (hc : ∀ z ∈ S, ∀ z' ∈ S, dot (expDual u' vl) z - dot (expDual u' vl) z' < c) :
    Set.InjOn (dot (c • expNormal u' vl + expNormal vl u')) (↑S : Set (ℤ × ℤ)) := by
  classical
  have hdotn : ∀ w : ℤ × ℤ,
      dot (c • expNormal u' vl + expNormal vl u') w
        = c * dot (expNormal u' vl) w + dot (expDual u' vl) w := by
    intro w
    rw [expNormal_swap_eq_expDual u' vl]
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  set fr := expFrame hunimod with hfr
  intro z hz z' hz' heq
  simp only [Finset.mem_coe] at hz hz'
  rw [hdotn z, hdotn z'] at heq
  have hcpos : 0 < c := by have := hc z hz z hz; simpa using this
  have hb1 : dot (expDual u' vl) z - dot (expDual u' vl) z' < c := hc z hz z' hz'
  have hb2 : dot (expDual u' vl) z' - dot (expDual u' vl) z < c := hc z' hz' z hz
  have hk : c * (dot (expNormal u' vl) z - dot (expNormal u' vl) z')
      = dot (expDual u' vl) z' - dot (expDual u' vl) z := by linarith
  have hk0 : dot (expNormal u' vl) z - dot (expNormal u' vl) z' = 0 := by
    by_contra hcon
    rcases lt_or_gt_of_ne hcon with hlt | hgt
    · have hle : dot (expNormal u' vl) z - dot (expNormal u' vl) z' ≤ -1 := by omega
      nlinarith [mul_le_mul_of_nonneg_left hle hcpos.le]
    · have hge : 1 ≤ dot (expNormal u' vl) z - dot (expNormal u' vl) z' := by omega
      nlinarith [mul_le_mul_of_nonneg_left hge hcpos.le]
  have hLeq : dot (expNormal u' vl) z = dot (expNormal u' vl) z' := by omega
  have hDeq : dot (expDual u' vl) z = dot (expDual u' vl) z' := by
    rw [hk0, mul_zero] at hk; omega
  have hLeq' : dot fr.n z = dot fr.n z' := by rw [expFrame_n]; exact hLeq
  have hDeq' : dot fr.d' z = dot fr.d' z' := by rw [expFrame_d']; exact hDeq
  exact fr.ext_dots hLeq' hDeq'

open Nivat.ColleReg Nivat.L3Band in
/-- The composite answering the flag directly: `exists_isVtx_of_injOn` fed Aface's `n`, once `c`
clears the `expDual`-spread of `S`. -/
theorem exists_isVtx_of_c_gt_dualSpread {u' vl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {S : Finset (ℤ × ℤ)} (hne : S.Nonempty) {c : ℤ}
    (hc : ∀ z ∈ S, ∀ z' ∈ S, dot (expDual u' vl) z - dot (expDual u' vl) z' < c)
    (hprim : Prim (c • expNormal u' vl + expNormal vl u')) :
    ∃ g, IsVtx (↑S : Set (ℤ × ℤ)) g :=
  exists_isVtx_of_injOn hne hprim (injOn_dot_of_c_gt_dualSpread hunimod hc)

/-! ## §8  A common minimiser of two functionals on a zonotope, from a generator-sign condition

L3band's reading (2026-09-19 18:3x) of where the corner-route `hα` really comes from: if two
linear functionals never disagree in sign on any generator of the zonotope, the *same* vertex
minimises both — each generator picks its endpoint (`0` or `h i`) independently, and agreement in
sign forces the per-generator choices to agree. -/

/-- Linearity of `dot` over a finite sum (not yet on chain elsewhere). -/
theorem dot_finset_sum {ι : Type*} (n : ℤ × ℤ) (s : Finset ι) (f : ι → ℤ × ℤ) :
    dot n (∑ i ∈ s, f i) = ∑ i ∈ s, dot n (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [dot_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, dot_add, ih, Finset.sum_insert ha]

/-- **Membership in `zonoF` via a per-generator choice function.**  `zonoF s h` is the
`Finset`-level pointwise sum `∑ i ∈ s, {0, h i}` (`NewtonZonotope.lean:134`); its members are
exactly the sums `∑ i, g i` of independent per-generator choices `g i ∈ {0, h i}`
(`coe_zonoF` + `Set.mem_fintype_sum`, the additive form of `Set.mem_fintype_prod`). -/
theorem mem_zonoF_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ι → ℤ × ℤ) (z : ℤ × ℤ) :
    z ∈ zonoF (Finset.univ : Finset ι) h ↔
      ∃ g : ι → ℤ × ℤ, (∀ i, g i = 0 ∨ g i = h i) ∧ z = ∑ i, g i := by
  rw [← Finset.mem_coe, coe_zonoF]
  rw [Set.mem_fintype_sum]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, fun i => by simpa [segOf] using hg i, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, fun i => by simpa [segOf] using hg i, rfl⟩

/-- **A common minimiser for two functionals whose sign never disagrees on a generator.**  Pick
the generator `h i` whenever it does not increase `dot n₁` (ties broken in favour of `dot n₂`);
sign agreement forces this to also be the `dot n₂`-minimising choice at every generator. -/
theorem exists_common_min_of_sign_agree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℤ × ℤ) (n₁ n₂ : ℤ × ℤ) (hsign : ∀ i, 0 ≤ dot n₁ (h i) * dot n₂ (h i)) :
    ∃ a ∈ zonoF (Finset.univ : Finset ι) h, ∀ b ∈ zonoF (Finset.univ : Finset ι) h,
      dot n₁ a ≤ dot n₁ b ∧ dot n₂ a ≤ dot n₂ b := by
  classical
  set g : ι → ℤ × ℤ := fun i =>
    if dot n₁ (h i) < 0 then h i
    else if dot n₁ (h i) = 0 then (if dot n₂ (h i) ≤ 0 then h i else 0)
    else 0 with hgdef
  have hgmem : ∀ i, g i = 0 ∨ g i = h i := by
    intro i; simp only [hgdef]; split_ifs <;> simp
  have hz1 : dot n₁ (0 : ℤ × ℤ) = 0 := dot_zero_right n₁
  have hz2 : dot n₂ (0 : ℤ × ℤ) = 0 := dot_zero_right n₂
  -- The two per-generator optimality bounds that `hsign` forces `g` to satisfy simultaneously.
  have hopt : ∀ i, (dot n₁ (g i) ≤ dot n₁ 0 ∧ dot n₁ (g i) ≤ dot n₁ (h i)) ∧
      (dot n₂ (g i) ≤ dot n₂ 0 ∧ dot n₂ (g i) ≤ dot n₂ (h i)) := by
    intro i
    have hs := hsign i
    rcases lt_trichotomy (dot n₁ (h i)) 0 with h1 | h1 | h1
    · -- `dot n₁ (h i) < 0`: `g i = h i`, and sign agreement forces `dot n₂ (h i) ≤ 0`.
      have hgi : g i = h i := by simp [hgdef, h1]
      have hn2 : dot n₂ (h i) ≤ 0 := by
        by_contra hc
        push Not at hc
        nlinarith [mul_neg_of_neg_of_pos h1 hc]
      rw [hgi, hz1, hz2]
      exact ⟨⟨h1.le, le_refl _⟩, ⟨hn2, le_refl _⟩⟩
    · -- `dot n₁ (h i) = 0`: tie broken on `dot n₂ (h i)`.
      by_cases h2 : dot n₂ (h i) ≤ 0
      · have hgi : g i = h i := by simp [hgdef, h1, h2]
        rw [hgi, hz1, hz2, h1]
        exact ⟨⟨le_refl _, le_refl _⟩, ⟨h2, le_refl _⟩⟩
      · have h2' : 0 < dot n₂ (h i) := not_le.mp h2
        have hgi : g i = 0 := by simp [hgdef, h1, not_le.mpr h2']
        rw [hgi, hz1, hz2, h1]
        exact ⟨⟨le_refl _, le_refl _⟩, ⟨le_refl _, h2'.le⟩⟩
    · -- `0 < dot n₁ (h i)`: `g i = 0`, and sign agreement forces `0 ≤ dot n₂ (h i)`.
      have hn2 : 0 ≤ dot n₂ (h i) := by
        by_contra hc
        push Not at hc
        nlinarith [mul_neg_of_pos_of_neg h1 hc]
      have hgi : g i = 0 := by simp [hgdef, not_lt.mpr h1.le, h1.ne']
      rw [hgi, hz1, hz2]
      exact ⟨⟨le_refl _, h1.le⟩, ⟨le_refl _, hn2⟩⟩
  have ha_mem : (∑ i, g i) ∈ zonoF (Finset.univ : Finset ι) h :=
    (mem_zonoF_iff h _).mpr ⟨g, hgmem, rfl⟩
  refine ⟨∑ i, g i, ha_mem, ?_⟩
  intro b hb
  obtain ⟨g', hg', rfl⟩ := (mem_zonoF_iff h b).mp hb
  constructor
  · rw [dot_finset_sum, dot_finset_sum]
    apply Finset.sum_le_sum
    intro i _
    rcases hg' i with h0 | h0 <;> rw [h0]
    · exact (hopt i).1.1
    · exact (hopt i).1.2
  · rw [dot_finset_sum, dot_finset_sum]
    apply Finset.sum_le_sum
    intro i _
    rcases hg' i with h0 | h0 <;> rw [h0]
    · exact (hopt i).2.1
    · exact (hopt i).2.2

/-- **Necessity, in one example** (L3band's counterexample shape): sign disagreement at a
generator (`(1,-1)`, where `dot (1,0) (1,-1) = 1 > 0` and `dot (0,1) (1,-1) = -1 < 0`) can
genuinely destroy the common minimiser.  The zonotope on generators `{(1,-1), (1,1)}` — the
four points `(0,0), (1,-1), (1,1), (2,0)` — has `dot (1,0)`-minimum only at `(0,0)` (value `0`)
and `dot (0,1)`-minimum only at `(1,-1)` (value `-1`); these are different points, so no single
vertex minimises both. -/
theorem not_exists_common_min_of_sign_disagree_example :
    ¬ ∃ a ∈ zonoF (Finset.univ : Finset (Fin 2)) ![((1 : ℤ), (-1 : ℤ)), (1, 1)],
        ∀ b ∈ zonoF (Finset.univ : Finset (Fin 2)) ![((1 : ℤ), (-1 : ℤ)), (1, 1)],
          dot (1, 0) a ≤ dot (1, 0) b ∧ dot (0, 1) a ≤ dot (0, 1) b := by
  rintro ⟨a, ha, hmin⟩
  obtain ⟨g, hg, rfl⟩ := (mem_zonoF_iff _ a).mp ha
  have hmem0 : (0 : ℤ × ℤ) ∈ zonoF (Finset.univ : Finset (Fin 2)) ![((1 : ℤ), (-1 : ℤ)), (1, 1)] :=
    (mem_zonoF_iff _ _).mpr ⟨fun _ => 0, fun _ => Or.inl rfl, by simp⟩
  have hmem1 : ((1 : ℤ), (-1 : ℤ)) ∈
      zonoF (Finset.univ : Finset (Fin 2)) ![((1 : ℤ), (-1 : ℤ)), (1, 1)] :=
    (mem_zonoF_iff _ _).mpr
      ⟨![((1 : ℤ), (-1 : ℤ)), 0], fun i => by fin_cases i <;> simp,
        by simp [Fin.sum_univ_two]⟩
  have h0 := (hmin 0 hmem0).1
  have h1 := (hmin ((1 : ℤ), (-1 : ℤ)) hmem1).2
  have hg0 := hg 0
  have hg1 := hg 1
  have hsum : ∑ i : Fin 2, g i = g 0 + g 1 := by rw [Fin.sum_univ_two]
  have hval1 : (![((1 : ℤ), (-1 : ℤ)), (1, 1)] : Fin 2 → ℤ × ℤ) 0 = ((1 : ℤ), (-1 : ℤ)) := rfl
  have hval2 : (![((1 : ℤ), (-1 : ℤ)), (1, 1)] : Fin 2 → ℤ × ℤ) 1 = ((1 : ℤ), (1 : ℤ)) := rfl
  rw [hsum] at h0 h1
  rw [dot_add] at h0 h1
  simp only [dot] at h0 h1
  rcases hg0 with hg0 | hg0 <;> rcases hg1 with hg1 | hg1 <;>
    simp [hg0, hg1, hval1, hval2] at h0 h1

end Nivat.VertexFromEdge
