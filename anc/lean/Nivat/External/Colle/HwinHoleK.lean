/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1SweepBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `HwinHoleK` — the `∃ K` repackaging of `HwinHoleZ` (Task 7)

`Nivat.L1SweepBridge.HwinHoleZ` (`L1SweepBridge.lean:849`) quantifies `∀ (B) (u) (c) (a) (K)`.
§21 of that file (`not_hwinHoleZ_of_case1`) shows the hole is **false** at every Case 1 instance,
precisely because of this `∀ K`: `not_exists_enum_hwin_hK_of_shear` exhibits one bad shear `K`
against which no `hamin`-vertex admits an enumeration, and one bad `K` kills a `∀ K` promise.

But the consumer `wedgeResidualR_of_hwinHoleZ` (`:868`) never needed the hole to hold for every
`K`. It `obtain`s a single `⟨K, a₁, ha₁, hcorner⟩` from a corner producer
(`L1StraddleWedge.exists_corner_shear`) and passes *that* `K` in. The `∀ K` in `HwinHoleZ` is an
artifact of how the hole was written, not a demand of the consumer. This file repackages the hole
with `K` (and the corner data that depends on it) existentially bundled inside, and checks what
survives the move.

## What is bundled with `K`, and why

The corner data needed at a shear `K` is the vertex `a` and its `hamin`-defeat direction
`expNormal (u' - K • vl) vl` — that direction is a genuine function of `K`, so `a` cannot be
chosen once and reused across different `K`. Concretely, at two different shears `K₁ ≠ K₂` the
minimiser of `dot (expNormal (u' - K₁ • vl) vl) ·` over `Sw` need not equal the minimiser at `K₂`
(this is exactly what lets `exists_shear_argmin_not_detMax`/`_not_detMin`, cited in §19, move the
argmin around by choosing `K`). So `a` **moves in with `K`**, existentially bundled together, not
left universal. `hconvS : LatticeConvex (Sw.erase a)` moves with it for the same reason — it is a
property of the *chosen* vertex, not of `Sw` alone. `B`, `u`, `c` stay universal exactly as
instructed: they are supplied by the caller (`exists_hD_of_case1`) at the call site, not chosen by
the hole. -/

namespace Nivat.L1SweepBridge

open Nivat Nivat.LE2 Nivat.Colle Nivat.Colle41 Nivat.ColleReg

/-- The `∃ K` repackaging of `HwinHoleZ`. Same content, with the shear `K` and its matching
corner data (`a`, `hamin`, `hconvS`) existentially bundled inside the hole instead of universally
quantified outside. `B`, `u`, `c` remain universal, as in `HwinHoleZ`. -/
def HwinHoleK (ξ : Config ℤ) (Sw : Finset (ℤ × ℤ)) (vl : ℤ × ℤ) : Prop :=
  ∃ u' : ℤ × ℤ, (det u' vl = 1 ∨ det u' vl = -1) ∧
    ∃ (K : ℤ) (a : ℤ × ℤ), a ∈ Sw ∧ Nivat.LatticeConvex (Sw.erase a) ∧
      (∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) ∧
      ∀ (B : Set (ℤ × ℤ)) (u : ℤ × ℤ) (c : ℤ),
        0 < c → B.Finite → EnvOf (Sw : Set (ℤ × ℤ)) B →
        (∀ z ∈ halfStrip B vl, (T u ξ) z = T (c • vl) (T u ξ) z) →
        ∃ b₀ ∈ B, ∃ enum : ℕ → ℕ → ℤ × ℤ,
          (∀ i j : ℕ, ∀ z ∈ Sw.erase a,
            z + (enum i j - a) ∈
              halfStrip B vl ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
                ∪ (enum i '' {j' | j' < j})) ∧
          chainFull B vl (u' - K • vl) b₀ 0 ⊆ halfStrip B vl ∪ (⋃ i, Set.range (enum i))

/-! ## Soundness: `HwinHoleZ → HwinHoleK`

**Not a bare implication.** `HwinHoleZ ξ ∅ vl` is provable whenever `∃ u', det u' vl = ±1` holds
(e.g. whenever `vl` is primitive), because its inner `∀ a, a ∈ (∅ : Finset _) → …` is vacuous —
the hole asks nothing of an empty `Sw`. But `HwinHoleK ξ ∅ vl` demands `∃ a ∈ (∅ : Finset _), …`,
which is false outright. So `HwinHoleZ ξ ∅ vl` is true while `HwinHoleK ξ ∅ vl` is false at
`Sw = ∅` (given a primitive `vl`), and the bare implication `HwinHoleZ → HwinHoleK` **does not
hold in full generality**.

The fix costs nothing at the one real call site: `wedgeResidualR_of_hwinHoleZ` (`:868`) always has
`Sw := d.Sphi` together with `d.isGeneratingSet : IsGeneratingSet ξ d.Sphi`, and `IsGeneratingSet`
already carries `Sw.Nonempty` (its first field) plus the vertex-selection property needed to
supply `a`/`hamin`/`hconvS` at *any* nonzero direction
(`MaxIndexProbe.exists_vertex_of_generating_dir`, `MaxIndexProbe.lean:547`). So the soundness
lemma below takes `IsGeneratingSet ξ Sw` as an extra hypothesis — exactly what is already in hand
at the only place this will be used — rather than asserting the false unconditional statement. -/

/-- Sound direction, under the hypothesis that is actually available at the call site.
`K := 0` suffices: we do not need to move the shear at all, only to supply *some* vertex/`hamin`
witness for the `u'` that `HwinHoleZ` already produced, and `exists_vertex_of_generating_dir`
supplies one unconditionally (no `hnc`, no corner producer). This is the same instantiation move
as `hwinHoleU_of_hwinHoleZ` (`HwinHoleWeaken.lean:104`), one level deeper. -/
theorem hwinHoleK_of_hwinHoleZ {ξ : Config ℤ} {Sw : Finset (ℤ × ℤ)} {vl : ℤ × ℤ}
    (hgen : IsGeneratingSet ξ Sw) (h : HwinHoleZ ξ Sw vl) : HwinHoleK ξ Sw vl := by
  obtain ⟨u', hunimod, hhole⟩ := h
  have hw0 : expNormal u' vl ≠ 0 := by
    intro heq
    have hdot := Nivat.ColleReg.dot_expNormal_vl hunimod
    rw [heq] at hdot
    simp [Nivat.LE2.dot] at hdot
  obtain ⟨a, ha, hamin, hconvS, _hgenAt⟩ :=
    Nivat.ColleReg.exists_vertex_of_generating_dir hw0 hgen
  refine ⟨u', hunimod, 0, a, ha, hconvS, by simpa using hamin, ?_⟩
  intro B u c hc hBfin hEnv hD
  have h' := hhole B u c a 0 ha hconvS hc hBfin hEnv (by simpa using hamin) hD
  simpa using h'

/-! ## Does §20's refutation transfer to `HwinHoleK`? **No.**

**Search run.** `grep -n "not_exists_enum_hwin_hK\|not_hwinHoleZ_of_case1" L1SweepBridge.lean`
(the only two refutation-shaped theorems in that file whose conclusion could possibly bear on a
hole of this shape); read both in full (`:1484`–`:1567`, `:1598`–`:1624`) together with their
docstrings' own reading limits (`:1476`–`:1483`, `:1536`–`:1539`, `:1593`–`:1597`) before writing
this section. §21's own docstring already flags the answer (`:1593`–`:1597`, "a hole that bundles
`K` existentially … is a different proposition, and nothing here refutes it"); the paragraph below
is that claim actually checked against `HwinHoleK`'s stated definition, not taken on faith.

**The shape of what is proved vs. what would be needed.**

* `not_exists_enum_hwin_hK_of_shear` (§19, `:1484`) proves, from `hnc` alone (no minimal-
  counterexample hypothesis): `∃ K, ∀ a ∈ Sw, hamin(K, a) → ∀ b₀ enum, hwin → ¬ hKsub`. This is an
  **existential over `K`** — exactly the shape needed to falsify `HwinHoleZ`'s `∀ K` (one witness
  `K` where the inner statement fails refutes a universal claim), and exactly the *wrong* shape to
  falsify `HwinHoleK`'s `∃ K`: an existential "some `K` is bad" places no constraint on whether a
  *different* `K` is good.
* `not_hwinHoleZ_of_case1` (§21, `:1598`) instantiates `hhole` at the one bad `K` from
  `not_exists_enum_hwin_hK_of_shear` and the `a` that `exists_vertex_of_generating_dir` returns
  *at that specific sheared direction*, deriving `False` from `HwinHoleZ`'s `∀ K` clause applied
  to that one instance. `HwinHoleK` has no `∀ K` clause to instantiate this way — there is no step
  in this proof that survives dropping the outer `∀`.
* `not_exists_enum_hwin_hK_at_corner_shear` (§20, `:1547`) is narrower still: it is a statement
  about one *producer* (`exists_corner_shear`'s output), not about the hole. It says that
  producer's `(K, a)` pair is always wrong-signed. It says nothing about whether *some other*
  `(K, a)` pair — e.g. the one `HbaseBridge.exists_shear_hlt_and_doubly_lower` may supply, per the
  dispatch's own note that its `a` sits at the opposite `det·vl` extreme — could satisfy
  `HwinHoleK`'s existential.

**What refuting `HwinHoleK` would actually require:** a statement of the form `∀ K, ∀ a ∈ Sw,
hamin(K,a) ∧ hconvS(a) → ¬ (∀ B u c, … → ∃ b₀ enum, hwin ∧ hKsub)` — i.e. *every* shear fails, not
*some* shear. Nothing of that shape is proved anywhere in `L1SweepBridge.lean`; §19/§20/§21 only
ever exhibit one bad `K` (or examine one fixed producer's `K`), never quantify over all `K`
inside a refutation. Since the `hamin`-minimiser cycles through only finitely many vertices of the
finite set `Sw` as `K` ranges over `ℤ` (there are finitely many distinct directions
`expNormal (u' - K • vl) vl` up to the finitely-many-vertices pigeonhole), a genuine `∀ K`
refutation is not obviously even true, let alone proved here — it would have to rule out every
vertex of `Sw` simultaneously across all shears, not just the one `exists_corner_shear` happens to
land on.

**Verdict: the refutation does not transfer.** `HwinHoleK` survives §19/§20/§21 intact; nothing in
this file weakens that verdict into a proof (no such theorem is stated or attempted above), and no
`sorry` is used anywhere in this file. -/

/-! ## Replay attempt, actually run (not just argued)

The paragraph above is not merely an assessment from reading the shapes — I wrote out the literal
replay of `not_hwinHoleZ_of_case1`'s proof against `HwinHoleK` as a scratch theorem (same
hypotheses `d`/`hcase1`/`hvl_prim`/`hp_mem`/`hp_ne`/`hdet_vl`, goal `¬ HwinHoleK ξ d.Sphi vl`,
proof body copied step for step) and ran it through `check1.sh` with a `sorry` at the exact point
where the original argument needs to move to the next step, to see whether everything *up to* that
point elaborates. It does: `rintro`-destructuring `HwinHoleK`'s existential, obtaining
`B`/`u`/`c`/`hD` from `exists_hD_of_case1`, `hBfin`, `hnc`, and the adversarial shear
`⟨Kbad, hKbad⟩ := not_exists_enum_hwin_hK_of_shear …` all typecheck unchanged. The break is exactly
where predicted: `HwinHoleK`'s `hhole` clause takes no `a`/`K` arguments (they were fixed by the
outer `rintro`, at whatever `K` the hole's witness happened to choose), so the call
`hhole B u c hc hBfin hEnv hD` produces `b₀`/`enum`/`hwin`/`hKsub` **at that fixed `K`**, not at
`Kbad`. There is no hypothesis anywhere connecting `K` to `Kbad`, and nothing in `HwinHoleK`'s
statement lets one demand they coincide. The scratch attempt has no move left and needs the
`sorry` to close — the file delivered here does not contain it; the scratch theorem was deleted
after this check and is not part of the final state. -/

/-! ## Does `HwinHoleK` collapse to a neighbour already on the tree? **No — checked structurally,
not by a failed `Iff.rfl` alone.**

`HwinHoleZ` turned out to be `HwinHoleE ξ Sw Sw vl` at `Iff.rfl` (§23) because the two definitions
have the *same* binder order and differ only in a set parameter being specialised. Checked whether
the same thing happens to `HwinHoleK` against every neighbour, by reading each definition's binder
order directly (not guessing from the name):

* `HwinHoleZ` (`L1SweepBridge.lean:859`): `∃ u', hunimod ∧ ∀ B u c a K, … → ∃ b₀ enum, hwin ∧ hKsub`.
* `HwinHoleE` (`:629`): `∃ u', hunimod ∧ ∀ B u c a K, … → ∃ b₀ enum, hwin ∧ hKsub` (adds `hEnv`, an
  extra hypothesis inside the same `∀`, plus a second `Finset` parameter).
* `HwinHole` (`:487`): `∃ u', hunimod ∧ ∀ B u c a K, … → ∃ b₀, hwin[enum := coverEnum]` (enum fixed,
  not free).
* `HwinHoleU` (`HwinHoleWeaken.lean:87`): `∀ B u c a K, … → ∃ u', hunimod ∧ (hamin → hD → ∃ b₀ enum,
  hwin ∧ hKsub)` — `∃ u'` moved *inside* the `∀`, opposite of every other rung.
* `HwinHoleSplit` (`:193`): `∃ u', hunimod ∧ ∀ B u c a K, … → (∃ enum, hwin) ∧ (∃ b₀ enum, hKsub)` —
  same `∀ B u c a K` prefix as `HwinHoleZ`, only the two existentials inside are pulled apart.

Every one of these keeps `a` and `K` **universally quantified alongside `B`, `u`, `c`** — a fresh
`a`/`K` is allowed at each tuple. `HwinHoleK` (this file, `:44`) instead pulls `∃ K a` **outside**
the `∀ B u c` entirely: one `K`/`a` pair has to work for *every* `B`, `u`, `c` at once. This is not
a rearrangement of the same binders (which is what made `HwinHoleZ ↔ HwinHoleE ξ Sw Sw vl` an
`Iff.rfl`) — it is a different quantifier prefix (`∃K∃a∀BUC` vs. `∀BUCaK∃…` or `∀BUC∃…`), and
swapping `∃∀` for `∀∃` is a genuine logical strengthening, not a relabelling: `HwinHoleK ξ Sw vl`
implies the corresponding "`a`, `K` fixed inside the `∀`" reading of the other holes (weaken the
existential's scope), but not conversely, so **no neighbour is even propositionally equivalent to
`HwinHoleK`, let alone definitionally**. `Iff.rfl` cannot succeed against any of the four candidates
above without first changing the statement of `HwinHoleK` itself (`Iff.rfl` requires syntactic
identity up to defeq, and these differ in the *position* of `∃`, which no amount of unfolding
removes) — so this was not run as a doomed tactic call; the binder-order comparison above is the
decisive check, and it settles the question without needing the tactic to fail on request.

**Verdict: `HwinHoleK` does not collapse. It is a genuinely new rung**, distinguished from every
existing hole by which quantifier it weakens (the outer `K`/`a`, not the enumeration's freedom or
the covering hypothesis `hEnv`). -/

/-! ## §22 composed: at a sufficiently negative shear, the generating-set vertex is `hamin`,
`LatticeConvex (Sw.erase a)`, and `det · vl`-maximal, simultaneously

`MaxIndexProbe.exists_vertex_of_generating_dir` (`:547`) already supplies `hamin` and
`LatticeConvex (Sw.erase a)` at *any* nonzero direction, unconditionally. `§22`'s
`detMax_of_hamin_of_shear_le` (`L1SweepBridge.lean:1699`) takes that `hamin` witness as a raw
hypothesis (does not choose its own vertex, unlike `exists_shear_argmin_detMax`), so it composes
directly: instantiate the generating-set producer at the sheared direction
`expNormal (u' - K • vl) vl` for a `K` below the threshold `detMax_of_hamin_of_shear_le` names,
then feed its `hamin` straight in. -/
theorem exists_vertex_hamin_convex_detMax_of_shear_le
    {ξ : Config ℤ} {Sw : Finset (ℤ × ℤ)} {u' vl : ℤ × ℤ}
    (hdet : det u' vl = 1) (hgen : IsGeneratingSet ξ Sw)
    {K : ℤ} (hK : K ≤ -(2 * ((Sw.sup (fun z => (det u' z).natAbs) : ℕ) : ℤ) + 2)) :
    ∃ a ∈ Sw,
      (∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) ∧
      Nivat.LatticeConvex (Sw.erase a) ∧
      (∀ z ∈ Sw, det z vl ≤ det a vl) := by
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [det_shear_vl]; exact Or.inl hdet
  have hw0 : expNormal (u' - K • vl) vl ≠ 0 := by
    intro heq
    have hdot := Nivat.ColleReg.dot_expNormal_vl hunimod'
    rw [heq] at hdot
    simp [Nivat.LE2.dot] at hdot
  obtain ⟨a, ha, hamin, hconvS, _hgenAt⟩ :=
    Nivat.ColleReg.exists_vertex_of_generating_dir hw0 hgen
  exact ⟨a, ha, hamin, hconvS, detMax_of_hamin_of_shear_le hdet hK ha hamin⟩

/-- **The unimodular form of §22, matching `HwinHoleK`'s actual `hunimod` disjunction.**
`exists_vertex_hamin_convex_detMax_of_shear_le` only covers `det u' vl = 1`; on the chain
`hunimod` is always the full disjunction, so half the instances would block on it. The two
branches need shears of *opposite sign* (`detMax_of_hamin_of_shear_unimod`'s own docstring,
`L1SweepBridge.lean:1737`): at `det u' vl = 1`, `K` must be very negative; at `det u' vl = -1`,
`K` must be very positive. This version picks the sign by cases up front, so the caller never
has to. -/
theorem exists_vertex_hamin_convex_detMax_of_shear_unimod
    {ξ : Config ℤ} {Sw : Finset (ℤ × ℤ)} {u' vl : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hgen : IsGeneratingSet ξ Sw) :
    ∃ (K : ℤ) (a : ℤ × ℤ), a ∈ Sw ∧
      (∀ b ∈ Sw, dot (expNormal (u' - K • vl) vl) a ≤ dot (expNormal (u' - K • vl) vl) b) ∧
      Nivat.LatticeConvex (Sw.erase a) ∧
      (∀ z ∈ Sw, det z vl ≤ det a vl) := by
  classical
  set M : ℕ := Sw.sup (fun z => (det u' z).natAbs) with hM
  obtain ⟨K, hK⟩ : ∃ K : ℤ, det u' vl * K ≤ -(2 * (M : ℤ) + 2) := by
    rcases hunimod with h1 | h1
    · exact ⟨-(2 * (M : ℤ) + 2), by rw [h1]; linarith⟩
    · exact ⟨2 * (M : ℤ) + 2, by rw [h1]; linarith⟩
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rw [det_shear_vl]; exact hunimod
  have hw0 : expNormal (u' - K • vl) vl ≠ 0 := by
    intro heq
    have hdot := Nivat.ColleReg.dot_expNormal_vl hunimod'
    rw [heq] at hdot
    simp [Nivat.LE2.dot] at hdot
  obtain ⟨a, ha, hamin, hconvS, _hgenAt⟩ :=
    Nivat.ColleReg.exists_vertex_of_generating_dir hw0 hgen
  exact ⟨K, a, ha, hamin, hconvS, detMax_of_hamin_of_shear_unimod hunimod hK ha hamin⟩

/-! ## What remains between this and `HwinHoleK`

**Search run.** `grep -rn "hK_of_coverEnum\|hwin_fn\|theorem.*enum.*halfStrip\|theorem.*chainFull.*halfStrip"
Nivat/External/Colle/*.lean` for anything tree-wide whose *conclusion* matches `hwin`/`hKsub`'s
shape (not by guessing from a name containing "sweep" or "window"); it surfaced my own prior file
`HwinHoleWeaken.lean`, whose §2/§4 had already pinned down exactly this `hwin`-vs-`hKsub`
separation for `HwinHoleZ`'s inner existential — same shape, `HwinHoleK` just moves `K`/`a` out
one binder. Read that file's §2 and §4 in full (`:110`–`:224`) rather than trusting the summary in
its own docstring. Also checked `exists_shear_hlt_and_doubly_lower_detMax`
(`HbaseBridge.lean:2143`) directly by `#check`-reading its statement rather than assuming from the
name.

`exists_vertex_hamin_convex_detMax_of_shear_le` supplies `a`, `hamin`, `hconvS`, and the
`det · vl`-maximality fact — everything `HwinHoleK`'s existential core asks for **except** `b₀`,
`enum`, `hwin`, and `hKsub`, which are the payload of `HwinHoleK`'s inner `∀ B u c, … → ∃ b₀ enum,
…` clause.

**`b₀`/`hKsub` alone are free; the joint `enum` shared with `hwin` is the actual gap — already
pinned down as one theorem in my own prior file (`HwinHoleWeaken.lean` §2/§4), cited here rather
than rediscovered.**

* **`b₀ ∈ B` together with `hKsub`, dropping `hwin`**: fully produced, unconditionally.
  `Nivat.ColleReg.hK_of_coverEnum` (`L1CoverWedge.lean:432`) makes `coverEnum vl u' b₀` satisfy
  `hKsub` for *any* `hunimod`, `B`, `D` — `exists_hK_of_nonempty` (`HwinHoleWeaken.lean:219`)
  packages exactly this: `∃ b₀ ∈ B, ∃ enum, chainFull B vl u' b₀ 0 ⊆ D ∪ ⋃ i, range (enum i)` from
  `hb₀ : b₀ ∈ B` alone.
* **`enum` satisfying `hwin` (with *any* `b₀`/`hKsub`, let alone the *same* `enum` also
  satisfying `hKsub`)**: unproduced. Worse than merely unproduced — the one candidate that
  discharges `hKsub` for free, `coverEnum`, **provably fails** `hwin` the moment `Sw.erase a` has
  a point at a different level from `a` (`HbaseBridge.not_hwin_coverEnum_halfStrip`,
  `HbaseBridge.lean:471`: row `0` of `coverEnum` is a `u'`-ray, so it meets only one level line,
  while `hwin` demands it absorb a point at a different level). `coverEnum_hK_and_not_hwin`
  (`HwinHoleWeaken.lean:144`) packages both halves of this as one theorem. So the enum that makes
  `hKsub` trivial is a *proved counterexample* to `hwin` — satisfying one buys no discount on the
  other; `HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet`'s conjunction is strictly harder than
  either conjunct alone (`HwinHoleWeaken.lean:110`–`127`).
* **Splitting `enum` in two (one for `hwin`, a separate one for `hKsub`) does not evade
  this**: `HwinHoleWeaken.HwinHoleSplit` is the split form and `hwinHoleSplit_of_hwinHoleZ` shows
  `HwinHoleZ → HwinHoleSplit` (sound), but after the split the `hKsub`-half is free
  (`exists_hK_of_nonempty` again) and the entire remaining difficulty collapses to the bare
  question `∃ enum, hwin(enum)` — which is exactly the unproduced item above, restated, not
  discharged. Whether that bare question is even satisfiable is left open in
  `HwinHoleWeaken.lean` §4 point 3 (checked there via `grep -rn hK_of_ Nivat/External/Colle/*.lean`
  — only `coverEnum`-sourced `hK` producers exist tree-wide; no `hwin` producer of any kind, joint
  or split, is landed anywhere).

**`exists_shear_hlt_and_doubly_lower_detMax`, checked, not assumed.** Its `T` is **existentially
bound and returned by the theorem**, not a free parameter the caller supplies and not pinned to
`detMax_of_hamin_of_shear_le`'s "sufficiently negative" threshold — the proof constructs its own
`T` internally (via an injectivity argument on `(expNormal u' vl, expNormal vl u')` pairs, per the
body at `HbaseBridge.lean:2159` onward) and there is no visible connection between that `T` and the
`K` bound in `exists_vertex_hamin_convex_detMax_of_shear_le` above — they are outputs of two
independent constructions, not (yet) shown equal or interchangeable. Its conclusion already
contains `∀ z ∈ S.erase a, det z vl ≤ det a vl` **directly** (no `hamin` intermediate, no
`detMax_of_hamin_of_shear_le` needed) plus a doubly-lower witness `n`/`z` — but it supplies **none**
of `b₀`, `enum`, `hwin`, `hKsub` either. It is a second, independent route to the same `a`/`detMax`
conclusion `exists_vertex_hamin_convex_detMax_of_shear_le` reaches above, not a route past the
`b₀`/`enum`/`hwin`/`hKsub` gap those two routes share.

**Net: the extremality obstruction (§19–§21) is now defeated at a chosen shear, on two independent
routes. Neither route touches the enumeration/window content `HwinHoleK` still needs.** -/

section AxiomReceipts

#print axioms hwinHoleK_of_hwinHoleZ
#print axioms exists_vertex_hamin_convex_detMax_of_shear_le
#print axioms exists_vertex_hamin_convex_detMax_of_shear_unimod

end AxiomReceipts

end Nivat.L1SweepBridge
