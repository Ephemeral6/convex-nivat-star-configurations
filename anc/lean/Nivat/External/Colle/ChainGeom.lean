/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.NotPeriodicShell
import Nivat.External.Colle.Generating
import Nivat.External.Colle.Step_Nonempty

/-!
# The chain data of §3 with its region geometry, and Claim 3.7 with no loose hypotheses

`ChainShell.lean` added Collé's shell formula (`b3_colle2.txt:440`) to `ChainData`, and
derived from it the two obligations of `Nivat.Colle37.claim37` — but `ChainDataWithShell.gen`
still carried the geometry of the `ℓ_J`-edge as ten explicit hypotheses, and
`ColleReg.region_not_periodic_of_shell` still carried `hrec`, `hdot` and `hgen_layers`.

This file bundles those into structure fields, so Claim 3.7 becomes a theorem whose only
inputs are the chain data and the outputs of Lemma 3.5.  Following CLAUDE.md
「定义修法：加强，不替换」 nothing upstream is edited: `ChainData` and `ChainDataWithShell`
are untouched and every lemma taking them keeps working.

## What the new fields say

`vJ` is Collé's `v_{ℓ'} = v_{ℓ_J}` (`:593`), the direction of the semi-infinite `ℓ_J`-edge of
the `(ℓ_ι, ℓ_J)`-region `Â_∞`, and hence the direction of both the orbit and the sliding
window of Claim 3.7.  It is *not* `vl = v_{ℓ_ι}`; see `blueprint/NOTE.md`, entry
"Claim 3.7 的轨道方向 — 2026-09-17".

* `latticeConvex_S`, `a_mem`, `a'_mem`, `lex`, `lex'`, `edge`, `edge'`, `dot_nJ_vJ` — the
  `ℓ_J`-parallel face of the window `S_φ` is its `⟪n_J, ·⟫`-minimal face, `a` and `a'` are its
  two endpoints, and its lattice points are `a, a + v_J, …, a + r·v_J = a'`.  (`a` is the
  `v_J`-minimal endpoint, `a'` the `v_J`-maximal one; the `-n_J` in `lex`/`lex'` is because the
  face is minimal, not maximal — see `ShellGeom.lean`'s "Orientation of `n`".)
* `bottom` — for each thickness `ε`, the sites of `Â_∞^{(ε+1)}` that are *not* already in
  `Â_∞^{(ε)}` form the half-line `{z₀ + k·v_J : k ≥ L}`, and `Â_∞` absorbs the translations
  `b - a` along it.  This is the statement that `Â_∞^{(ε)}` is an
  `(ℓ_ι, ℓ_J)`-region, which `:442` asserts outright.  (Four conjuncts since 2026-09-19; the
  former `b - a'` conjunct is derivable and was deleted — see the field's docstring.)
* `rec_p`, `dot_nJ_p` — `p` (the period of `x_per` carried by `ChainData`'s ambient data) is a
  recession direction of `Â_∞` transverse to `ℓ_J`; these feed `ChainDataWithShell.reach`.
* `vJ_ne`, `rec_vJ` — the *other* semi-infinite edge of `Â_∞` (`b3_colle2.txt:506`).  Only
  `region_periods_and_rays_of_geom` uses these two.

## Main results

* `ChainDataGeom` — the bundle.
* `ChainDataGeom.genLayers` — `Nivat.Colle37.RegionLayers.gen` at every thickness, with no
  hypotheses at all.
* `ColleReg.region_not_periodic_of_geom` — Claim 3.7, taking only the chain data, the
  generating-set property of `S_φ`, and the shell mismatch that Lemma 3.5 hands over.
* `ColleReg.region_periods_and_rays_of_geom` — the two periods of `ϑ` on `Â_∞` and the two
  rays, from the two recession directions plus `DoublyPeriodic x_per`.  ⚠ **Not usable in
  the assembly**: its `hxper_dp` is false in the branch `exists_chainData` serves; see the
  warning on the theorem itself.
-/

namespace Nivat.Colle35

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle Nivat.Colle37 Nivat.Colle37Geom

variable {α : Type*}

/-- **`ChainDataWithShell` together with the geometry of the `ℓ_J`-edge.**

See the module docstring for what each group of fields transcribes.  `p` is the period of
`xper` along which `Â_∞` recedes; it is a parameter rather than a field because the ambient
proof (`RegionSteps.exists_chainData`) already produces it alongside `vl`. -/
structure ChainDataGeom (η xper : Config α) (vl p : ℤ × ℤ)
    (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) extends ChainDataWithShell η xper vl S gen where
  /-- Collé's `v_{ℓ'} = v_{ℓ_J}` (`b3_colle2.txt:593`). -/
  vJ : ℤ × ℤ
  /-- The `v_J`-minimal endpoint of the `ℓ_J`-parallel face of `S_φ`. -/
  a : ℤ × ℤ
  /-- The `v_J`-maximal endpoint of that face. -/
  a' : ℤ × ℤ
  /-- That face has `r + 1` lattice points, `a = a + 0·v_J, …, a + r·v_J = a'`. -/
  r : ℕ
  /-- `S_φ` is lattice convex (also part of `IsGeneratingSet`). -/
  latticeConvex_S : LatticeConvex S
  /-- `a ∈ S_φ`. -/
  a_mem : a ∈ S
  /-- `a' ∈ S_φ`. -/
  a'_mem : a' ∈ S
  /-- `a` is strictly extreme for `(-n_J, -v_J)`. -/
  lex : ∀ b ∈ S.erase a,
    dot (-nJ) b < dot (-nJ) a ∨ (dot (-nJ) b = dot (-nJ) a ∧ dot (-vJ) b < dot (-vJ) a)
  /-- `a'` is strictly extreme for `(-n_J, v_J)`. -/
  lex' : ∀ b ∈ S.erase a',
    dot (-nJ) b < dot (-nJ) a' ∨ (dot (-nJ) b = dot (-nJ) a' ∧ dot vJ b < dot vJ a')
  /-- Every other point of `S_φ` is either on the face (at `a + j·v_J`) or strictly above it. -/
  edge : ∀ b ∈ S.erase a,
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a + (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a)
  /-- The mirror of `edge` at the other endpoint. -/
  edge' : ∀ b ∈ S.erase a',
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a' - (j : ℤ) • vJ) ∨ 1 ≤ dot nJ (b - a')
  /-- `v_J` spans `ℓ_J`, so it is orthogonal to the normal `n_J`. -/
  dot_nJ_vJ : dot nJ vJ = 0
  /-- **`Â_∞^{(ε)}` is an `(ℓ_ι, ℓ_J)`-region (`b3_colle2.txt:442`)**, in the one form the
  sweep of `ShellGen.lean` consumes: layer `ε + 1` exceeds layer `ε` exactly along a
  `v_J`-half-line, which `Â_∞` absorbs together with the translates `b - a`.

  ⚠ 引文分工（2026-09-24 订正，集成者亲读原文）：`:440` 是 `Â_∞^{(ε)}` 的**定义式**
  （`{g + t v⃗_{ℓ_{J-1}} : … dist ≤ d_ε}`），断言「is an `(ℓ_ι, ℓ_J)`-region」在 **`:442`**。
  本字段陈述的是那条**断言**，故引 `:442`；模块头 `:11` 引 `:440` 指的是蜕壳公式本身，不动。

  ⚠ **Conjunct (iv) deleted 2026-09-19.**  Between (iii) and the last conjunct this field used
  to carry the mirror of (iii) at the other endpoint,
  `∀ b ∈ S, ∀ k ≥ L, z₀ + k • vJ + (b - a') ∈ reachSet (⋃ Ahat) vJ1`.  Two facts retired it:

  * It is not a transcription.  `:440-442` says `Â_∞^{(ε)}` is an `(ℓ_ι, ℓ_J)`-region and
    `:597` says `S_φ` generates across the new line; neither writes a translate of the line
    by `S_φ - a'`.  (iii)/(iv) were the repo's sufficient condition for `gen_of_line`, nothing
    more (`ShellGeom.lean`, "What is left after this file").
  * It is derivable where the consumer reads it and false where it is not.  The face fields
    give `a' = a + j • vJ`, `j ≤ r` (`Colle37Geom.run_of_face`), so (iv) at site `k` is (iii)
    at site `k - j`; `ray_up` (`ShellGen.lean:75`) only reads the `a'`-side at `k > L + r`, where
    `k - j ≥ L` — that is `gen_of_shell` as it now stands (`ShellGeom.lean`).  Unguarded, (iv)
    at the on-face `b = a` demanded the `r` predecessors of the half-line's start, which the
    last conjunct forbids, and the kernel squeezed `a = a'` out of every bundle
    (`Nivat.ShellMink.ChainDataGeom.a_eq_a'`, now stated against `RetiredBottom`).

  ⚠ **Superseded repair, kept per §14 (2026-09-19 06:17–07:xx):** the first response was to
  *guard* (iv) by `1 ≤ dot nJ (b - a')`, which does remove the on-face instance and admits
  `a ≠ a'` (`ShellMink.cgwA`, `r = 1`).  Withdrawn the same day: the guarded (iv) is still
  false, together with the last conjunct, on the closed quadrant with the unit-square window
  `S_φ((X-1)(Y-1))`, `a = (0,0)`, `a' = (1,0)` — at the off-face `b = (0,1)`, `k = L` it asks
  for `(-1, -ε)` — while (i), (ii), (iii), (v) hold there at every `ε`
  (`tmp/Abottom_noIV.lean`: `not_guardedIV_quad_sq1`, `bottomShape3_quad_sq1`; receipts in
  `tmp/`, not landed).  The guard was the wrong repair; deletion is the right one.

  Conjunct (iii) is left unguarded on purpose: at on-face `b = a + j • vJ` it is conjunct (ii)
  shifted by `j ≥ 0`, so it is not over-strength. -/
  bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
    dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
    (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet (⋃ i, toChainData.Ahat i) vJ1) ∧
    (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
      z₀ + k • vJ + (b - a) ∈ reachSet (⋃ i, toChainData.Ahat i) vJ1) ∧
    (∀ z ∈ toChainData.shellInf (ε + 1),
      z ∈ toChainData.shellInf ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ)
  /-- `p` is a recession direction of `Â_∞`. -/
  rec_p : ∀ g ∈ ⋃ i, toChainData.Ahat i, g + p ∈ ⋃ i, toChainData.Ahat i
  /-- `p` is transverse to `ℓ_J`. -/
  dot_nJ_p : dot nJ p ≠ 0
  /-- `v_J` spans a line, so it is nonzero. -/
  vJ_ne : vJ ≠ 0
  /-- **`v_J` is primitive**, which is part of Collé's *definition* of `v_ℓ` and not an extra
  assumption: `b3_colle2.txt:351`, running text — *"`v_ℓ ∈ ℓ ∩ ℤ²` denotes the non-zero vector
  parallel to `ℓ` **of minimum norm**"*.  Added 2026-09-18 after an audit found the bundle
  recorded only `vJ_ne`.

  Two reasons this is the right field rather than a derivable convenience:

  * The producer already has it.  `Nivat.Colle35.exists_r_edge` (`FaceData.lean:189-191`),
    which is what manufactures the `r` (`:75`) and `edge` (`:89-90`) fields, takes
    `hvJprim : Primitive vJ` as a hypothesis — so any construction routed through it holds
    primitivity in hand and was simply discarding it.
  * The consumer needs it.  `bottom` (`:99-107`) describes the layer increment as exactly
    `{z₀ + k • vJ : L ≤ k}`; that is the correct rendering of a semi-infinite lattice edge
    only when `v_J` is primitive — otherwise the edge's lattice points are a proper subset of
    the stated set.

  `vJ_ne` is kept (it is implied by this field via `Primitive.ne_zero`,
  `Defs/Config.lean:158`) so that no existing consumer changes: 「加强，不替换」. -/
  vJ_prim : Primitive vJ
  /-- `v_J` is the other recession direction of `Â_∞` — `b3_colle2.txt:506`: *"with two
  semi-infinite edges, one of which is parallel to `ℓ` and the other one is parallel to
  `ℓ_J`"*. -/
  rec_vJ : ∀ g ∈ ⋃ i, toChainData.Ahat i, g + vJ ∈ ⋃ i, toChainData.Ahat i
  /-- The support value of the line `ℓ_ι` on `Â_∞`. -/
  cL : ℤ
  /-- **`ℓ_ι` supports `Â_∞`** — the mirror of `ChainDataWithShell.ahat_halfPlane`
  (`ChainShell.lean:63`) at the *other* edge.

  Definition 3.1 (`b3_colle2.txt:386`) gives an `(ℓ, ℓ')`-region **two** semi-infinite edges
  with fixed directions, and `ChainDataWithShell`'s own docstring (`ChainShell.lean:46-49`)
  argues that the support data is free for "a producer that already built the region" — but
  only the `ℓ_J` half was written down.  This field and `ahat_attained_L` are the `ℓ_ι` half,
  free by the identical argument.  The normal is `n_ℓ := det p v_J • (-p.2, p.1)`, the one
  orthogonal to the recession direction `p ∥ v_ℓ` and positive on `v_J`; it is written out
  rather than named so as to match `Claim414.claim414_ell` (`Claim414Ell.lean:296-298`)
  syntactically.

  Added 2026-09-18, while `exists_chainData` (`RegionSteps.lean:735`) — the only producer of
  this bundle — is still `sorry`, so the field costs nothing to add and a re-proof later. -/
  ahat_halfPlane_L : ∀ g ∈ ⋃ i, toChainData.Ahat i,
    cL ≤ dot (det p vJ • (-p.2, p.1)) g
  /-- The `ℓ_ι`-support line is attained: `Â_∞` touches it.  This is what
  `Claim414.claim414_ell` actually consumes (`hatt`); `ahat_halfPlane_L` is what makes `cL`
  the *support* value rather than an arbitrary level. -/
  ahat_attained_L : ∃ g ∈ ⋃ i, toChainData.Ahat i,
    dot (det p vJ • (-p.2, p.1)) g = cL
  /-- `n_J` is primitive.  Needed to read `ℓ_J` as a line: `Claim414.claim414_ellprime`
  (`Claim414EllPrime.lean:160`) takes its `ℓ'` as a `Primitive` normal.  A line's normal is
  primitive by construction in `b3_colle2.txt:253`; the bundle just never recorded it. -/
  nJ_prim : Primitive nJ
  /-- **`x_per|ℋ(ℓ_ι)` is not fully periodic** — Collé's Case 2 standing assumption
  (`b3_colle2.txt:890`), *at the level `cL` that this bundle itself fixes*.

  Why this is a field of the chain data rather than a hypothesis handed in from outside.  The
  half plane is not free: `Claim414.claim414` (`Claim414.lean:76-82`) takes its level `c` with
  `hatt`, so `c` is the **attained** `ℓ_ι`-support value of `Â_∞`, i.e. exactly `cL`; and
  `claim414_ell`'s `hexh` (`Claim414Ell.lean:122`) cannot be satisfied below it, because
  `dot n_ℓ p = 0` makes the recession direction `p` tangent to `ℓ_ι`, so no point strictly
  below `Â_∞` ever reaches `Â_∞`.  The assumption therefore mentions `cL`, which only exists
  once the chain does.

  That is also what the paper says: `b3_colle2.txt:922` — *"the support line of `Â^(ε)_∞`
  determined by `ℓ` **coincides with `ℓ^(−)`**"* — is an assertion about the chain that was
  built, not a consequence of `ℓ ∈ nexpd(η)`.  So discharging this field is an obligation on
  the **producer** (`ColleReg.exists_chainData`, `RegionSteps.lean:751`): it must place `Â_∞`
  so that its `ℓ_ι`-support line is the line carrying the disagreement of the ambiguous pair.
  The implication that then closes it is `Colle35.not_doublyPeriodicOn_both`
  (`HalfPlaneDoublyPeriodic.lean`), which is proved and kernel-clean; the pair it needs is the
  `hpartner` hypothesis of `exists_chainData`, exported by `ColleReg.exists_preamble`
  (`RegionSteps.lean:496`) on 2026-09-18.  What is *not* supplied and remains on the
  construction is the placement.  See `blueprint/NOTE.md`,
  「`:890` 的 WLOG — 半平面口径 — 2026-09-18」.

  Added 2026-09-18, while `exists_chainData` is still `sorry`, so the field costs nothing now
  and a strictly harder re-proof later.  It supersedes the note in `Claim414Wire.lean` that
  said a bundle field would be the wrong place; that note was written before the level `cL`
  was known to be forced. -/
  nfp_L : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
    PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h ∧
    PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h'

/-- **`Nivat.Colle37.RegionLayers.gen`, with no remaining hypotheses.**

Every input of `ChainDataWithShell.gen` is now a field, so this is a plain projection of the
bundle at each thickness `ε`. -/
theorem ChainDataGeom.genLayers {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen) (ε : ℕ) :
    ∃ i M : ℕ, ∀ t : ℕ, M ≤ t → ∀ z ∈ cg.toChainData.shellInf (ε + 1),
      GenClosure S (cg.toChainData.shellInf ε ∪
        (cg.toChainData.shellInf (ε + 1) ∩ winS i ((t : ℤ) • cg.vJ))) z := by
  obtain ⟨z₀, L, hdz, hline, hstab, hsplit⟩ := cg.bottom ε
  exact cg.toChainDataWithShell.gen (vJ := cg.vJ) (a := cg.a) (a' := cg.a') (z₀ := z₀)
    (r := cg.r) (L := L) ε cg.latticeConvex_S cg.a_mem cg.a'_mem cg.lex cg.lex'
    cg.edge cg.edge' cg.dot_nJ_vJ hdz hline (fun b hb _ k hk => hstab b hb k hk) hsplit

end Nivat.Colle35

namespace Nivat.ColleReg

open Nivat Nivat.Colle Nivat.Colle35 Nivat.Colle37 Nivat.LE2

/-- **Claim 3.7 over a `ChainDataGeom`** (`b3_colle2.txt:593`): the forward orbit of `ϑ` along
`v_{ℓ'}` has no fully periodic accumulation point.

Compared with `region_not_periodic_of_shell` this takes no geometry hypotheses: `hrec`,
`hdot` and `hgen_layers` are all supplied by the bundle.  What is left is exactly the data
that `Nivat.Colle35.lemma35` hands over (`ϑ`, `K`, `ε`, `hshell`, `hshell_not`) plus
`IsGeneratingSet ξ S_φ`.

The conclusion is Collé's, not the strictly stronger `¬ IsPeriodic ϑ`, which is refuted in
the tree (`Step_NotPeriodic.lean:430`); see `blueprint/FROZEN.md:93-96`. -/
theorem region_not_periodic_of_geom {ξ xper ϑ : Config ℤ} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (cg : ChainDataGeom ξ xper vl p S gen) {K ε : ℕ}
    (hp_ne : p ≠ 0) (hp_per : p ∈ Per xper)
    (hxper_mem : xper ∈ orbitClosure ξ) (hϑ_mem : ϑ ∈ orbitClosure ξ)
    (hshell : ∀ z ∈ cg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z)
    (hshell_not : ¬ (∀ z ∈ cg.toChainData.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z))
    (hS : IsGeneratingSet ξ S) :
    ¬ ∃ y : Config ℤ, Colle45.IsFullyPeriodic y ∧
      ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧
        ∀ z ∈ W, y z = T ((t : ℤ) • cg.vJ) ϑ z :=
  region_not_periodic_of_shell cg.toChainDataWithShell hp_ne hp_per hxper_mem hϑ_mem
    cg.rec_p cg.dot_nJ_p hshell hshell_not (cg.genLayers ε) hS

/-! ### Two independent periods with rays inside `Â_∞`

Collé `b3_colle2.txt:506`: `Â_∞` "is a weakly `E(S_φ)`-enveloped set … **with two
semi-infinite edges, one of which is parallel to `ℓ` and the other one is parallel to
`ℓ_J`**".  Those two edges are the two rays, and their directions `p` (‖ `ℓ`) and `v_J`
(‖ `ℓ_J`) are transverse because `⟪n_J, v_J⟫ = 0 ≠ ⟪n_J, p⟫`.

The periods come from `x_per`, which `b3_colle2.txt:600` says is fully periodic: `p` is a
period outright, and a suitable multiple of `v_J` is one because a doubly periodic
configuration has `N • ℤ²` inside its period group. -/

/-- A recession direction generates a forward ray from any point of the set. -/
theorem ray_of_recession {R : Set (ℤ × ℤ)} {d : ℤ × ℤ}
    (hd : ∀ g ∈ R, g + d ∈ R) {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ R) (k : ℕ) :
    z₀ + (k : ℤ) • d ∈ R := by
  induction k with
  | zero => simpa using hz₀
  | succ n ih =>
    have h := hd _ ih
    have he : z₀ + (n : ℤ) • d + d = z₀ + ((n + 1 : ℕ) : ℤ) • d := by
      push_cast [add_smul, one_smul]
      abel
    rwa [he] at h

theorem det_smul_right (u v : ℤ × ℤ) (c : ℤ) : det u (c • v) = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Transversality from a normal: if `v ≠ 0` lies on the line `⟪n, ·⟫ = 0` and `u` does not,
then `u` and `v` are independent. -/
theorem det_ne_zero_of_dot {n u v : ℤ × ℤ} (hv : v ≠ 0)
    (hnv : dot n v = 0) (hnu : dot n u ≠ 0) : det u v ≠ 0 := by
  intro hdet
  apply hnu
  simp only [det] at hdet
  simp only [dot] at hnv ⊢
  have h1 : v.1 * (n.1 * u.1 + n.2 * u.2) = u.1 * (n.1 * v.1 + n.2 * v.2) := by
    linear_combination (-n.2) * hdet
  have h2 : v.2 * (n.1 * u.1 + n.2 * u.2) = u.2 * (n.1 * v.1 + n.2 * v.2) := by
    linear_combination n.1 * hdet
  rw [hnv, mul_zero] at h1 h2
  by_cases hv1 : v.1 = 0
  · have hv2 : v.2 ≠ 0 := fun h => hv (by ext <;> simp [hv1, h])
    exact (mul_eq_zero.mp h2).resolve_left hv2
  · exact (mul_eq_zero.mp h1).resolve_left hv1

/-- **`region_periods_and_rays` over a `ChainDataGeom`.**

⚠ **Retired from the assembly, 2026-09-17 — `hxper_dp` is not available, and in Collé's
Case 2 it is false.**  The theorem itself is true as stated (it is a conditional), and is
kept as the record of what full periodicity of `x_per` *would* buy.  But `b3_colle2.txt:539`,
the sentence that makes `x_per` fully periodic, sits under the §3.1 contradiction hypothesis
`b3_colle2.txt:537` (*"as `−ℓ ∉ nexpd(η)` or `ℓ ∉ nexpd(η)` for all lines"*), which
`ColleReg.exists_chainData`'s `hw₁ : w ∈ ONED ξ`, `hw₂ : -w ∈ ONED ξ` negate; and §4 Case 2
— the branch that invokes Lemma 3.5 — assumes `x_per|ℋ(ℓ^(−))` is *not* fully periodic
(`b3_colle2.txt:890`).  The live route is `Nivat.Colle41.lemma41_colle_region_shape` on a
subregion `𝒦 ⊂ Â_∞^{(ε)}` (`b3_colle2.txt:904`).  Third occurrence of this conjunct in the
tree; see `blueprint/NOTE.md` 「`DoublyPeriodic xper` 第三次入侵」.

The two periods are `p` and `n • v_J` with `n = |N| ≠ 0` from `DoublyPeriodic.exists_smul_mem`
applied to `x_per`; both rays start at the single base point handed over by
`Nivat.ColleStep.region_nonempty`, since `rec_p` and `rec_vJ` make `Â_∞` recede in both
directions.  That `ϑ` has these periods on `Â_∞` is read off `hagree`: on `Â_∞` the
configuration `ϑ` *is* a translate of `x_per`, and a translate has the same period group
(`per_translate`). -/
theorem region_periods_and_rays_of_geom {ξ xper ϑ : Config ℤ} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (cg : ChainDataGeom ξ xper vl p S gen) {K : ℕ}
    (hB1 : (cg.toChainData.B 1).Nonempty)
    (hp_per : p ∈ Per xper)
    (hxper_dp : DoublyPeriodic xper)
    (hagree : ∀ z ∈ ⋃ i, cg.toChainData.Ahat i, ϑ z = T ((K : ℤ) • vl) xper z) :
    ∃ h h' z₀ z₀' : ℤ × ℤ, det h h' ≠ 0 ∧
      (∀ k : ℕ, z₀ + (k : ℤ) • h ∈ ⋃ i, cg.toChainData.Ahat i) ∧
      (∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ ⋃ i, cg.toChainData.Ahat i) ∧
      (∀ z ∈ ⋃ i, cg.toChainData.Ahat i, z + h ∈ ⋃ i, cg.toChainData.Ahat i →
        ϑ (z + h) = ϑ z) ∧
      (∀ z ∈ ⋃ i, cg.toChainData.Ahat i, z + h' ∈ ⋃ i, cg.toChainData.Ahat i →
        ϑ (z + h') = ϑ z) := by
  classical
  set R : Set (ℤ × ℤ) := ⋃ i, cg.toChainData.Ahat i with hR
  obtain ⟨w, hw⟩ : R.Nonempty :=
    Nivat.ColleStep.region_nonempty_of_nonempty_B1 cg.toChainData hB1
  -- the second period: a positive multiple of `v_J`
  obtain ⟨N, hN0, hN⟩ := hxper_dp.exists_smul_mem
  set n : ℕ := N.natAbs with hn
  have hn0 : n ≠ 0 := by simpa [hn, Int.natAbs_eq_zero] using hN0
  have hnv : ((n : ℤ)) • cg.vJ ∈ Per xper := by
    rcases Int.natAbs_eq N with h | h
    · rw [hn, ← h]; exact hN _
    · have : ((n : ℤ)) = -N := by rw [hn]; omega
      rw [this, neg_smul]
      exact AddSubgroup.neg_mem _ (hN cg.vJ)
  -- transversality: `v_J ⊥ n_J` while `p` is not
  have hdetpv : det p cg.vJ ≠ 0 :=
    det_ne_zero_of_dot cg.vJ_ne cg.dot_nJ_vJ cg.dot_nJ_p
  have hdet : det p ((n : ℤ) • cg.vJ) ≠ 0 := by
    rw [det_smul_right]
    exact mul_ne_zero (by exact_mod_cast hn0) hdetpv
  -- every period of `x_per` is a period of `ϑ` on `Â_∞`
  have hper : ∀ q ∈ Per xper, ∀ z ∈ R, z + q ∈ R → ϑ (z + q) = ϑ z := by
    intro q hq z hz hzq
    rw [hagree _ hzq, hagree _ hz]
    exact Per.apply (per_translate hq) z
  have hrayv : ∀ k : ℕ, w + (k : ℤ) • cg.vJ ∈ R := fun k =>
    ray_of_recession (fun g hg => cg.rec_vJ g hg) hw k
  refine ⟨p, (n : ℤ) • cg.vJ, w, w, hdet, ?_, ?_, ?_, ?_⟩
  · exact fun k => ray_of_recession (fun g hg => cg.rec_p g hg) hw k
  · intro k
    have he : (k : ℤ) • ((n : ℤ) • cg.vJ) = ((k * n : ℕ) : ℤ) • cg.vJ := by
      rw [smul_smul]; push_cast; ring_nf
    rw [he]
    exact hrayv (k * n)
  · exact hper p hp_per
  · exact hper _ hnv

end Nivat.ColleReg
