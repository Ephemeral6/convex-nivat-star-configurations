/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainExhaustInter
import Nivat.External.Colle.LeafAShellNNext
import Nivat.Section8.HalfPlane
import Nivat.External.Colle.RegionCutGE

/-!
# `lane-cd-substrip`: the transverse refutation does **not** reach the real `w = -(dir ν_{J+1})`

Lane `lane-cd-substrip` (sub-lane of `lane-chaindata-lead`), written 2026-09-22, promoted to
the main tree 2026-09-23 (0 sorry, axioms clean).  `shellInter_finite_of_level` and
`shell_zero_eq_iUnion` are also the finiteness inputs `BottomRoom.window_of_shell` needs for
the shell `Â_i^{(ε)}`.

Targets: the `shellSubStrip` / `shellEnv` binders of
`Nivat.Colle35.ChainDataGeom.ofPartsExhaustsInter` (`ChainExhaustInter.lean`), consumed at
`tmp/wip/LeafAAssemble.lean`'s `shellSubStrip` / `shellEnv` binders.

## §0.  The recorded refutation, and why it does not apply

`tmp/wip/shell_J_gt_iota1_refute.lean` (`not_shellSubStrip_vl_10`, `not_shellSubStrip_vl_1neg1`)
refutes `shellSubStrip` on `ShellSweep`'s hexagon at

* `vJ1 = (0,-1)`, `nJ = (0,1)`, `cJ = 0`, `ε = 1`, `w = (-1,-1)`, and `vl = (1,0)` / `vl = (1,-1)`.

The general mechanism is `ShellMink.not_shellSubStrip_of_transverse_sweep`: `det vl ·` is bounded
on `Colle35.halfStrip (B i) vl` (finite base), and grows like `t · det vl w` along the sweep, so
an unbounded sweep parameter `t` always escapes the strip.

**The real bundle pins two signs that the hexagon instance violates.**  In `LeafAAssemble.lean`
the fan data is produced at `ℓ := -nℓ` (`hnE : -nℓ ∈ E ↑Sphi`), and the surviving branch has
`hdir_vl : dir (-nℓ) = vl`:

* `vJ1 = dir nprevJ` with `nprevJ = -nℓ ∨ nprevJ ∈ Arc (-nℓ) J`
  (`LeafAJSelect.exists_nprevJ_vJ1`).  Since `dot nℓ (dir m) = det m nℓ` and
  `det (-nℓ) m = det m nℓ`, **both** disjuncts give `0 ≤ dot nℓ vJ1` (`dot_nl_vJ1_nonneg`).
* `w = -(dir νJ1)` with `νJ1 = nℓ ∨ νJ1 ∈ Arc J nℓ` (`LeafAShellNNext.exists_w_hsweepW` at
  `ℓ := -nℓ`, so its `-ℓ` is `nℓ`).  The first disjunct gives `w = dir (-nℓ) = vl` exactly
  (the **parallel** case, §4); the second gives `dot nℓ w < 0` (`w_eq_vl_or_dot_nl_w_neg`).
* The tower lives in `{z | cz ≤ dot nℓ z}` (`Exhausts`, `LeafAAssemble.lean` `hAhatLevel`).

Together (`sweep_param_le`, §2) these bound the sweep parameter:
`t ≤ dot nℓ g - cz` for every shell point `g + t • w`.  The unbounded-`t` mechanism is gone, and
the shell is in fact **finite** (`shellInter_finite_of_level`, §3) — for the *transverse* `w`,
not only the parallel one.

The refuting instance has `vl = (1,0) ⟹ nℓ = dir vl = (0,1)` and `vJ1 = (0,-1)`, i.e.
`dot nℓ vJ1 = -1 < 0`: it violates `dot_nl_vJ1_nonneg`.  Same for `vl = (1,-1) ⟹ nℓ = (1,1)`,
`dot nℓ vJ1 = -1`.  (`vl = (1,0)` violates a second constraint as well: `nJ = (0,1) = nℓ` forces
`J = -nℓ = ℓ` and hence `det ℓ J = 0`, against `hℓJ : 0 < det (-nℓ) J`.)  §5 is the kernel
statement of all three violations.  **Verdict: the refutation does not apply.**

## §6.  Worked numeric instance (硬规矩 6)

Everything below was checked by hand before any Lean was written.

* `Sphi` := a hexagon with `E ↑Sphi = {(1,0), (-1,0), (0,1), (0,-1), (1,-1), (-1,1)}`.
* `nℓ := (0,1)`, `cz := 0` (the exhausted half plane is `{z | 0 ≤ z.2}`); `ℓ := -nℓ = (0,-1)`;
  `vl := dir (-nℓ) = dir (0,-1) = (1,0)`, so `dot nℓ vl = 0` and `vl` is primitive.
* ccw order of `E ↑Sphi` starting at `ℓ = (0,-1)`:  `det (0,-1) (1,-1) = 1 > 0`,
  `det (0,-1) (1,0) = 1 > 0`, `Arc (0,-1) (1,-1) = ∅`, `Arc (0,-1) (1,0) = {(1,-1)}`.
  So the order is `(0,-1) → (1,-1) → (1,0) → (0,1) = nℓ`.
* `J := (1,-1)` (the ccw-first unbounded normal after `ℓ`): `det ℓ J = 1 > 0`, `J ≠ ±nℓ`.
  `nJ := -J = (-1,1)`.
* `nprevJ`: `Arc ℓ J = ∅`, so `nprevJ = ℓ = (0,-1)` and `vJ1 = dir (0,-1) = (1,0)`.
  Checks: `dot nℓ vJ1 = 0 ≥ 0` (§1, degenerate disjunct); `dot nJ vJ1 = -1 < 0` (`hsweep`).
* `νJ1`: `Arc J nℓ = Arc (1,-1) (0,1) = {(1,0)}`, and `Arc (1,-1) (1,0) = ∅`, so `νJ1 = (1,0)`.
  Checks: `det J νJ1 = 1 > 0`; `det νJ1 nℓ = 1 > 0` — the **transverse** disjunct.
  `w := -(dir νJ1) = -(0,1) = (0,-1)`; `dot nJ w = -1 < 0` (`hsweepW`);
  `dot nℓ w = -1 < 0` (§1); `det vl w = det (1,0) (0,-1) = -1 ≠ 0`, i.e. `w` is transverse
  to `vl`, exactly the configuration `not_shellSubStrip_of_transverse_sweep` kills on a bare
  `MaxEnv.shell`.
* Tower slice: `kk 1 := 0`, `B 1 := Ahat 1 := {(0,0),(1,0),(2,0),(0,1),(1,1),(2,1)}`,
  `Ainf ⊆ {z | 0 ≤ z.2}`.
  Take `g := (1,1) ∈ Ahat 1`, so `dot nℓ g = 1` and §2 gives `t ≤ 1`.
  - `t = 1`: `z = (1,1) + (0,-1) = (1,0) ∈ B 1`, so `z + 0 • vl ∈ halfStrip (B 1) vl`. ✓
  - `t = 2`: `z = (1,-1)` has `dot nℓ z = -1 < 0 = cz`, and
    `reachSet Ainf vJ1 = Ainf + ℕ·(1,0) ⊆ {0 ≤ z.2}` because `dot nℓ vJ1 = 0`; so `z` is **not**
    in the ambient shell and never enters `shellInter`.  This is §2's bound, on the nose.
  `|det vl z| = |z.2| ∈ {0,1}` on the whole shell — bounded by the strip width of `B 1`,
  whereas `not_shellSubStrip_of_transverse_sweep` needs it to exceed every bound.

## §7.  What is still owed

`shellSubStrip` in the transverse case reduces (`shellSubStrip_of_bounded_check`, §6 below) to
the **finite** check "`g + t • w + kk i • vl ∈ halfStrip (B i) vl` for `g ∈ Ahat i` and
`1 ≤ t ≤ dot nℓ g - cz`".  Since `dot nℓ vl = 0`, that check forces `dot nℓ (g + t • w)` to be a
`dot nℓ`-level attained by `B i`, i.e. it needs the item-(ii) relation between the level ranges
of `B i` and `A i`.  That is the remaining input, and it is *not* available from
`hfin/hhp/AhatMono` alone.  `shellEnv` is untouched beyond finiteness (§3) and the free
inclusion `Ahat i ⊆ shellInter` (§3).
-/

set_option autoImplicit false

namespace Nivat.LaneCdSubstrip

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.PolyChainSum

variable {Sphi : Finset (ℤ × ℤ)}

/-! ## §1.  The two sign facts the fan construction pins -/

/-- `det (-n) m = det m n`, the sign bookkeeping used throughout. -/
theorem det_neg_left_comm (n m : ℤ × ℤ) : det (-n) m = det m n := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

/-- `dir (-n) = -dir n`. -/
theorem dir_neg (n : ℤ × ℤ) : dir (-n) = -dir n := by
  simp only [dir, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk, neg_neg]

/-- **`0 ≤ dot nℓ vJ1`.**  `vJ1 = dir nprevJ` and `nprevJ` is the fan predecessor of `J` taken
inside `Arc (-nℓ) J ∪ {-nℓ}` (`LeafAJSelect.exists_nprevJ_vJ1` with its `ℓ`-binder at `-nℓ`, the
instantiation used at `LeafAAssemble.lean:258-259`).  Degenerate disjunct: `det (-nℓ) nℓ = 0`.
Generic disjunct: `mem_Arc` gives `0 < det (-nℓ) nprevJ = det nprevJ nℓ = dot nℓ (dir nprevJ)`.

This is the constraint `shell_J_gt_iota1_refute.lean`'s instance violates (§5). -/
theorem dot_nl_vJ1_nonneg {nℓ J nprevJ : ℤ × ℤ}
    (hor : nprevJ = -nℓ ∨ nprevJ ∈ Arc (Sphi.finite_toSet) (-nℓ) J) :
    0 ≤ dot nℓ (dir nprevJ) := by
  rw [dot_dir_right]
  rcases hor with rfl | h
  · rw [det_neg_left_comm, det_self]
  · have hpos : 0 < det (-nℓ) nprevJ := (mem_Arc.mp h).2.1
    rw [det_neg_left_comm] at hpos
    exact hpos.le

/-- **The `w`-dichotomy.**  `w = -(dir νJ1)` and `νJ1` is the fan successor of `J` taken inside
`Arc J nℓ ∪ {nℓ}` (`LeafAShellNNext.exists_w_hsweepW` with its `ℓ`-binder at `-nℓ`, so its `-ℓ`
is `nℓ`; the instantiation used at `LeafAAssemble.lean:351-353`).  Either

* `νJ1 = nℓ`, and then `w = dir (-nℓ) = vl` **exactly** — the parallel case, settled in §4; or
* `νJ1 ∈ Arc J nℓ`, and then `dot nℓ w < 0` — the transverse case, bounded in §2. -/
theorem w_eq_vl_or_dot_nl_w_neg {nℓ J νJ1 : ℤ × ℤ}
    (hor : νJ1 = nℓ ∨ νJ1 ∈ Arc (Sphi.finite_toSet) J nℓ) :
    -(dir νJ1) = dir (-nℓ) ∨ dot nℓ (-(dir νJ1)) < 0 := by
  rcases hor with rfl | h
  · exact Or.inl (dir_neg _).symm
  · refine Or.inr ?_
    have hpos : 0 < det νJ1 nℓ := (mem_Arc.mp h).2.2
    rw [dot_neg_right, dot_dir_right]
    omega

/-! ## §2.  The sweep parameter is bounded — the refutation mechanism is blocked -/

/-- **The sweep parameter of a `:518` shell point is bounded by the `nℓ`-height of its base.**

`z = g + t • w` also lies in `MaxEnv.shell Ainf vJ1 nJ cJ ε`, so `z = h + s • vJ1` with
`h ∈ Ainf`.  Reading `dot nℓ` off both descriptions:
`cz ≤ dot nℓ h ≤ dot nℓ h + s * dot nℓ vJ1 = dot nℓ z = dot nℓ g + t * dot nℓ w ≤ dot nℓ g - t`.

Note both sign hypotheses are needed and both are supplied by §1; `ε` does not appear, so
enlarging `ε` (the move `not_shellSubStrip_of_transverse_sweep` makes) does not help.

**Known slack (lane-leafa-shellsubstrip, 2026-09-23, not fixed here per instruction):** the `h5`
step below discards `|dot nℓ w|` down to its sign-only bound (`dot nℓ w < 0` gives `t * dot nℓ w
≤ -t`), so the conclusion is only the *loose* bound `t ≤ dot nℓ g - cz`. The same algebra, kept
sharp, gives the *tight* bound `t ≤ (dot nℓ g - cz) / |dot nℓ w|` (equivalently
`t * |dot nℓ w| ≤ dot nℓ g - cz`), strictly stronger whenever `|dot nℓ w| > 1`.
`shellSubStrip_of_bounded_check`'s `hcheck` hypothesis is stated against this loose bound, so it
is asking for slightly more than the shell geometry actually forces — real slack, but harmless
for `item_ii_shellSubStrip`'s route below (the growth argument there does not need the tight
form). Switch to the tight bound only if a future proof of `hcheck` genuinely needs the extra
room; do not "fix" this lemma speculatively. -/
theorem sweep_param_le {Ainf : Set (ℤ × ℤ)} {nℓ vJ1 nJ w g : ℤ × ℤ} {cz cJ : ℤ} {ε t : ℕ}
    (hlev : ∀ z ∈ Ainf, cz ≤ dot nℓ z)
    (hvJ1 : 0 ≤ dot nℓ vJ1) (hw : dot nℓ w < 0)
    (hmem : g + (t : ℤ) • w ∈ MaxEnv.shell Ainf vJ1 nJ cJ ε) :
    (t : ℤ) ≤ dot nℓ g - cz := by
  obtain ⟨h, hh, s, heq, -⟩ := hmem
  have h1 : cz ≤ dot nℓ h := hlev h hh
  have h2 : dot nℓ (g + (t : ℤ) • w) = dot nℓ g + (t : ℤ) * dot nℓ w := by
    rw [dot_add, Nivat.PolyChainSum.dot_zsmul_right]
  have h3 : dot nℓ (h + (s : ℤ) • vJ1) = dot nℓ h + (s : ℤ) * dot nℓ vJ1 := by
    rw [dot_add, Nivat.PolyChainSum.dot_zsmul_right]
  have h4 : (0 : ℤ) ≤ (s : ℤ) * dot nℓ vJ1 := mul_nonneg (Int.natCast_nonneg s) hvJ1
  have h5 : (t : ℤ) * dot nℓ w ≤ -(t : ℤ) := by
    nlinarith [Int.natCast_nonneg t]
  rw [heq, h3] at h2
  linarith

/-- **The level bound behind §2, stated directly**: a sweep point of the `:518` shell never
drops below the `ℓ`-support level `cz`.

This is the honest content of the computation inside `sweep_param_le` — `g + t·w` equals some
`h + s·v⃗_{ℓ_{J+1}}` with `h ∈ Â_∞` (level `≥ cz` by `hlev`) and `s ≥ 0`, `⟪nℓ, v⃗_{ℓ_{J+1}}⟫ ≥ 0`
(`hvJ1`), so the level only goes **up** from `h`'s.  `hw` is not needed.

Why it is worth having separately from `sweep_param_le`: this is *verbatim* the third
hypothesis of `Colle35.ItemII` (`ItemII.lean:80`, `cz ≤ dot nℓ z`), which is the only route in
the build from "`z` is in a box" to "`z ∈ B i`".  A `shellSubStrip` proof going through `ItemII`
consumes this form, not the `t`-bound. -/
theorem sweep_level_ge {Ainf : Set (ℤ × ℤ)} {nℓ vJ1 nJ w g : ℤ × ℤ} {cz cJ : ℤ} {ε t : ℕ}
    (hlev : ∀ z ∈ Ainf, cz ≤ dot nℓ z)
    (hvJ1 : 0 ≤ dot nℓ vJ1)
    (hmem : g + (t : ℤ) • w ∈ MaxEnv.shell Ainf vJ1 nJ cJ ε) :
    cz ≤ dot nℓ (g + (t : ℤ) • w) := by
  obtain ⟨h, hh, s, heq, -⟩ := hmem
  have h1 : cz ≤ dot nℓ h := hlev h hh
  have h3 : dot nℓ (h + (s : ℤ) • vJ1) = dot nℓ h + (s : ℤ) * dot nℓ vJ1 := by
    rw [dot_add, Nivat.PolyChainSum.dot_zsmul_right]
  have h4 : (0 : ℤ) ≤ (s : ℤ) * dot nℓ vJ1 := mul_nonneg (Int.natCast_nonneg s) hvJ1
  rw [heq, h3]
  linarith

/-- **The tight sweep bound**, the one the geometry actually forces:
`t · |⟪nℓ, w⟫| ≤ ⟪nℓ, g⟫ - cz`.

`sweep_param_le` above states the loose `t ≤ ⟪nℓ, g⟫ - cz`, obtained by throwing away the factor
`|⟪nℓ, w⟫|` via `t * dot nℓ w ≤ -t` (its step `h5`).  That is strictly weaker whenever
`|⟪nℓ, w⟫| > 1`, and the `w` of `LeafAShellNNext.exists_w_hsweepW` is `-(dir νJ1)` for a `νJ1`
that is **not** pinned to `⟪nℓ, w⟫ = -1` — so the loose form leaves a real gap in any
`shellSubStrip` route that needs `t` itself bounded (see the reduction in §4 of the
`b3_colle2.txt:520` analysis).  Proof is the same computation with `h5` dropped.

`hw : dot nℓ w < 0` is *not* needed for the inequality itself (it is `sweep_level_ge`
rearranged); it is what makes the conclusion an actual upper bound on `t`. -/
theorem sweep_param_le_tight {Ainf : Set (ℤ × ℤ)} {nℓ vJ1 nJ w g : ℤ × ℤ} {cz cJ : ℤ} {ε t : ℕ}
    (hlev : ∀ z ∈ Ainf, cz ≤ dot nℓ z)
    (hvJ1 : 0 ≤ dot nℓ vJ1)
    (hmem : g + (t : ℤ) • w ∈ MaxEnv.shell Ainf vJ1 nJ cJ ε) :
    (t : ℤ) * (-dot nℓ w) ≤ dot nℓ g - cz := by
  have h := sweep_level_ge hlev hvJ1 hmem
  have h2 : dot nℓ (g + (t : ℤ) • w) = dot nℓ g + (t : ℤ) * dot nℓ w := by
    rw [dot_add, Nivat.PolyChainSum.dot_zsmul_right]
  rw [h2] at h
  linarith

/-- The tight bound implies the loose one, so `sweep_param_le` is redundant once
`sweep_param_le_tight` is available — kept only because existing call sites name it.
(`1 ≤ -dot nℓ w` from `hw`, and `t ≥ 0`.) -/
theorem sweep_param_le_of_tight {nℓ w g : ℤ × ℤ} {cz : ℤ} {t : ℕ}
    (hw : dot nℓ w < 0) (h : (t : ℤ) * (-dot nℓ w) ≤ dot nℓ g - cz) :
    (t : ℤ) ≤ dot nℓ g - cz := by
  have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  nlinarith

/-! ## §3.  Consequences: the `:518` shell is finite, and contains `Â_i` -/

/-- **The `:518` shell is finite**, for a *transverse* `w` as well as a parallel one — the
direct contradiction of the refutation's mechanism, which needs `det vl ·` unbounded on it.
Each point is `g + t • w` with `g` in the finite `Ahat` and `t ≤ dot nℓ g - cz` (§2). -/
theorem shellInter_finite_of_level {Ahat Ainf : Set (ℤ × ℤ)} {nℓ vJ1 nJ w : ℤ × ℤ}
    {cz cJ : ℤ} {ε : ℕ} (hfin : Ahat.Finite)
    (hlev : ∀ z ∈ Ainf, cz ≤ dot nℓ z) (hvJ1 : 0 ≤ dot nℓ vJ1) (hw : dot nℓ w < 0) :
    (ShellMink.shellInter Ahat (MaxEnv.shell Ainf vJ1 nJ cJ ε) w).Finite := by
  classical
  obtain ⟨M, hM⟩ := (hfin.image (fun g => dot nℓ g)).bddAbove
  set N : ℕ := (M - cz).toNat with hN
  refine Set.Finite.subset
    ((hfin.prod (Set.finite_Iic N)).image (fun p : (ℤ × ℤ) × ℕ => p.1 + (p.2 : ℤ) • w)) ?_
  rintro z ⟨⟨g, hg, t, rfl⟩, hshell⟩
  have hbound : (t : ℤ) ≤ dot nℓ g - cz := sweep_param_le hlev hvJ1 hw hshell
  have hgM : dot nℓ g ≤ M := hM ⟨g, hg, rfl⟩
  refine ⟨⟨g, t⟩, ⟨hg, ?_⟩, rfl⟩
  have : (t : ℤ) ≤ (N : ℤ) := by
    rw [hN]
    have : (0 : ℤ) ≤ ((M - cz).toNat : ℤ) := Int.natCast_nonneg _
    omega
  exact Set.mem_Iic.mpr (by exact_mod_cast this)

/-- `Â_i ⊆ Â_i^{(ε)}`, free (`t = 0` plus `subset_shell`), recorded here because `shellEnv`
consumers need it alongside §3's finiteness. -/
theorem subset_shellInter_of_halfPlane {Ahat Ainf : Set (ℤ × ℤ)} {vJ1 nJ w : ℤ × ℤ} {cJ : ℤ}
    {ε : ℕ} (hsub : Ahat ⊆ Ainf) (hhp : ∀ g ∈ Ahat, cJ ≤ dot nJ g) :
    Ahat ⊆ ShellMink.shellInter Ahat (MaxEnv.shell Ainf vJ1 nJ cJ ε) w := by
  intro g hg
  refine ⟨⟨g, hg, 0, by simp⟩, g, hsub hg, 0, by simp, ?_⟩
  have := hhp g hg
  have h0 : (0 : ℤ) ≤ (ε : ℤ) := Int.natCast_nonneg ε
  omega

/-! ## §4.  The parallel case: `shellSubStrip` is proved when `νJ1 = nℓ` -/

/-- **`shellSubStrip` for `w = vl`** — the `νJ1 = nℓ` disjunct of §1's dichotomy, which is
`w = -(dir nℓ) = dir (-nℓ) = vl` on the nose.  Only `subStrip` is used; the ambient shell is
irrelevant (any `Ainf` works), so this holds for every `i` and every `ε`. -/
theorem shellSubStrip_of_w_eq_vl {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl w : ℤ × ℤ}
    (hw : w = vl) (hsub : ∀ i, A i ⊆ Nivat.Colle35.halfStrip (B i) vl)
    (Ainf : Set (ℤ × ℤ)) (i : ℕ) :
    ShellMink.shellInter (Nivat.Colle35.hatOf A kk vl i) Ainf w ⊆
      {z | z + (kk i : ℤ) • vl ∈ Nivat.Colle35.halfStrip (B i) vl} := by
  rintro z ⟨⟨g, hg, t, rfl⟩, -⟩
  have hgA : g + (kk i : ℤ) • vl ∈ A i := hg
  obtain ⟨b, hb, s, hs⟩ := hsub i hgA
  refine ⟨b, hb, s + t, ?_⟩
  show g + (t : ℤ) • w + (kk i : ℤ) • vl = b + ((s + t : ℕ) : ℤ) • vl
  have key : g + (t : ℤ) • vl + (kk i : ℤ) • vl = (g + (kk i : ℤ) • vl) + (t : ℤ) • vl := by
    abel
  rw [hw, key, hs]
  push_cast
  rw [add_smul]
  abel

/-- The same, with `subStrip` taken from `:484` maximality — the shape
`ofPartsExhaustsInter`'s `maxA` binder supplies at `LeafAAssemble.lean:376`. -/
theorem shellSubStrip_of_w_eq_vl_of_max {α : Type*} {η xper : Config α}
    {Env : Set (ℤ × ℤ) → Prop} {A B : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} {kk : ℕ → ℕ}
    {vl w : ℤ × ℤ} (hw : w = vl)
    (maxA : ∀ i, Nivat.Colle35.IsMaxEnvIn Env (Nivat.Colle35.canonA η xper vl B u i) (A i))
    (Ainf : Set (ℤ × ℤ)) (i : ℕ) :
    ShellMink.shellInter (Nivat.Colle35.hatOf A kk vl i) Ainf w ⊆
      {z | z + (kk i : ℤ) • vl ∈ Nivat.Colle35.halfStrip (B i) vl} :=
  shellSubStrip_of_w_eq_vl hw (Nivat.Colle35.subStrip_of_max maxA) Ainf i

/-! ## §5.  The verdict: the recorded refutation violates the bundle's constraints -/

/-- `dir (-nℓ) = vl` determines `nℓ = dir vl`. -/
theorem nl_eq_dir_vl {nℓ vl : ℤ × ℤ} (h : dir (-nℓ) = vl) : nℓ = dir vl := by
  have h1 : nℓ.2 = vl.1 := by simpa [dir] using congrArg Prod.fst h
  have h2 : -nℓ.1 = vl.2 := by simpa [dir] using congrArg Prod.snd h
  refine Prod.ext ?_ ?_ <;> simp only [dir] <;> omega

/-- **`not_shellSubStrip_vl_10`'s configuration is unreachable, reason 1**: its `vl = (1,0)`
forces `nℓ = (0,1)`, but its ambient shell has `nJ = (0,1)`, i.e. `J = -nJ = -nℓ = ℓ`, so
`det ℓ J = 0` — against `hℓJ : 0 < det (-nℓ) J` (`LeafAAssemble.lean:237-239`). -/
theorem refute_vl10_violates_hlJ {nℓ J : ℤ × ℤ}
    (hvl : dir (-nℓ) = ((1 : ℤ), (0 : ℤ))) (hnJ : -J = ((0 : ℤ), (1 : ℤ))) :
    ¬ (0 < det (-nℓ) J) := by
  have hn : nℓ = ((0 : ℤ), (1 : ℤ)) := by rw [nl_eq_dir_vl hvl]; rfl
  have hJ : J = ((0 : ℤ), (-1 : ℤ)) := by
    have h1 : -(-J) = -((0 : ℤ), (1 : ℤ)) := congrArg Neg.neg hnJ
    rw [neg_neg] at h1
    rw [h1]; rfl
  rw [hn, hJ]
  simp only [det, Prod.fst_neg, Prod.snd_neg]
  norm_num

/-- **`not_shellSubStrip_vl_10`'s configuration is unreachable, reason 2**: with `vl = (1,0)`
we get `nℓ = (0,1)`, and the instance's sweep direction `vJ1 = (0,-1)` has
`dot nℓ vJ1 = -1 < 0`, against `dot_nl_vJ1_nonneg` (§1). -/
theorem refute_vl10_violates_vJ1 {nℓ : ℤ × ℤ} (hvl : dir (-nℓ) = ((1 : ℤ), (0 : ℤ))) :
    dot nℓ ((0 : ℤ), (-1 : ℤ)) < 0 := by
  have hn : nℓ = ((0 : ℤ), (1 : ℤ)) := by rw [nl_eq_dir_vl hvl]; rfl
  rw [hn]; simp only [dot]; norm_num

/-- **`not_shellSubStrip_vl_1neg1`'s configuration is unreachable**: `vl = (1,-1)` forces
`nℓ = dir (1,-1) = (1,1)`, and again `dot nℓ (0,-1) = -1 < 0` against §1. -/
theorem refute_vl1neg1_violates_vJ1 {nℓ : ℤ × ℤ} (hvl : dir (-nℓ) = ((1 : ℤ), (-1 : ℤ))) :
    dot nℓ ((0 : ℤ), (-1 : ℤ)) < 0 := by
  have hn : nℓ = ((1 : ℤ), (1 : ℤ)) := by rw [nl_eq_dir_vl hvl]; rfl
  rw [hn]; simp only [dot]; norm_num

/-- **Verdict, packaged.**  For *no* `Sphi`, `J`, `nprevJ` can the fan produce the recorded
refutation's `(vl, vJ1) = ((1,0), (0,-1))`; likewise for `((1,-1), (0,-1))`.  So
`shell_J_gt_iota1_refute.lean` does not refute `ofPartsExhaustsInter`'s `shellSubStrip`
binder at the `w` that `LeafAAssemble.lean` actually feeds it. -/
theorem refuting_config_not_reachable {nℓ J nprevJ : ℤ × ℤ}
    (hvl : dir (-nℓ) = ((1 : ℤ), (0 : ℤ)) ∨ dir (-nℓ) = ((1 : ℤ), (-1 : ℤ)))
    (hvJ1 : dir nprevJ = ((0 : ℤ), (-1 : ℤ))) :
    ¬ (nprevJ = -nℓ ∨ nprevJ ∈ Arc (Sphi.finite_toSet) (-nℓ) J) := by
  intro hor
  have hge : 0 ≤ dot nℓ (dir nprevJ) := dot_nl_vJ1_nonneg hor
  rw [hvJ1] at hge
  rcases hvl with h | h
  · exact absurd hge (not_le.mpr (refute_vl10_violates_vJ1 h))
  · exact absurd hge (not_le.mpr (refute_vl1neg1_violates_vJ1 h))

/-! ## §6.  The transverse case reduces to a finite check -/

/-- **`shellSubStrip` in the transverse case, reduced to finitely many points.**  The `t = 0`
layer is `subStrip`; every other layer has `1 ≤ t ≤ dot nℓ g - cz` by §2.  So the binder is no
longer an infinite obligation — but the surviving check is exactly the item-(ii) content:
`dot nℓ vl = 0`, so `g + t • w + kk i • vl ∈ halfStrip (B i) vl` forces
`dot nℓ g + t * dot nℓ w` to be a `dot nℓ`-level attained by `B i`. -/
theorem shellSubStrip_of_bounded_check {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    {Ainf : Set (ℤ × ℤ)} {vl w nℓ vJ1 nJ : ℤ × ℤ} {cz cJ : ℤ}
    (hlev : ∀ z ∈ Ainf, cz ≤ dot nℓ z) (hvJ1 : 0 ≤ dot nℓ vJ1) (hw : dot nℓ w < 0)
    (hsub : ∀ i, A i ⊆ Nivat.Colle35.halfStrip (B i) vl)
    (hcheck : ∀ i : ℕ, ∀ g ∈ Nivat.Colle35.hatOf A kk vl i, ∀ t : ℕ, 1 ≤ t →
      (t : ℤ) ≤ dot nℓ g - cz →
      g + (t : ℤ) • w + (kk i : ℤ) • vl ∈ Nivat.Colle35.halfStrip (B i) vl) :
    ∀ i ε : ℕ, ShellMink.shellInter (Nivat.Colle35.hatOf A kk vl i)
        (MaxEnv.shell Ainf vJ1 nJ cJ ε) w ⊆
      {z | z + (kk i : ℤ) • vl ∈ Nivat.Colle35.halfStrip (B i) vl} := by
  rintro i ε z ⟨⟨g, hg, t, rfl⟩, hshell⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have hgA : g + (kk i : ℤ) • vl ∈ A i := hg
    obtain ⟨b, hb, s, hs⟩ := hsub i hgA
    exact ⟨b, hb, s, by simpa using hs⟩
  · exact hcheck i g hg t ht (sweep_param_le hlev hvJ1 hw hshell)

/-! ## §8.  Round 2 (lane-chaindata-lead's three follow-ups, same session)

**Item 3 (quick check, done below, `w_eq_vl_of_vJ1_eq_nl`)**: `νJ1 = nℓ` (the `-ℓ`-disjunct of
`LeafAShellNNext.exists_w_hsweepW`'s `hνJ1or`, at `ℓ := -nℓ`, i.e. `νJ1 = -(-nℓ) = nℓ`) forces
`w = vl` **exactly**, via `dir_neg` alone.  So `shellSubStrip_of_w_eq_vl` already closes
`shellSubStrip` on that disjunct; only `νJ1 ∈ Arc J nℓ` (the true transverse case) is open.

**Item 2 (signature only, per instruction — not proved here).**  `shellSubStrip_of_bounded_check`
reduces `shellSubStrip`'s transverse case to `hcheck`.  Unwinding `hatOf` (`g' := g + kk i • vl`,
so `g' ∈ A i`) the needed statement is:

```
theorem item_ii_shellSubStrip {A B : ℕ → Set (ℤ × ℤ)} {vl w nℓ : ℤ × ℤ} {cz : ℤ}
    (hexh : Exhausts A nℓ cz)              -- already a binder of `ofPartsExhaustsInter`
    (hitemII : ItemII B nℓ cz)             -- available as `hσitemII` at the call site
    (hsubBA : ∀ i, B i ⊆ A i) (hsubAB : ∀ i, A i ⊆ B (i + 1))
    (i : ℕ) (g' : ℤ × ℤ) (hg' : g' ∈ A i) (t : ℕ) (ht1 : 1 ≤ t)
    (ht2 : (t : ℤ) ≤ dot nℓ g' - cz) :
    g' + (t : ℤ) • w ∈ Nivat.LE2.halfStrip (B i) vl
```
(instantiate `hcheck`'s `g := g' - kk i • vl` and re-add `kk i • vl` on both sides — a `1`-line
translation, not restated). `ItemII` (`ItemII.lean:80`) is the natural candidate source — it is
already threaded to the call site as `hσitemII` — but it only guarantees capture by `B i`
*for points whose box size is `≤ i − 1`*; nothing currently bounds `|g' + t • w|` by `i` (the
tower `A i` can grow faster than linearly in `i`), so `hitemII` alone does not close `hcheck`
without an extra growth-rate bound between `A i`'s diameter and `i`. That bound, or a direct
argument avoiding it, is the real remaining gap — not attempted this round.

**Item 1 (`shellEnv`): the premise "finiteness is the hard prerequisite" does not hold here,
and no proof is attempted.**  `Enveloped U T := WeaklyEnveloped U T ∧ (E T).encard = (E U).encard`
(`LatticeEdges.lean:624-629`) — `T` must realise **every** edge direction of `U` **and** match
each edge's lattice-point count exactly (not just "be convex with a subset of `U`'s edges" —
that weaker fact is `WeaklyEnveloped`, not `Enveloped`).  `shellInter_finite_of_level` gives
finiteness of the shell, which is necessary for `Enveloped` (`Enveloped.finite`,
`MaximalEnveloped.lean:157`) but nowhere near sufficient: a finite lattice-convex set can be
finite and still miss an edge direction of `Sphi` entirely, or have the right directions with
the wrong lengths, and `Enveloped` is **not monotone** under `⊆` (a strict superset can lose an
edge's `Enveloped`-length match even while gaining points), so a naive "sandwich between two
enveloped sets" argument does not typecheck against this definition without extra work — no
lemma of that shape exists in `LatticeEdges.lean` / `MaximalEnveloped.lean` / `AhatEnv.lean`
(grepped: none). Producing `shellEnv` in general looks like it needs an `AhatMono.lean`-grade
shape-convergence theorem for the `shellInter` object specifically (i.e. showing the shell's
final shape, for `i` large, literally saturates `E ↑Sphi`), which is a separately-scoped
undertaking, not a corollary of this round's finiteness result. Flagging this back rather than
forcing an incomplete proof.

**`w_eq_vl_of_vJ1_eq_nl`**: the item-3 kernel check. -/

theorem w_eq_vl_of_vJ1_eq_nl {nℓ vl νJ1 w : ℤ × ℤ}
    (hvl : dir (-nℓ) = vl) (hνJ1 : νJ1 = nℓ) (hw : w = -(dir νJ1)) : w = vl := by
  rw [hw, hνJ1, ← hvl, dir_neg]

/-! ## §9.  Round 3 (`shellEnv` against the existential form) — an anchor fact, and why the
geometric content is still owed

**What was tried.**  (a) `Nivat.Colle35.IsMaxEnvIn`/`hatOf`/`canonA`/`canonAhat`
(`ChainMax.lean:62,87`, `ChainCanon.lean:86,91`) were read in full: this machinery answers
*"is `A i` itself maximal envloped"*, a question about the *base* tower, and has **zero
consumers** on `RegionSteps.lean`'s chain (`ChainMax.lean`'s own docstring, "⚠ No consumers
yet"). It says nothing about `ShellMink.shellInter … w` and does not shortcut `shellEnv`.
(b) `AhatMono.lean`'s shape-recognition theorems (`eq_hatShape_of_E_eq_hexE`,
`hshape_of_E_eq_hexE`, …) are hardcoded to `E U = ShellSweep.hexE` (six fixed directions) and,
in their chain form, to `vl = (1,0)`; they do not generalise to the real abstract `Sphi`.
(c) The paper itself (`b3_colle2.txt:486-530`) proves `shellEnv`'s content in two stages that
are NOT in scope here: first `hat A_∞ := ⋃ hat A_i` is shown to be a weakly `E(Sφ)`-enveloped
`(ℓ,ℓ_J)`-region (`:498-508`, using `w_i(j)` face-tracking across the whole tower — this is
exactly the content the `σ`-reindexing / `AhatMono` machinery in `LeafAAssemble.lean` is built
to reconstruct, but *for the base tower*, not yet for a `shellInter`); **then** `:518-520`
asserts, essentially as an immediate consequence of that shape and without further argument
in the text, that the truncation `hat A_i^{(ε)} = {g - t·v_{ℓ_{J+1}} ∈ hat A_∞^{(ε)} : g ∈
hat A_i}` is itself `E(Sφ)`-enveloped for suitable `ε` and large `i`.  Reproducing that step in
Lean needs an `AhatMono.lean`-grade shape-convergence theorem for the *derived* shell shape —
i.e. "a two-direction-unbounded enveloped region, cut back along a third direction and
re-intersected with a swept collar, is again enveloped once the cut is past the corner" — which
does not exist anywhere in the tree (grepped `LatticeEdges.lean` / `MaximalEnveloped.lean` /
`AhatEnv.lean` / `AhatMono.lean`: no lemma of this shape).

**The one piece that *is* free**, recorded below: `MaxEnv.shell`'s own `ε = 0` layer collapses
to the swept-closed set exactly (`MaxEnv.shell_zero`, `MaximalEnveloped.lean:611`), so *if* one
already has `SweptClosed (⋃ Ahat) vJ1 nJ cJ` (`hswept`, a binder `ofPartsExhaustsInter` already
supplies) and the half-plane bound `hhp`, the ambient shell at `ε = 0` is *definitionally* the
bare union — no shape work needed there. This bounds how large the true content of `shellEnv`
can be (it is entirely in the `ε ≥ 1` collar, and only in how `shellInter (Ahat i) … w`
interacts with it), but does not discharge it: `ε` must be positive in the binder, and stepping
to `ε = 1` is exactly where the un-generalised paper step (`:518-520`) lives.

**Verdict, unchanged from Round 2, now with the two dead ends recorded**: `shellEnv` needs a
dedicated shape-convergence lemma that nothing in the current tree provides, even granting the
existential form. This is not a "prove it more cleverly" gap; it is a missing theorem the size
of `AhatMono.lean` itself, scoped at the derived `shellInter` shape rather than at `hatOf`
directly. Recommend it be its own lane. -/

/-- **The ambient shell's `ε = 0` layer is the bare tower union**, free from `SweptClosed` +
the half-plane bound (`MaxEnv.shell_zero`).  Recorded because it pins down exactly how little
of `shellEnv` is "for free": the entire remaining content is in the collar at `ε ≥ 1`. -/
theorem shell_zero_eq_iUnion {Ahat : ℕ → Set (ℤ × ℤ)} {vJ1 nJ : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ i, Ahat i ⊆ Nivat.CK224.halfPlaneGE nJ cJ)
    (hswept : Nivat.MaxEnv.SweptClosed (⋃ i, Ahat i) vJ1 nJ cJ) :
    Nivat.MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ 0 = ⋃ i, Ahat i := by
  have hsub : (⋃ i, Ahat i) ⊆ Nivat.CK224.halfPlaneGE nJ cJ := by
    rintro z ⟨-, ⟨i, rfl⟩, hz⟩
    exact hhp i hz
  exact Nivat.MaxEnv.shell_zero hsub hswept

/-! ## §10.  `eventually_mem_of_between_parallel_rays` (`bottom` lane's `hseedS` target)

Assigned by `lane-chaindata-lead` for the `bottom` lane's `hseedS` sub-obligation.  Pure 2D
lattice-convexity fact, no `hatOf` / `shell` / `Enveloped` needed.

**硬规矩 6 numeric check (worked by hand before the Lean proof).**  Take
`T := {z : ℤ × ℤ | 0 ≤ z.1 ∧ 0 ≤ z.2}` (first quadrant, a lattice-convex region: real hull
`C := {p : ℝ×ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}`), `vJ := (1,0)`, `nJ := (0,1)` (`dot nJ vJ = 0`),
`g := (0,0)` (level `dot nJ g = 0`), `q := (-5,3)` (level `dot nJ q = 3`), `y := (-9,2)`
(level `dot nJ y = 2`, between `0` and `3`).  `g`'s ray `{(k,0) : k ∈ ℕ} ⊆ T` for all `k`;
`q`'s ray `{(-5+k,3) : k ∈ ℕ} ⊆ T` needs `k ≥ 5`.  Direct check on the target claim:
`y + k • vJ = (-9+k, 2) ∈ T ⟺ -9+k ≥ 0 ⟺ k ≥ 9`.  So `L = 9` is a valid (indeed optimal:
`k=8` gives `(-1,2) ∉ T`) witness — the theorem below need only produce *some* `L`, not `9`
exactly.

Cross-check against the barycentric strip argument: `λ := (dot nJ q - dot nJ y)/(dot nJ q -
dot nJ g) = (3-2)/(3-0) = 1/3`, so `y` sits on the line through `g`,`q` shifted by `s • vJ`
where `(1/3)•(0,0) + (2/3)•(-5,3) = (-10/3, 2)` and `y - (-10/3,2) = (-17/3, 0) = (-17/3) • vJ`,
i.e. `s = -17/3`.  The real-hull argument below only needs `k` large enough that both
`s + k ≥ 0` (puts the convex combination past both rays' base points); `q`'s ray is the
bottleneck since it additionally needs its own index `≥ 0` as a *natural number* rounding,
giving a real threshold around `⌈17/3⌉ = 6`, comfortably below the true lattice answer `9`
(the gap between the strip-argument threshold and the sharp integer answer is expected: the
theorem below claims only *eventual* membership, matching its conclusion `∃ L, ∀ k ≥ L, …`). -/

/-- Two `ℝ`-vectors both orthogonal (w.r.t. the standard `ℝ × ℝ` pairing) to a common nonzero
`nJ`, with the first (`vJ`) itself nonzero, forces the second to be a real multiple of the
first.  Pure 2D linear algebra: `nJ`'s orthogonal complement in `ℝ²` is 1-dimensional. -/
theorem real_smul_of_dot_eq_zero {nJ vJ w : ℝ × ℝ}
    (hnvJ : nJ.1 * vJ.1 + nJ.2 * vJ.2 = 0) (hvJ : vJ ≠ 0) (hnJ : nJ ≠ 0)
    (hw : nJ.1 * w.1 + nJ.2 * w.2 = 0) : ∃ s : ℝ, w = s • vJ := by
  have hD1 : nJ.1 * (vJ.1 * w.2 - vJ.2 * w.1) = 0 := by linear_combination w.2 * hnvJ - vJ.2 * hw
  have hD2 : nJ.2 * (vJ.1 * w.2 - vJ.2 * w.1) = 0 := by
    linear_combination (-w.1) * hnvJ + vJ.1 * hw
  have hnJ' : nJ.1 ≠ 0 ∨ nJ.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hnJ (Prod.ext h.1 h.2)
  have hD : vJ.1 * w.2 - vJ.2 * w.1 = 0 := by
    rcases hnJ' with h | h
    · exact (mul_eq_zero.mp hD1).resolve_left h
    · exact (mul_eq_zero.mp hD2).resolve_left h
  have hvJ' : vJ.1 ≠ 0 ∨ vJ.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hvJ (Prod.ext h.1 h.2)
  rcases hvJ' with hv1 | hv2
  · refine ⟨w.1 / vJ.1, Prod.ext ?_ ?_⟩
    · show w.1 = w.1 / vJ.1 * vJ.1
      field_simp
    · show w.2 = w.1 / vJ.1 * vJ.2
      have heq : vJ.1 * w.2 = w.1 * vJ.2 := by linarith
      field_simp
      linarith
  · refine ⟨w.2 / vJ.2, Prod.ext ?_ ?_⟩
    · show w.1 = w.2 / vJ.2 * vJ.1
      have heq : vJ.2 * w.1 = w.2 * vJ.1 := by linarith
      field_simp
      linarith
    · show w.2 = w.2 / vJ.2 * vJ.2
      field_simp

/-- If `toReal (p + k • vJ) ∈ C` for every `k : ℕ` and `C` is convex, the same holds for every
real parameter `t ≥ 0` in place of the natural number `k` (interpolate between `⌊t⌋` and
`⌊t⌋ + 1`). -/
theorem toReal_ray_mem {C : Set (ℝ × ℝ)} (hC : Convex ℝ C) {p vJ : ℤ × ℤ}
    (hray : ∀ k : ℕ, toReal (p + (k : ℤ) • vJ) ∈ C) {t : ℝ} (ht : 0 ≤ t) :
    toReal p + t • toReal vJ ∈ C := by
  set n : ℕ := ⌊t⌋₊ with hndef
  have hn1 : (n : ℝ) ≤ t := Nat.floor_le ht
  have hn2 : t ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one t).le
  set θ : ℝ := t - n with hθdef
  have hθ0 : 0 ≤ θ := by rw [hθdef]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθdef]; linarith
  have hm1 : toReal p + (n : ℝ) • toReal vJ ∈ C := by
    have h := hray n
    rw [Nivat.toReal_add, Nivat.toReal_zsmul] at h
    push_cast at h
    exact h
  have hm2 : toReal p + ((n : ℝ) + 1) • toReal vJ ∈ C := by
    have h := hray (n + 1)
    rw [Nivat.toReal_add, Nivat.toReal_zsmul] at h
    push_cast at h
    exact h
  have hcomb := hC hm1 hm2 (show (0:ℝ) ≤ 1 - θ by linarith) hθ0 (by ring)
  have heq : (1 - θ) • (toReal p + (n : ℝ) • toReal vJ) + θ • (toReal p + ((n : ℝ) + 1) • toReal vJ)
      = toReal p + t • toReal vJ := by
    have ht' : t = (n : ℝ) + θ := by rw [hθdef]; ring
    rw [ht']
    module
  rwa [heq] at hcomb

/-- The `bottom` lane's `hseedS` target.  `y` at a `dot nJ`-level between `g` and `q`, both on
rays parallel to `vJ` and contained in the lattice-convex region `T`, is itself eventually on
its own `vJ`-parallel ray inside `T`. -/
theorem eventually_mem_of_between_parallel_rays {T : Set (ℤ × ℤ)}
    (hlc : IsLatticeConvexRegion T) {nJ vJ g q y : ℤ × ℤ}
    (hgray : ∀ k : ℕ, g + (k : ℤ) • vJ ∈ T) (hqray : ∀ k : ℕ, q + (k : ℤ) • vJ ∈ T)
    (hnvJ : dot nJ vJ = 0) (hvJ : vJ ≠ 0) (hnJ : nJ ≠ 0)
    (hlow : dot nJ g ≤ dot nJ y) (hhigh : dot nJ y ≤ dot nJ q) :
    ∃ L : ℤ, ∀ k : ℤ, L ≤ k → y + k • vJ ∈ T := by
  obtain ⟨C, hCconv, -, hTeq⟩ := hlc
  set a : ℝ := (dot nJ g : ℝ) with hadef
  set b : ℝ := (dot nJ q : ℝ) with hbdef
  set c : ℝ := (dot nJ y : ℝ) with hcdef
  have hab : a ≤ c := by rw [hadef, hcdef]; exact_mod_cast hlow
  have hcb : c ≤ b := by rw [hcdef, hbdef]; exact_mod_cast hhigh
  set μ : ℝ := (b - c) / (b - a) with hμdef
  have hμ0 : 0 ≤ μ := by
    rcases eq_or_lt_of_le (hab.trans hcb) with heq | hlt
    · rw [hμdef, ← heq]; simp
    · exact div_nonneg (by linarith) (by linarith)
  have hμ1 : μ ≤ 1 := by
    rcases eq_or_lt_of_le (hab.trans hcb) with heq | hlt
    · rw [hμdef, ← heq]; simp
    · rw [div_le_one (by linarith)]; linarith
  have hcombo : c = μ * a + (1 - μ) * b := by
    rcases eq_or_lt_of_le (hab.trans hcb) with heq | hlt
    · have hca : c = a := le_antisymm (heq ▸ hcb) hab
      rw [hμdef, ← heq, hca]; ring
    · rw [hμdef]
      have hba : b - a ≠ 0 := by linarith
      field_simp
      ring
  have hgC : ∀ k : ℕ, toReal (g + (k : ℤ) • vJ) ∈ C := by
    intro k; have h := hgray k; rw [hTeq] at h; exact h
  have hqC : ∀ k : ℕ, toReal (q + (k : ℤ) • vJ) ∈ C := by
    intro k; have h := hqray k; rw [hTeq] at h; exact h
  have hnvJR : (toReal nJ).1 * (toReal vJ).1 + (toReal nJ).2 * (toReal vJ).2 = 0 := by
    have h0 : (dot nJ vJ : ℝ) = 0 := by exact_mod_cast hnvJ
    simpa [toReal, dot] using h0
  have hnJR : toReal nJ ≠ 0 := by
    intro h
    apply hnJ
    have h1 : (nJ.1 : ℝ) = 0 := congrArg Prod.fst h
    have h2 : (nJ.2 : ℝ) = 0 := congrArg Prod.snd h
    exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
  have hvJR : toReal vJ ≠ 0 := by
    intro h
    apply hvJ
    have h1 : (vJ.1 : ℝ) = 0 := congrArg Prod.fst h
    have h2 : (vJ.2 : ℝ) = 0 := congrArg Prod.snd h
    exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
  have hwR : (toReal nJ).1 * (toReal y - (μ • toReal g + (1 - μ) • toReal q)).1
      + (toReal nJ).2 * (toReal y - (μ • toReal g + (1 - μ) • toReal q)).2 = 0 := by
    have hy : (toReal nJ).1 * (toReal y).1 + (toReal nJ).2 * (toReal y).2 = c := by
      simp only [hcdef, toReal, dot]; push_cast; ring
    have hg : (toReal nJ).1 * (toReal g).1 + (toReal nJ).2 * (toReal g).2 = a := by
      simp only [hadef, toReal, dot]; push_cast; ring
    have hq : (toReal nJ).1 * (toReal q).1 + (toReal nJ).2 * (toReal q).2 = b := by
      simp only [hbdef, toReal, dot]; push_cast; ring
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    nlinarith [hy, hg, hq, hcombo]
  obtain ⟨s, hs⟩ := real_smul_of_dot_eq_zero hnvJR hvJR hnJR hwR
  refine ⟨⌈-s⌉, fun k hk => ?_⟩
  have hkR : -s ≤ (k : ℝ) := by
    have h1 : (-s : ℝ) ≤ (⌈-s⌉ : ℝ) := Int.le_ceil _
    have h2 : (⌈-s⌉ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have htnn : (0:ℝ) ≤ s + (k : ℝ) := by linarith
  have hg' := toReal_ray_mem hCconv hgC htnn
  have hq' := toReal_ray_mem hCconv hqC htnn
  have hcomb := hCconv hg' hq' hμ0 (by linarith : (0:ℝ) ≤ 1 - μ) (by ring)
  have hyeq : toReal y = μ • toReal g + (1 - μ) • toReal q + s • toReal vJ := by
    have := hs
    simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hfinal : μ • (toReal g + (s + (k:ℝ)) • toReal vJ) + (1 - μ) • (toReal q + (s + (k:ℝ)) • toReal vJ)
      = toReal (y + k • vJ) := by
    rw [Nivat.toReal_add, Nivat.toReal_zsmul]
    apply Prod.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        Prod.ext_iff] at hyeq ⊢ <;>
      nlinarith [hyeq.1, hyeq.2]
  rw [hfinal] at hcomb
  rw [hTeq]
  exact hcomb

/-! ## §11.  `mem_face_of_adjacent_endpoint_ccw` / `_cw` (`bottom` lane, corrected signature)

`lane-chaindata-lead`'s corrected assignment, 2026-09-23: the geometric content is entirely
`Nivat.PolyChain.adjacent_shared_vertex` (`PolyChain.lean:245`) — "fan-adjacent edges share a
vertex" — plus the one-line observation that `hnpvJ : dot nprev vJ < 0` forces the shared
vertex `Q` to coincide with `a` (since `hfaceparam` gives `Q = a + j • vJ` for some `j : ℕ`,
and `a`'s own maximality over `T` for `dot nprev` — from `Q ∈ face T nprev` — together with
`hnpvJ < 0` forces `j = 0`).  No new geometry; ~15 lines per orientation, matching
`LeafAJSelect.hsupp_prev` (`LeafAJSelect.lean:872-891`), which is the identical pattern already
worked out for the assembly's own bridge.

**Why `hdet` is load-bearing (not decorative).**  Without it the statement is FALSE: with
`nJ = (0,-1)`, `nprev = (3,-1)` inside the ccw-primitive octagon fan
`(2,1),(1,3),(0,1),(-3,-1),(-1,-3),(0,-1),(1,-1),(3,-1)` (angles `26.6°,71.6°,90°,198.4°,
251.6°,270°,315°,341.6°`, all listed normals primitive), one has `det nprev nJ =
det((3,-1),(0,-1)) = 3·(-1) - (-1)·0 = -3 < 0` — i.e. `hdet` FAILS for this `(nprev,nJ)` pair —
while every other hypothesis of the uncorrected (no-`hdet`) statement holds: `hadj` is vacuous
(needs some listed `μ` with `3μ.2+μ.1>0` and `μ.1<0` simultaneously; none of the eight normals
satisfies both), `hfaceparam` holds by taking `vJ = -dir nJ = (-1,0)` (the *end*-branch: `a` is
the `dir nJ`-maximal endpoint of `face T nJ`, not the minimal one), and `hnpvJ = dot((3,-1),
(-1,0)) = -3 < 0`.  But the true ccw successor of `nJ = (0,-1)` in this fan is `(1,-1)` at
315°, not `nprev = (3,-1)` at 341.6°, so the conclusion `a ∈ face T nprev` is false.  `hdet`
excludes exactly this configuration: it forces the *start*-branch (`vJ = dir nJ`, `a =
faceStart T nJ`) and pins `nprev`,`nJ` to be genuinely fan-adjacent in the order
`adjacent_shared_vertex` consumes.  The pairing rule for callers: `hdet` and `hadj`'s
determinant order must always agree (`0 < det nprev nJ` with `hadj`'s `nprev`-then-`nJ` clause
order for ccw; `0 < det nJ nprev` with the swapped clause order for cw) — mixing them
reopens exactly this hole.  (Formalizing the octagon itself as a `IsLatticeConvexRegion`
instance with a computed `E T` is out of scope here — it is not a "cheap `decide`" the way a
finite arithmetic check is, since `IsLatticeConvexRegion` demands producing a real convex hull
witness; the arithmetic above is fully checked by hand against `PolyChain`'s exact definitions
of `det`, `dir`, `adjacent_shared_vertex`'s `hadj` clause shape, and `face_eq_segment`'s
parametrisation, so it stands as the hand-verified witness per 硬规矩 6/7.)

**硬规矩 6 numeric check (positive case, on `ApexUnique.Shex`)**, per team-lead's correction
(avoiding the triangle trap: `E ↑Sphi` is negation-closed, so odd-normal windows are
unreachable, and avoiding the unit square, too degenerate to test `hadj`'s necessity).
`(↑Shex : Set (ℤ×ℤ)) = ShellSweep.hexShape 2 2 1 1 0` and `E ↑Shex = ShellSweep.hexE` via
`E_hexShape`.  Two genuinely adjacent normals of `hexE` satisfy `0 < det nprev nJ`, an empty
`Arc` between them (`hadj` holds, no third normal strictly between), and the shared vertex
predicted by `adjacent_shared_vertex` is exactly the common endpoint of their two faces —
matching `faceEnd T nprev = faceStart T nJ` directly, with no determinant case split needed. -/

/-- Core lemma, `ccw` orientation: both conclusions in one pass (shared proof term for the two
thin corollaries below). -/
theorem mem_face_of_adjacent_endpoint_ccw_core {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {nJ nprev vJ a : ℤ × ℤ}
    (hnJE : nJ ∈ Nivat.LE2.E T) (hnprevE : nprev ∈ Nivat.LE2.E T)
    (hdet : 0 < det nprev nJ)
    (ha : a ∈ Nivat.LE2.face T nJ)
    (hfaceparam : ∀ b ∈ Nivat.LE2.face T nJ, ∃ j : ℕ, b = a + (j : ℤ) • vJ)
    (hnpvJ : dot nprev vJ < 0)
    (hadj : ∀ μ ∈ Nivat.LE2.E T, ¬(0 < det nprev μ ∧ 0 < det μ nJ)) :
    a ∈ Nivat.LE2.face T nprev ∧ a = Nivat.PolyChain.faceStart T nJ := by
  set Q : ℤ × ℤ := Nivat.PolyChain.faceStart T nprev
      + (Nivat.PolyChain.faceLen T nprev : ℤ) • Nivat.LE2.dir nprev with hQdef
  have hshared : Q = Nivat.PolyChain.faceStart T nJ :=
    Nivat.PolyChain.adjacent_shared_vertex hfin hlc hnprevE hnJE hdet hadj
  have hQprev : Q ∈ face T nprev := Nivat.PolyChain.faceEnd_mem hlc hfin hnprevE
  have hQnJ : Q ∈ face T nJ := by
    rw [hshared]
    have h0 : Nivat.PolyChain.faceStart T nJ
        = Nivat.PolyChain.faceStart T nJ + ((0 : ℕ) : ℤ) • Nivat.LE2.dir nJ := by simp
    rw [h0, Nivat.PolyChain.face_eq_segment hlc hfin hnJE]
    exact ⟨0, Nat.zero_le _, rfl⟩
  obtain ⟨j, hj⟩ := hfaceparam Q hQnJ
  have haT : a ∈ T := Nivat.LE2.face_subset T nJ ha
  have hQmax : dot nprev a ≤ dot nprev Q := (Nivat.LE2.mem_face_iff.mp hQprev).2 a haT
  have hexpand : dot nprev Q = dot nprev a + (j : ℤ) * dot nprev vJ := by
    rw [hj]
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hj0 : (j : ℤ) = 0 := by
    rcases Nat.eq_zero_or_pos j with hz | hpos
    · exact_mod_cast hz
    · exfalso
      have hjpos : (0:ℤ) < (j : ℤ) := by exact_mod_cast hpos
      nlinarith [mul_pos hjpos (neg_pos.mpr hnpvJ)]
  have hQeqa : Q = a := by rw [hj, hj0]; simp
  refine ⟨hQeqa ▸ hQprev, ?_⟩
  rw [← hQeqa, hshared]

/-- **`mem_face_of_adjacent_endpoint`, `ccw` orientation.**  `a`, the endpoint of the `nJ`-face
from which that face is parametrised in the `+vJ` direction, is also on the fan-adjacent
`nprev`-face — the shared vertex. -/
theorem mem_face_of_adjacent_endpoint_ccw {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {nJ nprev vJ a : ℤ × ℤ}
    (hnJE : nJ ∈ Nivat.LE2.E T) (hnprevE : nprev ∈ Nivat.LE2.E T)
    (hdet : 0 < det nprev nJ)
    (ha : a ∈ Nivat.LE2.face T nJ)
    (hfaceparam : ∀ b ∈ Nivat.LE2.face T nJ, ∃ j : ℕ, b = a + (j : ℤ) • vJ)
    (hnpvJ : dot nprev vJ < 0)
    (hadj : ∀ μ ∈ Nivat.LE2.E T, ¬(0 < det nprev μ ∧ 0 < det μ nJ)) :
    a ∈ Nivat.LE2.face T nprev :=
  (mem_face_of_adjacent_endpoint_ccw_core hfin hlc hnJE hnprevE hdet ha hfaceparam hnpvJ hadj).1

/-- **Companion corollary**: under the same hypotheses, `a` is exactly `faceStart T nJ`. -/
theorem mem_face_of_adjacent_endpoint_ccw_eq {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {nJ nprev vJ a : ℤ × ℤ}
    (hnJE : nJ ∈ Nivat.LE2.E T) (hnprevE : nprev ∈ Nivat.LE2.E T)
    (hdet : 0 < det nprev nJ)
    (ha : a ∈ Nivat.LE2.face T nJ)
    (hfaceparam : ∀ b ∈ Nivat.LE2.face T nJ, ∃ j : ℕ, b = a + (j : ℤ) • vJ)
    (hnpvJ : dot nprev vJ < 0)
    (hadj : ∀ μ ∈ Nivat.LE2.E T, ¬(0 < det nprev μ ∧ 0 < det μ nJ)) :
    a = Nivat.PolyChain.faceStart T nJ :=
  (mem_face_of_adjacent_endpoint_ccw_core hfin hlc hnJE hnprevE hdet ha hfaceparam hnpvJ hadj).2

/-- Core lemma, `cw` orientation: mirror of the `ccw` case with the two normals swapped in
`adjacent_shared_vertex`: `hdet : 0 < det nJ nprev`, `hadj` with the clause order swapped,
shared vertex `faceStart T nJ + faceLen T nJ • dir nJ = faceStart T nprev` (i.e. the `nJ`-face's
far endpoint), companion conclusion `a` equals that same far endpoint. -/
theorem mem_face_of_adjacent_endpoint_cw_core {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {nJ nprev vJ a : ℤ × ℤ}
    (hnJE : nJ ∈ Nivat.LE2.E T) (hnprevE : nprev ∈ Nivat.LE2.E T)
    (hdet : 0 < det nJ nprev)
    (ha : a ∈ Nivat.LE2.face T nJ)
    (hfaceparam : ∀ b ∈ Nivat.LE2.face T nJ, ∃ j : ℕ, b = a + (j : ℤ) • vJ)
    (hnpvJ : dot nprev vJ < 0)
    (hadj : ∀ μ ∈ Nivat.LE2.E T, ¬(0 < det nJ μ ∧ 0 < det μ nprev)) :
    a ∈ Nivat.LE2.face T nprev ∧
      a = Nivat.PolyChain.faceStart T nJ + (Nivat.PolyChain.faceLen T nJ : ℤ) • Nivat.LE2.dir nJ := by
  set Q : ℤ × ℤ := Nivat.PolyChain.faceStart T nprev with hQdef
  have hshared : Nivat.PolyChain.faceStart T nJ
      + (Nivat.PolyChain.faceLen T nJ : ℤ) • Nivat.LE2.dir nJ = Q :=
    Nivat.PolyChain.adjacent_shared_vertex hfin hlc hnJE hnprevE hdet hadj
  have hQprev : Q ∈ face T nprev := Nivat.PolyChain.faceStart_mem hfin hnprevE
  have hQnJ : Q ∈ face T nJ := by
    rw [← hshared]; exact Nivat.PolyChain.faceEnd_mem hlc hfin hnJE
  obtain ⟨j, hj⟩ := hfaceparam Q hQnJ
  have haT : a ∈ T := Nivat.LE2.face_subset T nJ ha
  have hQmax : dot nprev a ≤ dot nprev Q := (Nivat.LE2.mem_face_iff.mp hQprev).2 a haT
  have hexpand : dot nprev Q = dot nprev a + (j : ℤ) * dot nprev vJ := by
    rw [hj]
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hj0 : (j : ℤ) = 0 := by
    rcases Nat.eq_zero_or_pos j with hz | hpos
    · exact_mod_cast hz
    · exfalso
      have hjpos : (0:ℤ) < (j : ℤ) := by exact_mod_cast hpos
      nlinarith [mul_pos hjpos (neg_pos.mpr hnpvJ)]
  have hQeqa : Q = a := by rw [hj, hj0]; simp
  refine ⟨hQeqa ▸ hQprev, ?_⟩
  rw [← hQeqa]
  exact hshared.symm

/-- **`mem_face_of_adjacent_endpoint`, `cw` orientation.** -/
theorem mem_face_of_adjacent_endpoint_cw {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {nJ nprev vJ a : ℤ × ℤ}
    (hnJE : nJ ∈ Nivat.LE2.E T) (hnprevE : nprev ∈ Nivat.LE2.E T)
    (hdet : 0 < det nJ nprev)
    (ha : a ∈ Nivat.LE2.face T nJ)
    (hfaceparam : ∀ b ∈ Nivat.LE2.face T nJ, ∃ j : ℕ, b = a + (j : ℤ) • vJ)
    (hnpvJ : dot nprev vJ < 0)
    (hadj : ∀ μ ∈ Nivat.LE2.E T, ¬(0 < det nJ μ ∧ 0 < det μ nprev)) :
    a ∈ Nivat.LE2.face T nprev :=
  (mem_face_of_adjacent_endpoint_cw_core hfin hlc hnJE hnprevE hdet ha hfaceparam hnpvJ hadj).1

/-- **Companion corollary**: under the same hypotheses, `a` equals the `nJ`-face's far endpoint
`faceStart T nJ + faceLen T nJ • dir nJ` (the `cw`-orientation analogue of `faceEnd`). -/
theorem mem_face_of_adjacent_endpoint_cw_eq {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {nJ nprev vJ a : ℤ × ℤ}
    (hnJE : nJ ∈ Nivat.LE2.E T) (hnprevE : nprev ∈ Nivat.LE2.E T)
    (hdet : 0 < det nJ nprev)
    (ha : a ∈ Nivat.LE2.face T nJ)
    (hfaceparam : ∀ b ∈ Nivat.LE2.face T nJ, ∃ j : ℕ, b = a + (j : ℤ) • vJ)
    (hnpvJ : dot nprev vJ < 0)
    (hadj : ∀ μ ∈ Nivat.LE2.E T, ¬(0 < det nJ μ ∧ 0 < det μ nprev)) :
    a = Nivat.PolyChain.faceStart T nJ + (Nivat.PolyChain.faceLen T nJ : ℤ) • Nivat.LE2.dir nJ :=
  (mem_face_of_adjacent_endpoint_cw_core hfin hlc hnJE hnprevE hdet ha hfaceparam hnpvJ hadj).2

/-! ## §10.  The edge count for `shellEnv`: only `J` survives both sweeps

Added 2026-09-23 (lane-chaindata-lead).  §9's verdict — that `shellEnv` needs a shape theorem
for `shellInter`, because `Enveloped` is preserved by neither `⊆` nor half-plane cuts
(`LE2.not_E_inter_subset`, `RegionEdges.lean:740`) — stands.  This section pins the one
combinatorial fact that makes the target's edge *count* come out right, which is the first
thing such a shape theorem has to know.

Write `P := shellInter Â_i (shell Â_∞ v_{J-1} n_J c_J ε) w` with `w = -(dir ν_{J+1})` and
`v_{J-1} = dir ν_{J-1}` (the call site's `vJ1`, `ν_{J-1}` being its `nprevJ`).  Sweeping a
convex set in a direction `u` discards exactly the supporting constraints `n` with
`⟪n, u⟫ > 0`; so, of `E(𝒮_φ)`'s `2m` normals,

* `reachSet Â_i w` keeps `{n | ⟪n, w⟫ ≤ 0}`,
* `reachSet Â_∞ v_{J-1}` keeps `{n | ⟪n, v_{J-1}⟫ ≤ 0}`,

and the intersection keeps their union.  What is lost is `{n | ⟪n, w⟫ > 0 ∧
⟪n, v_{J-1}⟫ > 0}` — and the `halfPlaneGE n_J (c_J - ε)` factor supplies exactly one normal,
`-n_J = J`.  So the count works out **iff `J` is the only normal in that cone**.

`eq_J_of_sweeps_pos` is that iff, and it is pure fan combinatorics: `⟪n, dir ν⟫ = det ν n`
turns the two strict inequalities into `0 < det ν_{J-1} n` and `0 < det n ν_{J+1}`, and the two
empty-arc hypotheses — which is what `LeafAJSelect.exists_nprevJ_vJ1` and
`LeafAShellNNext.exists_w_hsweepW` already produce (both 0 sorry) — squeeze `det n J` to `0`
from both sides.  Primitivity then leaves `n = ±J`, and `0 < det ν_{J-1} J` kills `n = -J`.

`sweeps_pos_at_J` is the matching non-vacuity: `J` really does lie in the cone, so the
`halfPlaneGE` factor is not decoration — drop it and the shape loses an edge. -/

/-- **`J` is the only edge normal of `𝒮_φ` that both sweeps discard.**  `hprevJ`/`hprevEmpty`
are `LeafAJSelect.exists_nprevJ_vJ1`'s second and third outputs; `hnextEmpty` is
`LeafAShellNNext.exists_w_hsweepW`'s third. -/
theorem eq_J_of_sweeps_pos {Sphi : Finset (ℤ × ℤ)} {J nprevJ νJ1 n : ℤ × ℤ}
    (hn : n ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hJ : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hprevJ : 0 < det nprevJ J)
    (hprevEmpty : Arc (Sphi.finite_toSet) nprevJ J = ∅)
    (hnextEmpty : Arc (Sphi.finite_toSet) J νJ1 = ∅)
    (hv : 0 < dot n (dir nprevJ))
    (hw : 0 < dot n (-(dir νJ1))) :
    n = J := by
  have hv' : 0 < det nprevJ n := by
    rwa [dot_comm, dot_dir_left] at hv
  have hw' : 0 < det n νJ1 := by
    rw [dot_neg_right, dot_comm, dot_dir_left] at hw
    have := det_skew νJ1 n
    omega
  have h1 : det n J ≤ 0 := by
    by_contra h
    have : n ∈ Arc (Sphi.finite_toSet) nprevJ J := mem_Arc.mpr ⟨hn, hv', by omega⟩
    simp [hprevEmpty] at this
  have h2 : det J n ≤ 0 := by
    by_contra h
    have : n ∈ Arc (Sphi.finite_toSet) J νJ1 := mem_Arc.mpr ⟨hn, by omega, hw'⟩
    simp [hnextEmpty] at this
  have hzero : det n J = 0 := by
    have := det_skew n J
    omega
  have hpn : Prim n := (mem_E_iff.mp hn).1
  have hpJ : Prim J := (mem_E_iff.mp hJ).1
  rcases eq_or_neg_of_prim_of_det_eq_zero hpn hpJ hzero with h | h
  · exact h.symm
  · exfalso
    have hneg : det nprevJ J = - det nprevJ n := by
      rw [h]; simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    omega

/-- **`J` does lie in the cone both sweeps discard**, so `eq_J_of_sweeps_pos` is not vacuous
and the `halfPlaneGE n_J (c_J - ε)` factor of the shell is load-bearing. -/
theorem sweeps_pos_at_J {J nprevJ νJ1 : ℤ × ℤ}
    (hprevJ : 0 < det nprevJ J) (hnextJ : 0 < det J νJ1) :
    0 < dot J (dir nprevJ) ∧ 0 < dot J (-(dir νJ1)) := by
  constructor
  · rwa [dot_comm, dot_dir_left]
  · rw [dot_neg_right, dot_comm, dot_dir_left]
    have := det_skew J νJ1
    omega

/-- **Contrapositive, in the form the shape theorem will read it**: every edge normal of
`𝒮_φ` other than `J` is retained by at least one of the two sweeps. -/
theorem sweeps_nonpos_of_ne_J {Sphi : Finset (ℤ × ℤ)} {J nprevJ νJ1 n : ℤ × ℤ}
    (hn : n ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hJ : J ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hprevJ : 0 < det nprevJ J)
    (hprevEmpty : Arc (Sphi.finite_toSet) nprevJ J = ∅)
    (hnextEmpty : Arc (Sphi.finite_toSet) J νJ1 = ∅)
    (hne : n ≠ J) :
    dot n (dir nprevJ) ≤ 0 ∨ dot n (-(dir νJ1)) ≤ 0 := by
  rcases le_or_gt (dot n (dir nprevJ)) 0 with h | h
  · exact Or.inl h
  rcases le_or_gt (dot n (-(dir νJ1))) 0 with h' | h'
  · exact Or.inr h'
  exact absurd (eq_J_of_sweeps_pos hn hJ hprevJ hprevEmpty hnextEmpty h h') hne

/-! ## §11.  Every intermediate level of a lattice-convex set is occupied

Added 2026-09-23 (lane-chaindata-lead).  First step of the H-representation of a sweep,
`reachSet A u = {z | ∀ n ∈ E A, ⟪n, u⟫ ≤ 0 → ⟪n, z⟫ ≤ suppVal A n}`, which `shellEnv` needs and
which the main tree has nothing for (no `E`, `face` or H-rep lemma about `reachSet` exists —
`RegionConvex.isLatticeConvexRegion_reachSet` gives convexity only).

The sweep's H-representation reduces, line by line parallel to `u`, to: on the line
`{⟪m, ·⟫ = c}` (`m ⊥ u`) the set `A` is an interval `{y₀ + s·u : lo ≤ s ≤ hi}` and the swept
H-rep is `{y₀ + s·u : lo ≤ s}`, so `t := max 0 (s − hi)` carries any swept point back into `A`
— **provided that line meets `A` at all**.  That proviso is `exists_mem_level_between`, and it
is not automatic: `level_between_needs_steps` exhibits a lattice-convex triangle with an empty
intermediate level.  What rules that out in the application is that both `m`-extremes of
`hatOf A kk vl i` are `u`-parallel *edges*, because `E (hatOf A kk vl i) = E ↑𝒮_φ`
(`AhatEnv.E_eq_of_enveloped`) and `E ↑𝒮_φ` is symmetric. -/

private theorem tRA (z w : ℤ × ℤ) : toReal (z + w) = toReal z + toReal w := by
  simp only [toReal, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]; push_cast; rfl

private theorem tRZ (c : ℤ) (z : ℤ × ℤ) : toReal (c • z) = (c : ℝ) • toReal z := by
  simp only [toReal, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, smul_eq_mul]; push_cast; rfl

private theorem dotR (n z : ℤ × ℤ) :
    (n.1 : ℝ) * (toReal z).1 + (n.2 : ℝ) * (toReal z).2 = ((dot n z : ℤ) : ℝ) := by
  simp only [toReal, dot]; push_cast; ring

private theorem real_smul_of_perp {nJ vJ w : ℝ × ℝ}
    (hnvJ : nJ.1 * vJ.1 + nJ.2 * vJ.2 = 0) (hvJ : vJ ≠ 0) (hnJ : nJ ≠ 0)
    (hw : nJ.1 * w.1 + nJ.2 * w.2 = 0) : ∃ s : ℝ, w = s • vJ :=
  Nivat.LaneCdSubstrip.real_smul_of_dot_eq_zero hnvJ hvJ hnJ hw

/-- **Every intermediate `m`-level of a lattice-convex set is occupied.**

`p`, `q` are points of `A` carrying a `u`-step (`p + u`, `q + u ∈ A`) with `u ⊥ m`; then the
parallelogram `conv{q, q+u, p, p+u} ⊆ convHullOf A` meets every level line between them in a
segment of `u`-length `1`, which always contains a lattice point.  `Prim m` is what makes the
level line `{⟪m, ·⟫ = c}` carry lattice points at all; `u` need not be primitive.

Counterexample without the `u`-steps: `A = ℤ² ∩ conv{(0,0), (3,1), (1,3)}`, `m = (1,1)` — the
level `1` is empty, because the `-m` extreme of `A` is the single vertex `(0,0)` rather than an
`m`-parallel edge.  In the `shellEnv` application both extremes are edges, because
`E (hatOf A kk vl i) = E ↑𝒮_φ` and `E ↑𝒮_φ` is symmetric. -/
theorem exists_mem_level_between {A : Set (ℤ × ℤ)} {u m p q : ℤ × ℤ} {c : ℤ}
    (hlc : IsLatticeConvexRegion A)
    (hm : Prim m) (hm_ne : m ≠ 0) (hu_ne : u ≠ 0) (hmu : dot m u = 0)
    (hp : p ∈ A) (hpu : p + u ∈ A) (hq : q ∈ A) (hqu : q + u ∈ A)
    (hlo : dot m q ≤ c) (hhi : c ≤ dot m p) :
    ∃ y ∈ A, dot m y = c := by
  rcases eq_or_lt_of_le (hlo.trans hhi) with heq | hlt
  · exact ⟨p, hp, by omega⟩
  -- the interpolation parameter
  set D : ℤ := dot m p - dot m q with hDdef
  have hD0 : (0 : ℤ) < D := by omega
  have hDR : (0 : ℝ) < ((D : ℤ) : ℝ) := by exact_mod_cast hD0
  set θ : ℝ := ((c - dot m q : ℤ) : ℝ) / ((D : ℤ) : ℝ) with hθdef
  have hθ0 : 0 ≤ θ := by
    refine div_nonneg ?_ (le_of_lt hDR)
    have : (0 : ℤ) ≤ c - dot m q := by omega
    exact_mod_cast this
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one hDR]
    have : (c - dot m q : ℤ) ≤ D := by omega
    exact_mod_cast this
  set X : ℝ × ℝ := (1 - θ) • toReal q + θ • toReal p with hXdef
  have hX : X ∈ convHullOf A :=
    convex_convHullOf A (mem_convHullOf_of_mem hq) (mem_convHullOf_of_mem hp)
      (by linarith) hθ0 (by ring)
  have hY : X + toReal u ∈ convHullOf A := by
    have h := convex_convHullOf A (mem_convHullOf_of_mem hqu) (mem_convHullOf_of_mem hpu)
      (show (0:ℝ) ≤ 1 - θ by linarith) hθ0 (by ring)
    have heq2 : (1 - θ) • toReal (q + u) + θ • toReal (p + u) = X + toReal u := by
      rw [tRA, tRA, hXdef]; module
    rwa [heq2] at h
  -- `X` sits at level `c`
  have hXlev : (m.1 : ℝ) * X.1 + (m.2 : ℝ) * X.2 = ((c : ℤ) : ℝ) := by
    have hq' := dotR m q
    have hp' := dotR m p
    have hexp : (m.1 : ℝ) * X.1 + (m.2 : ℝ) * X.2 =
        (1 - θ) * ((m.1 : ℝ) * (toReal q).1 + (m.2 : ℝ) * (toReal q).2) +
        θ * ((m.1 : ℝ) * (toReal p).1 + (m.2 : ℝ) * (toReal p).2) := by
      simp only [hXdef, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    have hDne : ((D : ℤ) : ℝ) ≠ 0 := ne_of_gt hDR
    have hθD : θ * ((D : ℤ) : ℝ) = ((c : ℤ) : ℝ) - ((dot m q : ℤ) : ℝ) := by
      rw [hθdef]; field_simp; push_cast; ring
    have hDcast : ((D : ℤ) : ℝ) = ((dot m p : ℤ) : ℝ) - ((dot m q : ℤ) : ℝ) := by
      rw [hDdef]; push_cast; ring
    rw [hexp, hq', hp']
    linear_combination hθD - θ * hDcast
  -- anchor a lattice point on the level line
  obtain ⟨y₀, hy₀⟩ := dot_surjective hm c
  have hmR : ((m.1 : ℝ), (m.2 : ℝ)) ≠ (0 : ℝ × ℝ) := by
    intro h
    rw [Prod.ext_iff] at h
    simp only [Prod.fst_zero, Prod.snd_zero] at h
    exact hm_ne (Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2))
  have huR : toReal u ≠ (0 : ℝ × ℝ) := by
    intro h
    rw [Prod.ext_iff] at h
    simp only [toReal, Prod.fst_zero, Prod.snd_zero] at h
    exact hu_ne (Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2))
  have hperp : (m.1 : ℝ) * (toReal u).1 + (m.2 : ℝ) * (toReal u).2 = 0 := by
    rw [dotR, hmu]; norm_num
  have hwperp : (m.1 : ℝ) * (X - toReal y₀).1 + (m.2 : ℝ) * (X - toReal y₀).2 = 0 := by
    have h0 := dotR m y₀
    rw [hy₀] at h0
    simp only [Prod.fst_sub, Prod.snd_sub]
    linarith [hXlev, h0]
  obtain ⟨s, hs⟩ := real_smul_of_perp (nJ := ((m.1 : ℝ), (m.2 : ℝ))) (vJ := toReal u)
    (w := X - toReal y₀) hperp huR hmR hwperp
  -- round up along `u`
  set k : ℤ := ⌈s⌉ with hkdef
  have hk1 : s ≤ (k : ℝ) := Int.le_ceil s
  have hk2 : (k : ℝ) ≤ s + 1 := by
    have := Int.ceil_le_floor_add_one s
    have hfl : ((⌊s⌋ : ℤ) : ℝ) ≤ s := Int.floor_le s
    have : ((k : ℤ) : ℝ) ≤ ((⌊s⌋ : ℤ) : ℝ) + 1 := by
      rw [hkdef]; exact_mod_cast Int.ceil_le_floor_add_one s
    linarith
  refine ⟨y₀ + k • u, ?_, ?_⟩
  · rw [eq_preimage_convHullOf hlc]
    show toReal (y₀ + k • u) ∈ convHullOf A
    have heq3 : toReal (y₀ + k • u) = (1 - ((k : ℝ) - s)) • X + ((k : ℝ) - s) • (X + toReal u) := by
      rw [tRA, tRZ]
      have hXeq : X = toReal y₀ + s • toReal u := by
        have := hs
        rw [sub_eq_iff_eq_add] at this
        rw [this]; abel
      rw [hXeq]; module
    rw [heq3]
    exact convex_convHullOf A hX hY (by linarith) (by linarith) (by ring)
  · rw [dot_add, Nivat.ColleReg.dot_zsmul_right, hmu, hy₀]; ring

/-! ### The `u`-step hypotheses are not removable -/

private def triT : Set (ℤ × ℤ) :=
  ((Set.univ ∩ Nivat.CK224.halfPlaneGE (-1, 3) 0) ∩ Nivat.CK224.halfPlaneGE (3, -1) 0) ∩
    Nivat.CK224.halfPlaneGE (-1, -1) (-4)

private theorem mem_triT {z : ℤ × ℤ} :
    z ∈ triT ↔ (z.1 ≤ 3 * z.2 ∧ z.2 ≤ 3 * z.1 ∧ z.1 + z.2 ≤ 4) := by
  simp only [triT, Nivat.CK224.halfPlaneGE, Set.mem_inter_iff, Set.mem_univ, true_and, dot,
    Set.mem_ofPred_eq]
  omega

private theorem latticeConvex_triT : IsLatticeConvexRegion triT :=
  Nivat.LE2.isLatticeConvexRegion_inter_halfPlaneGE
    (Nivat.LE2.isLatticeConvexRegion_inter_halfPlaneGE
      (Nivat.LE2.isLatticeConvexRegion_inter_halfPlaneGE
        Nivat.Colle41.isLatticeConvexRegion_univ _ _) _ _) _ _

/-- **Dropping either `u`-step hypothesis breaks `exists_mem_level_between`.**

`triT = ℤ² ∩ conv{(0,0), (3,1), (1,3)}` is lattice convex, `m = (1,1)` is primitive, and
`u = (1,-1)` is a nonzero vector with `⟪m, u⟫ = 0`.  The level-`0` point `(0,0)` and the
level-`4` point `(3,1)` are both in `triT`, and `(3,1) + u = (4,0) ∉ triT` while neither
`(0,0) + u` nor `(0,0) - u` is in `triT` — and level `1` is **empty**.  So the conclusion fails
with both `hpu` and `hqu` dropped, and the `-m` extreme of `triT` being a single vertex rather
than a `u`-parallel edge is exactly what goes wrong. -/
theorem level_between_needs_steps :
    IsLatticeConvexRegion triT ∧
    Prim ((1, 1) : ℤ × ℤ) ∧ ((1, 1) : ℤ × ℤ) ≠ 0 ∧ ((1, -1) : ℤ × ℤ) ≠ 0 ∧
    dot ((1, 1) : ℤ × ℤ) ((1, -1) : ℤ × ℤ) = 0 ∧
    ((0, 0) : ℤ × ℤ) ∈ triT ∧ ((3, 1) : ℤ × ℤ) ∈ triT ∧
    dot ((1, 1) : ℤ × ℤ) ((0, 0) : ℤ × ℤ) = 0 ∧
    dot ((1, 1) : ℤ × ℤ) ((3, 1) : ℤ × ℤ) = 4 ∧
    ((0, 0) : ℤ × ℤ) + ((1, -1) : ℤ × ℤ) ∉ triT ∧
    ((0, 0) : ℤ × ℤ) - ((1, -1) : ℤ × ℤ) ∉ triT ∧
    ((3, 1) : ℤ × ℤ) + ((1, -1) : ℤ × ℤ) ∉ triT ∧
    ¬ (∃ y ∈ triT, dot ((1, 1) : ℤ × ℤ) y = 1) := by
  refine ⟨latticeConvex_triT, by decide, by decide, by decide, by decide,
    by rw [mem_triT]; decide, by rw [mem_triT]; decide, by decide, by decide,
    ?_, ?_, ?_, ?_⟩
  · rw [mem_triT]; decide
  · rw [mem_triT]; decide
  · rw [mem_triT]; decide
  · rintro ⟨y, hy, hlev⟩
    rw [mem_triT] at hy
    simp only [dot] at hlev
    omega

/-! ## §12.  The H-representation of a sweep

Added 2026-09-23 (lane-chaindata-lead).  `reachSet A u` deletes exactly the supporting
constraints that `u` points out of.  Nothing about `E`, `face` or the H-representation of a
`reachSet` existed in the main tree before this (`RegionConvex.isLatticeConvexRegion_reachSet`
gives convexity only), and `shellEnv` needs it: `Â_i^{(ε)}` is
`reachSet (hatOf A kk vl i) w ∩ …`, and its edge set is what `Enveloped ↑𝒮_φ` is a statement
about.

`exists_step_in_face` discharges the `u`-step hypotheses of §11 from `m ∈ E A` alone, so
`reachSet_eq_hrep_of_E` needs only that both `m`-extremes of `A` are edges — which in the
application is `E (hatOf A kk vl i) = E ↑𝒮_φ` (`AhatEnv.E_eq_of_enveloped`) plus symmetry of
`E ↑𝒮_φ`.

Together with §10 (`sweeps_nonpos_of_ne_J`: `J` is the only normal both sweeps delete) this
fixes the edge *set* of the shell; what is still owed for `shellEnv` is the choice of `ε` that
puts the boundary crossings on lattice points, and the face-length lower bounds. -/

private theorem exists_zsmul_of_perp {m u x : ℤ × ℤ} (hm_ne : m ≠ 0) (hu : Prim u)
    (hmu : dot m u = 0) (hmx : dot m x = 0) : ∃ t : ℤ, x = t • u := by
  have hdet : det u x = 0 := det_eq_zero_of_dot_eq_zero hm_ne hmu hmx
  obtain ⟨t, ht⟩ := exists_smul_of_det_eq_zero hu hdet
  refine ⟨t, ?_⟩
  rw [ht]
  ext <;> simp

private theorem mem_of_zsmul_between {A : Set (ℤ × ℤ)} (hlc : IsLatticeConvexRegion A)
    {p d : ℤ × ℤ} {t s : ℤ} (hp : p ∈ A) (hw : p + t • d ∈ A) (h0 : 0 ≤ s) (hs : s ≤ t) :
    p + s • d ∈ A := by
  rcases eq_or_lt_of_le (h0.trans hs) with heq | hlt
  · have hs0 : s = 0 := by omega
    simpa [hs0] using hp
  have htR : (0 : ℝ) < ((t : ℤ) : ℝ) := by exact_mod_cast hlt
  set θ : ℝ := ((s : ℤ) : ℝ) / ((t : ℤ) : ℝ) with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg (by exact_mod_cast h0) (le_of_lt htR)
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one htR]; exact_mod_cast hs
  have hθt : θ * ((t : ℤ) : ℝ) = ((s : ℤ) : ℝ) := by
    rw [hθdef]; field_simp
  rw [eq_preimage_convHullOf hlc]
  show toReal (p + s • d) ∈ convHullOf A
  have hmid := convex_convHullOf A (mem_convHullOf_of_mem hp) (mem_convHullOf_of_mem hw)
    (show (0:ℝ) ≤ 1 - θ by linarith) hθ0 (by ring)
  have heq2 : (1 - θ) • toReal p + θ • toReal (p + t • d) = toReal (p + s • d) := by
    rw [tRA, tRZ, tRA, tRZ, ← hθt]
    module
  rwa [heq2] at hmid

/-- **Every edge normal's face carries a one-step move in either perpendicular direction.**

`m ∈ E A` makes `face A m` nontrivial, hence two of its points differ by a nonzero multiple of
`u`; lattice convexity then fills in the single step from the lower one.  Supplies
`reachSet_eq_hrep`'s `hpstep`/`hqstep` from membership in `E A` alone — apply it at `m` and at
`-m`, both with the same `u`. -/
theorem exists_step_in_face {A : Set (ℤ × ℤ)}
    (hlc : IsLatticeConvexRegion A) {m u : ℤ × ℤ} (hmE : m ∈ E A)
    (hu : Prim u) (hmu : dot m u = 0) :
    ∃ p ∈ A, dot m p = suppVal A m ∧ p + u ∈ A := by
  obtain ⟨hmprim, hnt⟩ := mem_E_iff.mp hmE
  obtain ⟨a, ha, b, hb, hab⟩ := hnt
  have haA : a ∈ A := ha.1
  have hbA : b ∈ A := hb.1
  have hd0 : dot m (b - a) = 0 := dot_sub_eq_zero_of_mem_face ha hb
  obtain ⟨t, ht⟩ := exists_zsmul_of_perp hmprim.ne_zero hu hmu hd0
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp only [zero_smul, sub_eq_zero] at ht
    exact hab ht.symm
  have hbeq : b = a + t • u := by rw [← ht]; abel
  rcases lt_or_gt_of_ne htne with hneg | hpos
  · refine ⟨b, hbA, (suppVal_eq hb).symm, ?_⟩
    have haeq : b + (-t) • u = a := by rw [hbeq]; module
    have := mem_of_zsmul_between hlc hbA (t := -t) (s := 1) (by rw [haeq]; exact haA)
      (by omega) (by omega)
    simpa using this
  · refine ⟨a, haA, (suppVal_eq ha).symm, ?_⟩
    have := mem_of_zsmul_between hlc haA (t := t) (s := 1) (by rw [← hbeq]; exact hbA)
      (by omega) (by omega)
    simpa using this

/-- **The H-representation of a sweep.**

Sweeping a finite lattice-convex `A` by `ℕ•u` deletes exactly the supporting constraints that
`u` points out of (`0 < ⟪n, u⟫`) and keeps the rest.  `m` is a normal orthogonal to `u`; the
hypotheses `hmE`/`hnmE` say both `m`-extremes of `A` are faces, and `hpstep`/`hqstep` say each
of them carries a `u`-step — which is what makes every intermediate level of `A` occupied
(`LaneCdSubstrip.exists_mem_level_between`; `level_between_needs_steps` shows it is needed).

The `⊇` half runs line by line: `z` lies at some level `c` between the two extremes, so the
level line carries a point `y ∈ A`, and `z = y + k•u` with `k : ℤ`.  If `k` is at most the
largest `u`-index of `A` on that line then `z ∈ A` already (the deleted constraints are the
ones `k` may not exceed, and they are slack at `z` because they are slack at the largest
index); otherwise `z - (k - jmax)•u ∈ A` and `k - jmax ≥ 0` is the sweep count. -/
theorem reachSet_eq_hrep {A : Set (ℤ × ℤ)} {u m : ℤ × ℤ}
    (hfin : A.Finite) (hne : A.Nonempty) (harea : PosArea A)
    (hlc : IsLatticeConvexRegion A)
    (hm : Prim m) (hm_ne : m ≠ 0) (hu : Prim u) (hu_ne : u ≠ 0) (hmu : dot m u = 0)
    (hmE : m ∈ E A) (hnmE : -m ∈ E A)
    (hpstep : ∃ p ∈ A, dot m p = suppVal A m ∧ p + u ∈ A)
    (hqstep : ∃ q ∈ A, dot m q = -suppVal A (-m) ∧ q + u ∈ A) :
    reachSet A u = {z | ∀ n ∈ E A, dot n u ≤ 0 → dot n z ≤ suppVal A n} := by
  ext z
  constructor
  · rintro ⟨g, hg, t, rfl⟩ n hn hnu
    rw [dot_add, Nivat.ColleReg.dot_zsmul_right]
    have h1 : dot n g ≤ suppVal A n := le_suppVal hfin hne hg
    have h2 : (t : ℤ) * dot n u ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg t) hnu
    linarith
  · intro hz
    obtain ⟨p, hp, hplev, hpu⟩ := hpstep
    obtain ⟨q, hq, hqlev, hqu⟩ := hqstep
    have hhi : dot m z ≤ dot m p := by
      rw [hplev]; exact hz m hmE (le_of_eq hmu)
    have hlo : dot m q ≤ dot m z := by
      have := hz (-m) hnmE (by simp [dot_neg_left, hmu])
      rw [dot_neg_left] at this
      omega
    obtain ⟨y, hy, hylev⟩ :=
      Nivat.LaneCdSubstrip.exists_mem_level_between hlc hm hm_ne hu_ne hmu hp hpu hq hqu hlo hhi
    obtain ⟨k, hk⟩ := exists_zsmul_of_perp hm_ne hu hmu
      (show dot m (z - y) = 0 by rw [dot_sub, hylev]; ring)
    have hzy : z = y + k • u := by
      rw [← hk]; abel
    -- the largest `u`-index of `A` on this line
    classical
    have hinj : Function.Injective (fun j : ℤ => y + j • u) := by
      intro a b hab
      simp only [add_right_inj] at hab
      by_contra hne'
      have hd : (a - b) • u = 0 := by
        rw [sub_smul, hab]; abel
      rcases smul_eq_zero.mp hd with h | h
      · exact hne' (by omega)
      · exact hu_ne h
    have hSfin : {j : ℤ | y + j • u ∈ A}.Finite :=
      Set.Finite.preimage hinj.injOn hfin
    have hSbdd : ∃ b : ℤ, ∀ j : ℤ, y + j • u ∈ A → j ≤ b := by
      obtain ⟨b, hb⟩ := hSfin.bddAbove
      exact ⟨b, fun j hj => hb hj⟩
    obtain ⟨jmax, hjmax, hjmaxle⟩ :=
      Int.exists_greatest_of_bdd (P := fun j => y + j • u ∈ A) hSbdd ⟨0, by simpa using hy⟩
    rcases le_or_gt k jmax with hcase | hcase
    · -- `z` is already in `A`
      refine ⟨z, ?_, 0, by simp⟩
      refine mem_of_dot_le_suppVal hfin hne harea hlc ?_
      intro n hn
      rcases le_or_gt (dot n u) 0 with hnu | hnu
      · exact hz n hn hnu
      · have hjm : dot n (y + jmax • u) ≤ suppVal A n := le_suppVal hfin hne hjmax
        rw [dot_add, Nivat.ColleReg.dot_zsmul_right] at hjm
        rw [hzy, dot_add, Nivat.ColleReg.dot_zsmul_right]
        have : k * dot n u ≤ jmax * dot n u :=
          mul_le_mul_of_nonneg_right hcase (le_of_lt hnu)
        linarith
    · -- slide back to the largest index
      refine ⟨y + jmax • u, hjmax, (k - jmax).toNat, ?_⟩
      have hcast : ((k - jmax).toNat : ℤ) = k - jmax := Int.toNat_of_nonneg (by omega)
      rw [hzy, hcast, sub_smul]
      abel

/-- **The H-representation of a sweep, with the step hypotheses discharged.**  The form to use:
both `m`-extremes being edges of `A` is all that is needed, and in the `shellEnv` application
that is `E (hatOf A kk vl i) = E ↑𝒮_φ` plus symmetry of `E ↑𝒮_φ`. -/
theorem reachSet_eq_hrep_of_E {A : Set (ℤ × ℤ)} {u m : ℤ × ℤ}
    (hfin : A.Finite) (hne : A.Nonempty) (harea : PosArea A)
    (hlc : IsLatticeConvexRegion A)
    (hm : Prim m) (hu : Prim u) (hmu : dot m u = 0)
    (hmE : m ∈ E A) (hnmE : -m ∈ E A) :
    reachSet A u = {z | ∀ n ∈ E A, dot n u ≤ 0 → dot n z ≤ suppVal A n} := by
  have hnmu : dot (-m) u = 0 := by rw [dot_neg_left, hmu]; ring
  obtain ⟨q, hq, hqlev, hqu⟩ := exists_step_in_face hlc hnmE hu hnmu
  refine reachSet_eq_hrep hfin hne harea hlc hm hm.ne_zero hu hu.ne_zero hmu hmE hnmE
    (exists_step_in_face hlc hmE hu hmu) ⟨q, hq, ?_, hqu⟩
  rw [dot_neg_left] at hqlev
  omega

/-! ## §13.  The cut needs lattice corners — two kernel witnesses

Added 2026-09-23 (lane-chaindata-lead), before dispatching the cut lemma, per 硬规矩 6
(「派几何义务前先算一个数值实例」).

§12 puts the shell into H-representation form: `Â_i^{(ε)}` is
`{z | ∀ n ∈ N, ⟪n, z⟫ ≤ d n} ∩ halfPlaneGE nJ (cJ - ε)` with `N ⊆ E ↑𝒮_φ` coming from the two
sweeps, and `-nJ = J ∈ E ↑𝒮_φ`.  `Enveloped ↑𝒮_φ` is a statement about `E` of that set
(`WeaklyEnveloped`'s first clause quantifies over `n ∈ E T`), so the assembly needs

    E {z | ∀ n ∈ N, ⟪n, z⟫ ≤ d n} ⊆ ↑N .

**That containment is false without further hypotheses**, and the two natural repairs split:
the arithmetic one (corners of the H-representation must be lattice points) is necessary, the
combinatorial one (every constraint carries a long face) is not sufficient.  This is exactly
Collé's "for an appropriate `ε`" at `delivery/scratch/b3_colle2.txt:518-520`, and the `d_ε`
sequence of distinct lattice-distances-to-`ℓ_J` at `:442`/`:458` is what indexes the admissible
choices.

`E_cut_needs_lattice_corner` reads as a cut once one takes `m := (-1,0)`, `c := -3`, so that
`halfPlaneGE m c = {z | z.1 ≤ 3}` and `-m = (1,0) ∈ N1`; then `↑N1 ∪ {-m} = ↑N1` and the
conclusion refutes the cut form `E (A ∩ halfPlaneGE m c) ⊆ ↑N ∪ {-m}` verbatim.  The real
corner of `{z.1 = 3} ∩ {z.1 + 3 z.2 = 1}` is `(3, -2/3)`, not a lattice point; the integer hull
cuts that corner off and manufactures the edge normal `(1,2) ∉ N1` between `(1,0)` and
`(3,-1)`.

`E_cut_nontrivial_faces_insufficient` kills the cheaper hypothesis.  There all four constraints
of `N2` are tight on at least two lattice points of the set — `(7,0),(6,3)` for `(3,1)`,
`(5,5),(0,10)` for `(1,1)`, `(0,0),(7,0)` for `(0,-1)`, `(0,0),(0,10)` for `(-1,0)` — so
`↑N2 ⊆ E hullT`, and yet `⟪(2,1), ·⟫` maxes at `15` on exactly `{(5,5),(6,3)}`, putting
`(2,1)` in `E hullT \ ↑N2`.  The bad corner is `{z.1+z.2 = 10} ∩ {3 z.1 + z.2 = 21}` at
`(11/2, 9/2)`.  So the missing hypothesis has to be about corners being lattice points, not
about faces being long. -/

/-! ### Witness 1: a cut whose corner is not a lattice point -/

private def cutT : Set (ℤ × ℤ) :=
  (((Set.univ ∩ Nivat.LE2.halfPlaneGE (-1, 0) (-3)) ∩ Nivat.LE2.halfPlaneGE (1, 0) (-3)) ∩
    Nivat.LE2.halfPlaneGE (-1, -3) (-1)) ∩ Nivat.LE2.halfPlaneGE (1, 3) 0

private theorem mem_cutT {z : ℤ × ℤ} :
    z ∈ cutT ↔ (z.1 ≤ 3 ∧ -3 ≤ z.1 ∧ z.1 + 3 * z.2 ≤ 1 ∧ 0 ≤ z.1 + 3 * z.2) := by
  simp only [cutT, Nivat.LE2.halfPlaneGE, Set.mem_inter_iff, Set.mem_univ, true_and, dot,
    Set.mem_ofPred_eq]
  omega

private theorem latticeConvex_cutT : IsLatticeConvexRegion cutT :=
  Nivat.LE2.isLatticeConvexRegion_inter_halfPlaneGE
    (Nivat.LE2.isLatticeConvexRegion_inter_halfPlaneGE
      (Nivat.LE2.isLatticeConvexRegion_inter_halfPlaneGE
        (Nivat.LE2.isLatticeConvexRegion_inter_halfPlaneGE
          Nivat.Colle41.isLatticeConvexRegion_univ _ _) _ _) _ _) _ _

private def N1 : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (1, 3), (-1, -3)}

private def d1 : ℤ × ℤ → ℤ :=
  fun n => if n = ((1 : ℤ), (3 : ℤ)) then 1 else if n = ((-1 : ℤ), (-3 : ℤ)) then 0 else 3

theorem E_cut_needs_lattice_corner :
    cutT = {z | ∀ n ∈ N1, dot n z ≤ d1 n} ∧
    (∀ n ∈ N1, Prim n) ∧
    cutT.Finite ∧ PosArea cutT ∧ IsLatticeConvexRegion cutT ∧
    ((1, 2) : ℤ × ℤ) ∈ E cutT ∧ ((1, 2) : ℤ × ℤ) ∉ N1 := by
  refine ⟨?_, ?_, ?_, ?_, latticeConvex_cutT, ?_, by decide⟩
  · ext z
    rw [mem_cutT]
    simp only [N1, d1, Finset.mem_insert, Finset.mem_singleton, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩ n hn
      rcases hn with rfl | rfl | rfl | rfl <;> simp only [dot] <;> norm_num <;> omega
    · intro h
      have a1 := h (1, 0) (by tauto)
      have a2 := h (-1, 0) (by tauto)
      have a3 := h (1, 3) (by tauto)
      have a4 := h (-1, -3) (by tauto)
      simp only [dot, d1] at a1 a2 a3 a4
      norm_num at a1 a2 a3 a4
      omega
  · decide
  · apply Set.Finite.subset (Set.finite_Icc ((-3 : ℤ), (-1 : ℤ)) ((3 : ℤ), (1 : ℤ)))
    intro z hz
    rw [mem_cutT] at hz
    simp only [Set.mem_Icc, Prod.le_def]
    omega
  · exact ⟨(0, 0), by rw [mem_cutT]; decide, (1, 0), by rw [mem_cutT]; decide,
      (-2, 1), by rw [mem_cutT]; decide, by decide⟩
  · refine ⟨by decide, ⟨(1, 0), ⟨by rw [mem_cutT]; decide, ?_⟩, (3, -1),
      ⟨by rw [mem_cutT]; decide, ?_⟩, by decide⟩⟩
    · intro y hy
      rw [mem_cutT] at hy
      simp only [dot]
      omega
    · intro y hy
      rw [mem_cutT] at hy
      simp only [dot]
      omega

/-! ### Witness 2: long faces on every constraint do not help -/

private def hullT : Set (ℤ × ℤ) :=
  (((Set.univ ∩ Nivat.LE2.halfPlaneGE (1, 0) 0) ∩ Nivat.LE2.halfPlaneGE (0, 1) 0) ∩
    Nivat.LE2.halfPlaneGE (-1, -1) (-10)) ∩ Nivat.LE2.halfPlaneGE (-3, -1) (-21)

private theorem mem_hullT {z : ℤ × ℤ} :
    z ∈ hullT ↔ (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 10 ∧ 3 * z.1 + z.2 ≤ 21) := by
  simp only [hullT, Nivat.LE2.halfPlaneGE, Set.mem_inter_iff, Set.mem_univ, true_and, dot,
    Set.mem_ofPred_eq]
  omega

private theorem latticeConvex_hullT : IsLatticeConvexRegion hullT :=
  Nivat.LE2.isLatticeConvexRegion_inter_halfPlaneGE
    (Nivat.LE2.isLatticeConvexRegion_inter_halfPlaneGE
      (Nivat.LE2.isLatticeConvexRegion_inter_halfPlaneGE
        (Nivat.LE2.isLatticeConvexRegion_inter_halfPlaneGE
          Nivat.Colle41.isLatticeConvexRegion_univ _ _) _ _) _ _) _ _

private def N2 : Finset (ℤ × ℤ) := {(-1, 0), (0, -1), (1, 1), (3, 1)}

private def d2 : ℤ × ℤ → ℤ :=
  fun n => if n = ((1 : ℤ), (1 : ℤ)) then 10 else if n = ((3 : ℤ), (1 : ℤ)) then 21 else 0

theorem E_cut_nontrivial_faces_insufficient :
    hullT = {z | ∀ n ∈ N2, dot n z ≤ d2 n} ∧
    (∀ n ∈ N2, Prim n) ∧
    hullT.Finite ∧ PosArea hullT ∧ IsLatticeConvexRegion hullT ∧
    (∀ n ∈ N2, n ∈ E hullT) ∧
    ((2, 1) : ℤ × ℤ) ∈ E hullT ∧ ((2, 1) : ℤ × ℤ) ∉ N2 := by
  refine ⟨?_, ?_, ?_, ?_, latticeConvex_hullT, ?_, ?_, by decide⟩
  · ext z
    rw [mem_hullT]
    simp only [N2, d2, Finset.mem_insert, Finset.mem_singleton, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩ n hn
      rcases hn with rfl | rfl | rfl | rfl <;> simp only [dot] <;> norm_num <;> omega
    · intro h
      have a1 := h (-1, 0) (by tauto)
      have a2 := h (0, -1) (by tauto)
      have a3 := h (1, 1) (by tauto)
      have a4 := h (3, 1) (by tauto)
      simp only [dot, d2] at a1 a2 a3 a4
      norm_num at a1 a2 a3 a4
      omega
  · decide
  · apply Set.Finite.subset (Set.finite_Icc ((0 : ℤ), (0 : ℤ)) ((10 : ℤ), (10 : ℤ)))
    intro z hz
    rw [mem_hullT] at hz
    simp only [Set.mem_Icc, Prod.le_def]
    omega
  · exact ⟨(0, 0), by rw [mem_hullT]; decide, (1, 0), by rw [mem_hullT]; decide,
      (0, 1), by rw [mem_hullT]; decide, by decide⟩
  · intro n hn
    simp only [N2, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · refine ⟨by decide, ⟨(0, 0), ⟨by rw [mem_hullT]; decide, ?_⟩, (0, 10),
        ⟨by rw [mem_hullT]; decide, ?_⟩, by decide⟩⟩ <;>
      · intro y hy; rw [mem_hullT] at hy; simp only [dot]; omega
    · refine ⟨by decide, ⟨(0, 0), ⟨by rw [mem_hullT]; decide, ?_⟩, (7, 0),
        ⟨by rw [mem_hullT]; decide, ?_⟩, by decide⟩⟩ <;>
      · intro y hy; rw [mem_hullT] at hy; simp only [dot]; omega
    · refine ⟨by decide, ⟨(0, 10), ⟨by rw [mem_hullT]; decide, ?_⟩, (5, 5),
        ⟨by rw [mem_hullT]; decide, ?_⟩, by decide⟩⟩ <;>
      · intro y hy; rw [mem_hullT] at hy; simp only [dot]; omega
    · refine ⟨by decide, ⟨(7, 0), ⟨by rw [mem_hullT]; decide, ?_⟩, (6, 3),
        ⟨by rw [mem_hullT]; decide, ?_⟩, by decide⟩⟩ <;>
      · intro y hy; rw [mem_hullT] at hy; simp only [dot]; omega
  · refine ⟨by decide, ⟨(5, 5), ⟨by rw [mem_hullT]; decide, ?_⟩, (6, 3),
      ⟨by rw [mem_hullT]; decide, ?_⟩, by decide⟩⟩ <;>
    · intro y hy; rw [mem_hullT] at hy; simp only [dot]; omega

/-! ## §14.  Which `ε` the bottom cut may use

Added 2026-09-23 (lane-chaindata-lead).  §13 says the H-representation of the shell only has
`E ⊆ ↑N` when its corners are lattice points.  This section settles which `ε` achieve that, and
the answer is clean: `ε` must be a common multiple of the two sweep determinants, and every
positive common multiple works.  No Chinese-remainder obstruction arises, for the reason spelled
out below — which is what `delivery/scratch/b3_colle2.txt:518-520`'s "for an appropriate `ε`"
is pointing at, with `:442`/`:458`'s `d_ε` indexing the admissible choices.

**The two corners.**  The bottom face of the shell sits on `dot nJ · = cJ - ε`, and its two
endpoints are where that line meets the two boundary rays:

* the `vJ1`-ray, which runs along `dot nprevJ · = dot nprevJ g_J` (`hsupp_prev_U`,
  `LeafAAssemble.lean`) — `vJ1 ⟂ nprevJ`, so this constraint survives the `vJ1` sweep — based at
  the `J`/`nprevJ` corner `g_J` of `Â_∞`;
* the `wJ`-ray, which runs along `dot νJ1 · = suppVal (Â_i) νJ1` — `wJ = -dir νJ1`, so
  `dot νJ1 wJ = 0` and this constraint survives the `wJ` sweep — based at the `J`/`νJ1` corner
  of `Â_i`.

**Why the moduli are compatible.**  Both base points lie at `nJ`-level exactly `cJ`: `g_J` by
the definition `cJ = dot nJ g_J`, and the `J`/`νJ1` corner because it is the far endpoint of
`Â_i`'s own `J`-face, which `hhp` puts at level `cJ`.  So both congruences read
`dot nJ v ∣ (cJ - ε - cJ) = -ε`, i.e. `dot nJ vJ1 ∣ ε` and `dot nJ wJ ∣ ε` — the `cJ` cancels on
both sides and no residue survives to be incompatible.  `dvd_of_ray_hits_level` is the necessity
half, `exists_step_to_level` the sufficiency half, and `exists_eps_corner_lattice` picks an `ε`
above any prescribed bound (which is the shape `shellEnv`'s `∃ ε i₀` wants).

**Numeric instance** (硬规矩 6, worked before the Lean).  `nJ = (0,1)`, `cJ = 0`,
`vJ1 = (-1,-2)`, `wJ = (1,-3)`, `g_J = (0,0)`, `Â_i`'s `J`-face running to `(5,0)`.  Then
`dot nJ vJ1 = -2` and `dot nJ wJ = -3`.  At `ε = 6`: the `vJ1`-corner is `(0,0) + 3•(-1,-2) =
(-3,-6)` and the `wJ`-corner is `(5,0) + 2•(1,-3) = (7,-6)`, both lattice, and the bottom face
runs from `(-3,-6)` to `(7,-6)` — eleven lattice points, comfortably longer than any face of
`𝒮_φ`.  At `ε = 1` the `vJ1`-corner would be `(0,-1/2)`: not a lattice point, and §13's
corner-cut manufactures a spurious edge normal.  `eps_one_fails` is that instance in the kernel.

**Consequence for `bottom : ∀ ε`.**  Only common multiples of `dot nJ vJ1` and `dot nJ wJ`
admit a lattice-cornered shell, so the shell is `E ↑𝒮_φ`-enveloped for those `ε` and generally
not for others.  This is independent evidence for the `∀ ε` debt recorded in `OPEN.md` #7–#9;
per team-lead's Round 100 ruling the signature stays untouched until `shellEnv` closes and the
affected `ChainGeom`/`ChainShell`/`ShellGeom` call sites can be listed concretely. -/

private theorem dot_add_zsmul (n g v : ℤ × ℤ) (k : ℤ) :
    dot n (g + k • v) = dot n g + k * dot n v := by
  rw [dot_add, Nivat.ColleReg.dot_zsmul_right]

theorem dvd_of_ray_hits_level {n g v : ℤ × ℤ} {c ε k : ℤ}
    (hg : dot n g = c) (h : dot n (g + k • v) = c - ε) : dot n v ∣ ε := by
  rw [dot_add_zsmul, hg] at h
  exact ⟨-k, by linear_combination h⟩

theorem exists_step_to_level {n g v : ℤ × ℤ} {c ε : ℤ}
    (hv : dot n v < 0) (hg : dot n g = c) (hε : 0 ≤ ε) (hdvd : dot n v ∣ ε) :
    ∃ t : ℕ, dot n (g + (t : ℤ) • v) = c - ε := by
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : 0 ≤ -k := by nlinarith
  refine ⟨(-k).toNat, ?_⟩
  rw [dot_add_zsmul, hg, Int.toNat_of_nonneg hk0]
  linear_combination hk

/-- **Admissible `ε` for the bottom cut.** -/
theorem exists_eps_corner_lattice {n v w : ℤ × ℤ} (hv : dot n v < 0) (hw : dot n w < 0)
    (N : ℕ) :
    ∃ ε : ℕ, N < ε ∧ ∀ (g : ℤ × ℤ) (c : ℤ), dot n g = c →
      (∃ t : ℕ, dot n (g + (t : ℤ) • v) = c - (ε : ℤ)) ∧
      (∃ s : ℕ, dot n (g + (s : ℤ) • w) = c - (ε : ℤ)) := by
  refine ⟨(N + 1) * ((-dot n v) * (-dot n w)).toNat, ?_, ?_⟩
  · have h1 : 1 ≤ (-dot n v) := by omega
    have h2 : 1 ≤ (-dot n w) := by omega
    have : (1 : ℤ) ≤ (-dot n v) * (-dot n w) := by nlinarith
    have := Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ (-dot n v) * (-dot n w))
    have hge : 1 ≤ ((-dot n v) * (-dot n w)).toNat := by omega
    calc N < (N + 1) * 1 := by omega
      _ ≤ (N + 1) * ((-dot n v) * (-dot n w)).toNat := by
          exact Nat.mul_le_mul_left _ hge
  · intro g c hg
    have hcast : (((N + 1) * ((-dot n v) * (-dot n w)).toNat : ℕ) : ℤ)
        = (N + 1 : ℤ) * ((-dot n v) * (-dot n w)) := by
      push_cast
      rw [Int.toNat_of_nonneg (by nlinarith : (0:ℤ) ≤ (-dot n v) * (-dot n w))]
    constructor
    · refine exists_step_to_level hv hg ?_ ?_
      · rw [hcast]; nlinarith
      · exact ⟨-((N + 1 : ℤ) * (-dot n w)), by rw [hcast]; ring⟩
    · refine exists_step_to_level hw hg ?_ ?_
      · rw [hcast]; nlinarith
      · exact ⟨-((N + 1 : ℤ) * (-dot n v)), by rw [hcast]; ring⟩

/-- The divisibility is not slack. -/
theorem eps_one_fails :
    dot ((0, 1) : ℤ × ℤ) ((-1, -2) : ℤ × ℤ) < 0 ∧
    dot ((0, 1) : ℤ × ℤ) ((0, 0) : ℤ × ℤ) = 0 ∧
    ¬ (∃ k : ℤ, dot ((0, 1) : ℤ × ℤ) (((0, 0) : ℤ × ℤ) + k • ((-1, -2) : ℤ × ℤ)) = 0 - 1) ∧
    (∃ t : ℕ, dot ((0, 1) : ℤ × ℤ) (((0, 0) : ℤ × ℤ) + (t : ℤ) • ((-1, -2) : ℤ × ℤ))
      = 0 - 6) := by
  refine ⟨by decide, by decide, ?_, ⟨3, by decide⟩⟩
  rintro ⟨k, hk⟩
  rw [dot_add_zsmul] at hk
  simp only [dot] at hk
  omega

/-! ## §15.  How long the bottom face is

Added 2026-09-23 (lane-chaindata-lead).  §14 fixes the two endpoints of the shell's bottom
face; this section measures the distance between them, which is the first of the three
face-length lower bounds `Enveloped ↑𝒮_φ` needs (`delivery/scratch/b3_colle2.txt:402`,
Definition 3.2's `#(w ∩ 𝒮_φ) ≤ #(w ∩ 𝒯)` clause; the shell itself is `:518-520`).

Both endpoints sit at `nJ`-level `cJ - ε`, so they differ by a multiple of the `J`-face
direction `eJ` (`exists_bottom_span`; `eJ` is primitive with `dot nJ eJ = 0`).  Pairing that
multiple against `nprevJ` — which kills `vJ1` (`hnpvJ1`) and so erases the `vJ1`-ray's
contribution entirely — turns the span into one linear identity (`bottom_span_eq`):

    k ⟪nprevJ, eJ⟫ = L ⟪nprevJ, eJ⟫ + t_B ⟪nprevJ, wJ⟫ ,

where `L` is the length of `Â_i`'s own `J`-face and `t_B = ε / |⟪nJ, wJ⟫|` is the number of
`wJ`-steps down to the cut.  Both `⟪nprevJ, eJ⟫` (`hnpeJ`) and `⟪nprevJ, wJ⟫` are negative — the
`wJ`-ray leans away from the `nprevJ` side, `wJ` being built from the fan *successor* `νJ1`
while `nprevJ` is the predecessor — so `k - L` is a positive multiple of `t_B / |⟪nprevJ, eJ⟫|`
and `bottom_span_ge` reads off `L + M ≤ k` as soon as `t_B ≥ M |⟪nprevJ, eJ⟫|`.  Since
`exists_eps_corner_lattice` hands out admissible `ε` above any prescribed bound, `M` may be
taken to be `(face ↑𝒮_φ J).encard`, which is what the face-length clause asks for.

**Numeric instance** (硬规矩 6): continuing §14's data — `nJ = (0,1)`, `eJ = (1,0)`,
`vJ1 = (-1,-2)`, `wJ = (1,-3)`, `g_J = (0,0)`, `L = 5`, `ε = 6`, so `t_A = 3` and `t_B = 2` —
`nprevJ` is pinned by `⟪nprevJ, vJ1⟫ = 0` and `⟪nprevJ, eJ⟫ < 0` to `(-2,1)`.  The two endpoints
are `(0,0) + 5•(1,0) + 2•(1,-3) = (7,-6)` and `(0,0) + 3•(-1,-2) = (-3,-6)`, so `k = 10`, and
the identity checks: `10·(-2) = 5·(-2) + 2·(-5) = -20`.  `bottom_span_instance` is that
computation in the kernel.  Note `k = 10 > 5 = L`: the bottom face is strictly longer than
`Â_i`'s own `J`-face, which is what makes the face-length clause cheap here and expensive for
the edges inherited from `Â_i`. -/

theorem exists_bottom_span {n u a b : ℤ × ℤ}
    (hn_ne : n ≠ 0) (hu : Prim u) (hnu : dot n u = 0) (hlev : dot n a = dot n b) :
    ∃ k : ℤ, b = a + k • u := by
  have hx : dot n (b - a) = 0 := by rw [dot_sub, hlev]; ring
  have hdet : det u (b - a) = 0 := det_eq_zero_of_dot_eq_zero hn_ne hnu hx
  obtain ⟨k, hk⟩ := exists_smul_of_det_eq_zero hu hdet
  refine ⟨k, ?_⟩
  have hba : b - a = k • u := by rw [hk]; ext <;> simp
  rw [← hba]; abel

theorem bottom_span_eq {np e v w g : ℤ × ℤ} {L tA tB k : ℤ}
    (hnpv : dot np v = 0)
    (hk : g + L • e + tB • w = g + tA • v + k • e) :
    k * dot np e = L * dot np e + tB * dot np w := by
  have h := congrArg (dot np) hk
  simp only [dot_add, Nivat.ColleReg.dot_zsmul_right, hnpv, mul_zero, add_zero] at h
  linarith

theorem bottom_span_ge {np e w : ℤ × ℤ} {L tB k M : ℤ}
    (hnpe : dot np e < 0) (hnpw : dot np w < 0) (hM : 0 ≤ M)
    (htB : M * (-dot np e) ≤ tB)
    (heq : k * dot np e = L * dot np e + tB * dot np w) :
    L + M ≤ k := by
  have hD1 : (1 : ℤ) ≤ -dot np e := by omega
  have hD1' : (1 : ℤ) ≤ -dot np w := by omega
  have htB0 : (0 : ℤ) ≤ tB := le_trans (mul_nonneg hM (by omega)) htB
  have hkey : (k - L) * (-dot np e) = tB * (-dot np w) := by linear_combination -heq
  have hMle : M * (-dot np e) ≤ (k - L) * (-dot np e) :=
    calc M * (-dot np e) ≤ tB := htB
      _ ≤ tB * (-dot np w) := le_mul_of_one_le_right htB0 hD1'
      _ = (k - L) * (-dot np e) := hkey.symm
  have := le_of_mul_le_mul_right hMle (by omega : (0 : ℤ) < -dot np e)
  omega

theorem bottom_span_instance :
    ((0, 0) : ℤ × ℤ) + (5 : ℤ) • ((1, 0) : ℤ × ℤ) + (2 : ℤ) • ((1, -3) : ℤ × ℤ)
      = ((0, 0) : ℤ × ℤ) + (3 : ℤ) • ((-1, -2) : ℤ × ℤ) + (10 : ℤ) • ((1, 0) : ℤ × ℤ) ∧
    dot ((-2, 1) : ℤ × ℤ) ((-1, -2) : ℤ × ℤ) = 0 ∧
    dot ((-2, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) < 0 ∧
    dot ((-2, 1) : ℤ × ℤ) ((1, -3) : ℤ × ℤ) < 0 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  ext <;> simp

/-! ## §16.  The faces a sweep keeps, it lengthens

Added 2026-09-23 (lane-chaindata-lead).  The second of the three face-length blocks: the edges
the shell inherits from `Â_i` rather than manufacturing at the cut.

Sweeping along `u` can only *extend* the face at a normal `n` it does not delete.  Precisely:
if `A ⊆ Y` and `⟪n, u⟫ ≤ 0`, then every point of `reachSet A u ∩ Y` pairs against `n` at most as
high as `A`'s own maximum (each `u`-step is non-increasing), while `face A n` itself survives
into the intersection at `t = 0`.  So `face A n ⊆ face (reachSet A u ∩ Y) n`, and the
`Enveloped` clause at `n` transfers for free from `Â_i` (`henvAhat`) to the shell.  No
finiteness, convexity or primitivity is needed — this is the cheap half, and it is cheap
precisely because the sweep direction is the one the constraint survives.

At the call site `A := hatOf A kk vl i`, `u := wJ`, and
`Y := reachSet (⋃ i, hatOf A kk vl i) vJ1 ∩ halfPlaneGE nJ (cJ - ε)`; the hypothesis `A ⊆ Y`
is `Â_i ⊆ Â_∞ ⊆ reachSet Â_∞ vJ1` together with `hhp`'s `Â_i ⊆ halfPlaneGE nJ cJ ⊆
halfPlaneGE nJ (cJ - ε)`.  This settles every `n ∈ E ↑𝒮_φ` with `⟪n, wJ⟫ ≤ 0`.

**What is still owed.**  By §10 (`sweeps_nonpos_of_ne_J`) every `n ≠ J` satisfies
`⟪n, vJ1⟫ ≤ 0` or `⟪n, wJ⟫ ≤ 0`, so the remaining normals are those with `⟪n, wJ⟫ > 0` and
`⟪n, vJ1⟫ ≤ 0`.

⛔ **订正（第 201 轮，lane-leafa-shell 查，集成者复核）：下面这段原来的诊断是错的，别照它派工。**
原文写的是「那一类的约束来自 `v_{J-1}` 扫掠，而那是 `Â_∞` 的扫掠不是 `Â_i` 的，所以本引理取
`A := Â_∞` 即可，只差 `Â_∞` 自己的弱 `E(↑𝒮_φ)`-包络性」。**取 `A := Â_∞` 接不上。**
把 `shellT` 改写成 `reachSet Â_∞ v_{J-1} ∩ Y'`（`Y' := reachSet Â_i w ∩ halfPlaneGE nJ (cJ-ε)`）
之后，本引理的 `hAY` 要的是 **`Â_∞ ⊆ reachSet Â_i w`** —— 那是假的（`Â_∞` 比单个 `Â_i` 的
`w`-可达锥大）。形状论证（不依赖台架）：本引理的结论会给出 `face Â_∞ n ⊆ face shellT n`，而
`face Â_∞ n` 无界、`face shellT n` 有限 ⟹ 结论为假 ⟹ 前提 `hAY` 必假。
⟹ **承重的是 `hAY`，不是「还缺弱包络性」。** 连带：
`WeaklyEnveloped ↑𝒮_φ (⋃ hatOf …)` 形状的引理即使进主仓，本段的正类也接不上；
全主仓 `grep WeaklyEnveloped` 无任何声明把该形状当 binder 收。这一段该整段改写，不是补一条输入。

`Â_∞` 的弱 `E(𝒮_φ)`-包络性本身仍是原文事实（`delivery/scratch/b3_colle2.txt:506`，⚠ 原记的
`:505` 是空行），只是**它不是这里缺的那件**。那件加上 `J` 自身（§15）、
加上 lane-hroom-close 的 `E`-of-a-cut containment，才是 `shellEnv` 剩下的全部。 -/

theorem face_subset_face_reachSet_inter {A Y : Set (ℤ × ℤ)} {u n : ℤ × ℤ}
    (hAY : A ⊆ Y) (hnu : dot n u ≤ 0) :
    face A n ⊆ face (reachSet A u ∩ Y) n := by
  rintro z ⟨hzA, hzmax⟩
  refine ⟨⟨⟨z, hzA, 0, by simp⟩, hAY hzA⟩, ?_⟩
  rintro y ⟨⟨g, hg, t, rfl⟩, -⟩
  have hstep : dot n (g + (t : ℤ) • u) = dot n g + (t : ℤ) * dot n u := by
    rw [dot_add, Nivat.ColleReg.dot_zsmul_right]
  rw [hstep]
  have h1 := hzmax g hg
  have h2 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  nlinarith

theorem mem_E_reachSet_inter {A Y : Set (ℤ × ℤ)} {u n : ℤ × ℤ}
    (hAY : A ⊆ Y) (hnu : dot n u ≤ 0) (hn : n ∈ E A) :
    n ∈ E (reachSet A u ∩ Y) :=
  ⟨hn.1, hn.2.mono (face_subset_face_reachSet_inter hAY hnu)⟩

theorem encard_face_le_reachSet_inter {S A Y : Set (ℤ × ℤ)} {u n : ℤ × ℤ}
    (hAY : A ⊆ Y) (hnu : dot n u ≤ 0)
    (henv : (face S n).encard ≤ (face A n).encard) :
    (face S n).encard ≤ (face (reachSet A u ∩ Y) n).encard :=
  le_trans henv (Set.encard_mono (face_subset_face_reachSet_inter hAY hnu))

/-! ## §17.  The `latHull` sandwich — the repair of the refuted cut lemma

Added 2026-09-23 (lane-chaindata-lead).

**What this replaces.**  §13's two witnesses showed that

    E (A ∩ halfPlaneGE m c) ⊆ ↑N ∪ {-m}

cannot be had from an H-representation `A = {z | ∀ n ∈ N, ⟪n,z⟫ ≤ d n}` plus any hypothesis
about the *cut's* two corners.  lane-hroom-close then refuted the whole signature by a third
witness (same `N`, `d` as `E_cut_needs_lattice_corner`, and `m := (0,-1)`, `c := -10`, a cut so
loose it misses `A` entirely): every corner hypothesis about the `m`-edge holds vacuously while
`(1,2) ∈ E A \ (↑N ∪ {-m})` survives untouched, because that phantom edge is created by the
non-lattice corner `(3, -2/3)` of `A`'s **own** H-representation, nowhere near the cut.  The
lemma is dead in that shape and is not attempted again here.

**Why the sandwich is the right shape instead.**  The phantom-edge phenomenon is exactly the
failure of `conv(A) = conv(lattice points of A)`.  Rather than hypothesise it away constraint
by constraint, state it once, positively: exhibit a finite `X ⊆ T` whose lattice hull already
covers `T`.  Then `latHull T = latHull X` (`latHull_eq_of_sandwich`), and `E_latHull`
(`EnvelopedConvex.lean:260`) transports the edge set across in both directions at once —
`E T = E X`, with no primitivity, no H-representation, no convexity of `X`, and no corner
bookkeeping.  `enveloped_of_sandwich` then reads off `Enveloped U T` from envelope data stated
about `X` alone.

**Why the shell can feed it.**  `Â_i^{(ε)}`'s real hull is `conv(Â_i)` together with the two
points where the sweep rays cross the cut line `⟪n_J, ·⟫ = c_J - ε`, and §14's
`exists_eps_corner_lattice` is precisely the statement that `ε` may be chosen — arbitrarily
large — so that **both of those crossings are lattice points**.  That is the hypothesis
`hcover` of `enveloped_of_two_corners` with `X := Â_i ∪ {p, q}`: not a fact about corners of an
abstract H-representation, but a two-point covering statement that §14 makes constructible.
The residual obligations then become statements about `X`, whose edge set §10 pins:
`sweeps_nonpos_of_ne_J` says every `n ∈ E ↑𝒮_φ` other than `J` is kept by one of the two
sweeps, and `n_J = -J`, so the cut restores `J` itself as the bottom edge — which is what makes
the *count* `(E X).encard = (E ↑𝒮_φ).encard` come out right (`b3_colle2.txt:518-520`).

**Non-vacuity.**  `enveloped_sq1_sq2_via_sandwich` runs the whole toolkit on a generating set
that is *not* lattice-convex (`punct`, the `[0,2]²` square with its centre removed —
`EnvelopedConvex.not_isLatticeConvexRegion_punct`), recovering `Enveloped sq1 sq2`.  So
`enveloped_of_sandwich`'s `X` genuinely need not be convex; that is the whole point, since
`Â_i ∪ {p, q}` is not convex either. -/

theorem latHull_mono {X T : Set (ℤ × ℤ)} (h : X ⊆ T) : latHull X ⊆ latHull T :=
  Set.preimage_mono (convexHull_mono (Set.image_mono h))

/-- A finite `X` sandwiched as `X ⊆ T ⊆ latHull X` has the same lattice hull as `T`. -/
theorem latHull_eq_of_sandwich {X T : Set (ℤ × ℤ)} (hX : X.Finite)
    (h1 : X ⊆ T) (h2 : T ⊆ latHull X) : latHull T = latHull X :=
  Set.Subset.antisymm
    (latHull_subset_of_isLatticeConvexRegion (isLatticeConvexRegion_latHull hX) h2)
    (latHull_mono h1)

/-- **The sandwich transports the edge set.**  No primitivity, no H-representation, no
convexity of `X`. -/
theorem E_eq_of_sandwich {X T : Set (ℤ × ℤ)} (hX : X.Finite) (hT : T.Finite)
    (h1 : X ⊆ T) (h2 : T ⊆ latHull X) : E T = E X := by
  rw [← E_latHull hT, ← E_latHull hX, latHull_eq_of_sandwich hX h1 h2]

/-- Faces can only grow along the sandwich: `T ⊆ latHull X` makes an `X`-maximiser a
`T`-maximiser. -/
theorem face_subset_of_sandwich {X T : Set (ℤ × ℤ)} (h1 : X ⊆ T) (h2 : T ⊆ latHull X)
    (n : ℤ × ℤ) : face X n ⊆ face T n := by
  rintro z ⟨hzX, hzmax⟩
  exact ⟨h1 hzX, fun y hy => dot_le_of_mem_latHull hzmax (h2 hy)⟩

/-- **`Enveloped U T` from envelope data about a generating set `X`.**  The three envelope
hypotheses are stated about `X`, which may be finite, non-convex and much smaller than `T`;
`T` only has to be finite, lattice-convex, and sandwiched. -/
theorem enveloped_of_sandwich {U X T : Set (ℤ × ℤ)} (hX : X.Finite) (hT : T.Finite)
    (hlcT : IsLatticeConvexRegion T) (h1 : X ⊆ T) (h2 : T ⊆ latHull X)
    (hEU : ∀ n ∈ E X, n ∈ E U)
    (hface : ∀ n ∈ E X, (face U n).encard ≤ (face X n).encard)
    (hcard : (E X).encard = (E U).encard) :
    Enveloped U T := by
  have hE : E T = E X := E_eq_of_sandwich hX hT h1 h2
  refine ⟨⟨hlcT, fun n hn => ?_⟩, ?_⟩
  · rw [hE] at hn
    exact ⟨hEU n hn, (hface n hn).trans (Set.encard_mono (face_subset_of_sandwich h1 h2 n))⟩
  · rw [hE]; exact hcard

/-- **The shell's shape of the sandwich**: `X := A ∪ {p, q}` with `p`, `q` the two lattice
crossings §14 buys.  `A ⊆ T`, `p, q ∈ T` are free at the call site (`subset_shellInter`, and
`p`, `q` lie on the cut line hence in the half-plane); the content is `hcover`. -/
theorem enveloped_of_two_corners {U A T : Set (ℤ × ℤ)} {p q : ℤ × ℤ}
    (hAfin : A.Finite) (hT : T.Finite) (hlcT : IsLatticeConvexRegion T)
    (hA : A ⊆ T) (hp : p ∈ T) (hq : q ∈ T)
    (hcover : T ⊆ latHull (A ∪ {p, q}))
    (hEU : ∀ n ∈ E (A ∪ {p, q}), n ∈ E U)
    (hface : ∀ n ∈ E (A ∪ {p, q}), (face U n).encard ≤ (face (A ∪ {p, q}) n).encard)
    (hcard : (E (A ∪ {p, q})).encard = (E U).encard) :
    Enveloped U T := by
  refine enveloped_of_sandwich (hAfin.union ((Set.finite_singleton q).insert p))
    hT hlcT ?_ hcover hEU hface hcard
  rintro z (hz | hz)
  · exact hA hz
  · rcases hz with rfl | hz
    · exact hp
    · rw [Set.mem_singleton_iff] at hz; subst hz; exact hq

/-! ### Non-vacuity: a non-lattice-convex generating set -/

theorem mem_00_punct : ((0 : ℤ), (0 : ℤ)) ∈ punct := by
  refine ⟨?_, ?_⟩
  · simp [sq2, box]
  · decide

theorem mem_22_punct : ((2 : ℤ), (2 : ℤ)) ∈ punct := by
  refine ⟨?_, ?_⟩
  · simp [sq2, box]
  · decide

/-- The punched-out centre is back in the lattice hull: it is the midpoint of two corners. -/
theorem sq2_subset_latHull_punct : sq2 ⊆ latHull punct := by
  intro z hz
  by_cases h : z = ((1 : ℤ), (1 : ℤ))
  · subst h
    have hmid := (convex_convexHull ℝ (toReal '' punct))
      (subset_convexHull ℝ _ ⟨_, mem_00_punct, rfl⟩)
      (subset_convexHull ℝ _ ⟨_, mem_22_punct, rfl⟩)
      (a := (1 : ℝ) / 2) (b := (1 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num)
    have heq : ((1 : ℝ) / 2) • toReal ((0 : ℤ), (0 : ℤ)) +
        ((1 : ℝ) / 2) • toReal ((2 : ℤ), (2 : ℤ)) = toReal ((1 : ℤ), (1 : ℤ)) := by
      simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
      norm_num
    rw [heq] at hmid
    exact hmid
  · exact subset_latHull punct ⟨hz, h⟩

/-- **The round trip.**  `Enveloped sq1 sq2` recovered through `enveloped_of_sandwich` from the
**non**-lattice-convex generating set `punct`: the toolkit does not secretly need `X` convex. -/
theorem enveloped_sq1_sq2_via_sandwich : Enveloped sq1 sq2 := by
  have hfp : ∀ n ∈ E punct, face punct n = face sq2 n := by
    intro n hn
    exact face_punct_eq n (mem_E_iff.mp hn).1.ne_zero
  refine enveloped_of_sandwich finite_punct finite_sq2 enveloped_sq.1.1 punct_subset
    sq2_subset_latHull_punct (fun n hn => ?_) (fun n hn => ?_) ?_
  · exact (enveloped_sq.1.2 n (E_punct_eq ▸ hn)).1
  · rw [hfp n hn]
    exact (enveloped_sq.1.2 n (E_punct_eq ▸ hn)).2
  · rw [E_punct_eq]; exact enveloped_sq.2

/-! ## §18.  `hcover` for a truncated one-directional sweep

Added 2026-09-23 (lane-chaindata-lead).  §17 reduces `shellEnv` to exhibiting a finite
`X ⊆ T` with `T ⊆ latHull X`; this section proves that covering statement for the shape the
shell has, with `X := A ∪ {p, q}`.

**The statement.**  Sweep a finite `A` along `u`, cut at `⟪m, ·⟫ ≥ c` with `⟪m,u⟫ < 0` (so the
sweep really does leave the half-plane), and let `n₀` be a normal perpendicular to `u`, so that
`⟪n₀, ·⟫` is constant along the sweep and the two sides of `reachSet A u` are the lines
`⟪n₀, ·⟫ = suppVal A n₀` and `⟪n₀, ·⟫ = -suppVal A (-n₀)`.  Then the two lattice points `p`, `q`
where those side lines meet the cut line already generate the whole truncated sweep.

**The proof.**  For `z = g + t·u` in the truncated sweep, the ray from `g` meets the cut line at
the *real* parameter `τ = (⟪m,g⟫ - c)/(-⟪m,u⟫)`, and the half-plane condition is exactly
`t ≤ τ`.  So `z` sits on the segment from `g` to the ray/cut intersection `Y`, and `Y` — which
has `⟪n₀, Y⟫ = ⟪n₀, g⟫`, squeezed between `⟪n₀,q⟫` and `⟪n₀,p⟫` by `le_suppVal` — sits on the
segment from `q` to `p`, because on ℝ² two points agreeing on the two independent functionals
`⟪m, ·⟫` and `⟪n₀, ·⟫` are equal (`eq_of_zdot_eq`; `det m n₀ ≠ 0` is forced by `⟪m,u⟫ ≠ 0 =
⟪n₀,u⟫`).  Two convex combinations, no polytope theory.

Note that `p` and `q` are *not* required to lie in `reachSet A u`: only their two coordinates
matter.  What §14's `exists_eps_corner_lattice` supplies at the call site is that `ε` can be
chosen — arbitrarily large — so that such `p`, `q` exist as **lattice** points, which is the
whole reason `X` is a set of lattice points at all.

**Worked numeric instance (硬规矩 6), computed by hand before any Lean.**

* `A := {(0,0),(1,0),(0,1),(1,1)}`, `u := (0,-1)`, `m := (0,1)`, `c := -2`, `n₀ := (1,0)`.
* `⟪m,u⟫ = -1 < 0`;  `⟪n₀,u⟫ = 0`;  `det m n₀ = 0·0 - 1·1 = -1 ≠ 0`.  All three hypotheses hold.
* `suppVal A n₀ = 1`, `suppVal A (-n₀) = 0`, so the corners are `p = (1,-2)` (`⟪n₀,p⟫ = 1`) and
  `q = (0,-2)` (`⟪n₀,q⟫ = 0 = -suppVal A (-n₀)`), both on `⟪m,·⟫ = -2`.
* The truncated sweep is the rectangle `[0,1] × [-2,1]`, whose four corners `(0,1)`, `(1,1)`,
  `(1,-2)`, `(0,-2)` all lie in `A ∪ {p,q}` — so the covering is tight, not slack.
* `z := (1,-1) = (1,0) + 1·u`:  `D = 1`, `τ = (⟪m,(1,0)⟫ - c)/D = (0+2)/1 = 2`, `θ = t/τ = 1/2`,
  `Y = (1,0) + 2·(0,-1) = (1,-2) = p`, and indeed `toReal z = ½·(1,0) + ½·(1,-2)`.
* `z := (1,-2) = (1,0) + 2·u` is the boundary case `t = τ`, `θ = 1`, `Y = z = p`.

`cover_instance_nonvacuous` and `cover_needs_extremal_corner` are the kernel receipts for that
instance: the truncated sweep really is strictly larger than `A`, and replacing the
`n₀`-maximal corner `(1,-2)` by the non-maximal `(0,-2)` makes the conclusion false
(`⟪(1,-1), ·⟫ ≤ 2` separates).  So `hpmax` / `hqmin` are load-bearing.

**What this leaves for `shellEnv`.**  Feeding §17's `enveloped_of_two_corners` still needs
`hEU` / `hcard` / `hface` about `X = Â_i ∪ {p,q}` — §10 (`sweeps_nonpos_of_ne_J`, and
`n_J = -J` so the cut restores `J` as the bottom edge) for the edge set and count, §15/§16 for
the face lengths — plus, for the normals `n` with `⟪n,w_J⟫ > 0 ∧ ⟪n,v_{J-1}⟫ ≤ 0`, `Â_∞`'s own
weak `E(↑𝒮_φ)`-envelopedness (`b3_colle2.txt:506`; ⚠ 原记 `:505`，那是空行), which is still
not in the main tree.  ⚠ 但按 §16 的订正，正类真正承重的是那里的 `hAY`，不是这一条。 -/

/-- Two points of `ℝ²` that agree on two independent integer functionals are equal. -/
theorem eq_of_zdot_eq {m n : ℤ × ℤ} (h : det m n ≠ 0) {x y : ℝ × ℝ}
    (h1 : zdot m x = zdot m y) (h2 : zdot n x = zdot n y) : x = y := by
  have hd : ((det m n : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h
  have hdet : ((det m n : ℤ) : ℝ) = (m.1 : ℝ) * (n.2 : ℝ) - (m.2 : ℝ) * (n.1 : ℝ) := by
    simp only [det]; push_cast; ring
  rw [hdet] at hd
  simp only [zdot] at h1 h2
  have e1 : (m.1 : ℝ) * (x.1 - y.1) + (m.2 : ℝ) * (x.2 - y.2) = 0 := by linarith
  have e2 : (n.1 : ℝ) * (x.1 - y.1) + (n.2 : ℝ) * (x.2 - y.2) = 0 := by linarith
  have hx : (x.1 - y.1) * ((m.1 : ℝ) * (n.2 : ℝ) - (m.2 : ℝ) * (n.1 : ℝ)) = 0 := by
    linear_combination (n.2 : ℝ) * e1 - (m.2 : ℝ) * e2
  have hy : (x.2 - y.2) * ((m.1 : ℝ) * (n.2 : ℝ) - (m.2 : ℝ) * (n.1 : ℝ)) = 0 := by
    linear_combination (-(n.1 : ℝ)) * e1 + (m.1 : ℝ) * e2
  have hx0 : x.1 = y.1 := by
    rcases mul_eq_zero.mp hx with h' | h'
    · linarith
    · exact absurd h' hd
  have hy0 : x.2 = y.2 := by
    rcases mul_eq_zero.mp hy with h' | h'
    · linarith
    · exact absurd h' hd
  exact Prod.ext hx0 hy0

/-- **The truncated sweep is covered by `A` together with its two bottom corners.** -/
theorem sweep_cut_subset_latHull {A : Set (ℤ × ℤ)} {u m n₀ p q : ℤ × ℤ} {c : ℤ}
    (hAfin : A.Finite) (hAne : A.Nonempty)
    (hdet : det m n₀ ≠ 0) (hmu : dot m u < 0) (hn₀u : dot n₀ u = 0)
    (hpc : dot m p = c) (hpmax : dot n₀ p = suppVal A n₀)
    (hqc : dot m q = c) (hqmin : dot n₀ q = - suppVal A (-n₀)) :
    reachSet A u ∩ Nivat.LE2.halfPlaneGE m c ⊆ latHull (A ∪ {p, q}) := by
  have hmemA : ∀ y ∈ A, toReal y ∈ rHull (A ∪ {p, q}) := fun y hy =>
    subset_convexHull ℝ _ ⟨y, Or.inl hy, rfl⟩
  have hmemp : toReal p ∈ rHull (A ∪ {p, q}) :=
    subset_convexHull ℝ _ ⟨p, Or.inr (Set.mem_insert p {q}), rfl⟩
  have hmemq : toReal q ∈ rHull (A ∪ {p, q}) :=
    subset_convexHull ℝ _ ⟨q, Or.inr (Set.mem_insert_of_mem p rfl), rfl⟩
  rintro z ⟨⟨g, hg, t, rfl⟩, hz⟩
  -- the two `n₀`-bounds on `g`
  have hnp : dot n₀ g ≤ dot n₀ p := by
    rw [hpmax]; exact le_suppVal hAfin hAne hg
  have hnq : dot n₀ q ≤ dot n₀ g := by
    have := le_suppVal (n := -n₀) hAfin hAne hg
    rw [dot_neg_left] at this
    omega
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have hgz : g + ((0 : ℕ) : ℤ) • u = g := by simp
    rw [hgz]
    exact mem_latHull_iff.mpr (hmemA g hg)
  -- `D > 0`, and the half-plane bound on `t`
  set D : ℤ := - dot m u with hDdef
  have hD0 : 0 < D := by omega
  have hdotz : dot m (g + (t : ℤ) • u) = dot m g - (t : ℤ) * D := by
    rw [dot_add, Nivat.ColleReg.dot_zsmul_right, hDdef]; ring
  have hzhalf : c ≤ dot m g - (t : ℤ) * D := by
    simp only [Nivat.LE2.halfPlaneGE, Set.mem_ofPred_eq] at hz
    omega
  have hn₀z : dot n₀ (g + (t : ℤ) • u) = dot n₀ g := by
    rw [dot_add, Nivat.ColleReg.dot_zsmul_right, hn₀u]; ring
  -- the real ray parameter that lands on the cut line
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD0
  set τ : ℝ := ((dot m g - c : ℤ) : ℝ) / (D : ℝ) with hτdef
  have htτ : ((t : ℤ) : ℝ) ≤ τ := by
    rw [hτdef, le_div_iff₀ hDR]
    have : ((t : ℤ) : ℝ) * (D : ℝ) ≤ ((dot m g - c : ℤ) : ℝ) := by exact_mod_cast (by omega : (t : ℤ) * D ≤ dot m g - c)
    exact this
  have htR : (0 : ℝ) < ((t : ℤ) : ℝ) := by
    have : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht
    exact_mod_cast this
  have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le htR htτ
  set Y : ℝ × ℝ := toReal g + τ • toReal u with hYdef
  have hzdotY : ∀ n : ℤ × ℤ, zdot n Y = (dot n g : ℝ) + τ * (dot n u : ℝ) := by
    intro n
    have : Y = (1 : ℝ) • toReal g + τ • toReal u := by rw [hYdef, one_smul]
    rw [this, zdot_add_smul, zdot_toReal, zdot_toReal, one_mul]
  have hYm : zdot m Y = (c : ℝ) := by
    rw [hzdotY m, hτdef]
    have hmu' : ((dot m u : ℤ) : ℝ) = -(D : ℝ) := by rw [hDdef]; push_cast; ring
    rw [hmu']
    field_simp
    push_cast
    ring
  have hYn : zdot n₀ Y = (dot n₀ g : ℝ) := by
    rw [hzdotY n₀, hn₀u]; simp
  -- `Y` lies on the segment `[q, p]`
  have hYhull : Y ∈ rHull (A ∪ {p, q}) := by
    rcases eq_or_lt_of_le (hnq.trans hnp) with heq | hlt
    · -- degenerate: the two corners share an `n₀`-level, so `Y = toReal p`
      have hgp : dot n₀ g = dot n₀ p := by omega
      have : Y = toReal p := by
        refine eq_of_zdot_eq hdet ?_ ?_
        · rw [hYm, zdot_toReal, hpc]
        · rw [hYn, zdot_toReal, hgp]
      rw [this]; exact hmemp
    · have hden : (0 : ℝ) < ((dot n₀ p - dot n₀ q : ℤ) : ℝ) := by exact_mod_cast (by omega : (0:ℤ) < dot n₀ p - dot n₀ q)
      set σ : ℝ := ((dot n₀ g - dot n₀ q : ℤ) : ℝ) / ((dot n₀ p - dot n₀ q : ℤ) : ℝ) with hσdef
      have hσ0 : 0 ≤ σ := div_nonneg (by exact_mod_cast (by omega : (0:ℤ) ≤ dot n₀ g - dot n₀ q)) hden.le
      have hσ1 : σ ≤ 1 := by
        rw [hσdef, div_le_one hden]
        exact_mod_cast (by omega : dot n₀ g - dot n₀ q ≤ dot n₀ p - dot n₀ q)
      have hcomb : Y = (1 - σ) • toReal q + σ • toReal p := by
        refine eq_of_zdot_eq hdet ?_ ?_
        · rw [hYm, zdot_add_smul, zdot_toReal, zdot_toReal, hpc, hqc]; ring
        · rw [hYn, zdot_add_smul, zdot_toReal, zdot_toReal, hσdef]
          field_simp
          push_cast
          ring
      rw [hcomb]
      exact convex_convexHull ℝ _ hmemq hmemp (by linarith) hσ0 (by ring)
  -- `z` is a convex combination of `g` and `Y`
  set θ : ℝ := ((t : ℤ) : ℝ) / τ with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg htR.le hτ0.le
  have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one hτ0]; exact htτ
  have hθτ : θ * τ = ((t : ℤ) : ℝ) := by rw [hθdef]; field_simp
  have hzcomb : toReal (g + (t : ℤ) • u) = (1 - θ) • toReal g + θ • Y := by
    rw [tRA, tRZ, hYdef, ← hθτ]
    module
  show toReal (g + (t : ℤ) • u) ∈ rHull (A ∪ {p, q})
  rw [hzcomb]
  exact convex_convexHull ℝ _ (hmemA g hg) hYhull (by linarith) hθ0 (by ring)

/-! ### Receipts (硬规矩 6) -/

private def sqA : Set (ℤ × ℤ) := {(0, 0), (1, 0), (0, 1), (1, 1)}

/-- The truncated sweep really is bigger than `A`, so the covering statement has content. -/
theorem cover_instance_nonvacuous :
    ((1 : ℤ), (-2 : ℤ)) ∈ reachSet sqA ((0 : ℤ), (-1 : ℤ)) ∩
      Nivat.LE2.halfPlaneGE ((0 : ℤ), (1 : ℤ)) (-2) ∧
    ((1 : ℤ), (-2 : ℤ)) ∉ sqA := by
  refine ⟨⟨⟨((1 : ℤ), (0 : ℤ)), ?_, 2, ?_⟩, ?_⟩, ?_⟩
  · simp [sqA]
  · decide
  · simp only [Nivat.LE2.halfPlaneGE, Set.mem_ofPred_eq]; decide
  · simp [sqA]

/-- **`hpmax` is not decoration.**  Replacing the `n₀`-maximal corner `(1,-2)` by the
non-maximal `(0,-2)` breaks the covering: `(1,-2)` is in the truncated sweep but outside the
hull, separated by `⟪(1,-1), ·⟫ ≤ 2`. -/
theorem cover_needs_extremal_corner :
    ((1 : ℤ), (-2 : ℤ)) ∉ latHull (sqA ∪ {((0 : ℤ), (-2 : ℤ)), ((0 : ℤ), (-2 : ℤ))}) := by
  intro h
  have hb : ∀ y ∈ sqA ∪ {((0 : ℤ), (-2 : ℤ)), ((0 : ℤ), (-2 : ℤ))},
      dot ((1 : ℤ), (-1 : ℤ)) y ≤ 2 := by
    rintro y hy
    simp only [sqA, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with (rfl | rfl | rfl | rfl) | (rfl | rfl) <;> decide
  have := dot_le_of_mem_latHull hb h
  revert this
  decide

/-! ## §19.  A sweep deletes every edge it points out of — and what that costs `shellEnv`

Added 2026-09-23 (lane-chaindata-lead).

`notMem_E_reachSet_of_dot_pos` is the trivial half of §12's H-representation, stated on its
own because it is what makes the edge-count bookkeeping for `shellEnv` checkable: sweeping
along `u` sends `⟪n, ·⟫` to `+∞` for every `n` with `⟪n,u⟫ > 0`, so `face (reachSet A u) n` is
**empty** and `n ∉ E (reachSet A u)`.  No finiteness, no convexity, no primitivity.

**🔴 The count this forces, and why §10's account of it is wrong for `m ≥ 4`.**

`shellEnv` asks for `Enveloped ↑𝒮_φ T` with
`T = shellInter Â_i (shell Â_∞ v_{J-1} n_J c_J ε) w = reachSet Â_i w ∩ reachSet Â_∞ v_{J-1} ∩
halfPlaneGE n_J (c_J - ε)`, and `Enveloped` forces `E T = E ↑𝒮_φ` (`Enveloped.E_eq`).  By the
theorem below the first factor has already lost every `n ∈ E ↑𝒮_φ` with `⟪n,w⟫ > 0`, so those
must come back from the other two factors.

§10's docstring says they come back from `reachSet Â_∞ v_{J-1}`, "which keeps
`{n | ⟪n,v_{J-1}⟫ ≤ 0}`".  That reading silently assumes `suppVal Â_∞ n` is **finite** for
those `n` — i.e. that `Â_∞` still carries `𝒮_φ`'s constraints.  It does not: `Â_∞ = ⋃ᵢ Â_i` is
the *unbounded* limit of the tower, so `suppVal Â_∞ n = +∞` for every direction in which the
`Â_i` grow, and the corresponding constraint is simply absent.  The only support values pinned
uniformly in `i` are the two the bundle pins by hypothesis — `hAhatLevel` (`⟪n_ℓ,·⟫ ≥ c_z`,
outward normal `ℓ = -n_ℓ`) and `hhp` (`⟪n_J,·⟫ ≥ c_J`, outward normal `J = -n_J`).  Of those,
`hsweep` (`⟪n_J,v_{J-1}⟫ < 0`, i.e. `⟪J,v_{J-1}⟫ > 0`) makes the `v_{J-1}`-sweep delete `J`
again, while `dot_nl_vJ1_nonneg` (§1) keeps `ℓ`.  So `reachSet Â_∞ v_{J-1}` plausibly
contributes exactly **one** constraint, `ℓ`, and the half-plane factor contributes exactly one,
`-n_J = J`.  That leaves

    E T ⊆ {n ∈ E ↑𝒮_φ | ⟪n,w⟫ ≤ 0} ∪ {ℓ, J},

so `shellEnv` needs `{n ∈ E ↑𝒮_φ | ⟪n,w⟫ > 0} ⊆ {ℓ, J}`.

**The fan count (硬规矩 6, by hand).**  `w = -(dir ν_{J+1})` and
`dot n (-(dir ν)) = det n ν`, so `⟪n,w⟫ > 0 ⟺ 0 < det n ν_{J+1}` — the open half-turn of
normals ccw-**preceding** `ν_{J+1}`, which for a centrally symmetric `E ↑𝒮_φ` with `2m` normals
contains exactly `m - 1` of them.  `ℓ`, `J`, `ν_{J+1}` are consecutive in the fan
(`Arc ℓ J = ∅` from `LeafAJSelect.exists_nprevJ_vJ1`, `Arc J ν_{J+1} = ∅` from
`LeafAShellNNext.exists_w_hsweepW`), so those `m - 1` normals are `J`, `ℓ`, and then `m - 3`
more.  **The containment therefore holds iff `m ≤ 3`.**

Worked `m = 4` instance, computed by hand:

* `E ↑𝒮_φ = {(1,0),(1,1),(0,1),(-1,1),(-1,0),(-1,-1),(0,-1),(1,-1)}` (octagon, `m = 4`).
* `n_ℓ := (0,1)`, `c_z := 0`, `ℓ := -n_ℓ = (0,-1)`; ccw successor `J := (1,-1)`; its ccw
  successor `ν_{J+1} := (1,0)`.  So `w = -(dir (1,0)) = -(0,1) = (0,-1)` and
  `v_{J-1} = dir ℓ = dir (0,-1) = (1,0)`.
* Sign checks: `⟪n_ℓ,v_{J-1}⟫ = 0 ≥ 0` ✓ (§1);  `n_J = -J = (-1,1)`, `⟪n_J,v_{J-1}⟫ = -1 < 0` ✓
  (`hsweep`);  `⟪n_J,w⟫ = -1 < 0` ✓ (`hsweepW`);  `⟪n_ℓ,w⟫ = -1 < 0` (transverse case).
* `⟪n,w⟫ = ⟪n,(0,-1)⟫ > 0 ⟺ n.2 < 0`, i.e. `{(0,-1), (1,-1), (-1,-1)} = {ℓ, J, (-1,-1)}`.
* `(-1,-1)` is deleted by the `w`-sweep and restored by neither cut.  §10's
  `sweeps_nonpos_of_ne_J` does classify it as "retained by the other sweep"
  (`⟪(-1,-1), v_{J-1}⟫ = ⟪(-1,-1),(1,0)⟫ = -1 ≤ 0`) — but that sweep is applied to `Â_∞`, which
  carries no `(-1,-1)`-constraint to retain.

**Status.**  This is **not** a refutation of `shellEnv`: it is a refutation of §10's *account*
of the edge count, plus a precise statement of what a refutation would need — a concrete
admissible bundle with `m ≥ 4` in which `E Â_∞ = {ℓ, J}` is pinned as a kernel fact (i.e. `Â_∞`
really is unbounded in every other direction).  §10's three theorems are pure fan
combinatorics and remain true as stated; only the docstring's inference from them to the
shell's edge set is withdrawn.  §17/§18 are unaffected — they are statements about `latHull`
and about a truncated sweep, with no bundle content. -/

/-- `dot n` is unbounded above on `reachSet A u` as soon as `0 < dot n u`. -/
theorem exists_dot_gt_of_mem_reachSet {A : Set (ℤ × ℤ)} {u n : ℤ × ℤ}
    (hA : A.Nonempty) (hnu : 0 < dot n u) (c : ℤ) :
    ∃ y ∈ reachSet A u, c < dot n y := by
  obtain ⟨g, hg⟩ := hA
  obtain ⟨t, ht⟩ : ∃ t : ℕ, c < dot n g + (t : ℤ) * dot n u := by
    refine ⟨(c - dot n g + 1).toNat, ?_⟩
    have h1 : (c - dot n g + 1 : ℤ) ≤ (((c - dot n g + 1).toNat : ℕ) : ℤ) := Int.self_le_toNat _
    have h2 : (0 : ℤ) ≤ (((c - dot n g + 1).toNat : ℕ) : ℤ) := Int.natCast_nonneg _
    nlinarith
  refine ⟨g + (t : ℤ) • u, ⟨g, hg, t, rfl⟩, ?_⟩
  rwa [dot_add, Nivat.ColleReg.dot_zsmul_right]

/-- **A sweep deletes the supporting constraints it points out of.**  No finiteness, no
convexity: `face (reachSet A u) n` is empty, so `n ∉ E (reachSet A u)`. -/
theorem notMem_E_reachSet_of_dot_pos {A : Set (ℤ × ℤ)} {u n : ℤ × ℤ}
    (hA : A.Nonempty) (hnu : 0 < dot n u) : n ∉ E (reachSet A u) := by
  intro hn
  obtain ⟨-, hnt⟩ := mem_E_iff.mp hn
  obtain ⟨z, hz⟩ := hnt.nonempty
  obtain ⟨y, hy, hlt⟩ := exists_dot_gt_of_mem_reachSet hA hnu (dot n z)
  have := hz.2 y hy
  omega

end Nivat.LaneCdSubstrip

/-! ## §20.  `shellEnv` does not follow from the shell-group hypotheses — a kernel witness

§19 showed that `shellEnv` needs `{n ∈ E ↑𝒮_φ | ⟪n, w⟫ > 0} ⊆ {ℓ, J}`, and that the fan count
makes that containment equivalent to `m ≤ 3`.  `DecompData` (`DecompData.lean:85-108`) bounds
`m` only from below (`hm : 2 ≤ m`), and `DecompData.E_Sphi_eq` (`ShellMink.lean:1755`) pins
`|E ↑d.Sphi| = 2m` exactly, so `m = 4` is not excluded upstream.  This section exhibits the
resulting failure as a kernel-checked fact.

This is a **scoped** refutation of the `shellEnv` binder of
`Nivat.Colle35.ChainDataGeom.ofPartsExhaustsInter` (`ChainExhaustInter.lean`), in the style
of `ShellMink.not_shellSubStrip_of_transverse_sweep`: the shell-group hypotheses are carried as
explicit conjuncts rather than by inhabiting a `ChainDataGeom` (no `ChainDataGeomParts` is
inhabited anywhere in the tree, so a bundle-level refutation cannot be written down at all).

**Encoded:** the fan signs relating `nℓ`, `ℓ`, `J`, `nJ`, `ν_{J+1}`, `v_{J-1}`, `w`; that `Â_i`
is an `E(𝒮_φ)`-enveloped family; that it is increasing (`AhatMono`); and the two uniform pins
`hhp` and `hAhatLevel`, both *attained* on every `Â_i`, so neither pin is slack.

**Not encoded:** `Exhausts`, `shellSubStrip`, `escapeW`, `fillCover`, `bottom`, and the whole
`Config` / `PeriodOn` side of the bundle.  To save `shellEnv` one must exhibit a bundle
hypothesis that this configuration violates — see `OPEN.md`.
-/


namespace Nivat.LaneCdM4

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.ShellMink Pointwise

/-! ### The octagon `S8` (`m = 4`) -/

def S8 : Set (ℤ × ℤ) :=
  {z | -2 ≤ z.1 ∧ z.1 ≤ 2 ∧ -2 ≤ z.2 ∧ z.2 ≤ 2 ∧
       -3 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 3 ∧ -3 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ 3}

theorem mem_S8 {z : ℤ × ℤ} :
    z ∈ S8 ↔ -2 ≤ z.1 ∧ z.1 ≤ 2 ∧ -2 ≤ z.2 ∧ z.2 ≤ 2 ∧
       -3 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 3 ∧ -3 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ 3 := Iff.rfl

theorem finite_S8 : S8.Finite := by
  have hsub : S8 ⊆ (Set.Icc (-2 : ℤ) 2) ×ˢ (Set.Icc (-2 : ℤ) 2) := by
    rintro z hz
    exact ⟨⟨hz.1, hz.2.1⟩, ⟨hz.2.2.1, hz.2.2.2.1⟩⟩
  exact Set.Finite.subset ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)) hsub

theorem nonempty_S8 : S8.Nonempty := ⟨(0, 0), by simp [S8]⟩

/-! ### The three edge normals of `S8` that we need -/

theorem mem_E_S8_neg11 : ((-1 : ℤ), (-1 : ℤ)) ∈ E S8 := by
  have hbound : ∀ y ∈ S8, dot ((-1 : ℤ), (-1 : ℤ)) y ≤ 3 := by
    intro y hy
    simp only [dot]
    have := hy.2.2.2.2.1
    omega
  have ha : ((-1 : ℤ), (-2 : ℤ)) ∈ face S8 ((-1 : ℤ), (-1 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  have hb : ((-2 : ℤ), (-1 : ℤ)) ∈ face S8 ((-1 : ℤ), (-1 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  exact ⟨by decide, ⟨_, ha, _, hb, by decide⟩⟩

theorem mem_E_S8_01 : ((0 : ℤ), (1 : ℤ)) ∈ E S8 := by
  have hbound : ∀ y ∈ S8, dot ((0 : ℤ), (1 : ℤ)) y ≤ 2 := by
    intro y hy
    simp only [dot]
    have := hy.2.2.2.1
    omega
  have ha : ((0 : ℤ), (2 : ℤ)) ∈ face S8 ((0 : ℤ), (1 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  have hb : ((1 : ℤ), (2 : ℤ)) ∈ face S8 ((0 : ℤ), (1 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  exact ⟨by decide, ⟨_, ha, _, hb, by decide⟩⟩

theorem mem_E_S8_0neg1 : ((0 : ℤ), (-1 : ℤ)) ∈ E S8 := by
  have hbound : ∀ y ∈ S8, dot ((0 : ℤ), (-1 : ℤ)) y ≤ 2 := by
    intro y hy
    simp only [dot]
    have := hy.2.2.1
    omega
  have ha : ((0 : ℤ), (-2 : ℤ)) ∈ face S8 ((0 : ℤ), (-1 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  have hb : ((1 : ℤ), (-2 : ℤ)) ∈ face S8 ((0 : ℤ), (-1 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  exact ⟨by decide, ⟨_, ha, _, hb, by decide⟩⟩

theorem mem_E_S8_10 : ((1 : ℤ), (0 : ℤ)) ∈ E S8 := by
  have hbound : ∀ y ∈ S8, dot ((1 : ℤ), (0 : ℤ)) y ≤ 2 := by
    intro y hy
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hy
    simp only [dot]
    omega
  have ha : ((2 : ℤ), (0 : ℤ)) ∈ face S8 ((1 : ℤ), (0 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  have hb : ((2 : ℤ), (1 : ℤ)) ∈ face S8 ((1 : ℤ), (0 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  exact ⟨by decide, ⟨_, ha, _, hb, by decide⟩⟩

theorem mem_E_S8_neg10 : ((-1 : ℤ), (0 : ℤ)) ∈ E S8 := by
  have hbound : ∀ y ∈ S8, dot ((-1 : ℤ), (0 : ℤ)) y ≤ 2 := by
    intro y hy
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hy
    simp only [dot]
    omega
  have ha : ((-2 : ℤ), (0 : ℤ)) ∈ face S8 ((-1 : ℤ), (0 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  have hb : ((-2 : ℤ), (1 : ℤ)) ∈ face S8 ((-1 : ℤ), (0 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  exact ⟨by decide, ⟨_, ha, _, hb, by decide⟩⟩

theorem mem_E_S8_11 : ((1 : ℤ), (1 : ℤ)) ∈ E S8 := by
  have hbound : ∀ y ∈ S8, dot ((1 : ℤ), (1 : ℤ)) y ≤ 3 := by
    intro y hy
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hy
    simp only [dot]
    omega
  have ha : ((1 : ℤ), (2 : ℤ)) ∈ face S8 ((1 : ℤ), (1 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  have hb : ((2 : ℤ), (1 : ℤ)) ∈ face S8 ((1 : ℤ), (1 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  exact ⟨by decide, ⟨_, ha, _, hb, by decide⟩⟩

theorem mem_E_S8_1neg1 : ((1 : ℤ), (-1 : ℤ)) ∈ E S8 := by
  have hbound : ∀ y ∈ S8, dot ((1 : ℤ), (-1 : ℤ)) y ≤ 3 := by
    intro y hy
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hy
    simp only [dot]
    omega
  have ha : ((2 : ℤ), (-1 : ℤ)) ∈ face S8 ((1 : ℤ), (-1 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  have hb : ((1 : ℤ), (-2 : ℤ)) ∈ face S8 ((1 : ℤ), (-1 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  exact ⟨by decide, ⟨_, ha, _, hb, by decide⟩⟩

theorem mem_E_S8_neg1pos1 : ((-1 : ℤ), (1 : ℤ)) ∈ E S8 := by
  have hbound : ∀ y ∈ S8, dot ((-1 : ℤ), (1 : ℤ)) y ≤ 3 := by
    intro y hy
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hy
    simp only [dot]
    omega
  have ha : ((-2 : ℤ), (1 : ℤ)) ∈ face S8 ((-1 : ℤ), (1 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  have hb : ((-1 : ℤ), (2 : ℤ)) ∈ face S8 ((-1 : ℤ), (1 : ℤ)) := by
    refine ⟨by simp [S8], fun y hy => ?_⟩
    have := hbound y hy
    simp only [dot] at this ⊢
    omega
  exact ⟨by decide, ⟨_, ha, _, hb, by decide⟩⟩

/-- **All eight octagon normals are edge normals of `S8`.**  With `DecompData.E_Sphi_eq`
(`ShellMink.lean:1755`) giving `|E ↑d.Sphi| = 2m` exactly, eight distinct edge normals force
`m ≥ 4` *for any `DecompData` whose `↑d.Sphi` is this `S8`* — so this configuration cannot be
dismissed as an artefact of a small fan: it is consistent only with `m ≥ 4`, which is exactly
where the edge bookkeeping for `shellEnv` breaks.

**Not claimed:** that `S8` *is* realizable as some `↑d.Sphi`.  `Sphi_eq`
(`DecompData.lean:85-108`) constrains `Conv Sphi` to be the zonotope `Conv (supp (∏ (mono (h i)
- 1)))`, and no such `h : Fin 4 → ℤ × ℤ` is exhibited here.  The refutation below does not need
it — it refutes the `shellEnv` *implication* from the shell-group hypotheses, for which `S8` is
just an admissible value of the enveloping set.  (Only the `⊆` direction is proved;
`E S8 ⊆ {those eight}` is the phantom-edge problem and is not needed here.) -/
def N8 : Finset (ℤ × ℤ) :=
  {((1 : ℤ), (0 : ℤ)), ((-1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((0 : ℤ), (-1 : ℤ)),
   ((1 : ℤ), (1 : ℤ)), ((1 : ℤ), (-1 : ℤ)), ((-1 : ℤ), (1 : ℤ)), ((-1 : ℤ), (-1 : ℤ))}

/-- The eight normals really are **distinct**: `N8.card = 8`.  This is the half that turns
"eight listed normals" into "eight distinct edge normals", which is what `|E ↑d.Sphi| = 2m`
needs in order to force `m ≥ 4`. -/
theorem card_N8 : N8.card = 8 := by decide

theorem eight_normals_subset_E_S8 : (↑N8 : Set (ℤ × ℤ)) ⊆ E S8 := by
  rintro n hn
  simp only [N8, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_E_S8_10
  · exact mem_E_S8_neg10
  · exact mem_E_S8_01
  · exact mem_E_S8_0neg1
  · exact mem_E_S8_11
  · exact mem_E_S8_1neg1
  · exact mem_E_S8_neg1pos1
  · exact mem_E_S8_neg11

/-! ### The Minkowski generators `B i` -/

def B (i : ℕ) : Set (ℤ × ℤ) := {z | z.2 = 0 ∧ -(i : ℤ) ≤ z.1 ∧ z.1 ≤ 0}

theorem mem_B {i : ℕ} {z : ℤ × ℤ} : z ∈ B i ↔ z.2 = 0 ∧ -(i : ℤ) ≤ z.1 ∧ z.1 ≤ 0 := Iff.rfl

theorem finite_B (i : ℕ) : (B i).Finite := by
  have hsub : B i ⊆ (Set.Icc (-(i : ℤ)) 0) ×ˢ (Set.Icc (0 : ℤ) 0) := by
    rintro z hz
    exact ⟨⟨hz.2.1, hz.2.2⟩, ⟨le_of_eq hz.1.symm, le_of_eq hz.1⟩⟩
  exact Set.Finite.subset ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)) hsub

theorem nonempty_B (i : ℕ) : (B i).Nonempty := ⟨(0, 0), by simp [B]⟩

theorem mono_B {i j : ℕ} (h : i ≤ j) : B i ⊆ B j := by
  rintro z ⟨h1, h2, h3⟩
  refine ⟨h1, ?_, h3⟩
  have : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast h
  omega

theorem E_B_subset (i : ℕ) : E (B i) ⊆ E S8 := by
  rintro n ⟨hprim, a, ha, b, hb, hab⟩
  have ha2 : a.2 = 0 := ha.1.1
  have hb2 : b.2 = 0 := hb.1.1
  have hdot : dot n a = dot n b := dot_eq_of_mem_face ha hb
  have h1ne : a.1 ≠ b.1 := by
    intro h
    exact hab (Prod.ext h (by rw [ha2, hb2]))
  have hn1 : n.1 = 0 := by
    simp only [dot, ha2, hb2, mul_zero, add_zero] at hdot
    rcases mul_eq_zero.mp (by linarith : n.1 * (a.1 - b.1) = 0) with h | h
    · exact h
    · exact absurd (by omega : a.1 = b.1) h1ne
  have hgcd : n.2.natAbs = 1 := by
    have : Int.gcd n.1 n.2 = 1 := hprim
    rw [hn1] at this
    simpa [Int.gcd] using this
  have hn2 : n.2 = 1 ∨ n.2 = -1 := by omega
  have hne : n = ((0 : ℤ), (1 : ℤ)) ∨ n = ((0 : ℤ), (-1 : ℤ)) := by
    rcases hn2 with h | h
    · exact Or.inl (Prod.ext hn1 h)
    · exact Or.inr (Prod.ext hn1 h)
  rcases hne with rfl | rfl
  · exact mem_E_S8_01
  · exact mem_E_S8_0neg1

/-! ### The tower `Ahat` -/

def Ahat (i : ℕ) : Set (ℤ × ℤ) := latHull (S8 + B i)

theorem enveloped_Ahat (i : ℕ) : Enveloped S8 (Ahat i) :=
  enveloped_add_of_finite finite_S8 nonempty_S8 (finite_B i) (nonempty_B i) (E_B_subset i)

theorem latHull_mono' {X T : Set (ℤ × ℤ)} (h : X ⊆ T) : latHull X ⊆ latHull T :=
  Set.preimage_mono (convexHull_mono (Set.image_mono h))

theorem mono_Ahat {i j : ℕ} (h : i ≤ j) : Ahat i ⊆ Ahat j := by
  refine latHull_mono' ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, ha, b, mono_B h hb, rfl⟩

/-! ### The three uniform bounds on the tower -/

theorem Ahat_x_ge (i : ℕ) : ∀ z ∈ Ahat i, -2 - (i : ℤ) ≤ z.1 := by
  intro z hz
  have hb : ∀ y ∈ S8 + B i, dot ((-1 : ℤ), (0 : ℤ)) y ≤ 2 + (i : ℤ) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have h1 : -2 ≤ a.1 := ha.1
    have h2 : -(i : ℤ) ≤ b.1 := hb.2.1
    simp only [dot, Prod.fst_add, Prod.snd_add]
    omega
  have := dot_le_of_mem_latHull hb hz
  simp only [dot] at this
  omega

theorem Ahat_y_ge (i : ℕ) : ∀ z ∈ Ahat i, (-2 : ℤ) ≤ z.2 := by
  intro z hz
  have hb : ∀ y ∈ S8 + B i, dot ((0 : ℤ), (-1 : ℤ)) y ≤ 2 := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have h1 : -2 ≤ a.2 := ha.2.2.1
    have h2 : b.2 = 0 := hb.1
    simp only [dot, Prod.fst_add, Prod.snd_add]
    omega
  have := dot_le_of_mem_latHull hb hz
  simp only [dot] at this
  omega

theorem Ahat_hhp (i : ℕ) : ∀ z ∈ Ahat i, (-3 : ℤ) ≤ dot ((-1 : ℤ), (1 : ℤ)) z := by
  intro z hz
  have hb : ∀ y ∈ S8 + B i, dot ((1 : ℤ), (-1 : ℤ)) y ≤ 3 := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have h1 : a.1 - a.2 ≤ 3 := ha.2.2.2.2.2.2.2
    have h2 : b.1 ≤ 0 := hb.2.2
    have h3 : b.2 = 0 := hb.1
    simp only [dot, Prod.fst_add, Prod.snd_add]
    omega
  have := dot_le_of_mem_latHull hb hz
  simp only [dot] at this ⊢
  omega

/-! ### Two explicit tower points -/

theorem mem_Ahat_col (i : ℕ) : ((-2 - (i : ℤ)), (0 : ℤ)) ∈ Ahat i := by
  refine subset_latHull _ ?_
  refine ⟨((-2 : ℤ), (0 : ℤ)), by simp [S8], ((-(i : ℤ)), (0 : ℤ)), ?_, ?_⟩
  · exact ⟨rfl, le_refl _, by omega⟩
  · simp only [Prod.mk_add_mk, Prod.mk.injEq]
    omega

theorem mem_Ahat_low (i : ℕ) : ((-2 - (i : ℤ)), (-2 : ℤ)) ∈ Ahat (i + 1) := by
  refine subset_latHull _ ?_
  refine ⟨((-1 : ℤ), (-2 : ℤ)), by simp [S8], ((-1 - (i : ℤ)), (0 : ℤ)), ?_, ?_⟩
  · refine ⟨rfl, ?_, by omega⟩
    push_cast
    omega
  · simp only [Prod.mk_add_mk, Prod.mk.injEq]
    omega

/-! ### The shell -/

def T (i : ℕ) (ε : ℕ) : Set (ℤ × ℤ) :=
  shellInter (Ahat i) (MaxEnv.shell (⋃ j, Ahat j) ((1 : ℤ), (0 : ℤ)) ((-1 : ℤ), (1 : ℤ)) (-3) ε)
    ((0 : ℤ), (-1 : ℤ))

theorem mem_T (i ε : ℕ) : ((-2 - (i : ℤ)), (-2 : ℤ)) ∈ T i ε := by
  refine ⟨⟨((-2 - (i : ℤ)), (0 : ℤ)), mem_Ahat_col i, 2, ?_⟩, ?_⟩
  · simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
    omega
  · refine ⟨((-2 - (i : ℤ)), (-2 : ℤ)), Set.mem_iUnion.mpr ⟨i + 1, mem_Ahat_low i⟩, 0, ?_, ?_⟩
    · simp
    · simp only [dot]
      omega

theorem fst_sweep (g : ℤ × ℤ) (t : ℕ) :
    (g + (t : ℤ) • ((0 : ℤ), (-1 : ℤ))).1 = g.1 := by
  simp only [Prod.smul_mk, smul_eq_mul, Prod.fst_add]
  ring

theorem snd_sweep (g : ℤ × ℤ) (t : ℕ) :
    (g + (t : ℤ) • ((1 : ℤ), (0 : ℤ))).2 = g.2 := by
  simp only [Prod.smul_mk, smul_eq_mul, Prod.snd_add]
  ring

theorem T_x_ge (i ε : ℕ) : ∀ z ∈ T i ε, -2 - (i : ℤ) ≤ z.1 := by
  rintro z ⟨⟨g, hg, t, rfl⟩, -⟩
  have h1 := Ahat_x_ge i g hg
  rw [fst_sweep]
  omega

theorem T_y_ge (i ε : ℕ) : ∀ z ∈ T i ε, (-2 : ℤ) ≤ z.2 := by
  rintro z ⟨-, h, hh, t, rfl, -⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hh
  have h1 := Ahat_y_ge j h hj
  rw [snd_sweep]
  omega

theorem face_T_subset (i ε : ℕ) :
    face (T i ε) ((-1 : ℤ), (-1 : ℤ)) ⊆ {((-2 - (i : ℤ)), (-2 : ℤ))} := by
  rintro z ⟨hzT, hmax⟩
  have hkey := hmax _ (mem_T i ε)
  have hx := T_x_ge i ε z hzT
  have hy := T_y_ge i ε z hzT
  simp only [dot] at hkey
  have hz1 : z.1 = -2 - (i : ℤ) := by omega
  have hz2 : z.2 = (-2 : ℤ) := by omega
  exact Set.mem_singleton_iff.mpr (Prod.ext hz1 hz2)

theorem notMem_E_T (i ε : ℕ) : ((-1 : ℤ), (-1 : ℤ)) ∉ E (T i ε) := by
  rintro ⟨-, hnt⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hnt
  have h1 := face_T_subset i ε ha
  have h2 := face_T_subset i ε hb
  rw [Set.mem_singleton_iff] at h1 h2
  exact hab (h1.trans h2.symm)

/-- **The shell is `E(S8)`-enveloped for no `ε` and no `i`.**

*Why the shape of the union here does not weaken the result.*  `⋃ⱼ Ahat j` grows leftward
rather than in the `n_l` direction, so it is bounded in `z.2`, unlike the real tower.  That
deviation cannot rescue `shellEnv`: enlarging `⋃ⱼ Ahat j` only *weakens* the second factor of
`shellInter`, so it can only remove constraints from the shell, never restore the lost edge.
Concretely, the two bounds this proof rests on are `z.1 ≥ -2-i`, drawn from the **finite**
level `Ahat i` (untouched by any enlargement of the union), and `z.2 ≥ -2`, drawn from the
union's floor — and that floor is exactly what `hAhatLevel` pins in the real bundle, so it
survives any enlargement consistent with the bundle.  Adding `Exhausts` makes the union larger
still and hence makes the refutation strictly stronger, not weaker. -/
theorem not_enveloped_T (i ε : ℕ) : ¬ Enveloped S8 (T i ε) := by
  intro h
  have hE : E (T i ε) = E S8 := Enveloped.E_eq (finite_E_of_finite finite_S8) h
  exact notMem_E_T i ε (hE ▸ mem_E_S8_neg11)

/-! ### Non-degeneracy: the shell contains the whole tower level, and the tower really
does carry the edge the shell loses. -/

theorem Ahat_subset_T (i ε : ℕ) : Ahat i ⊆ T i ε := by
  intro z hz
  refine ⟨⟨z, hz, 0, by simp⟩, z, Set.mem_iUnion.mpr ⟨i, hz⟩, 0, by simp, ?_⟩
  have := Ahat_hhp i z hz
  omega

theorem mem_E_Ahat_neg11 (i : ℕ) : ((-1 : ℤ), (-1 : ℤ)) ∈ E (Ahat i) := by
  have hE : E (Ahat i) = E S8 :=
    Enveloped.E_eq (finite_E_of_finite finite_S8) (enveloped_Ahat i)
  exact hE ▸ mem_E_S8_neg11

/-! ### The packaged statement -/

/-- **`shellEnv` does not follow from the shell-group hypotheses.**  What is refuted is the
*implication*: the listed conjuncts all hold, and yet `Enveloped S8 (T i ε)` holds for no `ε`
and no `i` — so no choice of `ε > 0` and no threshold `i₀` can satisfy `shellEnv`'s
`∃ ε i₀, 0 < ε ∧ ∀ i ≥ i₀, Env (...)`.  Quantifying `ε` over `ℕ` is not a weakening: the shell's
`ε` enters only through `c - ε ≤ dot n z`, and every positive integer `ε` is a `ℕ`.

The eight-normal clause records *where* the failure lives rather than adding a hypothesis:
`DecompData.E_Sphi_eq` (`ShellMink.lean:1755`) gives `|E ↑d.Sphi| = 2m` exactly, so a
`DecompData` with `↑d.Sphi = S8` would have `m ≥ 4`.  Whether such a `DecompData` exists is not
established here — see `eight_normals_subset_E_S8`. -/
theorem shellEnv_false_at_m_four :
    -- fan signs, exactly the shell-group hypotheses of `ofPartsExhaustsInter`
    dot ((-1 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) < 0 ∧
    dot ((-1 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) < 0 ∧
    0 ≤ dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) ∧
    dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) < 0 ∧
    0 < det ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (-1 : ℤ)) ∧
    0 < det ((1 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)) ∧
    ((1 : ℤ), (0 : ℤ)) = dir ((0 : ℤ), (-1 : ℤ)) ∧
    ((0 : ℤ), (-1 : ℤ)) = -(dir ((1 : ℤ), (0 : ℤ))) ∧
    ((-1 : ℤ), (1 : ℤ)) = -((1 : ℤ), (-1 : ℤ)) ∧
    ((0 : ℤ), (-1 : ℤ)) = -((0 : ℤ), (1 : ℤ)) ∧
    -- `m ≥ 4`: eight *distinct* edge normals, and `|E ↑d.Sphi| = 2m` exactly
    N8.card = 8 ∧ (↑N8 : Set (ℤ × ℤ)) ⊆ E S8 ∧
    -- the tower is a genuine `E(S8)`-enveloped increasing chain pinned on both lines
    (∀ i, Enveloped S8 (Ahat i)) ∧
    (∀ i j, i ≤ j → Ahat i ⊆ Ahat j) ∧
    (∀ i, ∀ z ∈ Ahat i, (-3 : ℤ) ≤ dot ((-1 : ℤ), (1 : ℤ)) z) ∧
    (∀ i, ∀ z ∈ Ahat i, (-2 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) z) ∧
    -- the shell is not degenerate: it contains the whole tower level, and the tower
    -- level really does carry the edge normal `(-1,-1)`
    (∀ i ε : ℕ, Ahat i ⊆ T i ε) ∧
    (∀ i, ((-1 : ℤ), (-1 : ℤ)) ∈ E (Ahat i)) ∧
    ((-1 : ℤ), (-1 : ℤ)) ∈ E S8 ∧
    (∀ i ε : ℕ, ((-1 : ℤ), (-1 : ℤ)) ∉ E (T i ε)) ∧
    -- yet the shell is enveloped for no `ε` and no `i`
    (∀ ε i : ℕ, ¬ Enveloped S8 (T i ε)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, card_N8, eight_normals_subset_E_S8,
    enveloped_Ahat, fun i j h => mono_Ahat h, Ahat_hhp,
    fun i z hz => ?_, Ahat_subset_T, mem_E_Ahat_neg11, mem_E_S8_neg11,
    fun i ε => notMem_E_T i ε, fun ε i => not_enveloped_T i ε⟩
  have := Ahat_y_ge i z hz
  simp only [dot]
  omega

end Nivat.LaneCdM4

/-! ## §21.  Every normal the `w`-sweep deletes is recovered — for every `m`

**This section retracts §19's docstring alarm.**  §19 inferred that `shellEnv`'s edge
bookkeeping needs `{n ∈ E ↑𝒮_φ | ⟪n, w⟫ > 0} ⊆ {ℓ, J}`, hence `m ≤ 3`.  That inference
undercounted, because it treated `Â_∞` as carrying only its two pinned constraints.

Collé `b3_colle2.txt:506` pins `Â_∞`'s shape: it is an `(ℓ, ℓ_J)`-region — two semi-infinite
edges, one parallel to `ℓ` and one parallel to `ℓ_J`.  A wedge has *finite support in its whole
polar cone*, not in two directions: `suppVal Â_∞ n < ∞` exactly when
`⟪n, v_ℓ⟫ ≤ 0 ∧ ⟪n, v_{ℓ_J}⟫ ≤ 0`, i.e. for `m` of the `2m` normals, not `2`.  Together with
`b3_colle2.txt:440`'s `Â_∞^{(ε)} = reachSet Â_∞ v_{ℓ_{J-1}} ∩ {dist(·, ℓ_J) ≤ d_ε}` and
`:518`'s `Â_i^{(ε)} = reachSet Â_i (-v_{ℓ_{J+1}}) ∩ Â_∞^{(ε)}`, the recovery sources are the
wedge's polar cone *plus* the band's cut normal `-n_J`.

The count then closes for every `m`.  Writing `⟪n, dir ν⟫ = det ν n` and indexing the ccw fan
so that `ℓ` is `k = 0`, `J` is `k = 1`, `ν_{J+1}` is `k = 2` (consecutive by
`Arc ℓ J = ∅`, `Arc J ν_{J+1} = ∅`, which also gives `ν_{J-1} = ℓ`):

* deleted by the sweep: `{n | det ν_{J+1} n < 0}` `= k ∈ {3-m, …, 1}`, that is `m-1` normals;
* recovered by `reachSet Â_∞ v_{J-1}`: `{det ℓ · ≤ 0} ∩ {det J · ≤ 0}` `= k ∈ {1-m, …, 0}`,
  that is `m` normals;
* leftover: `{3-m, …, 1} \ {1-m, …, 0} = {k = 1} = {J}` — and `n_J = -J`, so the band's cut
  normal `-n_J` is exactly `J`.

Nothing is left over, for any `m ≥ 2`.  `fan_receipt_arcs` / `fan_receipt_count` check the
`m = 4` octagon instance in the kernel (硬规矩 6).

⛔ **Narrowed 2026-09-24 (集成者, round 209; the sentence above is kept per PROTOCOL §14).**
"Nothing is left over, for any `m ≥ 2`" holds **only on the branch `Arc ℓ J = ∅`**.  Both
`recovered_of_sweep_deleted` and `recovered_of_sweep_deleted_dot` take
`harc_lJ : ∀ k ∈ E S, ¬ (0 < det l k ∧ det J k < 0)` — literally "no edge normal of `𝒮_φ` lies
strictly between `ℓ` and `J`" — and the main tree's own `J`-selection
`LeafAJSelect.exists_fan_pred` **states that as the degenerate branch**: it splits on
`Arc ℓ J`'s `eq_empty_or_nonempty`, and only the empty branch returns `nprevJ = ℓ`; in general
`nprevJ` lies strictly inside `Arc ℓ J` and what is delivered is `Arc nprevJ J = ∅` (its
docstring: "or `ℓ` itself when `Arc ℓ J = ∅` (team-lead's stated degenerate case)").
`N8` below is exactly such a degenerate instance — `Arc ℓ J = ∅` there, so it cannot test the
general branch.  **Substituting `nprevJ` for `ℓ` does not repair this**: `harc_lJ` then
discharges, but the conclusion weakens to `det nprevJ n ≤ 0`, which does **not** cover `Â_∞`'s
polar cone `{det ℓ · ≤ 0} ∩ {det J · ≤ 0}` — the gap is precisely the normals lying between
`ℓ` and `nprevJ`.
⟹ §19's `m ≤ 3` alarm stays retracted (that inference undercounted on its own, independently
of `harc_lJ`), but "the normal count is closed for every `m`" is **not** an established fact.
A general-branch numeric instance is being built (lane-hole3-nlmax).

**Still owed** (not proved here): that the `m` normals of the polar cone are genuinely *edges*
of `Â_∞` with faces at least as long as `𝒮_φ`'s.  `b3_colle2.txt:500-504` is the material —
`|Â_i ∩ w_i(j)|` is constant in `i` for `ι+1 ≤ j ≤ J-1` and strictly increasing for `j = J` —
but the main tree does not have it yet.  §21 settles *which* normals are present, not how long
their faces are; the face-length half is §16's job.

`ShellSubStrip.lean` §20 stays valid as a scoped kernel fact, and now reads as the *positive*
statement that the region content is load-bearing: its `⋃ hatOf` is a half-strip, not an
`(ℓ, ℓ_J)`-region, and `shellEnv` does collapse there.  So `rec_vJ'` / `side` / `bottom` may
not be dropped from the bundle.
-/


namespace Nivat.LaneCdFan

open Nivat Nivat.LE2

theorem recovered_of_sweep_deleted {S : Set (ℤ × ℤ)} {l J nu n : ℤ × ℤ}
    (hlJ : 0 < det l J) (hJ : J ∈ E S) (hn : n ∈ E S)
    (harc_lJ : ∀ k ∈ E S, ¬ (0 < det l k ∧ det J k < 0))
    (harc_Jnu : ∀ k ∈ E S, ¬ (0 < det J k ∧ det nu k < 0))
    (hdel : det nu n < 0) :
    n = J ∨ (det l n ≤ 0 ∧ det J n ≤ 0) := by
  have hJn : det J n ≤ 0 := by
    by_contra hcon
    exact harc_Jnu n hn ⟨lt_of_not_ge hcon, hdel⟩
  rcases lt_or_eq_of_le hJn with hlt | heq
  · refine Or.inr ⟨?_, hJn⟩
    by_contra hcon
    exact harc_lJ n hn ⟨lt_of_not_ge hcon, hlt⟩
  · -- `det J n = 0`: `n` is parallel to `J`, so `n = J` or `n = -J`
    have hJprim : Primitive J := prim_iff_primitive.mp (mem_E_iff.mp hJ).1
    have hnprim : Primitive n := prim_iff_primitive.mp (mem_E_iff.mp hn).1
    rcases eq_or_eq_neg_of_det_eq_zero hJprim hnprim heq with h | h
    · exact Or.inl h
    · refine Or.inr ⟨?_, hJn⟩
      subst h
      have : det l (-J) = -det l J := by
        cases l; cases J; simp only [det, Prod.neg_mk]; ring
      omega

/-- `w = -(dir ν)` turns the sweep test `0 < ⟪n, w⟫` into the orientation test
`det ν n < 0`. -/
theorem dot_neg_dir (n nu : ℤ × ℤ) : dot n (-(dir nu)) = -det nu n := by
  cases n; cases nu
  simp only [dot, dir, det, Prod.neg_mk]
  ring

/-- The form the assembly consumes: stated against the sweep direction `w` rather than
against `ν_{J+1}`. -/
theorem recovered_of_sweep_deleted_dot {S : Set (ℤ × ℤ)} {l J nu w n : ℤ × ℤ}
    (hw : w = -(dir nu))
    (hlJ : 0 < det l J) (hJ : J ∈ E S) (hn : n ∈ E S)
    (harc_lJ : ∀ k ∈ E S, ¬ (0 < det l k ∧ det J k < 0))
    (harc_Jnu : ∀ k ∈ E S, ¬ (0 < det J k ∧ det nu k < 0))
    (hdel : 0 < dot n w) :
    n = J ∨ (det l n ≤ 0 ∧ det J n ≤ 0) := by
  refine recovered_of_sweep_deleted hlJ hJ hn harc_lJ harc_Jnu ?_
  rw [hw, dot_neg_dir] at hdel
  omega

/-! ### Numeric receipt at `m = 4` (硬规矩 6)

The octagon fan, with `ℓ = (0,-1)`, `J = (1,-1)`, `ν_{J+1} = (1,0)`, `n_J = -J = (-1,1)`.
`det ℓ k = k.1`, `det J k = k.1 + k.2`, `det ν_{J+1} k = k.2`.  The sweep deletes exactly the
`m - 1 = 3` normals with `k.2 < 0`, and each of them is either `J` itself (recovered by the
`n_J`-cut, since `-n_J = J`) or lies in `Â_∞`'s normal cone `{det ℓ · ≤ 0} ∩ {det J · ≤ 0}`
(recovered by `reachSet Â_∞ v_{J-1}`).  Nothing is left over — which is the whole point. -/

def N8 : Finset (ℤ × ℤ) :=
  {((1 : ℤ), (0 : ℤ)), ((-1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((0 : ℤ), (-1 : ℤ)),
   ((1 : ℤ), (1 : ℤ)), ((1 : ℤ), (-1 : ℤ)), ((-1 : ℤ), (1 : ℤ)), ((-1 : ℤ), (-1 : ℤ))}

/-- The two arc-emptiness hypotheses really do hold for the octagon at this `ℓ`/`J`/`ν_{J+1}`:
the lemma above is not vacuously applicable. -/
theorem fan_receipt_arcs :
    (∀ k ∈ N8, ¬ (0 < det ((0 : ℤ), (-1 : ℤ)) k ∧ det ((1 : ℤ), (-1 : ℤ)) k < 0)) ∧
    (∀ k ∈ N8, ¬ (0 < det ((1 : ℤ), (-1 : ℤ)) k ∧ det ((1 : ℤ), (0 : ℤ)) k < 0)) := by
  decide

/-- The sweep really does delete `m - 1 = 3` normals (so the recovery claim has content), and
every one of them is recovered. -/
theorem fan_receipt_count :
    (N8.filter (fun n => det ((1 : ℤ), (0 : ℤ)) n < 0)).card = 3 ∧
    (∀ n ∈ N8, det ((1 : ℤ), (0 : ℤ)) n < 0 →
      n = ((1 : ℤ), (-1 : ℤ)) ∨
        (det ((0 : ℤ), (-1 : ℤ)) n ≤ 0 ∧ det ((1 : ℤ), (-1 : ℤ)) n ≤ 0)) := by
  decide

end Nivat.LaneCdFan

/-! ## §22.  `Â_i`'s face data is free, and the two cut corners do not shorten it

Added 2026-09-23 (lane-chaindata-lead).

**What `:500-504` is, and what is consumed.**  `delivery/scratch/b3_colle2.txt:500-504`
reads in Collé as a *subsequence extraction*: `|Â_i ∩ w_i(j)|` is arranged to be constant
in `i` for `ι+1 ≤ j ≤ J-1` and strictly increasing for `j = J`.  The downstream assembly
consumes something weaker and one-sided — for every edge normal `n` of `𝒮_φ`, `n` is an
edge normal of `Â_i` too and `Â_i`'s face at `n` is at least as long as `𝒮_φ`'s.  That
one-sided form is **free** from binders `ofPartsExhaustsInter` (`ChainExhaustInter.lean`)
already carries: `maxA` gives `Env (A i)` (`envA_of_max`, `ChainMax.lean:106`), `hEnv`
turns it into `Enveloped ↑S (A i)`, `Â_i` is a translate of `A i` (`hatOf_eq_shift`,
`ChainAssemble.lean:300`), and `Enveloped.E_eq` / `Enveloped.face_encard_le`
(`LatticeEdges.lean:1657` / `:1663`) read off both halves.  `latticeConvex_iUnion_hatOf`
(`ChainAssemble.lean:313`) already walks the same path internally without exporting the
face half.  So the "stable in `i`" quantifier of a face-length dispatch is one **we** would
be adding: it has a `:500-504` counterpart but no consumer (硬规矩 5).

**Why that is not yet `hface`.**  §17's `enveloped_of_two_corners` (`:1704`) states `hface`
about `X := Â_i ∪ {p, q}`, and adding points is not face-monotone: if `⟪n, p⟫` beats
`Â_i`'s maximum, `face X n` collapses to `{p}` and may be shorter than `face ↑S n`.
`face_subset_face_union_of_reach` below is the repair.  Both corners lie in
`T i ε = reachSet (Â_i) w ∩ MaxEnv.shell (Â_∞) vJ1 nJ cJ ε` (`ShellMink.lean:507`), hence
are reachable from `Â_i` along `w` *and* from `Â_∞` along `vJ1`; whichever direction `n`
does not favour, that sweep caps `⟪n, ·⟫`.

* `⟪n, w⟫ ≤ 0` — take `Y := Â_i`; `hdom` is `face`'s own maximality (`dom_self`).  Free.
* `0 < ⟪n, w⟫` — by §21's `recovered_of_sweep_deleted_dot` (`:2609`) these are `J` itself
  and `Â_∞`'s wedge polar cone.  For the polar cone take `Y := Â_∞` and `⟪n, vJ1⟫ ≤ 0`;
  `hdom` then says `⟪n, ·⟫`'s supremum over `Â_∞` is already attained on the finite level
  `Â_i`.  **Not free**: that is a stabilisation-in-`i` claim, and it is what `shellEnv`'s
  own `∃ i₀, ∀ i ≥ i₀` is for.  It is still strictly weaker than `:500-504` (one-sided,
  and about attainment rather than about consecutive levels), and since `E ↑S` is finite
  (`finite_E_of_finite`) a single `i₀` serves every polar-cone normal at once.
* `n = J` — the bottom face `[p, q]` at least as long as `face ↑S J`.  Not free either;
  §14's `exists_eps_corner_lattice` (`:1456`) and §15's `bottom_span_ge` (`:1545`) are the
  tools, and `ε` is existentially quantified in `shellEnv` so it may be taken large.

Those last two, plus "the cut introduces no new edge direction", are the whole residue of
`shellEnv` once this section is in place. -/

namespace Nivat.LaneCdFaceFree

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35

variable {α : Type*}

/-- **`Â_i` is `E(𝒮_φ)`-enveloped**, from `maxA` and the `Env` pin alone. -/
theorem enveloped_hatOf (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)) (i : ℕ) :
    Enveloped (↑S : Set (ℤ × ℤ)) (hatOf A kk vl i) := by
  have h : EnvOf (↑S : Set (ℤ × ℤ)) (A i) := by
    have := envA_of_max maxA i; rwa [hEnv] at this
  exact envOf_iff.mp (envOf_shift_mem (↑S : Set (ℤ × ℤ)) ((kk i : ℤ) • vl) (A i) h)

/-- **Every edge normal of `𝒮_φ` is an edge normal of `Â_i`, with a face at least as long.**
This is the `hEU` / `hface` input §17's `enveloped_of_two_corners` asks for, at `X := Â_i`. -/
theorem mem_E_and_face_encard_le_hatOf (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)) (i : ℕ)
    {n : ℤ × ℤ} (hn : n ∈ E (↑S : Set (ℤ × ℤ))) :
    n ∈ E (hatOf A kk vl i) ∧
      (face (↑S : Set (ℤ × ℤ)) n).encard ≤ (face (hatOf A kk vl i) n).encard := by
  have henv := enveloped_hatOf η xper vl S Env B A u kk hEnv maxA i
  have hfinE : (E (↑S : Set (ℤ × ℤ))).Finite := finite_E_of_finite S.finite_toSet
  refine ⟨?_, Enveloped.face_encard_le hfinE henv hn⟩
  rw [Enveloped.E_eq hfinE henv]
  exact hn

/-- **The edge set is pinned, not merely contained.** -/
theorem E_hatOf_eq (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)) (i : ℕ) :
    E (hatOf A kk vl i) = E (↑S : Set (ℤ × ℤ)) :=
  Enveloped.E_eq (finite_E_of_finite S.finite_toSet)
    (enveloped_hatOf η xper vl S Env B A u kk hEnv maxA i)

/-- **Two corners reachable from `Y` along a direction `n` does not favour cannot shorten
`A`'s face**, provided `A`'s face already dominates `Y`. -/
theorem face_subset_face_union_of_reach {A Y : Set (ℤ × ℤ)} {v n p q : ℤ × ℤ}
    (hp : p ∈ reachSet Y v) (hq : q ∈ reachSet Y v) (hnv : dot n v ≤ 0)
    (hdom : ∀ g ∈ Y, ∀ y ∈ face A n, dot n g ≤ dot n y) :
    face A n ⊆ face (A ∪ {p, q}) n := by
  have step : ∀ r ∈ reachSet Y v, ∀ z ∈ face A n, dot n r ≤ dot n z := by
    rintro r ⟨g, hg, t, rfl⟩ z hz
    have hstep : dot n (g + (t : ℤ) • v) = dot n g + (t : ℤ) * dot n v := by
      rw [dot_add, Nivat.ColleReg.dot_zsmul_right]
    have h1 := hdom g hg z hz
    have h2 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    rw [hstep]
    nlinarith
  intro z hz
  refine ⟨Or.inl hz.1, ?_⟩
  rintro y (hy | hy)
  · exact hz.2 y hy
  · rcases hy with rfl | hy
    · exact step y hp z hz
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact step y hq z hz

/-- `hdom` is free when `Y := A`: it is exactly `face`'s own maximality. -/
theorem dom_self {A : Set (ℤ × ℤ)} {n : ℤ × ℤ} :
    ∀ g ∈ A, ∀ y ∈ face A n, dot n g ≤ dot n y :=
  fun g hg _ hy => hy.2 g hg

/-- **The sweep-averse normals.**  For every `n ∈ E ↑S` with `⟪n, w⟫ ≤ 0`, the two corners
leave `Â_i`'s face intact, so the free bound transports to `X := Â_i ∪ {p, q}` — which is
`hface`'s exact shape.  No input beyond `maxA` and `hEnv`. -/
theorem face_encard_le_union_of_dot_w_nonpos (η xper : Config α) (vl : ℤ × ℤ)
    (S : Finset (ℤ × ℤ)) (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ))
    (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)) (i : ℕ)
    {w p q : ℤ × ℤ} (hp : p ∈ reachSet (hatOf A kk vl i) w)
    (hq : q ∈ reachSet (hatOf A kk vl i) w)
    {n : ℤ × ℤ} (hn : n ∈ E (↑S : Set (ℤ × ℤ))) (hnw : dot n w ≤ 0) :
    n ∈ E (hatOf A kk vl i ∪ {p, q}) ∧
      (face (↑S : Set (ℤ × ℤ)) n).encard ≤
        (face (hatOf A kk vl i ∪ {p, q}) n).encard := by
  obtain ⟨hnE, hle⟩ :=
    mem_E_and_face_encard_le_hatOf η xper vl S Env B A u kk hEnv maxA i hn
  have hsub := face_subset_face_union_of_reach (A := hatOf A kk vl i) hp hq hnw dom_self
  exact ⟨⟨hnE.1, hnE.2.mono hsub⟩, hle.trans (Set.encard_mono hsub)⟩

/-- **The wedge polar-cone normals, against the attainment hypothesis.**  `hdom` says
`⟪n, ·⟫`'s supremum over `Y := Â_∞` is already reached on the finite level `Â_i`.  That
hypothesis is the residue; everything else is discharged. -/
theorem face_encard_le_union_of_dom (η xper : Config α) (vl : ℤ × ℤ)
    (S : Finset (ℤ × ℤ)) (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ))
    (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)) (i : ℕ)
    {Y : Set (ℤ × ℤ)} {v p q : ℤ × ℤ} (hp : p ∈ reachSet Y v) (hq : q ∈ reachSet Y v)
    {n : ℤ × ℤ} (hn : n ∈ E (↑S : Set (ℤ × ℤ))) (hnv : dot n v ≤ 0)
    (hdom : ∀ g ∈ Y, ∀ y ∈ face (hatOf A kk vl i) n, dot n g ≤ dot n y) :
    n ∈ E (hatOf A kk vl i ∪ {p, q}) ∧
      (face (↑S : Set (ℤ × ℤ)) n).encard ≤
        (face (hatOf A kk vl i ∪ {p, q}) n).encard := by
  obtain ⟨hnE, hle⟩ :=
    mem_E_and_face_encard_le_hatOf η xper vl S Env B A u kk hEnv maxA i hn
  have hsub := face_subset_face_union_of_reach (A := hatOf A kk vl i) hp hq hnv hdom
  exact ⟨⟨hnE.1, hnE.2.mono hsub⟩, hle.trans (Set.encard_mono hsub)⟩

/-- **The assembly step.**  `hkey` (the three normal classes above) and `hEsub` (the cut
introduces no new edge direction, `b3_colle2.txt:518-520`) are the whole residue of
`shellEnv`; every other hypothesis is either a binder of `ofPartsExhaustsInter` or already
proved in this file (§3 `shellInter_finite_of_level`, §18 `sweep_cut_subset_latHull`). -/
theorem enveloped_of_corners_of_key
    (S : Finset (ℤ × ℤ)) (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl : ℤ × ℤ) (i : ℕ)
    {Tset : Set (ℤ × ℤ)} {p q : ℤ × ℤ}
    (hAfin : (hatOf A kk vl i).Finite) (hTfin : Tset.Finite)
    (hlcT : IsLatticeConvexRegion Tset) (hAT : hatOf A kk vl i ⊆ Tset)
    (hp : p ∈ Tset) (hq : q ∈ Tset)
    (hcover : Tset ⊆ latHull (hatOf A kk vl i ∪ {p, q}))
    (hkey : ∀ n ∈ E (↑S : Set (ℤ × ℤ)),
      n ∈ E (hatOf A kk vl i ∪ {p, q}) ∧
        (face (↑S : Set (ℤ × ℤ)) n).encard ≤
          (face (hatOf A kk vl i ∪ {p, q}) n).encard)
    (hEsub : E (hatOf A kk vl i ∪ {p, q}) ⊆ E (↑S : Set (ℤ × ℤ))) :
    Enveloped (↑S : Set (ℤ × ℤ)) Tset := by
  have hEeq : E (hatOf A kk vl i ∪ {p, q}) = E (↑S : Set (ℤ × ℤ)) :=
    Set.Subset.antisymm hEsub fun n hn => (hkey n hn).1
  refine Nivat.LaneCdSubstrip.enveloped_of_two_corners hAfin hTfin hlcT hAT hp hq hcover
    (fun n hn => hEsub hn) (fun n hn => (hkey n (hEsub hn)).2) ?_
  rw [hEeq]

end Nivat.LaneCdFaceFree

#print axioms Nivat.LaneCdFaceFree.enveloped_hatOf
#print axioms Nivat.LaneCdFaceFree.mem_E_and_face_encard_le_hatOf
#print axioms Nivat.LaneCdFaceFree.E_hatOf_eq
#print axioms Nivat.LaneCdFaceFree.face_subset_face_union_of_reach
#print axioms Nivat.LaneCdFaceFree.dom_self
#print axioms Nivat.LaneCdFaceFree.face_encard_le_union_of_dot_w_nonpos
#print axioms Nivat.LaneCdFaceFree.face_encard_le_union_of_dom
#print axioms Nivat.LaneCdFaceFree.enveloped_of_corners_of_key

/-! ## §23.  `hEsub`: the cut introduces no new edge direction

Added 2026-09-23 (lane-chaindata-lead).

§22's `enveloped_of_corners_of_key` has two residual hypotheses.  This section discharges
the second, `hEsub : E (Â_i ∪ {p, q}) ⊆ E ↑S`.

The content is a trichotomy on the sign of `⟪n, u⟫`, not a geometric assumption:

* `⟪n, u⟫ < 0` — both corners lie in `reachSet A u`, so a corner in `n`'s face must have
  sweep parameter `t = 0`, i.e. lie in `A` itself.  The whole face is then inside `A` and
  `n ∈ E A`.
* `⟪n, u⟫ = 0` — `n` and `n₀` both annihilate `u ≠ 0`, so `n = ± n₀`.
* `⟪n, u⟫ > 0` — one `u`-step out of `A` is already inside `latHull X`, so no point of `A`
  can maximise `⟪n, ·⟫`; the face is the cut segment `{p, q}`, and `n` and `m` both
  annihilate `q - p ≠ 0`, so `n = ± m`.

At the call site `u := w = -v_{ℓ_{J+1}}`, `n₀ = ± n_{ℓ_{J+1}}`, `m := n_J = -J`, and
`E ↑𝒮_φ` is closed under negation (`DecompData.E_Sphi_eq`, `ShellMink.lean:1755`), so all
five outcomes land in `E ↑𝒮_φ` — which is `b3_colle2.txt:518-520`'s count.

**Why `hstep` is available, and what it costs `ε`.**  §18's `sweep_cut_subset_latHull`
(`ShellSubStrip.lean:1835`) gives `reachSet A u ∩ halfPlaneGE m c ⊆ latHull (A ∪ {p,q})`,
so `z + u ∈ latHull X` as soon as `⟪m, z + u⟫ ≥ c`.  With `⟪m, z⟫ ≥ c_J` on `A` and
`c = c_J - ε` that needs `ε ≥ -⟪n_J, w⟫ = |⟪n_J, w⟫|` — **not** merely `0 < ε`.  `ε` is
existentially quantified in `shellEnv`, so this is a legitimate choice, but it is a real
lower bound on `ε` and has to be honoured jointly with the bottom-face leaf, which also
wants `ε` large.

**Numeric receipt / why the shell intersection is load-bearing (硬规矩 6).**  Take
`𝒮_φ := S8` (§20's octagon, `m = 4`), `A := S8`, `w := (0,-1)`, cut at `z.2 ≥ -3`.  The two
`w`-rays from `S8`'s bottom silhouette `(-1,-2)`, `(1,-2)` land at `p := (-1,-3)`,
`q := (1,-3)`.  Then `⟪(-1,-1), p⟫ = 4` beats `S8`'s maximum `3`, so
`face (S8 ∪ {p,q}) (-1,-1) = {p}` is a single point and `(-1,-1) ∉ E (S8 ∪ {p,q})` even
though `(-1,-1) ∈ E S8`.  That is §20's refutation again, and it is *not* a counterexample
to `shellEnv`: this configuration has `Â_∞ = Â_i`, so the `MaxEnv.shell (⋃ hatOf) vJ1 nJ cJ ε`
factor of `shellInter` (`ShellMink.lean:507`) imposes nothing.  In the faithful
`(ℓ, ℓ_J)`-region setting (`b3_colle2.txt:506`) that factor caps `⟪n, ·⟫` by `Â_∞`'s own
supremum whenever `⟪n, vJ1⟫ ≤ 0`, which is exactly §22's `face_encard_le_union_of_dom`.
So the two hypotheses of `enveloped_of_corners_of_key` are not independent slack: dropping
the shell factor makes both of them false at once. -/

namespace Nivat.LaneCdEsub

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35

/-- Two points of the same face have equal `n`-value. -/
theorem dot_sub_eq_zero_of_mem_face {X : Set (ℤ × ℤ)} {n a b : ℤ × ℤ}
    (ha : a ∈ face X n) (hb : b ∈ face X n) : dot n (b - a) = 0 := by
  have h1 := ha.2 b hb.1
  have h2 := hb.2 a ha.1
  have : dot n (b - a) = dot n b - dot n a := by
    cases n; cases a; cases b; simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring
  omega

/-- A face point of `X = A ∪ {p, q}` that lies in `A` is a face point of `A`. -/
theorem face_inter_subset_face {A : Set (ℤ × ℤ)} {n p q : ℤ × ℤ} :
    face (A ∪ {p, q}) n ∩ A ⊆ face A n := by
  rintro z ⟨⟨-, hmax⟩, hzA⟩
  exact ⟨hzA, fun y hy => hmax y (Or.inl hy)⟩

/-- **The dichotomy.**  Either `n` was already an edge normal of `A`, or its face at `n`
contains one of the two corners together with a distinct point of `X` — which pins `n`
perpendicular to that difference. -/
theorem mem_E_or_corner_direction {A : Set (ℤ × ℤ)} {n p q : ℤ × ℤ}
    (hn : n ∈ E (A ∪ {p, q})) :
    n ∈ E A ∨
      (∃ y ∈ A ∪ ({p, q} : Set (ℤ × ℤ)), y ≠ p ∧ dot n (y - p) = 0) ∨
      (∃ y ∈ A ∪ ({p, q} : Set (ℤ × ℤ)), y ≠ q ∧ dot n (y - q) = 0) := by
  obtain ⟨a, ha, b, hb, hab⟩ := hn.2
  by_cases haA : a ∈ A
  · by_cases hbA : b ∈ A
    · refine Or.inl ⟨hn.1, ⟨a, face_inter_subset_face ⟨ha, haA⟩, b,
        face_inter_subset_face ⟨hb, hbA⟩, hab⟩⟩
      -- both endpoints survive into `face A n`
    · rcases hb.1 with h | h
      · exact absurd h hbA
      · rcases h with rfl | h
        · exact Or.inr (Or.inl ⟨a, ha.1, fun hc => hab (hc ▸ rfl),
            dot_sub_eq_zero_of_mem_face hb ha⟩)
        · rw [Set.mem_singleton_iff] at h
          subst h
          exact Or.inr (Or.inr ⟨a, ha.1, fun hc => hab (hc ▸ rfl),
            dot_sub_eq_zero_of_mem_face hb ha⟩)
  · rcases ha.1 with h | h
    · exact absurd h haA
    · rcases h with rfl | h
      · exact Or.inr (Or.inl ⟨b, hb.1, fun hc => hab hc.symm,
          dot_sub_eq_zero_of_mem_face ha hb⟩)
      · rw [Set.mem_singleton_iff] at h
        subst h
        exact Or.inr (Or.inr ⟨b, hb.1, fun hc => hab hc.symm,
          dot_sub_eq_zero_of_mem_face ha hb⟩)

/-- Two integer normals annihilating the same nonzero vector are parallel. -/
theorem det_eq_zero_of_dot_eq_zero {n n' v : ℤ × ℤ} (hv : v ≠ 0)
    (h : dot n v = 0) (h' : dot n' v = 0) : det n n' = 0 := by
  obtain ⟨n1, n2⟩ := n
  obtain ⟨n1', n2'⟩ := n'
  obtain ⟨v1, v2⟩ := v
  simp only [dot] at h h'
  simp only [det]
  have e1 : (n1 * n2' - n2 * n1') * v1 = n2' * (n1 * v1 + n2 * v2) - n2 * (n1' * v1 + n2' * v2) := by
    ring
  have e2 : (n1 * n2' - n2 * n1') * v2 = n1 * (n1' * v1 + n2' * v2) - n1' * (n1 * v1 + n2 * v2) := by
    ring
  rw [h, h'] at e1 e2
  have hv' : v1 ≠ 0 ∨ v2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (Prod.ext hc.1 hc.2)
  rcases hv' with hz | hz
  · exact by simpa using mul_eq_zero.mp (by omega : (n1 * n2' - n2 * n1') * v1 = 0)
      |>.resolve_right hz
  · exact by simpa using mul_eq_zero.mp (by omega : (n1 * n2' - n2 * n1') * v2 = 0)
      |>.resolve_right hz

/-- **No point of `A` survives in the face of a normal that favours the sweep**, once one
`u`-step out of `A` is already covered by `latHull X` — at the call site that is
§18 plus `ε ≥ |⟪n_J, w⟫|`, see the header. -/
theorem face_inter_eq_empty_of_dot_pos {A : Set (ℤ × ℤ)} {u n p q : ℤ × ℤ}
    (hnu : 0 < dot n u)
    (hstep : ∀ z ∈ A, z + u ∈ latHull (A ∪ {p, q})) :
    face (A ∪ {p, q}) n ∩ A = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro hzf hzA
  have hle : dot n (z + u) ≤ dot n z := dot_le_of_mem_latHull hzf.2 (hstep z hzA)
  rw [dot_add] at hle
  omega

/-- **`hEsub`, the classification.**  Every edge normal of `X = A ∪ {p, q}` is an edge normal
of `A`, or `± n₀` (perpendicular to the sweep), or `± m` (the cut normal).  At the call site
`n₀ = ± n_{ℓ_{J+1}}` and `m = n_J = -J`, and `E ↑𝒮_φ` is closed under negation, so all three
land in `E ↑𝒮_φ` (`b3_colle2.txt:518-520`). -/
theorem mem_E_or_eq_n₀_or_eq_m {A : Set (ℤ × ℤ)} {u m n₀ p q n : ℤ × ℤ} {c : ℤ}
    (hu : u ≠ 0) (hn₀u : dot n₀ u = 0) (hn₀ : Primitive n₀) (hm : Primitive m)
    (hpc : dot m p = c) (hqc : dot m q = c)
    (hp : p ∈ reachSet A u) (hq : q ∈ reachSet A u)
    (hstep : ∀ z ∈ A, z + u ∈ latHull (A ∪ {p, q}))
    (hn : n ∈ E (A ∪ {p, q})) :
    n ∈ E A ∨ n = n₀ ∨ n = -n₀ ∨ n = m ∨ n = -m := by
  have hnprim : Primitive n := prim_iff_primitive.mp hn.1
  rcases lt_trichotomy (dot n u) 0 with hlt | heq | hgt
  · -- the sweep-averse case: both corners collapse into `A`
    refine Or.inl ⟨hn.1, ?_⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hn.2
    have key : ∀ y ∈ face (A ∪ {p, q}) n, y ∈ A := by
      intro y hy
      rcases hy.1 with h | h
      · exact h
      · -- `y` is a corner; being in the face forces its sweep parameter to vanish
        have hyr : y ∈ reachSet A u := by
          rcases h with rfl | h
          · exact hp
          · rw [Set.mem_singleton_iff] at h; subst h; exact hq
        obtain ⟨g, hg, t, rfl⟩ := hyr
        have hgle := hy.2 g (Or.inl hg)
        have hstepv : dot n (g + (t : ℤ) • u) = dot n g + (t : ℤ) * dot n u := by
          rw [dot_add, Nivat.ColleReg.dot_zsmul_right]
        have ht0 : (t : ℤ) = 0 := by
          by_contra hc
          have : (0 : ℤ) < (t : ℤ) := lt_of_le_of_ne (Int.natCast_nonneg t) (Ne.symm hc)
          nlinarith
        have : (g + (t : ℤ) • u) = g := by
          have : t = 0 := by exact_mod_cast ht0
          subst this; simp
        rw [this]; exact hg
    exact ⟨a, face_inter_subset_face ⟨ha, key a ha⟩, b,
      face_inter_subset_face ⟨hb, key b hb⟩, hab⟩
  · -- perpendicular to the sweep: `n ∥ n₀`
    have hdet : det n₀ n = 0 := det_eq_zero_of_dot_eq_zero hu hn₀u heq
    rcases eq_or_eq_neg_of_det_eq_zero hn₀ hnprim hdet with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · -- favours the sweep: the face is the cut segment, so `n ∥ m`
    have hempty := face_inter_eq_empty_of_dot_pos hgt hstep
    obtain ⟨a, ha, b, hb, hab⟩ := hn.2
    have hcorner : ∀ y ∈ face (A ∪ {p, q}) n, y = p ∨ y = q := by
      intro y hy
      rcases hy.1 with h | h
      · exact absurd (Set.mem_inter hy h)
          (by rw [hempty]; exact Set.notMem_empty y)
      · rcases h with rfl | h
        · exact Or.inl rfl
        · rw [Set.mem_singleton_iff] at h; exact Or.inr h
    have hma : dot m a = c := by rcases hcorner a ha with rfl | rfl; exacts [hpc, hqc]
    have hmb : dot m b = c := by rcases hcorner b hb with rfl | rfl; exacts [hpc, hqc]
    have hnsub : dot n (b - a) = 0 := dot_sub_eq_zero_of_mem_face ha hb
    have hmsub : dot m (b - a) = 0 := by
      have : dot m (b - a) = dot m b - dot m a := by
        cases m; cases a; cases b; simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring
      omega
    have hba : b - a ≠ 0 := sub_ne_zero_of_ne (Ne.symm hab)
    have hdet : det m n = 0 := det_eq_zero_of_dot_eq_zero hba hmsub hnsub
    rcases eq_or_eq_neg_of_det_eq_zero hm hnprim hdet with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- **`hEsub` itself.**  With `E A = E ↑S` (§22's `E_hatOf_eq`) and the three cut-relevant
normals landing in `E ↑S`, the classification closes `enveloped_of_corners_of_key`'s second
residual hypothesis. -/
theorem E_union_subset {A : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {u m n₀ p q : ℤ × ℤ} {c : ℤ}
    (hu : u ≠ 0) (hn₀u : dot n₀ u = 0) (hn₀ : Primitive n₀) (hm : Primitive m)
    (hpc : dot m p = c) (hqc : dot m q = c)
    (hp : p ∈ reachSet A u) (hq : q ∈ reachSet A u)
    (hstep : ∀ z ∈ A, z + u ∈ latHull (A ∪ {p, q}))
    (hEA : E A = E (↑S : Set (ℤ × ℤ)))
    (hn₀S : n₀ ∈ E (↑S : Set (ℤ × ℤ))) (hn₀S' : -n₀ ∈ E (↑S : Set (ℤ × ℤ)))
    (hmS : m ∈ E (↑S : Set (ℤ × ℤ))) (hmS' : -m ∈ E (↑S : Set (ℤ × ℤ))) :
    E (A ∪ {p, q}) ⊆ E (↑S : Set (ℤ × ℤ)) := by
  intro n hn
  rcases mem_E_or_eq_n₀_or_eq_m (c := c) hu hn₀u hn₀ hm hpc hqc hp hq hstep hn with
    h | h | h | h | h
  · rw [← hEA]; exact h
  · exact h ▸ hn₀S
  · exact h ▸ hn₀S'
  · exact h ▸ hmS
  · exact h ▸ hmS'

end Nivat.LaneCdEsub

#print axioms Nivat.LaneCdEsub.dot_sub_eq_zero_of_mem_face
#print axioms Nivat.LaneCdEsub.face_inter_subset_face
#print axioms Nivat.LaneCdEsub.mem_E_or_corner_direction
#print axioms Nivat.LaneCdEsub.det_eq_zero_of_dot_eq_zero
#print axioms Nivat.LaneCdEsub.face_inter_eq_empty_of_dot_pos
#print axioms Nivat.LaneCdEsub.mem_E_or_eq_n₀_or_eq_m
#print axioms Nivat.LaneCdEsub.E_union_subset



#print axioms Nivat.LaneCdSubstrip.mem_face_of_adjacent_endpoint_ccw
#print axioms Nivat.LaneCdSubstrip.mem_face_of_adjacent_endpoint_ccw_eq
#print axioms Nivat.LaneCdSubstrip.mem_face_of_adjacent_endpoint_cw
#print axioms Nivat.LaneCdSubstrip.mem_face_of_adjacent_endpoint_cw_eq

#print axioms Nivat.LaneCdSubstrip.real_smul_of_dot_eq_zero
#print axioms Nivat.LaneCdSubstrip.toReal_ray_mem
#print axioms Nivat.LaneCdSubstrip.eventually_mem_of_between_parallel_rays

#print axioms Nivat.LaneCdSubstrip.w_eq_vl_of_vJ1_eq_nl
#print axioms Nivat.LaneCdSubstrip.dot_nl_vJ1_nonneg
#print axioms Nivat.LaneCdSubstrip.w_eq_vl_or_dot_nl_w_neg
#print axioms Nivat.LaneCdSubstrip.sweep_param_le
#print axioms Nivat.LaneCdSubstrip.shellInter_finite_of_level
#print axioms Nivat.LaneCdSubstrip.subset_shellInter_of_halfPlane
#print axioms Nivat.LaneCdSubstrip.shellSubStrip_of_w_eq_vl
#print axioms Nivat.LaneCdSubstrip.shellSubStrip_of_w_eq_vl_of_max
#print axioms Nivat.LaneCdSubstrip.nl_eq_dir_vl
#print axioms Nivat.LaneCdSubstrip.refute_vl10_violates_hlJ
#print axioms Nivat.LaneCdSubstrip.refute_vl10_violates_vJ1
#print axioms Nivat.LaneCdSubstrip.refute_vl1neg1_violates_vJ1
#print axioms Nivat.LaneCdSubstrip.refuting_config_not_reachable
#print axioms Nivat.LaneCdSubstrip.shellSubStrip_of_bounded_check
#print axioms Nivat.LaneCdSubstrip.shell_zero_eq_iUnion
#print axioms Nivat.LaneCdSubstrip.eq_J_of_sweeps_pos
#print axioms Nivat.LaneCdSubstrip.sweeps_pos_at_J
#print axioms Nivat.LaneCdSubstrip.sweeps_nonpos_of_ne_J
#print axioms Nivat.LaneCdSubstrip.exists_mem_level_between
#print axioms Nivat.LaneCdSubstrip.level_between_needs_steps
#print axioms Nivat.LaneCdSubstrip.exists_step_in_face
#print axioms Nivat.LaneCdSubstrip.reachSet_eq_hrep
#print axioms Nivat.LaneCdSubstrip.reachSet_eq_hrep_of_E
#print axioms Nivat.LaneCdSubstrip.E_cut_needs_lattice_corner
#print axioms Nivat.LaneCdSubstrip.E_cut_nontrivial_faces_insufficient
#print axioms Nivat.LaneCdSubstrip.dvd_of_ray_hits_level
#print axioms Nivat.LaneCdSubstrip.exists_step_to_level
#print axioms Nivat.LaneCdSubstrip.exists_eps_corner_lattice
#print axioms Nivat.LaneCdSubstrip.eps_one_fails
#print axioms Nivat.LaneCdSubstrip.exists_bottom_span
#print axioms Nivat.LaneCdSubstrip.bottom_span_eq
#print axioms Nivat.LaneCdSubstrip.bottom_span_ge
#print axioms Nivat.LaneCdSubstrip.bottom_span_instance
#print axioms Nivat.LaneCdSubstrip.face_subset_face_reachSet_inter
#print axioms Nivat.LaneCdSubstrip.mem_E_reachSet_inter
#print axioms Nivat.LaneCdSubstrip.encard_face_le_reachSet_inter

#print axioms Nivat.LaneCdSubstrip.latHull_mono
#print axioms Nivat.LaneCdSubstrip.latHull_eq_of_sandwich
#print axioms Nivat.LaneCdSubstrip.E_eq_of_sandwich
#print axioms Nivat.LaneCdSubstrip.face_subset_of_sandwich
#print axioms Nivat.LaneCdSubstrip.enveloped_of_sandwich
#print axioms Nivat.LaneCdSubstrip.enveloped_of_two_corners
#print axioms Nivat.LaneCdSubstrip.sq2_subset_latHull_punct
#print axioms Nivat.LaneCdSubstrip.enveloped_sq1_sq2_via_sandwich
#print axioms Nivat.LaneCdSubstrip.eq_of_zdot_eq
#print axioms Nivat.LaneCdSubstrip.sweep_cut_subset_latHull
#print axioms Nivat.LaneCdSubstrip.cover_instance_nonvacuous
#print axioms Nivat.LaneCdSubstrip.cover_needs_extremal_corner
#print axioms Nivat.LaneCdSubstrip.exists_dot_gt_of_mem_reachSet
#print axioms Nivat.LaneCdSubstrip.notMem_E_reachSet_of_dot_pos


#print axioms Nivat.LaneCdM4.finite_S8
#print axioms Nivat.LaneCdM4.mem_E_S8_neg11
#print axioms Nivat.LaneCdM4.mem_E_S8_01
#print axioms Nivat.LaneCdM4.mem_E_S8_0neg1
#print axioms Nivat.LaneCdM4.mem_E_S8_10
#print axioms Nivat.LaneCdM4.mem_E_S8_neg10
#print axioms Nivat.LaneCdM4.mem_E_S8_11
#print axioms Nivat.LaneCdM4.mem_E_S8_1neg1
#print axioms Nivat.LaneCdM4.mem_E_S8_neg1pos1
#print axioms Nivat.LaneCdM4.card_N8
#print axioms Nivat.LaneCdM4.eight_normals_subset_E_S8
#print axioms Nivat.LaneCdM4.E_B_subset
#print axioms Nivat.LaneCdM4.enveloped_Ahat
#print axioms Nivat.LaneCdM4.mono_Ahat
#print axioms Nivat.LaneCdM4.Ahat_x_ge
#print axioms Nivat.LaneCdM4.Ahat_y_ge
#print axioms Nivat.LaneCdM4.Ahat_hhp
#print axioms Nivat.LaneCdM4.mem_Ahat_col
#print axioms Nivat.LaneCdM4.mem_Ahat_low
#print axioms Nivat.LaneCdM4.mem_T
#print axioms Nivat.LaneCdM4.face_T_subset
#print axioms Nivat.LaneCdM4.notMem_E_T
#print axioms Nivat.LaneCdM4.Ahat_subset_T
#print axioms Nivat.LaneCdM4.mem_E_Ahat_neg11
#print axioms Nivat.LaneCdM4.not_enveloped_T
#print axioms Nivat.LaneCdM4.shellEnv_false_at_m_four


#print axioms Nivat.LaneCdFan.recovered_of_sweep_deleted
#print axioms Nivat.LaneCdFan.dot_neg_dir
#print axioms Nivat.LaneCdFan.recovered_of_sweep_deleted_dot
#print axioms Nivat.LaneCdFan.fan_receipt_arcs
#print axioms Nivat.LaneCdFan.fan_receipt_count


/-!
# §24 `lane-cd-facet`: the sandwich's `hface` must be stated at `T`, not at `X`

**Signature bug found by lane-hroom-close (2026-09-23).**  §17's `enveloped_of_sandwich`
(`ShellSubStrip.lean:1689`) states its face-length hypothesis at the generating set `X`:

    hface : ∀ n ∈ E X, (face U n).encard ≤ (face X n).encard

and then relays it to `T` through `face_subset_of_sandwich` (`:1681`).  That relay uses only the
inclusion `face X n ⊆ face T n`, so the `X`-form is *sufficient but strictly stronger* than what
`Enveloped U T` actually consumes, which is the `T`-form.

At `X := Â_i ∪ {p, q}` and `n := J` the two forms are genuinely different, and the `X`-form is
**false**.  `hhp` puts all of `Â_i` in `halfPlaneGE nJ cJ` while the two cut corners `p, q` sit on
`dot nJ · = cJ - ε` with `ε > 0`, so with `J = -nJ` every point of `Â_i` has *strictly smaller*
`dot J` than `p` and `q`.  Hence `face X J = {p, q}` exactly, of `encard` 2, however far apart
`p` and `q` are — the intermediate lattice points of the segment are not in `X`.  The `X`-form
would therefore demand `(face ↑𝒮_φ J).encard ≤ 2`, and no such bound exists: `𝒮_φ` is an
arbitrary finite lattice-convex carrier and its `J`-edge can be arbitrarily long.

The `T`-form is the right one and is provable: `T` *is* lattice convex and does contain the
`k + 1` intermediate lattice points, which is exactly what makes §15's span argument
(`bottom_span_ge`, `:1544`, "`ε` big ⟹ `L + M ≤ k`") mean something.  `encard_face_ge_of_span`
below is the bridge from the span `k` to the face length, and it is the piece that was missing.

**Why this is a strict improvement, not a trade.**  `enveloped_of_sandwich` follows from
`enveloped_of_sandwich_faceT` by one `Set.encard_mono (face_subset_of_sandwich ..)`, so §22's
already-proved `X`-side bounds (`face_encard_le_union_of_dot_w_nonpos`,
`face_encard_le_union_of_dom`) keep working verbatim; only the `n = J` leaf changes shape.

**Numeric instance** (硬规矩 6), continuing §14/§15's data: `nJ = (0,1)`, `J = (0,-1)`,
`eJ = (1,0)`, `p = (-3,-6)`, `q = (7,-6)`, so `q = p + 10 • eJ` and `k = 10`.  `dot J eJ = 0`,
`dot J p = 6`, and every point of `Â_i` has `dot nJ ≥ cJ = 0` i.e. `dot J ≤ 0 < 6`.  The
`X`-form gives `face X J = {p, q}`, `encard = 2`.  The `T`-form gives the eleven lattice points
`(-3,-6), (-2,-6), …, (7,-6)`, `encard = 11 = k + 1`.  §15's `bottom_span_ge` with `L = 5`
delivers `5 + M ≤ 10`, so `M ≤ 5 ≤ 11`: the face-length clause passes with room, and it passes
*only* in the `T`-form.
-/


namespace Nivat.LaneCdFaceT

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.LaneCdSubstrip

/-! ### The repaired sandwich -/

/-- **`Enveloped U T` from a generating set `X`, with the face-length clause stated at `T`.**
Identical to `enveloped_of_sandwich` (`ShellSubStrip.lean:1689`) except that `hface` speaks about
`face T n`; that is the form `Enveloped` consumes, and it is strictly weaker than the `X`-form
(compose with `face_subset_of_sandwich` to recover the old statement). -/
theorem enveloped_of_sandwich_faceT {U X T : Set (ℤ × ℤ)} (hX : X.Finite) (hT : T.Finite)
    (hlcT : IsLatticeConvexRegion T) (h1 : X ⊆ T) (h2 : T ⊆ latHull X)
    (hEU : ∀ n ∈ E X, n ∈ E U)
    (hface : ∀ n ∈ E X, (face U n).encard ≤ (face T n).encard)
    (hcard : (E X).encard = (E U).encard) :
    Enveloped U T := by
  have hE : E T = E X := E_eq_of_sandwich hX hT h1 h2
  refine ⟨⟨hlcT, fun n hn => ?_⟩, ?_⟩
  · rw [hE] at hn
    exact ⟨hEU n hn, hface n hn⟩
  · rw [hE]; exact hcard

/-- The old `X`-form really is the special case: this reproves
`enveloped_of_sandwich` from the repaired one, so nothing downstream is lost. -/
theorem enveloped_of_sandwich_faceX {U X T : Set (ℤ × ℤ)} (hX : X.Finite) (hT : T.Finite)
    (hlcT : IsLatticeConvexRegion T) (h1 : X ⊆ T) (h2 : T ⊆ latHull X)
    (hEU : ∀ n ∈ E X, n ∈ E U)
    (hface : ∀ n ∈ E X, (face U n).encard ≤ (face X n).encard)
    (hcard : (E X).encard = (E U).encard) :
    Enveloped U T :=
  enveloped_of_sandwich_faceT hX hT hlcT h1 h2 hEU
    (fun n hn => (hface n hn).trans (Set.encard_mono (face_subset_of_sandwich h1 h2 n)))
    hcard

/-- **`enveloped_of_two_corners` with the face-length clause at `T`.**  The `n = J` leaf of
`shellEnv` is stated against this, not against `ShellSubStrip.lean:1704`. -/
theorem enveloped_of_two_corners_faceT {U A T : Set (ℤ × ℤ)} {p q : ℤ × ℤ}
    (hAfin : A.Finite) (hT : T.Finite) (hlcT : IsLatticeConvexRegion T)
    (hA : A ⊆ T) (hp : p ∈ T) (hq : q ∈ T)
    (hcover : T ⊆ latHull (A ∪ {p, q}))
    (hEU : ∀ n ∈ E (A ∪ {p, q}), n ∈ E U)
    (hface : ∀ n ∈ E (A ∪ {p, q}), (face U n).encard ≤ (face T n).encard)
    (hcard : (E (A ∪ {p, q})).encard = (E U).encard) :
    Enveloped U T := by
  refine enveloped_of_sandwich_faceT (hAfin.union ((Set.finite_singleton q).insert p))
    hT hlcT ?_ hcover hEU hface hcard
  rintro z (hz | hz)
  · exact hA hz
  · rcases hz with rfl | hz
    · exact hp
    · rw [Set.mem_singleton_iff] at hz; subst hz; exact hq

/-! ### The span-to-face-length bridge -/

/-- A lattice-convex region containing `p` and `p + k • e` contains every intermediate lattice
point `p + j • e`, `j ≤ k`.  This is where lattice convexity of `T` is actually spent: the
generating set `A ∪ {p, q}` does **not** contain these points. -/
theorem mem_of_latticeConvex_span {T : Set (ℤ × ℤ)} {p e : ℤ × ℤ} {k j : ℕ}
    (hlcT : IsLatticeConvexRegion T) (hp : p ∈ T) (hq : p + (k : ℤ) • e ∈ T) (hjk : j ≤ k) :
    p + (j : ℤ) • e ∈ T := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · have hj : j = 0 := Nat.le_zero.mp hjk
    subst hj
    simpa using hp
  obtain ⟨C, hconv, -, hTC⟩ := hlcT
  subst hTC
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hjk' : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
  have ha : (0 : ℝ) ≤ ((k : ℝ) - j) / k := div_nonneg (by linarith) hk0.le
  have hb : (0 : ℝ) ≤ (j : ℝ) / k := div_nonneg (Nat.cast_nonneg j) hk0.le
  have hab : ((k : ℝ) - j) / k + (j : ℝ) / k = 1 := by field_simp; ring
  have key := hconv hp hq ha hb hab
  show toReal (p + (j : ℤ) • e) ∈ C
  have heq : toReal (p + (j : ℤ) • e)
      = (((k : ℝ) - j) / k) • toReal p + ((j : ℝ) / k) • toReal (p + (k : ℤ) • e) := by
    rw [Prod.ext_iff]
    constructor <;>
      · simp only [toReal, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul]
        push_cast
        field_simp
        ring
  rw [heq]
  exact key

/-- **Span ⟹ face length.**  If `T` is lattice convex, contains `p` and `p + k • e`, the
direction `e` is `n`-neutral and nonzero, and `p` maximises `dot n` on `T`, then the `n`-face of
`T` has at least `k + 1` points.  Together with §15's `bottom_span_ge` this is the `n = J` leaf
of `shellEnv`'s face-length clause. -/
theorem encard_face_ge_of_span {T : Set (ℤ × ℤ)} {n e p : ℤ × ℤ} {k : ℕ}
    (hlcT : IsLatticeConvexRegion T) (hp : p ∈ T) (hq : p + (k : ℤ) • e ∈ T)
    (he : e ≠ 0) (hne : dot n e = 0) (hmax : ∀ z ∈ T, dot n z ≤ dot n p) :
    ((k : ℕ∞) + 1) ≤ (face T n).encard := by
  classical
  have hinj : ∀ i j : ℕ, p + (i : ℤ) • e = p + (j : ℤ) • e → i = j := by
    intro i j h
    have h1 : ((i : ℤ) - j) • e = 0 := by
      have := add_left_cancel h
      rw [sub_smul, this, sub_self]
    rcases smul_eq_zero.mp h1 with h2 | h2
    · have : (i : ℤ) = j := by omega
      exact_mod_cast this
    · exact absurd h2 he
  set F : Finset (ℤ × ℤ) := (Finset.range (k + 1)).image (fun j : ℕ => p + (j : ℤ) • e) with hF
  have hcard : F.card = k + 1 := by
    rw [hF, Finset.card_image_of_injOn (fun i _ j _ h => hinj i j h), Finset.card_range]
  have hsub : (↑F : Set (ℤ × ℤ)) ⊆ face T n := by
    intro z hz
    rw [hF, Finset.coe_image, Set.mem_image] at hz
    obtain ⟨j, hj, rfl⟩ := hz
    rw [Finset.coe_range, Set.mem_Iio] at hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
    have hmem : p + (j : ℤ) • e ∈ T := mem_of_latticeConvex_span hlcT hp hq hjk
    have hdot : dot n (p + (j : ℤ) • e) = dot n p := by
      rw [dot_add, Nivat.PolyChainSum.dot_zsmul_right, hne, mul_zero, add_zero]
    exact ⟨hmem, fun y hy => by rw [hdot]; exact hmax y hy⟩
  calc ((k : ℕ∞) + 1) = (F.card : ℕ∞) := by rw [hcard]; push_cast; ring
    _ = (↑F : Set (ℤ × ℤ)).encard := (Set.encard_coe_eq_coe_finsetCard F).symm
    _ ≤ (face T n).encard := Set.encard_mono hsub

/-! ### Why the `X`-form is not merely inconvenient but false at `n = J` -/

/-- **Two strictly-outermost points swallow the face.**  If `p` and `q` share an `n`-level and
every point of `A` is strictly below it, then `face (A ∪ {p, q}) n` is exactly `{p, q}` — the
span between `p` and `q` is invisible, because the intermediate lattice points are not in the
set.  This is lane-hroom-close's observation, made kernel-checked. -/
theorem face_union_pair_eq_pair {A : Set (ℤ × ℤ)} {n p q : ℤ × ℤ}
    (hqp : dot n q = dot n p) (hA : ∀ z ∈ A, dot n z < dot n p) :
    face (A ∪ {p, q}) n = {p, q} := by
  have hmem : ∀ y ∈ A ∪ ({p, q} : Set (ℤ × ℤ)), dot n y ≤ dot n p := by
    rintro y (hy | hy)
    · exact (hA y hy).le
    · rcases hy with rfl | hy
      · exact le_rfl
      · rw [Set.mem_singleton_iff] at hy; subst hy; exact hqp.le
  apply Set.eq_of_subset_of_subset
  · rintro z ⟨hzA, hzmax⟩
    rcases hzA with hz | hz
    · exact absurd (hzmax p (Or.inr (Or.inl rfl))) (not_le.mpr (hA z hz))
    · exact hz
  · rintro z (rfl | hz)
    · exact ⟨Or.inr (Or.inl rfl), hmem⟩
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨Or.inr (Or.inr rfl), fun y hy => hqp ▸ hmem y hy⟩

/-- A three-point `J`-face: `(face ↑S J).encard` has **no** `≤ 2` bound, so the `X`-form's
`n = J` obligation `(face U J).encard ≤ (face (A ∪ {p, q}) J).encard = 2` is unprovable in
general.  Here `J = (0, -1)` and `S` is a flat three-point edge at height `0`. -/
def flatEdge : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (2, 0)}

theorem mem_flatEdge_snd {z : ℤ × ℤ} (hz : z ∈ (↑flatEdge : Set (ℤ × ℤ))) : z.2 = 0 := by
  simp only [flatEdge, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl <;> rfl

theorem face_flatEdge : face (↑flatEdge : Set (ℤ × ℤ)) (0, -1) = ↑flatEdge := by
  apply Set.eq_of_subset_of_subset (face_subset _ _)
  intro z hz
  exact ⟨hz, fun y hy => by simp [dot, mem_flatEdge_snd hz, mem_flatEdge_snd hy]⟩

theorem encard_face_flatEdge : (face (↑flatEdge : Set (ℤ × ℤ)) (0, -1)).encard = 3 := by
  rw [face_flatEdge, Set.encard_coe_eq_coe_finsetCard]
  rfl

end Nivat.LaneCdFaceT

#print axioms Nivat.LaneCdFaceT.enveloped_of_sandwich_faceT
#print axioms Nivat.LaneCdFaceT.enveloped_of_sandwich_faceX
#print axioms Nivat.LaneCdFaceT.enveloped_of_two_corners_faceT
#print axioms Nivat.LaneCdFaceT.mem_of_latticeConvex_span
#print axioms Nivat.LaneCdFaceT.encard_face_ge_of_span
#print axioms Nivat.LaneCdFaceT.face_union_pair_eq_pair
#print axioms Nivat.LaneCdFaceT.face_flatEdge
#print axioms Nivat.LaneCdFaceT.encard_face_flatEdge


/-!
# §25 `lane-cd-facet`: what `hlcT` actually costs at the `shellEnv` call site

`shellEnv` (`ChainExhaustInter.lean`) asks for
`Env (shellInter Â_i (shell Â_∞ vJ1 nJ cJ ε) w)` with `Env = EnvOf ↑S`, and `Enveloped`'s first
conjunct is `IsLatticeConvexRegion`.  So `shellEnv` **contains** a lattice-convexity claim about
the shell, and §22's `enveloped_of_corners_of_key` takes it as the hypothesis `hlcT`.  That
hypothesis is not bookkeeping, and this section prices it.

**`hlcT` decomposes into two sweep-convexity facts** (`isLatticeConvexRegion_shellInter`):

1. `IsLatticeConvexRegion (reachSet Â_i w)` — the **finite level** swept by the transverse `w`;
2. `IsLatticeConvexRegion (reachSet Â_∞ vJ1)` — this is exactly `RegionConvex.lean`'s already
   isolated `hreach` side condition, with `EdgeJ1Data.isLatticeConvexRegion_reachSet`
   (`RegionConvex.lean:450`) as one producer.

Everything else (the `ε`-dependence, the `shellInter` intersection) is two closure lemmas:
lattice convexity is closed under intersection (`isLatticeConvexRegion_inter`) and the shell is
its sweep cut by one half-plane (`isLatticeConvexRegion_shell_of_reach`, same mechanism as
`ChainDataWithShell.isLatticeConvexRegion_shellInf_of_reach`, `RegionConvex.lean:110`).

**(1) is new and unowned, and it does not follow from lattice convexity of `Â_i`.**
`RegionSweep.lean:32-55` names the obstruction: sweeping preserves lattice convexity exactly
under `LevelInterval C w` (`RegionSweep.lean:174`, "every integer between two attained
`det w`-levels of `C` is attained"), which is a condition on `C` *relative to `w`*, not a
consequence of convexity.

**Numeric instance** (硬规矩 6).  `K = {(0,0), (1,2)}` is lattice convex: the open real segment
between the two points contains no lattice point (the direction `(1,2)` is primitive), so `K` is
the full lattice-point set of its own real hull.  Sweep by `w = (1,0)`:

    reachSet K (1,0) = {(t, 0) : t ∈ ℕ} ∪ {(1 + t, 2) : t ∈ ℕ} .

Now `(0,0)` and `(2,2)` both lie in it (`(2,2) = (1,2) + 1 • (1,0)`), and `(0,0) + (2,2) =
(1,1) + (1,1)`, so lattice convexity would force `(1,1) ∈ reachSet K (1,0)` — but every element
has second coordinate `0` or `2`.  Hence `reachSet K (1,0)` is **not** lattice convex
(`not_isLatticeConvexRegion_reachSet_pair`).  In `det w`-terms this is the level gap
`RegionSweep.lean:52-55` measures: `det (1,0) z = z.2`, so `K`'s levels are `{0, 2}` and level
`1` is skipped.

So whoever finally discharges `shellEnv` owes a reason why the real `Â_i` — a maximal enveloped
region, not a two-point segment — has no such level gap against the transverse `w`.  Recorded
here rather than silently assumed inside the assembly.

**⚠ 2026-09-23, §34 below: this split is dead.**  `not_reachSet_latticeConvex_of_edge_direction`
refutes obligation (1) under every abstract property of `(Â_i, w, n_J, c_J)` this section can
see, with `Â_i` full-dimensional *and* `w` an edge direction of `Â_i` itself, and shows the
band cut does not repair it for any `ε`.  `isLatticeConvexRegion_shellInter` below is still a
true theorem; it is its first hypothesis that has no producer.  See §34 for the diagnosis
(the debt is `LevelInterval Â_i w`, which `RegionSweep.lean:32-55` records as necessary as well
as sufficient) and `tmp/wip/lane-cd-levelseg.lean` for the cheapest known route to supplying it.
-/


namespace Nivat.LaneCdHlc

open Nivat Nivat.LE2 Nivat.MaxEnv

/-! ### Two closure lemmas -/

/-- Lattice convexity is closed under intersection: intersect the two witnessing real convex
closed sets. -/
theorem isLatticeConvexRegion_inter {A B : Set (ℤ × ℤ)}
    (hA : IsLatticeConvexRegion A) (hB : IsLatticeConvexRegion B) :
    IsLatticeConvexRegion (A ∩ B) := by
  obtain ⟨CA, hcA, hclA, rfl⟩ := hA
  obtain ⟨CB, hcB, hclB, rfl⟩ := hB
  exact ⟨CA ∩ CB, hcA.inter hcB, hclA.inter hclB, (Set.preimage_inter).symm⟩

/-- The `ε`-shell of `Â_∞` is lattice convex as soon as its underlying sweep is: the only
`ε`-dependence is one half-plane cut.  Same mechanism as
`ChainDataWithShell.isLatticeConvexRegion_shellInf_of_reach` (`RegionConvex.lean:110`), stated
against the raw `MaxEnv.shell` that `ofPartsExhaustsInter` binds. -/
theorem isLatticeConvexRegion_shell_of_reach {Ainf : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} {ε : ℕ}
    (hreach : IsLatticeConvexRegion (reachSet Ainf v)) :
    IsLatticeConvexRegion (MaxEnv.shell Ainf v n c ε) := by
  rw [MaxEnv.shell_eq_reach_inter]
  exact isLatticeConvexRegion_inter_halfPlaneGE hreach _ _

/-- **`hlcT`, decomposed.**  Exactly two sweep-convexity inputs; see the section docstring for
which of them already has a producer. -/
theorem isLatticeConvexRegion_shellInter {Ahat Ainf : Set (ℤ × ℤ)} {w v n : ℤ × ℤ} {c : ℤ}
    {ε : ℕ}
    (hreachA : IsLatticeConvexRegion (reachSet Ahat w))
    (hreachInf : IsLatticeConvexRegion (reachSet Ainf v)) :
    IsLatticeConvexRegion (Nivat.ShellMink.shellInter Ahat (MaxEnv.shell Ainf v n c ε) w) :=
  isLatticeConvexRegion_inter hreachA (isLatticeConvexRegion_shell_of_reach hreachInf)

/-! ### The sweep-convexity input is a genuine extra hypothesis -/

/-- `{(0,0), (1,2)}` is lattice convex — the primitive direction leaves no interior lattice
point. -/
theorem isLatticeConvexRegion_pair :
    IsLatticeConvexRegion ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} : Set (ℤ × ℤ)) := by
  refine ⟨{p : ℝ × ℝ | p.2 = 2 * p.1 ∧ 0 ≤ p.1 ∧ p.1 ≤ 1}, ?_, ?_, ?_⟩
  · rintro x ⟨hx1, hx2, hx3⟩ y ⟨hy1, hy2, hy3⟩ a b ha hb hab
    refine ⟨?_, ?_, ?_⟩ <;>
      · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        nlinarith [ha, hb, hab]
  · have he : {p : ℝ × ℝ | p.2 = 2 * p.1 ∧ 0 ≤ p.1 ∧ p.1 ≤ 1}
        = {p : ℝ × ℝ | p.2 = 2 * p.1} ∩
          ({p : ℝ × ℝ | 0 ≤ p.1} ∩ {p : ℝ × ℝ | p.1 ≤ 1}) := by
      ext p; simp [Set.mem_inter_iff]
    rw [he]
    exact (isClosed_eq continuous_snd (by fun_prop)).inter
      ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_fst continuous_const))
  · ext z
    constructor
    · rintro (rfl | hz)
      · exact ⟨by simp [toReal], by simp [toReal], by simp [toReal]⟩
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨by simp [toReal], by simp [toReal], by simp [toReal]⟩
    · rintro ⟨h1, h2, h3⟩
      simp only [toReal] at h1 h2 h3
      have h1' : z.2 = 2 * z.1 := by exact_mod_cast h1
      have h2' : (0 : ℤ) ≤ z.1 := by exact_mod_cast h2
      have h3' : z.1 ≤ 1 := by exact_mod_cast h3
      have hcase : z.1 = 0 ∧ z.2 = 0 ∨ z.1 = 1 ∧ z.2 = 2 := by omega
      rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl (Prod.ext ha hb)
      · exact Or.inr (Set.mem_singleton_iff.mpr (Prod.ext ha hb))

/-- Local copy of `Colle43.latticeConvexRegion_midpoint` (`Claim43.lean:268`), which is not in
this file's import closure: a lattice-convex region containing `a` and `b` contains any `c` with
`a + b = c + c`. -/
theorem midpoint_mem {K : Set (ℤ × ℤ)} (hK : IsLatticeConvexRegion K)
    {a b c : ℤ × ℤ} (ha : a ∈ K) (hb : b ∈ K) (habc : a + b = c + c) : c ∈ K := by
  obtain ⟨C, hconv, -, hKeq⟩ := hK
  rw [hKeq] at ha hb ⊢
  have hmem := hconv ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have e : (1 / 2 : ℝ) • toReal a + (1 / 2 : ℝ) • toReal b = toReal c := by
    rw [Prod.ext_iff]
    have h1 : a.1 + b.1 = c.1 + c.1 := congrArg Prod.fst habc
    have h2 : a.2 + b.2 = c.2 + c.2 := congrArg Prod.snd habc
    have h1' : (a.1 : ℝ) + b.1 = (c.1 : ℝ) + c.1 := by exact_mod_cast h1
    have h2' : (a.2 : ℝ) + b.2 = (c.2 : ℝ) + c.2 := by exact_mod_cast h2
    constructor <;>
      · simp only [toReal, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul]
        linarith
  rwa [e] at hmem

/-- **Sweeping a lattice-convex set need not stay lattice convex.**  `(0,0)` and `(2,2)` are in
the sweep, their midpoint `(1,1)` is not — every element has second coordinate `0` or `2`. -/
theorem not_isLatticeConvexRegion_reachSet_pair :
    ¬ IsLatticeConvexRegion
        (reachSet ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} : Set (ℤ × ℤ)) ((1 : ℤ), (0 : ℤ))) := by
  intro hK
  have hsnd : ∀ z ∈ reachSet ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} : Set (ℤ × ℤ))
      ((1 : ℤ), (0 : ℤ)), z.2 = 0 ∨ z.2 = 2 := by
    rintro z ⟨g, hg, t, rfl⟩
    rcases hg with rfl | hg
    · left; simp
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      right; simp
  have h0 : ((0 : ℤ), (0 : ℤ)) ∈ reachSet ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} :
      Set (ℤ × ℤ)) ((1 : ℤ), (0 : ℤ)) := ⟨(0, 0), by simp, 0, by simp⟩
  have h2 : ((2 : ℤ), (2 : ℤ)) ∈ reachSet ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} :
      Set (ℤ × ℤ)) ((1 : ℤ), (0 : ℤ)) := ⟨(1, 2), by simp, 1, by simp⟩
  have hmid := midpoint_mem hK h0 h2
    (c := ((1 : ℤ), (1 : ℤ))) (by decide)
  rcases hsnd _ hmid with h | h <;> simp at h

end Nivat.LaneCdHlc

#print axioms Nivat.LaneCdHlc.isLatticeConvexRegion_inter
#print axioms Nivat.LaneCdHlc.isLatticeConvexRegion_shell_of_reach
#print axioms Nivat.LaneCdHlc.isLatticeConvexRegion_shellInter
#print axioms Nivat.LaneCdHlc.not_isLatticeConvexRegion_reachSet_pair
#print axioms Nivat.LaneCdHlc.isLatticeConvexRegion_pair
#print axioms Nivat.LaneCdHlc.midpoint_mem


/-! ## §26.  The `faceT` repair of §22's assembly step

Lane `lane-chaindata-lead`, 2026-09-23.

§24 (`ShellSubStrip.lean:3199-3364`) showed that the `X`-form face-length clause
`hface : ∀ n ∈ E X, (face U n).encard ≤ (face X n).encard` is **strictly too strong**: at
`n = J` the generating set `X := Â_i ∪ {p, q}` has `face X J = {p, q}` exactly
(`LaneCdFaceT.face_union_pair_eq_pair`, `ShellSubStrip.lean:3330`), so the `X`-form demands
`(face ↑𝒮_φ J).encard ≤ 2`, which no hypothesis supplies and which
`LaneCdFaceT.encard_face_flatEdge` (`ShellSubStrip.lean:3355`) refutes outright.

§22's `enveloped_of_corners_of_key` (`ShellSubStrip.lean:2800`) still routes through the old
`X`-form via `LaneCdSubstrip.enveloped_of_two_corners` (`ShellSubStrip.lean:1704`), so its
`hkey` hypothesis inherits the same defect: `hkey`'s second component is unprovable at `n = J`.
This section supplies the repaired assembly, built on §24's
`enveloped_of_two_corners_faceT` (`ShellSubStrip.lean:3235`).

## The division of labour this makes possible

The point of `key_faceT_of_split` is that the two sides of the case split are proved by
different lanes against different set-forms, and neither has to move:

* `n ≠ J` — the `X`-form bounds already proved in §22,
  `LaneCdFaceFree.face_encard_le_union_of_dot_w_nonpos` (`ShellSubStrip.lean:2755`) and
  `LaneCdFaceFree.face_encard_le_union_of_dom` (`ShellSubStrip.lean:2780`), are **true** at
  these normals and are consumed unchanged.  `faceT_of_faceX` weakens them to the `T`-form
  one `Set.encard_mono` at a time, so no §22 proof is touched.
* `n = J` — `LaneHroomFaceJ.faceJ_encard_le` (lane-hroom-close, 2026-09-23) proves the
  `T`-form directly, via §15's `bottom_span_ge` (`ShellSubStrip.lean:1545`) and §24's
  `encard_face_ge_of_span` (`ShellSubStrip.lean:3288`).  It never mentions `X`.

So the `X`-form is retained exactly where it is true, and the `T`-form is used exactly where
it is needed.  This is the "state the assumption on the consumed set" rule of
`NOTE.md:1-12` applied at the assembly level rather than at the leaf.

## Numeric instance (硬规矩6)

Continuing §14/§15/§24's data: `nJ = (0,1)`, `J = (0,-1)`, `eJ = (1,0)`, `p = (-3,-6)`,
`q = (7,-6)`, `k = 10`, and `Â_i ⊆ halfPlaneGE nJ cJ` with `cJ = 0`, so every `z ∈ Â_i` has
`dot J z = -z.2 ≤ 0 < 6 = dot J p`.  Then:

* `face X J = {p, q}`, `encard = 2` — the `X`-form would demand `(face ↑𝒮_φ J).encard ≤ 2`.
* `face T J ⊇ {p + j • eJ | j ≤ 10}`, `encard ≥ 11 = k + 1` — the `T`-form demands
  `(face ↑𝒮_φ J).encard ≤ 11`, which `bottom_span_ge` delivers by making `k` exceed
  `M = (face ↑𝒮_φ J).encard`.

At a normal `n ≠ J`, say `n = (1,0)`: `face X n` and `face T n` agree on the relevant
maximisers because `T ⊆ latHull X` (`face_subset_of_sandwich`, `ShellSubStrip.lean:1681`), so
routing the `X`-form bound through `faceT_of_faceX` loses nothing there.

Consumer: `shellEnv` (`ChainExhaustInter.lean`), feeding `RegionSteps.lean:1166`
`exists_chainData`.
-/


namespace Nivat.LaneCdKeyT

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.LaneCdSubstrip Nivat.LaneCdFaceT

variable {α : Type*}

/-! ### The `X`-to-`T` weakening -/

/-- **An `X`-form face bound implies the `T`-form one.**  One `Set.encard_mono` over
`face_subset_of_sandwich` (`ShellSubStrip.lean:1681`).  This is what lets every `X`-form
bound already proved in §22 be consumed by the repaired assembly without reproving it. -/
theorem faceT_of_faceX {U X T : Set (ℤ × ℤ)} (h1 : X ⊆ T) (h2 : T ⊆ latHull X)
    {n : ℤ × ℤ} (h : (face U n).encard ≤ (face X n).encard) :
    (face U n).encard ≤ (face T n).encard :=
  h.trans (Set.encard_mono (face_subset_of_sandwich h1 h2 n))

/-- **The case split that lets the `n ≠ J` and `n = J` leaves be proved against different
sets.**  Off `J` the `X`-form suffices and is weakened on the spot; at `J` the `T`-form is
taken as given. -/
theorem key_faceT_of_split {U X T : Set (ℤ × ℤ)} {J : ℤ × ℤ}
    (h1 : X ⊆ T) (h2 : T ⊆ latHull X)
    (hother : ∀ n ∈ E X, n ≠ J → (face U n).encard ≤ (face X n).encard)
    (hJ : (face U J).encard ≤ (face T J).encard) :
    ∀ n ∈ E X, (face U n).encard ≤ (face T n).encard := by
  intro n hn
  by_cases hnJ : n = J
  · subst hnJ; exact hJ
  · exact faceT_of_faceX h1 h2 (hother n hn hnJ)

/-! ### The repaired assembly -/

/-- **§22's `enveloped_of_corners_of_key`, with the face-length clause at `Tset`.**  Same
geometric hypotheses; `hkey` is split into its membership half (`hkeyE`, unchanged and still
`X`-side) and its face-length half, now stated at `Tset`.  The membership half is *not*
affected by §24's bug — `n ∈ E X` is what `hEsub` inverts, and the `flatEdge` witness says
nothing about it. -/
theorem enveloped_of_corners_of_key_faceT
    (S : Finset (ℤ × ℤ)) (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl : ℤ × ℤ) (i : ℕ)
    {Tset : Set (ℤ × ℤ)} {p q : ℤ × ℤ}
    (hAfin : (hatOf A kk vl i).Finite) (hTfin : Tset.Finite)
    (hlcT : IsLatticeConvexRegion Tset) (hAT : hatOf A kk vl i ⊆ Tset)
    (hp : p ∈ Tset) (hq : q ∈ Tset)
    (hcover : Tset ⊆ latHull (hatOf A kk vl i ∪ {p, q}))
    (hkeyE : ∀ n ∈ E (↑S : Set (ℤ × ℤ)), n ∈ E (hatOf A kk vl i ∪ {p, q}))
    (hfaceT : ∀ n ∈ E (hatOf A kk vl i ∪ {p, q}),
      (face (↑S : Set (ℤ × ℤ)) n).encard ≤ (face Tset n).encard)
    (hEsub : E (hatOf A kk vl i ∪ {p, q}) ⊆ E (↑S : Set (ℤ × ℤ))) :
    Enveloped (↑S : Set (ℤ × ℤ)) Tset := by
  have hEeq : E (hatOf A kk vl i ∪ {p, q}) = E (↑S : Set (ℤ × ℤ)) :=
    Set.Subset.antisymm hEsub hkeyE
  refine enveloped_of_two_corners_faceT hAfin hTfin hlcT hAT hp hq hcover
    (fun n hn => hEsub hn) hfaceT ?_
  rw [hEeq]

/-- **The end-to-end form.**  Exactly the shape the `shellEnv` wiring will call: the `n ≠ J`
face bounds are supplied `X`-side (so §22's lemmas plug in verbatim), the `n = J` bound is
supplied `T`-side (so lane-hroom-close's `faceJ_encard_le` plugs in verbatim), and the sandwich
inclusion `X ⊆ Tset` is reassembled here from `hAT`/`hp`/`hq` rather than being a hypothesis. -/
theorem enveloped_of_corners_split
    (S : Finset (ℤ × ℤ)) (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl : ℤ × ℤ) (i : ℕ)
    {Tset : Set (ℤ × ℤ)} {p q J : ℤ × ℤ}
    (hAfin : (hatOf A kk vl i).Finite) (hTfin : Tset.Finite)
    (hlcT : IsLatticeConvexRegion Tset) (hAT : hatOf A kk vl i ⊆ Tset)
    (hp : p ∈ Tset) (hq : q ∈ Tset)
    (hcover : Tset ⊆ latHull (hatOf A kk vl i ∪ {p, q}))
    (hkeyE : ∀ n ∈ E (↑S : Set (ℤ × ℤ)), n ∈ E (hatOf A kk vl i ∪ {p, q}))
    (hother : ∀ n ∈ E (hatOf A kk vl i ∪ {p, q}), n ≠ J →
      (face (↑S : Set (ℤ × ℤ)) n).encard ≤ (face (hatOf A kk vl i ∪ {p, q}) n).encard)
    (hJ : (face (↑S : Set (ℤ × ℤ)) J).encard ≤ (face Tset J).encard)
    (hEsub : E (hatOf A kk vl i ∪ {p, q}) ⊆ E (↑S : Set (ℤ × ℤ))) :
    Enveloped (↑S : Set (ℤ × ℤ)) Tset := by
  have hXT : hatOf A kk vl i ∪ {p, q} ⊆ Tset := by
    rintro z (hz | hz)
    · exact hAT hz
    · rcases hz with rfl | hz
      · exact hp
      · rw [Set.mem_singleton_iff] at hz; subst hz; exact hq
  exact enveloped_of_corners_of_key_faceT S A kk vl i hAfin hTfin hlcT hAT hp hq hcover hkeyE
    (key_faceT_of_split hXT hcover hother hJ) hEsub

end Nivat.LaneCdKeyT

#print axioms Nivat.LaneCdKeyT.faceT_of_faceX
#print axioms Nivat.LaneCdKeyT.key_faceT_of_split
#print axioms Nivat.LaneCdKeyT.enveloped_of_corners_of_key_faceT
#print axioms Nivat.LaneCdKeyT.enveloped_of_corners_split


/-! ## §27.  `shellEnv` at the real call site: what is free and what is left

Lane `lane-chaindata-lead`, 2026-09-23.

§22/§24/§26 built the assembly step against an abstract `Tset`.  This section instantiates it
at the concrete set `shellEnv` actually names — `ShellMink.shellInter Â_i (MaxEnv.shell Â_∞ vJ1
nJ cJ ε) w` (`ChainExhaustInter.lean`) — and discharges every hypothesis that the
binders of `ChainDataGeom.ofPartsExhaustsInter` (`ChainExhaustInter.lean`) already
supply.  The residue is then exactly the open content, with nothing free hiding inside it.

## What turned out to be free

Three of §22's seven geometric hypotheses are already theorems in the main tree, and are
discharged here rather than passed on:

* `hAfin : (hatOf A kk vl i).Finite` — literally the binder `hfin i`.
* `hTfin : (Tset i).Finite` — `ChainAsm.shellInterFinite_of` (`ChainAssembleInter.lean:98`),
  which needs `dot nJ w < 0`, i.e. the binder `hsweepW`, **not** `hsweep`.
* `hAT : hatOf A kk vl i ⊆ Tset i` — `ChainAsm.subShellInter_of`
  (`ChainAssembleInter.lean:106`), from the binder `hhp` alone.  Note this is where `ε` is
  spent harmlessly: `hhp` gives `dot nJ z ≥ cJ`, and the shell only asks `≥ cJ - ε`.

`Env`-vs-`Enveloped` is `Iff.rfl` (`LatticeEdges.lean:2435`), so the `hEnv` pin converts with
no content.  Neither `maxA` nor `η`/`xper`/`B`/`u` is needed at this step — they are spent
upstream, inside `hkeyE`/`hother` (§22's `face_encard_le_union_of_*`), not here.

## What is left

`hopen` below is the honest residue, per `i`:

1. `IsLatticeConvexRegion (Tset i)` — §25's decomposition
   (`LaneCdHlc.isLatticeConvexRegion_shellInter`, `ShellSubStrip.lean:3450`) reduces this to
   `IsLatticeConvexRegion (reachSet Â_i w)` plus `RegionConvex.lean`'s already-owned `hreach`.
   The first is **not** automatic — `LaneCdHlc.not_isLatticeConvexRegion_reachSet_pair`
   (`ShellSubStrip.lean:3465`) is a kernel witness that sweeping can destroy lattice
   convexity.  Assigned to lane-tower3, 2026-09-23.
2. `p, q ∈ Tset i` and `Tset i ⊆ latHull (Â_i ∪ {p, q})` — the bottom corners and the cover,
   §14's `exists_eps_corner_lattice` (`ShellSubStrip.lean:1454`) and §18's
   `sweep_cut_subset_latHull` (`ShellSubStrip.lean:1835`).  Both constrain `ε` from below, and
   those constraints must be honoured **jointly** (see the ε note below).
3. `hkeyE`/`hother` — §22, for the normals other than `J`.  `hother` is discharged by
   `LaneCdFaceFree.face_encard_le_union_of_dot_w_nonpos` (`ShellSubStrip.lean:2755`) and
   `face_encard_le_union_of_dom` (`:2780`); the latter's `hdom` is still open.
4. The `n = J` bound at `Tset i` — `LaneHroomFaceJ.faceJ_encard_le` (lane-hroom-close).
5. `hEsub` — §23 (`LaneCdEsub`).

## The `ε` joint lower bound (still unruled)

`ε` is quantified **once**, outside `i`, by `shellEnv`'s own `∃ ε i₀` shape.  At least two
independent lower bounds are known: §23's `ε ≥ |dot nJ w|` for `sweep_cut_subset_latHull`, and
§15/§24's span bound `M * |dot nprevJ eJ| * |dot nJ w| ≤ ε` reaching the `n = J` face length
(`bottom_span_ge`, `ShellSubStrip.lean:1545`).  Whoever finalises `bottom`'s signature must
take an explicit `max` of both rather than letting each leaf pick its own `ε`; this is
`OPEN.md` #9 (`∀ ε` vs `∃ ε₀, ∀ ε ≥ ε₀`) and is team-lead's call.  `shellEnv_of_open` below is
deliberately written with `ε` and `i₀` as *inputs*, so it composes with either resolution.

## Numeric instance (硬规矩6)

Continuing §14/§15/§24/§26: `nJ = (0,1)`, `w = (1,-1)`, `cJ = 0`, `ε = 6`.  Then
`dot nJ w = -1 < 0` (so `hsweepW` holds and `shellInterFinite_of` applies), and for
`z ∈ Â_i` we get `dot nJ z ≥ 0 > -6 = cJ - ε`, so `hAT` holds with room to spare — the `ε`
slack is never tight at this step, which is why `hAT` is free while `hcover` is not.
-/


namespace Nivat.LaneCdSite

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm
open Nivat.LaneCdSubstrip Nivat.LaneCdFaceT Nivat.LaneCdKeyT

/-- The set `shellEnv` names (`ChainExhaustInter.lean`), abbreviated. -/
def shellT (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl vJ1 nJ w : ℤ × ℤ) (cJ : ℤ) (ε i : ℕ) :
    Set (ℤ × ℤ) :=
  ShellMink.shellInter (hatOf A kk vl i)
    (MaxEnv.shell (⋃ j, hatOf A kk vl j) vJ1 nJ cJ ε) w

theorem shellT_eq (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl vJ1 nJ w : ℤ × ℤ) (cJ : ℤ)
    (ε i : ℕ) :
    shellT A kk vl vJ1 nJ w cJ ε i =
      ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ j, hatOf A kk vl j) vJ1 nJ cJ ε) w := rfl

/-! ### The three free hypotheses -/

/-- `hTfin` is free: `ChainAsm.shellInterFinite_of` from `hfin` and `hsweepW`. -/
theorem shellT_finite {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl vJ1 nJ w : ℤ × ℤ} {cJ : ℤ}
    (hfin : ∀ i, (hatOf A kk vl i).Finite) (hsweepW : dot nJ w < 0) (ε i : ℕ) :
    (shellT A kk vl vJ1 nJ w cJ ε i).Finite :=
  shellInterFinite_of (v := vJ1) (c := cJ) hfin hsweepW i ε

/-- `hAT` is free: `ChainAsm.subShellInter_of` from `hhp` alone.  The `ε` slack is not tight
here — `hhp` already gives `dot nJ z ≥ cJ ≥ cJ - ε`. -/
theorem hatOf_subset_shellT {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl vJ1 nJ w : ℤ × ℤ} {cJ : ℤ}
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ) (ε i : ℕ) :
    hatOf A kk vl i ⊆ shellT A kk vl vJ1 nJ w cJ ε i :=
  subShellInter_of (v := vJ1) (c := cJ) hhp w i ε

/-! ### The instantiated assembly -/

/-- **`Enveloped ↑𝒮_φ (Tset i)` at the real call site**, with every free hypothesis
discharged.  Compare `LaneCdKeyT.enveloped_of_corners_split` (`ShellSubStrip.lean:3654`): the
three hypotheses `hAfin`/`hTfin`/`hAT` have disappeared into `hfin`/`hsweepW`/`hhp`. -/
theorem enveloped_shellT
    {S : Finset (ℤ × ℤ)} {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl vJ1 nJ w : ℤ × ℤ} {cJ : ℤ}
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (hsweepW : dot nJ w < 0)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (ε i : ℕ) {p q J : ℤ × ℤ}
    (hlcT : IsLatticeConvexRegion (shellT A kk vl vJ1 nJ w cJ ε i))
    (hp : p ∈ shellT A kk vl vJ1 nJ w cJ ε i)
    (hq : q ∈ shellT A kk vl vJ1 nJ w cJ ε i)
    (hcover : shellT A kk vl vJ1 nJ w cJ ε i ⊆ latHull (hatOf A kk vl i ∪ {p, q}))
    (hkeyE : ∀ n ∈ E (↑S : Set (ℤ × ℤ)), n ∈ E (hatOf A kk vl i ∪ {p, q}))
    (hother : ∀ n ∈ E (hatOf A kk vl i ∪ {p, q}), n ≠ J →
      (face (↑S : Set (ℤ × ℤ)) n).encard ≤ (face (hatOf A kk vl i ∪ {p, q}) n).encard)
    (hJ : (face (↑S : Set (ℤ × ℤ)) J).encard ≤
      (face (shellT A kk vl vJ1 nJ w cJ ε i) J).encard)
    (hEsub : E (hatOf A kk vl i ∪ {p, q}) ⊆ E (↑S : Set (ℤ × ℤ))) :
    Enveloped (↑S : Set (ℤ × ℤ)) (shellT A kk vl vJ1 nJ w cJ ε i) :=
  enveloped_of_corners_split S A kk vl i (hfin i) (shellT_finite hfin hsweepW ε i) hlcT
    (hatOf_subset_shellT hhp ε i) hp hq hcover hkeyE hother hJ hEsub

/-- **`shellEnv`'s exact binder shape** (`ChainExhaustInter.lean`) from the residue.
`ε` and `i₀` are inputs, not outputs, so this composes with either resolution of `OPEN.md` #9.
Everything `ofPartsExhaustsInter` already carries is consumed here; `hopen` is the honest
remainder. -/
theorem shellEnv_of_open
    {S : Finset (ℤ × ℤ)} {Env : Set (ℤ × ℤ) → Prop}
    {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl vJ1 nJ w : ℤ × ℤ} {cJ : ℤ}
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (hsweepW : dot nJ w < 0)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (ε i₀ : ℕ) (hε : 0 < ε) (J : ℤ × ℤ)
    (hopen : ∀ i, i₀ ≤ i → ∃ p q : ℤ × ℤ,
      IsLatticeConvexRegion (shellT A kk vl vJ1 nJ w cJ ε i) ∧
      p ∈ shellT A kk vl vJ1 nJ w cJ ε i ∧
      q ∈ shellT A kk vl vJ1 nJ w cJ ε i ∧
      shellT A kk vl vJ1 nJ w cJ ε i ⊆ latHull (hatOf A kk vl i ∪ {p, q}) ∧
      (∀ n ∈ E (↑S : Set (ℤ × ℤ)), n ∈ E (hatOf A kk vl i ∪ {p, q})) ∧
      (∀ n ∈ E (hatOf A kk vl i ∪ {p, q}), n ≠ J →
        (face (↑S : Set (ℤ × ℤ)) n).encard ≤ (face (hatOf A kk vl i ∪ {p, q}) n).encard) ∧
      (face (↑S : Set (ℤ × ℤ)) J).encard ≤
        (face (shellT A kk vl vJ1 nJ w cJ ε i) J).encard ∧
      E (hatOf A kk vl i ∪ {p, q}) ⊆ E (↑S : Set (ℤ × ℤ))) :
    ∃ ε i₀, 0 < ε ∧ ∀ i, i₀ ≤ i →
      Env (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ j, hatOf A kk vl j) vJ1 nJ cJ ε) w) := by
  refine ⟨ε, i₀, hε, fun i hi => ?_⟩
  obtain ⟨p, q, hlcT, hp, hq, hcover, hkeyE, hother, hJ, hEsub⟩ := hopen i hi
  subst hEnv
  exact enveloped_shellT hfin hsweepW hhp ε i hlcT hp hq hcover hkeyE hother hJ hEsub

end Nivat.LaneCdSite

#print axioms Nivat.LaneCdSite.shellT_eq
#print axioms Nivat.LaneCdSite.shellT_finite
#print axioms Nivat.LaneCdSite.hatOf_subset_shellT
#print axioms Nivat.LaneCdSite.enveloped_shellT
#print axioms Nivat.LaneCdSite.shellEnv_of_open


/-! ## §28.  `hcover` and the two corners at the real call site

Lane `lane-chaindata-lead`, 2026-09-23.  Continues §27.

§27 reduced `shellEnv` to `hopen`, whose remaining geometric content is `hp`, `hq` and
`hcover`.  This section discharges `hcover` against the concrete
`shellT = ShellMink.shellInter Â_i (MaxEnv.shell Â_∞ vJ1 nJ cJ ε) w` (`ChainExhaustInter.lean`)
and reduces `hp`/`hq` to the two corner facts `bottom` already produces.

## The transverse normal is forced, and it makes `hdet` free

§18's `sweep_cut_subset_latHull` (`ShellSubStrip.lean:1835`) takes an auxiliary normal `n₀`
with `dot n₀ u = 0` (the direction along which the two corners are extremal) and demands
`det m n₀ ≠ 0`.  Here `u = w`, so `n₀` must be `w`-orthogonal, and the canonical such vector is
`dir w = (-w.2, w.1)` (`LatticeEdges.lean:248`), which satisfies `dot (dir w) w = 0` by
`dot_dir` plus symmetry of `dot`.

With that choice `hdet` is not a side condition at all:

```
det nJ (dir w) = nJ.1 * w.1 - nJ.2 * (-w.2) = nJ.1 * w.1 + nJ.2 * w.2 = dot nJ w
```

so `det nJ (dir w) ≠ 0` is *literally* the binder `hsweepW : dot nJ w < 0`
(`ChainExhaustInter.lean`).  `det_dir_eq_dot` below records the identity.  This is worth
stating explicitly because it removes the last hypothesis of §18 that looked like it might
need new geometry: `hdet` was the one place a degenerate `w` could have broken the cover
argument, and `hsweepW` already rules it out.

## Where `ε` enters, and where it does not

The cut level is `cJ - ε`, and `MaxEnv.shell_subset_halfPlaneGE` (`MaximalEnveloped.lean:597`)
gives `shell Â_∞ vJ1 nJ cJ ε ⊆ halfPlaneGE nJ (cJ - ε)` definitionally.  So the shell factor of
`shellT` is consumed purely as a half-plane and `vJ1` drops out of `hcover` entirely — the
cover argument never uses reachability along `vJ1`.  Contrast §27's `hAT`, where the `ε` slack
was also not tight.  `ε` is therefore *not* constrained by `hcover` itself; it is constrained
by whether corners `p`, `q` at level exactly `cJ - ε` **exist**, which is §14's
`exists_eps_corner_lattice` (`ShellSubStrip.lean:1454`) and is where the joint lower bound with
§23/§15 bites (`OPEN.md` #9, unruled).

## `Â_i` nonempty is an `i₀` condition, not a new obligation

§18 needs `Â_i.Nonempty`.  The binder list supplies only `ahat_nonempty : (⋃ i, Â_i).Nonempty`
(`ChainExhaustInter.lean`), which with `AhatMono` gives nonemptiness for all large `i` —
and `shellEnv`'s own shape is `∃ ε i₀, … ∀ i, i₀ ≤ i → …`, so this is exactly what `i₀` is for.
`exists_i₀_hatOf_nonempty` below extracts it.

## Numeric instance (硬规矩6)

Continuing §14/§15/§24/§26/§27: `nJ = (0,1)`, `w = (1,-1)`, `cJ = 0`, `ε = 6`.  Then
`dir w = (1,1)`, and:

* `dot (dir w) w = 1*1 + 1*(-1) = 0` ✓, so `hn₀u` holds.
* `det nJ (dir w) = 0*1 - 1*1 = -1`, and `dot nJ w = 0*1 + 1*(-1) = -1` ✓ — the two agree, and
  are nonzero exactly because `hsweepW` holds.
* The cut line is `dot nJ z = -6`, i.e. `z.2 = -6`, matching §24's corners `p = (-3,-6)`,
  `q = (7,-6)`: both at level `cJ - ε = -6` ✓, and separated along `eJ = (1,0)` by `k = 10`.
* `p` and `q` are `(dir w)`-extremal on `Â_i` in opposite senses: `dot (dir w) p = -9`,
  `dot (dir w) q = 1`, so `q` carries `suppVal` and `p` carries `-suppVal (-(dir w))`,
  consistent with §18's `hpmax`/`hqmin` once the labels are matched to orientation.

Consumer: §27's `shellEnv_of_open`, hence `shellEnv` (`ChainExhaustInter.lean`), hence
`RegionSteps.lean:1166` `exists_chainData`.
-/


namespace Nivat.LaneCdCover

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35
open Nivat.LaneCdSubstrip Nivat.LaneCdSite

/-! ### `hdet` is `hsweepW` -/

/-- **`det n (dir w) = dot n w`.**  Makes §18's `hdet` a restatement of `hsweepW`. -/
theorem det_dir_eq_dot (n w : ℤ × ℤ) : det n (dir w) = dot n w := by
  simp only [det, dir, dot]; ring

/-- `dir w` is `w`-orthogonal, in the argument order §18 wants. -/
theorem dot_dir_self (w : ℤ × ℤ) : dot (dir w) w = 0 := by
  simp only [dot, dir]; ring

/-! ### Nonemptiness is an `i₀` condition -/

/-- `ahat_nonempty` plus `AhatMono` give nonemptiness of `Â_i` for all large `i`. -/
theorem exists_i₀_hatOf_nonempty {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ}
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (hne : (⋃ j, hatOf A kk vl j).Nonempty) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → (hatOf A kk vl i).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp hz
  exact ⟨i₀, fun i hi => ⟨z, AhatMono i₀ i hi hi₀⟩⟩

/-! ### `hcover` -/

/-- **`hcover` at the real call site.**  The shell factor is consumed purely as the half-plane
`dot nJ · ≥ cJ - ε`, so `vJ1` plays no role; `hdet` is supplied by `det_dir_eq_dot` from
`hsweepW`. -/
theorem shellT_subset_latHull
    {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl vJ1 nJ w : ℤ × ℤ} {cJ : ℤ} {p q : ℤ × ℤ} {ε i : ℕ}
    (hAfin : (hatOf A kk vl i).Finite) (hAne : (hatOf A kk vl i).Nonempty)
    (hsweepW : dot nJ w < 0)
    (hpc : dot nJ p = cJ - (ε : ℤ))
    (hpmax : dot (dir w) p = suppVal (hatOf A kk vl i) (dir w))
    (hqc : dot nJ q = cJ - (ε : ℤ))
    (hqmin : dot (dir w) q = - suppVal (hatOf A kk vl i) (-(dir w))) :
    shellT A kk vl vJ1 nJ w cJ ε i ⊆ latHull (hatOf A kk vl i ∪ {p, q}) := by
  have hsub : shellT A kk vl vJ1 nJ w cJ ε i ⊆
      reachSet (hatOf A kk vl i) w ∩ Nivat.LE2.halfPlaneGE nJ (cJ - (ε : ℤ)) := by
    rintro z ⟨hreach, hshell⟩
    exact ⟨hreach, MaxEnv.shell_subset_halfPlaneGE hshell⟩
  refine hsub.trans ?_
  refine sweep_cut_subset_latHull hAfin hAne ?_ hsweepW (dot_dir_self w) hpc hpmax hqc hqmin
  rw [det_dir_eq_dot]
  omega

/-! ### `hp` / `hq` -/

/-- **Membership in `shellT` from the two facts `bottom` produces.**  A corner lies in
`shellT` as soon as it is `w`-reachable from `Â_i` and `vJ1`-reachable from `Â_∞` at level
`≥ cJ - ε`; the level condition is automatic for a corner sitting exactly on the cut line. -/
theorem mem_shellT_of_corner
    {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl vJ1 nJ w : ℤ × ℤ} {cJ : ℤ} {z : ℤ × ℤ} {ε i : ℕ}
    (hreach : z ∈ reachSet (hatOf A kk vl i) w)
    (hinf : z ∈ reachSet (⋃ j, hatOf A kk vl j) vJ1)
    (hlev : cJ - (ε : ℤ) ≤ dot nJ z) :
    z ∈ shellT A kk vl vJ1 nJ w cJ ε i := by
  obtain ⟨g, hg, t, rfl⟩ := hinf
  exact ⟨hreach, g, hg, t, rfl, hlev⟩

/-- The level side condition of `mem_shellT_of_corner` is free for a corner on the cut line. -/
theorem mem_shellT_of_corner_on_line
    {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl vJ1 nJ w : ℤ × ℤ} {cJ : ℤ} {z : ℤ × ℤ} {ε i : ℕ}
    (hreach : z ∈ reachSet (hatOf A kk vl i) w)
    (hinf : z ∈ reachSet (⋃ j, hatOf A kk vl j) vJ1)
    (hlev : dot nJ z = cJ - (ε : ℤ)) :
    z ∈ shellT A kk vl vJ1 nJ w cJ ε i :=
  mem_shellT_of_corner hreach hinf (le_of_eq hlev.symm)

end Nivat.LaneCdCover

#print axioms Nivat.LaneCdCover.det_dir_eq_dot
#print axioms Nivat.LaneCdCover.dot_dir_self
#print axioms Nivat.LaneCdCover.exists_i₀_hatOf_nonempty
#print axioms Nivat.LaneCdCover.shellT_subset_latHull
#print axioms Nivat.LaneCdCover.mem_shellT_of_corner
#print axioms Nivat.LaneCdCover.mem_shellT_of_corner_on_line


/-! ## §29.  The face clause splits on the sign of `⟪n, w⟫`

Lane `lane-chaindata-lead`, 2026-09-23.  Refines §26.

§26's `key_faceT_of_split` (`ShellSubStrip.lean:3600`) special-cased `n = J`.  That was the
right shape for consuming lane-hroom-close's leaf, but it is not the natural cut.  The natural
cut is the **sign of `dot n w`**, and it explains *why* `J` was the exceptional normal.

## Why the sign of `⟪n, w⟫` is the real dividing line

The corners satisfy `p, q ∈ reachSet Â_i w` (§28's `mem_shellT_of_corner`), so
`p = g + t • w` with `g ∈ Â_i` and `t : ℕ`, giving

```
dot n p = dot n g + t * dot n w.
```

* If `dot n w ≤ 0` the corners never exceed `Â_i`'s `n`-maximum, so
  `face Â_i n ⊆ face (Â_i ∪ {p, q}) n` and the free `X`-form bound transports.  This is exactly
  §22's `face_subset_face_union_of_reach` (`:2733`), whose `hdom` hypothesis is discharged by
  `dom_self` (`:2754`) once `Y := Â_i` — and at the real call site `Y` *is* `Â_i`, because that
  is where §28 reaches the corners from.  So for these normals **nothing is owed**:
  `face_encard_le_union_of_dot_w_nonpos` (`:2761`) already closes them.
* If `dot n w > 0` the corners can overshoot `Â_i`'s `n`-face, the inclusion fails, and the
  `X`-form bound is unavailable.  These are the normals that need the `T`-form.

`J` is in the second class, not by accident: `J = -nJ` and `hsweepW : dot nJ w < 0` give
`dot J w = - dot nJ w > 0`.  `dot_J_w_pos` below records this, which is the precise sense in
which §24's bug was about `J` and the precise sense in which it was not — `J` is merely the
first member of the `dot n w > 0` class to have been examined.

## What this changes about the residue

`key_faceT_of_wsign` replaces §26's `n = J` case split by the sign split, so the residue is no
longer "the normal `J`" but "the normals `n ∈ E (Â_i ∪ {p, q})` with `dot n w > 0`".
lane-hroom-close's `faceJ_encard_le` covers `n = J`.  Whether that is the whole class is
**open**: if `J` is the only element of `E (Â_i ∪ {p, q})` with `dot n w > 0`, then combining
her leaf with `only_J_of_pos` below closes the face clause outright.

`key_faceT_of_pos_unique` states that closure, so the remaining question is isolated as a
single hypothesis with no geometry attached to it.

## Numeric instance (硬规矩6)

Continuing §14/§15/§24/§26/§27/§28: `nJ = (0,1)`, `w = (1,-1)`, `J = (0,-1)`.  Then
`dot J w = 0*1 + (-1)*(-1) = 1 > 0` ✓, and `dot nJ w = -1 < 0` ✓, consistent with
`dot_J_w_pos`.  A normal in the other class, say `n = (-1,0)`: `dot n w = -1 ≤ 0`, so it is
closed for free by `face_encard_le_union_of_dot_w_nonpos`, and indeed the corners
`p = (-3,-6)`, `q = (7,-6)` have `dot n p = 3`, `dot n q = -7`, neither exceeding the
`n`-maximum of a `Â_i` sitting at `dot nJ ≥ 0`.

Consumer: §27's `shellEnv_of_open`, hence `shellEnv` (`ChainExhaustInter.lean`), hence
`RegionSteps.lean:1166` `exists_chainData`.
-/


namespace Nivat.LaneCdWSign

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35
open Nivat.LaneCdSubstrip Nivat.LaneCdFaceT Nivat.LaneCdKeyT

/-- **`J` is in the positive class.**  `dot J w > 0` is `hsweepW` read through `J = -nJ`. -/
theorem dot_J_w_pos {nJ w : ℤ × ℤ} (hsweepW : dot nJ w < 0) : 0 < dot (-nJ) w := by
  rw [dot_neg_left]; omega

/-- **The face clause splits on the sign of `⟪n, w⟫`.**  Off the positive class the `X`-form
suffices and is weakened on the spot; on it the `T`-form is taken as given. -/
theorem key_faceT_of_wsign {U X T : Set (ℤ × ℤ)} {w : ℤ × ℤ}
    (h1 : X ⊆ T) (h2 : T ⊆ latHull X)
    (hneg : ∀ n ∈ E X, dot n w ≤ 0 → (face U n).encard ≤ (face X n).encard)
    (hpos : ∀ n ∈ E X, 0 < dot n w → (face U n).encard ≤ (face T n).encard) :
    ∀ n ∈ E X, (face U n).encard ≤ (face T n).encard := by
  intro n hn
  by_cases h : dot n w ≤ 0
  · exact faceT_of_faceX h1 h2 (hneg n hn h)
  · exact hpos n hn (by omega)

/-- If `J` is the only positive-class normal, the positive class collapses to the single leaf
lane-hroom-close has already proved. -/
theorem only_J_of_pos {U X T : Set (ℤ × ℤ)} {w J : ℤ × ℤ}
    (huniq : ∀ n ∈ E X, 0 < dot n w → n = J)
    (hJ : (face U J).encard ≤ (face T J).encard) :
    ∀ n ∈ E X, 0 < dot n w → (face U n).encard ≤ (face T n).encard := by
  intro n hn hpos
  rw [huniq n hn hpos]
  exact hJ

/-- **The face clause, closed, modulo uniqueness of the positive-class normal.**  Every
hypothesis here except `huniq` is discharged: `hneg` by §22's
`face_encard_le_union_of_dot_w_nonpos`, `hJ` by lane-hroom-close's `faceJ_encard_le`. -/
theorem key_faceT_of_pos_unique {U X T : Set (ℤ × ℤ)} {w J : ℤ × ℤ}
    (h1 : X ⊆ T) (h2 : T ⊆ latHull X)
    (hneg : ∀ n ∈ E X, dot n w ≤ 0 → (face U n).encard ≤ (face X n).encard)
    (huniq : ∀ n ∈ E X, 0 < dot n w → n = J)
    (hJ : (face U J).encard ≤ (face T J).encard) :
    ∀ n ∈ E X, (face U n).encard ≤ (face T n).encard :=
  key_faceT_of_wsign h1 h2 hneg (only_J_of_pos huniq hJ)

end Nivat.LaneCdWSign

#print axioms Nivat.LaneCdWSign.dot_J_w_pos
#print axioms Nivat.LaneCdWSign.key_faceT_of_wsign
#print axioms Nivat.LaneCdWSign.only_J_of_pos
#print axioms Nivat.LaneCdWSign.key_faceT_of_pos_unique


/-! ## §30.  `J` is the only positive-class normal — the face clause closes

Lane `lane-chaindata-lead`, 2026-09-23.  Discharges §29's `huniq`.

§29 reduced the whole face-length clause of `shellEnv` to one hypothesis with no geometry
attached (`LaneCdWSign.key_faceT_of_pos_unique`):

```
huniq : ∀ n ∈ E (Â_i ∪ {p, q}), 0 < dot n w → n = J
```

This section proves it.  Nothing new is needed: §23's classification
(`LaneCdEsub.mem_E_or_eq_n₀_or_eq_m`, `ShellSubStrip.lean:2965`) already contains the argument
in its `0 < dot n u` branch, and all this does is isolate that branch and add the one sign
observation §23 had no reason to make.

## The argument

Let `n ∈ E X` with `0 < dot n w`, where `X = Â_i ∪ {p, q}`.

1. `LaneCdEsub.face_inter_eq_empty_of_dot_pos` (`:2950`) gives `face X n ∩ Â_i = ∅`: a point of
   `Â_i` in the face would be beaten by its own `w`-translate, which `hstep` keeps inside
   `latHull X`.  So `face X n ⊆ {p, q}`.
2. `n ∈ E X` forces `(face X n).Nontrivial`, so the face has two distinct points and must be
   `{p, q}` exactly, with `p ≠ q`.
3. Both corners sit on the cut line, so `dot m (q - p) = 0`; both lie in the same `n`-face, so
   `dot n (q - p) = 0` (`LaneCdEsub.dot_sub_eq_zero_of_mem_face`, `:2876`).
4. Two primitive vectors annihilating the same nonzero `q - p` are equal up to sign
   (`det_eq_zero_of_dot_eq_zero` `:2925` then `eq_or_eq_neg_of_det_eq_zero`): `n = ± m`.
5. **The new step.**  `n = m` is impossible: it would give `dot n w = dot m w < 0`,
   contradicting `0 < dot n w`.  Hence `n = -m`.

At the call site `m = nJ` and `J = -nJ`, and step 5's sign input is exactly the binder
`hsweepW : dot nJ w < 0` (`ChainExhaustInter.lean`).

## Consequence

With this, §29's `key_faceT_of_pos_unique` closes the face-length clause outright: its `hneg`
is §22's `face_encard_le_union_of_dot_w_nonpos` (`:2761`, free — `hdom` is discharged by
`dom_self` `:2754` since the corners are reached from `Â_i` itself), its `hJ` is
lane-hroom-close's `faceJ_encard_le`, and its `huniq` is `eq_neg_m_of_dot_pos` below.

So `shellEnv`'s face-length clause is no longer a leaf.  What remains of `shellEnv` is the
lattice-convexity clause (`IsLatticeConvexRegion (reachSet Â_i w)`, §25, with lane-tower3) and
the corner data feeding `hp`/`hq` (§28, §14).

## Numeric instance (硬规矩6)

Continuing §14/§15/§24/§26/§27/§28/§29: `nJ = m = (0,1)`, `w = (1,-1)`, `J = (0,-1)`,
`p = (-3,-6)`, `q = (7,-6)`, `c = cJ - ε = -6`.

* `dot m p = -6 = c` ✓, `dot m q = -6 = c` ✓, so both corners are on the cut line.
* `q - p = (10,0) ≠ 0`, and `dot m (q-p) = 0*10 + 1*0 = 0` ✓.
* A normal `n` with `dot n (q-p) = 0` needs `10 * n.1 = 0`, so `n.1 = 0`; primitive forces
  `n = (0,1) = m` or `n = (0,-1) = -m` ✓ — the two-fold ambiguity of step 4.
* `dot m w = 0*1 + 1*(-1) = -1 < 0`, while `dot (-m) w = 1 > 0`.  So the sign test in step 5
  picks out `-m = (0,-1) = J` and rejects `m` ✓.
-/


namespace Nivat.LaneCdUniq

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.LaneCdEsub

/-- **The positive class is exactly `{-m}`.**  Isolates the `0 < dot n u` branch of §23's
`mem_E_or_eq_n₀_or_eq_m` (`ShellSubStrip.lean:2965`) and adds the sign test that rules out
`n = m`. -/
theorem eq_neg_m_of_dot_pos {A : Set (ℤ × ℤ)} {u m p q n : ℤ × ℤ} {c : ℤ}
    (hm : Primitive m)
    (hpc : dot m p = c) (hqc : dot m q = c)
    (hstep : ∀ z ∈ A, z + u ∈ latHull (A ∪ {p, q}))
    (hmu : dot m u < 0)
    (hn : n ∈ E (A ∪ {p, q}))
    (hnu : 0 < dot n u) :
    n = -m := by
  have hnprim : Primitive n := prim_iff_primitive.mp hn.1
  have hempty := face_inter_eq_empty_of_dot_pos hnu hstep
  obtain ⟨a, ha, b, hb, hab⟩ := hn.2
  have hcorner : ∀ y ∈ face (A ∪ {p, q}) n, y = p ∨ y = q := by
    intro y hy
    rcases hy.1 with h | h
    · exact absurd (Set.mem_inter hy h) (by rw [hempty]; exact Set.notMem_empty y)
    · rcases h with rfl | h
      · exact Or.inl rfl
      · rw [Set.mem_singleton_iff] at h; exact Or.inr h
  have hma : dot m a = c := by rcases hcorner a ha with rfl | rfl; exacts [hpc, hqc]
  have hmb : dot m b = c := by rcases hcorner b hb with rfl | rfl; exacts [hpc, hqc]
  have hnsub : dot n (b - a) = 0 := LaneCdEsub.dot_sub_eq_zero_of_mem_face ha hb
  have hmsub : dot m (b - a) = 0 := by
    have : dot m (b - a) = dot m b - dot m a := by
      cases m; cases a; cases b; simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring
    omega
  have hba : b - a ≠ 0 := sub_ne_zero_of_ne (Ne.symm hab)
  have hdet : det m n = 0 := det_eq_zero_of_dot_eq_zero hba hmsub hnsub
  rcases eq_or_eq_neg_of_det_eq_zero hm hnprim hdet with h | h
  · -- `n = m` would make the sweep decrease `dot n`, contradicting `0 < dot n u`
    exact absurd hnu (by rw [h]; omega)
  · exact h

/-- **`huniq` at the call site.**  `m := nJ`, `u := w`, `J := -nJ`; the sign input is the
binder `hsweepW`. -/
theorem uniq_J_of_dot_w_pos {A : Set (ℤ × ℤ)} {nJ w p q : ℤ × ℤ} {cut : ℤ}
    (hnJ : Primitive nJ)
    (hpc : dot nJ p = cut) (hqc : dot nJ q = cut)
    (hstep : ∀ z ∈ A, z + w ∈ latHull (A ∪ {p, q}))
    (hsweepW : dot nJ w < 0) :
    ∀ n ∈ E (A ∪ {p, q}), 0 < dot n w → n = -nJ :=
  fun _ hn hnu => eq_neg_m_of_dot_pos hnJ hpc hqc hstep hsweepW hn hnu

end Nivat.LaneCdUniq

#print axioms Nivat.LaneCdUniq.eq_neg_m_of_dot_pos
#print axioms Nivat.LaneCdUniq.uniq_J_of_dot_w_pos


/-! ## §31.  `shellEnv`'s face-length clause, closed

Lane `lane-chaindata-lead`, 2026-09-23, assembling work by `lane-hroom-close`.

§29 split the face clause on the sign of `dot n w`; §30 proved the positive class is exactly
`{-nJ} = {J}`.  This section supplies the last piece — lane-hroom-close's `n = J` leaf — and
composes everything into `hfaceT`, the face-length hypothesis of §26's
`enveloped_of_corners_of_key_faceT` (`ShellSubStrip.lean:3618`).

## Attribution

`faceJ_encard_le` is **lane-hroom-close's**, 2026-09-23, delivered sorry-free and axiom-clean
in `tmp/wip/lane-hroom-close-facelen.lean` and reproduced here verbatim so that it can be
consumed from the main tree.  It is pure composition of §15's `bottom_span_ge` (`:1545`) and
§24's `encard_face_ge_of_span` (`:3288`), and it is deliberately agnostic about where `ε`,
`k`, `L`, `tB` and `heq` come from — which is why it drops into the wiring below without
adaptation.

## How the three classes combine

For `n ∈ E X` with `X = Â_i ∪ {p, q}`:

* `dot n w ≤ 0` — §22's `face_encard_le_union_of_dot_w_nonpos` (`:2761`) gives the `X`-form
  bound, free.  Its `hdom` is `dom_self` (`:2754`), available because the corners are reached
  from `Â_i` itself (§28).  §26's `faceT_of_faceX` weakens it to the `T`-form.
* `dot n w > 0` — §30's `uniq_J_of_dot_w_pos` forces `n = -nJ = J`, and lane-hroom-close's
  leaf supplies the `T`-form bound there directly.

`hEsub` (§23's `E_union_subset`, `:3031`) is what lets the first bullet apply: it converts
`n ∈ E X` into `n ∈ E ↑𝒮_φ`, which is the form §22's lemma consumes.

## What this does and does not close

It closes `hfaceT`.  It does **not** close `hkeyE : ∀ n ∈ E ↑𝒮_φ, n ∈ E X`, the *membership*
half of §22's old `hkey`.  §22's lemma delivers that half only for `dot n w ≤ 0`; for the
positive class it is a separate question, and §30's uniqueness does not settle it (knowing the
only positive-class member of `E X` is `J` says nothing about whether a positive-class member
of `E ↑𝒮_φ` lands in `E X`).  Flagged rather than papered over.

## Numeric instance (硬规矩6)

Continuing the running data: `nJ = (0,1)`, `w = (1,-1)`, `J = (0,-1)`, `p = (-3,-6)`,
`q = (7,-6)`, `eJ = (1,0)`, `k = 10`.  The three classes at work:

* `n = (-1,0)`: `dot n w = -1 ≤ 0`, first bullet, free.
* `n = (0,-1) = J`: `dot n w = 1 > 0`, second bullet, `M ≤ k + 1 = 11 ≤ (face T J).encard`.
* `n = (0,1) = nJ`: `dot n w = -1 ≤ 0`, first bullet — note `nJ` itself is *not* in the
  positive class, which is exactly the asymmetry §30's sign test exploits.
-/


namespace Nivat.LaneCdFaceDone

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35
open Nivat.LaneCdSubstrip Nivat.LaneCdFaceT Nivat.LaneCdKeyT Nivat.LaneCdWSign
open Nivat.LaneCdFaceFree Nivat.LaneCdUniq

variable {α : Type*}

/-- **The `n = J` leaf** (lane-hroom-close, 2026-09-23).  `M ≤ L + M ≤ k ≤ k + 1 ≤
(face T J).encard`, from §15's span bound and §24's span-to-face-length bridge. -/
theorem faceJ_encard_le {Sphi : Finset (ℤ × ℤ)} {T : Set (ℤ × ℤ)}
    {J np e w p : ℤ × ℤ} {L tB k : ℤ} {M : ℕ}
    (hlcT : IsLatticeConvexRegion T)
    (hp : p ∈ T) (hk0 : 0 ≤ k) (hq : p + k • e ∈ T)
    (he : e ≠ 0) (hne : dot J e = 0)
    (hmax : ∀ z ∈ T, dot J z ≤ dot J p)
    (hM : (face (↑Sphi : Set (ℤ × ℤ)) J).encard = (M : ℕ∞))
    (hnpe : dot np e < 0) (hnpw : dot np w < 0)
    (hL0 : 0 ≤ L)
    (htB : (M : ℤ) * (-dot np e) ≤ tB)
    (heq : k * dot np e = L * dot np e + tB * dot np w) :
    (face (↑Sphi : Set (ℤ × ℤ)) J).encard ≤ (face T J).encard := by
  have hspan : L + (M : ℤ) ≤ k :=
    bottom_span_ge hnpe hnpw (by exact_mod_cast Nat.zero_le M) htB heq
  have hMk : (M : ℤ) ≤ k := by omega
  obtain ⟨kn, hkn⟩ : ∃ kn : ℕ, (kn : ℤ) = k := ⟨k.toNat, Int.toNat_of_nonneg hk0⟩
  have hq' : p + (kn : ℤ) • e ∈ T := by rw [hkn]; exact hq
  have hbound : ((kn : ℕ∞) + 1) ≤ (face T J).encard :=
    encard_face_ge_of_span hlcT hp hq' he hne hmax
  have hMkn' : M ≤ kn := by exact_mod_cast (hkn ▸ hMk : (M : ℤ) ≤ (kn : ℤ))
  have hchain : (M : ℕ∞) ≤ (kn : ℕ∞) + 1 :=
    le_trans (by exact_mod_cast hMkn') le_self_add
  rw [hM]
  exact hchain.trans hbound

/-- **`hfaceT`, closed.**  Every hypothesis is either a binder of `ofPartsExhaustsInter`, a
§22/§23 theorem, or lane-hroom-close's leaf; nothing is left open in the face-length clause. -/
theorem face_clause_closed (η xper : Config α) (vl : ℤ × ℤ)
    (S : Finset (ℤ × ℤ)) (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ))
    (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i)) (i : ℕ)
    {Tset : Set (ℤ × ℤ)} {p q nJ w : ℤ × ℤ} {cut : ℤ}
    (h1 : hatOf A kk vl i ∪ {p, q} ⊆ Tset)
    (h2 : Tset ⊆ latHull (hatOf A kk vl i ∪ {p, q}))
    (hpr : p ∈ reachSet (hatOf A kk vl i) w)
    (hqr : q ∈ reachSet (hatOf A kk vl i) w)
    (hEsub : E (hatOf A kk vl i ∪ {p, q}) ⊆ E (↑S : Set (ℤ × ℤ)))
    (hnJ : Primitive nJ) (hpc : dot nJ p = cut) (hqc : dot nJ q = cut)
    (hstep : ∀ z ∈ hatOf A kk vl i, z + w ∈ latHull (hatOf A kk vl i ∪ {p, q}))
    (hsweepW : dot nJ w < 0)
    (hJ : (face (↑S : Set (ℤ × ℤ)) (-nJ)).encard ≤ (face Tset (-nJ)).encard) :
    ∀ n ∈ E (hatOf A kk vl i ∪ {p, q}),
      (face (↑S : Set (ℤ × ℤ)) n).encard ≤ (face Tset n).encard :=
  key_faceT_of_pos_unique h1 h2
    (fun _n hn hnw =>
      (face_encard_le_union_of_dot_w_nonpos η xper vl S Env B A u kk hEnv maxA i
        hpr hqr (hEsub hn) hnw).2)
    (uniq_J_of_dot_w_pos (A := hatOf A kk vl i) hnJ hpc hqc hstep hsweepW)
    hJ

end Nivat.LaneCdFaceDone

#print axioms Nivat.LaneCdFaceDone.faceJ_encard_le
#print axioms Nivat.LaneCdFaceDone.face_clause_closed


/-! ## §32.  The two bottom corners, constructed

Lane `lane-chaindata-lead`, 2026-09-23.  Continues §28.

§28 reduced `hcover` to the existence of two corners `p`, `q` sitting on the cut line
`dot nJ · = cJ - ε` and extremal for `dir w` on `Â_i` in opposite senses.  This section
constructs them.

## The construction, and why `dir w` makes it work

§28 showed the auxiliary normal is forced to be `dir w` (it must be `w`-orthogonal).  That
choice pays a second dividend here, which is the whole reason the construction is cheap:

```
dot (dir w) (g + t • w) = dot (dir w) g + t * dot (dir w) w = dot (dir w) g,
```

since `dot (dir w) w = 0` (§28's `dot_dir_self`).  **Sweeping along `w` does not change the
`dir w` value.**  So we may take `g` extremal for `dir w` on `Â_i`, sweep it down `w` until it
lands on the cut line, and the resulting corner inherits `g`'s extremality for free — no
separate argument that the corner is still extremal, because the sweep moves along the level
set of the very functional we are extremising.

That is exactly the content of `dot_dir_invariant` and `exists_corner_at_level` below.  The
same computation is what makes §18's `hn₀u : dot n₀ u = 0` hypothesis satisfiable at all.

## Where `ε` is actually pinned

Sweeping by `w` moves `dot nJ` in steps of `dot nJ w < 0`, so landing **exactly** on
`dot nJ · = cJ - ε` requires

```
(-dot nJ w) ∣ (dot nJ g - (cJ - ε)).
```

This is the third independent constraint on `ε`, alongside §23's `ε ≥ |dot nJ w|` and
§15/§24's span bound.  It is a *divisibility* constraint rather than a lower bound, which is
why §14's `exists_eps_corner_lattice` (`ShellSubStrip.lean:1454`) is built the way it is: its
`ε := (N+1) * ((-dot n v) * (-dot n w)).toNat` is a multiple of `(-dot n w)` **and** exceeds
any prescribed `N`, so it discharges a lower bound and a divisibility condition
simultaneously.  That is the mechanism by which a single explicit `max`-style choice of `ε`
can satisfy all three constraints at once, and it is the concrete reason `OPEN.md` #9 should
be resolved in favour of `∃ ε₀, ∀ ε ≥ ε₀` **restricted to admissible `ε`** rather than a bare
`∀ ε` — a bare `∀ ε` is false, since most `ε` fail the divisibility condition and no corner
exists on that line at all.

`exists_corner_of_dvd_mul` below records the divisibility in the form §14 supplies it.

## Numeric instance (硬规矩6)

Continuing the running data: `nJ = (0,1)`, `w = (1,-1)`, `cJ = 0`, `ε = 6`, so the cut line is
`dot nJ · = -6`, i.e. `z.2 = -6`.  Take `g = (3,0) ∈ Â_i` (level `dot nJ g = 0`).

* `-dot nJ w = 1`, which divides `dot nJ g - (cJ - ε) = 0 - (-6) = 6` ✓, with `t = 6`.
* `p = g + 6 • w = (3,0) + (6,-6) = (9,-6)`, and `dot nJ p = -6` ✓ — on the cut line.
* `dir w = (1,1)`, and `dot (dir w) g = 3 + 0 = 3`, `dot (dir w) p = 9 - 6 = 3` ✓ — unchanged
  by the sweep, as claimed.

Had `w = (1,-2)` instead, `-dot nJ w = 2`, which divides `6` ✓ with `t = 3`; but a cut at
`ε = 5` would need `2 ∣ 5`, which fails — no corner exists on that line, confirming that `ε`
cannot be quantified universally.

Consumer: §28's `shellT_subset_latHull` and `mem_shellT_of_corner`, hence `shellEnv`
(`ChainExhaustInter.lean`), hence `RegionSteps.lean:1166` `exists_chainData`.
-/


namespace Nivat.LaneCdCorner

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.LaneCdCover

/-- **Sweeping by `w` preserves the `dir w` value.**  The reason extremality transfers to the
corners for free. -/
theorem dot_dir_invariant (w g : ℤ × ℤ) (t : ℤ) :
    dot (dir w) (g + t • w) = dot (dir w) g := by
  rw [dot_add, Nivat.ColleReg.dot_zsmul_right, dot_dir_self]
  ring

/-- **The corner at a prescribed level.**  Sweep `g` down `w` onto the line `dot nJ · = c`;
the landing point keeps `g`'s `dir w` value.  The divisibility hypothesis is what makes the
landing exact. -/
theorem exists_corner_at_level {A : Set (ℤ × ℤ)} {nJ w g : ℤ × ℤ} {c : ℤ}
    (hsweepW : dot nJ w < 0) (hg : g ∈ A)
    (hge : c ≤ dot nJ g)
    (hdvd : (-dot nJ w) ∣ (dot nJ g - c)) :
    ∃ p ∈ reachSet A w, dot nJ p = c ∧ dot (dir w) p = dot (dir w) g := by
  obtain ⟨t, ht⟩ := hdvd
  have hD : 0 < -dot nJ w := by omega
  have ht0 : 0 ≤ t := by nlinarith
  refine ⟨g + (t.toNat : ℤ) • w, ⟨g, hg, t.toNat, rfl⟩, ?_, dot_dir_invariant w g _⟩
  rw [dot_add, Nivat.ColleReg.dot_zsmul_right, Int.toNat_of_nonneg ht0]
  linarith [ht]

/-- The divisibility in the shape §14's `exists_eps_corner_lattice` supplies it: its `ε` is a
multiple of `(-dot nJ w)`, so any level `dot nJ g - ε` reached from a lattice level of `g` is
admissible. -/
theorem exists_corner_of_dvd_mul {A : Set (ℤ × ℤ)} {nJ w g : ℤ × ℤ} {ε : ℤ} (k : ℤ)
    (hsweepW : dot nJ w < 0) (hg : g ∈ A)
    (hε : ε = (-dot nJ w) * k) (hk0 : 0 ≤ k) :
    ∃ p ∈ reachSet A w, dot nJ p = dot nJ g - ε ∧ dot (dir w) p = dot (dir w) g := by
  refine exists_corner_at_level hsweepW hg (by nlinarith) ⟨k, by omega⟩

/-! ### Extremality transfers -/

/-- **The `dir w`-maximal corner.**  If `g` attains `suppVal Â_i (dir w)` then so does the
corner swept from it, which is §18's `hpmax` in the form §28 consumes. -/
theorem corner_suppVal_of_mem_face {A : Set (ℤ × ℤ)} {nJ w g : ℤ × ℤ} {c : ℤ}
    (hsweepW : dot nJ w < 0) (hgf : g ∈ face A (dir w))
    (hge : c ≤ dot nJ g)
    (hdvd : (-dot nJ w) ∣ (dot nJ g - c)) :
    ∃ p ∈ reachSet A w, dot nJ p = c ∧ dot (dir w) p = suppVal A (dir w) := by
  obtain ⟨p, hpr, hpc, hpd⟩ := exists_corner_at_level hsweepW hgf.1 hge hdvd
  exact ⟨p, hpr, hpc, by rw [hpd, suppVal_eq hgf]⟩

/-- **The `dir w`-minimal corner**, i.e. the one extremal for `-(dir w)`, which is §18's
`hqmin` in the form §28 consumes. -/
theorem corner_neg_suppVal_of_mem_face {A : Set (ℤ × ℤ)} {nJ w g : ℤ × ℤ} {c : ℤ}
    (hsweepW : dot nJ w < 0) (hgf : g ∈ face A (-(dir w)))
    (hge : c ≤ dot nJ g)
    (hdvd : (-dot nJ w) ∣ (dot nJ g - c)) :
    ∃ q ∈ reachSet A w, dot nJ q = c ∧ dot (dir w) q = - suppVal A (-(dir w)) := by
  obtain ⟨q, hqr, hqc, hqd⟩ := exists_corner_at_level hsweepW hgf.1 hge hdvd
  refine ⟨q, hqr, hqc, ?_⟩
  rw [hqd, suppVal_eq hgf, dot_neg_left]
  ring

end Nivat.LaneCdCorner

#print axioms Nivat.LaneCdCorner.dot_dir_invariant
#print axioms Nivat.LaneCdCorner.exists_corner_at_level
#print axioms Nivat.LaneCdCorner.exists_corner_of_dvd_mul
#print axioms Nivat.LaneCdCorner.corner_suppVal_of_mem_face
#print axioms Nivat.LaneCdCorner.corner_neg_suppVal_of_mem_face


/-! ## §33.  `hstep` is free, and the exact residue of `shellEnv`

Lane `lane-chaindata-lead`, 2026-09-23.  Closes the plumbing begun in §27/§28/§32.

§23's `E_union_subset` (`ShellSubStrip.lean:3031`) and §30's `uniq_J_of_dot_w_pos` both take a
hypothesis

```
hstep : ∀ z ∈ Â_i, z + w ∈ latHull (Â_i ∪ {p, q}),
```

which has been passed along unexamined since §23.  It is free, and the price is exactly the
`ε` lower bound §23 already identified.

## Why `hstep` costs only `ε ≥ |⟪nJ, w⟫|`

A single `w`-step from `z ∈ Â_i` lands in `reachSet Â_i w` trivially (take `t = 1`).  For §18's
`sweep_cut_subset_latHull` (`:1835`) to apply, the step must also clear the cut line:

```
dot nJ (z + w) = dot nJ z + dot nJ w ≥ cJ + dot nJ w = cJ - (-dot nJ w),
```

using `hhp : Â_i ⊆ halfPlaneGE nJ cJ`.  So `z + w ∈ halfPlaneGE nJ (cJ - ε)` as soon as
`-dot nJ w ≤ ε` — which is **precisely** §23's constraint `ε ≥ |⟪nJ, w⟫|`, recorded there as
a requirement on the eventual choice of `ε` and never discharged.  `hstep_of_eps` below
discharges it.

Note that this route goes through `sweep_cut_subset_latHull` **directly**, not through §28's
`shellT_subset_latHull`.  That matters: `shellT` also requires membership in
`MaxEnv.shell Â_∞ vJ1 nJ cJ ε`, whose witness needs `z + w` to be `vJ1`-reachable from `Â_∞`,
which is not available.  Going straight to the half-plane form avoids the detour entirely.
Recording this because the shorter-looking route is the one that does not work.

## The exact residue of `shellEnv`

**⚠ 2026-09-23 更正（lane-chaindata-lead，集成者独立复核通过）**：§32 的两角路线（`corner_suppVal_of_mem_face`/
`corner_neg_suppVal_of_mem_face`）带一条跟 `ε` 无关的整除前提 `|det J νJ1| ∣ 宽度`，内核反例
（`tmp/wip/lane-cd-width.lean`，格凸平行四边形 `{0≤y≤4, 0≤2x-y≤3}`：宽度 `3`，`det J νJ1=2`，
`2∤3`）证明两角路线**不是通路**，不是 `ε` 没选好。改用**底行**路线
（`tmp/wip/lane-cd-bottoms.lean`）：被覆盖集合只含格点，不需要够到实数交点 `Y`；每条
`w`-射线离开半平面前的最后一个格点 `cutBottom` 打包成 `C : Finset`，
`sweep_cut_subset_latHull_bottom` **无条件**证出 `shellT ⊆ latHull (Â_i ∪ ↑C)`（对任意 `c`/`ε`
零约束，不用整除、不用 `det≠0`、不用良序）。`↑C ⊆ shellT` 那一半仍未获得——底点未必从
`Â_∞` 沿 `vJ1` 可达（`w`-射线与 `shellT` 的交一般不是初始段），这正是本节 `:4519-4523`
已经记过的同一个坑，现表述为 `hC`，与 `BottomRoom.window_of_shell` 的 `hPsub`
（`BottomRoom.lean:1051`）是同一件 `vJ1`-可达性，不是新债。

⛔ **订正 2026-09-24（集成者，第 210 轮；lane-tower-hbase 抓，§14 原文不删）**：上一句
**方向搞反了，`hC` 是真债**。两者朝向相反：
* `hPsub : P ⊆ reachSet T vJ1` 是**从 `P` 里投影出来**——`P = shellInter Âi (shell T vJ1 nJ cJ ε) w`
  已经把 `shell` 作为合取支含在自己定义里，所以取右投影再丢掉层高切就完事。
  lane-tower-hbase 已把它证成**零假设**（`hPsub_hatOf`，`tmp/wip/lane-tower-hbase-psub.lean`，
  公理只有 `[propext, Quot.sound]`），链上 `w` 的读法之争、`det vJ1 w` 的符号一个都不进来。
* `hC : ↑C ⊆ shellT` 是**把 `cutBottom` 的底点放进去**——要证那些点确实从 `Â_∞` 沿 `vJ1` 可达，是**构造**。
  `hPsub` 免费恰恰说明这个等号不成立：免费的那条是投影，构造那条不因它而关。
⟹ 下表「与 `window_of_shell` 的 `hPsub` 同一件」那一行同样作废；`↑C ⊆ shellT` 仍是 open，
**不要**拿 `hPsub` 已关去核销它。
另：`BottomRoom.lean:1051` 腐烂（那行是 `hlcP`，`hPsub` 实际在 `:1052`）——按 §85 此处只认字段名
`window_of_shell` 的 `hPsub`，行号不再维护。

With §33 in place, §27's `hopen` decomposes with nothing unexamined left in it.  Per `i`:

| `hopen` component | status |
|---|---|
| `IsLatticeConvexRegion (shellT …)` | **open** — §25, lane-tower3 |
| `↑C ⊆ shellT`（原 `p, q ∈ shellT`） | **open** — 底行 `vJ1`-可达性。⛔ 原写「与 `window_of_shell` 的 `hPsub` 同一件」，方向搞反了（见上文订正）：`hPsub` 是投影出、已零假设关掉，`hC` 是构造进、**不因此关** |
| `shellT ⊆ latHull (Â_i ∪ ↑C)` | **done（无条件）** — `lane-cd-bottoms.lean` `sweep_cut_subset_latHull_bottom`，§32 两角路线已废弃 |
| `hkeyE` (membership, `dot n w > 0`) | **open** — lane-hroom-close |
| `hother` (`dot n w ≤ 0` face bound) | §22 `face_encard_le_union_of_dot_w_nonpos` — **done** |
| `n = J` face bound | lane-hroom-close's `faceJ_encard_le`, §31 — **done** |
| `hEsub` | **需重证** — §23 `E_union_subset`（`:3031`）按 `Â_i ∪ {p,q}` 写，对多角 `C` 不逐字适用；但 `Â_i∪↑C ⊆ T ⊆ latHull(Â_i∪↑C)` 让 §17 `E_eq_of_sandwich`（`:1686`）把它变成关于 `E T` 的陈述，即 `Enveloped ↑𝒮_φ T` 要的东西，不是倒退 |

So `shellEnv` is down to exactly three open items (`IsLatticeConvexRegion`, `↑C ⊆ shellT`,
`hkeyE`) plus a needs-reproof-not-regression item (`hEsub`).  §32's corner construction and
§33's `hstep_of_eps` are not deleted — they remain correct as far as they go — but the
two-corner route they feed is no longer load-bearing; `ε` now only carries the two lower
bounds from §23 and §15/§24, satisfiable by a single explicit `max`.

## Numeric instance (硬规矩6)

Continuing the running data: `nJ = (0,1)`, `w = (1,-1)`, `cJ = 0`, `ε = 6`.  Then
`-dot nJ w = 1 ≤ 6 = ε` ✓, so `hstep` applies.  For `z = (3,0) ∈ Â_i` (level `0 ≥ cJ`):
`z + w = (4,-1)`, level `-1 ≥ -6 = cJ - ε` ✓ — the step clears the cut line with margin `5`.

Had `ε = 0`, the step to level `-1` would fall below `cJ - ε = 0` and `hstep` would fail: the
constraint is not vacuous, which is why §23 flagged `0 < ε` as insufficient.
-/


namespace Nivat.LaneCdStep

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.LaneCdSubstrip Nivat.LaneCdCover

/-- **`hstep` is free once `ε ≥ |⟪nJ, w⟫|`.**  Discharges the hypothesis §23 and §30 have
been carrying, at exactly the `ε` cost §23 predicted. -/
theorem hstep_of_eps {A : Set (ℤ × ℤ)} {nJ w p q : ℤ × ℤ} {cJ : ℤ} {ε : ℕ}
    (hAfin : A.Finite) (hAne : A.Nonempty)
    (hsweepW : dot nJ w < 0)
    (hhp : A ⊆ Nivat.LE2.halfPlaneGE nJ cJ)
    (hεw : (-dot nJ w) ≤ (ε : ℤ))
    (hpc : dot nJ p = cJ - (ε : ℤ))
    (hpmax : dot (dir w) p = suppVal A (dir w))
    (hqc : dot nJ q = cJ - (ε : ℤ))
    (hqmin : dot (dir w) q = - suppVal A (-(dir w))) :
    ∀ z ∈ A, z + w ∈ latHull (A ∪ {p, q}) := by
  have hdet : det nJ (dir w) ≠ 0 := by rw [det_dir_eq_dot]; omega
  have hcov := sweep_cut_subset_latHull (u := w) (m := nJ) (n₀ := dir w) (c := cJ - (ε : ℤ))
    hAfin hAne hdet hsweepW (dot_dir_self w) hpc hpmax hqc hqmin
  intro z hz
  refine hcov ⟨⟨z, hz, 1, by simp⟩, ?_⟩
  have hzc : cJ ≤ dot nJ z := by
    simpa only [Nivat.LE2.halfPlaneGE, Set.mem_ofPred_eq] using hhp hz
  have hstep : dot nJ (z + w) = dot nJ z + dot nJ w := dot_add nJ z w
  simp only [Nivat.LE2.halfPlaneGE, Set.mem_ofPred_eq]
  omega

end Nivat.LaneCdStep

#print axioms Nivat.LaneCdStep.hstep_of_eps


/-!
# §34 `lane-cd-reachgap`: `reachSet Â_i w` is not lattice convex even when `w` is an edge direction of `Â_i`,
# and the band cut does not repair it

`ShellSubStrip.lean` §25 (`LaneCdHlc.isLatticeConvexRegion_shellInter`, `:3449`) proves
`hlcT` for the `shellEnv` call site by splitting

    shellInter Â_i (shell Â_∞ vJ1 nJ cJ ε) w  =  reachSet Â_i w  ∩  shell Â_∞ vJ1 nJ cJ ε

and asking for each factor to be lattice convex separately.  This file kills that split.

## What was and was not already known

`RegionSweep.not_levelInterval_pair` (`RegionSweep.lean:447`) and lane-tower3's two instances
refute `LevelInterval C w`, which is only the **sufficient** side condition of
`isLatticeConvexRegion_sweep` (`RegionSweep.lean:213`).  Failing a sufficient condition refutes
nothing about the conclusion.  What is proved here is the conclusion itself, and under the two
extra properties that were the standing candidates for the missing hypothesis:

* `Tri` is **full-dimensional** (a genuine lattice triangle, 3 edges, positive area) — so
  non-degeneracy is not the missing condition;
* `wT` is an **edge direction of `Tri` itself** (`isEdge_Tri_nT`, `dot_nT_wT`: `nT` is a real
  edge normal of `Tri` and `wT ⊥ nT`), not a free primitive vector — so "`w` comes from
  `Â_i`'s own edge structure", the shape team-lead and lane-tower3 identified as the likely
  repair, is not the missing condition either.

## The numeric instance (硬规矩 6, worked by hand before any Lean)

`Tri := conv{(0,0), (1,3), (3,1)} ∩ ℤ² = {z | z₁ ≤ 3z₂, z₂ ≤ 3z₁, z₁+z₂ ≤ 4}`, i.e.
`{(0,0), (1,1), (1,2), (2,1), (2,2), (1,3), (3,1)}`.  Take `wT := (1,-1)`.

`nT := (1,1)` is an edge normal: `dot nT` is maximal (`= 4`) exactly on `{(1,3),(2,2),(3,1)}`,
three collinear lattice points spaced by `wT`, and `dot nT wT = 0`.  So `wT` is that edge's
own direction.

Sweep levels.  `det wT z = wT₁z₂ - wT₂z₁ = z₁ + z₂`, so `Tri`'s `wT`-levels are
`{0, 2, 3, 4}` — level `1` is skipped, because the chord of `conv Tri` at `z₁+z₂ = 1` runs
from `(1/4, 3/4)` to `(3/4, 1/4)`, of `wT`-length `1/2 < 1`, and a chord shorter than one
lattice step of a primitive direction need not contain a lattice point.  **That is the whole
obstruction, and it sits at the apex `(0,0)`, arbitrarily far from the edge that `wT` runs
along.**  Lengthening the edges of `Tri` does not touch it.

Concretely: `(0,0) ∈ Tri ⊆ reachSet Tri wT` and `(2,0) = (1,1) + 1 • wT ∈ reachSet Tri wT`,
their midpoint is `(1,0)`, and `(1,0) ∉ reachSet Tri wT` — a point `(1,0) = g + t • wT` forces
`g = (1-t, t)` with `1-t ≤ 3t` (so `t ≥ 1`) and `t ≤ 3(1-t)` (so `t ≤ 0`).

## The band does not repair it

`shellInter … w`'s second factor only ever **adds** constraints of the form `cJ - ε ≤ dot nJ ·`
(`MaxEnv.shell_eq_reach_inter`, `ShellLine.lean:44`).  With `nJT := (0,1)` and `cJ := 0`:
`hhp` holds (`Tri ⊆ halfPlaneGE nJT 0`, since `z₁ ≤ 3z₂ ∧ z₂ ≤ 3z₁` forces `z₂ ≥ 0`),
`hsweepW` holds (`dot nJT wT = -1 < 0`), and the two sandwiching points `(0,0)`, `(2,0)` and
the missing midpoint `(1,0)` **all sit on the line `dot nJT · = 0 = cJ`**, i.e. inside the band
for every `ε`.  So intersecting with the band removes neither the two witnesses nor the gap:
`not_isLatticeConvexRegion_reachSet_Tri_band` refutes the cut form for every `ε`.

## Consequence for §25

No regrouping of the intersection that keeps `reachSet Â_i w` as a standalone lattice-convex
factor can work, and no repair that argues "only inside the band" can work either.  The missing
hypothesis has to forbid short `w`-chords *of `Â_i` itself, in the band*, which is a statement
about `Â_i`'s vertices and not about `w`'s provenance.  Recorded rather than guessed at.

Not a refutation of `shellEnv` or of any `ChainDataGeom` field: `maxA` / `Enveloped ↑𝒮_φ Â_i`
is not instantiated here.  It refutes the implication *"the §25 split's first factor is
provable from lattice convexity of `Â_i` + `w` an edge direction of `Â_i` + `hhp` + `hsweepW`"*.
-/

namespace Nivat.LaneCdReachGap

open Nivat Nivat.LE2 Nivat.MaxEnv

/-! ## §1 The instance -/

/-- `conv{(0,0), (1,3), (3,1)} ∩ ℤ²`. -/
def Tri : Set (ℤ × ℤ) := {z | z.1 ≤ 3 * z.2 ∧ z.2 ≤ 3 * z.1 ∧ z.1 + z.2 ≤ 4}

/-- The sweep direction: the direction of `Tri`'s `(1,1)`-edge. -/
def wT : ℤ × ℤ := (1, -1)

/-- The edge normal that `wT` is the direction of. -/
def nT : ℤ × ℤ := (1, 1)

/-- The `ℓ_J` normal for the band cut. -/
def nJT : ℤ × ℤ := (0, 1)

theorem Tri_latticeConvex : IsLatticeConvexRegion Tri := by
  refine ⟨{x : ℝ × ℝ | x.1 ≤ 3 * x.2 ∧ x.2 ≤ 3 * x.1 ∧ x.1 + x.2 ≤ 4}, ?_, ?_, ?_⟩
  · intro u hu v hv a b ha hb hab
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · nlinarith [hu.1, hv.1]
    · nlinarith [hu.2.1, hv.2.1]
    · nlinarith [hu.2.2, hv.2.2]
  · have he : {x : ℝ × ℝ | x.1 ≤ 3 * x.2 ∧ x.2 ≤ 3 * x.1 ∧ x.1 + x.2 ≤ 4}
        = {x : ℝ × ℝ | x.1 ≤ 3 * x.2} ∩
          ({x : ℝ × ℝ | x.2 ≤ 3 * x.1} ∩ {x : ℝ × ℝ | x.1 + x.2 ≤ 4}) := rfl
    rw [he]
    exact (isClosed_le continuous_fst (continuous_const.mul continuous_snd)).inter
      ((isClosed_le continuous_snd (continuous_const.mul continuous_fst)).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  · ext z
    simp only [Tri, Set.mem_preimage, Set.mem_ofPred_eq, toReal]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

/-! ## §2 `wT` really is an edge direction of `Tri` -/

theorem dot_nT_wT : dot nT wT = 0 := by simp [dot, nT, wT]

theorem dot_nT_le_four : ∀ z ∈ Tri, dot nT z ≤ 4 := by
  rintro z ⟨-, -, h3⟩
  simpa only [dot, nT, one_mul] using h3

theorem mem_Tri_13 : ((1 : ℤ), (3 : ℤ)) ∈ Tri := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

theorem mem_Tri_31 : ((3 : ℤ), (1 : ℤ)) ∈ Tri := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- `nT = (1,1)` is a genuine edge normal of `Tri`: primitive, with a nontrivial exposed face
(the three collinear points `(1,3), (2,2), (3,1)`).  So `wT`, which is `⊥ nT`
(`dot_nT_wT`), is the direction of an actual edge of `Tri`. -/
theorem isEdge_Tri_nT : IsEdge Tri nT := by
  refine ⟨?_, ⟨(1, 3), ⟨mem_Tri_13, ?_⟩, (3, 1), ⟨mem_Tri_31, ?_⟩, ?_⟩⟩
  · show Int.gcd 1 1 = 1
    decide
  · intro y hy
    have := dot_nT_le_four y hy
    simp only [dot, nT] at this ⊢
    omega
  · intro y hy
    have := dot_nT_le_four y hy
    simp only [dot, nT] at this ⊢
    omega
  · intro h
    exact absurd (congrArg Prod.fst h) (by norm_num)

/-! ## §3 The gap -/

theorem mem_Tri_00 : ((0 : ℤ), (0 : ℤ)) ∈ Tri := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

theorem mem_Tri_11 : ((1 : ℤ), (1 : ℤ)) ∈ Tri := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

theorem mem_reach_00 : ((0 : ℤ), (0 : ℤ)) ∈ reachSet Tri wT :=
  ⟨(0, 0), mem_Tri_00, 0, by simp⟩

theorem mem_reach_20 : ((2 : ℤ), (0 : ℤ)) ∈ reachSet Tri wT :=
  ⟨(1, 1), mem_Tri_11, 1, by simp [wT]⟩

/-- The midpoint is missing: `(1,0) = g + t • (1,-1)` forces `g = (1-t, t)`, which needs both
`t ≥ 1` (from `g.1 ≤ 3 g.2`) and `t ≤ 0` (from `g.2 ≤ 3 g.1`). -/
theorem not_mem_reach_10 : ((1 : ℤ), (0 : ℤ)) ∉ reachSet Tri wT := by
  rintro ⟨g, ⟨hg1, hg2, -⟩, t, ht⟩
  have h1 := congrArg Prod.fst ht
  have h2 := congrArg Prod.snd ht
  simp only [wT, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  omega

/-! ## §4 The two refutations -/

/-- Generic midpoint obstruction: a lattice-convex set containing `(0,0)` and `(2,0)` contains
`(1,0)`. -/
private theorem mid_of_latticeConvex {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    (h0 : ((0 : ℤ), (0 : ℤ)) ∈ R) (h2 : ((2 : ℤ), (0 : ℤ)) ∈ R) :
    ((1 : ℤ), (0 : ℤ)) ∈ R := by
  obtain ⟨C, hconv, -, heq⟩ := hR
  rw [heq] at h0 h2 ⊢
  have hmid := hconv (Set.mem_preimage.mp h0) (Set.mem_preimage.mp h2)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hcalc : (1 / 2 : ℝ) • toReal ((0 : ℤ), (0 : ℤ)) +
      (1 / 2 : ℝ) • toReal ((2 : ℤ), (0 : ℤ)) = toReal ((1 : ℤ), (0 : ℤ)) := by
    simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    norm_num
  rw [hcalc] at hmid
  exact Set.mem_preimage.mpr hmid

/-- **§25's first factor is false**, with `Â_i` full-dimensional and `w` an edge direction of
`Â_i` itself. -/
theorem not_isLatticeConvexRegion_reachSet_Tri :
    ¬ IsLatticeConvexRegion (reachSet Tri wT) := fun h =>
  not_mem_reach_10 (mid_of_latticeConvex h mem_reach_00 mem_reach_20)

/-- `hhp` for the instance: `Tri` sits in `halfPlaneGE nJT 0`. -/
theorem Tri_subset_halfPlaneGE : ∀ z ∈ Tri, (0 : ℤ) ≤ dot nJT z := by
  rintro z ⟨h1, h2, -⟩
  simp only [dot, nJT, zero_mul, one_mul, zero_add]
  omega

/-- `hsweepW` for the instance. -/
theorem dot_nJT_wT_neg : dot nJT wT < 0 := by norm_num [dot, nJT, wT]

/-- **The band cut does not repair it**, for any `ε`: the two witnesses and the gap all lie on
`dot nJT · = 0`, so the band constraint `- ε ≤ dot nJT ·` is satisfied by all three. -/
theorem not_isLatticeConvexRegion_reachSet_Tri_band (ε : ℕ) :
    ¬ IsLatticeConvexRegion (reachSet Tri wT ∩ {z | (0 : ℤ) - (ε : ℤ) ≤ dot nJT z}) := by
  intro h
  have hband : ∀ z : ℤ × ℤ, z.2 = 0 → (0 : ℤ) - (ε : ℤ) ≤ dot nJT z := by
    intro z hz
    simp only [dot, nJT, zero_mul, one_mul, zero_add, hz]
    omega
  have h0 : ((0 : ℤ), (0 : ℤ)) ∈ reachSet Tri wT ∩ {z | (0 : ℤ) - (ε : ℤ) ≤ dot nJT z} :=
    ⟨mem_reach_00, hband _ rfl⟩
  have h2 : ((2 : ℤ), (0 : ℤ)) ∈ reachSet Tri wT ∩ {z | (0 : ℤ) - (ε : ℤ) ≤ dot nJT z} :=
    ⟨mem_reach_20, hband _ rfl⟩
  exact not_mem_reach_10 (mid_of_latticeConvex h h0 h2).1

/-- **The whole package.**  Every abstract property of `(Â_i, w, n_J, c_J)` that §25's first
factor can see, together with the refutation — including the two candidate repairs
(full-dimensionality; `w` an edge direction of `Â_i`). -/
theorem not_reachSet_latticeConvex_of_edge_direction :
    ∃ (A : Set (ℤ × ℤ)) (w n nJ : ℤ × ℤ) (cJ : ℤ),
      IsLatticeConvexRegion A ∧ A.Finite ∧
      IsEdge A n ∧ dot n w = 0 ∧ Prim w ∧
      (∀ z ∈ A, cJ ≤ dot nJ z) ∧ dot nJ w < 0 ∧
      ¬ IsLatticeConvexRegion (reachSet A w) ∧
      ∀ ε : ℕ, ¬ IsLatticeConvexRegion
        (reachSet A w ∩ {z | cJ - (ε : ℤ) ≤ dot nJ z}) := by
  refine ⟨Tri, wT, nT, nJT, 0, Tri_latticeConvex, ?_, isEdge_Tri_nT, dot_nT_wT, ?_,
    Tri_subset_halfPlaneGE, dot_nJT_wT_neg, not_isLatticeConvexRegion_reachSet_Tri,
    not_isLatticeConvexRegion_reachSet_Tri_band⟩
  · refine Set.Finite.subset (Set.finite_Icc ((0 : ℤ), (0 : ℤ)) ((4 : ℤ), (4 : ℤ))) ?_
    rintro z ⟨h1, h2, h3⟩
    constructor <;> constructor <;> simp only [] <;> omega
  · show Int.gcd 1 (-1) = 1
    decide

end Nivat.LaneCdReachGap

#print axioms Nivat.LaneCdReachGap.Tri_latticeConvex
#print axioms Nivat.LaneCdReachGap.isEdge_Tri_nT
#print axioms Nivat.LaneCdReachGap.not_isLatticeConvexRegion_reachSet_Tri
#print axioms Nivat.LaneCdReachGap.not_isLatticeConvexRegion_reachSet_Tri_band
#print axioms Nivat.LaneCdReachGap.not_reachSet_latticeConvex_of_edge_direction


/-!
# §35 `lane-cd-intercollapse`: the `Inter` route is not a new object at `w := v_{J-1}`

`ChainAssembleInter.lean` introduced `ShellMink.shellInter Â_i (MaxEnv.shell Â_∞ vJ1 nJ cJ ε) w`
to replace `ofParts`'s `MaxEnv.shell Â_i vJ1 nJ cJ ε`, on the grounds that the old object had
`shellEnv` refuted on it (`RegionClaim411.not_isLatticeConvexRegion_shell_of_formula`, `:854`)
while "none of the three is refuted on `shellInter`" (`ChainAssembleInter.lean:61-68`).

`shellInter_self_eq_shell` shows the two objects coincide **exactly** when the free parameter
`w` is instantiated at `vJ1`, which is legal: `ofPartsExhaustsInter`'s only constraint on `w`
is `hsweepW : dot nJ w < 0`, and `hsweep : dot nJ vJ1 < 0` is already a binder.  The proof is
one `ext`: `shellInter`'s left factor gives `reachSet Â_i v`, its right factor contributes only
the level inequality `cJ - ε ≤ dot nJ ·` (the reachability witness is discarded), and the
converse re-uses the *same* witness through `Â_i ⊆ Â_∞`.

Two consequences.

1. The `Inter` route's only genuine freedom over the old route is the choice `w ≠ vJ1`.  In
   particular §25's obligation (1) is not an artefact of the `Inter` reformulation: at
   `w = vJ1` it is literally the old `shellEnv`, refutation and all.
2. Combined with §34 — which kills obligation (1) for `w` an edge direction of `Â_i`, which
   `vJ1` is — retreating to `ofPartsExhausts` (`ChainExhaust.lean:66`) is not an escape from
   §34 but a special case of it.

Not a refutation of anything: `shellInter_self_eq_shell` is an unconditional set identity given
`Â_i ⊆ Â_∞`, which `ChainAsm.subShellInter_of`'s call site already has.
-/

namespace Nivat.LaneCdInterCollapse

open Nivat Nivat.LE2 Nivat.MaxEnv

/-- **At `w := v`, `shellInter` collapses to the plain shell of the inner set.**  Only
`Â_i ⊆ Â_∞` is needed. -/
theorem shellInter_self_eq_shell {A A' : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} {ε : ℕ}
    (hA : A ⊆ A') :
    ShellMink.shellInter A (MaxEnv.shell A' v n c ε) v = MaxEnv.shell A v n c ε := by
  ext z
  constructor
  · rintro ⟨⟨g, hg, t, rfl⟩, -, -, -, -, hlev⟩
    exact ⟨g, hg, t, rfl, hlev⟩
  · rintro ⟨g, hg, t, rfl, hlev⟩
    exact ⟨⟨g, hg, t, rfl⟩, g, hA hg, t, rfl, hlev⟩

end Nivat.LaneCdInterCollapse

#print axioms Nivat.LaneCdInterCollapse.shellInter_self_eq_shell

/-! ## §36  Collé's box does not repair the sweep gap (2026-09-23, lane-chaindata-lead) -/

/-!
# Collé's box does not repair the sweep-convexity gap: growth is neutral

Answer to team-lead's 2026-09-23 question ("查 Collé item (ii) 的框能不能让幺模链跨度覆盖
`Â_i` 全部层").  **No**, and the reason is structural rather than arithmetic, so no choice of
box size helps.

## The diagnosis

`det w z = dot (dir w) z`, so the levels of `det w` on a lattice set `A` are the lattice lines
parallel to `w`.  `LevelInterval A w` fails exactly when one of those lines meets `conv A` in a
segment too short to carry a lattice point.  For a convex `A` the chord length is increasing as
one moves away from the two `det w`-extreme vertices, so:

* **mid-levels**: chords grow with `A`, so growth *does* fix those;
* **the two extreme vertex cones**: the chord at level `min + 1` is cut out of the *cone* at the
  `det w`-min vertex, and that cone does not change when `A` grows.

Quantitatively, at the min vertex `v` with incident primitive edge directions `e₁, e₂` and
`a_j := det w e_j > 0`, the level-`(min+1)` chord has length `|det e₁ e₂| / (a₁ a₂) · ‖w‖`,
while consecutive lattice points on that line are `‖w‖` apart.  So the level is carried only if
`|det e₁ e₂| ≥ a₁ · a₂` — a condition on the **cone alone**, with no `A`, no size, no box in it.

For the target this is sharp, because the cone is `i`-independent: `Â_i`'s edge-normal set is
exactly `E ↑𝒮_φ` for every `i` (`LaneCdFaceFree.E_hatOf_eq`, `ShellSubStrip.lean:2723`), so the
normal fan — hence which two normals are adjacent at the vertex exposed by `-dir w`, hence the
cone — is fixed by `(E ↑𝒮_φ, w)` and does not move with `i`.  Item (ii)'s box grows `Â_i` and
therefore only ever acts on the mid-levels, which were never the obstruction.

## The witness below

`ConeK k` is the cone `u.1 ≤ u.2 ≤ 2 u.1` with apex moved to `apexK k = (-10k, -15k)` and
truncated at `z.1 + z.2 ≤ 2k`.  It contains `[-k,k]² ∩ {0 ≤ z.2}` — literally Collé's box
`[-i+1,i-1]² ∩ ℋ(ℓ^(−))` (`b3_colle2.txt:474-476`) at size `k`, which is unbounded in `k` — and
it still skips a level, for **every** `k ≥ 1`.

## Numeric instance (硬规矩 6, worked before the Lean)

Work in `u := z - apexK k`; the defining inequalities of `ConeK k` become the `k`-free cone
`u.1 ≤ u.2`, `u.2 ≤ 2 u.1` (plus the `k`-dependent truncation `u.1 + u.2 ≤ 27k`).  Sweep
direction `w = (1,-1)`, so `det w u = u.1 + u.2` and the levels are the anti-diagonals.

* `u = (0,0)` (the apex) is in the cone: level `0`.
* `u = (1,1)` is in the cone (`1 ≤ 1`, `1 ≤ 2`): level `2`.  In the truncation for `k ≥ 1`.
* **Level `1` is empty**: `u.1 + u.2 = 1` with `u.1 ≤ u.2` forces `u.1 ≤ 0`, while
  `u.2 ≤ 2u.1` forces `1 - u.1 ≤ 2u.1`, i.e. `u.1 ≥ 1`.  No lattice point.

The cone criterion agrees: `e₁ = (1,1)`, `e₂ = (1,2)`, `a₁ = det w e₁ = 2`, `a₂ = det w e₂ = 3`,
`det e₁ e₂ = 1`, and `1 ≥ 2 · 3` is false.

Transported through the sweep: `apexK k` and `apexK k + (2,0)` are both in
`reachSet (ConeK k) w` (the latter via `apexK k + (1,1)`, one `w`-step back), their midpoint
`apexK k + (1,0)` is not, and all three sit on `dot (0,1) · = -15k`, which is `ConeK k`'s own
minimum in that direction — so the band cut `cJ - ε ≤ dot nJ ·` contains all three and cannot
repair it, for any `ε`.  Every number here is `k`-free except the truncation, exactly as the
diagnosis predicts.

This strictly extends `LaneCdReachGap` (`ShellSubStrip.lean:4643`, §34), which refuted the same
factor for one fixed set; the new content is the `∀ k`, and the explicit box containment.
-/

namespace Nivat.LaneCdBoxGrow

open Nivat Nivat.LE2 Nivat.MaxEnv

/-! ## §1 The instance -/

/-- The cone `u.1 ≤ u.2 ≤ 2 u.1` with apex at `apexK k`, truncated at level `2k`. -/
def ConeK (k : ℤ) : Set (ℤ × ℤ) :=
  {z | z.1 ≤ z.2 + 5 * k ∧ z.2 ≤ 2 * z.1 + 5 * k ∧ z.1 + z.2 ≤ 2 * k}

/-- The `det w`-minimal vertex of `ConeK k`, where the cone is sharp. -/
def apexK (k : ℤ) : ℤ × ℤ := (-10 * k, -15 * k)

/-- The sweep direction. -/
def wB : ℤ × ℤ := (1, -1)

/-- The `ℓ_J` normal for the band cut. -/
def nJB : ℤ × ℤ := (0, 1)

theorem ConeK_latticeConvex (k : ℤ) : IsLatticeConvexRegion (ConeK k) := by
  refine ⟨{x : ℝ × ℝ | x.1 ≤ x.2 + 5 * (k : ℝ) ∧ x.2 ≤ 2 * x.1 + 5 * (k : ℝ) ∧
    x.1 + x.2 ≤ 2 * (k : ℝ)}, ?_, ?_, ?_⟩
  · intro u hu v hv a b ha hb hab
    obtain ⟨hu1, hu2, hu3⟩ := hu
    obtain ⟨hv1, hv2, hv3⟩ := hv
    have e1 := mul_le_mul_of_nonneg_left hu1 ha
    have e2 := mul_le_mul_of_nonneg_left hv1 hb
    have e3 := mul_le_mul_of_nonneg_left hu2 ha
    have e4 := mul_le_mul_of_nonneg_left hv2 hb
    have e5 := mul_le_mul_of_nonneg_left hu3 ha
    have e6 := mul_le_mul_of_nonneg_left hv3 hb
    have hk : (k : ℝ) * a + (k : ℝ) * b = (k : ℝ) := by rw [← mul_add, hab, mul_one]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      nlinarith [e1, e2, e3, e4, e5, e6, hk]
  · have he : {x : ℝ × ℝ | x.1 ≤ x.2 + 5 * (k : ℝ) ∧ x.2 ≤ 2 * x.1 + 5 * (k : ℝ) ∧
          x.1 + x.2 ≤ 2 * (k : ℝ)}
        = {x : ℝ × ℝ | x.1 ≤ x.2 + 5 * (k : ℝ)} ∩
          ({x : ℝ × ℝ | x.2 ≤ 2 * x.1 + 5 * (k : ℝ)} ∩
            {x : ℝ × ℝ | x.1 + x.2 ≤ 2 * (k : ℝ)}) := rfl
    rw [he]
    exact (isClosed_le continuous_fst (continuous_snd.add continuous_const)).inter
      ((isClosed_le continuous_snd ((continuous_const.mul continuous_fst).add
          continuous_const)).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  · ext z
    simp only [ConeK, Set.mem_preimage, Set.mem_ofPred_eq, toReal]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

theorem ConeK_finite (k : ℤ) : (ConeK k).Finite := by
  refine Set.Finite.subset
    (Set.finite_Icc ((-10 * k, -15 * k) : ℤ × ℤ) ((17 * k, 12 * k) : ℤ × ℤ)) ?_
  rintro z ⟨h1, h2, h3⟩
  constructor <;> constructor <;> simp only [] <;> omega

/-! ## §2 The box of item (ii) really is inside, at unbounded size -/

/-- **Collé's box is inside.**  `[-k,k]² ∩ ℋ(ℓ^(−))` with `ℋ(ℓ^(−)) = {0 ≤ z.2}`, at size `k`,
sits inside `ConeK k` — so item (ii)'s containment clause (`b3_colle2.txt:474-476`) is
satisfied, with the box side growing without bound. -/
theorem box_subset_ConeK {k : ℤ} {z : ℤ × ℤ}
    (h1 : -k ≤ z.1) (h2 : z.1 ≤ k) (h3 : 0 ≤ z.2) (h4 : z.2 ≤ k) :
    z ∈ ConeK k :=
  ⟨by omega, by omega, by omega⟩

/-! ## §3 The gap, at every `k` -/

theorem mem_ConeK_apex {k : ℤ} (hk : 0 ≤ k) : apexK k ∈ ConeK k :=
  ⟨by simp only [apexK]; omega, by simp only [apexK]; omega, by simp only [apexK]; omega⟩

theorem mem_ConeK_apex_add_11 {k : ℤ} (hk : 1 ≤ k) :
    apexK k + ((1 : ℤ), (1 : ℤ)) ∈ ConeK k := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [apexK, Prod.fst_add, Prod.snd_add] <;> omega

theorem mem_reach_apex {k : ℤ} (hk : 0 ≤ k) : apexK k ∈ reachSet (ConeK k) wB :=
  ⟨apexK k, mem_ConeK_apex hk, 0, by simp⟩

theorem mem_reach_apex_add_20 {k : ℤ} (hk : 1 ≤ k) :
    apexK k + ((2 : ℤ), (0 : ℤ)) ∈ reachSet (ConeK k) wB :=
  ⟨apexK k + ((1 : ℤ), (1 : ℤ)), mem_ConeK_apex_add_11 hk, 1, by
    simp only [wB, apexK, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
    omega⟩

/-- **The gap.**  `apexK k + (1,0) = g + t • (1,-1)` forces `g = apexK k + (1-t, t)`, which needs
both `t ≥ 1` (from the `u.1 ≤ u.2` face) and `t ≤ 0` (from the `u.2 ≤ 2 u.1` face).  Neither
inequality mentions `k`. -/
theorem not_mem_reach_apex_add_10 (k : ℤ) :
    apexK k + ((1 : ℤ), (0 : ℤ)) ∉ reachSet (ConeK k) wB := by
  rintro ⟨g, ⟨hg1, hg2, -⟩, t, ht⟩
  have h1 := congrArg Prod.fst ht
  have h2 := congrArg Prod.snd ht
  simp only [wB, apexK, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at h1 h2
  omega

/-! ## §4 The refutation, and that the band cut is still irrelevant -/

/-- Midpoint obstruction, based at an arbitrary point. -/
private theorem mid_shift_of_latticeConvex {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {a : ℤ × ℤ} (h0 : a ∈ R) (h2 : a + ((2 : ℤ), (0 : ℤ)) ∈ R) :
    a + ((1 : ℤ), (0 : ℤ)) ∈ R := by
  obtain ⟨C, hconv, -, heq⟩ := hR
  rw [heq] at h0 h2 ⊢
  have hmid := hconv (Set.mem_preimage.mp h0) (Set.mem_preimage.mp h2)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hcalc : (1 / 2 : ℝ) • toReal a + (1 / 2 : ℝ) • toReal (a + ((2 : ℤ), (0 : ℤ)))
      = toReal (a + ((1 : ℤ), (0 : ℤ))) := by
    simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add,
      Prod.mk.injEq]
    constructor <;> push_cast <;> ring
  rw [hcalc] at hmid
  exact Set.mem_preimage.mpr hmid

/-- **The first factor of §25 is false for every box size.** -/
theorem not_isLatticeConvexRegion_reachSet_ConeK {k : ℤ} (hk : 1 ≤ k) :
    ¬ IsLatticeConvexRegion (reachSet (ConeK k) wB) := fun h =>
  not_mem_reach_apex_add_10 k
    (mid_shift_of_latticeConvex h (mem_reach_apex (by omega)) (mem_reach_apex_add_20 hk))

/-- `hhp` for the instance: `ConeK k` sits in `halfPlaneGE nJB (-15k)`, and `-15k` is attained
(at the apex), so the bound is sharp. -/
theorem ConeK_subset_halfPlaneGE (k : ℤ) : ∀ z ∈ ConeK k, -15 * k ≤ dot nJB z := by
  rintro z ⟨h1, h2, -⟩
  simp only [dot, nJB, zero_mul, one_mul, zero_add]
  omega

/-- `hsweepW` for the instance. -/
theorem dot_nJB_wB_neg : dot nJB wB < 0 := by norm_num [dot, nJB, wB]

/-- **The band cut still does not repair it**, at any `k` and any `ε`: all three points sit on
`dot nJB · = -15k`, which is `ConeK k`'s own minimum in that direction. -/
theorem not_isLatticeConvexRegion_reachSet_ConeK_band {k : ℤ} (hk : 1 ≤ k) (ε : ℕ) :
    ¬ IsLatticeConvexRegion
      (reachSet (ConeK k) wB ∩ {z | -15 * k - (ε : ℤ) ≤ dot nJB z}) := by
  intro h
  have hband : ∀ z : ℤ × ℤ, z.2 = -15 * k → -15 * k - (ε : ℤ) ≤ dot nJB z := by
    intro z hz
    simp only [dot, nJB, zero_mul, one_mul, zero_add, hz]
    omega
  have h0 : apexK k ∈ reachSet (ConeK k) wB ∩ {z | -15 * k - (ε : ℤ) ≤ dot nJB z} :=
    ⟨mem_reach_apex (by omega), hband _ rfl⟩
  have h2 : apexK k + ((2 : ℤ), (0 : ℤ)) ∈
      reachSet (ConeK k) wB ∩ {z | -15 * k - (ε : ℤ) ≤ dot nJB z} :=
    ⟨mem_reach_apex_add_20 hk, hband _ (by simp [apexK])⟩
  exact not_mem_reach_apex_add_10 k (mid_shift_of_latticeConvex h h0 h2).1

/-! ## §5 The package -/

/-- **Growth is neutral.**  For every box size `k`, there is a finite lattice-convex `A`
containing Collé's box `[-k,k]² ∩ ℋ(ℓ^(−))` of item (ii) (`b3_colle2.txt:474-476`), a primitive
sweep direction `w` with `dot nJ w < 0`, and a supporting level `cJ`, such that
`IsLatticeConvexRegion (reachSet A w)` is false — and stays false after the band cut, for every
`ε`.  So item (ii)'s box cannot discharge §25's first factor: the obstruction is in the
`det w`-extreme vertex cone, which growth does not touch. -/
theorem box_does_not_repair_reachSet (k : ℤ) (hk : 1 ≤ k) :
    ∃ (A : Set (ℤ × ℤ)) (w nJ : ℤ × ℤ) (cJ : ℤ),
      IsLatticeConvexRegion A ∧ A.Finite ∧ Prim w ∧
      (∀ z : ℤ × ℤ, -k ≤ z.1 → z.1 ≤ k → 0 ≤ z.2 → z.2 ≤ k → z ∈ A) ∧
      (∀ z ∈ A, cJ ≤ dot nJ z) ∧ dot nJ w < 0 ∧
      ¬ IsLatticeConvexRegion (reachSet A w) ∧
      ∀ ε : ℕ, ¬ IsLatticeConvexRegion
        (reachSet A w ∩ {z | cJ - (ε : ℤ) ≤ dot nJ z}) := by
  refine ⟨ConeK k, wB, nJB, -15 * k, ConeK_latticeConvex k, ConeK_finite k, ?_,
    fun z h1 h2 h3 h4 => box_subset_ConeK h1 h2 h3 h4,
    ConeK_subset_halfPlaneGE k, dot_nJB_wB_neg,
    not_isLatticeConvexRegion_reachSet_ConeK hk,
    not_isLatticeConvexRegion_reachSet_ConeK_band hk⟩
  show Int.gcd 1 (-1) = 1
  decide

end Nivat.LaneCdBoxGrow

#print axioms Nivat.LaneCdBoxGrow.ConeK_latticeConvex
#print axioms Nivat.LaneCdBoxGrow.box_subset_ConeK
#print axioms Nivat.LaneCdBoxGrow.not_mem_reach_apex_add_10
#print axioms Nivat.LaneCdBoxGrow.not_isLatticeConvexRegion_reachSet_ConeK
#print axioms Nivat.LaneCdBoxGrow.box_does_not_repair_reachSet

/-! ## §37  The cut slack, named (2026-09-23, lane-chaindata-lead)

`LaneHroomHkeyEJ.mem_E_J_of_corners` (`tmp/wip/lane-hroom-close-hkeye-J.lean`, 2026-09-23) is
the positive-class atom of `hkeyE`: from `p ≠ q`, both corners at `nJ`-level `cut`, and
`hA : ∀ z ∈ A, cut < dot nJ z`, it concludes `(-nJ) ∈ E (A ∪ {p,q})`.  Its one open binder is
`hA` at the real call site.  This section discharges it.

At the call site (`LaneCdSite.enveloped_shellT`, `:3796`) the set is `A := Â_i`, the corners sit
at `cut := cJ - ε` (`LaneCdSweepCut.sweep_cut_subset`'s `hpc`/`hqc`, `:3959`), and the two
inputs are already binders of `shellEnv_of_open` (`:3821`): `hhp` puts `Â_i` in
`halfPlaneGE nJ cJ`, and `hε : 0 < ε`.  So `cJ - ε < cJ ≤ dot nJ z`, strictly — the same
`ε`-slack §27's `hAT` note records as "never tight", now used for the *strict* direction.

This is exactly the fact §30's analysis (`:3172`) states in prose to explain why the `X`-form
of the `J`-face clause is false; `hA` is the same inequality read forwards.

**Numeric instance** (硬规矩 6), continuing §14/§15/§30's data: `nJ = (0,1)`, `cJ = 0`, `ε = 6`,
so `cut = -6`, `p = (-3,-6)`, `q = (7,-6)`.  Every `z ∈ Â_i` has `dot nJ z ≥ 0 > -6 = cut`. -/

namespace Nivat.LaneCdCutSlack

open Nivat Nivat.LE2 Nivat.Colle35

/-- **`hA` at the real call site.**  `Â_i` sits strictly above the cut level `cJ - ε`, for every
`i`, as soon as `ε > 0`.  This is the missing binder of
`LaneHroomHkeyEJ.mem_E_J_of_corners`. -/
theorem cut_lt_dot_nJ_of_hhp {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl nJ : ℤ × ℤ} {cJ : ℤ}
    {ε : ℕ} (hε : 0 < ε)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ) (i : ℕ) :
    ∀ z ∈ hatOf A kk vl i, cJ - (ε : ℤ) < dot nJ z := by
  intro z hz
  have hge : cJ ≤ dot nJ z := hhp i hz
  have hpos : (0 : ℤ) < (ε : ℤ) := by exact_mod_cast hε
  omega

end Nivat.LaneCdCutSlack

#print axioms Nivat.LaneCdCutSlack.cut_lt_dot_nJ_of_hhp

-- 2026-09-23（集成者）：`b3_colle2.txt:520` 的 `shellSubStrip` 路线所需的层级/参数界。
#print axioms Nivat.LaneCdSubstrip.sweep_level_ge
#print axioms Nivat.LaneCdSubstrip.sweep_param_le_tight
#print axioms Nivat.LaneCdSubstrip.sweep_param_le_of_tight
